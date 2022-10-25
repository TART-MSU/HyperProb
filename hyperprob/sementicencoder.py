import itertools

from z3 import And, Bool, Real, Int, Not, Or


def extendWithoutDuplicates(list1, list2):
    result = []
    if list1 is not None:
        result.extend(list1)
    if list2 is not None:
        result.extend(x for x in list2 if x not in result)
    return result


class SemanticsEncoder:
    def __init__(self, model, solver, list_of_subformula, list_of_bools, listOfBools, list_of_ints, listOfInts,
                 no_of_subformula, no_of_state_quantifier):
        self.model = model
        self.solver = solver
        self.list_of_subformula = list_of_subformula
        self.list_of_reals = []
        self.listOfReals = []
        self.list_of_bools = list_of_bools
        self.listOfBools = listOfBools
        self.list_of_ints = list_of_ints
        self.listOfInts = listOfInts
        self.no_of_subformula = no_of_subformula
        self.no_of_state_quantifier = no_of_state_quantifier

    def encodeSemantics(self, hyperproperty, prev_relevant_quantifier=[]):
        relevant_quantifier = []
        if len(prev_relevant_quantifier) > 0:
            relevant_quantifier.extend(prev_relevant_quantifier)

        if hyperproperty.data == 'true':
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            name = "holds"
            r_state = [0 for ind in range(self.no_of_state_quantifier)]
            for ind in r_state:
                name += "_" + str(ind)
            name += '_' + str(index_of_phi)
            self.addToVariableList(name)
            self.solver.add(self.listOfBools[self.list_of_bools.index(name)])
            self.no_of_subformula += 1
            return relevant_quantifier

        elif hyperproperty.data == 'atomic_proposition':
            ap_name = hyperproperty.children[0].children[0].value  # gets the name of the proposition
            proposition_relevant_quantifier = int(hyperproperty.children[1].children[0].value[1])  # gets the
            labeling = self.model.parsed_model.labeling
            if proposition_relevant_quantifier not in relevant_quantifier:
                relevant_quantifier.append(proposition_relevant_quantifier)
            and_for_yes = set()
            and_for_no = set()
            list_of_state_with_ap = []

            index_of_phi = self.list_of_subformula.index(hyperproperty)
            for state in self.model.getListOfStates():
                if ap_name in labeling.get_labels_of_state(state):
                    list_of_state_with_ap.append(state)
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            for r_state in combined_state_list:
                name = 'holds'
                for ind in r_state:
                    name += "_" + str(ind)
                name += '_' + str(index_of_phi)
                self.addToVariableList(name)
                if r_state[proposition_relevant_quantifier - 1] in list_of_state_with_ap:
                    and_for_yes.add(self.listOfBools[self.list_of_bools.index(name)])
                else:
                    and_for_no.add(Not(self.listOfBools[self.list_of_bools.index(name)]))
            self.solver.add(And(And([par for par in list(and_for_yes)]), And([par for par in list(and_for_no)])))
            self.no_of_subformula += 3
            and_for_yes.clear()
            and_for_no.clear()
            return relevant_quantifier
        elif hyperproperty.data == 'and':
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])
            index_of_phi2 = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for ind in r_state:
                    name1 += "_" + str(ind)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)], self.listOfBools[self.list_of_bools.index(name2)],
                                self.listOfBools[self.list_of_bools.index(name3)])
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 Or(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                    Not(self.listOfBools[self.list_of_bools.index(name3)])))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        # implement or, implies, equivalent before moving onto not
        else:
            self.encodeSemantics(hyperproperty.children[0])

    def addToVariableList(self, name):
        if name[0] == 'h' and not name.startswith('holdsToInt') and name not in self.list_of_bools:
            self.list_of_bools.append(name)
            self.listOfBools.append(Bool(name))
        elif (name[0] in ['p', 'd', 'r'] or name.startswith('holdsToInt')) and name not in self.list_of_reals:
            self.list_of_reals.append(name)
            self.listOfReals.append(Real(name))
        elif name[0] == 'a' and name not in self.list_of_ints:
            self.list_of_ints.append(name)
            self.listOfInts.append(Int(name))

    def generateComposedStates(self, list_of_relevant_quantifier):
        """
        Generates combination of states based on relevant quantifiers
        :param list_of_relevant_quantifier: ranges from value 1- (no. of quantifiers)
        :return: list of composed states.
        """
        stored_list = []
        for quant in range(1, self.no_of_state_quantifier + 1):
            if quant in list_of_relevant_quantifier:
                stored_list.append(self.model.getListOfStates())
            else:
                stored_list.append([0])
        return list(itertools.product(*stored_list))

