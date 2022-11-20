import itertools, copy

from lark import Tree
from z3 import And, Bool, Real, Int, Not, Or, Xor, RealVal, Implies


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
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)],
                                self.listOfBools[self.list_of_bools.index(name2)],
                                self.listOfBools[self.list_of_bools.index(name3)])
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 Or(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                    Not(self.listOfBools[self.list_of_bools.index(name3)])))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'or':
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
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)],
                                Or(self.listOfBools[self.list_of_bools.index(name2)],
                                   self.listOfBools[self.list_of_bools.index(name3)]))
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 And(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                     Not(self.listOfBools[self.list_of_bools.index(name3)])))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'implies':
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
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)],
                                Or(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                   self.listOfBools[self.list_of_bools.index(name3)]))
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 And(self.listOfBools[self.list_of_bools.index(name2)],
                                     Not(self.listOfBools[self.list_of_bools.index(name3)])))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'biconditional':
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
                first_and = And(self.listOfBools[self.list_of_bools.index(name1)],
                                Or(
                                    And(self.listOfBools[self.list_of_bools.index(name2)],
                                        self.listOfBools[self.list_of_bools.index(name3)]),
                                    And(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                        Not(self.listOfBools[self.list_of_bools.index(name3)]))))
                self.no_of_subformula += 1
                second_and = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 Or(
                                     And(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                                         self.listOfBools[self.list_of_bools.index(name3)]),
                                     And(self.listOfBools[self.list_of_bools.index(name2)],
                                         Not(self.listOfBools[self.list_of_bools.index(name3)]))))
                self.no_of_subformula += 1
                self.solver.add(Or(first_and, second_and))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'not':
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                          self.encodeSemantics(hyperproperty.children[0]))
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_of_phi1 = self.list_of_subformula.index(hyperproperty.children[0])

            combined_state_list = self.generateComposedStates(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'holds'
                for ind in r_state:
                    name1 += "_" + str(ind)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in r_state:
                    name2 += "_" + str(ind)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                self.solver.add(Xor(self.listOfBools[self.list_of_bools.index(name1)],
                                    self.listOfBools[self.list_of_bools.index(name2)]))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'probability':
            child = hyperproperty.children[0]
            if child.data == 'next':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeNextSemantics(hyperproperty,
                                                                                       relevant_quantifier))
            elif child.data == 'until_unbounded':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeUnboundedUntilSemantics(hyperproperty,
                                                                                                 relevant_quantifier))
            elif child.data == 'until_bounded':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeBoundedUntilSemantics(hyperproperty,
                                                                                               relevant_quantifier))
            elif child.data == 'future':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeFutureSemantics(hyperproperty,
                                                                                         relevant_quantifier))
            elif child.data == 'global':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeGlobalSemantics(hyperproperty,
                                                                                         relevant_quantifier))
            return relevant_quantifier
        elif hyperproperty.data == 'reward':
            child = hyperproperty.children[1]
            if child.data == 'next':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeRewNextSemantics(hyperproperty,
                                                                                          relevant_quantifier))
            elif child.data == 'until_unbounded':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeRewUnboundedUntilSemantics(hyperproperty,
                                                                                                    relevant_quantifier))
            elif child.data == 'until_bounded':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeRewBoundedUntilSemantics(hyperproperty,
                                                                                                  relevant_quantifier))
            elif child.data == 'future':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeRewFutureSemantics(hyperproperty,
                                                                                            relevant_quantifier))
            elif child.data == 'global':
                relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                                                              self.encodeRewGlobalSemantics(hyperproperty,
                                                                                            relevant_quantifier))
            return relevant_quantifier
        elif hyperproperty.data == 'less_probability':
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
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] < self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] >= self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'equal_probability':
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
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] == self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] != self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'greater_probability':
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
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] > self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] <= self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'greater_and_equal_probability':
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
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] >= self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] < self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'less_and_equal_probability':
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
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] <= self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] > self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'less_reward':
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
                name2 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] < self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] >= self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'equal_reward':
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
                name2 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] == self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] != self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'greater_reward':
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
                name2 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] > self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] <= self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'greater_and_equal_reward':
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
                name2 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] >= self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] < self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'less_and_equal_reward':
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
                name2 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.addToVariableList(name2)
                name3 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.addToVariableList(name3)
                and_eq = And(self.listOfBools[self.list_of_bools.index(name1)],
                             self.listOfReals[self.list_of_reals.index(name2)] <= self.listOfReals[
                                 self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.listOfBools[self.list_of_bools.index(name1)]),
                                 self.listOfReals[self.list_of_reals.index(name2)] > self.listOfReals[
                                     self.list_of_reals.index(name3)])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'constant_probability':
            constant = RealVal(hyperproperty.children[0].value).as_fraction().limit_denominator(10000)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            name = "prob"
            r_state = [0 for ind in range(self.no_of_state_quantifier)]
            for ind in r_state:
                name += "_" + str(ind)
            name += '_' + str(index_of_phi)
            self.addToVariableList(name)
            self.solver.add(self.listOfReals[self.list_of_reals.index(name)] == constant)
            self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'constant_reward':
            constant = hyperproperty.children[0].value
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            name = "rew"
            r_state = [range(self.no_of_state_quantifier)]
            for ind in r_state:
                name += "_" + str(ind)
            name += '_' + str(index_of_phi)
            self.addToVariableList(name)
            self.solver.add(self.listOfReals[self.list_of_reals.index(name)] == constant)
            self.no_of_subformula += 1
            return relevant_quantifier

        elif hyperproperty.data in ['add_probability', 'subtract_probability', 'multiply_probability']:
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_left = self.list_of_subformula.index(hyperproperty.children[0])
            index_right = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'prob'
                for ind in r_state:
                    name1 += "_" + str(ind)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_left)
                self.addToVariableList(name2)
                name3 = 'prob'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_right)
                self.addToVariableList(name3)
                if hyperproperty.data == 'add_probability':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] + self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'subtract_probability':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] - self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'multiply_probability':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] * self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                else:
                    print("Unexpected operator. Exiting")
                    return -1
            return relevant_quantifier

        elif hyperproperty.data in ['add_reward', 'subtract_reward', 'multiply_reward']:
            rel_quant1 = self.encodeSemantics(hyperproperty.children[0])
            rel_quant2 = self.encodeSemantics(hyperproperty.children[1])
            relevant_quantifier = extendWithoutDuplicates(rel_quant1, rel_quant2)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            index_left = self.list_of_subformula.index(hyperproperty.children[0])
            index_right = self.list_of_subformula.index(hyperproperty.children[1])
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            for r_state in combined_state_list:
                name1 = 'rew'
                for ind in r_state:
                    name1 += "_" + str(ind)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_left)
                self.addToVariableList(name2)
                name3 = 'rew'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_right)
                self.addToVariableList(name3)
                if hyperproperty.data == 'add_reward':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] + self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'subtract_reward':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] - self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'multiply_reward':
                    self.solver.add(self.listOfReals[self.list_of_reals.index(name1)] == (
                            self.listOfReals[self.list_of_reals.index(name2)] * self.listOfReals[
                        self.list_of_reals.index(name3)]))
                    self.no_of_subformula += 2
                else:
                    print("Unexpected operator. Exiting")
                    return -1
            return relevant_quantifier
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

    def encodeNextSemantics(self, hyperproperty, prev_relevant_quantifier=[]):
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        relevant_quantifier = self.encodeSemantics(phi1, prev_relevant_quantifier)
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            holdsToInt1 = 'holdsToInt' + str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holdsToInt1)
            prob_phi = 'prob' + str_r_state + "_" + str(index_of_phi)
            self.addToVariableList(prob_phi)
            first_and = Or(
                And(self.listOfReals[self.list_of_reals.index(holdsToInt1)] == float(1),
                    self.listOfBools[self.list_of_bools.index(holds1)]),
                And(self.listOfReals[self.list_of_reals.index(holdsToInt1)] == float(0),
                    Not(self.listOfBools[self.list_of_bools.index(holds1)])))
            self.no_of_subformula += 3
            self.solver.add(first_and)
            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                name = 'a_' + str(r_state[relevant_quantifier[0] - 1])
                self.addToVariableList(name)
                act_str = self.listOfInts[self.list_of_ints.index(name)] == int(ca[0])
                if len(relevant_quantifier) > 1:
                    for l in range(1, len(relevant_quantifier)):
                        name = 'a_' + str(relevant_quantifier[l] - 1)
                        self.addToVariableList(name)
                        act_str = And(act_str, self.listOfInts[self.list_of_ints.index(name)] == int(ca[l - 1]))

                implies_precedent = act_str
                self.no_of_subformula += 1

                dicts = []
                g = 0
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                    g += 1
                combined_succ = list(itertools.product(*dicts))

                first = True
                prod_left = None

                for cs in combined_succ:
                    f = 0
                    holdsToInt_succ = 'holdsToInt'
                    p_first = True
                    prod_left_part = None
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            space = cs[f].find(' ')
                            succ_state = cs[f][0:space]
                            holdsToInt_succ += '_' + succ_state
                            if p_first:
                                prod_left_part = RealVal(cs[f][space + 1:]).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(cs[f][space + 1:]).as_fraction()
                            f += 1

                        else:
                            holdsToInt_succ += '_' + str(0)
                            if p_first:
                                prod_left_part = RealVal(1).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(1).as_fraction()

                    holdsToInt_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(holdsToInt_succ)
                    prod_left_part *= self.listOfReals[self.list_of_reals.index(holdsToInt_succ)]

                    if first:
                        prod_left = prod_left_part
                        first = False
                    else:
                        prod_left += prod_left_part
                    self.no_of_subformula += 1

                implies_antecedent_and = self.listOfReals[self.list_of_reals.index(prob_phi)] == prod_left
                self.no_of_subformula += 1
                self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                self.no_of_subformula += 1
        return relevant_quantifier

    def encodeUnboundedUntilSemantics(self, hyperproperty, relevant_quantifier=[]):
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        rel_quant1 = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(rel_quant1, relevant_quantifier)
        phi2 = hyperproperty.children[0].children[1]
        index_of_phi2 = self.list_of_subformula.index(phi2)
        rel_quant2 = self.encodeSemantics(phi2)
        relevant_quantifier = extendWithoutDuplicates(rel_quant2, relevant_quantifier)
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    holds1 += "_" + str(r_state[ind])
                else:
                    holds1 += "_" + str(0)
            holds1 += "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            holds2 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    holds2 += "_" + str(r_state[ind])
                else:
                    holds2 += "_" + str(0)
            holds2 += "_" + str(index_of_phi2)
            self.addToVariableList(holds2)
            prob_phi = 'prob'
            for ind in r_state:
                prob_phi += "_" + str(ind)
            prob_phi += '_' + str(index_of_phi)
            self.addToVariableList(prob_phi)
            new_prob_const = self.listOfReals[self.list_of_reals.index(prob_phi)] >= float(0)
            first_implies = And(Implies(self.listOfBools[self.list_of_bools.index(holds2)],
                                        (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(1))),
                                Implies(And(Not(self.listOfBools[self.list_of_bools.index(holds1)]),
                                            Not(self.listOfBools[self.list_of_bools.index(holds2)])),
                                        (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(0))),
                                new_prob_const)
            self.no_of_subformula += 3

            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                name = 'a_' + str(r_state[relevant_quantifier[0] - 1])
                self.addToVariableList(name)
                act_str = self.listOfInts[self.list_of_ints.index(name)] == int(ca[0])
                if len(relevant_quantifier) > 1:
                    for l in range(2, len(relevant_quantifier) + 1):
                        name = 'a_' + str(relevant_quantifier[l - 1] - 1)
                        self.addToVariableList(name)
                        act_str = And(act_str, self.listOfInts[self.list_of_ints.index(name)] == int(ca[l - 1]))

                implies_precedent = And(self.listOfBools[self.list_of_bools.index(holds1)],
                                        Not(self.listOfBools[self.list_of_bools.index(holds2)]), act_str)
                self.no_of_subformula += 2

                dicts = []
                g = 0
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                    g += 1
                combined_succ = list(itertools.product(*dicts))

                first = True
                prod_left = None
                list_of_ors = []

                for cs in combined_succ:
                    f = 0
                    prob_succ = 'prob'
                    holds_succ = 'holds'
                    d_current = 'd'
                    d_succ = 'd'
                    p_first = True
                    prod_left_part = None
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            space = cs[f].find(' ')
                            succ_state = cs[f][0:space]
                            prob_succ += '_' + succ_state
                            holds_succ += '_' + succ_state
                            d_succ += '_' + succ_state
                            if p_first:
                                prod_left_part = RealVal(cs[f][space + 1:]).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(cs[f][space + 1:]).as_fraction()
                            f += 1

                        else:
                            prob_succ += '_' + str(0)
                            holds_succ += '_' + str(0)
                            d_succ += '_' + str(0)
                            if p_first:
                                prod_left_part = RealVal(1).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(1).as_fraction()
                        d_current += '_' + str(r_state[l - 1])

                    prob_succ += '_' + str(index_of_phi)
                    self.addToVariableList(prob_succ)
                    holds_succ += '_' + str(index_of_phi2)
                    self.addToVariableList(holds_succ)

                    d_current += '_' + str(index_of_phi2)
                    self.addToVariableList(d_current)
                    d_succ += '_' + str(index_of_phi2)
                    self.addToVariableList(d_succ)
                    prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]

                    if first:
                        prod_left = prod_left_part
                        first = False
                    else:
                        prod_left += prod_left_part
                    self.no_of_subformula += 1

                    list_of_ors.append(Or(self.listOfBools[self.list_of_bools.index(holds_succ)],
                                          self.listOfReals[self.list_of_reals.index(d_current)] > self.listOfReals[
                                              self.list_of_reals.index(d_succ)]))

                    self.no_of_subformula += 2

                implies_antecedent_and1 = self.listOfReals[self.list_of_reals.index(prob_phi)] == prod_left
                self.no_of_subformula += 1
                prod_right_or = Or([par for par in list_of_ors])
                self.no_of_subformula += 1
                implies_antecedent_and2 = Implies(self.listOfReals[self.list_of_reals.index(prob_phi)] > 0,
                                                  prod_right_or)
                self.no_of_subformula += 1
                implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
                self.no_of_subformula += 1
                self.solver.add(And(first_implies, Implies(implies_precedent, implies_antecedent)))
                self.no_of_subformula += 1

        return relevant_quantifier

    def encodeBoundedUntilSemantics(self, hyperproperty, relevant_quantifier=[]):
        k1 = int(hyperproperty.children[0].children[1].value)
        k2 = int(hyperproperty.children[0].children[2].value)

        index_of_phi = self.list_of_subformula.index(hyperproperty)
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        phi2 = hyperproperty.children[0].children[3]
        index_of_phi2 = self.list_of_subformula.index(phi2)

        if k2 == 0:
            rel_quant1 = self.encodeSemantics(phi1)
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant1)
            rel_quant2 = self.encodeSemantics(phi2)
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant2)
            combined_state_list = self.generateComposedStates(relevant_quantifier)

            for r_state in combined_state_list:
                name1 = 'prob'
                for ind in r_state:
                    name1 += "_" + str(ind)
                name1 += '_' + str(index_of_phi)
                self.addToVariableList(name1)
                name2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi2)
                self.addToVariableList(name2)

                eq1 = Implies(self.listOfBools[self.list_of_bools.index(name2)],
                              self.listOfReals[self.list_of_reals.index(name1)] == float(1))
                eq2 = Implies(Not(self.listOfBools[self.list_of_bools.index(name2)]),
                              self.listOfReals[self.list_of_reals.index(name1)] == float(0))
                self.no_of_subformula += 2
                self.solver.add(And(eq1, eq2))
                self.no_of_subformula += 1

        elif k1 == 0:
            left, k_1, k_2, right = hyperproperty.children[0].children
            par = copy.deepcopy(k_2)
            par.value = str(int(k_2.value) - 1)  # k2.value will have changed value but it won't show up in the formula
            # tree, hence it'll appear to be the same formula as formula_duplicate
            hyperproperty.children[0].children[2] = par  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2. Don't be confused!!
            self.list_of_subformula.append(hyperproperty)
            index_of_replaced = len(self.list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
            rel_quant = self.encodeBoundedUntilSemantics(hyperproperty)
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant)
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            rel_quant1 = int(str(hyperproperty.children[0].children[0].children[1].children[0])[1:])
            rel_quant2 = int(str(hyperproperty.children[0].children[3].children[1].children[0])[1:])

            for r_state in combined_state_list:
                holds1 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) == rel_quant1:
                        holds1 += "_" + str(r_state[ind])
                    else:
                        holds1 += "_" + str(0)
                holds1 += "_" + str(index_of_phi1)
                self.addToVariableList(holds1)
                holds2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) == rel_quant2:
                        holds2 += "_" + str(r_state[ind])
                    else:
                        holds2 += "_" + str(0)
                holds2 += "_" + str(index_of_phi2)
                self.addToVariableList(holds2)
                prob_phi = 'prob'
                for ind in r_state:
                    prob_phi += "_" + str(ind)
                prob_phi += '_' + str(index_of_phi)
                self.addToVariableList(prob_phi)

                new_prob_const = self.listOfReals[self.list_of_reals.index(prob_phi)] >= float(0)
                first_implies = And(Implies(self.listOfBools[self.list_of_bools.index(holds2)],
                                            (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(1))),
                                    Implies(And(Not(self.listOfBools[self.list_of_bools.index(holds1)]),
                                                Not(self.listOfBools[self.list_of_bools.index(holds2)])),
                                            (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(0))),
                                    new_prob_const)
                self.no_of_subformula += 3
                self.solver.add(first_implies)

                dicts = []
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts[r_state[l - 1]])
                combined_acts = list(itertools.product(*dicts))

                for ca in combined_acts:
                    name = 'a_' + str(r_state[relevant_quantifier[0] - 1])
                    self.addToVariableList(name)
                    act_str = self.listOfInts[self.list_of_ints.index(name)] == int(ca[0])
                    if len(relevant_quantifier) > 1:
                        for l in range(2, len(relevant_quantifier) + 1):
                            name = 'a_' + str(relevant_quantifier[l - 1] - 1)
                            self.addToVariableList(name)
                            act_str = And(act_str, self.listOfInts[self.list_of_ints.index(name)] == int(ca[l - 1]))

                    implies_precedent = And(self.listOfBools[self.list_of_bools.index(holds1)],
                                            Not(self.listOfBools[self.list_of_bools.index(holds2)]), act_str)
                    self.no_of_subformula += 2

                    dicts = []
                    g = 0
                    for l in relevant_quantifier:
                        dicts.append(self.model.dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                        g += 1
                    combined_succ = list(itertools.product(*dicts))

                    first = True
                    prod_left = None

                    for cs in combined_succ:
                        f = 0
                        prob_succ = 'prob'
                        p_first = True
                        prod_left_part = None
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in rel_quant:
                                space = cs[f].find(' ')
                                succ_state = cs[f][0:space]
                                prob_succ += '_' + succ_state
                                if p_first:
                                    prod_left_part = RealVal(cs[f][space + 1:]).as_fraction()
                                    p_first = False
                                else:
                                    prod_left_part *= RealVal(cs[f][space + 1:]).as_fraction()
                                f += 1

                            else:
                                prob_succ += '_' + str(0)
                                if p_first:
                                    prod_left_part = RealVal(1).as_fraction()
                                    p_first = False
                                else:
                                    prod_left_part *= RealVal(1).as_fraction()

                        prob_succ += '_' + str(index_of_replaced)
                        self.addToVariableList(prob_succ)
                        prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]

                        if first:
                            prod_left = prod_left_part
                            first = False
                        else:
                            prod_left += prod_left_part
                        self.no_of_subformula += 1

                    implies_antecedent_and = self.listOfReals[self.list_of_reals.index(prob_phi)] == prod_left
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                    self.no_of_subformula += 1

        elif k1 > 0:
            left, k_1, k_2, right = hyperproperty.children[0].children
            par1 = copy.deepcopy(k_1)
            par2 = copy.deepcopy(k_2)
            par1.value = str(int(k_1.value) - 1)
            par2.value = str(int(k_2.value) - 1)
            hyperproperty.children[0].children[1] = par1  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2 Don't be confused!!
            hyperproperty.children[0].children[2] = par2
            self.list_of_subformula.append(hyperproperty)
            index_of_replaced = len(self.list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
            rel_quant = self.encodeBoundedUntilSemantics(hyperproperty)
            relevant_quantifier = extendWithoutDuplicates(relevant_quantifier, rel_quant)
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            rel_quant1 = int(str(hyperproperty.children[0].children[0].children[1].children[0])[1:])
            rel_quant2 = int(str(hyperproperty.children[0].children[3].children[1].children[0])[1:])

            for r_state in combined_state_list:
                holds1 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) == rel_quant1:
                        holds1 += "_" + str(r_state[ind])
                    else:
                        holds1 += "_" + str(0)
                holds1 += "_" + str(index_of_phi1)
                self.addToVariableList(holds1)
                prob_phi = 'prob'
                for ind in r_state:
                    prob_phi += "_" + str(ind)
                prob_phi += '_' + str(index_of_phi)
                self.addToVariableList(prob_phi)

                first_implies = Implies(Not(self.listOfBools[self.list_of_bools.index(holds1)]),
                                        (self.listOfReals[self.list_of_reals.index(prob_phi)] == float(0)))
                self.no_of_subformula += 1
                self.solver.add(first_implies)

                dicts = []
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts[r_state[l - 1]])
                combined_acts = list(itertools.product(*dicts))

                for ca in combined_acts:
                    name = 'a_' + str(r_state[rel_quant[0] - 1])
                    self.addToVariableList(name)
                    act_str = self.listOfInts[self.list_of_ints.index(name)] == int(ca[0])
                    if len(rel_quant) > 1:
                        for l in range(2, len(rel_quant) + 1):
                            name = 'a_' + str(rel_quant[l - 1] - 1)
                            self.addToVariableList(name)
                            act_str = And(act_str, self.listOfInts[self.list_of_ints.index(name)] == int(ca[l - 1]))

                    implies_precedent = And(self.listOfBools[self.list_of_bools.index(holds1)], act_str)
                    self.no_of_subformula += 2

                    dicts = []
                    g = 0
                    for l in relevant_quantifier:
                        dicts.append(self.model.dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                        g += 1
                    combined_succ = list(itertools.product(*dicts))

                    first = True
                    prod_left = None

                    for cs in combined_succ:
                        f = 0
                        prob_succ = 'prob'
                        p_first = True
                        prod_left_part = None
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in rel_quant:
                                space = cs[f].find(' ')
                                succ_state = cs[f][0:space]
                                prob_succ += '_' + succ_state
                                if p_first:
                                    prod_left_part = RealVal(cs[f][space + 1:]).as_fraction()
                                    p_first = False
                                else:
                                    prod_left_part *= RealVal(cs[f][space + 1:]).as_fraction()
                                f += 1

                            else:
                                prob_succ += '_' + str(0)
                                if p_first:
                                    prod_left_part = RealVal(1).as_fraction()
                                    p_first = False
                                else:
                                    prod_left_part *= RealVal(1).as_fraction()

                        prob_succ += '_' + str(index_of_replaced)
                        self.addToVariableList(prob_succ)
                        prod_left_part *= self.listOfReals[self.list_of_reals.index(prob_succ)]

                        if first:
                            prod_left = prod_left_part
                            first = False
                        else:
                            prod_left += prod_left_part
                        self.no_of_subformula += 1

                    implies_antecedent_and = self.listOfReals[self.list_of_reals.index(prob_phi)] == prod_left
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                    self.no_of_subformula += 1
        return relevant_quantifier

    def encodeFutureSemantics(self, hyperproperty, relevant_quantifier=[]):
        pass

    def encodeGlobalSemantics(self, hyperproperty, relevant_quantifier=[]):
        pass

    def encodeRewNextSemantics(self, hyperproperty, prev_relevant_quantifier=[]):
        reward_model = self.model.parsed_model.reward_models.get(
            list(self.model.parsed_model.reward_models.keys())[0]).state_rewards
        rel_quant = int(hyperproperty.children[0].value[1])
        # prev_relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, [rel_quant])
        child = hyperproperty.children[1]
        # phi1 = hyperproperty.children[1].children[0]
        prob_formula = Tree('probability', [child])
        index_of_phi1 = self.list_of_subformula.index(child)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        index_of_phi_prob = self.list_of_subformula.index(prob_formula)
        relevant_quantifier = self.encodeNextSemantics(prob_formula, [rel_quant])
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        # holdsToInt has type real to avoid added complexity of multiplying integer to real values
        for r_state in combined_state_list:
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            prob_phi = 'prob' + str_r_state + "_" + str(index_of_phi_prob)
            self.addToVariableList(prob_phi)
            rew_phi = 'rew' + str_r_state + "_" + str(index_of_phi)
            self.addToVariableList(rew_phi)
            first_implies = Implies(Not(self.listOfReals[self.list_of_reals.index(prob_phi)] == float(1)),
                                    self.listOfReals[self.list_of_reals.index(rew_phi)] == float(-9999))
            self.no_of_subformula += 3
            self.solver.add(first_implies)
            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                name = 'a_' + str(r_state[relevant_quantifier[0] - 1])
                self.addToVariableList(name)
                act_str = self.listOfInts[self.list_of_ints.index(name)] == int(ca[0])
                if len(relevant_quantifier) > 1:
                    for l in range(2, len(relevant_quantifier) + 1):
                        name = 'a_' + str(relevant_quantifier[l - 1] - 1)
                        self.addToVariableList(name)
                        act_str = And(act_str, self.listOfInts[self.list_of_ints.index(name)] == int(ca[l - 1]))

                implies_precedent = And(self.listOfReals[self.list_of_reals.index(prob_phi)] == float(1), act_str)
                self.no_of_subformula += 1

                dicts = []
                g = 0
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                    g += 1
                combined_succ = list(itertools.product(*dicts))
                first = True
                prod_left = None
                for cs in combined_succ:
                    f = 0
                    rew_succ = 'rew'
                    p_first = True
                    prod_left_part = None
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            space = cs[f].find(' ')
                            succ_state = cs[f][0:space]
                            rew_succ += '_' + succ_state
                            if p_first:
                                prod_left_part = RealVal(cs[f][space + 1:]).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(cs[f][space + 1:]).as_fraction()
                            f += 1
                        else:
                            rew_succ += '_' + str(0)
                            if p_first:
                                prod_left_part = RealVal(1).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(1).as_fraction()

                    rew_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(rew_succ)
                    prod_left_part *= self.listOfReals[self.list_of_reals.index(rew_succ)]

                    if first:
                        prod_left = prod_left_part
                        first = False
                    else:
                        prod_left += prod_left_part
                    self.no_of_subformula += 1

                implies_antecedent_and = self.listOfReals[self.list_of_reals.index(rew_phi)] == (
                        float(reward_model[r_state[rel_quant - 1]]) + prod_left)
                self.no_of_subformula += 1
                self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                self.no_of_subformula += 1
        return relevant_quantifier

    def encodeRewUnboundedUntilSemantics(self, hyperproperty, relevant_quantifier=[]):
        pass

    def encodeRewBoundedUntilSemantics(self, hyperproperty, relevant_quantifier=[]):
        pass

    def encodeRewFutureSemantics(self, hyperproperty, relevant_quantifier=[]):
        pass

    def encodeRewGlobalSemantics(self, hyperproperty, relevant_quantifier=[]):
        pass
