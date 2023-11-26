import copy
import itertools

from lark import Tree
from pysmt.shortcuts import Symbol, Not, And, Or, Xor


def extendWithoutDuplicates(list1, list2):
    result = []
    if list1 is not None:
        result.extend(list1)
    if list2 is not None:
        result.extend(x for x in list2 if x not in result)
    return result


class SemanticsEncoder:
    def __init__(self, models, solver, list_of_subformula, dictOfBools, dictOfReals,
                 hyperproperty):
        self.list_of_model = models
        self.solver = solver
        self.list_of_subformula = list_of_subformula
        self.dictOfReals = dictOfReals
        self.dictOfBools = dictOfBools
        self.hyperproperty = hyperproperty

    def encodeSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        relevant_quantifier = []
        if len(prev_relevant_quantifier) > 0:
            relevant_quantifier.extend(prev_relevant_quantifier)

        if hyperproperty.data == 'true':
            name = "holds"
            for _ in range(len(self.hyperproperty.state_quantifiers)):
                name += "_" + str(0)
            name += '_' + str(self.list_of_subformula.index(hyperproperty))
            self.dictOfBools[name] = Symbol(name)
            self.solver.add_assertion(self.dictOfBools[name])
            return relevant_quantifier

        elif hyperproperty.data == 'atomic_proposition':
            # assuming we have only one quantifier associated with an AP
            ap_name = hyperproperty.children[0].children[0].value  # gets the name of the proposition
            proposition_relevant_quantifier = hyperproperty.children[1].children[
                0].value  # gets the relevant quantifier
            labeling = self.list_of_model[self.hyperproperty.quantifierDictionary["schedq"].index(
                self.hyperproperty.quantifierDictionary["stateq"][
                    proposition_relevant_quantifier])].parsed_model.labeling
            if proposition_relevant_quantifier not in relevant_quantifier:
                relevant_quantifier.append(proposition_relevant_quantifier)
            and_for_yes = []
            and_for_no = []
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            list_of_state_with_ap = labeling.get_states(ap_name)
            combined_state_list = self.generateComposedStates(relevant_quantifier)

            for r_state in combined_state_list:
                name = 'holds'
                for ind in r_state:
                    name += "_" + str(ind)
                name += '_' + str(index_of_phi)
                self.dictOfBools[name] = Symbol(name)
                if list_of_state_with_ap.get(r_state[list(self.hyperproperty.quantifierDictionary["stateq"].keys()).index(proposition_relevant_quantifier)]):
                    and_for_yes.append(self.dictOfBools[name])
                else:
                    and_for_no.append(Not(self.dictOfBools[name]))
            self.solver.add_assertion(And(And(and_for_yes), And(and_for_no)))
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
                self.dictOfBools[name1] = Symbol(name1)
                name2 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant1:
                        name2 += "_" + str(r_state[ind])
                    else:
                        name2 += "_" + str(0)
                name2 += '_' + str(index_of_phi1)
                self.dictOfBools[name2] = Symbol(name2)
                name3 = 'holds'
                for ind in range(0, len(r_state)):
                    if (ind + 1) in rel_quant2:
                        name3 += "_" + str(r_state[ind])
                    else:
                        name3 += "_" + str(0)
                name3 += '_' + str(index_of_phi2)
                self.dictOfBools[name3] = Symbol(name3)
                first_and = And(self.dictOfBools[name1],
                                self.dictOfBools[name2],
                                self.dictOfBools[name3])
                second_and = And(Not(self.dictOfBools[name1]),
                                 Or(Not(self.dictOfBools[name2]), Not(self.dictOfBools[name3])))
                self.solver.add_assertion(Or(first_and, second_and))
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
                first_and = And(self.dictOfBools[name1],
                                Or(self.dictOfBools[name2], self.dictOfBools[name3]))
                self.no_of_subformula += 1
                second_and = And(Not(self.dictOfBools[name1]),
                                 And(Not(self.dictOfBools[name2]), Not(self.dictOfBools[name3])))
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
                first_and = And(self.dictOfBools[name1],
                                Or(Not(self.dictOfBools[name2]), self.dictOfBools[name3]))
                self.no_of_subformula += 1
                second_and = And(Not(self.dictOfBools[name1]),
                                 And(self.dictOfBools[name2], Not(self.dictOfBools[name3])))
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
                first_and = And(self.dictOfBools[name1],
                                Or(And(self.dictOfBools[name2], self.dictOfBools[name3]),
                                   And(Not(self.dictOfBools[name2]), Not(self.dictOfBools[name3]))))
                self.no_of_subformula += 1
                second_and = And(Not(self.dictOfBools[name1]),
                                 Or(And(Not(self.dictOfBools[name2]), self.dictOfBools[name3]),
                                    And(self.dictOfBools[name2], Not(self.dictOfBools[name3]))))
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
                name2 = 'holds'
                for ind in r_state:
                    name1 += "_" + str(ind)
                    name2 += "_" + str(ind)
                name1 += '_' + str(index_of_phi)
                name2 += '_' + str(index_of_phi1)
                self.dictOfBools[name1] = Symbol(name1)
                self.dictOfBools[name2] = Symbol(name2)
                self.solver.add_assertion(Xor(self.dictOfBools[name1], self.dictOfBools[name2]))
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
                pass
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
                pass
                # relevant_quantifier = extendWithoutDuplicates(relevant_quantifier,
                #                                              self.encodeRewGlobalSemantics(hyperproperty,
                #                                                                            relevant_quantifier))
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] < self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] >= self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] == self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] != self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] > self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] <= self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] >= self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] < self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] <= self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] > self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] < self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] >= self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] == self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] != self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] > self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] <= self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] >= self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] < self.dictOfReals[name3])
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
                and_eq = And(self.dictOfBools[name1],
                             self.dictOfReals[name2] <= self.dictOfReals[name3])
                self.no_of_subformula += 1
                and_not_eq = And(Not(self.dictOfBools[name1]),
                                 self.dictOfReals[name2] > self.dictOfReals[name3])
                self.no_of_subformula += 1
                self.solver.add(Or(and_eq, and_not_eq))
                self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'constant_probability':
            constant = RealVal(hyperproperty.children[0].value).as_fraction().limit_denominator(10000)
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            name = "prob"
            r_state = [0 for _ in range(self.no_of_state_quantifier)]
            for ind in r_state:
                name += "_" + str(ind)
            name += '_' + str(index_of_phi)
            self.addToVariableList(name)
            self.solver.add(self.dictOfReals[name] == constant)
            self.no_of_subformula += 1
            return relevant_quantifier
        elif hyperproperty.data == 'constant_reward':
            constant = hyperproperty.children[0].value
            index_of_phi = self.list_of_subformula.index(hyperproperty)
            name = "rew"
            r_state = [0 for _ in range(self.no_of_state_quantifier)]
            for ind in r_state:
                name += "_" + str(ind)
            name += '_' + str(index_of_phi)
            self.addToVariableList(name)
            self.solver.add(self.dictOfReals[name] == constant)
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
                    self.solver.add(self.dictOfReals[name1] == (self.dictOfReals[name2] + self.dictOfReals[name3]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'subtract_probability':
                    self.solver.add(self.dictOfReals[name1] == (self.dictOfReals[name2] - self.dictOfReals[name3]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'multiply_probability':
                    self.solver.add(self.dictOfReals[name1] == (self.dictOfReals[name2] * self.dictOfReals[name3]))
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
                    self.solver.add(self.dictOfReals[name1] == (self.dictOfReals[name2] + self.dictOfReals[name3]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'subtract_reward':
                    self.solver.add(self.dictOfReals[name1] == (self.dictOfReals[name2] - self.dictOfReals[name3]))
                    self.no_of_subformula += 2
                elif hyperproperty.data == 'multiply_reward':
                    self.solver.add(self.dictOfReals[name1] == (self.dictOfReals[name2] * self.dictOfReals[name3]))
                    self.no_of_subformula += 2
                else:
                    print("Unexpected operator. Exiting")
                    return -1
            return relevant_quantifier
        else:
            self.encodeSemantics(hyperproperty.children[0])

    """
   def addToVariableList(self, name):
        if name[0] == 'h' and not name.startswith('holdsToInt') and name not in self.dictOfBools.keys():
            self.dictOfBools[name] = Symbol(name)
        elif name[0] in ['p', 'd', 'r'] or name.startswith('holdsToInt') and name not in self.dictOfReals.keys():
            self.dictOfReals[name] = Symbol(name, REAL)
        elif name[0] == 'a' and name not in self.dictOfInts.keys():
            self.dictOfInts[name] = Symbol(name, INT)
    """

    def generateComposedStates(self, list_of_relevant_quantifier):
        """
        Generates combination of states based on relevant quantifiers
        :param list_of_relevant_quantifier: ranges from value 1 - (no. of quantifiers)
        :return: list of composed states.
        """
        stored_list = []
        for quant in self.hyperproperty.quantifierDictionary["stateq"].keys():
            if quant in list_of_relevant_quantifier:
                stored_list.append(self.list_of_model[
                                       self.hyperproperty.quantifierDictionary["schedq"].index(
                                           self.hyperproperty.quantifierDictionary["stateq"][
                                               quant])].parsed_model.nr_states)
            else:
                stored_list.append(1)
        return list(itertools.product(*list(range(li) for li in stored_list)))

    def encodeNextSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
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
                And(self.dictOfReals[holdsToInt1] == float(1), self.dictOfBools[holds1]),
                And(self.dictOfReals[holdsToInt1] == float(0), Not(self.dictOfBools[holds1])))
            self.no_of_subformula += 3
            self.solver.add(first_and)
            dicts_act = []
            for l in relevant_quantifier:
                dicts_act.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts_act))

            for ca in combined_acts:
                act_str = []
                for l in range(len(relevant_quantifier)):
                    name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                    self.addToVariableList(name)
                    act_str.append(self.dictOfInts[name] == int(ca[l]))
                implies_precedent = And(act_str)
                self.no_of_subformula += 1

                combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                sum_left = RealVal(0).as_fraction()

                for cs in combined_succ:
                    holdsToInt_succ = 'holdsToInt'
                    prod_left_part = RealVal(1).as_fraction()
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            succ_state = cs[relevant_quantifier.index(l)][0]
                            holdsToInt_succ += '_' + succ_state
                            prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                        else:
                            holdsToInt_succ += '_' + str(0)

                    holdsToInt_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(holdsToInt_succ)
                    prod_left_part *= self.dictOfReals[holdsToInt_succ]

                    sum_left += prod_left_part
                    self.no_of_subformula += 1

                implies_antecedent_and = self.dictOfReals[prob_phi] == sum_left
                self.no_of_subformula += 1
                self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                self.no_of_subformula += 1
        return relevant_quantifier

    def genSuccessors(self, r_state, ca, relevant_quantifier):
        dicts = []
        for l in range(len(relevant_quantifier)):
            succ = (self.model.dict_of_acts_tran[str(r_state[relevant_quantifier[l] - 1]) + " " + str(ca[l])])
            list_of_all_succ = []
            for s in succ:
                space = s.find(' ')
                succ_state = int(s[0:space])
                list_of_all_succ.append([str(succ_state), s[space + 1:]])
            dicts.append(list_of_all_succ)
        return list(itertools.product(*dicts))

    def encodeUnboundedUntilSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        rel_quant1 = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(rel_quant1, prev_relevant_quantifier)
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
            new_prob_const = self.dictOfReals[prob_phi] >= float(0)
            first_implies = And(Implies(self.dictOfBools[holds2],
                                        (self.dictOfReals[prob_phi] == float(1))),
                                Implies(And(Not(self.dictOfBools[holds1]),
                                            Not(self.dictOfBools[holds2])),
                                        (self.dictOfReals[prob_phi] == float(0))),
                                new_prob_const)
            self.no_of_subformula += 3

            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                act_str = []
                for l in range(len(relevant_quantifier)):
                    name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                    self.addToVariableList(name)
                    act_str.append(self.dictOfInts[name] == int(ca[l]))
                implies_precedent = And(self.dictOfBools[holds1],
                                        Not(self.dictOfBools[holds2]), And(act_str))
                self.no_of_subformula += 2

                combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                sum_left = RealVal(0).as_fraction()
                list_of_ors = []

                for cs in combined_succ:
                    prob_succ = 'prob'
                    holds_succ = 'holds'
                    d_current = 'd'
                    d_succ = 'd'
                    prod_left_part = RealVal(1).as_fraction()
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            succ_state = cs[relevant_quantifier.index(l)][0]
                            prob_succ += '_' + succ_state
                            holds_succ += '_' + succ_state
                            d_succ += '_' + succ_state
                            prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                        else:
                            prob_succ += '_' + str(0)
                            holds_succ += '_' + str(0)
                            d_succ += '_' + str(0)
                        d_current += '_' + str(r_state[l - 1])

                    prob_succ += '_' + str(index_of_phi)
                    self.addToVariableList(prob_succ)
                    holds_succ += '_' + str(index_of_phi2)
                    self.addToVariableList(holds_succ)

                    d_current += '_' + str(index_of_phi2)
                    self.addToVariableList(d_current)
                    d_succ += '_' + str(index_of_phi2)
                    self.addToVariableList(d_succ)
                    prod_left_part *= self.dictOfReals[prob_succ]

                    sum_left = prod_left_part
                    self.no_of_subformula += 1

                    list_of_ors.append(Or(self.dictOfBools[holds_succ],
                                          self.dictOfReals[d_current] > self.dictOfReals[d_succ]))

                    self.no_of_subformula += 2

                implies_antecedent_and1 = self.dictOfReals[prob_phi] == sum_left
                self.no_of_subformula += 1
                prod_right_or = Or(list_of_ors)
                self.no_of_subformula += 1
                implies_antecedent_and2 = Implies(self.dictOfReals[prob_phi] > 0,
                                                  prod_right_or)
                self.no_of_subformula += 1
                implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
                self.no_of_subformula += 1
                self.solver.add(And(first_implies, Implies(implies_precedent, implies_antecedent)))
                self.no_of_subformula += 1

        return relevant_quantifier

    def encodeBoundedUntilSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            relevant_quantifier = []
        k1 = int(hyperproperty.children[0].children[1].value)
        k2 = int(hyperproperty.children[0].children[2].value)
        # TODO: change to return rel_quant1, rel_quant2 in both the other two cases.

        index_of_phi = self.list_of_subformula.index(hyperproperty)
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        phi2 = hyperproperty.children[0].children[3]
        index_of_phi2 = self.list_of_subformula.index(phi2)

        if k2 == 0:
            rel_quant1 = self.encodeSemantics(phi1)
            relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, rel_quant1)
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

                eq1 = Implies(self.dictOfBools[name2],
                              self.dictOfReals[name1] == float(1))
                eq2 = Implies(Not(self.dictOfBools[name2]),
                              self.dictOfReals[name1] == float(0))
                self.no_of_subformula += 2
                self.solver.add(And(eq1, eq2))
                self.no_of_subformula += 1

        elif k1 == 0:
            left, k_1, k_2, right = hyperproperty.children[0].children
            par = copy.deepcopy(k_2)
            par.value = str(int(k_2.value) - 1)  # k2.value will have changed value but it won't show up in the formula
            # tree, hence it'll appear to be the same formula as formula_duplicate
            hyperproperty.children[0].children[
                2] = par  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2. Don't be confused!!
            self.list_of_subformula.append(hyperproperty)
            index_of_replaced = len(
                self.list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
            rel_quant = self.encodeBoundedUntilSemantics(hyperproperty)
            relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, rel_quant)
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

                new_prob_const = self.dictOfReals[prob_phi] >= float(0)
                first_implies = And(Implies(self.dictOfBools[holds2], (self.dictOfReals[prob_phi] == float(1))),
                                    Implies(And(Not(self.dictOfBools[holds1]), Not(self.dictOfBools[holds2])),
                                            (self.dictOfReals[prob_phi] == float(0))),
                                    new_prob_const)
                self.no_of_subformula += 3
                self.solver.add(first_implies)

                dicts = []
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts[r_state[l - 1]])
                combined_acts = list(itertools.product(*dicts))

                for ca in combined_acts:
                    act_str = []
                    for l in range(len(relevant_quantifier)):
                        name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                        self.addToVariableList(name)
                        act_str.append(self.dictOfInts[name] == int(ca[l]))
                    implies_precedent = And(self.dictOfBools[holds1],
                                            Not(self.dictOfBools[holds2]), And(act_str))
                    self.no_of_subformula += 2

                    combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                    sum_left = RealVal(0).as_fraction()

                    for cs in combined_succ:
                        prob_succ = 'prob'
                        prod_left_part = RealVal(1).as_fraction()
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in relevant_quantifier:
                                succ_state = cs[relevant_quantifier.index(l)][0]
                                prob_succ += '_' + succ_state
                                prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                            else:
                                prob_succ += '_' + str(0)

                        prob_succ += '_' + str(index_of_replaced)
                        self.addToVariableList(prob_succ)
                        prod_left_part *= self.dictOfReals[prob_succ]

                        sum_left += prod_left_part
                        self.no_of_subformula += 1

                    implies_antecedent_and = self.dictOfReals[prob_phi] == sum_left
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                    self.no_of_subformula += 1

        elif k1 > 0:
            left, k_1, k_2, right = hyperproperty.children[0].children
            par1 = copy.deepcopy(k_1)
            par2 = copy.deepcopy(k_2)
            par1.value = str(int(k_1.value) - 1)
            par2.value = str(int(k_2.value) - 1)
            hyperproperty.children[0].children[
                1] = par1  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2 Don't be confused!!
            hyperproperty.children[0].children[2] = par2
            self.list_of_subformula.append(hyperproperty)
            index_of_replaced = len(
                self.list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
            rel_quant = self.encodeBoundedUntilSemantics(hyperproperty)
            relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, rel_quant)
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            rel_quant1 = int(str(hyperproperty.children[0].children[0].children[1].children[0])[1:])

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

                first_implies = Implies(Not(self.dictOfBools[holds1]),
                                        (self.dictOfReals[prob_phi] == float(0)))
                self.no_of_subformula += 1
                self.solver.add(first_implies)

                dicts = []
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts[r_state[l - 1]])
                combined_acts = list(itertools.product(*dicts))

                for ca in combined_acts:
                    act_str = []
                    for l in range(len(relevant_quantifier)):
                        name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                        self.addToVariableList(name)
                        act_str.append(self.dictOfInts[name] == int(ca[l]))
                    implies_precedent = And(self.dictOfBools[holds1],
                                            And(act_str))
                    self.no_of_subformula += 2

                    combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                    sum_left = RealVal(0).as_fraction()

                    for cs in combined_succ:
                        prob_succ = 'prob'
                        prod_left_part = RealVal(1).as_fraction()
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in relevant_quantifier:
                                succ_state = cs[relevant_quantifier.index(l)][0]
                                prob_succ += '_' + succ_state
                                prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                            else:
                                prob_succ += '_' + str(0)

                        prob_succ += '_' + str(index_of_replaced)
                        self.addToVariableList(prob_succ)
                        prod_left_part *= self.dictOfReals[prob_succ]

                        prod_left_part *= self.dictOfReals[prob_succ]
                        sum_left += prod_left_part
                        self.no_of_subformula += 1

                    implies_antecedent_and = self.dictOfReals[prob_phi] == sum_left
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                    self.no_of_subformula += 1
        return relevant_quantifier

    def encodeFutureSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        rel_quant = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, rel_quant)
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            prob_phi = 'prob'
            prob_phi += str_r_state + '_' + str(index_of_phi)
            self.addToVariableList(prob_phi)
            new_prob_const_0 = self.dictOfReals[prob_phi] >= float(0)
            first_implies = And(Implies(self.dictOfBools[holds1],
                                        (self.dictOfReals[prob_phi] == float(1))),
                                new_prob_const_0)
            self.no_of_subformula += 1

            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                act_str = []
                for l in range(len(relevant_quantifier)):
                    name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                    self.addToVariableList(name)
                    act_str.append(self.dictOfInts[name] == int(ca[l]))
                implies_precedent = And(Not(self.dictOfBools[holds1]), And(act_str))
                self.no_of_subformula += 2

                combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                sum_left = RealVal(0).as_fraction()
                list_of_ors = []

                for cs in combined_succ:
                    prob_succ = 'prob'
                    holds_succ = 'holds'
                    d_current = 'd'
                    d_succ = 'd'
                    prod_left_part = RealVal(1).as_fraction()
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            succ_state = cs[relevant_quantifier.index(l)][0]
                            prob_succ += '_' + succ_state
                            holds_succ += '_' + succ_state
                            d_succ += '_' + succ_state
                            prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                        else:
                            prob_succ += '_' + str(0)
                            holds_succ += '_' + str(0)
                            d_succ += '_' + str(0)
                        d_current += '_' + str(r_state[l - 1])

                    prob_succ += '_' + str(index_of_phi)
                    self.addToVariableList(prob_succ)
                    holds_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(holds_succ)
                    d_current += '_' + str(index_of_phi1)
                    self.addToVariableList(d_current)
                    d_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(d_succ)
                    prod_left_part *= self.dictOfReals[prob_succ]

                    sum_left += prod_left_part
                    self.no_of_subformula += 1
                    list_of_ors.append(Or(self.dictOfBools[holds_succ],
                                          self.dictOfReals[d_current] > self.dictOfReals[d_succ]))

                    self.no_of_subformula += 2

                implies_antecedent_and1 = self.dictOfReals[prob_phi] == sum_left
                self.no_of_subformula += 1
                prod_right_or = Or(list_of_ors)
                self.no_of_subformula += 1
                implies_antecedent_and2 = Implies(self.dictOfReals[prob_phi] > 0, prod_right_or)
                self.no_of_subformula += 1
                implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
                self.no_of_subformula += 1
                self.solver.add(And(first_implies, Implies(implies_precedent, implies_antecedent)))
                self.no_of_subformula += 1
        return relevant_quantifier

    def encodeGlobalSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        rel_quant = self.encodeSemantics(phi1)
        relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, rel_quant)
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            prob_phi = 'prob'
            prob_phi += str_r_state + '_' + str(index_of_phi)
            self.addToVariableList(prob_phi)
            new_prob_const_0 = self.dictOfReals[prob_phi] >= float(0)
            new_prob_const_1 = self.dictOfReals[prob_phi] <= float(1)
            first_implies = And(Implies(Not(self.dictOfBools[holds1]),
                                        (self.dictOfReals[prob_phi] == float(0))),
                                new_prob_const_0, new_prob_const_1)
            self.no_of_subformula += 1

            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                act_str = []
                for l in range(len(relevant_quantifier)):
                    name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                    self.addToVariableList(name)
                    act_str.append(self.dictOfInts[name] == int(ca[l]))
                implies_precedent = And(self.dictOfBools[holds1],
                                        And(act_str))
                self.no_of_subformula += 2

                combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                sum_left = RealVal(0).as_fraction()
                list_of_ors = []

                for cs in combined_succ:
                    prob_succ = 'prob'
                    holds_succ = 'holds'
                    d_current = 'd'
                    d_succ = 'd'
                    prod_left_part = RealVal(1).as_fraction()
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            succ_state = cs[relevant_quantifier.index(l)][0]
                            prob_succ += '_' + succ_state
                            holds_succ += '_' + succ_state
                            d_succ += '_' + succ_state
                            prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                        else:
                            prob_succ += '_' + str(0)
                            holds_succ += '_' + str(0)
                            d_succ += '_' + str(0)
                        d_current += '_' + str(r_state[l - 1])

                    prob_succ += '_' + str(index_of_phi)
                    self.addToVariableList(prob_succ)
                    holds_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(holds_succ)
                    d_current += '_' + str(index_of_phi1)
                    self.addToVariableList(d_current)
                    d_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(d_succ)
                    prod_left_part *= self.dictOfReals[prob_succ]

                    sum_left += prod_left_part
                    self.no_of_subformula += 1

                    list_of_ors.append(Or(Not(self.dictOfBools[holds_succ]),
                                          self.dictOfReals[d_current] > self.dictOfReals[d_succ]))

                    self.no_of_subformula += 2

                implies_antecedent_and1 = self.dictOfReals[prob_phi] == sum_left
                self.no_of_subformula += 1
                prod_right_or = Or(list_of_ors)
                self.no_of_subformula += 1
                implies_antecedent_and2 = Implies(self.dictOfReals[prob_phi] < 1,
                                                  prod_right_or)
                self.no_of_subformula += 1
                implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
                self.no_of_subformula += 1
                self.solver.add(And(first_implies, Implies(implies_precedent, implies_antecedent)))
                self.no_of_subformula += 1
        return relevant_quantifier

    def encodeRewNextSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        reward_model = self.model.parsed_model.reward_models.get(
            list(self.model.parsed_model.reward_models.keys())[0]).state_rewards
        rel_quant = int(hyperproperty.children[0].value[1])
        relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, [rel_quant])
        child = hyperproperty.children[1]
        # phi1 = hyperproperty.children[1].children[0]
        prob_formula = Tree('probability', [child])
        index_of_phi1 = self.list_of_subformula.index(child)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        index_of_phi_prob = self.list_of_subformula.index(prob_formula)
        relevant_quantifier = self.encodeNextSemantics(prob_formula, relevant_quantifier)
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        for r_state in combined_state_list:
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            prob_phi = 'prob' + str_r_state + "_" + str(index_of_phi_prob)
            self.addToVariableList(prob_phi)
            rew_phi = 'rew' + str_r_state + "_" + str(index_of_phi)
            self.addToVariableList(rew_phi)
            first_implies = Implies(Not(self.dictOfReals[prob_phi] == float(1)),
                                    self.dictOfReals[rew_phi] == float(-9999999))
            self.no_of_subformula += 3
            self.solver.add(first_implies)
            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                act_str = []
                for l in range(len(relevant_quantifier)):
                    name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                    self.addToVariableList(name)
                    act_str.append(self.dictOfInts[name] == int(ca[l]))
                implies_precedent = And(self.dictOfReals[prob_phi] == float(1), act_str)
                self.no_of_subformula += 1

                combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                sum_left = RealVal(0).as_fraction()

                for cs in combined_succ:
                    rew_succ = 'rew'
                    prod_left_part = RealVal(1).as_fraction()
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            succ_state = cs[relevant_quantifier.index(l)][0]
                            rew_succ += '_' + succ_state
                            prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                        else:
                            rew_succ += '_' + str(0)

                    rew_succ += '_' + str(index_of_phi1)
                    self.addToVariableList(rew_succ)
                    prod_left_part *= self.dictOfReals[rew_succ]
                    sum_left += prod_left_part
                    self.no_of_subformula += 1

                implies_antecedent_and = self.dictOfReals[rew_phi] == (
                        float(reward_model[r_state[rel_quant - 1]]) + sum_left)
                self.no_of_subformula += 1
                self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                self.no_of_subformula += 1
        return relevant_quantifier

    def encodeRewUnboundedUntilSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        reward_model = self.model.parsed_model.reward_models.get(
            list(self.model.parsed_model.reward_models.keys())[0]).state_rewards
        rel_quant = int(hyperproperty.children[0].value[1])
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        child = hyperproperty.children[1]
        prob_formula = Tree('probability', [child])
        index_of_phi_prob = self.list_of_subformula.index(prob_formula)
        phi2 = hyperproperty.children[1].children[1]
        index_of_phi2 = self.list_of_subformula.index(phi2)
        rel_quant1 = self.encodeUnboundedUntilSemantics(prob_formula, [rel_quant])
        rel_quant2 = self.encodeSemantics(phi2)
        relevant_quantifier = extendWithoutDuplicates(
            extendWithoutDuplicates(extendWithoutDuplicates(rel_quant2, [rel_quant]),
                                    rel_quant1), prev_relevant_quantifier)
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        for r_state in combined_state_list:
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
            prob_phi += '_' + str(index_of_phi_prob)
            self.addToVariableList(prob_phi)
            rew_phi = 'rew'
            for ind in r_state:
                rew_phi += "_" + str(ind)
            rew_phi += '_' + str(index_of_phi)
            self.addToVariableList(rew_phi)
            first_implies = And(Implies(self.dictOfBools[holds2],
                                        (self.dictOfReals[rew_phi] == float(
                                            reward_model.get_state_reward(r_state[rel_quant - 1])))),
                                Implies(Not(self.dictOfReals[prob_phi] == float(1)),
                                        self.dictOfReals[rew_phi] == float(-999999)))
            self.no_of_subformula += 3

            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                act_str = []
                for l in range(len(relevant_quantifier)):
                    name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                    self.addToVariableList(name)
                    act_str.append(self.dictOfInts[name] == int(ca[l]))
                implies_precedent = And(self.dictOfReals[prob_phi] == float(1),
                                        Not(self.dictOfBools[holds2]), And(act_str))
                self.no_of_subformula += 2

                combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                sum_left = RealVal(0).as_fraction()

                for cs in combined_succ:
                    rew_succ = 'rew'
                    prod_left_part = RealVal(1).as_fraction()
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                        else:
                            rew_succ += '_' + str(0)

                    rew_succ += '_' + str(index_of_phi)
                    self.addToVariableList(rew_succ)
                    prod_left_part *= self.dictOfReals[rew_succ]

                    sum_left = prod_left_part
                    self.no_of_subformula += 1

                implies_antecedent = self.dictOfReals[rew_phi] == (float(reward_model.get_state_reward(r_state[
                                                                                                           rel_quant - 1])) + sum_left)
                self.no_of_subformula += 1
                self.solver.add(And(first_implies, Implies(implies_precedent, implies_antecedent)))
                self.no_of_subformula += 1

        return relevant_quantifier

    def encodeRewBoundedUntilSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        k1 = int(hyperproperty.children[0].children[1].value)
        k2 = int(hyperproperty.children[0].children[2].value)
        # TODO: change to return rel_quant1, rel_quant2 in both the other two cases.
        reward_model = self.model.parsed_model.reward_models.get(
            list(self.model.parsed_model.reward_models.keys())[0]).state_rewards
        rel_quant = int(hyperproperty.children[0].value[1])
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        child = hyperproperty.children[1]
        prob_formula = Tree('probability', [child])
        index_of_phi_prob = self.list_of_subformula.index(prob_formula)
        rel_quant1 = self.encodeBoundedUntilSemantics(prob_formula, [rel_quant])
        phi1 = hyperproperty.children[0].children[0]
        index_of_phi1 = self.list_of_subformula.index(phi1)
        phi2 = hyperproperty.children[0].children[3]
        index_of_phi2 = self.list_of_subformula.index(phi2)

        if k2 == 0:
            rel_quant2 = self.encodeSemantics(phi2)
            relevant_quantifier = extendWithoutDuplicates(extendWithoutDuplicates([rel_quant], rel_quant2),
                                                          prev_relevant_quantifier)
            combined_state_list = self.generateComposedStates(relevant_quantifier)

            for r_state in combined_state_list:
                name1 = 'rew'
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
                # TODO: fix the relevant quantifier for get_state_reward
                eq1 = Implies(self.dictOfBools[name2],
                              self.dictOfReals[name1] == float(reward_model.get_state_reward(r_state[rel_quant - 1])))
                eq2 = Implies(Not(self.dictOfBools[name2]), self.dictOfReals[name1] == float(-9999))
                self.no_of_subformula += 2
                self.solver.add(And(eq1, eq2))
                self.no_of_subformula += 1

        elif k1 == 0:
            left, k_1, k_2, right = hyperproperty.children[0].children
            par = copy.deepcopy(k_2)
            par.value = str(int(k_2.value) - 1)  # k2.value will have changed value but it won't show up in the formula
            # tree, hence it'll appear to be the same formula as formula_duplicate
            hyperproperty.children[1].children[
                2] = par  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2. Don't be confused!!
            self.list_of_subformula.append(hyperproperty)
            index_of_replaced = len(
                self.list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
            relevant_quantifier = self.encodeRewBoundedUntilSemantics(hyperproperty, [rel_quant])
            relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, relevant_quantifier)
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            rel_quant1 = int(str(hyperproperty.children[0].children[0].children[1].children[0])[1:])
            rel_quant2 = int(str(hyperproperty.children[0].children[3].children[1].children[0])[1:])

            for r_state in combined_state_list:
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
                prob_phi += '_' + str(index_of_phi_prob)
                self.addToVariableList(prob_phi)
                rew_phi = 'rew'
                for ind in r_state:
                    rew_phi += "_" + str(ind)
                rew_phi += '_' + str(index_of_phi)
                self.addToVariableList(rew_phi)

                first_implies = And(Implies(self.dictOfBools[holds2],
                                            (self.dictOfReals[rew_phi] == float(
                                                reward_model.get_state_reward(r_state[rel_quant - 1])))),
                                    Implies(Not(self.dictOfReals[prob_phi] == float(1)),
                                            (self.dictOfReals[rew_phi] == float(
                                                reward_model.get_state_reward(r_state[rel_quant - 1])))))
                self.no_of_subformula += 3
                self.solver.add(first_implies)

                dicts = []
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts[r_state[l - 1]])
                combined_acts = list(itertools.product(*dicts))

                for ca in combined_acts:
                    act_str = []
                    for l in range(len(relevant_quantifier)):
                        name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                        self.addToVariableList(name)
                        act_str.append(self.dictOfInts[name] == int(ca[l]))
                    implies_precedent = And(self.dictOfReals[prob_phi] == float(1),
                                            Not(self.dictOfBools[holds2]), And(act_str))
                    self.no_of_subformula += 2

                    combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                    sum_left = RealVal(0).as_fraction()

                    for cs in combined_succ:
                        rew_succ = 'rew'
                        prod_left_part = RealVal(1).as_fraction()
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in rel_quant:
                                succ_state = cs[relevant_quantifier.index(l)][0]
                                rew_succ += '_' + succ_state
                                prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                            else:
                                rew_succ += '_' + str(0)

                        rew_succ += '_' + str(index_of_replaced)
                        self.addToVariableList(rew_succ)
                        prod_left_part *= self.dictOfReals[rew_succ]

                        sum_left += prod_left_part
                        self.no_of_subformula += 1

                    implies_antecedent_and = self.dictOfReals[rew_phi] == (float(reward_model.get_state_reward(r_state[
                                                                                                                   rel_quant - 1])) + sum_left)
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                    self.no_of_subformula += 1

        elif k1 > 0:
            left, k_1, k_2, right = hyperproperty.children[0].children
            par1 = copy.deepcopy(k_1)
            par2 = copy.deepcopy(k_2)
            par1.value = str(int(k_1.value) - 1)
            par2.value = str(int(k_2.value) - 1)
            hyperproperty.children[0].children[
                1] = par1  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2 Don't be confused!!
            hyperproperty.children[0].children[2] = par2
            self.list_of_subformula.append(hyperproperty)
            index_of_replaced = len(
                self.list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
            relevant_quantifier = self.encodeRewBoundedUntilSemantics(hyperproperty, [rel_quant])
            relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, relevant_quantifier)
            combined_state_list = self.generateComposedStates(relevant_quantifier)
            rel_quant1 = int(str(hyperproperty.children[0].children[0].children[1].children[0])[1:])

            for r_state in combined_state_list:
                prob_phi = 'prob'
                for ind in r_state:
                    prob_phi += "_" + str(ind)
                prob_phi += '_' + str(index_of_phi_prob)
                self.addToVariableList(prob_phi)
                rew_phi = 'rew'
                for ind in r_state:
                    rew_phi += "_" + str(ind)
                rew_phi += '_' + str(index_of_phi)
                self.addToVariableList(rew_phi)

                first_implies = Implies(Not(self.dictOfReals[prob_phi] == float(1)),
                                        (self.dictOfReals[rew_phi] == float(-999999)))
                self.no_of_subformula += 1
                self.solver.add(first_implies)

                dicts = []
                for l in relevant_quantifier:
                    dicts.append(self.model.dict_of_acts[r_state[l - 1]])
                combined_acts = list(itertools.product(*dicts))

                for ca in combined_acts:
                    act_str = []
                    for l in range(len(relevant_quantifier)):
                        name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                        self.addToVariableList(name)
                        act_str.append(self.dictOfInts[name] == int(ca[l]))
                    implies_precedent = And(self.dictOfReals[prob_phi] == float(1), And(act_str))
                    self.no_of_subformula += 2

                    combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                    sum_left = RealVal(0).as_fraction()

                    for cs in combined_succ:
                        rew_succ = 'rew'
                        prod_left_part = RealVal(1).as_fraction()
                        for l in range(1, self.no_of_state_quantifier + 1):
                            if l in relevant_quantifier:
                                succ_state = cs[relevant_quantifier.index(l)][0]
                                rew_succ += '_' + succ_state
                                prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                            else:
                                rew_succ += '_' + str(0)

                        rew_succ += '_' + str(index_of_replaced)
                        self.addToVariableList(rew_succ)
                        prod_left_part *= self.dictOfReals[rew_succ]

                        prod_left_part *= self.dictOfReals[rew_succ]
                        sum_left += prod_left_part
                        self.no_of_subformula += 1

                    implies_antecedent_and = self.dictOfReals[rew_phi] == (float(reward_model.get_state_reward(r_state[
                                                                                                                   rel_quant - 1])) + sum_left)
                    self.no_of_subformula += 1
                    self.solver.add(Implies(implies_precedent, implies_antecedent_and))
                    self.no_of_subformula += 1
        return relevant_quantifier

    def encodeRewFutureSemantics(self, hyperproperty, prev_relevant_quantifier=None):
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        reward_model = self.model.parsed_model.reward_models.get(
            list(self.model.parsed_model.reward_models.keys())[0]).state_rewards
        rel_quant = int(hyperproperty.children[0].value[1])
        phi1 = hyperproperty.children[1].children[0]
        child = hyperproperty.children[1]
        prob_formula = Tree('probability', [child])
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        index_of_phi_prob = self.list_of_subformula.index(prob_formula)
        relevant_quantifier = self.encodeFutureSemantics(prob_formula, [rel_quant])
        relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, relevant_quantifier)
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            prob_phi = 'prob'
            prob_phi += str_r_state + '_' + str(index_of_phi_prob)
            self.addToVariableList(prob_phi)
            rew_phi = 'rew'
            rew_phi += str_r_state + '_' + str(index_of_phi)
            self.addToVariableList(rew_phi)

            first_implies = And(Implies(self.dictOfBools[holds1],
                                        (self.dictOfReals[rew_phi] == float(reward_model[r_state[rel_quant - 1]]))),
                                Implies(Not(self.dictOfReals[prob_phi] == float(1)),
                                        self.dictOfReals[rew_phi] == float(-9999999)))
            # float(fpPlusInfinity()  # How do we handle the case where prob != 1? TBD
            self.no_of_subformula += 2

            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                act_str = []
                for l in range(len(relevant_quantifier)):
                    name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                    self.addToVariableList(name)
                    act_str.append(self.dictOfInts[name] == int(ca[l]))

                implies_precedent = And(self.dictOfReals[prob_phi] == float(1), Not(self.dictOfBools[holds1]),
                                        And(act_str))
                self.no_of_subformula += 2

                combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                sum_left = RealVal(0).as_fraction()

                for cs in combined_succ:
                    rew_succ = 'rew'
                    prod_left_part = RealVal(1).as_fraction()
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            succ_state = cs[relevant_quantifier.index(l)][0]
                            rew_succ += '_' + succ_state
                            prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                        else:
                            rew_succ += '_' + str(0)

                    rew_succ += '_' + str(index_of_phi)
                    self.addToVariableList(rew_succ)
                    prod_left_part *= self.dictOfReals[rew_succ]
                    sum_left += prod_left_part
                    self.no_of_subformula += 1

                implies_antecedent = self.dictOfReals[rew_phi] == (
                        float(reward_model[r_state[rel_quant - 1]]) + sum_left)
                self.no_of_subformula += 1
                sav = And(first_implies, Implies(implies_precedent, implies_antecedent))
                self.solver.add(sav)
                self.no_of_subformula += 1
        return relevant_quantifier

    def encodeRewGlobalSemantics(self, hyperproperty, prev_relevant_quantifier):
        '''
        if prev_relevant_quantifier is None:
            prev_relevant_quantifier = []
        reward_model = self.model.parsed_model.reward_models.get(
            list(self.model.parsed_model.reward_models.keys())[0]).state_rewards
        rel_quant = int(hyperproperty.children[0].value[1])
        phi1 = hyperproperty.children[1].children[0]
        child = hyperproperty.children[1]
        prob_formula = Tree('probability', [child])
        index_of_phi1 = self.list_of_subformula.index(phi1)
        index_of_phi = self.list_of_subformula.index(hyperproperty)
        index_of_phi_prob = self.list_of_subformula.index(prob_formula)
        relevant_quantifier = self.encodeGlobalSemantics(prob_formula, [rel_quant])
        relevant_quantifier = extendWithoutDuplicates(prev_relevant_quantifier, relevant_quantifier)
        combined_state_list = self.generateComposedStates(relevant_quantifier)

        for r_state in combined_state_list:
            holds1 = 'holds'
            str_r_state = ""
            for ind in r_state:
                str_r_state += "_" + str(ind)
            holds1 += str_r_state + "_" + str(index_of_phi1)
            self.addToVariableList(holds1)
            prob_phi = 'prob'
            prob_phi += str_r_state + '_' + str(index_of_phi_prob)
            self.addToVariableList(prob_phi)
            rew_phi = 'rew'
            rew_phi += str_r_state + '_' + str(index_of_phi)
            self.addToVariableList(rew_phi)

            first_implies = And(Implies(self.dictOfBools[holds1],
                                        (self.dictOfReals[rew_phi] == float(reward_model[r_state[rel_quant - 1]]))),
                                Implies(Not(self.dictOfReals[prob_phi] == float(1)),
                                        self.dictOfReals[rew_phi] == float(-9999999)))
            # float(fpPlusInfinity()  # How do we handle the case where prob != 1? TBD
            self.no_of_subformula += 2

            dicts = []
            for l in relevant_quantifier:
                dicts.append(self.model.dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                act_str = []
                for l in range(len(relevant_quantifier)):
                    name = 'a_' + str(r_state[relevant_quantifier[l] - 1])
                    self.addToVariableList(name)
                    act_str.append(self.dictOfInts[name] == int(ca[l]))

                implies_precedent = And(self.dictOfReals[prob_phi] == float(1), Not(self.dictOfBools[holds1]), And(act_str))
                self.no_of_subformula += 2

                combined_succ = self.genSuccessors(r_state, ca, relevant_quantifier)
                sum_left = RealVal(0).as_fraction()

                for cs in combined_succ:
                    rew_succ = 'rew'
                    prod_left_part = RealVal(1).as_fraction()
                    for l in range(1, self.no_of_state_quantifier + 1):
                        if l in relevant_quantifier:
                            succ_state = cs[relevant_quantifier.index(l)][0]
                            rew_succ += '_' + succ_state
                            prod_left_part *= RealVal(cs[relevant_quantifier.index(l)][1]).as_fraction()
                        else:
                            rew_succ += '_' + str(0)

                    rew_succ += '_' + str(index_of_phi)
                    self.addToVariableList(rew_succ)
                    prod_left_part *= self.dictOfReals[rew_succ]
                    sum_left += prod_left_part
                    self.no_of_subformula += 1

                implies_antecedent = self.dictOfReals[rew_phi] == (
                        float(reward_model[r_state[rel_quant - 1]]) + sum_left)
                self.no_of_subformula += 1
                sav = And(first_implies, Implies(implies_precedent, implies_antecedent))
                self.solver.add(sav)
                self.no_of_subformula += 1
        return relevant_quantifier
    '''
