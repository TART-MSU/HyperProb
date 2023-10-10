import copy
import time
import itertools

from lark import Tree
from z3 import Solver, Bool, Int, Or, sat, And

from hyperprob.utility import common
from hyperprob import propertyparser
from hyperprob.sementicencoder import SemanticsEncoder


class ModelChecker:
    def __init__(self, model, hyperproperty):
        self.model = model
        self.initial_hyperproperty = hyperproperty  # object of property class
        self.solver = Solver()
        self.list_of_subformula = []
        self.dictOfBools = dict()
        self.dictOfInts = dict()
        self.dictOfReals = dict()
        self.no_of_subformula = 0
        self.no_of_state_quantifier = 0

    def modelCheck(self):
        non_quantified_property, self.no_of_state_quantifier = propertyparser.findNumberOfStateQuantifier(
            copy.deepcopy(self.initial_hyperproperty.parsed_property))
        non_quantified_property = non_quantified_property.children[0]
        start_time = time.perf_counter()
        self.encodeActions()
        combined_list_of_states = list(
            itertools.product(self.model.getListOfStates(), repeat=self.no_of_state_quantifier))

        if self.initial_hyperproperty.parsed_property.data == 'exist_scheduler':
            self.addToSubformulaList(non_quantified_property)
            self.encodeStateQuantifiers(combined_list_of_states)
            common.colourinfo("Encoded state quantifiers", False)
            semanticEncoder = SemanticsEncoder(self.model, self.solver,
                                               self.list_of_subformula, self.dictOfBools, self.dictOfInts, self.dictOfReals,
                                               self.no_of_subformula, self.no_of_state_quantifier)
            semanticEncoder.encodeSemantics(non_quantified_property)
            common.colourinfo("Encoded non-quantified formula...", False)
            smt_end_time = time.perf_counter() - start_time
            self.printResult(smt_end_time, 'exists')

        elif self.initial_hyperproperty.parsed_property.data == 'forall_scheduler':
            negated_non_quantified_property = propertyparser.negateForallProperty(self.initial_hyperproperty.parsed_property)
            self.addToSubformulaList(negated_non_quantified_property)
            self.encodeStateQuantifiers(combined_list_of_states)
            common.colourinfo("Encoded state quantifiers", False)
            semanticEncoder = SemanticsEncoder(self.model, self.solver,
                                               self.list_of_subformula, self.dictOfBools, self.dictOfInts, self.dictOfReals,
                                               self.no_of_subformula, self.no_of_state_quantifier)
            semanticEncoder.encodeSemantics(negated_non_quantified_property)
            common.colourinfo("Encoded non-quantified formula...", False)
            smt_end_time = time.perf_counter() - start_time
            self.printResult(smt_end_time, 'forall')

    def encodeActions(self):
        for state in self.model.parsed_model.states:
            list_of_eqns = []
            name = "a_" + str(state.id)  # a_1 means action for state 1
            self.dictOfInts[name] = Int(name)
            for action in state.actions:
                list_of_eqns.append(self.dictOfInts[name] == int(action.id))
            self.solver.add(Or(list_of_eqns))
            self.no_of_subformula += 1
        common.colourinfo("Encoded actions in the MDP...")

    def addToSubformulaList(self, formula_phi):  # add as you go any new subformula part as needed
        if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist_state', 'forall_state']:
            formula_phi = formula_phi.children[1]
            self.addToSubformulaList(formula_phi)
        elif formula_phi.data == 'quantifiedscheduler':
            formula_phi = formula_phi.children[0]
        elif formula_phi.data in ['and', 'or', 'implies', 'biconditional',
                                  'less_probability', 'equal_probability', 'greater_probability',
                                  'greater_and_equal_probability', 'less_and_equal_probability',
                                  'less_reward', 'equal_reward', 'greater_reward', 'greater_and_equal_reward',
                                  'less_and_equal_reward',
                                  'add_probability', 'subtract_probability', 'multiply_probability',
                                  'add_reward', 'subtract_reward', 'multiply_reward',
                                  'until_unbounded'
                                  ]:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            left_child = formula_phi.children[0]
            self.addToSubformulaList(left_child)
            right_child = formula_phi.children[1]
            self.addToSubformulaList(right_child)
        elif formula_phi.data in ['atomic_proposition', 'true', 'constant_probability', 'constant_reward']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
        elif formula_phi.data in ['next', 'not', 'future', 'global']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            self.addToSubformulaList(formula_phi.children[0])
        elif formula_phi.data in ['probability']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            self.addToSubformulaList(formula_phi.children[0])
        elif formula_phi.data in ['reward']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
                prob_formula = Tree('probability', [formula_phi.children[1]])
                self.list_of_subformula.append(prob_formula)
            self.addToSubformulaList(formula_phi.children[1])
        elif formula_phi.data in ['until_bounded']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            left_child = formula_phi.children[0]
            self.addToSubformulaList(left_child)
            right_child = formula_phi.children[3]
            self.addToSubformulaList(right_child)

    def encodeStateQuantifiers(self, combined_list_of_states):
        list_of_AV = []  # will have the OR, AND according to the quantifier in that index in the formula
        changed_hyperproperty = self.initial_hyperproperty.parsed_property
        while len(changed_hyperproperty.children) > 0:
            if changed_hyperproperty.data in ['exist_scheduler', 'forall_scheduler']:
                changed_hyperproperty = changed_hyperproperty.children[1]
            elif changed_hyperproperty.data == 'exist_state':
                list_of_AV.append('V')
                changed_hyperproperty = changed_hyperproperty.children[2]
            elif changed_hyperproperty.data == 'forall_state':
                list_of_AV.append('A')
                changed_hyperproperty = changed_hyperproperty.children[2]
            elif changed_hyperproperty.data == 'quantifiedstate':
                break
            elif changed_hyperproperty.data == 'quantifiedscheduler':
                changed_hyperproperty = changed_hyperproperty.children[0]
        index_of_phi = self.list_of_subformula.index(changed_hyperproperty.children[0])
        list_of_holds = []

        for i in range(len(combined_list_of_states)):
            name = "holds_"
            for j in range(self.no_of_state_quantifier):
                name += str(combined_list_of_states[i][j]) + "_"
            name += str(index_of_phi)
            self.dictOfBools[name] = Bool(name)
            list_of_holds.append(self.dictOfBools[name])

        list_of_holds_replace = []
        for i in range(self.no_of_state_quantifier - 1, -1, -1):
            count = -1
            limit = len(list_of_holds)
            quo = 0
            for j in range(limit):
                count += 1
                if count == len(self.model.getListOfStates()) - 1:
                    index = quo * len(self.model.getListOfStates())
                    if list_of_AV[i] == 'V':
                        list_of_holds_replace.append(Or([par for par in list_of_holds[index:index + count + 1]]))
                        self.no_of_subformula += 1
                    elif list_of_AV[i] == 'A':
                        list_of_holds_replace.append(And([par for par in list_of_holds[index:index + count + 1]]))
                        self.no_of_subformula += 1
                    count = -1
                    quo += 1
            list_of_holds = copy.deepcopy(list_of_holds_replace)
            list_of_holds_replace.clear()
        self.solver.add(list_of_holds[0])
        list_of_holds.clear()
        list_of_holds_replace.clear()

    def checkResult(self):
        starting_time = time.perf_counter()
        truth = self.solver.check()
        z3_time = time.perf_counter() - starting_time
        list_of_actions = None
        if truth == sat:
            z3model = self.solver.model()
            list_of_actions = [None] * len(self.model.getListOfStates())
            for li in z3model:
                if li.name()[0] == 'a':
                    list_of_actions[int(li.name()[2:])] = z3model[li]
        if truth.r == 1:
            return True, list_of_actions, self.solver.statistics(), z3_time
        elif truth.r == -1:
            return False, list_of_actions, self.solver.statistics(), z3_time

    def printResult(self, smt_end_time, scheduler_quantifier):
        common.colourinfo("Checking...", False)
        smt_result, actions, statistics, z3_time = self.checkResult()
        if scheduler_quantifier == 'exists':
            if smt_result:
                common.colouroutput("The property HOLDS!")
                print("\nThe values of variables of the witness are:")
                for i in range(0, len(self.model.getListOfStates())):
                    common.colouroutput("At state " + str(i) + " choose action " + str(actions[i]), False)
            else:
                common.colourerror("The property DOES NOT hold!")
        elif scheduler_quantifier == 'forall':
            if smt_result:
                common.colourerror("The property DOES NOT hold!")
                print("\nThe actions at the corresponding states of a counterexample are:")
                for i in range(0, len(self.model.getListOfStates())):
                    common.colouroutput("At state " + str(i) + " choose action " + str(actions[i]), False)
            else:
                common.colouroutput("The property HOLDS!")
        common.colourinfo("\nTime to encode in seconds: " + str(round(smt_end_time, 2)), False)
        common.colourinfo("Time required by z3 in seconds: " + str(round(z3_time, 2)), False)
        common.colourinfo("Number of variables: " + str(len(self.dictOfInts.keys()) + len(self.dictOfReals.keys()) + len(self.dictOfBools.keys())), False)
        common.colourinfo("Number of formula checked: " + str(self.no_of_subformula), False)
        common.colourinfo("z3 statistics:", False)
        common.colourinfo(str(statistics), False)
