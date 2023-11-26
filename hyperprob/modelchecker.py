import copy
import itertools
import time

from lark import Tree
# from z3 import Solver, Bool, Int, Or, sat, And
from pysmt.shortcuts import Symbol, Int, Real, Bool, LE, GE, Equals, And, Or, Not, Implies, Plus, Minus, Times, Div, \
    Solver
from pysmt.typing import REAL

from hyperprob import propertyparser
from hyperprob.sementicencoder import SemanticsEncoder
from hyperprob.utility import common


class ModelChecker:
    def __init__(self, list_of_model, hyperproperty):
        self.list_of_model = list_of_model  # list of models of Model class
        self.initial_hyperproperty = hyperproperty  # object of Property class

        self.list_of_subformula = []
        self.dictOfBools = dict()
        self.dictOfReals = dict()
        self.solver = Solver()  # (name='z3')

    def modelCheck(self):
        non_quantified_property, self.initial_hyperproperty.quantifierDictionary, self.initial_hyperproperty.scheduler_quantifiers, self.initial_hyperproperty.state_quantifiers = propertyparser.parseQuantifiersToDictionary(
            copy.deepcopy(self.initial_hyperproperty.parsed_property))
        start_time = time.perf_counter()
        list_of_state_ranges = []
        for st in self.initial_hyperproperty.quantifierDictionary["stateq"].keys():
            list_of_state_ranges.append(self.list_of_model[
                                            self.initial_hyperproperty.quantifierDictionary["schedq"].index(
                                                self.initial_hyperproperty.quantifierDictionary["stateq"][
                                                    st])].parsed_model.nr_states)

        if self.initial_hyperproperty.parsed_property.data == 'exist_scheduler':
            self.encodeActions()
            self.addToSubformulaList(non_quantified_property)
            self.encodeStateQuantifiers(list_of_state_ranges)
            common.colourinfo("Encoded state quantifiers", False)
            semanticEncoder = SemanticsEncoder(self.list_of_model, self.solver,
                                               self.list_of_subformula, self.dictOfBools,
                                               self.dictOfReals, self.initial_hyperproperty)
            semanticEncoder.encodeSemantics(non_quantified_property)
            common.colourinfo("Encoded non-quantified formula...", False)
            smt_end_time = time.perf_counter() - start_time
            self.printResult(smt_end_time, 'exists')

        elif self.initial_hyperproperty.parsed_property.data == 'forall_scheduler':
            negated_non_quantified_property, self.initial_hyperproperty.scheduler_quantifiers, self.initial_hyperproperty.state_quantifiers = propertyparser.convertToInitialExistentialProperty(
                self.initial_hyperproperty.parsed_property)
            self.encodeActions()
            self.addToSubformulaList(negated_non_quantified_property)
            self.encodeStateQuantifiers(list_of_state_ranges)
            common.colourinfo("Encoded state quantifiers", False)
            semanticEncoder = SemanticsEncoder(self.list_of_model, self.solver,
                                               self.list_of_subformula, self.dictOfBools,
                                               self.dictOfReals, self.initial_hyperproperty)
            semanticEncoder.encodeSemantics(negated_non_quantified_property)
            common.colourinfo("Encoded non-quantified formula...", False)
            smt_end_time = time.perf_counter() - start_time
            self.printResult(smt_end_time, 'forall')

    def encodeActions(self):
        """
        We encode the action choices allowed in every model
        a_sh_s_act: action for model associated with scheduler sh (as in the list of schedulers in
        the token dictionary), state s, and action act.
        """
        for loop in range(len(self.list_of_model)):
            flag = self.initial_hyperproperty.scheduler_quantifiers[loop]
            for state in self.list_of_model[loop].parsed_model.states:
                actions_in_state = []
                for action in state.actions:
                    name = "a_" + str(loop) + "_" + str(state.id) + "_" + str(action.id)
                    self.dictOfBools[name] = Symbol(name)
                    actions_in_state.append(self.dictOfBools[name])
                if flag:
                    self.solver.add_assertion(And(actions_in_state))
                else:
                    self.solver.add_assertion(Or(actions_in_state))
        common.colourinfo("Encoded actions in the MDP...")

    def addToSubformulaList(self, formula_phi):  # add any new subformula part as needed

        if formula_phi.data in ['and', 'or', 'implies', 'biconditional',
                                'less_probability', 'equal_probability', 'greater_probability',
                                'greater_and_equal_probability', 'less_and_equal_probability',
                                'less_reward', 'equal_reward', 'greater_reward', 'greater_and_equal_reward',
                                'less_and_equal_reward',
                                'add_probability', 'subtract_probability', 'multiply_probability',
                                'add_reward', 'subtract_reward', 'multiply_reward',
                                'until_unbounded']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            self.addToSubformulaList(formula_phi.children[0])
            self.addToSubformulaList(formula_phi.children[1])
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
                self.list_of_subformula.append(Tree('probability', [formula_phi.children[1]]))
            self.addToSubformulaList(formula_phi.children[1])
        elif formula_phi.data in ['until_bounded']:
            if formula_phi not in self.list_of_subformula:
                self.list_of_subformula.append(formula_phi)
            self.addToSubformulaList(formula_phi.children[0])
            self.addToSubformulaList(formula_phi.children[3])

    def encodeStateQuantifiers(self, list_of_state_ranges):
        list_of_holds = []
        combined_list_of_states = list(itertools.product(*list(range(li) for li in list_of_state_ranges)))
        for tup in combined_list_of_states:
            name = "holds_"
            for j in tup:
                name += str(j) + "_"
            name += str(0)  # we are encoding for the outermost non-quantified formula, so assuming this is safe
            self.dictOfBools[name] = Symbol(name)
            list_of_holds.append(self.dictOfBools[name])

        list_of_holds_replace = []
        for i in range(len(self.initial_hyperproperty.state_quantifiers) - 1, -1, -1):
            count = -1
            limit = len(list_of_holds)
            quo = 0
            for j in range(limit):
                count += 1
                if count == list_of_state_ranges[i] - 1:
                    index = quo * list_of_state_ranges[i]
                    if not self.initial_hyperproperty.state_quantifiers[i]:
                        list_of_holds_replace.append(Or([par for par in list_of_holds[index:index + count + 1]]))
                    elif self.initial_hyperproperty.state_quantifiers[i]:
                        list_of_holds_replace.append(And([par for par in list_of_holds[index:index + count + 1]]))
                    count = -1
                    quo += 1
            list_of_holds = copy.deepcopy(list_of_holds_replace)
            list_of_holds_replace.clear()
        self.solver.add_assertion(list_of_holds[0])
        del list_of_holds
        del list_of_holds_replace

    def checkResult(self):
        starting_time = time.perf_counter()
        truth = self.solver.solve()
        z3_time = time.perf_counter() - starting_time
        list_of_actions = None
        for x in self.dictOfBools.keys():
            print("%s = %s" % (x, self.solver.get_value(self.dictOfBools[x])))
        """
        # if model:
            #list_of_actions = [None] * len(self.model.getListOfStates())
            #for li in z3model:
            #    if li.name()[0] == 'a':
            #        list_of_actions[int(li.name()[2:])] = z3model[li]
        if model == 1:
            return True, list_of_actions, self.solver.statistics(), z3_time
        elif model == -1:
            return False, list_of_actions, self.solver.statistics(), z3_time
        """

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
        common.colourinfo("Number of variables: " + str(
            len(self.dictOfInts.keys()) + len(self.dictOfReals.keys()) + len(self.dictOfBools.keys())), False)
        common.colourinfo("Number of formula checked: " + str(self.no_of_subformula), False)
        common.colourinfo("z3 statistics:", False)
        common.colourinfo(str(statistics), False)
