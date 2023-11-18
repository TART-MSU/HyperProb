import copy
from lark import Lark, Token, Tree
from hyperprob.utility import common


class Hyperproperty:
    def __init__(self, initial_property_string):
        self.parsed_grammar = None
        self.property_string = initial_property_string
        self.parsed_property = None
        self.quantifierDictionary = dict()
        self.scheduler_quantifiers = []
        self.state_quantifiers = []

    def parseGrammar(self):
        turtle_grammar = """
                        quantifiedscheduler:   "AS" NAME "." quantifiedscheduler -> forall_scheduler
                            | "ES" NAME "." quantifiedscheduler -> exist_scheduler 
                            | quantifiedstate
                             
                        quantifiedstate:  "A" NAME "(" with ")" "." quantifiedstate -> forall_state  
                            | "E" NAME "(" with ")" "." quantifiedstate -> exist_state
                            | formula
                        
                        formula: proposition "(" with ")"  -> atomic_proposition
                            | "(" formula "&" formula ")"-> and
                            | "(" formula "|" formula ")"-> or
                            | "(" formula "->" formula ")"-> implies
                            | "(" formula "<->" formula ")"-> biconditional
                            | "~" formula -> not
                            | "true" -> true
                            | "(" p "<" p ")" -> less_probability
                            | "(" p "=" p ")" -> equal_probability
                            | "(" p ">" p ")" -> greater_probability
                            | "(" p ">=" p ")" -> greater_and_equal_probability
                            | "(" p "<=" p ")" -> less_and_equal_probability
                            | "(" r "<" r ")" -> less_reward
                            | "(" r "=" r ")" -> equal_reward
                            | "(" r ">" r ")" -> greater_reward
                            | "(" r ">=" r ")" -> greater_and_equal_reward
                            | "(" r "<=" r ")" -> less_and_equal_reward

                        p: "P" phi  -> probability
                            | p "+" p -> add_probability
                            | p "-" p -> subtract_probability
                            | p "." p -> multiply_probability
                            | NUM -> constant_probability

                        r: "R" NAME phi  -> reward
                            | r "+" r -> add_reward
                            | r "-" r -> subtract_reward
                            | r "." r -> multiply_reward
                            | NUM -> constant_reward

                        phi:  "(X" formula ")" -> next
                            | "(" formula "U" formula ")"-> until_unbounded
                            | "(" formula "U["NUM "," NUM"]" formula ")"-> until_bounded
                            | "(F" formula ")" -> future
                            | "(G" formula ")" -> global

                        proposition: NAME 
                        with: NAME

                        %import common.CNAME -> NAME
                        %import common.NUMBER ->NUM
                        %import common.WS_INLINE
                        %ignore WS_INLINE
                    """
        self.parsed_grammar = Lark(turtle_grammar, start="quantifiedscheduler")

    def parseProperty(self, print_property):
        try:
            self.parseGrammar()
            self.parsed_property = self.parsed_grammar.parse(self.property_string)
            if print_property:
                self.printProperty()
        except Exception as err:
            raise SystemExit("Encountered error in property: " + str(err))

    def printProperty(self):
        print(self.parsed_property.pretty())


def parseQuantifiersToDictionary(hyperproperty):
    """
    Creates dictionary mapping state quantifiers to their schedulers
    :param hyperproperty: hyperproperty
    :return: unquantified formula and token dictionary
    """
    tokenDictionary = dict()
    tokenDictionary["schedq"] = []
    tokenDictionary["stateq"] = dict()
    list_of_sched_quantifier = [] # store true for AS false for ES
    list_of_state_quantifier = []  # store true for A false for E
    formula_duplicate = hyperproperty
    while len(formula_duplicate.children) > 0:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            if formula_duplicate.data == 'exist_scheduler':
                list_of_sched_quantifier.append(False)
            else:
                list_of_sched_quantifier.append(True)
            tokenDictionary["schedq"].append(formula_duplicate.children[0].value)
            formula_duplicate = formula_duplicate.children[1]

        elif formula_duplicate.data in ['exist_state', 'forall_state']:
            temp = formula_duplicate.children[1].children[0].value
            if temp not in tokenDictionary["schedq"]:
                raise SystemExit("Unknown scheduler quantifier name: " + temp)
            if formula_duplicate.children[0].value in tokenDictionary["stateq"].keys():
                raise SystemExit("Duplicate state quantifier name: " + formula_duplicate.children[0].value)
            if formula_duplicate.data == 'exist_state':
                list_of_state_quantifier.append(False)
            else:
                list_of_state_quantifier.append(True)
            tokenDictionary["stateq"][formula_duplicate.children[0].value] = temp
            formula_duplicate = formula_duplicate.children[2]

        elif formula_duplicate.data == 'quantifiedscheduler':
            formula_duplicate = formula_duplicate.children[0]
        elif formula_duplicate.data == 'quantifiedstate':
            formula_duplicate = formula_duplicate.children[0]
        else:
            break
    if len(tokenDictionary["schedq"]) > len(tokenDictionary["stateq"].values()):
        raise SystemExit("Unused scheduler variable. Please rewrite property!")
    return formula_duplicate, tokenDictionary, list_of_sched_quantifier, list_of_state_quantifier


def convertToInitialExistentialProperty(parsed_property):
    """
    We use this method to convert forall x . Q y.... properties to exists x. -neg Q .
    This can convert just outer question to witness/counterexample search.
    An assumption here is that the formula starting with an exists does not reach this method.
    :param parsed_property: hyperproperty from user
    :return: hyperproperty starting with existential quantifier and negated as necessary
    """
    list_of_sched_quantifier = []  # store true for AS false for ES
    list_of_state_quantifier = []  # store true for A false for E
    temp_traversed_property = parsed_property
    while len(temp_traversed_property.children) > 0:
        if temp_traversed_property.data == 'forall_scheduler':
            temp_traversed_property.data = 'exist_scheduler'
            list_of_sched_quantifier.append(False)
            temp_traversed_property = temp_traversed_property.children[1]
        elif temp_traversed_property.data == 'exist_scheduler':
            temp_traversed_property.data = 'forall_scheduler'
            list_of_sched_quantifier.append(True)
            temp_traversed_property = temp_traversed_property.children[1]
        elif temp_traversed_property.data == 'exist_state':
            temp_traversed_property.data = 'forall_state'
            list_of_state_quantifier.append(True)
            temp_traversed_property = temp_traversed_property.children[2]
        elif temp_traversed_property.data == 'forall_state':
            temp_traversed_property.data = 'exist_state'
            list_of_state_quantifier.append(False)
            temp_traversed_property = temp_traversed_property.children[2]
        elif temp_traversed_property.data == 'quantifiedscheduler':
            temp_traversed_property = temp_traversed_property.children[0]
        elif temp_traversed_property.data == 'quantifiedstate':
            break
    if temp_traversed_property.children[0].data == 'not':
        temp_traversed_property.children[0] = temp_traversed_property.children[0].children[0]
    else:
        temp_traversed_property.children[0] = Tree('not', [temp_traversed_property.children[0]])

    return temp_traversed_property.children[0], list_of_sched_quantifier, list_of_state_quantifier
