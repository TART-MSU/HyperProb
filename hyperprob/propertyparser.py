from lark import Lark, Token, Tree
from hyperprob.utility import common


class Property:
    def __init__(self, initial_property_string):
        self.parsed_grammar = None
        self.property_string = initial_property_string
        self.parsed_property = None

    def parseGrammar(self):
        turtle_grammar = """
                        start:    "AS" NAME "." quantifiedformulastate -> forall_scheduler
                            | "ES" NAME "." quantifiedformulastate -> exist_scheduler
                            
                        quantifiedformulastate:  "A" NAME "." quantifiedformulastate -> forall_state  
                            | "E" NAME "." quantifiedformulastate -> exist_state
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

                        proposition: NAME 
                        with: NAME

                        %import common.CNAME -> NAME
                        %import common.NUMBER ->NUM
                        %import common.WS_INLINE
                        %ignore WS_INLINE
                    """
        self.parsed_grammar = Lark(turtle_grammar)

    def parseProperty(self, print_property):
        try:
            self.parseGrammar()
            self.parsed_property = self.parsed_grammar.parse(self.property_string)
            if print_property:
                self.printProperty()
        except Exception as err:
            common.colourerror("Encountered error in property: " + str(err))

    def printProperty(self):
        print(self.parsed_property.pretty())


def findNumberOfStateQuantifier(hyperproperty):
    formula_duplicate = hyperproperty
    no_of_quantifier = 0
    while len(formula_duplicate.children) > 0:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist_state', 'forall_state']:
            no_of_quantifier += 1
            formula_duplicate = formula_duplicate.children[1]
        else:
            break
    return formula_duplicate, no_of_quantifier


def negateForallProperty(parsed_property):
    temp_traversed_property = parsed_property
    while len(temp_traversed_property.children) > 0 and type(temp_traversed_property.children[0]) == Token:
        if temp_traversed_property.data == 'forall_scheduler':
            temp_traversed_property.data = 'exist_scheduler'
        elif temp_traversed_property.data == 'exist_state':
            temp_traversed_property.data = 'forall_state'
        elif temp_traversed_property.data == 'forall_state':
            temp_traversed_property.data = 'exist_state'
        temp_traversed_property = temp_traversed_property.children[1]
        if temp_traversed_property.data == 'quantifiedformulastate':
            break
    if temp_traversed_property.children[0].data == 'not':
        temp_traversed_property.children[0] = temp_traversed_property.children[0].children[0]
    else:
        temp_traversed_property.children[0] = Tree('not', [temp_traversed_property.children[0]])

    return temp_traversed_property.children[0]
