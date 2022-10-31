from lark import Lark
from hyperprob.utility import common


# Note the change in name of state quantifiers
def parser(formula):
    try:
        turtle_grammar = """
            start:    "AS" NAME "." formula -> forall_scheduler
                | "ES" NAME "." formula -> exist_scheduler
            
            formula:  "A" NAME "." formula -> forall_state  
                    | "E" NAME "." formula -> exist_state
                    | proposition "(" withstate ")"  -> atomic_proposition
                    | "(" formula "&" formula ")"-> and
                    | "(" formula "|" formula ")"-> or
                    | "(" formula "->" formula ")"-> implies
                    | "(" formula "<->" formula ")"-> equivalent
                    | "~" formula -> not
                    | "true" -> true
                    | "(" p "<" p ")" -> less
                    | "(" p "=" p ")" -> equal
                    | "(" p ">" p ")" -> greater
                    | "(" p ">=" p ")" -> greater_and_equal
                    | "(" p "<=" p ")" -> less_and_equal
            
            p: "P" phi  -> probability
                |p "+" p -> add
                | p "-" p -> subtract
                | p "." p -> multiply
                | NUM -> constant

            phi:  "(X" formula ")" -> next
                | "(" formula "U" formula ")"-> until_unbounded
                | "(" formula "U["NUM "," NUM"]" formula ")"-> until_bounded
                | "(F" formula ")" -> future
                | "(G" formula ")" -> global
    
            proposition: NAME 
            withstate: NAME 

            %import common.CNAME -> NAME
            %import common.NUMBER ->NUM
            %import common.WS_INLINE
            %ignore WS_INLINE
        """

        parsed_grammar = Lark(turtle_grammar)
        parsed_formula_initial = parsed_grammar.parse(formula)
        print(parsed_formula_initial.pretty())
    except Exception as err:
        common.colourerror("Encountered error: " + str(err), 'red')