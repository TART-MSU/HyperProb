import itertools
import time

import stormpy
from lark import Lark, Token
from z3 import *

import files

turtle_grammar = """
    start:  "AS" NAME "." start -> forall_scheduler
          | "ES" NAME "." start -> exist_scheduler
          | "A" NAME "." start -> forall
          | "E" NAME "." start -> exist
          | varname  -> var
          | "(" start "&" start ")"-> and_op
          | "(" start "|" start ")"-> or_op
          | "~" start -> neg_op
          | "true" -> true
          | "(" p "<" p ")" -> less_prob
          | "(" p "=" p ")" -> equal_prob
          | "(" p ">" p ")" -> greater_prob
          | "(" p ">=" p ")" -> greatereq_prob
          | "(" p "<=" p ")" -> lesseq_prob
    p: "P" phi  -> calc_probability
          |p "+" p -> add_prob
          | p "-" p -> minus_prob
          | p "." p -> mul_prob
          | NUM -> const
    phi:  "(X" start ")" -> calc_next
          | "(" start "U" start ")"-> calc_until_unbounded
          | "(" start "U["NUM "," NUM"]" start ")"-> calc_until_bounded
          | "(F" start ")" -> calc_future
    ap: "f"
          |"t"
          | varname
          | varname "&" ap  ->and_vars
          |"(" varname "|" varname ")" ->or_vars
          |ap "=>" start ->imply_vars
          |ap "<->" ap ->iff_vars
    varname: NAME "(" NAME ")" ->varname
    %import common.CNAME -> NAME
    %import common.NUMBER ->NUM
    %import common.WS_INLINE
    %ignore WS_INLINE
"""
parser = None
list_of_subformula = []
list_of_reals = []
listOfReals = []
list_of_bools = []
listOfBools = []
list_of_ints = []
listOfInts = []
s = None
nos_of_subformula = 0


def SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n):
    print("Starting until")
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    phi2 = formula_duplicate.children[0].children[1]
    index_of_phi2 = list_of_subformula.index(phi2)
    result_string = 'A(' + Semantics(model, phi1, combined_list_of_states, n) + ' ' + Semantics(model, phi2,
                                                                                                combined_list_of_states,
                                                                                                n) + ')'
    index_of_phi = list_of_subformula.index(formula_duplicate)
    dict_of_acts = dict()
    dict_of_acts_tran = dict()
    for state in model.states:
        list_of_act = []
        for action in state.actions:
            list_of_tran = []
            list_of_act.append(action.id)
            for tran in action.transitions:
                list_of_tran.append(str(tran.column) + ' ' + str(tran.value()))
            dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
        dict_of_acts[state.id] = list_of_act

    for li in combined_list_of_states:
        result_string = 'A(' + result_string + ' '
        first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(
            li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
        if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
            list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
        second_implies = 'I(A(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ') N(holds_' + str(
            li[0]) + '_' + str(li[1]) + '_' + str(
            index_of_phi2) + ')) ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=0)'
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
        new_prob_const = 'G(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' 0)'
        result_string += first_implies + ' ' + second_implies + ' ' + new_prob_const + ')'
        combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
        for ca in combined_acts:
            implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ') A(a_' + str(li[0]) + '=' + str(ca[0]) + ' a_' + str(li[1]) + '=' + str(ca[1]) + '))'
            if 'a_' + str(li[0]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[0]))
            if 'a_' + str(li[1]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[1]))

            implies_antecedent_and1 = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
            combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                   dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
            first = False
            if len(combined_succ) == 1:
                first = True
            prod_left = 'P('
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                if first:
                    prod_left = 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + \
                                cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi) + ') '
                else:
                    prod_left += 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + \
                                 cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi) + ') '
                if 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi) not in list_of_z3_variables:
                    list_of_z3_variables.append(
                        'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi))
            if first:
                implies_antecedent_and1 += prod_left[0:len(prod_left) - 1] + ')'
            else:
                implies_antecedent_and1 += prod_left[0:len(prod_left) - 1] + '))'
            implies_antecedent_and2 = 'I(g(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' 0) '
            prod_right_or = 'V('
            first = False
            if len(combined_succ) == 1:
                first = True
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                if first:
                    prod_right_or = 'V(holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) + ' g(d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                        index_of_phi2) + ' d_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) + ')) '
                else:
                    prod_right_or += 'V(holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) + ' g(d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                        index_of_phi2) + ' d_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) + ')) '
                if 'holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append(
                        'holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2))
                if 'd_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append('d_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
                if 'd_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_of_phi2) not in list_of_z3_variables:
                    list_of_z3_variables.append(
                        'd_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2))
            if first:
                implies_antecedent_and2 += prod_right_or[0:len(prod_right_or) - 1] + ')'
            else:
                implies_antecedent_and2 += prod_right_or[0:len(prod_right_or) - 1] + '))'
            implies_antecedent = 'A(' + implies_antecedent_and1 + ' ' + implies_antecedent_and2 + ')'
            result_string = 'A(' + result_string + ' I(' + implies_precedent + ' ' + implies_antecedent + '))'
    print("Done with until")
    return result_string


def SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n):
    result_string = ''
    phi1 = formula_duplicate.children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    phi2 = formula_duplicate.children[3]
    index_of_phi2 = list_of_subformula.index(phi2)
    k1 = int(formula_duplicate.children[1].value)
    k2 = int(formula_duplicate.children[2].value)
    index_of_phi = list_of_subformula.index(formula_duplicate)
    if k2 == 0:
        result_string = 'A(' + Semantics(model, phi1, combined_list_of_states, n) + ' ' + Semantics(model, phi2,
                                                                                                    combined_list_of_states,
                                                                                                    n) + ')'
        result_string = 'A(' + result_string + ' '
        sum_of_loop1 = 'A('
        sum_of_loop2 = 'A('
        for li in combined_list_of_states:
            first_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + '=1' + ' holds_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) + ')'
            second_and1 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + '=0' + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + '))'
            final_or1 = 'V(' + first_and1 + ' ' + second_and1 + ')'
            sum_of_loop1 += final_or1 + ' '
            first_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + '=1' + ' holds_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ')'
            second_and2 = "A(prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + '=0' + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + '))'
            final_or2 = 'V(' + first_and2 + ' ' + second_and2 + ')'
            sum_of_loop2 += final_or2 + ' '
            if "prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append("prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            if "prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append("prob_" + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
        sum_of_loop1 = sum_of_loop1[0:len(sum_of_loop1) - 1] + ')'
        sum_of_loop2 = sum_of_loop2[0:len(sum_of_loop2) - 1] + ')'
        result_string += sum_of_loop1 + ')'
        result_string = 'A(' + result_string + ' ' + sum_of_loop2 + ')'

        for li in combined_list_of_states:
            result_string = 'A(' + result_string + ' '
            first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                list_of_z3_variables.append(
                    'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
            second_implies = 'I(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ')' + ' prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi) + '=0)'
            result_string += first_implies + ' ' + second_implies + ')'
        result_string += ')'

    elif k1 == 0:
        left, k_1, k_2, right = formula_duplicate.children
        par = copy.deepcopy(k_2)
        par.value = str(
            int(
                k_2.value) - 1)  # k2.value will have changed value but it won't show up in the formula tree, hence it'll appear to be the same formula as formula_duplicate
        formula_duplicate.children[
            2] = par  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2. Don't be confused!!
        list_of_subformula.append(formula_duplicate)
        index_of_replaced = len(
            list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
        result_string = SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)

        dict_of_acts = dict()
        dict_of_acts_tran = dict()
        for state in model.states:
            list_of_act = []
            for action in state.actions:
                list_of_tran = []
                list_of_act.append(action.id)
                for tran in action.transitions:
                    # list_of_tran.append({tran.column: tran.value()})
                    list_of_tran.append(tran.value())
                dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
            dict_of_acts[state.id] = list_of_act

        for li in combined_list_of_states:
            result_string = 'A(' + result_string + ' '
            first_implies = 'I(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) + ' ' + 'prob_' + str(
                li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=1)'
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2))
            second_implies = 'I(A(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + ') N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi2) + ')) ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + '=0)'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            result_string += first_implies + ' ' + second_implies + ')'
            combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
            for ca in combined_acts:
                implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_of_phi1) + ' N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_of_phi2) + ') A(a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) + '=' + str(
                    ca[0]) + ' a_s' + str(
                    combined_list_of_states.index(li)) + '_' + str(1) + '=' + str(ca[1]) + '))'
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(0))
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(1))

                implies_antecedent = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
                combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                       dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
                if len(combined_succ) == 1:
                    first = True
                prod = 'P('
                for cs in combined_succ:
                    if first:
                        prod = 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(
                            combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    else:
                        prod += 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(
                            combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    if 'prob_s' + str(combined_succ.index(cs)) + '_' + str(
                            index_of_replaced) not in list_of_z3_variables:
                        list_of_z3_variables.append(
                            'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced))
                if first:
                    implies_antecedent += prod[0:len(prod) - 1]
                    first = False
                else:
                    implies_antecedent += prod[0:len(prod) - 1] + ')'
                result_string = 'A(' + result_string + ' I(' + implies_precedent + ' ' + implies_antecedent + ')))'

    elif k1 > 0:
        left, k_1, k_2, right = formula_duplicate.children
        par1 = copy.deepcopy(k_1)
        par2 = copy.deepcopy(k_2)
        par1.value = str(int(k_1.value) - 1)
        par2.value = str(int(k_2.value) - 1)
        formula_duplicate.children[
            1] = par1  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2 Don't be confused!!
        formula_duplicate.children[2] = par2
        list_of_subformula.append(formula_duplicate)
        index_of_replaced = len(
            list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
        result_string = SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)

        dict_of_acts = dict()
        dict_of_acts_tran = dict()
        for state in model.states:
            list_of_act = []
            for action in state.actions:
                list_of_tran = []
                list_of_act.append(action.id)
                for tran in action.transitions:
                    # list_of_tran.append({tran.column: tran.value()})
                    list_of_tran.append(tran.value())
                dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
            dict_of_acts[state.id] = list_of_act

        for li in combined_list_of_states:
            result_string = 'A(' + result_string + ' '
            first_implies = 'I(N(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi1) + ') ' + 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                index_of_phi) + '=0)'
            if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1) not in list_of_z3_variables:
                list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi1))
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) not in list_of_z3_variables:
                list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi))
            result_string += first_implies + ')'
            combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
            for ca in combined_acts:
                implies_precedent = 'A(holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    index_of_phi1) + ' A(a_s' + str(combined_list_of_states.index(li)) + '_' + str(
                    0) + '=' + str(ca[0]) + ' a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) + '=' + str(
                    ca[1]) + '))'
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(0) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(0))
                if 'a_s' + str(combined_list_of_states.index(li)) + '_' + str(1) not in list_of_z3_variables:
                    list_of_z3_variables.append('a_s' + str(combined_list_of_states.index(li)) + '_' + str(1))

                implies_antecedent = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi) + ' '
                combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                       dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
                if len(combined_succ) == 1:
                    first = True
                prod = 'P('
                for cs in combined_succ:
                    if first:
                        prod = 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(
                            combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    else:
                        prod += 'M(' + str(cs[0]) + ' ' + str(cs[1]) + ' ' + 'prob_s' + str(
                            combined_succ.index(cs)) + '_' + str(index_of_replaced) + ') '
                    if 'prob_s' + str(combined_succ.index(cs)) + '_' + str(
                            index_of_replaced) not in list_of_z3_variables:
                        list_of_z3_variables.append(
                            'prob_s' + str(combined_succ.index(cs)) + '_' + str(index_of_replaced))
                if first:
                    implies_antecedent += prod[0:len(prod) - 1]
                    first = False
                else:
                    implies_antecedent += prod[0:len(prod) - 1] + ')'
                implies_antecedent += ')'

                result_string = 'A(' + result_string + ' I(' + implies_precedent + ' ' + implies_antecedent + '))'

    return result_string


def SemanticsNext(model, formula_duplicate, combined_list_of_states, n):
    phi1 = formula_duplicate.children[0].children[0]
    Semantics(model, phi1, combined_list_of_states, n)
    index_phi1 = list_of_subformula.index(phi1)
    for li in combined_list_of_states:
        pos_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '=1 holds_' + str(
            li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + ')'
        if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
        if 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) not in list_of_z3_variables:
            list_of_z3_variables.append('holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1))
        neg_and = 'A(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '=0 N(holds_' + str(
            li[0]) + '_' + str(li[1]) + '_' + str(index_phi1) + '))'
        result_string += 'V(' + pos_and + ' ' + neg_and + ') '
    result_string = result_string[0:len(result_string) - 1] + '))'
    dict_of_acts = dict()
    dict_of_acts_tran = dict()
    for state in model.states:
        list_of_act = []
        for action in state.actions:
            list_of_tran = []
            list_of_act.append(action.id)
            for tran in action.transitions:
                list_of_tran.append(str(tran.column) + ' ' + str(
                    tran.value()))  # storing just transition values, not state it transitions to
            dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
        dict_of_acts[state.id] = list_of_act
    result_string = 'A(' + result_string + ' '
    for li in combined_list_of_states:
        combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
        for ca in combined_acts:
            implies_precedent = 'A(a_' + str(li[0]) + '=' + str(ca[0]) + ' a_' + str(li[1]) + '=' + str(ca[1]) + ')'
            if 'a_' + str(li[0]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[0]))
            if 'a_' + str(li[1]) not in list_of_z3_variables:
                list_of_z3_variables.append('a_' + str(li[1]))
            mul_clause = 'E(prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                list_of_subformula.index(formula_duplicate)) + ' '
            if 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(
                    list_of_subformula.index(formula_duplicate)) not in list_of_z3_variables:
                list_of_z3_variables.append(
                    'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate)))
            combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                   dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))

            if len(combined_succ) == 1:
                first = True
            prod = 'P('
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                if first:
                    prod = 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[0][
                                                                                                                  0:space_in0] + '_' + \
                           cs[1][0:space_in1] + '_' + str(
                        index_phi1) + ') '
                else:
                    prod += 'M(' + str(cs[0][space_in0 + 1:]) + ' ' + str(cs[1][space_in1 + 1:]) + ' ' + 'prob_' + cs[
                                                                                                                       0][
                                                                                                                   0:space_in0] + '_' + \
                            cs[1][0:space_in1] + '_' + str(
                        index_phi1) + ') '
                if 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(
                        index_phi1) not in list_of_z3_variables:
                    list_of_z3_variables.append(
                        'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_phi1))
            if first:
                mul_clause += prod[0:len(prod) - 1] + ')'
                first = False
            else:
                mul_clause += prod[0:len(prod) - 1] + '))'
            # implies_antecedent = '(' + mul_clause + ')'
            implies_antecedent = mul_clause
            state_act_clause = 'I(' + implies_precedent + ' ' + implies_antecedent + ')'
            result_string += state_act_clause + ' '
    result_string = result_string[0:len(result_string) - 1] + ')'
    return result_string


def SemanticsFuture(model, formula_duplicate, combined_list_of_states, n):
    global nos_of_subformula
    print("Starting future")
    phi2 = formula_duplicate.children[0].children[0]
    index_of_phi2 = list_of_subformula.index(phi2)
    index_of_phi = list_of_subformula.index(formula_duplicate)
    Semantics(model, phi2, combined_list_of_states, n)

    dict_of_acts = dict()
    dict_of_acts_tran = dict()
    for state in model.states:
        list_of_act = []
        for action in state.actions:
            list_of_tran = []
            list_of_act.append(action.id)
            for tran in action.transitions:
                list_of_tran.append(str(tran.column) + ' ' + str(tran.value()))
            dict_of_acts_tran[str(state.id) + ' ' + str(action.id)] = list_of_tran
        dict_of_acts[state.id] = list_of_act

    print("In future , staring line 4 of algo")

    for li in combined_list_of_states:
        name1 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2)
        add_to_variable_list(name1)
        name2 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi)
        add_to_variable_list(name2)
        first_implies = Implies(listOfBools[list_of_bools.index(name1)],
                                (listOfReals[list_of_reals.index(name2)] == float(1)))
        nos_of_subformula += 2
        new_prob_const = listOfReals[list_of_reals.index(name2)] >= float(0)
        nos_of_subformula += 1
        s.add(And(first_implies, new_prob_const))
        nos_of_subformula += 1

        combined_acts = list(itertools.product(dict_of_acts[li[0]], dict_of_acts[li[1]]))
        for ca in combined_acts:
            name_0 = 'a_' + str(li[0])
            add_to_variable_list(name_0)
            name_1 = 'a_' + str(li[1])
            add_to_variable_list(name_1)
            implies_precedent = And(Not(listOfBools[list_of_bools.index(name1)]),
                                    And(listOfInts[list_of_ints.index(name_0)] == int(ca[0]),
                                        listOfInts[list_of_ints.index(name_1)] == int(ca[1])))
            nos_of_subformula += 5

            prob_phi = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi)
            add_to_variable_list(prob_phi)
            combined_succ = list(itertools.product(dict_of_acts_tran[str(li[0]) + " " + str(ca[0])],
                                                   dict_of_acts_tran[str(li[1]) + " " + str(ca[1])]))
            first = True
            # one = False
            # if len(combined_succ) == 1:
            #     one = True
            prod_left = None
            prod_right_or = None
            list_of_ors = []
            for cs in combined_succ:
                space_in0 = cs[0].find(' ')
                space_in1 = cs[1].find(' ')
                prob_succ = 'prob_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi)
                add_to_variable_list(prob_succ)
                holds_succ = 'holds_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2)
                add_to_variable_list(holds_succ)
                d_current = 'd_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi2)
                add_to_variable_list(d_current)
                d_succ = 'd_' + cs[0][0:space_in0] + '_' + cs[1][0:space_in1] + '_' + str(index_of_phi2)
                add_to_variable_list(d_succ)
                list_of_ors.append(Or(listOfBools[list_of_bools.index(holds_succ)],
                                      listOfReals[list_of_reals.index(d_current)] > listOfReals[
                                          list_of_reals.index(d_succ)]))
                nos_of_subformula += 2
                if first:
                    prod_left = float(cs[0][space_in0 + 1:]) * float(cs[1][space_in1 + 1:]) * listOfReals[
                        list_of_reals.index(prob_succ)]
                    first = False
                else:
                    prod_left += float(cs[0][space_in0 + 1:]) * float(cs[1][space_in1 + 1:]) * listOfReals[
                        list_of_reals.index(prob_succ)]
                nos_of_subformula += 1
            implies_antecedent_and1 = listOfReals[list_of_reals.index(prob_phi)] == prod_left
            nos_of_subformula += 1
            prod_right_or = Or([par for par in list_of_ors])
            nos_of_subformula += 1
            implies_antecedent_and2 = Implies(listOfReals[list_of_reals.index(prob_phi)] > 0, prod_right_or)
            nos_of_subformula += 1
            implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
            nos_of_subformula += 1
            s.add(Implies(implies_precedent, implies_antecedent))
            nos_of_subformula += 1
    print("Done with future")


def Semantics(model, formula_duplicate, combined_list_of_states, n):
    global nos_of_subformula
    if formula_duplicate.data == 'true':
        print("Starting with true")
        list_of_holds = []
        index_of_phi = list_of_subformula.index(formula_duplicate)
        for i in range(len(combined_list_of_states)):
            name = "holds_" + str(combined_list_of_states[i][0]) + "_" + str(combined_list_of_states[i][1]) + "_" + str(
                index_of_phi)
            add_to_variable_list(name)
            list_of_holds.append(listOfBools[list_of_bools.index(name)])
        s.add(And([par for par in list_of_holds]))
        nos_of_subformula += 1
        list_of_holds.clear()
        print("Done with true")
    elif formula_duplicate.data == 'var':  # var handles the inside varname
        list_of_state_with_ap = []
        ap_name = formula_duplicate.children[0].children[0].value
        ap_state = formula_duplicate.children[0].children[1].value[1]
        labeling = model.labeling
        and_for_yes = []
        and_for_no = []
        index_of_phi = list_of_subformula.index(formula_duplicate)
        for state in model.states:
            zzzzz = labeling.get_labels_of_state(state.id)
            if ap_name in labeling.get_labels_of_state(state.id):
                list_of_state_with_ap.append(state.id)
        for li in combined_list_of_states:
            name = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_of_phi)
            add_to_variable_list(name)
            if li[int(ap_state) - 1] in list_of_state_with_ap:
                and_for_yes.append(listOfBools[list_of_bools.index(name)])
            else:
                and_for_no.append(Not(listOfBools[list_of_bools.index(name)]))
        s.add(And(And([par for par in and_for_yes]), And([par for par in and_for_no])))
        nos_of_subformula += 3
        and_for_yes.clear()
        and_for_no.clear()
        print("Done with var " + str(ap_name))
    elif formula_duplicate.data == 'and_op':
        Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        Semantics(model, formula_duplicate.children[1], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        for li in combined_list_of_states:
            name1 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi)
            add_to_variable_list(name1)
            name2 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1)
            add_to_variable_list(name2)
            name3 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2)
            add_to_variable_list(name3)
            first_and = And(listOfBools[list_of_bools.index(name1)], listOfBools[list_of_bools.index(name2)],
                            listOfBools[list_of_bools.index(name3)])
            nos_of_subformula += 1
            second_and = And(Not(listOfBools[list_of_bools.index(name1)]),
                             Or(Not(listOfBools[list_of_bools.index(name2)]),
                                Not(listOfBools[list_of_bools.index(name3)])))
            nos_of_subformula += 2
            s.add(Or(first_and, second_and))
            nos_of_subformula += 1
        print("Done with and")
    elif formula_duplicate.data == 'neg_op':
        print("Starting with neg")
        Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        list_of_xors = []
        for li in combined_list_of_states:
            name1 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi)
            add_to_variable_list(name1)
            name2 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1)
            add_to_variable_list(name2)
            list_of_xors.append(Xor(listOfBools[list_of_bools.index(name1)], listOfBools[list_of_bools.index(name2)]))
            nos_of_subformula += 1
        s.add(And([par for par in list_of_xors]))
        nos_of_subformula += 1
        print("Done with neg")
    elif formula_duplicate.data == 'less_prob':
        Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        Semantics(model, formula_duplicate.children[1], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        for li in combined_list_of_states:
            name1 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi)
            add_to_variable_list(name1)
            name2 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1)
            add_to_variable_list(name2)
            name3 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2)
            add_to_variable_list(name3)
            and_less = And(listOfBools[list_of_bools.index(name1)],
                           listOfReals[list_of_reals.index(name2)] < listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_greateq = And(Not(listOfBools[list_of_bools.index(name1)]),
                              listOfReals[list_of_reals.index(name2)] >= listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_less, and_greateq))
            nos_of_subformula += 1
        print("Done with less_prob")
    elif formula_duplicate.data == 'greater_prob':
        Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        Semantics(model, formula_duplicate.children[1], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        for li in combined_list_of_states:
            name1 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi)
            add_to_variable_list(name1)
            name2 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1)
            add_to_variable_list(name2)
            name3 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2)
            add_to_variable_list(name3)
            and_great = And(listOfBools[list_of_bools.index(name1)],
                            listOfReals[list_of_reals.index(name2)] > listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_lesseq = And(Not(listOfBools[list_of_bools.index(name1)]),
                             listOfReals[list_of_reals.index(name2)] <= listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_great, and_lesseq))
            nos_of_subformula += 1
        print("Done with greater_prob")
    elif formula_duplicate.data == 'equal_prob':
        Semantics(model, formula_duplicate.children[0], combined_list_of_states, n)
        Semantics(model, formula_duplicate.children[1], combined_list_of_states, n)
        index_phi = list_of_subformula.index(formula_duplicate)
        index_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        for li in combined_list_of_states:
            name1 = 'holds_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi)
            add_to_variable_list(name1)
            name2 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi1)
            add_to_variable_list(name2)
            name3 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_phi2)
            add_to_variable_list(name3)
            and_eq = And(listOfBools[list_of_bools.index(name1)],
                         listOfReals[list_of_reals.index(name2)] == listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_noteq = And(Not(listOfBools[list_of_bools.index(name1)]),
                            listOfReals[list_of_reals.index(name2)] != listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_eq, and_noteq))
            nos_of_subformula += 1
        print("Done with equal_prob")
    elif formula_duplicate.data == 'calc_probability':
        child = formula_duplicate.children[0]
        print("Starting probability")
        if child.data == 'calc_next':
            SemanticsNext(model, formula_duplicate, combined_list_of_states, n)
        elif child.data == 'calc_until_unbounded':
            SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n)
        elif child.data == 'calc_until_bounded':
            SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)
        elif child.data == 'calc_future':
            SemanticsFuture(model, formula_duplicate, combined_list_of_states, n)
        print("Done with probability")
    elif formula_duplicate.data == 'calc_until_unbounded':  # might be redundant
        print("Starting until unbounded")
        SemanticsUnboundedUntil(model, formula_duplicate, combined_list_of_states, n)
    elif formula_duplicate.data == 'calc_until_bounded':
        SemanticsBoundedUntil(model, formula_duplicate, combined_list_of_states, n)
    elif formula_duplicate.data == 'const':
        c = formula_duplicate.children[0].value
        list_of_probs = []
        for li in combined_list_of_states:
            name1 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate))
            add_to_variable_list(name1)
            list_of_probs.append(listOfReals[list_of_reals.index(name1)] == c)
            nos_of_subformula += 1
        s.add(And([par for par in list_of_probs]))
        nos_of_subformula += 1
        print("Done with constant")
    elif formula_duplicate.data in ['add_prob', 'minus_prob', 'mul_prob']:
        left = formula_duplicate.children[0]
        index_left = list_of_subformula.index(left)
        right = formula_duplicate.children[1]
        index_right = list_of_subformula.index(right)
        Semantics(model, left, combined_list_of_states, n)
        Semantics(model, right, combined_list_of_states, n)
        for li in combined_list_of_states:
            name1 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_left)
            add_to_variable_list(name1)
            name2 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(index_right)
            add_to_variable_list(name2)
            name3 = 'prob_' + str(li[0]) + '_' + str(li[1]) + '_' + str(list_of_subformula.index(formula_duplicate))
            add_to_variable_list(name3)
            if formula_duplicate.data == 'add_prob':
                s.add(listOfReals[list_of_reals.index(name3)] == (
                        listOfReals[list_of_reals.index(name1)] + listOfReals[list_of_reals.index(name2)]))
                nos_of_subformula += 2
            elif formula_duplicate.data == 'minus_prob':
                s.add(listOfReals[list_of_reals.index(name3)] == (
                        listOfReals[list_of_reals.index(name1)] - listOfReals[list_of_reals.index(name2)]))
                nos_of_subformula += 2
            elif formula_duplicate.data == 'mul_prob':
                s.add(listOfReals[list_of_reals.index(name3)] == (
                        listOfReals[list_of_reals.index(name1)] * listOfReals[list_of_reals.index(name2)]))
                nos_of_subformula += 2


def Truth(model, formula_initial, combined_list_of_states, n):
    global nos_of_subformula
    list_of_AV = []  # will have the OR, AND according to the quantifier in that index in the formula

    while len(formula_initial.children) > 0 and type(formula_initial.children[0]) == Token:
        if formula_initial.data in ['exist_scheduler', 'forall_scheduler']:
            formula_initial = formula_initial.children[1]
        elif formula_initial.data == 'exist':
            list_of_AV.append('V')
            formula_initial = formula_initial.children[1]
        elif formula_initial.data == 'forall':
            list_of_AV.append('A')
            formula_initial = formula_initial.children[1]
    index_of_phi = list_of_subformula.index(formula_initial)
    list_of_holds = []

    print("Starting big loop in Truth")
    for i in range(len(combined_list_of_states)):
        name = "holds_"
        for j in range(n):
            name += str(combined_list_of_states[i][j]) + "_"
        name += str(index_of_phi)
        add_to_variable_list(name)
        list_of_holds.append(listOfBools[list_of_bools.index(name)])

    list_of_holds_replace = []
    for i in range(n - 1, -1, -1):
        count = -1
        limit = len(list_of_holds)
        quo = 0
        for j in range(limit):
            count += 1
            if count == len(model.states) - 1:
                index = quo * len(model.states)
                if list_of_AV[i] == 'V':
                    list_of_holds_replace.append(Or([par for par in list_of_holds[index:index + count + 1]]))
                elif list_of_AV[i] == 'A':
                    list_of_holds_replace.append(And([par for par in list_of_holds[index:index + count + 1]]))
                count = -1
                quo += 1
        list_of_holds = copy.deepcopy(list_of_holds_replace)
        list_of_holds_replace.clear()
    s.add(list_of_holds[0])
    print("Truth done")


def add_to_subformula_list(formula_phi):  # add as you go any new subformula part as needed
    if formula_phi.data in ['exist_scheduler', 'forall_scheduler', 'exist', 'forall']:
        formula_phi = formula_phi.children[1]
        add_to_subformula_list(formula_phi)
    elif formula_phi.data in ['and_op', 'less_prob', 'greater_prob', 'add_prob', 'minus_prob', 'mul_prob',
                              'calc_until_unbounded', 'equal_prob']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
        left_child = formula_phi.children[0]
        add_to_subformula_list(left_child)
        right_child = formula_phi.children[1]
        add_to_subformula_list(right_child)
    elif formula_phi.data in ['var', 'true', 'const']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
    elif formula_phi.data in ['calc_next', 'neg_op', 'calc_future']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
        add_to_subformula_list(formula_phi.children[0])
    elif formula_phi.data in ['calc_probability']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
        add_to_subformula_list(formula_phi.children[0])
    elif formula_phi.data in ['calc_until_bounded']:
        if formula_phi not in list_of_subformula:
            list_of_subformula.append(formula_phi)
        left_child = formula_phi.children[0]
        add_to_subformula_list(left_child)
        right_child = formula_phi.children[3]
        add_to_subformula_list(right_child)


def add_to_variable_list(name):
    if name[0] == 'h' and name not in list_of_bools:
        list_of_bools.append(name)
        listOfBools.append(Bool(name))
    elif name[0] in ['p', 'd'] and name not in list_of_reals:
        list_of_reals.append(name)
        listOfReals.append(Real(name))
    elif name[0] == 'a' and name not in list_of_ints:
        list_of_ints.append(name)
        listOfInts.append(Int(name))


def check_result():
    starting = time.process_time()
    s.set('timeout', 8000000)  # time is in milliseconds so change it accordingly
    t = s.check()
    z3time = time.process_time() - starting
    if t == sat:
        model = s.model()
        li_h = dict()
        for li in model:
            if li.name()[0] == 'h':
                li_h[li.name()] = model[li]
                print(str(li.name()) + ' = ' + str(model[li]))
        li_p = dict()
        for li in model:
            if li.name()[0] == 'p':
                li_p[li.name()] = model[li]
                print(str(li.name()) + ' = ' + str(model[li]))
        li_d = dict()
        for li in model:
            if li.name()[0] == 'd':
                li_d[li.name()] = model[li]
                print(str(li.name()) + ' = ' + str(model[li]))
        li_a = dict()
        for li in model:
            if li.name()[0] == 'a':
                li_a[li.name()] = model[li]
                print(str(li.name()) + ' = ' + str(model[li]))
    print(s.statistics())
    print("\n")
    print("Number of variables: " + str(len(list_of_ints) + len(list_of_reals) + len(list_of_bools)))
    print("Number of formula checked: " + str(nos_of_subformula))
    print("Time required by z3: " + str(z3time))
    if t.r == 1:
        return True
    elif t.r == -1:
        return False


def main_smt_encoding(model, formula_initial, formula):
    global nos_of_subformula
    list_of_states = []
    starttime = time.process_time()
    for state in model.states:
        list_of_eqns = []
        for action in state.actions:
            name = "a_" + str(state.id)  # + "=" + str(action.id)# a1 means action for state 1
            add_to_variable_list(name)
            list_of_eqns.append(listOfInts[list_of_ints.index(name)] == int(action.id))
        s.add(Or([par for par in list_of_eqns]))
        nos_of_subformula += 1
    n_of_state_quantifier = 0
    formula_duplicate = formula_initial
    while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
        if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
            formula_duplicate = formula_duplicate.children[1]
        elif formula_duplicate.data in ['exist', 'forall']:
            n_of_state_quantifier += 1
            formula_duplicate = formula_duplicate.children[1]
    for state in model.states:
        list_of_states.append(state.id)
    combined_list_of_states = list(itertools.product(list_of_states, repeat=n_of_state_quantifier))
    if formula_initial.data == 'exist_scheduler':
        add_to_subformula_list(formula_initial)
        print("Calling Truth...")
        Truth(model, formula_initial, combined_list_of_states, n_of_state_quantifier)
        print("Calling Semantics...")
        Semantics(model, formula_duplicate, combined_list_of_states, n_of_state_quantifier)
        smt_end_time = time.process_time() - starttime
        print("Time to encode: " + str(smt_end_time))
        print("Checking...")
        if check_result():
            return True
        else:
            return False

    elif formula_initial.data == 'forall_scheduler':
        new_formula = ''
        i = 0

        first = True
        while i < len(formula):
            jjj = formula[i]  # just to see what char we are accessing. Can be removed later.
            if formula[i] == 'E':
                if formula[i + 1] == 'S':
                    new_formula += formula[i] + formula[i + 1]
                    i += 2
                elif formula[i + 1] == ' ':
                    new_formula += 'A' + formula[i + 1]
                    i += 2
            elif formula[i] == 'A':
                if formula[i + 1] == 'S':
                    new_formula += 'E' + formula[i + 1]
                    i += 2
                elif formula[i + 1] == ' ':
                    new_formula += 'E' + formula[i + 1]
                    i += 2
            else:
                if first and formula[i - 1] == ' ' and formula[i - 2] == '.':
                    if formula[i] == '~':  # added this to avoid double negation for exist. Might want to remove the
                        # extra brace around the formula due to previous not.
                        first = False
                        i += 1
                        continue
                    else:
                        new_formula += '~'
                    first = False
                new_formula += formula[i]
                i += 1
        new_parsed_formula = parser.parse(new_formula)
        formula_duplicate = new_parsed_formula
        n_of_state_quantifier = 0
        while len(formula_duplicate.children) > 0 and type(formula_duplicate.children[0]) == Token:
            if formula_duplicate.data in ['exist_scheduler', 'forall_scheduler']:
                formula_duplicate = formula_duplicate.children[1]
            elif formula_duplicate.data in ['exist', 'forall']:
                n_of_state_quantifier += 1
                formula_duplicate = formula_duplicate.children[1]
        add_to_subformula_list(new_parsed_formula)
        print("Calling Truth...")
        Truth(model, new_parsed_formula, combined_list_of_states, n_of_state_quantifier)
        print("Calling Semantics...")
        Semantics(model, formula_duplicate, combined_list_of_states, n_of_state_quantifier)
        smt_end_time = time.process_time() - starttime
        print("Time to encode: " + str(smt_end_time))
        print("Checking...")
        if check_result():
            return False
        else:
            return True


if __name__ == '__main__':
    part_path = sys.argv[1]
    folder_file = part_path.split('_', 1)
    subfolder_file = folder_file[1].split('_', 1)
    path = files._path(folder_file[0], subfolder_file[0], subfolder_file[1] + '.nm')
    print(path)
    initial_prism_program = stormpy.parse_prism_program(path)
    initial_model = stormpy.build_model(initial_prism_program)
    print("No of state: " + str(len(initial_model.states)))
    tar = 0
    for state in initial_model.states:
        for action in state.actions:
            for tran in action.transitions:
                tar += 1
    print("Total transitions: " + str(tar))

    lab = initial_model.labeling
    for state in initial_model.states:
        print(lab.get_labels_of_state(state.id))

    parser = Lark(turtle_grammar)
    formula = sys.argv[2]
    parsed_formula_initial = parser.parse(formula)
    s = Solver()

    result = main_smt_encoding(initial_model, parsed_formula_initial, formula)
    print(result)
