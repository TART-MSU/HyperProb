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
f_pointer = None


def SemanticsUnboundedUntil(model, formula_duplicate, n):

    global nos_of_subformula
    rel_quant = []
    index_of_phi = list_of_subformula.index(formula_duplicate)
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    rel_quant1 = Semantics(model, phi1, n)
    rel_quant.extend(rel_quant1)
    phi2 = formula_duplicate.children[0].children[1]
    index_of_phi2 = list_of_subformula.index(phi2)
    rel_quant2 = Semantics(model, phi2, n)
    rel_quant.extend(rel_quant2)
    r_state = [0 for ind in range(n)]

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

    # n = no.of quantifier, k = no. of state in the model
    index = []
    for j in range(0, n):
        index.append(0)
    i = n - 1
    flag = False
    while i >= 0:
        holds1 = 'holds'
        for ind in range(0, len(r_state)):
            if (ind + 1) in rel_quant1:
                holds1 += "_" + str(r_state[ind])
            else:
                holds1 += "_" + str(0)
        holds1 += "_" + str(index_of_phi1)
        add_to_variable_list(holds1)
        holds2 = 'holds'
        for ind in range(0, len(r_state)):
            if (ind + 1) in rel_quant2:
                holds2 += "_" + str(r_state[ind])
            else:
                holds2 += "_" + str(0)
        holds2 += "_" + str(index_of_phi2)
        add_to_variable_list(holds2)
        prob_phi = 'prob'
        for ind in r_state:
            prob_phi += "_" + str(ind)
        prob_phi += '_' + str(index_of_phi)
        add_to_variable_list(prob_phi)
        new_prob_const = listOfReals[list_of_reals.index(prob_phi)] >= float(0)
        first_implies = And(Implies(listOfBools[list_of_bools.index(holds2)],
                                    (listOfReals[list_of_reals.index(prob_phi)] == float(1))),
                            Implies(And(Not(listOfBools[list_of_bools.index(holds1)]),
                                        Not(listOfBools[list_of_bools.index(holds2)])),
                                    (listOfReals[list_of_reals.index(prob_phi)] == float(0))),
                            new_prob_const)
        nos_of_subformula += 3

        dicts = []
        for l in rel_quant:
            dicts.append(dict_of_acts[r_state[l - 1]])
        combined_acts = list(itertools.product(*dicts))

        for ca in combined_acts:
            name = 'a_' + str(r_state[rel_quant[0] - 1])
            add_to_variable_list(name)
            act_str = listOfInts[list_of_ints.index(name)] == int(ca[0])
            if len(rel_quant) > 1:
                for l in range(2, len(rel_quant) + 1):
                    name = 'a_' + str(rel_quant[l - 1] - 1)
                    add_to_variable_list(name)
                    act_str = And(act_str, listOfInts[list_of_ints.index(name)] == int(ca[l - 1]))

            implies_precedent = And(listOfBools[list_of_bools.index(holds1)],
                                    Not(listOfBools[list_of_bools.index(holds2)]), act_str)
            nos_of_subformula += 2

            dicts = []
            g = 0
            for l in rel_quant:
                dicts.append(dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
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
                for l in range(1, n + 1):
                    if l in rel_quant:
                        space = cs[f].find(' ')
                        succ_state = cs[f - 1][0:space]
                        prob_succ += '_' + succ_state
                        holds_succ += '_' + succ_state
                        d_succ += '_' + succ_state
                        if p_first:
                            prod_left_part = RealVal(cs[f - 1][space + 1:]).as_fraction()
                            p_first = False
                        else:
                            prod_left_part *= RealVal(cs[f - 1][space + 1:]).as_fraction()
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
                add_to_variable_list(prob_succ)
                holds_succ += '_' + str(index_of_phi2)
                add_to_variable_list(holds_succ)

                d_current += '_' + str(index_of_phi2)
                add_to_variable_list(d_current)
                d_succ += '_' + str(index_of_phi2)
                add_to_variable_list(d_succ)
                prod_left_part *= listOfReals[list_of_reals.index(prob_succ)]

                if first:
                    prod_left = prod_left_part
                    first = False
                else:
                    prod_left += prod_left_part
                nos_of_subformula += 1

                list_of_ors.append(Or(listOfBools[list_of_bools.index(holds_succ)],
                                      listOfReals[list_of_reals.index(d_current)] > listOfReals[
                                          list_of_reals.index(d_succ)]))

                nos_of_subformula += 2

            implies_antecedent_and1 = listOfReals[list_of_reals.index(prob_phi)] == prod_left
            nos_of_subformula += 1
            prod_right_or = Or([par for par in list_of_ors])
            nos_of_subformula += 1
            implies_antecedent_and2 = Implies(listOfReals[list_of_reals.index(prob_phi)] > 0, prod_right_or)
            nos_of_subformula += 1
            implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
            nos_of_subformula += 1
            s.add(And(first_implies, Implies(implies_precedent, implies_antecedent)))
            nos_of_subformula += 1

        while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
            r_state[i] = 0
            index[i] = 0
            i = i - 1

        if i >= 0:
            index[i] = index[i] + 1
            r_state[i] = index[i]

    return rel_quant


def SemanticsBoundedUntil(model, formula_duplicate, n):
    global nos_of_subformula
    rel_quant = []
    index_of_phi = list_of_subformula.index(formula_duplicate)
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    phi2 = formula_duplicate.children[0].children[1]
    index_of_phi2 = list_of_subformula.index(phi2)
    r_state = [0 for ind in range(n)]
    k1 = int(formula_duplicate.children[1].value)
    k2 = int(formula_duplicate.children[2].value)

    if k2 == 0:
        rel_quant1 = Semantics(model, phi1, n)
        rel_quant2 = Semantics(model, phi2, n)
        rel_quant.extend(rel_quant1)
        rel_quant.extend(rel_quant2)
        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            name1 = 'prob'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    name2 += "_" + str(r_state[ind])
                else:
                    name2 += "_" + str(0)
            name2 += '_' + str(index_of_phi2)
            add_to_variable_list(name2)

            eq1 = Implies(listOfBools[list_of_bools.index(name2)], listOfReals[list_of_reals.index(name1)] == float(1))
            eq2 = Implies(Not(listOfBools[list_of_bools.index(name2)]),
                          listOfReals[list_of_reals.index(name1)] == float(0))
            nos_of_subformula += 2
            s.add(And(eq1, eq2))
            nos_of_subformula += 1

            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and (k) >= 0 and index[k] < (len(
                        model.states) - 1):  # special case when the current quantifier is relevant but it has reached the end of model states. SO we increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]

    elif k1 == 0:
        left, k_1, k_2, right = formula_duplicate.children
        par = copy.deepcopy(k_2)
        par.value = str(int(k_2.value) - 1)  # k2.value will have changed value but it won't show up in the formula
        # tree, hence it'll appear to be the same formula as formula_duplicate
        formula_duplicate.children[
            2] = par  # so now formula_duplicate is basically phi1_until[0,k2-1]_phi2. Don't be confused!!
        list_of_subformula.append(formula_duplicate)
        index_of_replaced = len(
            list_of_subformula) - 1  # forcefully inserting new replaced formula, will obviously be inserted at the end
        rel_quant.extend(SemanticsBoundedUntil(model, formula_duplicate, n))

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

        # n = no.of quantifier, k = no. of state in the model
        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            holds1 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) == 1:  # try to remove this hard-coded value later
                    holds1 += "_" + str(r_state[ind])
                else:
                    holds1 += "_" + str(0)
            holds1 += "_" + str(index_of_phi1)
            add_to_variable_list(holds1)
            holds2 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) == 2:  # try to remove this hard-coded value later
                    holds2 += "_" + str(r_state[ind])
                else:
                    holds2 += "_" + str(0)
            holds2 += "_" + str(index_of_phi2)
            add_to_variable_list(holds2)
            prob_phi = 'prob'
            for ind in r_state:
                prob_phi += "_" + str(ind)
            prob_phi += '_' + str(index_of_phi)
            add_to_variable_list(prob_phi)

            new_prob_const = listOfReals[list_of_reals.index(prob_phi)] >= float(0)
            first_implies = And(Implies(listOfBools[list_of_bools.index(holds2)],
                                        (listOfReals[list_of_reals.index(prob_phi)] == float(1))),
                                Implies(And(Not(listOfBools[list_of_bools.index(holds1)]),
                                            Not(listOfBools[list_of_bools.index(holds2)])),
                                        (listOfReals[list_of_reals.index(prob_phi)] == float(0))),
                                new_prob_const)
            nos_of_subformula += 3
            s.add(first_implies)

            dicts = []
            for l in rel_quant:
                dicts.append(dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                name = 'a_' + str(r_state[rel_quant[0] - 1])
                add_to_variable_list(name)
                act_str = listOfInts[list_of_ints.index(name)] == int(ca[0])
                if len(rel_quant) > 1:
                    for l in range(2, len(rel_quant) + 1):
                        name = 'a_' + str(rel_quant[l - 1] - 1)
                        add_to_variable_list(name)
                        act_str = And(act_str, listOfInts[list_of_ints.index(name)] == int(ca[l - 1]))

                implies_precedent = And(listOfBools[list_of_bools.index(holds1)],
                                        Not(listOfBools[list_of_bools.index(holds2)]), act_str)
                nos_of_subformula += 2

                dicts = []
                g = 0
                for l in rel_quant:
                    dicts.append(dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                    g += 1
                combined_succ = list(itertools.product(*dicts))

                first = True
                prod_left = None

                for cs in combined_succ:
                    f = 0
                    prob_succ = 'prob'
                    p_first = True
                    prod_left_part = None
                    for l in range(1, n + 1):
                        if l in rel_quant:
                            space = cs[f].find(' ')
                            succ_state = cs[f - 1][0:space]
                            prob_succ += '_' + succ_state
                            if p_first:
                                prod_left_part = RealVal(cs[f - 1][space + 1:]).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(cs[f - 1][space + 1:]).as_fraction()
                            f += 1

                        else:
                            prob_succ += '_' + str(0)
                            if p_first:
                                prod_left_part = RealVal(1).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(1).as_fraction()

                    prob_succ += '_' + str(index_of_replaced)
                    add_to_variable_list(prob_succ)
                    prod_left_part *= listOfReals[list_of_reals.index(prob_succ)]

                    if first:
                        prod_left = prod_left_part
                        first = False
                    else:
                        prod_left += prod_left_part
                    nos_of_subformula += 1

                implies_antecedent_and = listOfReals[list_of_reals.index(prob_phi)] == prod_left
                nos_of_subformula += 1
                s.add(Implies(implies_precedent, implies_antecedent_and))
                nos_of_subformula += 1

            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                i = i - 1

            if i >= 0:
                index[i] = index[i] + 1
                r_state[i] = index[i]

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
        rel_quant.extend(SemanticsBoundedUntil(model, formula_duplicate, n))

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

        # n = no.of quantifier, k = no. of state in the model
        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            holds1 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) == 1:  # try to remove this hard-coded value later
                    holds1 += "_" + str(r_state[ind])
                else:
                    holds1 += "_" + str(0)
            holds1 += "_" + str(index_of_phi1)
            add_to_variable_list(holds1)
            prob_phi = 'prob'
            for ind in r_state:
                prob_phi += "_" + str(ind)
            prob_phi += '_' + str(index_of_phi)
            add_to_variable_list(prob_phi)

            first_implies = Implies(Not(listOfBools[list_of_bools.index(holds1)]),
                                    (listOfReals[list_of_reals.index(prob_phi)] == float(0)))
            nos_of_subformula += 1
            s.add(first_implies)

            dicts = []
            for l in rel_quant:
                dicts.append(dict_of_acts[r_state[l - 1]])
            combined_acts = list(itertools.product(*dicts))

            for ca in combined_acts:
                name = 'a_' + str(r_state[rel_quant[0] - 1])
                add_to_variable_list(name)
                act_str = listOfInts[list_of_ints.index(name)] == int(ca[0])
                if len(rel_quant) > 1:
                    for l in range(2, len(rel_quant) + 1):
                        name = 'a_' + str(rel_quant[l - 1] - 1)
                        add_to_variable_list(name)
                        act_str = And(act_str, listOfInts[list_of_ints.index(name)] == int(ca[l - 1]))

                implies_precedent = And(listOfBools[list_of_bools.index(holds1)], act_str)
                nos_of_subformula += 2

                dicts = []
                g = 0
                for l in rel_quant:
                    dicts.append(dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                    g += 1
                combined_succ = list(itertools.product(*dicts))

                first = True
                prod_left = None

                for cs in combined_succ:
                    f = 0
                    prob_succ = 'prob'
                    p_first = True
                    prod_left_part = None
                    for l in range(1, n + 1):
                        if l in rel_quant:
                            space = cs[f].find(' ')
                            succ_state = cs[f - 1][0:space]
                            prob_succ += '_' + succ_state
                            if p_first:
                                prod_left_part = RealVal(cs[f - 1][space + 1:]).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(cs[f - 1][space + 1:]).as_fraction()
                            f += 1

                        else:
                            prob_succ += '_' + str(0)
                            if p_first:
                                prod_left_part = RealVal(1).as_fraction()
                                p_first = False
                            else:
                                prod_left_part *= RealVal(1).as_fraction()

                    prob_succ += '_' + str(index_of_replaced)
                    add_to_variable_list(prob_succ)
                    prod_left_part *= listOfReals[list_of_reals.index(prob_succ)]

                    if first:
                        prod_left = prod_left_part
                        first = False
                    else:
                        prod_left += prod_left_part
                    nos_of_subformula += 1

                implies_antecedent_and = listOfReals[list_of_reals.index(prob_phi)] == prod_left
                nos_of_subformula += 1
                s.add(Implies(implies_precedent, implies_antecedent_and))
                nos_of_subformula += 1

            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                i = i - 1

            if i >= 0:
                index[i] = index[i] + 1
                r_state[i] = index[i]

    return rel_quant


def SemanticsNext(model, formula_duplicate, n):
    global nos_of_subformula
    rel_quant = []
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    index_of_phi = list_of_subformula.index(formula_duplicate)
    rel_quant.extend(Semantics(model, phi1, n))
    r_state = [0 for ind in range(n)]

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

    # n = no.of quantifier, k = no. of state in the model
    # holdsToInt has type real to avoid added complexity of multiplying integer to real values
    index = []
    for j in range(0, n):
        index.append(0)
    i = n - 1
    flag = False
    while i >= 0:
        holds1 = 'holds'
        str_r_state = ""
        for ind in r_state:
            str_r_state += "_" + str(ind)
        holds1 += str_r_state + "_" + str(index_of_phi1)
        add_to_variable_list(holds1)
        holdsToInt1 = 'holdsToInt' + str_r_state + "_" + str(index_of_phi1)
        add_to_variable_list(holdsToInt1)
        prob_phi = 'prob' + str_r_state + "_" + str(index_of_phi)
        add_to_variable_list(prob_phi)
        first_and = Or(
            And(listOfReals[list_of_reals.index(holdsToInt1)] == float(1), listOfBools[list_of_bools.index(holds1)]),
            And(listOfReals[list_of_reals.index(holdsToInt1)] == float(0),
                Not(listOfBools[list_of_bools.index(holds1)])))
        nos_of_subformula += 3
        s.add(first_and)
        dicts = []
        for l in rel_quant:
            dicts.append(dict_of_acts[r_state[l - 1]])
        combined_acts = list(itertools.product(*dicts))

        for ca in combined_acts:
            name = 'a_' + str(r_state[rel_quant[0] - 1])
            add_to_variable_list(name)
            act_str = listOfInts[list_of_ints.index(name)] == int(ca[0])
            if len(rel_quant) > 1:
                for l in range(2, len(rel_quant) + 1):
                    name = 'a_' + str(rel_quant[l - 1] - 1)
                    add_to_variable_list(name)
                    act_str = And(act_str, listOfInts[list_of_ints.index(name)] == int(ca[l - 1]))

            implies_precedent = act_str
            nos_of_subformula += 1

            dicts = []
            g = 0
            for l in rel_quant:
                dicts.append(dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                g += 1
            combined_succ = list(itertools.product(*dicts))

            first = True
            prod_left = None

            for cs in combined_succ:
                f = 0
                holdsToInt_succ = 'holdsToInt'
                p_first = True
                prod_left_part = None
                for l in range(1, n + 1):
                    if l in rel_quant:
                        space = cs[f].find(' ')
                        succ_state = cs[f - 1][0:space]
                        holdsToInt_succ += '_' + succ_state
                        if p_first:
                            prod_left_part = RealVal(cs[f - 1][space + 1:]).as_fraction()
                            p_first = False
                        else:
                            prod_left_part *= RealVal(cs[f - 1][space + 1:]).as_fraction()
                        f += 1

                    else:
                        holdsToInt_succ += '_' + str(0)
                        if p_first:
                            prod_left_part = RealVal(1).as_fraction()
                            p_first = False
                        else:
                            prod_left_part *= RealVal(1).as_fraction()

                holdsToInt_succ += '_' + str(index_of_phi1)
                add_to_variable_list(holdsToInt_succ)
                prod_left_part *= listOfReals[list_of_reals.index(holdsToInt_succ)]

                if first:
                    prod_left = prod_left_part
                    first = False
                else:
                    prod_left += prod_left_part
                nos_of_subformula += 1

            implies_antecedent_and = listOfReals[list_of_reals.index(prob_phi)] == prod_left
            nos_of_subformula += 1
            s.add(Implies(implies_precedent, implies_antecedent_and))
            nos_of_subformula += 1

        while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
            r_state[i] = 0
            index[i] = 0
            i = i - 1

        if i >= 0:
            index[i] = index[i] + 1
            r_state[i] = index[i]

    return rel_quant


def SemanticsFuture(model, formula_duplicate, n):
    global nos_of_subformula
    rel_quant = []
    phi1 = formula_duplicate.children[0].children[0]
    index_of_phi1 = list_of_subformula.index(phi1)
    index_of_phi = list_of_subformula.index(formula_duplicate)
    rel_quant.extend(Semantics(model, phi1, n))
    r_state = [0 for ind in range(n)]

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


    # actions thing          n = no.of quantifier, k = no. of state in the model
    index = []
    for j in range(0, n):
        index.append(0)
    i = n - 1
    flag = False
    while i >= 0:
        holds1 = 'holds'
        str_r_state = ""
        for ind in r_state:
            str_r_state += "_" + str(ind)
        holds1 += str_r_state + "_" + str(index_of_phi1)
        add_to_variable_list(holds1)
        prob_phi = 'prob'
        prob_phi += str_r_state + '_' + str(index_of_phi)
        add_to_variable_list(prob_phi)
        new_prob_const = listOfReals[list_of_reals.index(prob_phi)] >= float(0)
        first_implies = And(Implies(listOfBools[list_of_bools.index(holds1)],
                                    (listOfReals[list_of_reals.index(prob_phi)] == float(1))), new_prob_const)
        nos_of_subformula += 1

        dicts = []
        for l in rel_quant:
            dicts.append(dict_of_acts[r_state[l - 1]])
        combined_acts = list(itertools.product(*dicts))

        for ca in combined_acts:
            name = 'a_' + str(r_state[rel_quant[0] - 1])
            add_to_variable_list(name)
            act_str = listOfInts[list_of_ints.index(name)] == int(ca[0])
            if len(rel_quant) > 1:
                for l in range(2, len(rel_quant) + 1):
                    name = 'a_' + str(rel_quant[l - 1] - 1)
                    add_to_variable_list(name)
                    act_str = And(act_str, listOfInts[list_of_ints.index(name)] == int(ca[l - 1]))

            implies_precedent = And(Not(listOfBools[list_of_bools.index(holds1)]), act_str)
            nos_of_subformula += 2

            dicts = []
            g = 0
            for l in rel_quant:
                dicts.append(dict_of_acts_tran[str(r_state[l - 1]) + " " + str(ca[g])])
                g += 1
            combined_succ = list(itertools.product(*dicts))

            first = True
            prod_left = None
            list_of_ors = []

            for cs in combined_succ:
                f = 0
                prob_succ = 'prob'
                # prob_succ1 = 'prob'
                holds_succ = 'holds'
                d_current = 'd'
                d_succ = 'd'
                p_first = True
                prod_left_part = None
                for l in range(1, n + 1):
                    if l in rel_quant:
                        space = cs[f].find(' ')
                        succ_state = cs[f - 1][0:space]
                        prob_succ += '_' + succ_state
                        holds_succ += '_' + succ_state
                        d_succ += '_' + succ_state
                        if p_first:
                            prod_left_part = RealVal(cs[f - 1][space + 1:]).as_fraction()
                            p_first = False
                        else:
                            prod_left_part *= RealVal(cs[f - 1][space + 1:]).as_fraction()
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
                add_to_variable_list(prob_succ)
                holds_succ += '_' + str(index_of_phi1)
                add_to_variable_list(holds_succ)
                d_current += '_' + str(index_of_phi1)
                add_to_variable_list(d_current)
                d_succ += '_' + str(index_of_phi1)
                add_to_variable_list(d_succ)
                prod_left_part *= listOfReals[list_of_reals.index(prob_succ)]

                if first:
                    prod_left = prod_left_part
                    first = False
                else:
                    prod_left += prod_left_part
                nos_of_subformula += 1

                list_of_ors.append(Or(listOfBools[list_of_bools.index(holds_succ)],
                                      listOfReals[list_of_reals.index(d_current)] > listOfReals[
                                          list_of_reals.index(d_succ)]))

                nos_of_subformula += 2

            implies_antecedent_and1 = listOfReals[list_of_reals.index(prob_phi)] == prod_left
            nos_of_subformula += 1
            prod_right_or = Or([par for par in list_of_ors])
            nos_of_subformula += 1
            implies_antecedent_and2 = Implies(listOfReals[list_of_reals.index(prob_phi)] > 0, prod_right_or)
            nos_of_subformula += 1
            implies_antecedent = And(implies_antecedent_and1, implies_antecedent_and2)
            nos_of_subformula += 1
            s.add(And(first_implies, Implies(implies_precedent, implies_antecedent)))
            nos_of_subformula += 1

        while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
            r_state[i] = 0
            index[i] = 0
            i = i - 1

        if i >= 0:
            index[i] = index[i] + 1
            r_state[i] = index[i]

    return rel_quant


def Semantics(model, formula_duplicate, n):
    global nos_of_subformula
    r_state = [0 for ind in range(n)]
    rel_quant = []
    if formula_duplicate.data == 'true':
        index_of_phi = list_of_subformula.index(formula_duplicate)
        name = "holds"
        for ind in r_state:
            name += "_" + str(ind)
        name += '_' + str(index_of_phi)
        add_to_variable_list(name)
        s.add(listOfBools[list_of_bools.index(name)])
        nos_of_subformula += 1
        return rel_quant

    elif formula_duplicate.data == 'var':  # var handles the inside varname
        ap_name = formula_duplicate.children[0].children[0].value
        relevant_quantifier = int(formula_duplicate.children[0].children[1].value[1])
        labeling = model.labeling
        rel_quant.append(relevant_quantifier)  # n = no.of quantifier, k = no. of state in the model
        and_for_yes = set()
        and_for_no = set()
        list_of_state_with_ap = []
        index = []
        index_of_phi = list_of_subformula.index(formula_duplicate)
        for state in model.states:
            if ap_name in labeling.get_labels_of_state(state.id):
                list_of_state_with_ap.append(state.id)
        for j in range(0, n):
            index.append(0)
        i = n - 1
        while i >= 0:
            name = 'holds'
            for ind in r_state:
                name += "_" + str(ind)
            name += '_' + str(index_of_phi)
            add_to_variable_list(name)
            if r_state[relevant_quantifier - 1] in list_of_state_with_ap:
                and_for_yes.add(listOfBools[list_of_bools.index(name)])
            else:
                and_for_no.add(Not(listOfBools[list_of_bools.index(name)]))
            while i >= 0 and (index[i] == (len(model.states) - 1) or (relevant_quantifier - 1) != i):
                r_state[i] = 0
                index[i] = 0
                i = i - 1
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        s.add(And(And([par for par in list(and_for_yes)]), And([par for par in list(and_for_no)])))
        nos_of_subformula += 3
        and_for_yes.clear()
        and_for_no.clear()
        index.clear()
        return rel_quant

    elif formula_duplicate.data == 'and_op':
        rel_quant1 = Semantics(model, formula_duplicate.children[0], n)
        rel_quant.extend(rel_quant1)
        rel_quant2 = Semantics(model, formula_duplicate.children[1], n)
        rel_quant.extend(rel_quant2)
        tmp_set = set(rel_quant)
        rel_quant = list(tmp_set)
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_of_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_of_phi2 = list_of_subformula.index(formula_duplicate.children[1])
        # n = no.of quantifier, k = no. of state in the model
        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            name1 = 'holds'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    name2 += "_" + str(r_state[ind])
                else:
                    name2 += "_" + str(0)
            name2 += '_' + str(index_of_phi1)
            add_to_variable_list(name2)
            name3 = 'holds'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    name3 += "_" + str(r_state[ind])
                else:
                    name3 += "_" + str(0)
            name3 += '_' + str(index_of_phi2)
            add_to_variable_list(name3)
            first_and = And(listOfBools[list_of_bools.index(name1)], listOfBools[list_of_bools.index(name2)],
                            listOfBools[list_of_bools.index(name3)])
            nos_of_subformula += 1
            second_and = And(Not(listOfBools[list_of_bools.index(name1)]),
                             Or(Not(listOfBools[list_of_bools.index(name2)]),
                                Not(listOfBools[list_of_bools.index(name3)])))
            nos_of_subformula += 1
            s.add(Or(first_and, second_and))
            nos_of_subformula += 1
            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and k >= 0 and index[k] < (len(model.states) - 1):  # special case
                    # when the current quantifier is relevant but it has reached the end of model states. So we
                    # increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        return rel_quant

    elif formula_duplicate.data == 'neg_op':
        rel_quant.extend(Semantics(model, formula_duplicate.children[0], n))
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_of_phi1 = list_of_subformula.index(formula_duplicate.children[0])

        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            name1 = 'holds'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'holds'
            for ind in r_state:
                name2 += "_" + str(ind)
            name2 += '_' + str(index_of_phi1)
            add_to_variable_list(name2)
            s.add(Xor(listOfBools[list_of_bools.index(name1)], listOfBools[list_of_bools.index(name2)]))
            nos_of_subformula += 1
            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and (k) >= 0 and index[k] < (len(
                        model.states) - 1):  # special case when the current quantifier is relevant but it has reached the end of model states. SO we increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        return rel_quant

    elif formula_duplicate.data == 'less_prob':
        rel_quant1 = Semantics(model, formula_duplicate.children[0], n)
        rel_quant2 = Semantics(model, formula_duplicate.children[1], n)
        rel_quant.extend(rel_quant1)
        rel_quant.extend(rel_quant2)
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_of_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_of_phi2 = list_of_subformula.index(formula_duplicate.children[1])

        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            name1 = 'holds'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    name2 += "_" + str(r_state[ind])
                else:
                    name2 += "_" + str(0)
            name2 += '_' + str(index_of_phi1)
            add_to_variable_list(name2)
            name3 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    name3 += "_" + str(r_state[ind])
                else:
                    name3 += "_" + str(0)
            name3 += '_' + str(index_of_phi2)
            add_to_variable_list(name3)
            and_eq = And(listOfBools[list_of_bools.index(name1)],
                         listOfReals[list_of_reals.index(name2)] < listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_not_eq = And(Not(listOfBools[list_of_bools.index(name1)]),
                             listOfReals[list_of_reals.index(name2)] >= listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_eq, and_not_eq))
            nos_of_subformula += 1

            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and (k) >= 0 and index[k] < (len(
                        model.states) - 1):  # special case when the current quantifier is relevant but it has reached the end of model states. SO we increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        return rel_quant

    elif formula_duplicate.data == 'greater_prob':
        rel_quant1 = Semantics(model, formula_duplicate.children[0], n)
        rel_quant2 = Semantics(model, formula_duplicate.children[1], n)
        rel_quant.extend(rel_quant1)
        rel_quant.extend(rel_quant2)
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_of_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_of_phi2 = list_of_subformula.index(formula_duplicate.children[1])

        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            name1 = 'holds'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    name2 += "_" + str(r_state[ind])
                else:
                    name2 += "_" + str(0)
            name2 += '_' + str(index_of_phi1)
            add_to_variable_list(name2)
            name3 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    name3 += "_" + str(r_state[ind])
                else:
                    name3 += "_" + str(0)
            name3 += '_' + str(index_of_phi2)
            add_to_variable_list(name3)
            and_eq = And(listOfBools[list_of_bools.index(name1)],
                         listOfReals[list_of_reals.index(name2)] > listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_not_eq = And(Not(listOfBools[list_of_bools.index(name1)]),
                             listOfReals[list_of_reals.index(name2)] <= listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_eq, and_not_eq))
            nos_of_subformula += 1

            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and (k) >= 0 and index[k] < (len(
                        model.states) - 1):  # special case when the current quantifier is relevant but it has reached the end of model states. SO we increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        return rel_quant
    elif formula_duplicate.data == 'equal_prob':
        rel_quant1 = Semantics(model, formula_duplicate.children[0], n)
        rel_quant2 = Semantics(model, formula_duplicate.children[1], n)
        rel_quant.extend(rel_quant1)
        rel_quant.extend(rel_quant2)
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_of_phi1 = list_of_subformula.index(formula_duplicate.children[0])
        index_of_phi2 = list_of_subformula.index(formula_duplicate.children[1])

        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            name1 = 'holds'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    name2 += "_" + str(r_state[ind])
                else:
                    name2 += "_" + str(0)
            name2 += '_' + str(index_of_phi1)
            add_to_variable_list(name2)
            name3 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    name3 += "_" + str(r_state[ind])
                else:
                    name3 += "_" + str(0)
            name3 += '_' + str(index_of_phi2)
            add_to_variable_list(name3)
            and_eq = And(listOfBools[list_of_bools.index(name1)],
                         listOfReals[list_of_reals.index(name2)] == listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            and_not_eq = And(Not(listOfBools[list_of_bools.index(name1)]),
                             listOfReals[list_of_reals.index(name2)] != listOfReals[list_of_reals.index(name3)])
            nos_of_subformula += 1
            s.add(Or(and_eq, and_not_eq))
            nos_of_subformula += 1

            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and (k) >= 0 and index[k] < (len(
                        model.states) - 1):  # special case when the current quantifier is relevant but it has reached the end of model states. SO we increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        return rel_quant

    elif formula_duplicate.data == 'calc_probability':
        child = formula_duplicate.children[0]
        if child.data == 'calc_next':
            SemanticsNext(model, formula_duplicate, n)
        elif child.data == 'calc_until_unbounded':
            SemanticsUnboundedUntil(model, formula_duplicate, n)
        elif child.data == 'calc_until_bounded':
            SemanticsBoundedUntil(model, formula_duplicate, n)
        elif child.data == 'calc_future':
            rel_quant.extend(SemanticsFuture(model, formula_duplicate, n))
        return rel_quant

    elif formula_duplicate.data == 'const':
        c = formula_duplicate.children[0].value
        index_of_phi = list_of_subformula.index(formula_duplicate)
        name = "prob"
        for ind in r_state:
            name += "_" + str(ind)
        name += '_' + str(index_of_phi)
        add_to_variable_list(name)
        s.add(listOfReals[list_of_reals.index(name)] == c)
        nos_of_subformula += 1
        return rel_quant

    elif formula_duplicate.data in ['add_prob', 'minus_prob', 'mul_prob']:
        rel_quant1 = Semantics(model, formula_duplicate.children[0], n)
        rel_quant2 = Semantics(model, formula_duplicate.children[1], n)
        rel_quant.extend(rel_quant1)
        rel_quant.extend(rel_quant2)
        index_of_phi = list_of_subformula.index(formula_duplicate)
        index_left = list_of_subformula.index(formula_duplicate.children[0])
        index_right = list_of_subformula.index(formula_duplicate.children[1])

        index = []
        for j in range(0, n):
            index.append(0)
        i = n - 1
        flag = False
        while i >= 0:
            name1 = 'prob'
            for ind in r_state:
                name1 += "_" + str(ind)
            name1 += '_' + str(index_of_phi)
            add_to_variable_list(name1)
            name2 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant1:
                    name2 += "_" + str(r_state[ind])
                else:
                    name2 += "_" + str(0)
            name2 += '_' + str(index_left)
            add_to_variable_list(name2)
            name3 = 'prob'
            for ind in range(0, len(r_state)):
                if (ind + 1) in rel_quant2:
                    name3 += "_" + str(r_state[ind])
                else:
                    name3 += "_" + str(0)
            name3 += '_' + str(index_right)
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
            else:
                print("Unexpected operator. Exiting")
                return 0

            while i >= 0 and (index[i] == (len(model.states) - 1) or (i + 1) not in rel_quant):
                r_state[i] = 0
                index[i] = 0
                k = i - 1
                flago = False
                while k >= 0:
                    if k + 1 in rel_quant:
                        flago = True
                        break
                    else:
                        k -= 1
                if flago and (i + 1) in rel_quant and (k) >= 0 and index[k] < (len(
                        model.states) - 1):  # special case when the current quantifier is relevant but it has reached the end of model states. SO we increase the previous quantifier value and continue with current quantifier
                    index[i - 1] += 1
                    r_state[i - 1] += 1
                    flag = True
                else:
                    i = i - 1
            if flag:
                flag = False
                continue
            if i >= 0:
                index[i] += 1
                r_state[i] = index[i]
        return rel_quant


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

    print("Encoded quantifiers...")


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
    if name[0] == 'h' and not name.startswith('holdsToInt') and name not in list_of_bools:
        list_of_bools.append(name)
        listOfBools.append(Bool(name))
    elif name[0] in ['p', 'd'] or name.startswith('holdsToInt') and name not in list_of_reals:
        list_of_reals.append(name)
        listOfReals.append(Real(name))
    elif name[0] == 'a' and name not in list_of_ints:
        list_of_ints.append(name)
        listOfInts.append(Int(name))


def check_result(mdp_model):
    starting = time.process_time()
    t = s.check()
    z3time = time.process_time() - starting
    li_a = None
    if t == sat:
        model = s.model()
        li_a = [None] * len(mdp_model.states)
        for li in model:
            if li.name()[0] == 'a':
                li_a[int(li.name()[2:])] = model[li]
    if t.r == 1:
        return True, li_a, s.statistics(), z3time
    elif t.r == -1:
        return False, li_a, s.statistics(), z3time



def main_smt_encoding(model, formula_initial, formula):
    global nos_of_subformula
    list_of_states = []
    starttime = time.process_time()
    for state in model.states:
        list_of_eqns = []
        name = "a_" + str(state.id)  # a_1 means action for state 1
        add_to_variable_list(name)
        for action in state.actions:
            list_of_eqns.append(listOfInts[list_of_ints.index(name)] == int(action.id))
        if len(list_of_eqns) == 1:
            s.add(list_of_eqns[0])
        else:
            s.add(Or([par for par in list_of_eqns]))
        nos_of_subformula += 1
    print("Encoded actions in the MDP...")
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
        Truth(model, formula_initial, combined_list_of_states, n_of_state_quantifier)

        Semantics(model, formula_duplicate, n_of_state_quantifier)
        print("Encoded non-quantified formula...")
        smt_end_time = time.process_time() - starttime

        print("Time to encode in seconds: " + str(round(smt_end_time,2)))
        print("Checking...")
        res, li_a, statis, z3time = check_result(model)
        if res:
            print("The property HOLDS!\n")
            print("\nThe actions at the corresponding states of the witness are:")
            for i in range(0, len(model.states)):
                print("State " + str(i) + ' = ' + str(li_a[i]))
            print("\n")
        else:
            print("The property DOES NOT hold!")

        print("z3 statistics:")
        print(statis)
        print("\nTime to encode in seconds: " + str(round(smt_end_time, 2)))
        print("Time required by z3 in seconds: " + str(round(z3time, 2)))
        print("\n")
        print("Number of variables: " + str(len(list_of_ints) + len(list_of_reals) + len(list_of_bools)))
        print("Number of formula checked: " + str(nos_of_subformula))

    elif formula_initial.data == 'forall_scheduler':
        new_formula = ''
        i = 0
        first = True
        while i < len(formula):

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
                    if formula[i] == '~':
                        # added this to avoid double negation for exist. Might want to remove the extra brace around
                        # the formula due to previous not.
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
        Truth(model, new_parsed_formula, combined_list_of_states, n_of_state_quantifier)
        Semantics(model, formula_duplicate, n_of_state_quantifier)
        print("Encoded non-quantified formula...")
        smt_end_time = time.process_time() - starttime

        print("Time to encode in seconds: " + str(round(smt_end_time, 2)))
        print("Checking...")
        res, li_a, statis, z3time = check_result(model)
        if res:
            print("The property DOES NOT hold!")
            print("\nThe actions at the corresponding states of a counterexample are:")
            for i in range(0, len(model.states)):
                print("State " + str(i) + ' = ' + str(li_a[i]))
            print("\n")
        else:
            print("The property HOLDS!")

        print("z3 statistics:")
        print(statis)
        print("\nTime to encode in seconds: " + str(round(smt_end_time, 2)))
        print("Time required by z3 in seconds: " + str(round(z3time, 2)))
        print("\n")
        print("Number of variables: " + str(len(list_of_ints) + len(list_of_reals) + len(list_of_bools)))
        print("Number of formula checked: " + str(nos_of_subformula))




def rebuild_exact_value_model(initial_mod):
    file_str = ""
    file_str += "builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, force_dimensions=False, has_custom_row_grouping=True, row_groups=0)\n"
    count_action = 0
    for state in initial_mod.states:
        file_str += "\nbuilder.new_row_group(" + str(count_action) + ")\n"
        for action in state.actions:
            for tran in action.transitions:
                va = RealVal(tran.value()).as_fraction().limit_denominator(10000)
                file_str += "builder.add_next_value(" + str(count_action) + ", "
                file_str += str(tran.column) + ", stormpy.Rational(" + str(va.numerator) + ")/ stormpy.Rational(" + str(
                    va.denominator) + "))\n"
            count_action += 1
    file_str += "\ntransition_matrix = builder.build()\n"
    loc = {}
    exec(file_str, {"stormpy": stormpy}, loc)
    transition_matrix = loc["transition_matrix"]
    state_labeling = initial_mod.labeling
    components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix, state_labeling=state_labeling)
    mdp = stormpy.storage.SparseExactMdp(components)
    return mdp


if __name__ == '__main__':
    part_path = sys.argv[1]

    last_occurrence = part_path.rfind('/')
    file_name = part_path[last_occurrence + 1:]
    if last_occurrence == -1:
        folder_path = ''
    else:
        folder_path = part_path[:last_occurrence]
    path = files._path(folder_path, file_name)
    print("Model file is located at: " + path)

    initial_prism_program = stormpy.parse_prism_program(path)
    initial_model = stormpy.build_model(initial_prism_program)
    print("Total number of states: " + str(len(initial_model.states)))
    tar = 0
    ac = 0

    initial_model = rebuild_exact_value_model(initial_model)

    for state in initial_model.states:
        for action in state.actions:
            ac += 1
            for tran in action.transitions:
                tar += 1

    print("Total number of transitions: " + str(tar))
    print("Total number of actions: " + str(ac) + '\n')

    parser = Lark(turtle_grammar)
    formula = sys.argv[2]
    parsed_formula_initial = parser.parse(formula)
    s = Solver()

    main_smt_encoding(initial_model, parsed_formula_initial, formula)


