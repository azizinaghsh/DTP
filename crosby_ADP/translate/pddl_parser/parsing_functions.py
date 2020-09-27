# -*- coding: utf-8 -*-

from __future__ import print_function

import sys

import graph
import pddl
from pddl import pddl_types


def parse_typed_list(alist, only_variables=False,
                     constructor=pddl.TypedObject,
                     default_type="object"):
    result = []
    while alist:
        try:
            separator_position = alist.index("-")
        except ValueError:
            items = alist
            _type = default_type
            alist = []
        else:
            items = alist[:separator_position]
            _type = alist[separator_position + 1]
            alist = alist[separator_position + 2:]
        for item in items:
            assert not only_variables or item.startswith("?"), \
                "Expected item to be a variable: %s in (%s)" % (
                    item, " ".join(items))
            entry = constructor(item, _type)
            result.append(entry)
    return result


def set_supertypes(type_list):
    # TODO: This is a two-stage construction, which is perhaps
    # not a great idea. Might need more thought in the future.
    type_name_to_type = {}
    child_types = []
    for type in type_list:
        type.supertype_names = []
        type_name_to_type[type.name] = type
        if type.basetype_name:
            child_types.append((type.name, type.basetype_name))
    for (desc_name, anc_name) in graph.transitive_closure(child_types):
        type_name_to_type[desc_name].supertype_names.append(anc_name)


def parse_predicate(alist):
    name = alist[0]
    arguments = parse_typed_list(alist[1:], only_variables=True)
    return pddl.Predicate(name, arguments)


def parse_function(alist, type_name):
    name = alist[0]
    arguments = parse_typed_list(alist[1:])
    return pddl.Function(name, arguments, type_name)


def parse_condition(alist, type_dict, predicate_dict):
    condition = parse_condition_aux(alist, False, type_dict, predicate_dict)
    # TODO: The next line doesn't appear to do anything good,
    # since uniquify_variables doesn't modify the condition in place.
    # Conditions in actions or axioms are uniquified elsewhere, but
    # it looks like goal conditions are never uniquified at all
    # (which would be a bug).
    condition.uniquify_variables({})
    return condition


def parse_condition_aux(alist, negated, type_dict, predicate_dict):
    """Parse a PDDL condition. The condition is translated into NNF on the fly."""
    tag = alist[0]
    if tag in ("and", "or", "not", "imply"):
        args = alist[1:]
        if tag == "imply":
            assert len(args) == 2
        if tag == "not":
            assert len(args) == 1
            return parse_condition_aux(
                args[0], not negated, type_dict, predicate_dict)
    elif tag in ("forall", "exists"):
        parameters = parse_typed_list(alist[1])
        args = alist[2:]
        assert len(args) == 1
    else:
        return parse_literal(alist, type_dict, predicate_dict, negated=negated)

    if tag == "imply":
        parts = [parse_condition_aux(
            args[0], not negated, type_dict, predicate_dict),
            parse_condition_aux(
                args[1], negated, type_dict, predicate_dict)]
        tag = "or"
    else:
        parts = [parse_condition_aux(part, negated, type_dict, predicate_dict)
                 for part in args]

    if tag == "and" and not negated or tag == "or" and negated:
        return pddl.Conjunction(parts)
    elif tag == "or" and not negated or tag == "and" and negated:
        return pddl.Disjunction(parts)
    elif tag == "forall" and not negated or tag == "exists" and negated:
        return pddl.UniversalCondition(parameters, parts)
    elif tag == "exists" and not negated or tag == "forall" and negated:
        return pddl.ExistentialCondition(parameters, parts)


def parse_literal(alist, type_dict, predicate_dict, negated=False):
    if alist[0] == "not":
        assert len(alist) == 2
        alist = alist[1]
        negated = not negated

    pred_id, arity = _get_predicate_id_and_arity(
        alist[0], type_dict, predicate_dict)

    if arity != len(alist) - 1:
        raise SystemExit("predicate used with wrong arity: (%s)"
                         % " ".join(alist))

    if negated:
        return pddl.NegatedAtom(pred_id, alist[1:])
    else:
        return pddl.Atom(pred_id, alist[1:])


SEEN_WARNING_TYPE_PREDICATE_NAME_CLASH = False


def _get_predicate_id_and_arity(text, type_dict, predicate_dict):
    global SEEN_WARNING_TYPE_PREDICATE_NAME_CLASH

    the_type = type_dict.get(text)
    the_predicate = predicate_dict.get(text)

    if the_type is None and the_predicate is None:
        raise SystemExit("Undeclared predicate: %s" % text)
    elif the_predicate is not None:
        if the_type is not None and not SEEN_WARNING_TYPE_PREDICATE_NAME_CLASH:
            msg = ("Warning: name clash between type and predicate %r.\n"
                   "Interpreting as predicate in conditions.") % text
            print(msg, file=sys.stderr)
            SEEN_WARNING_TYPE_PREDICATE_NAME_CLASH = True
        return the_predicate.name, the_predicate.get_arity()
    else:
        assert the_type is not None
        return the_type.get_predicate_name(), 1


def parse_effects(alist, result, type_dict, predicate_dict):
    """Parse a PDDL effect (any combination of simple, conjunctive, conditional, and universal)."""
    tmp_effect = parse_effect(alist, type_dict, predicate_dict)
    normalized = tmp_effect.normalize()
    cost_eff, rest_effect = normalized.extract_cost()
    add_effect(rest_effect, result)
    if cost_eff:
        return cost_eff.effect
    else:
        return None


def add_effect(tmp_effect, result):
    """tmp_effect has the following structure:
       [ConjunctiveEffect] [UniversalEffect] [ConditionalEffect] SimpleEffect."""

    if isinstance(tmp_effect, pddl.ConjunctiveEffect):
        for effect in tmp_effect.effects:
            add_effect(effect, result)
        return
    else:
        parameters = []
        condition = pddl.Truth()
        if isinstance(tmp_effect, pddl.UniversalEffect):
            parameters = tmp_effect.parameters
            if isinstance(tmp_effect.effect, pddl.ConditionalEffect):
                condition = tmp_effect.effect.condition
                assert isinstance(tmp_effect.effect.effect, pddl.SimpleEffect)
                effect = tmp_effect.effect.effect.effect
            else:
                assert isinstance(tmp_effect.effect, pddl.SimpleEffect)
                effect = tmp_effect.effect.effect
        elif isinstance(tmp_effect, pddl.ConditionalEffect):
            condition = tmp_effect.condition
            assert isinstance(tmp_effect.effect, pddl.SimpleEffect)
            effect = tmp_effect.effect.effect
        else:
            assert isinstance(tmp_effect, pddl.SimpleEffect)
            effect = tmp_effect.effect
        assert isinstance(effect, pddl.Literal)
        # Check for contradictory effects
        condition = condition.simplified()
        new_effect = pddl.Effect(parameters, condition, effect)
        contradiction = pddl.Effect(parameters, condition, effect.negate())
        if not contradiction in result:
            result.append(new_effect)
        else:
            # We use add-after-delete semantics, keep positive effect
            if isinstance(contradiction.literal, pddl.NegatedAtom):
                result.remove(contradiction)
                result.append(new_effect)


def parse_effect(alist, type_dict, predicate_dict):
    tag = alist[0]
    if tag == "and":
        return pddl.ConjunctiveEffect(
            [parse_effect(eff, type_dict, predicate_dict) for eff in alist[1:]])
    elif tag == "forall":
        assert len(alist) == 3
        parameters = parse_typed_list(alist[1])
        effect = parse_effect(alist[2], type_dict, predicate_dict)
        return pddl.UniversalEffect(parameters, effect)
    elif tag == "when":
        assert len(alist) == 3
        condition = parse_condition(
            alist[1], type_dict, predicate_dict)
        effect = parse_effect(alist[2], type_dict, predicate_dict)
        return pddl.ConditionalEffect(condition, effect)
    elif tag == "increase":
        assert len(alist) == 3
        assert alist[1] == ['total-cost']
        assignment = parse_assignment(alist)
        return pddl.CostEffect(assignment)
    else:
        # We pass in {} instead of type_dict here because types must
        # be static predicates, so cannot be the target of an effect.
        return pddl.SimpleEffect(parse_literal(alist, {}, predicate_dict))


def parse_expression(exp):
    if isinstance(exp, list):
        functionsymbol = exp[0]
        return pddl.PrimitiveNumericExpression(functionsymbol, exp[1:])
    elif exp.replace(".", "").isdigit():
        return pddl.NumericConstant(float(exp))
    elif exp[0] == "-":
        raise ValueError("Negative numbers are not supported")
    else:
        return pddl.PrimitiveNumericExpression(exp, [])


def parse_assignment(alist):
    assert len(alist) == 3
    op = alist[0]
    head = parse_expression(alist[1])
    exp = parse_expression(alist[2])
    if op == "=":
        return pddl.Assign(head, exp)
    elif op == "increase":
        return pddl.Increase(head, exp)
    else:
        assert False, "Assignment operator not supported."


def parse_action(alist, type_dict, predicate_dict):
    iterator = iter(alist)
    action_tag = next(iterator)
    assert action_tag == ":action" or action_tag == ':action'
    name = next(iterator)
    parameters_tag_opt = next(iterator)
    if parameters_tag_opt == ":parameters":
        parameters = parse_typed_list(next(iterator),
                                      only_variables=True)
        precondition_tag_opt = next(iterator)
    else:
        parameters = []
        precondition_tag_opt = parameters_tag_opt
    if precondition_tag_opt == ":precondition":
        precondition_list = next(iterator)
        if not precondition_list:
            # Note that :precondition () is allowed in PDDL.
            precondition = pddl.Conjunction([])
        else:
            precondition = parse_condition(
                precondition_list, type_dict, predicate_dict)
            precondition = precondition.simplified()
        effect_tag = next(iterator)
    else:
        precondition = pddl.Conjunction([])
        effect_tag = precondition_tag_opt
    assert effect_tag == ":effect"
    effect_list = next(iterator)
    eff = []
    if effect_list:
        try:
            cost = parse_effects(
                effect_list, eff, type_dict, predicate_dict)
        except ValueError as e:
            raise SystemExit("Error in Action %s\nReason: %s." % (name, e))
    next(iterator) == ":duration"
    duration = next(iterator)
    if len(duration[2]) == 1:
        duration = pddl.NumericConstant(int(duration[2]))
    else:
        duration = pddl.f_expression.PrimitiveNumericExpression(duration[2][0], duration[2][1:])
    for rest in iterator:
        assert False, rest
    if eff:
        return pddl.Action(name, parameters, len(parameters),
                           precondition, eff, cost, duration)
    else:
        return None


def parse_axiom(alist, type_dict, predicate_dict):
    assert len(alist) == 3
    assert alist[0] == ":derived"
    predicate = parse_predicate(alist[1])
    condition = parse_condition(
        alist[2], type_dict, predicate_dict)
    return pddl.Axiom(predicate.name, predicate.arguments,
                      len(predicate.arguments), condition)


'''frees_dict_stored_value = [con[2][0]]
is_free_predicate = [con[2][0] + '-free']
free_con_eff = [con[2][0] + '-free']
for par in con[2][1:]:
    free_con_eff.append(par)
    is_free_predicate.extend([par, '-', param_types[par]])
    frees_dict_stored_value.extend([param_types[par]])
if parse_predicate(is_free_predicate) not in the_predicates:
    the_predicates.append(parse_predicate(is_free_predicate))
if con[2][0] not in frees.keys():
    frees[con[2][0]] = frees_dict_stored_value
if not is_effect and is_start:
    _con_eff.append(free_con_eff)
if is_start:
    _frees.append(['not', free_con_eff])
if not is_start:
    _frees.append(free_con_eff)'''
import copy


def append_precondition(action, precondition):
    # action: pddl.Action
    if isinstance(action.precondition, pddl.Conjunction):
        action.precondition.parts += (copy.deepcopy(precondition),)
    else:
        action.precondition = pddl.Conjunction([action.precondition, copy.deepcopy(precondition)])
    return


def append_effect_for_overall(action, is_free_name, overall, predicate_dict):
    # action: pddl.Action
    # is_free: pddl.Atom
    overall_a_list = [is_free_name]
    overall_a_list.extend(list(overall.args))
    eff_out = []
    add_effect(pddl.SimpleEffect(parse_literal(overall_a_list, {}, predicate_dict, action.name.endswith('start'))), eff_out)
    action.effects.extend(eff_out)


def construct_free(act, overall):
    free_element = [overall.predicate]
    for arg in overall.args:
        for par in act.parameters:
            if par.name == arg:
                free_element.append(par.type_name)
    return free_element


def unify_par_name(a1, a2, free_cond, violating_eff):
    for i in range(len(free_cond.args)):
        if free_cond.args[i][0] == '?':
            for par in a1.parameters:
                if par.name == free_cond.args[i]:
                    did_unify = False
                    for par2 in a2.parameters:
                        if par2.type_name == par.type_name and par2.name in violating_eff.literal.args:
                            new_args = list(free_cond.args);
                            new_args[i] = par2.name
                            free_cond.args = tuple(new_args)
                            did_unify = True
                    if not did_unify:
                        return False
    return True


def add_overall_to_start_and_end(overalls, actions, predicates, predicate_dict):
    for a1 in actions:
        if a1.name in overalls.keys():
            for overall in overalls[a1.name]:
                skip = False
                if a1.name.endswith('start'):
                    for eff in a1.effects:
                        if eff.literal.predicate == overall.predicate and eff.literal.negated ^ overall.predicate.negated:
                            skip = True
                    if not skip:
                        append_precondition(a1, overall)


def process_is_free_propositions(overalls, actions, predicates, predicate_dict):
    frees = dict()
    for a1 in actions:
        # a1: pddl.Action
        if a1.name in overalls.keys():
            for overall in overalls[a1.name]:
                # overall: pddl.Atom
                is_free_predicate_name = ''
                if overall.negated:
                    is_free_predicate_name = 'not-'
                is_free_predicate_name += overall.predicate + '-free'
                if overall.predicate not in frees.keys():
                    frees[overall.predicate] = construct_free(a1, overall)
                is_free_predicate = copy.deepcopy(predicate_dict[overall.predicate])
                is_free_predicate.name = is_free_predicate_name
                cond = copy.deepcopy(overall)
                cond.predicate = is_free_predicate_name
                if cond.negated:
                    cond = cond.negate()
                append_precondition(a1, cond)
                if is_free_predicate not in predicates:
                    predicates.append(is_free_predicate)
                    predicate_dict[is_free_predicate.name] = is_free_predicate
                    for a2 in actions:
                        # a2: pddl.Action
                        for eff in a2.effects:
                            # eff: pddl.Effect
                            if eff.literal.predicate == overall.predicate and eff.literal.negated ^ overall.negated:
                                if unify_par_name(a1, a2, cond, eff):
                                    append_precondition(a2, cond)
                append_effect_for_overall(a1, is_free_predicate_name, overall, predicate_dict)

    return frees


def POPF_compress(actions):
    # check end conditions - start adds = null
    # check starts adds + end deletes = null
    # check del start and conditions end = null
    return


def merge_actions(actions, can_be_compressed=None):
    new_actions = []
    for i in range(0, len(actions) - 1, 2):
        act_start = actions[i]
        act_end = actions[i + 1]
        assert act_start.name.endswith('start') and act_end.name.endswith('end') and act_start.name[0:len(
            act_start.name) - 5] == act_end.name[0:len(act_end.name) - 3]
        if can_be_compressed is not None and not can_be_compressed[act_start.name]:
            new_actions.append(act_start)
            new_actions.append(act_end)
            continue
        eff_size = len(act_start.effects)
        j = 0
        while j < eff_size:
            eff_s = act_start.effects[j]
            for eff_e in act_end.effects:
                if eff_e.literal.key == eff_s.literal.key:
                    if eff_e.literal.negated ^ eff_s.literal.negated:
                        act_start.effects.remove(eff_s)
                        eff_size = eff_size - 1
                        j = j - 1
                    act_end.effects.remove(eff_e)
                    break
            j = j + 1
        act_start.effects.extend(act_end.effects)
    new_actions.extend([act for act in actions if
                        (act.name.endswith('start') and (can_be_compressed is None or can_be_compressed[act.name]))])
    return new_actions


def condition_depends_on_effect(action, cond, eff, depend_list, axiom_list, should_negate):
    if cond.predicate == eff.literal.predicate and \
            ((cond.negated == eff.literal.negated and not should_negate) or \
             (cond.negated ^ eff.literal.negated and should_negate)):
        if not should_negate:
            if action not in depend_list:
                depend_list.append(action)
                axiom_list.append(cond)
            # if cond not in axiom_list:
            # axiom_list.append(cond)
        return True


def action_depends_on_other(action, other_action, depend_list, axiom_list, should_negate):
    does_depend = False
    for eff in other_action.effects:
        if isinstance(action.precondition, pddl.Conjunction):
            for cond in action.precondition.parts:
                if condition_depends_on_effect(action, cond, eff, depend_list, axiom_list, should_negate):
                    does_depend = True
        else:
            if condition_depends_on_effect(action, action.precondition, eff, depend_list, axiom_list, should_negate):
                does_depend = True
    return does_depend


def analyze_compressible(actions):
    start_actions = []
    end_actions = []
    for act in actions:
        if act.name.endswith('start'):
            start_actions.append(act)
        else:
            end_actions.append(act)
    dependents = []
    dependents_axiom = []
    for start_act in start_actions:
        act_dependents = []
        act_dependents_axiom = []
        dependents.append(act_dependents)
        dependents_axiom.append(act_dependents_axiom)
        for act in actions:
            if act.name == start_act.name:
                continue
            if start_act.name[0:len(start_act.name) - 5] == act.name[0:len(act.name) - 3]:
                continue
            action_depends_on_other(act, start_act, act_dependents, act_dependents_axiom, False)

    can_be_compressed = dict()
    for act in start_actions:
        can_be_compressed[act.name] = True
    can_be_compressed_relaxed = can_be_compressed.copy()

    for i in range(len(start_actions)):
        start_act = start_actions[i]
        end_act = end_actions[i]
        for dependant in dependents[i]:
            if dependant.name == end_act.name:
                continue
            if can_be_compressed[start_act.name]:
                can_be_compressed[start_act.name] = not action_depends_on_other(dependant, end_act, None, None, True)
        for axiom in dependents_axiom[i]:
            for eff in end_act.effects:
                if axiom.predicate == eff.literal.predicate and axiom.negated ^ eff.literal.negated and (
                        can_be_compressed_relaxed[start_act.name]):
                    can_be_compressed_relaxed[start_act.name] = False
    return can_be_compressed


def parse_task(domain_pddl, task_pddl):
    domain_name, domain_requirements, types, type_dict, constants, predicates, predicate_dict, functions, actions, \
    axioms, overalls = parse_domain_pddl(domain_pddl)
    frees = dict()
    frees = process_is_free_propositions(overalls, actions, predicates, predicate_dict)
    #add_overall_to_start_and_end(overalls, actions, predicates, predicate_dict)
    can_be_compressed = analyze_compressible(actions)
    actions = merge_actions(actions, can_be_compressed)
    task_name, task_domain_name, task_requirements, objects, init, goal, use_metric = parse_task_pddl(task_pddl,
                                                                                                      type_dict,
                                                                                                      predicate_dict,
                                                                                                      frees)

    assert domain_name == task_domain_name
    requirements = pddl.Requirements(sorted(set(
        domain_requirements.requirements +
        task_requirements.requirements)))
    objects = constants + objects
    check_for_duplicates(
        [o.name for o in objects],
        errmsg="error: duplicate object %r",
        finalmsg="please check :constants and :objects definitions")
    init += [pddl.Atom("=", (obj.name, obj.name)) for obj in objects]

    return pddl.Task(
        domain_name, task_name, requirements, types, objects,
        predicates, functions, init, goal, actions, axioms, use_metric)


def parse_domain_pddl(domain_pddl):
    iterator = iter(domain_pddl)

    define_tag = next(iterator)
    assert define_tag == "define"
    domain_line = next(iterator)
    assert domain_line[0] == "domain" and len(domain_line) == 2
    yield domain_line[1]

    ## We allow an arbitrary order of the requirement, types, constants,
    ## predicates and functions specification. The PDDL BNF is more strict on
    ## this, so we print a warning if it is violated.
    requirements = pddl.Requirements([":strips"])
    the_types = [pddl.Type("object")]
    constants, the_predicates, the_functions = [], [], []
    correct_order = [":requirements", ":types", ":constants", ":predicates",
                     ":functions"]
    seen_fields = []
    first_action = None
    for opt in iterator:
        field = opt[0]
        if field not in correct_order:
            first_action = opt
            break
        if field in seen_fields:
            raise SystemExit("Error in domain specification\n" +
                             "Reason: two '%s' specifications." % field)
        if (seen_fields and
                correct_order.index(seen_fields[-1]) > correct_order.index(field)):
            msg = "\nWarning: %s specification not allowed here (cf. PDDL BNF)" % field
            print(msg, file=sys.stderr)
        seen_fields.append(field)
        if field == ":requirements":
            requirements = pddl.Requirements(opt[1:])
        elif field == ":types":
            the_types.extend(parse_typed_list(
                opt[1:], constructor=pddl.Type))
        elif field == ":constants":
            constants = parse_typed_list(opt[1:])
        elif field == ":predicates":
            the_predicates = [parse_predicate(entry)
                              for entry in opt[1:]]
            the_predicates += [pddl.Predicate("=",
                                              [pddl.TypedObject("?x", "object"),
                                               pddl.TypedObject("?y", "object")])]
        elif field == ":functions":
            the_functions = parse_typed_list(
                opt[1:],
                constructor=parse_function,
                default_type="number")
    set_supertypes(the_types)
    yield requirements

    entries = []
    if first_action is not None:
        entries.append(first_action)
    entries.extend(iterator)

    the_axioms = []
    the_actions = []

    start_entries = []
    end_entries = []
    divided_entries = []

    overalls = dict()

    yield the_types
    type_dict = dict((type.name, type) for type in the_types)
    yield type_dict

    predicate_dict = dict((pred.name, pred) for pred in the_predicates)

    # divide each action into a start and end
    index = 0
    for entry in entries:
        start_entries.append(get_start_end_action(entry, True, type_dict, predicate_dict, the_predicates, overalls))
        end_entries.append(get_start_end_action(entry, False, type_dict, predicate_dict, the_predicates, overalls))
        divided_entries.append(start_entries[index])
        divided_entries.append(end_entries[index])
        index = index + 1

    '''for entry in divided_entries:
        for free in frees.keys():
            deletes_overall(entry, frees[free])'''

    yield constants
    yield the_predicates
    predicate_dict = dict((pred.name, pred) for pred in the_predicates)
    yield predicate_dict
    yield the_functions

    for entry in divided_entries:
        if entry[0] == ":derived":
            axiom = parse_axiom(entry, type_dict, predicate_dict)
            the_axioms.append(axiom)
        else:
            action = parse_action(entry, type_dict, predicate_dict)
            if action is not None:
                the_actions.append(action)

    yield the_actions
    yield the_axioms
    yield overalls


def get_param_types(entry):
    index = entry.index(':parameters')
    assert index >= 0
    param_types = dict();
    i = 0
    for p in entry[index + 1]:
        if p[0] == '?':
            param_types[p] = entry[index + 1][i + 2]
        i += 1
    return param_types


def deletes_overall(entry, overall):
    param_types = get_param_types(entry)
    index = entry.index(':effect')
    assert index >= 0
    index += 1
    cond_index = entry.index(':precondition')
    assert cond_index >= 0
    cond_index += 1
    for e in entry[index][1:]:
        if e[0] == 'not':
            e_types = ['not', []]
            args = [];
            for p in e[1]:
                if p[0] == '?':
                    e_types[1].append(param_types[p])
                    args.append(p)
                else:
                    e_types[1].append(p)
            if e_types == ['not', overall]:
                precond = [overall[0] + '-free']
                precond.extend(args)
                entry[cond_index].append(precond)


def add_start_end_eff_con(eff_con, action_started_predicate, action_ended_predicate, is_start, is_effect, type_dict,
                          predicate_dict, actions_name, overalls):
    _con_eff = ['and']
    if eff_con[0] == 'and':
        cons = eff_con[1:]
    else:
        cons = ['and', eff_con[0:]]

    for con in cons:
        if (con[1] == 'start' and is_start) or (con[1] == 'end' and not is_start) or con[1] == 'all':
            _con_eff.append(con[2])
        if con[1] == 'all':
            if actions_name not in overalls.keys():
                overalls[actions_name] = []
            overalls[actions_name].append(parse_condition(con[2], type_dict, predicate_dict))
            '''frees_dict_stored_value = [con[2][0]]
            is_free_predicate = [con[2][0] + '-free']
            free_con_eff = [con[2][0] + '-free']
            for par in con[2][1:]:
                free_con_eff.append(par)
                is_free_predicate.extend([par, '-', param_types[par]])
                frees_dict_stored_value.extend([param_types[par]])
            if parse_predicate(is_free_predicate) not in the_predicates:
                the_predicates.append(parse_predicate(is_free_predicate))
            if con[2][0] not in frees.keys():
                frees[con[2][0]] = frees_dict_stored_value
            if not is_effect and is_start:
                _con_eff.append(free_con_eff)
            if is_start:
                _frees.append(['not', free_con_eff])
            if not is_start:
                _frees.append(free_con_eff)'''

    if is_effect:
        if not is_start:
            _con_eff.append(['not', action_started_predicate])
            #_con_eff.append(action_ended_predicate)
        else:
            _con_eff.append(action_started_predicate)
            #_con_eff.append(['not', action_ended_predicate])
    elif not is_start:
        _con_eff.append(action_started_predicate)

    return _con_eff


def get_start_end_action(entry, is_start, types_dict, predicates_dict, the_predicates, overalls):
    it = iter(entry)
    _entry = []
    tag = next(it)
    if tag == ':action':
        return entry
    assert tag == ':durative-action'
    _entry.append(':action')
    name = next(it)
    action_name = name
    if is_start:
        action_name += '-start'
    else:
        action_name += '-end'
    _entry.append(action_name)
    tag = next(it)
    assert tag == ':parameters'
    _entry.append(tag)
    params = next(it)
    _entry.append(params)
    tag = next(it)
    assert tag == ':duration'
    duration = next(it)

    tag = next(it)
    assert tag == ':condition'
    _entry.append(':precondition')
    conditions = next(it)
    started_predicate = [name + '-started']
    started_effect = [name + '-started']
    started_effect.extend([s for s in params if s.startswith('?')])
    started_predicate.extend(params)
    ended_predicate = [name + '-ended']
    ended_effect = [name + '-ended']
    ended_effect.extend([s for s in params if s.startswith('?')])
    ended_predicate.extend(params)

    # add start and end predicates only once
    if is_start:
        the_predicates.append(parse_predicate(started_predicate))
        #the_predicates.append(parse_predicate(ended_predicate))

    res = add_start_end_eff_con(conditions, started_effect, ended_effect, is_start, False, types_dict,
                                predicates_dict, action_name, overalls)
    _entry.append(res)
    tag = next(it)
    assert tag == ':effect'
    _entry.append(tag)
    conditions = next(it)
    eff = add_start_end_eff_con(conditions, started_effect, ended_effect, is_start, True, types_dict,
                                predicates_dict, action_name, overalls)
    _entry.append(eff)

    _entry.append(':duration')
    _entry.append(duration)
    return _entry


def add_all_frees_to_init(free, type_dict, objects_dict, arg_index, assignment, assignments):
    if arg_index == len(free):
        return assignment
    if arg_index == 0:
        assignment = [free[0] + '-free']
        arg_index += 1
    children = get_child_types(type_dict, free[arg_index])
    children.append(free[arg_index])
    objects = []
    for c in children:
        if c in objects_dict.keys():
            objects.extend(objects_dict[c])
    for var in objects:
        if len(assignment) <= arg_index:
            assignment.append('')
        assignment[arg_index] = var
        final_assignment = add_all_frees_to_init(free, type_dict, objects_dict, arg_index + 1, assignment, assignments)
        if (final_assignment != None):
            copy_assign = []
            for s in final_assignment:
                copy_assign.append(s)
            assignments.append(copy_assign)
    return


def get_child_types(type_dict, parent_type):
    children = []
    for _ in range(len(type_dict)):
        for type1 in type_dict:
            if parent_type in type_dict[type1].supertype_names and type1 not in children:
                children.append(type1)
            else:
                for type2 in type_dict[type1].supertype_names:
                    if type2 in children and type1 not in children:
                        children.append(type1)
    return children


def parse_task_pddl(task_pddl, type_dict, predicate_dict, frees):
    iterator = iter(task_pddl)
    define_tag = next(iterator)
    assert define_tag == "define"
    problem_line = next(iterator)
    assert problem_line[0] == "problem" and len(problem_line) == 2
    yield problem_line[1]
    domain_line = next(iterator)
    assert domain_line[0] == ":domain" and len(domain_line) == 2
    yield domain_line[1]

    requirements_opt = next(iterator)
    if requirements_opt[0] == ":requirements":
        requirements = requirements_opt[1:]
        objects_opt = next(iterator)
    else:
        requirements = []
        objects_opt = requirements_opt
    yield pddl.Requirements(requirements)

    if objects_opt[0] == ":objects":
        yield parse_typed_list(objects_opt[1:])
        init = next(iterator)
    else:
        yield []
        init = objects_opt

    objects_dict = dict()
    index = 0
    first_var_index = 1
    for o in objects_opt:
        if o == '-':
            if objects_opt[index + 1] not in objects_dict.keys():
                objects_dict[objects_opt[index + 1]] = []
            objects_dict[objects_opt[index + 1]].extend(objects_opt[first_var_index:index])
            first_var_index = index + 2
        index += 1
    assignments = []
    for free in frees.values():
        free_assignments = []
        add_all_frees_to_init(free, type_dict, objects_dict, 0, [], free_assignments)
        assignments.extend(free_assignments)
    init.extend(assignments)
    assert init[0] == ":init"
    initial = []
    initial_true = set()
    initial_false = set()
    initial_assignments = dict()
    for fact in init[1:]:
        if fact[0] == "=":
            try:
                assignment = parse_assignment(fact)
            except ValueError as e:
                raise SystemExit("Error in initial state specification\n" +
                                 "Reason: %s." % e)
            if not isinstance(assignment.expression,
                              pddl.NumericConstant):
                raise SystemExit("Illegal assignment in initial state " +
                                 "specification:\n%s" % assignment)
            if assignment.fluent in initial_assignments:
                prev = initial_assignments[assignment.fluent]
                if assignment.expression == prev.expression:
                    print("Warning: %s is specified twice" % assignment,
                          "in initial state specification")
                else:
                    raise SystemExit("Error in initial state specification\n" +
                                     "Reason: conflicting assignment for " +
                                     "%s." % assignment.fluent)
            else:
                initial_assignments[assignment.fluent] = assignment
                initial.append(assignment)
        elif fact[0] == "not":
            atom = pddl.Atom(fact[1][0], fact[1][1:])
            check_atom_consistency(atom, initial_false, initial_true, False)
            initial_false.add(atom)
        else:
            atom = pddl.Atom(fact[0], fact[1:])
            check_atom_consistency(atom, initial_true, initial_false)
            initial_true.add(atom)
    initial.extend(initial_true)
    yield initial

    goal = next(iterator)
    assert goal[0] == ":goal" and len(goal) == 2
    yield parse_condition(goal[1], type_dict, predicate_dict)

    use_metric = False
    for entry in iterator:
        if entry[0] == ":metric":
            if entry[1] == "minimize" and entry[2][0] == "total-cost":
                use_metric = True
            # else:
            # assert False, "Unknown metric."
    yield use_metric

    for entry in iterator:
        assert False, entry


def check_atom_consistency(atom, same_truth_value, other_truth_value, atom_is_true=True):
    if atom in other_truth_value:
        raise SystemExit("Error in initial state specification\n" +
                         "Reason: %s is true and false." % atom)
    if atom in same_truth_value:
        if not atom_is_true:
            atom = atom.negate()
        print("Warning: %s is specified twice in initial state specification" % atom)


def check_for_duplicates(elements, errmsg, finalmsg):
    seen = set()
    errors = []
    for element in elements:
        if element in seen:
            errors.append(errmsg % element)
        else:
            seen.add(element)
    if errors:
        raise SystemExit("\n".join(errors) + "\n" + finalmsg)
