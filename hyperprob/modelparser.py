import os
import stormpy
from z3 import RealVal
from hyperprob.utility import common
import traceback


def rebuildExactValueModel(initial_model):
    action_per_state = [int] * len(initial_model.states)
    file_str = ""
    file_str += "builder = stormpy.ExactSparseMatrixBuilder(rows=0, columns=0, entries=0, force_dimensions=False, has_custom_row_grouping=True, row_groups=0)\n"
    count_action = 0
    for state in initial_model.states:
        file_str += "\nbuilder.new_row_group(" + str(count_action) + ")\n"
        for action in state.actions:
            for tran in action.transitions:
                va = RealVal(tran.value()).as_fraction().limit_denominator(10000)
                file_str += "builder.add_next_value(" + str(count_action) + ", "
                file_str += str(tran.column) + ", stormpy.Rational(" + str(
                    va.numerator) + ")/ stormpy.Rational(" + str(
                    va.denominator) + "))\n"
            count_action += 1
        action_per_state[state.id] = len(state.actions)
    file_str += "\ntransition_matrix = builder.build()\n"
    loc = {}
    exec(file_str, {"stormpy": stormpy}, loc)
    # creating new transition matrix
    transition_matrix = loc["transition_matrix"]
    # creating new label model
    state_labeling = initial_model.labeling
    # creating new rewards model
    if len(list(initial_model.reward_models.keys())) > 0:
        reward = {}
        if len(list(initial_model.reward_models.keys())) > 1:
            common.colourother(
                "Multiple reward models not supported. Using rewards model: " + str(
                    list(initial_model.reward_models.keys())[0]))
        reward_models = initial_model.reward_models.get(list(initial_model.reward_models.keys())[0]).state_rewards
        state_rewards = []
        for rew in reward_models:
            rew_fraction = RealVal(rew).as_fraction().limit_denominator(10000)
            state_rewards.append(
                stormpy.Rational(rew_fraction.numerator) / stormpy.Rational(rew_fraction.denominator))
        reward[list(initial_model.reward_models.keys())[0]] = stormpy.storage.SparseExactRewardModel(
            optional_state_reward_vector=state_rewards)
        components = stormpy.SparseExactModelComponents(reward_models=reward, transition_matrix=transition_matrix,
                                                        state_labeling=state_labeling)
    else:
        components = stormpy.SparseExactModelComponents(transition_matrix=transition_matrix,
                                                        state_labeling=state_labeling)
    mdp = stormpy.storage.SparseExactMdp(components)
    return mdp, action_per_state


class Model:
    def __init__(self, model_path):
        self.number_of_actions_at_state = list()
        self.has_rewards = False
        self.model_path = model_path
        self.parsed_model = None

    def parseModel(self):
        common.colourinfo("Parsing model at: " + self.model_path, False)
        try:
            if os.path.exists(self.model_path):
                initial_prism_program = stormpy.parse_prism_program(self.model_path)
                initial_model = stormpy.build_model(initial_prism_program)
                self.parsed_model, self.number_of_actions_at_state = rebuildExactValueModel(initial_model)
                if len(list(self.parsed_model.reward_models.keys())) != 0:
                    self.has_rewards = True

                common.colourinfo("Total number of states: " + str(self.parsed_model.nr_states), False)
                common.colourinfo("Total number of actions: " + str(self.parsed_model.nr_choices), False)
                common.colourinfo("Total number of transitions: " + str(self.parsed_model.nr_transitions), False)
            else:
                common.colourother("Model file does not exist!")
                raise SystemExit(1)
        except IOError as e:
            raise SystemExit("I/O error({0}): {1}".format(e.errno, e.strerror))
        except Exception as err:  # handle other exceptions such as attribute errors
            raise SystemExit("Unexpected error in file {0} is {1}".format(self.model_path, traceback.print_exc()))

    def getListOfStates(self):
        return list(self.parsed_model.states)

    def getNumberOfActions(self):
        return self.getNumberOfActions()

    def hasRewards(self):
        return self.has_rewards


def parseListOfModels(model_list):
    list_of_models = []
    for i in range(len(model_list)):
        list_of_models.append(Model(model_list[i]))
        list_of_models[i].parseModel()

    return list_of_models

