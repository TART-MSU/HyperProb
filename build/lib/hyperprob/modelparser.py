import os
import stormpy
from hyperprob.utility import common


def parse_model(model_path):
    try:
        if os.path.exists(model_path):
            initial_prism_program = stormpy.parse_prism_program(model_path)
            initial_model = stormpy.build_model(initial_prism_program)
            common.colourinfo("Total number of states: " + str(len(initial_model.states)), 'green')
        else:
            common.colourother("Model file does not exist!", 'red')
    except IOError as e:
        common.colourerror("I/O error({0}): {1}".format(e.errno, e.strerror), 'red')
    except Exception as err:  # handle other exceptions such as attribute errors
        common.colourerror("Unexpected error opening file at {model_path} is " + repr(err), 'red')
        raise
