from hyperprob.inputparser import parseArguments
from hyperprob.utility import common
from hyperprob.propertyparser import Hyperproperty
from hyperprob.modelparser import Model, parseListOfModels
from hyperprob.modelchecker import ModelChecker
import traceback


def main():
    try:
        input_args = parseArguments()
        if input_args.checkProperty:
            hyperproperty = Hyperproperty(input_args.hyperString)
            hyperproperty.parseProperty(True)
        if input_args.checkModel:
            parseListOfModels(input_args.modelPaths)
        if not input_args.checkModel and not input_args.checkProperty:
            hyperproperty = Hyperproperty(input_args.hyperString)
            hyperproperty.parseProperty(False)
            list_of_models = parseListOfModels(input_args.modelPaths)
            modelchecker = ModelChecker(list_of_models, hyperproperty)
            modelchecker.modelCheck()
        print("\n")
    except Exception as err:
        common.colourerror("Unexpected error encountered: " + str(err) + "\n" + str(traceback.print_exc()))


if __name__ == "__main__":
    main()
