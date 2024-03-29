from hyperprob.inputparser import parseArguments
from hyperprob.utility import common
from hyperprob.propertyparser import Property
from hyperprob.modelparser import Model
from hyperprob.modelchecker import ModelChecker
import traceback


def main():
    try:
        input_args = parseArguments()
        if input_args.checkProperty:
            hyperproperty = Property(input_args.hyperString)
            hyperproperty.parseProperty(True)
        if input_args.checkModel:
            model = Model(input_args.modelPath)
            model.parseModel(False)
        if not input_args.checkModel and not input_args.checkProperty:
            hyperproperty = Property(input_args.hyperString)
            hyperproperty.parseProperty(False)
            model = Model(input_args.modelPath)
            model.parseModel(True)
            modelchecker = ModelChecker(model, hyperproperty)
            modelchecker.modelCheck()
        print("\n")
    except Exception as err:
        common.colourerror("Unexpected error encountered: " + str(err) + "\n" + str(traceback.print_exc()))


if __name__ == "__main__":
    main()
