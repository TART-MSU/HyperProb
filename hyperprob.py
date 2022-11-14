from hyperprob.inputparser import parseArguments
from hyperprob.utility import common
from hyperprob.propertyparser import Property
from hyperprob.modelparser import Model
from hyperprob.modelchecker import ModelChecker


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
            if input_args.stutterLength:
                stutterLength = int(input_args.stutterLength)
            else:
                stutterLength = 1
            model.parseModel(True)
            modelchecker = ModelChecker(model, hyperproperty, stutterLength)
            modelchecker.modelCheck()
        print("\n")
    except Exception as err:
        common.colourerror("Unexpected error encountered: " + str(err))


if __name__ == "__main__":
    main()
