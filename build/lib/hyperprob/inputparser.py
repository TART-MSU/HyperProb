import argparse


def parse_arguments():
    parser = argparse.ArgumentParser(description='Modelchecks an Markov Chain against a given HyperPCTL specification.')
    parser.add_argument('-model', required=True, help='the MDP/DTMC model file in PRISM language')
    parser.add_argument('-hyper', required=True, help='the specification file in HyperPCTL')
    parser.add_argument('--check_model', action='store_true', help='check if model file can be parsed')
    parser.add_argument('--check_property', action='store_true', help='check if property file can be parsed')
    args = parser.parse_args()
    return args
