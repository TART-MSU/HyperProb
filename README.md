**HyperOnMDP**
========
<!--- [![Build Status](https://travis-ci.org/moves-rwth/prophesy.svg?branch=master)](https://travis-ci.org/moves-rwth/prophesy) ---> 

This is a tool set for verifying Hyperproperties on Markov Decision Processes.
The release of this tool is accompanied by an [overview paper](https://arxiv.org/pdf/2005.06115.pdf).

Please notice that prophesy is academic software, and mostly meant as a sandbox for developing new algorithms.
It is licensed under the MIT License. If you are interested in other licensing options, do not hesitate to contact us!

Dependencies
------------

This script uses python 3. It is mainly dependent on :

- [CArL](http://smtrat.github.io/carl/) from `master14` branch installed.
- [Carl-parser](https://github.com/ths-rwth/carl-parser) from `master14` is optional for added features.
- [PyCarl](https://moves-rwth.github.io/pycarl/) to utilize the features of CArl in python.
- [Storm](https://www.stormchecker.org/) for probabilistic modelchecking. 
- [Stormpy](https://moves-rwth.github.io/stormpy/) to utilize Storm's features in python.

The above library has its own dependencies which need to be resolved first.

Installation
------------

Currently working on a integrated downloadable tool set. 
The easist way to use the tool currently is generating a container from the [docker image](https://hub.docker.com/r/oyendrila/hyper_on_mdp_tool) which comes with all the dependencies and the script pre-installed. 

Getting Started
---------------

The arguments that the script needs are as follows:

- Path of the model file

- HyperProperty to be verified

For examples on how to represent these parameters refer to this [script](docs/Experiments.txt).
Authors
-------

This tool is mainly developed at Michigan State University by:

- Oyendrila Dobe 

Prophesy is developed in close cooperation with:
- [Erika Abraham](https://ths.rwth-aachen.de/people/erika-abraham/)
- [Ezio Bartocci](https://informatics.tuwien.ac.at/people/ezio-bartocci)
- [Borzoo Bonakdarpour](http://www.cse.msu.edu/~borzoo/)

We would like to thank [Mattias Volk](https://moves.rwth-aachen.de/people/volk/) and [Sebastian Junges](https://sjunges.github.io/sebastian-junges/) for their help with Stormpy during the tool development.


