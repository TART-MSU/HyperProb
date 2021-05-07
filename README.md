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

Getting Started
---------------

The arguments that the script needs are as follows:

- Path of the model file

- HyperProperty to be verified

For examples on how to represent these parameters refer to this [script](benchmark_files/Experiments.txt).

Using the tool
--------------

The easist way to use the tool is generating a container from the [docker image](https://hub.docker.com/r/oyendrila/hyperprob) which comes with all the dependencies and the script pre-installed.
- The docker operates on Ubuntu.
- The dependency libraries are loacted in ```/opt``` folder and hav ebeen added to global path.
- The tool files are located under ```/home/HyperOnMDPtool``` folder.
- Add the model file anywhere under this folder.
- The property has to be written when calling the script.
- To run the tool, invoke the ```source.py``` as follows:
  - ```python source.py file_path_for_model hyperproperty```
  - ```file_path_for_model``` refers to the file path with respect to ```/home/HyperOnMDPtool``` as base. For example, if your file is located in ```/home/HyperOnMDPtool/models/mdp.nm```, your command would be ```python source.py models/mdp.nm hyperproperty```

People
-------
  Authors:
  - Oyendrila Dobe, Michigan State University. 
  - [Borzoo Bonakdarpour](http://www.cse.msu.edu/~borzoo/), Michigan State University. 
  
  Other Contributors:
  - [Erika Abraham](https://ths.rwth-aachen.de/people/erika-abraham/), RWTH Aachen.
  - [Ezio Bartocci](https://informatics.tuwien.ac.at/people/ezio-bartocci), TU-Vienna.

  Acknowledgements:
  - United States National Science Foundation 
  - We would like to thank [Mattias Volk](https://moves.rwth-aachen.de/people/volk/) and [Sebastian Junges](https://sjunges.github.io/sebastian-junges/) for their help with Stormpy during the tool development.


