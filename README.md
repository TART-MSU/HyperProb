# HyperProb

This package model checks probabilistic hyperproperties written in HyperPCTL ON MDPs/DTMCs. 
The release of this tool is accompanied by an [overview paper](https://www.sciencedirect.com/science/article/pii/S089054012200133X?casa_token=JT3zBQFzNoEAAAAA:x3OqqK63TLkTh1COUYeg2s_5XzEKSPI5HFTknAN43XnSacb1ZvZaBRIPHOWlnFM6XavP8CoQebk).

HyperProb is licensed under the MIT License. If you are interested in other licensing options, do not hesitate to contact us!

## Dependencies

This script uses python 3. HyperProb depends on [stormpy](https://github.com/moves-rwth/stormpy) which has its own dependencies. Currently you can find scripts in the `resources` folder to help install the dependencies. The [README.md](resources/README.md) inside this folder provides a guide for these installations. It is mainly dependent on :

- [CArL](http://smtrat.github.io/carl/) from `master14` branch installed.
- [Carl-parser](https://github.com/ths-rwth/carl-parser) from `master14` is optional for added features.
- [PyCarl](https://moves-rwth.github.io/pycarl/) to utilize the features of CArl in python.
- [Storm](https://www.stormchecker.org/) for probabilistic modelchecking. 
- [Stormpy](https://moves-rwth.github.io/stormpy/) to utilize Storm's features in python.

The above libraries has its own dependencies which might need to be resolved first. Follow the instructions on their respective website if the shell scripts mentioned above does not work. Do raise an issue so that we can add it to our instructions too.


## Installation

Begin by cloning this folder locally:
```
git clone https://github.com/TART-MSU/HyperProb
cd HyperProb
```

To install HyperProb (and its dependencies) run:
`pip install .` from the `HyperProb` folder.


## Getting Started

The arguments that the script needs are as follows:

- Path of the model file (used with the flag -modelPath)

- HyperProperty to be verified (used with the flag -hyperString)

Additionally we allow flags to check if the typed property is correct (--checkProperty) and if the model file complies correctly (--checkModel).

For examples on how to represent these parameters refer to this [script](benchmark_files/Experiments.txt).<br>
A detailed user manual (in progress) can be accessed at [User Manual](https://oyendrila-dobe.github.io/HyperProb/).

Using the tool
--------------



People
-------
  Authors:
  - [Oyendrila Dobe](https://oyendrila-dobe.github.io/), Michigan State University. 
  - [Borzoo Bonakdarpour](http://www.cse.msu.edu/~borzoo/), Michigan State University. 
  
  Other Contributors:
  - [Erika Abraham](https://ths.rwth-aachen.de/people/erika-abraham/), RWTH Aachen.
  - [Ezio Bartocci](https://informatics.tuwien.ac.at/people/ezio-bartocci), TU-Vienna.

Acknowledgements
----------------
 - United States National Science Foundation 
 - We would like to thank [Mattias Volk](https://moves.rwth-aachen.de/people/volk/) and [Sebastian Junges](https://sjunges.github.io/sebastian-junges/) for their help with Stormpy during the tool development.


