# HyperProb

This package model checks probabilistic hyperproperties specified in HyperPCTL ON MDPs/DTMCs. 
The release of this tool is accompanied by an [overview paper](https://www.sciencedirect.com/science/article/pii/S089054012200133X?casa_token=JT3zBQFzNoEAAAAA:x3OqqK63TLkTh1COUYeg2s_5XzEKSPI5HFTknAN43XnSacb1ZvZaBRIPHOWlnFM6XavP8CoQebk).

HyperProb is licensed under the MIT License. If you are interested in other licensing options, do not hesitate to contact us!

## Dependencies

This script uses python 3. HyperProb depends on [stormpy](https://github.com/moves-rwth/stormpy) which has its own dependencies. Currently you can find scripts in the `resources` folder to help install the dependencies. The [README.md](resources/README.md) inside this folder provides a guide for these installations. It is mainly dependent on :

- [CArL](http://smtrat.github.io/carl/) from `master14` branch installed.
- [Carl-parser](https://github.com/ths-rwth/carl-parser) from `master14` is optional for added features.
- [PyCarl](https://moves-rwth.github.io/pycarl/) to utilize the features of CArl in python.
- [Storm](https://www.stormchecker.org/) for probabilistic model checking. 
- [Stormpy](https://moves-rwth.github.io/stormpy/) to utilize Storm's features in python.

The above libraries has its own dependencies which might need to be resolved first. Follow the instructions on their respective website if the shell scripts mentioned above does not work. Do raise an issue so that we can add it to our instructions too.


## Installation

Begin by cloning this folder locally:
```
git clone https://github.com/TART-MSU/HyperProb
cd HyperProb
```

To install HyperProb (and its python dependencies) run:
`pip install .` from the `HyperProb` folder.


## Getting Started

The arguments that the script needs are as follows:

- Path of the model file (used with the flag `-modelPath`). We currently allow a single model file.
- Hyperproperty to be verified (used with the flag `-hyperString`)

Additionally, we allow the following flags,
- to check if the typed property is correct (`--checkProperty`)
- to check if the model file complies correctly (`--checkModel`).

```
python hyperprop.py -modelPath path_to_model_file -hyperString
"ES sh . A s1 . E s2 .((hg0(s1) & hle0(s2)) -> ~(P(F le1(s1)) = P(F le1(s2))))"
```
### Dissecting the above hyperprob command:


In HyperPCTL, we express properties involving multiple computation trees. In the above example our properties involve two such computation trees. Keeping in mind the above MDP:
- `ES sh`: we are looking for the existence (specified by `ES`) of a scheduler (specified by `sh`).
- `A s1 . E s2`: we want to verify if for all possible initial states for the first computation tree (`A s1`), there exists another computation tree (`A s2`), satifying the rest of the specification.
- `(hg0(s1) & hle0(s2))`: specifies the condition for which state can be used as in initial state.
- `~(P(F le1(s1)) = P(F le1(s2)))`: specifies how the probabilities across the trees should be related.

### Points to note
Let us consider the hyperproperty above:
```
"ES sh . A s1 . A s2 .((hg0(s1) & hle0(s2)) -> ~(P(F le1(s1)) = P(F le1(s2))))"
```
- We currently support a single scheduler quantifier and a single model.
  - Here, `sh`, the scheduler quantifier variable can have any name whatsoever.
  - We can use `ES` to find the existence of a scheduler and `AS` to check for all schedulers.
- We have specific naming convention used for state variables.
  - Here `s1`,`s2`, the state variable names, have been associated with our atomic propositions, e.g., `hg0(s1)`. 
  - The name does not matter here, but the numbering of the state quantifiers should start from 1.
  - We can use `E` to specify existence of an initial state  and `A` to specify for all possible initials states.
- We can use HyperProb to verify DTMCs.
  - We can specify the hyperproperty in a similar manner and keep the scheduler variable as `ES sh` as we have only one scheduler.

For examples on how to represent these parameters refer to [this script](benchmark_files/Experiments.txt).


## People

### Authors:
  - [Oyendrila Dobe](https://oyendrila-dobe.github.io/), Michigan State University. 
  - [Borzoo Bonakdarpour](http://www.cse.msu.edu/~borzoo/), Michigan State University. 
  
### Other Contributors:
  - [Erika Abraham](https://ths.rwth-aachen.de/people/erika-abraham/), RWTH Aachen.
  - [Ezio Bartocci](https://informatics.tuwien.ac.at/people/ezio-bartocci), TU-Vienna.

## Acknowledgements

 - United States National Science Foundation 
 - We would like to thank [Mattias Volk](https://moves.rwth-aachen.de/people/volk/) and [Sebastian Junges](https://sjunges.github.io/sebastian-junges/) for their help with Stormpy during the tool development.


