---
layout: page
title: Model
permalink: /model/
description: How to describe the model we use as input
---
For our current version of the tool, we verify properties solely over Markov Decision Processes (MDPs). MDPs allow the expression of non-determinism in a system. The non-determinism might be a part of the system or maybe used to express uncontrollable inputs from the environment. 

We define a MDP formally as a tuple <i>M</i> = {<span style="color:yellowgreen;"><i>S</i>, <i>Act</i>, <i>P</i>, <i>AP</i>, <i>L</i></span>}, where,
- <span style="color:yellowgreen;">S</span> is the finite set of states.
- <span style="color:yellowgreen;">Act</span>  is a set of actions.
- <span style="color:yellowgreen;">P</span>  describes a transition probability function such that  <b>P : S x Act x S → [0,1]</b>, such that for all s in S, the sum of probabilities for all transitions for each of its actions is equal to 1.
- <span style="color:yellowgreen;">AP</span>  finite set of atomic propositions used in the system.
- <span style="color:yellowgreen;">L</span>  is the labelling function that maps atomic propositions to states in the system.

<div style="text-align:center"><img src="../assets/images/mdp.jpg" width = "300"/></div>
<div style="text-align: center;"> Figure: Example of a MDP </div>
<br>
In the above MDP,
- <span style="color:yellowgreen;">S</span> is { s0, s1, s2, s3 }
- <span style="color:yellowgreen;">Act</span>  is { α, β, τ}.
- <span style="color:yellowgreen;">AP</span> is { h>0, h≤0, l=1, l=2}



MDP have the following properties:
- They follow the Markovian property that the transition from the present state to the next depends only on the present state.
- Each state is associated with one or more actions which are used to express the non-determinism.
- Corresponding to each action we describe one or more probabilistic transitions.
- We argue about the states based on the labels associated with them.

We use [PRISM](https://www.prismmodelchecker.org/manual/ThePRISMLanguage/Introduction "prism") language to express the models. We currently use the old extension,  <span style="color:yellowgreen;">.nm</span> for MDPs. 

<div style="text-align:center"><img src="../assets/images/prism_mdp.jpg" /></div>
<div style="text-align: center;"> Figure: Example of the PRISM code for a MDP </div>
<br>

 Lets go over the important syntaxes of the above PRISM code:
 - The keyword `mdp` in line 1 is used to specify the type of model.
 - We then need to assign a module name followed by the keyword `module`.
 - In the next step (line 3-4), we define the variables used, like <i>h, l</i> and define the range of values that they can be assigned. You can also specify the init value, or datatypes as in [here](https://www.prismmodelchecker.org/manual/ThePRISMLanguage/ModulesAndVariables "variables").
 - For lines 5-8, we specify the transitions and the conditions they are based on. Since MDPs have actions, we can label them with names (alpha and beta in the above example) for our ease. With that ends the description of the module. Your code can have multiples modules in the same file.
 <div style="text-align:center"><img src="../assets/images/transition.jpg" width = "400"/></div>
<div style="text-align: center;"> Figure: description of the different components of a transition </div>
<br>
 - As in line 10, you can use an optional init block to describe the conditions for initial states.
 - Finally, we assign various labels, which are essentially chosen from the set of atomic propositions of the MDP. We further use these when specifying properties about the model.
 <br>
 <br>
<b>Note</b>: The seperators like ':' to seperate probabilities from the state descriptors, ';' to end every line, '→' to express transition to, are extremely crucial. Missing them would cause HyperProb to fail in parsing the model.  






