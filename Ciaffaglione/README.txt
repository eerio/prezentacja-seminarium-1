Alberto Ciaffaglione, University of Udine (Italy) - October 2015
"Towards Turing Computability via Coinduction" in Coq 8.4(pl5)

------------------------------------------------------------------
The contribution is structured as follows:
- directory "animation": the whole contribution
[metathory is not present in this repo // eerio]
- directory "metatheory": first part of the contribution (doubled),
via a parametric (i.e., abstract) encoding for States and Alphabet

------------------------------------------------------------------
The directory is structured as follows:
- file "index":
order of precedence for files

- file "datatypes":
formalization of Turing Machines via streams

- file "coinduction":
introduction to coinduction in Coq

- file "bigstep":
big-step semantics with streams

- file "bf_vs_bi":
relationship between big-step convergence and divergence

- directory "adequacy":
big-step semantics with lists and relationship with streams
small-step semantics and equivalence with big-step semantics

- directory "examples":
proofs of convergence and divergence for 3 sample machines
(also a divergence proof that fails to be "guarded")

- directory "join":
sequential composition of Turing Machines and its properties

- directory "halting":
prove of the undecidability of the halting problem, via:
preliminary definitions (file "halting_defs")
machines Copy, Dither and Witness
the two paths of the proof (files "halt_not_halt" and "not_halt_halt")