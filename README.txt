This repository upgrades the Coq code from "Towards Turing computability via coinduction"
from 8.4pl5 to 8.20.1

Please note that 8.4pl5 contained a serious inconsistency bug, as documented by:
https://github.com/clarus/falso

link to the paper:
https://doi.org/10.1016/j.scico.2016.02.004

source:
https://users.dimi.uniud.it/~alberto.ciaffaglione/Turing/Halting/


Install opam and the correct version of Coq, coq-lsp and the vscode extension
Coq-lsp is completely superior to VSCoq, emacs and vim versions
It is superior to VSCoq, because the former is not really supported anymore
And it is superior to emacs and vim plugins, because it really
works well out of the box. I just spend ~10 hours using it while
working on this project and, given you use Open Folder in VSCode on the correct folder
(i.e. on the directory containing _CoqProject, so not the root of this repo but the Ciaffaglione dir),
it really works better than CoqIDE or anything. Only doesn't synchronize well with
working on multiple files at once and compiling it independently from
the terminal - it requires LSP server restart when it doesn't see
that an imported file has changed.

$ sudo apt install opam
$ opam init
$ opam pin add coq 8.20.1
$ opam install coq-lsp && code --install-extension ejgallego.coq-lsp

$ coqc --version
The Coq Proof Assistant, version 8.20.1
compiled with OCaml 5.2.1
$ cd Ciaffaglione
$ coq_makefile -f _CoqProject -o CoqMakefile && make -f CoqMakefile
COQDEP VFILES
COQC datatypes.v
COQC bigstep.v
COQC coinduction.v
[...]
 


A good material on coinductive types in Coq:
https://link.springer.com/chapter/10.1007/3-540-60579-7_3