## DARE 2024 Formal Methods Session ##

We will do our demonstrations in FStar, a dependently-typed functional
programming language and proof system. 

### Installing FStar ###

FStar's
[Install.md](https://github.com/FStarLang/FStar/blob/master/INSTALL.md)
lists various ways to install FStar. If you are on OS X or Linux, I
recommend installing via opam:

1. Opam is the package manager for [OCaml](https://ocaml.org/) -- the language in which FStar is
   written. FStar programs can be extracted to OCaml. To install opam,
   follow he instructions [here](https://opam.ocaml.org/doc/Install.html).
2. After installing Opam, run `eval $(opam env)` to load opam config in to
   your shell environment. 
2. To install the latest stable release of FStar, run `opam install fstar`
3. To install the dev version:
  1. `git clone git@github.com:FStarLang/FStar.git`
  2. `cd Fstar`
  3. `opam pin add fstar .`. This will start installing FStar as an opam
     package. Answer `Y` to questions opam asks.
4. Re-run `eval $(opam env)`
5. Check fstar installation using `fstar.exe --version`

FStar uses [Z3 Prover](https://github.com/Z3Prover/z3) to discharge
verification conditions. Follow the instructions on [Z3
repo](https://github.com/Z3Prover/z3/blob/master/README.md) to compile Z3
from its sources. You may also install Z3 via opam (`opam install z3`).
Once the installation is complete, make sure the `z3` executable is on your
`PATH`. At this point, you should be able to verify simple fstar programs,
such as [Fib.fst](Fib.fst) by running `fstar.exec Fib.fst`.

The easiest way to program in FStar is via vscode IDE. Install
[fstar-vscode-assistant](https://marketplace.visualstudio.com/items?itemName=FStarLang.fstar-vscode-assistant)
extension via the extensions tab in your vscode IDE. Restart vscode after
the extension is installed. You should now be able to write fstar programs
in vscode and verify them interactively; Refer to "Basic Navigation"
section of
[fstar-vscode-assistant](https://marketplace.visualstudio.com/items?itemName=FStarLang.fstar-vscode-assistant)
for hotkey bindings. 


### FStar Tutorials ###

* [Proof-Oriented Programming In
F*](https://fstar-lang.org/tutorial/proof-oriented-programming-in-fstar.pdf)
is the official tutorial/manual for the language. There is also an [online](https://fstar-lang.org/tutorial/) version.
* Lectures and course material from OPLSS 2021 are available [online](https://fstar-lang.org/oplss2021/index.html).
  
