# goSAT
goSAT is an SMT solver for the theory of floating-point arithmetic (FPA) that is based 
on global optimization.

## Overview 
goSAT is an SMT solver based on mathematical global optimization. It casts the satisfiability
problem of FPA to a corresponding global optimization problem. 
It builds on the ideas proposed in [XSat]. Compared to XSat, we implemented 
the following key features:

- JIT compilation of SMT formulas using LLVM.
- Integration with NLopt, a feature-rich mathematical optimization package.

In our experiments, goSAT demonstrated better *efficiency* compared to `z3` and `mathsat`
by an order of magnitude or more. 
More details are available in our FMCAD'17 [paper] and this [appendix].     

## Citing

If you use goSAT in an academic work, please cite:

```
@inproceedings{BenKhadra2017a,
author = {{Ben Khadra}, M Ammar and Stoffel, Dominik and Kunz, Wolfgang},
booktitle = {Proceedings of Formal Methods in Computer-Aided Design (FMCAD'17)},
doi = {10.23919/FMCAD.2017.8102235},
pages = {11--14},
title = {{goSAT: Floating-point Satisfiability as Global Optimization}},
year = {2017}
}
```

## Dependencies

This project depends on:

- [Z3] library for input file parsing and model validation
- [LLVM] for JIT execution of SMT formulas.
- [NLopt] for finding the minima of the objective function. 
 
Installing z3 and nlopt should be straightforward. As for installing LLVM, you might 
find this [tutorial] to be useful. 

goSAT is known to work with z3 v4.6, LLVM v4.0.1, nlopt v2.4.2.
We recommend building LLVM from source as the official pre-built package might be broken.
Specifically, we are aware of such issues on Ubuntu 16.04.

## Building 

You can build the project using a command like,

```bash
mkdir build; cd build
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_PREFIX_PATH=/home/gosat/local/ -DLLVM_DIR=/home/gosat/local/llvm/lib/cmake/llvm/ ..
make
```
assuming that `libnlopt` and `libz3` are installed at the prefix `${HOME}/local/` 
while `llvm` is installed at `${HOME}/local/llvm`. 

## Usage
An SMT file needs to be provided using `-f` option. Additionally, the tool operation mode
can be set. goSAT supports three operation modes:

 - **Native solving**. This is the default mode where a given formula is first transformed
 to an objective function in LLVM IR. Then, the objective function is jitted using MCJIT
 and solved using the NLopt backend. This mode can be explicitly set
 using `-mode=go` option.
 
 - **Code generation**. This mode can be enabled using `-mode=cg` option.
  It mimics the behavior of [XSat] where C code gets generated representing 
  the objective function. 
  Generated code needs to be compiled and solved using on of the tools we provide in 
  `tools` folder. Moreover, you can specify an API dump format like
  `-mode=cg -fmt=plain` for generating several objective functions. The latter is useful for 
  building a library as discussed [here](tools/README.md).

 - **Formula analysis**. A simple analysis to show the number of variables, their
 types, and other misc facts about a given SMT formula. This mode is enabled
 using `-mode=fa` option.

The default output of goSAT is in csv format. It lists the benchmark name, sat result, 
elapsed time (seconds), minimum found, and status code returned by `nlopt`. 
The minimum found should be zero in case of `sat`. 
Use option `-smtlib-output` to obtain conventional solver output which is more succinct.

Note that goSAT relies on stochastic search which means that we can 
not generally *prove* an instance to be `unsat` even if it is actually so. 
Therefore, goSAT reports back either `sat` or `unknown`.
Being stochastic, gives goSAT an edge in efficiency over conventional solvers like `z3` 
and `mathsat`. However, this also restricts the application domains of goSAT.

## Model validation

In the case of `sat` result, it is possible to intruct `goSAT` to externally validate the 
generated model using `z3`. This can be done by providing parameter `-c`. For example,

```bash
./gosat -c -f formula.smt2
```

So far, we have not encountered any unsound result. Please report to us if you 
find any such cases.


  [Z3]: <https://github.com/Z3Prover/z3>
  [LLVM]: <http://llvm.org/>
  [online]: <http://www.cs.nyu.edu/~barrett/smtlib/QF_FP_Hierarchy.zip>
  [XSat]: <http://dx.doi.org/10.1007/978-3-319-41540-6_11>
  [NLopt]: <https://github.com/stevengj/nlopt>
  [paper]: <https://blog.formallyapplied.com/docs/gosat.pdf>
  [appendix]: <https://blog.formallyapplied.com/2017/05/gosat-faq/>
  [tutorial]: <https://github.com/abenkhadra/llvm-pass-tutorial>
