# Polytope Packing

## Prerequisites

You need to have CGAL libraries installed. They can be
obtained at http://www.cgal.org.

Directories convexhull, display, processhull rely on CGAL. You
need to change directory into each of them and create the makefiles
as indicated by the respective READMEs.

## Compilation

Enter each of the directories convexhull, display, initializeproblem,
processhull and type ``make''.

## Execution

We rely on Z3 to compute the solution to the smt2 problem. You
need to have z3 available under directory ../z3/build/z3. You can
download z3 from https://github.com/Z3Prover/z3 and follow the
instruction for its compilation.

Directory benchmark contains some problems that could be already run.
For instance you can try with

    ./go benchmark/problem_7.pk 12 10 30

You will find the results under results/problem_7.pk_12_10_30.*
