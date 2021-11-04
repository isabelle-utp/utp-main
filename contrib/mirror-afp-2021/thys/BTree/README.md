# A Verified Imperative Implementation of B-Trees

This repository contains all definitions, lemmas and proofs
related to the Bachelors Thesis "A Verified Imperative Implementation of B-Trees"
by Niels Mündler.

For a detailed description of the project, [see the thesis](https://github.com/nielstron/btrees-thesis).

## Overview

A functional specification of B-trees, B-tree operations and a
height analysis may be found in
the files `BTree*.thy` that do not contain `Imp`.

An imperative specification of B-trees may be found in `BTree_Imp*.thy`.
This imperative specification makes use of the auxiliary definition
of "Partially Filled Arrays" as list refinements, which may be found in `Partially_Filled_Array.thy`.
Further an extension of the standard array blit operation in Isabelle,
such that it allows error-free array-internal copy operations,
may be found in `Array_SBlit.thy`.

The remaining files contain auxiliary lemmas and definitions that are due to
Dr. Peter Lammich or me. 

All above mentioned files contain definitions as well as proofs of functional correctness.


## Usage

These theories have been tested with [Isabelle2020](https://isabelle.in.tum.de/website-Isabelle2020/index.html), although it should be compatible to newer versions of the tool.

The files `BTree*.thy` that do not contain `Imp` only need a regular Isabelle2020 setup.

The rest of the theories build upon [Refine_Imperative_HOL](https://www.isa-afp.org/entries/Refine_Imperative_HOL.html), you will need to succesfully set up that project first as described in the [rArchive of Formal Proofs](https://www.isa-afp.org/using.html).
The script `start_isabelle.sh` uses and if not available compiles a session
containing the content of the Refinement Framework which significantly enhances
working with the files provided in this project.
