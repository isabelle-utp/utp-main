## Concrete heap translator

This directory contains a Haskell program for translating high-level
descriptions of heaps into Isabelle `.thy` files and Graphviz `dot`
files. A sample input file is `input_heap.txt`.

> ghci Main
> > main

> dot -Tpdf input.dot -o output.pdf

The input file consists of two parts split by `--`.

The first part describes the mutators and their roots. For example:

  0 1 2 3
  1 3
  2 2 5

stands for the following:

There are three mutators called 0, 1, 2, respectively. The mutator 1
has references to the object 1, 2, and 3. The mutator 1 has a
reference to the object 3. The mutator 2 has references to the
object 2 and 5.

The second part describes the objects and their fields.

  0
  1
  2
  3 0 1 1 2
  4
  5

stands for the following:

There are six objects called 0, 1, 2, 3, 4, 5, respectively. The
object 3 has two fields called 0 and 1 respectively. In the field 0, a
reference to the object 1 is stored, while the field 1 contains a
reference to the object 2.
