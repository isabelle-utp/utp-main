Isabelle/UTP Shallow
====================

This is a semantic embedding of Hoare and He's _Unifying Theories of Programming_ (UTP) in
the Isabelle/HOL proof assistant. We base this particular implementation on the shallow embedding
first created by Feliachi, Gaudel, and Wolff (2010), but we also integrates a number of ideas
from the alternative deep model of the UTP in Isabelle by Foster, Zeyda, and Woodcock (2015).
In particular we add semantic approximations of syntactic notions like fresh variables 
(unrestriction) and substitution, and also add a form of "deep variables" that provides a more
flexible form of alphabet extension (whilst being subject to certain cardinality constraints).

Our aim is to use this version of Isabelle/UTP to support the mechanised semantics work we
are doing on EU H2020 project "INTO-CPS" (Grant agreement 644047) -- see <http://into-cps.au.dk/>
for more information.

Isabelle/UTP is very much still a work in progress, and currently requires some Isabelle expertise
to use effectively.

Installation
------------

Installation requires that you have already installed the latest version of Isabelle on your
system from <http://isabelle.in.tum.de/> (at time of writing this is Isabelle2015). We provide
a ROOT file in this repository with a number of heap images. If you wish to develop something
using UTP, then you can use the heap image called "UTP", that can be loaded by invoking

```bash
isabelle jedit -d. -l UTP
```

from the command line in the installed directory. Alternatively you can configure your main Isabelle
ROOTS file so that it knows about the location of Isabelle/UTP 
(see <https://isabelle.in.tum.de/dist/Isabelle2015/doc/system.pdf>). If you're developing the
Isabelle/UTP core you can instead invoke the UTP-IMPORTS heap image.

Usage
-----

There's little documentation at the moment -- this will follow later. For now check out <utp/utp_boyle.thy>
for a very basic UTP theory, and then <utp/utp_designs.thy> for the the theory of designs. You can also
check out the proof document in <utp/output/document.pdf>.