Isabelle/UTP
============

This is a semantic embedding of Hoare and He's _Unifying Theories of Programming_ (UTP) in the Isabelle/HOL proof
assistant. We base this particular implementation on the shallow embedding first created by Feliachi, Gaudel, and Wolff
(2010), but we also integrates a number of ideas from the alternative deep model of the UTP in Isabelle by Foster,
Zeyda, and Woodcock (2015).  In particular we recast variables to characterised by lenses (see Foster, Zeyda, and
Woodcock (2016)), and add semantic approximations of syntactic notions like fresh variables (unrestriction) and
substitution, and also add a form of "deep variables" that provides a more flexible form of alphabet extension (whilst
being subject to certain cardinality constraints).

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

There's little documentation at the moment -- this will follow later. However we provide some preliminary notes below.
You can also check out [Boyle's law](utp/utp_boyle.thy) for a very basic UTP theory, and then the 
[theory of designs](utp/utp_designs.thy). You can also check out the [proof document](utp/output/document.pdf). 

### Parser

As for the former deep model we make every effort to preserve the standard UTP syntax as presented in
the UTP book and other publications. Unlike the deep model of UTP we do not employ a backtick parser, 
but rather use the top-level Isabelle expression grammar for UTP expressions. This achieved, firstly 
by (adhoc) overloading operators where possible. For example we overload the HOL predicate operators 
(like conjunction, negation etc.) with UTP versions. This means that we have to use the type system 
of Isabelle to disambiguate expressions, and so sometimes type annotations are required (though not 
often). Where it is not possible or feasible to override we instead use the UTP operator with a 
``u`` subscript. For example, it does not seem sensible to override the HOL equality operator as this
would compromise the elegance of Isar for equational proofs, and so we call it =_u. Incidentally
subscripts in Isabelle can be written using the ```\<^sub>``` code. In general where an operator is 
polymorphic (e.g. arithmetic operators) we just use standard syntax. See
the [UTP expression theory](utp/utp_expr.thy) for more examples.

Variables are a potential source of confusion. There are three main syntaxes for variables in
UTP predicates:

* ``&x`` -- a variable in a non-relational predicate
* ``$x`` -- an input variable in a relational predicate
* ``$x\<^acute>`` -- an output variable in a relational predicate

The reason we have to have three is to do with the type system of Isabelle -- since alphabets
are types, a relation has a different type to a flat predicate and so variables in these constructions
also have different types.

## Proof support

We employ a number of proof tactics for UTP:

* ``pred_tac`` -- for predicate conjectures
* ``rel_tac`` -- for relational conjectures
* ``subst_tac`` -- apply substitution laws in a predicate

There is actually little difference between the predicate and relational tactic; if one doesn't
work try the other. When you define your own operators you need to add them to the tactic's
simplification set(s) in order for the tactic to correct simplify the construct. You can do this
for example by writing something like:

```isabelle
declare my_op_def [upred_defs]
```

The simplification sets corresponding to the tactics are, respectively:

* ``upred_defs``
* ``urel_defs``
* ``usubst``

We've also loaded a number of equational laws into the simplifier, so try ``simp`` out if it seems
the obvious thing to do, or maybe even ``auto``. Additionally there is always **sledgehammer** available which often works
well when suitable algebraic laws have been proven (see <http://isabelle.in.tum.de/dist/doc/sledgehammer.pdf>). 
You can also try to combine sledgehammer with a UTP tactic. Probably more tactics will be written
and the existing ones will continue to improve.

Have fun!

References
----------

* C. A. R. Hoare and He Jifeng. _Unifying Theories of Programming_. Prentice Hall 1998. <http://unifyingtheories.org/>
* Simon Foster, Frank Zeyda, and Jim Woodcock. _Unifying Heterogeneous State-Spaces with Lenses_. Proc. 13th Intl. Colloquium on Theoretical Aspects of Computing (ICTAC 2016).
* Abderrahmane Feliachi, Marie-Claude Gaudel, and Burkhart Wolff. _Unifying Theories in Isabelle/HOL_. Proc. 3rd UTP Symposium, 2010. <https://www.lri.fr/~wolff/papers/conf/2010-utp-unifying-theories.pdf>
* Simon Foster, Frank Zeyda, and Jim Woodcock. _Isabelle/UTP: A Mechanised Theory Engineering Framework_. Proc. 5th UTP Symposium, 2014. <http://link.springer.com/chapter/10.1007%2F978-3-319-14806-9_2>