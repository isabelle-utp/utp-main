Isabelle/UTP
============

This is a semantic embedding of Hoare and He's [Unifying Theories of Programming](http://www.unifyingtheories.org/)
(UTP) in the Isabelle/HOL proof assistant. We base this particular implementation on the shallow embedding first created
by Feliachi, Gaudel, and Wolff (2010), but we also integrates a number of ideas from the alternative deep model of the
UTP in Isabelle by Foster, Zeyda, and Woodcock (2015).  In particular we recast variables to characterised by lenses
(see Foster, Zeyda, and Woodcock (2016)), and add semantic approximations of syntactic notions like fresh variables
(unrestriction) and substitution, and also add a form of "deep variables" that provides a more flexible form of alphabet
extension (whilst being subject to certain cardinality constraints).

Our aim is to use this version of Isabelle/UTP to support the mechanised semantics work we
are doing on EU H2020 project "INTO-CPS" (Grant agreement 644047) -- see <http://into-cps.au.dk/>
for more information.

Isabelle/UTP is very much still a work in progress, and currently requires some Isabelle expertise to use
effectively. For viewing the git repository I highly recommend the _Matisa_ plugin by York colleague [Pedro Ribeiro](https://www-users.cs.york.ac.uk/~pfr/) which
allows Isabelle symbols to be pretty-printed in the browser and can be obtained from the [Google Chrome
store](https://chrome.google.com/webstore/detail/matisa/jkpdfeicbjekckenhpippdllibmbcinf?hl=en-GB) or [Firefox
Add-ons](https://addons.mozilla.org/en-US/firefox/addon/matisa/).

Installation
------------

Installation requires that you have already installed the latest version of Isabelle on your system from
<http://isabelle.in.tum.de/> (at time of writing this is Isabelle2017). We provide a ROOT file in this repository with a
number of heap images. Our Isabelle theories depend on a number of entries from the [Archive of Formal
Proofs](https://www.isa-afp.org) (AFP), and without installing these dependencies you will not be able to start
Isabelle/UTP. Our repository notably depends on the [Optics](https://www.isa-afp.org/entries/Optics.html) session which
provides support for lenses, which we use to model variables. Our hybrid systems modelling session ``UTP-Hybrid`` also
depends on [Ordinary Differential Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html).

The easiest way to build the key heap images is using the build script located in ``bin/build.sh``, which also handles
fetching of appropriate AFP dependencies. Running this script will first attempt to download all the necessary libraries
from the AFP, and will then build the main UTP heap images one by one.

Alternatively, you can follow the [AFP instructions](https://www.isa-afp.org/using.html), which requires that you
download and install the whole AFP first. Our build scripts rely on knowing the location of where Isabelle/UTP is
installed. If they do not correctly guess the location then please set the environment variable ``ISABELLE_UTP`` to the
absolute path where it is installed.

Either way, once the depedencies are installed and appropriate heap images built, you're ready to go. If you wish to
develop something using UTP, then you can use the heap image called ``UTP``, that can be loaded by invoking

```bash
bin/utp-jedit UTP
```

from the command line in the installed directory. Alternatively you can configure your main Isabelle
``ROOTS`` file so that it knows about the location of Isabelle/UTP 
(see <https://isabelle.in.tum.de/dist/Isabelle2017/doc/system.pdf>). If you're developing the
Isabelle/UTP core you can instead invoke the ``UTP-Toolkit`` heap image. Various other heap images
exist including:

* ``UTP-Designs`` - imperative programs with total correctness
* ``UTP-Reactive`` - UTP theory of Generalised Reactive Processes
* ``UTP-Reactive-Designs`` - Reactive Designs
* ``UTP-Circus`` - Circus modelling language
* ``UTP-Hybrid - hybrid relational calculus``

Some of these heap images rely on other entries from the AFP. We therefore provide a utility under ``bin/``
called ``afp_get.sh`` which fetches entries and places them in the contrib directory. For example, 
[Ordinary Differential Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.shtml)
can be obtained by running

```bash
bin/afp_get.sh Ordinary_Differential_Equations
```

from the main UTP root directory. Alternatively there is a script ``bin/build.sh`` which fetches all dependencies
and builds all heap images, and thus may be an easier option for installation. 

Repository overview
-------------------

The core UTP Isabelle theories are located under the ``utp/`` directory. In particular, this contains 
the following key UTP theories:

* [``utp_expr.thy``](utp/utp_expr.thy) -- UTP expression model
* [``utp_pred.thy``](utp/utp_pred.thy) -- alphabetised predicate calculus and laws
* [``utp_rel.thy``](utp/utp_rel.thy) -- alphabetised relational calculus and laws
* [``utp_concurrency.thy``](utp/utp_concurrency.thy) -- concurrency with parallel by merge
* [``utp_hoare.thy``](utp/utp_hoare.thy) -- the Hoare calculus and associated laws
* [``utp_wp.thy``](utp/utp_wp.thy) -- weakest precondition calculus
* [``utp_opsem.thy``](utp/utp_rel_opsem.thy) -- operational semantics for UTP relations
* [``utp_theory.thy``](utp/utp_theory.thy) -- an account of UTP theories

Additionally, under the ``theories/`` directory a number of UTP theories that we have developed can be found,
including:

* [``utp_designs.thy``](theories/designs/utp_designs.thy) -- theory of designs, including signature, healthiness conditions, and laws
* [``utp_reactive.thy``](theories/reactive/utp_reactive.thy) -- theory of reactive processes
* [``utp_rea_designs.thy``](theories/rea_designs/utp_rea_designs.thy) -- theory of reactive designs
* [``utp_csp.thy``](theories/circus/utp_circus.thy) -- theory of Circus and CSP
* [``utp_cml.thy``](theories/utp_cml.thy) -- the COMPASS modelling language (see <http://compass-research.eu>)

This repository is constantly a work in progress, so not all laws have yet been proved, though the number
is constantly growing. Additionally to the UTP theories there is a number of contributed UTP theories included
under the ``contrib/`` directory. Notably this includes an adapted version of Armstrong and Struth's 
[Kleene Algebra library](https://www.isa-afp.org/entries/Kleene_Algebra.shtml), which is a dependency and
thus is included for convenience.

Under the ``vdm/`` directory a prototype implementation of VDM-SL, as an embedding into the theory of designs, may
be found. Moreover, under ``hybrid/`` a mechanisation of our hybrid relational calculus can be found which enables
us to give denotational semantics to hybrid systems languages like Modelica and Simulink.

Usage
-----

Isabelle/UTP is documented by a number of tutorial theories under the ``tutorial/`` directory. First and
foremost it is worth checking the [UTP tutorial theory](tutorial/utp_tutorial.thy) which attempts to give
an overview of the UTP in Isabelle. You can view the associated [PDF of the tutorial](doc/UTP-Tutorial.pdf) 
as well. You can also check out [Boyle's law](tutorial/utp_boyle.thy) for a very 
basic UTP theory. An example of usage of the theory of designs for proving properties about programs can
be found in the [library example](tutorial/utp_library.thy). You can also check out the 
[proof document](doc/UTP.pdf). We also provide some preliminary usage notes below.

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

For more details of the Isabelle/UTP grammar please see the [syntax reference document](doc/syntax/utp-syntax.pdf).

## Proof support

We employ a number of proof tactics for UTP:

* ``pred_auto`` -- for predicate conjectures
* ``rel_auto`` -- for relational conjectures
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
* Simon Foster, Frank Zeyda, and Jim Woodcock. _Unifying Heterogeneous State-Spaces with Lenses_. Proc. 13th Intl. Colloquium on Theoretical Aspects of Computing (ICTAC 2016). [Paper link](https://pure.york.ac.uk/portal/en/publications/unifying-heterogeneous-statespaces-with-lenses(f3673ce3-7643-4b1f-aff3-bc7773d93a65).html)
* Frank Zeyda, Simon Foster, and Leo Freitas. _An Axiomatic Value Model for Isabelle/UTP_. Proc. 6th Intl. UTP Symposium, 2016. [Paper link](https://pure.york.ac.uk/portal/en/publications/an-axiomatic-value-model-for-isabelleutp(36eb03fd-bcce-48fa-b1e0-2c3d4ecb71b1).html)
* Simon Foster and Jim Woodcock. _Towards Verification of Cyber-Physical Systems with UTP and Isabelle/HOL_. In Concurrency, Security, and Puzzles, January 2017. [Paper link](https://pure.york.ac.uk/portal/en/publications/towards-verification-of-cyberphysical-systems-with-utp-and-isabellehol(ead04827-1fe8-404a-9da0-e3e4b250cdba).html)
* Abderrahmane Feliachi, Marie-Claude Gaudel, and Burkhart Wolff. _Unifying Theories in Isabelle/HOL_. Proc. 3rd Intl. UTP Symposium, 2010. [Paper link](https://www.lri.fr/~wolff/papers/conf/2010-utp-unifying-theories.pdf)
* Simon Foster, Frank Zeyda, and Jim Woodcock. _Isabelle/UTP: A Mechanised Theory Engineering Framework_. Proc. 5th Intl. UTP Symposium, 2014. [Paper link]<http://link.springer.com/chapter/10.1007%2F978-3-319-14806-9_2>
