------------
Quadratic Virtual Substitution Formalization
-----------

********** Isabelle File Organization **********

Here is a quick summary from top to down of all the files

Exports:
  Creates an SML export of the developed algorithms for testing purposes

VSQuad:
  Provides the overarching algorithms to ramp up the VS procedure throughout the
whole formula from inside to outside

Unpower:
  Simplifies polynomials by factoring out zero roots, simplification algorithm

PushForall:
  Simplification algorithm which pushes forall statements inwards in a formula

ClearQuantifiers:
  Clears the successfully eliminated quantifiers after performing QE

SimpFm:
  Simplifies fully computed formulas by evaluation constant polynomials

GeneralVSProofs:
  Proofs associated with verifying the GeneralVS algorithm and its
univariate counterpart

DNFUni:
  Disjunctive Normal Form algorithm for univariate polynomials and associated
proofs

QE:
  Main lemmas for univarate quantifier elimination for quadratic polynomials,
proofs not necessarily dependant on the framework

InfinitesimalsUni:
  Univariate functions for the infinitesimal virtual substitution and associated
proofs

EqualityVS:
  Proofs for the equality virtual substitution procedure

LuckyFind:
  Optimization which quickly finds a nonzero root to eliminate the quantifier quickly

EliminateVariable:
  Substitution procedure which calls all other procedures for linear and quadratic
roots

Infinitesimals:
  Function for computing infinitesimal virtual substitution

QuadraticCase:
  Quadratic equality substitution case of virtual substitution

NegInfinityUni:
  Univariate version of negative infinity virtual substitution and associated
proofs

NegInfinity:
  Negative infinity virtual substitution

UniAtoms:
  Univariate formulation of atoms

LinearCase:
  Linear case of equality virtual substitution

DNF:
  Algorithm which splits up the formula into DNF form, while trying to maximize
the information content

Debrujin:
  Lifting and lowering of indices in polynomials to formalize DeBrujin indices

UsefulLemmas:
  Collection of miscellaneous lemmas used in several proofs

NNF:
  negation normal form and associated proofs

PolyAtoms:
  Formalization of real-arithmetic formulas

FunWithPoly:
  creation of polynomial code theorems and some proofs

PrettyPrinting:
  Helpful printing function for polynomials

