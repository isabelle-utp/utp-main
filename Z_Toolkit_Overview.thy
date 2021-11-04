section \<open> Overview \<close>

(*<*)
theory Z_Toolkit_Overview
  imports Main
begin
(*>*)

text \<open> The objective of this theory development is an implementation of the Z mathematical 
  toolkit~\cite{zrm} (ISO 13568:2002\footnote{Z formal specification notation. 
  \url{https://www.iso.org/standard/21573.html}}) that is both efficient for proof and faithful to the standard. 

  The main challenge to overcome is a mismatch between the type system of Z, and the way that 
  Isabelle/HOL theories are typically developed. This is because the objectives of Z and HOL 
  are a little different: Z targets a mathematically pure foundational development for formal
  specification based on ZF set theory, whereas HOL targets an efficient proof system capable
  of scalable verification. The aim then is to reconcile these two objectives in one development.

  In Z, the type system is very simple, consisting only of given types closed under powerset and 
  product constructions. For example, in Z a total function is simply encoded as its graph in a 
  relation, and a relation is simply a set of pairs. There is no distinct type constructor for
  functions. Similarly, a sequence (list in HOL) is a finite function whose domain is 
  @{term "{1::nat..n}"}, for some natural number @{term n}. This means in Z, we can write expressions
  that compare a relation and sequence, since they have the same type. 

  In contrast, in HOL it is impossible to directly compare a relation and a list since they have 
  distinct type constructors, and only values of the same types can typically be related. It is
  necessary to insert explicit coercions between values of different types in this case.
  Indeed, the dominant paradigm for theory development in HOL is to constantly extend the type 
  system to capture new mathematical concepts, such as vectors, bounded continuous functions, and
  physical quantities, to name a few examples. This approach has proven to be very successful and
  scalable, as evidenced by large verification projects like seL4, and the ever growing Archive of 
  Formal Proofs.
  
  Now, it is entirely possible to reconstruct the Z mathematical toolkit in the way described above, 
  following the ISO standard, such that everything boils down to sets. However, there is a major 
  downside to this, which is that we cannot easily use the results in the HOL standard library (@{theory Main}) 
  and the Archive of Formal Proofs\footnote{Archive of Formal Proofs. \url{http://www.isa-afp.org}}, 
  since these are all built using the HOL type universe extension paradigm. There are also several 
  benefits to the HOL approach, notably that the type system can be used to deduce when a function 
  is closed under a set. This in turn greatly improves proof automation, since there is no 
  obligation to check well-formedness of expressions as part of the proof. Consequently, we chose
  to stick with the HOL approach.
  
  However, in order to be faithful with Z, we also implement the Z universe as a set of definitions,
  based on the ISO standard. Much of this already in implemented in the theory @{theory HOL.Relation},
  but we extend it with functions like application, domain restriction, and overriding, which
  are all part of the Z metalanguage. Crucially, this development is all based on sets and relations,
  not HOL functions, and therefore is a faithful encoding with Z. Upon this foundation, we construct
  a hierarchy of types corresponding to partial functions, finite functions, and total functions, 
  and we reuse the HOL @{typ "'a list"} type. We then prove that every HOL typed construction can
  be safely converted into a Z-like set-based construction, which provides the link between the
  efficiently implement HOL functions, and their Z counterparts.

  In order to achieve compatibility between this HOL type hierarchy, and the Z mathematical toolkit, 
  the principle problem to solve is the necessity of type coercions. As mentioned, in Z, sequences 
  are subtypes of sets, and so set-based functions can be directly applied to functions, which is 
  often benefical. For example, the domain of a sequence is the set of indices of that sequence. So 
  the technical goal s to allow HOL to accept expressions of this kind. Our solution is to use a 
  mixture of coercive subtyping and type overloading to achieve this. This allows the user to
  write Z expressions into Isabelle, which are then internally mapped into HOL expressions.

  There are basically two types of situation we need to capture. The first is the use of a more 
  abstract type (e.g. set) to act as a view on a more concrete type (e.g. a sequence). Thus
  we can find the length of a list by asking for its cardinality. The second is the composition
  of two abstract types. For example, concatenation of two sequences always results in a sequence,
  which is readily the case in HOL. There are more subtle examples, for example we can take union
  of two partial functions with disjoint domains, and produce a new partial function. In Z, we 
  would need to prove this, whereas with HOL's type system this can be deduced by construction.

  The first of these situations can be captured by coercive subtyping. In HOL, we can create a
  function between a concrete type @{typ "'c"} and an abstract type @{typ "'a"}, and request that 
  whenever a value of type @{typ "'a"} is required, but @{typ "'c"} is present, then the coercion
  @{term "f :: 'c \<Rightarrow> 'a"} is inserted automatically during type inference. The second situation
  can be solve by overloading the operators in Z that are essentially polymorphic. Union is a good
  example: in HOL we can create a polymorphic function symbol with different implementations for
  different types. Thus, we can take the union of two partial functions, under the aformentioned
  disjointness conditions. This development therefore implements the Z toolkit in this way.

  In conclusion, we wish to retain the generality of Z, whilst also taking full advantage of the
  automation afforded by Isabelle/HOL. We hope our theory development achieves this.
 \<close>

(*<*)
end
(*>*)