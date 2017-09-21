(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Time.thy                                                             *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@york.ac.uk and simon.foster@york.ac.uk                 *)
(******************************************************************************)
(* LAST REVIEWED: 14 Sept 2017 *)

section {* Time Model *}

theory Time
imports Positive_New Continuum Two
begin

text {*
  The rationale for this theory is to define an abstract model of time that
  identifies reasonable assumptions that are sufficient for reasoning about
  time, namely without having to specify in detail the notion of time that
  we are dealing with such as discrete, continuous or super-dense time.
*}

subsection {* Abstract Time *}

text {*
  We introduce permissible time domains abstractly as a type class. Clearly,
  the elements of the type have to be linearly ordered while membership to
  the class @{class semidom_divide} entails many key properties of addition,
  subtraction, multiplication and division. Note that we cannot require time
  to form a field as there may not be an additive inverse i.e.~if we confine
  ourselves to positive time instants. Lastly, we also assume that time does
  not stop, meaning that the ordering is unbounded (class @{class no_top});
  there may be a bottom though which, if so, must be the same as @{term 0}.
*}

class time = linorder + semidom_divide + no_top

text {*
  Positive time makes the additional assumption that the ordering has a bottom
  which must be @{const zero}.
*}

class pos_time = time + zero + order_bot +
assumes zero_is_bot: "0 = \<bottom>"

text {*
  I wonder if we can get away with weaker assumptions below. It would mean that
  we may also be able to instantiate @{typ "int pos"} as both @{class time} and
  @{class pos_time} (note that integers do not form a field). If not, this is
  not an issue of course, since we can otherwise always use @{typ nat} in place
  of the type @{typ "int pos"}.
*}

instance pos :: (linordered_field) time
apply (intro_classes)
done

instantiation pos :: (linordered_field) pos_time
begin
lift_definition bot_pos :: "'a pos"
is "0" ..
instance
apply (intro_classes)
apply (transfer; simp)
apply (transfer; simp)
done
end

subsection {* Discrete Time *}

text {* Naturals, integers and rationals are used to model discrete time. *}

instance nat :: time
apply (intro_classes)
done

instance int :: time
apply (intro_classes)
done

instance rat :: time
apply (intro_classes)
done

instantiation nat :: pos_time
begin
instance
apply (intro_classes)
apply (unfold bot_nat_def)
apply (rule refl)
done
end

subsection {* Continuous Time *}

text {* Reals and positive reals are used to model continuous time. *}

type_notation real ("\<real>")

type_synonym pos_real = "real pos" ("\<real>\<^sup>+")

translations (type) "\<real>\<^sup>+" \<leftharpoondown> (type) "real pos"

instance real :: time
apply (intro_classes)
done

text {*
  Membership of @{typ pos_real} to the sort @{class time} follows from the
  earlier instantiation of @{typ "'a pos"} as class @{class time}, provided
  the type parameter @{typ "'a"} constitutes a @{class linordered_field}.
*}

subsection {* Instantiations *}

text {* Instantiation of class @{class time}. *}

lemma "OFCLASS(nat, time_class)" ..
lemma "OFCLASS(int, time_class)" ..
lemma "OFCLASS(rat, time_class)" ..
lemma "OFCLASS(real, time_class)" ..
lemma "OFCLASS(rat pos, time_class)" ..
lemma "OFCLASS(real pos, time_class)" ..

text {* Instantiation of class @{class pos_time}. *}

lemma "OFCLASS(nat, pos_time_class)" ..
lemma "OFCLASS(rat pos, pos_time_class)" ..
lemma "OFCLASS(real pos, pos_time_class)" ..

text {* Instantiation of class @{class two}. *}

lemma "OFCLASS(nat, two_class)" ..
lemma "OFCLASS(int, two_class)" ..
lemma "OFCLASS(rat, two_class)" ..
lemma "OFCLASS(real, two_class)" ..
lemma "OFCLASS(int pos, two_class)" ..
lemma "OFCLASS(rat pos, two_class)" ..
lemma "OFCLASS(real pos, two_class)" ..

text {* Instantiation of class @{class continuum}. *}

lemma "OFCLASS(nat, continuum_class)" ..
lemma "OFCLASS(int, continuum_class)" ..
lemma "OFCLASS(rat, continuum_class)" ..
lemma "OFCLASS(real, continuum_class)" ..
lemma "OFCLASS(int pos, continuum_class)" ..
lemma "OFCLASS(rat pos, continuum_class)" ..
lemma "OFCLASS(real pos, continuum_class)" ..
end