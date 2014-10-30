(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: bset.thy                                                             *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 24 March 2014 *)

header {* Bounded Sets *}

theory bset
imports Main infinity cardinals
begin

text {*
  We consider sets with bounded cardinalities here. Their main advantage is
  that we can use them in recursive constructor functions of (BNF) datatypes.
  They thus provide a limited facility for infinite sets in datatype-based
  models, for instance, of UTP values. For now, only countably-infinite sets
  are supported. It is, however, very easy to modify the theory in order to
  support higher cardinalities. Essentially, the only change needed is to
  alter the translation rule for @{text "c\<^sub>b\<^sub>s\<^sub>e\<^sub>t"}. In terms of proof, we must
  show that the cardinality bound is infinite. The theory @{theory infinity}
  provides support to automate such proofs for various common HOL types.
*}

subsection {* Cardinality Bound *}

syntax "_bset_limit" :: "logic" ("c\<^sub>b\<^sub>s\<^sub>e\<^sub>t")

text {* Change the cardinality bound by using a different HOL type. *}

translations "c\<^sub>b\<^sub>s\<^sub>e\<^sub>t" \<rightharpoonup> "c\<^sub>\<T> TYPE(nat)"

subsubsection {* Proof Obligation *}

text {*
  The theorem below is the only proviso for the bound. The simplifications
  that are introduced by the theory @{theory infinity} ought to suffice to
  automate its proof  when common HOL types are used to specify the bound.
*}

theorem infinite_bset_limit :
"infinite c\<^sub>b\<^sub>s\<^sub>e\<^sub>t"
apply (unfold type_card_def)
apply (unfold UNIV_TYPE_def)
apply (simp)
done

text {* If using @{text "c\<^sub>\<T> TYPE(...)"} the proof retains its validity. *}

theorem card_order_bset_limit :
"card_order |c\<^sub>b\<^sub>s\<^sub>e\<^sub>t|"
apply (unfold type_card_def)
apply (unfold UNIV_TYPE_def)
apply (rule card_of_card_order_on)
done

subsection {* Type Definition *}

definition bset :: "'a set set" where
"bset \<equiv> {s :: 'a set . s \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t}"

theorem bset_member (* [iff] *) :
"s \<in> bset \<longleftrightarrow> s \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t"
apply (simp add: bset_def)
done

typedef 'a bset = "bset :: 'a set set"
morphisms DestBSet MkBSet
apply (rule_tac x = "{}" in exI)
apply (simp add: bset_def)
apply (unfold leq_card_def)
apply (simp only: inj_on_empty image_empty empty_subsetI)
apply (simp)
done

subsection {* Proof Support *}

theorem DestBSet_inject_sym :
"(x = y) = (DestBSet x = DestBSet y)"
apply (rule sym [OF DestBSet_inject])
done

declare MkBSet_inverse [simp, intro!]
declare DestBSet_inverse [simp]
declare MkBSet_inject [simp]
declare DestBSet_inject_sym [simp]
declare DestBSet [simp]

theorem bset_intro [intro] :
"s \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t \<Longrightarrow> s \<in> bset"
apply (simp add: bset_member)
done

theorem bset_dest [dest] :
"s \<in> bset \<Longrightarrow> s \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t"
apply (simp add: bset_member)
done

subsection {* Closure Theorems *}

theorem empty_bset :
"{} \<in> bset"
apply (unfold bset_member)
apply (simp add: leq_card_empty)
done

theorem insert_bset :
"\<lbrakk>s \<in> bset\<rbrakk> \<Longrightarrow> (insert x s) \<in> bset"
apply (unfold bset_member)
apply (insert infinite_bset_limit)
apply (unfold type_card_def)
apply (unfold UNIV_TYPE_def)
apply (unfold leq_card_iff_ordLeq)
apply (subgoal_tac "insert x s = s \<union> {x}")
apply (erule ssubst)
apply (erule card_of_Un_ordLeq_infinite)
apply (assumption)
apply (rule card_of_singl_ordLeq)
apply (simp_all)
done

theorem subset_bset :
"\<lbrakk>s \<subseteq> t; t \<in> bset\<rbrakk> \<Longrightarrow> s \<in> bset"
apply (unfold bset_member)
apply (metis leq_card_subset leq_card_trans)
done

theorem union_bset :
"\<lbrakk>s \<in> bset; t \<in> bset\<rbrakk> \<Longrightarrow> (s \<union> t) \<in> bset"
apply (unfold bset_member)
apply (insert infinite_bset_limit)
apply (unfold type_card_def)
apply (unfold UNIV_TYPE_def)
apply (unfold leq_card_iff_ordLeq)
apply (metis card_of_Un_ordLeq_infinite)
done

theorem inter1_bset :
"\<lbrakk>s \<in> bset\<rbrakk> \<Longrightarrow> (s \<inter> t) \<in> bset"
apply (subgoal_tac "s \<inter> t \<subseteq> s")
apply (erule subset_bset)
apply (assumption)
apply (auto)
done

theorem inter2_bset :
"\<lbrakk>t \<in> bset\<rbrakk> \<Longrightarrow> (s \<inter> t) \<in> bset"
apply (subgoal_tac "s \<inter> t \<subseteq> t")
apply (erule subset_bset)
apply (assumption)
apply (auto)
done

theorem minus_bset :
"\<lbrakk>s \<in> bset\<rbrakk> \<Longrightarrow> s - t \<in> bset"
apply (subgoal_tac "s - t \<subseteq> s")
apply (erule subset_bset)
apply (assumption)
apply (auto)
done

theorem image_bset :
"s \<in> bset \<Longrightarrow> (f ` s) \<in> bset"
apply (unfold bset_member)
apply (erule leq_image_mono)
done

theorem countable_member_bset :
"(s :: 'a::countable set) \<in> bset"
apply (unfold bset_member)
apply (insert infinite_bset_limit)
apply (drule infinite_nat_card_leq)
apply (subgoal_tac "s \<preceq>\<^sub>c c\<^sub>\<nat>")
apply (erule leq_card_trans)
apply (assumption)
apply (simp add: countable_leq_nat_card)
done

subsection {* Default Simplifications *}

declare empty_bset [simp]
declare insert_bset [simp, intro!]
declare subset_bset [simp, intro]
declare union_bset [simp, intro!]
declare inter1_bset [simp, intro]
declare inter2_bset [simp, intro]
declare minus_bset [simp, intro!]
declare image_bset [simp, intro]
declare countable_member_bset [simp]

subsection {* Lifted Operators *}

setup_lifting type_definition_bset

lift_definition bset_empty :: "'a bset" ("{}\<^sub>b")is
"{}"
apply (metis empty_bset)
done

lift_definition bset_insert :: "'a \<Rightarrow> 'a bset \<Rightarrow> 'a bset" is
"insert"
apply (metis insert_bset)
done

text {* Lifting fails as @{const bset} is not closed under set complement. *}

definition bset_uminus ::
  "'a bset \<Rightarrow> 'a bset" ("-\<^sub>b _" [81] 80) where
"-\<^sub>b s = MkBSet(-DestBSet s)"

lift_definition bset_union ::
  "'a bset \<Rightarrow> 'a bset \<Rightarrow> 'a bset" (infixl "\<union>\<^sub>b" 65)
is "op \<union>"
apply (metis union_bset)
done

lift_definition bset_inter ::
  "'a bset \<Rightarrow> 'a bset \<Rightarrow> 'a bset" (infixl "\<inter>\<^sub>b" 70)
is "op \<inter>"
apply (metis inter1_bset)
done

lift_definition bset_minus ::
  "'a bset \<Rightarrow> 'a bset \<Rightarrow> 'a bset" (infixl "-\<^sub>b" 65)
is "op -"
apply (metis minus_bset)
done

lift_definition bset_member ::
  "'a \<Rightarrow> 'a bset \<Rightarrow> bool" ("(_/ \<in>\<^sub>b _)" [51, 51] 50)
is "op \<in>" .

lift_definition bset_subset_eq ::
  "'a bset \<Rightarrow> 'a bset \<Rightarrow> bool" ("(_/ \<subseteq>\<^sub>b _)" [51, 51] 50)
is "op \<subseteq>" .

lift_definition bset_subset ::
  "'a bset \<Rightarrow> 'a bset \<Rightarrow> bool" ("(_/ \<subset>\<^sub>b _)" [51, 51] 50)
is "op \<subset>" .

text {* Default Simplifications *}

declare bset_empty.rep_eq [simp]
declare bset_insert.rep_eq [simp]
declare bset_uminus_def [simp]
declare bset_union.rep_eq [simp]
declare bset_inter.rep_eq [simp]
declare bset_minus.rep_eq [simp]
declare bset_member.rep_eq [simp]
declare bset_subset_eq.rep_eq [simp]
declare bset_subset.rep_eq [simp]

subsection {* Set Enumeration *}

syntax
  "_bset" :: "args => 'a bset" ("{(_)}\<^sub>b")

translations
  "{x, xs}\<^sub>b" == "(CONST bset_insert) x {xs}\<^sub>b"
  "{x}\<^sub>b"     == "(CONST bset_insert) x {}\<^sub>b"

subsection {* Set Comprehension *}

definition bset_Collect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a bset" where
"bset_Collect = (MkBSet o Collect)"

declare bset_Collect_def [simp]

syntax
  "_bColl" :: "pttrn => bool => 'a bset" ("(1{_./ _}\<^sub>b)")

translations
  "{x . P}\<^sub>b" \<rightleftharpoons> "(CONST bset_Collect) (\<lambda> x . P)"

-- {* Avoid eta-contraction for robust pretty-printing. *}

print_translation {*
 [Syntax_Trans.preserve_binder_abs_tr'
   @{const_syntax bset_Collect} @{syntax_const "_bColl"}]
*}

subsection {* BNF Integration *}

subsubsection {* Auxiliary Operators *}

lift_definition bset_image :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a bset \<Rightarrow> 'b bset)"
is "image"
apply (metis image_bset)
done

lift_definition bset_rel ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a bset \<Rightarrow> 'b bset \<Rightarrow> bool"
is "rel_set" .

subsubsection {* Instantiation Lemmas *}

theorem times_ordLeq_infinite :
  assumes inf_c3 : "infinite c3"
  assumes c1_leq_c3 : "c1 \<preceq>\<^sub>c c3"
  assumes c2_leq_c3 : "c2 \<preceq>\<^sub>c c3"
  shows "(c1 \<times> c2) \<preceq>\<^sub>c c3"
proof
  from c1_leq_c3 have "|c1| \<le>o |c3|"
    by (simp add: card_transfer)
  hence 1: "|c1 \<times> c2| \<le>o |c3 \<times> c2|"
    by (rule card_of_Times_mono1)
  from c2_leq_c3 have "|c2| \<le>o |c3|"
    by (simp add: card_transfer)
  hence 2: "|c3 \<times> c2| \<le>o |c3 \<times> c3|"
    by (rule card_of_Times_mono2)
  from 1 and 2 have 3: "|c1 \<times> c2| \<le>o |c3 \<times> c3|"
    by (rule ordLeq_transitive)
  from inf_c3 have "|c3 \<times> c3| =o |c3|"
    by (rule card_of_Times_same_infinite)
  hence 4: "|c3 \<times> c3| \<le>o |c3|"
    by (simp add: ordIso_iff_ordLeq)
  from 3 and 4 show "|c1 \<times> c2| \<le>o |c3|"
    by (rule ordLeq_transitive)
qed

theorem union_ordLeq_infinite :
"infinite c3 \<Longrightarrow> c1 \<preceq>\<^sub>c c3 \<Longrightarrow> c2 \<preceq>\<^sub>c c3 \<Longrightarrow> (c1 \<union> c2) \<preceq>\<^sub>c c3"
apply (simp add: card_transfer)
done

theorem image_leq_cardD :
"(f ` A) \<preceq>\<^sub>c c \<Longrightarrow> \<exists> B \<subseteq> A . B \<preceq>\<^sub>c c \<and> f ` B = f ` A"
apply (rule_tac x = "(inv_into A f) ` (f ` A)" in exI)
apply (safe)
apply (simp_all)
-- {* Subgoal 1 *}
apply (rule inv_into_into)
apply (simp)
-- {* Subgoal 2 *}
apply (erule leq_image_mono)
-- {* Subgoal 3 *}
apply (rule imageI)
apply (rule inv_into_into)
apply (simp)
-- {* Subgoal 4 *}
apply (simp add: image_inv_into_cancel)
done

lemma leq_card_rel_set_lemma :
"infinite c\<^sub>b\<^sub>s\<^sub>e\<^sub>t \<Longrightarrow>
 A \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t \<Longrightarrow>
 B \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t \<Longrightarrow>
 {(x, y). x \<in> A \<and> y \<in> B \<and> R x y} \<preceq>\<^sub>c c\<^sub>b\<^sub>s\<^sub>e\<^sub>t"
apply (rule_tac B = "A \<times> B" in leq_card_trans)
-- {* Subgoal 1 *}
apply (rule leq_card_subset)
apply (auto) [1]
-- {* Subgoal 2 *}
apply (erule times_ordLeq_infinite)
apply (assumption)+
done

subsubsection {* BNF Registration *}

bnf "'a bset"
  map: bset_image
  sets: DestBSet 
  bd: "|c\<^sub>b\<^sub>s\<^sub>e\<^sub>t|"
  wits: "bset_empty"
  rel: bset_rel
apply -
-- {* Subgoal 1 *}
apply (rule ext)
apply (transfer)
apply (simp)
-- {* Subgoal 2 *}
apply (rule ext)
apply (transfer)
apply (simp add: image_comp)
-- {* Subgoal 3 *}
apply (transfer)
apply (simp add: image_def)
-- {* Subgoal 4 *}
apply (rule ext)
apply (transfer)
apply (simp)
-- {* Subgoal 5 *}
apply (rule card_order_bset_limit)
-- {* Subgoal 6 *}
apply (unfold cinfinite_def)
apply (unfold Field_card_of)
apply (rule infinite_bset_limit)
-- {* Subgoal 7 *}
apply (transfer)
apply (unfold bset_member)
apply (simp add: bset_member leq_card_iff_ordLeq)
-- {* Subgoal 8 *}
apply (auto)[1]
apply (transfer)
apply (simp add: rel_set_def)
apply (unfold bset_member)
apply (auto)[1]
apply (metis relcompp.simps)
apply (metis relcompp.relcompI)
-- {* Subgoal 9 *}
apply (rule ext)+
apply (rename_tac R x y)
apply (simp add: Grp_def relcompp.simps conversep.simps)
apply (transfer)
apply (clarsimp)
apply (auto)
-- {* Subgoal 9.1 *}
apply (simp add: bset_def)
apply (rule_tac x = "{(a, b) . a \<in> x \<and> b \<in> y \<and> R a b}" in exI)
apply (simp add: infinite_bset_limit leq_card_rel_set_lemma)
apply (simp add: rel_set_def)
apply (clarify)
apply (simp add: image_def)
apply (safe) [1]
apply (metis)
apply (metis)
-- {* Subgoal 9.2 *}
apply (simp add: rel_set_def)
apply (safe)
apply (metis Collect_splitD set_rev_mp)
apply (metis Collect_splitD set_rev_mp)
done
end
