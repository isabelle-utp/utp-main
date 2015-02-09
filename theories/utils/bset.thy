(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: bset.thy                                                             *)
(* Author: Frank Zeyda, University of York (UK)                               *)
(******************************************************************************)
(* LAST REVIEWED: 24 March 2014 *)

header {* Bounded Sets *}

theory bset
imports Main infinity cardinals "Library_extra/FSet_extra"
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

lemma Collect_bset: 
  "A \<in> bset \<Longrightarrow> {x \<in> A. P x} \<in> bset"
  by (metis (no_types, lifting) mem_Collect_eq subsetI subset_bset)

lemma bset_Domain: "s \<in> bset \<Longrightarrow> Domain(s) \<in> bset"
  by (metis fst_eq_Domain image_bset)
  
lemma bset_Range: "s \<in> bset \<Longrightarrow> Range(s) \<in> bset"
  by (metis snd_eq_Range image_bset)
  
lemma bset_Times: "\<lbrakk> s \<in> bset; t \<in> bset \<rbrakk> \<Longrightarrow> s \<times> t \<in> bset"
  apply (simp add:bset_def)
  apply (metis countable_SIGMA countable_def countable_leq_nat_card leq_card_def nat_card_def)
done

lemma bset_relcomp: 
  assumes "s \<in> bset" "t \<in> bset"
  shows "s O t \<in> bset"
proof -
  have "s O t \<subseteq> Domain(s) \<times> Range(t)"
    by (auto)
  moreover have "Domain(s) \<times> Range(t) \<in> bset"
    by (metis assms bset_Domain bset_Range bset_Times)
  ultimately show ?thesis
    by (metis subset_bset)
qed

lemma bset_Id_on:
  assumes "s \<in> bset"
  shows "Id_on s \<in> bset"
proof -
  have "Id_on s \<subseteq> s \<times> s"
    by (metis Id_on_subset_Times)
  thus ?thesis
    by (metis assms bset_Times subset_bset)
qed

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

lift_definition bset_not_member ::
  "'a \<Rightarrow> 'a bset \<Rightarrow> bool" ("(_/ \<notin>\<^sub>b _)" [51, 51] 50)
is "op \<notin>" .

lift_definition bset_subset_eq ::
  "'a bset \<Rightarrow> 'a bset \<Rightarrow> bool" ("(_/ \<subseteq>\<^sub>b _)" [51, 51] 50)
is "op \<subseteq>" .

lift_definition bset_subset ::
  "'a bset \<Rightarrow> 'a bset \<Rightarrow> bool" ("(_/ \<subset>\<^sub>b _)" [51, 51] 50)
is "op \<subset>" .

lift_definition bset_set :: "'a list \<Rightarrow> 'a bset" is set
  apply (simp add: bset_def)
  apply (metis List.finite_set countable_finite countable_leq_nat_card nat_card_def)
done

lift_definition bcard :: "'a bset \<Rightarrow> nat" is card .

lift_definition bTimes :: "'a bset \<Rightarrow> 'b bset \<Rightarrow> ('a * 'b) bset" (infixr "\<times>\<^sub>b" 80) is "op \<times>"
  by (fact bset_Times)

lift_definition bDomain :: "('a * 'b) bset \<Rightarrow> 'a bset" is Domain
  by (fact bset_Domain)

lift_definition bRange :: "('a * 'b) bset \<Rightarrow> 'b bset" is Range
  by (fact bset_Range)

lift_definition bComp :: "('a * 'b) bset \<Rightarrow> ('b * 'c) bset \<Rightarrow> ('a * 'c) bset" is "op O"
  by (fact bset_relcomp)

lift_definition bId :: "'a bset \<Rightarrow> ('a * 'a) bset" is "Id_on"
  by (fact bset_Id_on)
  
lift_definition bfset :: "'a fset \<Rightarrow> 'a bset" is id
  apply (simp add:bset_def)
  apply (metis countable_finite countable_leq_nat_card nat_card_def)
done

lift_definition bfinite :: "'a bset \<Rightarrow> bool" is finite .
lift_definition blist :: "'a::linorder bset \<Rightarrow> 'a list" is sorted_list_of_set . 

text {* Default Simplifications *}

declare bset_empty.rep_eq [simp]
declare bset_insert.rep_eq [simp]
declare bset_uminus_def [simp]
declare bset_union.rep_eq [simp]
declare bset_inter.rep_eq [simp]
declare bset_minus.rep_eq [simp]
declare bset_member.rep_eq [simp]
declare bset_not_member.rep_eq [simp]
declare bset_subset_eq.rep_eq [simp]
declare bset_subset.rep_eq [simp]
declare bset_set.rep_eq [simp]

subsection {* Set Enumeration *}

syntax
  "_bset" :: "args => 'a bset" ("{(_)}\<^sub>b")

translations
  "{x, xs}\<^sub>b" == "(CONST bset_insert) x {xs}\<^sub>b"
  "{x}\<^sub>b"     == "(CONST bset_insert) x {}\<^sub>b"

subsection {* Set Comprehension *}

definition bset_Collect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a bset" where
"bset_Collect = (MkBSet o Collect)"
 
lift_definition bset_Coll :: "'a bset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a bset" is "\<lambda> A P. {x \<in> A. P x}" 
  by (fact Collect_bset)

lemma bset_Coll_equiv: "bset_Coll A P = bset_Collect (\<lambda> x. x \<in>\<^sub>b A \<and> P x)"
  by (simp add:bset_Collect_def bset_Coll_def)
  
declare bset_Collect_def [simp]

syntax
  "_bColl" :: "pttrn => bool => 'a bset" ("(1{_./ _}\<^sub>b)")

translations
  "{x . P}\<^sub>b" \<rightleftharpoons> "(CONST bset_Collect) (\<lambda> x . P)"

syntax (xsymbols)
  "_bCollect" :: "pttrn => 'a bset => bool => 'a bset"    ("(1{_ \<in>\<^sub>b/ _./ _}\<^sub>b)")
translations
  "{x \<in>\<^sub>b A. P}\<^sub>b" => "CONST bset_Coll A (\<lambda> x. P)"

lemma bset_CollectI: "P (a :: 'a::countable) \<Longrightarrow> a \<in>\<^sub>b {x. P x}\<^sub>b"
  by simp
  
lemma bset_CollI: "\<lbrakk> a \<in>\<^sub>b A; P a \<rbrakk> \<Longrightarrow> a \<in>\<^sub>b {x \<in>\<^sub>b A. P x}\<^sub>b"
  by (transfer, auto)
 
lemma bset_CollectD: "(a :: 'a::countable) \<in>\<^sub>b {x. P x}\<^sub>b \<Longrightarrow> P a"
  by simp

  lemma bset_Collect_cong: "(\<And>x. P x = Q x) ==> {x. P x}\<^sub>b = {x. Q x}\<^sub>b"
  by simp

-- {* Avoid eta-contraction for robust pretty-printing. *}

print_translation {*
 [Syntax_Trans.preserve_binder_abs_tr'
   @{const_syntax bset_Collect} @{syntax_const "_bColl"}]
*}

subsection {* BNF Integration *}

subsubsection {* Auxiliary Operators *}

lift_definition bset_image :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a bset \<Rightarrow> 'b bset)" (infixr "`\<^sub>b" 90)
is "image"
apply (metis image_bset)
done

definition bset_option :: "'a option bset \<Rightarrow> 'a bset option" where
"bset_option A = (if (bset_member None A) then None else Some (bset_image the A))"

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
    by (metis leq_card_iff_ordLeq)
  hence 1: "|c1 \<times> c2| \<le>o |c3 \<times> c2|"
    by (rule card_of_Times_mono1)
  from c2_leq_c3 have "|c2| \<le>o |c3|"
    by (metis leq_card_iff_ordLeq)
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
  by (metis card_of_Un_ordLeq_infinite leq_card_iff_ordLeq)

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

lemma bfset_inj:
  "inj bfset"
  apply (rule injI)
  apply (transfer)
  apply (simp)
done

definition "bBall A P = (\<forall>x. x \<in>\<^sub>b A \<longrightarrow> P x)"
definition "bBex A P = (\<exists>x. x \<in>\<^sub>b A \<longrightarrow> P x)"

declare bBall_def [mono,simp]
declare bBex_def [mono,simp]

syntax
  "_bBall" :: "pttrn => 'a bset => bool => bool" ("(3\<forall> _\<in>\<^sub>b_./ _)" [0, 0, 10] 10)
  "_bBex"  :: "pttrn => 'a bset => bool => bool" ("(3\<exists> _\<in>\<^sub>b_./ _)" [0, 0, 10] 10)

translations
  "\<forall> x\<in>\<^sub>bA. P" == "CONST bBall A (%x. P)"
  "\<exists> x\<in>\<^sub>bA. P" == "CONST bBex  A (%x. P)"
  
subsection {* Useful bounded sets *}

lift_definition bStrings :: "string bset" is UNIV
  by (fact countable_member_bset)

lift_definition bNats :: "'a::semiring_1 bset" is Nats
  by (metis Nats_def countable_member_bset image_bset)
  
lift_definition bInts :: "'a::ring_1 bset" is Ints
  by (metis Ints_def countable_member_bset image_bset)

lift_definition bRats :: "'a::field_char_0 bset" is Rats
  by (metis Rats_def countable_member_bset image_bset)

subsection {* Complete Lattice Operators *}
  
text {* In this section we prove that the supremum (big union) of a countable set of countable
        sets is again countable, and thus the supremum operator is closed. The proof proceeds
        by showing that countable sets can be encoded as infinite sequences, and then that
        merging two infinite sequences yields an infinite sequence. Thus we can also show that
        that the supremum yields a countable set. *}

text {* For any non-empty, countable set, A, there exists a sequence whose range is equal to A. *}
        
lemma seq_of_countable_exists: "\<lbrakk> A \<noteq> {}; A \<preceq>\<^sub>c c\<^sub>\<nat> \<rbrakk> \<Longrightarrow> \<exists> f :: nat \<Rightarrow> 'a. A = range(f)"
  by (metis inj_on_iff_surj leq_card_def subset_UNIV)

type_synonym 'a cseq = "nat \<Rightarrow> 'a"

text {* The merge operator uses a product encoding the renumber the indices of the sequence,
        yielding a sequence containing the elements from both sequences. *} 

definition merge_cseq :: "'a cseq cseq \<Rightarrow> 'a cseq" where
"merge_cseq s = (\<lambda> i. s (fst (prod_decode i)) (snd (prod_decode i)))"

definition seq_of_countable :: "'a set \<Rightarrow> 'a cseq" where
"seq_of_countable A = (SOME f :: nat \<Rightarrow> 'a. A = range(f))"

definition countable_of_seq :: "'a cseq \<Rightarrow> 'a set" where
"countable_of_seq f = range f"

lemma seq_of_countable_inv: 
  "\<lbrakk> A \<noteq> {}; A \<preceq>\<^sub>c c\<^sub>\<nat> \<rbrakk> \<Longrightarrow> countable_of_seq (seq_of_countable A) = A"
  apply (simp add:seq_of_countable_def countable_of_seq_def)
  apply (metis (mono_tags, lifting) seq_of_countable_exists tfl_some)
done
  
lift_definition seq_of_bset :: "'a bset \<Rightarrow> 'a cseq" is "seq_of_countable" .

lemma inj_seq_of_bset: "\<lbrakk> A \<noteq> {}\<^sub>b; B \<noteq> {}\<^sub>b; seq_of_bset A = seq_of_bset B \<rbrakk> \<Longrightarrow> A = B"
  by (metis MkBSet_cases MkBSet_inverse bset_empty.abs_eq bset_member nat_card_def seq_of_bset.rep_eq seq_of_countable_inv)

lemma member_countable_of_seq: 
  "x \<in> countable_of_seq F \<longleftrightarrow> (\<exists> i. F(i) = x)"
  by (auto simp add:countable_of_seq_def)

lemma Union_countable_of_seq:
  "\<Union> (countable_of_seq (countable_of_seq \<circ> F)) = countable_of_seq (merge_cseq F)"
  apply (auto simp add: member_countable_of_seq merge_cseq_def)
  apply (metis fst_conv prod_encode_inverse snd_conv)
  apply (metis comp_eq_dest_lhs member_countable_of_seq)
done

text {* Now we can show that the supremum and infimum operators are (mainly) closed over 
        bounded sets. Note that since there is no top bounded set in general we do not quite 
        have a complete lattice, though it's pretty close. *}

lemma Union_bset_aux:
  assumes Abset: "A \<in> bset" and contbset: "A \<subseteq> bset" and
  nempty: "A \<noteq> {}" and contnempty: "\<forall> a \<in> A. a \<noteq> {}"
  shows "\<Union> A \<in> bset"
proof -
  term "seq_of_countable \<circ> seq_of_countable A"

  have "A = (countable_of_seq (countable_of_seq \<circ> seq_of_countable \<circ> seq_of_countable A))"
    apply (subst seq_of_countable_inv[THEN sym])
    apply (metis nempty)
    apply (metis Abset bset_member nat_card_def)
    apply (metis (full_types) Abset bset_member comp_apply contbset contnempty member_countable_of_seq nat_card_def nempty seq_of_countable_inv subsetCE)
  done
  
  then obtain F where "A = (countable_of_seq (countable_of_seq \<circ> F))"
    by (metis fun.map_comp)

  moreover then have "\<Union> A = countable_of_seq (merge_cseq F)"
    by (metis Union_countable_of_seq)
    
  moreover have "countable_of_seq (merge_cseq F) \<in> bset"
    by (metis countable_member_bset countable_of_seq_def image_bset)
    
  ultimately show ?thesis
    by simp
qed

lemma Union_bset:
  assumes Abset: "A \<in> bset" and contbset: "A \<subseteq> bset"
  shows "\<Union> A \<in> bset"
proof (cases "A = {} \<or> A = {{}}")
  case True thus ?thesis
    by (metis Sup_empty cSup_singleton empty_bset)
next
  case False note as1 = this show ?thesis
  proof -
    have "\<Union> (A - {{}}) = \<Union> A"
      by auto
    moreover have "\<forall> a \<in> A - {{}}. a \<noteq> {}"
      by auto
    moreover with assms as1 have "\<Union> (A - {{}}) \<in> bset"
      by (auto intro: Union_bset_aux)
    ultimately show ?thesis
      by simp
  qed
qed

lemma Inter_bset:
  assumes "A \<noteq> {}" "A \<subseteq> bset"
  shows "\<Inter> A \<in> bset"
  by (metis Inf_lower all_not_in_conv assms subsetCE subset_bset)

lemma countable_finite_power: 
  "countable(A) \<Longrightarrow> countable {B. B \<subseteq> A \<and> finite(B)}"
  by (metis Collect_conj_eq Int_commute countable_Collect_finite_subset)
  
lemma bset_countable: "A \<in> bset \<longleftrightarrow> countable(A)"
  by (metis bset_def countable_def countable_leq_nat_card leq_card_def mem_Collect_eq nat_card_def) 
   
text {* Finite power set operator *}
  
lift_definition bPow :: "'a bset \<Rightarrow> 'a bset bset" is
"\<lambda> A. {B. B \<subseteq>\<^sub>b A \<and> bfinite(B)}"
proof -
  fix A
  have "{B :: 'a bset. B \<subseteq>\<^sub>b A \<and> bfinite B} = MkBSet ` {B :: 'a set. B \<subseteq> DestBSet A \<and> finite B}"
    apply (auto simp add: bfinite.rep_eq)
    apply (metis DestBSet_inverse imageI mem_Collect_eq)
  done
  
  moreover have "countable {B :: 'a set. B \<subseteq> DestBSet A \<and> finite B}"
    apply (rule countable_finite_power)
    apply (metis DestBSet bset_countable)
  done
  
  ultimately show "{B. B \<subseteq>\<^sub>b A \<and> bfinite B} \<in> bset"
  using bset_countable by auto
qed

(* Is there a way of getting this operator through the lifting mechanism? *)
  
definition BUnion :: "'a bset bset \<Rightarrow> 'a bset" ("\<Union>\<^sub>b_" [900] 900) where
"BUnion A = MkBSet (\<Union> (DestBSet ` DestBSet A))"

lemma BUnion_rep_eq [simp]: "DestBSet (BUnion A) = \<Union> (DestBSet ` DestBSet A)"
proof -
  have "\<Union> (DestBSet ` DestBSet A) \<in> bset"
    by (metis DestBSet Union_bset bset_image.rep_eq image_subset_iff)
  thus ?thesis
    by (metis BUnion_def MkBSet_inverse)
qed

lemma BUnion_lower: "a \<in>\<^sub>b A \<Longrightarrow> a \<subseteq>\<^sub>b \<Union>\<^sub>b A"
  by (auto simp add: bset_member.rep_eq BUnion_rep_eq)
  
lemma BUnion_greatest: "(\<And>x. x \<in>\<^sub>b A \<Longrightarrow> x \<subseteq>\<^sub>b z) \<Longrightarrow> \<Union>\<^sub>b A \<subseteq>\<^sub>b z" 
  by (auto simp add: bset_member.rep_eq BUnion_rep_eq)

definition BInter :: "'a bset bset \<Rightarrow> 'a bset" ("\<Inter>\<^sub>b_" [900] 900) where
"BInter A = MkBSet (\<Inter> (DestBSet ` DestBSet A))"

lemma BInter_rep_eq [simp]: 
  assumes "A \<noteq> {}\<^sub>b"
  shows "DestBSet (BInter A) = \<Inter> (DestBSet ` DestBSet A)"
proof -
  have "\<Inter> (DestBSet ` DestBSet A) \<in> bset"
    by (metis DestBSet DestBSet_inverse Inter_bset assms bset_empty.abs_eq image_is_empty image_subset_iff)
  thus ?thesis
    by (metis BInter_def MkBSet_inverse)
qed

subsection {* Default simplifications *}

lemma bfinite_empty [simp]: "bfinite {}\<^sub>b"
  by (transfer, simp)
  
lemma bfinite_insert [simp]: "bfinite A \<Longrightarrow> bfinite (bset_insert x A)"
  by (transfer, simp)
  
lemma bset_not_member_empty [simp]: "x \<notin>\<^sub>b {}\<^sub>b"
  by (transfer, simp)
  
lemma bset_not_member_insert [simp]: "\<lbrakk> x \<noteq> y; x \<notin>\<^sub>b A \<rbrakk> \<Longrightarrow> x \<notin>\<^sub>b bset_insert y A"
  by (transfer, simp)
  
lemma bcard_empty [simp]: "bcard {}\<^sub>b = 0"
  by (transfer, metis card_empty)
  
lemma bcard_insert_disjoint [simp]:
  "\<lbrakk> bfinite A; x \<notin>\<^sub>b A \<rbrakk> \<Longrightarrow> bcard (bset_insert x A) = Suc (bcard A)"
  by (transfer, auto)

end
