(******************************************************************************)
(* Project: Mechanisation of the UTP                                          *)
(* File: utp/utp_common.thy                                                   *)
(* Author: Frank Zeyda, University of York                                    *)
(******************************************************************************)

header {* Common Definitions *}

theory utp_common
imports "utp_config" "utils/utp_sets"
begin

subsection {* Uncurrying *}

text {* Isabelle provides a currying operator but it seems none for uncurrying. *}

definition uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'c)" where
"uncurry f = (\<lambda> p . f (fst p) (snd p))"

declare uncurry [simp]

subsection {* Application of Relations *}

text {* It would be nice to have a neater syntax here. *}

definition RelApp :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" where
"RelApp r x = (THE y . y \<in> r `` {x})"

declare RelApp_def [simp]

subsection {* Coercion *}

definition Coerce :: "'a \<Rightarrow> ('a set) \<Rightarrow> 'a" (infix "\<hookrightarrow>" 100) where
"x \<hookrightarrow> s = (if x \<in> s then x else (SOME x . x \<in> s))"

text {* Fundamental Theorem *}

theorem Coerce_member :
"\<lbrakk>s \<noteq> {}\<rbrakk> \<Longrightarrow> x \<hookrightarrow> s \<in> s"
apply (simp add: Coerce_def)
apply (clarify)
apply (subgoal_tac "\<exists> x . x \<in> s")
apply (clarify)
apply (rule_tac a = "xa" in someI2)
apply (auto)
done

subsection {* Theorems *}

subsubsection {* Logic *}

theorem some_member_rule [simp, intro!]:
"s \<noteq> {} \<Longrightarrow> (SOME x . x \<in> s) \<in> s"
apply (auto)
apply (rule_tac Q = "(SOME x. x \<in> s) \<notin> s" in contrapos_pp)
apply (assumption)
apply (rule_tac a = "x" in someI2)
apply (simp_all)
done

subsubsection {* Sets and Pairs *}

theorem pairI :
"p = (fst p, snd p)"
apply (auto)
done

theorem non_empty_exists :
"s \<noteq> {} \<longleftrightarrow> (\<exists> x . x \<in> s)"
apply (auto)
done

subsubsection {* Functions *}

text {* Function Update *}

theorem fun_upd_cancel [simp] :
"f (x := f x) = f"
apply (auto)
done

theorem fun_upd_comm :
"x \<noteq> y \<Longrightarrow> f (x := a, y := b) = f (y := b, x := a)"
apply (rule ext)
apply (simp)
done

theorem image_chain_elim :
"f ` g ` a = {y . \<exists> x . x \<in> a \<and> y = f (g x)}"
apply (auto)
done

text {* Function Override *}

text {* We first define a neater syntax for function overriding. *}

notation override_on ("_ \<oplus> _ on _" [56, 56, 0] 55)

theorem override_on_idem [simp]:
"f \<oplus> f on a = f"
apply (simp add: override_on_def)
done

theorem override_on_comm :
"f \<oplus> g on a = g \<oplus> f on (- a)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_assoc :
"(f \<oplus> g on a) \<oplus> h on b = f \<oplus> (g \<oplus> h on b) on (a \<union> b)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_comm_sym :
"f \<oplus> g on (- a) = g \<oplus> f on a"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_singleton :
"(f \<oplus> g on {x}) = f(x := g x)"
apply (rule ext)
apply (auto)
done

theorem override_on_chain [simp] :
"(f \<oplus> g on a) \<oplus> g on b = f \<oplus> g on (a \<union> b)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_cancel1 [simp] :
"(f \<oplus> g on {x})(x := y) = f (x := y)"
apply (rule ext)
apply (auto)
done

theorem override_on_cancel2 [simp] :
"f \<oplus> (g \<oplus> f on a) on a = f"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_cancel3 [simp] :
"(f \<oplus> g on a) \<oplus> f on a = f"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_cancel3' [simp] :
"(f \<oplus> g on a) \<oplus> h on a = f \<oplus> h on a"
apply (simp add: override_on_def)
apply (rule ext)
apply(auto)
done

theorem override_on_cancel4 [simp] :
"f \<oplus> (g \<oplus> h on a) on (b - a) = f \<oplus> g on (b - a)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

theorem override_on_cancel5 [simp] :
"(f \<oplus> g on (a \<union> b)) \<oplus> h on (a \<union> c) = (f \<oplus> g on b) \<oplus> h on (a \<union> c)"
apply (simp add: override_on_def)
apply (rule ext)
apply (auto)
done

lemma override_on_cancel6: 
"f \<oplus> (g \<oplus> h on a) on a = f \<oplus> h on a"
  by (metis override_on_assoc override_on_chain override_on_emptyset)

lemma override_image[simp]: 
"(f \<oplus> g on a) ` b = f ` (b \<inter> -a) \<union> g ` (b \<inter> a)"
  by (auto simp add:override_on_def)

lemma override_before[simp]: 
"bij h \<Longrightarrow> ((f \<oplus> g on a) \<circ> h) = (f \<circ> h) \<oplus> (g \<circ> h) on (inv h) ` a"
  apply (auto simp add:bij_def override_on_def)
  apply (rule ext)
  apply (auto)
  apply (metis (lifting) image_surj_f_inv_f inj_image_mem_iff)
  apply (metis surj_f_inv_f)
done

lemma override_imageR[simp]: "(f \<oplus> g on a) ` a = g ` a"
  by (auto simp add:override_on_def)

lemma override_imageL[simp]: "a \<inter> b = {} \<Longrightarrow> (f \<oplus> g on a) ` b = f ` b"
  by (auto simp add:override_on_def)

subsubsection {* Function equivalence *}

definition beta_equiv ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow>
   ('a set) \<Rightarrow> bool" where
"(beta_equiv b1 b2 a) \<longleftrightarrow> (\<forall> x \<in> a . b1 x = b2 x)"

notation beta_equiv ("_ \<cong> _ on _")

theorem  beta_equiv_refl :
"b \<cong> b on a"
by (simp add: beta_equiv_def)

theorem  beta_equiv_comm :
"b1 \<cong> b2 on a \<Longrightarrow> b2 \<cong> b1 on a"
by (simp add: beta_equiv_def)

theorem  beta_equiv_trans :
"\<lbrakk>b1 \<cong> b2 on a; b2 \<cong> b3 on a\<rbrakk> \<Longrightarrow> b1 \<cong> b3 on a"
apply (simp add: beta_equiv_def)
done

lemma beta_equiv_single[simp]: "b1 x = b2 x \<Longrightarrow> b1 \<cong> b2 on {x}"
  by (simp add:beta_equiv_def)

lemma beta_equiv_combine[simp]: 
"\<lbrakk> b1 \<cong> b2 on a; b1 \<cong> b2 on b \<rbrakk> \<Longrightarrow> b1 \<cong> b2 on a \<union> b"
  by (auto simp add:beta_equiv_def)

theorem beta_equiv_override :
"b1 \<cong> b2 on a \<Longrightarrow> b1 \<oplus> b2 on a = b1"
apply (simp add: beta_equiv_def)
apply (rule ext)
apply (case_tac "x \<in> a")
apply (auto)
done

theorem beta_equiv_override_2 :
"a1 \<inter> a2 = {} \<Longrightarrow> b1 \<oplus> b2 on a1 \<cong> b1 on a2"
  by (auto simp add: beta_equiv_def override_on_def)

theorem beta_equiv_override_3 [simp] :
"f \<oplus> g on a \<cong> h on a = g \<cong> h on a"
  by (simp add: beta_equiv_def override_on_def)
 
theorem beta_equiv_override_4 [simp] :
"\<lbrakk> a \<subseteq> b; f \<oplus> g on a \<cong> h on b \<rbrakk> \<Longrightarrow> g \<cong> h on a"
apply (auto simp add: beta_equiv_def override_on_def)
apply (case_tac "x \<in> b")
apply (auto)
done

theorem beta_equiv_override_5 [simp] :
"\<lbrakk> a \<subseteq> b; f \<oplus> g on a \<cong> h on b \<rbrakk> \<Longrightarrow> f \<cong> h on b - a"
  by (auto simp add: beta_equiv_def override_on_def)

theorem beta_equiv_empty:
"a \<subseteq> {} \<Longrightarrow> b1 \<cong> b2 on a"
  by (simp add:beta_equiv_def)

theorem beta_equiv_union :
"b1 \<cong> b2 on (a \<union> b) = (b1 \<cong> b2 on a \<and> b1 \<cong> b2 on b)"
  by (auto simp add:beta_equiv_def)

theorem beta_equiv_subset :
"\<lbrakk> a \<subseteq> b; x \<cong> y on b \<rbrakk> \<Longrightarrow> x \<cong> y on a"
  by (metis Un_absorb1 beta_equiv_union)

theorem beta_equiv_override_intro1[intro]:
"\<lbrakk> f \<cong> h on b - a ; g \<cong> h on a \<inter> b \<rbrakk> \<Longrightarrow> f \<oplus> g on a \<cong> h on b"
  by (auto simp add:beta_equiv_def override_on_def)

subsubsection {* Bijections *}

text {* Bijections with two disjoint partitions *}

definition bij_split :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
"bij_split f a b \<equiv> bij_betw f a b \<and> bij_betw f (-a) (-b)"

theorem bij_comp_inject :
"bij g \<Longrightarrow> (f1 \<circ> g = f2 \<circ> g) = (f1 = f2)"
apply (safe)
apply (rule ext)
apply (subgoal_tac "\<exists> y . x = g y")
apply (clarify)
apply (drule_tac x = "y" in fun_cong)
apply (auto)
apply (simp add: bij_def surj_def)
done

declare bij_imp_bij_inv [simp, intro!]

lemma bij_betw_empty[simp]: "bij_betw f {} {}"
  by (simp add:bij_betw_def)

lemma bij_split_bij: 
"\<lbrakk> bij_split f a b \<rbrakk> \<Longrightarrow> bij f"
apply(simp add:bij_betw_def bij_split_def bij_def inj_on_def)
apply(auto)
apply(blast)+
done

lemma bij_split_id:
"bij_split id a a"
  by (simp add:bij_betw_def bij_split_def bij_def inj_on_def)

lemma bij_split_override:
"\<lbrakk> bij_split f a b; bij_betw g (-a) (-b) \<rbrakk> \<Longrightarrow> bij_split (g \<oplus> f on a) a b"
  by (auto simp add:bij_split_def bij_betw_def inj_on_def override_on_def)

declare bij_split_def[simp]

lemma override_bij:
  assumes "bij_betw f a a" "bij_betw g b b" "a \<inter> b = {}"
  shows "bij_betw (g \<oplus> f on a) (a \<union> b) (a \<union> b)"
proof -
  from assms have "inj_on (g \<oplus> f on a) (a \<union> b)"
    apply(simp add:bij_betw_def inj_on_def override_on_def)
    apply(clarify)
    apply (metis Int_iff Un_iff empty_iff imageI)
  done

  moreover from assms have " (g \<oplus> f on a) ` (a \<union> b) = a \<union> b"
  proof (auto simp add:bij_betw_def inj_on_def override_on_def)
    fix x
    assume "g ` b = b" "x \<notin> g ` ((a \<union> b) \<inter> {x. x \<notin> a})" "x \<in> b"
    moreover from assms have "(a \<union> b) \<inter> (-a) = b"
      by force

    ultimately show "x \<in> f ` ((a \<union> b) \<inter> a)"
      by (auto)
  qed

  ultimately show ?thesis
    by (simp add:bij_betw_def)
qed

lemma override_inv:
  assumes "bij_split f a b" "bij_split g a b"
  shows "(inv (g \<oplus> f on a)) = ((inv g) \<oplus> (inv f) on b)"
proof -
  from assms have "bij f" "bij g"
    by (metis bij_split_bij)+

  with assms show ?thesis
apply(auto)
apply(rule ext)
apply(simp add:bij_betw_def bij_def override_on_def)
apply(rule conjI)
apply(clarify)
apply(simp add:inv_f_f)
apply(rule inv_f_eq)
apply(simp add:inj_on_def)
apply(blast)
apply(force)
apply(subgoal_tac "\<exists>xa.(x = g xa)")
apply(clarify)
apply(simp add:inv_f_f)
apply(rule inv_f_eq)
apply(simp add:inj_on_def)
apply(auto)
done

qed

lemma override_inv_id:
  assumes "bij_split f a a"
  shows "inv (id \<oplus> f on a) = id \<oplus> inv f on a"
  by (metis assms bij_split_id inv_id override_inv)

lemma f_inv [simp]: "surj f \<Longrightarrow> f \<circ> inv f = id"
  by (metis surj_iff)

subsubsection {* Miscellaneous *}

theorem let_pair_simp [simp] :
"(let (a, b) = p in e a b) = e (fst p) (snd p)"
apply (auto)
apply (simp add: prod_case_beta)
done

theorem case_pair_simp [simp] :
"(case p of (x, y) \<Rightarrow> f x y) = f (fst p) (snd p)"
apply (subst pairI)
apply (simp add: prod_case_beta)
done

subsection {* Proof Experiments *}

theorem relapp_test_lemma :
"RelApp {(1::nat, 2::nat)} 1 = 2"
apply (simp)
done
end
