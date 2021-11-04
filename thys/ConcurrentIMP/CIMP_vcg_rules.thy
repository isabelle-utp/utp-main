(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP_vcg_rules
imports
  CIMP_vcg
begin

(*>*)
subsubsection\<open> VCG rules \label{sec:cimp:vcg_rules} \<close>

text\<open>

We can develop some (but not all) of the familiar Hoare rules; see
@{cite [cite_macro=citet] "DBLP:journals/acta/Lamport80"} and the
seL4/l4.verified lemma buckets for inspiration. We avoid many of the
issues Lamport mentions as we only treat basic (atomic) commands.

\<close>

context
  fixes coms :: "('answer, 'location, 'proc, 'question, 'state) programs"
  fixes p :: "'proc"
  fixes aft :: "('answer, 'location, 'question, 'state) loc_comp"
begin

abbreviation
  valid_syn :: "('answer, 'location, 'proc, 'question, 'state) state_pred
             \<Rightarrow> ('answer, 'location, 'question, 'state) com
             \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred \<Rightarrow> bool" where
  "valid_syn P c Q \<equiv> coms, p, aft \<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
notation valid_syn ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>")

abbreviation
  valid_inv_syn :: "('answer, 'location, 'proc, 'question, 'state) state_pred
                  \<Rightarrow> ('answer, 'location, 'question, 'state) com \<Rightarrow> bool" where
  "valid_inv_syn P c \<equiv> \<lbrace>P\<rbrace> c \<lbrace>P\<rbrace>"
notation valid_inv_syn ("\<lbrace>_\<rbrace>/ _")

lemma vcg_True:
  "\<lbrace>P\<rbrace> c \<lbrace>\<langle>True\<rangle>\<rbrace>"
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_conj:
  "\<lbrakk> \<lbrace>I\<rbrace> c \<lbrace>Q\<rbrace>; \<lbrace>I\<rbrace> c \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>I\<rbrace> c \<lbrace>Q \<^bold>\<and> R\<rbrace>"
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_pre_imp:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> Q s; \<lbrace>Q\<rbrace> c \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> c \<lbrace>R\<rbrace>"
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemmas vcg_pre = vcg_pre_imp[rotated]

lemma vcg_post_imp:
  "\<lbrakk> \<And>s. Q s \<Longrightarrow> R s; \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> c \<lbrace>R\<rbrace>"
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_prop[intro]:
  "\<lbrace>\<langle>P\<rangle>\<rbrace> c"
by (cases c) (fastforce intro: vcg.intros)+

lemma vcg_drop_imp:
  assumes "\<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> c \<lbrace>R \<^bold>\<longrightarrow> Q\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_conj_lift:
  assumes x: "\<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  shows      "\<lbrace>P \<^bold>\<and> P'\<rbrace> c \<lbrace>Q \<^bold>\<and> Q'\<rbrace>"
apply (rule vcg_conj)
 apply (rule vcg_pre[OF x], simp)
apply (rule vcg_pre[OF y], simp)
done

lemma vcg_disj_lift:
  assumes x: "\<lbrace>P\<rbrace>  c \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  shows      "\<lbrace>P \<^bold>\<or> P'\<rbrace> c \<lbrace>Q \<^bold>\<or> Q'\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_imp_lift:
  assumes "\<lbrace>P'\<rbrace> c \<lbrace>\<^bold>\<not> P\<rbrace>"
  assumes "\<lbrace>Q'\<rbrace> c \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P' \<^bold>\<or> Q'\<rbrace> c \<lbrace>P \<^bold>\<longrightarrow> Q\<rbrace>"
by (simp only: imp_conv_disj vcg_disj_lift[OF assms])

lemma vcg_ex_lift:
  assumes "\<And>x. \<lbrace>P x\<rbrace> c \<lbrace>Q x\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> c \<lbrace>\<lambda>s. \<exists>x. Q x s\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_all_lift:
  assumes "\<And>x. \<lbrace>P x\<rbrace> c \<lbrace>Q x\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> c \<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_name_pre_state:
  assumes "\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> c \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_lift_comp:
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (f s :: 'a :: type)\<rbrace> c"
  assumes P: "\<And>x. \<lbrace>Q x\<rbrace> c \<lbrace>P x\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q (f s) s\<rbrace> c \<lbrace>\<lambda>s. P (f s) s\<rbrace>"
apply (rule vcg_name_pre_state)
apply (rename_tac s)
apply (rule vcg_pre)
 apply (rule vcg_post_imp[rotated])
  apply (rule vcg_conj_lift)
   apply (rule_tac x="f s" in P)
  apply (rule_tac P="\<lambda>fs. fs = f s" in f)
 apply simp
apply simp
done


subsubsection\<open>Cheap non-interference rules\<close>

text\<open>

These rules magically construct VCG lifting rules from the easier to
prove \<open>eq_imp\<close> facts. We don't actually use these in the GC,
but we do derive @{const "fun_upd"} equations using the same
mechanism. Thanks to Thomas Sewell for the requisite syntax magic.

As these \<open>eq_imp\<close> facts do not usefully compose, we make the
definition asymmetric (i.e., \<open>g\<close> does not get a bundle of
parameters).

Note that these are effectively parametricity rules.

\<close>

definition eq_imp :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'e) \<Rightarrow> bool" where
  "eq_imp f g \<equiv> (\<forall>s s'. (\<forall>x. f x s = f x s') \<longrightarrow> (g s = g s'))"

lemma eq_impD:
  "\<lbrakk> eq_imp f g; \<forall>x. f x s = f x s' \<rbrakk> \<Longrightarrow> g s = g s'"
by (simp add: eq_imp_def)

lemma eq_imp_vcg:
  assumes g: "eq_imp f g"
  assumes f: "\<forall>x P. \<lbrace>P \<circ> (f x)\<rbrace> c"
  shows "\<lbrace>P \<circ> g\<rbrace> c"
apply (rule vcg_name_pre_state)
apply (rename_tac s)
apply (rule vcg_pre)
 apply (rule vcg_post_imp[rotated])
  apply (rule vcg_all_lift[where 'a='a])
  apply (rule_tac x=x and P="\<lambda>fs. fs = f x s" in f[rule_format])
 apply simp
 apply (frule eq_impD[where f=f, OF g])
 apply simp
apply simp
done

lemma eq_imp_vcg_LST:
  assumes g: "eq_imp f g"
  assumes f: "\<forall>x P. \<lbrace>P \<circ> (f x) \<circ> LST\<rbrace> c"
  shows "\<lbrace>P \<circ> g \<circ> LST\<rbrace> c"
apply (rule vcg_name_pre_state)
apply (rename_tac s)
apply (rule vcg_pre)
 apply (rule vcg_post_imp[rotated])
  apply (rule vcg_all_lift[where 'a='a])
  apply (rule_tac x=x and P="\<lambda>fs. fs = f x s\<down>" in f[rule_format])
 apply simp
 apply (frule eq_impD[where f=f, OF g])
 apply simp
apply simp
done

lemma eq_imp_fun_upd:
  assumes g: "eq_imp f g"
  assumes f: "\<forall>x. f x (s(fld := val)) = f x s"
  shows "g (s(fld := val)) = g s"
apply (rule eq_impD[OF g])
apply (rule f)
done

lemma curry_forall_eq:
  "(\<forall>f. P f) = (\<forall>f. P (case_prod f))"
by (metis case_prod_curry)

lemma pres_tuple_vcg:
  "(\<forall>P. \<lbrace>P \<circ> (\<lambda>s. (f s, g s))\<rbrace> c)
    \<longleftrightarrow> ((\<forall>P. \<lbrace>P \<circ> f\<rbrace> c) \<and> (\<forall>P. \<lbrace>P \<circ> g\<rbrace> c))"
apply (simp add: curry_forall_eq o_def)
apply safe
  apply fast
 apply fast
apply (rename_tac P)
apply (rule_tac f="f" and P="\<lambda>fs s. P fs (g s)" in vcg_lift_comp; simp)
done

lemma pres_tuple_vcg_LST:
  "(\<forall>P. \<lbrace>P \<circ> (\<lambda>s. (f s, g s)) \<circ> LST\<rbrace> c)
    \<longleftrightarrow> ((\<forall>P. \<lbrace>P \<circ> f \<circ> LST\<rbrace> c) \<and> (\<forall>P. \<lbrace>P \<circ> g \<circ> LST\<rbrace> c))"
apply (simp add: curry_forall_eq o_def)
apply safe
  apply fast
 apply fast
apply (rename_tac P)
apply (rule_tac f="\<lambda>s. f s\<down>" and P="\<lambda>fs s. P fs (g s)" for g in vcg_lift_comp; simp)
done

no_notation valid_syn ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>")

end

(*<*)

end
(*>*)
