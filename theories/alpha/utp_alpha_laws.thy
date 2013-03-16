(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_laws.thy                                                   *)
(* Author: Simon Foster and Frank Zeyda, University of York (UK)              *)
(******************************************************************************)

header {* Algebraic Laws *}

theory utp_alpha_laws
imports 
  utp_alpha_pred 
  utp_alpha_rel 
  "../tactics/utp_alpha_expr_tac" 
  "../parser/utp_alpha_pred_parser"
begin

subsection {* Basic properties *}

theorem AndA_assoc:
  "`p \<and> (q \<and> r)` = `(p \<and> q) \<and> r`"
  by (utp_alpha_tac2, utp_pred_tac)

theorem AndA_comm:
  "`p \<and> q` = `q \<and> p`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

theorem AndA_idem [simp]:
  "`p \<and> p` = `p`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

theorem OrA_assoc:
  "`p \<or> (q \<or> r)` = `(p \<or> q) \<or> r`"
  by (utp_alpha_tac2, utp_pred_tac)

theorem OrA_comm:
  "`p \<or> q` = `q \<or> p`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

theorem OrA_idem [simp]:
  "`p \<or> p` = `p`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

lemma AndA_OrA_dist:
  "`(p \<or> q) \<and> r` = `(p \<and> r) \<or> (q \<and> r)`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

lemma OrA_AndA_dist:
  "`(p \<and> q) \<or> r` = `(p \<or> r) \<and> (q \<or> r)`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

lemma demorgan1: "`\<not>(x\<or>y)` = `(\<not>x)\<and>(\<not>y)`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

lemma demorgan2: "`\<not>(x\<and>y)` = `(\<not>x)\<or>(\<not>y)`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

lemma demorgan3: "`x\<or>y` = `\<not>((\<not>x)\<and>(\<not>y))`"
  by (utp_alpha_tac2, utp_pred_auto_tac)

subsection {* Conditional Laws *}

theorem CondA_unfold:
"\<lbrakk> p \<in> WF_RELATION; q \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> p = \<alpha> q; \<alpha> b \<subseteq>\<^sub>f \<alpha> p \<rbrakk> \<Longrightarrow>
  p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q = (b \<and>\<alpha> p) \<or>\<alpha> (\<not>\<alpha> b \<and>\<alpha> q)"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem CondA_idem:
"\<lbrakk>p \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> b \<subseteq>\<^sub>f \<alpha> p\<rbrakk> \<Longrightarrow> 
 p \<triangleleft>\<alpha> b \<alpha>\<triangleright> p = p"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem CondA_sym:
"\<lbrakk>p \<in> WF_RELATION; q \<in> WF_RELATION; b \<in> WF_CONDITION; \<alpha> p = \<alpha> q; \<alpha> b \<subseteq>\<^sub>f \<alpha> p\<rbrakk> \<Longrightarrow> 
  p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q = q \<triangleleft>\<alpha> \<not>\<alpha> b \<alpha>\<triangleright> p"
  by (utp_alpha_tac, utp_pred_auto_tac)

theorem CondA_assoc:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
    "b \<in> WF_CONDITION" "c \<in> WF_CONDITION" 
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p" "\<alpha> b = \<alpha> c"
  shows "(p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q) \<triangleleft>\<alpha> c \<alpha>\<triangleright> r = p \<triangleleft>\<alpha> b \<and>\<alpha> c \<alpha>\<triangleright> (q \<triangleleft>\<alpha> c \<alpha>\<triangleright> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_distr:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" 
    "b \<in> WF_CONDITION" "c \<in> WF_CONDITION" 
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p" "\<alpha> b = \<alpha> c"
  shows "p \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q \<triangleleft>\<alpha> c \<alpha>\<triangleright> r) = (p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q) \<triangleleft>\<alpha> c \<alpha>\<triangleright> (p \<triangleleft>\<alpha> b \<alpha>\<triangleright> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_unit:
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "\<alpha> p = \<alpha> q"
  shows "p \<triangleleft>\<alpha> true (\<alpha> p) \<alpha>\<triangleright> q = q \<triangleleft>\<alpha> false (\<alpha> p) \<alpha>\<triangleright> p"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done


theorem CondA_conceal:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" "b \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p"
  shows "p \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q \<triangleleft>\<alpha> b \<alpha>\<triangleright> r) = p \<triangleleft>\<alpha> b \<alpha>\<triangleright> r"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_disj:
  assumes
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "b \<in> WF_CONDITION" "c \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> c \<subseteq>\<^sub>f \<alpha> p" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p"
  shows "p \<triangleleft>\<alpha> b \<alpha>\<triangleright> (p \<triangleleft>\<alpha> c \<alpha>\<triangleright> q) = p \<triangleleft>\<alpha> b \<or>\<alpha> c \<alpha>\<triangleright> q"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem CondA_refinement:
  assumes
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" "b \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p"
  shows "p \<sqsubseteq>\<alpha> (q \<triangleleft>\<alpha> b \<alpha>\<triangleright> r) = (p \<sqsubseteq>\<alpha> b \<and>\<alpha> q) \<and>\<alpha> (p \<sqsubseteq>\<alpha> \<not>\<alpha> b \<and>\<alpha> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem AndA_refinement:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r"
  shows "(p \<and>\<alpha> q) \<sqsubseteq>\<alpha> r = (p \<sqsubseteq>\<alpha> r) \<and>\<alpha> (q \<sqsubseteq>\<alpha> r)"
  apply (insert assms)
  apply (utp_alpha_tac)
  apply (utp_pred_auto_tac)
done

theorem UNREST_WF_RELATION_DASHED_TWICE[unrest]: 
"r \<in> WF_RELATION \<Longrightarrow> UNREST DASHED_TWICE (\<pi> r)"
  apply (auto simp add:WF_RELATION_def WF_ALPHA_PREDICATE_def WF_PREDICATE_OVER_def REL_ALPHABET_def)
  apply (rule_tac ?vs1.0="VAR - \<langle>\<alpha> r\<rangle>\<^sub>f" in UNREST_subset)
  apply (auto)
done

theorem UNREST_WF_CONDITION_DASHED[unrest]: 
"r \<in> WF_CONDITION \<Longrightarrow> UNREST DASHED (\<pi> r)"
  by (simp add:WF_CONDITION_def)

theorem SemiA_CondA_distr:
  assumes 
    "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION" "b \<in> WF_CONDITION"
    "\<alpha> p = \<alpha> q" "\<alpha> q = \<alpha> r" "\<alpha> b \<subseteq>\<^sub>f \<alpha> p"
  shows "(p \<triangleleft>\<alpha> b \<alpha>\<triangleright> q) ;\<alpha> r = (p ;\<alpha> r) \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q ;\<alpha> r)"
proof -
  from assms have "\<alpha> b \<subseteq>\<^sub>f \<alpha> (p ;\<alpha> r)"
    apply (simp add:WF_CONDITION_def)
    apply (simp add:alphabet in_out_union closure)
  done
    
  moreover hence "(p ;\<alpha> r) \<triangleleft>\<alpha> b \<alpha>\<triangleright> (q ;\<alpha> r) \<in> WF_RELATION"
    by (simp add:closure alphabet assms)

  moreover from assms have "\<alpha> b \<subseteq>\<^sub>f \<alpha> (q ;\<alpha> r)"
    apply (simp add:WF_CONDITION_def)
    apply (simp add:alphabet in_out_union closure)
  done

  ultimately show ?thesis using assms
    apply (utp_alpha_tac)
    apply (rule_tac SemiR_CondR_distr)
    apply (auto intro:SemiR_CondR_distr unrest closure simp add:EvalA_def)
  done
qed

theorem RenameA_TRUE [urename]: 
"TRUE[ss]\<alpha> = TRUE"
  by (utp_alpha_tac, utp_pred_tac)

theorem RenameA_FALSE [urename]: 
"FALSE[ss]\<alpha> = FALSE"
  by (utp_alpha_tac, utp_pred_tac)

theorem RenameA_id [urename]:
"p[id\<^sub>s]\<alpha> = p"
  by (utp_alpha_tac2, simp add:RenameP_id)

theorem RenameA_inverse1 :
"p[ss]\<alpha>[inv\<^sub>s ss]\<alpha> = p"
  by (utp_alpha_tac2, simp add:RenameP_inverse1)

theorem RenameA_inverse2 :
"p[inv\<^sub>s ss]\<alpha>[ss]\<alpha> = p"
  by (utp_alpha_tac2, simp add:RenameP_inverse2)

theorem RenameA_compose :
"p[ss1]\<alpha>[ss2]\<alpha> = p[ss2 \<circ>\<^sub>s ss1]\<alpha>"
  by (utp_alpha_tac2, simp add:RenameP_compose)

theorem RenameA_NotA_distr [urename]:
"(\<not>\<alpha> p)[ss]\<alpha> = \<not>\<alpha> p[ss]\<alpha>"
  by (utp_alpha_tac2, utp_pred_tac)

theorem RenameA_AndA_distr [urename]:
"(p1 \<and>\<alpha> p2)[ss]\<alpha> = p1[ss]\<alpha> \<and>\<alpha> p2[ss]\<alpha>"
  by (utp_alpha_tac2, utp_pred_auto_tac)

theorem RenameA_OrA_distr [urename]:
"(p1 \<or>\<alpha> p2)[ss]\<alpha> = p1[ss]\<alpha> \<or>\<alpha> p2[ss]\<alpha>"
  by (utp_alpha_tac2, utp_pred_auto_tac)

theorem RenameA_ImpliesA_distr [urename]:
"(p1 \<Rightarrow>\<alpha> p2)[ss]\<alpha> = p1[ss]\<alpha> \<Rightarrow>\<alpha> p2[ss]\<alpha>"
  by (utp_alpha_tac2, utp_pred_auto_tac)

theorem RenameA_IffA_distr [urename]:
"(p1 \<Leftrightarrow>\<alpha> p2)[ss]\<alpha> = p1[ss]\<alpha> \<Leftrightarrow>\<alpha> p2[ss]\<alpha>"
  by (utp_alpha_tac2, utp_pred_auto_tac)

theorem RenameA_ClosureA [urename]:
"[p[ss]\<alpha>]\<alpha> = [p]\<alpha>"
  by (utp_alpha_tac2, metis RenameP_ClosureP)

theorem RenameA_ExtA [urename]:
"(p \<oplus>\<alpha> a)[ss]\<alpha> = (p[ss]\<alpha> \<oplus>\<alpha> (\<langle>ss\<rangle>\<^sub>s `\<^sub>f a))"
  by (utp_alpha_tac)

theorem RenameA_VarA [urename]:
"&x[ss]\<alpha> = &(\<langle>ss\<rangle>\<^sub>s x)"
  apply (utp_alpha_tac2)
  apply (simp add:RenameP_VarP)
done

theorem RenameA_EqualA [urename]:
"(e ==\<alpha> f)[ss]\<alpha> = e[ss]\<alpha>\<epsilon> ==\<alpha> f[ss]\<alpha>\<epsilon>"
  by (utp_alpha_tac2, simp add:urename)

theorem RenameAE_id [urename]:
"e[id\<^sub>s]\<alpha>\<epsilon> = e"
  by (utp_alpha_tac, utp_expr_tac, auto)

theorem RenameAE_LitAE [urename]:
"v : t \<Longrightarrow> (LitAE v)[ss]\<alpha>\<epsilon> = LitAE v"
  by (utp_alpha_tac, utp_expr_tac)

theorem RenameAE_VarAE [urename]:
"(VarAE x)[ss]\<alpha>\<epsilon> = VarAE (\<langle>ss\<rangle>\<^sub>s x)"
  by (utp_alpha_tac, simp add:urename)

text {* Finite unfolding of renamings *}

lemma REL_ALPHABET_in_out: 
  "a \<in> REL_ALPHABET \<Longrightarrow> (in\<^sub>\<alpha> a \<union>\<^sub>f out\<^sub>\<alpha> a) = a"
  by (simp add:REL_ALPHABET_def)


abbreviation "SS1_MapR a \<equiv> MapR [flist (out\<^sub>\<alpha> a) [\<mapsto>] flist (dash `\<^sub>f out\<^sub>\<alpha> a)]"
abbreviation "SS2_MapR a \<equiv> MapR [flist (in\<^sub>\<alpha> a) [\<mapsto>] flist (dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> a)]"




(*
lemma "x \<in>\<^sub>f a \<Longrightarrow> SS1_MapR a \<cong>\<^sub>s MapR [x \<mapsto> x\<acute>\<acute>] \<circ>\<^sub>s SS1_MapR (a -\<^sub>f \<lbrace>x\<rbrace>) on \<langle>a\<rangle>\<^sub>f"
  apply (simp add:rename_equiv_def MapR_rep_eq)
*)  


lemma SS1_eq_map: 
  assumes "a \<in> REL_ALPHABET"
  shows "SS1 \<cong>\<^sub>s SS1_MapR a on \<langle>a\<rangle>\<^sub>f"
proof -

  let ?xs = "flist (out\<^sub>\<alpha> a)" and ?ys = "flist (dash `\<^sub>f out\<^sub>\<alpha> a)"
  
  have tys:"\<forall>i<length ?xs. vtype (?xs ! i) = vtype (?ys ! i) \<and> aux (?xs ! i) = aux (?ys ! i)"
    by (simp add:rename_equiv_def flist_fimage dash_strict_mono)

  moreover have inter:"set ?xs \<inter> set ?ys = {}"
    by (auto simp add:rename_equiv_def flist_fimage dash_strict_mono var_defs)

  moreover have lens:"length ?ys = length ?xs"
    by (simp add:rename_equiv_def flist_fimage dash_strict_mono)

  ultimately show ?thesis using assms
  proof (auto simp add:rename_equiv_def MapR_rep_eq[of ?xs ?ys])
    fix x
    assume x_in_a: "x \<in> \<langle>a\<rangle>\<^sub>f"

    show "\<langle>SS1\<rangle>\<^sub>s x = MapRename [?xs [\<mapsto>] ?ys] x"
    proof (cases "x \<in>\<^sub>f out\<^sub>\<alpha> a")
      case True 
      note x_in_out = this
      show ?thesis
      proof -
        from x_in_out inter lens tys have "x \<in> dom ([?xs [\<mapsto>] ?ys])"
          by (simp)

        moreover from x_in_out inter lens tys 
        obtain i where ithms: "x = ?xs!i" "i < length (flist (out\<^sub>\<alpha> a))"
          by (metis (lifting) flist_set fmember.rep_eq in_set_conv_nth)

        moreover from ithms x_in_out have "(flist (out\<^sub>\<alpha> a) ! i) \<in> DASHED"
          by (simp add:var_defs)

        ultimately show ?thesis
          by (simp add:dash_strict_mono flist_fimage urename)
      qed
    next
      case False
      note x_nin_out = this
      show ?thesis
      proof -

        from x_nin_out x_in_a assms have "x \<in>\<^sub>f in\<^sub>\<alpha> a"
          by (force dest!:REL_ALPHABET_in_out elim!:Rep_fset_elim simp add:var_defs)

        moreover hence "x \<in> UNDASHED"
          by (metis fmember.rep_eq set_mp utp_alphabet.in_UNDASHED)

        moreover hence "x \<notin>\<^sub>f (dash `\<^sub>f out\<^sub>\<alpha> a)"
          by auto

        ultimately show ?thesis using lens inter tys x_nin_out
          by (simp add:urename)

      qed
    qed
  qed
qed

lemma SS2_eq_map: 
  assumes "a \<in> REL_ALPHABET"
  shows "SS2 \<cong>\<^sub>s SS2_MapR a on \<langle>a\<rangle>\<^sub>f"
proof -

  let ?xs = "flist (in\<^sub>\<alpha> a)" and ?ys = "flist (dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> a)"
  
  have tys:"\<forall>i<length ?xs. vtype (?xs ! i) = vtype (?ys ! i) \<and> aux (?xs ! i) = aux (?ys ! i)"
    by (simp add:rename_equiv_def flist_fimage dash_strict_mono)

  moreover have inter:"set ?xs \<inter> set ?ys = {}"
    by (auto simp add:rename_equiv_def flist_fimage dash_strict_mono var_defs)

  moreover have lens:"length ?ys = length ?xs"
    by (simp add:rename_equiv_def flist_fimage dash_strict_mono)

  ultimately show ?thesis using assms
  proof (auto simp add:rename_equiv_def MapR_rep_eq[of ?xs ?ys])
    fix x
    assume x_in_a: "x \<in> \<langle>a\<rangle>\<^sub>f"

    show "\<langle>SS2\<rangle>\<^sub>s x = MapRename [?xs [\<mapsto>] ?ys] x"
    proof (cases "x \<in>\<^sub>f in\<^sub>\<alpha> a")
      case True 
      note x_in_in = this
      show ?thesis
      proof -
        from x_in_in inter lens tys have "x \<in> dom ([?xs [\<mapsto>] ?ys])"
          by (simp)

        moreover from x_in_in inter lens tys 
        obtain i where ithms: "x = ?xs!i" "i < length (flist (in\<^sub>\<alpha> a))"
          by (metis (lifting) flist_set fmember.rep_eq in_set_conv_nth)

        moreover from ithms x_in_in have "(flist (in\<^sub>\<alpha> a) ! i) \<in> UNDASHED"
          by (simp add:var_defs)

        ultimately show ?thesis
          by (simp add:dash_strict_mono flist_fimage urename)
      qed
    next
      case False
      note x_nin_in = this
      show ?thesis
      proof -

        from x_nin_in x_in_a assms have "x \<in>\<^sub>f out\<^sub>\<alpha> a"
          by (force dest!:REL_ALPHABET_in_out elim!:Rep_fset_elim simp add:var_defs)

        moreover hence "x \<in> DASHED"
          by (metis fmember.rep_eq set_mp utp_alphabet.out_DASHED)

        moreover hence "x \<notin>\<^sub>f (dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> a)"
          by auto

        ultimately show ?thesis using lens inter tys x_nin_in
          by (simp add:urename)

      qed
    qed
  qed
qed

theorem ExistsA_ident :
  "a \<inter>\<^sub>f \<alpha> p = \<lbrace>\<rbrace> \<Longrightarrow> (\<exists>-\<alpha> a . p) = p"
  apply (utp_alpha_tac2)
  apply (rule_tac ExistsP_ident)
  apply (rule UNREST_subset)
  apply (rule EvalA_UNREST)
  apply (force)
done

theorem ExistsA_ident1 :
  "x \<notin>\<^sub>f \<alpha> p \<Longrightarrow> `\<exists>- x . p` = p"
  by (auto intro: ExistsA_ident)

theorem ExistsA_union :
"(\<exists>-\<alpha> a1 \<union>\<^sub>f a2 . p) = (\<exists>-\<alpha> a1 . \<exists>-\<alpha> a2 . p)"
  by (utp_alpha_tac2, metis ExistsP_union)

theorem ExistsA_AndA_expand1:
"a \<inter>\<^sub>f \<alpha> p2 = \<lbrace>\<rbrace>  \<Longrightarrow>
 (\<exists>-\<alpha> a. p1) \<and>\<alpha> p2 = (\<exists>-\<alpha> a. (p1 \<and>\<alpha> p2))"
  apply (utp_alpha_tac2)
  apply (rule_tac ExistsP_AndP_expand1)
  apply (insert EvalA_UNREST[of p2])
  apply (force intro:unrest)
done

theorem ExistsA_AndA_expand2:
"a \<inter>\<^sub>f \<alpha> p1 = \<lbrace>\<rbrace>  \<Longrightarrow>
 p1 \<and>\<alpha> (\<exists>-\<alpha> a. p2) = (\<exists>-\<alpha> a. (p1 \<and>\<alpha> p2))"
  apply (utp_alpha_tac2)
  apply (rule_tac ExistsP_AndP_expand2)
  apply (insert EvalA_UNREST[of p1])
  apply (force intro:unrest)
done

subsection {* Alphabet laws *}

text {* These are needed so the evaluation tactic works correctly *}

theorem SubstA_alphabet_alt [alphabet]:
"\<lbrakk> v \<rhd>\<^sub>\<alpha> x; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow>  
  \<alpha>(p[v|x]\<alpha>) = (if (x \<in>\<^sub>f \<alpha> p) then (\<alpha> p -\<^sub>f \<lbrace>x\<rbrace>) \<union>\<^sub>f \<alpha> v
               else \<alpha> p)"
  by (simp add:EvalAE_def alphabet)

theorem SubstAE_alphabet_alt [alphabet]:
"v \<rhd>\<^sub>\<alpha> x \<Longrightarrow> \<alpha>(f[v|x]\<alpha>\<epsilon>) = (\<alpha> f -\<^sub>f \<lbrace>x\<rbrace>) \<union>\<^sub>f \<alpha> v"
  by (simp add:EvalAE_def alphabet)

subsection {* Substitution Laws *}

ML {*
  structure usubst =
    Named_Thms (val name = @{binding usubst} val description = "substitution theorems")
*}

setup usubst.setup

lemma SubstA_AndA [usubst]: 
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x ; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> (p \<and>\<alpha> q)[v|x]\<alpha> = p[v|x]\<alpha> \<and>\<alpha> q[v|x]\<alpha>"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (force)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
done

lemma SubstA_ImpliesA [usubst]: "\<lbrakk> v \<rhd>\<^sub>\<alpha> x ; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> (p \<Rightarrow>\<alpha> q)[v|x]\<alpha> = p[v|x]\<alpha> \<Rightarrow>\<alpha> q[v|x]\<alpha>"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (force)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
done

lemma SubstA_OrA [usubst]: "\<lbrakk> v \<rhd>\<^sub>\<alpha> x ; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> (p \<or>\<alpha> q)[v|x]\<alpha> = p[v|x]\<alpha> \<or>\<alpha> q[v|x]\<alpha>"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (force)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
done

lemma SubstA_IffA [usubst]: 
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x ; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> (p \<Leftrightarrow>\<alpha> q)[v|x]\<alpha> = p[v|x]\<alpha> \<Leftrightarrow>\<alpha> q[v|x]\<alpha>"
  apply (utp_alpha_tac2)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
done

(*
lemma SubstA_EqualA [usubst]:
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x ; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> (e ==\<alpha> f)[v|x]\<alpha> = (e[v|x]\<alpha>\<epsilon> ==\<alpha> f[v|x]\<alpha>\<epsilon>)"
  apply (rule EvalA_intro)
  apply (simp add:alphabet)
  apply (auto)
  apply (utp_alpha_tac2)
  apply (rule EvalP_intro)
  apply (simp add:evala eval)
*)

lemma SubstA_var [usubst]: "\<lbrakk> vtype x = BoolType; v \<rhd>\<^sub>\<alpha> x; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> &x[v|x]\<alpha> = ExprA v"
  apply (subgoal_tac "v :\<^sub>\<alpha> BoolType")
  apply (utp_alpha_tac2)
  apply (rule EvalP_intro)
  apply (auto simp add:evala eval closure typing)
done

lemma SubstA_no_var [usubst]: "\<lbrakk> v \<rhd>\<^sub>\<alpha> x ; x \<notin> \<langle>\<alpha> p\<rangle>\<^sub>f; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> 
  \<Longrightarrow> p[v|x]\<alpha> = p"
  apply (utp_alpha_tac2)
  apply (simp add:EvalA_SubstA)
  apply (rule SubstP_no_var)
  apply (metis EvalAE_compat)
  apply (metis EvalA_is_SubstP_var)
  apply (auto intro:unrest)
done

lemma SubstA_PROGRAM_ALPHABET [usubst]: 
  "\<lbrakk> v \<rhd>\<^sub>\<alpha> x ; aux x; \<alpha> p \<in> PROGRAM_ALPHABET; x \<notin> \<langle>\<alpha> v\<rangle>\<^sub>f \<rbrakk> 
  \<Longrightarrow> p[v|x]\<alpha> = p"
  apply (rule SubstA_no_var)
  apply (simp_all add:eavar_compat_def)
  apply (simp add:PROGRAM_ALPHABET_def PROGRAM_VARS_def )
  apply (auto)
done

theorem SkipA_empty :
  shows "II\<alpha> \<lbrace>\<rbrace> = TRUE"
  apply (utp_alpha_tac2)
  apply (simp add:SkipRA_empty)
done

theorem SkipA_unfold :
  assumes "x \<in>\<^sub>f a" "dash x \<in>\<^sub>f a" "x \<in> UNDASHED" "a \<in> REL_ALPHABET" "HOM_ALPHA a"
  shows "II\<alpha> a = (VarAE (dash x) ==\<alpha> VarAE x) \<and>\<alpha> II\<alpha> (a -\<^sub>f \<lbrace>x,dash x\<rbrace>)"
  using assms
  apply (utp_alpha_tac2)
  apply (simp add:SkipRA_unfold HOM_ALPHA_HOMOGENEOUS)
done

(*
lemma "\<lbrakk> UNREST (VAR - vs) p; ss1 \<cong>\<^sub>s ss2 on vs \<rbrakk> \<Longrightarrow> p[ss1] = p[ss2]"
  apply (utp_pred_tac)
  apply (clarsimp)
  apply (simp add:RenameB_def)
  apply (simp add:EvalP_def)
  apply (subgoal_tac "CompB b ss1 = CompB b ss2")
  apply (simp)
  apply (rule Rep_WF_BINDING_intro)
  apply (simp add:CompB_rep_eq)
  apply (rule ext)
  apply (auto simp add:rename_equiv_def)
  apply (case_tac "x \<in> vs")
  apply (simp)
  apply (simp)
*)

lemma RenameA_equiv: 
  "\<lbrakk> \<langle>\<alpha> p\<rangle>\<^sub>f \<subseteq> vs; ss1 \<cong>\<^sub>s ss2 on vs \<rbrakk> \<Longrightarrow> p[ss1]\<alpha> = p[ss2]\<alpha>"
  apply (utp_alpha_tac2)
  apply (simp add:rename_equiv_def)
  apply (force)
  apply (utp_pred_tac)
  apply (simp add:EvalA_def EvalP_def rename_equiv_def rename_equiv_def RenameB_def)
  apply (clarify)
  apply (subgoal_tac "CompB b ss1 \<cong> CompB b ss2 on vs")
  apply (insert WF_ALPHA_PREDICATE_UNREST [of p])
  apply (simp add:UNREST_def)
  apply (auto)
  apply (drule_tac x="CompB b ss1" in bspec,simp)
  apply (smt binding_override_equiv binding_override_simps(10) binding_override_simps(2) binding_override_simps(4) binding_override_simps(5) binding_override_subset)
  apply (drule_tac x="CompB b ss2" in bspec,simp)
  apply (metis binding_override_equiv binding_override_simps(10) binding_override_simps(5) binding_override_subset)
  apply (simp add:binding_equiv_def)
done

lemma RenameAE_equiv: 
  "\<lbrakk> \<langle>\<alpha> e\<rangle>\<^sub>f \<subseteq> vs; ss1 \<cong>\<^sub>s ss2 on vs \<rbrakk> \<Longrightarrow> e[ss1]\<alpha>\<epsilon> = e[ss2]\<alpha>\<epsilon>"
  apply (utp_alpha_tac)
  apply (simp add:rename_equiv_def)
  apply (rule conjI)
  apply (force)
  apply (utp_expr_tac)
  apply (simp add:EvalAE_def EvalE_def rename_equiv_def rename_equiv_def RenameB_def)
  apply (clarify)
  apply (subgoal_tac "CompB b ss1 \<cong> CompB b ss2 on vs")
  apply (insert WF_ALPHA_EXPRESSION_UNREST_EXPR [of e])
  apply (simp add:UNREST_EXPR_def)
  apply (drule_tac x="CompB b ss1" in spec)
  apply (drule_tac x="CompB b ss2" in spec)
  apply (smt binding_override_equiv binding_override_simps(10) binding_override_simps(2) binding_override_simps(4) binding_override_simps(5) binding_override_subset)
  apply (simp add:binding_equiv_def)
done

theorem RenameA_SS1_UNDASHED [urename]:
  "\<lbrakk> \<langle>\<alpha> p\<rangle>\<^sub>f \<subseteq> UNDASHED \<rbrakk> \<Longrightarrow> p[SS1]\<alpha> = p"
  by (metis RenameA_id SS1_eq_id RenameA_equiv)
  
theorem RenameA_SS2_DASHED [urename]:
  "\<lbrakk> \<langle>\<alpha> p\<rangle>\<^sub>f \<subseteq> DASHED \<rbrakk> \<Longrightarrow> p[SS2]\<alpha> = p"
  by (metis RenameA_id SS2_eq_id RenameA_equiv)

theorem RenameAE_SS1_UNDASHED [simp]:
  "\<lbrakk> \<langle>\<alpha> e\<rangle>\<^sub>f \<subseteq> UNDASHED \<rbrakk> \<Longrightarrow> e[SS1]\<alpha>\<epsilon> = e"
  by (metis RenameAE_id SS1_eq_id RenameAE_equiv)
  
theorem RenameAE_SS2_DASHED [simp]:
  "\<lbrakk> \<langle>\<alpha> e\<rangle>\<^sub>f \<subseteq> DASHED \<rbrakk> \<Longrightarrow> e[SS2]\<alpha>\<epsilon> = e"
  by (metis RenameAE_id SS2_eq_id RenameAE_equiv)

text {* If the right-hand side of a sequential composition contains only undashed
variables it can be transferred to the left-hand side by renaming to dashed variables *}
theorem SemiA_ConjA_right_precond: 
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION"
    "\<langle>\<alpha> q\<rangle>\<^sub>f \<subseteq> UNDASHED"
  shows "p ;\<alpha> (q \<and>\<alpha> r) = (p \<and>\<alpha> q[SS]\<alpha>) ;\<alpha> r"
proof -

  let ?A = "dash `\<^sub>f out\<^sub>\<alpha> (\<alpha> p) \<union>\<^sub>f dash `\<^sub>f dash `\<^sub>f (in\<^sub>\<alpha> (\<alpha> q) \<union>\<^sub>f in\<^sub>\<alpha> (\<alpha> r))"
  from assms have "p ;\<alpha> (q \<and>\<alpha> r) = (\<exists>-\<alpha> ?A . p[SS1]\<alpha> \<and>\<alpha> (q \<and>\<alpha> r)[SS2]\<alpha>)"
    by (simp add:SemiA_algebraic closure alphabet_dist alphabet)

  also from assms have "... = (\<exists>-\<alpha> ?A . p[SS1]\<alpha> \<and>\<alpha> (q[SS2]\<alpha> \<and>\<alpha> r[SS2]\<alpha>))"
    by (metis (no_types) RenameA_AndA_distr)

  also from assms have "... = (\<exists>-\<alpha> ?A . p[SS1]\<alpha> \<and>\<alpha> (q[SS]\<alpha>[SS1]\<alpha> \<and>\<alpha> r[SS2]\<alpha>))"
    apply (simp add:RenameA_compose)
    apply (unfold RenameA_equiv[of "q" UNDASHED "SS1 \<circ>\<^sub>s SS" SS2,OF assms(4) SS1_SS_eq_SS2])
    apply (simp)
  done

  also from assms have "... = (\<exists>-\<alpha> ?A . (p \<and>\<alpha> q[SS]\<alpha>)[SS1]\<alpha> \<and>\<alpha> r[SS2]\<alpha>)"
    by (smt AndA_assoc RenameA_AndA_distr)

  also from assms have "... = (p \<and>\<alpha> q[SS]\<alpha>) ;\<alpha> r"
    by (simp add:SemiA_algebraic closure alphabet_dist alphabet SS_alpha_image)

  ultimately show ?thesis
    by (simp)
qed

theorem SemiA_ConjA_right_postcond: 
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION"
    "\<langle>\<alpha> r\<rangle>\<^sub>f \<subseteq> DASHED"
  shows "p ;\<alpha> (q \<and>\<alpha> r) = (p ;\<alpha> q) \<and>\<alpha> r" (is "?P = ?Q")
proof -

  let ?A = "dash `\<^sub>f out\<^sub>\<alpha> (\<alpha> p) \<union>\<^sub>f dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> q)"

  from assms have "p ;\<alpha> (q \<and>\<alpha> r) = (\<exists>-\<alpha> ?A. (p[SS1]\<alpha> \<and>\<alpha> q[SS2]\<alpha> \<and>\<alpha> r))"
    by (simp add:SemiA_algebraic closure alphabet_dist alphabet alphabet_simps urename)

  also from assms have "... = (\<exists>-\<alpha> ?A. ((p[SS1]\<alpha> \<and>\<alpha> q[SS2]\<alpha>) \<and>\<alpha> r))"
    by (smt AndA_assoc)

  also from assms have "... = (\<exists>-\<alpha> ?A. p[SS1]\<alpha> \<and>\<alpha> q[SS2]\<alpha>) \<and>\<alpha> r"
    apply (rule_tac ExistsA_AndA_expand1[THEN sym])
    apply (auto)
    apply (metis DASHED_dash_DASHED_TWICE DASHED_not_DASHED_TWICE UnI2 sup.commute sup_absorb2 utp_var.out_DASHED)
    apply (smt in_mono not_dash_dash_member_out var_simps)
  done
 
  ultimately show ?thesis using assms
    by (simp add:SemiA_algebraic closure alphabet_dist alphabet alphabet_simps urename)

qed

theorem SemiA_ConjA_left_postcond: 
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION"
    "\<langle>\<alpha> q\<rangle>\<^sub>f \<subseteq> DASHED"
  shows "(p \<and>\<alpha> q) ;\<alpha> r = p ;\<alpha> (q[SS]\<alpha> \<and>\<alpha> r)"
proof -

  let ?A = "dash `\<^sub>f out\<^sub>\<alpha> (\<alpha> p) \<union>\<^sub>f (dash `\<^sub>f \<alpha> q \<union>\<^sub>f dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> r))"
  from assms have "(p \<and>\<alpha> q) ;\<alpha> r = (\<exists>-\<alpha> ?A . (p[SS1]\<alpha> \<and>\<alpha> q[SS1]\<alpha>) \<and>\<alpha> r[SS2]\<alpha>)"
    by (simp add:SemiA_algebraic closure alphabet_dist alphabet urename)

  also from assms have "... = (\<exists>-\<alpha> ?A . (p[SS1]\<alpha> \<and>\<alpha> q[SS]\<alpha>[SS2]\<alpha>) \<and>\<alpha> r[SS2]\<alpha>)"
    apply (simp add:RenameA_compose)
    apply (unfold RenameA_equiv[of "q" DASHED "SS2 \<circ>\<^sub>s SS" SS1,OF assms(4) SS2_SS_eq_SS1])
    apply (simp)
  done

  also from assms have "... = (\<exists>-\<alpha> ?A . p[SS1]\<alpha> \<and>\<alpha> (q[SS]\<alpha> \<and>\<alpha> r)[SS2]\<alpha>)"
    by (smt AndA_assoc RenameA_AndA_distr)

  also from assms have "... = p ;\<alpha> (q[SS]\<alpha> \<and>\<alpha> r)"
    apply (simp add:SemiA_algebraic closure alphabet_dist alphabet alphabet_simps SS_alpha_image)
    apply (smt alphabet_simps)
  done

  ultimately show ?thesis
    by (simp)
qed

theorem SemiA_ConjA_left_precond: 
  assumes "p \<in> WF_RELATION" "q \<in> WF_RELATION" "r \<in> WF_RELATION"
    "\<langle>\<alpha> p\<rangle>\<^sub>f \<subseteq> UNDASHED"
  shows "(p \<and>\<alpha> q) ;\<alpha> r = p \<and>\<alpha> (q ;\<alpha> r)" (is "?P = ?Q")
using assms
proof -

  let ?A = "dash `\<^sub>f out\<^sub>\<alpha> (\<alpha> q) \<union>\<^sub>f dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> r)"

  from assms have "(p \<and>\<alpha> q) ;\<alpha> r = (\<exists>-\<alpha> ?A. ((p \<and>\<alpha> q[SS1]\<alpha>) \<and>\<alpha> r[SS2]\<alpha>))"
    by (simp add:SemiA_algebraic closure alphabet_dist alphabet alphabet_simps urename)

  also from assms have "... = (\<exists>-\<alpha> ?A. (p \<and>\<alpha> (q[SS1]\<alpha> \<and>\<alpha> r[SS2]\<alpha>)))"
    by (smt AndA_assoc)

  also from assms have "... = p \<and>\<alpha> (\<exists>-\<alpha> ?A. q[SS1]\<alpha> \<and>\<alpha> r[SS2]\<alpha>)"
    apply (rule_tac ExistsA_AndA_expand2[THEN sym])
    apply (auto)
    apply (metis UNDASHED_eq_dash_contra set_mp)
    apply (metis UNDASHED_eq_dash_contra set_mp)
  done
 
  ultimately show ?thesis using assms
    by (simp add:SemiA_algebraic closure alphabet_dist alphabet alphabet_simps urename)

qed

theorem SemiA_ExistsA_left:
  assumes
  "p \<in> WF_RELATION"
  "q \<in> WF_RELATION"
  "dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> q) \<subseteq>\<^sub>f out\<^sub>\<alpha> (\<alpha> p)"
  shows "(\<exists>-\<alpha> (out\<^sub>\<alpha> (\<alpha> p) -\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> q)). p) ;\<alpha> q = p ;\<alpha> q"
  using assms
  apply (utp_alpha_tac)
  apply (simp add:alphabet_dist)
  apply (rule_tac SemiP_ExistsP_left)
  apply (auto intro: unrest closure)
done

theorem SemiA_ExistsA_right:
  assumes
  "p \<in> WF_RELATION"
  "q \<in> WF_RELATION"
  "out\<^sub>\<alpha> (\<alpha> p) \<subseteq>\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> q)"
  shows "p ;\<alpha> (\<exists>-\<alpha> (in\<^sub>\<alpha> (\<alpha> q) -\<^sub>f undash `\<^sub>f out\<^sub>\<alpha> (\<alpha> p)). q) = p ;\<alpha> q"
  using assms
  apply (utp_alpha_tac)
  apply (simp add:alphabet_dist)
  apply (rule_tac SemiP_ExistsP_right)
  apply (auto intro: unrest closure)
done

lemma SubstA_one_point:
  assumes "v \<rhd>\<^sub>\<alpha> x" "x \<notin>\<^sub>f \<alpha> v" "x \<in>\<^sub>f \<alpha> p"
  shows "`(\<exists>- x . p \<and> $x = v)` = `p[v/x]`" (is "?P = ?Q")
proof (rule EvalA_intro)

  from assms show "\<alpha> ?P = \<alpha> ?Q"
    by (force simp add:alphabet alphabet_dist alphabet_simps)

  from assms show "\<lbrakk>?P\<rbrakk>\<pi> = \<lbrakk>?Q\<rbrakk>\<pi>"
    apply (simp add:evala typing unrest EvalA_SubstA)
    apply (rule_tac SubstP_one_point)
    apply (auto intro:unrest simp add:evala typing EvalA_SubstA)
  done
qed


lemma utp_alpha_pred_simps_simple [simp]:
  "\<not>\<alpha> (false a) = true a"
  "\<not>\<alpha> (true a)  = false a"
  "TRUE \<and>\<alpha> x = x"
  "x \<and>\<alpha> TRUE = x"
  "`true\<^bsub>a\<^esub> \<and> x` = `x \<oplus> a`"
  "`x \<and> true\<^bsub>a\<^esub>` = `x \<oplus> a`"
  "TRUE \<Rightarrow>\<alpha> x = x"
  "`p \<and> false\<^bsub>a\<^esub>` = `false\<^bsub>\<alpha> p \<union>\<^sub>f a\<^esub>`"
  "`false\<^bsub>a\<^esub> \<and> p` = `false\<^bsub>\<alpha> p \<union>\<^sub>f a\<^esub>`"
  "\<alpha> p \<union>\<^sub>f a = \<alpha> p \<Longrightarrow> `p \<oplus> a` = `p`"
  "`p \<Rightarrow> FALSE` = `\<not> p`" 
  "`p \<Rightarrow> TRUE` = `true\<^bsub>\<alpha> p\<^esub>`"
  "`p \<oplus> a \<and> q` = `(p \<and> q) \<oplus> a`"
  "`p \<oplus> a \<or> q` = `(p \<or> q) \<oplus> a`"
  "`p \<and> q \<oplus> a` = `(p \<and> q) \<oplus> a`"
  "`p \<or> q \<oplus> a` = `(p \<or> q) \<oplus> a`"
  by (utp_alpha_tac2)+

lemma utp_alpha_pred_simps [simp]:
  "`p \<or> false\<^bsub>a\<^esub>` = `p \<oplus> a`"
  "`false\<^bsub>a\<^esub> \<or> p` = `p \<oplus> a`"
  "`p \<Leftrightarrow> p` = true (\<alpha> p)"
  "`\<not> \<not> p` = p"
  "taut [p]\<alpha> \<longleftrightarrow> taut p"
  apply (utp_alpha_tac2, utp_pred_tac)+
  apply (utp_alpha_tac, utp_pred_tac)
done

lemma hom_simps [simp]:
  "out\<^sub>\<alpha> (homr a) = out\<^sub>\<alpha> a"
  "in\<^sub>\<alpha> (homr a) = undash `\<^sub>f out\<^sub>\<alpha> a"
  "out\<^sub>\<alpha> (homl a) = dash `\<^sub>f in\<^sub>\<alpha> a"
  "in\<^sub>\<alpha> (homl a) = in\<^sub>\<alpha> a"
  "x \<in> UNDASHED \<Longrightarrow> x \<in>\<^sub>f homl a \<longleftrightarrow> x \<in>\<^sub>f a"
  "x \<in> DASHED \<Longrightarrow> x \<in>\<^sub>f homl a \<longleftrightarrow> undash x \<in>\<^sub>f a"
  apply (simp_all add:hom_right_def hom_left_def alphabet_dist var_simps var_dist)
  apply (metis Int_iff UNDASHED_not_DASHED in_vars_def out_dash out_vars_def)
  apply (metis IntE IntI dash_undash_DASHED imageI out_dash out_vars_def undash_dash_image utp_var.not_dash_member_in)
done

lemma HOM_ALPHABET_homr  [simp]: "a \<in> HOM_ALPHABET \<Longrightarrow> homr a = a"
  apply (simp add:HOM_ALPHABET_def hom_right_def HOM_ALPHA_unfold alphabet_dist alphabet_simps)
  apply (metis SkipA_alphabet SkipA_closure WF_RELATION_UNDASHED_DASHED alphabet_simps(14))
done

lemma HOM_ALPHABET_homl [simp]: "a \<in> HOM_ALPHABET \<Longrightarrow> homl a = a"
  apply (simp add:HOM_ALPHABET_def hom_left_def HOM_ALPHA_unfold alphabet_dist alphabet_simps)
  apply (metis SkipA_alphabet SkipA_closure WF_RELATION_UNDASHED_DASHED alphabet_simps(14))
done

lemma ClosureA_intro: "\<lbrakk> \<alpha> p = \<alpha> q; [p \<Leftrightarrow> q] \<rbrakk> \<Longrightarrow> p = q"
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
done

lemma EvalAE_SubstA_LitAE [evala]: 
  "v \<rhd> x \<Longrightarrow> \<lbrakk>\<lbrakk>p[LitAE v|x]\<alpha>\<rbrakk>\<pi>\<rbrakk>b = \<lbrakk>\<lbrakk>p\<rbrakk>\<pi>\<rbrakk>(b(x :=\<^sub>b v))"
  apply (subgoal_tac "LitAE v \<rhd>\<^sub>\<alpha> x")
  apply (subgoal_tac "v : vtype x")
  apply (simp add:evala evale closure defined alphabet)
  apply (simp add:typing)
  apply (metis (lifting) LitAE_defined LitAE_type eavar_compat_intros(1) eavar_compat_intros(2) var_compat_def)
done

(*
lemma SubstA_intro:
  "\<lbrakk> x \<in>\<^sub>f \<alpha> P; \<forall> v. v \<rhd>\<^sub>\<alpha> x \<and> x \<notin>\<^sub>f \<alpha> v \<longrightarrow> [P[v/x]] \<rbrakk> \<Longrightarrow> [P]"
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
  apply (simp add:evala)
  apply (auto)
 
  apply ()
*)


lemma eq_iff_taut: "\<lbrakk> \<alpha> P = \<alpha> Q \<rbrakk> \<Longrightarrow> P = Q \<longleftrightarrow> taut (P \<Leftrightarrow>\<alpha> Q)"
  apply (auto)
  apply (utp_alpha_tac)
  apply (rule ClosureA_intro)
  apply (auto)
done

(* A tautology can be proven by proven it for any substitution of a variable *)
lemma taut_cases:
  "\<lbrakk> x \<in>\<^sub>f \<alpha> p; \<And> v. v \<rhd> x \<Longrightarrow> taut (p[LitAE v|x]\<alpha>) \<rbrakk> \<Longrightarrow> taut p"
  apply (utp_alpha_tac)
  apply (utp_pred_tac)
  apply (metis EvalAE_SubstA_LitAE binding_compat binding_upd_triv)
done

lemma AssignA_unfold:
  "\<lbrakk> a \<in> REL_ALPHABET; x \<in>\<^sub>f a; dash x \<in>\<^sub>f a; \<alpha> v \<subseteq>\<^sub>f a \<rbrakk> \<Longrightarrow>
   `x :=\<^bsub>a\<^esub> v` = ((VarAE (dash x) ==\<alpha> v) \<and>\<alpha> II\<alpha> (a -\<^sub>f \<lbrace>x,dash x\<rbrace>)) \<oplus>\<alpha> \<lbrace>x\<rbrace>"
  apply (utp_alpha_tac2)
  apply (simp add:AssignR_def)
done

lemma SubstA_ident_twice:
  assumes "x \<noteq> y" "vtype x = vtype y" "aux x = aux y" "x \<in>\<^sub>f \<alpha> P" "y \<notin>\<^sub>f \<alpha> P"
  shows "`P[$y/x][$x/y]` = P"
proof -

  from assms have "VarAE y \<rhd>\<^sub>\<alpha> x" "VarAE x \<rhd>\<^sub>\<alpha> y"
    by (auto intro!:typing defined)

  with assms have "`P[$y/x][$x/y]` = `\<exists>- y. (\<exists>- x. P \<and> $x = $y) \<and> $y = $x`"
    apply (simp)
    apply (insert SubstA_one_point[of "VarAE y" "x" "P", THEN sym])
    apply (insert SubstA_one_point[of "VarAE x" "y" "`\<exists>- x. P \<and> $x = $y`", THEN sym])
    apply (simp add:alphabet)
  done

  also from assms have "`\<exists>- y. (\<exists>- x. P \<and> $x = $y) \<and> $y = $x` = P"
    apply (utp_alpha_tac)
    apply (rule conjI)
    apply (force)
    apply (utp_pred_tac)
    apply (utp_expr_tac)
    apply (clarify)
    apply (rule iffI)
    apply (clarsimp)
    apply (subgoal_tac "\<langle>b\<rangle>\<^sub>b x \<rhd> y")
    apply (subgoal_tac "UNREST (VAR - \<langle>\<alpha> P\<rangle>\<^sub>f) \<lbrakk>P\<rbrakk>\<pi>")
    apply (simp add: EvalP_UNREST_binding_upd binding_upd_twist)
    apply (simp add: unrest)
    apply (simp add: typing)
    apply (rule_tac x="b(y:=\<^sub>b(\<langle>b\<rangle>\<^sub>b x))" in exI)
    apply (clarsimp)
    apply (rule_tac x="b" in exI)
    apply (simp)
    apply (subgoal_tac "\<langle>b\<rangle>\<^sub>b x \<rhd> y")
    apply (subgoal_tac "UNREST (VAR - \<langle>\<alpha> P\<rangle>\<^sub>f) \<lbrakk>P\<rbrakk>\<pi>")
    apply (simp add: EvalP_UNREST_binding_upd binding_upd_twist)
    apply (simp add: unrest)
    apply (simp add: typing)
  done

  ultimately show ?thesis
    by simp
qed

lemma ExistsA_insert: 
  assumes "x \<in>\<^sub>f \<alpha> P" "y \<notin>\<^sub>f \<alpha> P" "x \<noteq> y" "vtype x = vtype y" "aux x = aux y"
  shows "P = `\<exists>- y. P[$y/x] \<and> $y = $x`"
proof -

  from assms have "P = `P[$y/x][$x/y]`"
    by (metis SubstA_ident_twice)

  also from assms have "... = `\<exists>- y. P[$y/x] \<and> $y = $x`"
    apply (subgoal_tac "VarAE x \<rhd>\<^sub>\<alpha> y")
    apply (subgoal_tac "VarAE y \<rhd>\<^sub>\<alpha> x")
    apply (insert SubstA_one_point[of "VarAE x" "y" "`P[$y/x]`"])
    apply (simp_all add:unrest typing alphabet)
    apply (auto intro!:typing defined)
  done

  ultimately show ?thesis by simp

qed

(*
lemma 
  shows "p[ss]\<alpha> = p[Abs_VAR_RENAME (MapRename [flist (\<alpha> p) [\<mapsto>] (map \<langle>ss\<rangle>\<^sub>s (flist (\<alpha> p)))])]\<alpha>"
proof -

  obtain xs where "\<alpha> p = fset xs" "sorted xs" "distinct xs"
    by (metis flist_inv flist_props)

  thus ?thesis
    apply (simp)
    apply (rule_tac vs="\<langle>\<alpha> p\<rangle>\<^sub>f" in RenameA_equiv)
    apply (simp)
    apply (simp add:rename_equiv_def)
    apply (induct xs)
    apply (auto)
    thm VAR_RENAME_MapRename
    apply (simp add:closure)
    thm MapRename_
    thm Abs_VAR_RENAME_inverse
    apply (auto)
    apply (case_tac "x=a")
    apply (simp add:)

    apply (simp add:RenameA.rep_eq)

  apply (induct "\<alpha> p")
  apply (simp)
  apply (drule sym)
  apply (erule WF_ALPHA_PREDICATE_empty_elim)
  apply (simp add:urename)+
  apply (drule sym)
  apply (simp)

  done
*)

lemma EqualA_WF_RELATION [closure]: 
  "\<lbrakk> \<alpha> e \<in> REL_ALPHABET; \<alpha> f \<in> REL_ALPHABET \<rbrakk> \<Longrightarrow> e ==\<alpha> f \<in> WF_RELATION"
  by (auto intro:closure simp add:WF_RELATION_def alphabet)

lemma AssignA_SubstA: 
  assumes "p \<in> WF_RELATION" "v \<in> WF_REL_EXPR"
   "x \<in> UNDASHED" "x \<in>\<^sub>f \<alpha> p" "\<alpha> v \<subseteq>\<^sub>f in\<^sub>\<alpha> (\<alpha> p)" 
  shows "`(x :=\<^bsub>homl (\<alpha> p)\<^esub> v) ; p` = `p[v/x]`"
proof -
 
  let ?A = "(dash `\<^sub>f out\<^sub>\<alpha> (\<alpha> v) \<union>\<^sub>f (dash `\<^sub>f (dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> p) -\<^sub>f \<lbrace>x\<acute>\<rbrace>) \<union>\<^sub>f dash `\<^sub>f dash `\<^sub>f in\<^sub>\<alpha> (\<alpha> p)))"

  from assms have "\<alpha> v \<subseteq>\<^sub>f homl (\<alpha> p)"
    by (auto simp add:hom_left_def)

  with assms have "`(x :=\<^bsub>homl (\<alpha> p)\<^esub> v) ; p` = `(($x\<acute> = v \<and> II\<^bsub>homl (\<alpha> p) -\<^sub>f \<lbrace>x, x\<acute>\<rbrace>\<^esub>) \<oplus> \<lbrace>x\<rbrace>) ; p`"
    by (smt AssignA_unfold REL_ALPHABET_hom_left UNDASHED_dash_DASHED hom_simps undash_dash)

  also from assms 
  have "... = (\<exists>-\<alpha> finsert x\<acute>\<acute> ?A. ((VarAE x\<acute>\<acute> ==\<alpha> v) \<and>\<alpha> (II\<alpha> (homl (\<alpha> p) -\<^sub>f \<lbrace>x, x\<acute>\<rbrace>))[SS1]\<alpha>) 
                       \<and>\<alpha> p[SS2]\<alpha> \<oplus>\<alpha> \<lbrace>x\<rbrace>)"
    apply (subgoal_tac "\<langle>\<alpha> v\<rangle>\<^sub>f \<subseteq> UNDASHED")
    apply (simp add:SemiA_algebraic closure alphabet alphabet_dist alphabet_simps urename)
    apply (auto)
    apply (smt set_mp utp_var.in_UNDASHED)
  done

  have "... = (\<exists>-\<alpha> ?A. ((II\<alpha> (homl (\<alpha> p) -\<^sub>f \<lbrace>x, x\<acute>\<rbrace>))[SS1]\<alpha>) \<and>\<alpha> (p[SS2]\<alpha> \<oplus>\<alpha> \<lbrace>x\<rbrace>)[v|x\<acute>\<acute>]\<alpha>)"
    sorry

oops

end