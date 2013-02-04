theory Cfun_Partial
imports HOLCF Tr_Logic
begin

text {* Reasoning about partial functions *}

section {* LCF-style functions *}

definition cdom :: "('a \<Rightarrow> 'b::pcpo) \<Rightarrow> 'a set" where
"cdom f = {x. f x \<noteq> \<bottom>}"

definition cran :: "('a \<Rightarrow> 'b::pcpo) \<Rightarrow> 'b set" where
"cran f = { (f x) | x . (f x) \<noteq> \<bottom>}"

definition cgraph :: "('a \<Rightarrow> 'b::pcpo) \<Rightarrow> ('a * 'b) set" where
"cgraph f = { (x, f x) | x . (f x) \<noteq> \<bottom>}"

definition chain_closed :: "('a::cpo) set \<Rightarrow> bool" where
"chain_closed xs \<equiv> \<forall> Y i. (chain Y \<and> Y i \<in> xs) \<longrightarrow> (\<forall> j. Y j \<in> xs)"

definition flat_value :: "'a::pcpo \<Rightarrow> bool" where
"flat_value x \<equiv> x \<noteq> \<bottom> \<and> (\<forall> Y. (chain Y \<and> x \<in> range Y) \<longrightarrow> range Y \<subseteq> {\<bottom>,x})"

definition flat :: "('a::pcpo) set" where
"flat = Collect flat_value"

lemma flat_valueI: 
  "\<lbrakk> x \<noteq> \<bottom>; (\<forall>y. x \<sqsubseteq> y \<longrightarrow> x = y); (\<forall>y. y \<sqsubseteq> x \<longrightarrow> x = y \<or> y = \<bottom>) \<rbrakk> \<Longrightarrow> x \<in> flat"
  apply (simp add:flat_def flat_value_def)
  apply (safe)
  apply (metis chain_mono_less linorder_cases)
done

lemma Def_below_elim1 [elim!]:
  "\<lbrakk> Def x \<sqsubseteq> y; y = Def x \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (case_tac y, simp_all)

lemma Def_below_elim2 [elim!]:
  "\<lbrakk> x \<sqsubseteq> Def y; x = \<bottom> \<Longrightarrow> P; x = Def y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (case_tac x, simp_all add:flat_below_iff)

lemma flat_value_Def [simp]:
  "flat_value (Def x)"
  apply (auto simp add:flat_value_def)
  apply (case_tac "xa \<le> xb")
  apply (smt chain_mono flat_below_iff)
  apply (metis Def_below_elim1 chain_mono_less linorder_not_le)
done

lemma flat_nbot[simp]: "\<bottom> \<notin> flat"
  by (simp add:flat_def flat_value_def)

lemma flat_subset_max: "\<lbrakk> x \<in> flat; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> x = y"
  apply (simp add:flat_def flat_value_def, clarify)
  apply (drule_tac x="\<lambda> i. if (i = 0) then x else y" in spec)
  apply (subgoal_tac "chain (\<lambda> i. if (i = 0) then x else y)")
  apply (force)
  apply (rule chainI)
  apply (simp)
done

lemma flat_subset_min: "\<lbrakk> y \<in> flat; x \<sqsubseteq> y; x \<noteq> \<bottom> \<rbrakk> \<Longrightarrow> x = y"
  apply (simp add:flat_def flat_value_def, clarify)
  apply (drule_tac x="\<lambda> i. if (i = 0) then x else y" in spec)
  apply (subgoal_tac "chain (\<lambda> i. if (i = 0) then x else y)")
  apply (auto)[1]
  apply (rule chainI)
  apply (simp)
done

lemma cont_flat_cdom:
  assumes f_flat: "cdom f \<subseteq> flat"
  shows "cont f"
proof (rule contI)
  fix Y :: "nat \<Rightarrow> 'a"
  assume chain: "chain Y"

  from f_flat have f_strict: "f \<bottom> = \<bottom>"
    by (auto simp add:flat_def flat_value_def cdom_def)

  show "range (\<lambda>i. f (Y i)) <<| f (\<Squnion> i. Y i)"
  proof (cases "\<exists>x\<in>cdom f. x \<in> range Y")
    case True 
    with chain f_flat show ?thesis
      apply (simp add:flat_def flat_value_def subset_iff)[1]
      apply (erule bexE)
      apply (drule_tac x="x" in spec)
      apply (simp, erule conjE)
      apply (drule_tac x="Y" in spec, simp)
      apply (rule is_lubI)
      apply (rule ub_rangeI)
      apply (case_tac "Y i = \<bottom>")
      apply (simp add:f_strict)
      apply (subgoal_tac "(\<Squnion> i. Y i) = x")
      apply (simp)
      apply (subgoal_tac "Y i = x")
      apply (simp)
      apply (metis (full_types) empty_iff insert_iff rangeI set_mp)
      apply (metis (lifting) assms flat_subset_max is_ub_thelub rangeE set_rev_mp)
      apply (metis assms flat_subset_max image_eqI is_ubD is_ub_thelub rangeE range_composition set_mp)
    done

  next

    case False
    note nmem_chain = this

    show ?thesis
    proof (cases "(\<Squnion> i. Y i) \<in> cdom f")
      case False with nmem_chain show ?thesis
        by (auto intro!: is_lubI ub_rangeI simp add:cdom_def)

    next
      
      case True
      note supindom = this

      obtain x where xinY:"x \<in> range Y" and xnbot: "x \<noteq> \<bottom>" and xusup:"x \<sqsubseteq> (\<Squnion> i. Y i)"
        by (metis (no_types) nmem_chain supindom chain is_ub_thelub lub_eq_bottom_iff rangeI)

      have "x = (\<Squnion> i. Y i)"        
        apply (auto intro!: flat_subset_min f_flat supindom xusup xnbot)
        apply (rule_tac A="cdom f" in subsetD)
        apply (auto intro!: flat_subset_min f_flat supindom xusup xnbot)
      done

      thus ?thesis
        by (metis (no_types) nmem_chain supindom xinY)
       
    qed
  qed
qed

definition dclosed :: "('a::po) set \<Rightarrow> bool" where
"dclosed xs = (\<forall>x\<in>xs. \<forall>y. y \<sqsubseteq> x \<longrightarrow> y\<in>xs)"

definition chfin :: "('a::po) set \<Rightarrow> bool" where
"chfin xs = (\<forall> Y. chain Y \<and> (\<forall> i. Y i \<in> xs) \<longrightarrow> (\<exists>n. max_in_chain n Y))"

(*
definition 
  cfun_override :: "('a::flat \<rightarrow> 'b::pcpo) \<Rightarrow> ('a \<rightarrow> 'b) \<Rightarrow> ('a \<rightarrow> 'b)" (infixl "\<oplus>" 65) where
"f \<oplus> g = (\<Lambda> x. if (f\<cdot>x = \<bottom>) then g\<cdot>x else f\<cdot>x)"
*)

end
