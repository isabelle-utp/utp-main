header {* \isaheader{Set Interface} *}
theory Intf_Set
imports "../../../Refine_Monadic/Refine_Monadic"
begin
consts i_set :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of set_rel i_set]


definition [simp]: "op_set_delete x s \<equiv> s - {x}"
definition [simp]: "op_set_isEmpty s \<equiv> s = {}"
definition [simp]: "op_set_isSng s \<equiv> card s = 1"
definition [simp]: "op_set_size_abort m s \<equiv> min m (card s)"
definition [simp]: "op_set_disjoint a b \<equiv> a\<inter>b={}"
definition [simp]: "op_set_filter P s \<equiv> {x\<in>s. P x}"
definition [simp]: "op_set_sel P s \<equiv> SPEC (\<lambda>x. x\<in>s \<and> P x)"
definition [simp]: "op_set_pick s \<equiv> SPEC (\<lambda>x. x\<in>s)"

(* TODO: Do op_set_pick_remove (like op_map_pick_remove) *)

context begin interpretation autoref_syn .
lemma [autoref_op_pat]:
  "s - {x} \<equiv> op_set_delete$x$s"

  "s = {} \<equiv> op_set_isEmpty$s"
  "{}=s \<equiv> op_set_isEmpty$s"

  "card s = 1 \<equiv> op_set_isSng$s"
  "\<exists>x. s={x} \<equiv> op_set_isSng$s"
  "\<exists>x. {x}=s \<equiv> op_set_isSng$s"

  "min m (card s) \<equiv> op_set_size_abort$m$s"
  "min (card s) m \<equiv> op_set_size_abort$m$s"

  "a\<inter>b={} \<equiv> op_set_disjoint$a$b"

  "{x\<in>s. P x} \<equiv> op_set_filter$P$s"

  "SPEC (\<lambda>x. x\<in>s \<and> P x) \<equiv> op_set_sel$P$s"
  "SPEC (\<lambda>x. P x \<and> x\<in>s) \<equiv> op_set_sel$P$s"

  "SPEC (\<lambda>x. x\<in>s) \<equiv> op_set_pick$s"
  by (auto intro!: eq_reflection simp: card_Suc_eq)

lemma [autoref_op_pat]:
  "SPEC (\<lambda>(u,v). (u,v)\<in>s) \<equiv> op_set_pick$s"
  "SPEC (\<lambda>(u,v). P u v \<and> (u,v)\<in>s) \<equiv> op_set_sel$(prod_case P)$s"
  "SPEC (\<lambda>(u,v). (u,v)\<in>s \<and> P u v) \<equiv> op_set_sel$(prod_case P)$s"
  by (auto intro!: eq_reflection)
end

lemma [autoref_itype]:
  "{} ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "insert ::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "op_set_delete ::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "op \<in> ::\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "op_set_isEmpty ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "op_set_isSng ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "op \<union> ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "op \<inter> ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "op - ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "op = ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "op \<subseteq> ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "op_set_disjoint ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_bool"
  "Ball ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i (I \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i i_bool"
  "Bex ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i (I \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i i_bool"
  "op_set_filter ::\<^sub>i (I \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "card ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_nat"
  "op_set_size_abort ::\<^sub>i i_nat \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_nat"
  "set ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "op_set_sel ::\<^sub>i (I \<rightarrow>\<^sub>i i_bool) \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_nres"
  "op_set_pick ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_nres"
  "Sigma ::\<^sub>i \<langle>Ia\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i (Ia \<rightarrow>\<^sub>i \<langle>Ib\<rangle>\<^sub>ii_set) \<rightarrow>\<^sub>i \<langle>\<langle>Ia,Ib\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_set"
  "op ` ::\<^sub>i (Ia\<rightarrow>\<^sub>iIb) \<rightarrow>\<^sub>i \<langle>Ia\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>Ib\<rangle>\<^sub>ii_set"
  by simp_all

lemma hom_set1[autoref_hom]:
  "CONSTRAINT {} (\<langle>R\<rangle>Rs)"
  "CONSTRAINT insert (R\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op \<in> (R\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op \<union> (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op \<inter> (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op - (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op = (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op \<subseteq> (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT Ball (\<langle>R\<rangle>Rs\<rightarrow>(R\<rightarrow>Id)\<rightarrow>Id)"
  "CONSTRAINT Bex (\<langle>R\<rangle>Rs\<rightarrow>(R\<rightarrow>Id)\<rightarrow>Id)"
  "CONSTRAINT card (\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT set (\<langle>R\<rangle>Rl\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op ` ((Ra\<rightarrow>Rb) \<rightarrow> \<langle>Ra\<rangle>Rs\<rightarrow>\<langle>Rb\<rangle>Rs)"
  by simp_all

lemma hom_set2[autoref_hom]:
  "CONSTRAINT op_set_delete (R\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op_set_isEmpty (\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op_set_isSng (\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op_set_size_abort (Id\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op_set_disjoint (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>Id)"
  "CONSTRAINT op_set_filter ((R\<rightarrow>Id)\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rs)"
  "CONSTRAINT op_set_sel ((R \<rightarrow> Id)\<rightarrow>\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rn)"
  "CONSTRAINT op_set_pick (\<langle>R\<rangle>Rs\<rightarrow>\<langle>R\<rangle>Rn)"
  by simp_all

lemma hom_set_Sigma[autoref_hom]:
  "CONSTRAINT Sigma (\<langle>Ra\<rangle>Rs \<rightarrow> (Ra \<rightarrow> \<langle>Rb\<rangle>Rs) \<rightarrow> \<langle>\<langle>Ra,Rb\<rangle>prod_rel\<rangle>Rs2)"
  by simp_all
  
definition "finite_set_rel R \<equiv> Range R \<subseteq> Collect (finite)"

lemma finite_set_rel_trigger: "finite_set_rel R \<Longrightarrow> finite_set_rel R" .

declaration {* Tagged_Solver.add_triggers 
  "Relators.relator_props_solver" @{thms finite_set_rel_trigger} *}

end
