theory alpha_boolean_algebra2
imports "../generic/utp_gen_pred" "~~/src/HOL/Algebra/Lattice"
begin

declare [[smt_solver = z3]]

sledgehammer_params [timeout = 40]

record ('a , 'b) alpha_boolean_algebra =
  carrier :: "'a set"
  wfalpha :: "('b set) set"
  alpha :: "'a \<Rightarrow> 'b set" ("\<alpha>\<index>_" [90] 90)
  conj  :: "['a, 'a] \<Rightarrow> 'a" (infixl "\<sqinter>\<index>" 80)
  disj  :: "['a, 'a] \<Rightarrow> 'a" (infixl "\<squnion>\<index>" 70)
  compl :: "'a \<Rightarrow> 'a" ("`\<index>_" [90] 90)
  top   :: "'b set \<Rightarrow> 'a" ("\<top>\<index>\<^bsub>_\<^esub>")
  bot   :: "'b set \<Rightarrow> 'a" ("\<bottom>\<index>\<^bsub>_\<^esub>")
  ble   :: "['a, 'a] => bool" (infixl "\<sqsubseteq>\<index>" 50)

locale alpha_boolean_algebra =
  fixes B (structure)
  assumes disj_closed:  "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> x \<squnion> y \<in> (carrier B)"
  and     compl_closed: "x \<in> carrier B \<Longrightarrow> ` x \<in> carrier B"
  and     top_closed:   "a \<in> wfalpha B \<Longrightarrow> \<top>\<^bsub>a\<^esub> \<in> carrier B"
  and     wfalpha:      "x \<in> carrier B \<Longrightarrow> (\<alpha> x) \<in> wfalpha B"
  and     empty_alpha:  "{} \<in> wfalpha B"
  and     union_alpha:  "\<lbrakk> a \<in> wfalpha B; b \<in> wfalpha B \<rbrakk> \<Longrightarrow> a \<union> b \<in> wfalpha B" 
  and     disj_alpha:   "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> \<alpha> (x \<squnion> y) = \<alpha> x \<union> \<alpha> y"
  and     compl_alpha:  "\<lbrakk> x \<in> carrier B \<rbrakk> \<Longrightarrow> \<alpha> (` x) = \<alpha> x"
  and     top_alpha:    "a \<in> wfalpha B \<Longrightarrow> \<alpha> (\<top>\<^bsub>a\<^esub>) = a"
  and     conj_defn:    "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> x \<sqinter> y = ` (` x \<squnion> ` y)"
  and     top_defn:     "\<lbrakk> x \<in> carrier B \<rbrakk> \<Longrightarrow> x \<squnion> ` x = \<top>\<^bsub>\<alpha>(x)\<^esub>"
  and     bot_defn:     "a \<in> wfalpha B \<Longrightarrow> \<bottom>\<^bsub>a\<^esub> = ` \<top>\<^bsub>a\<^esub>"
  and     leq_defn:     "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow>
                         x \<sqsubseteq> y \<longleftrightarrow> \<alpha> x = \<alpha> y \<and> (x \<squnion> y = y)"
  and     disj_assoc:   "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B \<rbrakk> \<Longrightarrow>  
                         (x\<squnion>y)\<squnion>z = x\<squnion>(y\<squnion>z)"
  and     disj_comm:    "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> x\<squnion>y = y\<squnion>x"
  and     disj_ident:   "x \<in> carrier B \<Longrightarrow> x \<squnion> \<bottom>\<^bsub>\<alpha>(x)\<^esub> = x"
  and     dist_1:        "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B \<rbrakk> \<Longrightarrow> x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  and     disj_compl:   "x \<in> carrier B \<Longrightarrow> x \<squnion> `x = \<top>\<^bsub>\<alpha>(x)\<^esub>"

(*  and     compl:        "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> y \<subseteq> \<alpha> x \<rbrakk> \<Longrightarrow> x = `(`x\<squnion>`y)\<squnion>(`(`x\<squnion>y))" *)

begin

lemma carrier_non_empty: "\<exists> x. x \<in> carrier B"
  by (metis empty_alpha top_closed)

lemma carrier_non_empty_alpha: "\<forall> a\<in>wfalpha B. \<exists> x. (x \<in> carrier B \<and> \<alpha> x = a)"
  by (metis top_alpha top_closed)

lemma bot_closed: "a \<in> wfalpha B \<Longrightarrow> \<bottom>\<^bsub>a\<^esub> \<in> carrier B"
  by (metis bot_defn compl_closed top_closed)

lemma conj_closed:  "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> x \<sqinter> y \<in> carrier B"
  by (metis compl_closed conj_defn disj_closed)

lemma conj_alpha: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> \<alpha> (x \<sqinter> y) = \<alpha> x \<union> \<alpha> y"
  by (smt compl_alpha compl_closed conj_defn disj_alpha disj_closed)

lemma bot_alpha: "a \<in> wfalpha B \<Longrightarrow> \<alpha> (\<bottom>\<^bsub>a\<^esub>) = a"
  by (metis bot_defn compl_alpha top_alpha top_closed)

lemma disj_alpha_subset: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> \<alpha> y \<subseteq> \<alpha> x \<Longrightarrow> \<alpha> (x \<squnion> y) = \<alpha> x"
  by (metis disj_alpha sup_absorb1)

lemma disj_wfalpha: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> \<alpha> (x \<squnion> y) \<in> wfalpha B"
  by (metis disj_closed wfalpha)

lemma conj_alpha_subset: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> \<alpha> y \<subseteq> \<alpha> x \<Longrightarrow> \<alpha> (x \<sqinter> y) = \<alpha> x"
by (metis conj_alpha sup_absorb1)

lemma conj_wfalpha: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> \<alpha> (x \<sqinter> y) \<in> wfalpha B"
  by (metis conj_closed wfalpha)

lemma compl_wfalpha: "x \<in> carrier B \<Longrightarrow> \<alpha> (`x) \<in> wfalpha B"
  by (metis compl_closed wfalpha)

lemma union_wfalpha: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> \<alpha> x \<union> \<alpha> y \<in> wfalpha B"
  by (metis union_alpha wfalpha)

(*
lemma alpha_disj_intro[intro]: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; a \<in> \<alpha> x \<or> a \<in> \<alpha> y \<rbrakk> \<Longrightarrow> a \<in> \<alpha>(x \<squnion> y)"
  by auto

lemma alpha_conj_intro[intro]: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; a \<in> \<alpha> x \<or> a \<in> \<alpha> y \<rbrakk> \<Longrightarrow> a \<in> \<alpha>(x \<sqinter> y)"
  by (auto)

lemma alpha_disj_elim[elim!]: "\<lbrakk> a \<in> \<alpha> (x \<squnion> y);  x \<in> carrier B; y \<in> carrier B; a \<in> \<alpha> x \<Longrightarrow> P; a \<in> \<alpha> y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

lemma alpha_conj_elim[elim!]: "\<lbrakk> a \<in> \<alpha> (x \<sqinter> y);  x \<in> carrier B; y \<in> carrier B; a \<in> \<alpha> x \<Longrightarrow> P; a \<in> \<alpha> y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto
*)

lemma top_alpha_eq: "\<lbrakk> a \<in> wfalpha B; b \<in> wfalpha B \<rbrakk> \<Longrightarrow> \<top>\<^bsub>a\<^esub> = \<top>\<^bsub>b\<^esub> \<Longrightarrow> a = b"
  by (metis top_alpha)

lemma split_arb: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> x = \<alpha> y \<rbrakk> \<Longrightarrow> x \<squnion> `x = y \<squnion> `y"
  by (metis top_defn)

lemma alpha_compl_sub:"\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> y \<subseteq> \<alpha> x \<rbrakk> \<Longrightarrow> \<alpha>(`x\<squnion>y) = \<alpha>(x)"
  by (metis compl_alpha compl_closed disj_alpha sup_absorb1)

lemma alpha_compl_eq:"\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> y = \<alpha> x \<rbrakk> \<Longrightarrow> \<alpha>(`x\<squnion>y) = \<alpha>(x)"
  by (metis compl_alpha compl_closed disj_alpha top_alpha top_defn wfalpha)


lemma double_compl: "x \<in> carrier B \<Longrightarrow> ` ` x = x"
  by (smt bot_defn compl_alpha compl_closed conj_defn disj_comm disj_compl disj_ident dist_1 split_arb surjective wfalpha)

lemma disj_anhil: "\<lbrakk> x \<in> carrier B \<rbrakk> \<Longrightarrow>  x \<squnion> \<top>\<^bsub>\<alpha> x\<^esub> = \<top>\<^bsub>\<alpha> x\<^esub>"
  by (smt bot_defn compl_alpha compl_closed conj_defn disj_alpha disj_assoc disj_closed disj_compl disj_ident dist_1 double_compl top_alpha top_closed wfalpha)

lemma disj_bots: "a \<in> wfalpha B \<Longrightarrow> \<bottom>\<^bsub>a\<^esub> = \<bottom>\<^bsub>a \<^esub>\<squnion> \<bottom>\<^bsub>a\<^esub>"
  by (metis bot_alpha bot_closed disj_ident)

lemma disj_idem: "x \<in> carrier B \<Longrightarrow> x \<squnion> x = x"
  by (smt bot_defn compl_closed conj_defn disj_anhil disj_closed disj_compl disj_ident dist_1 double_compl wfalpha)

lemma conj_idem: "x \<in> carrier B \<Longrightarrow> x \<sqinter> x = x"
  by (metis compl_closed conj_defn disj_idem double_compl)

lemma conj_assoc: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B \<rbrakk> \<Longrightarrow>  (x\<sqinter>y)\<sqinter>z = x\<sqinter>(y\<sqinter>z)"
  by (smt compl_closed conj_closed conj_defn disj_assoc disj_closed double_compl)

lemma conj_comm:  "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> x\<sqinter>y = y\<sqinter>x"
  by (metis compl_closed conj_defn disj_comm)

lemma conj_ident: "x \<in> carrier B \<Longrightarrow> x \<sqinter> \<top>\<^bsub>\<alpha>(x)\<^esub> = x"
  by (smt bot_defn compl_alpha compl_closed conj_defn disj_ident double_compl top_closed wfalpha)

lemma dist_2: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B \<rbrakk> \<Longrightarrow> x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
  by (smt compl_closed conj_closed conj_defn disj_closed disj_comm dist_1 double_compl)  

lemma conj_compl: "x \<in> carrier B \<Longrightarrow> x \<sqinter> `x = \<bottom>\<^bsub>\<alpha>(x)\<^esub>"
  by (metis bot_defn compl_alpha compl_closed conj_defn disj_compl wfalpha)

lemma conj_anhil: "\<lbrakk> x \<in> carrier B \<rbrakk> \<Longrightarrow> \<bottom>\<^bsub>\<alpha> x\<^esub> \<sqinter> x = \<bottom>\<^bsub>\<alpha> x\<^esub>"
  by (metis compl_closed conj_assoc conj_comm conj_compl conj_idem)

lemma top_bot: "a \<in> wfalpha B \<Longrightarrow> \<top>\<^bsub>a\<^esub> = ` \<bottom>\<^bsub>a\<^esub>"
  by (metis bot_defn double_compl top_closed)

lemma compl: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> y \<subseteq> \<alpha> x \<rbrakk> \<Longrightarrow> x = `(`x\<squnion>`y)\<squnion>(`(`x\<squnion>y))"
  by (smt alpha_compl_sub compl_alpha compl_closed conj_assoc conj_compl conj_defn conj_idem conj_ident disj_alpha disj_assoc disj_closed disj_comm disj_compl disj_ident dist_2 double_compl)

lemma leq_refl: "\<lbrakk> x \<in> carrier B \<rbrakk> \<Longrightarrow> x \<sqsubseteq> x"
  by (metis disj_idem leq_defn subset_refl)

lemma leq_trans: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B \<rbrakk> \<Longrightarrow>
                  x \<sqsubseteq> y \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> z"
  by (smt disj_assoc leq_defn)


lemma leq_antisym: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B \<rbrakk> \<Longrightarrow> 
                    x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
  by (metis disj_comm leq_defn)

lemma alpha_iso: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B; \<alpha> x \<subseteq> \<alpha> y \<rbrakk> \<Longrightarrow> \<alpha> (x\<squnion>z) \<subseteq> \<alpha> (y\<squnion>z)"
  by (metis Un_least Un_upper2 disj_alpha le_supI1)

lemma disj_iso: 
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "z \<in> carrier B" "x \<sqsubseteq> y" 
  shows "x\<squnion>z \<sqsubseteq> y\<squnion>z"
  by (smt assm disj_alpha disj_assoc disj_closed disj_comm disj_idem leq_defn)

lemma disj_ub: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> x \<sqsubseteq> x\<squnion>y"
  by (smt disj_assoc disj_closed disj_idem leq_defn)

lemma disj_lub: "\<lbrakk> x \<in> carrier B ; y \<in> carrier B ; z \<in> carrier B \<rbrakk> 
                \<Longrightarrow> x\<squnion>y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  by (smt disj_assoc disj_closed disj_comm disj_ub leq_defn)

lemma comp_anti: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> x = \<alpha> y \<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<longleftrightarrow> `y \<sqsubseteq> `x"
  by (smt alpha_compl_eq compl compl_closed disj_closed disj_comm disj_ub double_compl disj_idem leq_defn order_refl top_defn)

text {* We now show that $0$ and $1$ are the least and greatest
elements of the order *}

lemma bot_min: "\<lbrakk> x \<in> carrier B \<rbrakk> \<Longrightarrow> \<bottom>\<^bsub>\<alpha>(x)\<^esub> \<sqsubseteq> x"
  by (metis bot_alpha bot_closed disj_ident disj_lub leq_refl wfalpha)

lemma top_max: "\<lbrakk> x \<in> carrier B \<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<top>\<^bsub>\<alpha>(x)\<^esub>"
  by (metis compl_alpha compl_closed disj_compl disj_ub subset_refl)

lemma conj_iso: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> x\<sqinter>z \<sqsubseteq> y\<sqinter>z"
  by (metis conj_closed conj_comm disj_ub dist_2 leq_defn)

lemma leq_conj: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> x = \<alpha> y \<rbrakk> \<Longrightarrow> 
                 x \<sqsubseteq> y \<longleftrightarrow> x\<sqinter>y = x"
  by (smt bot_closed conj_anhil conj_comm conj_ident conj_iso disj_ident dist_1 leq_defn top_closed top_max wfalpha)

lemma conj_lb: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> x\<sqinter>y \<sqsubseteq> x"
  proof -
    assume assm: "x \<in> carrier B" "y \<in> carrier B"
    then have "x\<sqinter>y \<in> carrier B"
      by (metis conj_closed)

    then have a1:"(x \<sqinter> y) \<squnion> x = ((x \<sqinter> y) \<squnion> x) \<sqinter> \<top>\<^bsub>\<alpha>((x \<sqinter> y) \<squnion> x)\<^esub>"
      by (metis assm conj_ident disj_closed)

    fix a::"'b set"

    assume "\<alpha> x = \<alpha> y"

    have "((x \<sqinter> y) \<squnion> x) \<sqinter> \<top>\<^bsub>a\<^esub> = ((x \<sqinter> y) \<sqinter> \<top>\<^bsub>a\<^esub>) \<squnion> (x \<sqinter> \<top>\<^bsub>a\<^esub>)"
      
    have "... = ((x \<squnion> \<top>\<^bsub>a\<^esub>) \<sqinter> (y \<squnion> \<top>\<^bsub>a\<^esub>) \<sqinter> (x \<squnion> \<top>\<^bsub>a\<^esub>)"

by (metis assm(1) assm(2) conj_ident disj_anhil dist_2 top_closed wfalpha)
      by (metis assm(1) assm(2) conj_idem dist_2)

    

    then also have "x \<sqinter> (y \<squnion> x) = x"
      by (metis a1 assm conj_ident disj_anhil dist_2 top_closed wfalpha)


    with assm show ?thesis
      apply(simp add:leq_defn)
  by (metis conj_alpha_subset conj_assoc conj_closed conj_comm leq_conj leq_refl)




lemma conj_lb': "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> x \<subseteq> \<alpha> y \<rbrakk> \<Longrightarrow> x\<sqinter>y \<sqsubseteq> y"
  by (metis conj_comm conj_lb)
 
lemma conj_glb: "\<lbrakk> x \<in> carrier B ; y \<in> carrier B ; z \<in> carrier B; \<alpha> x = \<alpha> y; \<alpha> y = \<alpha> z \<rbrakk> \<Longrightarrow> 
                 z \<sqsubseteq>  x\<sqinter>y \<longleftrightarrow> z\<sqsubseteq>x \<and> z\<sqsubseteq>y"
  by (smt conj_alpha_subset conj_assoc conj_closed conj_comm conj_lb leq_conj subset_refl)

lemma leq_symm_intro: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; x \<sqsubseteq> y; y \<sqsubseteq> x \<rbrakk> \<Longrightarrow> x = y"
  by (metis disj_comm leq_defn)

text {* Next we show the absorption laws of lattice theory *}

lemma absorption1: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> y \<subseteq> \<alpha> x \<rbrakk> \<Longrightarrow> (x\<squnion>y)\<sqinter>x = x"
  by (metis conj_comm disj_alpha_subset disj_closed disj_ub leq_conj)

lemma absorption2: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> y \<subseteq> \<alpha> x \<rbrakk> \<Longrightarrow> x\<squnion>x\<sqinter>y=x"
  by (metis conj_alpha_subset conj_closed conj_lb disj_comm leq_defn)

text {* Next we prove some simple laws about $0$ and $1$ *}

lemma top_disj: "x \<in> carrier B \<Longrightarrow> x \<squnion> \<top>\<^bsub>\<alpha> x\<^esub> = \<top>\<^bsub>\<alpha> x\<^esub>"
  by (metis leq_defn top_alpha top_closed top_max wfalpha)

lemma top_conj: "x \<in> carrier B \<Longrightarrow> x \<sqinter> \<top>\<^bsub>\<alpha> x\<^esub> = x"
  by (metis leq_conj top_alpha top_closed top_max wfalpha)


lemma demorgan1: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> `(x \<sqinter> y) = `x \<squnion> `y"
  by (metis compl_closed conj_defn disj_closed double_compl)

lemma demorgan2: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> `(x \<squnion> y) = `x \<sqinter> `y"
  by (metis compl_closed conj_defn double_compl)

lemma demorgan3: "\<lbrakk> x \<in> carrier B; y \<in> carrier B \<rbrakk> \<Longrightarrow> x\<squnion>y = `((`x)\<sqinter>(`y))"
  by (metis compl_closed demorgan1 double_compl)

lemma ba_1: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B; \<alpha> x = \<alpha> y; \<alpha> y = \<alpha> z \<rbrakk> \<Longrightarrow> x\<squnion>y\<squnion>(`y) = z\<squnion>(`z)"
  by (metis compl_closed disj_assoc top_defn top_disj)

lemma ba_2: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> x = \<alpha> y \<rbrakk> \<Longrightarrow> x\<squnion>x = x\<squnion>(`(y\<squnion>(`y)))"
  by (metis bot_defn disj_compl disj_idem disj_ident wfalpha)

lemma ba_3: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> y \<subseteq> \<alpha> x \<rbrakk> \<Longrightarrow> x = (x\<sqinter>y)\<squnion>(x\<sqinter>(`y))"
  by (metis compl compl_closed conj_defn double_compl)

lemma ba_4: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> x = \<alpha> y \<rbrakk> \<Longrightarrow> x = (x\<squnion>(`y))\<sqinter>(x\<squnion>y)"
  by (metis compl_closed conj_comm conj_compl disj_ident dist_1)

lemma ba_5:
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "\<alpha> y = \<alpha> x"
  shows "(x\<squnion>y)\<sqinter>(`x) = y\<sqinter>(`x)"
  by (smt assm compl_alpha compl_closed conj_anhil conj_closed conj_comm conj_compl disj_closed disj_comm disj_ident dist_2)

lemma compl_1: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> x = \<alpha> y \<rbrakk> \<Longrightarrow> `x = `(x\<squnion>y)\<squnion>(`(x\<squnion>(`y)))"
  by (metis compl compl_alpha compl_closed double_compl order_eq_iff)

lemma compl_2:
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "\<alpha> y \<subseteq> \<alpha> x"
  shows "x \<squnion> `(y \<squnion> `x) = x"
  by (smt assm compl compl_alpha compl_closed disj_alpha_subset disj_closed disj_comm disj_lub leq_defn leq_refl) 

lemma compl_3:
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "\<alpha> y \<subseteq> \<alpha> x"
  shows "`x \<squnion> `(y \<squnion> x) = `x"
  by (metis assm compl_2 compl_alpha compl_closed double_compl)

lemma compl_4:
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "z \<in> carrier B" "\<alpha> x = \<alpha> y" "\<alpha> y = \<alpha> z"
  shows "`(x \<squnion> y) \<squnion> (z \<squnion> `(x \<squnion> `y)) = `x \<squnion> z"
  by (smt assm compl_1 compl_closed disj_assoc disj_closed disj_comm)

lemma compl_5:
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "\<alpha> x = \<alpha> y"
  shows "x \<squnion> `(y \<squnion> x) = x \<squnion> `y"
  by (smt assm ba_4 ba_5 compl_alpha compl_closed demorgan2 demorgan3 disj_closed disj_comm double_compl)

lemma compl_6:
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "z \<in> carrier B" "\<alpha> x = \<alpha> y" "\<alpha> y = \<alpha> z"
  shows "`x = `(y \<squnion> x) \<squnion> `(x \<squnion> `(z \<squnion> y))"
  by (smt alpha_compl_eq assm(1) assm(2) assm(3) assm(4) assm(5) compl_1 compl_5 compl_alpha compl_closed demorgan2 disj_assoc disj_closed disj_comm double_compl)

lemma compl7:
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "\<alpha> x = \<alpha> y"
  shows "x \<squnion> `(`y \<squnion> x) = x \<squnion> y"
  by (metis assm(1) assm(2) assm(3) compl_5 compl_alpha compl_closed double_compl)


lemma conj_compl1: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; \<alpha> x = \<alpha> y \<rbrakk> \<Longrightarrow> `(x\<sqinter>y)\<sqinter>x = x\<sqinter>(`y)"
  by (smt ba_5 compl_alpha compl_closed conj_comm demorgan1 double_compl)

lemma conj_compl2: "\<lbrakk> x \<in> carrier B; y \<in> carrier B; z \<in> carrier B; \<alpha> x = \<alpha> y; \<alpha> y = \<alpha> z \<rbrakk> \<Longrightarrow> `x\<sqinter>y = `(z\<sqinter>x)\<sqinter>(`x\<sqinter>y)"
  by (smt absorption2 compl_closed conj_assoc conj_closed conj_comm demorgan2 order_refl)

lemma galois_1:
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "z \<in> carrier B" "\<alpha> x = \<alpha> y" "\<alpha> y = \<alpha> z"
  shows "x\<sqinter>(`y) \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> y\<squnion>z"
proof
  assume "x \<sqinter> `y \<sqsubseteq> z"
  thus "x \<sqsubseteq> y \<squnion> z"
    by (smt assm compl7 compl_closed conj_closed conj_defn disj_alpha disj_assoc disj_closed disj_comm double_compl leq_defn)
next
  assume "x \<sqsubseteq> y \<squnion> z"
  thus "x \<sqinter> `y \<sqsubseteq> z"
    by (smt alpha_compl_eq assm ba_5 compl_alpha compl_closed conj_assoc conj_comm conj_defn demorgan3 disj_closed leq_conj)
qed

lemma galois_2: 
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "z \<in> carrier B" "\<alpha> x = \<alpha> y" "\<alpha> y = \<alpha> z"
  shows "x \<sqsubseteq> y\<squnion>(`z) \<longleftrightarrow> x\<sqinter>z \<sqsubseteq> y"
  by (auto, (metis assm compl_alpha compl_closed disj_comm double_compl galois_1)+)

lemma galois_aux: 
  assumes assm: "x \<in> carrier B" "y \<in> carrier B" "\<alpha> x = \<alpha> y"
  shows "x\<sqinter>y = \<bottom>\<^bsub>\<alpha>(x)\<^esub> \<longleftrightarrow> x \<sqsubseteq> `y"
apply(auto)
apply(metis assm bot_min compl_alpha compl_closed double_compl galois_1 disj_idem)
apply(smt assm bot_defn compl_5 compl_alpha compl_closed conj_comm conj_defn leq_defn top_defn wfalpha)
done

abbreviation "ba_partial_order \<equiv>
 \<lparr> partial_object.carrier = carrier B,
   eq = (\<lambda> x y. x = y), 
   le = ble B \<rparr>"
end

sublocale alpha_boolean_algebra \<subseteq> lattice "ba_partial_order" where
  "partial_object.carrier ba_partial_order = carrier B" and
  "eq ba_partial_order = (\<lambda> x y. x = y)" and
  "le ba_partial_order = ble B"
apply(unfold_locales)
apply(auto)
apply(metis leq_refl)
apply (metis leq_symm_intro)
apply(metis leq_trans)
apply(rule_tac x="x\<squnion>y" in exI)
apply(simp add:least_def)
apply(safe)
apply(simp_all add:Upper_def)
apply(safe)
apply(subgoal_tac "\<alpha> x = \<alpha> y")
apply (metis disj_ub subset_refl)


done

end


