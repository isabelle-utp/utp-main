(* Title: Examples/Vector_Spaces/VS_Modules.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Modules\<close>
theory VS_Modules
  imports 
    VS_Groups
    Complex_Main
begin



subsection\<open>\<^text>\<open>module_with\<close>\<close>

locale module_with = ab_group_add plus\<^sub>M zero\<^sub>M minus\<^sub>M uminus\<^sub>M
  for plus\<^sub>M :: "['m, 'm] \<Rightarrow> 'm" (infixl \<open>+\<^sub>M\<close> 65)
    and zero\<^sub>M (\<open>0\<^sub>M\<close>)
    and minus\<^sub>M (infixl \<open>-\<^sub>M\<close> 65)
    and uminus\<^sub>M (\<open>-\<^sub>M _\<close> [81] 80) +
  fixes scale :: "['cr1::comm_ring_1, 'm] \<Rightarrow> 'm" (infixr "*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h" 75)
  assumes scale_right_distrib[algebra_simps]: 
    "a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h (x +\<^sub>M y) = a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x +\<^sub>M a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h y"
    and scale_left_distrib[algebra_simps]:
      "(a + b) *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x = a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x +\<^sub>M b *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x"
    and scale_scale[simp]: "a *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h (b *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x) = (a * b) *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x"
    and scale_one[simp]: "1 *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h x = x"

lemma module_with_overloaded[ud_with]: "module = module_with (+) 0 (-) uminus"
  unfolding module_def module_with_def module_with_axioms_def
  by (simp add: comm_ring_1_axioms ab_group_add_axioms)

locale module_pair_with =
  M\<^sub>1: module_with plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 +
  M\<^sub>2: module_with plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
  for plus\<^sub>M\<^sub>_\<^sub>1 :: "['m_1, 'm_1] \<Rightarrow> 'm_1" (infixl \<open>+\<^sub>M\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>M\<^sub>_\<^sub>1 (\<open>0\<^sub>M\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>M\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>M\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>M\<^sub>_\<^sub>1 (\<open>-\<^sub>M\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>1\<close> 75)
    and plus\<^sub>M\<^sub>_\<^sub>2 :: "['m_2, 'm_2] \<Rightarrow> 'm_2" (infixl \<open>+\<^sub>M\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>M\<^sub>_\<^sub>2 (\<open>0\<^sub>M\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>M\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>M\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>M\<^sub>_\<^sub>2 (\<open>-\<^sub>M\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>2\<close> 75)

lemma module_pair_with_overloaded[ud_with]: 
  "module_pair =
    (
      \<lambda>scale\<^sub>1 scale\<^sub>2.
        module_pair_with (+) 0 (-) uminus scale\<^sub>1 (+) 0 (-) uminus scale\<^sub>2
    )"
  unfolding module_pair_def module_pair_with_def 
  unfolding module_with_overloaded
  ..

locale module_hom_with = 
  M\<^sub>1: module_with plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 +
  M\<^sub>2: module_with plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
  for plus\<^sub>M\<^sub>_\<^sub>1 :: "['m_1, 'm_1] \<Rightarrow> 'm_1" (infixl \<open>+\<^sub>M\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>M\<^sub>_\<^sub>1 (\<open>0\<^sub>M\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>M\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>M\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>M\<^sub>_\<^sub>1 (\<open>-\<^sub>M\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>1\<close> 75)
    and plus\<^sub>M\<^sub>_\<^sub>2 :: "['m_2, 'm_2] \<Rightarrow> 'm_2" (infixl \<open>+\<^sub>M\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>M\<^sub>_\<^sub>2 (\<open>0\<^sub>M\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>M\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>M\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>M\<^sub>_\<^sub>2 (\<open>-\<^sub>M\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 (infixr \<open>*s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>'_\<^sub>2\<close> 75) +
  fixes f :: "'m_1 \<Rightarrow> 'm_2"
  assumes add: "f (b1 +\<^sub>M\<^sub>_\<^sub>1 b2) = f b1 +\<^sub>M\<^sub>_\<^sub>2 f b2"
    and scale: "f (r *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>_\<^sub>1 b) = r *s\<^sub>w\<^sub>i\<^sub>t\<^sub>h\<^sub>_\<^sub>2 f b"
begin

sublocale module_pair_with ..

end

lemma module_hom_with_overloaded[ud_with]: 
  "module_hom =
    (
      \<lambda>scale\<^sub>1 scale\<^sub>2.
        module_hom_with (+) 0 (-) uminus scale\<^sub>1 (+) 0 (-) uminus scale\<^sub>2
    )"
  unfolding 
    module_hom_def module_hom_axioms_def 
    module_hom_with_def module_hom_with_axioms_def
  unfolding module_with_overloaded
  ..
ud \<open>module.subspace\<close> (\<open>(with _ _ _ : \<guillemotleft>subspace\<guillemotright> _)\<close> [1000, 999, 998, 1000] 10)
ud \<open>module.span\<close> (\<open>(with _ _ _ : \<guillemotleft>span\<guillemotright> _)\<close> [1000, 999, 998, 1000] 10)
ud \<open>module.dependent\<close> 
  (\<open>(with _ _ _ _ : \<guillemotleft>dependent\<guillemotright> _)\<close> [1000, 999, 998, 997, 1000] 10)
ud \<open>module.representation\<close> 
  (
    \<open>(with _ _ _ _ : \<guillemotleft>representation\<guillemotright> _ _)\<close> 
    [1000, 999, 998, 997, 1000, 999] 10
  )

abbreviation independent_with 
  (\<open>(with _ _ _ _ : \<guillemotleft>independent\<guillemotright> _)\<close> [1000, 999, 998, 997, 1000] 10)
  where 
    "(with zero\<^sub>C\<^sub>R\<^sub>1 zero\<^sub>M  scale\<^sub>M plus\<^sub>M : \<guillemotleft>independent\<guillemotright> s) \<equiv>
      \<not>(with zero\<^sub>C\<^sub>R\<^sub>1 zero\<^sub>M scale\<^sub>M plus\<^sub>M : \<guillemotleft>dependent\<guillemotright> s)"

lemma span_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows 
    "(
      A ===> 
      (A ===> A ===> A) ===>
      ((=) ===> A ===> A) ===> 
      rel_set A ===> 
      rel_set A
    ) span.with span.with"
  unfolding span.with_def
proof(intro rel_funI)
  fix p p' z z' X X' and s s'::"'c \<Rightarrow> _"
  assume transfer_rules[transfer_rule]:   
    "(A ===> A ===> A) p p'" 
    "A z z'" 
    "((=) ===> A ===> A) s s'" 
    "rel_set A X X'"
  have "Domainp A z" using \<open>A z z'\<close> by force
  have *: "t \<subseteq> X \<Longrightarrow> (\<forall>x\<in>t. Domainp A x)" for t
    by (meson Domainp.DomainI \<open>rel_set A X X'\<close> rel_setD1 subsetD)
  note swt = sum_with_transfer
    [
      OF assms(1,2,2), 
      THEN rel_funD, 
      THEN rel_funD, 
      THEN rel_funD,  
      THEN rel_funD,  
      OF transfer_rules(1,2)
    ]
  have DsI: "Domainp A (sum_with p z r t)" 
    if "\<And>x. x \<in> t \<Longrightarrow> Domainp A (r x)" "t \<subseteq> Collect (Domainp A)" for r t
    by (metis that Domainp_sum_with transfer_rules(1,2))
  from Domainp_apply2I[OF transfer_rules(3)]
  have Domainp_sI: "Domainp A x \<Longrightarrow> Domainp A (s y x)" for x y by auto
  show "rel_set A
    {sum_with p z (\<lambda>a. s (r a) a) t |t r. finite t \<and> t \<subseteq> X}
        {sum_with p' z' (\<lambda>a. s' (r a) a) t |t r. finite t \<and> t \<subseteq> X'}"
    apply transfer_prover_start 
    apply transfer_step+
    by (insert *) (auto intro!: DsI Domainp_sI)
qed

lemma dependent_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows 
    "(
      (=) ===>
      A ===> 
      (A ===> A ===> A) ===>
      ((=) ===> A ===> A) ===> 
      rel_set A ===> 
      (=)
    ) dependent.with dependent.with"
  unfolding dependent.with_def 
proof(intro rel_funI)
  fix p p' z z' X X' and zb zb' ::'c and s s'::"'c \<Rightarrow> _"
  assume [transfer_rule]: 
    "(A ===> A ===> A) p p'"
    "A z z'"
    "zb = zb'"
    "((=) ===> A ===> A) s s'" 
    "rel_set A X X'"
  have *: "t \<subseteq> X \<Longrightarrow> (\<forall>x\<in>t. Domainp A x)" for t
    by (meson Domainp.DomainI \<open>rel_set A X X'\<close> rel_setD1 subsetD)
  show 
    "(
        \<exists>t u. 
          finite t \<and> 
          t \<subseteq> X \<and> 
          sum_with p z (\<lambda>v. s (u v) v) t = z \<and> 
          (\<exists>v\<in>t. u v \<noteq> zb)
     ) =
      (
        \<exists>t u. 
          finite t \<and> 
          t \<subseteq> X' \<and> 
          sum_with p' z' (\<lambda>v. s' (u v) v) t = z' \<and> 
          (\<exists>v\<in>t. u v \<noteq> zb')
      )"
    apply transfer_prover_start
    apply transfer_step+
    by (insert *) (auto intro!: comm_monoid_add_ow.sum_with_closed)
qed

ctr relativization
  synthesis ctr_simps
  assumes [transfer_rule]: "is_equality A" "bi_unique B"
  trp (?'a A) and (?'b B) 
  in subspace_with: subspace.with_def



subsection\<open>\<open>module_ow\<close>\<close>


subsubsection\<open>Definitions and common properties\<close>


text\<open>Single module.\<close>

locale module_ow = ab_group_add_ow U\<^sub>M plus\<^sub>M zero\<^sub>M minus\<^sub>M uminus\<^sub>M
  for U\<^sub>M :: "'m set" 
    and plus\<^sub>M (infixl \<open>+\<^sub>M\<close> 65)
    and zero\<^sub>M (\<open>0\<^sub>M\<close>)
    and minus\<^sub>M (infixl \<open>-\<^sub>M\<close> 65)
    and uminus\<^sub>M (\<open>-\<^sub>M _\<close> [81] 80) +
  fixes scale :: "['cr1::comm_ring_1, 'm] \<Rightarrow> 'm" (infixr "*s\<^sub>M" 75)
  assumes scale_closed[simp, intro]: "x \<in> U\<^sub>M \<Longrightarrow> a *s\<^sub>M x \<in> U\<^sub>M"
    and scale_right_distrib[algebra_simps]: 
    "\<lbrakk> x \<in> U\<^sub>M; y \<in> U\<^sub>M \<rbrakk> \<Longrightarrow> a *s\<^sub>M (x +\<^sub>M y) = a *s\<^sub>M x +\<^sub>M a *s\<^sub>M y"
    and scale_left_distrib[algebra_simps]: 
      "x \<in> U\<^sub>M \<Longrightarrow> (a + b) *s\<^sub>M x = a *s\<^sub>M x +\<^sub>M b *s\<^sub>M x"
    and scale_scale[simp]: 
      "x \<in> U\<^sub>M \<Longrightarrow> a *s\<^sub>M (b *s\<^sub>M x) = (a * b) *s\<^sub>M x"
    and scale_one[simp]: "x \<in> U\<^sub>M \<Longrightarrow> 1 *s\<^sub>M x = x"
begin

lemma scale_closed'[simp]: "\<forall>a. \<forall>x\<in>U\<^sub>M. a *s\<^sub>M x \<in> U\<^sub>M" by simp

lemma minus_closed'[simp]: "\<forall>x\<in>U\<^sub>M. \<forall>y\<in>U\<^sub>M. x -\<^sub>M y \<in> U\<^sub>M"
  by (simp add: ab_diff_conv_add_uminus add_closed' uminus_closed)

lemma uminus_closed'[simp]: "\<forall>x\<in>U\<^sub>M. -\<^sub>M x \<in> U\<^sub>M" by (simp add: uminus_closed)

tts_register_sbts \<open>(*s\<^sub>M)\<close> | U\<^sub>M
  by (rule tts_AB_C_transfer[OF scale_closed])
    (auto simp: bi_unique_eq right_total_eq)

tts_register_sbts plus\<^sub>M | U\<^sub>M
  by (rule tts_AB_C_transfer[OF add_closed])
    (auto simp: bi_unique_eq right_total_eq)

tts_register_sbts zero\<^sub>M | U\<^sub>M 
  by (meson Domainp.cases zero_closed)

end


text\<open>Pair of modules.\<close>

locale module_pair_ow = 
  M\<^sub>1: module_ow U\<^sub>M\<^sub>_\<^sub>1 plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 +
  M\<^sub>2: module_ow U\<^sub>M\<^sub>_\<^sub>2 plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
  for U\<^sub>M\<^sub>_\<^sub>1 :: "'m_1 set"
    and plus\<^sub>M\<^sub>_\<^sub>1 (infixl \<open>+\<^sub>M\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>M\<^sub>_\<^sub>1 (\<open>0\<^sub>M\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>M\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>M\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>M\<^sub>_\<^sub>1 (\<open>-\<^sub>M\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['cr1::comm_ring_1, 'm_1] \<Rightarrow> 'm_1" (infixr \<open>*s\<^sub>M\<^sub>'_\<^sub>1\<close> 75)
    and U\<^sub>M\<^sub>_\<^sub>2 :: "'m_2 set"
    and plus\<^sub>M\<^sub>_\<^sub>2 (infixl \<open>+\<^sub>M\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>M\<^sub>_\<^sub>2 (\<open>0\<^sub>M\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>M\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>M\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>M\<^sub>_\<^sub>2 (\<open>-\<^sub>M\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['cr1::comm_ring_1, 'm_2] \<Rightarrow> 'm_2" (infixr \<open>*s\<^sub>M\<^sub>'_\<^sub>2\<close> 75)


text\<open>Module homomorphisms.\<close>

locale module_hom_ow = 
  M\<^sub>1: module_ow U\<^sub>M\<^sub>_\<^sub>1 plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 +
  M\<^sub>2: module_ow U\<^sub>M\<^sub>_\<^sub>2 plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
  for U\<^sub>M\<^sub>_\<^sub>1 :: "'m_1 set"
    and plus\<^sub>M\<^sub>_\<^sub>1 (infixl \<open>+\<^sub>M\<^sub>'_\<^sub>1\<close> 65)
    and zero\<^sub>M\<^sub>_\<^sub>1 (\<open>0\<^sub>M\<^sub>'_\<^sub>1\<close>)
    and minus\<^sub>M\<^sub>_\<^sub>1 (infixl \<open>-\<^sub>M\<^sub>'_\<^sub>1\<close> 65)
    and uminus\<^sub>M\<^sub>_\<^sub>1 (\<open>-\<^sub>M\<^sub>'_\<^sub>1 _\<close> [81] 80)
    and scale\<^sub>1 :: "['cr1::comm_ring_1, 'm_1] \<Rightarrow> 'm_1" (infixr \<open>*s\<^sub>M\<^sub>'_\<^sub>1\<close> 75)
    and U\<^sub>M\<^sub>_\<^sub>2 :: "'m_2 set"
    and plus\<^sub>M\<^sub>_\<^sub>2 (infixl \<open>+\<^sub>M\<^sub>'_\<^sub>2\<close> 65)
    and zero\<^sub>M\<^sub>_\<^sub>2 (\<open>0\<^sub>M\<^sub>'_\<^sub>2\<close>)
    and minus\<^sub>M\<^sub>_\<^sub>2 (infixl \<open>-\<^sub>M\<^sub>'_\<^sub>2\<close> 65)
    and uminus\<^sub>M\<^sub>_\<^sub>2 (\<open>-\<^sub>M\<^sub>'_\<^sub>2 _\<close> [81] 80)
    and scale\<^sub>2 :: "['cr1::comm_ring_1, 'm_2] \<Rightarrow> 'm_2" (infixr \<open>*s\<^sub>M\<^sub>'_\<^sub>2\<close> 75) +
  fixes f :: "'m_1 \<Rightarrow> 'm_2"
  assumes f_closed[simp]: "f ` U\<^sub>M\<^sub>_\<^sub>1 \<subseteq> U\<^sub>M\<^sub>_\<^sub>2" 
    and add: "\<lbrakk> b1 \<in> U\<^sub>M\<^sub>_\<^sub>1; b2 \<in> U\<^sub>M\<^sub>_\<^sub>1 \<rbrakk> \<Longrightarrow> f (b1 +\<^sub>M\<^sub>_\<^sub>1 b2) = f b1 +\<^sub>M\<^sub>_\<^sub>2 f b2"
    and scale: "\<lbrakk> r \<in> U\<^sub>C\<^sub>R\<^sub>1; b \<in> U\<^sub>M\<^sub>_\<^sub>1 \<rbrakk> \<Longrightarrow> f (r *s\<^sub>M\<^sub>_\<^sub>1 b) = r *s\<^sub>M\<^sub>_\<^sub>2 f b"
begin

tts_register_sbts f | \<open>U\<^sub>M\<^sub>_\<^sub>1\<close> and \<open>U\<^sub>M\<^sub>_\<^sub>2\<close> by (rule tts_AB_transfer[OF f_closed])

lemma f_closed'[simp]: "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2" using f_closed by blast

sublocale module_pair_ow ..

end


subsubsection\<open>Transfer.\<close>

lemma module_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique B" "right_total B"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B ===> B ===> B) ===>
        B ===>
        (B ===> B ===> B) ===>
        (B ===> B) ===>
        ((=) ===> B ===> B) ===>
        (=)
      )"
    and
      "lhs \<equiv> 
        (
          \<lambda> plus\<^sub>M zero\<^sub>M minus\<^sub>M uminus\<^sub>M scale.
          module_ow (Collect (Domainp B)) plus\<^sub>M zero\<^sub>M minus\<^sub>M uminus\<^sub>M scale
        )"
  shows "PP lhs (module_with)"
proof-
  let ?rhs = 
    "(
      \<lambda>plus\<^sub>M zero\<^sub>M minus\<^sub>M uminus\<^sub>M scale.
        (\<forall>a \<in> UNIV. \<forall>x \<in> UNIV. scale a x \<in> UNIV) \<and>
         module_with plus\<^sub>M zero\<^sub>M minus\<^sub>M uminus\<^sub>M scale
    )"
  have "PP lhs ?rhs"
    unfolding 
      PP_def lhs_def
      module_ow_def module_with_def
      module_ow_axioms_def module_with_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by (intro ext) blast
  then show ?thesis by simp
qed

lemma module_pair_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: 
    "bi_unique B\<^sub>1" "right_total B\<^sub>1" "bi_unique B\<^sub>2" "right_total B\<^sub>2"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        B\<^sub>1 ===>
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>1 ===> B\<^sub>1) ===>
        ((=) ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        B\<^sub>2 ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (B\<^sub>2 ===> B\<^sub>2) ===>
        ((=) ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (=)
    )"
    and
      "lhs \<equiv> 
        (
          \<lambda>
            plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1
            plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2.
          module_pair_ow 
            (Collect (Domainp B\<^sub>1)) plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1
            (Collect (Domainp B\<^sub>2)) plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
        )"
    shows "PP lhs module_pair_with"
  unfolding PP_def lhs_def
proof(intro rel_funI) 
  let ?rhs = 
    "(
      \<lambda>
        plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1
        plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2.
          (\<forall>a \<in> UNIV. \<forall>x \<in> UNIV. scale\<^sub>1 a x \<in> UNIV) \<and>
          (\<forall>a \<in> UNIV. \<forall>x \<in> UNIV. scale\<^sub>2 a x \<in> UNIV) \<and>
          module_pair_with 
            plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1
            plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
    )"
  fix 
    plus\<^sub>M\<^sub>_\<^sub>1 plus\<^sub>M\<^sub>_\<^sub>1' 
    zero\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1' 
    minus\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1' 
    uminus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1' 
    plus\<^sub>M\<^sub>_\<^sub>2 plus\<^sub>M\<^sub>_\<^sub>2' 
    zero\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2' 
    minus\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2' 
    uminus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2' 
    and scale\<^sub>1 :: "'f::comm_ring_1 \<Rightarrow> 'a \<Rightarrow> 'a" and scale\<^sub>1' 
    and scale\<^sub>2 :: "'f::comm_ring_1 \<Rightarrow> 'c \<Rightarrow> 'c" and scale\<^sub>2'
  assume [transfer_rule]: 
    "(B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) plus\<^sub>M\<^sub>_\<^sub>1 plus\<^sub>M\<^sub>_\<^sub>1'"
    "B\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1'"
    "(B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) minus\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1'"
    "(B\<^sub>1 ===> B\<^sub>1) uminus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1'"
    "(B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) plus\<^sub>M\<^sub>_\<^sub>2 plus\<^sub>M\<^sub>_\<^sub>2'"
    "B\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2'"
    "(B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) minus\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2'"
    "(B\<^sub>2 ===> B\<^sub>2) uminus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2'"
    "((=) ===> B\<^sub>1 ===> B\<^sub>1) scale\<^sub>1 scale\<^sub>1'"
    "((=) ===> B\<^sub>2 ===> B\<^sub>2) scale\<^sub>2 scale\<^sub>2'"
  show 
    "module_pair_ow 
      (Collect (Domainp B\<^sub>1)) plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 
      (Collect (Domainp B\<^sub>2)) plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
      =
    module_pair_with
      plus\<^sub>M\<^sub>_\<^sub>1' zero\<^sub>M\<^sub>_\<^sub>1' minus\<^sub>M\<^sub>_\<^sub>1' uminus\<^sub>M\<^sub>_\<^sub>1' scale\<^sub>1'
      plus\<^sub>M\<^sub>_\<^sub>2' zero\<^sub>M\<^sub>_\<^sub>2' minus\<^sub>M\<^sub>_\<^sub>2' uminus\<^sub>M\<^sub>_\<^sub>2' scale\<^sub>2'"
    unfolding module_pair_ow_def module_pair_with_def
    apply transfer_prover_start
    apply transfer_step+
    by simp
qed

lemma module_hom_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: 
    "bi_unique B\<^sub>1" "right_total B\<^sub>1" "bi_unique B\<^sub>2" "right_total B\<^sub>2"     
  fixes PP lhs
  defines
    "PP \<equiv> 
      (
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        B\<^sub>1 ===>
        (B\<^sub>1 ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>1 ===> B\<^sub>1) ===>
        ((=) ===> B\<^sub>1 ===> B\<^sub>1) ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        B\<^sub>2 ===>
        (B\<^sub>2 ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (B\<^sub>2 ===> B\<^sub>2) ===>
        ((=) ===> B\<^sub>2 ===> B\<^sub>2) ===>
        (B\<^sub>1 ===> B\<^sub>2) ===>
        (=)
      )"
    and
      "lhs \<equiv> 
        (
          \<lambda>
            plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1
            plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
            f.
          module_hom_ow 
            (Collect (Domainp B\<^sub>1)) plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1
            (Collect (Domainp B\<^sub>2)) plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
            f
        )"
    shows "PP lhs module_hom_with"
proof-
  let ?rhs = 
    "(
      \<lambda>
        plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1
        plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
        f. 
        (\<forall>x \<in> UNIV. f x \<in> UNIV) \<and>
        module_hom_with
          plus\<^sub>M\<^sub>_\<^sub>1 zero\<^sub>M\<^sub>_\<^sub>1 minus\<^sub>M\<^sub>_\<^sub>1 uminus\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1
          plus\<^sub>M\<^sub>_\<^sub>2 zero\<^sub>M\<^sub>_\<^sub>2 minus\<^sub>M\<^sub>_\<^sub>2 uminus\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
          f
    )"
  have "PP lhs ?rhs"
    unfolding 
      PP_def lhs_def 
      module_hom_ow_def module_hom_with_def
      module_hom_ow_axioms_def module_hom_with_axioms_def
    apply transfer_prover_start
    apply transfer_step+
    by (intro ext) blast
  then show ?thesis by simp
qed



subsection\<open>\<open>module_on\<close>\<close>


subsubsection\<open>Definitions and common properties\<close>

locale module_on =
  fixes U\<^sub>M
    and scale :: "'a::comm_ring_1 \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*s" 75)
  assumes scale_right_distrib_on[algebra_simps]: 
      "\<lbrakk> x \<in> U\<^sub>M; y \<in> U\<^sub>M \<rbrakk> \<Longrightarrow> a *s (x + y) = a *s x + a *s y"
    and scale_left_distrib_on[algebra_simps]: 
      "x \<in> U\<^sub>M \<Longrightarrow> (a + b) *s x = a *s x + b *s x"
    and scale_scale_on[simp]: "x \<in> U\<^sub>M \<Longrightarrow> a *s (b *s x) = (a * b) *s x"
    and scale_one_on[simp]: "x \<in> U\<^sub>M \<Longrightarrow> 1 *s x = x"
    and closed_add: "\<lbrakk> x \<in> U\<^sub>M; y \<in> U\<^sub>M \<rbrakk> \<Longrightarrow> x + y \<in> U\<^sub>M"
    and closed_zero: "0 \<in> U\<^sub>M"
    and closed_scale: "x \<in> U\<^sub>M \<Longrightarrow> a *s x \<in> U\<^sub>M"
begin

lemma S_ne: "U\<^sub>M \<noteq> {}" using closed_zero by auto

lemma scale_minus_left_on: 
  assumes "x \<in> U\<^sub>M" 
  shows "scale (- a) x = - scale a x" 
  by 
    (
      metis 
        add_cancel_right_right scale_left_distrib_on neg_eq_iff_add_eq_0 assms
    )

lemma closed_uminus: 
  assumes "x \<in> U\<^sub>M"
  shows "-x \<in> U\<^sub>M"
  by (metis assms closed_scale scale_minus_left_on scale_one_on)

sublocale implicit\<^sub>M: ab_group_add_ow U\<^sub>M \<open>(+)\<close> 0 \<open>(-)\<close> uminus
  by unfold_locales (simp_all add: closed_add closed_zero closed_uminus)

sublocale implicit\<^sub>M: module_ow U\<^sub>M \<open>(+)\<close> 0 \<open>(-)\<close> uminus \<open>(*s)\<close>
  by unfold_locales 
    (simp_all add: closed_scale scale_right_distrib_on scale_left_distrib_on)

definition subspace :: "'b set \<Rightarrow> bool"
  where subspace_on_def: "subspace T \<longleftrightarrow> 
    0 \<in> T \<and> (\<forall>x\<in>T. \<forall>y\<in>T. x + y \<in> T) \<and> (\<forall>c. \<forall>x\<in>T. c *s x \<in> T)"

definition span :: "'b set \<Rightarrow> 'b set"
  where span_on_def: "span b = {sum (\<lambda>a. r a *s  a) t | t r. finite t \<and> t \<subseteq> b}"

definition dependent :: "'b set \<Rightarrow> bool"
  where dependent_on_def: "dependent s \<longleftrightarrow> 
    (\<exists>t u. finite t \<and> t \<subseteq> s \<and> (sum (\<lambda>v. u v *s v) t = 0 \<and> (\<exists>v\<in>t. u v \<noteq> 0)))"

lemma implicit_subspace_with[tts_implicit]: "subspace.with (+) 0 (*s) = subspace"
  unfolding subspace_on_def subspace.with_def ..

lemma implicit_dependent_with[tts_implicit]: 
  "dependent.with 0 0 (+) (*s) = dependent"
  unfolding dependent_on_def dependent.with_def sum_with ..

lemma implicit_span_with[tts_implicit]: "span.with 0 (+) (*s) = span"
  unfolding span_on_def span.with_def sum_with ..

end

lemma implicit_module_ow[tts_implicit]:
  "module_ow U\<^sub>M (+) 0 (-) uminus = module_on U\<^sub>M"
proof (intro ext iffI)
  fix s::"'a\<Rightarrow>'b\<Rightarrow>'b" assume "module_on U\<^sub>M s"
  then interpret module_on U\<^sub>M s .
  show "module_ow U\<^sub>M (+) 0 (-) uminus s" 
    by (simp add: implicit\<^sub>M.module_ow_axioms)
next
  fix s::"'a\<Rightarrow>'b\<Rightarrow>'b" assume "module_ow U\<^sub>M (+) 0 (-) uminus s"
  then interpret module_ow U\<^sub>M \<open>(+)\<close> 0 \<open>(-)\<close> uminus s .
  show "module_on U\<^sub>M s" 
    by (simp add: scale_left_distrib scale_right_distrib module_on.intro)
qed

locale module_pair_on = 
  M\<^sub>1: module_on U\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 + M\<^sub>2: module_on U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
  for U\<^sub>M\<^sub>_\<^sub>1:: "'b::ab_group_add set" 
    and U\<^sub>M\<^sub>_\<^sub>2::"'c::ab_group_add set"
    and scale\<^sub>1::"'a::comm_ring_1 \<Rightarrow> _ \<Rightarrow> _" (infixr \<open>*s\<^sub>1\<close> 75)
    and scale\<^sub>2::"'a::comm_ring_1 \<Rightarrow> _ \<Rightarrow> _" (infixr \<open>*s\<^sub>2\<close> 75)
begin

sublocale implicit\<^sub>M: module_pair_ow 
  U\<^sub>M\<^sub>_\<^sub>1 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>2
  by unfold_locales

end

lemma implicit_module_pair_ow[tts_implicit]:
  "module_pair_ow U\<^sub>M\<^sub>_\<^sub>1 (+) 0 (-) uminus scale\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (+) 0 (-) uminus scale\<^sub>2 = 
    module_pair_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2"
  unfolding module_pair_ow_def implicit_module_ow module_pair_on_def ..

locale module_hom_on = M\<^sub>1: module_on U\<^sub>M\<^sub>_\<^sub>1 scale\<^sub>1 + M\<^sub>2: module_on U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>2
  for U\<^sub>M\<^sub>_\<^sub>1 :: "'b::ab_group_add set" and U\<^sub>M\<^sub>_\<^sub>2 :: "'c::ab_group_add set"
    and scale\<^sub>1 :: "'a::comm_ring_1 \<Rightarrow> 'b \<Rightarrow> 'b" (infixr \<open>*s\<^sub>1\<close> 75)
    and scale\<^sub>2 :: "'a::comm_ring_1 \<Rightarrow> 'c \<Rightarrow> 'c" (infixr \<open>*s\<^sub>2\<close> 75) +
  fixes f :: "'b \<Rightarrow> 'c"
  assumes hom_closed: "f ` U\<^sub>M\<^sub>_\<^sub>1 \<subseteq> U\<^sub>M\<^sub>_\<^sub>2"
    and add: "\<And>b1 b2. \<lbrakk> b1 \<in> U\<^sub>M\<^sub>_\<^sub>1; b2 \<in> U\<^sub>M\<^sub>_\<^sub>1 \<rbrakk> \<Longrightarrow> f (b1 + b2) = f b1 + f b2"
    and scale: "\<And>b. b \<in> U\<^sub>M\<^sub>_\<^sub>1 \<Longrightarrow> f (r *s\<^sub>1 b) = r *s\<^sub>2 f b"
begin

sublocale module_pair_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2 by unfold_locales

sublocale implicit\<^sub>M: module_hom_ow 
  U\<^sub>M\<^sub>_\<^sub>1 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 \<open>(+)\<close> 0 \<open>(-)\<close> uminus scale\<^sub>2
  by unfold_locales (simp_all add: hom_closed add scale)
 
end

lemma implicit_module_hom_ow[tts_implicit]:
  "module_hom_ow U\<^sub>M\<^sub>_\<^sub>1 (+) 0 (-) uminus scale\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (+) 0 (-) uminus scale\<^sub>2 = 
    module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 scale\<^sub>1 scale\<^sub>2"
  unfolding 
    module_hom_ow_def 
    module_hom_on_def 
    module_hom_ow_axioms_def
    module_hom_on_axioms_def
    tts_implicit
  by (intro ext) auto



subsection\<open>Relativization.\<close>

context module_on
begin

tts_context
  tts: (?'b to \<open>U\<^sub>M::'b set\<close>)
  rewriting ctr_simps
  substituting implicit\<^sub>M.module_ow_axioms
    and implicit\<^sub>M.ab_group_add_ow_axioms
  eliminating \<open>?a \<in> U\<^sub>M\<close> and \<open>?B \<subseteq> U\<^sub>M\<close> through auto
  applying 
    [
      OF 
        implicit\<^sub>M.carrier_ne 
        implicit\<^sub>M.add_closed' 
        implicit\<^sub>M.minus_closed' 
        implicit\<^sub>M.uminus_closed' 
        implicit\<^sub>M.scale_closed',
      unfolded tts_implicit
    ]
begin

tts_lemma scale_left_commute:
  assumes "x \<in> U\<^sub>M"
  shows "a *s b *s x = b *s a *s x"
    is module.scale_left_commute.

tts_lemma scale_zero_left:
  assumes "x \<in> U\<^sub>M"
  shows "0 *s x = 0"
    is module.scale_zero_left.
    
tts_lemma scale_minus_left:
  assumes "x \<in> U\<^sub>M"
  shows "- a *s x = - (a *s x)"
    is module.scale_minus_left.

tts_lemma scale_left_diff_distrib:
  assumes "x \<in> U\<^sub>M"
  shows "(a - b) *s x = a *s x - b *s x"
    is module.scale_left_diff_distrib.

tts_lemma scale_sum_left:
  assumes "x \<in> U\<^sub>M"
  shows "sum f A *s x = (\<Sum>a\<in>A. f a *s x)"
    is module.scale_sum_left.

tts_lemma scale_zero_right: "a *s 0 = 0"
    is module.scale_zero_right.
    
tts_lemma scale_minus_right:
  assumes "x \<in> U\<^sub>M"
  shows "a *s - x = - (a *s x)"
    is module.scale_minus_right.
    
tts_lemma scale_right_diff_distrib:
  assumes "x \<in> U\<^sub>M" and "y \<in> U\<^sub>M"
  shows "a *s (x - y) = a *s x - a *s y"
    is module.scale_right_diff_distrib.

tts_lemma scale_sum_right:
  assumes "range f \<subseteq> U\<^sub>M"
  shows "a *s sum f A = (\<Sum>x\<in>A. a *s f x)"
    is module.scale_sum_right.

tts_lemma sum_constant_scale:
  assumes "y \<in> U\<^sub>M"
  shows "(\<Sum>x\<in>A. y) = of_nat (card A) *s y"
    is module.sum_constant_scale.

tts_lemma subspace_def:
  assumes "S \<subseteq> U\<^sub>M"
  shows "subspace S =
    (0 \<in> S \<and> (\<forall>x. \<forall>y\<in>S. x *s y \<in> S) \<and> (\<forall>x\<in>S. \<forall>y\<in>S. x + y \<in> S))"
    is module.subspace_def.

tts_lemma subspaceI:
  assumes "S \<subseteq> U\<^sub>M"
    and "0 \<in> S"
    and "\<And>x y. \<lbrakk>x \<in> U\<^sub>M; y \<in> U\<^sub>M; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> x + y \<in> S"
    and "\<And>c x. \<lbrakk>x \<in> U\<^sub>M; x \<in> S\<rbrakk> \<Longrightarrow> c *s x \<in> S"
  shows "subspace S"
    is module.subspaceI.

tts_lemma subspace_single_0: "subspace {0}"
    is module.subspace_single_0.

tts_lemma subspace_0:
  assumes "S \<subseteq> U\<^sub>M" and "subspace S"
  shows "0 \<in> S"
    is module.subspace_0.

tts_lemma subspace_add:
  assumes "S \<subseteq> U\<^sub>M" and "subspace S" and "x \<in> S" and "y \<in> S"
  shows "x + y \<in> S"
    is module.subspace_add.

tts_lemma subspace_scale:
  assumes "S \<subseteq> U\<^sub>M" and "subspace S" and "x \<in> S"
  shows "c *s x \<in> S"
    is module.subspace_scale.

tts_lemma subspace_neg:
  assumes "S \<subseteq> U\<^sub>M" and "subspace S" and "x \<in> S"
  shows "- x \<in> S"
    is module.subspace_neg.

tts_lemma subspace_diff:
  assumes "S \<subseteq> U\<^sub>M" and "subspace S" and "x \<in> S" and "y \<in> S"
  shows "x - y \<in> S"
    is module.subspace_diff.

tts_lemma subspace_sum:
  assumes "A \<subseteq> U\<^sub>M"
    and "range f \<subseteq> U\<^sub>M"
    and "subspace A"
    and "\<And>x. x \<in> B \<Longrightarrow> f x \<in> A"
  shows "sum f B \<in> A"
    is module.subspace_sum.

tts_lemma subspace_inter:
  assumes "A \<subseteq> U\<^sub>M" and "B \<subseteq> U\<^sub>M" and "subspace A" and "subspace B"
  shows "subspace (A \<inter> B)"
    is module.subspace_inter.

tts_lemma span_explicit':
  assumes "b \<subseteq> U\<^sub>M"
  shows "span b = 
    {
      x \<in> U\<^sub>M. \<exists>f. 
        x = (\<Sum>v\<in>{x \<in> U\<^sub>M. f x \<noteq> 0}. f v *s v) \<and> 
        finite {x \<in> U\<^sub>M. f x \<noteq> 0} \<and> 
        (\<forall>x\<in>U\<^sub>M. f x \<noteq> 0 \<longrightarrow> x \<in> b)
    }"
   is module.span_explicit'.

tts_lemma span_finite:
  assumes "S \<subseteq> U\<^sub>M" and "finite S"
  shows "span S = range (\<lambda>u. \<Sum>v\<in>S. u v *s v)"
    is module.span_finite.

tts_lemma span_induct_alt:
  assumes "x \<in> U\<^sub>M"
    and "S \<subseteq> U\<^sub>M"
    and "x \<in> span S"
    and "h 0"
    and "\<And>c x y. \<lbrakk>x \<in> U\<^sub>M; y \<in> U\<^sub>M; x \<in> S; h y\<rbrakk> \<Longrightarrow> h (c *s x + y)"
  shows "h x"
    is module.span_induct_alt.

tts_lemma span_mono:
  assumes "B \<subseteq> U\<^sub>M" and "A \<subseteq> B"
  shows "span A \<subseteq> span B"
    is module.span_mono.

tts_lemma span_base:
  assumes "S \<subseteq> U\<^sub>M" and "a \<in> S"
  shows "a \<in> span S"
    is module.span_base.

tts_lemma span_superset:
  assumes "S \<subseteq> U\<^sub>M"
  shows "S \<subseteq> span S"
    is module.span_superset.

tts_lemma span_zero:
  assumes "S \<subseteq> U\<^sub>M"
  shows "0 \<in> span S"
    is module.span_zero.

tts_lemma span_add:
  assumes "x \<in> U\<^sub>M"
    and "S \<subseteq> U\<^sub>M"
    and "y \<in> U\<^sub>M"
    and "x \<in> span S"
    and "y \<in> span S"
  shows "x + y \<in> span S"
    is module.span_add.

tts_lemma span_scale:
  assumes "x \<in> U\<^sub>M" and "S \<subseteq> U\<^sub>M" and "x \<in> span S"
  shows "c *s x \<in> span S"
    is module.span_scale.

tts_lemma subspace_span:
  assumes "S \<subseteq> U\<^sub>M"
  shows "subspace (span S)"
    is module.subspace_span.

tts_lemma span_neg:
  assumes "x \<in> U\<^sub>M" and "S \<subseteq> U\<^sub>M" and "x \<in> span S"
  shows "- x \<in> span S"
    is module.span_neg.

tts_lemma span_diff:
  assumes "x \<in> U\<^sub>M"
    and "S \<subseteq> U\<^sub>M"
    and "y \<in> U\<^sub>M"
    and "x \<in> span S"
    and "y \<in> span S"
  shows "x - y \<in> span S"
    is module.span_diff.

tts_lemma span_sum:
  assumes "range f \<subseteq> U\<^sub>M" and "S \<subseteq> U\<^sub>M" and "\<And>x. x \<in> A \<Longrightarrow> f x \<in> span S"
  shows "sum f A \<in> span S"
    is module.span_sum.

tts_lemma span_minimal:
  assumes "T \<subseteq> U\<^sub>M" and "S \<subseteq> T" and "subspace T"
  shows "span S \<subseteq> T"
    is module.span_minimal.

tts_lemma span_subspace_induct:
  assumes "x \<in> U\<^sub>M"
    and "S \<subseteq> U\<^sub>M"
    and "P \<subseteq> U\<^sub>M"
    and "x \<in> span S"
    and "subspace P"
    and "\<And>x. x \<in> S \<Longrightarrow> x \<in> P"
  shows "x \<in> P"
    given module.span_subspace_induct 
    by simp

tts_lemma span_induct:
  assumes "x \<in> U\<^sub>M"
    and "S \<subseteq> U\<^sub>M"
    and "x \<in> span S"
    and "subspace {x. P x \<and> x \<in> U\<^sub>M}"
    and "\<And>x. x \<in> S \<Longrightarrow> P x"
  shows "P x"
    given module.span_induct by blast

tts_lemma span_empty: "span {} = {0}"
    is module.span_empty.

tts_lemma span_subspace:
  assumes "B \<subseteq> U\<^sub>M" and "A \<subseteq> B" and "B \<subseteq> span A" and "subspace B"
  shows "span A = B"
    is module.span_subspace.

tts_lemma span_span:
  assumes "A \<subseteq> U\<^sub>M"
  shows "span (span A) = span A"
    is module.span_span.

tts_lemma span_add_eq:
  assumes "x \<in> U\<^sub>M" and "S \<subseteq> U\<^sub>M" and "y \<in> U\<^sub>M" and "x \<in> span S"
  shows "(x + y \<in> span S) = (y \<in> span S)"
    is module.span_add_eq.

tts_lemma span_add_eq2:
  assumes "y \<in> U\<^sub>M" and "S \<subseteq> U\<^sub>M" and "x \<in> U\<^sub>M" and "y \<in> span S"
  shows "(x + y \<in> span S) = (x \<in> span S)"
    is module.span_add_eq2.

tts_lemma span_singleton:
  assumes "x \<in> U\<^sub>M"
  shows "span {x} = range (\<lambda>k. k *s x)"
    is module.span_singleton.

tts_lemma span_Un:
  assumes "S \<subseteq> U\<^sub>M" and "T \<subseteq> U\<^sub>M"
  shows "span (S \<union> T) = 
    {x \<in> U\<^sub>M. \<exists>a\<in>U\<^sub>M. \<exists>b\<in>U\<^sub>M. x = a + b \<and> a \<in> span S \<and> b \<in> span T}"
    is module.span_Un.

tts_lemma span_insert:
  assumes "a \<in> U\<^sub>M" and "S \<subseteq> U\<^sub>M"
  shows "span (insert a S) = {x \<in> U\<^sub>M. \<exists>y. x - y *s a \<in> span S}"
    is module.span_insert.

tts_lemma span_breakdown:
  assumes "S \<subseteq> U\<^sub>M" and "a \<in> U\<^sub>M" and "b \<in> S" and "a \<in> span S"
  shows "\<exists>x. a - x *s b \<in> span (S - {b})"
    is module.span_breakdown.

tts_lemma span_breakdown_eq:
  assumes "x \<in> U\<^sub>M" and "a \<in> U\<^sub>M" and "S \<subseteq> U\<^sub>M"
  shows "(x \<in> span (insert a S)) = (\<exists>y. x - y *s a \<in> span S)"
    is module.span_breakdown_eq.

tts_lemma span_clauses:
  "\<lbrakk>S \<subseteq> U\<^sub>M; a \<in> S\<rbrakk> \<Longrightarrow> a \<in> span S"
  "S \<subseteq> U\<^sub>M \<Longrightarrow> 0 \<in> span S"
  "\<lbrakk>x \<in> U\<^sub>M; S \<subseteq> U\<^sub>M; y \<in> U\<^sub>M; x \<in> span S; y \<in> span S\<rbrakk> \<Longrightarrow> x + y \<in> span S"
  "\<lbrakk>x \<in> U\<^sub>M; S \<subseteq> U\<^sub>M; x \<in> span S\<rbrakk> \<Longrightarrow> c *s x \<in> span S"
  is module.span_clauses.

tts_lemma span_eq_iff:
  assumes "s \<subseteq> U\<^sub>M"
  shows "(span s = s) = subspace s"
    is module.span_eq_iff.

tts_lemma span_eq:
  assumes "S \<subseteq> U\<^sub>M" and "T \<subseteq> U\<^sub>M"
  shows "(span S = span T) = (S \<subseteq> span T \<and> T \<subseteq> span S)"
    is module.span_eq.

tts_lemma eq_span_insert_eq:
  assumes "x \<in> U\<^sub>M" and "y \<in> U\<^sub>M" and "S \<subseteq> U\<^sub>M" and "x - y \<in> span S"
  shows "span (insert x S) = span (insert y S)"
    is module.eq_span_insert_eq.

tts_lemma dependent_mono:
  assumes "A \<subseteq> U\<^sub>M" and "dependent B" and "B \<subseteq> A"
  shows "dependent A"
    is module.dependent_mono.

tts_lemma independent_mono:
  assumes "A \<subseteq> U\<^sub>M" and "\<not> dependent A" and "B \<subseteq> A"
  shows "\<not> dependent B"
    is module.independent_mono.

tts_lemma dependent_zero:
  assumes "A \<subseteq> U\<^sub>M" and "0 \<in> A"
  shows "dependent A"
    is module.dependent_zero.

tts_lemma independent_empty: "\<not> dependent {}"
    is module.independent_empty.

tts_lemma independentD:
  assumes "s \<subseteq> U\<^sub>M"
    and "\<not> dependent s"
    and "finite t"
    and "t \<subseteq> s"
    and "(\<Sum>v\<in>t. u v *s v) = 0"
    and "v \<in> t"
  shows "u v = 0"
    is module.independentD.

tts_lemma independent_Union_directed:
  assumes "C \<subseteq> Pow U\<^sub>M"
    and "\<And>c d. \<lbrakk>c \<subseteq> U\<^sub>M; d \<subseteq> U\<^sub>M; c \<in> C; d \<in> C\<rbrakk> \<Longrightarrow> c \<subseteq> d \<or> d \<subseteq> c"
    and "\<And>c. \<lbrakk>c \<subseteq> U\<^sub>M; c \<in> C\<rbrakk> \<Longrightarrow> \<not> dependent c"
  shows "\<not> dependent (\<Union> C)"
    is module.independent_Union_directed.

tts_lemma dependent_finite:
  assumes "S \<subseteq> U\<^sub>M" and "finite S"
  shows "dependent S = (\<exists>x. (\<exists>y\<in>S. x y \<noteq> 0) \<and> (\<Sum>v\<in>S. x v *s v) = 0)"
    is module.dependent_finite.

tts_lemma independentD_alt:
  assumes "B \<subseteq> U\<^sub>M"
    and "x \<in> U\<^sub>M"
    and "\<not> dependent B"
    and "finite {x \<in> U\<^sub>M. X x \<noteq> 0}"
    and "{x \<in> U\<^sub>M. X x \<noteq> 0} \<subseteq> B"
    and "(\<Sum>x | x \<in> U\<^sub>M \<and> X x \<noteq> 0. X x *s x) = 0"
  shows "X x = 0"
    is module.independentD_alt.

tts_lemma spanning_subset_independent:
  assumes "A \<subseteq> U\<^sub>M" and "B \<subseteq> A" and "\<not> dependent A" and "A \<subseteq> span B"
  shows "A = B"
    is module.spanning_subset_independent.

tts_lemma unique_representation:
  assumes "basis \<subseteq> U\<^sub>M"
    and "\<not> dependent basis"
    and "\<And>v. \<lbrakk>v \<in> U\<^sub>M; f v \<noteq> 0\<rbrakk> \<Longrightarrow> v \<in> basis"
    and "\<And>v. \<lbrakk>v \<in> U\<^sub>M; g v \<noteq> 0\<rbrakk> \<Longrightarrow> v \<in> basis"
    and "finite {x \<in> U\<^sub>M. f x \<noteq> 0}"
    and "finite {x \<in> U\<^sub>M. g x \<noteq> 0}"
    and 
      "(\<Sum>v\<in>{x \<in> U\<^sub>M. f x \<noteq> 0}. f v *s v) = (\<Sum>v\<in>{x \<in> U\<^sub>M. g x \<noteq> 0}. g v *s v)"
  shows "\<forall>x\<in>U\<^sub>M. f x = g x"
    is module.unique_representation[unfolded fun_eq_iff].

tts_lemma independentD_unique:
  assumes "B \<subseteq> U\<^sub>M"
    and "\<not> dependent B"
    and "finite {x \<in> U\<^sub>M. X x \<noteq> 0}"
    and "{x \<in> U\<^sub>M. X x \<noteq> 0} \<subseteq> B"
    and "finite {x \<in> U\<^sub>M. Y x \<noteq> 0}"
    and "{x \<in> U\<^sub>M. Y x \<noteq> 0} \<subseteq> B"
    and "(\<Sum>x | x \<in> U\<^sub>M \<and> X x \<noteq> 0. X x *s x) = 
      (\<Sum>x | x \<in> U\<^sub>M \<and> Y x \<noteq> 0. Y x *s x)"
  shows "\<forall>x\<in>U\<^sub>M. X x = Y x"
    is module.independentD_unique[unfolded fun_eq_iff].

tts_lemma subspace_UNIV: "subspace U\<^sub>M"
  is module.subspace_UNIV.

tts_lemma span_UNIV: "span U\<^sub>M = U\<^sub>M"
  is module.span_UNIV.

tts_lemma span_alt:
  assumes "B \<subseteq> U\<^sub>M"
  shows 
    "span B = 
      {
        x \<in> U\<^sub>M. \<exists>f. 
          x = (\<Sum>x | x \<in> U\<^sub>M \<and> f x \<noteq> 0. f x *s x) \<and> 
          finite {x \<in> U\<^sub>M. f x \<noteq> 0} \<and> 
          {x \<in> U\<^sub>M. f x \<noteq> 0} \<subseteq> B
      }"
    is module.span_alt.

tts_lemma dependent_alt:
  assumes "B \<subseteq> U\<^sub>M"
  shows "dependent B = 
    (
      \<exists>f. 
        finite {v \<in> U\<^sub>M. f v \<noteq> 0} \<and> 
        {v \<in> U\<^sub>M. f v \<noteq> 0} \<subseteq> B \<and> 
        (\<exists>v\<in>U\<^sub>M. f v \<noteq> 0) \<and> 
        (\<Sum>x | x \<in> U\<^sub>M \<and> f x \<noteq> 0. f x *s x) = 0
    )"
    is module.dependent_alt.

tts_lemma independent_alt:
  assumes "B \<subseteq> U\<^sub>M"
  shows 
    "(\<not> dependent B) = 
      (
        \<forall>f. 
          finite {x \<in> U\<^sub>M. f x \<noteq> 0} \<longrightarrow> 
          {x \<in> U\<^sub>M. f x \<noteq> 0} \<subseteq> B \<longrightarrow> 
          (\<Sum>x | x \<in> U\<^sub>M \<and> f x \<noteq> 0. f x *s x) = 0 \<longrightarrow> 
          (\<forall>x\<in>U\<^sub>M. f x = 0)
    )"
    is module.independent_alt.

tts_lemma subspace_Int:
  assumes "range s \<subseteq> Pow U\<^sub>M" and "\<And>i. i \<in> I \<Longrightarrow> subspace (s i)"
  shows "subspace (\<Inter> (s ` I) \<inter> U\<^sub>M)"
    is module.subspace_Int.

tts_lemma subspace_Inter:
  assumes "f \<subseteq> Pow U\<^sub>M" and "Ball f subspace"
  shows "subspace (\<Inter> f \<inter> U\<^sub>M)"
    is module.subspace_Inter.

tts_lemma module_hom_scale_self: "module_hom_on U\<^sub>M U\<^sub>M (*s) (*s) ((*s) c)"
  is module.module_hom_scale_self.

tts_lemma module_hom_scale_left:
  assumes "x \<in> U\<^sub>M"
  shows "module_hom_on UNIV U\<^sub>M (*) (*s) (\<lambda>r. r *s x)"
  is module.module_hom_scale_left.

tts_lemma module_hom_id: "module_hom_on U\<^sub>M U\<^sub>M (*s) (*s) id"
  is module.module_hom_id.

tts_lemma module_hom_ident: "module_hom_on U\<^sub>M U\<^sub>M (*s) (*s) (\<lambda>x. x)"
  is module.module_hom_ident.

tts_lemma module_hom_uminus: "module_hom_on U\<^sub>M U\<^sub>M (*s) (*s) uminus"
  is module.module_hom_uminus.

end

tts_context
  tts: (?'b to \<open>U\<^sub>M::'b set\<close>)
  rewriting ctr_simps
  substituting implicit\<^sub>M.module_ow_axioms
    and implicit\<^sub>M.ab_group_add_ow_axioms
  eliminating \<open>?a \<in> U\<^sub>M\<close> and \<open>?B \<subseteq> U\<^sub>M\<close> through clarsimp
  applying 
    [
      OF 
        implicit\<^sub>M.carrier_ne
        implicit\<^sub>M.add_closed' 
        implicit\<^sub>M.minus_closed' 
        implicit\<^sub>M.uminus_closed' 
        implicit\<^sub>M.scale_closed',
      unfolded tts_implicit
    ]
begin

tts_lemma span_explicit:
  assumes "b \<subseteq> U\<^sub>M"
  shows "span b = 
    {x \<in> U\<^sub>M. \<exists>y\<subseteq>U\<^sub>M. \<exists>f. (finite y \<and> y \<subseteq> b) \<and> x = (\<Sum>a\<in>y. f a *s a)}"
  given module.span_explicit by auto
    
tts_lemma span_unique:
  assumes "S \<subseteq> U\<^sub>M"
    and "T \<subseteq> U\<^sub>M"
    and "S \<subseteq> T"
    and "subspace T"
    and "\<And>T'. \<lbrakk>T' \<subseteq> U\<^sub>M; S \<subseteq> T'; subspace T'\<rbrakk> \<Longrightarrow> T \<subseteq> T'"
  shows "span S = T"
    is module.span_unique.
    
tts_lemma dependent_explicit:
  assumes "V \<subseteq> U\<^sub>M"
  shows "dependent V = 
    (\<exists>U\<subseteq>U\<^sub>M. \<exists>f. finite U \<and> U \<subseteq> V \<and> (\<exists>v\<in>U. f v \<noteq> 0) \<and> (\<Sum>v\<in>U. f v *s v) = 0)"
    given module.dependent_explicit by auto

tts_lemma independent_explicit_module:
  assumes "V \<subseteq> U\<^sub>M"
  shows "(\<not> dependent V) = 
    (
      \<forall>U\<subseteq>U\<^sub>M. \<forall>f. \<forall>v\<in>U\<^sub>M. 
        finite U \<longrightarrow> 
        U \<subseteq> V \<longrightarrow> 
        (\<Sum>u\<in>U. f u *s u) = 0 \<longrightarrow> 
        v \<in> U \<longrightarrow> 
        f v = 0
    )"
    given module.independent_explicit_module by auto

end

end

context module_pair_on 
begin

tts_context
  tts: (?'b to \<open>U\<^sub>M\<^sub>_\<^sub>1::'b set\<close>) and (?'c to \<open>U\<^sub>M\<^sub>_\<^sub>2::'c set\<close>)
  rewriting ctr_simps
  substituting M\<^sub>1.implicit\<^sub>M.module_ow_axioms
    and M\<^sub>2.implicit\<^sub>M.module_ow_axioms
    and M\<^sub>1.implicit\<^sub>M.ab_group_add_ow_axioms
    and M\<^sub>2.implicit\<^sub>M.ab_group_add_ow_axioms
    and implicit\<^sub>M.module_pair_ow_axioms
  eliminating through auto
  applying [unfolded tts_implicit]
begin

tts_lemma module_hom_zero: "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. 0)"
    is module_pair.module_hom_zero.

tts_lemma module_hom_add:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. g x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) g"
  shows "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. f x + g x)"
    is module_pair.module_hom_add.
    
tts_lemma module_hom_sub:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. g x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) g"
  shows "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. f x - g x)"
    is module_pair.module_hom_sub.
    
tts_lemma module_hom_neg:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2" and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. - f x)"
    is module_pair.module_hom_neg.
  
tts_lemma module_hom_scale:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2" and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
  shows "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. c *s\<^sub>2 f x)"
    is module_pair.module_hom_scale.
    
tts_lemma module_hom_compose_scale:
  assumes "c \<in> U\<^sub>M\<^sub>_\<^sub>2" and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 UNIV (*s\<^sub>1) (*) f"
  shows "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. f x *s\<^sub>2 c)"
    is module_pair.module_hom_compose_scale.
    
tts_lemma module_hom_sum:
  assumes "\<forall>u. \<forall>v\<in>U\<^sub>M\<^sub>_\<^sub>1. f u v \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<And>i. i \<in> I \<Longrightarrow> module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (f i)"
    and "I = {} \<Longrightarrow> module_on U\<^sub>M\<^sub>_\<^sub>1 (*s\<^sub>1) \<and> module_on U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>2)"
  shows "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) (\<lambda>x. \<Sum>i\<in>I. f i x)"
  is module_pair.module_hom_sum.

tts_lemma module_hom_eq_on_span:
  assumes "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. f x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "\<forall>x\<in>U\<^sub>M\<^sub>_\<^sub>1. g x \<in> U\<^sub>M\<^sub>_\<^sub>2"
    and "B \<subseteq> U\<^sub>M\<^sub>_\<^sub>1"
    and "x \<in> U\<^sub>M\<^sub>_\<^sub>1"
    and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) f"
    and "module_hom_on U\<^sub>M\<^sub>_\<^sub>1 U\<^sub>M\<^sub>_\<^sub>2 (*s\<^sub>1) (*s\<^sub>2) g"
    and "\<And>x. \<lbrakk>x \<in> U\<^sub>M\<^sub>_\<^sub>1; x \<in> B\<rbrakk> \<Longrightarrow> f x = g x"
    and "x \<in> M\<^sub>1.span B"
  shows "f x = g x"
    is module_pair.module_hom_eq_on_span.

end

end

text\<open>\newpage\<close>

end