(* Title: ETTS/ETTS_Auxiliary.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

Auxiliary functionality for the ETTS.
*)

section\<open>Auxiliary functionality and helpful lemmas for Types-To-Sets\<close>
theory ETTS_Auxiliary
  imports ETTS
begin



subsection\<open>Further transfer rules\<close>

lemma Domainp_eq[transfer_domain_rule, transfer_rule]: 
  "Domainp (=) = (\<lambda>x. x \<in> UNIV)"
  by auto

lemma Domainp_rel_prod[transfer_domain_rule, transfer_rule]:
  assumes "Domainp cr\<^sub>1 = (\<lambda>x. x \<in> \<UU>\<^sub>1)" and "Domainp cr\<^sub>2 = (\<lambda>x. x \<in> \<UU>\<^sub>2)"
  shows "Domainp (rel_prod cr\<^sub>1 cr\<^sub>2) = (\<lambda>x. x \<in> \<UU>\<^sub>1 \<times> \<UU>\<^sub>2)"
  using assms by (simp add: ctr_simps_pred_prod_eq_cart prod.Domainp_rel)



subsection\<open>Constant function\<close>

definition const_fun :: "['b, 'a] \<Rightarrow> 'b" where "const_fun c = (\<lambda>x. c)"

lemma const_fun_transfer[transfer_rule]:
  includes lifting_syntax
  assumes "Domainp A = (\<lambda>x. x \<in> \<UU>A)" and "\<forall>x \<in> \<UU>A. f x = c" and "B c c'"
  shows "(A ===> B) f (const_fun c')"
proof(intro rel_funI)
  fix x y assume "A x y"
  then have "x \<in> \<UU>A" by (meson Domainp.DomainI assms(1))
  then have "f x = c" by (rule assms(2)[rule_format])
  show "B (f x) (const_fun c' y)" 
    unfolding \<open>f x = c\<close> const_fun_def by (rule assms(3))
qed



subsection\<open>Transfer rules suitable for instantiation\<close>

lemma Domainp_eq_Collect: "Domainp A = (\<lambda>x. x \<in> \<UU>) = (\<UU> = Collect (Domainp A))"
  by (metis mem_Collect_eq pred_equals_eq)

context
  includes lifting_syntax
begin

lemma tts_rel_set_transfer:
  fixes A :: "'al \<Rightarrow> 'ar \<Rightarrow> bool"
    and B :: "'bl \<Rightarrow> 'br \<Rightarrow> bool"
  assumes "S \<subseteq> Collect (Domainp A)" 
  shows "\<exists>S'. rel_set A S S'"
  by (metis assms(1)[folded Ball_Collect] DomainpE Domainp_set)

lemma tts_AB_transfer:
  fixes f :: "'al \<Rightarrow> 'bl"
    and A :: "'al \<Rightarrow> 'ar \<Rightarrow> bool"
    and B :: "'bl \<Rightarrow> 'br \<Rightarrow> bool"
  assumes closed: "f ` \<UU>A \<subseteq> \<UU>B"
  assumes 
    "Domainp A = (\<lambda>x. x \<in> \<UU>A)" "bi_unique A" "right_total A" 
    "Domainp B = (\<lambda>x. x \<in> \<UU>B)" "bi_unique B" "right_total B" 
  shows "\<exists>rcdt. (A ===> B) f rcdt"
proof-
  from closed have closed': "x \<in> \<UU>A \<Longrightarrow> f x \<in> \<UU>B" for x by auto
  from assms(3,4) obtain Rep_a :: "'ar \<Rightarrow> 'al" and Abs_a :: "'al \<Rightarrow> 'ar" 
    where td_a: "type_definition Rep_a Abs_a (Collect (Domainp A))"
      and A_Rep: "A b b' = (b = Rep_a b')" for b b'
    by (blast dest: ex_type_definition)
  from assms(6,7) obtain Rep_b :: "'br \<Rightarrow> 'bl" and Abs_b :: "'bl \<Rightarrow> 'br" 
    where td_b: "type_definition Rep_b Abs_b (Collect (Domainp B))"
      and B_Rep: "B b b' = (b = Rep_b b')" for b b'
    by (blast dest: ex_type_definition)
  define f' where f': "f' = (Rep_a ---> Abs_b) f"  
  have f_closed: "f (Rep_a a) \<in> \<UU>B" for a 
    using td_a td_b by (intro closed') (simp add: assms(2,5))+
  have rep_abs_b: "y \<in> \<UU>B \<Longrightarrow> y = Rep_b (Abs_b y)" for y
    using td_b unfolding type_definition_def by (simp add: assms(5))
  have "(A ===> B) f f'"
    unfolding f' map_fun_apply
    by 
      (
        intro rel_funI, 
        unfold A_Rep B_Rep,
        elim ssubst, 
        intro rep_abs_b f_closed
      )
  then show ?thesis by auto
qed

lemma tts_AB_transfer':
  fixes f' :: "'ar \<Rightarrow> 'br"
    and A :: "'al \<Rightarrow> 'ar \<Rightarrow> bool"
    and B :: "'bl \<Rightarrow> 'br \<Rightarrow> bool"
  assumes 
    "Domainp A = (\<lambda>x. x \<in> \<UU>A)" "bi_unique A" "right_total A" 
    "Domainp B = (\<lambda>x. x \<in> \<UU>B)" "bi_unique B" "right_total B" 
  shows "\<exists>f. (A ===> B) f f'"
proof-
  from assms(2,3) obtain Rep_a :: "'ar \<Rightarrow> 'al" and Abs_a :: "'al \<Rightarrow> 'ar" 
    where td_a: "type_definition Rep_a Abs_a (Collect (Domainp A))"
      and A_Rep: "A b b' = (b = Rep_a b')" for b b'
    by (blast dest: ex_type_definition)
  from assms(5,6) obtain Rep_b :: "'br \<Rightarrow> 'bl" and Abs_b :: "'bl \<Rightarrow> 'br" 
    where td_b: "type_definition Rep_b Abs_b (Collect (Domainp B))"
      and B_Rep: "B b b' = (b = Rep_b b')" for b b'
    by (blast dest: ex_type_definition)
  define f where f: "f = (Abs_a ---> Rep_b) f'"  
  have abs_rep_a: "y = Abs_a (Rep_a y)" for y
    using td_a unfolding type_definition_def by simp
  have "(A ===> B) f f'"
    unfolding f map_fun_apply
    by 
      (
        intro rel_funI, 
        unfold A_Rep B_Rep,
        elim ssubst, 
        fold abs_rep_a, 
        intro refl
      )
  then show ?thesis by auto
qed

lemma tts_AB_C_transfer: 
  fixes f :: "'al \<Rightarrow> 'bl \<Rightarrow> 'cl" 
    and A :: "'al \<Rightarrow> 'ar \<Rightarrow> bool"
    and B :: "'bl \<Rightarrow> 'br \<Rightarrow> bool"
    and C :: "'cl \<Rightarrow> 'cr \<Rightarrow> bool" 
  assumes closed: "\<And>a b. \<lbrakk> a \<in> \<UU>A; b \<in> \<UU>B \<rbrakk> \<Longrightarrow> f a b \<in> \<UU>C"
  assumes 
    "Domainp A = (\<lambda>x. x \<in> \<UU>A)" "bi_unique A" "right_total A" 
    "Domainp B = (\<lambda>x. x \<in> \<UU>B)" "bi_unique B" "right_total B" 
    "Domainp C = (\<lambda>x. x \<in> \<UU>C)" "bi_unique C" "right_total C"
  shows "\<exists>rcdt. (A ===> B ===> C) f rcdt"
proof-
  from assms(3,4) obtain Rep_a :: "'ar \<Rightarrow> 'al" and Abs_a :: "'al \<Rightarrow> 'ar" 
    where td_a: "type_definition Rep_a Abs_a (Collect (Domainp A))"
      and A_Rep: "A b b' = (b = Rep_a b')" for b b'
    by (blast dest: ex_type_definition)
  from assms(6,7) obtain Rep_b :: "'br \<Rightarrow> 'bl" and Abs_b :: "'bl \<Rightarrow> 'br" 
    where td_b: "type_definition Rep_b Abs_b (Collect (Domainp B))"
      and B_Rep: "B b b' = (b = Rep_b b')" for b b'
    by (blast dest: ex_type_definition)
  from assms(9,10) obtain Rep_c :: "'cr \<Rightarrow> 'cl" and Abs_c :: "'cl \<Rightarrow> 'cr" 
    where td_c: "type_definition Rep_c Abs_c (Collect (Domainp C))"
      and C_Rep: "C b b' = (b = Rep_c b')" for b b'
    by (blast dest: ex_type_definition)
  define f' where f': "f' = (Rep_a ---> Rep_b ---> Abs_c) f"  
  from td_a td_b td_c have f_closed: "f (Rep_a a) (Rep_b b) \<in> \<UU>C" for a b
    by (intro closed; simp_all add: assms(2,5,8))+
  have rep_abs_c: "y \<in> \<UU>C \<Longrightarrow> y = Rep_c (Abs_c y)" for y
    using td_c unfolding type_definition_def by (simp add: assms(8))
  have "(A ===> B ===> C) f f'"
    unfolding f' map_fun_apply
    by 
      (
        intro rel_funI, 
        unfold A_Rep B_Rep C_Rep,
        elim ssubst, 
        intro rep_abs_c f_closed
      )
  then show ?thesis by auto
qed

lemma tts_AA_A_transfer: 
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes closed: "\<And>a b. \<lbrakk> a \<in> \<UU>; b \<in> \<UU> \<rbrakk> \<Longrightarrow> f a b \<in> \<UU>"
  assumes "Domainp A = (\<lambda>x. x \<in> \<UU>)" "bi_unique A" "right_total A" 
  shows "\<exists>rcdt. (A ===> A ===> A) f rcdt"
  using closed 
  by (rule tts_AB_C_transfer[OF _ assms(2-4) assms(2-4) assms(2-4)])

lemma tts_AA_eq_transfer: 
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "Domainp A = (\<lambda>x. x \<in> \<UU>)" "bi_unique A" "right_total A" 
  shows "\<exists>rcdt. (A ===> A ===> (=)) f rcdt"
proof-
  have closed: "f x y \<in> UNIV" for x y by auto
  have dom_eq: "Domainp (=) = (\<lambda>x. x \<in> UNIV)" by auto
  from tts_AB_C_transfer[
      OF _ assms(1-3) assms(1-3) dom_eq bi_unique_eq right_total_eq
      ]
  show ?thesis by auto
qed

lemma Dom_fun_eq_set:
  assumes
    "Domainp A = (\<lambda>x. x \<in> \<UU>A)" "bi_unique A" "right_total A" 
    "Domainp B = (\<lambda>x. x \<in> \<UU>B)" "bi_unique B" "right_total B" 
  shows "{f. f ` \<UU>A \<subseteq> \<UU>B} = Collect (Domainp (A ===> B))"
proof(standard; (standard, intro CollectI, elim CollectE DomainpE))
  fix x assume "x ` \<UU>A \<subseteq> \<UU>B" 
  from tts_AB_transfer[OF this assms] obtain x' where xx': 
    "(A ===> B) x x'" by clarsimp
  show "Domainp (A ===> B) x" by standard (rule xx')
next
  fix x b assume "(A ===> B) x b" 
  then show "x ` \<UU>A \<subseteq> \<UU>B"
    unfolding 
      rel_fun_def 
      Domainp_eq_Collect[THEN iffD1, OF assms(1)] 
      Domainp_eq_Collect[THEN iffD1, OF assms(4)] 
    by auto
qed

lemma Dom_AB_eq_pred: 
  assumes 
    "Domainp A = (\<lambda>x. x \<in> \<UU>A)" "bi_unique A" "right_total A" 
    "Domainp B = (\<lambda>x. x \<in> \<UU>B)" "bi_unique B" "right_total B" 
  shows "(Domainp (A ===> B) f) = (f ` \<UU>A \<subseteq> \<UU>B)" 
  using Dom_fun_eq_set[OF assms] by blast

end

end