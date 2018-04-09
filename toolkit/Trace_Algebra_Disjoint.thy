(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Trace_Algebra_Disjoint.thy                                           *)
(* Authors: Pedro Ribeiro                                                     *)
(* Emails: pedro.ribeiro@york.ac.uk                                           *)
(******************************************************************************)

section \<open> Trace Algebra (Disjoint variant) \<close>

theory Trace_Algebra_Disjoint
  imports
  Lattices
  Trace_Algebra_Preorder
begin

text \<open> This theory presents a trace algebra that uses a notion of disjointedness
       in the prefix relation so as to allow, for example, traces that use sets
       and subset inclusion as part of their prefix relation. It reuses @{term f\<^sub>0}
       from the Trace Algebra Preorder variant, and is also a semigroup. However
       we only have a partially left-cancellative unary semigroup as a result of
       our weakening of axioms wrt. preorder variant. \<close>

subsection \<open> Motivation \<close>

text \<open> First, we ask ourselves whether a set can be an fzero_trace, or even a trace.
       It cannot as addition of two sets cannot possibly be injective, and so 
       necessarily there is no reasonable way to define a prefix relation based on
       + that is reflexive, and transitive, and for which the semigroup is also 
       left-cancellative. However, if we weaken our axioms to consider sums involving
       disjoint sets we can obtain similar properties. \<close>

lemma "a \<inter> b = {} \<and> a \<inter> c = {} \<and> a \<union> b = a \<union> c \<Longrightarrow> b = c"
  by auto

text \<open> And in particular, the following property also holds. \<close>

lemma "a \<inter> b = {} \<and> a \<union> b = a \<union> c \<Longrightarrow> b \<subseteq> c"
  by auto

text \<open> The subset inclusion relation, which is anti-symmetric, reflexive and transitive,
       can be defined based on + (set union) also by considering only @{term c} which are
       disjoint from @{term a}. \<close>

lemma "(\<exists>c. a \<union> c = d \<and> a \<inter> c = {}) \<longleftrightarrow> a \<subseteq> d"
  by auto

text \<open> The question is then, can we find a set of axioms that characterise this relation,
       and which in the light of a trace algebra allow a weakened left-cancellative axiom,
       yet still satisfy similar laws (necessarily with the additional provisos) to those
       of the Trace Algebra Preorder variant? \<close>

subsection \<open> Disjoint relation \<close>

text \<open> We characterise the disjoint relation for types that provide a plus
       operator and an @{term f\<^sub>0}. \<close>

class disjoint_rel_def =
  -- \<open> A disjoint_rel is a relation, here modelled via a function. \<close>
  fixes disjoint_rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<bar>" 67)

class disjoint_rel = disjoint_rel_def + plus + fzero +
  assumes
      -- \<open> Symmetric \<close>
       (*   disjoint_rel_sym  : "(a \<bar> b) = b \<bar> a" *)
      -- \<open> Every element is related to its @{term f\<^sub>0}. \<close>
         disjoint_rel_zero : "a \<bar> f\<^sub>0(a)" "f\<^sub>0(a) \<bar> a"
      -- \<open> For every pair of non-related elements there is some element @{term d},
           such that the + of these elements can also be obtained by a + d where
           a and d are related by disjoint_rel. In the context of sets this corresponds to stating
           that any sum of non-disjoint sets can be replaced by a sum of disjoint sets. \<close> 
      and disjoint_rel_sum  : "(\<not> a \<bar> b) \<Longrightarrow> (\<exists>d. a + b = a + d \<and> a \<bar> d)"
      -- \<open> A sum of related elements is related to another element iff. each component
           of the sum is also related to that other element. This holds for sets as well. \<close>
      and disjoint_rel_dist : "((a + b) \<bar> c) \<longleftrightarrow> ((a \<bar> c) \<and> (b \<bar> c))" "((c \<bar> a) \<and> (c \<bar> b)) \<longrightarrow> c \<bar> (a + b)"
      and disjoint_rel_fzeros : "(f\<^sub>0(a) \<bar> b) \<and> (f\<^sub>0(a) \<bar> c) \<and> (a \<bar> (f\<^sub>0(a) + b + c)) \<longleftrightarrow> ((a \<bar> b) \<and> a \<bar> c)"
text \<open> For disjoint relations where no two elements are ever non-disjoint we have
       a universal relation. \<close>

class disjoint_rel_universal = disjoint_rel +
  assumes disjoint_rel_univ : "a \<bar> b"

(*
instantiation set :: (type) disjoint_rel
begin
  definition disjoint_rel_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where "disjoint_rel_set a b \<equiv> (a \<inter> b = {})"
  definition plus_set :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where "plus_set a b \<equiv> a \<union> b"
  definition fzero_set :: "'a set \<Rightarrow> 'a set" where "fzero_set a = {}"

  lemma disjoint_rel_set_sum: "\<exists>d. a \<union> b = a \<union> d \<and> a \<inter> d = {}"
    by (metis Diff_iff Int_emptyI Un_Diff_cancel)

  (* A stronger version of this is possible:
  lemma disjoint_rel_set_sum1: "\<exists>!d. a \<union> b = a \<union> d \<and> a \<inter> d = {}"
    by (metis Compl_disjoint2 Diff_Int_distrib Diff_cancel Diff_disjoint Diff_eq Int_Un_distrib2 Int_empty_right Un_Diff Un_Diff_Int Un_Diff_cancel Un_Int_crazy Un_commute Un_empty_left Un_insert_right bot_eq_sup_iff disjoint_rel_set_sum empty_Diff ex_in_conv inf.commute inf_commute insert_absorb sup.left_commute sup.left_idem sup_bot.right_neutral)
  *)

instance
proof
  fix a b c :: "'a set"
  show "(a \<bar> b) = b \<bar> a"
    by (simp add:disjoint_rel_set_def, auto)
  show "a \<bar> f\<^sub>0(a)"
    by (simp add:disjoint_rel_set_def fzero_set_def)
  show "\<not> a \<bar> b \<Longrightarrow> (\<exists>d. a + b = a + d \<and> a \<bar> d)"
    by (simp add:disjoint_rel_set_def plus_set_def disjoint_rel_set_sum)
  show "(a + b) \<bar> c = ((a \<bar> c) \<and> b \<bar> c)"
    by (simp add:disjoint_rel_set_def plus_set_def, auto)
qed
end *)

text \<open> However, we cannot fully instantiate set as fzero_disjoint_trace because
       set subtraction, is, in general, not the same as our definition. \<close>

class fzero_weak_add_zero = fzero_add_zero + disjoint_rel

context fzero_weak_add_zero
begin

definition fzero_weak_le (infix "\<le>\<^sub>s" 50)
  where "a \<le>\<^sub>s b \<longleftrightarrow> (\<exists>c. b = a + c \<and> a \<bar> c)"

definition fzero_weak_subtract (infixl "-\<^sub>s" 65)
  where "a -\<^sub>s b = (if (b \<le>\<^sub>s a) then THE c. a = b + c \<and> b \<bar> c else f\<^sub>0(b))" 

text \<open> The prefix relation is equivalent under the assumption disjoint_rel_sum,
       which means we do not need to redefine \<le>, furthermore we know that this is
       also a preorder too.

       Observe that without the assumption @{term disjoint_rel_sum}
       it would not be possible to rely on this equality by itself to obtain the
       properties analogous to those induced by the left_cancellative semigroup
       in the preorder trace algebra theory. \<close>

lemma fzero_le_iff: "a \<le>\<^sub>s b = (a \<le>\<^sub>u\<^sub>s b)"
  unfolding local.fzero_le_def fzero_weak_le_def
  using local.disjoint_rel_sum by blast

(* Could subtraction also be the same? Likely not, because of \<bar> *)

lemma fzero_weak_le_refl: 
  "a \<le>\<^sub>s a"
  unfolding fzero_weak_le_def 
  by (metis local.add_fzero_right local.disjoint_rel_zero)

lemma fzero_weak_le_least_zero:
  "f\<^sub>0(a) \<le>\<^sub>s a"
  by (simp add: fzero_le_iff local.fzero_le_least_fzero)
   
lemma fzero_weak_le_trans: 
  "\<lbrakk> a \<le>\<^sub>s b; b \<le>\<^sub>s c \<rbrakk> \<Longrightarrow> a \<le>\<^sub>s c"
  using add_assoc fzero_weak_le_def local.disjoint_rel_dist 
  by (meson fzero_le_iff local.fzero_le_trans)
(* local.disjoint_rel_sym by auto *)

lemma fzero_weak_le_add: "a \<le>\<^sub>s a + b"
  unfolding fzero_weak_le_def
  using local.disjoint_rel_zero local.disjoint_rel_sum
  by blast

lemma fzero_weak_le_add_left_mono: 
  "a \<le>\<^sub>s b \<Longrightarrow> c + a \<le>\<^sub>s c + b"
  using add_assoc fzero_le_iff local.fzero_le_def by auto
    
end

class fzero_weak_left_cancel = fzero_add_fzero_ord + fzero_weak_add_zero +
  assumes 
      -- \<open> Assume a partial left cancellative property which is applicable for
           a \<bar> b and a \<bar> c. This is valid for sets. \<close>
          add_left_imp_eq: "((a \<bar> b) \<and> (a \<bar> c) \<and> (a + b = a + c)) \<Longrightarrow> b = c"
      -- \<open> To be able to show @{thm add_le_imp_le_left} we need, in addition, the
           following assumption as our cancellation property is too weak. In this case,
           however we only require that a \<bar> b. \<close>
     (* and add_left_le: "((a \<bar> b) \<and> (a \<bar> c) \<and> (a + b = a + c)) \<Longrightarrow> b \<le> c" *)
begin

text \<open> The cancellation for subtraction requires that a \<bar> b. This lemma is true of sets as well. \<close>

lemma fzero_weak_diff_cancel_left [simp]: 
  assumes "a \<bar> b"
  shows "(a + b) -\<^sub>s a = b"
  using assms apply (simp add: fzero_weak_subtract_def fzero_weak_le_add)
  apply (rule the_equality)
   apply (simp)
  using local.add_left_imp_eq by blast

text \<open> While under the assumption of c \<bar> a, a \<le> b implies that c + a \<le> c + b. \<close>

lemma fzero_weak_add_le_imp_le_left:
  assumes "c \<bar> a" "c \<bar> b" "c + a \<le> c + b"
  shows "a \<le> b"
proof -
  have "c + a \<le> c + b = (\<exists>d. c + a + d = c + b \<and> (c + a) \<bar> d)"
    by (metis local.disjoint_rel_sum local.fzero_le_def local.le_is_fzero_le)
  also have "... \<longrightarrow> (\<exists>d. a + d = b \<and> (a \<bar> d))"
  proof (cases "c \<bar> b")
    case True
    then show ?thesis using assms(1)
      by (metis add_assoc fzero_weak_diff_cancel_left local.disjoint_rel_dist(1) local.disjoint_rel_dist(2))
  next
    case False then show ?thesis using assms(1,2)
      
      by (metis add_assoc  local.disjoint_rel_dist(1) local.disjoint_rel_dist(2) local.disjoint_rel_sum local.fzero_le_def local.le_is_fzero_le)
  qed
  also have "... = (a \<le> b)"
    using local.le_is_fzero_le fzero_le_iff unfolding fzero_weak_le_def 
    by metis
  finally show ?thesis
    using assms(3) by blast
qed

lemma fzero_weak_le_is_le : "a \<le> b \<longleftrightarrow> a \<le>\<^sub>s b"
  by (simp add: local.fzero_le_iff local.le_is_fzero_le)

lemma fzero_weak_less_is_less : "a < b \<longleftrightarrow> a \<le>\<^sub>s b \<and> \<not> (b \<le>\<^sub>s a)"
  by (simp add: fzero_weak_le_is_le local.less_iff)

end

text \<open> If we consider the universal disjoint relation then we can show that minus_us and minus_s are
       the same. First we instantiate the right class. \<close>

class fzero_weak_left_cancel_rel_universal = fzero_weak_left_cancel + disjoint_rel_universal

instance fzero_weak_left_cancel_rel_universal \<subseteq> semigroup_add_left_cancel
proof
  fix a b c :: "'a"
  show "a + b = a + c \<Longrightarrow> b = c"
    by (metis fzero_weak_diff_cancel_left disjoint_rel_univ)
qed

instance fzero_weak_left_cancel_rel_universal \<subseteq> fzero_add_left_cancel
  by intro_classes

lemma
  fixes a :: "'a::fzero_weak_left_cancel_rel_universal"
  shows "a -\<^sub>s b = (a -\<^sub>u\<^sub>s b)"
proof -
  have "a -\<^sub>s b = (a -\<^sub>u\<^sub>s b)"
  proof (cases "b \<le>\<^sub>s a")
    case True
    obtain d where d:"d = a -\<^sub>s b" by auto

    have "a = b + d \<and> b \<bar> d"
      using True d fzero_weak_le_def by force
    then have "a = b + d"
      using disjoint_rel_univ by auto 
    then have "d = a -\<^sub>u\<^sub>s b"
    proof -
      have "b \<le>\<^sub>u\<^sub>s a"
        using True fzero_le_iff by auto
      have "b \<le>\<^sub>u\<^sub>s a \<Longrightarrow> \<forall>x. x = a -\<^sub>u\<^sub>s b \<longleftrightarrow> b + x = a"
        using fzero_add_left_cancel_class.diff_add_cancel_left' by auto
      then show ?thesis using True fzero_le_iff
        by (simp add: \<open>a = b + d\<close>)
    qed
    then show ?thesis using d by auto

  next
    case False
    have "a -\<^sub>s b = f\<^sub>0(b)" "a -\<^sub>u\<^sub>s b = f\<^sub>0(b)"
      using False apply (auto simp add:fzero_weak_subtract_def)
      using False fzero_le_iff by (auto simp add:fzero_subtract_def)

    then show ?thesis by auto
  qed
  then show ?thesis .
qed

class fzero_weak_left_cancel_minus_ord = fzero_weak_left_cancel + minus +
  assumes minus_def: "a - b = a -\<^sub>s b"
begin
  
  lemma le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists> c. b = a + c \<and> a \<bar> c)"
    using local.disjoint_rel_sum local.fzero_le_def local.le_is_fzero_le by auto
    
  lemma le_add [simp]: "a \<le> a + b"
    by (simp add: local.le_is_fzero_le local.fzero_le_add)
      
  lemma add_diff_cancel_left [simp]: "a \<bar> b \<Longrightarrow> (a + b) - a = b"
    by (simp add: minus_def)
      
  lemma add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by (simp add: local.le_is_fzero_le local.fzero_le_add_left_mono)

  lemma add_le_imp_le_left: 
    assumes "c \<bar> a" "c \<bar> b"
    shows "c + a \<le> c + b \<Longrightarrow> a \<le> b"
    using assms local.fzero_weak_add_le_imp_le_left local.le_is_fzero_le by blast

lemma 
  assumes "c \<bar> b"
  shows fzero_plus_right: "f\<^sub>0(c + b) = f\<^sub>0(b)" 
proof -
  have f1: "\<forall>a aa. (aa::'a) + (f\<^sub>0(aa) + a) = aa + a"
    by (metis (no_types) local.add.semigroup_axioms local.add_fzero_right semigroup.assoc)
  have f2: "\<forall>a. f\<^sub>0(f\<^sub>0(a::'a)) = f\<^sub>0(a)"
    by simp
  then have "\<forall>a aa. f\<^sub>0(aa::'a) \<bar> (f\<^sub>0(aa) + a)"
    by (metis local.disjoint_rel_dist(2) local.disjoint_rel_zero(1) local.le_add local.le_iff_add)
  then show ?thesis
    using f2 f1 assms
  proof -
      have "c \<bar> (b + f\<^sub>0(c + b))"
  by (metis assms local.disjoint_rel_dist(1) local.disjoint_rel_dist(2) local.disjoint_rel_zero(1)) (* 9 ms *)
    then have "b + f\<^sub>0(c + b) = b + f\<^sub>0(b)"
      by (metis (no_types) add_assoc assms local.add_diff_cancel_left local.add_fzero_right) (* 90 ms *)
    then show ?thesis
      by (meson local.add_left_imp_eq local.disjoint_rel_dist(1) local.disjoint_rel_zero(1)) (* 3 ms *)
  qed
qed
  
  (* This is used in many theories without this assumption, so care will be needed. *)
  lemma add_diff_cancel_left' [simp]:  
    assumes "c \<bar> a" "c \<bar> b"
    shows "(c + a) - (c + b) = a - b" 
      proof (cases "b \<le> a")
        case True 
        then have a:"\<exists>d. (c + b) + d = c + a \<and> (c + b) \<bar> d"
          by (metis (full_types) add_assoc local.disjoint_rel_sum local.le_iff_add)
        then have b:"\<exists>d. b + d = a \<and> b \<bar> d"
          using True local.le_iff_add by auto
        then show ?thesis 
          by (metis a add_assoc assms(1) assms(2) local.add_diff_cancel_left local.disjoint_rel_dist(1) local.disjoint_rel_dist(2))

      next
        case False 
        have "(c + a) - (c + b) = fzero (c + b)"
          using assms
          using False local.add_le_imp_le_left local.fzero_le_iff local.fzero_weak_subtract_def local.le_is_fzero_le local.minus_def by auto
        also have "... = fzero b"
          by (simp add: assms(2) fzero_plus_right)
        also have "... = a - b"
          using False local.add_le_imp_le_left local.fzero_le_iff local.fzero_weak_subtract_def local.le_is_fzero_le local.minus_def by auto
          
        finally show ?thesis by auto
      qed
    
  lemma diff_add_cancel_left': "a \<le> b \<Longrightarrow> a + (b - a) = b"
    using local.le_iff_add local.le_is_fzero_le by auto
      
  lemma add_left_strict_mono: "a \<bar> b \<Longrightarrow> a \<bar> c \<Longrightarrow> \<lbrakk> a + b < a + c \<rbrakk> \<Longrightarrow> b < c"
    using local.add_le_imp_le_left local.add_left_mono local.less_iff by blast
 
  lemma sum_minus_left: "a \<bar> b \<Longrightarrow> c \<le> a \<Longrightarrow> (a + b) - c = (a - c) + b"
    using add_assoc local.le_iff_add local.disjoint_rel_dist by auto
  
  lemma minus_cancel_le: "\<lbrakk> x \<le> y; y \<le> z \<rbrakk> \<Longrightarrow> y - x \<le> z - x"
    using local.le_iff_add local.le_is_fzero_le local.fzero_le_add local.sum_minus_left by auto

  lemma sum_minus_right: "a \<bar> b \<Longrightarrow> c \<ge> a \<Longrightarrow> a + b - c = b - (c - a)"
    using local.le_iff_add by auto
  
  lemma diff_diff_add: "b \<bar> c \<Longrightarrow> b + c \<le> a \<Longrightarrow> a - (b + c) = a - b - c"
   proof -
    assume a1: "b + c \<le> a"
      assume a2: "b \<bar> c"
    obtain aa :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
      "\<forall>x0 x1. (\<exists>v2. x0 = x1 + v2 \<and> x1 \<bar> v2) = (x0 = x1 + aa x0 x1 \<and> x1 \<bar> (aa x0 x1))"
        by moura
    then have f3: "a = b + c + aa a (b + c) \<and> (b + c) \<bar> (aa a (b + c))"
      using a1 by (simp add: local.le_iff_add)
      have "b \<le> b + c"
        using a2 by auto
      then show ?thesis
        using f3 a2 by (metis (no_types) local.fzero_weak_diff_cancel_left local.minus_def local.disjoint_rel_dist local.sum_minus_left) (* 68 ms *)
    qed

  lemma least_zero [simp]: 
    "a \<bar> b \<Longrightarrow> f\<^sub>0(a) \<le> b"
    using local.fzero_weak_add_le_imp_le_left local.disjoint_rel_zero by fastforce
  
  lemma not_le_minus [simp]:  "\<not> (a \<le> b) \<Longrightarrow> b - a = f\<^sub>0(a)"
    by (simp add: local.fzero_weak_le_is_le local.fzero_weak_subtract_def local.minus_def)
      
  lemma diff_zero [simp]: "b \<bar> a \<Longrightarrow> a - f\<^sub>0(b) = a"
    using local.add_diff_cancel_left' local.disjoint_rel_zero(1) by fastforce
  
  lemma diff_zero_same [simp]: "a - f\<^sub>0(a) = a"
    by (metis local.add_diff_cancel_left local.diff_zero local.disjoint_rel_zero(1) local.disjoint_rel_zero(2) local.least_zero local.sum_minus_right)
  
  lemma diff_cancel [simp]: "a - a = f\<^sub>0(a)"
    using local.add_diff_cancel_left local.disjoint_rel_zero by fastforce
     
  lemma zero_le_minus_imp_le: "\<lbrakk> b \<le> a; f\<^sub>0(b) < a - b \<rbrakk> \<Longrightarrow> b < a"
    using local.less_iff local.minus_cancel_le by fastforce
  
  lemma le_imp_zero_le_minus: "\<lbrakk> b \<le> a; b < a \<rbrakk> \<Longrightarrow> f\<^sub>0(b) < a - b"
    using local.add_left_strict_mono local.disjoint_rel_zero(1) local.fzero_weak_diff_cancel_left local.le_iff_add by fastforce
    
  lemma le_iff_zero_leq_minus: "\<lbrakk> b \<le> a \<rbrakk> \<Longrightarrow> b < a \<longleftrightarrow> f\<^sub>0(b) < a - b"
    using zero_le_minus_imp_le le_imp_zero_le_minus by blast
      
  lemma le_and_minus_is_zero_imp_eq: "\<lbrakk> b < a \<and> a - b = f\<^sub>0(b)\<rbrakk> \<Longrightarrow> b = a"
    using local.less_iff le_imp_zero_le_minus by force
      
  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = f\<^sub>0(b) \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add by auto

  lemma minus_minus_fzero [simp]: "a - b - f\<^sub>0(b) = a - b"
    by (metis local.add_fzero_right local.diff_diff_add local.diff_zero local.disjoint_rel_zero(1) local.not_le_minus)

  lemma minus_prefix_disjoint: "b \<le> a \<and> a - b = c \<longleftrightarrow> a = b + c \<and> b \<bar> c"
    using local.diff_add_cancel_left' local.disjoint_rel_sum by fastforce
(*
lemma "d = a + b + c \<and> (fzero(a) \<bar> b) \<and> ((fzero(a) + b) \<bar> c) \<and> a \<bar> (fzero(a) + b + c) \<and> a \<le> d \<longleftrightarrow> d = a + b + c \<and> a \<bar> b \<and> (a + b) \<bar> c \<and> a \<le> d"
  nitpick*)
  (* Sadd:unit *)
  lemma 
  assumes "a \<bar> b"
  shows "a + b = a \<longrightarrow> b = fzero(b)"
    using assms local.add_diff_cancel_left by fastforce
  
  (* SSub:same *)
  lemma "c \<le> a \<and> c \<le> b \<longrightarrow> a - c = b - c \<longleftrightarrow> a = b"
    by (metis local.diff_add_cancel_left')
      
  (* SSub:subsub *)    
  lemma "c \<le> a \<and> c \<le> b \<and> b \<le> a \<longrightarrow>(a - c) - (b - c) = a - b"
    by (metis local.fzero_weak_diff_cancel_left local.le_iff_add local.minus_def local.sum_minus_right)
  
end

class fzero_weak_left_cancel_minus_ord_rel_universal = fzero_weak_left_cancel_minus_ord + disjoint_rel_universal

(* TODO: Complete instantiation 
instance fzero_weak_left_cancel_minus_ord_rel_universal \<subseteq> semigroup_add_left_cancel_minus_ord
proof
  fix a b :: "'a::fzero_weak_left_cancel_minus_ord_rel_universal"
  show "a - b = a -\<^sub>u\<^sub>s b"
    using disjoint_rel_univ
*)

(* NOTE: It turns out this axiom is not necessary in the original Trace Algebra for the
         generalised reactive processes hierarchy. However, there are still some questions
         to be answered here, even in the context of a boolean algebra. For example, the
         following law:

         a \<bar> c \<and> a \<le> b + c \<Longrightarrow> a \<le> b

         This is not satisfied for sure without the following weakened version of sum_eq_sum_conv,
         but also it is not clear whether it can be proved. *)

class fzero_weak_pre_trace = fzero_weak_left_cancel_minus_ord +
  assumes (* TODO: move this out of pre_trace class, so it doesn't need to be repeated *)
  sum_eq_sum_conv: "a \<bar> b \<and> (a \<bar> d) \<and> (a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
begin

  (* Does this work for sets? You bet it does.
  lemma "a \<inter> b = {} \<and> (a \<inter> d = {}) \<and> (a \<union> b) = (c \<union> d) \<Longrightarrow> \<exists> e . a = c \<union> e \<and> e \<union> b = d \<or> a \<union> e = c \<and> b = e \<union> d"
     by (smt abel_semigroup.commute inf.abel_semigroup_axioms inf_sup_absorb inf_sup_distrib1 sup.abel_semigroup_axioms sup_bot.right_neutral sup_left_idem)

  lemma "a \<inter> c = {} \<and> a \<subseteq> b \<union> c \<Longrightarrow> a \<subseteq> b"
    by auto*)

  (* The original le_common_total cannot possibly hold, even in a weakened form
     where a \<bar> b. But the following might hold, however I haven't proved it.  
  lemma le_common_total: "\<lbrakk> (\<not> a \<bar> b); a \<le> c; b \<le> c \<rbrakk> \<Longrightarrow> a \<le> b \<or> b \<le> a"
    oops
  *)

  lemma le_sum_cases: "a \<bar> c \<and> a \<le> b + c \<longrightarrow> b \<le> a \<or> a \<le> b" 
  proof -
    have "(a \<bar> c \<and> a \<le> b + c) = (\<exists>e. (a \<bar> e) \<and> a \<bar> c \<and>  a + e = b + c )"
      using local.le_iff_add by fastforce
    also have "... = (\<exists>e. (a \<bar> e) \<and> a \<bar> c \<and> a + e = b + c \<and> (\<exists>d. a = b + d \<and> d + e = c \<or> a + d = b \<and> e = d + c))" (* \<exists>d. a = b + d \<and> d + e = c *)
    proof -
      have "\<forall>a c e b. ((a \<bar> e) \<and> a \<bar> c \<and> a + e = b + c) \<longrightarrow> (\<exists>d. a = b + d \<and> d + e = c \<or> a + d = b \<and> e = d + c)"
        by (simp add: sum_eq_sum_conv)
      then show ?thesis by auto
    qed
    also have "... \<longrightarrow> (\<exists>d. a = b + d \<or> a + d = b)"
      by auto

    then have "... = (b \<le> a \<or> a \<le> b)"
      using local.fzero_le_def local.le_is_fzero_le by auto

    then show ?thesis using calculation by auto
  qed
            
  lemma le_sum_cases':
    "a \<bar> c \<and> a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    by (metis (full_types) local.add_diff_cancel_left local.disjoint_rel_dist(1) local.fzero_weak_add_le_imp_le_left local.le_iff_add local.le_sum_cases)
     
  lemma le_sum_iff: 
    assumes "a \<bar> c"
    shows "a \<le> b + c \<longleftrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    using assms by (metis local.add_left_mono local.diff_add_cancel_left' local.le_is_fzero_le local.le_sum_cases' local.fzero_le_add local.fzero_le_trans)

end

text \<open> Like in the preorder variant of the trace algebra, fzero needs to be constant
       to obtain anti-symmetry. \<close>
  
lemma fzero_weak_le_antisym :
  fixes a :: "'a::{fzero_is_0,fzero_weak_pre_trace,fzero_sum_zero}"
  assumes "a \<le> b" "b \<le> a"
  shows "a = b"
proof -
  obtain a' where a': "b = a + a' \<and> a \<bar> a'"
    using assms(1) by (auto simp add:fzero_weak_le_is_le fzero_weak_le_def)

  obtain b' where b': "a = b + b' \<and> b \<bar> b'"
    using assms(2) by (auto simp add:fzero_weak_le_is_le fzero_weak_le_def)

  have "b' = (b' + a' + b')"
    by (metis a' add.assoc add_fzero_right assms(1) b' disjoint_rel_zero fzero_plus_right fzero_weak_left_cancel_minus_ord_class.add_diff_cancel_left fzero_weak_left_cancel_minus_ord_class.sum_minus_left)
    
  hence "f\<^sub>0(b') + f\<^sub>0(b') + b' = (b' + a' + b')"
    by (metis add.semigroup_axioms add_fzero_left semigroup.assoc)
      
  hence "f\<^sub>0(b') + f\<^sub>0(b') = b' + a'"
    by (metis a' add_fzero_right assms(2) b' disjoint_rel_zero fzero_is_0 fzero_weak_left_cancel_minus_ord_class.add_diff_cancel_left fzero_weak_left_cancel_minus_ord_class.sum_minus_left)
      
  hence "b' + a' = f\<^sub>0(b')"
    by (metis add_fzero_right fzero_is_0)
      
  hence "a' = f\<^sub>0(a')" "b' = f\<^sub>0(b')"
    using fzero_sum apply blast
    using \<open>b' + a' = f\<^sub>0(b')\<close> fzero_sum_left by auto

  with a' b' show ?thesis
    by (metis add_fzero_right fzero_is_0)

qed

text \<open> We then define the weak fzero algebra. \<close>

class fzero_weak_trace = fzero_weak_left_cancel_minus_ord + fzero_sum_zero
begin
 lemma neq_zero_impl_greater:
    "x \<noteq> fzero x \<Longrightarrow> fzero x < x"
   by (metis local.add_fzero_left local.diff_cancel local.disjoint_rel_zero(2) local.fzero_sum_right local.fzero_weak_le_is_le local.fzero_weak_le_least_zero local.fzero_weak_less_is_less local.sum_minus_left)
end

(* instantiation set :: (type) fzero_trace
begin
fzero_le_def trace_class.le_iff_add *)

typedef 'a myset = "{x::'a set. True}"
  morphisms myset2set set2myset 
  by auto

setup_lifting type_definition_myset

declare [[coercion_enabled]]
        [[coercion myset2set]]

instantiation myset :: (type) ord
begin
  lift_definition less_eq_myset :: "'a myset \<Rightarrow> 'a myset \<Rightarrow> bool" is "op \<subseteq>" .
  lift_definition less_myset :: "'a myset \<Rightarrow> 'a myset \<Rightarrow> bool" is "op \<subset>" .
instance 
  by intro_classes
end

instantiation myset :: (type) minus
begin
  lift_definition original_minus :: "'a myset \<Rightarrow> 'a myset \<Rightarrow> 'a myset" is "op -" .

  definition minus_myset :: "'a myset \<Rightarrow> 'a myset \<Rightarrow> 'a myset" where 
  "minus_myset a b \<equiv> if b \<le> a then (original_minus a b) else set2myset {}"

instance by intro_classes
end
(*
instantiation myset :: (type) fzero_weak_add_zero
begin
  definition disjoint_rel_myset :: "'a myset \<Rightarrow> 'a myset \<Rightarrow> bool" where "disjoint_rel_myset a b \<equiv> a \<inter> b = {}"
  lift_definition plus_myset :: "'a myset \<Rightarrow> 'a myset \<Rightarrow> 'a myset" is "op \<union>" .
  lift_definition fzero_myset :: "'a myset \<Rightarrow> 'a myset" is "\<lambda>x. {}" .

  lemma set_p1: "a \<inter> b \<noteq> {} \<longrightarrow> (\<exists>d. a \<union> b = a \<union> d \<and> a \<inter> d = {})"
    by (metis Diff_disjoint Un_Diff_cancel)

  lemma set_subtract: "a \<subseteq> b \<longrightarrow> (\<exists>c. b = c \<union> a \<and> c \<inter> a = {})"
    by (metis Diff_disjoint Diff_partition abel_semigroup.commute inf_commute sup.abel_semigroup_axioms)

instance
proof (intro_classes)
  fix a b c :: "'a myset"
  show "(a \<bar> b) = b \<bar> a"
    by (auto simp add:disjoint_rel_myset_def)
  show "a \<bar> f\<^sub>0(a)"
    by (auto simp add:disjoint_rel_myset_def fzero_myset_def set2myset_inverse)
  show "(\<not> a \<bar> b) \<Longrightarrow> \<exists>d. a + b = a + d \<and> a \<bar> d"
    apply (simp add:disjoint_rel_myset_def plus_myset_def)
    by (metis Diff_cancel Int_Diff Un_Diff_cancel inf_bot_right inf_commute original_minus.rep_eq)
  show "(a + b) \<bar> c = ((a \<bar> c) \<and> b \<bar> c)"
    apply (simp add:disjoint_rel_myset_def plus_myset_def set2myset_inverse)
    by (simp add: Int_Un_distrib2)
  show "f\<^sub>0(f\<^sub>0(a)) = f\<^sub>0(a)"
    by (auto simp add:fzero_myset_def)
  show "a + b + c = a + (b + c)"
    apply (auto simp add:plus_myset_def set2myset_inverse)
    by (simp add: sup_assoc)
  show "f\<^sub>0(a) + a = a"
    by (auto simp add:plus_myset_def fzero_myset_def set2myset_inverse myset2set_inverse)
  show "a + f\<^sub>0(a) = a"
    by (auto simp add:plus_myset_def fzero_myset_def set2myset_inverse myset2set_inverse)
qed    
 
end

instance myset :: (type) fzero_add_fzero_ord
proof
  fix a b :: "'a myset"
  show "(a \<le> b) = (a \<le>\<^sub>u\<^sub>s b)"
    apply (simp add:less_eq_myset_def fzero_le_def)
    using myset2set_inject plus_myset.rep_eq by fastforce
  show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    apply (simp add:less_myset_def)
    by (simp add: less_eq_myset.rep_eq less_le_not_le)
qed

lemma set2myset_dist: "set2myset(a \<union> b) = set2myset(a) + set2myset(b)"
  by (simp add: eq_onp_same_args plus_myset.abs_eq)

lemma set_sum_eq_weak_conv: "a \<inter> b = {} \<and> (a \<inter> d = {}) \<and> (a \<union> b) = (c \<union> d) \<Longrightarrow> \<exists> e . a = c \<union> e \<and> e \<union> b = d \<or> a \<union> e = c \<and> b = e \<union> d"
  by (smt abel_semigroup.commute inf.abel_semigroup_axioms inf_sup_absorb inf_sup_distrib1 sup.abel_semigroup_axioms sup_bot.right_neutral sup_left_idem)


instance myset :: (type) fzero_weak_trace
proof
  fix a b c d :: "'a myset"
  show "(a \<bar> b) \<and> a \<bar> c \<and> a + b = a + c \<Longrightarrow> b = c"
    apply (simp add:disjoint_rel_myset_def plus_myset_def set2myset_inject)
    by (metis Diff_Diff_Int Diff_empty Un_Diff Un_Diff_Int Un_empty_right inf_commute myset2set_inject)
  show "a \<bar> b \<and> a + b = a + c \<Longrightarrow> b \<le> c"
    apply (simp add:disjoint_rel_myset_def)
    by (metis (no_types, lifting) Int_Un_distrib2 Un_empty_right inf.absorb_iff2 inf.idem inf_sup_aci(5) less_eq_myset.rep_eq plus_myset.rep_eq sup_inf_absorb)
  show "a - b = a -\<^sub>s b"
  proof (cases "b \<le> a")
    case True
    then obtain d where d:"b + d = a \<and> b \<bar> d"  
      by (metis (no_types) le_is_fzero_le disjoint_rel_sum fzero_le_def)
    
    have "b \<le> a = (b \<le>\<^sub>s a)" 
      by (auto simp add:le_is_fzero_le fzero_le_iff)
    then have "d = a -\<^sub>s b"
      using True apply (simp add:fzero_weak_subtract_def)
      apply (rule sym)
      apply (rule the_equality)
       apply (simp add: d)
        proof -
          fix ca :: "'a myset"
          assume a1: "a = b + ca \<and> b \<bar> ca"
          have f2: "myset2set b \<inter> myset2set d = {}"
            by (metis d disjoint_rel_myset_def)
            have f3: "\<forall>A Aa. (Aa::'a set) \<inter> A = A \<inter> Aa"
              by blast
            have f4: "myset2set b \<inter> myset2set ca = {}"
              using a1 by (simp add: disjoint_rel_myset_def)
            have "\<forall>A. (A::'a set) \<inter> A = A"
              by simp
            then show "ca = d"
              using f4 f3 f2 a1 by (metis (no_types) Int_Un_distrib2 d myset2set_inverse plus_myset.rep_eq sup_bot.left_neutral)
          qed
          case True
          then show ?thesis
            by (smt Diff_Diff_Int Diff_empty Diff_partition Diff_triv Int_lower2 Un_Diff \<open>d = a -\<^sub>s b\<close> d disjoint_rel_myset_def disjoint_rel_sym map_fun_apply minus_myset_def myset2set_inverse original_minus_def plus_myset.rep_eq)      
  next
    case False
    then show ?thesis
      by (metis eq_onp_same_args fzero_myset.abs_eq fzero_weak_le_def fzero_weak_subtract_def less_eq_myset.rep_eq minus_myset_def myset2set_inverse plus_myset.rep_eq sup_ge1)
  qed
  show "a + b = f\<^sub>0(b) \<Longrightarrow> b = f\<^sub>0(b)"
    apply (auto simp add:plus_myset_def fzero_myset_def)
    by (metis fzero_myset.rep_eq monoid.left_neutral myset2set_inverse plus_myset.rep_eq sup.commute sup_bot.monoid_axioms sup_left_idem)
qed *)

text \<open> Also every boolean algebra where plus is the lub and fzero is bot
       can be instantiated in a simple way as a fzero_weak_add_zero. \<close>

class boolean_fzero = inf + sup + bot + fzero + plus + disjoint_rel_def +
  assumes fzero_is_bot : "f\<^sub>0(a) = bot"
      and plus_is_lub  : "a + b = (sup a b)"
      and disjoint_rel_is_glb_no_bot: "a \<bar> b \<longleftrightarrow> (inf a b = bot)"

class boolean_fzero_algebra = boolean_fzero + boolean_algebra

instance boolean_fzero_algebra \<subseteq> fzero_weak_add_zero
proof
  fix a b c :: "'a::boolean_fzero_algebra"
(*  show "(a \<bar> b) = b \<bar> a"
    by (auto simp add:disjoint_rel_is_glb_no_bot inf_commute) *)
  show "a \<bar> f\<^sub>0(a)"
    by (auto simp add:disjoint_rel_is_glb_no_bot fzero_is_bot)
  show "f\<^sub>0(a) \<bar> a"
    by (auto simp add:disjoint_rel_is_glb_no_bot fzero_is_bot)
  show "(\<not> a \<bar> b) \<Longrightarrow> \<exists>d. a + b = a + d \<and> a \<bar> d"
    apply (auto simp add:disjoint_rel_is_glb_no_bot plus_is_lub)
    by (metis inf_compl_bot_left1 inf_left_commute inf_sup_absorb sup_compl_top sup_inf_distrib1)
  show "(a + b) \<bar> c = ((a \<bar> c) \<and> b \<bar> c)"
    by (auto simp add:disjoint_rel_is_glb_no_bot plus_is_lub inf_sup_distrib2)
  show "f\<^sub>0(f\<^sub>0(a)) = f\<^sub>0(a)"
    by (auto simp add:fzero_is_bot)
  show "a + b + c = a + (b + c)"
    by (auto simp add:plus_is_lub sup_assoc)
  show "f\<^sub>0(a) + a = a"
    by (auto simp add:plus_is_lub fzero_is_bot)
  show "a + f\<^sub>0(a) = a"
    by (auto simp add:plus_is_lub fzero_is_bot)
  show "((c \<bar> a) \<and> c \<bar> b) \<longrightarrow> c \<bar> (a + b)"
    by (auto simp add:disjoint_rel_is_glb_no_bot plus_is_lub inf_sup_distrib1) 
qed

instance boolean_fzero_algebra \<subseteq> fzero_weak_left_cancel
proof
  fix a b c :: "'a::boolean_fzero_algebra"
  show "(a \<le> b) = (a \<le>\<^sub>u\<^sub>s b)"
    apply (auto simp add:fzero_le_def plus_is_lub)
    by (metis le_iff_sup)
  show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    by (auto simp add:fzero_le_def)
  show "a \<bar> b \<and> (a \<bar> c) \<and> a + b = a + c \<Longrightarrow> b = c"
    apply (auto simp add:disjoint_rel_is_glb_no_bot plus_is_lub)
    by (metis inf.absorb_iff2 inf_commute inf_sup_distrib1 sup_ge2)
 (* show "a \<bar> b \<and> a \<bar> c \<and> a + b = a + c \<Longrightarrow> b \<le> c"
    apply (auto simp add:disjoint_rel_is_glb_no_bot plus_is_lub)
    by (metis compl_inf double_compl inf_sup_aci(5) le_iff_sup sup_bot.left_neutral sup_ge2 sup_inf_distrib2)*)
qed

end