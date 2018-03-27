(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Trace_Algebra_Extended.thy                                           *)
(* Authors: Pedro Ribeiro                                                     *)
(* Emails: pedro.ribeiro@york.ac.uk                                           *)
(******************************************************************************)

section \<open> Trace Algebra (Preorder variant) \<close>

theory Trace_Algebra_Preorder
  imports Main
begin

text \<open> In this theory we present a variant of the trace algebra where instead of
       a partial order we have a preorder. This is possible by generalising the
       zero of the monoid-based trace algebra and dropping anti-symmetry.
       Effectively we have a left-cancellative unary semigroup whose unary
       function @{term f\<^sub>0} is idempotent.  \<close>

subsection \<open> Unary fzero \<close>

text \<open> We call the unitary function fzero @{term f\<^sub>0}, that is, a functional zero
       when compared to the monoid-based trace algebra. \<close>
  
class fzero = 
  fixes fzero :: "'a \<Rightarrow> 'a" ("f\<^sub>0'(_')")

class fzero_idem = fzero +
  assumes fzero_idem[simp]: "f\<^sub>0(f\<^sub>0(a)) = f\<^sub>0(a)"    

text \<open> The monoid-based trace algebra can be obtained by fixing @{term f\<^sub>0} as 0.
       We explore this in the trace algebra hierarchy theory file \<close>
    
class fzero_is_0 = fzero + zero +
  assumes fzero_is_0: "f\<^sub>0(a) = 0"

text \<open> If we admit @{term f\<^sub>0} to be the identity, then we obtain a semigroup that
       belongs to the class of U-semigroups. In particular, when combined with the
       trace algebra presented in this theory, we obtain a *-semigroup. \<close>

class fzero_ident = fzero +
  assumes fzero_ident: "f\<^sub>0(a) = a"

subsection \<open> Unary fzero semigroup \<close>

text \<open> The class of semigroups with a unary function is then defined. \<close>

class semigroup_add_fzero = semigroup_add + fzero
    
text \<open> We then define mirror properties of a monoid, but instead we
       require the zero property on fzero, rather than 0. \<close>
    
class fzero_add_zero = fzero_idem + semigroup_add_fzero +
  assumes add_fzero_left[simp]: "f\<^sub>0(a) + a = a"
  assumes add_fzero_right[simp]: "a + f\<^sub>0(a) = a"
    
text \<open> In this algebra we only require zero_sum_right, but not
        zero_sum_left. The immediate consequence is that we do
        not obtain an order as there is no anti-symmetry. \<close>
    
class fzero_sum_zero = fzero_add_zero +
  assumes fzero_sum_right: "a + b = f\<^sub>0(b) \<Longrightarrow> b = f\<^sub>0(b)"
    
instance fzero_sum_zero \<subseteq> fzero_add_zero
  by intro_classes  
  
instance fzero_add_zero \<subseteq> semigroup_add_fzero
  by intro_classes
    
instance fzero_sum_zero \<subseteq> semigroup_add_fzero
  by intro_classes    
    
text \<open> However, when in addition we consider the class fzero_is_0, then trivially we have that 
       sum_left and sum properties are satisfied as expected. \<close>
    
lemma fzero_sum_left:
  fixes a :: "'a::{fzero_is_0,fzero_sum_zero}"
  shows "a + b = f\<^sub>0(a) \<Longrightarrow> a = f\<^sub>0(a)"
  by (metis fzero_add_zero_class.add_fzero_right fzero_sum_right fzero_is_0)
    
lemma fzero_sum:
  fixes a :: "'a::{fzero_is_0,fzero_sum_zero}"
  shows "a + b = f\<^sub>0(a) \<longleftrightarrow> a = f\<^sub>0(a) \<and> b = f\<^sub>0(b)"
  by (metis add_fzero_left fzero_is_0 fzero_sum_left)    

text \<open> We define less and minus in terms of plus in the context of the class fzero_add_zero
       as this is sufficient to define a prefix relation that is reflexive and transitive. \<close>

context fzero_add_zero
begin
  
definition fzero_le (infix "\<le>\<^sub>u\<^sub>s" 50)
  where "a \<le>\<^sub>u\<^sub>s b \<longleftrightarrow> (\<exists>c. b = a + c)"

definition fzero_subtract (infixl "-\<^sub>u\<^sub>s" 65)
  where "a -\<^sub>u\<^sub>s b = (if (b \<le>\<^sub>u\<^sub>s a) then THE c. a = b + c else f\<^sub>0(b))"  
    
lemma fzero_refl:
  "a \<le>\<^sub>u\<^sub>s a"
  by (metis fzero_le_def local.add_fzero_right)
    
lemma fzero_le_trans: 
  "\<lbrakk> a \<le>\<^sub>u\<^sub>s b; b \<le>\<^sub>u\<^sub>s c \<rbrakk> \<Longrightarrow> a \<le>\<^sub>u\<^sub>s c"
  unfolding fzero_le_def
  using add_assoc by blast

lemma fzero_le_least_fzero: "fzero a \<le>\<^sub>u\<^sub>s a"
  by (metis local.add_fzero_left local.fzero_le_def)
   
lemma fzero_le_add: "a \<le>\<^sub>u\<^sub>s a + b"
  using fzero_le_def
  by blast

lemma fzero_le_add_left_mono: 
  "a \<le>\<^sub>u\<^sub>s b \<Longrightarrow> c + a \<le>\<^sub>u\<^sub>s c + b"
  using fzero_le_def
  using add_assoc by auto

end

text \<open> The following class allows @term{\<le>}, @term{<} and @term{-} to be related with
       that of fzero_add_zero. \<close>

class fzero_add_fzero_ord_minus = fzero_add_zero + ord + minus +
  assumes le_is_fzero_le: "a \<le> b \<longleftrightarrow> (a \<le>\<^sub>u\<^sub>s b)"
  and less_iff: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)"
  and minus_def: "a - b = a -\<^sub>u\<^sub>s b"

text \<open> We then show we have a preorder. \<close>

instance fzero_add_fzero_ord_minus \<subseteq> preorder
proof
  fix x y z :: "'a::fzero_add_fzero_ord_minus" 
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_iff)
  show "x \<le> x"
    by (simp add: fzero_add_zero_class.fzero_refl le_is_fzero_le)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using le_is_fzero_le 
    by (metis fzero_add_zero_class.fzero_le_trans)
qed

subsection \<open> Unary left-cancellative fzero semigroup class \<close>
  
class semigroup_add_left_cancel = fzero_add_zero +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
begin
  
lemma add_fzero_diff_cancel_left [simp]: 
  "(a + b) -\<^sub>u\<^sub>s a = b"
  apply (simp add: fzero_subtract_def fzero_le_add)
  apply (rule the_equality)
   apply (simp)
    using local.add_left_imp_eq by blast
    
lemma add_le_imp_le_left:
  "c + a \<le>\<^sub>u\<^sub>s c + b \<Longrightarrow> a \<le>\<^sub>u\<^sub>s b"
  unfolding fzero_le_def
  by (metis add_assoc local.add_left_imp_eq)

end 
  
class semigroup_add_left_cancel_minus_ord = fzero_add_fzero_ord_minus + semigroup_add_left_cancel
begin
  
  lemma le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists> c. b = a + c)"
    by (simp add: local.fzero_le_def local.le_is_fzero_le)
  
  lemma le_add [simp]: "a \<le> a + b"
    by (simp add: local.le_is_fzero_le local.fzero_le_add)
      
  lemma add_diff_cancel_left [simp]: "(a + b) - a = b"
    by (simp add: minus_def)
      
  lemma add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by (simp add: local.le_is_fzero_le local.fzero_le_add_left_mono)

  lemma add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"
    using local.add_le_imp_le_left local.le_is_fzero_le by blast
      
  lemma add_diff_cancel_left' [simp]:  " (c + a) - (c + b) = a - b"
    proof (cases "b \<le> a")
      case True thus ?thesis
        by (metis add_assoc local.add_fzero_diff_cancel_left local.le_iff_add local.minus_def)
    next
      case False thus ?thesis
        using local.add_le_imp_le_left
        by (metis add_assoc local.add_fzero_diff_cancel_left local.add_fzero_right local.fzero_subtract_def local.le_is_fzero_le local.minus_def)
    qed
    
  lemma diff_add_cancel_left': "a \<le> b \<Longrightarrow> a + (b - a) = b"
    using local.le_iff_add local.le_is_fzero_le by auto
      
  lemma add_left_strict_mono: "\<lbrakk> a + b < a + c \<rbrakk> \<Longrightarrow> b < c"
    using local.add_le_imp_le_left local.add_left_mono local.less_iff by blast
      
  lemma sum_minus_left: "c \<le> a \<Longrightarrow> (a + b) - c = (a - c) + b"
    by (metis add_assoc diff_add_cancel_left' local.add_fzero_diff_cancel_left local.minus_def)
  
  lemma minus_cancel_le: "\<lbrakk> x \<le> y; y \<le> z \<rbrakk> \<Longrightarrow> y - x \<le> z - x"
    by (metis local.diff_add_cancel_left' local.le_is_fzero_le local.fzero_le_add local.sum_minus_left)

  lemma sum_minus_right: "c \<ge> a \<Longrightarrow> a + b - c = b - (c - a)"
    by (metis diff_add_cancel_left' local.add_diff_cancel_left') 
  
  lemma diff_diff_add: "b + c \<le> a \<Longrightarrow> a - (b + c) = a - b - c"
    by (metis local.add_diff_cancel_left' local.diff_add_cancel_left' local.le_is_fzero_le local.fzero_le_add local.fzero_le_trans)

  lemma least_zero [simp]: "f\<^sub>0(a) \<le> b"
    by (metis local.add.semigroup_axioms local.add_fzero_right local.add_left_imp_eq local.le_iff_add semigroup.assoc)

  (* TODO: Check this still works in CTA theory *)
  lemma not_le_minus [simp]:  "\<not> (a \<le> b) \<Longrightarrow> b - a = f\<^sub>0(a)"
    by (simp add: local.fzero_subtract_def local.le_is_fzero_le local.minus_def)
      
  lemma diff_zero [simp]: "a - f\<^sub>0(b) = a"
    by (metis local.add.semigroup_axioms local.add_fzero_right local.diff_add_cancel_left' local.fzero_idem local.least_zero semigroup.assoc)
       
  lemma diff_cancel [simp]: "a - a = f\<^sub>0(a)"
    by (metis local.add_diff_cancel_left' local.add_fzero_right local.diff_zero)
     
  lemma zero_le_minus_imp_le: "\<lbrakk> b \<le> a; f\<^sub>0(b) < a - b \<rbrakk> \<Longrightarrow> b < a"
    using local.less_iff local.minus_cancel_le by fastforce
  
  lemma le_imp_zero_le_minus: "\<lbrakk> b \<le> a; b < a \<rbrakk> \<Longrightarrow> f\<^sub>0(b) < a - b"
    by (metis local.add_fzero_right local.add_left_strict_mono local.diff_add_cancel_left')
 
  lemma le_iff_zero_leq_minus: "\<lbrakk> b \<le> a \<rbrakk> \<Longrightarrow> b < a \<longleftrightarrow> f\<^sub>0(b) < a - b"
    using zero_le_minus_imp_le le_imp_zero_le_minus by blast
      
  lemma le_and_minus_is_zero_imp_eq: "\<lbrakk> b < a \<and> a - b = f\<^sub>0(b)\<rbrakk> \<Longrightarrow> b = a"
    using local.less_iff le_imp_zero_le_minus by force
      
  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = f\<^sub>0(b) \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add by auto

  text \<open> Lemmas of CTA traces \<close>

  (* Sadd:unit *)
  lemma sadd_unit: "a + b = a \<longrightarrow> b = f\<^sub>0(b)"
    by (metis local.add.semigroup_axioms local.add_fzero_right local.add_left_imp_eq semigroup.assoc)
  
  (* SSub:same *)
  lemma ssub_same: "c \<le> a \<and> c \<le> b \<longrightarrow> a - c = b - c \<longleftrightarrow> a = b"
    by (metis local.diff_add_cancel_left')
      
  (* SSub:subsub *)    
  lemma ssub_subsub: "c \<le> a \<and> c \<le> b \<and> b \<le> a \<longrightarrow>(a - c) - (b - c) = a - b"
    by (metis local.diff_add_cancel_left' local.sum_minus_right)

end

text \<open> Following the approach in Trace_Algebra we define a @{term pre_trace} class,
       where in addition to satisfying @{term fzero_sum_zero}, and being a left cancellative
       semigroup, also requires @{term sum_eq_sum_conv}. \<close>
  
class fzero_pre_trace = semigroup_add_left_cancel_minus_ord  +
  assumes
  sum_eq_sum_conv: "(a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
begin

  text {* The set subtraces of a common trace $c$ is totally ordered *} 

  lemma le_common_total: "\<lbrakk> a \<le> c; b \<le> c \<rbrakk> \<Longrightarrow> a \<le> b \<or> b \<le> a"
    by (metis diff_add_cancel_left' le_add local.sum_eq_sum_conv)
  
  lemma le_sum_cases: "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a"
    by (simp add: le_common_total)
            
  lemma le_sum_cases':
    "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    apply auto
    using local.le_sum_cases apply auto[1]
    by (metis local.add_le_imp_le_left local.diff_add_cancel_left' local.le_sum_cases)
    
  lemma le_sum_iff: "a \<le> b + c \<longleftrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    by (metis local.add_le_imp_le_left local.add_left_mono local.diff_add_cancel_left' local.le_is_fzero_le local.le_sum_cases local.fzero_le_add local.fzero_le_trans)
   
end

instance fzero_pre_trace \<subseteq> semigroup_add_fzero
  by intro_classes  
 
text {* As stated earlier, there is no antisymmetry unless fzero
        is a constant. *}  
  
lemma fzero_monoid_le_antisym :
  fixes a :: "'a::{fzero_is_0,semigroup_add_left_cancel_minus_ord,fzero_sum_zero}"
  assumes "a \<le>\<^sub>u\<^sub>s b" "b \<le>\<^sub>u\<^sub>s a"
  shows "a = b"
proof -
  obtain a' where a': "b = a + a'"
    using assms(1) fzero_le_def by auto

  obtain b' where b': "a = b + b'"
    using assms(2) fzero_le_def by auto

  have "b' = (b' + a' + b')"
    by (metis a' add.assoc b' semigroup_add_left_cancel_class.add_left_imp_eq)
    
  hence "f\<^sub>0(b') + f\<^sub>0(b') + b' = (b' + a' + b')"
    by (metis add.semigroup_axioms add_fzero_left semigroup.assoc)
      
  hence "f\<^sub>0(b') + f\<^sub>0(b') = b' + a'"
    by (metis (no_types, lifting) add.assoc fzero_is_0 fzero_sum sadd_unit)
      
  hence "b' + a' = f\<^sub>0(b')"
    by (metis add_fzero_right fzero_is_0)
      
  hence "a' = f\<^sub>0(a')" "b' = f\<^sub>0(b')"
    using fzero_sum 
    using \<open>b' + a' = fzero b'\<close> fzero_sum_left by auto

  with a' b' show ?thesis
    by (metis add_fzero_right fzero_is_0)

qed

text \<open> We finally define the extended trace algebra that uses @{term f\<^sub>0}. \<close>

class fzero_trace = fzero_pre_trace + semigroup_add_left_cancel_minus_ord + fzero_sum_zero
begin
  -- \<open> The following lemma requires fzero_sum_zero. \<close>
  lemma neq_zero_impl_greater:
    "x \<noteq> f\<^sub>0(x) \<Longrightarrow> f\<^sub>0(x) < x"
    by (metis least_zero local.add_fzero_left local.diff_cancel local.fzero_sum_right local.less_iff sum_minus_left)
end
  
text {* This algebra forms a preorder. It turns out this is
        sufficient for the theories on reactive processes. *}  
  
instance fzero_trace \<subseteq> preorder
  by (intro_classes)
 
(* the following are properties satisfied by left/right restriction semigroups,
   but the fzero_trace class does not satisfy all of them. I do not think that
   properties related to commutativity are ever satisfied in the general case. *)    
    
lemma fzero_restrict0:
  fixes a :: "'a::fzero_trace"
  shows "f\<^sub>0(f\<^sub>0(a) + b) = f\<^sub>0(a) + f\<^sub>0(b)"
  by (metis add.assoc add_fzero_diff_cancel_left add_fzero_right)
  
lemma fzero_restrict1:
  fixes a :: "'a::fzero_trace"
  shows "f\<^sub>0(a) + b = b + f\<^sub>0(a + b)"
  by (metis add.assoc add_fzero_right semigroup_add_left_cancel_class.add_left_imp_eq)
  
lemma fzero_dist_plus:
  fixes a :: "'a::fzero_trace"
  shows "f\<^sub>0(a + b) = f\<^sub>0(a) + f\<^sub>0(b)"
  by (metis (no_types, lifting) fzero_idem fzero_restrict0 fzero_restrict1 semigroup_add_left_cancel_class.add_left_imp_eq)
 
lemma 
  fixes a :: "'a::fzero_trace"
  shows "f\<^sub>0(a + b) = f\<^sub>0(b)"
  by (metis add.assoc add_fzero_right semigroup_add_left_cancel_class.add_left_imp_eq)
    
lemma 
  fixes x :: "'a::fzero_trace"
  shows "(x + f\<^sub>0(x)) = x"
  by simp
    
lemma    
  fixes x :: "'a::fzero_trace"
    and y :: "'a::fzero_trace"
  shows "f\<^sub>0(x + y) = f\<^sub>0(f\<^sub>0(x)+y)"
  by (simp add: fzero_dist_plus)
    
lemma    
  fixes x :: "'a::fzero_trace"
    and y :: "'a::fzero_trace"
  shows "f\<^sub>0(f\<^sub>0(x) + f\<^sub>0(y)) = f\<^sub>0(y)+f\<^sub>0(x)+f\<^sub>0(y)"  
    by (metis (mono_tags, lifting) add.assoc fzero_dist_plus fzero_idem fzero_restrict1)
  
lemma    
  fixes x :: "'a::fzero_trace"
    and y :: "'a::fzero_trace"
  shows "f\<^sub>0(x) + f\<^sub>0(x) = f\<^sub>0(x)"
  by (metis add_fzero_right fzero_idem)
    
end
