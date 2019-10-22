section {* Monoid variants and extra properties *}

theory Monoid_extra
  imports List_extra "~~/src/HOL/Library/Prefix_Order"
begin

class ordered_semigroup = semigroup_add + order +
  assumes add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
  and add_right_mono: "a \<le> b \<Longrightarrow> a + c \<le> b + c"
begin

lemma add_mono:
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d"
  using local.add_left_mono local.add_right_mono local.order.trans by blast

end
  
class left_cancel_semigroup = plus +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
    
class left_cancel_monoid = monoid_add + left_cancel_semigroup
    
class right_cancel_semigroup = plus +
  assumes add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"

class right_cancel_monoid = monoid_add + right_cancel_semigroup
    
class monoid_sum_0 = monoid_add +
  assumes zero_sum_left: "a + b = 0 \<Longrightarrow> a = 0" 
begin

lemma zero_sum_right: "a + b = 0 \<Longrightarrow> b = 0"
  by (metis local.add_0_left local.zero_sum_left)

lemma zero_sum: "a + b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  by (metis local.add_0_right zero_sum_right)
end

context monoid_add
begin

definition monoid_le (infix "\<le>\<^sub>m" 50)
where "a \<le>\<^sub>m b \<longleftrightarrow> (\<exists>c. b = a + c)"

definition monoid_subtract (infixl "-\<^sub>m" 65)
where "a -\<^sub>m b = (if (b \<le>\<^sub>m a) then THE c. a = b + c else 0)"

end

class pre_trace = left_cancel_semigroup + monoid_sum_0 +
  assumes
  sum_eq_sum_conv: "(a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
begin
  
lemma monoid_le_least_zero: "0 \<le>\<^sub>m a"
    by (metis local.add_0_left local.monoid_le_def)

lemma monoid_le_refl: "a \<le>\<^sub>m a"
  apply (simp add: monoid_le_def)
    by (metis local.sum_eq_sum_conv)

lemma monoid_le_trans: "\<lbrakk> a \<le>\<^sub>m b; b \<le>\<^sub>m c \<rbrakk> \<Longrightarrow> a \<le>\<^sub>m c"
  by (metis add.assoc monoid_le_def)

lemma monoid_le_antisym:
  assumes "a \<le>\<^sub>m b" "b \<le>\<^sub>m a"
  shows "a = b"
proof -
  obtain a' where a': "b = a + a'"
    using assms(1) monoid_le_def by auto

  obtain b' where b': "a = b + b'"
    using assms(2) monoid_le_def by auto

  have "b' = (b' + a' + b')"
    by (metis a' add_assoc b' local.add_left_imp_eq)

  hence "0 + 0 + b' = (b' + a' + b')"
    using add_assoc by auto
     
  hence "0 + 0 = b' + a'"
    by (metis add_assoc local.add_0_right local.add_left_imp_eq)
      
  hence "b' + a' = 0"
    by simp
      
  hence "a' = 0" "b' = 0"
    using local.zero_sum by blast+

  with a' b' show ?thesis
    by simp
qed

lemma monoid_le_add: "a \<le>\<^sub>m a + b"
  by (auto simp add: monoid_le_def)

lemma monoid_le_add_left_mono: "a \<le>\<^sub>m b \<Longrightarrow> c + a \<le>\<^sub>m c + b"
  using add_assoc by (auto simp add: monoid_le_def)

lemma add_monoid_diff_cancel_left [simp]: "(a + b) -\<^sub>m a = b"
  apply (simp add: monoid_subtract_def monoid_le_add)
  apply (rule the_equality)
  apply (simp)
  using local.add_left_imp_eq apply blast
done

end
  
class trace = pre_trace + ord + minus +
  assumes le_is_monoid_le: "a \<le> b \<longleftrightarrow> (a \<le>\<^sub>m b)"
  and less_iff: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)"
  and minus_def: "a - b = a -\<^sub>m b"
begin

  lemma le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists> c. b = a + c)"
    by (simp add: local.le_is_monoid_le local.monoid_le_def)

  lemma least_zero [simp]: "0 \<le> a"
    by (simp add: local.le_is_monoid_le local.monoid_le_least_zero)

  lemma le_add [simp]: "a \<le> a + b"
    by (simp add: le_is_monoid_le local.monoid_le_add)

  lemma not_le_minus [simp]:  "\<not> (a \<le> b) \<Longrightarrow> b - a = 0"
    by (simp add: le_is_monoid_le local.minus_def local.monoid_subtract_def)

  lemma add_diff_cancel_left [simp]: "(a + b) - a = b"
    by (simp add: minus_def)

  lemma diff_zero [simp]: "a - 0 = a"
    by (metis local.add_0_left local.add_diff_cancel_left)
 
  lemma diff_cancel [simp]: "a - a = 0"
    by (metis local.add_0_right local.add_diff_cancel_left)

  lemma add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by (simp add: local.le_is_monoid_le local.monoid_le_add_left_mono)

  lemma add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"
    by (auto simp add: le_iff_add, metis add_assoc local.add_diff_cancel_left)
      
  lemma add_diff_cancel_left' [simp]:  "(c + a) - (c + b) = a - b"
  proof (cases "b \<le> a")
    case True thus ?thesis
      by (metis add_assoc local.add_diff_cancel_left local.le_iff_add)
  next
    case False thus ?thesis
      using local.add_le_imp_le_left not_le_minus by metis
  qed
    
  lemma zero_le_minus_imp_le: "\<lbrakk> b \<le> a; 0 < a - b \<rbrakk> \<Longrightarrow> b < a"
    by (smt local.add.semigroup_axioms local.add_monoid_diff_cancel_left local.le_iff_add local.less_iff local.minus_def semigroup.assoc)

  lemma le_imp_zero_le_minus: "\<lbrakk> b \<le> a; b < a \<rbrakk> \<Longrightarrow> 0 < a - b"
    by (metis local.add_0_right local.add_diff_cancel_left local.add_le_imp_le_left local.add_left_mono local.le_iff_add local.less_iff)
  
  lemma le_iff_zero_leq_minus: "\<lbrakk> b \<le> a \<rbrakk> \<Longrightarrow> b < a \<longleftrightarrow> 0 < a - b"
    using zero_le_minus_imp_le le_imp_zero_le_minus by blast
      
  lemma le_and_minus_is_zero_imp_eq: "\<lbrakk> b < a \<and> a - b = 0\<rbrakk> \<Longrightarrow> b = a"
    using local.less_iff le_imp_zero_le_minus by force

  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = 0 \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add by auto
 
  lemma diff_add_cancel_left': "a \<le> b \<Longrightarrow> a + (b - a) = b"
    using local.le_iff_add local.monoid_le_def by auto

  lemma add_left_strict_mono: "\<lbrakk> a + b < a + c \<rbrakk> \<Longrightarrow> b < c"
    using local.add_le_imp_le_left local.add_left_mono local.less_iff by blast
      
  lemma sum_minus_left: "c \<le> a \<Longrightarrow> (a + b) - c = (a - c) + b"
    by (metis add_assoc diff_add_cancel_left' local.add_monoid_diff_cancel_left local.minus_def)      
     
  lemma neq_zero_impl_greater:
    "x \<noteq> 0 \<Longrightarrow> 0 < x"
    by (metis least_zero local.add_0_left local.diff_cancel local.less_iff local.zero_sum_left sum_minus_left)

  lemma minus_cancel_le:
    "\<lbrakk> x \<le> y; y \<le> z \<rbrakk> \<Longrightarrow> y - x \<le> z - x"
    using add_assoc le_iff_add by auto

  text {* The set subtraces of a common trace $c$ is totally ordered *} 
  lemma le_common_total: "\<lbrakk> a \<le> c; b \<le> c \<rbrakk> \<Longrightarrow> a \<le> b \<or> b \<le> a"
    by (metis diff_add_cancel_left' le_add local.sum_eq_sum_conv)
  
  lemma le_sum_cases: "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a"
    by (simp add: le_common_total)
            
  lemma le_sum_cases':
    "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    by (auto, metis le_sum_cases, metis minus_def le_is_monoid_le add_monoid_diff_cancel_left monoid_le_def sum_eq_sum_conv)

  lemma le_sum_iff: "a \<le> b + c \<longleftrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    by (metis le_sum_cases' add_monoid_diff_cancel_left le_is_monoid_le minus_def monoid_le_add_left_mono monoid_le_def monoid_le_trans)
    
  lemma sum_minus_right: "c \<ge> a \<Longrightarrow> a + b - c = b - (c - a)"
    by (metis diff_add_cancel_left' local.add_diff_cancel_left')
      
end

instance trace \<subseteq> order
  apply (intro_classes)
  apply (simp_all add: less_iff le_is_monoid_le monoid_le_refl)
  using monoid_le_trans apply blast
  apply (simp add: monoid_le_antisym)
  done
    

instantiation list :: (type) monoid_add
begin

  definition zero_list :: "'a list" where "zero_list = []"
  definition plus_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where "plus_list = op @"

instance
  by (intro_classes, simp_all add: zero_list_def plus_list_def)
end
  

lemma monoid_le_list:
  "(xs :: 'a list) \<le>\<^sub>m ys \<longleftrightarrow> xs \<le> ys"
  apply (simp add: monoid_le_def plus_list_def)
  using Prefix_Order.prefixE Prefix_Order.prefixI apply blast
done

lemma monoid_subtract_list:
  "(xs :: 'a list) -\<^sub>m ys = xs - ys"
  apply (auto simp add: monoid_subtract_def monoid_le_list minus_list_def less_eq_list_def)
  apply (rule the_equality)
  apply (simp_all add: zero_list_def plus_list_def prefix_drop)
done

instance list :: (type) trace
  apply (intro_classes, simp_all add: zero_list_def plus_list_def monoid_le_def monoid_subtract_list)
  apply (simp add: append_eq_append_conv2)
  using Prefix_Order.prefixE Prefix_Order.prefixI apply blast
  apply (simp add: less_list_def)
  done
    
lemma monoid_le_nat:
  "(x :: nat) \<le>\<^sub>m y \<longleftrightarrow> x \<le> y"
  by (simp add: monoid_le_def nat_le_iff_add)

lemma monoid_subtract_nat:
  "(x :: nat) -\<^sub>m y = x - y"
  by (auto simp add: monoid_subtract_def monoid_le_nat)

instance nat :: trace
  apply (intro_classes, simp_all add: monoid_subtract_nat)
  apply (metis Nat.diff_add_assoc Nat.diff_add_assoc2 add_diff_cancel_right' add_le_cancel_left add_le_cancel_right add_less_mono cancel_ab_semigroup_add_class.add_diff_cancel_left' less_irrefl not_le)
  apply (simp add: nat_le_iff_add monoid_le_def)
  apply linarith+
  done
    
text \<open> In this theory we present a variant of the trace algebra where instead of
       a partial order we have a preorder. This is possible by generalising the
       zero of the monoid-based trace algebra and dropping anti-symmetry.
       Effectively we have a left-cancellative unary semigroup whose unary
       function @{term f\<^sub>0} is idempotent.  \<close>

subsection \<open> Unary fzero \<close>

text \<open> We call the unitary function fzero @{term f\<^sub>0}, that is, a functional zero
       when compared to the monoid-based trace algebra. \<close>
  
class fzero = 
  fixes fzero :: "'a \<Rightarrow> 'a" ("f0'(_')")

class fzero_idem = fzero +
  assumes fzero_idem[simp]: "f0(f0(a)) = f0(a)"    

text \<open> The monoid-based trace algebra can be obtained by fixing @{term f\<^sub>0} as 0.
       We explore this in the trace algebra hierarchy theory file \<close>
    
class fzero_is_0 = fzero + zero +
  assumes fzero_is_0: "f0(a) = 0"

text \<open> If we admit @{term f\<^sub>0} to be the identity, then we obtain a semigroup that
       belongs to the class of U-semigroups. In particular, when combined with the
       trace algebra presented in this theory, we obtain a *-semigroup. \<close>

class fzero_ident = fzero +
  assumes fzero_ident: "f0(a) = a"

subsection \<open> Unary fzero semigroup \<close>

text \<open> The class of semigroups with a unary function is then defined. \<close>

class semigroup_add_fzero = semigroup_add + fzero
    
text \<open> We then define mirror properties of a monoid, but instead we
       require the zero property on fzero, rather than 0. \<close>
    
class fzero_add_zero = fzero_idem + semigroup_add_fzero +
  assumes add_fzero_left[simp]: "f0(a) + a = a"
  assumes add_fzero_right[simp]: "a + f0(a) = a"

class fzero_add_zero_any = fzero_add_zero +
    assumes add_fzero_any_left[simp]: "f0(b) + a = a"

instance fzero_add_zero_any \<subseteq> fzero_add_zero
  by (intro_classes)
      
text \<open> In this algebra we only require zero_sum_right, but not
        zero_sum_left. The immediate consequence is that we do
        not obtain an order as there is no anti-symmetry. \<close>
    
class fzero_sum_zero = fzero_add_zero +
  assumes fzero_sum_right: "a + b = f0(b) \<Longrightarrow> b = f0(b)"
    
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
  shows "a + b = f0(a) \<Longrightarrow> a = f0(a)"
  by (metis fzero_add_zero_class.add_fzero_right fzero_sum_right fzero_is_0)
    
lemma fzero_sum:
  fixes a :: "'a::{fzero_is_0,fzero_sum_zero}"
  shows "a + b = f0(a) \<longleftrightarrow> a = f0(a) \<and> b = f0(b)"
  by (metis add_fzero_left fzero_is_0 fzero_sum_left)    

text \<open> We define less and minus in terms of plus in the context of the class fzero_add_zero
       as this is sufficient to define a prefix relation that is reflexive and transitive. \<close>

context fzero_add_zero
begin
  
definition fzero_le (infix "\<le>us" 50)
  where "a \<le>us b \<longleftrightarrow> (\<exists>c. b = a + c)"

definition fzero_subtract (infixl "-us" 65)
  where "a -us b = (if (b \<le>us a) then THE c. a = b + c else f0(a))"  
    
lemma fzero_refl:
  "a \<le>us a"
  by (metis fzero_le_def local.add_fzero_right)
    
lemma fzero_le_trans: 
  "\<lbrakk> a \<le>us b; b \<le>us c \<rbrakk> \<Longrightarrow> a \<le>us c"
  unfolding fzero_le_def
  using add_assoc by blast

lemma fzero_le_least_fzero: "fzero a \<le>us a"
  by (metis local.add_fzero_left local.fzero_le_def)
   
lemma fzero_le_add: "a \<le>us a + b"
  using fzero_le_def
  by blast

lemma fzero_le_add_left_mono: 
  "a \<le>us b \<Longrightarrow> c + a \<le>us c + b"
  using fzero_le_def
  using add_assoc by auto

end

text \<open> The following class allows @term{\<le>}, @term{<} and @term{-} to be related with
       that of fzero_add_zero. \<close>

class fzero_add_fzero_ord = fzero_add_zero + ord + 
  assumes le_is_fzero_le: "a \<le> b \<longleftrightarrow> (a \<le>us b)"
  and less_iff: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)"
  
class fzero_add_fzero_ord_minus = fzero_add_fzero_ord + ord + minus +
  assumes minus_def: "a - b = a -us b"

text \<open> We then show we have a preorder. \<close>

instance fzero_add_fzero_ord \<subseteq> preorder
proof
  fix x y z :: "'a::fzero_add_fzero_ord" 
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_iff)
  show "x \<le> x"
    by (simp add: fzero_add_zero_class.fzero_refl le_is_fzero_le)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using le_is_fzero_le 
    by (metis fzero_add_zero_class.fzero_le_trans)
qed

subsection \<open> Unary left-cancellative fzero semigroup class \<close>
  
class semigroup_add_left_cancel = semigroup_add +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"

class fzero_add_left_cancel = semigroup_add_left_cancel + fzero_add_zero 
begin
  
lemma add_fzero_diff_cancel_left [simp]: 
  "(a + b) -us a = b"
  apply (simp add: fzero_subtract_def fzero_le_add)
  apply (rule the_equality)
   apply (simp)
    using local.add_left_imp_eq by blast
    
lemma add_le_imp_le_left:
  "c + a \<le>us c + b \<Longrightarrow> a \<le>us b"
  unfolding fzero_le_def
  by (metis add_assoc local.add_left_imp_eq)

lemma diff_add_cancel_left': "a \<le>us b \<Longrightarrow> a + (b -us a) = b"
  using local.fzero_subtract_def
  by (metis add_fzero_diff_cancel_left local.fzero_le_def)

lemma "b \<le>us a \<Longrightarrow> x = a -us b \<longleftrightarrow> b + x = a"
  by (metis diff_add_cancel_left' local.add_left_imp_eq)

end 
  
class fzero_add_zero_any_left_cancel = fzero_add_left_cancel + fzero_add_zero_any
  
class semigroup_add_left_cancel_minus_ord = fzero_add_fzero_ord_minus + fzero_add_left_cancel
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

  lemma least_zero [simp]: "f0(a) \<le> b"
    by (metis local.add.semigroup_axioms local.add_fzero_right local.add_left_imp_eq local.le_iff_add semigroup.assoc)

  (* TODO: Check this still works in CTA theory *)
  lemma not_le_minus [simp]:  "\<not> (a \<le> b) \<Longrightarrow> b - a = f0(b)"
    by (simp add: local.fzero_subtract_def local.le_is_fzero_le local.minus_def)
      
  lemma diff_zero [simp]: "a - f0(b) = a"
    by (metis local.add.semigroup_axioms local.add_fzero_right local.diff_add_cancel_left' local.fzero_idem local.least_zero semigroup.assoc)
       
  lemma diff_cancel [simp]: "a - a = f0(a)"
    by (metis local.add_diff_cancel_left' local.add_fzero_right local.diff_zero)
     
  lemma zero_le_minus_imp_le: "\<lbrakk> b \<le> a; f0(b) < a - b \<rbrakk> \<Longrightarrow> b < a"
    using local.less_iff local.minus_cancel_le by fastforce
  
  lemma le_imp_zero_le_minus: "\<lbrakk> b \<le> a; b < a \<rbrakk> \<Longrightarrow> f0(b) < a - b"
    by (metis local.add_fzero_right local.add_left_strict_mono local.diff_add_cancel_left')
 
  lemma le_iff_zero_leq_minus: "\<lbrakk> b \<le> a \<rbrakk> \<Longrightarrow> b < a \<longleftrightarrow> f0(b) < a - b"
    using zero_le_minus_imp_le le_imp_zero_le_minus by blast
      
  lemma le_and_minus_is_zero_imp_eq: "\<lbrakk> b < a \<and> a - b = f0(b)\<rbrakk> \<Longrightarrow> b = a"
    using local.less_iff le_imp_zero_le_minus by force
      
  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = f0(b) \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add by auto

  text \<open> Lemmas of CTA traces \<close>

  (* Sadd:unit *)
  lemma sadd_unit: "a + b = a \<longrightarrow> b = f0(b)"
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
  assumes "a \<le>us b" "b \<le>us a"
  shows "a = b"
proof -
  obtain a' where a': "b = a + a'"
    using assms(1) fzero_le_def by auto

  obtain b' where b': "a = b + b'"
    using assms(2) fzero_le_def by auto

  have "b' = (b' + a' + b')"
    by (metis a' add.assoc b' semigroup_add_left_cancel_class.add_left_imp_eq)
    
  hence "f0(b') + f0(b') + b' = (b' + a' + b')"
    by (metis add.semigroup_axioms add_fzero_left semigroup.assoc)
      
  hence "f0(b') + f0(b') = b' + a'"
    by (metis (no_types, lifting) add.assoc fzero_is_0 fzero_sum sadd_unit)
      
  hence "b' + a' = f0(b')"
    by (metis add_fzero_right fzero_is_0)
      
  hence "a' = f0(a')" "b' = f0(b')"
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
    "x \<noteq> f0(x) \<Longrightarrow> f0(x) < x"
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
  shows "f0(f0(a) + b) = f0(a) + f0(b)"
  by (metis add.assoc add_fzero_diff_cancel_left add_fzero_right)
  
lemma fzero_restrict1:
  fixes a :: "'a::fzero_trace"
  shows "f0(a) + b = b + f0(a + b)"
  by (metis add.assoc add_fzero_right semigroup_add_left_cancel_class.add_left_imp_eq)
  
lemma fzero_dist_plus:
  fixes a :: "'a::fzero_trace"
  shows "f0(a + b) = f0(a) + f0(b)"
  by (metis (no_types, lifting) fzero_idem fzero_restrict0 fzero_restrict1 semigroup_add_left_cancel_class.add_left_imp_eq)
 
lemma 
  fixes a :: "'a::fzero_trace"
  shows "f0(a + b) = f0(b)"
  by (metis add.assoc add_fzero_right semigroup_add_left_cancel_class.add_left_imp_eq)
    
lemma 
  fixes x :: "'a::fzero_trace"
  shows "(x + f0(x)) = x"
  by simp
    
lemma    
  fixes x :: "'a::fzero_trace"
    and y :: "'a::fzero_trace"
  shows "f0(x + y) = f0(f0(x)+y)"
  by (simp add: fzero_dist_plus)
    
lemma    
  fixes x :: "'a::fzero_trace"
    and y :: "'a::fzero_trace"
  shows "f0(f0(x) + f0(y)) = f0(y)+f0(x)+f0(y)"  
    by (metis (mono_tags, lifting) add.assoc fzero_dist_plus fzero_idem fzero_restrict1)
  
lemma    
  fixes x :: "'a::fzero_trace"
    and y :: "'a::fzero_trace"
  shows "f0(x) + f0(x) = f0(x)"
  by (metis add_fzero_right fzero_idem)
    
class fzero_is_0_sum_zero = fzero_is_0 + fzero_sum_zero

instance fzero_is_0_sum_zero \<subseteq> monoid_sum_0
  apply intro_classes
  apply (metis add_fzero_left fzero_is_0)
  apply (metis add_fzero_right fzero_is_0)
  by (metis fzero_is_0 fzero_sum)

text \<open> A semigroup trace with a fixed zero (@{term fzero_is_0}) 
       is a monoid. \<close>

class fzero_trace_0 = fzero_trace + fzero_is_0

instance fzero_trace_0 \<subseteq> monoid_add
proof
  fix a :: "'a::fzero_trace_0"
  show add_fzero_left: 
    "0 + a = a"
    by (metis add_fzero_right fzero_is_0 fzero_restrict1)
  show add_zero_right: 
    "a + 0 = a"
    by (metis add_fzero_right fzero_is_0)
qed

text \<open> A semigroup trace with a fixed zero (@{term fzero_is_0}) 
       is a monoid trace. \<close>

instance fzero_trace_0 \<subseteq> trace 
proof
  fix a b c d :: "'a::fzero_trace_0"
  show left_cancellative: 
    "a + b = a + c \<Longrightarrow> b = c"
    using semigroup_add_left_cancel_class.add_left_imp_eq by blast
  show sum_left_zero:
    "a + b = 0 \<Longrightarrow> a = 0"
    by (metis add.right_neutral add_fzero_right fzero_sum_left semigroup_add_left_cancel_class.add_left_imp_eq)
  show sum_eq_conv:
    "a + b = c + d \<Longrightarrow> \<exists>e. a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
    by (simp add: fzero_pre_trace_class.sum_eq_sum_conv)
  show monoid_le:
    "(a \<le> b) = (a \<le>\<^sub>m b)"
    by (simp add: monoid_le_def semigroup_add_left_cancel_minus_ord_class.le_iff_add)
  show less:
    "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    by (simp add: fzero_add_fzero_ord_class.less_iff)
  show minus:
    "a - b = a -\<^sub>m b"
    by (metis fzero_add_fzero_ord_minus_class.minus_def fzero_is_0 fzero_subtract_def le_is_fzero_le monoid_le_def monoid_subtract_def semigroup_add_left_cancel_minus_ord_class.le_iff_add)
qed

text \<open> Similarly, a trace which has a fixed @{term f\<^sub>0} is a semigroup satisfying the 
       mirror properties of a monoid. \<close>

class trace_fzero_0 = trace + fzero_is_0

instance trace_fzero_0 \<subseteq> fzero_add_zero
proof
  fix a b :: "'a::trace_fzero_0"
  show "f0(f0(a)) = f0(a)"
    by (simp add: fzero_is_0)
  show "f0(b) + a = a"
    by (simp add: fzero_is_0)
  show "a + f0(a) = a"
    by (simp add: fzero_is_0)
qed

text \<open> Hence such a trace is also a semigroup trace. \<close>

instance trace_fzero_0 \<subseteq> fzero_trace
proof
  fix a b c d :: "'a::trace_fzero_0"
  show "(a \<le> b) = (a \<le>us b)"
    by (simp add: fzero_le_def trace_class.le_iff_add)
  show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    by (simp add: trace_class.less_iff)
  show "a - b = a -us b"
    by (metis fzero_is_0 fzero_le_def fzero_subtract_def le_is_monoid_le monoid_subtract_def trace_class.le_iff_add trace_class.minus_def)
  show "a + b = a + c \<Longrightarrow> b = c"
    by (metis left_cancel_semigroup_class.add_left_imp_eq)
  show "a + b = c + d \<Longrightarrow> \<exists>e. a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
    by (simp add: pre_trace_class.sum_eq_sum_conv)
  show "a + b = f0(b) \<Longrightarrow> b = f0(b)"
    by (simp add: fzero_is_0 zero_sum_right)
qed

text \<open> Therefore, a semigroup trace with a fixed @{term f\<^sub>0} is exactly the same as the
       monoid trace. This is convenient as any type instantiated with the class @{class trace}
       can also be instantiated with the class @{class fzero_trace} by defining an appropriate
       @{term f\<^sub>0}. \<close>
  
  
class fzero_add_any_pre_trace = fzero_add_zero_any_left_cancel + fzero_pre_trace  
  
class fzero_add_any_trace = fzero_add_zero_any + fzero_trace   
  
instance fzero_add_any_trace \<subseteq> fzero_add_any_pre_trace
  by intro_classes  
    
instance trace_fzero_0 \<subseteq> fzero_add_zero_any
  apply intro_classes
  by (simp add: fzero_is_0)
    
section \<open> Models \<close>

subsection \<open> Lists \<close>

instantiation list :: (type) fzero_is_0
begin
  definition fzero_list :: "'a list \<Rightarrow> 'a list" where "fzero_list a = []"

  instance by (intro_classes, simp add:fzero_list_def zero_list_def)
end
    
instantiation list :: (type) fzero_add_zero
begin
 
  instance by (intro_classes, simp_all add:fzero_list_def plus_list_def)
end
    
lemma fzero_le_list:
  "(xs :: 'a list) \<le>us ys \<longleftrightarrow> xs \<le> ys"
  apply (simp add: fzero_le_def plus_list_def)
  using Prefix_Order.prefixE Prefix_Order.prefixI by blast
    
lemma fzero_subtract_list:
  "(xs :: 'a list) -us ys = xs - ys"
  proof (cases "ys \<le> xs")
    case True
    then show ?thesis 
      apply (auto simp add: fzero_subtract_def fzero_le_list minus_list_def less_eq_list_def)
      apply (rule the_equality)
      by (simp_all add: fzero_list_def plus_list_def prefix_drop)
  next
    case False then show ?thesis
      by (simp add: fzero_is_0 fzero_le_list fzero_subtract_def)
  qed

instance list :: (type) trace_fzero_0
  by intro_classes

subsection \<open> Naturals \<close>

instantiation nat :: fzero_is_0
begin
  
  definition fzero_nat :: "nat \<Rightarrow> nat" where "fzero_nat a = 0"
 
  instance
    by (intro_classes, auto simp add:fzero_nat_def)
end
  
instantiation nat :: fzero_add_zero
begin
  instance by (intro_classes, simp_all add:fzero_nat_def)
end
  
lemma fzero_le_nat:
  "(x :: nat) \<le>us y \<longleftrightarrow> x \<le> y"
  by (simp add: fzero_le_def trace_class.le_iff_add)
  
lemma fzero_subtract_nat:
  "(x :: nat) -us y = x - y"
  by (auto simp add:fzero_subtract_def fzero_le_nat fzero_nat_def) 

instance nat :: trace_fzero_0
  by intro_classes

instance nat :: fzero_trace
  by intro_classes
  
end
