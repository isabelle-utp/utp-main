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
    
subsection {* Trace algebra based on left-cancellative unitary semigroup whose
  unitary function is idempotent. *}
  


text {* We call the unitary function fzero (as in a functional zero
        when compared to the monoid-based trace algebra). *}
  
class fzero = 
  fixes fzero :: "'a \<Rightarrow> 'a"
    
class semigroup_add_fzero = semigroup_add + fzero

class fzero_idem = fzero +
  assumes fzero_idem[simp]: "fzero (fzero a) = fzero a"    
    
text {* The class of the monoid-based trace algebra can be obtained
        by fixing fzero as 0. *}     
    
class fzero_is_0 = fzero + zero +
  assumes fzero_is_0: "fzero a = 0"

text {* Another algebra is likely obtained by considering the identity
        function. *}

class fzero_ident = fzero +
  assumes fzero_ident: "fzero a = a"
    
text {* We then define mirror properties of a monoid, but instead we
        require the zero property on fzero, rather than 0. *}    
    
class fzero_add_zero = fzero_idem + semigroup_add_fzero +
  assumes add_fzero_left[simp]: "(fzero a) + a = a"
  assumes add_fzero_right[simp]: "a + (fzero a) = a"
    
text {* In this algebra we only require zero_sum_right, but not
        zero_sum_left. The immediate consequence is that we do
        not obtain an order as there is no anti-symmetry. *}
    
class fzero_sum_zero = fzero_add_zero +
  assumes fzero_sum_right: "a + b = (fzero b) \<Longrightarrow> (b = fzero b)"
    
instance fzero_sum_zero \<subseteq> fzero_add_zero
  by intro_classes  
  
instance fzero_add_zero \<subseteq> semigroup_add_fzero
  by intro_classes
    
instance fzero_sum_zero \<subseteq> semigroup_add_fzero
  by intro_classes    
    
text {* However, when we restrict the class to fzero_is_0, then
        trivially we have that sum_left and sum properties are
        satisfied as expected. *}    
    
lemma fzero_sum_left:
  fixes a :: "'a::{fzero_is_0,fzero_sum_zero}"
  shows "a + b = fzero a \<Longrightarrow> a = fzero a"
  by (metis fzero_add_zero_class.add_fzero_right fzero_sum_right fzero_is_0)
    
lemma fzero_sum:
  fixes a :: "'a::{fzero_is_0,fzero_sum_zero}"
  shows "a + b = fzero a \<longleftrightarrow> a = fzero a \<and> b = fzero b"
  by (metis add_fzero_left fzero_is_0 fzero_sum_left)    
    
class fzero_is_0_sum_zero = fzero_is_0 + fzero_sum_zero

instance fzero_is_0_sum_zero \<subseteq> monoid_sum_0
  apply intro_classes
  apply (metis add_fzero_left fzero_is_0)
  apply (metis add_fzero_right fzero_is_0)
  by (metis fzero_is_0 fzero_sum)
  
text {* We also define the less operator and minus in terms of
        plus. *}  
  

    
context semigroup_add
begin
  
definition fzero_le (infix "\<le>\<^sub>d" 50)
  where "a \<le>\<^sub>d b \<longleftrightarrow> (\<exists>c. b = a + c)"
    
lemma monoid_le_trans: 
  "\<lbrakk> a \<le>\<^sub>d b; b \<le>\<^sub>d c \<rbrakk> \<Longrightarrow> a \<le>\<^sub>d c"
  using add_assoc local.fzero_le_def by auto
    
lemma monoid_le_add: "a \<le>\<^sub>d a + b"
  by (auto simp add: fzero_le_def)

lemma monoid_le_add_left_mono: 
  "a \<le>\<^sub>d b \<Longrightarrow> c + a \<le>\<^sub>d c + b"
  using add_assoc local.fzero_le_def by auto
    
end
  
context semigroup_add_fzero
begin
 
definition fzero_subtract (infixl "-\<^sub>d" 65)
  where "a -\<^sub>d b = (if (b \<le>\<^sub>d a) then THE c. a = b + c else fzero a)"  
    
end
  
text {* We then define an equivalent class as a pre_trace, where
        in addition to satisfying fzero_sum_zero, and being a left
        cancellative semigroup, we also require sum_eq_sum_conv. *}

context fzero_add_zero
begin
  
lemma monoid_le_least_zero: "fzero a \<le>\<^sub>d a"
  by (metis local.add_fzero_left local.monoid_le_add)
 
lemma monoid_le_refl: "a \<le>\<^sub>d a"
  apply (simp add: local.fzero_le_def)
  by (metis local.add_fzero_right)
    

end
  
class fzero_pre_trace = left_cancel_semigroup + fzero_sum_zero +
  assumes
  sum_eq_sum_conv: "(a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
begin
  
  (* still unsure whether this should be moved into another class *)
lemma add_monoid_diff_cancel_left [simp]: 
  "(a + b) -\<^sub>d a = b"
  apply (simp add: fzero_subtract_def monoid_le_add)
  apply (rule the_equality)
  apply (simp)
  using left_cancel_semigroup_class.add_left_imp_eq 
  by (metis local.add_left_imp_eq)
end
  
instance fzero_pre_trace \<subseteq> semigroup_add_fzero
  by intro_classes  
 
text {* As stated earlier, there is no antisymmetry unless fzero
        is a constant. *}  
  
lemma fzero_monoid_le_antisym :
  fixes a :: "'a::{fzero_is_0,fzero_pre_trace}"
  assumes "a \<le>\<^sub>d b" "b \<le>\<^sub>d a"
  shows "a = b"
proof -
  obtain a' where a': "b = a + a'"
    using assms(1) fzero_le_def by auto

  obtain b' where b': "a = b + b'"
    using assms(2) fzero_le_def by auto

  have "b' = (b' + a' + b')"
    by (metis a' add.semigroup_axioms b' left_cancel_semigroup_class.add_left_imp_eq semigroup.assoc)

  hence "fzero b' + fzero b' + b' = (b' + a' + b')"
    by (metis add.semigroup_axioms add_fzero_left semigroup.assoc)
      
  hence "fzero b' + fzero b' = b' + a'"
    by (metis (no_types, lifting) add.semigroup_axioms add_fzero_right fzero_is_0 left_cancel_semigroup_class.add_left_imp_eq semigroup.assoc)
      
  hence "b' + a' = fzero b'"
    by (metis add_fzero_right fzero_is_0)
      
  hence "a' = fzero a'" "b' = fzero b'"
    using fzero_sum apply blast
    using \<open>b' + a' = fzero b'\<close> fzero_sum_left by auto

  with a' b' show ?thesis
    by (metis add_fzero_right fzero_is_0)

qed
  
text {* We then define the trace algebra using fzero. We reprove
        properties of the monoid-based trace algebra. *}  

class fzero_trace = fzero_pre_trace + ord + minus +
  assumes le_is_fzero_le: "a \<le> b \<longleftrightarrow> (a \<le>\<^sub>d b)"
  and less_iff: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)"
  and minus_def: "a - b = a -\<^sub>d b"
begin
  
  lemma le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists> c. b = a + c)"
    by (simp add: local.fzero_le_def local.le_is_fzero_le)

  lemma least_zero [simp]: 
     "fzero a \<le> b"
     by (metis local.add.semigroup_axioms local.add_fzero_right local.add_left_imp_eq local.le_iff_add semigroup.assoc)
    
  lemma le_add [simp]:
    "a \<le> a + b"
    using local.le_iff_add by blast
   
  lemma not_le_minus [simp]:  "\<not> (a \<le> b) \<Longrightarrow> b - a = fzero b"
    by (simp add: fzero_subtract_def local.le_is_fzero_le local.minus_def)

  lemma add_diff_cancel_left [simp]: 
    "(a + b) - a = b"
    by (simp add: minus_def)
      
  lemma diff_zero [simp]: "a - fzero b = a"
    by (metis add_assoc local.add_diff_cancel_left local.add_fzero_right)
       
  lemma diff_cancel [simp]: "a - a = fzero a"
    by (metis local.add_fzero_right local.add_diff_cancel_left)
      
  lemma add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by (simp add: local.le_is_fzero_le local.monoid_le_add_left_mono)

  lemma add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"
    by (auto simp add: le_iff_add, metis add_assoc local.add_diff_cancel_left)
      
  lemma add_diff_cancel_left' [simp]:  "(c + a) - (c + b) = a - b"
  proof (cases "b \<le> a")
    case True thus ?thesis
      by (metis add_assoc local.add_diff_cancel_left local.le_iff_add)
  next
    case False thus ?thesis
      using local.add_le_imp_le_left not_le_minus 
      by (metis add_assoc local.add_fzero_right local.add_monoid_diff_cancel_left)
  qed
   
  lemma zero_le_minus_imp_le: "\<lbrakk> b \<le> a; fzero b < a - b \<rbrakk> \<Longrightarrow> b < a"
    by (smt local.add.semigroup_axioms local.add_monoid_diff_cancel_left local.le_iff_add local.less_iff local.minus_def semigroup.assoc)

  lemma le_imp_zero_le_minus: "\<lbrakk> b \<le> a; b < a \<rbrakk> \<Longrightarrow> fzero b < a - b"
    by (metis local.add_fzero_right local.add_diff_cancel_left local.add_le_imp_le_left local.add_left_mono local.le_iff_add local.less_iff)
 
  lemma le_iff_zero_leq_minus: "\<lbrakk> b \<le> a \<rbrakk> \<Longrightarrow> b < a \<longleftrightarrow> fzero b < a - b"
    using zero_le_minus_imp_le le_imp_zero_le_minus by blast
      
  lemma le_and_minus_is_zero_imp_eq: "\<lbrakk> b < a \<and> a - b = fzero b\<rbrakk> \<Longrightarrow> b = a"
    using local.less_iff le_imp_zero_le_minus by force
      
  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = fzero b \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add by auto
 
  lemma diff_add_cancel_left': "a \<le> b \<Longrightarrow> a + (b - a) = b"
    using local.le_iff_add local.le_is_fzero_le by auto

  lemma add_left_strict_mono: "\<lbrakk> a + b < a + c \<rbrakk> \<Longrightarrow> b < c"
    using local.add_le_imp_le_left local.add_left_mono local.less_iff by blast
      
  lemma sum_minus_left: "c \<le> a \<Longrightarrow> (a + b) - c = (a - c) + b"
    by (metis add_assoc diff_add_cancel_left' local.add_monoid_diff_cancel_left local.minus_def)      
     
  lemma neq_zero_impl_greater:
    "x \<noteq> fzero x \<Longrightarrow> fzero x < x"
    by (metis least_zero local.add_fzero_left local.diff_cancel local.fzero_sum_right local.less_iff sum_minus_left)

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
    by (auto, metis le_sum_cases, metis minus_def le_is_fzero_le add_monoid_diff_cancel_left fzero_le_def sum_eq_sum_conv)

  lemma le_sum_iff: "a \<le> b + c \<longleftrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    by (metis le_sum_cases' add_monoid_diff_cancel_left le_is_fzero_le minus_def monoid_le_add_left_mono fzero_le_def monoid_le_trans)
    
  lemma sum_minus_right: "c \<ge> a \<Longrightarrow> a + b - c = b - (c - a)"
    by (metis diff_add_cancel_left' local.add_diff_cancel_left') 

  (* under what circumstances is - associative? *)
end
  
text {* This algebra forms a preorder. It turns out this is
        sufficient for the theories on reactive processes. *}  
  
instance fzero_trace \<subseteq> preorder
  apply (intro_classes)
  apply (simp add: fzero_trace_class.less_iff)
  apply (simp add: fzero_add_zero_class.monoid_le_refl le_is_fzero_le)
  using fzero_trace_class.le_is_fzero_le 
  by (metis semigroup_add_class.monoid_le_trans)

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
  "(xs :: 'a list) \<le>\<^sub>d ys \<longleftrightarrow> xs \<le> ys"
  apply (simp add: fzero_le_def plus_list_def)
  using Prefix_Order.prefixE Prefix_Order.prefixI apply blast
  done
    
lemma fzero_subtract_list:
  "(xs :: 'a list) -\<^sub>d ys = xs - ys"
  apply (auto simp add: fzero_subtract_def fzero_le_list minus_list_def less_eq_list_def)
  apply (rule the_equality)
  by (simp_all add: fzero_list_def plus_list_def prefix_drop)
    
instance list :: (type) fzero_trace
  apply intro_classes
  apply (simp_all add:fzero_list_def plus_list_def)
  apply (simp add: append_eq_append_conv2)
  using Prefix_Order.prefixE Prefix_Order.prefixI
  apply (simp add: fzero_le_list)
  apply (simp add: less_le_not_le)
  by (simp add: fzero_subtract_list)

instantiation nat :: fzero_is_0
begin
  
  definition fzero_nat :: "nat \<Rightarrow> nat" where "fzero_nat a = 0"
 
  instance
    by (intro_classes, auto simp add:fzero_nat_def)
end
    
(* the following are properties satisfied by left/right restriction semigroups,
   but the fzero_trace class does not satisfy all of them. I do not think that
   properties related to commutativity will ever be satisfied in the general case. *)    
    
lemma fzero_restrict0:
  fixes a :: "'a::fzero_trace"
  shows "fzero(fzero(a) + b) = fzero(a) + fzero b"
  by (metis fzero_trace_class.add_diff_cancel_left fzero_trace_class.diff_zero)
    
lemma fzero_restrict1:
  fixes a :: "'a::fzero_trace"
  shows "fzero(a) + b = b + fzero(a + b)"
  by (metis (no_types, lifting) add_fzero_right fzero_trace_class.add_diff_cancel_left fzero_trace_class.le_add fzero_trace_class.sum_minus_left)

lemma fzero_dist_plus:
  fixes a :: "'a::fzero_trace"
  shows "fzero(a + b) = fzero(a) + fzero(b)"
  by (metis add.assoc add_fzero_right fzero_trace_class.add_diff_cancel_left)
    
end