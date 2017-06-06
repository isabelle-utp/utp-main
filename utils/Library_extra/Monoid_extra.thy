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
  
class left_cancel_monoid = plus +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"

class right_cancel_monoid = plus +
  assumes add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"

class monoid_sum_0 = monoid_add +
  assumes zero_sum_left: "a + b = 0 \<Longrightarrow> a = 0" 
begin
  
(* we only need sum_right or sum_left, the other can be derived.
   the reason to pick right over left will become apparent,
   because in the weaker form, we only want to have one kind.

   if we take that a + 0 = a and a + b = b, for example, then
   the left_cancel_monoid does not hold.

   it's also interesting to note that even without assuming
   that a + 0 = a, by assuming zero_sum_left it is still
   possible to show zero_sum_right and zero_sum, and therefore
   that we have anti-sym for monoid_le. And similarly the other
   way round. *)

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
  
(* BEGIN NEW *)
  
class dzero = 
  fixes dzero :: "'a \<Rightarrow> 'a"
  assumes dzero_idem: "dzero (dzero a) = dzero a"    

(* the class of the original trace algebra: *)    
    
class dzero_unique = dzero +
  assumes dzero_unique: "dzero a = dzero b"
    
class dzero_is_0 = dzero + zero +
  assumes dzero_is_0: "dzero a = 0"

(* likely the refusals class: *)
    
class dzero_same = dzero +
  assumes dzero_same: "dzero a = a"
    
(* mirror properties of the trace algebra *)
    
class dzero_add_zero = dzero + semigroup_add +
  assumes add_dzero_left[simp]: "(dzero a) + a = a"
  assumes add_dzero_right[simp]: "a + (dzero a) = a"
begin
  
definition dzero_le (infix "\<le>\<^sub>d" 50)
where "a \<le>\<^sub>d b \<longleftrightarrow> (\<exists>c. b = a + c)"
 
definition dzero_subtract (infixl "-\<^sub>d" 65)
where "a -\<^sub>d b = (if (b \<le>\<^sub>d a) then THE c. a = b + c else dzero b)"  
  
end
    
class dzero_sum_zero = dzero_add_zero +
  assumes dzero_sum_right: "a + b = (dzero b) \<Longrightarrow> (b = dzero b)"
    
lemma dzero_sum_left:
  fixes a :: "'a::{dzero_is_0,dzero_sum_zero}"
  shows "a + b = dzero a \<Longrightarrow> a = dzero a"
  by (metis dzero_add_zero_class.add_dzero_right dzero_sum_right dzero_is_0)
    
lemma dzero_sum:
  fixes a :: "'a::{dzero_is_0,dzero_sum_zero}"
  shows "a + b = dzero a \<longleftrightarrow> a = dzero a \<and> b = dzero b"
  by (metis add_dzero_left dzero_is_0 dzero_sum_left)    
    
(* New stuff above *)    
    
(* Is there a nicer way to show a combined type class is an instace? *)    
class dzero_is_0_sum_zero = dzero_is_0 + dzero_sum_zero

instance dzero_is_0_sum_zero \<subseteq> monoid_sum_0
  apply intro_classes
  apply (metis add_dzero_left dzero_is_0)
  apply (metis add_dzero_right dzero_is_0)
  by (metis dzero_is_0 dzero_sum)
    
class dzero_pre_trace = left_cancel_monoid + dzero_sum_zero +
  assumes
  sum_eq_sum_conv: "(a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
begin
  
lemma monoid_le_least_zero: "dzero a \<le>\<^sub>d a"
    by (metis local.add_dzero_left local.dzero_le_def)

lemma monoid_le_refl: "a \<le>\<^sub>d a"
  apply (simp add: dzero_le_def)
  by (metis local.sum_eq_sum_conv)

lemma monoid_le_trans: "\<lbrakk> a \<le>\<^sub>d b; b \<le>\<^sub>d c \<rbrakk> \<Longrightarrow> a \<le>\<^sub>d c"
  by (metis add.assoc dzero_le_def) 
    
lemma monoid_le_add: "a \<le>\<^sub>d a + b"
  by (auto simp add: dzero_le_def)

lemma monoid_le_add_left_mono: "a \<le>\<^sub>d b \<Longrightarrow> c + a \<le>\<^sub>d c + b"
  using add_assoc by (auto simp add: dzero_le_def)

lemma add_monoid_diff_cancel_left [simp]: "(a + b) -\<^sub>d a = b"
  apply (simp add: dzero_subtract_def monoid_le_add)
  apply (rule the_equality)
  apply (simp)
  using local.add_left_imp_eq apply blast
  done
    
end
   
lemma dzero_monoid_le_antisym :
  fixes a :: "'a::{dzero_is_0,dzero_pre_trace}"
  assumes "a \<le>\<^sub>d b" "b \<le>\<^sub>d a"
  shows "a = b"
proof -
  obtain a' where a': "b = a + a'"
    using assms(1) dzero_le_def by auto

  obtain b' where b': "a = b + b'"
    using assms(2) dzero_le_def by auto

  have "b' = (b' + a' + b')"
    by (metis a' add.semigroup_axioms b' left_cancel_monoid_class.add_left_imp_eq semigroup.assoc)

  hence "dzero b' + dzero b' + b' = (b' + a' + b')"
    by (metis add.semigroup_axioms add_dzero_left semigroup.assoc)
      
  hence "dzero b' + dzero b' = b' + a'"
    by (metis (no_types, lifting) add.semigroup_axioms add_dzero_right dzero_is_0 left_cancel_monoid_class.add_left_imp_eq semigroup.assoc)
      
  hence "b' + a' = dzero b'"
    by (metis add_dzero_right dzero_is_0)
      
  hence "a' = dzero a'" "b' = dzero b'"
    using dzero_sum apply blast
    using \<open>b' + a' = dzero b'\<close> dzero_sum_left by auto

  with a' b' show ?thesis
    by (metis add_dzero_right dzero_is_0)

qed
  
 (* END NEW *)

class pre_trace = left_cancel_monoid + monoid_sum_0 +
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
  
class dzero_trace = dzero_pre_trace + ord + minus +
  assumes le_is_dzero_le: "a \<le> b \<longleftrightarrow> (a \<le>\<^sub>d b)"
  and less_iff: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> (b \<le> a)"
  and minus_def: "a - b = a -\<^sub>d b"
begin
  
 lemma le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists> c. b = a + c)"
    by (simp add: local.le_is_dzero_le local.dzero_le_def)

  lemma least_zero [simp]: "dzero a \<le> a"
    by (simp add: local.le_is_dzero_le local.monoid_le_least_zero)

  lemma le_add [simp]: "a \<le> a + b"
    by (simp add: le_is_dzero_le local.monoid_le_add)

  lemma not_le_minus [simp]:  "\<not> (a \<le> b) \<Longrightarrow> b - a = dzero a"
    by (simp add: le_is_dzero_le local.minus_def local.dzero_subtract_def)

  lemma add_diff_cancel_left [simp]: "(a + b) - a = b"
    by (simp add: minus_def)

  lemma diff_zero [simp]: "a - dzero a = a"
    by (metis local.add_dzero_left local.add_diff_cancel_left)
 
  lemma diff_cancel [simp]: "a - a = dzero a"
    by (metis local.add_dzero_right local.add_diff_cancel_left)
  
  lemma add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
    by (simp add: local.le_is_dzero_le local.monoid_le_add_left_mono)

  lemma add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"
    by (auto simp add: le_iff_add, metis add_assoc local.add_diff_cancel_left)
      
  lemma add_diff_cancel_left' [simp]:  "(c + a) - (c + b) = a - b"
  proof (cases "b \<le> a")
    case True thus ?thesis
      by (metis add_assoc local.add_diff_cancel_left local.le_iff_add)
  next
    case False thus ?thesis
      using local.add_le_imp_le_left not_le_minus 
      by (metis add_assoc local.add_dzero_right local.add_monoid_diff_cancel_left)
  qed
    
  lemma tt: "\<lbrakk> b \<le> a; dzero b < a - b \<rbrakk> \<Longrightarrow> b < a"
    by (smt local.add.semigroup_axioms local.add_monoid_diff_cancel_left local.le_iff_add local.less_iff local.minus_def semigroup.assoc)

  lemma tt1: "\<lbrakk> b \<le> a; b < a \<rbrakk> \<Longrightarrow> dzero b < a - b"
    by (metis local.add_dzero_right local.add_diff_cancel_left local.add_le_imp_le_left local.add_left_mono local.le_iff_add local.less_iff)
 
  lemma tt2: "\<lbrakk> b \<le> a \<rbrakk> \<Longrightarrow> b < a \<longleftrightarrow> dzero b < a - b"
    using tt tt1 by blast
      
  lemma tt4: "\<lbrakk> b < a \<and> a - b = dzero b\<rbrakk> \<Longrightarrow> b = a"
    using local.less_iff tt1 by force
      
  lemma minus_zero_eq: "\<lbrakk> b \<le> a; a - b = dzero b \<rbrakk> \<Longrightarrow> a = b"
    using local.le_iff_add by auto
 
  lemma diff_add_cancel_left': "a \<le> b \<Longrightarrow> a + (b - a) = b"
    using local.le_iff_add local.le_is_dzero_le by auto

  lemma add_left_strict_mono: "\<lbrakk> a + b < a + c \<rbrakk> \<Longrightarrow> b < c"
    using local.add_le_imp_le_left local.add_left_mono local.less_iff by blast
      
  lemma sum_minus_left: "c \<le> a \<Longrightarrow> (a + b) - c = (a - c) + b"
    by (metis add_assoc diff_add_cancel_left' local.add_monoid_diff_cancel_left local.minus_def)      
     
  lemma neq_zero_impl_greater:
    "x \<noteq> dzero x \<Longrightarrow> dzero x < x"
    by (metis least_zero local.add_dzero_left local.diff_cancel local.dzero_sum_right local.less_iff sum_minus_left)

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
    by (auto, metis le_sum_cases, metis minus_def le_is_dzero_le add_monoid_diff_cancel_left dzero_le_def sum_eq_sum_conv)

  lemma le_sum_iff: "a \<le> b + c \<longleftrightarrow> a \<le> b \<or> b \<le> a \<and> a - b \<le> c"
    by (metis le_sum_cases' add_monoid_diff_cancel_left le_is_dzero_le minus_def monoid_le_add_left_mono dzero_le_def monoid_le_trans)
    
  lemma sum_minus_right: "c \<ge> a \<Longrightarrow> a + b - c = b - (c - a)"
    by (metis diff_add_cancel_left' local.add_diff_cancel_left')  
  
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
      using local.add_le_imp_le_left not_le_minus 
      by (metis add_assoc local.add_0_right local.add_monoid_diff_cancel_left)
  qed
    
  lemma tt: "\<lbrakk> b \<le> a; 0 < a - b \<rbrakk> \<Longrightarrow> b < a"
    by (smt local.add.semigroup_axioms local.add_monoid_diff_cancel_left local.le_iff_add local.less_iff local.minus_def semigroup.assoc)

  lemma tt1: "\<lbrakk> b \<le> a; b < a \<rbrakk> \<Longrightarrow> 0 < a - b"
    by (metis local.add_0_right local.add_diff_cancel_left local.add_le_imp_le_left local.add_left_mono local.le_iff_add local.less_iff)
  
  lemma tt2: "\<lbrakk> b \<le> a \<rbrakk> \<Longrightarrow> b < a \<longleftrightarrow> 0 < a - b"
    using tt tt1 by blast
      
  lemma tt4: "\<lbrakk> b < a \<and> a - b = 0\<rbrakk> \<Longrightarrow> b = a"
    using local.less_iff tt1 by force

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
    
instance dzero_trace \<subseteq> preorder
  apply (intro_classes)
  apply (simp add: dzero_trace_class.less_iff)
  apply (simp add: dzero_pre_trace_class.monoid_le_refl le_is_dzero_le)
  using dzero_pre_trace_class.monoid_le_trans le_is_dzero_le by blast
        
instantiation list :: (type) monoid_add
begin

  definition zero_list :: "'a list" where "zero_list = []"
  definition plus_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where "plus_list = op @"

instance
  by (intro_classes, simp_all add: zero_list_def plus_list_def)
end
  
instantiation list :: (type) dzero_add_zero
begin
definition dzero_list :: "'a list \<Rightarrow> 'a list" where "dzero_list a = []"
 
instance by (intro_classes, simp_all add:dzero_list_def dzero_list_def plus_list_def)
end
  
lemma dzero_le_list:
  "(xs :: 'a list) \<le>\<^sub>d ys \<longleftrightarrow> xs \<le> ys"
  apply (simp add: dzero_le_def plus_list_def)
  using Prefix_Order.prefixE Prefix_Order.prefixI apply blast
  done
    
lemma dzero_subtract_list:
  "(xs :: 'a list) -\<^sub>d ys = xs - ys"
  apply (auto simp add: dzero_subtract_def dzero_le_list minus_list_def less_eq_list_def)
  apply (rule the_equality)
  by (simp_all add: dzero_list_def plus_list_def prefix_drop)
    
instance list :: (type) dzero_trace
  apply intro_classes
  apply (simp_all add:dzero_list_def plus_list_def)
  apply (simp add: append_eq_append_conv2)
  using Prefix_Order.prefixE Prefix_Order.prefixI
  apply (simp add: dzero_le_list)
  apply (simp add: less_le_not_le)
  by (simp add: dzero_subtract_list)

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
    
instantiation nat :: dzero_is_0
begin
  
  definition dzero_nat :: "nat \<Rightarrow> nat" where "dzero_nat a = 0"
 
  instance
    by (intro_classes, auto simp add:dzero_nat_def)
end

lemma monoid_le_nat:
  "(x :: nat) \<le>\<^sub>m y \<longleftrightarrow> x \<le> y"
  by (simp add: monoid_le_def nat_le_iff_add)

lemma monoid_subtract_nat:
  "(x :: nat) -\<^sub>m y = x - y"
  by (auto simp add: monoid_subtract_def monoid_le_nat dzero_nat_def)

instance nat :: trace
  apply (intro_classes, simp_all add: monoid_subtract_nat)
  apply (metis Nat.diff_add_assoc Nat.diff_add_assoc2 add_diff_cancel_right' add_le_cancel_left add_le_cancel_right add_less_mono cancel_ab_semigroup_add_class.add_diff_cancel_left' less_irrefl not_le)
  apply (simp add: nat_le_iff_add monoid_le_def)
  apply linarith+
done
end