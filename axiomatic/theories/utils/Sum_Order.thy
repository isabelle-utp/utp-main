(******************************************************************************)
(* Project: Isabelle/UTP: Unifying Theories of Programming in Isabelle/HOL    *)
(* File: Sum_Order.thy                                                        *)
(* Authors: Frank Zeyda and Simon Foster (University of York, UK)             *)
(* Emails: frank.zeyda@gmail.com and simon.foster@york.ac.uk                  *)
(******************************************************************************)
(* LAST REVIEWED: 09 Jun 2022 *)

section \<open>Sum Type Order\<close>

theory Sum_Order
imports Main
begin

subsection \<open>Instantiation of @{class ord}\<close>

instantiation sum :: (ord, ord) ord
begin
fun less_eq_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
"less_eq_sum (Inl x) (Inl y) \<longleftrightarrow> x \<le> y" |
"less_eq_sum (Inr x) (Inr y) \<longleftrightarrow> x \<le> y" |
"less_eq_sum (Inl x) (Inr y) \<longleftrightarrow> False" |
"less_eq_sum (Inr x) (Inl y) \<longleftrightarrow> False"

definition less_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool" where
"less_sum x y \<longleftrightarrow> (x \<le> y) \<and> x \<noteq> y"
instance by (intro_classes)
end

subsection \<open>Instantiation of @{class order}\<close>

instantiation sum :: (order, order) order
begin
theorem less_le_not_le_sum :
fixes x :: "'a + 'b"
fixes y :: "'a + 'b"
shows "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
apply (unfold less_sum_def)
apply (induct x; induct y)
apply (auto)
done

theorem order_refl_sum :
fixes x :: "'a + 'b"
shows "x \<le> x"
apply (induct x)
apply (auto)
done

theorem order_trans_sum :
fixes x :: "'a + 'b"
fixes y :: "'a + 'b"
fixes z :: "'a + 'b"
shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
apply (atomize (full))
apply (induct x; induct y; induct z)
apply (auto)
done

theorem antisym_sum :
fixes x :: "'a + 'b"
fixes y :: "'a + 'b"
shows "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
apply (atomize (full))
apply (induct x; induct y)
apply (auto)
done

instance
apply (intro_classes)
apply (metis less_le_not_le_sum)
apply (metis order_refl_sum)
apply (metis order_trans_sum)
apply (metis antisym_sum)
done
end
end