section {* Slotted Circus *}

theory utp_slotted_circus
  imports 
    Monoid_extra
    "../utils/Library_extra/Terminated_lists"
    "~~/src/HOL/Library/Prefix_Order"
begin
  
subsection {* Type definitions *}
  
(*subsubsection {* Refusals *}
  
typedef '\<alpha> refusal = "{x::'\<alpha> set. True}"
  morphisms refusal2set set2refusal
  by auto
    
setup_lifting type_definition_refusal
  
instantiation refusal :: (type) plus
begin
  definition plus_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal" where "plus_refusal a b = b"
  
  instance by (intro_classes)
end
  
(* I'm not sure whether we need to instantiate fzero for refusal type,
   but for the sake of generality of the slotted_trace fzero, we do it. *)  
  
instantiation refusal :: (type) fzero
begin
  definition fzero_refusal :: "'a refusal \<Rightarrow> 'a refusal" where "fzero_refusal a = a"
  
  instance by (intro_classes)
end*)  
  
subsubsection {* Slots *}
  
typedef ('\<alpha>,'\<beta>) slot = "{x::('\<alpha> \<times> '\<beta> set). True}" 
  morphisms slot2pair pair2slot
  by auto
    
declare [[coercion_enabled]]
        [[coercion pair2slot]]
    
setup_lifting type_definition_slot
  
(* We can define plus on slots *)
instantiation slot :: (plus,type) plus
begin
  lift_definition plus_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot \<Rightarrow> ('a,'b) slot" 
    is "\<lambda> (h1,_) (h2,r2). (h1+h2,r2)" .

  instance by intro_classes
end

instantiation slot :: (fzero,type) fzero
begin
  lift_definition fzero_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot" is
    "\<lambda> (h1,r1). (fzero h1,r1)" .
    
  instance by intro_classes
end
  
instantiation slot :: (fzero_add_zero,type) fzero_add_zero
begin
  
instance 
  apply intro_classes
  apply (simp add:plus_slot_def add.assoc pair2slot_inverse split_beta)
  apply (metis (mono_tags, lifting) fzero_idem fzero_slot.rep_eq prod.collapse prod.sel(1) slot2pair_inverse split_beta)
  apply (metis (mono_tags, lifting) add_fzero_left fzero_slot.rep_eq plus_slot.rep_eq prod.collapse prod.sel(1) slot2pair_inject split_beta)
  by (metis (mono_tags, lifting) add_fzero_right fzero_slot.rep_eq old.prod.case plus_slot.rep_eq prod.collapse slot2pair_inject split_beta)
end
  
instantiation slot :: (fzero_sum_zero,type)  fzero_sum_zero
begin
instance
  apply intro_classes
  by (metis (mono_tags, lifting) fzero_slot.rep_eq fzero_sum_right plus_slot.rep_eq prod.collapse prod.sel(1) slot2pair_inverse split_beta)
end
  
instantiation slot :: (left_cancel_semigroup,type) left_cancel_semigroup
begin
instance apply intro_classes
    apply (simp add:plus_slot_def)
    by (smt Pair_inject left_cancel_semigroup_class.add_left_imp_eq plus_slot.rep_eq prod.collapse slot2pair_inverse split_beta)
end
  
instantiation slot :: (fzero_pre_trace,type) fzero_pre_trace
begin
  
lemma slot_sum_eq_conv:
  fixes a :: "('\<alpha>::fzero_pre_trace,'\<beta>) slot"
  assumes "a + b = c + d"
  shows "\<exists>e. a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
proof -
  obtain ah ar where a: "a = pair2slot (ah,ar)"
    by (cases a, auto)
      
  obtain bh br where b: "b = pair2slot (bh,br)"
    by (cases b, auto)
      
  obtain ch cr where c: "c = pair2slot (ch,cr)"
    by (cases c, auto)
      
  obtain dh dr where d: "d = pair2slot (dh,dr)"
    by (cases d, auto)
  
  
  have a':"a + b = pair2slot (ah+bh,br)"
    using a and b
    by (metis (no_types, lifting) mem_Collect_eq pair2slot_inject plus_slot.rep_eq prod.sel(1) prod.sel(2) slot2pair_inverse split_beta)
  
  have c':"c + d = pair2slot (ch+dh,dr)"
    using c and d
    by (metis (no_types, lifting) mem_Collect_eq pair2slot_inject plus_slot.rep_eq prod.sel(1) prod.sel(2) slot2pair_inverse split_beta)
  
  from assms have "pair2slot (ah+bh,br) = pair2slot (ch+dh,dr)"
    using a' c' by simp
  then have "ah+bh = ch+dh \<and> br = dr"
    using pair2slot_inject by fastforce
  then have "\<exists>g. ah = ch + g \<and> g + bh = dh \<or> ah + g = ch \<and> bh = g + dh \<and> br = dr"     
    by (simp add: fzero_pre_trace_class.sum_eq_sum_conv)
  then have "\<exists>g e. (ah = ch + g \<and> ar = e \<and> g + bh = dh \<and> br = dr)
                     \<or> 
                   (ah + g = ch \<and> e = cr \<and> bh = g + dh \<and> br = dr)"
    using \<open>ah + bh = ch + dh \<and> br = dr\<close> by auto
  then have "\<exists>g e. pair2slot (ah,ar) = pair2slot (ch,cr) + pair2slot (g,e) \<and> pair2slot (g,e) + pair2slot (bh,br) = pair2slot (dh,dr)
                   \<or>
                   pair2slot (ah,ar) + pair2slot (g,e) = pair2slot (ch,cr) \<and> pair2slot (bh,br) = pair2slot (g,e) + pair2slot (dh,dr)"
    apply (simp add:plus_slot_def pair2slot_inverse slot2pair_inverse)
    by blast
  then have "\<exists>f. a = c + f \<and> f + b = d \<or> a + f = c \<and> b = f + d"
    using a b c d by auto
      
  then show ?thesis by blast
qed
  
instance by (intro_classes, simp add:slot_sum_eq_conv)
end
  
class fzero_add_zero_0 = fzero_add_zero + fzero_is_0
  
class fzero_sum_zero_0 = fzero_sum_zero + fzero_is_0
  
class fzero_almost_pre_trace_0 = left_cancel_semigroup + fzero_sum_zero + fzero_is_0  
  
class fzero_pre_trace_0 = fzero_pre_trace + fzero_is_0 (*left_cancel_semigroup + fzero_sum_zero_0*) 

class fzero_trace_0 = fzero_trace + fzero_is_0
 
instance fzero_add_zero_0 \<subseteq> monoid_add
  apply intro_classes
  using fzero_is_0 apply (metis add_fzero_left)
  using fzero_is_0 by (metis add_fzero_right)
    
instance fzero_almost_pre_trace_0 \<subseteq> left_cancel_semigroup
  by intro_classes
    
instance fzero_almost_pre_trace_0 \<subseteq> fzero_sum_zero_0
  by intro_classes
  
instance fzero_sum_zero_0 \<subseteq> monoid_sum_0
  apply intro_classes
  using fzero_is_0 apply (metis add_fzero_left)
  using fzero_is_0 apply (metis add_fzero_right)
  using fzero_is_0 by (metis fzero_sum)
    
instance fzero_pre_trace_0 \<subseteq> fzero_sum_zero_0
  by intro_classes
    
instance fzero_trace_0 \<subseteq> fzero_pre_trace_0
  by intro_classes
    
instance fzero_pre_trace_0 \<subseteq> pre_trace
  apply intro_classes
  using fzero_is_0 by (simp add: fzero_pre_trace_class.sum_eq_sum_conv)
  
instance fzero_trace_0 \<subseteq> trace
  apply intro_classes
  using fzero_is_0 apply (simp add: fzero_trace_class.le_iff_add monoid_le_def)
  using fzero_is_0 apply (simp add: less_le_not_le)
  using fzero_is_0
  by (metis fzero_pre_trace_class.add_monoid_diff_cancel_left fzero_trace_class.le_iff_add fzero_trace_class.minus_def fzero_trace_class.not_le_minus monoid_le_def monoid_subtract_def pre_trace_class.add_monoid_diff_cancel_left)

instance fzero_trace_0 \<subseteq> monoid_add
  by intro_classes
    
instance fzero_trace_0 \<subseteq> fzero_trace
  by intro_classes
    
instantiation slot :: (fzero_trace,type) fzero_trace
begin
  definition less_eq_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot \<Rightarrow> bool" where "less_eq_slot == fzero_le"
  definition minus_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot \<Rightarrow> ('a,'b) slot" where "minus_slot == fzero_subtract"
  definition less_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot \<Rightarrow> bool" where "less_slot a b == a \<le> b \<and> \<not> (b \<le> a)"

instance by (intro_classes, simp_all add: less_eq_slot_def less_slot_def minus_slot_def)
end
  
(*
instantiation slot :: (fzero_trace_0,type) monoid_add
begin
  lift_definition zero_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot" is "\<lambda> (a,b). (0,b)" by auto
  
instance apply intro_classes
   apply (simp add:zero_slot_def)
   apply (case_tac a, auto)
   apply (simp add:plus_slot_def pair2slot_inverse)
   sledgehammer
  apply (simp add:zero_slot_def)
  apply (case_tac a, auto)
  apply (simp add:plus_slot_def pair2slot_inverse)
  nitpick
end*)
  
lemma slot_minus:
  fixes s1 s2 :: "('a::fzero_trace,'b) slot"
  shows "s1 - s2 = (fst (slot2pair s1) - fst (slot2pair s2), snd (slot2pair s1))"
  
  apply (cases s1)
  apply (cases s2)
  apply (simp add:minus_slot_def pair2slot_inverse)
  oops
    
lemma pair2slot_le_imp_leq_histories:
  fixes h1 :: "'a::fzero_trace"
  shows "pair2slot (h2,r2) \<le> pair2slot (h1,r1) \<Longrightarrow> h2 \<le> h1"
  apply (simp add:less_eq_slot_def fzero_le_def)
  apply auto
  apply (case_tac c)
  apply auto
  by (simp add:plus_slot_def pair2slot_inverse pair2slot_inject)
    
lemma leq_histories_imp_pair2slot_le:
  fixes h1 :: "'a::fzero_trace"
  assumes "h2 \<le> h1"
  shows "pair2slot (h2,r2) \<le> pair2slot (h1,r1)"
proof -
  have a:"\<exists>h. h1 = h2 + h"
    using assms by (simp add:le_is_fzero_le fzero_le_def)
      
  have "pair2slot (h2,r2) \<le> pair2slot (h1,r1) = (\<exists>c d. pair2slot (h1, r1) = pair2slot (h2, r2) + pair2slot(c,d))"
    apply (simp add:less_eq_slot_def fzero_le_def)
    by (metis prod.collapse slot2pair_inverse)
  then have "\<exists>c. pair2slot (h1, r1) = pair2slot (h2, r2) + pair2slot(c,r1)"
    apply (simp add:plus_slot_def slot2pair_inverse pair2slot_inverse)
    using a by blast
  then have "\<exists>c d. pair2slot (h1, r1) = pair2slot (h2, r2) + d \<and> d = pair2slot(c,r1)"
    by blast
  
  then have "\<exists>d. pair2slot (h1, r1) = pair2slot (h2, r2) + d"
    by blast
      
  then show ?thesis by (simp add:less_eq_slot_def fzero_le_def)
qed
  
lemma slot_le_iff_histories_le:
  "pair2slot (h2,r2) \<le> pair2slot (h1,r1) \<longleftrightarrow> h2 \<le> h1"
  by (meson leq_histories_imp_pair2slot_le pair2slot_le_imp_leq_histories)
    
lemma slot_plus_2:
  fixes h1 :: "'a::fzero_trace"
  shows "pair2slot (h1,r1) + pair2slot (h2,r2) = pair2slot(h1+h2,r2)"
  apply (simp add:plus_slot_def)    
  by (simp add:pair2slot_inject pair2slot_inverse)
    
lemma slot_minus_2:
  fixes h1 :: "'a::fzero_trace"
  shows "pair2slot (h1,r1) - pair2slot (h2,r2) = pair2slot(h1-h2,r1)"
  apply (cases "pair2slot (h2,r2) \<le> pair2slot (h1,r1)")
  apply (simp add:minus_slot_def fzero_subtract_def le_is_fzero_le fzero_le_def)
  apply auto
  apply (case_tac c)
  apply auto
  apply (simp add:plus_slot_def)
  apply (rule the_equality)
  apply (metis (no_types, lifting) fzero_trace_class.add_diff_cancel_left mem_Collect_eq pair2slot_inverse prod.sel(1) prod.sel(2) split_beta)
  apply (metis (no_types, lifting) Pair_inject fzero_trace_class.add_diff_cancel_left mem_Collect_eq pair2slot_inject prod.collapse slot2pair_inverse split_beta)
  apply (simp add:fzero_slot_def pair2slot_inject pair2slot_inverse)
  by (metis fzero_trace_class.not_le_minus leq_histories_imp_pair2slot_le)
(* So an individual slot is an fzero_trace on its own *)
  
subsubsection {* Slotted traces *}
  
typedef ('\<alpha>,'\<beta>) slotted_trace = "{x::('\<alpha>,'\<beta>) slot stlist. True}"
  morphisms slotted2stlist stlist2slotted
  by auto

setup_lifting type_definition_slotted_trace

instantiation slotted_trace :: (fzero_is_0,type) fzero
begin
  lift_definition fzero_slotted_trace :: "('a,'b) slotted_trace \<Rightarrow> ('a,'b) slotted_trace" 
    is "\<lambda> s. [;fzero (last s)]" .    
      
  instance by (intro_classes)
end  
  
instantiation slotted_trace :: (plus,plus) plus
begin
  lift_definition plus_slotted_trace :: "('a,'b) slotted_trace \<Rightarrow> ('a,'b) slotted_trace \<Rightarrow> ('a,'b) slotted_trace" 
    is "op +" . 
  
  instance by (intro_classes)
end
  
instantiation slotted_trace :: (left_cancel_semigroup,plus) left_cancel_semigroup
begin
  instance
   apply intro_classes
   by (metis left_cancel_semigroup_class.add_left_imp_eq plus_slotted_trace.rep_eq slotted2stlist_inject)
end


    
instantiation slotted_trace :: (fzero_sum_zero_0,plus) fzero_sum_zero
begin
  
lemma stlist2slotted_dist_plus:
  "stlist2slotted (a + b) = stlist2slotted(a) + stlist2slotted(b)"
  by (simp add:plus_slotted_trace_def stlist2slotted_inverse)
  
lemma fzero_last_add_fzero_left:
  fixes x :: "'a stlist"
  shows "fzero (Terminated_lists.last x) + y = y"
  apply (induct x)
  apply auto
  using add_fzero_left by (metis fzero_is_0)
  
lemma slotted_add_fzero_left:
  fixes a :: "('a,'b) slotted_trace"
  shows "fzero a + a = a"
  apply (induct a)
  apply (simp add:fzero_slotted_trace_def plus_slotted_trace_def stlist2slotted_inverse)
  apply (simp add:stlist2slotted_dist_plus slotted2stlist_inverse)
  apply (induct_tac y)
  apply auto
   apply (simp add:plus_slotted_trace_def stlist2slotted_inverse)
   apply (simp add:stlist2slotted_inject)
   apply (simp add:plus_stlist_def)
  apply (simp add:plus_slotted_trace_def stlist2slotted_inverse)
  apply (simp add:plus_stlist_def)  
  apply (simp add:stlist2slotted_inject)
  by (metis (mono_tags, lifting) fzero_is_0 fzero_slot.rep_eq plus_slot.rep_eq prod.collapse prod.sel(1) slot2pair_inject split_beta utp_slotted_circus.fzero_last_add_fzero_left)
  
lemma slotted_add_fzero_right:
  fixes a :: "('a,'b) slotted_trace"
  shows "a + fzero a = a"
  apply (induct a)
  apply (simp add:fzero_slotted_trace_def plus_slotted_trace_def stlist2slotted_inverse)
  apply (simp add:stlist2slotted_dist_plus slotted2stlist_inverse)
  apply (induct_tac y)
  apply auto
   apply (simp add:plus_slotted_trace_def stlist2slotted_inverse)
   apply (simp add:stlist2slotted_inject)
   apply (simp add:plus_stlist_def)
  apply (simp add:plus_slotted_trace_def stlist2slotted_inverse)
  apply (simp add:plus_stlist_def)  
  by (simp add:stlist2slotted_inject)
    
lemma slotted_fzero_sum_zero:
  fixes a :: "('a,'b) slotted_trace"
  shows "a + b = fzero b \<Longrightarrow> b = fzero b"
  apply (induct b)
  apply auto
  apply (induct a)
  apply auto
  apply (simp add:plus_slotted_trace_def)
  apply (case_tac ya)
   apply auto
   apply (simp add:stlist2slotted_inverse fzero_slotted_trace_def stlist2slotted_inject)
   apply (case_tac y)
    using fzero_sum_right stlist_plus_nils apply blast
    apply (simp add: plus_stlist_def)
   apply (simp add:stlist2slotted_inverse fzero_slotted_trace_def stlist2slotted_inject)
   apply (case_tac y)
    apply (simp add: stlist_nil_concat_cons) 
    by (simp add: plus_stlist_def)
    
instance
  apply intro_classes
  apply (metis (mono_tags, lifting) plus_seq_assoc plus_slotted_trace.rep_eq slotted2stlist_inject)
  apply (metis (mono_tags, lifting) Terminated_lists.last.simps(1) fzero_idem fzero_slotted_trace.rep_eq fzero_slotted_trace_def map_fun_apply)
  apply (simp add:slotted_add_fzero_left)
  apply (simp add:slotted_add_fzero_right)
  by (simp add:slotted_fzero_sum_zero)
end
    
lemma stlist_fzero_eq_sum_conv_nils:
  fixes a :: "'a::fzero_pre_trace"
  assumes "[;a] + [;b] = [;c] + [;d]"
  shows "\<exists> e . [;a] = [;c] + e \<and> e + [;b] = [;d] \<or> [;a] + e = [;c] \<and> [;b] = e + [;d]"
proof -  
 
  have a: "([;a] + [;b] = [;c] + [;d]) = (a + b = c + d)"
    by (metis stlist_plus_nils)
      
  have b: "(a + b = c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
    by (simp add: fzero_pre_trace_class.sum_eq_sum_conv)
  
  then have "(a + b = c + d) \<Longrightarrow> \<exists> e . [;a] = [;c] + e \<and> e + [;b] = [;d] \<or> [;a] + e = [;c] \<and> [;b] = e + [;d]"   
    by (metis stlist_plus_nils)
    
  with a b show ?thesis using assms by simp
qed
  
lemma stlist_fzero_eq_sum_conv_nils1:
  fixes a :: "'a::fzero_pre_trace stlist"
  assumes "a + [;b] = c + [;d]"
  shows "\<exists> e . a = c + e \<and> e + [;b] = [;d] \<or> a + e = c \<and> [;b] = e + [;d]"
  using assms
  apply (induct a c rule:stlist_induct_cons)
  apply (simp add: stlist_fzero_eq_sum_conv_nils)
  by (simp_all add: plus_stlist_def)
    
lemma stlist_fzero_eq_sum_conv_nils2:
  fixes a :: "'a::fzero_pre_trace"
  assumes "[;a] + b = [;c] + d"
  shows "\<exists> e . [;a] = [;c] + e \<and> e + b = d \<or> [;a] + e = [;c] \<and> b = e + d"
  using assms
  proof (induct b d arbitrary: a c rule:stlist_induct_cons)
    case (1 a b)
    then show ?case by (simp add: stlist_fzero_eq_sum_conv_nils)
  next
    case (2 a x xs)
    then show ?case by (simp add: plus_stlist_def)
  next
    case (3 a y ys)
    then show ?case by (simp add: plus_stlist_def)
  next
    case (4 x xs y ys)
    have a:"([;a] + (x #\<^sub>t xs) = [;c] + (y #\<^sub>t ys))
         =
         (((a + x) #\<^sub>t xs) = ((c + y) #\<^sub>t ys))"
      by (simp add: stlist_nil_concat_cons)
    
    hence eq1:"a + x = c + y"
      using "4.prems" by blast
      
    hence eq2:"xs=ys"
      using "4.prems" a by blast
    
    from eq1 have "\<exists>e. a = c + e \<and> e + x = y \<or> a + e = c \<and> x = e + y"
      by (simp add: fzero_pre_trace_class.sum_eq_sum_conv)
        
    then have "\<exists>e. [;a] = [;c] + e \<and> e + [;x] = [;y] \<or> [;a] + e = [;c] \<and> [;x] = e + [;y]"
      by (metis stlist_plus_nils)
        
    hence "\<exists>e z. [;z] = e \<and> ([;a] = [;c] + e \<and> e + [;x] = [;y] \<or> [;a] + e = [;c] \<and> [;x] = e + [;y])"
      by (metis stlist_eq_nil_pluses_imp0)
    
    hence "\<exists>e z. [;z] = e \<and> ([;a] = [;c] + e \<and> [;z] + (x#\<^sub>txs) = (y#\<^sub>tys) \<or> [;a] + e = [;c] \<and> [;x] = [;z + y])"    
      using eq2 by (metis (no_types, lifting) "4.prems" concat_stlist.simps(1) plus_seq_assoc plus_stlist_def stlist_left_cancel_monoid0) 
    
    hence "\<exists>e z. [;z] = e \<and> ([;a] = [;c] + e \<and> [;z] + (x#\<^sub>txs) = (y#\<^sub>tys) \<or> [;a] + e = [;c] \<and> (x#\<^sub>txs) = [;z] + (y#\<^sub>tys))"
      using eq2 by (metis (no_types, lifting) "4.prems" concat_stlist.simps(1) plus_seq_assoc plus_stlist_def stlist_left_cancel_monoid0) 
    
    hence eq3:"\<exists>e. [;a] = [;c] + e \<and> e + (x#\<^sub>txs) = (y#\<^sub>tys) \<or> [;a] + e = [;c] \<and> (x#\<^sub>txs) = e + (y#\<^sub>tys)"
      by auto
        
    then show ?case by auto   
qed
    
lemma stlist_fzero_sum_eq_sum_conv:
  fixes a :: "'a::fzero_pre_trace stlist"
  shows "(a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"  
  apply (induct a c rule:stlist_induct_cons)
  apply (simp add:stlist_fzero_eq_sum_conv_nils2)+ 
  apply (case_tac d)
  apply (simp add: plus_stlist_def)
  apply (metis concat_stlist.simps(3) plus_stlist_def stlist_cons_plus_nils_eq_cons)
  apply (case_tac b)
  apply (simp add: plus_stlist_def)
  apply (metis concat_stlist.simps(3) plus_stlist_def stlist_cons_plus_nils_eq_cons)
  by (simp add: plus_stlist_def) 
  
instantiation slotted_trace :: (fzero_pre_trace_0,plus) fzero_pre_trace
begin
  
lemma slotted_fzero_sum_eq_sum_conv:
  fixes a :: "('a,'b) slotted_trace"
  shows "(a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
  using stlist_fzero_sum_eq_sum_conv
  by (smt plus_slotted_trace.rep_eq slotted2stlist_inverse stlist2slotted_dist_plus)
  
instance
  apply (intro_classes)
  by (simp add:slotted_fzero_sum_eq_sum_conv)
end
  
instantiation slotted_trace :: (fzero_pre_trace_0,plus) fzero_trace
begin
  definition less_eq_slotted_trace :: "('a,'b) slotted_trace \<Rightarrow> ('a,'b) slotted_trace \<Rightarrow> bool" where "less_eq_slotted_trace == fzero_le"
  definition minus_slotted_trace :: "('a,'b) slotted_trace \<Rightarrow> ('a,'b) slotted_trace \<Rightarrow> ('a,'b) slotted_trace" where "minus_slotted_trace == fzero_subtract"
  definition less_slotted_trace :: "('a,'b) slotted_trace \<Rightarrow> ('a,'b) slotted_trace \<Rightarrow> bool" where "less_slotted_trace a b == a \<le> b \<and> \<not> (b \<le> a)"

instance by (intro_classes, simp_all add: less_eq_slotted_trace_def less_slotted_trace_def minus_slotted_trace_def)
end
  
(* TODO: Check, are these liftings ok?
         Need to find a way of defining front, etc, so that it can be reused with 
         different types. *)
lift_definition front :: "('a::fzero_add_zero,'b) slotted_trace \<Rightarrow> ('a::fzero_add_zero,'b) slotted_trace" is "Terminated_lists.front" .
lift_definition tail :: "('a::fzero_add_zero,'b) slotted_trace \<Rightarrow> ('a::fzero_add_zero,'b) slotted_trace" is "Terminated_lists.tail" .
lift_definition head :: "('a::fzero_add_zero,'b) slotted_trace \<Rightarrow> ('a,'b) slot" is "\<lambda>x. slot2pair (Terminated_lists.head x)" .
lift_definition last :: "('a::fzero_add_zero,'b) slotted_trace \<Rightarrow> ('a,'b) slot" is "\<lambda>x. slot2pair (Terminated_lists.last x)" .
  
lemma 
  fixes a :: "('a::fzero_pre_trace_0,'b::plus) slotted_trace"
  shows "a + b = front(a) + stlist2slotted [;last(a) + head(b)] + tail(b)"
  apply (induct a)
  apply (induct b)
  apply auto
  apply (simp_all add:last_def head_def tail_def front_def)
  apply (simp add:plus_slotted_trace_def)
  apply (simp add:stlist2slotted_inject stlist2slotted_inverse front_def slot2pair_inverse)
  apply (induct_tac ya)
   apply auto
   apply (metis (mono_tags, lifting) add_fzero_left plus_seq_assoc stlist_head_concat_tail stlist_plus_nils)
  by (simp add: plus_stlist_def) 

definition subtract_x :: "'a::plus \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "-\<^sub>x" 65) where  "subtract_x t s = (THE c. t = s + c)"    
    
lemma the_left_cancel_semigroup_eq:
  "(THE c::('a::fzero_trace_0, 'b::plus) slot stlist. s + y = s + c) = (THE c. y = c)"  
  apply (rule the_equality)
  apply auto
  using left_cancel_semigroup_class.add_left_imp_eq by blast

lemma stlist2slotted_minus_simp:
  fixes t s :: "('a::fzero_trace_0, 'b::plus) slot stlist"
  assumes "stlist2slotted s \<le> stlist2slotted t"
  shows "stlist2slotted(t) - stlist2slotted(s) = stlist2slotted(t -\<^sub>x s)"
  using assms
  apply (simp add:subtract_x_def minus_slotted_trace_def fzero_subtract_def less_eq_slotted_trace_def)
  apply (rule the_equality)
   apply (simp add:stlist2slotted_dist_plus[symmetric] stlist2slotted_inject)
   apply (simp add:fzero_le_def, auto)
   apply (case_tac c, auto)
   apply (simp add:stlist2slotted_dist_plus[symmetric] stlist2slotted_inject)
   apply (simp add:the_left_cancel_semigroup_eq)
  apply (simp add:fzero_le_def, auto)
  apply (case_tac ca, auto)
  apply (simp add:stlist2slotted_dist_plus[symmetric] stlist2slotted_inject)
  apply (case_tac c, auto)
  apply (simp add:stlist2slotted_dist_plus[symmetric] stlist2slotted_inject)
  apply (simp add:the_left_cancel_semigroup_eq)
  using left_cancel_semigroup_class.add_left_imp_eq by blast
    
lemma xx: "stlist2slotted a + b - (stlist2slotted a + c) = b - c"
  by auto
    
lemma slotted_minus_prefix_diff:
  fixes t :: "('a::fzero_trace_0,'b::plus) slotted_trace"
  assumes "t \<le> s"
  shows "\<exists>pfx slot\<^sub>T slot\<^sub>S sfx. t = pfx + stlist2slotted [;slot\<^sub>T] \<and> s = pfx + stlist2slotted [;slot\<^sub>S] + sfx"
  using assms
  by (metis (no_types, lifting) fzero_slotted_trace_def fzero_trace_class.le_iff_add map_fun_apply slotted_add_fzero_right)
   
lemma 
  fixes z :: "'a::fzero_trace_0"
  assumes "[;z] \<le> [;x] + [0;y]"
  shows "([;x] + [0;y]) - [;z] = ([;x] - [;z]) + [0;y]"
  using assms
  by (metis (no_types, lifting) add.right_neutral stlist_cons_minus_nil_eq stlist_minus_nils_imp_minus stlist_nil_concat_cons trace_class.not_le_minus trace_class.sum_minus_left zero_stlist_def)

lemma 
  fixes z :: "'a::fzero_trace_0"
  assumes "[;z] \<le> [;x]"
  shows "([;x] + y) - [;z] = ([;x] - [;z]) + y"
  using assms
  using trace_class.sum_minus_left by blast

lemma xyz:
  fixes x :: "'a::fzero_trace_0"
  assumes "[;x] \<le> [y;z]"
  shows "[y;z] - [;x] = [y-x;z]"
  using assms
  using stlist_cons_minus_nil_eq by blast


      
    
lemma
  fixes t :: "'a::fzero_trace_0 stlist"
  assumes "t \<le> s"
          "t = [;slot\<^sub>t]"
          "s = [;slot\<^sub>s] + sfx"
          "sfx = [0;d]"
    shows "s - t = [;slot\<^sub>s - slot\<^sub>t] + sfx"
  using assms
  apply (induct sfx, auto)
  apply (simp add:plus_stlist_def)
  using stlist_cons_minus_nil_eq by blast

    
declare [[show_sorts]]    
lemma
  fixes t :: "('a::fzero_trace_0,'b::plus) slotted_trace"
  assumes "t \<le> s"
  shows "s - t = stlist2slotted [;pair2slot (fst(slot2pair(head(s - front(t)))),snd(slot2pair(last t)))] + tail(s - front(t))"
  using assms
  apply (simp add:plus_slotted_trace_def stlist2slotted_inverse)
  apply (simp add:stlist2slotted_dist_plus slotted2stlist_inverse)
  apply (simp add:front_def head_def last_def slot2pair_inverse)
  apply (induct s, auto)
  apply (induct t, auto)
  apply (simp add:stlist2slotted_inverse)
  apply (simp add:stlist2slotted_minus_simp)
    
lemma
  fixes t :: "('a::fzero_trace_0,'b::plus) slotted_trace"
     and slot\<^sub>t :: "('a::fzero_trace_0,'b::plus) slot"
  assumes "t \<le> s"
          "t = stlist2slotted [;slot\<^sub>t]"
          "s = stlist2slotted [;slot\<^sub>s] + sfx"
          "sfx = stlist2slotted [pair2slot(0,x);d]"
    shows "s - t = stlist2slotted [;slot\<^sub>s - slot\<^sub>t] + sfx"
  using assms
  apply auto
  apply (simp add:plus_slotted_trace_def stlist2slotted_inverse stlist2slotted_inject)
  apply (simp add:plus_slotted_trace_def stlist2slotted_inverse stlist2slotted_inject)
  apply (simp add:plus_stlist_def)
  apply (cases slot\<^sub>S)
  using stlist_cons_minus_nil_eq 
proof -
  from assms
  have "s - t = (pfx + (stlist2slotted [;slot\<^sub>s]) + sfx) - (pfx + (stlist2slotted [;slot\<^sub>T]))"
    by simp
  also have "... = stlist2slotted [;slot\<^sub>s] + sfx - stlist2slotted [;slot\<^sub>T]"
    by (simp add: add.assoc)
  also have "... = (stlist2slotted [;slot\<^sub>s] - stlist2slotted [;slot\<^sub>T]) + sfx"
    
    apply (induct sfx, auto)
    apply (case_tac y, auto)
    
    
  using assms
  apply (simp add:minus_slotted_trace_def)
  apply (simp add:plus_slotted_trace_def)
  apply (simp add:stlist2slotted_dist_plus stlist2slotted_inverse stlist2slotted_inject)
  apply (simp add: slotted2stlist_inverse)
  apply (induct pfx, auto)
  
  apply (induct sfx, auto)
  apply (simp add:stlist2slotted_inverse)
  apply (simp add:stlist2slotted_dist_plus)
  apply (simp add:xx)
  apply auto
  