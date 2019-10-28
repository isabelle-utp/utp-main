section {* Slotted Circus *}

theory utp_slotted_circus
  imports 
    Monoid_extra
    "../utils/Library_extra/Terminated_lists"
    "~~/src/HOL/Library/Prefix_Order"
begin
  
subsection {* Type definitions *}
  
subsubsection {* Slots *}
  
text {* We begin by defining a slot as a pair. We use a type definition so that
        we can instantiate particular type classes. *}
  
typedef ('\<alpha>,'\<beta>) slot = "{x::('\<alpha> \<times> '\<beta>). True}" 
  morphisms slot2pair pair2slot
  by auto
    
declare [[coercion_enabled]]
        [[coercion pair2slot]]
  
setup_lifting type_definition_slot
  
lift_definition fst\<^sub>s :: "('a,'b) slot \<Rightarrow> 'a" is "fst" .
lift_definition snd\<^sub>s :: "('a,'b) slot \<Rightarrow> 'b" is "snd" .
  
text {* Plus is defined following the definition in page 80 of @{cite "Butterfield2007"}. *}

instantiation slot :: (plus,type) plus
begin
  lift_definition plus_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot \<Rightarrow> ('a,'b) slot" 
    is "\<lambda> (h1,_) (h2,r2). (h1+h2,r2)" .

  instance by intro_classes
end

text {* Here we define an fzero for slots that is coherent with the definition of plus,
        and where we apply fzero to the trace of the parametrised type. So compared with
        @{cite "Butterfield2007"} we have a fixed definition of 'HNull', but which is
        parametrised by the type. We later show that it satisfies the required laws. *}  
  
instantiation slot :: (fzero,type) fzero
begin
  lift_definition fzero_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot" is
    "\<lambda> (h1,r1). (fzero h1,r1)" .
    
  instance by intro_classes
end
  
text {* By instantiating the type class fzero_add_zero, we also instantiate fzero_idem
        and semigroup_add_fzero. The former requires fzero to be idempotent, while the
        latter requires that plus forms a semigroup (semigroup_add).
        
        In addition, as part of the type class fzero_add_zero, we also need to show
        that fzero a is both a left-zero as well as a right-zero, for any value of a.*}  
  
instantiation slot :: (fzero_add_zero,type) fzero_add_zero
begin
  
instance 
  apply intro_classes
  by (simp_all add:fzero_slot_def plus_slot_def add.assoc pair2slot_inverse slot2pair_inverse split_beta)
end

text {* We also instantiate the class fzero_sum_zero which requires that if the addition
        of two elements (a + b) yields fzero(b), then b must be equal to fzero(b). This
        is a mirror type class of monoid_sum_0.*}
  
instantiation slot :: (fzero_sum_zero,type)  fzero_sum_zero
begin
instance
  apply intro_classes
  by (metis (mono_tags, lifting) fzero_slot.rep_eq fzero_sum_right plus_slot.rep_eq prod.collapse prod.sel(1) slot2pair_inverse split_beta)
end
  
text {* Provided the parametrised trace forms a left cancellative semigroup, and given
        our definition of plus, we also have a left cancellative semigroup. *}  
  
instantiation slot :: (left_cancel_semigroup,type) left_cancel_semigroup
begin
instance apply intro_classes
    apply (simp add:plus_slot_def)
    by (smt Pair_inject left_cancel_semigroup_class.add_left_imp_eq plus_slot.rep_eq prod.collapse slot2pair_inverse split_beta)
end
  
text {* We then instantiate the type class fzero_pre_trace that requires that
        sum_eq_sum_conv holds. *}  
  
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
    using mem_Collect_eq pair2slot_inject plus_slot.rep_eq prod.simps(2) slot2pair_inverse
    by smt
      
  have c':"c + d = pair2slot (ch+dh,dr)"
    using c and d
    using mem_Collect_eq pair2slot_inject plus_slot.rep_eq prod.simps(2) slot2pair_inverse
    by smt
    
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
  
text {* Finally we instantiate the fzero_trace class, with the only requirement being that the
        parametrised trace must be of type class fzero_pre_trace. *}
    
instantiation slot :: (fzero_trace,type) fzero_trace
begin
  
  definition less_eq_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot \<Rightarrow> bool" where "less_eq_slot == fzero_le"
  definition minus_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot \<Rightarrow> ('a,'b) slot" where "minus_slot == fzero_subtract"
  definition less_slot :: "('a,'b) slot \<Rightarrow> ('a,'b) slot \<Rightarrow> bool" where "less_slot a b == a \<le> b \<and> \<not> (b \<le> a)"
    
instance 
  apply (intro_classes, simp_all add: less_eq_slot_def less_slot_def minus_slot_def slot_sum_eq_conv)
  using left_cancel_semigroup_class.add_left_imp_eq by blast
end
  
text {* As it turns out, this structure satisfies an axiom stronger than left-identity
        with respect to the USTA axioms. *}  
  
instantiation slot :: (fzero_trace,type) fzero_add_any_trace
begin
instance
  apply (intro_classes)
    by (metis semigroup_add_left_cancel_minus_ord_class.add_diff_cancel_left semigroup_add_left_cancel_minus_ord_class.diff_zero)
end
  
lemma slot_least_elem:
  fixes d :: "('a::fzero_trace_0,'b) slot"
  shows "pair2slot (0, SOME d. True) \<le> d"
proof -
  have "pair2slot (0, SOME d. True) \<le> d
        =
        (\<exists>c. d = pair2slot (0, SOME d. True) + c)"
       by (simp add:less_eq_slot_def fzero_le_def)
      
  obtain y where y:"pair2slot(fst(slot2pair(d)), snd(slot2pair(d))) = y" by auto
  
  then have "(d = pair2slot (0, SOME d. True) + y)"
    by (simp add:plus_slot_def pair2slot_inverse slot2pair_inverse)
    
  then show ?thesis using less_eq_slot_def fzero_le_def y
    by auto
qed
  
  
lemma slotted_stlist_least_elem:
  fixes d ::"('a::fzero_trace_0,'b) slot stlist"
  shows "[;pair2slot (0, SOME d. True)] \<le> d"
proof -
  have "d = [;pair2slot (0, SOME d. True)] + d"
  proof -
    have "head d = pair2slot (0, SOME B. True) + head d"
      by (simp add: pair2slot_inverse plus_slot_def slot2pair_inverse)
    then show ?thesis
      by (metis (no_types) add.assoc concat_stlist.simps(1) plus_stlist_def stlist_head_concat_tail)
  qed
  
  then show ?thesis
    using less_eq_stlist_def 
    by (metis fzero_le_add)
qed
    
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
  
text {* The following lemma makes it clear that the preorder over the slots only depends
        on the relation between histories, and not the refusals, as we expect. *}  
  
lemma slot_le_iff_histories_le:
  fixes h2 :: "'a::fzero_trace"
  shows "pair2slot (h2,r2) \<le> pair2slot (h1,r1) \<longleftrightarrow> h2 \<le> h1"
  by (meson leq_histories_imp_pair2slot_le pair2slot_le_imp_leq_histories)

text {* We show in the following lemma that our definition of plus corresponds
        to that of Sadd in page 80 of @cite{"Butterfield2007"}. *}
    
lemma slot_plus_2:
  fixes h1 :: "'a::fzero_trace"
  shows "pair2slot (h1,r1) + pair2slot (h2,r2) = pair2slot(h1+h2,r2)"
  apply (simp add:plus_slot_def)    
  by (simp add:pair2slot_inject pair2slot_inverse)
    
text {* The following lemma corresponds to the definition of Ssub in page 80 of 
        @cite{"Butterfield2007"}. Rather than a definition we have it as a lemma.

        Just like in the discussion in @cite{"Butterfield2007"} that requires
        h2 \<le> h1 for minus to be well defined, we also require this assumption. *}      

lemma slot_minus_2:
  fixes h1 :: "'a::fzero_trace"
  assumes "h2 \<le> h1"
  shows "pair2slot (h1,r1) - pair2slot (h2,r2) = pair2slot(h1-h2,r1)"
  apply (simp add:minus_slot_def fzero_subtract_def le_is_fzero_le fzero_le_def)
  apply auto
  apply (case_tac c)
  apply auto
  apply (simp add:plus_slot_def)
  apply (rule the_equality)
  apply (metis (no_types, lifting) add_diff_cancel_left mem_Collect_eq pair2slot_inverse prod.sel(1) prod.sel(2) split_beta)
  apply (metis (no_types, lifting) Pair_inject add_diff_cancel_left mem_Collect_eq pair2slot_inject prod.collapse slot2pair_inverse split_beta)
  apply (simp add:fzero_slot_def pair2slot_inverse pair2slot_inject)
  using assms slot_le_iff_histories_le 
  by (metis semigroup_add_left_cancel_minus_ord_class.le_iff_add)
  
subsubsection {* Synchronous traces *}    
  
text {* The traces are defined using the type for non-empty lists 'stlist'. *}
  
type_synonym ('\<alpha>,'\<beta>) slotted_trace = "('\<alpha>,'\<beta>) slot stlist"
    
text {* We then show that a slotted trace satisfies sum_eq_sum_conv by breaking the proof into
        multiple lemmas, where we treat the base cases separately from the main proof.*}  

(* TODO: Move these into stlist theory file? *)  
  

text {* We then instantiate slotted_trace with the type class fzero_pre_trace.*}    

instance fzero_pre_trace_0 \<subseteq> fzero_pre_trace
  by intro_classes

lemma stlist_strict_prefix_eq:
  fixes t :: "'a::fzero_trace"
  shows "t < s \<longrightarrow> (\<exists>z. t + z = s \<and> z \<noteq> fzero t)"
  by (metis add_fzero_right less_le_not_le semigroup_add_left_cancel_minus_ord_class.le_iff_add)
    
lemma stlist_head_front_last_slotted:
  fixes t :: "('a::fzero_trace,'b::plus) slotted_trace"
  assumes "t \<le> s"
  shows "[;head(s - (front(t) + [;last(t)]))] = [;head(s - front(t)) - last(t)]"
  using assms
  using stlist_head_front_last by blast
 
lemma the_left_cancel_semigroup_eq:
  "(THE c::('a::fzero_trace_0, 'b::plus) slot stlist. s + y = s + c) = (THE c. y = c)"  
  apply (rule the_equality)
  apply auto
  using left_cancel_semigroup_class.add_left_imp_eq by blast

lemma slotted_minus_prefix_diff:
  fixes t :: "('a::fzero_trace,'b) slotted_trace"
  assumes "t \<le> s"
  shows "\<exists>pfx slot\<^sub>T slot\<^sub>S sfx. t = pfx + [;slot\<^sub>T] \<and> s = pfx + [;slot\<^sub>S] + sfx"
  using assms
  by (metis semigroup_add_left_cancel_minus_ord_class.le_iff_add stlist_front_concat_last)
    
lemma prefix_minus_plus_eq:
  fixes x :: "'a::fzero_trace"
  assumes "t \<le> s"
  shows "(s - t) + x = (s + x) - t"
  using assms
  by (simp add: semigroup_add_left_cancel_minus_ord_class.sum_minus_left)
    
lemma fzero_add_any_trace_stlist_plus_nils:
  fixes s :: "'a::fzero_add_any_trace"
  assumes "t \<le> s"
  shows "[;s + x] - [;t] = [;s - t + x]"
proof -
  have "t \<le> s + x"
    using assms order_trans semigroup_add_left_cancel_minus_ord_class.le_add by blast
  then have "[;s + x] - [;t] = [;(s + x) - t]"
    using stlist_minus_imp_minus_nils by blast
  also have "... = [;s - t + x]"
    using assms semigroup_add_left_cancel_minus_ord_class.sum_minus_left by blast
  finally show ?thesis .
qed
  
lemma stlist_nil_plus:
  "[;s - t + x] = [;s - t] + [;x]"
  by (metis stlist_plus_nils)
              
lemma
  fixes sfx :: "('a::fzero_trace_0,'b) slotted_trace"
  shows "[;f0(b)] + sfx = sfx"
  by (metis Terminated_lists.last.simps(1) add_fzero_any_left fzero_stlist_def)
  
lemma slotted_trace_le_front_le:
  fixes t :: "('a::fzero_trace,'b) slotted_trace"
  assumes "t \<le> s"
  shows "front(t) \<le> s" 
  using assms
  apply (simp add: less_eq_stlist_def)
  by (metis le_add less_eq_stlist_def stlist_front_concat_last fzero_le_trans)
      
lemma stlist_front_prefix_imp:
  fixes y :: "'a::fzero_add_zero_any stlist"
  assumes "y \<le> ya"
  shows "front(y) \<le> ya"
  using assms
  apply (induct y, auto)
   apply (cases ya, auto)
    apply (simp_all add:less_eq_stlist_def fzero_le_def)
    apply (metis front.simps(1) plus_seq_assoc stlist_front_concat_last)
   apply (metis add.assoc front.simps(1) stlist_front_concat_last)
  by (metis add.assoc front.simps(2) stlist_front_concat_last)
    
lemma pair2slot_fst_snd_slot2pair: "pair2slot(fst (slot2pair x), snd (slot2pair x)) = x"
  by (auto simp add:slot2pair_inverse)
    
lemma 
  fixes a :: "'a::fzero_trace"
  shows "([;pair2slot(a,b)]) - ([;pair2slot(a,b)]) = ([;pair2slot(f0(a),b)])"
  apply (auto)
  apply (simp add:fzero_stlist_def)
  by (simp add:fzero_slot_def pair2slot_inverse)    

lemma x1:
  fixes a b :: "'a::fzero_trace_0"
  shows "([;pair2slot(a,r\<^sub>0)]) + ([pair2slot(0,r\<^sub>0);pair2slot(b,r\<^sub>1)])
         =
         ([pair2slot(a,r\<^sub>0);pair2slot(b,r\<^sub>1)])"
  by (metis (no_types, lifting) add.monoid_axioms monoid.right_neutral slot_plus_2 stlist_nil_concat_cons)

lemma x2:
  fixes a b :: "'a::fzero_trace_0"
  shows "([pair2slot(a,r\<^sub>0);pair2slot(b,r\<^sub>1)]) + ([pair2slot(0,r\<^sub>1);pair2slot(c,r\<^sub>2)])
         =
         ([pair2slot(a,r\<^sub>0),pair2slot(b,r\<^sub>1);pair2slot(c,r\<^sub>2)])"
  by (smt Quotient_rep_abs_eq concat_stlist.simps(3) eq_onp_True eq_onp_le_eq plus_stlist_def x1)

lemma x3:
  fixes a b :: "'a::fzero_trace_0"
  shows "([pair2slot(a,r\<^sub>0);pair2slot(d,r\<^sub>1)]) + ([pair2slot(b,r\<^sub>1);pair2slot(c,r\<^sub>2)])
         =
         ([pair2slot(a,r\<^sub>0),pair2slot(d+b,r\<^sub>1);pair2slot(c,r\<^sub>2)])"
  by (metis (no_types, lifting) concat_stlist.simps(3) plus_stlist_def slot_plus_2 stlist_cons_plus_nils_eq_cons)

(* TODO: Move this into Monoid_extra.thy *)    
lemma subtract_iff_plus:
  fixes a :: "'a::trace"
  assumes "b \<le> a"
  shows "a - b = c \<longleftrightarrow> b + c = a"
  by (metis assms pre_trace_class.add_monoid_diff_cancel_left trace_class.le_iff_add trace_class.minus_def)

lemma fzero_trace_subtract_iff_plus:
  fixes a :: "'a::fzero_trace"
  assumes "b \<le> a"
  shows "a - b = c \<longleftrightarrow> b + c = a"
  using assms diff_add_cancel_left' by auto
    
lemma 
  fixes a b :: "'a::fzero_trace_0"
  shows "([pair2slot(a,r\<^sub>0);pair2slot(b,r\<^sub>1)]) - ([;pair2slot(a,r\<^sub>0)]) 
         = 
         ([pair2slot(0,r\<^sub>0);pair2slot(b,r\<^sub>1)])"
  using x1   
  by (metis add_diff_cancel_left)
    
lemma 
  fixes a b :: "'a::fzero_trace_0"
  shows "([pair2slot(a,r\<^sub>0),pair2slot(b,r\<^sub>1);pair2slot(c,r\<^sub>2)]) 
         - ([pair2slot(a,r\<^sub>0);pair2slot(b,r\<^sub>1)]) 
         = 
         ([pair2slot(0,r\<^sub>1);pair2slot(c,r\<^sub>2)])"
  by (metis add_diff_cancel_left x2)
        
lemma 
  fixes a b :: "'a::fzero_trace_0"
  assumes 
    "d \<le> b"
  shows "([pair2slot(a,r\<^sub>0),pair2slot(b,r\<^sub>1);pair2slot(c,r\<^sub>2)]) 
         - ([pair2slot(a,r\<^sub>0);pair2slot(d,r\<^sub>1)]) 
         = 
         ([pair2slot(b-d,r\<^sub>1);pair2slot(c,r\<^sub>2)])"
  by (metis assms add_diff_cancel_left diff_add_cancel_left' x3)

lemma
  fixes t :: "('a::fzero_trace,'b::plus) slotted_trace"
  assumes "s \<le> t"
  shows "head(t-s) = head(t-front(s)) - last(s)"
  using assms stlist_head_minus_last_eq_head 
  oops
    
lemma fsts_minus_dist:
  fixes t :: "('a::fzero_trace,'b) slot"
  assumes "s \<le> t"
  shows "fst\<^sub>s(t - s) = fst\<^sub>s(t) - fst\<^sub>s(s)"
  using assms
proof -
  have "eq_onp (\<lambda>p. True) (fst (slot2pair t) - fst (slot2pair s), snd (slot2pair t)) (fst (slot2pair t) - fst (slot2pair s), snd (slot2pair t))"
    by (simp add: eq_onp_True)
  then show ?thesis
    by (metis (no_types) assms fst\<^sub>s.abs_eq fst\<^sub>s.rep_eq pair2slot_fst_snd_slot2pair pair2slot_le_imp_leq_histories prod.sel(1) slot_minus_2)
qed
    
lemma snds_head_minus_last:
  fixes t :: "('a::fzero_trace,'b) slotted_trace"
  assumes "s \<le> t"
  shows "snd\<^sub>s(head(t-front(s)) - last(s)) = snd\<^sub>s(head(t-front(s)))"
  using assms slot_minus_2
  by (smt eq_onp_True map_fun_apply pair2slot_fst_snd_slot2pair pair2slot_le_imp_leq_histories prod.sel(2) slot2pair_inverse snd\<^sub>s.abs_eq  stlist_front_prefix_imp stlist_last_le_head_minus_front last_def)
  (* there is a nicer proof for this *)
    
(* Key theorem in original definition of R2 for Circus Time *)
lemma slotted_trace_diff:
  fixes t :: "('a::fzero_trace,'b) slotted_trace"
  assumes "s \<le> t"
  shows "t - s = [;pair2slot (fst\<^sub>s(head(t - front(s)))-fst\<^sub>s(last(s)),snd\<^sub>s(head(t-front(s))))] + tail(t - front(s))"
proof -
  have "t - s = [;head(t-s)] + tail(t-s)"
    using stlist_head_concat_tail
    by (metis (no_types, lifting) map_fun_apply slot2pair_inject tail_def)
  also have "... = [;head(t-front(s)) - last(s)] + tail(t-s)"
    using assms stlist_head_minus_last_eq_head 
    by (smt eq_onp_True map_fun_apply slot2pair_inverse stlist_front_prefix_imp last_def)
  also have "... = [;head(t-front(s)) - last(s)] + tail(t - front(s))"   
    using assms
    by (metis (no_types, lifting) stlist_front_prefix_imp stlist_tail_minus_eq_tail_minus_front)
  also have "... = [;pair2slot(fst\<^sub>s(head(t-front(s)) - last(s)),
                                              snd\<^sub>s(head(t-front(s)) - last(s)))] + tail(t - front(s))"
    by (simp add: fst\<^sub>s.rep_eq slot2pair_inverse snd\<^sub>s.rep_eq)
  also have "... = [;pair2slot(fst\<^sub>s(head(t-front(s))) - fst\<^sub>s(last(s)),
                                              snd\<^sub>s(head(t-front(s)) - last(s)))] + tail(t - front(s))"
    using assms stlist_last_le_head_minus_front fsts_minus_dist
    by (smt eq_onp_True map_fun_apply slot2pair_inverse stlist_front_prefix_imp last_def)
  also have "... = [;pair2slot(fst\<^sub>s(head(t-front(s))) - fst\<^sub>s(last(s)),
                                              snd\<^sub>s(head(t-front(s))))] + tail(t - front(s))"
    using assms  
    by (simp add: snds_head_minus_last)
      
  finally show ?thesis .
qed
  
lemma less_eq_slotted_trace_imp:
  fixes t :: "('a::fzero_trace,'b) slotted_trace"
  assumes "s \<le> t"
  shows "fst\<^sub>s(last(s)) \<le> fst\<^sub>s(head(t - front(s)))"
  by (metis assms fst\<^sub>s.rep_eq pair2slot_fst_snd_slot2pair pair2slot_le_imp_leq_histories stlist_last_le_head_minus_front)
    
lemma
  fixes t :: "('a::fzero_trace,'b) slotted_trace"
  assumes "s \<le> t"
  shows "front(s) \<le> t \<and> fst\<^sub>s(last(s)) \<le> fst\<^sub>s(head(t - front(s)))"
  by (simp add: assms less_eq_slotted_trace_imp stlist_front_prefix_imp)
    
lemma 
  fixes a :: "('a::fzero_trace,'b) slotted_trace"
  shows "a + b = front(a) + [;last(a) + head(b)] + tail(b)"
  apply (induct a)
  apply (induct b)
  by (simp_all add: add.assoc plus_stlist_def)
end