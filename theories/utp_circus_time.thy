section {* Circus Time model *}

theory utp_circus_time
  imports 
    utp_cml
    "../utils/Library_extra/Terminated_lists"
    "~~/src/HOL/Library/Prefix_Order"
begin
  
(* Mini theory of option sets *)
  
(*
typedef '\<alpha> opset = "{x::'\<alpha> option set. True}" by auto
 *)
  
datatype '\<alpha> opset = None ("\<bullet>") | Some "'\<alpha> set"
  
fun opset_add :: "'\<alpha> opset \<Rightarrow> '\<alpha> opset \<Rightarrow> '\<alpha> opset" where
"opset_add s z = z"

lemma opset_add_left_zero:
  "opset_add \<bullet> s = s"
  apply (induct s rule:opset.induct)
  by simp_all
    
lemma opset_add_right_zero:
  "opset_add s \<bullet> = s"
  by (simp only:opset_add.simps(1))
    
lemma opset_assoc:
  "opset_add a (opset_add b c) = opset_add (opset_add a b) c"
  apply (induct a)
  apply (induct b, auto)
  apply (induct c, auto)
  apply (simp add: opset_add_left_zero)
  by (metis opset_add.elims opset_add.simps(1))

instantiation opset :: (type) zero
begin
   definition zero_opset :: "'a opset" where "zero_opset == \<bullet>"
   instance by (intro_classes)
end
  
instantiation opset :: (type) plus
begin
  definition plus_opset :: "'a opset \<Rightarrow> 'a opset \<Rightarrow> 'a opset" where "plus_opset == opset_add"
  instance by (intro_classes)
end  
  
instantiation opset :: (type) monoid_add
begin
instance 
  apply (intro_classes)
  apply (simp add:plus_opset_def opset_assoc)
  apply (simp add:plus_opset_def zero_opset_def opset_add_left_zero)
  by (simp add:plus_opset_def zero_opset_def)
end

instantiation opset :: (type) minus
begin
  definition minus_opset :: "'a opset \<Rightarrow> 'a opset \<Rightarrow> 'a opset" where "minus_opset == monoid_subtract"
  instance by intro_classes
end 
   
no_adhoc_overloading uconj conj
no_adhoc_overloading udisj disj  
no_adhoc_overloading unot Not   
  
instantiation opset :: (type) ord
begin
definition less_eq_opset :: "'a opset \<Rightarrow> 'a opset \<Rightarrow> bool" where "less_eq_opset == monoid_le"
definition less_opset :: "'a opset \<Rightarrow> 'a opset \<Rightarrow> bool" where "less_opset a b == a \<le> b \<and> \<not> (b \<le> a)"
  
instance by intro_classes
end
  
adhoc_overloading uconj conj
adhoc_overloading udisj disj  
adhoc_overloading unot Not
  
lemma 
  fixes a :: "'a opset"
  shows "a + b = a + c \<Longrightarrow> b = c"
  oops
    
lemma 
  fixes a :: "'a opset"
  shows "b + a = c + a \<Longrightarrow> b = c"
  
instantiation opset :: (type) left_cancel_monoid
begin
  
    
  
lemma 
  fixes a :: "'a::pre_trace"
  assumes "a \<le> b"
  shows "b - a = 0 \<longleftrightarrow> a = b"
  using assms
  apply auto
  using minus_zero_eq by auto
  
declare [[show_sorts]]  
  
lemma
   assumes "x \<bowtie> y" "y \<sharp> P"
  shows "y \<sharp> (\<exists> x \<bullet> P)"
  oops
    
lemma
  assumes "x \<sharp> P"
  shows "(\<exists>x \<bullet> P) = P"
  using assms
    
lemma
  assumes "P\<lbrakk>e/x\<rbrakk> = P"
  shows "x \<sharp> P"
  using assms
  apply pred_simp
  apply auto
  nitpick
    
lemma
  assumes "x \<sharp> P"
  shows "(\<exists>x \<bullet> P) = P \<longleftrightarrow> (P\<lbrakk>e/x\<rbrakk> = P)"
  using assms
  by pred_simp
    
lemma
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "e \<noteq> &x"
  shows "(\<exists>x \<bullet> P) = P \<longleftrightarrow> (P\<lbrakk>e/x\<rbrakk> = P)"
  using assms
  apply pred_simp
  nitpick
  sledgehammer
  

(* Need to revise this given the new trace algebra *)  
  
subsection {* Types *}

text {* A trace of events is a list. *}  

typedef '\<alpha> trace = "{x::'\<alpha>::trace. True}" by auto
    
(* Then show it is an instance of the type class by lifting *)

(* Then typedef refusal and define plus *)    
    
(* Then define the slots as (trace,refusal) *)

(* Question: - is there any use for a trace parametrised by something
             other than events? 

             - in a reactive theory is there any healthiness condition
             relating trace and refusals? *)    
    
(*  
typedef '\<alpha> trace = "{x::'\<alpha>::trace. True}" by auto
   
setup_lifting type_definition_trace  
    
instantiation trace :: (type) trace
begin
end

*)
    
lemma
  fixes a :: "'\<alpha> trace"
  shows "a + b = c"
  
  
text {* We define a separate type for refusals, a set of events, so that
        we can instantiate it with specific type classes, separate from
        the generic set type. *}  
  
typedef      '\<alpha> refusal = "{x::'\<alpha> set. True}" 
  morphisms refusal2set set2refusal
  by auto

text {* Two morphisms are defined between this type and that of generic sets,
        refusal2set from refusal to set, and set2refusal in the opposite
        direction. *}
    
text {* We set-up the lifting package to provide support for lifting on the
        new declared type refusal. Furthermore we also enable default coercion
        from sets to this refusal type below. *}  
  
setup_lifting type_definition_refusal    
declare [[coercion_enabled]]
        [[coercion set2refusal]]
        
text {* We now define the zero for refusals as the empty set by lifting
        from sets. *}
   
instantiation refusal :: (type) zero
begin
   lift_definition zero_refusal :: "'a refusal" is "{}" ..
   instance by (intro_classes)
end  
 
text {* As for the difference operator, we actually have a choice between 
        lifting to set difference, or using the monoid_subtract. If we use
        monoid_subtract then we need to instantiate refusals as monoid_add,
        where plus is lifted from set union.*}  
 
instantiation refusal :: (type) monoid_add
begin
   lift_definition plus_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal" is "op \<union>" .

   instance by (intro_classes,(transfer,auto)+)
end
  
instantiation refusal :: (type) monoid_sum_0
begin
  
   instance by (intro_classes,(transfer,auto)+)
end

no_adhoc_overloading uconj conj
no_adhoc_overloading udisj disj  
no_adhoc_overloading unot Not 
  (*
instantiation refusal :: (type) ord
begin
   definition less_eq_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" where "less_eq_refusal == monoid_le"
   definition less_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" where "less_refusal x y == x \<le> y \<and> \<not> (y \<le> x)"
  
lemma refusal_zero_least:
  fixes a :: "'a refusal"
  shows "0 \<le> a"
  apply (simp add:zero_refusal_def)  
  apply (transfer, auto)
  by (metis add.left_neutral monoid_le_def utp_circus_time.less_eq_refusal_def zero_refusal_def)
    
   instance by intro_classes
end*)

adhoc_overloading uconj conj
adhoc_overloading udisj disj  
adhoc_overloading unot Not 
  
instantiation refusal :: (type) minus
begin
  definition minus_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal" where "minus_refusal == monoid_subtract"
  
(*lift_definition minus_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal" is "op -" .

  lemma refusal_zero_minus_zero:
  "(0::'a refusal) - 0 = 0"
  by (simp add:minus_refusal_def zero_refusal_def)*)
      
  lemma refusal_zero_minus_zero:
  "(0::'a refusal) - 0 = 0"
    apply (simp add:minus_refusal_def zero_refusal_def monoid_subtract_def)
    by (metis (mono_tags, lifting) add.left_neutral the_equality zero_refusal.abs_eq)
    
  instance by (intro_classes)
end
  
text {* The point with these instantiations is that we can then define
        the type ttrace as an stlist of pairs (trace \<times> refusal) below.
        
        We observe that in general this does not yield an ordered
        cancelative monoid, as there is no injective function from 
        a pair of sets to sets. *}
  
type_synonym '\<alpha> ttrace = "('\<alpha> \<times> '\<alpha> refusal) stlist"
  
text {* To achieve a trace algebra, we define the type of circus
        time traces (cttrace) as a ttrace, where the refusal of the 
        ttrace is always empty (the zero). *}
  
typedef '\<alpha> cttrace = "{ct::'\<alpha> ttrace. snd(last(ct)) = 0}"
morphisms ct2ttrace ttrace2ct
  by (auto, metis Terminated_lists.last.simps(1) prod.sel(2))
 
text {* Just as before, we have two morphisms, ct2ttrace from cttrace
        to ttrace and ttrace2ct in the opposite direction. *}    
    
value ct2ttrace  
value ttrace2ct

declare [[coercion ttrace2ct]]
    
setup_lifting type_definition_cttrace

  (*
lemma cttrace_snd_last_0_minus:
  fixes s z :: "('a list \<times> 'a refusal) stlist"
  shows "snd (last s) = 0 \<and> snd (last z) = 0 \<Longrightarrow> snd ((last z) - (last s)) = 0"
  apply auto
  by (simp add:refusal_zero_minus_zero)
    
lemma cttrace_snd_last_0_minus2:
  fixes s z :: "('a list \<times> 'a refusal) stlist"
  shows "\<forall> (s::('a list \<times> 'a refusal) stlist) z. snd (last s) = 0 \<and> snd (last z) = 0 \<longrightarrow> snd ((last z) - (last s)) = 0"
  apply auto
  by (simp add:refusal_zero_minus_zero)
    
lemma stlist_last_minus_property:
  fixes s z :: "'a::ordered_cancel_monoid_diff stlist"
  assumes "s < z"
  and "\<forall>x y. P (last x) \<and> P (last y) \<longrightarrow> P ((last x) - (last y))" 
  shows "P (last z) \<and> P (last s) \<Longrightarrow> P (last (z - s))"
  unfolding minus_stlist_def
  using assms
  apply (induct z s rule:stlist_induct_cons)
  apply (metis Terminated_lists.last.simps(1) minus_stlist_def stlist_nil_minus)
  apply simp_all
  apply (metis Terminated_lists.last.simps(2) less_imp_le minus_stlist_def stlist_cons_minus_nil_eq) 
  apply (metis concat_stlist.simps(3) diff_add_cancel_left' less_imp_le plus_stlist_def stlist.distinct(1))
  by (metis add_monoid_diff_cancel_left concat_stlist.simps(3) diff_add_cancel_left' le_add less_stlist_def plus_stlist_def stlist.inject(2))
  *)

text {* We now show that cttrace is an additive monoid with any parametrised
        type by lifting the definition of zero and plus from stlist. *}

instantiation cttrace :: (type) monoid_add
begin
  
  lift_definition zero_cttrace :: "'a cttrace" is "0"
    by (simp add: zero_stlist_def)
  
  text {* The lifting of plus relies on proving closure of cttrace under plus,
          that is, the second component of nil is empty. *}
    
  lift_definition plus_cttrace :: "'a cttrace \<Rightarrow> 'a cttrace \<Rightarrow> 'a cttrace" is "op +"
    apply (case_tac stlist2)
    apply (case_tac stlist1)
    apply (simp add: plus_stlist_def)
    apply (simp add: stlist_last_concat3)
    by (simp add: stlist_last_concat)
  
  instance 
    apply (intro_classes)
    apply (metis (mono_tags, lifting) ct2ttrace_inject plus_cttrace.rep_eq plus_seq_assoc)
    using ct2ttrace_inject plus_cttrace.rep_eq zero_cttrace.rep_eq apply fastforce
    using ct2ttrace_inject plus_cttrace.rep_eq zero_cttrace.rep_eq by fastforce
end
  
text {* To show that cttrace forms a trace algebra we need to show that
        ttrace satisfies the monoid laws under the assumption that the 
        second component of the nil element is empty. *}
  
lemma ct2ttrace_ttrace2ct_eq:
  fixes a :: "'a ttrace"
  assumes "snd(last a) = 0"
  shows "ct2ttrace (ttrace2ct a) = a"
  using assms
  apply (induct a)
  apply auto
  apply (simp add: ttrace2ct_inverse)
  by (simp add: ttrace2ct_inverse)
  
lemma ttrace2ct_dist_plus:
  assumes "snd(last a) = 0" and "snd(last b) = 0"
  shows "ttrace2ct (a + b) = ttrace2ct a + ttrace2ct b"
  using assms
  apply (simp add:plus_stlist_def plus_cttrace_def)
  by (simp add:ct2ttrace_ttrace2ct_eq)

thm cttrace.ct2ttrace_inject    

text {* Below we reprove the left cancelative monoid lemmas for ttrace. *}
  
lemma ttrace_left_zero_cancel:
  fixes a :: "'\<alpha> ttrace"
  assumes "snd(last a) = 0"
  and "snd(b) = 0"
  and "snd(c) = 0"
  shows "a + [;b] = a + [;c] \<Longrightarrow> [;b] = [;c]"
  using assms
  unfolding plus_stlist_def
  apply (induct a)
  apply auto
  by (metis fst_add left_cancel_monoid_class.add_left_imp_eq prod.collapse)

lemma ttrace_left_cancel_monoid0:
  fixes b c :: "'\<alpha> ttrace"
  assumes "snd(a) = 0"
  and "snd(last b) = 0"
  and "snd(last c) = 0"
  shows "[;a] + b = [;a] + c \<Longrightarrow> b = c"
  using assms
  unfolding plus_stlist_def
  apply (induct rule:stlist_induct_cons)
  apply auto
  apply (metis fst_add fst_conv left_cancel_monoid_class.add_left_imp_eq)
  apply (metis fst_add fst_conv left_cancel_monoid_class.add_left_imp_eq)
  by (metis add.left_neutral snd_add snd_conv)        

lemma ttrace_left_cancel_monoid:
  fixes a b c :: "'\<alpha> ttrace"
  assumes "snd(last a) = 0"
  and "snd(last b) = 0"
  and "snd(last c) = 0"
  shows "a + b = a + c \<Longrightarrow> b = c"
  using assms
  apply (induct a rule:stlist.induct)
  using ttrace_left_cancel_monoid0 apply auto[1]
  by (simp add: plus_stlist_def)
    
text {* Below we reprove the right cancelative monoid lemmas for ttrace. *}

lemma ttrace_right_cancel_monoid0:
  fixes b c :: "'\<alpha> ttrace"
  assumes "snd(a) = 0"
  and "snd(last b) = 0"
  and "snd(last c) = 0"
  shows "(b + [;a] = c + [;a]) \<Longrightarrow> b = c"
  using assms
  unfolding plus_stlist_def
  apply (induct b c rule:stlist_induct_cons, auto)
  by (metis fst_add fst_conv right_cancel_monoid_class.add_right_imp_eq)

lemma ttrace_right_cancel_monoid1:
  fixes b c :: "'\<alpha> ttrace"
  assumes  "snd(d) = 0"
  and "snd(last b) = 0"
  and "snd(last c) = 0"
  shows "(b + [a;d] = c + [a;d]) \<Longrightarrow> b = c"
  using assms
  unfolding plus_stlist_def
  apply (induct b c rule:stlist_induct_cons, auto)
  apply (metis fst_add fst_conv right_cancel_monoid_class.add_right_imp_eq)
  apply (case_tac "xs", simp+)
  by (case_tac "ys", simp+)
    
lemma ttrace_right_cancel_monoid2:
  fixes a :: "'\<alpha> ttrace"
  shows "(b#\<^sub>ta) = (c#\<^sub>ta) \<Longrightarrow> b = c"  
  by auto
    
lemma ttrace_zero_monoid_sum:
  fixes a :: "'\<alpha> ttrace"
  assumes "snd(last a) = 0"
  and "snd(last b) = 0"
  shows "a + b = 0 \<Longrightarrow> a = 0"
  using assms
  apply (induct a b rule:stlist_induct_cons)
  apply (smt Terminated_lists.last.simps(1) add.right_neutral concat_stlist.simps(1) fst_add fst_zero plus_prod_def plus_stlist_def snd_zero zero_sum_right)
  by (simp add: plus_stlist_def zero_stlist_def zero_sum_left)+     
    
lemma ttrace_plus_follow_concat:
  fixes a c :: "'\<alpha> ttrace"
  shows "a + (b #\<^sub>t c) = a + [b;0] + c"
  by (metis concat_stlist.simps(3) plus_seq_assoc plus_stlist_def stlist_concat_zero_left)

lemma last_concat_pair:
  shows "last (b + [x1a; 0]) = 0"
  by (simp add: stlist_last_concat)

lemma snd_last_concat_pair:
  shows "snd(last (b + [x1a; 0])) = 0"
  by (simp add: stlist_last_concat)    
    
lemma ttrace_plus_closure:
  fixes a b :: "'\<alpha> ttrace"
  assumes "snd(last a) = 0"
  and "snd(last b) = 0"
  shows "snd(last (a+b)) = 0"
  using assms
  apply (induct a b rule:stlist_induct_cons)
  apply auto
  apply (simp add: plus_stlist_def)
  apply (simp add: stlist_last_concat3)
  by (simp add: stlist_last_concat)+

    (*
lemma trace_refusal_right_cancel:
  fixes b1 :: "'\<alpha> trace" and b2 :: "'\<alpha> refusal" and a :: "('\<alpha> trace \<times> '\<alpha> refusal)"
  assumes "b2 = 0" and "c2 = 0"
  shows "((b1, b2) + a) = ((c1, c2) + a) \<Longrightarrow> ((b1 = c1) \<and> (b2 = c2))"
  using assms
  by (metis fst_add fst_conv right_cancel_monoid_class.add_right_imp_eq)
    *)
    
lemma ttrace_right_cancel_monoid3:
  fixes c :: "'\<alpha> ttrace"
  shows "[;(a, 0)] + c = [;(b, 0)] + c \<Longrightarrow> a = b"
  apply (induct c)
  apply (metis (mono_tags, lifting) Terminated_lists.last.simps(1) concat_stlist.simps(1) fstI fst_add plus_stlist_def right_cancel_monoid_class.add_right_imp_eq)
  by (metis (no_types, lifting) fst_add fst_conv right_cancel_monoid_class.add_right_imp_eq stlist_nil_concat_cons ttrace_right_cancel_monoid2)

lemma ttrace_right_cancel_monoid:
  fixes b c :: "'\<alpha> ttrace"
  assumes "snd(last a) = 0"
  and "snd(last b) = 0"
  and "snd(last c) = 0"
  shows "b+a = c+a \<Longrightarrow> b = c"
  using assms
  apply (induct a arbitrary:b c rule:stlist.induct, auto)
  apply (meson snd_conv ttrace_right_cancel_monoid0)
  by (metis (mono_tags, lifting) snd_last_concat_pair ttrace_plus_follow_concat ttrace_right_cancel_monoid1)
 
(*  (* alternative step-by-step proof below *)
proof (induct a arbitrary: b c rule:stlist.induct)
  case (Nil x)
  then show ?case by (simp add: ttrace_right_cancel_monoid0)
next
  case a:(Cons x1a x2)
      
  then show ?case
    proof -
      from a
      have c:"b + [x1a;0] + x2 = c + [x1a;0] + x2"
        by (metis ttrace_plus_follow_concat)
      
      then have "(b + [x1a;0]) + x2 = (c + [x1a;0]) + x2"
        by auto
      
      have c:"snd(last(b + [x1a;0])) = 0"
        by (metis snd_last_concat_pair)
          
      have d:"snd(last(c + [x1a;0])) = 0"
        by (metis snd_last_concat_pair)
          
      from a and c and d 
      have "b + [x1a;0] = c + [x1a;0]"
        by (metis Terminated_lists.last.simps(2) \<open>b + [x1a; 0] + x2 = c + [x1a; 0] + x2\<close>)
      then have "b = c"
        using ttrace_right_cancel_monoid1
        using a.prems(3) a.prems(4) snd_zero by blast
  
    qed*)
    
text {* We then instantiate cttrace as a cancelative monoid, which relies
        on the lemmas we have just proved. *}
    
instantiation cttrace :: (type) cancel_monoid
begin
instance 
  apply intro_classes
  apply (metis (mono_tags, lifting) ct2ttrace ct2ttrace_inject mem_Collect_eq plus_cttrace.rep_eq ttrace_left_cancel_monoid)
  apply (metis (mono_tags, lifting) ct2ttrace ct2ttrace_inject mem_Collect_eq plus_cttrace.rep_eq ttrace_zero_monoid_sum zero_cttrace.rep_eq)
  using ttrace_right_cancel_monoid
  by (metis (mono_tags, lifting) ct2ttrace ct2ttrace_inject mem_Collect_eq plus_cttrace.rep_eq) (* can't complete because have not proved right cancellative monoid for type *)
end

text {* Finally to show that we have a trace algebra we define less_eq, less
        and minus directly in terms of the monoid definitions. The proof is
        now trivial. *}  
  
no_adhoc_overloading uconj conj
no_adhoc_overloading udisj disj  
no_adhoc_overloading unot Not
  
instantiation cttrace :: (type) pre_trace
begin
  
  definition less_eq_cttrace :: "'a cttrace \<Rightarrow> 'a cttrace \<Rightarrow> bool" where "less_eq_cttrace == monoid_le"
  definition less_cttrace :: "'a cttrace \<Rightarrow> 'a cttrace \<Rightarrow> bool" where "less_cttrace x y == (x \<le> y \<and> \<not> (y \<le> x))"
  definition minus_cttrace :: "'a cttrace \<Rightarrow> 'a cttrace \<Rightarrow> 'a cttrace" where "minus_cttrace == monoid_subtract"
  
instance
  apply intro_classes
  apply (simp add: less_eq_cttrace_def)
  apply (simp add: less_cttrace_def)
  by (simp add: minus_cttrace_def)
end
  
lemma stlist_le_sum_cases_nil:
  fixes a :: "'a::trace"
  shows "[;a] \<le> [;x + c] \<Longrightarrow> [;a] \<le> [;x] \<or> [;x] \<le> [;a]"
  by (simp add: le_sum_cases stlist_le_nil_iff_le_elements)
    
lemma cttrace_nil_le_cons_imp_le:
  fixes a c :: "'a::pre_trace"
  shows "[;(a, 0)] \<le> [;(c, 0)] \<Longrightarrow> a \<le> c"
  apply (simp add: less_eq_stlist_def monoid_le_def)
  apply auto
  apply (case_tac ca)
  apply auto
  apply (simp add: plus_stlist_def)
  by (simp add:stlist_nil_concat_cons)
    
lemma cttrace_eq_nils_plus_ex:
  shows "([;(a, 0)] = [;(b, 0)] + c) \<Longrightarrow> \<exists>z y. c = [;(z,y)]"
  apply (induct c)
  apply auto
  by (simp add:plus_stlist_def)
    
(* I was here *)
    
lemma refusal_sum_exists:
  "(\<exists>ca. [;(c, 0::'a::monoid_add)] = [;(a, 0)] + ca) 
    \<longleftrightarrow>
   (\<exists>x. [;(c, 0::'a::monoid_add)] = [;(a, 0)] + [;(x,0)])"
  apply auto
  apply (case_tac ca)
  apply auto
  apply (simp add:plus_stlist_def plus_refusal_def, auto)
  by (simp add:plus_stlist_def plus_refusal_def)
    
lemma cttrace_prefix_iff:
  fixes a c :: "'a::pre_trace"
  shows "[;(a, 0)] \<le> [;(c, 0)] \<longleftrightarrow> a \<le> c"
  apply auto
  using cttrace_nil_le_cons_imp_le apply blast
  apply (simp add:less_eq_stlist_def le_is_monoid_le monoid_le_def)
  apply (simp add:refusal_sum_exists)
  by (simp add:plus_stlist_def)
    
lemma stlist_nil_prefix_nil_cons:
  shows "[;a] \<le> (a #\<^sub>t xs)"
  by (metis add.right_neutral less_eq_stlist_def monoid_le_def stlist_nil_concat_cons)
    
lemma stlist_less_eq_imp_less_eq_cons:
  fixes a :: "'a::pre_trace"
  shows "a \<le> x \<Longrightarrow> [;a] \<le> (x #\<^sub>t xs)"
  by (meson dual_order.trans stlist_le_nil_iff_le_elements stlist_nil_prefix_nil_cons)

lemma stlist_nil_less_eq_imp_less_eq_cons:
  shows "[;a] \<le> [;x] \<Longrightarrow> [;a] \<le> (x #\<^sub>t xs)"
proof -
  assume "[;a] \<le> [;x]"
  then have "\<exists>ps. x #\<^sub>t xs = [;a] + ps"
    by (metis (no_types) add.assoc less_eq_stlist_def monoid_le_def stlist_nil_prefix_nil_cons)
  then show ?thesis
    by (simp add: less_eq_stlist_def monoid_le_def)
qed
  
lemma stlist_nil_less_eq_imp_less_eq_nil:
  shows "[;a] \<le> (x #\<^sub>t xs) \<Longrightarrow> [;a] \<le> [;x]"
  apply (simp add:less_eq_stlist_def le_is_monoid_le monoid_le_def)
  apply auto
  apply (case_tac c)
  apply (simp add: plus_stlist_def)
  by (metis concat_stlist.simps(1) plus_stlist_def stlist.inject(2) stlist_nil_concat_cons)

lemma stlist_nil_less_eq_iff:
  shows "[;a] \<le> (x #\<^sub>t xs) \<longleftrightarrow> [;a] \<le> [;x]"
  apply (auto)
  apply (simp add:stlist_nil_less_eq_imp_less_eq_nil)
  by (simp add:stlist_nil_less_eq_imp_less_eq_cons)

lemma ctrace_split_zero_plus:
  fixes a :: "'a::monoid_add" and c :: "'b::monoid_add"
  shows "[;(a, 0)] + [;(0,c)] = [;(a, c)]"
  by (simp add:plus_stlist_def)

lemma ctrace_refusal_zero_le:
  fixes a :: "'a::monoid_add" and b :: "'b::monoid_add"
  shows "[;(a, 0)] \<le> [;(a, c)]"
  apply (simp add:less_eq_stlist_def monoid_le_def)
  by (metis ctrace_split_zero_plus)
    
lemma ctrace_refusal_zero_le2:
  fixes a :: "'a::monoid_add" and c :: "'b::monoid_sum_0"
  shows "[;(a, c)] \<le> [;(b, 0)] \<Longrightarrow> c = 0"
  apply (simp add:less_eq_stlist_def monoid_le_def)
  apply auto
  apply (case_tac ca)
  apply auto
  apply (simp add:plus_stlist_def)
  apply (simp add:zero_sum)
  by (simp add:plus_stlist_def)
    
lemma stlist_pair_ptrace_le_imp_le:
  fixes a :: "'a::pre_trace" and c :: "'b::monoid_add"
  shows "[;(a, 0)] \<le> [;(b, c)] \<Longrightarrow> [;a] \<le> [;b]"
  apply (simp add:less_eq_stlist_def monoid_le_def)
  apply auto
  apply (case_tac ca)
  apply auto
  apply (metis concat_stlist.simps(1) fst_add fst_conv plus_stlist_def stlist.inject(1))
  by (simp add: stlist_nil_concat_cons)
    
lemma stlist_nil_trans:
  "[;a] \<le> [;b] \<Longrightarrow> [;b] \<le> [;c] \<Longrightarrow> [;a] \<le> [;c]"
  by (metis (no_types, lifting) add.assoc less_eq_stlist_def monoid_le_def)

lemma stlist_pair_ptrace_le_imp_le_arbitrary:
  fixes a b :: "'a::pre_trace" and c :: "'b::monoid_add"
  shows "[;a] \<le> [;b] \<Longrightarrow> [;(a, 0)] \<le> [;(b, c)]"
  by (meson ctrace_refusal_zero_le cttrace_prefix_iff stlist_le_nil_imp_le_elements stlist_nil_trans)
    
lemma stlist_pair_ptrace_le_iff_le_arbitrary:
  fixes a :: "'a::pre_trace" and c :: "'b::monoid_add"
  shows "[;(a, 0)] \<le> [;(b, c)] \<longleftrightarrow> [;a] \<le> [;b]"
  by (metis stlist_pair_ptrace_le_imp_le stlist_pair_ptrace_le_imp_le_arbitrary)
 
lemma ctrace_refusal_zero_le2_rev:
  fixes a :: "'a::monoid_add" and c :: "'b::monoid_sum_0"
  shows "c \<noteq> 0 \<Longrightarrow> \<not> [;(a, c)] \<le> [;(b, 0)]"
  by (metis ctrace_refusal_zero_le2)

declare [[show_sorts]]    
lemma list_refusal_imp_le_sum_cases:
  fixes a b c :: "('a list \<times> 'a refusal)"
  assumes "snd(c) = 0" and "snd(a) = 0"
  and "[;a] \<le> [;b + c]"
  shows "[;a] \<le> [;b] \<or> [;b] \<le> [;a]"
proof -
  fix xa and xc
  assume xa:"a = (xa,0)" and xc:"c = (xc,0)"
  from assms have step0:"[;(xa,0)] \<le> [;b + (xc,0)]"
    using xa and xc by (simp)
      
  fix xb and rb
  assume xb:"b = (xb,rb)"
  from assms and step0 have "[;(xa,0)] \<le> [;(xb,rb) + (xc,0)]"
    using xb by simp
   (* by (simp add: stlist_pair_ptrace_le_iff_le_arbitrary)*)
      
  also have "[;(xa,0)] \<le> [;(xb,rb) + (xc,0)] = ([;(xa,0)] \<le> [;(xb+xc,rb)])"
    by simp
  also have "... = ([;xa] \<le> [;xb+xc])"
    by (simp add:stlist_pair_ptrace_le_iff_le_arbitrary)
  also have f:"... = (xa \<le> xb + xc)"
    by (simp add:stlist_le_nil_iff_le_elements)
      
  from f have "(xa \<le> xb + xc) \<Longrightarrow> xa \<le> xb \<or> xb \<le> xa"
    by (simp add:le_sum_cases)
  also have "xa \<le> xb \<or> xb \<le> xa \<Longrightarrow> [;(xa,0)] \<le> [;(xb,rb)] \<or> [;(xb,rb)] \<le> [;(xa,0)]"
    sledgehammer
      
  (* This is not looking true. Need to show that the order \<le> can be built from LHS \<rightarrow> RHS *)     
      
  (*
  using assms
  apply (case_tac c)
  apply auto
  apply (case_tac a)
  apply auto
  apply (case_tac b)
  apply auto
  apply (simp add:stlist_pair_ptrace_le_iff_le_arbitrary)
  apply (case_tac "ba=0")
  using stlist_le_sum_cases_nil stlist_pair_ptrace_le_imp_le_arbitrary apply blast
  apply (simp add:ctrace_refusal_zero_le2_rev)
  apply (simp add:stlist_le_nil_iff_le_elements)
  apply (thin_tac "c = (aa, 0::'a refusal)")
  apply (thin_tac "a = (aaa, 0::'a refusal)")
  apply (thin_tac "b = (ab, ba)")
  apply (thin_tac "b \<noteq> (0::'a refusal)")
  using le_sum_cases sledgehammer*)
  oops
    
instantiation cttrace :: (type) trace
begin
  
lemma
  fixes a :: "('a list \<times> 'a refusal)"
  shows "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a"
  apply (simp add:plus_refusal_def)
  oops

    
lemma ttrace_zero_le_sum_cases:
  fixes a\<^sub>t :: "'a list"
  shows "(a\<^sub>t,0::'a refusal) \<le> (b\<^sub>t,0::'a refusal) + (c\<^sub>t,0::'a refusal) \<Longrightarrow> (a\<^sub>t,0::'a refusal) \<le> (b\<^sub>t,0::'a refusal) \<or> (b\<^sub>t,0::'a refusal) \<le> (a\<^sub>t,0::'a refusal)"
  apply simp_all
  apply (simp add:refusal_zero_least)
  by (simp add: le_sum_cases)
    

  
lemma
  fixes b :: "'a ttrace"
  assumes "snd(last b) = 0"
  shows "[;(a, 0::'a refusal)] \<le> b + [;(c, 0::'a refusal)] \<Longrightarrow> [;(a, 0)] \<le> b \<or> b \<le> [;(a, 0)]"
  using assms
  apply (induct b rule:stlist.induct)
  apply (simp add:plus_stlist_def)
  apply (case_tac x)
  apply (simp_all add:cttrace_prefix_iff)
  using le_sum_cases apply blast
  
  apply (simp_all add:plus_stlist_def)
 
  apply (simp_all add:cttrace_prefix_iff, auto)
   
lemma
  fixes b c :: "'a ttrace"
  assumes "snd(last b) = 0"
  and "snd(last c) = 0"
  shows "[;(a, 0::'a refusal)] \<le> b + c \<Longrightarrow> [;(a, 0::'a refusal)] \<le> b \<or> b \<le> [;(a, 0)]"
  using assms
  apply (induct c arbitrary: b rule:stlist.induct, auto)
  
  apply (simp add:le_sum_cases)
  oops
     
lemma
  fixes c :: "'a ttrace"
  assumes "snd(last c) = 0"
  and "snd(a) = 0" and "snd(b) = 0"
  shows "[;a] \<le> [;b] + c \<Longrightarrow> [;a] \<le> [;b] \<or> [;b] \<le> [;a]"
  using assms
  apply (induct c)
  apply (simp add:plus_stlist_def)
  apply (metis add.right_neutral cttrace_prefix_iff le_add le_common_total plus_prod_def prod.collapse)
  apply (simp add:plus_stlist_def)
  apply (simp add:stlist_nil_less_eq_iff)
  apply (simp add:list_refusal_imp_le_sum_cases)
  oops
    
(* Proving the property below is proving more challenging than anticipated *)
lemma 
  fixes a :: "'a ttrace"
  assumes "snd(last a) = 0"
  and "snd(last b) = 0"
  and "snd(last c) = 0"
  shows "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a"  
  using assms
(*  apply (induct a b arbitrary:c rule:stlist_induct_cons)
 *)
  apply (induct a arbitrary:b c rule:stlist.induct)
  sledgehammer
    
  
   apply (simp add:)
   apply auto
   apply (case_tac ba)
   apply auto
   apply (metis ttrace_zero_le_sum_cases)
  
  apply (induct a b rule:stlist_induct_cons)
      apply (case_tac c)
  oops
    
instance apply intro_classes
      
end    
        
adhoc_overloading uconj conj
adhoc_overloading unot Not

end