section {* Circus Time model *}

theory utp_circus_time
  imports 
    utp_cml
    "../utils/Library_extra/Terminated_lists"
    "~~/src/HOL/Library/Prefix_Order"
begin

no_adhoc_overloading uconj conj
no_adhoc_overloading udisj disj
no_adhoc_overloading unot Not
  
text {* TODO: Move these into the theory of Terminated_lists. *}
    
lemma stlist_last_concat:
  fixes s z :: "'a::plus stlist"
  shows "last (s + (x#\<^sub>tz)) = last z"
  unfolding plus_stlist_def
  apply (induct s)
  by auto
    
lemma stlist_last_concat2:
  fixes s :: "'a::plus stlist"
  shows "last (x#\<^sub>t(s + [;z])) = last s + z"
  unfolding plus_stlist_def
  apply (induct s)
  by auto
    
lemma stlist_last_concat3:
  fixes s :: "'a::plus stlist"
  shows "last ((x#\<^sub>ts) + [;z]) = last s + z"
  unfolding plus_stlist_def
  apply (induct s)
  by auto
   
lemma monoid_le_stlist2:
  "(xs :: 'a::monoid_add stlist) \<le>\<^sub>m ys \<longleftrightarrow> xs \<le> ys"
  by (simp add: less_eq_stlist_def)
    
lemma stlist_eq_nil:
  fixes a b :: "'a::ordered_cancel_monoid_diff"
  shows "a = b \<longleftrightarrow> [;a] = [;b]"
  by simp
    
lemma stlist_le_nil:
  fixes a b :: "'a::ordered_cancel_monoid_diff"
  shows "\<not> a < a"
  by simp   
  
lemma monoid_plus_prefix_iff_zero:
  fixes a b :: "'a::ordered_cancel_monoid_diff"
  shows "a + x \<le> a \<longleftrightarrow> x = 0"
  by (metis add.right_neutral antisym le_add left_cancel_monoid_class.add_left_imp_eq)
    
lemma stlist_le_nil_imp_le_elements:
  fixes a b :: "'a::ordered_cancel_monoid_diff"
  shows "[;a] \<le> [;b] \<Longrightarrow> a \<le> b"
  apply (simp add: less_eq_stlist_def monoid_le_def)
  apply auto
  apply (case_tac c)
  apply auto
  apply (simp add: plus_stlist_def)
  by (simp add: stlist_nil_concat_cons)
    
lemma stlist_le_nil_iff_le_elements:
  fixes a b :: "'a::ordered_cancel_monoid_diff"
  shows "[;a] \<le> [;b] \<longleftrightarrow> a \<le> b"
  by (metis concat_stlist.simps(1) ordered_cancel_monoid_diff_class.le_iff_add plus_stlist_def stlist_le_nil_imp_le_elements)
    
lemma stlist_plus_nils:
  fixes a b :: "'a::ordered_cancel_monoid_diff"
  shows "a + b = c \<longleftrightarrow> [;a] + [;b] = [;c]"
  by (simp add: plus_stlist_def)      
    
lemma stlist_nil_minus:
  fixes a b :: "'a::ordered_cancel_monoid_diff"
  shows "[;a] - [;b] = [;a-b]"
  apply (case_tac "b \<le> a")
  apply auto
  apply (metis add_monoid_diff_cancel_left concat_stlist.simps(1) diff_add_cancel_left' minus_stlist_def plus_stlist_def)
  apply (simp add:stlist_le_nil_iff_le_elements)
  by (simp add:zero_stlist_def)
    
lemma stlist_minus_cons:
  fixes xs ys :: "'a::ordered_cancel_monoid_diff"
  assumes "x \<le> y" "xs \<le> ys"
  shows "(y + ys) - (x + xs) = (y-x) + (ys-xs)"
  using assms
  apply (simp add:le_is_monoid_le)
  apply (simp add:minus_def monoid_subtract_def)
  apply auto
  
  oops
    
lemma listconsconcat:
  fixes xs ys :: "'a::ordered_cancel_monoid_diff list"
  assumes "x \<le> y" "xs \<le> ys"
  shows "(y#ys) - (x#xs) = [y]-[x]+(ys-xs)"
  using assms
  apply (simp add:le_is_monoid_le minus_def monoid_subtract_def)
  apply auto
  oops
        
lemma stlist_nil_le_cons_imp_le:
  fixes xs :: "'a::ordered_cancel_monoid_diff stlist"
  shows "[;a] \<le> (x#\<^sub>txs) \<Longrightarrow> a \<le> x"
  apply (simp add:le_is_monoid_le monoid_le_def)
  apply auto
  apply (case_tac c)
  apply (simp add: plus_stlist_def)
  by (metis stlist.inject(2) stlist_nil_concat_cons)

lemma stlist_cons_minus_nil_eq:
  fixes xs :: "'a::ordered_cancel_monoid_diff stlist"
  assumes "[;a] \<le> (x#\<^sub>txs)"
  shows "(x#\<^sub>txs) - [;a] = (x-a)#\<^sub>txs" 
  using assms
  apply (simp add:minus_stlist_def minus_def le_is_monoid_le)
  by (smt Terminated_lists.last.simps(1) add.assoc add.right_neutral assms concat_stlist.simps(2) diff_add_cancel_left' front.simps(1) left_cancel_monoid_class.add_left_imp_eq minus_def stlist_front_concat_last stlist_nil_concat_cons stlist_nil_le_cons_imp_le stlist_plus_follow_concat zero_stlist_def)
    
subsection {* Types *}

text {* A trace of events is a list. *}  
  
type_synonym '\<alpha> trace = "'\<alpha> list"
  
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
        two sets to sets. *}
  
type_synonym '\<alpha> ttrace = "('\<alpha> trace \<times> '\<alpha> refusal) stlist"  
  
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

lemma trace_refusal_right_cancel:
  fixes b1 :: "'\<alpha> trace" and b2 :: "'\<alpha> refusal"
  assumes "b2 = 0" and "c2 = 0"
  shows "(b1, b2) + a = (c1, c2) + a \<Longrightarrow> b1 = c1 \<and> b2 = c2"
  using assms
  by (metis fst_add fst_conv right_cancel_monoid_class.add_right_imp_eq)
    
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
  
instantiation cttrace :: (type) ordered_cancel_monoid_diff
begin
  
  definition less_eq_cttrace :: "'a cttrace \<Rightarrow> 'a cttrace \<Rightarrow> bool" where "less_eq_cttrace == monoid_le"
  definition less_cttrace :: "'a cttrace \<Rightarrow> 'a cttrace \<Rightarrow> bool" where "less_cttrace x y == x \<le> y \<and> \<not> (y \<le> x)"
  definition minus_cttrace :: "'a cttrace \<Rightarrow> 'a cttrace \<Rightarrow> 'a cttrace" where "minus_cttrace == monoid_subtract"
  
instance
  apply intro_classes
  apply (simp add: less_eq_cttrace_def)
  apply (simp add: less_cttrace_def)
  by (simp add: minus_cttrace_def)

(* REVISED UP TO HERE *)
  
text {* What is the meaning of "empty" refusals in the CML trace?
  That is, a trace like [Event a, Event b] should have an unrestricted
  trace, rather than being empty? *}
  
fun ccut :: "'\<theta> tevent list \<Rightarrow> (('\<theta> trace \<times> '\<theta> refusal) \<times> '\<theta> tevent list)" where
"ccut [] = (([],{}),[])" |
"ccut (Tock T # t) = (([],T), t)" |
"ccut (Event e # t) = ((e # fst (fst (ccut t)), snd (fst (ccut t))),snd (ccut t))"
  
function c2ct :: "'\<theta> tevent list \<Rightarrow> '\<theta> timedtrace" where 
"c2ct T = (fst (ccut T)) # (c2ct (snd (ccut T)))"
by auto

value "ccut []"
value "ccut [Event a, Event b]"
value "ccut [Event a, Event b, Tock {d}, Event e, Event f, Tock {g}]"
(*

fun cml2ct :: "'\<theta> tevent list \<Rightarrow> '\<theta> timedtrace" where
"cml2ct [] = [([],{})]" |
"cml2ct (Tock T # t) = (([],T), t)"

"c2ct (Tock T # t) = [fst (ccut (Tock T # t))] # c2ct t" |
"c2ct (Event e # t) = [fst (ccut (Event e # t))] # "
*)
text {* Could we really reuse the generalised reactive designs
        with the trace model of Circus Time? I don't think so
        for several reasons:
    
        1. Traces are non-empty.
        2. Zero element cannot just be empty trace.
        3. R2 as defined would not apply?  *}

end