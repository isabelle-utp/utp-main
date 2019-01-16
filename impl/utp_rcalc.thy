subsection {* Refinement Calculus *}

theory utp_rcalc
  imports utp_prog
begin

subsection {* Operators *}
  
lift_definition spec :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha> upred) \<Rightarrow> '\<alpha> prog"
is "\<lambda> x p q. (\<Squnion> v \<bullet> ((p \<and> &\<^bold>v =\<^sub>u \<guillemotleft>v\<guillemotright>) \<turnstile>\<^sub>n x:[\<lceil>q(v)\<rceil>\<^sub>>]))"
  by (simp add: closure)
  
lift_definition log_const :: "'a itself \<Rightarrow> ('a \<Rightarrow> '\<alpha> prog) \<Rightarrow> '\<alpha> prog" 
is "\<lambda> t P. \<Squnion> i \<bullet> P i" by (simp add: closure)
  
declare spec.rep_eq [prog_rep_eq]
declare log_const.rep_eq [prog_rep_eq]
  
subsection {* Syntax Translations *}
  
syntax
  "_spec"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_,/ _]" [99,0,0] 100)
  "_log_const" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("con _ :: _ \<bullet> _" [0, 10] 10)
  "_init_val"  :: "svid \<Rightarrow> logic" ("&\<^sub>0_" [998] 998)
  "_init_expr" :: "logic \<Rightarrow> logic" ("[_]\<^sub>0")
  
translations
  "_spec x p q" => "CONST spec x p (\<lambda> _init_var. q)"
  "_spec (_salphaset (_salphamk x)) p q" <= "CONST spec x p (\<lambda> iv. q)"
  "con x :: 'a \<bullet> P" == "CONST log_const TYPE('a) (\<lambda> x. P)"
  "_init_val x" => "CONST uop (CONST lens_get x) (CONST lit _init_var)"
  "_init_expr e" => "e\<lbrakk>\<guillemotleft>_init_var\<guillemotright>/&\<^bold>v\<rbrakk>"
  
abbreviation "chose x \<equiv> {&x}:[true,true]"
  
abbreviation passume :: "'\<alpha> upred \<Rightarrow> '\<alpha> prog" ("{_}\<^sub>p") where
"{b}\<^sub>p \<equiv> \<emptyset>:[b, true]"

abbreviation passert :: "'\<alpha> upred \<Rightarrow> '\<alpha> prog" ("[_]\<^sub>p") where
"[b]\<^sub>p \<equiv> \<emptyset>:[true, b]"

subsection {* Refinement Laws *}
  
lemma spec_abort:
  "x:[false,post] = abort"
  by pauto
 
lemma spec_skip:
  "\<emptyset>:[true,true] = skip"
  by (pauto)
 
lemma rc_spec_expand:
  "vwb_lens w \<Longrightarrow> w:[pre, post(iv :: '\<alpha>)] = (con s :: '\<alpha> \<bullet> w:[pre \<and> &\<^bold>v =\<^sub>u \<guillemotleft>s\<guillemotright>, post(s)])"
  by (peq)
    
lemma rc_strengthen_post:
  assumes "`post' \<Rightarrow> post`"
  shows "w:[pre, post] \<sqsubseteq> w:[pre, post']"
  using assms by (pauto)

lemma rc_weaken_pre:
  assumes "`pre \<Rightarrow> pre'`"
  shows "w:[pre, post] \<sqsubseteq> w:[pre', post]"
  using assms by prefine

lemma rc_skip:
  assumes "vwb_lens w" "`pre \<Rightarrow> post`"
  shows "w:[pre, post] \<sqsubseteq> skip"
  using assms by prefine

lemma rc_assign:
  assumes "vwb_lens x" "vwb_lens w" "x \<bowtie> w" "`pre \<Rightarrow> post\<lbrakk>e/w\<rbrakk>`"
  shows "{&w,&x}:[pre,post] \<sqsubseteq> w := e"
  using assms by prefine
      
lemma rc_seq:
  assumes "vwb_lens w" "w \<natural> mid"
  shows "w:[pre, post] \<sqsubseteq> w:[pre, mid] ;; w:[mid, post]"
  using assms by (prefine, metis mwb_lens.put_put vwb_lens_mwb)
   
lemma rc_intro_log_const:
  assumes "`pre \<Rightarrow> (\<^bold>\<exists> c :: 'a \<bullet> pre'(c))`"
  shows "w:[pre, post] \<sqsubseteq> (con c :: 'a \<bullet> w:[pre'(c), post])"
  using assms by (prefine)

lemma rc_fix_init_val:
  "w:[pre, post] \<sqsubseteq> (con c :: 'a \<bullet> w:[pre \<and> \<guillemotleft>c\<guillemotright> =\<^sub>u E, post])"
  by (prefine)
    
lemma rc_remove_log_const:
  "(con c :: 'a \<bullet> P) \<sqsubseteq> P"
  by (prefine')
  
lemma rc_expand_frame:
  assumes "vwb_lens x" "w \<bowtie> x" "\<And> iv. x \<sharp> post(iv)"
  shows "{&w}:[pre, post(iv)] = {&w,&x}:[pre, post(iv) \<and> &x =\<^sub>u &\<^sub>0x]"
  using assms
  apply (peq)
  apply (rename_tac b c)
  apply (metis lens_indep_def)
  apply (simp add: lens_indep.lens_put_comm)
done
  
lemma rc_iterate:
  fixes V :: "(nat, 'a) uexpr"
  assumes "vwb_lens w"
  shows "w:[ivr, ivr \<and> \<not> (\<Or> i\<in>A \<bullet> g(i))] 
        \<sqsubseteq> (do i\<in>A \<bullet> g(i) \<rightarrow> w:[ivr \<and> g(i), ivr \<and> (V <\<^sub>u [V]\<^sub>0)] od)" (is "?lhs \<sqsubseteq> ?rhs")
proof -
  have "(\<Squnion> v \<bullet> (ivr \<and> &\<^bold>v =\<^sub>u \<guillemotleft>v\<guillemotright>) \<turnstile>\<^sub>n w:[\<lceil>ivr \<and> \<not> (\<Sqinter> i \<in> A \<bullet> g i)\<rceil>\<^sub>>]) =
        (ivr \<turnstile>\<^sub>n w:[\<lceil>ivr \<and> \<not> (\<Sqinter> i \<in> A \<bullet> g i)\<rceil>\<^sub>>])"
    by (rel_auto)
  also have "... \<sqsubseteq> do i\<in>A \<bullet> g(i) \<rightarrow> \<Squnion> v \<bullet> ((ivr \<and> g i) \<and> &\<^bold>v =\<^sub>u \<guillemotleft>v\<guillemotright>) \<turnstile>\<^sub>n w:[\<lceil>ivr \<and> V <\<^sub>u V\<lbrakk>\<guillemotleft>v\<guillemotright>/&\<^bold>v\<rbrakk>\<rceil>\<^sub>>] od"
    apply (rule order_trans)
    defer
    apply (rule IterateD_refine_intro[of _ _ _ _ V], simp add: assms)
    apply (rule IterateD_mono_refine)
    apply (simp_all add: ndes_simp closure)
    apply (rule ndesign_refine_intro)
    apply (rel_auto)+
  done
  finally show ?thesis
    by (ptransfer, simp add: usubst)
qed

lemma rc_iterate_single:
  fixes V :: "(nat, 'a) uexpr"
  assumes "vwb_lens w"
  shows "w:[ivr, ivr \<and> \<not> g] \<sqsubseteq> (do g \<rightarrow> w:[ivr \<and> g, ivr \<and> (V <\<^sub>u [V]\<^sub>0)] od)"
oops

end