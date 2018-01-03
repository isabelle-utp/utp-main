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
  "_init_var"  :: "logic"
  "_spec"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_,/ _]" [99,0,0] 100)
  "_log_const" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("con _ :: _ \<bullet> _" [0, 10] 10)
  "_init_val"  :: "svid \<Rightarrow> logic" ("&\<^sub>0_" [998] 998)
  
translations
  "_spec x p q" => "CONST spec x p (\<lambda> _init_var. q)"
  "_spec (_salphaset (_salphamk x)) p q" <= "CONST spec x p (\<lambda> iv. q)"
  "con x :: 'a \<bullet> P" == "CONST log_const TYPE('a) (\<lambda> x. P)"
  "_init_val x" => "CONST uop (CONST lens_get x) (CONST lit _init_var)"
  
parse_translation {*
let
  fun init_var_tr [] = Syntax.free "iv"
    | init_var_tr _  = raise Match;
in
[(@{syntax_const "_init_var"}, K init_var_tr)]
end
*}
   
abbreviation "chose x \<equiv> {&x}:[true,true]"
  
abbreviation passume :: "'\<alpha> upred \<Rightarrow> '\<alpha> prog" ("{_}\<^sub>p") where
"{b}\<^sub>p \<equiv> \<emptyset>:[b, true]"

subsection {* Refinement Laws *}
  
lemma spec_abort:
  "x:[false,post] = abort"
  by pauto
 
lemma spec_skip:
  "\<emptyset>:[true,true] = skip"
  by (pauto)
    
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
  shows "w:[pre, post] \<sqsubseteq> w:[pre, mid] ; w:[mid, post]"
  using assms by prefine
   
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
  apply (rule_tac x="put\<^bsub>x\<^esub> c (get\<^bsub>x\<^esub> b)" in exI)
  apply (simp)
done
    
end