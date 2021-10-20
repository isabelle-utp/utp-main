section \<open>Refinement Calculus\<close>

theory utp_des_refcalc
  imports utp_des_prog
begin
  
definition des_spec :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha> upred) \<Rightarrow> '\<alpha> hrel_des" where
[upred_defs, ndes_simp]: "des_spec x p q = (\<Squnion> v \<bullet> ((p \<and> &\<^bold>v =\<^sub>u \<guillemotleft>v\<guillemotright>) \<turnstile>\<^sub>n x:[\<lceil>q(v)\<rceil>\<^sub>>]))"

syntax
  "_init_var"      :: "logic"
  "_des_spec"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_,/ _]\<^sub>D" [99,0,0] 100)
  "_des_log_const" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("con\<^sub>D _ \<bullet> _" [0, 10] 10)
  
translations
  "_des_spec x p q" => "CONST des_spec x p (\<lambda> _init_var. q)"
  "_des_spec (_salphaset (_salphamk x)) p q" <= "CONST des_spec x p (\<lambda> iv. q)"
  "_des_log_const x P" => "\<Squnion> x \<bullet> P"

parse_translation \<open>
let
  fun init_var_tr [] = Syntax.free "iv"
    | init_var_tr _  = raise Match;
in
[(@{syntax_const "_init_var"}, K init_var_tr)]
end
\<close>
  
abbreviation "choose\<^sub>D x \<equiv> {&x}:[true,true]\<^sub>D"
  
lemma des_spec_simple_def: 
  "x:[pre,post]\<^sub>D = (pre \<turnstile>\<^sub>n x:[\<lceil>post\<rceil>\<^sub>>])"
  by (rel_auto)
  
lemma des_spec_abort:
  "x:[false,post]\<^sub>D = \<bottom>\<^sub>D"
  by (rel_auto)
 
lemma des_spec_skip: "\<emptyset>:[true,true]\<^sub>D = II\<^sub>D"
  by (rel_auto)
      
lemma des_spec_strengthen_post:
  assumes "`post' \<Rightarrow> post`"
  shows "w:[pre, post]\<^sub>D \<sqsubseteq> w:[pre, post']\<^sub>D"
  using assms by (rel_auto)

lemma des_spec_weaken_pre:
  assumes "`pre \<Rightarrow> pre'`"
  shows "w:[pre, post]\<^sub>D \<sqsubseteq> w:[pre', post]\<^sub>D"
  using assms by (rel_auto)

lemma des_spec_refine_skip:
  assumes "vwb_lens w" "`pre \<Rightarrow> post`"
  shows "w:[pre, post]\<^sub>D \<sqsubseteq> II\<^sub>D"
  using assms by (rel_auto)
    
lemma rc_iter:
  fixes V :: "(nat, 'a) uexpr"
  assumes "vwb_lens w"
  shows "w:[ivr, ivr \<and> \<not> (\<Or> i\<in>A \<bullet> g(i))]\<^sub>D
        \<sqsubseteq> (do i\<in>A \<bullet> g(i) \<rightarrow> \<Squnion> iv \<bullet> w:[ivr \<and> g(i) \<and> \<guillemotleft>iv\<guillemotright> =\<^sub>u &\<^bold>v, ivr \<and> (V <\<^sub>u V\<lbrakk>\<guillemotleft>iv\<guillemotright>/\<^bold>v\<rbrakk>)]\<^sub>D od)" (is "?lhs \<sqsubseteq> ?rhs")
  apply (rule order_trans)
   defer
   apply (simp add: des_spec_simple_def)
   apply (rule IterateD_refine_intro[of _ _ _ _ V])
   apply (simp add: assms)
  apply (rule IterateD_mono_refine)
    apply (simp_all add: ndes_simp closure)
   apply (rel_auto)
  done
  
end