section {* Refinement calculus *}

theory utp_refcalc
  imports utp_designs
begin
  
definition spec :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha> upred) \<Rightarrow> '\<alpha> hrel_des" where
[upred_defs]: "spec x p q = (\<Squnion> v \<bullet> (\<lceil>p \<and> &\<^bold>v =\<^sub>u \<guillemotleft>v\<guillemotright>\<rceil>\<^sub>< \<turnstile>\<^sub>r x:[\<lceil>q(v)\<rceil>\<^sub>>]))"

syntax
  "_init_var"  :: "logic"
  "_spec"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_:[_,/ _]" [99,0,0] 100)
  "_log_const" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("con _ \<bullet> _" [0, 10] 10)
  
translations
  "_spec x p q" => "CONST spec x p (\<lambda> _init_var. q)"
  "_spec (_salphaset (_salphamk x)) p q" <= "CONST spec x p (\<lambda> iv. q)"
  "_log_const x P" => "\<Squnion> x \<bullet> P"

parse_translation {*
let
  fun init_var_tr [] = Syntax.free "iv"
    | init_var_tr _  = raise Match;
in
[(@{syntax_const "_init_var"}, K init_var_tr)]
end
*}
  
abbreviation abort :: "'\<alpha> hrel_des" where
"abort \<equiv> true"

abbreviation magic :: "'\<alpha> hrel_des" where
"magic \<equiv> \<top>\<^sub>D"

abbreviation skip :: "'\<alpha> hrel_des" where
"skip \<equiv> \<emptyset>:[true,true]"
  
abbreviation "chose x \<equiv> {&x}:[true,true]"

  
lemma spec_simple_def: 
  "x:[pre,post] = (\<lceil>pre\<rceil>\<^sub>< \<turnstile>\<^sub>r x:[\<lceil>post\<rceil>\<^sub>>])"
  by (rel_auto)
  
lemma spec_abort:
  "x:[false,post] = true"
  by (rel_auto)
 
lemma spec_skip:
  "\<emptyset>:[true,true] = skip"
  by simp
    
lemma skip_des_skip: "skip = II\<^sub>D"
  by (rel_auto)

  
abbreviation spec_stat :: "('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> hrel_des" where
"spec_stat w pre post \<equiv> (pre \<turnstile>\<^sub>n w:[\<lceil>post\<rceil>\<^sub>>])"

syntax
  "_spec_stat" :: "salpha \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> hrel_des" ("_:[_,_]\<^sub>u" [90,0,0] 90)

translations
  "_spec_stat w pre post" \<rightleftharpoons> "CONST spec_stat w pre post"

lemma rc_strengthen_post:
  assumes "`post' \<Rightarrow> post`"
  shows "w:[pre, post]\<^sub>u \<sqsubseteq> w:[pre, post']\<^sub>u"
  using assms by (rel_auto)

lemma rc_weaken_pre:
  assumes "`pre \<Rightarrow> pre'`"
  shows "w:[pre, post]\<^sub>u \<sqsubseteq> w:[pre', post]\<^sub>u"
  using assms by (rel_auto)

lemma rc_skip:
  assumes "vwb_lens w" "`pre \<Rightarrow> post`"
  shows "w:[pre, post]\<^sub>u \<sqsubseteq> II\<^sub>D"
  using assms by (rel_auto)

lemma rc_seq:
  assumes "vwb_lens w"
  shows "w:[pre, post]\<^sub>u \<sqsubseteq> w:[pre, mid]\<^sub>u ;; w:[mid, post]\<^sub>u"
  using assms oops
  (* FIXME: Need to correct this law *)

end