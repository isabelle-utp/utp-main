section {* Lifting expressions *}

theory utp_lift
  imports 
    utp_alphabet
begin

subsection {* Lifting definitions *}

text {* We define operators for converting an expression to and from a relational state space *}

abbreviation lift_pre :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uexpr" ("\<lceil>_\<rceil>\<^sub><")
where "\<lceil>P\<rceil>\<^sub>< \<equiv> P \<oplus>\<^sub>p fst\<^sub>L"

abbreviation drop_pre :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<lfloor>_\<rfloor>\<^sub><")
where "\<lfloor>P\<rfloor>\<^sub>< \<equiv> P \<restriction>\<^sub>p fst\<^sub>L"

abbreviation lift_post :: "('a, '\<beta>) uexpr \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uexpr" ("\<lceil>_\<rceil>\<^sub>>")
where "\<lceil>P\<rceil>\<^sub>> \<equiv> P \<oplus>\<^sub>p snd\<^sub>L"

abbreviation drop_post :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta>) uexpr" ("\<lfloor>_\<rfloor>\<^sub>>")
where "\<lfloor>P\<rfloor>\<^sub>> \<equiv> P \<restriction>\<^sub>p snd\<^sub>L"

abbreviation lift_cond_pre ("\<lceil>_\<rceil>\<^sub>\<leftarrow>") where "\<lceil>P\<rceil>\<^sub>\<leftarrow> \<equiv> P \<oplus>\<^sub>p (1\<^sub>L \<times>\<^sub>L 0\<^sub>L)"
abbreviation lift_cond_post ("\<lceil>_\<rceil>\<^sub>\<rightarrow>") where "\<lceil>P\<rceil>\<^sub>\<rightarrow> \<equiv> P \<oplus>\<^sub>p (0\<^sub>L \<times>\<^sub>L 1\<^sub>L)"

abbreviation drop_cond_pre ("\<lfloor>_\<rfloor>\<^sub>\<leftarrow>") where "\<lfloor>P\<rfloor>\<^sub>\<leftarrow> \<equiv> P \<restriction>\<^sub>p (1\<^sub>L \<times>\<^sub>L 0\<^sub>L)"
abbreviation drop_cond_post ("\<lfloor>_\<rfloor>\<^sub>\<rightarrow>") where "\<lfloor>P\<rfloor>\<^sub>\<rightarrow> \<equiv> P \<restriction>\<^sub>p (0\<^sub>L \<times>\<^sub>L 1\<^sub>L)"

subsection {* Lifting laws *}

lemma lift_pre_var [simp]:
  "\<lceil>var x\<rceil>\<^sub>< = $x"
  by (alpha_tac)

lemma lift_post_var [simp]:
  "\<lceil>var x\<rceil>\<^sub>> = $x\<acute>"
  by (alpha_tac)

lemma lift_cond_pre_var [simp]:
  "\<lceil>$x\<rceil>\<^sub>\<leftarrow> = $x"
  by (pred_auto)

lemma lift_cond_post_var [simp]:
  "\<lceil>$x\<acute>\<rceil>\<^sub>\<rightarrow> = $x\<acute>"
  by (pred_auto)

subsection {* Unrestriction laws *}

lemma unrest_dash_var_pre [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "$x\<acute> \<sharp> \<lceil>p\<rceil>\<^sub><"
  by (pred_auto)

lemma unrest_dash_var_cond_pre [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "$x\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>\<leftarrow>"
  by (pred_auto)

end
