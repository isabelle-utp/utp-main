theory Sfun_Extra
imports HOLCF Tr_Logic
begin

default_sort pcpo

declare strictify_cancel [simp]
declare Abs_sfun_strict [simp]
declare Rep_sfun_strict [simp]
declare cont_Rep_sfun [simp,cont2cont]

lemma cont_sfun_abs [simp,cont2cont]: "cont (\<lambda> f. Abs_sfun (strictify\<cdot>f))"
  by (rule cont_Abs_sfun, simp_all)

lemma sfun_abs_strict [simp]: "sfun_abs\<cdot>\<bottom> = \<bottom>"
  by (simp add:sfun_abs_def)

abbreviation sfun_rep' :: "('a::pcpo \<rightarrow>! 'b::pcpo) \<Rightarrow> 'a \<Rightarrow> 'b" where
"sfun_rep' f x \<equiv> sfun_rep\<cdot>f\<cdot>x"

abbreviation sfun_abs' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a::pcpo \<rightarrow>! 'b::pcpo)" where
"sfun_abs' f \<equiv> sfun_abs\<cdot>(Abs_cfun f)"

lemma sfun_abs'_sfun_rep' [simp]: "sfun_abs' (sfun_rep' f) = f"
  by (simp add: eta_cfun)

notation
  sfun_rep'  ("(_$!/_)" [999,1000] 999)

notation (xsymbols)
  sfun_rep'  ("(_\<cdot>!/_)" [999,1000] 999)

notation (HTML output)
  sfun_rep'  ("(_\<cdot>!/_)" [999,1000] 999)

syntax
  "_sfun_abs'" :: "[cargs, logic] \<Rightarrow> logic"  ("(3SLAM _./ _)" [1000, 10] 10)

syntax (xsymbols)
  "_sfun_abs'" :: "[cargs, logic] \<Rightarrow> logic" ("(3\<Lambda>! _./ _)" [1000, 10] 10)

translations
  "SLAM x. t" == "CONST sfun_abs' (\<lambda> x. t)"

lemma sfun_eqI: "(\<And>x. f\<cdot>!x = g\<cdot>!x) \<Longrightarrow> f = g"
  by (simp add: sfun_eq_iff cfun_eq_iff)

subsection {* Identity and composition *}

definition
  SID :: "'a \<rightarrow>! 'a" where
  "SID = sfun_abs\<cdot>ID"

definition
  sfcomp  :: "('b \<rightarrow>! 'c) \<rightarrow> ('a \<rightarrow>! 'b) \<rightarrow> 'a \<rightarrow>! 'c" where
  soo_def: "sfcomp = (\<Lambda> f g. \<Lambda>! x. f\<cdot>!(g\<cdot>!x))"

abbreviation
  dfcomp_syn :: "['b \<rightarrow>! 'c, 'a \<rightarrow>! 'b] \<Rightarrow> 'a \<rightarrow>! 'c"  (infixr "oo!" 100)  where
  "f oo! g == sfcomp\<cdot>f\<cdot>g"

lemma SID1 [simp]: "SID\<cdot>!x = x"
  by (simp add: SID_def)

lemma sfcomp1: "(f oo! g) = (\<Lambda>! x. f\<cdot>!(g\<cdot>!x))"
  by (simp add: soo_def)

lemma sfcomp2 [simp]: "(f oo! g)\<cdot>!x = f\<cdot>!(g\<cdot>!x)"
  by (simp add: sfcomp1)

lemma sfcomp_strict [simp]: "\<bottom> oo! f = \<bottom>" "f oo! \<bottom> = \<bottom>"
  by (simp_all add: sfun_eq_iff sfcomp1)

default_sort cpo

end

