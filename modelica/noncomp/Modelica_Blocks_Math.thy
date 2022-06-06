theory Modelica_Blocks_Math
  imports Modelica_Blocks_Core "../Modelica_Math"
begin

definition MathBlock ::  "('a, 'l, 'c) mexpr \<Rightarrow> ('a, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: 
  "MathBlock e y = \<lparr> mieqs = true
                   , mdeqs = true
                   , maeqs = (&y =\<^sub>u e)
                   , mqeqs = true
                   , mreqs = {}
                   , mzcfs = {}
                   , mtevs = (\<lambda> t. False) \<rparr>"
  
lemma uapply_const [simp]: 
  "\<guillemotleft>\<lambda>x. c\<guillemotright>(v)\<^sub>a = \<guillemotleft>c\<guillemotright>"
  by (rel_auto)
    
lemma MathBlock_test:
  "(\<epsilon>, s, q) \<Turnstile> \<lbrakk>MathBlock e y\<rbrakk>\<^sub>m = \<^bold>R\<^sub>s (R1 true \<turnstile> [&y =\<^sub>u e]\<^sub>C\<^sub>> ;; (\<lceil>$y\<acute> =\<^sub>u \<lceil>e\<rceil>\<^sub>>\<rceil>\<^sub>h \<and> q \<leftarrow>\<^sub>h $q) \<diamondop> false)"
  apply (simp add: mblock_sem_def MathBlock_def srd_mu_equiv gfp_const alpha hrdUntil_false hrdPred_non_term closure unrest Let_def false_alt_def[THEN sym])
  apply (simp add: rdes_def closure unrest rpred wp)
done

abbreviation MathBlockUnary :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'l, 'c) mcon \<Rightarrow> ('b, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
"MathBlockUnary f u y \<equiv> MathBlock (\<guillemotleft>f\<guillemotright>(&u)\<^sub>a) y"
  
definition Gain :: 
  "real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: "Gain k u y = MathBlock (\<guillemotleft>k\<guillemotright>*&u) y"

definition Sum :: 
  "'i itself \<Rightarrow> real ^ 'i::finite \<Rightarrow> (real^'i, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where 
[urel_defs, mo_defs]: "Sum nin k u y = MathBlock (sum\<^sub>u(\<guillemotleft>k\<guillemotright> * &u)) y"

definition Add ::
  "real \<Rightarrow> real \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: "Add k1 k2 u1 u2 y = MathBlock (\<guillemotleft>k1\<guillemotright>*&u1 + \<guillemotleft>k2\<guillemotright>*&u2) y"

definition Product ::
  "(real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: "Product u1 u2 y = MathBlock (&u1 * &u2) y"

definition Division ::
  "(real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where
[upred_defs, mo_defs]: "Division u1 u2 y = MathBlock (&u1 / &u2) y"

definition Abs :: "(real, 'l, 'c) mcon \<Rightarrow> (real, 'l, 'c) mcon \<Rightarrow> ('l, 'c) mblock" where 
[upred_defs, mo_defs]: "Abs = MathBlockUnary abs"

end
