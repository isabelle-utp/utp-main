theory Modelica_Blocks_Math
  imports Modelica_Blocks_Core "../Modelica_Math"
begin

definition MathBlock ::  "('a, 'c mst_scheme) hexpr \<Rightarrow> ('a, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]: "MathBlock e y = \<lparr> minit = true, mceqs = y \<leftarrow>\<^sub>H e, mgrds = [] \<rparr>"

abbreviation MathBlockUnary :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'c) mcon \<Rightarrow> ('b, 'c) mcon \<Rightarrow> 'c mblock" where
"MathBlockUnary f u y \<equiv> MathBlock (\<guillemotleft>f\<guillemotright>($u\<acute>)\<^sub>a) y"
  
definition Gain :: 
  "real \<Rightarrow> (real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]: "Gain k u y = MathBlock (\<guillemotleft>k\<guillemotright>*$u\<acute>) y"

definition Sum :: 
  "'i itself \<Rightarrow> real ^ 'i::finite \<Rightarrow> (real^'i, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where 
[urel_defs, mo_defs]: "Sum nin k u y = MathBlock (sum\<^sub>u(\<guillemotleft>k\<guillemotright> * $u\<acute>)) y"

definition Add ::
  "real \<Rightarrow> real \<Rightarrow> (real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]: "Add k1 k2 u1 u2 y = MathBlock (\<guillemotleft>k1\<guillemotright>*$u1\<acute> + \<guillemotleft>k1\<guillemotright>*$u2\<acute>) y"

definition Product ::
  "(real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]: "Product u1 u2 y = MathBlock ($u1\<acute> * $u2\<acute>) y"

definition Division ::
  "(real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where
[upred_defs, mo_defs]: "Division u1 u2 y = MathBlock ($u1\<acute> / $u2\<acute>) y"

definition Abs :: "(real, 'c) mcon \<Rightarrow> (real, 'c) mcon \<Rightarrow> 'c mblock" where 
[upred_defs, mo_defs]: "Abs = MathBlockUnary abs"

end
