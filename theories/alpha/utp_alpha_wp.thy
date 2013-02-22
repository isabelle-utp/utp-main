theory utp_alpha_wp
  imports utp_alpha_laws
begin

ML {*
  structure wp =
    Named_Thms (val name = @{binding wp} val description = "weakest precondition theorems")
*}

setup wp.setup

definition alpha_wp :: 
  "'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE \<Rightarrow> 'VALUE WF_ALPHA_PREDICATE" (infixr "wp" 150) where
"Q wp r \<equiv> \<not>\<alpha> (Q ;\<alpha> (\<not>\<alpha> r))"

lemma SemiA_wp [wp]: 
  "\<lbrakk> P \<in> WF_RELATION; Q \<in> WF_RELATION; r \<in> WF_RELATION \<rbrakk> \<Longrightarrow> (P ;\<alpha> Q) wp r = (P wp (Q wp r))"
  by (simp add: alpha_wp_def, smt NotA_WF_RELATION SemiA_assoc)

end