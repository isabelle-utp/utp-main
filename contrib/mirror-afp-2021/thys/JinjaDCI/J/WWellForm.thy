(*  Title:      JinjaDCI/J/WWellForm.thy

    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/WWellForm.thy by Tobias Nipkow
*)

section \<open> Weak well-formedness of Jinja programs \<close>

theory WWellForm imports "../Common/WellForm" Expr begin

definition wwf_J_mdecl :: "J_prog \<Rightarrow> cname \<Rightarrow> J_mb mdecl \<Rightarrow> bool"
where
  "wwf_J_mdecl P C  \<equiv>  \<lambda>(M,b,Ts,T,(pns,body)).
 length Ts = length pns \<and> distinct pns \<and> \<not>sub_RI body \<and>
  (case b of
   NonStatic \<Rightarrow> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns
 | Static \<Rightarrow> fv body \<subseteq> set pns)"

lemma wwf_J_mdecl_NonStatic[simp]:
  "wwf_J_mdecl P C (M,NonStatic,Ts,T,pns,body) =
  (length Ts = length pns \<and> distinct pns \<and> \<not>sub_RI body \<and> this \<notin> set pns \<and> fv body \<subseteq> {this} \<union> set pns)"
(*<*)by(simp add:wwf_J_mdecl_def)(*>*)

lemma wwf_J_mdecl_Static[simp]:
  "wwf_J_mdecl P C (M,Static,Ts,T,pns,body) =
  (length Ts = length pns \<and> distinct pns \<and> \<not>sub_RI body \<and> fv body \<subseteq> set pns)"
(*<*)by(simp add:wwf_J_mdecl_def)(*>*)

abbreviation
  wwf_J_prog :: "J_prog \<Rightarrow> bool" where
  "wwf_J_prog \<equiv> wf_prog wwf_J_mdecl"


lemma sees_wwf_nsub_RI:
 "\<lbrakk> wwf_J_prog P; P \<turnstile> C sees M,b : Ts\<rightarrow>T = (pns, body) in D \<rbrakk> \<Longrightarrow> \<not>sub_RI body"
apply(drule sees_wf_mdecl, simp)
apply(unfold wwf_J_mdecl_def wf_mdecl_def, simp)
done

end
