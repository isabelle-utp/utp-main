(******************************************************************************)
(* Project: Isabelle/UTP                                                      *)
(* File: McCarthy_Logic.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* McCarthy 3-value logic *}

theory McCarthy_Logic
imports Main
begin

type_synonym tvl = "bool option"

notation
  Some ("\<lfloor>_\<rfloor>")

abbreviation mdef :: "tvl \<Rightarrow> bool" ("\<D>\<^sub>3") where
"mdef p \<equiv> p \<noteq> None"

syntax
  "_TT_tvl" :: "tvl" ("TT")
  "_FF_tvl" :: "tvl" ("FF")
  "_UU_tvl" :: "tvl" ("UU")

translations
  "_TT_tvl" => "CONST Some CONST True"
  "_FF_tvl" => "CONST Some CONST False"
  "_UU_tvl" => "CONST None"

definition mconj :: "tvl \<Rightarrow> tvl \<Rightarrow> tvl" where
  "mconj p q = (case (p, q) of 
                     (Some True, x)  \<Rightarrow> x
                   | (Some False, _) \<Rightarrow> Some False
                   | (_, _) \<Rightarrow> None)"

definition mdisj :: "tvl \<Rightarrow> tvl \<Rightarrow> tvl" where
  "mdisj p q = (case (p, q) of 
                     (Some True, _) \<Rightarrow> Some True
                   | (Some False, x) \<Rightarrow> x
                   | (_, _) \<Rightarrow> None)"

definition mnot :: "tvl \<Rightarrow> tvl" where
"mnot p = (case p of None \<Rightarrow> None | Some x \<Rightarrow> Some (\<not> x))"

definition mimplies :: "tvl \<Rightarrow> tvl \<Rightarrow> tvl" where
"mimplies p q = (mdisj (mnot p) q)"

definition mtaut :: "tvl \<Rightarrow> bool" where
"mtaut b \<longleftrightarrow> b = TT" 

notation
  mconj (infixr "\<and>\<^sub>3" 35) and
  mdisj (infixr "\<or>\<^sub>3" 35) and
  mimplies (infixr "\<Rightarrow>\<^sub>3" 25) and
  mnot ("\<not>\<^sub>3 _" [40] 40) and
  mtaut ("[_]\<^sub>3")

lemma tvl_cases:
  "\<lbrakk> p = TT \<Longrightarrow> P; p = FF \<Longrightarrow> P; p = UU \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

(* Simplication Rules *)

lemma mconj_simps [simp]:
  "(TT \<and>\<^sub>3 q) = q" "(FF \<and>\<^sub>3 q) = FF" "(UU \<and>\<^sub>3 q) = UU"
  by (auto simp add: mconj_def)

lemma mdisj_simps [simp]:
  "(TT \<or>\<^sub>3 p) = TT" "(FF \<or>\<^sub>3 p) = p" "(UU \<or>\<^sub>3 q) = UU"
  by (auto simp add: mdisj_def)

lemma mnot_simps [simp]:
  "(\<not>\<^sub>3 UU) = UU" "(\<not>\<^sub>3 (Some p)) = Some (\<not> p)"
  by (simp_all add:mnot_def)

lemma mimplies_simps [simp]:
  "(FF \<Rightarrow>\<^sub>3 q) = TT" "(TT \<Rightarrow>\<^sub>3 q) = q" "(UU \<Rightarrow>\<^sub>3 q) = UU"
  by (simp_all add:mimplies_def)

lemma mtaut_Some [simp]: "[Some p]\<^sub>3 = p"
  by (simp add:mtaut_def)

lemma mtaut_None [simp]: "[None]\<^sub>3 = False"
  by (simp add:mtaut_def)

lemma mconj_Some_Some [simp]: 
  "(\<lfloor>p\<rfloor> \<and>\<^sub>3 \<lfloor>q\<rfloor>) = \<lfloor>p \<and> q\<rfloor>"
  by (case_tac p, case_tac[!] q, simp_all)

lemma mdisj_Some_Some [simp]: 
  "(\<lfloor>p\<rfloor> \<or>\<^sub>3 \<lfloor>q\<rfloor>) = \<lfloor>p \<or> q\<rfloor>"
  by (case_tac p, case_tac[!] q, simp_all)

lemma mimplies_Some_Some [simp]: 
  "(\<lfloor>p\<rfloor> \<Rightarrow>\<^sub>3 \<lfloor>q\<rfloor>) = \<lfloor>p \<longrightarrow> q\<rfloor>"
  by (case_tac p, case_tac[!] q, simp_all)

lemma mconj_True_right [simp]: 
  "(p \<and>\<^sub>3 TT) = p"
  by (cases p rule:tvl_cases, simp_all)

lemma mtaut_mimplies_rNone [simp]:
  "[p \<Rightarrow>\<^sub>3 None]\<^sub>3 = [\<not>\<^sub>3 p]\<^sub>3"
  by (cases p rule:tvl_cases, simp_all)

lemma mand_mimplies [simp]: "(p \<and>\<^sub>3 q \<Rightarrow>\<^sub>3 r) = (p \<Rightarrow>\<^sub>3 q \<Rightarrow>\<^sub>3 r)"
  by (cases p rule:tvl_cases, simp_all)
  
lemma mand_assoc [simp]: "((p \<and>\<^sub>3 q) \<and>\<^sub>3 r) = (p \<and>\<^sub>3 (q \<and>\<^sub>3 r))" 
  by (cases p rule:tvl_cases, simp_all)

(* Deduction Rules for TVL *)

lemma mimpliesI_Some [intro]: "\<lbrakk> x \<Longrightarrow> [y]\<^sub>3 \<rbrakk> \<Longrightarrow> [\<lfloor>x\<rfloor> \<Rightarrow>\<^sub>3 y]\<^sub>3"
  by (cases y rule:tvl_cases, auto)

lemma mconjI [intro]:
  "\<lbrakk> [p]\<^sub>3; [q]\<^sub>3 \<rbrakk> \<Longrightarrow> [p \<and>\<^sub>3 q]\<^sub>3"
  by (simp add:mtaut_def)

lemma mconjE [elim]: 
  "\<lbrakk> [P \<and>\<^sub>3 Q]\<^sub>3; \<lbrakk> [P]\<^sub>3; [Q]\<^sub>3 \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (cases P rule:tvl_cases, auto)

lemma mdisjI1 [intro]: 
  "[p]\<^sub>3 \<Longrightarrow> [p \<or>\<^sub>3 q]\<^sub>3"
  by (simp add:mtaut_def)

lemma mdisjI2 [intro]: 
  "\<lbrakk> \<D>\<^sub>3(p); [q]\<^sub>3 \<rbrakk> \<Longrightarrow> [p \<or>\<^sub>3 q]\<^sub>3"
  apply (cases p rule:tvl_cases)
  apply (simp_all add:mtaut_def)
done

lemma mdisjE [elim]:
  "\<lbrakk> [P \<or>\<^sub>3 Q]\<^sub>3; [P]\<^sub>3 \<Longrightarrow> R; [Q]\<^sub>3 \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (cases P rule:tvl_cases, simp_all)

lemma mnot_double [simp]:
  "(\<not>\<^sub>3 (\<not>\<^sub>3 p)) = p"
  by (cases p rule:tvl_cases, simp_all)

lemma p_TT [simp]: "p = TT \<longleftrightarrow> [p]\<^sub>3"
  by (auto simp add: mtaut_def) 

end
