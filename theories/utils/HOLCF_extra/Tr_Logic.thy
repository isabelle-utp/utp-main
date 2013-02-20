theory Tr_Logic
imports HOLCF
begin

default_sort cpo

(*
definition bool2tr :: "bool \<rightarrow> tr" where
"bool2tr = (\<Lambda> x. if x then TT else FF)"
*)

section {* Logical operators *}

definition vor :: "tr \<rightarrow> tr \<rightarrow> tr" where
"vor = (\<Lambda> (Def x) (Def y). Def (x \<or> y))"

abbreviation vor_syn :: "tr \<Rightarrow> tr \<Rightarrow> tr" (infixr "\<or>\<or>" 60) where
"vor_syn x y \<equiv> vor\<cdot>x\<cdot>y"  

definition vand :: "tr \<rightarrow> tr \<rightarrow> tr" where
"vand = (\<Lambda> (Def x) (Def y). Def (x \<and> y))"

abbreviation vand_syn :: "tr \<Rightarrow> tr \<Rightarrow> tr" (infixr "\<and>\<and>" 60) where
"vand_syn x y \<equiv> vand\<cdot>x\<cdot>y"

definition vnot :: "tr \<rightarrow> tr" where
"vnot = (\<Lambda> (Def x). Def (\<not> x))"

lemma vor_thms [simp]: 
  "x \<or>\<or> FF = x" "TT \<or>\<or> TT = TT" "FF \<or>\<or> x = x"
  "\<bottom> \<or>\<or> y = \<bottom>" "x \<or>\<or> \<bottom> = \<bottom>"
  apply (simp_all add:vor_def TT_def FF_def)
  apply (case_tac[!] x)
  apply (simp_all)
done

lemma vor_assoc:
  "x \<or>\<or> (y \<or>\<or> z) = (x \<or>\<or> y) \<or>\<or> z"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (case_tac[!] z rule:trE)
  apply (simp_all)  
done

lemma vor_comm:
  "x \<or>\<or> y = y \<or>\<or> x"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

lemma vor_idem [simp]:
  "x \<or>\<or> x = x"
  by (case_tac x rule:trE, simp_all)

lemma vor_nbot [simp]: "\<lbrakk>x\<noteq>\<bottom>;y\<noteq>\<bottom>\<rbrakk> \<Longrightarrow> x \<or>\<or> y \<noteq> \<bottom>"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

lemma vor_nbot_dest1 [dest]: "x \<or>\<or> y \<noteq> \<bottom> \<Longrightarrow> x \<noteq> \<bottom>"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

lemma vor_nbot_dest2 [dest]: "x \<or>\<or> y \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom>"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

lemma vor_bot [dest]: "x \<or>\<or> y = \<bottom> \<Longrightarrow> x = \<bottom> \<or> y = \<bottom>"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

lemma vand_thms [simp]:
  "TT \<and>\<and> x = x" "x \<and>\<and> TT = x" "FF \<and>\<and> FF = FF"
  "\<bottom> \<and>\<and> y = \<bottom>" "x \<and>\<and> \<bottom> = \<bottom>"
  apply (simp_all add:vand_def TT_def FF_def)
  apply (case_tac[!] x)
  apply (simp_all)
done

lemma vand_assoc:
  "x \<and>\<and> (y \<and>\<and> z) = (x \<and>\<and> y) \<and>\<and> z"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (case_tac[!] z rule:trE)
  apply (simp_all)  
done

lemma vand_comm:
  "x \<and>\<and> y = y \<and>\<and> x"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

lemma vand_idem [simp]:
  "x \<and>\<and> x = x"
  by (case_tac x rule:trE, simp_all)

lemma vand_nbot [simp]: "\<lbrakk>x\<noteq>\<bottom>;y\<noteq>\<bottom>\<rbrakk> \<Longrightarrow> x \<and>\<and> y \<noteq> \<bottom>"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

subsection {* Weak and strong tautologies *}

definition staut :: "tr \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>st") where
"staut x = (x = TT)"

definition wtaut :: "tr \<Rightarrow> bool" ("\<lbrakk>_\<rbrakk>wt") where
"wtaut x = (x \<noteq> \<bottom> \<longrightarrow> \<lbrakk>x\<rbrakk>st)"

lemma wtaut_thms[simp]:
  "\<lbrakk>TT\<rbrakk>wt" "\<lbrakk>\<bottom>\<rbrakk>wt""\<not> \<lbrakk>FF\<rbrakk>wt"
  by (simp_all add:staut_def wtaut_def)

lemma staut_thms[simp]:
  "\<lbrakk>TT\<rbrakk>st" "\<not> \<lbrakk>\<bottom>\<rbrakk>st""\<not> \<lbrakk>FF\<rbrakk>st"
  by (simp_all add:staut_def)

lemma stautI[intro]: "\<lbrakk> \<lbrakk>p\<rbrakk>wt; p \<noteq> \<bottom> \<rbrakk> \<Longrightarrow> \<lbrakk>p\<rbrakk>st"
  by (simp add:wtaut_def)

lemma vand_st[simp]: "\<lbrakk>x \<and>\<and> y\<rbrakk>st = (\<lbrakk>x\<rbrakk>st \<and> \<lbrakk>y\<rbrakk>st)"
  apply (simp add:staut_def)
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

lemma vor_wt[simp]: "\<lbrakk>x \<or>\<or> y\<rbrakk>wt = (\<lbrakk>x\<rbrakk>wt \<or> \<lbrakk>y\<rbrakk>wt)"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (auto)
done

lemma wt_st_eq [intro]: "\<lbrakk> \<lbrakk>x\<rbrakk>wt = \<lbrakk>y\<rbrakk>wt; \<lbrakk>x\<rbrakk>st = \<lbrakk>y\<rbrakk>st \<rbrakk> \<Longrightarrow> x = y"
  apply (case_tac x rule:trE)
  apply (case_tac[!] y rule:trE)
  apply (simp_all)
done

(*
lemma bool2tr_st[simp]: "\<lbrakk>bool2tr\<cdot>x\<rbrakk>st = x"
  by (simp add:bool2tr_def)

lemma bool2tr_wt[simp]: "\<lbrakk>bool2tr\<cdot>x\<rbrakk>wt = x"
  by (simp add:bool2tr_def)
*)

end
