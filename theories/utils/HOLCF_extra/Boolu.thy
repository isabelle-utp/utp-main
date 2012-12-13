theory Boolu
imports HOLCF
begin

instantiation bool :: po
begin
definition
  "x \<sqsubseteq> y \<longleftrightarrow> (x \<longrightarrow> y)"
instance by (default, unfold below_bool_def, fast+)
end

instance bool :: chfin
apply default
apply (drule finite_range_imp_finch)
apply (rule finite)
apply (simp add: finite_chain_def)
done

instance bool :: pcpo
proof
  have "\<forall>y. False \<sqsubseteq> y" by (simp add: below_bool_def)
  thus "\<exists>x::bool. \<forall>y. x \<sqsubseteq> y" ..
qed

lemma is_lub_bool: "S <<| (True \<in> S)"
  unfolding is_lub_def is_ub_def below_bool_def by auto

lemma lub_bool: "lub S = (True \<in> S)"
  using is_lub_bool by (rule lub_eqI)

lemma bottom_eq_False[simp]: "\<bottom> = False"
by (rule below_antisym [OF minimal], simp add: below_bool_def)

definition tt :: "bool\<^sub>\<bottom>" where
"tt = up\<cdot>True"

definition ff :: "bool\<^sub>\<bottom>" where
"ff = up\<cdot>False"

lemma Exh_boolu: "t = \<bottom> \<or> t = tt \<or> t = ff"
unfolding ff_def tt_def by (induct t) auto

lemma booluE [case_names bottom tt ff]:
  "\<lbrakk>p = \<bottom> \<Longrightarrow> Q; p = tt \<Longrightarrow> Q; p = ff \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding ff_def tt_def by (induct p) auto

lemma boolu_induct [case_names bottom tt ff]:
  "\<lbrakk>P \<bottom>; P tt; P ff\<rbrakk> \<Longrightarrow> P x"
by (cases x rule: booluE) simp_all

text {* distinctness for type boolu *}

lemma dist_below_boolu [simp]:
  "tt \<notsqsubseteq> \<bottom>" "ff \<notsqsubseteq> \<bottom>" "tt \<notsqsubseteq> ff"
unfolding tt_def ff_def by (simp_all add: below_bool_def)

lemma dist_eq_tr [simp]:
  "tt \<noteq> \<bottom>" "ff \<noteq> \<bottom>" "tt \<noteq> ff" "\<bottom> \<noteq> tt" "\<bottom> \<noteq> ff" "ff \<noteq> tt"
unfolding tt_def ff_def by simp_all

lemma  ff_below_tt [simp]: "ff \<sqsubseteq> tt"
  by (simp add:tt_def ff_def below_bool_def)

definition oor :: "bool\<^sub>\<bottom> \<rightarrow> bool\<^sub>\<bottom> \<rightarrow> bool\<^sub>\<bottom>" where
"oor = fup\<cdot>(\<Lambda> x. fup\<cdot>(\<Lambda> y. up\<cdot>(x \<or> y)))"

abbreviation oor_syn :: "bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom>" (infixr "\<or>\<or>" 60) where
"oor_syn x y \<equiv> oor\<cdot>x\<cdot>y"  

definition oand :: "bool\<^sub>\<bottom> \<rightarrow> bool\<^sub>\<bottom> \<rightarrow> bool\<^sub>\<bottom>" where
"oand = fup\<cdot>(\<Lambda> x. fup\<cdot>(\<Lambda> y. up\<cdot>(x \<and> y)))"

abbreviation oand_syn :: "bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom> \<Rightarrow> bool\<^sub>\<bottom>" (infixr "\<and>\<and>" 60) where
"oand_syn x y \<equiv> oand\<cdot>x\<cdot>y"

lemma cont_or1[simp,cont2cont]: "cont (\<lambda> x. x \<or> y)"
  apply (rule chfindom_monofun2cont)
  apply (simp add: below_fun_def monofun_def below_bool_def)
done

lemma cont_or2[simp,cont2cont]: "cont (\<lambda> y. x \<or> y)"
  apply (rule chfindom_monofun2cont)
  apply (simp add: below_fun_def monofun_def below_bool_def)
done

lemma cont_and1[simp,cont2cont]: "cont (\<lambda> x. x \<and> y)"
  apply (rule chfindom_monofun2cont)
  apply (simp add: below_fun_def monofun_def below_bool_def)
done

lemma cont_and2[simp,cont2cont]: "cont (\<lambda> y. x \<and> y)"
  apply (rule chfindom_monofun2cont)
  apply (simp add: below_fun_def monofun_def below_bool_def)
done

lemma cont_fup[simp,cont2cont]: "cont f \<Longrightarrow> cont (\<lambda> x. fup\<cdot>(f x))"
  by (simp)

lemma oor_thms [simp]: 
  "x \<or>\<or> ff = x" "tt \<or>\<or> tt = tt" "ff \<or>\<or> x = x"
  "\<bottom> \<or>\<or> y = \<bottom>" "x \<or>\<or> \<bottom> = \<bottom>"
  apply (case_tac[!] x rule:booluE)
  apply (simp_all add:oor_def tt_def ff_def cont2cont_LAM)
done

lemma oand_thms [simp]:
  "tt \<and>\<and> x = x" "x \<and>\<and> tt = x" "ff \<and>\<and> ff = ff"
  "\<bottom> \<and>\<and> y = \<bottom>" "x \<and>\<and> \<bottom> = \<bottom>"
  apply (case_tac[!] x rule:booluE)
  apply (simp_all add:oand_def tt_def ff_def cont2cont_LAM)
done

lemma cont2cont_if [simp, cont2cont]:
  assumes b: "cont b" and f: "cont f" and g: "cont g"
  shows "cont (\<lambda>x. if b x then f x else g x)"
  apply (rule contI)
oops

end