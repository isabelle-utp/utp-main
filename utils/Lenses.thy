section {* Functional programming lenses *}

theory Lenses
imports Main
begin

record ('a, '\<alpha>) lens =
  lens_get :: "'\<alpha> \<Rightarrow> 'a" ("get\<index>")
  lens_put :: "'\<alpha> \<Rightarrow> 'a \<Rightarrow> '\<alpha>" ("put\<index>")

subsection {* Lens independence *}

definition lens_indep :: "('a, '\<alpha>) lens \<Rightarrow> ('b, '\<alpha>) lens \<Rightarrow> bool" (infix "\<bowtie>" 50) where
"x \<bowtie> y \<longleftrightarrow> (\<forall> u v \<sigma>. lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v)"

lemma lens_indep_sym:  "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
  by (simp add: lens_indep_def)

lemma lens_indep_comm:
  "x \<bowtie> y \<Longrightarrow> lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v"
  by (simp add: lens_indep_def)

subsection {* Lens composition and identity *}

definition lens_comp :: "('a, 'b) lens \<Rightarrow> ('b, 'c) lens \<Rightarrow> ('a, 'c) lens" (infixr "\<circ>\<^sub>l" 80) where
"lens_comp y x = \<lparr> lens_get = lens_get y \<circ> lens_get x, lens_put = (\<lambda> \<sigma> v. lens_put x \<sigma> (lens_put y (lens_get x \<sigma>) v)) \<rparr>"

definition id_lens :: "('\<alpha>, '\<alpha>) lens" ("I\<^sub>l") where
"id_lens = \<lparr> lens_get = id, lens_put = (\<lambda> _. id) \<rparr>"

lemma lens_comp_assoc: "(x \<circ>\<^sub>l y) \<circ>\<^sub>l z = x \<circ>\<^sub>l (y \<circ>\<^sub>l z)"
  by (auto simp add: lens_comp_def)

lemma lens_comp_left_id [simp]: "I\<^sub>l \<circ>\<^sub>l x = x"
  by (simp add: id_lens_def lens_comp_def)

lemma lens_comp_right_id [simp]: "x \<circ>\<^sub>l I\<^sub>l = x"
  by (simp add: id_lens_def lens_comp_def)

subsection {* Weak lenses *}

locale weak_lens =
  fixes x :: "('a, '\<alpha>) lens" (structure)
  assumes put_get: "get (put \<sigma> v) = v"
begin

  definition update :: "('a \<Rightarrow> 'a) \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha>)" where
  "update f \<sigma> = put \<sigma> (f (get \<sigma>))"

  lemma get_update: "get (update f \<sigma>) = f (get \<sigma>)"
    by (simp add: put_get update_def)

  lemma view_determination: "put \<sigma> u = put \<rho> v \<Longrightarrow> u = v"
    by (metis put_get)

  lemma put_inj: "inj (put \<sigma>)"
    by (simp add: injI view_determination)

end

declare weak_lens.put_get [simp]

subsection {* Well-behaved lenses *}

locale wb_lens = weak_lens +
  assumes get_put: "put \<sigma> (get \<sigma>) = \<sigma>"
begin

  lemma put_twice: "put (put \<sigma> v) v = put \<sigma> v"
    by (metis get_put put_get)

  lemma put_surjectivity: "\<exists> \<rho> v. put \<rho> v = \<sigma>"
    using get_put by blast

  lemma source_stability: "\<exists> v. put \<sigma> v = \<sigma>"
    using get_put by auto

end

declare wb_lens.get_put [simp]

lemma wb_lens_weak [simp]: "wb_lens x \<Longrightarrow> weak_lens x"
  by (simp_all add: wb_lens_def) 

lemma lens_indep_get [simp]:
  assumes "wb_lens x" "x \<bowtie> y"
  shows "lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>"
proof -
  have "lens_get x (lens_put y \<sigma> v) = lens_get x (lens_put y (lens_put x \<sigma> (lens_get x \<sigma>)) v)"
    by (simp add: assms(1))
  also have "... = lens_get x (lens_put x (lens_put y \<sigma> v) (lens_get x \<sigma>))"
    by (simp add: assms(2) lens_indep_comm)
  also have "... = lens_get x \<sigma>"
    by (simp add: assms(1))
  finally show ?thesis .
qed

lemma id_wb_lens: "wb_lens id_lens"
  by (unfold_locales, simp_all add: id_lens_def)

lemma comp_wb_lens: "\<lbrakk> wb_lens x; wb_lens y \<rbrakk> \<Longrightarrow> wb_lens (x \<circ>\<^sub>l y)"
  by (unfold_locales, simp_all add: lens_comp_def)

subsection {* Mainly well-behaved lenses *}

locale mwb_lens = weak_lens +
  assumes put_put: "put (put \<sigma> v) u = put \<sigma> u"
begin

  lemma update_comp: "update f (update g \<sigma>) = update (f \<circ> g) \<sigma>"
    by (simp add: put_get put_put update_def)

end

declare mwb_lens.put_put [simp]

lemma mwb_lens_weak [simp]:
  "mwb_lens x \<Longrightarrow> weak_lens x"
  by (simp add: mwb_lens_def)

lemma id_mwb_lens: "mwb_lens id_lens"
  by (unfold_locales, simp_all add: id_lens_def)

lemma comp_mwb_lens: "\<lbrakk> mwb_lens x; mwb_lens y \<rbrakk> \<Longrightarrow> mwb_lens (x \<circ>\<^sub>l y)"
  by (unfold_locales, simp_all add: lens_comp_def)

subsection {* Very well-behaved lenses *}

locale vwb_lens = wb_lens + mwb_lens
begin

  lemma source_determination:"get \<sigma> = get \<rho> \<Longrightarrow> put \<sigma> v = put \<rho> v \<Longrightarrow> \<sigma> = \<rho>"
    by (metis get_put put_put)

 lemma put_eq: 
   "\<lbrakk> get \<sigma> = k; put \<sigma> u = put \<rho> v \<rbrakk> \<Longrightarrow> put \<rho> k = \<sigma>"
   by (metis get_put put_put)   

end

lemma vwb_lens_wb [simp]: "vwb_lens x \<Longrightarrow> wb_lens x"
  by (simp_all add: vwb_lens_def)

lemma vwb_lens_mwb [simp]: "vwb_lens x \<Longrightarrow> mwb_lens x"
  by (simp_all add: vwb_lens_def)

lemma id_vwb_lens: "vwb_lens id_lens"
  by (unfold_locales, simp_all add: id_lens_def)

lemma comp_vwb_lens: "\<lbrakk> vwb_lens x; vwb_lens y \<rbrakk> \<Longrightarrow> vwb_lens (x \<circ>\<^sub>l y)"
  by (unfold_locales, simp_all add: lens_comp_def)

subsection {* Lense implementations *}

definition prod_lens :: "('a, '\<alpha>) lens \<Rightarrow> ('b, '\<alpha>) lens \<Rightarrow> ('a \<times> 'b, '\<alpha>) lens" where
"prod_lens x y = \<lparr> lens_get = (\<lambda> \<sigma>. (lens_get x \<sigma>, lens_get y \<sigma>))
                 , lens_put = (\<lambda> \<sigma> (u, v). lens_put x (lens_put y \<sigma> v) u) \<rparr>"

lemma prod_wb_lens:
  assumes "wb_lens x" "wb_lens y" "x \<bowtie> y"
  shows "wb_lens (prod_lens x y)"
  using assms
  apply (unfold_locales, simp_all add: prod_lens_def)
  apply (simp add: lens_indep_sym prod.case_eq_if)
done

lemma prod_vwb_lens:
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "vwb_lens (prod_lens x y)"
  using assms
  apply (unfold_locales, simp_all add: prod_lens_def)
  apply (simp add: lens_indep_sym prod.case_eq_if)
  apply (simp add: lens_indep_def prod.case_eq_if)
done

definition fst_lens :: "('a, '\<alpha>) lens \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) lens" where
"fst_lens x = \<lparr> lens_get = (\<lambda> (\<sigma>, \<rho>). lens_get x \<sigma>), lens_put = (\<lambda> (\<sigma>, \<rho>) u. (lens_put x \<sigma> u, \<rho>)) \<rparr>"

lemma fst_wb_lens:
  assumes "wb_lens x"
  shows "wb_lens (fst_lens x)"
  using assms
  by (unfold_locales, simp_all add: fst_lens_def prod.case_eq_if)

lemma fst_lens_pres_indep: "x \<bowtie> y \<Longrightarrow> fst_lens x \<bowtie> fst_lens y"
  by (simp add: fst_lens_def lens_indep_def)

definition snd_lens :: "('a, '\<beta>) lens \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) lens" where
"snd_lens x = \<lparr> lens_get = (\<lambda> (\<sigma>, \<rho>). lens_get x \<rho>), lens_put = (\<lambda> (\<sigma>, \<rho>) u. (\<sigma>, lens_put x \<rho> u)) \<rparr>"

lemma snd_wb_lens:
  assumes "wb_lens x"
  shows "wb_lens (snd_lens x)"
  using assms
  by (unfold_locales, simp_all add: snd_lens_def prod.case_eq_if)

lemma snd_lens_pres_indep: "x \<bowtie> y \<Longrightarrow> snd_lens x \<bowtie> snd_lens y"
  by (simp add: snd_lens_def lens_indep_def)

lemma fst_snd_lens_indep: "fst_lens x \<bowtie> snd_lens y"
  by (simp add: lens_indep_def fst_lens_def snd_lens_def)

lemma fst_mwb_lens:
  "mwb_lens x \<Longrightarrow> mwb_lens (fst_lens x)"
  by (unfold_locales, simp_all add: fst_lens_def prod.case_eq_if)

lemma snd_mwb_lens:
  "mwb_lens x \<Longrightarrow> mwb_lens (snd_lens x)"
  by (unfold_locales, simp_all add: snd_lens_def prod.case_eq_if)

lemma fst_vwb_lens:
  "vwb_lens x \<Longrightarrow> vwb_lens (fst_lens x)"
  by (unfold_locales, simp_all add: fst_lens_def prod.case_eq_if)

lemma snd_vwb_lens:
  "vwb_lens x \<Longrightarrow> vwb_lens (snd_lens x)"
  by (unfold_locales, simp_all add: snd_lens_def prod.case_eq_if)

definition fun_lens :: "'a \<Rightarrow> ('b, 'a \<Rightarrow> 'b) lens" where
"fun_lens x = \<lparr> lens_get = (\<lambda> f. f x), lens_put = (\<lambda> f u. f(x := u)) \<rparr>"

lemma fun_wb_lens: "wb_lens (fun_lens x)"
  by (unfold_locales, simp_all add: fun_lens_def)

definition map_lens :: "'a \<Rightarrow> ('b, 'a \<rightharpoonup> 'b) lens" where
"map_lens x = \<lparr> lens_get = (\<lambda> f. the (f x)), lens_put = (\<lambda> f u. f(x := Some u)) \<rparr>"

lemma map_mwb_lens: "mwb_lens (map_lens x)"
  by (unfold_locales, simp_all add: map_lens_def)

fun list_update_alt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"list_update_alt [] n y = (if (n = 0) then [y] else undefined # list_update_alt [] (n - 1) y)" |
"list_update_alt (x # xs) n y = (if (n = 0) then y # xs else x # list_update_alt xs (n - 1) y)"

declare list_update_alt.simps [simp del]

lemma nth_list_update_alt: "(list_update_alt xs i x) ! i = x"
  apply (induct xs)
  apply (subst list_update_alt.simps)
  apply (auto)
  apply (induct i)
  apply (auto)
  apply (simp add: list_update_alt.simps(1))
  apply (subst list_update_alt.simps)
  apply (auto)
  apply (induct i)
  apply (auto)
  apply (smt One_nat_def diff_Suc_1 less_Suc_eq_le less_numeral_extra(3) less_or_eq_imp_le list_update_alt.elims list_update_alt.simps(2) neq0_conv nth_Cons')
done

definition list_lens :: "nat \<Rightarrow> ('a, 'a list) lens" where
"list_lens i = \<lparr> lens_get = (\<lambda> xs. xs ! i), lens_put = (\<lambda> xs x. list_update_alt xs i x) \<rparr>"

lemma list_mwb_lens: "mwb_lens (list_lens x)"
  apply (unfold_locales, simp_all add: list_lens_def)
oops

end