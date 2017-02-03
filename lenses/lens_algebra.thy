theory lens_algebra
imports lens_laws
begin

subsection \<open>Lens composition, plus, unit, and identity\<close>

definition lens_comp :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c)" (infixr ";\<^sub>L" 80) where
[lens_defs]: "lens_comp Y X = \<lparr> lens_get = lens_get Y \<circ> lens_get X
                              , lens_put = (\<lambda> \<sigma> v. lens_put X \<sigma> (lens_put Y (lens_get X \<sigma>) v)) \<rparr>"

definition lens_plus :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Longrightarrow> 'c" (infixr "+\<^sub>L" 75) where
[lens_defs]: "X +\<^sub>L Y = \<lparr> lens_get = (\<lambda> \<sigma>. (lens_get X \<sigma>, lens_get Y \<sigma>))
                       , lens_put = (\<lambda> \<sigma> (u, v). lens_put X (lens_put Y \<sigma> v) u) \<rparr>"

definition fst_lens :: "'a \<Longrightarrow> 'a \<times> 'b" ("fst\<^sub>L") where
[lens_defs]: "fst\<^sub>L = \<lparr> lens_get = fst, lens_put = (\<lambda> (\<sigma>, \<rho>) u. (u, \<rho>)) \<rparr>"

definition snd_lens :: "'b \<Longrightarrow> 'a \<times> 'b" ("snd\<^sub>L") where
[lens_defs]: "snd\<^sub>L = \<lparr> lens_get = snd, lens_put = (\<lambda> (\<sigma>, \<rho>) u. (\<sigma>, u)) \<rparr>"

lemma get_fst_lens [simp]: "get\<^bsub>fst\<^sub>L\<^esub> (x, y) = x"
  by (simp add: fst_lens_def)

lemma get_snd_lens [simp]: "get\<^bsub>snd\<^sub>L\<^esub> (x, y) = y"
  by (simp add: snd_lens_def)

abbreviation swap_lens :: "'a \<times> 'b \<Longrightarrow> 'b \<times> 'a" ("swap\<^sub>L") where
"swap\<^sub>L \<equiv> snd\<^sub>L +\<^sub>L fst\<^sub>L"

definition unit_lens :: "unit \<Longrightarrow> 'a" ("0\<^sub>L") where
[lens_defs]: "0\<^sub>L = \<lparr> lens_get = (\<lambda> _. ()), lens_put = (\<lambda> \<sigma> x. \<sigma>) \<rparr>"

text {* The quotient operator $X /_L Y$ shortens lens $X$ by cutting off $Y$ from the end. It is
  thus the dual of the composition operator. *}

definition lens_quotient :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> 'a \<Longrightarrow> 'b" (infixr "'/\<^sub>L" 90) where
[lens_defs]: "X /\<^sub>L Y = \<lparr> lens_get = \<lambda> \<sigma>. get\<^bsub>X\<^esub> (create\<^bsub>Y\<^esub> \<sigma>)
                       , lens_put = \<lambda> \<sigma> v. get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (create\<^bsub>Y\<^esub> \<sigma>) v) \<rparr>"

definition id_lens :: "'a \<Longrightarrow> 'a" ("1\<^sub>L") where
[lens_defs]: "1\<^sub>L = \<lparr> lens_get = id, lens_put = (\<lambda> _. id) \<rparr>"

definition lens_override :: "'a \<Rightarrow> 'a \<Rightarrow> ('b \<Longrightarrow> 'a) \<Rightarrow> 'a" ("_ \<oplus>\<^sub>L _ on _" [95,0,96] 95) where
[lens_defs]: "S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on X = put\<^bsub>X\<^esub> S\<^sub>1 (get\<^bsub>X\<^esub> S\<^sub>2)"

definition lens_inv :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b \<Longrightarrow> 'a)" where
[lens_defs]: "lens_inv x = \<lparr> lens_get = create\<^bsub>x\<^esub>, lens_put = \<lambda> \<sigma>. get\<^bsub>x\<^esub> \<rparr>"

subsection \<open>Closure properties\<close>

lemma id_wb_lens: "wb_lens id_lens"
  by (unfold_locales, simp_all add: id_lens_def)

lemma unit_wb_lens: "wb_lens unit_lens"
  by (unfold_locales, simp_all add: unit_lens_def)

lemma comp_wb_lens: "\<lbrakk> wb_lens x; wb_lens y \<rbrakk> \<Longrightarrow> wb_lens (x ;\<^sub>L y)"
  by (unfold_locales, simp_all add: lens_comp_def)

lemma comp_mwb_lens: "\<lbrakk> mwb_lens x; mwb_lens y \<rbrakk> \<Longrightarrow> mwb_lens (x ;\<^sub>L y)"
  by (unfold_locales, simp_all add: lens_comp_def)

lemma id_vwb_lens: "vwb_lens 1\<^sub>L"
  by (unfold_locales, simp_all add: id_lens_def)

lemma unit_vwb_lens: "vwb_lens 0\<^sub>L"
  by (unfold_locales, simp_all add: unit_lens_def)

lemma comp_vwb_lens: "\<lbrakk> vwb_lens x; vwb_lens y \<rbrakk> \<Longrightarrow> vwb_lens (x ;\<^sub>L y)"
  by (unfold_locales, simp_all add: lens_comp_def)

lemma lens_comp_anhil [simp]: "wb_lens x \<Longrightarrow> 0\<^sub>L ;\<^sub>L x = 0\<^sub>L"
  by (simp add: unit_lens_def lens_comp_def comp_def)

lemma unit_ief_lens: "ief_lens 0\<^sub>L"
  by (unfold_locales, simp_all add: unit_lens_def)

lemma plus_mwb_lens:
  assumes "mwb_lens x" "mwb_lens y" "x \<bowtie> y"
  shows "mwb_lens (x +\<^sub>L y)"
  using assms
  apply (unfold_locales)
  apply (simp_all add: lens_plus_def prod.case_eq_if lens_indep_sym)
  apply (simp add: lens_indep_comm)
done
    
lemma plus_wb_lens:
  assumes "wb_lens x" "wb_lens y" "x \<bowtie> y"
  shows "wb_lens (x +\<^sub>L y)"
  using assms
  apply (unfold_locales, simp_all add: lens_plus_def)
  apply (simp add: lens_indep_sym prod.case_eq_if)
done

lemma plus_vwb_lens:
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "vwb_lens (x +\<^sub>L y)"
  using assms
  apply (unfold_locales, simp_all add: lens_plus_def)
  apply (simp add: lens_indep_sym prod.case_eq_if)
  apply (simp add: lens_indep_comm prod.case_eq_if)
done

lemma fst_vwb_lens: "vwb_lens fst\<^sub>L"
  by (unfold_locales, simp_all add: fst_lens_def prod.case_eq_if)

lemma snd_vwb_lens: "vwb_lens snd\<^sub>L"
  by (unfold_locales, simp_all add: snd_lens_def prod.case_eq_if)

lemma id_bij_lens: "bij_lens 1\<^sub>L"
  by (unfold_locales, simp_all add: id_lens_def)

lemma inv_id_lens: "lens_inv 1\<^sub>L = 1\<^sub>L"
  by (auto simp add: lens_inv_def id_lens_def lens_create_def)

lemma lens_inv_bij: "bij_lens X \<Longrightarrow> bij_lens (lens_inv X)"
  by (unfold_locales, simp_all add: lens_inv_def lens_create_def)
    
subsection \<open>Composition laws\<close>

lemma lens_comp_assoc: "(X ;\<^sub>L Y) ;\<^sub>L Z = X ;\<^sub>L (Y ;\<^sub>L Z)"
  by (auto simp add: lens_comp_def)

lemma lens_comp_left_id [simp]: "1\<^sub>L ;\<^sub>L X = X"
  by (simp add: id_lens_def lens_comp_def)

lemma lens_comp_right_id [simp]: "X ;\<^sub>L 1\<^sub>L = X"
  by (simp add: id_lens_def lens_comp_def)
    
subsection \<open>Independence laws\<close>
  
lemma lens_indep_quasi_irrefl: "\<lbrakk> wb_lens x; eff_lens x \<rbrakk> \<Longrightarrow> \<not> (x \<bowtie> x)"
  by (auto simp add: lens_indep_def ief_lens_def ief_lens_axioms_def, metis (full_types) wb_lens.get_put)

lemma lens_indep_left_comp:
  "\<lbrakk> mwb_lens z; x \<bowtie> y \<rbrakk> \<Longrightarrow> (x ;\<^sub>L z) \<bowtie> (y ;\<^sub>L z)"
  apply (rule lens_indepI)
  apply (auto simp add: lens_comp_def)
  apply (simp add: lens_indep_comm)
  apply (simp add: lens_indep_sym)
done

lemma lens_indep_right_comp:
  "y \<bowtie> z \<Longrightarrow> (x ;\<^sub>L y) \<bowtie> (x ;\<^sub>L z)"
  apply (auto intro!: lens_indepI simp add: lens_comp_def)
  using lens_indep_comm lens_indep_sym apply fastforce
  apply (simp add: lens_indep_sym)
done

lemma lens_indep_left_ext [intro]:
  "y \<bowtie> z \<Longrightarrow> (x ;\<^sub>L y) \<bowtie> z"
  apply (auto intro!: lens_indepI simp add: lens_comp_def)
  apply (simp add: lens_indep_comm)
  apply (simp add: lens_indep_sym)
done

lemma lens_indep_right_ext [intro]:
  "x \<bowtie> z \<Longrightarrow> x \<bowtie> (y ;\<^sub>L z)"
  by (simp add: lens_indep_left_ext lens_indep_sym)

lemma fst_snd_lens_indep:
  "fst\<^sub>L \<bowtie> snd\<^sub>L"
  by (simp add: lens_indep_def fst_lens_def snd_lens_def)
    
lemma split_prod_lens_indep:
  assumes "mwb_lens X"
  shows "(fst\<^sub>L ;\<^sub>L X) \<bowtie> (snd\<^sub>L ;\<^sub>L X)"
  using assms fst_snd_lens_indep lens_indep_left_comp vwb_lens_mwb by blast
        
end