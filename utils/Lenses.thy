section {* Lenses *}

theory Lenses
imports Main
begin

subsection {* Lens signature *}

record ('a, 'b) lens =
  lens_get :: "'b \<Rightarrow> 'a" ("get\<index>")
  lens_put :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("put\<index>")

definition lens_create :: "('a, 'b) lens \<Rightarrow> 'a \<Rightarrow> 'b" ("create\<index>") where
"lens_create X v = lens_put X undefined v"

definition effectual :: "('a, 'b) lens \<Rightarrow> bool" where
"effectual X = (\<forall> \<sigma>. \<exists> v. lens_put X \<sigma> v \<noteq> \<sigma>)"

abbreviation "ineffectual X \<equiv> (\<not> effectual X)"

subsection {* Lens composition, plus, unit, and identity *}

definition lens_comp :: "('a, 'b) lens \<Rightarrow> ('b, 'c) lens \<Rightarrow> ('a, 'c) lens" (infixr ";\<^sub>L" 80) where
"lens_comp Y X = \<lparr> lens_get = lens_get Y \<circ> lens_get X, lens_put = (\<lambda> \<sigma> v. lens_put X \<sigma> (lens_put Y (lens_get X \<sigma>) v)) \<rparr>"

definition lens_plus :: "('a, 'c) lens \<Rightarrow> ('b, 'c) lens \<Rightarrow> ('a \<times> 'b, 'c) lens" (infixr "+\<^sub>L" 75) where
"X +\<^sub>L Y = \<lparr> lens_get = (\<lambda> \<sigma>. (lens_get X \<sigma>, lens_get Y \<sigma>))
          , lens_put = (\<lambda> \<sigma> (u, v). lens_put X (lens_put Y \<sigma> v) u) \<rparr>"

definition fst_lens :: "('a, 'a \<times> 'b) lens" ("fst\<^sub>L") where
"fst\<^sub>L = \<lparr> lens_get = fst, lens_put = (\<lambda> (\<sigma>, \<rho>) u. (u, \<rho>)) \<rparr>"

lemma get_fst_lens [simp]: "get\<^bsub>fst\<^sub>L\<^esub> (x, y) = x"
  by (simp add: fst_lens_def)

definition snd_lens :: "('b, 'a \<times> 'b) lens" ("snd\<^sub>L") where
"snd\<^sub>L = \<lparr> lens_get = snd, lens_put = (\<lambda> (\<sigma>, \<rho>) u. (\<sigma>, u)) \<rparr>"

lemma get_snd_lens [simp]: "get\<^bsub>snd\<^sub>L\<^esub> (x, y) = y"
  by (simp add: snd_lens_def)

definition unit_lens :: "(unit, 'a) lens" ("0\<^sub>L") where
"0\<^sub>L = \<lparr> lens_get = (\<lambda> _. ()), lens_put = (\<lambda> \<sigma> x. \<sigma>) \<rparr>"

lemma ineffectual_unit_lens: "ineffectual 0\<^sub>L"
  by (auto simp add: effectual_def unit_lens_def)

text {* The quotient operator $X /_L Y$ shortens lens $X$ by cutting off $Y$ from the end. It is
  thus the dual of the composition operator. *} 

definition lens_quotient :: "('a, 'c) lens \<Rightarrow> ('b, 'c) lens \<Rightarrow> ('a, 'b) lens" (infixr "'/\<^sub>L" 90) where
"X /\<^sub>L Y = \<lparr> lens_get = \<lambda> \<sigma>. get\<^bsub>X\<^esub> (create\<^bsub>Y\<^esub> \<sigma>), lens_put = \<lambda> \<sigma> v. get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (create\<^bsub>Y\<^esub> \<sigma>) v) \<rparr>"

definition id_lens :: "('\<alpha>, '\<alpha>) lens" ("1\<^sub>L") where
"1\<^sub>L = \<lparr> lens_get = id, lens_put = (\<lambda> _. id) \<rparr>"

lemma lens_comp_assoc: "(X ;\<^sub>L Y) ;\<^sub>L Z = X ;\<^sub>L (Y ;\<^sub>L Z)"
  by (auto simp add: lens_comp_def)

lemma lens_comp_left_id [simp]: "1\<^sub>L ;\<^sub>L X = X"
  by (simp add: id_lens_def lens_comp_def)

lemma lens_comp_right_id [simp]: "X ;\<^sub>L 1\<^sub>L = X"
  by (simp add: id_lens_def lens_comp_def)

subsection {* Weak lenses *}

locale weak_lens =
  fixes x :: "('a, '\<alpha>) lens" (structure)
  assumes put_get: "get (put \<sigma> v) = v"
begin

  lemma create_get: "get (create v) = v"
    by (simp add: lens_create_def put_get)

  lemma create_inj: "inj create"
    by (metis create_get injI)

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
declare weak_lens.create_get [simp]

lemma ineffectual_const_get:
  "\<lbrakk> weak_lens x; ineffectual x \<rbrakk> \<Longrightarrow> \<exists> v.  \<forall> \<sigma>. lens_get x \<sigma> = v"
  apply (auto simp add: effectual_def)
  apply (metis weak_lens.put_get)
done

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

lemma id_wb_lens: "wb_lens id_lens"
  by (unfold_locales, simp_all add: id_lens_def)

lemma unit_wb_lens: "wb_lens unit_lens"
  by (unfold_locales, simp_all add: unit_lens_def)

lemma comp_wb_lens: "\<lbrakk> wb_lens x; wb_lens y \<rbrakk> \<Longrightarrow> wb_lens (x ;\<^sub>L y)"
  by (unfold_locales, simp_all add: lens_comp_def)

subsection {* Lens independence *}

definition lens_indep :: "('a, '\<alpha>) lens \<Rightarrow> ('b, '\<alpha>) lens \<Rightarrow> bool" (infix "\<bowtie>" 50) where
"x \<bowtie> y \<longleftrightarrow> (\<forall> u v \<sigma>. lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v
                    \<and> lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>
                    \<and> lens_get y (lens_put x \<sigma> u) = lens_get y \<sigma>)"

lemma lens_indepI:
  "\<lbrakk> \<And> u v \<sigma>. lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v;
     \<And> v \<sigma>. lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>;
     \<And> u \<sigma>. lens_get y (lens_put x \<sigma> u) = lens_get y \<sigma> \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lens_indep_def)

text {* Independence is irreflexive for effectual lenses *}

lemma lens_indep_sym:  "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
  by (simp add: lens_indep_def)

lemma lens_indep_comm:
  "x \<bowtie> y \<Longrightarrow> lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v"
  by (simp add: lens_indep_def)

lemma lens_indep_get [simp]:
  assumes "x \<bowtie> y"
  shows "lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>"
  using assms lens_indep_def by fastforce

lemma plus_wb_lens:
  assumes "wb_lens x" "wb_lens y" "x \<bowtie> y"
  shows "wb_lens (x +\<^sub>L y)"
  using assms
  apply (unfold_locales, simp_all add: lens_plus_def)
  apply (simp add: lens_indep_sym prod.case_eq_if)
done

lemma fst_lens_plus:
  "wb_lens y \<Longrightarrow> fst\<^sub>L ;\<^sub>L (x +\<^sub>L y) = x"
  by (simp add: fst_lens_def lens_plus_def lens_comp_def comp_def)

lemma fst_snd_lens_indep:
  "fst\<^sub>L \<bowtie> snd\<^sub>L"
  by (simp add: lens_indep_def fst_lens_def snd_lens_def)

text {* The second law requires independence as we have to apply x first, before y *}

lemma snd_lens_prod:
  "\<lbrakk> wb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> snd\<^sub>L ;\<^sub>L (x +\<^sub>L y) = y"
  apply (simp add: snd_lens_def lens_plus_def lens_comp_def comp_def)
  apply (subst lens_indep_comm)
  apply (simp_all)
done

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

lemma comp_mwb_lens: "\<lbrakk> mwb_lens x; mwb_lens y \<rbrakk> \<Longrightarrow> mwb_lens (x ;\<^sub>L y)"
  by (unfold_locales, simp_all add: lens_comp_def)

lemma lens_indep_quasi_irrefl: "\<lbrakk> mwb_lens x; effectual x \<rbrakk> \<Longrightarrow> \<not> (x \<bowtie> x)"
  by (metis effectual_def lens_indep_def mwb_lens.put_put)

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
  
lemma lens_indep_left_ext:
  "y \<bowtie> z \<Longrightarrow> (x ;\<^sub>L y) \<bowtie> z" 
  apply (auto intro!: lens_indepI simp add: lens_comp_def)
  apply (simp add: lens_indep_comm)
  apply (simp add: lens_indep_sym)
done

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

lemma id_vwb_lens: "vwb_lens 1\<^sub>L"
  by (unfold_locales, simp_all add: id_lens_def)

lemma unit_vwb_lens: "vwb_lens 0\<^sub>L"
  by (unfold_locales, simp_all add: unit_lens_def)

lemma comp_vwb_lens: "\<lbrakk> vwb_lens x; vwb_lens y \<rbrakk> \<Longrightarrow> vwb_lens (x ;\<^sub>L y)"
  by (unfold_locales, simp_all add: lens_comp_def)

lemma lens_comp_anhil [simp]: "wb_lens x \<Longrightarrow> 0\<^sub>L ;\<^sub>L x = 0\<^sub>L"
  by (simp add: unit_lens_def lens_comp_def comp_def)

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

subsection {* Bijective lenses *}

text {* Bijective lenses express that two views of a particular source are equivalent. *}

locale bij_lens = weak_lens +
  assumes strong_get_put: "put \<sigma> (get \<rho>) = \<rho>"
begin

sublocale vwb_lens
proof
  fix \<sigma> v u
  show "put \<sigma> (get \<sigma>) = \<sigma>"
    by (simp add: strong_get_put)
  show "put (put \<sigma> v) u = put \<sigma> u"
    by (metis put_get strong_get_put)
qed

  lemma put_surj: "surj (put \<sigma>)"
    by (metis strong_get_put surj_def)

  lemma put_bij: "bij (put \<sigma>)"
    by (simp add: bijI put_inj put_surj)

  lemma put_is_create: "put \<sigma> v = create v"
    by (metis create_get strong_get_put)

  lemma get_create: "create (get \<sigma>) = \<sigma>"
    by (metis put_get put_is_create source_stability)

end

declare bij_lens.strong_get_put [simp]
declare bij_lens.get_create [simp]

lemma bij_lens_weak [simp]: 
  "bij_lens x \<Longrightarrow> weak_lens x"
  by (simp_all add: bij_lens_def)

lemma bij_lens_vwb [simp]: "bij_lens x \<Longrightarrow> vwb_lens x"
  by (unfold_locales, simp_all add: bij_lens.put_is_create)

definition lens_inv :: "('a, 'b) lens \<Rightarrow> ('b, 'a) lens" where
"lens_inv x = \<lparr> lens_get = create\<^bsub>x\<^esub>, lens_put = \<lambda> \<sigma>. get\<^bsub>x\<^esub> \<rparr>"

lemma id_bij_lens: "bij_lens 1\<^sub>L"
  by (unfold_locales, simp_all add: id_lens_def)

lemma inv_id_lens: "lens_inv 1\<^sub>L = 1\<^sub>L"
  by (auto simp add: lens_inv_def id_lens_def lens_create_def)

lemma lens_inv_bij: "bij_lens X \<Longrightarrow> bij_lens (lens_inv X)"
  by (unfold_locales, simp_all add: lens_inv_def lens_create_def)

subsection {* Order and equivalence on lenses *}

text {* A lens $X$ is a sub-lens of $Y$ if there is a well-behaved lens $Z$ such that $X = Z ; Y$,
  or in other words if $X$ can be expressed purely in terms of $Y$. *}

definition sublens :: "('a, '\<alpha>) lens \<Rightarrow> ('b, '\<alpha>) lens \<Rightarrow> bool" (infix "\<subseteq>\<^sub>L" 55) where
"sublens X Y = (\<exists> Z :: ('a, 'b) lens. vwb_lens Z \<and> X = Z ;\<^sub>L Y)"

lemma sublens_pres_mwb:
  "\<lbrakk> mwb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> mwb_lens X"
  by (unfold_locales, auto simp add: sublens_def lens_comp_def)

lemma sublens_pres_wb:
  "\<lbrakk> wb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> wb_lens X"
  by (unfold_locales, auto simp add: sublens_def lens_comp_def)

lemma sublens_pres_vwb:
  "\<lbrakk> vwb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> vwb_lens X"
  by (unfold_locales, auto simp add: sublens_def lens_comp_def)

lemma sublens_refl:
  "X \<subseteq>\<^sub>L X"
  using id_vwb_lens sublens_def by force

lemma sublens_trans:
  "\<lbrakk> X \<subseteq>\<^sub>L Y; Y \<subseteq>\<^sub>L Z \<rbrakk> \<Longrightarrow> X \<subseteq>\<^sub>L Z"
  apply (auto simp add: sublens_def lens_comp_assoc)
  apply (rename_tac Z\<^sub>1 Z\<^sub>2)
  apply (rule_tac x="Z\<^sub>1 ;\<^sub>L Z\<^sub>2" in exI)
  apply (simp add: lens_comp_assoc)
  using comp_vwb_lens apply blast
done

lemma sublens_least: "wb_lens X \<Longrightarrow> 0\<^sub>L \<subseteq>\<^sub>L X"
  using sublens_def unit_vwb_lens by fastforce

lemma sublens_greatest: "vwb_lens X \<Longrightarrow> X \<subseteq>\<^sub>L 1\<^sub>L"
  by (simp add: sublens_def)

lemma sublens_put_put:
  "\<lbrakk> mwb_lens X; Y \<subseteq>\<^sub>L X \<rbrakk> \<Longrightarrow> lens_put X (lens_put Y \<sigma> v) u = lens_put X \<sigma> u"
  by (auto simp add: sublens_def lens_comp_def)

lemma sublens_obs_get:
  "\<lbrakk> mwb_lens X; Y \<subseteq>\<^sub>L X \<rbrakk> \<Longrightarrow>  get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> \<sigma> v) = get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> \<rho> v)"
  by (auto simp add: sublens_def lens_comp_def)

definition lens_equiv :: "('a, '\<alpha>) lens \<Rightarrow> ('b, '\<alpha>) lens \<Rightarrow> bool" (infix "\<approx>\<^sub>L" 51) where
"lens_equiv X Y = (X \<subseteq>\<^sub>L Y \<and> Y \<subseteq>\<^sub>L X)"

lemma lens_equivI [intro]:
  "\<lbrakk> X \<subseteq>\<^sub>L Y; Y \<subseteq>\<^sub>L X \<rbrakk> \<Longrightarrow> X \<approx>\<^sub>L Y"
  by (simp add: lens_equiv_def) 

lemma lens_equiv_refl:
  "X \<approx>\<^sub>L X"
  by (simp add: lens_equiv_def sublens_refl)

lemma lens_equiv_sym:
  "X \<approx>\<^sub>L Y \<Longrightarrow> Y \<approx>\<^sub>L X"
  by (simp add: lens_equiv_def)

lemma lens_equiv_trans:
  "\<lbrakk> X \<approx>\<^sub>L Y; Y \<approx>\<^sub>L Z \<rbrakk> \<Longrightarrow> X \<approx>\<^sub>L Z"
  by (auto intro: sublens_trans simp add: lens_equiv_def)

lemma unit_lens_indep: "0\<^sub>L \<bowtie> X"
  by (auto simp add: unit_lens_def lens_indep_def lens_equiv_def)

lemma fst_snd_id_lens: "fst\<^sub>L +\<^sub>L snd\<^sub>L = 1\<^sub>L"
  by (auto simp add: lens_plus_def fst_lens_def snd_lens_def id_lens_def)

lemma sublens_pres_indep:
  "\<lbrakk> X \<subseteq>\<^sub>L Y; Y \<bowtie> Z \<rbrakk> \<Longrightarrow> X \<bowtie> Z" 
  apply (auto intro!:lens_indepI simp add: sublens_def lens_comp_def lens_indep_comm)
  apply (simp add: lens_indep_sym)
done

lemma plus_pres_lens_indep: "\<lbrakk> X \<bowtie> Z; Y \<bowtie> Z \<rbrakk> \<Longrightarrow> (X +\<^sub>L Y) \<bowtie> Z"
  apply (rule lens_indepI)
  apply (simp_all add: lens_plus_def prod.case_eq_if)
  apply (simp add: lens_indep_comm)
  apply (simp add: lens_indep_sym)
done

lemma lens_comp_indep_cong_left:
  "\<lbrakk> mwb_lens Z; X ;\<^sub>L Z \<bowtie> Y ;\<^sub>L Z \<rbrakk> \<Longrightarrow> X \<bowtie> Y"
  apply (rule lens_indepI)
  apply (rename_tac u v \<sigma>)
  apply (drule_tac u=u and v=v and \<sigma>="create\<^bsub>Z\<^esub> \<sigma>" in lens_indep_comm)
  apply (simp add: lens_comp_def)
  apply (meson mwb_lens_weak weak_lens.view_determination)
  apply (rename_tac v \<sigma>)
  apply (drule_tac v=v and \<sigma>="create\<^bsub>Z\<^esub> \<sigma>" in lens_indep_get)
  apply (simp add: lens_comp_def)
  apply (drule lens_indep_sym)
  apply (rename_tac u \<sigma>)
  apply (drule_tac v=u and \<sigma>="create\<^bsub>Z\<^esub> \<sigma>" in lens_indep_get)
  apply (simp add: lens_comp_def)
done
  
lemma lens_quotient_mwb:
  "\<lbrakk> mwb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> mwb_lens (X /\<^sub>L Y)"
  by (unfold_locales, auto simp add: lens_quotient_def lens_create_def sublens_def lens_comp_def comp_def)  

subsection {* Lens algebraic laws *}

lemma plus_lens_distr: "mwb_lens Z \<Longrightarrow> (X +\<^sub>L Y) ;\<^sub>L Z = (X ;\<^sub>L Z) +\<^sub>L (Y ;\<^sub>L Z)"
  by (auto simp add: lens_comp_def lens_plus_def comp_def)

text {* This law explains the behaviour of lens quotient. *}

lemma lens_quotient_comp:
  "\<lbrakk> weak_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> (X /\<^sub>L Y) ;\<^sub>L Y = X"
  by (auto simp add: lens_quotient_def lens_comp_def comp_def sublens_def)

lemma lens_comp_quotient:
  "weak_lens Y \<Longrightarrow> (X ;\<^sub>L Y) /\<^sub>L Y = X"
  by (simp add: lens_quotient_def lens_comp_def)

lemma lens_quotient_id: "weak_lens X \<Longrightarrow> (X /\<^sub>L X) = 1\<^sub>L"
  by (force simp add: lens_quotient_def id_lens_def)

lemma lens_quotient_id_denom: "X /\<^sub>L 1\<^sub>L = X"
  by (simp add: lens_quotient_def id_lens_def lens_create_def)

lemma lens_quotient_unit: "weak_lens X \<Longrightarrow> (0\<^sub>L /\<^sub>L X) = 0\<^sub>L"
  by (simp add: lens_quotient_def unit_lens_def)

lemma lens_quotient_plus:
  "\<lbrakk> mwb_lens Z; X \<subseteq>\<^sub>L Z; Y \<subseteq>\<^sub>L Z \<rbrakk> \<Longrightarrow> (X +\<^sub>L Y) /\<^sub>L Z = (X /\<^sub>L Z) +\<^sub>L (Y /\<^sub>L Z)"
  apply (auto simp add: lens_quotient_def lens_plus_def sublens_def lens_comp_def comp_def)
  apply (rule ext)
  apply (rule ext)
  apply (simp add: prod.case_eq_if)
done

lemma plus_pred_sublens: "\<lbrakk> mwb_lens Z; X \<subseteq>\<^sub>L Z; Y \<subseteq>\<^sub>L Z; X \<bowtie> Y \<rbrakk> \<Longrightarrow> (X +\<^sub>L Y) \<subseteq>\<^sub>L Z"
  apply (auto simp add: sublens_def)
  apply (rename_tac Z\<^sub>1 Z\<^sub>2)
  apply (rule_tac x="Z\<^sub>1 +\<^sub>L Z\<^sub>2" in exI)
  apply (auto intro!: plus_wb_lens)
  apply (simp add: lens_comp_indep_cong_left plus_vwb_lens)
  apply (simp add: plus_lens_distr)
done

lemma lens_plus_sub_assoc_1:
  "\<lbrakk> X \<bowtie> Y; Y \<bowtie> Z; X \<bowtie> Z \<rbrakk> \<Longrightarrow> X +\<^sub>L Y +\<^sub>L Z \<subseteq>\<^sub>L (X +\<^sub>L Y) +\<^sub>L Z"
  apply (simp add: sublens_def)
  apply (rule_tac x="(fst\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (snd\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L snd\<^sub>L" in exI)
  apply (auto)
  apply (rule plus_vwb_lens)
  apply (simp add: comp_vwb_lens fst_vwb_lens)
  apply (rule plus_vwb_lens)
  apply (simp add: comp_vwb_lens fst_vwb_lens snd_vwb_lens)
  apply (simp add: snd_vwb_lens)
  apply (simp add: fst_snd_lens_indep lens_indep_left_ext)
  apply (rule lens_indep_sym)
  apply (rule plus_pres_lens_indep)
  using fst_snd_lens_indep fst_vwb_lens lens_indep_left_comp lens_indep_sym vwb_lens_mwb apply blast
  using fst_snd_lens_indep lens_indep_left_ext lens_indep_sym apply blast
  apply (auto simp add: lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if split_beta')[1]
done

lemma lens_plus_sub_assoc_2:
  "\<lbrakk> X \<bowtie> Y; Y \<bowtie> Z; X \<bowtie> Z \<rbrakk> \<Longrightarrow> (X +\<^sub>L Y) +\<^sub>L Z \<subseteq>\<^sub>L X +\<^sub>L Y +\<^sub>L Z"
  apply (simp add: sublens_def)
  apply (rule_tac x="(fst\<^sub>L +\<^sub>L (fst\<^sub>L ;\<^sub>L snd\<^sub>L)) +\<^sub>L (snd\<^sub>L ;\<^sub>L snd\<^sub>L)" in exI)
  apply (auto)
  apply (rule plus_vwb_lens)
  apply (rule plus_vwb_lens)
  apply (simp add: fst_vwb_lens)
  apply (simp add: comp_vwb_lens fst_vwb_lens snd_vwb_lens)
  apply (rule lens_indep_sym)
  apply (rule lens_indep_left_ext)
  using fst_snd_lens_indep lens_indep_sym apply blast
  apply (auto intro: comp_vwb_lens simp add: snd_vwb_lens)
  apply (rule plus_pres_lens_indep)
  apply (simp add: fst_snd_lens_indep lens_indep_left_ext lens_indep_sym)
  apply (simp add: fst_snd_lens_indep lens_indep_left_comp snd_vwb_lens)
  apply (auto simp add: lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if split_beta')[1]
done

lemma lens_plus_assoc:
  "\<lbrakk> X \<bowtie> Y; Y \<bowtie> Z; X \<bowtie> Z \<rbrakk> \<Longrightarrow> (X +\<^sub>L Y) +\<^sub>L Z \<approx>\<^sub>L X +\<^sub>L Y +\<^sub>L Z"
  by (simp add: lens_equivI lens_plus_sub_assoc_1 lens_plus_sub_assoc_2)

lemma lens_plus_swap:
  "X \<bowtie> Y \<Longrightarrow> (snd\<^sub>L +\<^sub>L fst\<^sub>L) ;\<^sub>L (X +\<^sub>L Y) = (Y +\<^sub>L X)"
  by (auto simp add: lens_plus_def fst_lens_def snd_lens_def id_lens_def lens_comp_def lens_indep_comm)

lemma lens_plus_sub_comm: "X \<bowtie> Y \<Longrightarrow> X +\<^sub>L Y \<subseteq>\<^sub>L Y +\<^sub>L X"
  apply (simp add: sublens_def)
  apply (rule_tac x="snd\<^sub>L +\<^sub>L fst\<^sub>L" in exI)
  apply (auto)
  apply (simp add: fst_snd_lens_indep fst_vwb_lens lens_indep_sym plus_vwb_lens snd_vwb_lens)
  apply (simp add: lens_indep_sym lens_plus_swap)
done
  
lemma lens_plus_comm: "X \<bowtie> Y \<Longrightarrow> X +\<^sub>L Y \<approx>\<^sub>L Y +\<^sub>L X"
  by (simp add: lens_equivI lens_indep_sym lens_plus_sub_comm)

lemma lens_plus_ub: "wb_lens Y \<Longrightarrow> X \<subseteq>\<^sub>L X +\<^sub>L Y"
  by (metis fst_lens_plus fst_vwb_lens sublens_def vwb_lens_wb)

lemma lens_comp_lb: "vwb_lens X \<Longrightarrow> X ;\<^sub>L Y \<subseteq>\<^sub>L Y"
  by (auto simp add: sublens_def)

lemma lens_unit_plus_sublens_1: "X \<subseteq>\<^sub>L 0\<^sub>L +\<^sub>L X"
  by (metis lens_comp_lb snd_lens_prod snd_vwb_lens unit_lens_indep unit_wb_lens vwb_lens_wb)

lemma lens_unit_prod_sublens_2: "0\<^sub>L +\<^sub>L x \<subseteq>\<^sub>L x"
  apply (auto simp add: sublens_def)
  apply (rule_tac x="0\<^sub>L +\<^sub>L 1\<^sub>L" in exI)
  apply (auto)
  apply (rule plus_vwb_lens)
  apply (simp add: unit_vwb_lens)
  apply (simp add: id_vwb_lens)
  apply (simp add: unit_lens_indep)
  apply (auto simp add: lens_plus_def unit_lens_def lens_comp_def id_lens_def prod.case_eq_if comp_def)
  apply (rule ext)
  apply (rule ext)
  apply (auto)
done

lemma bij_lens_inv_left:
  "bij_lens X \<Longrightarrow> lens_inv X ;\<^sub>L X = 1\<^sub>L"
  by (auto simp add: lens_inv_def lens_comp_def comp_def id_lens_def, rule ext, auto)

lemma bij_lens_inv_right:
  "bij_lens X \<Longrightarrow> X ;\<^sub>L lens_inv X = 1\<^sub>L"
  by (auto simp add: lens_inv_def lens_comp_def comp_def id_lens_def, rule ext, auto)

text {* Bijective lenses are precisely those that are equivalent to identity *}

lemma bij_lens_equiv_id:
  "bij_lens X \<longleftrightarrow> X \<approx>\<^sub>L 1\<^sub>L"
  apply (auto)
  apply (rule lens_equivI)
  apply (simp_all add: sublens_def)
  apply (rule_tac x="lens_inv X" in exI)
  apply (simp add: bij_lens_inv_left lens_inv_bij)
  apply (auto simp add: lens_equiv_def sublens_def id_lens_def lens_comp_def comp_def)
  apply (unfold_locales)
  apply (simp)
  apply (simp)
  apply (metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)
done

lemma lens_id_unique:
  "weak_lens Y \<Longrightarrow> Y = X ;\<^sub>L Y \<Longrightarrow> X = 1\<^sub>L"
  apply (cases Y)
  apply (cases X)
  apply (auto simp add: lens_comp_def comp_def id_lens_def fun_eq_iff)
  apply (metis select_convs(1) weak_lens.create_get)
  apply (metis select_convs(1) select_convs(2) weak_lens.put_get)
done

lemma bij_lens_via_comp_id_left:
  "\<lbrakk> wb_lens X; wb_lens Y; X ;\<^sub>L Y = 1\<^sub>L \<rbrakk> \<Longrightarrow> bij_lens X"
  apply (cases Y)
  apply (cases X)
  apply (auto simp add: lens_comp_def comp_def id_lens_def fun_eq_iff)
  apply (unfold_locales)
  apply (simp_all)
  using vwb_lens_wb wb_lens_weak weak_lens.put_get apply fastforce
  apply (metis select_convs(1) select_convs(2) wb_lens_weak weak_lens.put_get)
done

lemma bij_lens_via_comp_id_right:
  "\<lbrakk> wb_lens X; wb_lens Y; X ;\<^sub>L Y = 1\<^sub>L \<rbrakk> \<Longrightarrow> bij_lens Y"
  apply (cases Y)
  apply (cases X)
  apply (auto simp add: lens_comp_def comp_def id_lens_def fun_eq_iff)
  apply (unfold_locales)
  apply (simp_all)
  using vwb_lens_wb wb_lens_weak weak_lens.put_get apply fastforce
  apply (metis select_convs(1) select_convs(2) wb_lens_weak weak_lens.put_get)
done

text {* An equivalence can be proved by demonstrating a suitable bijective lens *}

lemma lens_equiv_via_bij:
  assumes "bij_lens Z" "X = Z ;\<^sub>L Y"
  shows "X \<approx>\<^sub>L Y"
  using assms
  apply (auto simp add: lens_equiv_def sublens_def)
  using bij_lens_vwb apply blast
  apply (rule_tac x="lens_inv Z" in exI)
  apply (auto simp add: lens_comp_assoc bij_lens_inv_left)
  using bij_lens_vwb lens_inv_bij apply blast
  apply (simp add: bij_lens_inv_left lens_comp_assoc[THEN sym])
done

lemma lens_equiv_iff_bij:
  assumes "weak_lens Y"
  shows "X \<approx>\<^sub>L Y \<longleftrightarrow> (\<exists> Z. bij_lens Z \<and> X = Z ;\<^sub>L Y)"
  apply (rule iffI)
  apply (auto simp add: lens_equiv_def sublens_def lens_id_unique)[1]
  apply (rename_tac Z\<^sub>1 Z\<^sub>2)
  apply (rule_tac x="Z\<^sub>1" in exI)
  apply (simp)
  apply (subgoal_tac "Z\<^sub>2 ;\<^sub>L Z\<^sub>1 = 1\<^sub>L")
  apply (meson bij_lens_via_comp_id_right vwb_lens_wb)
  apply (metis assms lens_comp_assoc lens_id_unique)
  using lens_equiv_via_bij apply blast
done

subsection {* Lens implementations *}

text {* Product functor lens *}

definition prod_lens :: "('\<alpha>, '\<gamma>) lens \<Rightarrow> ('\<beta>, '\<delta>) lens \<Rightarrow> ('\<alpha> \<times> '\<beta>, '\<gamma> \<times> '\<delta>) lens" (infixr "\<times>\<^sub>L" 85) where
"prod_lens X Y = \<lparr> lens_get = map_prod get\<^bsub>X\<^esub> get\<^bsub>Y\<^esub>
                 , lens_put = \<lambda> (u, v) (x, y). (put\<^bsub>X\<^esub> u x, put\<^bsub>Y\<^esub> v y) \<rparr>"

lemma prod_mwb_lens:
  "\<lbrakk> mwb_lens X; mwb_lens Y \<rbrakk> \<Longrightarrow> mwb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_wb_lens:
  "\<lbrakk> wb_lens X; wb_lens Y \<rbrakk> \<Longrightarrow> wb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_vwb_lens:
  "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> vwb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_as_plus: "X \<times>\<^sub>L Y = X ;\<^sub>L fst\<^sub>L +\<^sub>L Y ;\<^sub>L snd\<^sub>L"
  by (auto simp add: prod_lens_def fst_lens_def snd_lens_def lens_comp_def lens_plus_def)

lemma prod_lens_sublens_cong:
  "\<lbrakk> X\<^sub>1 \<subseteq>\<^sub>L X\<^sub>2; Y\<^sub>1 \<subseteq>\<^sub>L Y\<^sub>2 \<rbrakk> \<Longrightarrow> (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) \<subseteq>\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
  apply (auto simp add: sublens_def)
  apply (rename_tac Z\<^sub>1 Z\<^sub>2)
  apply (rule_tac x="Z\<^sub>1 \<times>\<^sub>L Z\<^sub>2" in exI)
  apply (auto)
  using prod_vwb_lens apply blast
  apply (auto simp add: prod_lens_def lens_comp_def prod.case_eq_if)
  apply (rule ext, rule ext)
  apply (auto simp add: prod_lens_def lens_comp_def prod.case_eq_if)
done

lemma prod_lens_equiv_cong:
  "\<lbrakk> X\<^sub>1 \<approx>\<^sub>L X\<^sub>2; Y\<^sub>1 \<approx>\<^sub>L Y\<^sub>2 \<rbrakk> \<Longrightarrow> (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) \<approx>\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
  by (simp add: lens_equiv_def prod_lens_sublens_cong)

lemma prod_lens_id_equiv:
  "1\<^sub>L \<times>\<^sub>L 1\<^sub>L = 1\<^sub>L"
  by (auto simp add: prod_lens_def id_lens_def)

lemma lens_indep_prod:
  "\<lbrakk> X\<^sub>1 \<bowtie> X\<^sub>2; Y\<^sub>1 \<bowtie> Y\<^sub>2 \<rbrakk> \<Longrightarrow> X\<^sub>1 \<times>\<^sub>L Y\<^sub>1 \<bowtie> X\<^sub>2 \<times>\<^sub>L Y\<^sub>2"
  apply (rule lens_indepI)
  apply (auto simp add: prod_lens_def prod.case_eq_if lens_indep_comm map_prod_def)
  apply (simp_all add: lens_indep_sym)
done

lemma lens_plus_prod_exchange:
  "(X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2) \<approx>\<^sub>L (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
proof (rule lens_equivI)
  show "(X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2) \<subseteq>\<^sub>L (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
    apply (simp add: sublens_def)
    apply (rule_tac x="((fst\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (fst\<^sub>L ;\<^sub>L snd\<^sub>L)) +\<^sub>L ((snd\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (snd\<^sub>L ;\<^sub>L snd\<^sub>L))" in exI)
    apply (auto)
    apply (auto intro!: plus_vwb_lens comp_vwb_lens fst_vwb_lens snd_vwb_lens lens_indep_right_comp)
    apply (auto intro!: lens_indepI simp add: lens_comp_def lens_plus_def fst_lens_def snd_lens_def)
    apply (auto simp add: prod_lens_def lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if comp_def)[1]
    apply (rule ext, rule ext, auto simp add: prod.case_eq_if)
  done  
  show "(X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) \<subseteq>\<^sub>L (X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2)"
    apply (simp add: sublens_def)
    apply (rule_tac x="((fst\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (fst\<^sub>L ;\<^sub>L snd\<^sub>L)) +\<^sub>L ((snd\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (snd\<^sub>L ;\<^sub>L snd\<^sub>L))" in exI)
    apply (auto)
    apply (auto intro!: plus_vwb_lens comp_vwb_lens fst_vwb_lens snd_vwb_lens lens_indep_right_comp)
    apply (auto intro!: lens_indepI simp add: lens_comp_def lens_plus_def fst_lens_def snd_lens_def)
    apply (auto simp add: prod_lens_def lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if comp_def)[1]
    apply (rule ext, rule ext, auto simp add: prod_lens_def prod.case_eq_if)
  done
qed

definition fun_lens :: "'a \<Rightarrow> ('b, 'a \<Rightarrow> 'b) lens" where
"fun_lens x = \<lparr> lens_get = (\<lambda> f. f x), lens_put = (\<lambda> f u. f(x := u)) \<rparr>"

lemma fun_wb_lens: "wb_lens (fun_lens x)"
  by (unfold_locales, simp_all add: fun_lens_def)

lemma fun_lens_indep:
  "x \<noteq> y \<Longrightarrow> fun_lens x \<bowtie> fun_lens y"
  by (simp add: fun_lens_def lens_indep_def fun_upd_twist)

definition map_lens :: "'a \<Rightarrow> ('b, 'a \<rightharpoonup> 'b) lens" where
"map_lens x = \<lparr> lens_get = (\<lambda> f. the (f x)), lens_put = (\<lambda> f u. f(x \<mapsto> u)) \<rparr>"

lemma map_mwb_lens: "mwb_lens (map_lens x)"
  by (unfold_locales, simp_all add: map_lens_def)

definition list_pad_out :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
"list_pad_out xs k = xs @ replicate (k + 1 - length xs) undefined"

definition list_augment :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"list_augment xs k v = (list_pad_out xs k)[k := v]"

definition nth' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
"nth' xs i = (if (length xs > i) then xs ! i else undefined)"

lemma list_update_append_lemma1: "i < length xs \<Longrightarrow> xs[i := v] @ ys = (xs @ ys)[i := v]"
  by (simp add: list_update_append)

lemma list_update_append_lemma2: "i < length ys \<Longrightarrow> xs @ ys[i := v] = (xs @ ys)[i + length xs := v]"
  by (simp add: list_update_append)

lemma list_augment_twice:
  "list_augment (list_augment xs i u) j v = list_pad_out xs (max i j)[i := u, j := v]"
  apply (auto simp add: list_augment_def list_pad_out_def list_update_append_lemma1 replicate_add[THEN sym] max_def)
  apply (metis Suc_le_mono add.commute diff_diff_add diff_le_mono le_add_diff_inverse2)
done

lemma list_augment_commute:
  "i \<noteq> j \<Longrightarrow> list_augment (list_augment \<sigma> j v) i u = list_augment (list_augment \<sigma> i u) j v"
  by (simp add: list_augment_twice list_update_swap max.commute)

lemma nth_list_augment: "list_augment xs k v ! k = v"
  by (simp add: list_augment_def list_pad_out_def)

lemma nth'_list_augment: "nth' (list_augment xs k v) k = v"
  by (auto simp add: nth'_def nth_list_augment list_augment_def list_pad_out_def)

lemma list_augment_same_twice: "list_augment (list_augment xs k u) k v = list_augment xs k v"
  by (simp add: list_augment_def list_pad_out_def)

lemma nth'_list_augment_diff: "i \<noteq> j \<Longrightarrow> nth' (list_augment \<sigma> i v) j = nth' \<sigma> j"
  by (auto simp add: list_augment_def list_pad_out_def nth_append nth'_def)

definition list_lens :: "nat \<Rightarrow> ('a, 'a list) lens" where
"list_lens i = \<lparr> lens_get = (\<lambda> xs. nth' xs i), lens_put = (\<lambda> xs x. list_augment xs i x) \<rparr>"

lemma list_mwb_lens: "mwb_lens (list_lens x)"
  by (unfold_locales, simp_all add: list_lens_def nth'_list_augment list_augment_same_twice)

lemma list_lens_indep:
  "i \<noteq> j \<Longrightarrow> list_lens i \<bowtie> list_lens j"
  by (simp add: list_lens_def lens_indep_def list_augment_commute nth'_list_augment_diff)

subsection {* Record field lenses *}

abbreviation (input) "fld_put f \<equiv> (\<lambda> \<sigma> u. f (\<lambda>_. u) \<sigma>)"

syntax "_FLDLENS" :: "id \<Rightarrow> ('a, 'r) lens"  ("FLDLENS _")
translations "FLDLENS x" => "\<lparr> lens_get = x, lens_put = CONST fld_put (_update_name x) \<rparr>"

end