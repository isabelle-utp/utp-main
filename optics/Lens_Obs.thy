theory Lens_Obs
  imports Lenses
begin
  
lemma refl_UNIV: "refl UNIV"
  by (simp add: refl_onI)
  
lemma equiv_UNIV [simp]: "equiv UNIV UNIV"
  by (auto intro!: equivI refl_UNIV symI transI)
  
lemma equiv_Id [simp]: "equiv UNIV Id"
  by (auto intro!: equivI refl_Id symI transI)

typedef 's obs = "{(R :: 's rel, C :: 's rel). equiv UNIV R \<and> equiv UNIV C \<and> R \<inter> C = Id}"
  by (rule_tac x="(Id, UNIV)" in exI, auto simp add: equiv_def refl_Id refl_on_def sym_def trans_def)
    
setup_lifting type_definition_obs
  
lift_definition region :: "'s obs \<Rightarrow> ('s \<times> 's) set" is fst .
lift_definition coregion :: "'s obs \<Rightarrow> ('s \<times> 's) set" is snd .
    
lemma state_eq_iff:
  "x = y \<longleftrightarrow> (x, y) \<in> region S \<and> (x, y) \<in> coregion S"
  by (transfer, auto, blast)

lemma state_dist_either:
  "\<lbrakk> (x, y) \<in> region S; x \<noteq> y \<rbrakk> \<Longrightarrow> (x, y) \<notin> coregion S"
  by (meson state_eq_iff)
    
    
lift_definition lens_obs :: "('v \<Longrightarrow> 's) \<Rightarrow> 's obs" ("\<lbrakk>_\<rbrakk>\<^sub>\<sim>") is
"\<lambda> X. if (vwb_lens X) 
         then ({(s\<^sub>1, s\<^sub>2). s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X = s\<^sub>1}, {(s\<^sub>1, s\<^sub>2). s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X = s\<^sub>2})
         else (UNIV, Id)"
  apply (auto intro!:equivI refl_onI symI transI)
  apply (metis lens_override_def lens_override_idem mwb_lens_weak vwb_lens_mwb weak_lens.put_get)
  apply (metis lens_override_def mwb_lens_weak vwb_lens_mwb weak_lens.put_get)
   apply (metis lens_override_def vwb_lens.put_eq)+
done

lemma "\<lbrakk> equiv UNIV A; equiv UNIV B; A \<inter> B = Id \<rbrakk> \<Longrightarrow> equiv UNIV (A \<union> B)"
  apply (auto intro!: equivI symI refl_onI transI elim!: equivE dest: refl_onD)
  apply (meson symE)+
     apply (meson transE)+
oops

instantiation obs :: (type) order
begin
  lift_definition less_eq_obs :: "'a obs \<Rightarrow> 'a obs \<Rightarrow> bool" is
  "\<lambda> (X\<^sub>1, X\<^sub>2) (Y\<^sub>1, Y\<^sub>2). Y\<^sub>1 \<subseteq> X\<^sub>1 \<and> X\<^sub>2 \<subseteq> Y\<^sub>2" .
  definition less_obs :: "'a obs \<Rightarrow> 'a obs \<Rightarrow> bool" where
  "less_obs x y = (x \<le> y \<and> \<not> y \<le> x)"
instance
  apply (intro_classes)
  apply (simp add: less_obs_def)
  apply (transfer, auto simp add: prod.case_eq_if)+
done
end
  
lemma "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> coregion \<lbrakk>Y\<rbrakk>\<^sub>\<sim> \<subseteq> region \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  apply (transfer, auto)
  
lemma "region \<lbrakk>fst\<^sub>L\<rbrakk>\<^sub>\<sim> \<subseteq> coregion \<lbrakk>snd\<^sub>L\<rbrakk>\<^sub>\<sim>"
  by (transfer, simp add: fst_vwb_lens snd_vwb_lens, auto simp add: lens_defs)
  by (simp add: fst_lens_def lens_override_def snd_lens_def)
  
instantiation obs :: (type) "{zero, one, uminus, plus}"
begin
  lift_definition zero_obs :: "'s obs" is "(UNIV, Id)"by (auto)  
  lift_definition one_obs :: "'s obs" is "(Id, UNIV)" by (auto)
  lift_definition uminus_obs :: "'s obs \<Rightarrow> 's obs" is "\<lambda> (R,C). (C,R)" by (auto)
  lift_definition plus_obs :: "'s obs \<Rightarrow> 's obs \<Rightarrow> 's obs" is 
   "\<lambda> (X\<^sub>1, X\<^sub>2) (Y\<^sub>1, Y\<^sub>2). (X\<^sub>1 \<inter> Y\<^sub>1, X\<^sub>2 \<union> Y\<^sub>2)" (* - ((X\<^sub>2 \<inter> Y\<^sub>2) - Id) *)
    apply (auto)
     apply (metis Int_UNIV equiv_def refl_on_Int sym_Int trans_Int)
    apply (auto intro!: equivI refl_onI symI elim!: equivE)
    apply (meson symE)
    apply (meson symE)  
     
  instance ..
end
  
lemma "(0::'a obs) \<le> X"
  by (transfer, auto)
    
lemma "X \<le> (1::'a obs)"    
  by (transfer, auto)
    
lemma fst_lens_inv_snd: "- \<lbrakk>fst\<^sub>L\<rbrakk>\<^sub>\<sim> = \<lbrakk>snd\<^sub>L\<rbrakk>\<^sub>\<sim>"
  by (transfer, auto simp add: fst_vwb_lens snd_vwb_lens, simp_all add: lens_defs)
    
lemma "\<lbrakk>fst\<^sub>L\<rbrakk>\<^sub>\<sim> + \<lbrakk>snd\<^sub>L\<rbrakk>\<^sub>\<sim> = 1"
  by (transfer, auto)
    
lemma 
  fixes X :: "'s obs"
  shows "X + 0 = 1"
  apply (transfer, simp)

    
lemma "vwb_lens X \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> + (- \<lbrakk>X\<rbrakk>\<^sub>\<sim>) = 1"
  by (transfer, auto)
    
(*
*)
  
    
lemma one_lens_obs: "\<lbrakk>1\<^sub>L\<rbrakk>\<^sub>\<sim> = 1"
  by (transfer, auto)
    
lemma zero_lens_obs: "\<lbrakk>0\<^sub>L\<rbrakk>\<^sub>\<sim> = 0"
  by (transfer, auto) 
    
lemma "x + 0 = (x :: 's obs)"
  apply (transfer, simp add: prod.case_eq_if)
    
lemma plus_lens_obs: 
  "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> = \<lbrakk>X\<rbrakk>\<^sub>\<sim> + \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  apply (transfer, auto simp add: plus_vwb_lens)
  apply (metis lens_indep.lens_put_irr2 lens_override_def lens_override_plus vwb_lens.put_eq)

    

(*
lemma lens_obs_nempty: "\<lbrakk>X\<rbrakk>\<^sub>\<sim> \<noteq> {}"
  by (auto simp add: lens_obs_def)

lemma refl_lens_obs: "refl \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  by (rule refl_onI, simp_all add: lens_obs_def)

lemma sym_lens_obs: "sym \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  by (rule symI, simp_all add: lens_obs_def)
*)


lemma zero_lens_obs: "\<lbrakk>0\<^sub>L\<rbrakk>\<^sub>\<sim> = UNIV"
  by (auto simp add: lens_defs)

lemma one_lens_obs: "\<lbrakk>1\<^sub>L\<rbrakk>\<^sub>\<sim> = Id"
  by (auto simp add: lens_defs)

lemma plus_lens_obs: 
  "\<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> = (\<lbrakk>X\<rbrakk>\<^sub>\<sim> \<inter> \<lbrakk>Y\<rbrakk>\<^sub>\<sim>)"
  by (auto simp add: lens_defs)
    
lemma sublens_obs:
  "X \<subseteq>\<^sub>L Y \<Longrightarrow> \<lbrakk>Y\<rbrakk>\<^sub>\<sim> \<subseteq> \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  by (auto simp add: lens_defs)
    
lemma lens_equiv_obs:
  "X \<approx>\<^sub>L Y \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> = \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (simp add: lens_equiv_def set_eq_subset sublens_obs)

lemma "(\<lbrakk>fst\<^sub>L\<rbrakk>\<^sub>\<sim> - Id) \<inter> (\<lbrakk>snd\<^sub>L\<rbrakk>\<^sub>\<sim> - Id) = {}"
  by (auto simp add: lens_defs)
    
end