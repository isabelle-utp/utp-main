theory Lens_Obs
  imports Lenses
begin
  
lemma refl_UNIV: "refl UNIV"
  by (simp add: refl_onI)
  
lemma equiv_UNIV [simp]: "equiv UNIV UNIV"
  by (auto intro!: equivI refl_UNIV symI transI)
  
lemma equiv_Id [simp]: "equiv UNIV Id"
  by (auto intro!: equivI refl_Id symI transI)

thm Ex_def

locale overrider =
  fixes F :: "'s \<Rightarrow> 's \<Rightarrow> 's"
  assumes 
    ovr_overshadow_left: "F (F x y) z = F x z" and
    ovr_overshadow_right: "F x (F y z) = F x z" and
    ovr_idem: "F x x = x"

declare overrider.ovr_overshadow_left [simp]
declare overrider.ovr_overshadow_right [simp]
declare overrider.ovr_idem [simp]

typedef 's scene = "{F :: 's \<Rightarrow> 's \<Rightarrow> 's. overrider F}"
  by (rule_tac x="\<lambda> x y. x" in exI, simp, unfold_locales, simp_all)

setup_lifting type_definition_scene

lift_definition region :: "'s scene \<Rightarrow> 's rel" 
is "\<lambda> F. {(s\<^sub>1, s\<^sub>2). (\<forall> s. F s s\<^sub>1 = F s s\<^sub>2)}" .

lift_definition coregion :: "'s scene \<Rightarrow> 's rel" 
is "\<lambda> F. {(s\<^sub>1, s\<^sub>2). (\<forall> s. F s\<^sub>1 s = F s\<^sub>2 s)}" .

lemma equiv_region: "equiv UNIV (region X)"
  apply (transfer)
  apply (rule equivI)
    apply (rule refl_onI)
     apply (auto)
   apply (rule symI)
   apply (auto)
  apply (rule transI)
  apply (auto)
  done

lemma equiv_coregion: "equiv UNIV (coregion X)"
  apply (transfer)
  apply (rule equivI)
    apply (rule refl_onI)
     apply (auto)
   apply (rule symI)
   apply (auto)
  apply (rule transI)
  apply (auto)
  done

lemma region_coregion_Id:
  "region X \<inter> coregion X = Id"
  by (transfer, auto, metis overrider.ovr_idem)

lemma state_eq_iff: "x = y \<longleftrightarrow> (x, y) \<in> region S \<and> (x, y) \<in> coregion S"
  by (metis IntE IntI pair_in_Id_conv region_coregion_Id)

lift_definition scene_override :: "'a \<Rightarrow> 'a \<Rightarrow> ('a scene) \<Rightarrow> 'a" ("_ \<oplus>\<^sub>S _ on _" [95,0,96] 95)
is "\<lambda> s\<^sub>1 s\<^sub>2 F. F s\<^sub>1 s\<^sub>2" .

lemma scene_override_idem: "s \<oplus>\<^sub>S s on X = s"
  by (transfer, simp)

lemma lens_override_idem [simp]:
  "\<lbrakk> mwb_lens X; S \<in> \<S>\<^bsub>X\<^esub> \<rbrakk> \<Longrightarrow> S \<oplus>\<^sub>L S on X = S"
  by (simp add: lens_override_def)

lemma obs_override_overshadow_left [simp]:
  "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X \<oplus>\<^sub>S S\<^sub>3 on X = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on X"
  by (transfer, simp)

lift_definition lens_scene :: "('v \<Longrightarrow> 's) \<Rightarrow> 's scene" ("\<lbrakk>_\<rbrakk>\<^sub>\<sim>") is
"\<lambda> X. if (vwb_lens X) then (\<lambda> s\<^sub>1 s\<^sub>2. s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X) else (\<lambda> s\<^sub>1 s\<^sub>2. s\<^sub>1)"
  by (unfold_locales, auto simp add: lens_override_def)

lemma lens_scene_override: 
  "vwb_lens X \<Longrightarrow> s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  by (transfer, simp)

lift_definition scene_indep :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix "\<bowtie>\<^sub>S" 50)
is "\<lambda> F G. (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. G (F s\<^sub>1 s\<^sub>2) s\<^sub>3 = F (G s\<^sub>1 s\<^sub>3) s\<^sub>2)" .

lemma scene_indep_override:
  "X \<bowtie>\<^sub>S Y = (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on X \<oplus>\<^sub>S s\<^sub>3 on Y = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>3 on Y \<oplus>\<^sub>S s\<^sub>2 on X)"
  by (transfer, auto)

lemma scene_indep_commute:
  "X \<bowtie>\<^sub>S Y \<Longrightarrow> Y \<bowtie>\<^sub>S X"
  by (transfer, auto)

lemma lens_indep_scene:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "(X \<bowtie> Y) \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  using assms
  by (auto, (simp add: scene_indep_override, transfer, simp add: lens_indep_override_def)+)

lemma scene_override_commute_indep:
  assumes "X \<bowtie>\<^sub>S Y"
  shows "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X \<oplus>\<^sub>S S\<^sub>3 on Y = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on Y \<oplus>\<^sub>S S\<^sub>2 on X"
  using assms
  by (transfer, auto)

instantiation scene :: (type) "{zero, one, uminus, plus}"
begin
  lift_definition zero_scene   :: "'s scene" is "\<lambda> x y. x" by (unfold_locales, simp_all)
  lift_definition one_scene    :: "'s scene" is "\<lambda> x y. y" by (unfold_locales, simp_all)
  lift_definition uminus_scene :: "'s scene \<Rightarrow> 's scene" is "\<lambda> F x y. F y x"
    by (unfold_locales, simp_all)
  lift_definition plus_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" 
    is "\<lambda> X Y. if (X \<bowtie>\<^sub>S Y) then (\<lambda> s\<^sub>1 s\<^sub>2. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on X \<oplus>\<^sub>S s\<^sub>2 on Y) else (\<lambda> x y. y)"
    apply (unfold_locales, auto simp add: scene_indep_override scene_override_idem)
    apply (metis (no_types, lifting) Rep_scene mem_Collect_eq overrider.ovr_overshadow_right scene_override.rep_eq)
  done
  instance ..
end

lemma uminus_scene_twice: "- (- (X :: 's scene)) = X"
  by (transfer, simp)

lemma scene_override_id: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on 1 = S\<^sub>2"
  by (transfer, simp)

lemma scene_override_unit: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on 0 = S\<^sub>1"
  by (transfer, simp)

lemma obs_override_commute: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X = S\<^sub>2 \<oplus>\<^sub>S S\<^sub>1 on (- X)"
  by (transfer, simp)

lemma "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> = \<lbrakk>X\<rbrakk>\<^sub>\<sim> + \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  apply (simp add:  lens_indep_scene)
  apply (simp add: scene_indep_def lens_scene_def Rep_scene_inverse)
  apply (transfer)
  oops

lemma scene_plus_commute:
  "X \<bowtie>\<^sub>S Y \<Longrightarrow> X + Y = Y + X"
  by (transfer, simp_all add: scene_indep_commute scene_indep_override)

lemma scene_plus_unit: "(X::'s scene) + 0 = X"
  by (simp add: plus_scene_def scene_indep_override, transfer, auto simp add: scene_override_def Rep_scene_inverse)

instantiation scene :: (type) preorder
begin
  lift_definition less_eq_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" is
  "\<lambda> F G. (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. G (F s\<^sub>1 s\<^sub>2) s\<^sub>3 = G s\<^sub>1 s\<^sub>3)" .
  definition less_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  "less_scene x y = (x \<le> y \<and> \<not> y \<le> x)"
instance
  apply (intro_classes)
     apply (simp add: less_scene_def)
  apply (transfer, simp)
  apply (transfer, simp)
   apply metis
  done
end

lemma zero_scene_least: "0 \<le> (X :: 'a scene)"
  by (transfer, simp_all)

lemma one_scene_greatest: "(X :: 'a scene) \<le> 1"
  by (transfer, simp_all)

lemma "\<lbrakk> vwb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (transfer, auto simp add: lens_override_def sublens_put_put)

(*
abbreviation "ovr_fun R C F \<equiv> \<forall> S\<^sub>1 S\<^sub>2. (F S\<^sub>1 S\<^sub>2, S\<^sub>1) \<in> C \<and> (F S\<^sub>1 S\<^sub>2, S\<^sub>2) \<in> R"

lemma ovr_fun_swap: 
  "ovr_fun R C F \<Longrightarrow> ovr_fun C R (\<lambda> x y. F y x)"
  by (auto)

definition is_override :: "'s rel \<Rightarrow> 's rel \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
"is_override R C F = (ovr_fun R C F \<and> (\<forall> G. ovr_fun R C G \<longrightarrow> G = F))"

lemma is_override_fst [simp]: "Ex (is_override UNIV Id)"
  by (rule_tac x="\<lambda> x y. x" in exI, auto simp add: is_override_def)

lemma is_override_snd [simp]: "Ex (is_override Id UNIV)"
  by (rule_tac x="\<lambda> x y. y" in exI, auto simp add: is_override_def)

typedef 's obs = 
  "{(R :: 's rel, C :: 's rel). equiv UNIV R \<and> equiv UNIV C \<and> R \<inter> C = Id \<and> (\<exists> F. is_override R C F)}"
  by (rule_tac x="(Id, UNIV)" in exI, auto simp add: equiv_def refl_Id refl_on_def sym_def trans_def is_override_def fun_eq_iff)
    
setup_lifting type_definition_obs
  
lift_definition region :: "'s obs \<Rightarrow> ('s \<times> 's) set" is fst .
lift_definition coregion :: "'s obs \<Rightarrow> ('s \<times> 's) set" is snd .
    
lemma state_eq_iff:
  "x = y \<longleftrightarrow> (x, y) \<in> region S \<and> (x, y) \<in> coregion S"
  by (transfer, auto, blast)

lemma state_dist_either:
  "\<lbrakk> (x, y) \<in> region S; x \<noteq> y \<rbrakk> \<Longrightarrow> (x, y) \<notin> coregion S"
  by (meson state_eq_iff)

lemma equiv_region [simp]: "equiv UNIV (region S)"
  by (transfer, auto)

lemma equiv_coregion [simp]: "equiv UNIV (coregion S)"
  by (transfer, auto)

lemma ovr_ex_region_coregion: 
  obtains F where "is_override (region S) (coregion S) F"
  by (transfer, auto)

definition obs_override :: "'a \<Rightarrow> 'a \<Rightarrow> ('a obs) \<Rightarrow> 'a" ("_ \<oplus>\<^sub>O _ on _" [95,0,96] 95) where
[lens_defs]: "S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X = (THE S. (S, S\<^sub>1) \<in> coregion X \<and> (S, S\<^sub>2) \<in> region X)"

lemma obs_override:
  assumes "is_override (region X) (coregion X) F"
  shows "S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X = F S\<^sub>1 S\<^sub>2"
  using assms
  apply (simp add: obs_override_def)
  apply (rule the_equality)
   apply (simp_all add: is_override_def)
   apply (safe)
  apply (metis equiv_coregion equiv_def equiv_region state_eq_iff trans_def)
  done

lemma obs_override_is_override:
  "is_override (region X) (coregion X) (\<lambda> S\<^sub>1 S\<^sub>2. S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X)"
proof -
  obtain F :: "'a obs \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
    f1: "\<And>z. is_override (region z) (coregion z) (F z)"
    by (meson ovr_ex_region_coregion)
  then have "\<And>z. (\<lambda> S\<^sub>1 S\<^sub>2. S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on z) = F z"
    using obs_override by fastforce
then show ?thesis
    using f1 by simp
qed

lemma obs_override_region: "(S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X, S\<^sub>2) \<in> region X"
  by (metis (full_types) is_override_def obs_override ovr_ex_region_coregion)

lemma obs_override_coregion: "(S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X, S\<^sub>1) \<in> coregion X"
  by (metis (full_types) is_override_def obs_override ovr_ex_region_coregion)

lemma obs_override_idem [simp]:
  "s \<oplus>\<^sub>O s on V = s"
  apply (auto simp add: obs_override_def)
  apply (rule the_equality)
  apply (auto)
  apply (meson state_eq_iff)+
  done

lift_definition lens_obs :: "('v \<Longrightarrow> 's) \<Rightarrow> 's obs" ("\<lbrakk>_\<rbrakk>\<^sub>\<sim>") is
"\<lambda> X. if (vwb_lens X) 
         then ({(s\<^sub>1, s\<^sub>2). s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X = s\<^sub>1}, {(s\<^sub>1, s\<^sub>2). s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X = s\<^sub>2})
         else (UNIV, Id)"
  apply (auto intro!:equivI refl_onI symI transI)
  apply (metis lens_override_def lens_override_idem mwb_lens_weak vwb_lens_mwb weak_lens.put_get)
  apply (metis lens_override_def mwb_lens_weak vwb_lens_mwb weak_lens.put_get)
     apply (metis lens_override_def vwb_lens.put_eq)
    apply (metis lens_override_def vwb_lens.put_eq)
  apply (rename_tac X)
   apply (rule_tac x="(\<lambda> S\<^sub>1 S\<^sub>2. lens_override S\<^sub>1 S\<^sub>2 X)" in exI)
   apply (simp add: is_override_def)
  apply (auto)
  apply (simp_all add: lens_override_overshadow sublens_refl)
   apply (metis lens_override_def mwb_lens_axioms_def mwb_lens_def vwb_lens_mwb)
  done

lemma lens_override_is_obs_override:
  "vwb_lens X \<Longrightarrow> S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on X = S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  apply (simp add: lens_override_def obs_override_def, transfer)
  apply (auto)
  apply (rule sym)
  apply (rule the_equality)
  apply (auto simp add: lens_override_def)
  apply (metis mwb_lens.put_put vwb_lens_mwb)
  done

definition obs_indep :: "'a obs \<Rightarrow> 'a obs \<Rightarrow> bool" (infix "\<bowtie>\<^sub>O" 50) where
[lens_defs]: "X \<bowtie>\<^sub>O Y = (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>O s\<^sub>2 on X \<oplus>\<^sub>O s\<^sub>3 on Y = s\<^sub>1 \<oplus>\<^sub>O s\<^sub>3 on Y \<oplus>\<^sub>O s\<^sub>2 on X)"

lemma lens_indep_as_obs_indep:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "X \<bowtie> Y \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>O \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (simp add: assms lens_indep_override_def lens_override_is_obs_override obs_indep_def)

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
  
instantiation obs :: (type) "{zero, one, uminus}"
begin
  lift_definition zero_obs :: "'s obs" is "(UNIV, Id)"by (auto)  
  lift_definition one_obs :: "'s obs" is "(Id, UNIV)" by (auto)
  lift_definition uminus_obs :: "'s obs \<Rightarrow> 's obs" is "\<lambda> (R,C). (C,R)"
    apply (auto)
    apply (simp add: is_override_def)
    apply (rename_tac R C F)
    apply (rule_tac x="(\<lambda> x y . F y x)" in exI)
    apply (simp add: is_override_def fun_eq_iff)
    apply (safe)
    apply meson
    done
instance ..
end

lemma obs_override_id: "S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on 1 = S\<^sub>2"
  unfolding obs_override_def
  by (rule the_equality; transfer, simp)+

lemma obs_override_unit: "S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on 0 = S\<^sub>1"
  unfolding obs_override_def
  by (rule the_equality; transfer, simp)+


lemma obs_override_commute: "S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X = S\<^sub>2 \<oplus>\<^sub>O S\<^sub>1 on (- X)"
  by (smt coregion.rep_eq equiv_coregion equiv_def obs_override_coregion obs_override_region prod.exhaust_sel prod.sel(1) region.rep_eq snd_conv split_conv state_eq_iff symE trans_def uminus_obs.rep_eq)

lemma obs_override_commute_indep:
  assumes "X \<bowtie>\<^sub>O Y"
  shows "S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X \<oplus>\<^sub>O S\<^sub>3 on Y = S\<^sub>1 \<oplus>\<^sub>O S\<^sub>3 on Y \<oplus>\<^sub>O S\<^sub>2 on X"
  using assms
  unfolding obs_override_def obs_indep_def by (auto)

lemma obs_override_overshadow:
  "S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X \<oplus>\<^sub>O S\<^sub>3 on X = S\<^sub>1 \<oplus>\<^sub>O S\<^sub>3 on X"
  by (metis equiv_coregion equiv_def equiv_region obs_override_coregion obs_override_region state_dist_either trans_def)

lemma obs_override_lemma1:
  assumes "X \<bowtie>\<^sub>O Y"
  shows "(S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X \<oplus>\<^sub>O S\<^sub>2 on Y) \<oplus>\<^sub>O S\<^sub>1 on X \<oplus>\<^sub>O S\<^sub>1 on Y = S\<^sub>1"
  using assms
  by (simp add: obs_indep_def obs_override_overshadow)


lemma "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> coregion \<lbrakk>Y\<rbrakk>\<^sub>\<sim> \<subseteq> region \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  apply (transfer, auto)
  by (metis lens_indep_get lens_override_def vwb_lens.put_eq)

lemma "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> region \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> \<subseteq> region \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  apply (transfer, auto)
  apply (metis lens_override_def lens_override_put_right_in lens_plus_ub vwb_lens_wb wb_lens.get_put)
  using plus_vwb_lens by blast

lemma "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> coregion \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<subseteq> coregion \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim>"
  apply (transfer, auto)
  apply (simp add: lens_override_plus)
  using plus_vwb_lens by blast

lemma "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> region \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> = region \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<inter> region \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  apply (transfer, auto)
  apply (metis lens_override_def lens_override_put_right_in lens_plus_ub vwb_lens_wb wb_lens.get_put)
  apply (metis lens_override_def lens_override_plus mwb_lens.put_put vwb_lens_mwb)
  apply (simp add: lens_override_plus)
  using plus_vwb_lens apply blast
  using plus_vwb_lens by blast

lemma "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> coregion \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> = {(s\<^sub>1, s\<^sub>2). (s\<^sub>1 \<oplus>\<^sub>O s\<^sub>2 on \<lbrakk>X\<rbrakk>\<^sub>\<sim>) \<oplus>\<^sub>O s\<^sub>2 on \<lbrakk>Y\<rbrakk>\<^sub>\<sim> = s\<^sub>2}"
  apply (simp add: lens_override_is_obs_override[THEN sym])
  apply (transfer)
  apply (auto)
  apply (simp add: lens_override_plus)
  apply (simp add: lens_override_plus)
  using plus_vwb_lens by blast

lemma plus_override_equiv:
  "X \<bowtie>\<^sub>O Y \<Longrightarrow> equiv UNIV {(s\<^sub>1, s\<^sub>2). s\<^sub>1 \<oplus>\<^sub>O s\<^sub>2 on X \<oplus>\<^sub>O s\<^sub>2 on Y = s\<^sub>2}"
  apply (rule equivI)
    apply (rule refl_onI)
     apply (auto)
   apply (rule symI)
   apply (auto)
  apply (metis obs_override_lemma1)
  apply (smt mem_Collect_eq obs_override_commute_indep obs_override_overshadow prod.simps(2) trans_def)
done

lemma "region \<lbrakk>fst\<^sub>L\<rbrakk>\<^sub>\<sim> \<subseteq> coregion \<lbrakk>snd\<^sub>L\<rbrakk>\<^sub>\<sim>"
  by (transfer, simp add: fst_vwb_lens snd_vwb_lens, auto simp add: lens_defs)
  
instantiation obs :: (type) "{plus}"
begin
  lift_definition plus_obs :: "'s obs \<Rightarrow> 's obs \<Rightarrow> 's obs" is 
  "\<lambda> O\<^sub>1 O\<^sub>2. if (O\<^sub>1 \<bowtie>\<^sub>O O\<^sub>2) 
            then (region O\<^sub>1 \<inter> region O\<^sub>2, {(s\<^sub>1, s\<^sub>2). (s\<^sub>1 \<oplus>\<^sub>O s\<^sub>2 on O\<^sub>1) \<oplus>\<^sub>O s\<^sub>2 on O\<^sub>2 = s\<^sub>2})
            else (UNIV, Id)"
    apply (auto)
    apply (smt IntE IntI equalityI equiv_UNIV equiv_def equiv_region refl_on_def sym_def top.extremum trans_def)
    apply (simp add: plus_override_equiv)
    apply (metis equiv_def equiv_region obs_override_coregion obs_override_region state_dist_either trans_def)
    apply (meson state_eq_iff)
    apply (meson state_eq_iff)
    apply (rename_tac X Y)
        apply (rule_tac x="\<lambda> S\<^sub>1 S\<^sub>2. S\<^sub>1 \<oplus>\<^sub>O S\<^sub>2 on X \<oplus>\<^sub>O S\<^sub>2 on Y" in exI)
    apply (auto simp add: is_override_def)
    apply (simp add: obs_override_lemma1)
    using obs_override_commute_indep obs_override_region apply fastforce
    apply (simp add: obs_override_region)
    apply (metis (no_types, hide_lams) equiv_def equiv_region obs_override_coregion obs_override_lemma1 obs_override_overshadow obs_override_region state_eq_iff trans_def)
    done
     
  instance ..
end

lemma "(0::'a obs) \<le> X"
  by (transfer, auto)
    
lemma "X \<le> (1::'a obs)"    
  by (transfer, auto)
    
lemma fst_lens_inv_snd: "- \<lbrakk>fst\<^sub>L\<rbrakk>\<^sub>\<sim> = \<lbrakk>snd\<^sub>L\<rbrakk>\<^sub>\<sim>"
  by (transfer, auto simp add: fst_vwb_lens snd_vwb_lens, simp_all add: lens_defs)
    
lemma "\<lbrakk>fst\<^sub>L\<rbrakk>\<^sub>\<sim> + \<lbrakk>snd\<^sub>L\<rbrakk>\<^sub>\<sim> = 1"
  apply (transfer)
    
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
*) 
 
end