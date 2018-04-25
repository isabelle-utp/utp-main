section \<open> Scenes \<close>

theory Lens_Obs
  imports Lenses
begin
  
subsection \<open> Overriding Functions \<close>

locale overrider =
  fixes F :: "'s \<Rightarrow> 's \<Rightarrow> 's"
  assumes 
    ovr_overshadow_left: "F (F x y) z = F x z" and
    ovr_overshadow_right: "F x (F y z) = F x z" and
    ovr_idem: "F x x = x"

declare overrider.ovr_overshadow_left [simp]
declare overrider.ovr_overshadow_right [simp]
declare overrider.ovr_idem [simp]

subsection \<open> Scene Type \<close>

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

lift_definition scene_indep :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix "\<bowtie>\<^sub>S" 50)
is "\<lambda> F G. (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. G (F s\<^sub>1 s\<^sub>2) s\<^sub>3 = F (G s\<^sub>1 s\<^sub>3) s\<^sub>2)" .

lift_definition scene_agree :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" (infix "##\<^sub>S" 50)
is "\<lambda> F G. (\<forall> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2 = F (G s\<^sub>1 s\<^sub>2) s\<^sub>2)" .

lemma scene_indep_override:
  "X \<bowtie>\<^sub>S Y = (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on X \<oplus>\<^sub>S s\<^sub>3 on Y = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>3 on Y \<oplus>\<^sub>S s\<^sub>2 on X)"
  by (transfer, auto)

lemma scene_indep_commute:
  "X \<bowtie>\<^sub>S Y \<Longrightarrow> Y \<bowtie>\<^sub>S X"
  by (transfer, auto)

lemma scene_override_commute_indep:
  assumes "X \<bowtie>\<^sub>S Y"
  shows "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X \<oplus>\<^sub>S S\<^sub>3 on Y = S\<^sub>1 \<oplus>\<^sub>S S\<^sub>3 on Y \<oplus>\<^sub>S S\<^sub>2 on X"
  using assms
  by (transfer, auto)

instantiation scene :: (type) "{bot, top, uminus, sup, inf}"
begin
  lift_definition bot_scene    :: "'s scene" is "\<lambda> x y. x" by (unfold_locales, simp_all)
  lift_definition top_scene    :: "'s scene" is "\<lambda> x y. y" by (unfold_locales, simp_all)
  lift_definition uminus_scene :: "'s scene \<Rightarrow> 's scene" is "\<lambda> F x y. F y x"
    by (unfold_locales, simp_all)
  lift_definition sup_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" 
    is "\<lambda> F G. if (\<forall> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2 = F (G s\<^sub>1 s\<^sub>2) s\<^sub>2) then (\<lambda> s\<^sub>1 s\<^sub>2. G (F s\<^sub>1 s\<^sub>2) s\<^sub>2) else (\<lambda> s\<^sub>1 s\<^sub>2. s\<^sub>2)"
    by (unfold_locales, auto, metis overrider.ovr_overshadow_right)
  definition inf_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" where
    "inf_scene X Y = - (sup (- X) (- Y))"
  instance ..
end

abbreviation union_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" (infixl "\<squnion>\<^sub>S" 65)
where "union_scene \<equiv> sup"

abbreviation inter_scene :: "'s scene \<Rightarrow> 's scene \<Rightarrow> 's scene" (infixl "\<sqinter>\<^sub>S" 70)
where "inter_scene \<equiv> inf"

abbreviation top_scene :: "'s scene" ("\<top>\<^sub>S")
where "top_scene \<equiv> top"

abbreviation bot_scene :: "'s scene" ("\<bottom>\<^sub>S")
where "bot_scene \<equiv> bot"

lemma uminus_scene_twice: "- (- (X :: 's scene)) = X"
  by (transfer, simp)

lemma scene_override_id: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on \<top>\<^sub>S = S\<^sub>2"
  by (transfer, simp)

lemma scene_override_unit: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on \<bottom>\<^sub>S = S\<^sub>1"
  by (transfer, simp)

lemma obs_override_commute: "S\<^sub>1 \<oplus>\<^sub>S S\<^sub>2 on X = S\<^sub>2 \<oplus>\<^sub>S S\<^sub>1 on (- X)"
  by (transfer, simp)

lemma scene_union_unit: "X \<squnion>\<^sub>S \<bottom>\<^sub>S = X"
  by (transfer, simp)

lemma scene_union_annhil: "X \<squnion>\<^sub>S \<top>\<^sub>S = \<top>\<^sub>S"
  by (transfer, simp)

lemma scene_union_assoc: 
  assumes "X ##\<^sub>S Y" "X ##\<^sub>S Z" "Y ##\<^sub>S Z"
  shows "X \<squnion>\<^sub>S (Y \<squnion>\<^sub>S Z) = (X \<squnion>\<^sub>S Y) \<squnion>\<^sub>S Z"
  using assms
  by (transfer, auto)

lemma scene_union_idem: "(X :: 's scene) \<squnion>\<^sub>S X = X"
  by (transfer, simp)

lemma scene_union_compl: "X \<squnion>\<^sub>S - X = \<top>\<^sub>S"
  by (transfer, auto)

lemma scene_inter_idem: "(X :: 's scene) \<sqinter>\<^sub>S X = X"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_indep_agree: 
  "X \<bowtie>\<^sub>S Y \<Longrightarrow> X ##\<^sub>S Y"
  by (transfer, auto)

lemma scene_union_commute:
  "X ##\<^sub>S Y \<Longrightarrow> X \<squnion>\<^sub>S Y = Y \<squnion>\<^sub>S X"
  by (transfer, auto)
  
lemma scene_inter_compl: "X \<sqinter>\<^sub>S - X = \<bottom>\<^sub>S"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_demorgan1: "-(X \<squnion>\<^sub>S Y) = -X \<sqinter>\<^sub>S -Y"
  by (simp add: inf_scene_def, transfer, auto)

lemma scene_demorgan2: "-(X \<sqinter>\<^sub>S Y) = -X \<squnion>\<^sub>S -Y"
  by (simp add: inf_scene_def, transfer, auto)


instantiation scene :: (type) order
begin
  -- {* $X$ is a subscene of $Y$ provided that overriding with first $Y$ and then $X$ can
        be rewritten using the complement of $X$. *}
  definition less_eq_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  "less_eq_scene X Y = (\<forall> s\<^sub>1 s\<^sub>2 s\<^sub>3. s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on Y \<oplus>\<^sub>S s\<^sub>3 on X = s\<^sub>1 \<oplus>\<^sub>S (s\<^sub>3 \<oplus>\<^sub>S s\<^sub>2 on (- X)) on Y)"
  definition less_scene :: "'a scene \<Rightarrow> 'a scene \<Rightarrow> bool" where
  "less_scene x y = (x \<le> y \<and> \<not> y \<le> x)"
instance
  apply (intro_classes)
  apply (simp_all add: less_scene_def less_eq_scene_def)
  apply (transfer, simp)
  apply (transfer, simp)
   apply (metis (no_types, hide_lams) overrider.ovr_idem)
  apply (transfer, auto)
  apply (rule ext)
  apply (rule ext)
  apply (metis (no_types, hide_lams) overrider_def)
  done
end

lemma subscene_eliminate:
  "X \<le> Y \<Longrightarrow> s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on X \<oplus>\<^sub>S s\<^sub>3 on Y = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>3 on Y"
  by (metis less_eq_scene_def obs_override_overshadow_left scene_override_idem)
    
lemma scene_bot_least: "\<bottom>\<^sub>S \<le> X"
  unfolding less_eq_scene_def by (transfer, auto)

lemma scene_top_greatest: "(X :: 'a scene) \<le> \<top>\<^sub>S"
  unfolding less_eq_scene_def by (transfer, auto)

subsection \<open> Linking Scenes and Lenses \<close>

lift_definition lens_scene :: "('v \<Longrightarrow> 's) \<Rightarrow> 's scene" ("\<lbrakk>_\<rbrakk>\<^sub>\<sim>") is
"\<lambda> X. if (vwb_lens X) then (\<lambda> s\<^sub>1 s\<^sub>2. s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X) else (\<lambda> s\<^sub>1 s\<^sub>2. s\<^sub>1)"
  by (unfold_locales, auto simp add: lens_override_def)

lemma zero_lens_scene: "\<lbrakk>0\<^sub>L\<rbrakk>\<^sub>\<sim> = \<bottom>\<^sub>S"
  by (transfer, simp)

lemma one_lens_scene: "\<lbrakk>1\<^sub>L\<rbrakk>\<^sub>\<sim> = \<top>\<^sub>S"
  by (transfer, simp)

lemma lens_scene_override: 
  "vwb_lens X \<Longrightarrow> s\<^sub>1 \<oplus>\<^sub>L s\<^sub>2 on X = s\<^sub>1 \<oplus>\<^sub>S s\<^sub>2 on \<lbrakk>X\<rbrakk>\<^sub>\<sim>"
  by (transfer, simp)

lemma lens_indep_scene:
  assumes "vwb_lens X" "vwb_lens Y"
  shows "(X \<bowtie> Y) \<longleftrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<bowtie>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  using assms
  by (auto, (simp add: scene_indep_override, transfer, simp add: lens_indep_override_def)+)

lemma lens_plus_scene:
  "\<lbrakk> vwb_lens X; vwb_lens Y; X \<bowtie> Y \<rbrakk> \<Longrightarrow> \<lbrakk>X +\<^sub>L Y\<rbrakk>\<^sub>\<sim> = \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<squnion>\<^sub>S \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  by (transfer, auto simp add: lens_override_plus lens_indep_override_def lens_indep_overrideI plus_vwb_lens)

lemma sublens_implies_subscene:
  "\<lbrakk> vwb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim>"
  apply (auto simp add: less_eq_scene_def sublens_def)
  apply (rename_tac Z)
  apply (transfer, auto)
  apply (metis lens_comp_lb lens_override_def lens_override_put_right_in)
  done

lemma "\<lbrakk> vwb_lens Y; \<lbrakk>X\<rbrakk>\<^sub>\<sim> \<le> \<lbrakk>Y\<rbrakk>\<^sub>\<sim> \<rbrakk> \<Longrightarrow> X \<subseteq>\<^sub>L Y"
  oops
 
end