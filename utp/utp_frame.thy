section \<open> Relational Frames \<close>

theory utp_frame
  imports utp_theory
begin

subsection \<open> Frame Constructs \<close>

text \<open> Alphabet extension and restriction add additional variables by the given lens in both
  their primed and unprimed versions. \<close>
  
definition rel_aext :: "'\<beta> hrel \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" 
where [upred_defs]: "rel_aext P a = P \<oplus>\<^sub>p (a \<times>\<^sub>L a)"

definition rel_ares :: "'\<alpha> hrel \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> hrel" 
  where [upred_defs]: "rel_ares P a = (P \<restriction>\<^sub>p (a \<times> a))"

text \<open> We next describe frames and antiframes with the help of lenses. A frame states that $P$
  defines how variables in $a$ changed, and all those outside of $a$ remain the same. An
  antiframe describes the converse: all variables outside $a$ are specified by $P$, and all those in
  remain the same. For more information please see \cite{Morgan90a}.\<close>

definition frame :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "frame a P = (P \<and> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v \<oplus> $\<^bold>v\<acute> on &a)"
  
definition antiframe :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "antiframe a P = (P \<and> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v\<acute> \<oplus> $\<^bold>v on &a)"

text \<open> The following operator states that a relation only modifies variables within @{term a}. \<close>

abbreviation modifies :: "'s hrel \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> bool"  where
"modifies P a \<equiv> P is frame a"

abbreviation not_modifies :: "'s hrel \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> bool" where
"not_modifies P a \<equiv> P is antiframe a"

text \<open> We also describe variable restriction, which is an extension of @{const antiframe}. It 
  effectively forbids a relation from accessing a variable by assigning it arbitrary values, and
  copying its original value. \<close>

definition rrestr :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[upred_defs]: "rrestr x P = (\<Sqinter> (v, v') \<bullet> antiframe x (P\<lbrakk>\<guillemotleft>v\<guillemotright>,\<guillemotleft>v'\<guillemotright>/$x,$x\<acute>\<rbrakk>))"

text \<open> If restricting a variable has no effect, then it is neither read nor written. \<close>

abbreviation "not_uses P a \<equiv> P is rrestr a"

text \<open> Frame extension combines alphabet extension with the frame operator to both add additional 
  variables and then frame those. \<close>

definition rel_frext :: "('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<beta> hrel \<Rightarrow> '\<alpha> hrel"  where
[upred_defs]: "rel_frext a P = frame a (rel_aext P a)"

text \<open> The nameset operator can be used to hide a portion of the after-state that lies outside
  the lens $a$. It can be useful to partition a relation's variables in order to conjoin it
  with another relation. \<close>

definition nameset :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "nameset a P = (P \<restriction>\<^sub>v {$\<^bold>v,$a\<acute>})" 

text \<open> The modify and freeze operators below are analogous to the frame and antiframe, but they
  discard updates to variables outside (inside) the frame, rather than requiring that they do
  not change. \<close>

definition modify :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "modify a P = (\<^bold>\<exists> st' \<bullet> P\<lbrakk>\<guillemotleft>st'\<guillemotright>/$\<^bold>v\<acute>\<rbrakk> \<and> $\<^bold>v\<acute> =\<^sub>u $\<^bold>v \<oplus> \<guillemotleft>st'\<guillemotright> on &a)"

definition freeze :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "freeze a P = (\<^bold>\<exists> st' \<bullet> P\<lbrakk>\<guillemotleft>st'\<guillemotright>/$\<^bold>v\<acute>\<rbrakk> \<and> $\<^bold>v\<acute> =\<^sub>u \<guillemotleft>st'\<guillemotright> \<oplus> $\<^bold>v on &a)"

syntax
  \<comment> \<open> Frame \<close>
  "_frame"          :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [99,0] 100)
  \<comment> \<open> Antiframe \<close>
  "_antiframe"      :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:\<lbrakk>_\<rbrakk>" [79,0] 80)
  \<comment> \<open> Relational Alphabet Extension \<close>
  "_rel_aext"  :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\<oplus>\<^sub>r" 90)
  \<comment> \<open> Relational Alphabet Restriction \<close>
  "_rel_ares"  :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\<restriction>\<^sub>r" 90)
  \<comment> \<open> Frame Extension \<close>
  "_rel_frext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sup>+" [99,0] 100)
  \<comment> \<open> Nameset \<close>
  "_nameset"        :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>n\<^bold>s _ \<bullet> _" [0,10] 10)
  \<comment> \<open> Modify \<close>
  "_modify"         :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>m\<^bold>d\<^bold>f _ \<bullet> _" [0,10] 10)
  \<comment> \<open> Freeze \<close>
  "_freeze"         :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>f\<^bold>r\<^bold>z _ \<bullet> _" [0,10] 10)
  \<comment> \<open> Modifies Predicate \<close>
  "_modifies"     :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infix "mods" 30)
  \<comment> \<open> Not Modifies Predicate \<close>
  "_not_modifies" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infix "nmods" 30)
  \<comment> \<open> Not Uses Predicate \<close>
  "_not_uses"     :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infix "nuses" 30)

translations
  "_frame x P" => "CONST frame x P"
  "_frame (_salphaset (_salphamk x)) P" <= "CONST frame x P"
  "_antiframe x P" => "CONST antiframe x P"
  "_antiframe (_salphaset (_salphamk x)) P" <= "CONST antiframe x P"
  "_nameset x P" == "CONST nameset x P"
  "_modify x P" == "CONST modify x P"
  "_freeze x P" == "CONST freeze x P"
  "_rel_aext P a" == "CONST rel_aext P a"
  "_rel_ares P a" == "CONST rel_ares P a"
  "_rel_frext a P" == "CONST rel_frext a P"
  "_modifies P x" == "CONST modifies P x"
  "_not_modifies P x" == "CONST not_modifies P x"
  "_not_uses P x" == "CONST not_uses P x"

subsection \<open> Unrestriction Laws \<close>

lemma unrest_in_rel_aext [unrest]: "x \<bowtie> y \<Longrightarrow> $y \<sharp> P \<oplus>\<^sub>r x"
  by (simp add: rel_aext_def unrest_aext_indep)

lemma unrest_out_rel_aext [unrest]: "x \<bowtie> y \<Longrightarrow> $y\<acute> \<sharp> P \<oplus>\<^sub>r x"
  by (simp add: rel_aext_def unrest_aext_indep)

subsection \<open> Alphabet Laws \<close>

lemma rel_aext_false [alpha]:
  "false \<oplus>\<^sub>r a = false"
  by (pred_auto)

lemma rel_aext_seq [alpha]:
  "weak_lens a \<Longrightarrow> (P ;; Q) \<oplus>\<^sub>r a = (P \<oplus>\<^sub>r a ;; Q \<oplus>\<^sub>r a)"
  apply (rel_auto)
  apply (rename_tac aa b y)
  apply (rule_tac x="create\<^bsub>a\<^esub> y" in exI)
  apply (simp)
  done

lemma rel_aext_cond [alpha]:
  "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<oplus>\<^sub>r a = (P \<oplus>\<^sub>r a \<triangleleft> b \<oplus>\<^sub>p a \<triangleright>\<^sub>r Q \<oplus>\<^sub>r a)"
  by (rel_auto)

lemma rel_ares_aext [alpha]: 
  "vwb_lens a \<Longrightarrow> (P \<oplus>\<^sub>r a) \<restriction>\<^sub>r a = P"
  by (rel_auto)

lemma rel_aext_ares [alpha]:
  "{$a, $a\<acute>} \<natural> P \<Longrightarrow> P \<restriction>\<^sub>r a \<oplus>\<^sub>r a = P"
  by (rel_auto)

lemma rel_aext_uses [unrest]:
  "vwb_lens a \<Longrightarrow> {$a, $a\<acute>} \<natural> (P \<oplus>\<^sub>r a)"
  by (rel_auto)    

lemma Pre_conj_rel_aext [prepost]:
  "\<lbrakk> vwb_lens a; vwb_lens b; a \<bowtie> b \<rbrakk> \<Longrightarrow> Pre(P \<oplus>\<^sub>r a \<and> Q \<oplus>\<^sub>r b) = (Pre(P \<oplus>\<^sub>r a) \<and> Pre(Q \<oplus>\<^sub>r b))"
  by (rel_auto, metis (no_types, lifting) lens_indep_def mwb_lens_def vwb_lens_mwb weak_lens_def)

subsection \<open> Frame and Antiframe Laws \<close>

named_theorems frame

lemma frame_all [frame]: "\<Sigma>:[P] = P"
  by (rel_auto)

lemma frame_none [frame]: 
  "\<emptyset>:[P] = (P \<and> II)"
  by (rel_auto)

lemma frame_commute:
  assumes "$y \<sharp> P" "$y\<acute> \<sharp> P" "$x \<sharp> Q" "$x\<acute> \<sharp> Q" "x \<bowtie> y" 
  shows "x:[P] ;; y:[Q] = y:[Q] ;; x:[P]"
  apply (insert assms)
  apply (rel_auto)
   apply (rename_tac s s' s\<^sub>0)
   apply (subgoal_tac "(s \<oplus>\<^sub>L s' on y) \<oplus>\<^sub>L s\<^sub>0 on x = s\<^sub>0 \<oplus>\<^sub>L s' on y")
    apply (metis lens_indep_get lens_indep_sym lens_override_def)
   apply (simp add: lens_indep.lens_put_comm lens_override_def)
  apply (rename_tac s s' s\<^sub>0)
  apply (subgoal_tac "put\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> s (get\<^bsub>x\<^esub> (put\<^bsub>x\<^esub> s\<^sub>0 (get\<^bsub>x\<^esub> s')))) (get\<^bsub>y\<^esub> (put\<^bsub>y\<^esub> s (get\<^bsub>y\<^esub> s\<^sub>0))) 
                      = put\<^bsub>x\<^esub> s\<^sub>0 (get\<^bsub>x\<^esub> s')")
   apply (metis lens_indep_get lens_indep_sym)
  apply (metis lens_indep.lens_put_comm)
  done
 
lemma frame_miracle [simp]:
  "x:[false] = false"
  by (rel_auto)

lemma frame_skip [simp]:
  "vwb_lens x \<Longrightarrow> x:[II] = II"
  by (rel_auto)
    
lemma frame_assign_in [frame]:
  "\<lbrakk> vwb_lens a; x \<subseteq>\<^sub>L a \<rbrakk> \<Longrightarrow> a:[x := v] = x := v"
  by (rel_auto, simp_all add: lens_get_put_quasi_commute lens_put_of_quotient)

lemma frame_conj_true [frame]:
  "\<lbrakk> {$x,$x\<acute>} \<natural> P; vwb_lens x \<rbrakk> \<Longrightarrow> (P \<and> x:[true]) = x:[P]"
  by (rel_auto)
    
lemma frame_is_assign [frame]:
  "vwb_lens x \<Longrightarrow> x:[$x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub><] = x := v"
  by (rel_auto)
    
lemma frame_seq [frame]:
  "\<lbrakk> vwb_lens x; {$x,$x\<acute>} \<natural> P; {$x,$x\<acute>} \<natural> Q \<rbrakk> \<Longrightarrow> x:[P ;; Q] = x:[P] ;; x:[Q]"
  apply (rel_auto)
   apply (metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens_def weak_lens.put_get)
  apply (metis mwb_lens.put_put vwb_lens_mwb)
  done

lemma frame_assign_commute_unrest:
  assumes "vwb_lens x" "x \<bowtie> a" "a \<sharp> v" "$x \<sharp> P" "$x\<acute> \<sharp> P"
  shows "x := v ;; a:[P] = a:[P] ;; x := v"
  using assms
  apply (rel_auto)
  apply (metis (no_types, lifting) lens_indep.lens_put_irr2 lens_indep_comm)
  apply (metis (no_types, opaque_lifting) lens_indep_def)
  done

lemma frame_to_antiframe [frame]:
  "\<lbrakk> x \<bowtie> y; x +\<^sub>L y = 1\<^sub>L \<rbrakk> \<Longrightarrow> x:[P] = y:\<lbrakk>P\<rbrakk>"
  by (rel_auto, metis lens_indep_def, metis lens_indep_def surj_pair)

lemma rel_frext_miracle [frame]: 
  "a:[false]\<^sup>+ = false"
  by (rel_auto)
    
lemma rel_frext_skip [frame]: 
  "vwb_lens a \<Longrightarrow> a:[II]\<^sup>+ = II"
  by (rel_auto)

lemma rel_frext_seq [frame]:
  "vwb_lens a \<Longrightarrow> a:[P ;; Q]\<^sup>+ = (a:[P]\<^sup>+ ;; a:[Q]\<^sup>+)"
  apply (rel_auto)
   apply (rename_tac s s' s\<^sub>0)
   apply (rule_tac x="put\<^bsub>a\<^esub> s s\<^sub>0" in exI)
   apply (auto)
  apply (metis mwb_lens.put_put vwb_lens_mwb)
  done

lemma rel_frext_assigns [frame]:
  "vwb_lens a \<Longrightarrow> a:[\<langle>\<sigma>\<rangle>\<^sub>a]\<^sup>+ = \<langle>\<sigma> \<oplus>\<^sub>s a\<rangle>\<^sub>a"
  by (rel_auto)

lemma rel_frext_rcond [frame]:
  "a:[P \<triangleleft> b \<triangleright>\<^sub>r Q]\<^sup>+ = (a:[P]\<^sup>+ \<triangleleft> b \<oplus>\<^sub>p a \<triangleright>\<^sub>r a:[Q]\<^sup>+)"
  by (rel_auto)

lemma rel_frext_commute: 
  "x \<bowtie> y \<Longrightarrow> x:[P]\<^sup>+ ;; y:[Q]\<^sup>+ = y:[Q]\<^sup>+ ;; x:[P]\<^sup>+"
  apply (rel_auto)
   apply (rename_tac a c b)
   apply (subgoal_tac "\<And>b a. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b a) = get\<^bsub>y\<^esub> b")
    apply (metis (no_types, opaque_lifting) lens_indep_comm lens_indep_get)
   apply (simp add: lens_indep.lens_put_irr2)
  apply (subgoal_tac "\<And>b c. get\<^bsub>x\<^esub> (put\<^bsub>y\<^esub> b c) = get\<^bsub>x\<^esub> b")
   apply (subgoal_tac "\<And>b a. get\<^bsub>y\<^esub> (put\<^bsub>x\<^esub> b a) = get\<^bsub>y\<^esub> b")
    apply (metis (mono_tags, lifting) lens_indep_comm)
   apply (simp_all add: lens_indep.lens_put_irr2)    
  done
    
lemma antiframe_disj [frame]: "(x:\<lbrakk>P\<rbrakk> \<or> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<or> Q\<rbrakk>"
  by (rel_auto)

lemma antiframe_seq [frame]:
  "\<lbrakk> vwb_lens x; $x\<acute> \<sharp> P; $x \<sharp> Q \<rbrakk>  \<Longrightarrow> (x:\<lbrakk>P\<rbrakk> ;; x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P ;; Q\<rbrakk>"
  apply (rel_auto)
   apply (metis vwb_lens_wb wb_lens_def weak_lens.put_get)
  apply (metis vwb_lens_wb wb_lens.put_twice wb_lens_def weak_lens.put_get)
  done

lemma antiframe_copy_assign:
  "vwb_lens x \<Longrightarrow> (x := \<guillemotleft>v\<guillemotright> ;; x:\<lbrakk>P\<rbrakk> ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> ;; x:\<lbrakk>P\<rbrakk>)"
  by rel_auto

  
lemma nameset_skip: "vwb_lens x \<Longrightarrow> (\<^bold>n\<^bold>s x \<bullet> II) = II\<^bsub>x\<^esub>"
  by (rel_auto, meson vwb_lens_wb wb_lens.get_put)
    
lemma nameset_skip_ra: "vwb_lens x \<Longrightarrow> (\<^bold>n\<^bold>s x \<bullet> II\<^bsub>x\<^esub>) = II\<^bsub>x\<^esub>"
  by (rel_auto)
    
declare sublens_def [lens_defs]

subsection \<open> Modification Laws \<close>

lemma mods_skip [closure]:
  "vwb_lens a \<Longrightarrow> II mods a"
  by (rel_auto)

lemma mods_assigns [closure]:
  "\<lbrakk> mwb_lens a; \<sigma> \<rhd>\<^sub>s a = \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a mods a"
  by (rel_auto)

lemma mods_disj [closure]:
  assumes "P mods a" "Q mods a"
  shows "(P \<or> Q) mods a"
proof -
  have "(a:[P] \<or> a:[Q]) mods a"
    by (rel_auto)
  thus ?thesis by (simp add: Healthy_if assms)
qed

lemma mods_cond [closure]:
  assumes "P mods a" "Q mods a"
  shows "P \<triangleleft> b \<triangleright>\<^sub>r Q mods a"
proof -
  have "a:[P] \<triangleleft> b \<triangleright>\<^sub>r a:[Q] mods a"
    by (rel_auto)
  thus ?thesis by (simp add: Healthy_if assms)
qed

lemma mods_seq [closure]:
  assumes "mwb_lens a" "P mods a" "Q mods a"
  shows "P ;; Q mods a"
proof -
  from assms(1) have "a:[P] ;; a:[Q] mods a"
    by (rel_auto, metis mwb_lens.put_put)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma nmods_copy_assign:
  "\<lbrakk> vwb_lens x; P nmods x \<rbrakk> \<Longrightarrow> (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> ;; P)"
  by (metis Healthy_if antiframe_copy_assign)

lemma nmods_intro:
  "\<lbrakk> vwb_lens x; \<And> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> ;; P) \<rbrakk> \<Longrightarrow> P nmods x"
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put wb_lens.put_twice)

lemma nmods_iff_copy_assign:
  assumes "vwb_lens x"
  shows "P nmods x \<longleftrightarrow> (\<forall> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> ;; P))"
proof
  show "(\<forall> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> ;; P)) \<Longrightarrow> P nmods x"
    by (simp add: assms nmods_intro)
  show "P nmods x \<Longrightarrow> (\<forall> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright> ;; P))"
    by (simp add: assms nmods_copy_assign)
qed

lemma nmods_zero [closure]: "P nmods \<emptyset>"
  by (rel_auto)

lemma nmods_plus [closure]: "\<lbrakk> P nmods a; P nmods b \<rbrakk> \<Longrightarrow> P nmods (a ; b)"
  by (rel_auto, metis)

lemma nmods_skip [closure]: "vwb_lens a \<Longrightarrow> II nmods a" 
  by rel_auto

lemma nmods_seq [closure]:
  assumes "weak_lens a" "P nmods a" "Q nmods a"
  shows "P ;; Q nmods a"
  using assms by (rel_auto', metis weak_lens.put_get)

lemma nmods_cond [closure]:
  assumes "P nmods a" "Q nmods a"
  shows "P \<triangleleft> b \<triangleright>\<^sub>r Q nmods a"
  using assms by (rel_auto')

lemma nmods_gcmd [closure]: "P nmods a \<Longrightarrow> (b \<longrightarrow>\<^sub>r P) nmods a"
  by (rel_auto)

lemma nmods_choice [closure]: "\<lbrakk> P nmods a; Q nmods a \<rbrakk> \<Longrightarrow> P \<sqinter> Q nmods a"
  by (rel_auto)

lemma nmods_assigns [closure]:
  "\<lbrakk> vwb_lens x; x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a nmods x"
  by (rel_auto, metis vwb_lens.put_eq)

lemma nmods_assign [closure]: "\<lbrakk> vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> x := v nmods y"
  by (rel_auto, metis lens_indep.lens_put_comm vwb_lens_wb wb_lens.get_put)

lemma nmods_frext_comp [closure]:"\<lbrakk> vwb_lens a; vwb_lens x; P nmods x \<rbrakk> \<Longrightarrow> a:[P]\<^sup>+ nmods &a:x"
  by (rel_auto, metis lens_override_def lens_override_idem)

lemma nmods_frext_indep [closure]:"\<lbrakk> vwb_lens a; vwb_lens x; x \<bowtie> a \<rbrakk> \<Longrightarrow> a:[P]\<^sup>+ nmods x"
  by (rel_auto, metis lens_indep_get lens_override_def lens_override_idem)

lemma nmods_UINF [closure]: "\<lbrakk> \<And> v. P v nmods x \<rbrakk> \<Longrightarrow> (\<Sqinter> v \<bullet> P v) nmods x"
  by (rel_auto)

lemma nmods_guard [closure]: "vwb_lens x \<Longrightarrow> ?[p] nmods x"
  by (rel_auto)

lemma nmods_miracle [closure]: "false nmods x"
  by rel_auto

lemma nmods_disj [closure]: "\<lbrakk> P nmods a; Q nmods a \<rbrakk> \<Longrightarrow> (P \<or> Q) nmods a"
  by (rel_auto)

no_utp_lift frame antiframe modify freeze

subsection \<open> Modify and Freeze Laws \<close>

text \<open> Assignments made to modify variables are retained, but lost for frozen ones. \<close>

lemma modify_assigns: "(\<^bold>m\<^bold>d\<^bold>f a \<bullet> \<langle>\<sigma>\<rangle>\<^sub>a) = \<langle>\<sigma> \<rhd>\<^sub>s a\<rangle>\<^sub>a"
  by (rel_auto)

lemma modify_assign:
  "vwb_lens x \<Longrightarrow> (\<^bold>m\<^bold>d\<^bold>f x \<bullet> x := v) = x := v"
  by (simp add: modify_assigns usubst)

lemma freeze_assigns: "(\<^bold>f\<^bold>r\<^bold>z a \<bullet> \<langle>\<sigma>\<rangle>\<^sub>a) = \<langle>\<sigma> -\<^sub>s a\<rangle>\<^sub>a"
  by (rel_auto)

lemma freeze_assign:
  "vwb_lens x \<Longrightarrow> (\<^bold>f\<^bold>r\<^bold>z x \<bullet> x := v) = II"
  by (simp add: freeze_assigns usubst skip_r_def)

lemma frame_modify_same_fixpoints:
  "mwb_lens a \<Longrightarrow> P mods a \<longleftrightarrow> P is modify a"
  by (rel_simp, metis mwb_lens_weak weak_lens_def)

lemma antiframe_freeze_same_fixpoints:
  "mwb_lens a \<Longrightarrow> P is antiframe a \<longleftrightarrow> P is freeze a"
  by (rel_simp, metis mwb_lens.put_put)

subsection \<open> Variable Use Laws \<close>

lemma rrestr_Idempotent [closure]: "vwb_lens x \<Longrightarrow> Idempotent (rrestr x)"
  unfolding Idempotent_def by (rel_auto)

lemma hide_Continuous [closure]: "Continuous (rrestr x)"
  by (rel_auto)

lemma hide_nmods [closure]: "rrestr x P nmods x"
  by (rel_auto)

lemma nuses_implies_nmods [closure]: "P nuses x \<Longrightarrow> P nmods x"
  by (metis Healthy_if hide_nmods)

lemma nuses_assign_commute:
  assumes "mwb_lens x" "P nuses x"
  shows "x := \<guillemotleft>v\<guillemotright> ;; P = P ;; x := \<guillemotleft>v\<guillemotright>"
proof -
  from assms(1) have "x := \<guillemotleft>v\<guillemotright> ;; rrestr x P = rrestr x P ;; x := \<guillemotleft>v\<guillemotright>"
    by (rel_auto, metis mwb_lens.put_put, metis)
  thus ?thesis
    by (simp add: Healthy_if assms(2))
qed

lemma nuses_iff_assign_commute:
  assumes "vwb_lens x"
  shows "P nuses x \<longleftrightarrow> (\<forall> v. x := \<guillemotleft>v\<guillemotright> ;; P = P ;; x := \<guillemotleft>v\<guillemotright>)"
proof
  assume "P nuses x"
  thus "\<forall>v. x := \<guillemotleft>v\<guillemotright> ;; P = P ;; x := \<guillemotleft>v\<guillemotright>"
    by (simp add: assms nuses_assign_commute)
next
  assume "\<forall>v. x := \<guillemotleft>v\<guillemotright> ;; P = P ;; x := \<guillemotleft>v\<guillemotright>"
  thus "P nuses x"
    by (rel_simp, metis (full_types) assms mwb_lens.put_put vwb_lens_mwb vwb_lens_wb 
        wb_lens.source_stability wb_lens_def weak_lens.put_get)
qed

lemma nuses_nmods_intro:
  assumes "vwb_lens x" "P nmods x" "(\<forall> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (P ;; x := \<guillemotleft>v\<guillemotright>))"
  shows "P nuses x"
  by (metis assms(1) assms(2) assms(3) nmods_copy_assign nuses_iff_assign_commute)

lemma nuses_zero [closure]: "P nuses \<emptyset>"
  by (rel_auto)

lemma rrestr_twice: "\<lbrakk> vwb_lens a; vwb_lens b; a \<bowtie> b \<rbrakk> \<Longrightarrow> rrestr a (rrestr b P) = rrestr (a +\<^sub>L b) P"
  by (rel_auto, auto simp add: lens_indep_vwb_iff, (metis vwb_lens.put_eq)+)

lemma nuses_plus [closure]: 
  assumes "vwb_lens a" "vwb_lens b" "a \<bowtie> b" "P nuses a" "P nuses b" 
  shows "P nuses (a ; b)"
  by (metis Healthy_def assms rrestr_twice)

lemma nuses_iff_nmods_and_reduce:
  assumes "vwb_lens x"
  shows "P nuses x \<longleftrightarrow> ((P nmods x) \<and>(\<forall> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (P ;; x := \<guillemotleft>v\<guillemotright>)))"
proof 
  have "P nuses x \<Longrightarrow> (\<forall> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (P ;; x := \<guillemotleft>v\<guillemotright>))"
    by (simp add: assms nmods_copy_assign nuses_assign_commute nuses_implies_nmods)
  thus "P nuses x \<Longrightarrow> (P nmods x) \<and> (\<forall> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (P ;; x := \<guillemotleft>v\<guillemotright>))"
    by (simp add: closure)
  show "((P nmods x) \<and> (\<forall> v. (x := \<guillemotleft>v\<guillemotright> ;; P ;; x := \<guillemotleft>v\<guillemotright>) = (P ;; x := \<guillemotleft>v\<guillemotright>))) \<Longrightarrow> P nuses x"
    using assms nuses_nmods_intro by blast
qed

lemma nuses_false [closure]: "false nuses x" 
  by rel_auto

lemma nuses_skip [closure]: "vwb_lens x \<Longrightarrow> II nuses x"
  by (rel_auto, metis vwb_lens.put_eq)

lemma nuses_assigns [closure]:
  "\<lbrakk> vwb_lens x; x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>a nuses x"
  apply (rel_auto)
  apply (metis mwb_lens_def vwb_lens.put_eq vwb_lens_mwb weak_lens.put_get)
  apply (metis vwb_lens_wb wb_lens.get_put)
  done

lemma nuses_assign:
  "\<lbrakk> vwb_lens x; x \<bowtie> y; x \<sharp> e \<rbrakk> \<Longrightarrow> y := e nuses x"
  by (simp add: closure unrest)

lemma nuses_nd_assign [closure]:
  "\<lbrakk> vwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> y := * nuses x"
  by (simp add: nd_assign_def closure unrest)

lemma nuses_seq [closure]:
  assumes "mwb_lens x" "P nuses x" "Q nuses x"
  shows "P ;; Q nuses x"
proof -
  have "(rrestr x P ;; rrestr x Q) is rrestr x"
    apply (rel_auto)
    apply (metis (no_types, opaque_lifting) assms(1) mwb_lens.put_put mwb_lens_def weak_lens.put_get)
    using assms(1) apply auto
    apply blast
    apply (metis mwb_lens_def weak_lens.put_get)  
    done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
  
lemma nuses_choice [closure]:
  "\<lbrakk> P nuses x; Q nuses x \<rbrakk> \<Longrightarrow> (P \<sqinter> Q) nuses x"
  by (simp add: Healthy_def Continuous_choice_dist closure)

lemma nuses_guard [closure]:
  assumes "vwb_lens x" "x \<sharp> b"
  shows "?[b] nuses x"
  using assms
  by (rel_auto)
     (metis mwb_lens_def vwb_lens.source_determination vwb_lens_mwb weak_lens.put_get)

lemma nuses_cond [closure]:
  assumes "vwb_lens x" "x \<sharp> b" "P nuses x" "Q nuses x"
  shows "(P \<triangleleft> b \<triangleright>\<^sub>r Q) nuses x"
  using assms
  by (simp add: rcond_rassume_expand closure unrest)

lemma nuses_power [closure]:
  "\<lbrakk> vwb_lens x; P nuses x \<rbrakk> \<Longrightarrow> P\<^bold>^n nuses x"
  by (induct n, simp_all add: closure upred_semiring.power_Suc) 

lemma nuses_star [closure]:
  "\<lbrakk> vwb_lens x; P nuses x \<rbrakk> \<Longrightarrow> P\<^sup>\<star> nuses x"
  unfolding ustar_def by (simp add: closure)

lemma nuses_while [closure]:
  "\<lbrakk> vwb_lens x; x \<sharp> b; P nuses x \<rbrakk> \<Longrightarrow> (while b do P od) nuses x"
  by (simp add: while_star_form closure unrest)

subsection \<open> UTP Theories \<close>

text \<open> A UTP theory that characterises relations that only modify a region of the state space 
  characterised by a lens @{term a}. \<close>

theorem frame_theory: 
  assumes vwb_frame: "vwb_lens a"
  shows "utp_theory_cont_unital (frame a) II"
proof
  fix P Q
  show "a:[a:[P]] = a:[P]" 
    by rel_auto
  show "P mods a \<Longrightarrow> Q mods a \<Longrightarrow> P ;; Q mods a"
    using vwb_frame mods_seq vwb_lens_mwb by blast 
  show "Continuous (frame a)"
    by (rel_auto)
  show "II mods a"
    by (simp add: vwb_frame mods_skip)
qed (simp_all)

theorem antiframe_theory: 
  assumes vwb_frame: "vwb_lens a"
  shows "utp_theory_cont_unital (antiframe a) II"
proof
  fix P Q
  show "a:\<lbrakk>a:\<lbrakk>P\<rbrakk>\<rbrakk> = a:\<lbrakk>P\<rbrakk>" 
    by rel_auto
  show "P nmods a \<Longrightarrow> Q nmods a \<Longrightarrow> P ;; Q nmods a"
    by (simp add: nmods_seq vwb_frame)
  show "Continuous (antiframe a)"
    by (rel_auto)
  show "II nmods a"
    by (simp add: nmods_skip vwb_frame)
qed (simp_all)

theorem rrestr_theory: 
  assumes vwb_frame: "vwb_lens a"
  shows "utp_theory_cont_unital (rrestr a) II"
proof
  fix P Q
  show "rrestr a (rrestr a P) = rrestr a P"
    using Idempotent_def rrestr_Idempotent vwb_frame by blast
  show "P nuses a \<Longrightarrow> Q nuses a \<Longrightarrow> P ;; Q nuses a"
    by (simp add: nuses_seq vwb_frame)
  show "Continuous (rrestr a)"
    by (simp add: hide_Continuous)
  show "II nuses a"
    by (simp add: nuses_skip vwb_frame)
qed (simp_all)

end