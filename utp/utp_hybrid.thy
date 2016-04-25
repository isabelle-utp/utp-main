section {* Hybrid relations *}

theory utp_hybrid
imports 
  utp_designs
begin

text {* Theory takes about 2:15 minutes to load; brute force proof innit? *}

no_notation disj (infixr "|" 30)

subsection {* Preliminary setup *}

text {* A hybrid state in terms of its discrete, continuous, and algebraic variables. *}

record ('d, 'c) hyflst =
  hdisc :: "'d \<times> 'c"

record ('d, 'c) hyst = "('d, 'c) hyflst" +
  htime :: real
  htraj :: "real \<Rightarrow> 'c"

type_synonym ('d, 'c) hycond = "('d, 'c) hyst condition"
type_synonym ('d, 'c) hypred = "('d, 'c) hyst upred"
type_synonym ('d, 'c) hyrel = "('d, 'c) hyst hrelation"
type_synonym ('a, 'd, 'c) hyexpr = "('a, ('d, 'c) hyst) uexpr"
type_synonym ('a, 'd, 'c) hyrexpr = "('a, ('d, 'c) hyst \<times> ('d, 'c) hyst) uexpr"

definition "time = VAR htime"
definition "disc = VAR hdisc"
definition "traj = VAR htraj"

declare time_def [upred_defs] and disc_def [upred_defs] and traj_def [upred_defs]

lemma uvar_time [simp]: "uvar time"
  apply (unfold_locales)
  apply (auto simp add: time_def)
  apply (metis hyflst.select_convs(1) hyst.select_convs(2) hyst.select_convs(3) hyst.surjective hyst.update_convs(1))
done

lemma uvar_disc [simp]: "uvar disc"
  apply (unfold_locales)
  apply (auto simp add: disc_def)
  apply (metis hyflst.surjective hyflst.update_convs(1))
done

lemma uvar_traj [simp]: "uvar traj"
  apply (unfold_locales)
  apply (auto simp add: traj_def)
  apply (metis hyflst.ext_inject hyst.ext_inject hyst.surjective hyst.update_convs(2))
done

lemma hyst_indeps [simp]:
  "time \<bowtie> disc" "disc \<bowtie> time"
  "time \<bowtie> traj" "traj \<bowtie> time"
  "disc \<bowtie> traj" "traj \<bowtie> disc"
  by (simp add: uvar_indep_def, pred_tac)+

definition cont_var :: "('a, 'c) uvar \<Rightarrow> ('a, 'd \<times> 'c) uvar" ("[_]\<^sub>c") where
"cont_var x = out_var x"

definition disc_var :: "('a, 'd) uvar \<Rightarrow> ('a, 'd \<times> 'c) uvar" ("[_]\<^sub>d") where
"disc_var x = in_var x"

definition "con\<alpha> = out\<alpha>"
definition "disc\<alpha> = in\<alpha>"

declare con\<alpha>_def [upred_defs] and disc\<alpha>_def [upred_defs] and cont_var_def [upred_defs] and disc_var_def [upred_defs]

subsection {* Hybrid healthiness conditions *}

definition "HCT1(P) = (P \<and> $time \<ge>\<^sub>u 0 \<and> $time \<le>\<^sub>u $time\<acute>)"

definition "HCT2(P) = (P \<and> ($time\<acute> >\<^sub>u $time \<Rightarrow> 
                              (\<^bold>\<exists> I \<bullet> elems\<^sub>u(\<guillemotleft>I\<guillemotright>) \<subseteq>\<^sub>u {$time .. $time\<acute>}\<^sub>u 
                                   \<and> {$time, $time\<acute>}\<^sub>u \<subseteq>\<^sub>u elems\<^sub>u(\<guillemotleft>I\<guillemotright>)
                                   \<and> (\<^bold>\<forall> n \<bullet> \<guillemotleft>n\<guillemotright> <\<^sub>u length\<^sub>u(\<guillemotleft>I\<guillemotright>) - 1
                                       \<Rightarrow> $traj cont-on\<^sub>u {\<guillemotleft>I\<guillemotright>\<lparr>\<guillemotleft>n\<guillemotright>\<rparr>\<^sub>u ..< \<guillemotleft>I\<guillemotright>\<lparr>\<guillemotleft>n\<guillemotright>+1\<rparr>\<^sub>u}\<^sub>u)
                                   \<and> sorted\<^sub>u(\<guillemotleft>I\<guillemotright>) \<and> distinct\<^sub>u(\<guillemotleft>I\<guillemotright>))))"

definition "HTRAJ(P) = (P \<and> $traj =\<^sub>u $traj\<acute>)"

declare HCT1_def [upred_defs] and HCT2_def [upred_defs] and HTRAJ_def [upred_defs]

abbreviation "HCT(P) \<equiv> HCT1(HCT2(HTRAJ(P)))"

subsection {* Hybrid relational operators *}

definition hTrue :: "('d, 'c::topological_space) hyrel" ("true\<^sub>H") where
"true\<^sub>H = HCT(true)"

definition hSkip :: "('d, 'c::topological_space) hyrel" ("II\<^sub>H") where
"II\<^sub>H = ($time \<ge>\<^sub>u 0 \<and> II)"

definition hAssigns :: "('d \<times> 'c::topological_space) usubst \<Rightarrow> ('d, 'c) hyrel" where
"hAssigns \<sigma> = ($time \<ge>\<^sub>u 0 \<and> disc := \<guillemotleft>\<sigma>\<guillemotright>\<lparr>&disc\<rparr>\<^sub>u)"

abbreviation hAssign :: "('a, 'd \<times> 'c::topological_space) uvar \<Rightarrow> ('a, 'd \<times> 'c) uexpr \<Rightarrow> ('d, 'c) hyrel" (infixl ":=\<^sub>H" 60)
where "x :=\<^sub>H v \<equiv> hAssigns [x \<mapsto>\<^sub>s v]"

lift_definition cont_lift :: "(real \<Rightarrow> ('d \<times> 'c) condition) \<Rightarrow> (real, ('d, 'c) hyst \<times> ('d, 'c) hyst) uexpr \<Rightarrow> ('d, 'c) hyrel" (infix "@\<^sub>u" 65)
is "\<lambda> P t (A, A'). P (t (A, A')) (fst (hdisc A), htraj A (t (A, A')))" .

definition hInt :: "(real \<Rightarrow> ('d \<times> 'c :: topological_space) condition) \<Rightarrow> ('d, 'c) hyrel"
where "hInt P = HCT($time\<acute> >\<^sub>u $time \<and> (\<^bold>\<forall> t \<in> {$time ..< $time\<acute>}\<^sub>u \<bullet> P @\<^sub>u \<guillemotleft>t\<guillemotright>))"

definition hDisInt :: "(real \<Rightarrow> ('d \<times> 'c :: t2_space) condition) \<Rightarrow> ('d, 'c) hyrel"
where "hDisInt P = (hInt P \<and> 
                    \<pi>\<^sub>1($disc\<acute>) =\<^sub>u \<pi>\<^sub>1($disc) \<and>
                    \<pi>\<^sub>2($disc) =\<^sub>u $traj\<lparr>$time\<rparr>\<^sub>u \<and> 
                    \<pi>\<^sub>2($disc\<acute>) =\<^sub>u lim\<^sub>u(x \<rightarrow> $time\<acute>\<^sup>-)($traj\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u)
                    )"

syntax
  "_time_var" :: "logic"
  "_hInt"     :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>H")
  "_hDisInt"  :: "logic \<Rightarrow> logic" ("\<lceil>|_|\<rceil>\<^sub>H")

parse_translation {*
let
  fun time_var_tr [] = Syntax.free "\<tau>"
    | time_var_tr _  = raise Match;
in
[(@{syntax_const "_time_var"}, K time_var_tr)]
end
*}

translations
  "\<lceil>P\<rceil>\<^sub>H"   == "CONST hInt (\<lambda> _time_var. P)"
  "\<lceil>|P|\<rceil>\<^sub>H" == "CONST hDisInt (\<lambda> _time_var. P)"

declare hTrue_def [urel_defs] and hInt_def [urel_defs] and hDisInt_def [urel_defs] and hSkip_def [urel_defs] and hAssigns_def [urel_defs]

definition hPreempt :: 
  "('d, 'c::topological_space) hyrel \<Rightarrow> ('d \<times> 'c) condition \<Rightarrow> 
    ('d, 'c) hyrel \<Rightarrow> ('d, 'c) hyrel" ("_ \<lbrakk>_\<rbrakk>\<^sub>u _" [64,0,65] 64)
where "P\<lbrakk>B\<rbrakk>\<^sub>uQ = ((Q \<triangleleft> (\<lambda>_.B) @\<^sub>u $time \<triangleright> (P \<and> \<lceil>\<not> B\<rceil>\<^sub>H)) \<or> ((\<lceil>B\<rceil>\<^sub>H \<and> ((\<lambda>_.B) @\<^sub>u $time) \<and> P) ;; Q))"

declare hPreempt_def [urel_defs]

type_synonym 'c ODE = "real \<times> 'c \<Rightarrow> 'c"

lift_definition hasDerivAt :: 
  "(real \<Rightarrow> 'c :: real_normed_vector) \<Rightarrow> 'c ODE \<Rightarrow> real \<Rightarrow> ('a, 'b) relation" ("_ has-deriv _ at _" [90, 0, 91] 90)
is "\<lambda> \<F> \<F>' \<tau> A. (\<F> has_vector_derivative (\<F>' (\<tau>, \<F> \<tau>))) (at \<tau> within {0..})" .

definition hODE :: "('c :: real_normed_vector) ODE \<Rightarrow> ('d, 'c) hyrel" ("\<langle>_\<rangle>\<^sub>H") where
"\<langle>\<F>'\<rangle>\<^sub>H = (\<^bold>\<exists> \<F> \<bullet> \<lceil>| \<F> has-deriv \<F>' at \<tau> \<and> &con\<alpha> =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u |\<rceil>\<^sub>H)"

definition hDAE :: "('c :: real_normed_vector) ODE \<Rightarrow> ('d \<times> 'c) condition \<Rightarrow> ('d, 'c) hyrel" ("\<langle>_|_\<rangle>\<^sub>H") where
"\<langle>\<F>'|B\<rangle>\<^sub>H = (\<langle>\<F>'\<rangle>\<^sub>H \<and> \<lceil>|B|\<rceil>\<^sub>H)"

definition hODE_init :: "('c, 'd, 'c) hyrexpr \<Rightarrow> ('c :: real_normed_vector) ODE \<Rightarrow> ('d, 'c) hyrel" ("_ \<Turnstile> \<langle>_\<rangle>\<^sub>H") where
"\<I> \<Turnstile> \<langle>\<F>'\<rangle>\<^sub>H = (\<langle>\<F>'\<rangle>\<^sub>H \<and> $traj\<lparr>$time\<rparr>\<^sub>u =\<^sub>u \<I>)"

declare hODE_def [urel_defs] and hDAE_def [urel_defs] and hODE_init_def [urel_defs]

lemma HCT_idempotent:
  "HCT(HCT(P)) = HCT(P)"
  by (rel_tac)

lemma HCT_monotone:
  "P \<sqsubseteq> Q \<Longrightarrow> HCT(P) \<sqsubseteq> HCT(Q)"
  by (rel_tac)

lemma HCT_hTrue: "HCT(true\<^sub>H) = true\<^sub>H"
  by (simp add: HCT_idempotent hTrue_def)

lemma hTrue_HCT_top: "P is HCT \<Longrightarrow> true\<^sub>H \<sqsubseteq> P"
  by (rel_tac, blast)

lemma HCT_false: "HCT(false) = false"
  by (rel_tac)

lemma HCT_conj: "HCT(P \<and> Q) = (HCT(P) \<and> HCT(Q))"
  by (rel_tac)

lemma HCT_disj: "HCT(P \<or> Q) = (HCT(P) \<or> HCT(Q))"
  by (rel_tac)

lemma HCT_cond_r: "HCT(P \<triangleleft> b \<triangleright> Q) = (HCT(P) \<triangleleft> b \<triangleright> HCT(Q))"
  by (rel_tac)

lemma HCT_hSkip: "HCT(II\<^sub>H) = II\<^sub>H"
  by (rel_tac)

lemma HCT_hAssigns: "HCT(hAssigns \<sigma>) = hAssigns \<sigma>"
  by (rel_tac)

lemma HCT_seq_r: "HCT(HCT(P) ;; HCT(Q)) = (HCT(P) ;; HCT(Q))"
  apply (rel_tac)
  apply blast
  apply blast
  apply (rename_tac P Q b b' b\<^sub>0 I\<^sub>1 I\<^sub>2)
  apply (case_tac "htime b = htime b\<^sub>0")
  apply (simp, blast)
  apply (case_tac "htime b\<^sub>0 = htime b'")
  apply (simp, blast)
  apply (subgoal_tac "htime b < htime b\<^sub>0")
  apply (subgoal_tac "htime b\<^sub>0 < htime b'")
  defer
  apply (linarith)
  apply (linarith)
  apply (subgoal_tac "hd(I\<^sub>2) = htime b\<^sub>0")
  apply (rule_tac x="I\<^sub>1 @ tl(I\<^sub>2)" in exI)
  apply (safe, simp_all)
  apply (metis atLeastAtMost_iff empty_iff list.set(1) list.set_sel(2) order_trans subsetCE)
  apply (rule disjI2)
  apply (rule tl_element)
  apply (simp)
  apply (smt in_set_conv_nth le0 list.sel(1) list.set_cases nth_Cons_0 sorted_nth_mono)
  apply (rename_tac P Q b b' b\<^sub>0 I\<^sub>1 I\<^sub>2 x)
  apply (simp add: nth_append)
  apply (auto)[1]
  apply (subgoal_tac "I\<^sub>1 ! x = hd(I\<^sub>2)")
  apply (simp add: nth_tl)
  apply (metis Suc_inject Suc_lessI Suc_pred add.right_neutral hd_conv_nth length_greater_0_conv length_pos_if_in_set nat_neq_iff neq0_conv)
  apply (subgoal_tac "I\<^sub>1 ! x = last(I\<^sub>1)")
  apply (subgoal_tac "last(I\<^sub>1) = htime b\<^sub>0")
  apply (simp)
  apply (metis antisym_conv atLeastAtMost_iff nth_mem sorted_last subsetCE)
  apply (metis One_nat_def Suc_lessI add.right_neutral add_Suc_right add_diff_cancel_right' last_conv_nth length_greater_0_conv length_pos_if_in_set)
  apply (simp add: nth_tl Suc_diff_le)
  apply (simp add: sorted_append sorted_tl)
  apply (auto)[1]
  apply (metis atLeastAtMost_iff length_greater_0_conv length_pos_if_in_set list.set_sel(2) order_trans subsetCE)
  apply (auto simp add: distinct_tl)
  apply (subgoal_tac "set (tl I\<^sub>2) \<subseteq> {htime b\<^sub>0<..htime b'}")
  apply (meson atLeastAtMost_iff greaterThanAtMost_iff not_le subset_code(1))
  apply (auto)
  apply (metis (no_types, hide_lams) One_nat_def Suc_less_eq Suc_pred in_set_conv_nth le_less length_pos_if_in_set length_tl list.exhaust_sel list.size(3) nat.discI nth_Cons_0 nth_eq_iff_index_eq nth_tl sorted_Cons)
  apply (metis Suc_pred atLeastAtMost_iff length_pos_if_in_set list.set_sel(2) list.size(3) old.nat.distinct(2) subsetCE)
  apply (smt Suc_pred antisym_conv atLeastAtMost_iff hd_conv_nth in_set_conv_nth le0 length_pos_if_in_set list.size(3) old.nat.distinct(2) sorted_nth_mono subsetCE)
done

lemma seq_r_HCT_closed:
  assumes "P is HCT" "Q is HCT"
  shows "(P ;; Q) is HCT"
  by (metis HCT_seq_r Healthy_def' assms(1) assms(2))

declare hInt_def [urel_defs]
declare hDisInt_def [urel_defs]

lemma HCT_hInt: "HCT(\<lceil>P\<rceil>\<^sub>H) = \<lceil>P\<rceil>\<^sub>H"
  by (simp add: HCT_idempotent hInt_def)

lemma HCT_hDisInt: "HCT(\<lceil>|P|\<rceil>\<^sub>H) = \<lceil>|P|\<rceil>\<^sub>H"
  by (rel_tac)

lemma hInt_true: "\<lceil>true\<rceil>\<^sub>H = HCT($time\<acute> >\<^sub>u $time)"
  by rel_tac

lemma hDisInt_false: "\<lceil>|false|\<rceil>\<^sub>H = false"
  by (rel_tac)

lemma hDisInt_conj: "\<lceil>|P(\<tau>) \<and> Q(\<tau>)|\<rceil>\<^sub>H = (\<lceil>|P(\<tau>)|\<rceil>\<^sub>H \<and> \<lceil>|Q(\<tau>)|\<rceil>\<^sub>H)"
  by (rel_tac)

lemma hInt_false: "\<lceil>false\<rceil>\<^sub>H = false"
  by rel_tac

lemma hInt_disj: "\<lceil>P(\<tau>) \<or> Q(\<tau>)\<rceil>\<^sub>H \<sqsubseteq> (\<lceil>P(\<tau>)\<rceil>\<^sub>H \<or> \<lceil>Q(\<tau>)\<rceil>\<^sub>H)"
  by (rel_tac)

lemma hInt_conj: "\<lceil>P(\<tau>) \<and> Q(\<tau>)\<rceil>\<^sub>H = (\<lceil>P(\<tau>)\<rceil>\<^sub>H \<and> \<lceil>Q(\<tau>)\<rceil>\<^sub>H)"
  by (rel_tac)

lemma hDisInt_refine_strengthen:
  "\<lbrakk> \<And> \<tau>. `Q(\<tau>) \<Rightarrow> P(\<tau>)` \<rbrakk> \<Longrightarrow> \<lceil>|P(\<tau>)|\<rceil>\<^sub>H \<sqsubseteq> \<lceil>|Q(\<tau>)|\<rceil>\<^sub>H"
  by rel_tac

lemma hPreempt_HCT_closed:
  assumes "P is HCT" "Q is HCT"
  shows "P\<lbrakk>B\<rbrakk>\<^sub>uQ is HCT"
proof -
  have "(\<lceil>B\<rceil>\<^sub>H \<and> ((\<lambda>_.B) @\<^sub>u $time) \<and> P) is HCT"
    by (rel_tac)
  hence "HCT((\<lceil>B\<rceil>\<^sub>H \<and> ((\<lambda>_.B) @\<^sub>u $time) \<and> P) ;; Q) = ((\<lceil>B\<rceil>\<^sub>H \<and> ((\<lambda>_.B) @\<^sub>u $time) \<and> P) ;; Q)"
    by (metis HCT_seq_r Healthy_def' assms(2))
  with assms show ?thesis
    by (simp add: Healthy_def hPreempt_def HCT_conj HCT_disj HCT_cond_r HCT_hInt)
qed

lemma gravity_ode_refine:
  "((\<guillemotleft>v\<^sub>0\<guillemotright>, \<guillemotleft>h\<^sub>0\<guillemotright>)\<^sub>u \<Turnstile> \<langle>\<lambda> (t, v, h). (- g, v)\<rangle>\<^sub>H \<and> $time =\<^sub>u 0) \<sqsubseteq> 
   (\<lceil>| &con\<alpha> =\<^sub>u (\<guillemotleft>v\<^sub>0\<guillemotright> - \<guillemotleft>g\<guillemotright>*\<guillemotleft>\<tau>\<guillemotright>, \<guillemotleft>v\<^sub>0\<guillemotright>*\<guillemotleft>\<tau>\<guillemotright> - \<guillemotleft>g\<guillemotright>*(\<guillemotleft>\<tau>\<guillemotright>*\<guillemotleft>\<tau>\<guillemotright>) / 2 + \<guillemotleft>h\<^sub>0\<guillemotright>)\<^sub>u |\<rceil>\<^sub>H \<and> $time =\<^sub>u 0)"
  apply (rel_tac)
  apply (rule exI)
  apply (auto)
  apply (safe intro!: has_vector_derivative_Pair, (rule has_vector_derivative_eq_rhs, (rule derivative_intros; (simp)?)+, simp)+)
done

end