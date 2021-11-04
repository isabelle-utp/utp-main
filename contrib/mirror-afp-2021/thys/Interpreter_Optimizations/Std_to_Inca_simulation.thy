theory Std_to_Inca_simulation
  imports Global List_util Std Inca
    "VeriComp.Simulation"
begin

section \<open>Generic definitions\<close>

print_locale std

locale std_inca_simulation =
  Sstd: std
    Fstd_empty Fstd_get Fstd_add Fstd_to_list
    heap_empty heap_get heap_add heap_to_list
    is_true is_false
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> +
  Sinca: inca
    Finca_empty Finca_get Finca_add Finca_to_list
    heap_empty heap_get heap_add heap_to_list
    is_true is_false
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll>
  for
    \<comment> \<open>Functions environments\<close>
    Fstd_empty and
    Fstd_get :: "'fenv_std \<Rightarrow> 'fun \<Rightarrow> ('dyn, 'var, 'fun, 'op) Std.instr fundef option" and
    Fstd_add and Fstd_to_list and

    Finca_empty and
    Finca_get :: "'fenv_inca \<Rightarrow> 'fun \<Rightarrow> ('dyn, 'var, 'fun, 'op, 'opinl) Inca.instr fundef option" and
    Finca_add and Finca_to_list and
    
    \<comment> \<open>Memory heap\<close>
    heap_empty and heap_get :: "'henv \<Rightarrow> 'var \<times> 'dyn \<Rightarrow> 'dyn option" and heap_add and heap_to_list and

    \<comment> \<open>Dynamic values\<close>
    is_true :: "'dyn \<Rightarrow> bool" and is_false and

    \<comment> \<open>n-ary operations\<close>
    \<OO>\<pp> :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn" and \<AA>\<rr>\<ii>\<tt>\<yy> and
    \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> :: "'opinl \<Rightarrow> 'op"
begin

fun norm_instr where
  "norm_instr (Inca.IPush d) = Std.IPush d" |
  "norm_instr Inca.IPop = Std.IPop" |
  "norm_instr (Inca.ILoad x) = Std.ILoad x" |
  "norm_instr (Inca.IStore x) = Std.IStore x" |
  "norm_instr (Inca.IOp op) = Std.IOp op" |
  "norm_instr (Inca.IOpInl opinl) = Std.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl)" |
  "norm_instr (Inca.ICJump n) = Std.ICJump n" |
  "norm_instr (Inca.ICall x) = Std.ICall x"

abbreviation (input) norm_eq where
  "norm_eq x y \<equiv> x = norm_instr y"

definition rel_fundefs where
  "rel_fundefs f g = (\<forall>x. rel_option (rel_fundef (\<lambda>x y. x = norm_instr y)) (f x) (g x))"

lemma rel_fundefs_Some1:
  assumes "rel_fundefs f g" and "f x = Some y"
  shows "\<exists>z. g x = Some z \<and> rel_fundef norm_eq y z"
proof -
  from assms(1) have "rel_option (rel_fundef norm_eq) (f x) (g x)"
    unfolding rel_fundefs_def by simp
  with assms(2) show ?thesis
    by (simp add: option_rel_Some1)
qed

lemma rel_fundefs_Some2:
  assumes "rel_fundefs f g" and "g x = Some y"
  shows "\<exists>z. f x = Some z \<and> rel_fundef norm_eq z y"
proof -
  from assms(1) have "rel_option (rel_fundef norm_eq) (f x) (g x)"
    unfolding rel_fundefs_def by simp
  with assms(2) show ?thesis
    by (simp add: option_rel_Some2)
qed

lemma rel_fundef_body_nth:
  assumes "rel_fundef norm_eq fd1 fd2" and "pc < length (body fd1)"
  shows "body fd1 ! pc = norm_instr (body fd2 ! pc)"
  using assms
  by (auto dest: list_all2_nthD simp: fundef.rel_sel)

lemma rel_fundef_rewrite_body:
  assumes
    "rel_fundef norm_eq fd1 fd2" and
    "norm_instr (body fd2 ! pc) = norm_instr instr"
  shows "rel_fundef norm_eq fd1 (rewrite_fundef_body fd2 pc instr)"
  using assms(1)
proof (cases rule: fundef.rel_cases)
  case (Fundef xs ar' ys ar)
  hence "length xs = length ys"
    by (simp add: list_all2_conv_all_nth)
  hence "length xs = length (rewrite ys pc instr)"
    by simp
  hence "list_all2 norm_eq xs (rewrite ys pc instr)"
  proof (elim list_all2_all_nthI)
    fix n
    assume "n < length xs"
    hence "n < length ys"
      by (simp add: \<open>length xs = length ys\<close>)
    thus "xs ! n = norm_instr (rewrite ys pc instr ! n)"
      using list_all2_nthD[OF \<open>list_all2 norm_eq xs ys\<close> \<open>n < length xs\<close>, symmetric]
      using assms(2)[unfolded Fundef(2), simplified]
      by (cases "pc = n"; simp)
  qed
  thus ?thesis
    using Fundef by simp
qed

lemma rel_fundefs_rewrite:
  assumes
    rel_F1_F2: "rel_fundefs (Fstd_get F1) (Finca_get F2)" and
    F2_get_f: "Finca_get F2 f = Some fd2" and
    F2_add_f: "Finca_add F2 f (rewrite_fundef_body fd2 pc instr) = F2'" and
    norm_eq: "norm_instr (body fd2 ! pc) = norm_instr instr"
  shows "rel_fundefs (Fstd_get F1) (Finca_get F2')"
  unfolding rel_fundefs_def
proof
  fix x
  show "rel_option (rel_fundef norm_eq) (Fstd_get F1 x) (Finca_get F2' x)"
  proof (cases "x = f")
    case True
    then have F2'_get_x: "Finca_get F2' x = Some (rewrite_fundef_body fd2 pc instr)"
      using F2_add_f by auto
    obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2 F2_get_f] by auto
    thus ?thesis
      unfolding F2'_get_x option_rel_Some2
      using True rel_fundef_rewrite_body[OF _ norm_eq]
      by auto
  next
    case False
    then have "Finca_get F2' x = Finca_get F2 x"
      using F2_add_f by auto
    then show ?thesis
      using rel_F1_F2 rel_fundefs_def
      by fastforce
  qed
qed


section \<open>Simulation relation\<close>

inductive match (infix "\<sim>" 55) where
  "rel_fundefs (Fstd_get F1) (Finca_get F2) \<Longrightarrow> (State F1 H st) \<sim> (State F2 H st)"

section \<open>Backward simulation\<close>

lemma backward_lockstep_simulation:
  assumes "Sinca.step s2 s2'" and "s1 \<sim> s2"
  shows "\<exists>s1'. Sstd.step s1 s1' \<and> s1' \<sim> s2'"
proof -
  from assms(2) obtain F1 F2 H st where
    s1_def: "s1 = State F1 H st" and
    s2_def: "s2 = State F2 H st" and
    rel_F1_F2: "rel_fundefs (Fstd_get F1) (Finca_get F2)"
    by (auto elim: match.cases)
  from assms(1) show "?thesis"
    unfolding s1_def s2_def
  proof (induction "State F2 H st" s2' rule: Sinca.step.induct)
    case (step_push f fd2 pc d \<Sigma> st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc) (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_push \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sstd.step_push simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_pop f fd2 pc d \<Sigma> st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc) \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_pop \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sstd.step_pop simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_load f fd2 pc x y d \<Sigma> st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc) (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_load \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sstd.step_load simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_store f fd2 pc x y d H' \<Sigma> st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H' (Frame f (Suc pc) \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_store \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sstd.step_store simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op f fd2 pc op ar \<Sigma> x st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_op \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sstd.step_op simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op_inl f fd2 pc op ar \<Sigma> opinl x F2' st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_op_inl \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        using  Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct Sinca.\<II>\<nn>\<ll>_invertible
        by (auto intro!: Sstd.step_op simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using step_op_inl Sinca.\<II>\<nn>\<ll>_invertible
        by (auto intro!: match.intros rel_fundefs_rewrite[OF rel_F1_F2])
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op_inl_hit f fd2 pc opinl ar \<Sigma> x st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_op_inl_hit \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close> Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct
        by (auto intro!: Sstd.step_op simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op_inl_miss f fd2 pc opinl ar \<Sigma> x F' st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_op_inl_miss \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close> Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct
        by (auto intro!: Sstd.step_op simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using step_op_inl_miss rel_fundefs_rewrite[OF rel_F1_F2]
        by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_cjump_true f fd2 pc n d \<Sigma> st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f n \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_cjump_true \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sstd.step_cjump_true simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_cjump_false f fd2 pc n d \<Sigma> st')
    then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc) \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_cjump_false \<open>Fstd_get F1 f = Some fd1\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sstd.step_cjump_false simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_fun_call f fd2 pc g gd2 \<Sigma> frame\<^sub>f frame\<^sub>g st')
    obtain fd1 where "Fstd_get F1 f = Some fd1" and rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
      using step_fun_call rel_fundefs_Some2[OF rel_F1_F2] by blast
    obtain gd1 where "Fstd_get F1 g = Some gd1" and rel_gd1_gd2: "rel_fundef norm_eq gd1 gd2"
      using step_fun_call rel_fundefs_Some2[OF rel_F1_F2] by blast
    have pc_in_range: "pc < length (body fd1)"
      using \<open>pc < length (body fd2)\<close> rel_fundef_body_length[OF rel_fd1_fd2]
      by simp
    have arity_gd1_gd2: "arity gd2 = arity gd1"
      using rel_fundef_arities[OF rel_gd1_gd2, symmetric] .
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?\<Sigma>g = "take (arity gd1) \<Sigma>"
      let ?s1' = "State F1 H (Frame g 0 ?\<Sigma>g # Frame f pc \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_fun_call pc_in_range
        using \<open>Fstd_get F1 f = Some fd1\<close> \<open>Fstd_get F1 g = Some gd1\<close>
        using rel_fundef_body_nth[OF rel_fd1_fd2 pc_in_range] arity_gd1_gd2
        by (auto intro: Sstd.step_fun_call)
      moreover have "?MATCH ?s1'"
        using step_fun_call rel_F1_F2 arity_gd1_gd2 by (auto intro: match.intros)
      ultimately show ?thesis by auto
    qed
  next
    case (step_fun_end g gd2 \<Sigma>\<^sub>f pc\<^sub>g frame\<^sub>g \<Sigma>\<^sub>g frame\<^sub>f f pc\<^sub>f frame\<^sub>f' st')
    then obtain gd1 where "Fstd_get F1 g = Some gd1" and rel_gd1_gd2: "rel_fundef norm_eq gd1 gd2"
      using rel_fundefs_Some2[OF rel_F1_F2] by blast
    have arity_gd1_gd2: "arity gd2 = arity gd1"
      using rel_fundef_arities[OF rel_gd1_gd2, symmetric] .
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F1 H (Frame f (Suc pc\<^sub>f) (\<Sigma>\<^sub>g @ drop (arity gd1) \<Sigma>\<^sub>f) # st')"
      have "?STEP ?s1'"
        using step_fun_end \<open>Fstd_get F1 g = Some gd1\<close>
        using rel_fundef_body_length[OF rel_gd1_gd2] arity_gd1_gd2
        by (auto intro: Sstd.step_fun_end)
      moreover have "?MATCH ?s1'"
        using step_fun_end rel_F1_F2 arity_gd1_gd2 by (auto intro: match.intros)
      ultimately show ?thesis by auto
    qed
  qed
qed

lemma match_final_backward:
  "s1 \<sim> s2 \<Longrightarrow> Sinca.final s2 \<Longrightarrow> Sstd.final s1"
proof (induction s1 s2 rule: match.induct)
  case (1 F1 F2 H st)
  then obtain f fd2 pc \<Sigma> where
    st_def: "st = [Frame f pc \<Sigma>]" and
    "Finca_get F2 f = Some fd2" and
    pc_def: "pc = length (body fd2)"
    by (auto elim: Sinca.final.cases)
  then obtain fd1 where "Fstd_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
    using 1 rel_fundefs_Some2 by fast
  then show ?case
    unfolding st_def
    using pc_def rel_fundef_body_length[OF \<open>rel_fundef norm_eq fd1 fd2\<close>]
    by (auto intro: Sstd.final.intros)
qed

sublocale std_inca_simulation:
  backward_simulation Sstd.step Sinca.step Sstd.final Sinca.final "\<lambda>_ _. False" "\<lambda>_. match"
  using match_final_backward backward_lockstep_simulation
    lockstep_to_plus_backward_simulation[of match Sinca.step Sstd.step]
  by unfold_locales auto

section \<open>Forward simulation\<close>

lemma forward_lockstep_simulation:
  assumes "Sstd.step s1 s1'" and "s1 \<sim> s2"
  shows "\<exists>s2'. Sinca.step s2 s2' \<and> s1' \<sim> s2'"
proof -
  from assms(2) obtain F1 F2 H st where
    s1_def: "s1 = State F1 H st" and
    s2_def: "s2 = State F2 H st" and
    rel_F1_F2: "rel_fundefs (Fstd_get F1) (Finca_get F2)"
    by (auto elim: match.cases)
  from assms(1) show "?thesis"
    unfolding s1_def s2_def
  proof(induction "State F1 H st" s1' rule: Sstd.step.induct)
    case (step_push f fd1 pc d \<Sigma> st')
    then obtain fd2 where "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f (Suc pc) (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_push \<open>Finca_get F2 f = Some fd2\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sinca.step_push elim!: norm_instr.elims simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_pop f fd1 pc d \<Sigma> st')
    then obtain fd2 where "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f (Suc pc) \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_pop \<open>Finca_get F2 f = Some fd2\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sinca.step_pop elim!: norm_instr.elims simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_load f fd1 pc x y d \<Sigma> st')
    then obtain fd2 where "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f (Suc pc) (d # \<Sigma>) # st')"
      have "?STEP ?s1'"
        using step_load \<open>Finca_get F2 f = Some fd2\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sinca.step_load elim!: norm_instr.elims simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_store f fd1 pc x y d H' \<Sigma> st')
    then obtain fd2 where "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H' (Frame f (Suc pc) \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_store \<open>Finca_get F2 f = Some fd2\<close> \<open>rel_fundef norm_eq fd1 fd2\<close>
        by (auto intro!: Sinca.step_store elim!: norm_instr.elims simp: rel_fundef_body_nth)
      moreover have "?MATCH ?s1'"
        using rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_op f fd1 pc op ar \<Sigma> x st')
    then obtain fd2 where F2_get_f[intro]: "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    have pc_in_range[intro]: "pc < length (body fd2)"
      using step_op \<open>rel_fundef norm_eq fd1 fd2\<close> rel_fundef_body_length by fastforce
    have norm_body2: "norm_instr (body fd2 ! pc) = Std.IOp op"
      using step_op rel_fundef_body_nth[OF \<open>rel_fundef norm_eq fd1 fd2\<close>, of pc]
      by simp
    then show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof (cases "body fd2 ! pc")
      case (IOp op')
      then have "op' = op" using norm_body2 by simp
      show ?thesis
      proof (cases "\<II>\<nn>\<ll> op' (take ar \<Sigma>)")
        case None
        let ?s2' = "State F2 H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st')"
        have "?STEP ?s2'"
          using None IOp step_op \<open>op' = op\<close>
          by (auto intro: Sinca.step_op)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 by (auto intro: match.intros)
        ultimately show ?thesis by auto
      next
        case (Some opinl)
        let ?fd2' = "rewrite_fundef_body fd2 pc (IOpInl opinl)"
        let ?s2' = "State (Finca_add F2 f ?fd2') H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st')"
        have "?STEP ?s2'"
          using Some IOp step_op \<open>op' = op\<close>
          using Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct Sinca.\<II>\<nn>\<ll>_invertible
          by (auto intro: Sinca.step_op_inl)  
        moreover have "?MATCH ?s2'"
          using Some IOp Sinca.\<II>\<nn>\<ll>_invertible
          by (auto intro!: match.intros rel_fundefs_rewrite[OF rel_F1_F2])
        ultimately show ?thesis by auto
      qed
    next
      case (IOpInl op')
      then have "\<DD>\<ee>\<II>\<nn>\<ll> op' = op" using norm_body2 by simp
      show ?thesis
      proof (cases "\<II>\<ss>\<II>\<nn>\<ll> op' (take ar \<Sigma>)")
        case True
        let ?s2' = "State F2 H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st')"
        have "?STEP ?s2'"
          using True IOpInl step_op \<open>\<DD>\<ee>\<II>\<nn>\<ll> op' = op\<close> Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct
          by (auto intro!: Sinca.step_op_inl_hit)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 by (auto intro: match.intros)
        ultimately show ?thesis by auto
      next
        case False
        let ?fd2' = "rewrite_fundef_body fd2 pc (IOp (\<DD>\<ee>\<II>\<nn>\<ll> op'))"
        let ?s2' = "State (Finca_add F2 f ?fd2') H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st')"
        have "?STEP ?s2'"
          using False IOpInl step_op \<open>\<DD>\<ee>\<II>\<nn>\<ll> op' = op\<close> Sinca.\<II>\<nn>\<ll>\<OO>\<pp>_correct
          by (auto intro!: Sinca.step_op_inl_miss)
        moreover have "?MATCH ?s2'"
          using IOpInl
          by (auto intro!: match.intros intro: rel_fundefs_rewrite[OF rel_F1_F2])
        ultimately show ?thesis by auto
      qed
    qed simp_all
  next
    case (step_cjump_true f fd1 pc n d \<Sigma> st')
    then obtain fd2 where F2_get_f[intro]: "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    have pc_in_range[intro]: "pc < length (body fd2)"
      using \<open>rel_fundef norm_eq fd1 fd2\<close> rel_fundef_body_length step_cjump_true.hyps(2) by fastforce
    have norm_body2: "norm_instr (body fd2 ! pc) = Std.ICJump n"
      using step_cjump_true rel_fundef_body_nth[OF \<open>rel_fundef norm_eq fd1 fd2\<close>, of pc]
      by simp
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f n \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_cjump_true norm_body2
        by (auto intro: Sinca.step_cjump_true elim: norm_instr.elims)
      moreover have "?MATCH ?s1'"
        using step_cjump_true rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_cjump_false f fd1 pc n d \<Sigma> st')
    then obtain fd2 where F2_get_f[intro]: "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    have pc_in_range[intro]: "pc < length (body fd2)"
      using \<open>rel_fundef norm_eq fd1 fd2\<close> rel_fundef_body_length step_cjump_false by fastforce
    have norm_body2: "norm_instr (body fd2 ! pc) = Std.ICJump n"
      using step_cjump_false rel_fundef_body_nth[OF \<open>rel_fundef norm_eq fd1 fd2\<close>, of pc]
      by simp
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f (Suc pc) \<Sigma> # st')"
      have "?STEP ?s1'"
        using step_cjump_false norm_body2
        by (auto intro: Sinca.step_cjump_false elim: norm_instr.elims)
      moreover have "?MATCH ?s1'"
        using step_cjump_false rel_F1_F2 by (auto intro: match.intros)
      ultimately show "?thesis" by blast
    qed
  next
    case (step_fun_call f fd1 pc g gd1 \<Sigma> frame\<^sub>f frame\<^sub>g st')
    then obtain fd2 where "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    obtain gd2 where "Finca_get F2 g = Some gd2" and rel_gd1_gd2: "rel_fundef norm_eq gd1 gd2"
      using step_fun_call rel_fundefs_Some1[OF rel_F1_F2] by blast
    have pc_in_range: "pc < length (body fd2)"
      using step_fun_call \<open>rel_fundef norm_eq fd1 fd2\<close> rel_fundef_body_length by fastforce
    have arity_gd1_gd2: "arity gd1 = arity gd2"
      using rel_fundef_arities[OF rel_gd1_gd2] .
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?\<Sigma>g = "take (arity gd2) \<Sigma>"
      let ?s2' = "State F2 H (Frame g 0 ?\<Sigma>g # Frame f pc \<Sigma> # st')"
      have "?STEP ?s2'"
      proof -
        have "arity gd2 \<le> length \<Sigma>"
          using \<open>arity gd1 \<le> length \<Sigma>\<close> arity_gd1_gd2 by simp
        moreover have "body fd2 ! pc = Inca.ICall g"
          using step_fun_call rel_fundef_body_nth[OF \<open>rel_fundef norm_eq fd1 fd2\<close>, of pc]
          by (auto elim: norm_instr.elims)
        ultimately show ?thesis
          using step_fun_call
          using \<open>Finca_get F2 g = Some gd2\<close> \<open>Finca_get F2 f = Some fd2\<close>
          using pc_in_range \<open>body fd2 ! pc = Inca.ICall g\<close>
          by (auto intro: Sinca.step_fun_call)
      qed
      moreover have "?MATCH ?s2'"
        using step_fun_call rel_F1_F2 arity_gd1_gd2 by (auto intro: match.intros)
      ultimately show ?thesis by auto
    qed
  next
    case (step_fun_end g gd1 \<Sigma>\<^sub>f pc\<^sub>g frame\<^sub>g \<Sigma>\<^sub>g frame\<^sub>f f pc\<^sub>f frame\<^sub>f' st')
    then obtain gd2 where "Finca_get F2 g = Some gd2" and rel_gd1_gd2: "rel_fundef norm_eq gd1 gd2"
      using rel_fundefs_Some1[OF rel_F1_F2] by blast
    have pc_at_end: "pc\<^sub>g = length (body gd2)"
      using rel_fundef_body_length[OF rel_gd1_gd2] step_fun_end by fastforce
    have arity_gd1_gd2: "arity gd1 = arity gd2"
      using rel_fundef_arities[OF rel_gd1_gd2] .
    show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
    proof -
      let ?s1' = "State F2 H (Frame f (Suc pc\<^sub>f) (\<Sigma>\<^sub>g @ drop (arity gd2) \<Sigma>\<^sub>f) # st')"
      have "?STEP ?s1'"
      proof -
        have "arity gd2 \<le> length \<Sigma>\<^sub>f"
          using \<open>arity gd1 \<le> length \<Sigma>\<^sub>f\<close> arity_gd1_gd2 by simp
        then show ?thesis
          using step_fun_end pc_at_end \<open>Finca_get F2 g = Some gd2\<close>
          by (auto intro: Sinca.step_fun_end)
      qed
      moreover have "?MATCH ?s1'"
        using step_fun_end rel_F1_F2 arity_gd1_gd2 by (auto intro: match.intros)
      ultimately show "?thesis" by auto
    qed
  qed
qed

lemma forward_match_final:
  "s1 \<sim> s2 \<Longrightarrow> Sstd.final s1 \<Longrightarrow> Sinca.final s2"
proof (induction s1 s2 rule: match.induct)
  case (1 F1 F2 H st)
  then obtain f fd1 pc \<Sigma> where
    st_def: "st = [Frame f pc \<Sigma>]" and
    "Fstd_get F1 f = Some fd1" and
    pc_def: "pc = length (body fd1)"
    by (auto elim: Sstd.final.cases)
  then obtain fd2 where "Finca_get F2 f = Some fd2" and "rel_fundef norm_eq fd1 fd2"
    using 1 rel_fundefs_Some1 by fast
  then show ?case
    unfolding st_def
    using pc_def rel_fundef_body_length[OF \<open>rel_fundef norm_eq fd1 fd2\<close>]
    by (auto intro: Sinca.final.intros)
qed

sublocale std_inca_forward_simulation:
  forward_simulation Sstd.step Sinca.step Sstd.final Sinca.final "\<lambda>_ _. False" "\<lambda>_. match"
  using forward_match_final forward_lockstep_simulation
    lockstep_to_plus_forward_simulation[of match Sstd.step _ Sinca.step]
  by unfold_locales auto


section \<open>Bisimulation\<close>

sublocale std_inca_bisimulation:
  bisimulation Sstd.step Sinca.step Sstd.final Sinca.final "\<lambda>_ _. False" "\<lambda>_. match"
  by unfold_locales

end

end