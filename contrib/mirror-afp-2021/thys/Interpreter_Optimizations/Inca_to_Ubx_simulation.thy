theory Inca_to_Ubx_simulation
  imports List_util Option_applicative Result
    "VeriComp.Simulation"
    Inca Ubx Ubx_type_inference Unboxed_lemmas
begin


section \<open>Locale imports\<close>

locale inca_to_ubx_simulation =
  Sinca: inca
    Finca_empty Finca_get Finca_add Finca_to_list
    heap_empty heap_get heap_add heap_to_list
    is_true is_false
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll> +
  Subx: ubx_sp
    Fubx_empty Fubx_get Fubx_add Fubx_to_list
    heap_empty heap_get heap_add heap_to_list
    is_true is_false box_ubx1 unbox_ubx1 box_ubx2 unbox_ubx2
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll> \<UU>\<bb>\<xx>\<OO>\<pp> \<UU>\<bb>\<xx> \<BB>\<oo>\<xx> \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
  for
    \<comment> \<open>Functions environments\<close>
    Finca_empty and
    Finca_get :: "'fenv_inca \<Rightarrow> 'fun \<Rightarrow> ('dyn, 'var, 'fun, 'op, 'opinl) Inca.instr fundef option" and
    Finca_add and Finca_to_list and

    Fubx_empty and
    Fubx_get :: "'fenv_ubx \<Rightarrow> 'fun \<Rightarrow> ('dyn, 'var, 'fun, 'op, 'opinl, 'opubx, 'ubx1, 'ubx2) Ubx.instr fundef option" and
    Fubx_add and Fubx_to_list and

    \<comment> \<open>Memory heap\<close>
    heap_empty and heap_get :: "'henv \<Rightarrow> 'var \<times> 'dyn \<Rightarrow> 'dyn option" and heap_add and heap_to_list and

    \<comment> \<open>Unboxed values\<close>
    is_true and is_false and
    box_ubx1 and unbox_ubx1 and
    box_ubx2 and unbox_ubx2 and

    \<comment> \<open>n-ary operations\<close>
    \<OO>\<pp> and \<AA>\<rr>\<ii>\<tt>\<yy> and \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> and \<UU>\<bb>\<xx>\<OO>\<pp> and \<UU>\<bb>\<xx> and \<BB>\<oo>\<xx> and \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
begin

declare Subx.sp_append[simp]


section \<open>Strongest postcondition\<close>

definition sp_fundef where
  "sp_fundef F fd xs \<equiv> Subx.sp F xs (replicate (arity fd) None)"

lemmas sp_fundef_generalize =
  Subx.sp_generalize[where \<Sigma> = "replicate (arity fd) None" for fd, simplified, folded sp_fundef_def]

lemma eq_sp_to_eq_sp_fundef:
  assumes "Subx.sp F1 = (Subx.sp F2 :: ('dyn, 'id, _, _, _, _, 'num, 'bool) Ubx.instr list \<Rightarrow> _)"
  shows "sp_fundef F1 = (sp_fundef F2 :: _ \<Rightarrow> ('dyn, 'id, _, _, _, _, 'num, 'bool) Ubx.instr list \<Rightarrow> _)"
  using assms(1)
  by (intro ext; simp add: sp_fundef_def)

definition sp_fundefs where
  "sp_fundefs F \<equiv> \<forall>f fd. F f = Some fd \<longrightarrow> sp_fundef F fd (body fd) = Ok [None]"

section \<open>Normalization\<close>

fun norm_instr where
  "norm_instr (Ubx.IPush d) = Inca.IPush d" |
  "norm_instr (Ubx.IPushUbx1 n) = Inca.IPush (box_ubx1 n)" |
  "norm_instr (Ubx.IPushUbx2 b) = Inca.IPush (box_ubx2 b)" |
  "norm_instr Ubx.IPop = Inca.IPop" |
  "norm_instr (Ubx.ILoad x) = Inca.ILoad x" |
  "norm_instr (Ubx.ILoadUbx _ x) = Inca.ILoad x" |
  "norm_instr (Ubx.IStore x) = Inca.IStore x" |
  "norm_instr (Ubx.IStoreUbx _ x) = Inca.IStore x" |
  "norm_instr (Ubx.IOp op) = Inca.IOp op" |
  "norm_instr (Ubx.IOpInl op) = Inca.IOpInl op" |
  "norm_instr (Ubx.IOpUbx op) = Inca.IOpInl (\<BB>\<oo>\<xx> op)" |
  "norm_instr (Ubx.ICJump n) = Inca.ICJump n" |
  "norm_instr (Ubx.ICall x) = Inca.ICall x"

definition rel_fundefs where
  "rel_fundefs f g = (\<forall>x. rel_option (rel_fundef (\<lambda>y z. y = norm_instr z)) (f x) (g x))"

abbreviation (input) norm_eq where
  "norm_eq x y \<equiv> x = norm_instr y"

lemma norm_generalize_instr: "norm_instr (Subx.generalize_instr instr) = norm_instr instr"
  by (cases instr) simp_all

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

lemma rel_fundef_generalize:
  assumes "rel_fundef norm_eq fd1 fd2"
  shows "rel_fundef norm_eq fd1 (Subx.generalize_fundef fd2)"
  using assms(1)
proof (cases rule: fundef.rel_cases)
  case (Fundef xs ar' ys ar)
  hence "list_all2 (\<lambda>x y. x = norm_instr y) xs (map Subx.generalize_instr ys)"
    by (auto elim!: list_all2_mono simp: list.rel_map norm_generalize_instr)
  thus ?thesis
    using Fundef by simp
qed

lemma rel_fundefs_empty: "rel_fundefs (\<lambda>_. None) (\<lambda>_. None)"
  by (simp add: rel_fundefs_def)

lemma rel_fundefs_None1:
  assumes "rel_fundefs f g" and "f x = None"
  shows "g x = None"
  by (metis assms rel_fundefs_def rel_option_None1)

lemma rel_fundefs_None2:
  assumes "rel_fundefs f g" and "g x = None"
  shows "f x = None"
  by (metis assms rel_fundefs_def rel_option_None2)

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

lemma rel_fundefs_rel_option:
  assumes "rel_fundefs f g" and "\<And>x y. rel_fundef norm_eq x y \<Longrightarrow> h x y"
  shows "rel_option h (f z) (g z)"
proof -
  have "rel_option (rel_fundef norm_eq) (f z) (g z)"
    using assms(1)[unfolded rel_fundefs_def] by simp
  then show ?thesis
    unfolding rel_option_unfold
    by (auto simp add: assms(2))
qed


section \<open>Equivalence of call stacks\<close>

definition norm_stack :: "('dyn, 'ubx1, 'ubx2) unboxed list \<Rightarrow> 'dyn list" where
  "norm_stack \<Sigma> \<equiv> List.map Subx.norm_unboxed \<Sigma>"

lemma norm_stack_Nil[simp]: "norm_stack [] = []"
  by (simp add: norm_stack_def)

lemma norm_stack_Cons[simp]: "norm_stack (d # \<Sigma>) = Subx.norm_unboxed d # norm_stack \<Sigma>"
  by (simp add: norm_stack_def)

lemma norm_stack_append: "norm_stack (xs @ ys) = norm_stack xs @ norm_stack ys"
  by (simp add: norm_stack_def)

lemmas drop_norm_stack = drop_map[where f = Subx.norm_unboxed, folded norm_stack_def]
lemmas take_norm_stack = take_map[where f = Subx.norm_unboxed, folded norm_stack_def]
lemmas norm_stack_map = map_map[where f = Subx.norm_unboxed, folded norm_stack_def]

lemma norm_box_stack[simp]: "norm_stack (map Subx.box_operand \<Sigma>) = norm_stack \<Sigma>"
  by (induction \<Sigma>) (auto simp: norm_stack_def)

lemma length_norm_stack[simp]: "length (norm_stack xs) = length xs"
  by (simp add: norm_stack_def)

definition is_valid_fun_call where
  "is_valid_fun_call get fd2 n \<Sigma>2 g \<equiv> n < length (body fd2) \<and> body fd2 ! n = ICall g \<and>
      (\<exists>gd. get g = Some gd \<and> list_all is_dyn_operand (take (arity gd) \<Sigma>2))"

inductive rel_stacktraces for get where
  rel_stacktraces_Nil:
    "rel_stacktraces get [] [] opt" |

  rel_stacktraces_Cons:
    "rel_stacktraces get st1 st2 (Some f) \<Longrightarrow>
    \<Sigma>1 = norm_stack \<Sigma>2 \<Longrightarrow>
    get f = Some fd2 \<Longrightarrow>
    sp_fundef get fd2 (take n (body fd2)) = Ok (map typeof \<Sigma>2) \<Longrightarrow>
    pred_option (is_valid_fun_call get fd2 n \<Sigma>2) opt \<Longrightarrow>
    rel_stacktraces get (Frame f n \<Sigma>1 # st1) (Frame f n \<Sigma>2 # st2) opt"

definition all_same_arities where
  "all_same_arities F1 F2 \<equiv> \<forall>f. rel_option (\<lambda>fd gd. arity fd = arity gd) (F1 f) (F2 f)"

lemma all_same_arities_commutative: "all_same_arities F1 F2 = all_same_arities F2 F1"
proof
  assume "all_same_arities F1 F2"
  then show "all_same_arities F2 F1"
    unfolding all_same_arities_def
    by (simp add: rel_option_unfold)
next
  assume "all_same_arities F2 F1"
  then show "all_same_arities F1 F2"
    unfolding all_same_arities_def
    by (simp add: rel_option_unfold)
qed

lemma sp_instr_same_arities:
  "all_same_arities F1 F2 \<Longrightarrow> Subx.sp_instr F1 x ys = Subx.sp_instr F2 x ys"
proof (induction F1 x ys rule: Subx.sp_instr.induct)
  fix F1 f \<Sigma>
  assume assms: "all_same_arities F1 F2"
  show "Subx.sp_instr F1 (Ubx.ICall f) \<Sigma> = Subx.sp_instr F2 (Ubx.ICall f) \<Sigma>"
  proof (cases "F1 f")
    case None
    then have "F2 f = None"
      using HOL.spec[OF assms[unfolded all_same_arities_def], of f] by simp
    with None show ?thesis by simp
  next
    case (Some a)
    then obtain b where "F2 f = Some b" and "arity a = arity b"
      using HOL.spec[OF assms[unfolded all_same_arities_def], of f] by (auto simp: option_rel_Some1)
    with Some show ?thesis by simp
  qed
qed simp_all

lemma sp_same_arities:
  assumes "all_same_arities F1 F2"
  shows "Subx.sp F1 = Subx.sp F2"
proof (intro ext allI)
  fix xs ys
  show "Subx.sp F1 xs ys = Subx.sp F2 xs ys"
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)
    show ?case
      apply simp
      apply (cases "(F1, x, ys)" rule: Subx.sp_instr.cases;
          simp add: Cons.IH Let_def)
      subgoal for opubx
        apply (cases "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx")
        by (auto simp: Cons.IH Let_def)
      subgoal for f
        apply (rule option.rel_induct[of "(\<lambda>fd gd. arity fd = arity gd)" "F1 f" "F2 f"])
        using assms(1)[unfolded all_same_arities_def]
        by (auto simp add: Cons.IH)
      done
  qed
qed

lemmas sp_fundef_same_arities = sp_same_arities[THEN eq_sp_to_eq_sp_fundef]

lemma all_same_arities_add:
  assumes "Fubx_get F f = Some fd1" and "arity fd1 = arity fd2"
  shows "all_same_arities (Fubx_get F) (Fubx_get (Fubx_add F f fd2))"
  unfolding  all_same_arities_def
proof (intro allI)
  fix g
  show "rel_option (\<lambda>fd gd. arity fd = arity gd)
           (Fubx_get F g)
           (Fubx_get (Fubx_add F f fd2) g)"
    using assms
    by (cases "f = g") (simp_all add: option.rel_refl)
qed

lemma all_same_arities_generalize_fundef:
  assumes "Fubx_get F f = Some fd"
  shows "all_same_arities (Fubx_get F) (Fubx_get (Fubx_add F f (Subx.generalize_fundef fd)))"
  using all_same_arities_add[OF assms(1)]
  using ubx.arity_generalize_fundef
  by simp

lemma rel_stacktraces_box:
  assumes
    "rel_stacktraces F1 xs ys opt" and
    "F2 f = map_option Subx.generalize_fundef (F1 f)" and
    "\<And>g. f \<noteq> g \<Longrightarrow> F2 g = F1 g" and
    "all_same_arities F1 F2"
  shows "rel_stacktraces F2 xs (Subx.box_stack f ys) opt"
  using assms(1)
proof (induction xs ys opt rule: rel_stacktraces.induct)
  case rel_stacktraces_Nil
  then show ?case
    by (auto intro: rel_stacktraces.intros)
next
  case (rel_stacktraces_Cons st1 st2 g \<Sigma>1 \<Sigma>2 gd n opt)
  note sp_F1_eq_sp_F2[simp] = sp_same_arities[OF assms(4)]
  note sp_fundef_F1_eq_sp_fundef_F2[simp] = eq_sp_to_eq_sp_fundef[OF sp_F1_eq_sp_F2]
  show ?case
    apply simp
  proof (intro conjI impI)
    assume "f = g"
    then have get2_g: "F2 g = Some (Subx.generalize_fundef gd)"
      using assms(2) \<open>F1 g = Some gd\<close> by simp

    show "rel_stacktraces F2 (Frame g n \<Sigma>1 # st1)
      (Frame g n (map Subx.box_operand \<Sigma>2) # Subx.box_stack g st2) opt"
    proof (intro rel_stacktraces.intros)
      show "rel_stacktraces F2 st1 (Subx.box_stack g st2) (Some g)"
        using rel_stacktraces_Cons.IH
        unfolding \<open>f = g\<close>
        by simp
    next
      show "\<Sigma>1 = norm_stack (map Subx.box_operand \<Sigma>2)"
        using \<open>\<Sigma>1 = norm_stack \<Sigma>2\<close> by simp
    next
      show "F2 g = Some (Subx.generalize_fundef gd)"
        using get2_g .
    next
      show "sp_fundef F2 (Subx.generalize_fundef gd) (take n (body (Subx.generalize_fundef gd))) =
        Ok (map typeof (map Subx.box_operand \<Sigma>2))"
        using sp_fundef_generalize[OF rel_stacktraces_Cons.hyps(4)]
        by (simp add: take_map sp_fundef_def)
    next
      show "pred_option
        (is_valid_fun_call F2 (Subx.generalize_fundef gd) n (map Subx.box_operand \<Sigma>2)) opt"
      proof (cases opt)
        case (Some h)
        then show ?thesis
          using rel_stacktraces_Cons.hyps(5)
          apply (simp add: take_map list.pred_map list.pred_True is_valid_fun_call_def)
          using \<open>f = g\<close> assms(3) get2_g by fastforce
      qed simp
    qed
  next
    assume "f \<noteq> g"
    show "rel_stacktraces F2 (Frame g n \<Sigma>1 # st1) (Frame g n \<Sigma>2 # Subx.box_stack f st2) opt"
      using rel_stacktraces_Cons assms(3)[OF \<open>f \<noteq> g\<close>]
      apply (auto intro!: rel_stacktraces.intros;
          cases opt; simp add: sp_fundef_def is_valid_fun_call_def)
      subgoal for h
        using assms(2,3) by (cases "f = h"; auto)
      done
  qed
qed

lemma rel_stacktraces_generalize:
  assumes
    "rel_stacktraces (Fubx_get F) st1 st2 (Some f)" and
    "Fubx_get F f = Some fd " and
    sp_prefix: "sp_fundef (Fubx_get F) fd (take pc (body fd)) = Ok (None # map typeof \<Sigma>2)" and
    norm_stacks: "\<Sigma>1 = norm_stack \<Sigma>2" and
    pc_in_range: "pc < length (body fd)" and
    sp_instr: "Subx.sp_instr (Fubx_get F) (Subx.generalize_instr (body fd ! pc))
      (None # map (\<lambda>_. None) \<Sigma>2) = Ok (None # map (typeof \<circ> Subx.box_operand) \<Sigma>2)"
  shows "rel_stacktraces (Fubx_get (Fubx_add F f (Subx.generalize_fundef fd)))
          (Frame f (Suc pc) (d # \<Sigma>1) # st1)
          (Frame f (Suc pc) (OpDyn d # map Subx.box_operand \<Sigma>2) # Subx.box_stack f st2) None"
proof -
  let ?fd' = "Subx.generalize_fundef fd"
  let ?F' = "Fubx_add F f ?fd'"
  show ?thesis
  proof (intro rel_stacktraces_Cons)
    show "rel_stacktraces (Fubx_get ?F') st1 (Subx.box_stack f st2) (Some f)"
      using assms(2) all_same_arities_generalize_fundef
      by (auto intro: rel_stacktraces_box[OF assms(1)])
  next
    show "d # \<Sigma>1 = norm_stack (OpDyn d # map Subx.box_operand \<Sigma>2)"
      using norm_stacks by simp
  next
    show "Fubx_get ?F' f = Some ?fd'"
      by simp
  next
    show "sp_fundef (Fubx_get ?F') ?fd' (take (Suc pc) (body ?fd')) =
      Ok (map typeof (OpDyn d # map Subx.box_operand \<Sigma>2))"
      unfolding all_same_arities_generalize_fundef[THEN sp_fundef_same_arities,
          OF assms(2), symmetric]
      using sp_fundef_generalize[OF sp_prefix] sp_instr
      by (auto simp add: sp_fundef_def take_map take_Suc_conv_app_nth[OF pc_in_range])
  qed simp_all
qed

lemma rel_fundefs_rewrite:
  assumes
    rel_F1_F2: "rel_fundefs (Finca_get F1) (Fubx_get F2)" and
    F2_get_f: "Fubx_get F2 f = Some fd2" and
    F2_add_f: "Fubx_add F2 f (rewrite_fundef_body fd2 pc instr) = F2'" and
    eq_norm: "norm_instr (body fd2 ! pc) = norm_instr instr"
  shows "rel_fundefs (Finca_get F1) (Fubx_get F2')"
  unfolding rel_fundefs_def
proof
  fix x
  show "rel_option (rel_fundef norm_eq) (Finca_get F1 x) (Fubx_get F2' x)"
  proof (cases "x = f")
    case True
    then have F2'_get_x: "Fubx_get F2' x = Some (rewrite_fundef_body fd2 pc instr)"
      using F2_add_f by auto
    obtain fd1 where "Finca_get F1 f = Some fd1" and rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2 F2_get_f] by auto
    thus ?thesis
      unfolding F2'_get_x option_rel_Some2
      using True rel_fundef_rewrite_body[OF rel_fd1_fd2 eq_norm]
      by auto
  next
    case False
    then have "Fubx_get F2' x = Fubx_get F2 x"
      using F2_add_f by auto
    then show ?thesis
      using rel_F1_F2 rel_fundefs_def
      by fastforce
  qed
qed

lemma rel_fundef_rewrite_both:
  assumes "rel_fundef norm_eq fd1 fd2" and "norm_instr y = x"
  shows "rel_fundef norm_eq (rewrite_fundef_body fd1 pc x) (rewrite_fundef_body fd2 pc y)"
  using assms by (auto simp: fundef.rel_sel)

lemma rel_fundefs_rewrite_both:
  assumes
    rel_init: "rel_fundefs (Finca_get F1) (Fubx_get F2)" and
    rel_new: "rel_fundef norm_eq fd1 fd2"
  shows "rel_fundefs (Finca_get (Finca_add F1 f fd1)) (Fubx_get (Fubx_add F2 f fd2))"
  unfolding rel_fundefs_def
proof
  fix x
  show "rel_option (rel_fundef norm_eq) (Finca_get (Finca_add F1 f fd1) x) (Fubx_get (Fubx_add F2 f fd2) x)"
  proof (cases "x = f")
    case True
    then show ?thesis
      using rel_new by simp
  next
    case False
    then show ?thesis
      using rel_init
      by (simp add: rel_fundefs_def)
  qed
qed

lemma rel_fundefs_generalize:
  assumes
    rel_F1_F2: "rel_fundefs (Finca_get F1) (Fubx_get F2)" and
    F2_get_f: "Fubx_get F2 f = Some fd2"
  shows "rel_fundefs (Finca_get F1) (Fubx_get (Fubx_add F2 f (Subx.generalize_fundef fd2)))"
  unfolding rel_fundefs_def
proof
  let ?F2' = "(Fubx_add F2 f (Subx.generalize_fundef fd2))"
  fix x
  show "rel_option (rel_fundef norm_eq) (Finca_get F1 x) (Fubx_get ?F2' x)"
  proof (cases "x = f")
    case True
    then have F2'_get_x: "Fubx_get ?F2' x = Some (Subx.generalize_fundef fd2)"
      using Subx.Fenv.get_add_eq by auto
    obtain fd1 where "Finca_get F1 f = Some fd1" and "rel_fundef norm_eq fd1 fd2"
      using rel_fundefs_Some2[OF rel_F1_F2 F2_get_f] by auto
    thus ?thesis
      unfolding F2'_get_x option_rel_Some2
      using True rel_fundef_generalize
      by auto
  next
    case False
    then have "Fubx_get ?F2' x = Fubx_get F2 x"
      using Subx.Fenv.get_add_neq by auto
    then show ?thesis
      using rel_F1_F2 rel_fundefs_def
      by fastforce
  qed
qed

lemma rel_stacktraces_rewrite_fundef:
  assumes
    "rel_stacktraces (Fubx_get F2) xs ys opt" and
    "Fubx_get F2 f = Some fd" and
    "pc < length (body fd)" and
    "\<forall>\<Sigma>. Subx.sp_instr (Fubx_get F2) (body fd ! pc) \<Sigma> = Subx.sp_instr (Fubx_get F2) instr \<Sigma>" and
    "\<not> is_fun_call (body fd ! pc)"
  shows "rel_stacktraces
     (Fubx_get (Fubx_add F2 f (rewrite_fundef_body fd pc instr))) xs ys opt"
  using assms(1)
proof (induction xs ys opt rule: rel_stacktraces.induct)
  case rel_stacktraces_Nil
  then show ?case
    by (auto intro: rel_stacktraces.intros)
next
  case (rel_stacktraces_Cons st1 st2 g \<Sigma>1 \<Sigma>2 gd n opt)
  have same_arities: "all_same_arities (Fubx_get F2)
    (Fubx_get (Fubx_add F2 f (rewrite_fundef_body fd pc instr)))"
    using all_same_arities_add[OF assms(2)]
    by simp

  show ?case
  proof (cases "g = f")
    case True
    then have "gd = fd"
      using assms(2) rel_stacktraces_Cons.hyps(3) by auto
    thus ?thesis
      using True rel_stacktraces_Cons
      apply (auto intro!: rel_stacktraces.intros
        simp: sp_fundef_same_arities[OF same_arities, symmetric])
      apply (cases "n \<le> pc"; simp add: sp_fundef_def)
      subgoal
        using assms(3,4)
        by (simp add: Subx.sp_rewrite_eq_Ok take_rewrite_swap)
      subgoal
         using rel_stacktraces_Cons.hyps(5)
       proof (induction opt)
         case (Some h)
         hence "rewrite (body fd) pc instr ! n = Ubx.ICall h"
           using \<open>gd = fd\<close>
           apply (simp add: is_valid_fun_call_def)
           by (metis assms(5) instr.disc nth_rewrite_neq)
         then show ?case
           using Some \<open>gd = fd\<close>
           apply (simp add: is_valid_fun_call_def)
           by (metis arity_rewrite_fundef_body assms(2) option.inject Subx.Fenv.get_add_eq Subx.Fenv.get_add_neq)
       qed simp
       done
  next
    case False
    thus ?thesis
      using rel_stacktraces_Cons
      apply (auto intro!: rel_stacktraces.intros
        simp: sp_fundef_same_arities[OF same_arities, symmetric])
    proof (induction opt)
      case (Some h)
      then show ?case
        using Some assms(2)
        by (cases "h = f"; simp add: is_valid_fun_call_def)
    qed simp
  qed
qed


section \<open>Matching relation\<close>

lemma sp_fundefs_get:
  assumes "sp_fundefs F" and "F f = Some fd"
  shows "sp_fundef F fd (body fd) = Ok [None]"
  using assms by (simp add: sp_fundefs_def)

lemma sp_fundefs_generalize:
  assumes "sp_fundefs (Fubx_get F)" and "Fubx_get F f = Some fd"
  shows "sp_fundefs (Fubx_get (Fubx_add F f (Subx.generalize_fundef fd)))"
  unfolding sp_fundefs_def
proof (intro allI impI)
  fix g gd
  assume get_g: "Fubx_get (Fubx_add F f (Subx.generalize_fundef fd)) g = Some gd"
  note sp_F_eq_sp_F' = all_same_arities_generalize_fundef[OF assms(2), THEN sp_same_arities, symmetric]
  show "sp_fundef (Fubx_get (Fubx_add F f (Subx.generalize_fundef fd))) gd (body gd) = Ok [None]"
  proof (cases "f = g")
    case True
    then have "gd = Subx.generalize_fundef fd"
      using get_g by simp
    then show ?thesis
      using assms
      by (simp add: sp_fundefs_def sp_fundef_def sp_F_eq_sp_F' Subx.sp_generalize2)
  next
    case False
    then show ?thesis
      using get_g assms
      by (simp add: sp_fundefs_def sp_fundef_def sp_F_eq_sp_F')
  qed
qed

lemma sp_fundefs_add:
  assumes
    "sp_fundefs (Fubx_get F)" and
    "sp_fundef (Fubx_get F) fd (body fd) = Ok [None]" and
    "all_same_arities (Fubx_get F) (Fubx_get (Fubx_add F f fd))"
  shows "sp_fundefs (Fubx_get (Fubx_add F f fd))"
  unfolding sp_fundefs_def
proof (intro allI impI)
  fix g gd
  assume "Fubx_get (Fubx_add F f fd) g = Some gd"
  show "sp_fundef (Fubx_get (Fubx_add F f fd)) gd (body gd) = Ok [None]"
  proof (cases "f = g")
    case True
    then have "gd = fd"
      using \<open>Fubx_get (Fubx_add F f fd) g = Some gd\<close> by simp
    then show ?thesis
      unfolding sp_fundef_same_arities[OF assms(3), symmetric]
      using assms(2) by simp 
  next
    case False
    then show ?thesis
      unfolding sp_fundef_same_arities[OF assms(3), symmetric]
      using \<open>Fubx_get (Fubx_add F f fd) g = Some gd\<close>
      using sp_fundefs_get[OF assms(1)]
      by simp
  qed
qed

inductive match (infix "\<sim>" 55) where
  "rel_fundefs (Finca_get F1) (Fubx_get F2) \<Longrightarrow>
  sp_fundefs (Fubx_get F2) \<Longrightarrow>
  rel_stacktraces (Fubx_get F2) st1 st2 None \<Longrightarrow>
  match (State F1 H st1) (State F2 H st2)"


section \<open>Backward simulation\<close>

lemma traverse_cast_Dyn_to_norm: "traverse cast_Dyn xs = Some ys \<Longrightarrow> norm_stack xs = ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems show ?case
    by (auto intro: Cons.IH elim: cast_Dyn.elims simp: Option.bind_eq_Some_conv)
qed

lemma traverse_cast_Dyn_to_all_Dyn:
  "traverse cast_Dyn xs = Some ys \<Longrightarrow> list_all (\<lambda>x. typeof x = None) xs"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems show ?case
    by (auto intro: Cons.IH elim: cast_Dyn.elims simp: Option.bind_eq_Some_conv)
qed

lemma backward_lockstep_simulation:
  assumes "Subx.step s2 s2'" and "s1 \<sim> s2"
  shows "\<exists>s1'. Sinca.step s1 s1' \<and> s1' \<sim> s2'"
  using assms(2,1)
proof (induction s1 s2 rule: match.induct)
  case (1 F1 F2 st1 st2 H)
  have rel_F1_F2: "rel_fundefs (Finca_get F1) (Fubx_get F2)" using 1 by simp
  have sp_F2: "sp_fundefs (Fubx_get F2)" using 1 by simp

  from "1"(3,4) show ?case
  proof (induction st1 st2 "None :: 'fun option" rule: rel_stacktraces.induct)
    case rel_stacktraces_Nil
    hence False by (auto elim: Subx.step.cases)
    thus ?case by simp
  next
    case (rel_stacktraces_Cons st1 st2 f \<Sigma>1 \<Sigma>2 fd2 pc)
    have F2_f: "Fubx_get F2 f = Some fd2"
      using rel_stacktraces_Cons by simp
    have rel_st1_st2: "rel_stacktraces (Fubx_get F2) st1 st2 (Some f)"
      using rel_stacktraces_Cons by simp
    have sp_fundef_prefix: "sp_fundef (Fubx_get F2) fd2 (take pc (body fd2)) = Ok (map typeof \<Sigma>2)"
      using rel_stacktraces_Cons by simp
    have \<Sigma>1_def: "\<Sigma>1 = norm_stack \<Sigma>2"
      using rel_stacktraces_Cons by simp

    note sp_fundef_def[simp]
    note sp_prefix = sp_fundef_prefix[unfolded sp_fundef_def]

    have sp_generalized: "Subx.sp (Fubx_get (Fubx_add F2 f (Subx.generalize_fundef fd2)))
      (map Subx.generalize_instr (take pc (body fd2))) (replicate (arity fd2) None) =
      Ok (map (\<lambda>_. None) \<Sigma>2)"
      using Subx.sp_generalize[OF sp_prefix, simplified]
      using all_same_arities_generalize_fundef[OF F2_f]
      by (simp add: sp_same_arities)
    
    from rel_stacktraces_Cons.prems(1) show ?case
    proof (induction "State F2 H (Frame f pc \<Sigma>2 # st2)" s2' rule: Subx.step.induct)
      case (step_push fd2' d)
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where fd1_thms: "Finca_get F1 f = Some fd1" "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (d # \<Sigma>1) # st1)"
        have "?STEP ?s1'"
          using step_push fd1_thms
          by (auto intro: Sinca.step_push simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
          using step_push rel_stacktraces_Cons rel_F1_F2 sp_F2
          by (auto intro!: match.intros intro: rel_stacktraces.intros simp: take_Suc_conv_app_nth)
        ultimately show "?thesis" by blast
      qed
    next
      case (step_push_ubx1 fd2' n)
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where fd1_thms: "Finca_get F1 f = Some fd1" "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (box_ubx1 n # \<Sigma>1) # st1)"
        have "?STEP ?s1'"
          using step_push_ubx1 fd1_thms
          by (auto intro: Sinca.step_push simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
          using step_push_ubx1 rel_stacktraces_Cons rel_F1_F2 sp_F2
          by (auto intro!: match.intros intro: rel_stacktraces.intros simp: take_Suc_conv_app_nth)
        ultimately show "?thesis" by blast
      qed
    next
      case (step_push_ubx2 fd2' b)
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where fd1_thms: "Finca_get F1 f = Some fd1" "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (box_ubx2 b # \<Sigma>1) # st1)"
        have "?STEP ?s1'"
          using step_push_ubx2 fd1_thms
          by (auto intro: Sinca.step_push simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
          using step_push_ubx2 rel_stacktraces_Cons rel_F1_F2 sp_F2
          by (auto intro!: match.intros intro: rel_stacktraces.intros simp: take_Suc_conv_app_nth)
        ultimately show "?thesis" by blast
      qed
    next
      case (step_pop fd2' x \<Sigma>2')
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where fd1_thms: "Finca_get F1 f = Some fd1" "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (norm_stack \<Sigma>2') # st1)"
        have "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_pop fd1_thms
          by (auto intro!: Sinca.step_pop simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
          using step_pop rel_stacktraces_Cons rel_F1_F2 sp_F2
          by (auto intro!: match.intros intro: rel_stacktraces.intros simp: take_Suc_conv_app_nth)
        ultimately show "?thesis" by blast
      qed
    next
      case (step_load fd2' x i i' d \<Sigma>2')
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where
        F1_f: "Finca_get F1 f = Some fd1" and
        rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (d # norm_stack \<Sigma>2') # st1)"
        have pc_in_range: "pc < length (body fd1)"
          using rel_fd1_fd2 step_load(2) by simp
        have "?STEP ?s1'"
          using step_load rel_fundef_body_nth[OF rel_fd1_fd2 pc_in_range]
          by (auto intro!: Sinca.step_load[OF F1_f pc_in_range, of x]
                dest: cast_inversions(1)
                simp: \<Sigma>1_def)
        moreover have "?MATCH ?s1'"
          using step_load refl rel_stacktraces_Cons rel_F1_F2 sp_F2
          by (auto intro!: match.intros intro: rel_stacktraces.intros(2)[OF rel_st1_st2]
              dest!: cast_inversions(1)
              simp: take_Suc_conv_app_nth[OF step_load(2), simplified])
        ultimately show "?thesis" by blast
      qed
    next
      case (step_load_ubx_hit fd2' \<tau> x i i' d blob \<Sigma>2')
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where
        F1_f: "Finca_get F1 f = Some fd1" and
        rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (d # norm_stack \<Sigma>2') # st1)"
        have pc_in_range: "pc < length (body fd1)"
          using rel_fd1_fd2 step_load_ubx_hit(2) by simp
        have "?STEP ?s1'"
          using step_load_ubx_hit rel_fundef_body_nth[OF rel_fd1_fd2 pc_in_range]
          by (auto intro!: Sinca.step_load[OF F1_f pc_in_range, of x]
              dest: cast_inversions(1)
              simp: rel_fundef_body_nth \<Sigma>1_def)
        moreover have "?MATCH ?s1'"
          using step_load_ubx_hit rel_stacktraces_Cons rel_F1_F2 sp_F2
          by (auto intro!: match.intros intro: rel_stacktraces.intros(2)[OF rel_st1_st2]
              dest!: cast_inversions(1)
              simp: take_Suc_conv_app_nth[OF step_load_ubx_hit(2), simplified])
        ultimately show "?thesis" by blast
      qed
    next
      case (step_load_ubx_miss fd2' \<tau> x i i' d F2' \<Sigma>2')
      then have fd2'_def[simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where
        F1_f: "Finca_get F1 f = Some fd1" and
        rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (d # norm_stack \<Sigma>2') # st1)"
        have pc_in_range: "pc < length (body fd1)"
          using rel_fd1_fd2 step_load_ubx_miss(2) by simp
        have "?STEP ?s1'"
          using step_load_ubx_miss F1_f rel_fd1_fd2
          by (auto intro!: Sinca.step_load[OF F1_f pc_in_range, of x]
              dest!: cast_inversions(1)
              simp: rel_fundef_body_nth \<Sigma>1_def)
        moreover have "?MATCH ?s1'"
        proof (rule match.intros)
          show "rel_fundefs (Finca_get F1) (Fubx_get F2')"
            unfolding step_load_ubx_miss.hyps(7)[symmetric]
            using rel_fundefs_generalize[OF rel_F1_F2 F2_f]
            by simp
        next
          show "sp_fundefs (Fubx_get F2')"
            unfolding step_load_ubx_miss.hyps(7)[symmetric]
            using sp_fundefs_generalize[OF sp_F2 F2_f]
            by simp
        next
          show "rel_stacktraces (Fubx_get F2')
            (Frame f (Suc pc) (d # norm_stack \<Sigma>2') # st1)
            (Subx.box_stack f (Frame f (Suc pc) (OpDyn d # \<Sigma>2') # st2)) None"
            using step_load_ubx_miss sp_fundef_prefix
            by (auto intro!: rel_stacktraces_generalize[OF rel_st1_st2 F2_f] dest: cast_inversions)
        qed
        ultimately show "?thesis" by blast
      qed
    next
      case (step_store fd2' x i i' y d H' \<Sigma>2')
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where fd1_thms: "Finca_get F1 f = Some fd1" "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H' (Frame f (Suc pc) (norm_stack \<Sigma>2') # st1)"
        have "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_store fd1_thms
          by (auto intro!: Sinca.step_store dest!: cast_inversions
              simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
          using step_store rel_stacktraces_Cons rel_F1_F2 sp_F2
          by (auto intro!: match.intros rel_stacktraces.intros dest!: cast_inversions
              simp: take_Suc_conv_app_nth)
        ultimately show "?thesis" by blast
      qed
    next
      case (step_store_ubx fd2' \<tau> x i i' blob d H' \<Sigma>2')
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where
        F1_f: "Finca_get F1 f = Some fd1" and
        rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H' (Frame f (Suc pc) (norm_stack \<Sigma>2') # st1)"
        have pc_in_range: "pc < length (body fd1)"
          using rel_fd1_fd2 step_store_ubx.hyps(2) by auto
        have "?STEP ?s1'"
          unfolding \<Sigma>1_def \<open>i # blob # \<Sigma>2' = \<Sigma>2\<close>[symmetric]
          using step_store_ubx pc_in_range
          by (auto intro!: Sinca.step_store[OF F1_f]
              dest!: cast_inversions
              simp: rel_fundef_body_nth[OF rel_fd1_fd2])
        moreover have "?MATCH ?s1'"
          using step_store_ubx rel_stacktraces_Cons rel_F1_F2 sp_F2
          by (auto intro!: match.intros rel_stacktraces.intros
              dest!: cast_inversions
              simp: take_Suc_conv_app_nth)
        ultimately show "?thesis" by blast
      qed
    next
      case (step_op fd2' op ar \<Sigma>2' x)
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where fd1_thms: "Finca_get F1 f = Some fd1" "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (x # drop ar (norm_stack \<Sigma>2)) # st1)"
        have "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op fd1_thms take_norm_stack traverse_cast_Dyn_to_norm
          by (auto intro!: Sinca.step_op simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
          using step_op rel_stacktraces_Cons rel_F1_F2 sp_F2 
          by (auto intro!: match.intros rel_stacktraces.intros
              simp: take_Suc_conv_app_nth drop_norm_stack Let_def take_map drop_map
                traverse_cast_Dyn_replicate)
        ultimately show "?thesis" by blast
      qed    
    next
      case (step_op_inl fd2' op ar \<Sigma>2' opinl x F2')
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where
        F1_f: "Finca_get F1 f = Some fd1" and
        rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?F1' = "Finca_add F1 f (rewrite_fundef_body fd1 pc (Inca.IOpInl opinl))"
        let ?s1' = "State ?F1' H (Frame f (Suc pc) (x # drop ar (norm_stack \<Sigma>2)) # st1)"
        have "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op_inl F1_f rel_fd1_fd2 take_norm_stack traverse_cast_Dyn_to_norm
          by (auto intro!: Sinca.step_op_inl simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
        proof
          show "rel_fundefs (Finca_get ?F1') (Fubx_get F2')"
            using step_op_inl.hyps(9)
            using rel_fundefs_rewrite_both[OF rel_F1_F2]
            using rel_fundef_rewrite_both[OF rel_fd1_fd2]
            by auto
        next
          show "sp_fundefs (Fubx_get F2')"
            using step_op_inl.hyps all_same_arities_add sp_fundefs_get[OF sp_F2]
            using Sinca.\<II>\<nn>\<ll>_invertible
            by (auto intro!: sp_fundefs_add[OF sp_F2] Subx.sp_rewrite_eq_Ok
                simp: Subx.sp_instr_op Let_def)
        next
          have sp_F2_F2': "Subx.sp (Fubx_get F2) = Subx.sp (Fubx_get F2')"
            using step_op_inl.hyps(1,9)
            by (auto intro!: sp_same_arities all_same_arities_add)
          
          let ?fd2' = "rewrite_fundef_body fd2' pc (Ubx.IOpInl opinl)"
          
          show "rel_stacktraces (Fubx_get F2')
            (Frame f (Suc pc) (x # drop ar (norm_stack \<Sigma>2)) # st1)
            (Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>2) # st2) None"
            using step_op_inl
          proof (intro rel_stacktraces.intros)
            show "rel_stacktraces (Fubx_get F2') st1 st2 (Some f)"
              using step_op_inl Sinca.\<II>\<nn>\<ll>_invertible
              by (auto intro!: rel_stacktraces_rewrite_fundef[OF rel_st1_st2] simp: Subx.sp_instr_op)
          next
            show "sp_fundef (Fubx_get F2') ?fd2' (take (Suc pc) (body ?fd2'))  =
              Ok (map typeof (OpDyn x # drop ar \<Sigma>2))"
              using step_op_inl Sinca.\<II>\<nn>\<ll>_invertible sp_prefix
              using traverse_cast_Dyn_to_all_Dyn
              by (auto simp: take_Suc_conv_app_nth[of pc] sp_F2_F2'[symmetric] Let_def
                    take_map drop_map traverse_cast_Dyn_replicate)
          qed (auto simp add: drop_norm_stack)
        qed
        ultimately show "?thesis" by blast
      qed
    next
      case (step_op_inl_hit fd2' opinl ar \<Sigma>2' x)
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where fd1_thms: "Finca_get F1 f = Some fd1" "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (x # drop ar (norm_stack \<Sigma>2)) # st1)"
        have "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op_inl_hit fd1_thms take_norm_stack traverse_cast_Dyn_to_norm
          by (auto intro!: Sinca.step_op_inl_hit simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
          using step_op_inl_hit rel_stacktraces_Cons rel_F1_F2 sp_F2
          apply (auto intro!: match.intros rel_stacktraces.intros simp: take_Suc_conv_app_nth)
          using drop_norm_stack apply blast
          by (simp add: Let_def drop_map take_map traverse_cast_Dyn_replicate)
        ultimately show "?thesis" by blast
      qed
    next
      case (step_op_inl_miss fd2' opinl ar \<Sigma>2' x F2')
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where
        F1_f: "Finca_get F1 f = Some fd1" and
        rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?F1' = "Finca_add F1 f (rewrite_fundef_body fd1 pc (Inca.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl)))"
        let ?s1' = "State ?F1' H (Frame f (Suc pc) (x # drop ar (norm_stack \<Sigma>2)) # st1)"
        have "?STEP ?s1'"
          unfolding \<Sigma>1_def
          using step_op_inl_miss F1_f rel_fd1_fd2 take_norm_stack traverse_cast_Dyn_to_norm
          by (auto intro!: Sinca.step_op_inl_miss simp: rel_fundef_body_nth)
        moreover have "?MATCH ?s1'"
        proof
          show "rel_fundefs (Finca_get ?F1') (Fubx_get F2')"
            using step_op_inl_miss
            using rel_fundefs_rewrite_both[OF rel_F1_F2]
            using rel_fundef_rewrite_both[OF rel_fd1_fd2]
            by auto
        next
          show "sp_fundefs (Fubx_get F2')"
            using step_op_inl_miss.hyps all_same_arities_add sp_fundefs_get[OF sp_F2] 
            by (auto intro!: sp_fundefs_add[OF sp_F2] Subx.sp_rewrite_eq_Ok
                simp: Subx.sp_instr_op[symmetric])
        next
          have sp_F2_F2': "Subx.sp (Fubx_get F2) = Subx.sp (Fubx_get F2')"
            using step_op_inl_miss
            by (auto intro!: sp_same_arities all_same_arities_add)

          let ?fd2' = "rewrite_fundef_body fd2' pc (Ubx.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl))"

          show "rel_stacktraces (Fubx_get F2')
            (Frame f (Suc pc) (x # drop ar (norm_stack \<Sigma>2)) # st1)
            (Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>2) # st2) None"
          proof
            show "rel_stacktraces (Fubx_get F2') st1 st2 (Some f)"
              using step_op_inl_miss.hyps
              by (auto intro: rel_stacktraces_rewrite_fundef[OF rel_st1_st2] simp: Subx.sp_instr_op[symmetric])
          next
            show "Fubx_get F2' f = Some ?fd2'"
              using step_op_inl_miss Subx.Fenv.get_add_eq by blast
          next
            show "sp_fundef (Fubx_get F2') ?fd2' (take (Suc pc) (body ?fd2')) =
              Ok (map typeof (OpDyn x # drop ar \<Sigma>2))"
              using \<open>pc < length (body fd2')\<close>
              using sp_prefix step_op_inl_miss traverse_cast_Dyn_to_all_Dyn
              by (auto simp add: take_Suc_conv_app_nth[of pc] sp_F2_F2'[symmetric]
                  traverse_cast_Dyn_replicate take_map drop_map)
          qed (simp_all add: drop_norm_stack)
        qed
        ultimately show "?thesis" by blast
      qed
    next
      case (step_op_ubx fd2' opubx op ar x)
      then have [simp]: "fd2' = fd2" using F2_f by simp
      obtain fd1 where fd1_thms: "Finca_get F1 f = Some fd1" "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame f (Suc pc) (Subx.norm_unboxed x # drop ar (norm_stack \<Sigma>2)) # st1)"
        have "pc < length (body fd1)"
          using fd1_thms(2) step_op_ubx.hyps(2) by auto
        hence nth_fd1: "body fd1 ! pc = Inca.instr.IOpInl (\<BB>\<oo>\<xx> opubx)"
          using rel_fundef_body_nth[OF fd1_thms(2)]
          using \<open>body fd2' ! pc = IOpUbx opubx\<close>
          by simp
        have "\<II>\<ss>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx) (take ar (map Subx.norm_unboxed \<Sigma>2))"
          using step_op_ubx
          by (auto intro: Sinca.\<II>\<nn>\<ll>_\<II>\<ss>\<II>\<nn>\<ll> Subx.\<UU>\<bb>\<xx>\<OO>\<pp>_to_\<II>\<nn>\<ll> simp: take_map)
        hence "?STEP ?s1'"
          unfolding norm_stack_def \<Sigma>1_def
          using step_op_ubx fd1_thms(1) nth_fd1 \<open>pc < length (body fd1)\<close>
          using Subx.\<UU>\<bb>\<xx>\<OO>\<pp>_correct
          by (auto intro!: Sinca.step_op_inl_hit simp: take_map)
        moreover have "?MATCH ?s1'"
          using step_op_ubx rel_stacktraces_Cons rel_F1_F2 sp_F2 Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_complete
          by (auto intro!: match.intros rel_stacktraces.intros
              simp: take_Suc_conv_app_nth drop_norm_stack Let_def drop_map take_map min.absorb2)
        ultimately show "?thesis" by blast
      qed
    next
      case (step_cjump_true fd2' n x \<Sigma>2')
      then have False
        using F2_f sp_fundefs_get[OF sp_F2, unfolded sp_fundef_def, THEN Subx.sp_no_jump] nth_mem
        by force
      thus ?case by simp
    next
      case (step_cjump_false fd2' n x \<Sigma>2')
      then have False
        using F2_f sp_fundefs_get[OF sp_F2, unfolded sp_fundef_def, THEN Subx.sp_no_jump] nth_mem
        by force
      thus ?case by simp
    next
      case (step_fun_call f' fd2' pc' g gd2 ar \<Sigma>2' frame\<^sub>g)
      then have [simp]: "f' = f" "pc' = pc" "fd2' = fd2" using F2_f by auto
      obtain fd1 where "Finca_get F1 f = Some fd1" and rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      obtain gd1 where "Finca_get F1 g = Some gd1" and rel_gd1_gd2: "rel_fundef norm_eq gd1 gd2"
        using step_fun_call rel_fundefs_Some2[OF rel_F1_F2] by blast
      have pc_in_range: "pc < length (body fd1)"
        using \<open>pc' < length (body fd2')\<close> rel_fundef_body_length[OF rel_fd1_fd2]
        by simp
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame g 0 (take (arity gd1) \<Sigma>1) # Frame f pc \<Sigma>1 # st1)"
        have "?STEP ?s1'"
          using step_fun_call rel_stacktraces_Cons.hyps(2) pc_in_range
          using \<open>Finca_get F1 f = Some fd1\<close> \<open>Finca_get F1 g = Some gd1\<close>
          using rel_fundef_body_nth[OF rel_fd1_fd2]
          using rel_fundef_arities[OF rel_gd1_gd2, symmetric]
          by (auto intro!: Sinca.step_fun_call)
        moreover have "?MATCH ?s1'"
        proof
          show "rel_fundefs (Finca_get F1) (Fubx_get F2)"
            using rel_F1_F2 .
        next
          show "sp_fundefs (Fubx_get F2)"
            using sp_F2 .
        next
          show "rel_stacktraces (Fubx_get F2)
            (Frame g 0 (take (arity gd1) \<Sigma>1) # Frame f pc \<Sigma>1 # st1)
            (frame\<^sub>g # Frame f pc \<Sigma>2 # st2) None"
            unfolding step_fun_call(9)
          proof (rule rel_stacktraces.intros(2))
            show "rel_stacktraces (Fubx_get F2) (Frame f pc \<Sigma>1 # st1) (Frame f pc \<Sigma>2 # st2) (Some g)"
              using rel_st1_st2 F2_f \<Sigma>1_def sp_prefix
              using step_fun_call
              by (auto intro!: rel_stacktraces.intros
                  elim!: list.pred_mono_strong simp: is_valid_fun_call_def)
          next
            show "take (arity gd1) \<Sigma>1 = norm_stack (take ar \<Sigma>2')"
              using \<Sigma>1_def rel_fundef_arities[OF rel_gd1_gd2]
              using step_fun_call by (simp add: take_norm_stack)
          next
            show "Fubx_get F2 g = Some gd2"
              using step_fun_call by simp
          next
            show "sp_fundef (Fubx_get F2) gd2 (take 0 (body gd2)) = Ok (map typeof (take ar \<Sigma>2'))"
              using step_fun_call
              by (auto elim: replicate_eq_map)
          qed simp_all
        qed
        ultimately show "?thesis" by blast
      qed
    next
      case (step_fun_end f' fd2' \<Sigma>2\<^sub>g pc' \<Sigma>2' frame\<^sub>g g pc\<^sub>g frame\<^sub>g' st2')
      then have [simp]: "f' = f" "fd2' = fd2" "pc' = pc" "\<Sigma>2' = \<Sigma>2" using F2_f by auto
      obtain fd1 where "Finca_get F1 f = Some fd1" and rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using rel_fundefs_Some2[OF rel_F1_F2 F2_f] by auto
      obtain gd2 \<Sigma>1\<^sub>g st1' where
        st1_def: "st1 = Frame g pc\<^sub>g \<Sigma>1\<^sub>g # st1'" and
        "\<Sigma>1\<^sub>g = norm_stack \<Sigma>2\<^sub>g" and
        rel_st1'_st2': "rel_stacktraces (Fubx_get F2) st1' st2' (Some g)" and
        "Fubx_get F2 g = Some gd2" and
        sp_prefix_gd2: "Subx.sp (Fubx_get F2) (take pc\<^sub>g (body gd2))
          (replicate (arity gd2) None) = Ok (map typeof \<Sigma>2\<^sub>g)" and
        pc\<^sub>g_in_range: "pc\<^sub>g < length (body gd2)" and
        "body gd2 ! pc\<^sub>g = Ubx.ICall f" and
        prefix_all_dyn_\<Sigma>2\<^sub>g: "list_all is_dyn_operand (take (arity fd2) \<Sigma>2\<^sub>g)"
        using rel_st1_st2 step_fun_end
        by (auto elim: rel_stacktraces.cases simp: is_valid_fun_call_def)
      have pc_at_end: "pc = length (body fd1)"
        using \<open>pc' = length (body fd2')\<close>
        using rel_fundef_body_length[OF rel_fd1_fd2]
        by simp
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F1 H (Frame g (Suc pc\<^sub>g) (\<Sigma>1 @ drop (arity fd1) \<Sigma>1\<^sub>g) # st1')"
        have "?STEP ?s1'"
          using step_fun_end.hyps(2)
          using st1_def \<open>\<Sigma>1\<^sub>g = norm_stack \<Sigma>2\<^sub>g\<close>
          using \<open>Finca_get F1 f = Some fd1\<close> pc_at_end
          using rel_fundef_arities[OF rel_fd1_fd2, symmetric]
          by (auto intro!: Sinca.step_fun_end)
        moreover have "?MATCH ?s1'"
          using rel_F1_F2 sp_F2
        proof
          show "rel_stacktraces (Fubx_get F2)
            (Frame g (Suc pc\<^sub>g) (\<Sigma>1 @ drop (arity fd1) \<Sigma>1\<^sub>g) # st1')
            (frame\<^sub>g' # st2') None"
            unfolding step_fun_end(6)
            using rel_st1'_st2'
          proof (rule rel_stacktraces.rel_stacktraces_Cons)
            show "\<Sigma>1 @ drop (arity fd1) \<Sigma>1\<^sub>g = norm_stack (\<Sigma>2' @ drop (arity fd2') \<Sigma>2\<^sub>g)"
              using \<Sigma>1_def \<open>\<Sigma>1\<^sub>g = norm_stack \<Sigma>2\<^sub>g\<close>
              using rel_fundef_arities[OF rel_fd1_fd2]
              by (simp add: norm_stack_append drop_norm_stack)
          next
            show "Fubx_get F2 g = Some gd2"
              using \<open>Fubx_get F2 g = Some gd2\<close> .
          next
            have "arity fd2 \<le> length \<Sigma>2\<^sub>g"
              using step_fun_end.hyps(2) by simp
            moreover have "list_all (\<lambda>x. x = None) (take (arity fd2) (map typeof \<Sigma>2\<^sub>g))"
              using prefix_all_dyn_\<Sigma>2\<^sub>g
              by (auto elim!: list.pred_mono_strong simp: take_map list.pred_map is_dyn_operand_def)
            moreover have "map typeof \<Sigma>2 = [None]"
              using \<open>pc' = length (body fd2')\<close> sp_prefix
              using sp_fundefs_get[OF sp_F2 F2_f] 
              by simp
            ultimately show "sp_fundef (Fubx_get F2) gd2 (take (Suc pc\<^sub>g) (body gd2)) =
              Ok (map typeof (\<Sigma>2' @ drop (arity fd2') \<Sigma>2\<^sub>g))"
              using sp_prefix_gd2
              using \<open>body gd2 ! pc\<^sub>g = Ubx.ICall f\<close> F2_f
              by (auto dest: list_all_eq_const_imp_replicate
                  simp: take_Suc_conv_app_nth[OF pc\<^sub>g_in_range] Let_def drop_map)
          qed simp
        qed
        ultimately show "?thesis" by blast
      qed
    qed
  qed
qed

lemma match_final_backward:
  "s1 \<sim> s2 \<Longrightarrow> Subx.final s2 \<Longrightarrow> Sinca.final s1"
proof (induction s1 s2 rule: match.induct)
  case (1 F1 F2 st1 st2 H)
  obtain f fd2 pc \<Sigma>2 where
    st2_def: "st2 = [Frame f pc \<Sigma>2]" and "Fubx_get F2 f = Some fd2" and "pc = length (body fd2)"
    using \<open>Subx.final (State F2 H st2)\<close>
    by (auto elim!: Subx.final.cases)
  obtain \<Sigma>1 where st1_def: "st1 = [Frame f pc \<Sigma>1]"
    using \<open>rel_stacktraces (Fubx_get F2) st1 st2 None\<close>
    unfolding st2_def
    by (auto elim!: rel_stacktraces.cases)
  obtain fd1 where "Finca_get F1 f = Some fd1" and rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
    using \<open>rel_fundefs (Finca_get F1) (Fubx_get F2)\<close> \<open>Fubx_get F2 f = Some fd2\<close>
    using rel_fundefs_Some2
    by fastforce
  have "length (body fd1) = length (body fd2)"
    using rel_fd1_fd2 by simp
  thus ?case
    unfolding st1_def
    using \<open>Finca_get F1 f = Some fd1\<close> \<open>pc = length (body fd2)\<close>
    by (auto intro: Sinca.final.intros)
qed

sublocale inca_to_ubx_simulation:
  backward_simulation Sinca.step Subx.step Sinca.final Subx.final "\<lambda>_ _. False" "\<lambda>_. match"
  using match_final_backward backward_lockstep_simulation
   lockstep_to_plus_backward_simulation[of match Subx.step Sinca.step]
  by unfold_locales auto


section \<open>Forward simulation\<close>

lemma traverse_cast_Dyn_eq_norm_stack:
  assumes "list_all (\<lambda>x. x = None) (map typeof xs)"
  shows "traverse cast_Dyn xs = Some (norm_stack xs)"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems have
    typeof_x: "typeof x = None" and
    typeof_xs: "list_all (\<lambda>x. x = None) (map typeof xs)"
    by simp_all
  obtain x' where "x = OpDyn x'"
    using typeof_unboxed_inversion(1)[OF typeof_x] by auto
  then show ?case
    using Cons.IH[OF typeof_xs]
    by simp
qed

lemma forward_lockstep_simulation:
  assumes "Sinca.step s1 s1'" and "s1 \<sim> s2"
  shows "\<exists>s2'. Subx.step s2 s2' \<and> s1' \<sim> s2'"
  using assms(2,1)
proof (induction s1 s2 rule: match.induct)
  case (1 F1 F2 st1 st2 H)
  have rel_F1_F2: "rel_fundefs (Finca_get F1) (Fubx_get F2)" using 1 by simp
  have sp_F2: "sp_fundefs (Fubx_get F2)" using 1 by simp

  note rel_fundefs_rewrite_both' =
    rel_fundef_rewrite_both[THEN rel_fundefs_rewrite_both[OF rel_F1_F2]]

  from "1"(3,4) show ?case
  proof (induction st1 st2 "None :: 'fun option" rule: rel_stacktraces.induct)
    case rel_stacktraces_Nil
    hence False by (auto elim: Sinca.step.cases)
    thus ?case by simp
  next
    case (rel_stacktraces_Cons st1 st2 f \<Sigma>1 \<Sigma>2 fd2 pc)
    have F2_f: "Fubx_get F2 f = Some fd2"
      using rel_stacktraces_Cons by simp
    have rel_st1_st2: "rel_stacktraces (Fubx_get F2) st1 st2 (Some f)"
      using rel_stacktraces_Cons by simp
    have sp_fundef_prefix: "sp_fundef (Fubx_get F2) fd2 (take pc (body fd2)) = Ok (map typeof \<Sigma>2)"
      using rel_stacktraces_Cons by simp
    have \<Sigma>1_def: "\<Sigma>1 = norm_stack \<Sigma>2"
      using rel_stacktraces_Cons by simp

    note sp_fundef_def[simp]
    note sp_prefix = sp_fundef_prefix[unfolded sp_fundef_def]

    note ex_F1_f = rel_fundefs_Some2[OF rel_F1_F2 F2_f]
    note sp_fundef_full = sp_fundefs_get[OF sp_F2 \<open>Fubx_get F2 f = Some fd2\<close>]
    note sp_full = sp_fundef_full[unfolded sp_fundef_def]
    hence sp_sufix: "Subx.sp (Fubx_get F2)
      (body fd2 ! pc # drop (Suc pc) (body fd2)) (map typeof \<Sigma>2) = Ok [None]"
      if pc_in_range: "pc < length (body fd2)"
      unfolding Cons_nth_drop_Suc[OF pc_in_range]
      unfolding Subx.sp_eq_bind_take_drop[of _ "body fd2" _ pc]
      unfolding sp_prefix
      by simp

    from rel_stacktraces_Cons.prems(1) show ?case
    proof (induction "State F1 H (Frame f pc \<Sigma>1 # st1)" s1' rule: Sinca.step.induct)
      case (step_push fd1 d)
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_push rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_push rel_fundef_body_length[OF rel_fd1_fd2] by simp
  
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
        using step_push norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (IPush d2)
        then have d_def: "d = d2"
          using norm_instr_nth_body step_push.hyps(3) by auto
        let ?s2' = "State F2 H (Frame f (Suc pc) (OpDyn d2 # \<Sigma>2) # st2)"
        have "?STEP ?s2'"
          using IPush step_push d_def F2_f pc_in_range
          by (auto intro: Subx.step_push)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<Sigma>1_def
          using IPush d_def sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
          by (auto intro!: match.intros rel_stacktraces.intros)
        ultimately show ?thesis by auto
      next
        case (IPushUbx1 n)
        then have d_def: "d = box_ubx1 n"
          using norm_instr_nth_body step_push.hyps(3) by auto
        let ?s2' = "State F2 H (Frame f (Suc pc) (OpUbx1 n # \<Sigma>2) # st2)"
        have "?STEP ?s2'"
          using IPushUbx1 step_push d_def F2_f pc_in_range
          by (auto intro: Subx.step_push_ubx1)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<Sigma>1_def
          using IPushUbx1 d_def sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
          by (auto intro!: match.intros rel_stacktraces.intros)
        ultimately show ?thesis by auto
      next
        case (IPushUbx2 b)
        then have d_def: "d = box_ubx2 b"
          using norm_instr_nth_body step_push.hyps(3) by auto
        let ?s2' = "State F2 H (Frame f (Suc pc) (OpUbx2 b # \<Sigma>2) # st2)"
        have "?STEP ?s2'"
          using IPushUbx2 step_push d_def F2_f pc_in_range
          by (auto intro: Subx.step_push_ubx2)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<Sigma>1_def
          using IPushUbx2 d_def sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
          by (auto intro!: match.intros rel_stacktraces.intros)
        ultimately show ?thesis by auto
      qed simp_all
    next
      case (step_pop fd1 x \<Sigma>1')
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_pop rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_pop rel_fundef_body_length[OF rel_fd1_fd2] by simp
      obtain x' \<Sigma>2' where \<Sigma>2_def: "\<Sigma>2 = x' # \<Sigma>2'" and "\<Sigma>1' = norm_stack \<Sigma>2'"
        using step_pop \<open>\<Sigma>1 = norm_stack \<Sigma>2\<close> norm_stack_def by auto
  
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
        using step_pop norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case IPop
        let ?s2' = "State F2 H (Frame f (Suc pc) \<Sigma>2' # st2)"
        have "?STEP ?s2'"
          using IPop step_pop F2_f pc_in_range \<Sigma>2_def
          by (auto intro: Subx.step_pop)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<open>\<Sigma>1' = norm_stack \<Sigma>2'\<close>
          using IPop sp_prefix take_Suc_conv_app_nth[OF pc_in_range] \<Sigma>2_def
          by (auto intro!: match.intros rel_stacktraces.intros)
        ultimately show ?thesis by auto
      qed simp_all
    next
      case (step_load fd1 var i d \<Sigma>1')
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_load rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_load rel_fundef_body_length[OF rel_fd1_fd2] by simp
      obtain i' \<Sigma>2' where
        \<Sigma>2_def: "\<Sigma>2 = i' # \<Sigma>2'" and norm_i': "Subx.norm_unboxed i' = i" and "norm_stack \<Sigma>2' = \<Sigma>1'"
        using step_load \<Sigma>1_def norm_stack_def by auto
  
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
        using step_load norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (ILoad var')
        then have [simp]: "var' = var"
          using norm_instr_nth_body step_load.hyps(3) by auto
        let ?s2' = "State F2 H (Frame f (Suc pc) (OpDyn d # \<Sigma>2') # st2)"
        have "i' = OpDyn i"
          using sp_sufix[OF pc_in_range, unfolded \<Sigma>2_def ILoad, simplified]
          using norm_i'
          by (cases i'; simp)
        hence "?STEP ?s2'"
          using ILoad step_load F2_f pc_in_range
          by (auto intro!: Subx.step_load simp: \<Sigma>2_def)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<Sigma>1_def
          using ILoad sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
          by (auto intro!: match.intros rel_stacktraces.intros
              simp: \<open>norm_stack \<Sigma>2' = \<Sigma>1'\<close> \<open>i' = OpDyn i\<close> \<Sigma>2_def)
        ultimately show ?thesis by auto
      next
        case (ILoadUbx \<tau> var')
        then have [simp]: "var' = var"
          using norm_instr_nth_body step_load.hyps(3) by auto
        have [simp]: "i' = OpDyn i"
          using sp_sufix[OF pc_in_range, unfolded \<Sigma>2_def ILoadUbx, simplified]
          using norm_i'
          by (cases i'; simp)
        show ?thesis
        proof (cases "Subx.unbox \<tau> d")
          case None
          let ?F2' = "Fubx_add F2 f (Subx.generalize_fundef fd2)"
          let ?frame = "Frame f (Suc pc) (OpDyn d # \<Sigma>2')"
          let ?s2' = "State ?F2' H (Subx.box_stack f (?frame # st2))"
          have "?STEP ?s2'"
            using None ILoadUbx
            using step_load pc_in_range F2_f
            by (auto intro!: Subx.step_load_ubx_miss
                simp add: \<Sigma>2_def
                simp del: Subx.box_stack_Cons)
          moreover have "?MATCH ?s2'"
            using rel_fundefs_generalize[OF rel_F1_F2 F2_f]
            using sp_fundefs_generalize[OF sp_F2 F2_f]
            using sp_fundef_prefix ILoadUbx
            using pc_in_range
            by (auto intro!: match.intros rel_stacktraces_generalize[OF rel_st1_st2 F2_f]
                simp: \<Sigma>2_def \<open>norm_stack \<Sigma>2' = \<Sigma>1'\<close>)
          ultimately show ?thesis by auto
        next
          case (Some blob)
          let ?s2' = "State F2 H (Frame f (Suc pc) (blob # \<Sigma>2') # st2)"
          have "?STEP ?s2'"
            using Some ILoadUbx step_load F2_f pc_in_range
            by (auto intro: Subx.step_load_ubx_hit simp: \<Sigma>2_def)
          moreover have "?MATCH ?s2'"
            using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<Sigma>1_def
            using Some ILoadUbx sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
            by (auto intro!: match.intros rel_stacktraces.intros
                simp: \<open>norm_stack \<Sigma>2' = \<Sigma>1'\<close> \<Sigma>2_def)
          ultimately show ?thesis by auto
        qed
      qed simp_all
    next
    case (step_store fd1 var i x H' \<Sigma>1')
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_store rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_store rel_fundef_body_length[OF rel_fd1_fd2] by simp
      obtain i' x' \<Sigma>2' where
        \<Sigma>2_def: "\<Sigma>2 = i' # x' # \<Sigma>2'" and
        norm_i': "Subx.norm_unboxed i' = i" and
        norm_x': "Subx.norm_unboxed x' = x" and
        "norm_stack \<Sigma>2' = \<Sigma>1'"
        using step_store \<Sigma>1_def norm_stack_def by auto
  
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
        using step_store norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (IStore var')
        then have [simp]: "var' = var"
          using norm_instr_nth_body step_store.hyps(3) by auto
        note sp_sufix' = sp_sufix[OF pc_in_range, unfolded \<Sigma>2_def IStore, simplified]
        have [simp]: "i' = OpDyn i"
          using norm_i' sp_sufix' by (cases i'; simp)
        have [simp]: "x' = OpDyn x"
          using norm_x' sp_sufix' by (cases x'; simp)
        let ?s2' = "State F2 (heap_add H (var, i) x) (Frame f (Suc pc) \<Sigma>2' # st2)"
        have "?STEP ?s2'"
          using IStore \<Sigma>2_def pc_in_range F2_f
          by (auto intro: Subx.step_store)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<Sigma>2_def
          using \<open>norm_stack \<Sigma>2' = \<Sigma>1'\<close> \<open>heap_add H (var, i) x = H'\<close>
          using IStore sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
          by (auto intro!: match.intros rel_stacktraces.intros)
        ultimately show ?thesis by auto
      next
        case (IStoreUbx \<tau> var')
        then have [simp]: "var' = var"
          using norm_instr_nth_body step_store.hyps(3) by auto
        note sp_sufix' = sp_sufix[OF pc_in_range, unfolded \<Sigma>2_def IStoreUbx, simplified]
        have [simp]: "i' = OpDyn i"
          using norm_i' sp_sufix' by (cases i'; simp)
        have typeof_x'[simp]: "typeof x' = Some \<tau>"
          using sp_sufix' apply (auto simp add: Result.bind_eq_Ok_conv elim!: Subx.sp_instr.elims)
          by (metis result.simps(4))
        let ?s2' = "State F2 (heap_add H (var, i) x) (Frame f (Suc pc) \<Sigma>2' # st2)"
        have "?STEP ?s2'"
          unfolding \<Sigma>2_def
          using F2_f pc_in_range IStoreUbx
          using Subx.typeof_and_norm_unboxed_imp_cast_and_box[OF typeof_x' norm_x']
          by (auto intro!: Subx.step_store_ubx)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<Sigma>2_def
          using \<open>norm_stack \<Sigma>2' = \<Sigma>1'\<close> \<open>heap_add H (var, i) x = H'\<close>
          using IStoreUbx sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
          by (auto intro!: match.intros rel_stacktraces.intros)
        ultimately show ?thesis by auto
      qed simp_all
    next
      case (step_op fd1 op ar x)
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_op rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_op rel_fundef_body_length[OF rel_fd1_fd2] by simp
  
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
        using step_op norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (IOp op')
        then have "op' = op"
          using norm_instr_nth_body step_op.hyps(3) by auto
        hence "ar \<le> length \<Sigma>2" and
          all_arg_Dyn: "list_all (\<lambda>x. x = None) (map typeof (take ar \<Sigma>2))"
          using IOp step_op sp_sufix[OF pc_in_range]
          by (auto simp: take_map)
        let ?s2' = "State F2 H (Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>2) # st2)"
        have "?STEP ?s2'"
          using IOp step_op \<open>op' = op\<close> \<Sigma>1_def pc_in_range F2_f
          using traverse_cast_Dyn_eq_norm_stack[OF all_arg_Dyn]
          by (auto intro!: Subx.step_op simp: take_norm_stack)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f
          using IOp sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
          using arg_cong[OF \<Sigma>1_def, of "drop ar"] \<open>ar \<le> length \<Sigma>2\<close>
          using \<open>op' = op\<close> all_arg_Dyn \<Sigma>1_def \<open>\<AA>\<rr>\<ii>\<tt>\<yy> op = ar\<close>
          by (auto intro!: match.intros rel_stacktraces.intros
              dest: list_all_eq_const_imp_replicate
              simp: drop_norm_stack[symmetric] Let_def take_map drop_map)
        ultimately show ?thesis by auto
      qed simp_all
    next
      case (step_op_inl fd1 op ar opinl x F1')
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_op_inl rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_op_inl rel_fundef_body_length[OF rel_fd1_fd2] by simp
  
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
        using step_op_inl norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (IOp op')
        then have "op' = op"
          using norm_instr_nth_body step_op_inl.hyps(3) by simp
        hence "ar \<le> length \<Sigma>2" and
          all_arg_Dyn: "list_all (\<lambda>x. x = None) (map typeof (take ar \<Sigma>2))"
          using IOp step_op_inl sp_sufix[OF pc_in_range]
          by (auto simp: take_map)
        let ?fd2' = "rewrite_fundef_body fd2 pc (Ubx.IOpInl opinl)"
        let ?F2' = "Fubx_add F2 f ?fd2'"
        let ?frame = "Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>2)"
        let ?s2' = "State ?F2' H (?frame # st2)"
        have "?STEP ?s2'"
          using IOp step_op_inl \<open>op' = op\<close>
          using \<Sigma>1_def pc_in_range \<open>Fubx_get F2 f = Some fd2\<close>
          using all_arg_Dyn take_norm_stack traverse_cast_Dyn_eq_norm_stack
          by (auto intro!: Subx.step_op_inl)
        moreover have "?MATCH ?s2'"
        proof
          show "rel_fundefs (Finca_get F1') (Fubx_get ?F2')"
            using step_op_inl rel_fd1_fd2
            by (auto intro: rel_fundefs_rewrite_both')
        next
          have "arity fd2 = arity ?fd2'" by simp
          hence "all_same_arities (Fubx_get F2) (Fubx_get ?F2')"
            using all_same_arities_add[OF F2_f] by simp
          thus "sp_fundefs (Fubx_get ?F2')"
            apply (auto intro!: sp_fundefs_add[OF sp_F2])
            apply (rule Subx.sp_rewrite_eq_Ok[OF pc_in_range _ sp_full])
            apply (rule allI)
            unfolding IOp
            apply (rule Subx.sp_instr_op)
            using Sinca.\<II>\<nn>\<ll>_invertible \<open>op' = op\<close> step_op_inl.hyps(6) by blast
        next
          have "rel_stacktraces (Fubx_get F2)
            (Frame f (Suc pc) (x # drop ar \<Sigma>1) # st1) (?frame # st2) None"
              using rel_st1_st2 sp_prefix F2_f
              using IOp take_Suc_conv_app_nth[OF pc_in_range]
              using arg_cong[OF \<Sigma>1_def, of "drop ar"] \<open>ar \<le> length \<Sigma>2\<close>
              using \<open>op' = op\<close> step_op_inl.hyps(4) all_arg_Dyn
              by (auto intro!: rel_stacktraces.intros
                  dest: list_all_eq_const_imp_replicate
                  simp: drop_norm_stack[symmetric] Let_def take_map drop_map)
          thus "rel_stacktraces (Fubx_get ?F2')
          (Frame f (Suc pc) (x # drop ar \<Sigma>1) # st1) (?frame # st2) None"
            using F2_f pc_in_range IOp
            using Sinca.\<II>\<nn>\<ll>_invertible \<open>op' = op\<close> step_op_inl.hyps(6)
            by (auto intro!: rel_stacktraces_rewrite_fundef simp: Subx.sp_instr_op Let_def)
        qed
        ultimately show ?thesis by auto
      qed simp_all
    next
      case (step_op_inl_hit fd1 opinl ar x)
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_op_inl_hit rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_op_inl_hit rel_fundef_body_length[OF rel_fd1_fd2] by simp
  
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
        using step_op_inl_hit norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (IOpInl opinl')
        then have "opinl' = opinl"
          using norm_instr_nth_body step_op_inl_hit.hyps(3) by simp
        hence "ar \<le> length \<Sigma>2" and
          all_arg_Dyn: "list_all (\<lambda>x. x = None) (map typeof (take ar \<Sigma>2))"
          using IOpInl step_op_inl_hit sp_sufix[OF pc_in_range]
          by (auto simp: take_map)

        let ?s2' = "State F2 H (Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>2) # st2)"
        have "?STEP ?s2'"
          using IOpInl step_op_inl_hit \<open>opinl' = opinl\<close>
          using \<Sigma>1_def pc_in_range F2_f all_arg_Dyn
          by (auto intro: Subx.step_op_inl_hit traverse_cast_Dyn_eq_norm_stack
                simp: take_norm_stack)
        moreover have "?MATCH ?s2'"
          using rel_F1_F2 sp_F2 rel_st1_st2 F2_f
          using IOpInl sp_prefix take_Suc_conv_app_nth[OF pc_in_range]
          using arg_cong[OF \<Sigma>1_def, of "drop ar"]
          using \<open>ar \<le> length \<Sigma>2\<close> \<open>opinl' = opinl\<close> step_op_inl_hit.hyps(4,5) all_arg_Dyn
          by (auto intro!: match.intros rel_stacktraces.intros
              dest: list_all_eq_const_imp_replicate
              simp: drop_norm_stack[symmetric] Let_def take_map drop_map)
        ultimately show ?thesis by auto
      next
        case (IOpUbx opubx)
        then have "\<BB>\<oo>\<xx> opubx = opinl"
          using norm_instr_nth_body step_op_inl_hit.hyps(3) by simp
        hence \<AA>\<rr>\<ii>\<tt>\<yy>_opubx[simp]: "\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx)) = ar"
          using step_op_inl_hit.hyps(4,5) by simp
        note sp_sufix' = sp_sufix[OF pc_in_range, unfolded IOpUbx, simplified, unfolded Let_def, simplified]
        obtain dom codom where typeof_opubx: "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx = (dom, codom)"
          using prod.exhaust_sel by blast
        hence dom_def: "dom = map typeof (take ar \<Sigma>2)"
          unfolding \<AA>\<rr>\<ii>\<tt>\<yy>_opubx[unfolded Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy>, symmetric]
          using sp_sufix'
          by (auto simp: Let_def take_map)

        obtain x' where
          eval_op: "\<UU>\<bb>\<xx>\<OO>\<pp> opubx (take ar \<Sigma>2) = Some x'" and
          typeof_x': "typeof x' = codom"
          using typeof_opubx[unfolded dom_def, THEN Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_correct]
          by auto

        let ?s2' = "State F2 H (Frame f (Suc pc) (x' # drop ar \<Sigma>2) # st2)"
        have "?STEP ?s2'"
          using \<Sigma>1_def step_op_inl_hit eval_op \<AA>\<rr>\<ii>\<tt>\<yy>_opubx
          using pc_in_range IOpUbx F2_f
          by (auto intro!: Subx.step_op_ubx)
        moreover have "?MATCH ?s2'"
        proof -
          have "x = Subx.norm_unboxed x'"
            using Subx.\<UU>\<bb>\<xx>\<OO>\<pp>_correct[OF eval_op, unfolded \<open>\<BB>\<oo>\<xx> opubx = opinl\<close>]
            using step_op_inl_hit \<Sigma>1_def
            by (simp add: take_map norm_stack_def)
          thus ?thesis
            using rel_F1_F2 sp_F2 rel_st1_st2 F2_f \<Sigma>1_def
            using sp_prefix take_Suc_conv_app_nth[OF pc_in_range, unfolded IOpUbx]
            using step_op_inl_hit
            using typeof_opubx typeof_x'
            by (auto intro!: match.intros rel_stacktraces.intros
                simp: dom_def drop_norm_stack Let_def min.absorb2 take_map drop_map)
        qed
        ultimately show ?thesis by auto
      qed simp_all
    next
      case (step_op_inl_miss fd1 opinl ar x F1')
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_op_inl_miss rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_op_inl_miss rel_fundef_body_length[OF rel_fd1_fd2] by simp
  
      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
        using step_op_inl_miss norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (IOpInl opinl')
        then have "opinl' = opinl"
          using norm_instr_nth_body step_op_inl_miss.hyps(3) by simp
        hence "ar \<le> length \<Sigma>2" and
          all_arg_Dyn: "list_all (\<lambda>x. x = None) (map typeof (take ar \<Sigma>2))"
          using IOpInl step_op_inl_miss sp_sufix[OF pc_in_range]
          by (auto simp: take_map)

        let ?fd2' = "rewrite_fundef_body fd2 pc (Ubx.IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl))"
        let ?F2' = "Fubx_add F2 f ?fd2'"
        let ?frame = "Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>2)"
        let ?s2' = "State ?F2' H (?frame # st2)"
        have "?STEP ?s2'"
          using IOpInl step_op_inl_miss \<open>opinl' = opinl\<close>
          using \<Sigma>1_def pc_in_range F2_f
          using traverse_cast_Dyn_eq_norm_stack[OF all_arg_Dyn]
          by (auto intro!: Subx.step_op_inl_miss simp: take_norm_stack)
        moreover have "?MATCH ?s2'"
        proof
          show "rel_fundefs (Finca_get F1') (Fubx_get ?F2')"
            using step_op_inl_miss rel_fd1_fd2
            by (auto intro: rel_fundefs_rewrite_both')
        next
          show "sp_fundefs (Fubx_get ?F2')"
            using IOpInl \<open>opinl' = opinl\<close> all_same_arities_add[OF F2_f] sp_full
            by (auto intro: sp_fundefs_add[OF sp_F2]
                simp: Subx.sp_instr_op[symmetric] Subx.sp_rewrite[OF pc_in_range])
        next
          have "rel_stacktraces (Fubx_get F2)
            (Frame f (Suc pc) (x # drop ar \<Sigma>1) # st1) (?frame # st2) None"
              using rel_st1_st2 sp_prefix F2_f
              using IOpInl \<Sigma>1_def take_Suc_conv_app_nth[OF pc_in_range]
              using \<open>ar \<le> length \<Sigma>2\<close> \<open>opinl' = opinl\<close> step_op_inl_miss.hyps(4,5)
              using all_arg_Dyn
              by (auto intro!: rel_stacktraces.intros
                  dest: list_all_eq_const_imp_replicate
                  simp: drop_norm_stack Let_def take_map drop_map)
              
          thus "rel_stacktraces (Fubx_get ?F2')
            (Frame f (Suc pc) (x # drop ar \<Sigma>1) # st1) (?frame # st2) None"
            using F2_f pc_in_range IOpInl
            by (auto intro: rel_stacktraces_rewrite_fundef
                simp: \<open>opinl' = opinl\<close> Let_def Subx.sp_instr_op[symmetric])
        qed
        ultimately show ?thesis by auto
      next
        case (IOpUbx opubx)
        then have "\<BB>\<oo>\<xx> opubx = opinl"
          using norm_instr_nth_body step_op_inl_miss.hyps(3) by simp
        hence \<AA>\<rr>\<ii>\<tt>\<yy>_opubx: "\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx)) = ar"
          using step_op_inl_miss.hyps(4,5) by simp
        obtain dom codom where "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx = (dom, codom)"
          using prod.exhaust_sel by blast
        hence "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx = (map typeof (take ar \<Sigma>2), codom)"
          unfolding \<AA>\<rr>\<ii>\<tt>\<yy>_opubx[unfolded Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy>, symmetric]
          using sp_sufix[OF pc_in_range]
          unfolding IOpUbx
          by (auto simp: Let_def case_prod_beta take_map)
        then obtain x where eval_op: "\<UU>\<bb>\<xx>\<OO>\<pp> opubx (take ar \<Sigma>2) = Some x"
          using Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_correct by blast
        hence "\<II>\<ss>\<II>\<nn>\<ll> opinl (take ar \<Sigma>1)"
          unfolding \<Sigma>1_def norm_stack_def
          using \<open>\<BB>\<oo>\<xx> opubx = opinl\<close>
          by (auto intro: Sinca.\<II>\<nn>\<ll>_\<II>\<ss>\<II>\<nn>\<ll> Subx.\<UU>\<bb>\<xx>\<OO>\<pp>_to_\<II>\<nn>\<ll> simp: take_map)
        hence False
          using step_op_inl_miss by auto
        thus ?thesis by simp
      qed simp_all
    next
      case (step_cjump_true fd1 n \<Sigma>1')
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_cjump_true rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_cjump_true rel_fundef_body_length[OF rel_fd1_fd2] by simp
  
      show ?case
        using step_cjump_true norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (ICJump n')
        then have False
          using F2_f sp_fundefs_get[OF sp_F2, unfolded sp_fundef_def, THEN Subx.sp_no_jump]
          using nth_mem pc_in_range by fastforce
        thus ?thesis by simp
      qed simp_all
    next
      case (step_cjump_false fd1 n \<Sigma>1')
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using ex_F1_f by simp
      hence norm_instr_nth_body: "norm_instr (body fd2 ! pc) = body fd1 ! pc"
        using step_cjump_false rel_fundef_body_nth by metis
      have pc_in_range: "pc < length (body fd2)"
        using step_cjump_false rel_fundef_body_length[OF rel_fd1_fd2] by simp
  
      show ?case
        using step_cjump_false norm_instr_nth_body
      proof (cases "body fd2 ! pc")
        case (ICJump n')
        then have False
          using F2_f sp_fundefs_get[OF sp_F2, unfolded sp_fundef_def, THEN Subx.sp_no_jump]
          using nth_mem pc_in_range by fastforce
        thus ?thesis by simp
      qed simp_all
    next
      case (step_fun_call f' fd1 pc' g gd1 \<Sigma>1' frame\<^sub>g)
      hence [simp]: "f' = f" "pc' = pc" "\<Sigma>1' = \<Sigma>1" by auto
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using step_fun_call ex_F1_f by simp
      obtain gd2 where "Fubx_get F2 g = Some gd2" and rel_gd1_gd2: "rel_fundef norm_eq gd1 gd2"
        using step_fun_call rel_fundefs_Some1[OF rel_F1_F2] by blast
      have pc_in_range: "pc < length (body fd2)"
        using step_fun_call rel_fd1_fd2 by simp

      have nth_body2: "body fd2 ! pc = Ubx.ICall g"
        using rel_fundef_body_nth[OF rel_fd1_fd2 \<open>pc' < length (body fd1)\<close>, symmetric]
        unfolding \<open>body fd1 ! pc' = Inca.ICall g\<close>
        by (cases "body fd2 ! pc'"; simp)

      have prefix_\<Sigma>2_all_Dyn: "list_all (\<lambda>x. x = None) (map typeof (take (arity gd2) \<Sigma>2))"
        using \<open>Fubx_get F2 g = Some gd2\<close> sp_sufix[OF pc_in_range] nth_body2
        by (auto simp: Let_def take_map)
      hence all_dyn_args: "list_all is_dyn_operand (take (arity gd2) \<Sigma>2)"
        by (auto elim: list.pred_mono_strong simp add: list.pred_map comp_def)

      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?args = "map OpDyn (norm_stack (take (arity gd2) \<Sigma>2))"
        let ?frame = "Frame g 0 ?args"
        let ?s1' = "State F2 H (?frame # Frame f pc \<Sigma>2 # st2)"
        have "?STEP ?s1'"
        proof -
          have "arity gd2 \<le> length \<Sigma>2"
            using \<open>arity gd1 \<le> length \<Sigma>1'\<close>
            using rel_fundef_arities[OF rel_gd1_gd2] \<Sigma>1_def
            by simp
          thus ?thesis
            using pc_in_range nth_body2
            using  \<open>Fubx_get F2 g = Some gd2\<close> rel_stacktraces_Cons.hyps(3)
            using all_dyn_args
            by (auto intro!: Subx.step_fun_call[of _ _ fd2] nth_equalityI
                simp: typeof_unboxed_eq_const list_all_length norm_stack_def)
        qed
        moreover have "?MATCH ?s1'"
          using rel_F1_F2 sp_F2
        proof
          show "rel_stacktraces (Fubx_get F2)
           (frame\<^sub>g # Frame f pc \<Sigma>1 # st1)
           (?frame # Frame f pc \<Sigma>2 # st2) None"
            unfolding step_fun_call(7)
          proof (rule rel_stacktraces.intros)
            show "rel_stacktraces (Fubx_get F2) (Frame f pc \<Sigma>1 # st1) (Frame f pc \<Sigma>2 # st2)
              (Some g)"
              using pc_in_range nth_body2 rel_stacktraces_Cons
              using \<open>Fubx_get F2 g = Some gd2\<close> all_dyn_args
              by (auto intro!: rel_stacktraces.intros simp: is_valid_fun_call_def)
          next
            show "take (arity gd1) \<Sigma>1' = norm_stack ?args"
              using \<Sigma>1_def
              using rel_fundef_arities[OF rel_gd1_gd2]
              by (simp add: norm_stack_map take_norm_stack)
          next
            show "Fubx_get F2 g = Some gd2"
              using \<open>Fubx_get F2 g = Some gd2\<close> .
          next
            show "sp_fundef (Fubx_get F2) gd2 (take 0 (body gd2)) = Ok (map typeof ?args)"
              using \<Sigma>1_def step_fun_call.hyps(5)
              using rel_fundef_arities[OF rel_gd1_gd2]
              by (simp add: map_replicate_const)
          qed simp_all
        qed
        ultimately show "?thesis" by blast
      qed
    next
      case (step_fun_end f' fd1 \<Sigma>1\<^sub>g pc' \<Sigma>1' frame\<^sub>g g pc\<^sub>g frame\<^sub>g' st1')
      hence [simp]: "f' = f" "pc' = pc" "\<Sigma>1' = \<Sigma>1" by auto
      hence rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
        using step_fun_end ex_F1_f by simp

      note arities_fd1_fd2 = rel_fundef_arities[OF rel_fd1_fd2]

      obtain \<Sigma>2\<^sub>g st2' where
        st2_def: "st2 = Frame g pc\<^sub>g \<Sigma>2\<^sub>g # st2'"
        using step_fun_end rel_st1_st2
        by (auto elim: rel_stacktraces.cases)

      hence all_dyn_prefix_\<Sigma>2\<^sub>g: "list_all (\<lambda>x. x = None) (map typeof (take (arity fd2) \<Sigma>2\<^sub>g))"
        using step_fun_end rel_st1_st2 F2_f
        by (auto
            elim!: rel_stacktraces.cases[of _ "_ # _"] list.pred_mono_strong
            simp: list.pred_map is_valid_fun_call_def)

      show ?case (is "\<exists>x. ?STEP x \<and> ?MATCH x")
      proof -
        let ?s1' = "State F2 H (Frame g (Suc pc\<^sub>g) (\<Sigma>2 @ drop (arity fd2) \<Sigma>2\<^sub>g) # st2')"
        have "?STEP ?s1'"
          unfolding st2_def
          using step_fun_end st2_def rel_st1_st2
          using arities_fd1_fd2
          using rel_fundef_body_length[OF rel_fd1_fd2]
          by (auto intro!: Subx.step_fun_end[OF \<open>Fubx_get F2 f = Some fd2\<close>]
              elim!: rel_stacktraces.cases[of _ "_ # _"])
        moreover have "?MATCH ?s1'"
        proof -
          have "map typeof \<Sigma>2 = [None]"
            using step_fun_end st2_def rel_st1_st2
            using rel_fd1_fd2 sp_full sp_prefix
            by (auto elim!: rel_stacktraces.cases[of _ "_ # _"])
            
          thus ?thesis
            using step_fun_end st2_def rel_st1_st2
            using arities_fd1_fd2 \<Sigma>1_def F2_f all_dyn_prefix_\<Sigma>2\<^sub>g
            by (auto intro!: match.intros rel_stacktraces.intros
                intro: rel_F1_F2 sp_F2
                elim!: rel_stacktraces.cases[of _ "_ # _"]
                dest: list_all_eq_const_imp_replicate
                simp: take_Suc_conv_app_nth Let_def drop_norm_stack take_map drop_map
                simp: is_valid_fun_call_def)
        qed
        ultimately show ?thesis by auto
      qed
    qed
  qed
qed

lemma match_final_forward:
  "s1 \<sim> s2 \<Longrightarrow> Sinca.final s1 \<Longrightarrow> Subx.final s2"
proof (induction s1 s2 rule: match.induct)
  case (1 F1 F2 st1 st2 H)
  obtain f fd1 pc \<Sigma>1 where
    st1_def: "st1 = [Frame f pc \<Sigma>1]" and
    F1_f: "Finca_get F1 f = Some fd1" and
    pc_def: "pc = length (body fd1)"
    using \<open>Sinca.final (State F1 H st1)\<close>
    by (auto elim: Sinca.final.cases)
  obtain \<Sigma>2 where st2_def: "st2 = [Frame f pc \<Sigma>2]"
    using \<open>rel_stacktraces (Fubx_get F2) st1 st2 None\<close>
    unfolding st1_def
    by (auto elim: rel_stacktraces.cases)
  obtain fd2 where F2_f: "Fubx_get F2 f = Some fd2" and rel_fd1_fd2: "rel_fundef norm_eq fd1 fd2"
    using rel_fundefs_Some1[OF \<open>rel_fundefs (Finca_get F1) (Fubx_get F2)\<close> F1_f]
    by auto
  have "length (body fd1) = length (body fd2)"
    using rel_fd1_fd2 by simp
  thus ?case
    unfolding st2_def pc_def
    using F2_f by (auto intro: Subx.final.intros)
qed

sublocale inca_ubx_forward_simulation:
  forward_simulation Sinca.step Subx.step Sinca.final Subx.final "\<lambda>_ _. False" "\<lambda>_. match"
  using match_final_forward forward_lockstep_simulation
  using lockstep_to_plus_forward_simulation[of match Sinca.step _ Subx.step]
  by unfold_locales auto


section \<open>Bisimulation\<close>

sublocale inca_ubx_bisimulation:
  bisimulation Sinca.step Subx.step Sinca.final Subx.final "\<lambda>_ _. False" "\<lambda>_. match"
  by unfold_locales

end

end
