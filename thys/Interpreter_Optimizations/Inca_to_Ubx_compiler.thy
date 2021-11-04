theory Inca_to_Ubx_compiler
  imports Inca_to_Ubx_simulation Result
    "VeriComp.Compiler"
    "HOL-Library.Monad_Syntax"
begin

section \<open>Generic program rewriting\<close>

context
  fixes rewrite_instr :: "nat \<Rightarrow> 'a \<Rightarrow> 'stack \<Rightarrow> ('err, 'b \<times> 'stack) result"
begin

fun rewrite_prog :: "nat \<Rightarrow> 'a list \<Rightarrow> 'stack \<Rightarrow> ('err, 'b list \<times> 'stack) result" where
  "rewrite_prog _ [] \<Sigma> = Ok ([], \<Sigma>)" |
  "rewrite_prog n (x # xs) \<Sigma> = do {
    (x', \<Sigma>') \<leftarrow> rewrite_instr n x \<Sigma>;
    (xs', \<Sigma>'') \<leftarrow> rewrite_prog (Suc n) xs \<Sigma>';
    Ok (x' # xs', \<Sigma>'')
  }"

lemma rewrite_prog_map_f:
  assumes "\<And>x \<Sigma>1 n x' \<Sigma>2. rewrite_instr n x \<Sigma>1 = Ok (x', \<Sigma>2) \<Longrightarrow> f x' = x"
  shows "rewrite_prog n xs \<Sigma>1 = Ok (ys, \<Sigma>2) \<Longrightarrow> map f ys = xs"
  by (induction xs arbitrary: \<Sigma>1 n ys; auto simp: assms)

end

fun gen_pop_push where
  "gen_pop_push instr (domain, codomain) \<Sigma> = (
    let ar = length domain in
    if ar \<le> length \<Sigma> \<and> take ar \<Sigma> = domain then
      Ok (instr, codomain # drop ar \<Sigma>)
    else
      Error ()
  )"

context inca_to_ubx_simulation begin

lemma sp_rewrite_prog:
  assumes
    "rewrite_prog f n p1 \<Sigma>1 = Ok (p2, \<Sigma>2)" and
    "\<And>x \<Sigma>1 n x' \<Sigma>2. f n x \<Sigma>1 = Ok (x', \<Sigma>2) \<Longrightarrow> Subx.sp_instr F x' \<Sigma>1 = Ok \<Sigma>2"
  shows "Subx.sp F p2 \<Sigma>1 = Ok \<Sigma>2"
  using assms(1)
  by (induction p1 arbitrary: \<Sigma>1 n p2; auto simp: assms(2))


section \<open>Lifting\<close>

context
  fixes
    get_arity :: "'fun \<Rightarrow> nat option" and
    load_oracle :: "nat \<Rightarrow> type option"
begin

fun lift_instr where
  "lift_instr (Inca.IPush x) \<Sigma> = Ok (IPush x, None # \<Sigma>)" |
  "lift_instr Inca.IPop (_ # \<Sigma>) = Ok (IPop, \<Sigma>)" |
  "lift_instr (Inca.ILoad x) (None # \<Sigma>) = Ok (ILoad x, None # \<Sigma>)" |
  "lift_instr (Inca.IStore x) (None # None # \<Sigma>) = Ok (IStore x, \<Sigma>)" |
  "lift_instr (Inca.IOp op) \<Sigma> = gen_pop_push (IOp op) (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> op) None, None) \<Sigma>" |
  "lift_instr (Inca.IOpInl opinl) \<Sigma> =
    gen_pop_push (IOpInl opinl) (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl)) None, None) \<Sigma>" |
  "lift_instr (Inca.ICall f) \<Sigma> = do {
    ar \<leftarrow> Result.of_option () (get_arity f);
    gen_pop_push (ICall f) (replicate ar None, None) \<Sigma>
  }" |
  "lift_instr _ _ = Error ()"

definition lift where
  "lift = rewrite_prog (\<lambda>_. lift_instr)"

lemma sp_lift_instr:
  assumes
    "lift_instr instr \<Sigma>1 = Ok (instr', \<Sigma>2)" and
    "\<And>x. rel_option (\<lambda>ar fd. arity fd = ar) (get_arity x) (F x)"
  shows "Subx.sp_instr F instr' \<Sigma>1 = Ok \<Sigma>2"
  using assms(1)
proof (induction instr \<Sigma>1 rule: lift_instr.induct)
  fix f \<Sigma> n
  assume "lift_instr (Inca.ICall f) \<Sigma> = Ok (instr', \<Sigma>2)"
  thus "Subx.sp_instr F instr' \<Sigma> = Ok \<Sigma>2"
    using assms(2)[of f]
    by (auto simp: option_rel_Some1)
qed (auto simp add: Let_def)

lemma sp_lift: 
  assumes
    "lift n p1 \<Sigma>1 = Ok (p2, \<Sigma>2)" and
    "\<And>x. rel_option (\<lambda>ar fd. arity fd = ar) (get_arity x) (F x)"
  shows "Subx.sp F p2 \<Sigma>1 = Ok \<Sigma>2"
  using assms
  by (auto elim!: sp_rewrite_prog sp_lift_instr simp: lift_def)

lemma norm_lift_instr: "lift_instr x \<Sigma>1 = Ok (x', \<Sigma>2) \<Longrightarrow> norm_instr x' = x"
  by (induction x \<Sigma>1 rule: lift_instr.induct;
        auto simp: Let_def )

lemma norm_lift:
  assumes "lift n xs \<Sigma>1 = Ok (ys, \<Sigma>2)"
  shows "map norm_instr ys = xs"
  by (auto intro!: rewrite_prog_map_f[OF _ assms[unfolded lift_def]] simp: norm_lift_instr)


section \<open>Optimization\<close>

fun result_alternative :: "('a, 'b) result \<Rightarrow> ('a, 'b) result \<Rightarrow> ('a, 'b) result" (infixr "<|>" 51) where
  "result_alternative (Ok x) _ = Ok x" |
  "result_alternative _ (Ok x) = Ok x" |
  "result_alternative (Error e) _ = Error e"

definition try_unbox where
  "try_unbox \<tau> x \<Sigma> unbox mk_instr \<equiv>
    (case unbox x of Some n \<Rightarrow> Ok (mk_instr n, Some \<tau> # \<Sigma>) | None \<Rightarrow> Error ())"

fun optim_instr where
  "optim_instr _ (IPush d) \<Sigma> =
    try_unbox Ubx1 d \<Sigma> unbox_ubx1 IPushUbx1 <|>
    try_unbox Ubx2 d \<Sigma> unbox_ubx2 IPushUbx2 <|>
    Ok (IPush d, None # \<Sigma>)
  " |
  "optim_instr _ (IPushUbx1 n) \<Sigma> = Ok (IPushUbx1 n, Some Ubx1 # \<Sigma>)" |
  "optim_instr _ (IPushUbx2 b) \<Sigma> = Ok (IPushUbx2 b, Some Ubx2 # \<Sigma>)" |
  "optim_instr _ IPop (_ # \<Sigma>) = Ok (IPop, \<Sigma>)" |
  "optim_instr n (ILoad x) (None # \<Sigma>) = (
    case load_oracle n of
      Some \<tau> \<Rightarrow> Ok (ILoadUbx \<tau> x, Some \<tau> # \<Sigma>) |
      _ \<Rightarrow> Ok (ILoad x, None # \<Sigma>)
  )" |
  "optim_instr _ (ILoadUbx \<tau> x) (None # \<Sigma>) = Ok (ILoadUbx \<tau> x, Some \<tau> # \<Sigma>)" |
  "optim_instr _ (IStore x) (None # None # \<Sigma>) = Ok (IStore x, \<Sigma>)" |
  "optim_instr _ (IStore x) (None # Some \<tau> # \<Sigma>) = Ok (IStoreUbx \<tau> x, \<Sigma>)" |
  "optim_instr _ (IStoreUbx \<tau>\<^sub>1 x) (None # Some \<tau>\<^sub>2 # \<Sigma>) = (if \<tau>\<^sub>1 = \<tau>\<^sub>2 then Ok (IStoreUbx \<tau>\<^sub>1 x, \<Sigma>) else Error ())" |
  "optim_instr _ (IOp op) \<Sigma> = gen_pop_push (IOp op) (replicate (\<AA>\<rr>\<ii>\<tt>\<yy> op) None, None) \<Sigma>" |
  "optim_instr _ (IOpInl opinl) \<Sigma> = (
    let ar = \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) in
    if ar \<le> length \<Sigma> then
      case \<UU>\<bb>\<xx> opinl (take ar \<Sigma>) of
        None \<Rightarrow> gen_pop_push (IOpInl opinl) (replicate ar None, None) \<Sigma> |
        Some opubx \<Rightarrow> Ok (IOpUbx opubx, snd (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx) # drop ar \<Sigma>)
    else
      Error ()
  )" |
  "optim_instr _ (IOpUbx opubx) \<Sigma> = gen_pop_push (IOpUbx opubx) (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx) \<Sigma>" |
  "optim_instr _ (ICall f) \<Sigma> = do {
    ar \<leftarrow> Result.of_option () (get_arity f);
    gen_pop_push (ICall f) (replicate ar None, None) \<Sigma>
  }" |
  "optim_instr _ _ _ = Error ()"

definition optim where
  "optim \<equiv> rewrite_prog optim_instr"

lemma
  assumes
    "optim 0 [IPush d\<^sub>1, IPush d\<^sub>2, IStore y] [] = Ok (xs, ys)"
    "unbox_ubx1 d\<^sub>1 = Some x"
    "unbox_ubx1 d\<^sub>2 = None" "unbox_ubx2 d\<^sub>2 = None"
  shows "xs = [IPushUbx1 x, IPush d\<^sub>2, IStoreUbx Ubx1 y] \<and> ys = []"
  using assms(1)
  by (simp add: assms optim_def try_unbox_def)

lemma norm_optim_instr: "optim_instr n x \<Sigma>1 = Ok (x', \<Sigma>2) \<Longrightarrow> norm_instr x' = norm_instr x"
    for x \<Sigma>1 n x' \<Sigma>2
proof (induction n x \<Sigma>1 rule: optim_instr.induct)
  fix d \<Sigma>1 n
  assume "optim_instr n (Ubx.IPush d) \<Sigma>1 = Ok (x', \<Sigma>2)"
  thus "norm_instr x' = norm_instr (Ubx.instr.IPush d)"
    using Subx.box_unbox_inverse
    by (auto elim!: result_alternative.elims simp: try_unbox_def option.case_eq_if)
next
  fix x \<Sigma>1 n
  assume assms: "optim_instr n (Ubx.ILoad x) (None # \<Sigma>1) = Ok (x', \<Sigma>2)"
  thus "norm_instr x' = norm_instr (Ubx.ILoad x)"
  proof (cases "load_oracle n")
    case None
    then show ?thesis using assms by simp
  next
    case (Some x)
    then show ?thesis
      using assms by (cases x) auto
  qed
next
  fix opinl \<Sigma>1 n
  assume assms: "optim_instr n (IOpInl opinl) \<Sigma>1 = Ok (x', \<Sigma>2)"
  then have arity_le_\<Sigma>1: "\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) \<le> length \<Sigma>1"
    using prod.inject by fastforce

  show "norm_instr x' = norm_instr (IOpInl opinl)"
  proof (cases "\<UU>\<bb>\<xx> opinl (take (\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl)) \<Sigma>1)")
    case None
    then show ?thesis
      using assms arity_le_\<Sigma>1
      by (simp add: Let_def)
  next
    case (Some opubx)
    then show ?thesis
      using assms arity_le_\<Sigma>1
      by (auto simp: case_prod_beta Subx.\<UU>\<bb>\<xx>_invertible)
  qed
next
  fix opubx \<Sigma>1 n
  assume assms: "optim_instr n (IOpUbx opubx) \<Sigma>1 = Ok (x', \<Sigma>2)"
  then show "norm_instr x' = norm_instr (IOpUbx opubx)"
    by (cases "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx"; auto simp: Let_def)
qed (auto simp: Let_def)

lemma norm_optim:
  assumes "optim n xs \<Sigma>1 = Ok (ys, \<Sigma>2)"
  shows "map norm_instr ys = map norm_instr xs"
  using assms
  unfolding optim_def
  by (induction xs arbitrary: \<Sigma>1 n ys \<Sigma>2; auto simp: norm_optim_instr)

lemma sp_optim_instr:
  assumes
    "optim_instr n instr \<Sigma>1 = Ok (instr', \<Sigma>2)" and
    "\<And>x. rel_option (\<lambda>ar fd. arity fd = ar) (get_arity x) (F x) "
  shows "Subx.sp_instr F instr' \<Sigma>1 = Ok \<Sigma>2"
  using assms(1)
  apply (induction n instr \<Sigma>1 rule: optim_instr.induct;
      (auto simp: Let_def; fail)?)
  subgoal for _ d
    by (auto elim!: result_alternative.elims simp: try_unbox_def option.case_eq_if)
  subgoal for n
    by (cases "load_oracle n"; auto)
  subgoal for _ opinl \<Sigma>
    apply (simp add: Let_def)
    apply (cases "\<UU>\<bb>\<xx> opinl (take (\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl)) \<Sigma>)")
    apply (auto dest: list_all_eq_const_imp_replicate
        simp: case_prod_beta Let_def min.absorb2)
    subgoal for opubx
      using Subx.\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy>[of opubx]
      by (cases "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx"; auto simp: Subx.\<UU>\<bb>\<xx>_invertible dest: Subx.\<UU>\<bb>\<xx>_opubx_type)
    done
  subgoal for _ opubx
    by (cases "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx"; auto simp add: Let_def)
  subgoal for _ f
    using assms(2)[of f]
    by (auto simp: option_rel_Some1)
  done

lemma sp_optim:
  assumes
    "optim n p1 \<Sigma>1 = Ok (p2, \<Sigma>2)" and
    "\<And>x. rel_option (\<lambda>ar fd. arity fd = ar) (get_arity x) (F x)"
  shows "Subx.sp F p2 \<Sigma>1 = Ok \<Sigma>2"
  using assms
  by (auto elim!: sp_rewrite_prog sp_optim_instr simp: optim_def)


section \<open>Compilation of function definition\<close>

fun compile_fundef where
  "compile_fundef (Fundef instrs ar) = do {
    (xs, \<Sigma>\<^sub>1) \<leftarrow> lift 0 instrs (replicate ar None :: type option list);

    \<comment> \<open>Ensure that the function returns a single dynamic result\<close>
    () \<leftarrow> if \<Sigma>\<^sub>1 = [None] then Ok () else Error ();

    (ys, \<Sigma>\<^sub>2) \<leftarrow> optim 0 xs (replicate ar None);

    Ok (Fundef (
    if \<Sigma>\<^sub>2 = [None] then
      ys \<comment> \<open>use optimization\<close>
    else
      xs \<comment> \<open>cancel optimization\<close>
    ) ar)
  }"

lemma rel_compile_fundef:
  assumes "compile_fundef fd1 = Ok fd2"
  shows "rel_fundef norm_eq fd1 fd2"
proof (cases fd1)
  case (Fundef xs ar)
  obtain ys zs \<Sigma>2 where
    lift_xs: "lift 0 xs (replicate ar None :: type option list) = Ok (ys, [None])" and
    optim_ys: "optim 0 ys (replicate ar None :: type option list) = Ok (zs, \<Sigma>2)" and
    check: "fd2 = Fundef (if \<Sigma>2 = [None] then zs else ys) ar"
    using assms unfolding Fundef
    unfolding compile_fundef.simps
    by (auto simp: Nitpick.case_unit_unfold if_then_else_distributive)

  then have "map norm_instr ys = xs"
    by (auto intro: norm_lift)

  show ?thesis
  proof (cases "\<Sigma>2 = [None]")
    case True
    then show ?thesis
      using True Fundef
      using check norm_lift[OF lift_xs, symmetric]
      using norm_optim[OF optim_ys, symmetric]
      by (simp add: list.rel_map list.rel_refl)
  next
    case False
    then show ?thesis
      using Fundef check norm_lift[OF lift_xs, symmetric]
      by (simp add: list.rel_map list.rel_refl)
  qed
qed

lemma sp_compile_fundef:
  assumes
    "compile_fundef fd1 = Ok fd2" and
    "\<And>x. rel_option (\<lambda>ar fd. arity fd = ar) (get_arity x) (F x)"
  shows "sp_fundef F fd2 (body fd2) = Ok [None]"
proof (cases fd1)
  case (Fundef xs ar)
  with assms show ?thesis
    by (auto elim!: sp_optim sp_lift simp: sp_fundef_def Nitpick.case_unit_unfold if_eq_const_conv)
qed

end
end

locale inca_ubx_compiler =
  inca_to_ubx_simulation Finca_empty Finca_get
  for
    Finca_empty and
    Finca_get :: "_ \<Rightarrow> 'fun \<Rightarrow> _ option" +
  fixes
    load_oracle :: "'fun \<Rightarrow> nat \<Rightarrow> type option"
begin

section \<open>Compilation of function environment\<close>

definition compile_env_entry where
  "compile_env_entry \<A> \<O> x = map_result id (Pair (fst x)) (compile_fundef \<A> (\<O> (fst x)) (snd x))"

lemma rel_compile_env_entry:
  assumes "compile_env_entry \<O> \<A> (f, fd1) = Ok (f, fd2)"
  shows "rel_fundef norm_eq fd1 fd2"
  using assms unfolding compile_env_entry_def
  using rel_compile_fundef
  by auto

lemma sp_compile_env_entry:
  assumes
    "compile_env_entry \<A> \<O> (f, fd1) = Ok (f, fd2)" and
    "\<And>x. rel_option (\<lambda>ar fd. arity fd = ar) (\<A> x) (F x)"
  shows "sp_fundef F fd2 (body fd2) = Ok [None]"
  using assms unfolding compile_env_entry_def
  by (auto elim: sp_compile_fundef)

definition compile_env where
  "compile_env \<A> \<O> e \<equiv>
    map_result id Subx.Fenv.from_list
      (Result.those (map (compile_env_entry \<A> \<O>) (Finca_to_list e))) "

lemma list_assoc_those_compile_env_entries:
  "Result.those (map (compile_env_entry \<A> \<O>) xs) = Ok ys \<Longrightarrow>
  rel_option (\<lambda>fd1 fd2. compile_fundef \<A> (\<O> f) fd1 = Ok fd2) (map_of xs f) (map_of ys f)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then obtain y ys' where
    xs_def: "ys = y # ys'" and
    comp_x: "compile_env_entry \<A> \<O> x = Ok y" and
    comp_xs: "Result.those (map (compile_env_entry \<A> \<O>) xs) = Ok ys'"
    by auto

  obtain g fd1 fd2 where prods: "x = (g, fd1)" "y = (g, fd2)"
    using comp_x
    by (cases x) (auto simp: compile_env_entry_def)

  have "compile_fundef \<A> (\<O> g) fd1 = Ok fd2"
    using comp_x unfolding prods compile_env_entry_def
    by auto

  then show ?case
    unfolding prods xs_def
    using Cons.IH[OF comp_xs]
    by simp
qed

lemma compile_env_rel_compile_fundef:
  assumes "compile_env \<A> \<O> F1 = Ok F2"
  shows "rel_option (\<lambda>fd1 fd2. compile_fundef \<A> (\<O> f) fd1 = Ok fd2) (Finca_get F1 f) (Fubx_get F2 f)"
proof -
  obtain xs where those_xs: "Result.those (map (compile_env_entry \<A> \<O>) (Finca_to_list F1)) = Ok xs"
    using assms[unfolded compile_env_def]
    by auto
  hence F2_def: "F2 = Subx.Fenv.from_list xs"
    using assms[unfolded compile_env_def]
    by simp
  show ?thesis
  proof (cases "map_of (Finca_to_list F1) f")
    case None
    then show ?thesis
      unfolding F2_def Subx.Fenv.from_list_correct[symmetric]
      unfolding Sinca.Fenv.to_list_correct[symmetric]
      using list_assoc_those_compile_env_entries[OF those_xs, of f]
      by simp
  next
    case (Some fd1)
    then show ?thesis 
      unfolding F2_def Subx.Fenv.from_list_correct[symmetric]
      unfolding Sinca.Fenv.to_list_correct[symmetric]
      using list_assoc_those_compile_env_entries[OF those_xs, of f]
      by simp
  qed
qed

lemma rel_those_compile_env_entries:
  "Result.those (map (compile_env_entry \<A> \<O>) xs) = Ok ys \<Longrightarrow>
  rel_fundefs (Finca_get (Sinca.Fenv.from_list xs)) (Fubx_get (Subx.Fenv.from_list ys))"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case
    using rel_fundefs_empty by simp
next
  case (Cons x xs)
  then obtain y ys' where
    xs_def: "ys = y # ys'" and
    comp_x: "compile_env_entry \<A> \<O> x = Ok y" and
    comp_xs: "Result.those (map (compile_env_entry \<A> \<O>) xs) = Ok ys'"
    by auto

  obtain f fd1 fd2 where prods: "x = (f, fd1)" "y = (f, fd2)"
    using comp_x
    by (cases x) (auto simp: compile_env_entry_def)

  have "rel_fundef norm_eq fd1 fd2"
    using rel_compile_env_entry[OF comp_x[unfolded prods]] .

  then show ?case
    unfolding prods xs_def
    unfolding Sinca.Fenv.from_list_correct[symmetric] Subx.Fenv.from_list_correct[symmetric]
    unfolding rel_fundefs_def
    apply auto
    using Cons.IH[OF comp_xs]
    unfolding Sinca.Fenv.from_list_correct[symmetric] Subx.Fenv.from_list_correct[symmetric]
    by (simp add: rel_fundefs_def)
qed

lemma rel_fundefs_compile_env:
  assumes "compile_env \<A> \<O> e = Ok e'"
  shows "rel_fundefs (Finca_get e) (Fubx_get e')"
proof -
  obtain xs where
    FOO: "Result.those (map (compile_env_entry \<A> \<O>) (Finca_to_list e)) = Ok xs" and
    BAR: "e' = Subx.Fenv.from_list xs"
    using assms
    by (auto simp: compile_env_def)

  show ?thesis
    using rel_those_compile_env_entries[OF FOO]
    unfolding BAR
    unfolding Sinca.Fenv.get_from_list_to_list
    .
qed

lemma sp_fundefs_compile_env:
  assumes
    "compile_env \<A> \<O> F1 = Ok F2" and
    "\<And>x. rel_option (\<lambda>ar fd. arity fd = ar) (\<A> x) (Finca_get F1 x)"
  shows "sp_fundefs (Fubx_get F2)"
  unfolding sp_fundefs_def
  proof (intro allI impI)
    fix f fd2
    assume F2_f: "Fubx_get F2 f = Some fd2"
    then obtain fd1 where
      "Finca_get F1 f = Some fd1" and
      compile_fd1: "compile_fundef \<A> (\<O> f) fd1 = Ok fd2"
      using compile_env_rel_compile_fundef[OF assms(1), of f]
      by (auto simp: option_rel_Some2)

    note rel_F1_F2 = rel_fundefs_compile_env[OF assms(1)]

    have "rel_option (\<lambda>ar fd. arity fd = ar) (\<A> f) (Fubx_get F2 f)" for f
      using assms(2)[of f]
    proof (cases rule: option.rel_cases)
      case None
      then show ?thesis
        using rel_fundefs_None1[OF rel_F1_F2]
        by simp
    next
      case (Some ar fd1)
      then obtain fd2 where
        "Fubx_get F2 f = Some fd2" and
        rel_fd1_fd2: "rel_fundef (\<lambda>x y. x = norm_instr y) fd1 fd2"
        using rel_fundefs_Some1[OF rel_F1_F2]
        by (meson rel_fundefs_Some1)
      with Some show ?thesis
        by (simp add: rel_fundef_arities)
    qed
    thus "sp_fundef (Fubx_get F2) fd2 (body fd2) = Ok [None]"
      by (auto intro!: sp_compile_fundef[OF compile_fd1])
  qed


section \<open>Compilation of program\<close>

fun compile where
  "compile (Prog F H f) = Result.to_option (do {
    F' \<leftarrow> compile_env (map_option arity \<circ> Finca_get F) load_oracle F;
    Ok (Prog F' H f)
  })"

lemma compile_load:
  assumes
    compile_p1: "compile p1 = Some p2" and
    load: "Subx.load p2 s2"
  shows "\<exists>s1. Sinca.load p1 s1 \<and> match s1 s2"
proof -
  obtain F1 H main where p1_def: "p1 = Prog F1 H main"
    by (cases p1) simp
  then obtain F2 where
    compile_F1: "compile_env (map_option arity \<circ> Finca_get F1) load_oracle F1 = Ok F2" and
    p2_def: "p2 = Prog F2 H main"
    using compile_p1
    by auto

  note rel_F1_F2 = rel_fundefs_compile_env[OF compile_F1]

  show ?thesis
    using assms(2) unfolding p2_def
  proof (cases _ s2 rule: Subx.load.cases)
    case (1 fd2)
    let ?s1 = "State F1 H [Frame main 0 []]"

    from 1 obtain fd1 where
      Fstd_main: "Finca_get F1 main = Some fd1" and
      "compile_fundef (map_option arity \<circ> Finca_get F1) (load_oracle main) fd1 = Ok fd2"
      using compile_env_rel_compile_fundef[OF compile_F1, of main]
      by (auto simp: option_rel_Some2)
    with 1 have "arity fd1 = 0"
      using fundef.rel_sel rel_compile_fundef by metis
    hence "Sinca.load p1 ?s1"
      unfolding p1_def
      by (auto intro!: Sinca.load.intros[OF Fstd_main])
    moreover have "?s1 \<sim> s2"
    proof -
      have "sp_fundefs (Fubx_get F2)"
        by (auto intro: sp_fundefs_compile_env[OF compile_F1] simp: option.rel_map option.rel_refl)
      moreover have "rel_stacktraces (Fubx_get F2) [Frame main 0 []] [Frame main 0 []] None"
        using 1 by (auto intro!: rel_stacktraces.intros simp: sp_fundef_def)
      ultimately show ?thesis
        unfolding 1
        using rel_F1_F2
        by (auto intro!: match.intros)
    qed
    ultimately show ?thesis by auto
  qed
qed

interpretation std_to_inca_compiler:
  compiler Sinca.step Subx.step Sinca.final Subx.final Sinca.load Subx.load
    "\<lambda>_ _. False" "\<lambda>_. match" compile
using compile_load
  by unfold_locales auto

end

end
