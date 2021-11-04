section \<open>A universal partial recursive function\<close>

theory Universal
  imports Partial_Recursive
begin

text \<open>The main product of this section is a universal partial recursive
function, which given a code $i$ of an $n$-ary partial recursive function $f$
and an encoded list @{term xs} of $n$ arguments, computes @{term "eval f
xs"}. From this we can derive fixed-arity universal functions satisfying the
usual results such as the $s$-$m$-$n$ theorem. To represent the code $i$, we
need a way to encode @{typ recf}s as natural numbers (Section~\ref{s:recf_enc}). To
construct the universal function, we devise a ternary function taking $i$,
$xs$, and a step bound $t$ and simulating the execution of $f$ on input $xs$ for
$t$ steps. This function is useful in its own right, enabling techniques like
dovetailing or ``concurrent'' evaluation of partial recursive functions.

The notion of a ``step'' is not part of the definition of (the evaluation of)
partial recursive functions, but one can simulate the evaluation on an
abstract machine (Section~\ref{s:step}). This machine's configurations can be
encoded as natural numbers, and this leads us to a step function @{typ "nat
\<Rightarrow> nat"} on encoded configurations (Section~\ref{s:step_enc}).
This function in turn can be computed by a primitive recursive function, from
which we develop the aforementioned ternary function of $i$, @{term xs}, and
$t$ (Section~\ref{s:step_recf}). From this we can finally derive
a universal function (Section~\ref{s:the_universal}).\<close>

subsection \<open>A step function\label{s:step}\<close>

text \<open>We simulate the stepwise execution of a partial recursive
function in a fairly straightforward way reminiscent of the execution of
function calls in an imperative programming language. A configuration of the
abstract machine is a pair consisting of:
\begin{enumerate}
\item A stack of frames. A frame represents the execution of a function and is
  a triple @{term "(f, xs, locals)"} of
  \begin{enumerate}
    \item a @{typ recf} @{term f} being executed,
    \item a @{typ "nat list"} of arguments of @{term f},
    \item a @{typ "nat list"} of local variables, which holds intermediate
      values when @{term f} is of the form @{term Cn}, @{term Pr}, or @{term Mn}.
  \end{enumerate}
\item A register of type @{typ "nat option"} representing the return value of
  the last function call: @{term None} signals that in the previous step the
  stack was not popped and hence no value was returned, whereas @{term "Some
  v"} means that in the previous step a function returned @{term v}.
\end{enumerate}
For computing @{term h} on input @{term xs}, the initial configuration is
@{term "([(h, xs, [])], None)"}. When the computation for a frame ends, it is
popped off the stack, and its return value is put in the register. The entire
computation ends when the stack is empty. In such a final configuration the
register contains the value of @{term h} at @{term xs}. If no final
configuration is ever reached, @{term h} diverges at @{term xs}.

The execution of one step depends on the topmost (that is, active) frame. In
the step when a frame @{term "(h, xs, locals)"} is pushed onto the stack, the
local variables are @{term "locals = []"}. The following happens until the
frame is popped off the stack again (if it ever is):
\begin{itemize}
\item For the base functions @{term "h = Z"}, @{term "h = S"},
  @{term[names_short] "h = Id m n"}, the frame is popped off the stack right away,
  and the return value is placed in the register.
\item For @{term "h = Cn n f gs"}, for each function $g$ in @{term gs}:
  \begin{enumerate}
  \item A new frame of the form @{term "(g, xs, [])"} is pushed onto the stack.
  \item When (and if) this frame
    is eventually popped, the value in the register is @{term "eval g xs"}. This value
    is appended to the list @{term locals} of local variables.
  \end{enumerate}
  When all $g$ in $gs$ have been evaluated in this manner, $f$ is evaluated on the local variables
  by pushing @{term "(f, locals, [])"}. The resulting register value is kept
  and the active frame for $h$ is popped off the stack.
\item For @{text "h = Pr n f g"}, let @{term "xs = y # ys"}. First @{term "(f,
  ys, [])"} is pushed and the return value stored in the @{term
  locals}. Then @{term "(g, x # v # ys, [])"} is pushed,
  where $x$ is the length of @{term locals} and $v$ the most recently
  appended value. The return value is appended to @{term locals}. This is
  repeated until the length of @{term locals} reaches @{term y}. Then the most
  recently appended local is placed in the register, and the stack is popped.
\item For @{text "h = Mn n f"}, frames @{term "(f, x # xs, [])"} are pushed
  for $x = 0, 1, 2, \ldots$ until one of them returns $0$. Then this
  $x$ is placed in the register and the stack is popped. Until then $x$ is
  stored in @{term locals}. If none of these evaluations return $0$, the
  stack never shrinks, and thus the machine never reaches a final state.
\end{itemize}\<close>

type_synonym frame = "recf \<times> nat list \<times> nat list"

type_synonym configuration = "frame list \<times> nat option"


subsubsection \<open>Definition of the step function\<close>

fun step :: "configuration \<Rightarrow> configuration" where
  "step ([], rv) = ([], rv)"
| "step (((Z, _, _) # fs), rv) = (fs, Some 0)"
| "step (((S, xs, _) # fs), rv) = (fs, Some (Suc (hd xs)))"
| "step (((Id m n, xs, _) # fs), rv) = (fs, Some (xs ! n))"
| "step (((Cn n f gs, xs, ls) # fs), rv) =
    (if length ls = length gs
     then if rv = None
          then ((f, ls, []) # (Cn n f gs, xs, ls) # fs, None)
          else (fs, rv)
     else if rv = None
          then if length ls < length gs
               then ((gs ! (length ls), xs, []) # (Cn n f gs, xs, ls) # fs, None)
               else (fs, rv)   \<comment>\<open>cannot occur, so don't-care term\<close>
          else ((Cn n f gs, xs, ls @ [the rv]) # fs, None))"
| "step (((Pr n f g, xs, ls) # fs), rv) =
    (if ls = []
     then if rv = None
          then ((f, tl xs, []) # (Pr n f g, xs, ls) # fs, None)
          else ((Pr n f g, xs, [the rv]) # fs, None)
     else if length ls = Suc (hd xs)
          then (fs, Some (hd ls))
          else if rv = None
               then ((g, (length ls - 1) # hd ls # tl xs, []) # (Pr n f g, xs, ls) # fs, None)
               else ((Pr n f g, xs, (the rv) # ls) # fs, None))"
| "step (((Mn n f, xs, ls) # fs), rv) =
    (if ls = []
     then ((f, 0 # xs, []) # (Mn n f, xs, [0]) # fs, None)
     else if rv = Some 0
          then (fs, Some (hd ls))
          else ((f, (Suc (hd ls)) # xs, []) # (Mn n f, xs, [Suc (hd ls)]) # fs, None))"

definition reachable :: "configuration \<Rightarrow> configuration \<Rightarrow> bool" where
  "reachable x y \<equiv> \<exists>t. iterate t step x = y"

lemma step_reachable [intro]:
  assumes "step x = y"
  shows "reachable x y"
  unfolding reachable_def using assms by (metis iterate.simps(1,2) comp_id)

lemma reachable_transitive [trans]:
  assumes "reachable x y" and "reachable y z"
  shows "reachable x z"
  using assms iterate_additive[where ?f=step] reachable_def by metis

lemma reachable_refl: "reachable x x"
  unfolding reachable_def by (metis iterate.simps(1) eq_id_iff)

text \<open>From a final configuration, that is, when the stack is empty,
only final configurations are reachable.\<close>

lemma step_empty_stack:
  assumes "fst x = []"
  shows "fst (step x) = []"
  using assms by (metis prod.collapse step.simps(1))

lemma reachable_empty_stack:
  assumes "fst x = []" and "reachable x y"
  shows "fst y = []"
proof -
  have "fst (iterate t step x) = []" for t
    using assms step_empty_stack by (induction t) simp_all
  then show ?thesis
    using reachable_def assms(2) by auto
qed

abbreviation nonterminating :: "configuration \<Rightarrow> bool" where
  "nonterminating x \<equiv> \<forall>t. fst (iterate t step x) \<noteq> []"

lemma reachable_nonterminating:
  assumes "reachable x y" and "nonterminating y"
  shows "nonterminating x"
proof -
  from assms(1) obtain t\<^sub>1 where t1: "iterate t\<^sub>1 step x = y"
    using reachable_def by auto
  have "fst (iterate t step x) \<noteq> []" for t
  proof (cases "t \<le> t\<^sub>1")
    case True
    then show ?thesis
      using t1 assms(2) reachable_def reachable_empty_stack iterate_additive'
      by (metis le_Suc_ex)
  next
    case False
    then have "iterate t step x = iterate (t\<^sub>1 + (t - t\<^sub>1)) step x"
      by simp
    then have "iterate t step x = iterate (t - t\<^sub>1) step (iterate t\<^sub>1 step x)"
      by (simp add: iterate_additive')
    then have "iterate t step x = iterate (t - t\<^sub>1) step y"
      using t1 by simp
    then show "fst (iterate t step x) \<noteq> []"
      using assms(2) by simp
  qed
  then show ?thesis ..
qed

text \<open>The function @{term step} is underdefined, for example, when the
top frame contains a non-well-formed @{typ recf} or too few arguments. All is
well, though, if every frame contains a well-formed @{typ recf} whose arity
matches the number of arguments. Such stacks will be called
\emph{valid}.\<close>

definition valid :: "frame list \<Rightarrow> bool" where
  "valid stack \<equiv> \<forall>s\<in>set stack. recfn (length (fst (snd s))) (fst s)"

lemma valid_frame: "valid (s # ss) \<Longrightarrow> valid ss \<and> recfn (length (fst (snd s))) (fst s)"
  using valid_def by simp

lemma valid_ConsE: "valid ((f, xs, locs) # rest) \<Longrightarrow> valid rest \<and> recfn (length xs) f"
  using valid_def by simp

lemma valid_ConsI: "valid rest \<Longrightarrow> recfn (length xs) f \<Longrightarrow> valid ((f, xs, locs) # rest)"
  using valid_def by simp

text \<open>Stacks in initial configurations are valid, and performing a step
maintains the validity of the stack.\<close>

lemma step_valid: "valid stack \<Longrightarrow> valid (fst (step (stack, rv)))"
proof (cases stack)
  case Nil
  then show ?thesis using valid_def by simp
next
  case (Cons s ss)
  assume valid: "valid stack"
  then have *: "valid ss \<and> recfn (length (fst (snd s))) (fst s)"
    using valid_frame Cons by simp
  show ?thesis
  proof (cases "fst s")
    case Z
    then show ?thesis using Cons valid * by (metis fstI prod.collapse step.simps(2))
  next
    case S
    then show ?thesis using Cons valid * by (metis fst_conv prod.collapse step.simps(3))
  next
    case Id
    then show ?thesis using Cons valid * by (metis fstI prod.collapse step.simps(4))
  next
    case (Cn n f gs)
    then obtain xs ls where "s = (Cn n f gs, xs, ls)"
      using Cons by (metis prod.collapse)
    moreover consider
        "length ls = length gs \<and> rv \<up>"
      | "length ls = length gs \<and> rv \<down>"
      | "length ls < length gs \<and> rv \<up>"
      | "length ls \<noteq> length gs \<and> rv \<down>"
      | "length ls > length gs \<and> rv \<up>"
      by linarith
    ultimately show ?thesis using valid Cons valid_def by (cases) auto
  next
    case (Pr n f g)
    then obtain xs ls where s: "s = (Pr n f g, xs, ls)"
      using Cons by (metis prod.collapse)
    consider
        "length ls = 0 \<and> rv \<up>"
      | "length ls = 0 \<and> rv \<down>"
      | "length ls \<noteq> 0 \<and> length ls = Suc (hd xs)"
      | "length ls \<noteq> 0 \<and> length ls \<noteq> Suc (hd xs) \<and> rv \<up>"
      | "length ls \<noteq> 0 \<and> length ls \<noteq> Suc (hd xs) \<and> rv \<down>"
      by linarith
    then show ?thesis using Cons * valid_def s by (cases) auto
  next
    case (Mn n f)
    then obtain xs ls where s: "s = (Mn n f, xs, ls)"
      using Cons by (metis prod.collapse)
    consider
        "length ls = 0"
      | "length ls \<noteq> 0 \<and> rv \<up>"
      | "length ls \<noteq> 0 \<and> rv \<down>"
      by linarith
    then show ?thesis using Cons * valid_def s by (cases) auto
  qed
qed

corollary iterate_step_valid:
  assumes "valid stack"
  shows "valid (fst (iterate t step (stack, rv)))"
  using assms
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  moreover have "iterate (Suc t) step (stack, rv) = step (iterate t step (stack, rv))"
    by simp
  ultimately show ?case using step_valid valid_def by (metis prod.collapse)
qed


subsubsection \<open>Correctness of the step function\<close>

text \<open>The function @{term step} works correctly for a @{typ recf} $f$
on arguments @{term xs} in some configuration if (1) in case $f$ converges, @{term
step} reaches a configuration with the topmost frame popped and @{term "eval
f xs"} in the register, and (2) in case $f$ diverges, @{term step} does not
reach a final configuration.\<close>

fun correct :: "configuration \<Rightarrow> bool" where
  "correct ([], r) = True"
| "correct ((f, xs, ls) # rest, r) =
    (if eval f xs \<down> then reachable ((f, xs, ls) # rest, r) (rest, eval f xs)
     else nonterminating ((f, xs, ls) # rest, None))"

lemma correct_convergI:
  assumes "eval f xs \<down>" and "reachable ((f, xs, ls) # rest, None) (rest, eval f xs)"
  shows "correct ((f, xs, ls) # rest, None)"
  using assms by auto

lemma correct_convergE:
  assumes "correct ((f, xs, ls) # rest, None)" and "eval f xs \<down>"
  shows "reachable ((f, xs, ls) # rest, None) (rest, eval f xs)"
  using assms by simp

text \<open>The correctness proof for @{term step} is by structural induction
on the @{typ recf} in the top frame. The base cases @{term Z}, @{term S},
and @{term[names_short] Id} are simple. For @{text "X = Cn, Pr, Mn"}, the
lemmas named @{text reachable_X} show which configurations are reachable for
@{typ recf}s of shape @{text X}. Building on those, the lemmas named @{text
step_X_correct} show @{term step}'s correctness for @{text X}.\<close>

lemma reachable_Cn:
  assumes "valid (((Cn n f gs), xs, []) # rest)" (is "valid ?stack")
    and "\<And>xs rest. valid ((f, xs, []) # rest) \<Longrightarrow> correct ((f, xs, []) # rest, None)"
    and "\<And>g xs rest.
      g \<in> set gs \<Longrightarrow> valid ((g, xs, []) # rest) \<Longrightarrow> correct ((g, xs, []) # rest, None)"
    and "\<forall>i<k. eval (gs ! i) xs \<down>"
    and "k \<le> length gs"
  shows "reachable
    (?stack, None)
    ((Cn n f gs, xs, take k (map (\<lambda>g. the (eval g xs)) gs)) # rest, None)"
  using assms(4,5)
proof (induction k)
  case 0
  then show ?case using reachable_refl by simp
next
  case (Suc k)
  let ?ys = "map (\<lambda>g. the (eval g xs)) gs"
  from Suc have "k < length gs" by simp
  have valid: "recfn (length xs) (Cn n f gs)" "valid rest"
    using assms(1) valid_ConsE[of "(Cn n f gs)"] by simp_all
  from Suc have "reachable (?stack, None) ((Cn n f gs, xs, take k ?ys) # rest, None)"
      (is "_ (?stack1, None)")
    by simp
  also have "reachable ... ((gs ! k, xs, []) # ?stack1, None)"
    using step_reachable \<open>k < length gs\<close>
    by (auto simp: min_absorb2)
  also have "reachable ... (?stack1, eval (gs ! k) xs)"
      (is "_ (_, ?rv)")
    using Suc.prems(1) \<open>k < length gs\<close> assms(3) valid valid_ConsI by auto
  also have "reachable ... ((Cn n f gs, xs, (take (Suc k) ?ys)) # rest, None)"
      (is "_ (?stack2, None)")
  proof -
    have "step (?stack1, ?rv) = ((Cn n f gs, xs, (take k ?ys) @ [the ?rv]) # rest, None)"
      using Suc by auto
    also have "... = ((Cn n f gs, xs, (take (Suc k) ?ys)) # rest, None)"
      by (simp add: \<open>k < length gs\<close> take_Suc_conv_app_nth)
    finally show ?thesis
      using step_reachable by auto
  qed
  finally show "reachable (?stack, None) (?stack2, None)" .
qed

lemma step_Cn_correct:
  assumes "valid (((Cn n f gs), xs, []) # rest)" (is "valid ?stack")
    and "\<And>xs rest. valid ((f, xs, []) # rest) \<Longrightarrow> correct ((f, xs, []) # rest, None)"
    and "\<And>g xs rest.
      g \<in> set gs \<Longrightarrow> valid ((g, xs, []) # rest) \<Longrightarrow> correct ((g, xs, []) # rest, None)"
  shows "correct (?stack, None)"
proof -
  have valid: "recfn (length xs) (Cn n f gs)" "valid rest"
    using valid_ConsE[OF assms(1)] by auto
  let ?ys = "map (\<lambda>g. the (eval g xs)) gs"
  consider
      (diverg_f) "\<forall>g\<in>set gs. eval g xs \<down>" and "eval f ?ys \<up>"
    | (diverg_gs) "\<exists>g\<in>set gs. eval g xs \<up>"
    | (converg) "eval (Cn n f gs) xs \<down>"
    using valid_ConsE[OF assms(1)] by fastforce
  then show ?thesis
  proof (cases)
    case diverg_f
    then have "\<forall>i<length gs. eval (gs ! i) xs \<down>" by simp
    then have "reachable (?stack, None) ((Cn n f gs, xs, ?ys) # rest, None)"
        (is "_ (?stack1, None)")
      using reachable_Cn[OF assms, where ?k="length gs"] by simp
    also have "reachable ... ((f, ?ys, []) # ?stack1, None)" (is "_ (?stack2, None)")
      by (simp add: step_reachable)
    finally have "reachable (?stack, None) (?stack2, None)" .
    moreover have "nonterminating (?stack2, None)"
      using diverg_f(2) assms(2)[of ?ys ?stack1] valid_ConsE[OF assms(1)] valid_ConsI
      by auto
    ultimately have "nonterminating (?stack, None)"
      using reachable_nonterminating by simp
    moreover have "eval (Cn n f gs) xs \<up>"
      using diverg_f(2) assms(1) eval_Cn valid_ConsE by presburger
    ultimately show ?thesis by simp
  next
    case diverg_gs
    then have ex_i: "\<exists>i<length gs. eval (gs ! i) xs \<up>"
      using in_set_conv_nth[of _ gs] by auto
    define k where "k = (LEAST i. i < length gs \<and> eval (gs ! i) xs \<up>)" (is "_ = Least ?P")
    then have gs_k: "eval (gs ! k) xs \<up>"
      using LeastI_ex[OF ex_i] by simp
    have "\<forall>i<k. eval (gs ! i) xs \<down>"
      using k_def not_less_Least[of _ ?P] LeastI_ex[OF ex_i] by simp
    moreover from this have "k < length gs"
      using ex_i less_le_trans not_le by blast
    ultimately have "reachable (?stack, None) ((Cn n f gs, xs, take k ?ys) # rest, None)"
      using reachable_Cn[OF assms] by simp
    also have "reachable ...
      ((gs ! (length (take k ?ys)), xs, []) # (Cn n f gs, xs, take k ?ys) # rest, None)"
      (is "_ (?stack1, None)")
    proof -
      have "length (take k ?ys) < length gs"
        by (simp add: \<open>k < length gs\<close> less_imp_le_nat min_less_iff_disj)
      then show ?thesis using step_reachable by auto
    qed
    finally have "reachable (?stack, None) (?stack1, None)" .
    moreover have "nonterminating (?stack1, None)"
    proof -
      have "recfn (length xs) (gs ! k)"
        using \<open>k < length gs\<close> valid(1) by simp
      then have "correct (?stack1, None)"
        using \<open>k < length gs\<close> nth_mem valid valid_ConsI
          assms(3)[of "gs ! (length (take k ?ys))" xs]
        by auto
      moreover have "length (take k ?ys) = k"
        by (simp add: \<open>k < length gs\<close> less_imp_le_nat min_absorb2)
      ultimately show ?thesis using gs_k by simp
    qed
    ultimately have "nonterminating (?stack, None)"
      using reachable_nonterminating by simp
    moreover have "eval (Cn n f gs) xs \<up>"
      using diverg_gs valid by fastforce
    ultimately show ?thesis by simp
  next
    case converg
    then have f: "eval f ?ys \<down>" and g: "\<And>g. g \<in> set gs \<Longrightarrow> eval g xs \<down>"
      using valid(1) by (metis eval_Cn)+
    then have "\<forall>i<length gs. eval (gs ! i) xs \<down>"
      by simp
    then have "reachable (?stack, None) ((Cn n f gs, xs, take (length gs) ?ys) # rest, None)"
      using reachable_Cn assms by blast
    also have "reachable ... ((Cn n f gs, xs, ?ys) # rest, None)" (is "_ (?stack1, None)")
      by (simp add: reachable_refl)
    also have "reachable ... ((f, ?ys, []) # ?stack1, None)"
      using step_reachable by auto
    also have "reachable ... (?stack1, eval f ?ys)"
      using assms(2)[of "?ys"] correct_convergE valid f valid_ConsI by auto
    also have "reachable (?stack1, eval f ?ys) (rest, eval f ?ys)"
      using f by auto
    finally have "reachable (?stack, None) (rest, eval f ?ys)" .
    moreover have "eval (Cn n f gs) xs = eval f ?ys"
      using g valid(1) by auto
    ultimately show ?thesis
      using converg correct_convergI by auto
  qed
qed

text \<open>During the execution of a frame with a partial recursive function
of shape @{term "Pr n f g"} and arguments @{term "x # xs"}, the list of local
variables collects all the function values up to @{term x} in reversed
order. We call such a list a @{term trace} for short.\<close>

definition trace :: "nat \<Rightarrow> recf \<Rightarrow> recf \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat list" where
  "trace n f g xs x \<equiv> map (\<lambda>y. the (eval (Pr n f g) (y # xs))) (rev [0..<Suc x])"

lemma trace_length: "length (trace n f g xs x) = Suc x"
  using trace_def by simp

lemma trace_hd: "hd (trace n f g xs x) = the (eval (Pr n f g) (x # xs))"
  using trace_def by simp

lemma trace_Suc:
  "trace n f g xs (Suc x) = (the (eval (Pr n f g) (Suc x # xs))) # (trace n f g xs x)"
  using trace_def by simp

lemma reachable_Pr:
  assumes "valid (((Pr n f g), x # xs, []) # rest)" (is "valid ?stack")
    and "\<And>xs rest. valid ((f, xs, []) # rest) \<Longrightarrow> correct ((f, xs, []) # rest, None)"
    and "\<And>xs rest. valid ((g, xs, []) # rest) \<Longrightarrow> correct ((g, xs, []) # rest, None)"
    and "y \<le> x"
    and "eval (Pr n f g) (y # xs) \<down>"
  shows "reachable (?stack, None) ((Pr n f g, x # xs, trace n f g xs y) # rest, None)"
  using assms(4,5)
proof (induction y)
  case 0
  have valid: "recfn (length (x # xs)) (Pr n f g)" "valid rest"
    using valid_ConsE[OF assms(1)] by simp_all
  then have f: "eval f xs \<down>" using 0 by simp
  let ?as = "x # xs"
  have "reachable (?stack, None) ((f, xs, []) # ((Pr n f g), ?as, []) # rest, None)"
    using step_reachable by auto
  also have "reachable ... (?stack, eval f xs)"
    using assms(2)[of xs "((Pr n f g), ?as, []) # rest"]
      correct_convergE[OF _ f] f valid valid_ConsI
    by simp
  also have "reachable ... ((Pr n f g, ?as, [the (eval f xs)]) # rest, None)"
    using step_reachable valid(1) f by auto
  finally have "reachable (?stack, None) ((Pr n f g, ?as, [the (eval f xs)]) # rest, None)" .
  then show ?case using trace_def valid(1) by simp
next
  case (Suc y)
  have valid: "recfn (length (x # xs)) (Pr n f g)" "valid rest"
    using valid_ConsE[OF assms(1)] by simp_all
  let ?ls = "trace n f g xs y"
  have lenls: "length ?ls = Suc y"
    using trace_length by auto
  moreover have hdls: "hd ?ls = the (eval (Pr n f g) (y # xs))"
    using Suc trace_hd by auto
  ultimately have g:
    "eval g (y # hd ?ls # xs) \<down>"
    "eval (Pr n f g) (Suc y # xs) = eval g (y # hd ?ls # xs)"
    using eval_Pr_Suc_converg hdls valid(1) Suc by simp_all
  then have "reachable (?stack, None) ((Pr n f g, x # xs, ?ls) # rest, None)"
      (is "_ (?stack1, None)")
    using Suc valid(1) by fastforce
  also have "reachable ... ((g, y # hd ?ls # xs, []) # (Pr n f g, x # xs, ?ls) # rest, None)"
    using Suc.prems lenls by fastforce
  also have "reachable ... (?stack1, eval g (y # hd ?ls # xs))"
      (is "_ (_, ?rv)")
    using assms(3) g(1) valid valid_ConsI by auto
  also have "reachable ... ((Pr n f g, x # xs, (the ?rv) # ?ls) # rest, None)"
    using Suc.prems(1) g(1) lenls by auto
  finally have "reachable (?stack, None) ((Pr n f g, x # xs, (the ?rv) # ?ls) # rest, None)" .
  moreover have "trace n f g xs (Suc y) = (the ?rv) # ?ls"
    using g(2) trace_Suc by simp
  ultimately show ?case by simp
qed

lemma step_Pr_correct:
  assumes "valid (((Pr n f g), xs, []) # rest)" (is "valid ?stack")
    and "\<And>xs rest. valid ((f, xs, []) # rest) \<Longrightarrow> correct ((f, xs, []) # rest, None)"
    and "\<And>xs rest. valid ((g, xs, []) # rest) \<Longrightarrow> correct ((g, xs, []) # rest, None)"
  shows "correct (?stack, None)"
proof -
  have valid: "valid rest" "recfn (length xs) (Pr n f g)"
    using valid_ConsE[OF assms(1)] by simp_all
  then have "length xs > 0"
    by auto
  then obtain y ys where y_ys: "xs = y # ys"
    using list.exhaust_sel by auto
  let ?t = "trace n f g ys"
  consider
      (converg) "eval (Pr n f g) xs \<down>"
    | (diverg_f) "eval (Pr n f g) xs \<up>" and "eval f ys \<up>"
    | (diverg) "eval (Pr n f g) xs \<up>" and "eval f ys \<down>"
    by auto
  then show ?thesis
  proof (cases)
    case converg
    then have "\<And>z. z \<le> y \<Longrightarrow> reachable (?stack, None) (((Pr n f g), xs, ?t z) # rest, None)"
      using assms valid by (simp add: eval_Pr_converg_le reachable_Pr y_ys)
    then have "reachable (?stack, None) (((Pr n f g), xs, ?t y) # rest, None)"
      by simp
    moreover have "reachable (((Pr n f g), xs, ?t y) # rest, None) (rest, Some (hd (?t y)))"
      using trace_length step_reachable y_ys by fastforce
    ultimately have "reachable (?stack, None) (rest, Some (hd (?t y)))"
      using reachable_transitive by blast
    then show ?thesis
      using assms(1) trace_hd converg y_ys by simp
  next
    case diverg_f
    have *: "step (?stack, None) = ((f, ys, []) # ((Pr n f g), xs, []) # tl ?stack, None)"
        (is "_ = (?stack1, None)")
      using assms(1,2) y_ys by simp
    then have "reachable (?stack, None) (?stack1, None)"
      using step_reachable by force
    moreover have "nonterminating (?stack1, None)"
      using assms diverg_f valid valid_ConsI * by auto
    ultimately have "nonterminating (?stack, None)"
      using reachable_nonterminating by blast
    then show ?thesis using diverg_f(1) assms(1) by simp
  next
    case diverg
    let ?h = "\<lambda>z. the (eval (Pr n f g) (z # ys))"
    let ?Q = "\<lambda>z. z < y \<and> eval (Pr n f g) (z # ys) \<down>"
    have "?Q 0"
      using assms diverg neq0_conv y_ys valid by fastforce
    define zmax where "zmax = Greatest ?Q"
    then have "?Q zmax"
      using \<open>?Q 0\<close> GreatestI_nat[of ?Q 0 y] by simp
    have le_zmax: "\<And>z. ?Q z \<Longrightarrow> z \<le> zmax"
      using Greatest_le_nat[of ?Q _ y] zmax_def by simp
    have len: "length (?t zmax) < Suc y"
      by (simp add: \<open>?Q zmax\<close> trace_length)
    have "eval (Pr n f g) (y # ys) \<down>" if "y \<le> zmax" for y
      using that zmax_def \<open>?Q zmax\<close> assms eval_Pr_converg_le[of n f g ys zmax y] valid y_ys
      by simp
    then have "reachable (?stack, None) (((Pr n f g), xs, ?t y) # rest, None)"
        if "y \<le> zmax" for y
      using that \<open>?Q zmax\<close> diverg y_ys assms reachable_Pr by simp
    then have "reachable (?stack, None) (((Pr n f g), xs, ?t zmax) # rest, None)"
        (is "reachable _ (?stack1, None)")
      by simp
    also have "reachable ...
        ((g, zmax # ?h zmax # tl xs, []) # (Pr n f g, xs, ?t zmax) # rest, None)"
        (is "_ (?stack2, None)")
    proof (rule step_reachable)
      have "length (?t zmax) \<noteq> Suc (hd xs)"
        using len y_ys by simp
      moreover have "hd (?t zmax) = ?h zmax"
        using trace_hd by auto
      moreover have "length (?t zmax) = Suc zmax"
        using trace_length by simp
      ultimately show "step (?stack1, None) = (?stack2, None)" 
        by auto
    qed
    finally have "reachable (?stack, None) (?stack2, None)" .
    moreover have "nonterminating (?stack2, None)"
    proof -
      have "correct (?stack2, None)"
        using y_ys assms valid_ConsI valid by simp
      moreover have "eval g (zmax # ?h zmax # ys) \<up>"
        using \<open>?Q zmax\<close> diverg le_zmax len less_Suc_eq trace_length y_ys valid
        by fastforce
      ultimately show ?thesis using y_ys by simp
    qed
    ultimately have "nonterminating (?stack, None)"
      using reachable_nonterminating by simp
    then show ?thesis using diverg assms(1) by simp
  qed
qed

lemma reachable_Mn:
  assumes "valid ((Mn n f, xs, []) # rest)" (is "valid ?stack")
    and "\<And>xs rest. valid ((f, xs, []) # rest) \<Longrightarrow> correct ((f, xs, []) # rest, None)"
    and "\<forall>y<z. eval f (y # xs) \<notin> {None, Some 0}"
  shows "reachable (?stack, None) ((f, z # xs, []) # (Mn n f, xs, [z]) # rest, None)"
  using assms(3)
proof (induction z)
  case 0
  then have "step (?stack, None) = ((f, 0 # xs, []) # (Mn n f, xs, [0]) # rest, None)"
    using assms by simp
  then show ?case
    using step_reachable assms(1) by force
next
  case (Suc z)
  have valid: "valid rest" "recfn (length xs) (Mn n f)"
    using valid_ConsE[OF assms(1)] by auto
  have f: "eval f (z # xs) \<notin> {None, Some 0}"
    using Suc by simp
  have "reachable (?stack, None) ((f, z # xs, []) # (Mn n f, xs, [z]) # rest, None)"
    using Suc by simp
  also have "reachable ... ((Mn n f, xs, [z]) # rest, eval f (z # xs))"
    using f assms(2)[of "z # xs"] valid correct_convergE valid_ConsI by auto
  also have "reachable ... ((f, (Suc z) # xs, []) # (Mn n f, xs, [Suc z]) # rest, None)"
      (is "_  (?stack1, None)")
    using step_reachable f by force
  finally have "reachable (?stack, None) (?stack1, None)" .
  then show ?case by simp
qed

lemma iterate_step_empty_stack: "iterate t step ([], rv) = ([], rv)"
  using step_empty_stack by (induction t) simp_all

lemma reachable_iterate_step_empty_stack:
  assumes "reachable cfg ([], rv)"
  shows "\<exists>t. iterate t step cfg = ([], rv) \<and> (\<forall>t'<t. fst (iterate t' step cfg) \<noteq> [])"
proof -
  let ?P = "\<lambda>t. iterate t step cfg = ([], rv)"
  from assms have "\<exists>t. ?P t"
    by (simp add: reachable_def)
  moreover define tmin where "tmin = Least ?P"
  ultimately have "?P tmin"
    using LeastI_ex[of ?P] by simp
  have "fst (iterate t' step cfg) \<noteq> []" if "t' < tmin" for t'
  proof
    assume "fst (iterate t' step cfg) = []"
    then obtain v where v: "iterate t' step cfg = ([], v)"
      by (metis prod.exhaust_sel)
    then have "iterate t'' step ([], v) = ([], v)" for t''
      using iterate_step_empty_stack by simp
    then have "iterate (t' + t'') step cfg = ([], v)" for t''
      using v iterate_additive by fast
    moreover obtain t'' where "t' + t'' = tmin"
      using \<open>t' < tmin\<close> less_imp_add_positive by auto
    ultimately have "iterate tmin step cfg = ([], v)"
      by auto
    then have "v = rv"
      using \<open>?P tmin\<close> by simp
    then have "iterate t' step cfg = ([], rv)"
      using v by simp
    moreover have "\<forall>t'<tmin. \<not> ?P t'"
      unfolding tmin_def using not_less_Least[of _ ?P] by simp
    ultimately show False
      using that by simp
  qed
  then show ?thesis using \<open>?P tmin\<close> by auto
qed

lemma step_Mn_correct:
  assumes "valid ((Mn n f, xs, []) # rest)" (is "valid ?stack")
    and "\<And>xs rest. valid ((f, xs, []) # rest) \<Longrightarrow> correct ((f, xs, []) # rest, None)"
  shows "correct (?stack, None)"
proof -
  have valid: "valid rest" "recfn (length xs) (Mn n f)"
    using valid_ConsE[OF assms(1)] by auto
  consider
      (diverg) "eval (Mn n f) xs \<up>" and "\<forall>z. eval f (z # xs) \<down>"
    | (diverg_f) "eval (Mn n f) xs \<up>" and "\<exists>z. eval f (z # xs) \<up>"
    | (converg) "eval (Mn n f) xs \<down>"
    by fast
  then show ?thesis
  proof (cases)
    case diverg
    then have "\<forall>z. eval f (z # xs) \<noteq> Some 0"
      using eval_Mn_diverg[OF valid(2)] by simp
    then have "\<forall>y<z. eval f (y # xs) \<notin> {None, Some 0}" for z
      using diverg by simp
    then have reach_z:
      "\<And>z. reachable (?stack, None) ((f, z # xs, []) # (Mn n f, xs, [z]) # rest, None)"
      using reachable_Mn[OF assms] diverg by simp

    define h :: "nat \<Rightarrow> configuration" where
      "h z \<equiv> ((f, z # xs, []) # (Mn n f, xs, [z]) # rest, None)" for z
    then have h_inj: "\<And>x y. x \<noteq> y \<Longrightarrow> h x \<noteq> h y" and z_neq_Nil: "\<And>z. fst (h z) \<noteq> []"
      by simp_all

    have z: "\<exists>z\<^sub>0. \<forall>z>z\<^sub>0. \<not> (\<exists>t'\<le>t. iterate t' step (?stack, None) = h z)" for t
    proof (induction t)
      case 0
      then show ?case by (metis h_inj le_zero_eq less_not_refl3)
    next
      case (Suc t)
      then show ?case
        using h_inj by (metis (no_types, hide_lams) le_Suc_eq less_not_refl3 less_trans)
    qed

    have "nonterminating (?stack, None)"
    proof (rule ccontr)
      assume "\<not> nonterminating (?stack, None)"
      then obtain t where t: "fst (iterate t step (?stack, None)) = []"
        by auto
      then obtain z\<^sub>0 where "\<forall>z>z\<^sub>0. \<not> (\<exists>t'\<le>t. iterate t' step (?stack, None) = h z)"
        using z by auto
      then have not_h: "\<forall>t'\<le>t. iterate t' step (?stack, None) \<noteq> h (Suc z\<^sub>0)"
        by simp
      have "\<forall>t'\<ge>t. fst (iterate t' step (?stack, None)) = []"
        using t iterate_step_empty_stack iterate_additive'[of t]
        by (metis le_Suc_ex prod.exhaust_sel)
      then have "\<forall>t'\<ge>t. iterate t' step (?stack, None) \<noteq> h (Suc z\<^sub>0)"
        using z_neq_Nil by auto
      then have "\<forall>t'. iterate t' step (?stack, None) \<noteq> h (Suc z\<^sub>0)"
        using not_h nat_le_linear by auto
      then have "\<not> reachable (?stack, None) (h (Suc z\<^sub>0))"
        using reachable_def by simp
      then show False
        using reach_z[of "Suc z\<^sub>0"] h_def by simp
    qed
    then show ?thesis using diverg by simp
  next
    case diverg_f
    let ?P = "\<lambda>z. eval f (z # xs) \<up>"
    define zmin where "zmin \<equiv> Least ?P"
    then have "\<forall>y<zmin. eval f (y # xs) \<notin> {None, Some 0}"
      using diverg_f eval_Mn_diverg[OF valid(2)] less_trans not_less_Least[of _ ?P]
      by blast
    moreover have f_zmin: "eval f (zmin # xs) \<up>"
      using diverg_f LeastI_ex[of ?P] zmin_def by simp
    ultimately have
      "reachable (?stack, None) ((f, zmin # xs, []) # (Mn n f, xs, [zmin]) # rest, None)"
        (is "reachable _ (?stack1, None)")
      using reachable_Mn[OF assms] by simp
    moreover have "nonterminating (?stack1, None)"
      using f_zmin assms valid diverg_f valid_ConsI by auto
    ultimately have "nonterminating (?stack, None)"
      using reachable_nonterminating by simp
    then show ?thesis using diverg_f by simp
  next
    case converg
    then obtain z where z: "eval (Mn n f) xs \<down>= z" by auto
    have f_z: "eval f (z # xs) \<down>= 0"
      and f_less_z: "\<And>y. y < z \<Longrightarrow> eval f (y # xs) \<down>\<noteq> 0"
      using eval_Mn_convergE(2,3)[OF valid(2) z] by simp_all
    then have
      "reachable (?stack, None) ((f, z # xs, []) # (Mn n f, xs, [z]) # rest, None)"
      using reachable_Mn[OF assms] by simp
    also have "reachable ... ((Mn n f, xs, [z]) # rest, eval f (z # xs))"
      using assms(2)[of "z # xs"] valid f_z valid_ConsI correct_convergE
      by auto
    also have "reachable ... (rest, Some z)"
      using f_z f_less_z step_reachable by auto
    finally have "reachable (?stack, None) (rest, Some z)" .
    then show ?thesis using z by simp
  qed
qed

theorem step_correct:
  assumes "valid ((f, xs, []) # rest)"
  shows "correct ((f, xs, []) # rest, None)"
  using assms
proof (induction f arbitrary: xs rest)
  case Z
  then show ?case using valid_ConsE[of Z] step_reachable by auto
next
  case S
  then show ?case using valid_ConsE[of S] step_reachable by auto
next
  case (Id m n)
  then show ?case using valid_ConsE[of "Id m n"] by auto
next
  case Cn
  then show ?case using step_Cn_correct by presburger
next
  case Pr
  then show ?case using step_Pr_correct by simp
next
  case Mn
  then show ?case using step_Mn_correct by presburger
qed


subsection \<open>Encoding partial recursive functions\label{s:recf_enc}\<close>

text \<open>In this section we define an injective, but not surjective,
mapping from @{typ recf}s to natural numbers.\<close>

abbreviation triple_encode :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
   "triple_encode x y z \<equiv> prod_encode (x, prod_encode (y, z))"

abbreviation quad_encode :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
   "quad_encode w x y z \<equiv> prod_encode (w, prod_encode (x, prod_encode (y, z)))"

fun encode :: "recf \<Rightarrow> nat" where
  "encode Z = 0"
| "encode S = 1"
| "encode (Id m n) = triple_encode 2 m n"
| "encode (Cn n f gs) = quad_encode 3 n (encode f) (list_encode (map encode gs))"
| "encode (Pr n f g) = quad_encode 4 n (encode f) (encode g)"
| "encode (Mn n f) = triple_encode 5 n (encode f)"

lemma prod_encode_gr1: "a > 1 \<Longrightarrow> prod_encode (a, x) > 1"
  using le_prod_encode_1 less_le_trans by blast

lemma encode_not_Z_or_S: "encode f = prod_encode (a, b) \<Longrightarrow> a > 1 \<Longrightarrow> f \<noteq> Z \<and> f \<noteq> S"
  by (metis encode.simps(1) encode.simps(2) less_numeral_extra(4) not_one_less_zero
    prod_encode_gr1)

lemma encode_injective: "encode f = encode g \<Longrightarrow> f = g"
proof (induction g arbitrary: f)
  case Z
  have "\<And>a x. a > 1 \<Longrightarrow> prod_encode (a, x) > 0"
    using prod_encode_gr1 by (meson less_one less_trans)
  then have "f \<noteq> Z \<Longrightarrow> encode f > 0"
    by (cases f) auto
  then have "encode f = 0 \<Longrightarrow> f = Z" by fastforce
  then show ?case using Z by simp
next
  case S
  have "\<And>a x. a > 1 \<Longrightarrow> prod_encode (a, x) \<noteq> Suc 0"
    using prod_encode_gr1 by (metis One_nat_def less_numeral_extra(4))
  then have "encode f = 1 \<Longrightarrow> f = S"
    by (cases f) auto
  then show ?case using S by simp
next
  case Id
  then obtain z where *: "encode f = prod_encode (2, z)" by simp
  show ?case
    using Id by (cases f) (simp_all add: * encode_not_Z_or_S prod_encode_eq)
next
  case Cn
  then obtain z where *: "encode f = prod_encode (3, z)" by simp
  show ?case
  proof (cases f)
    case Z
    then show ?thesis using * encode_not_Z_or_S by simp
  next
    case S
    then show ?thesis using * encode_not_Z_or_S by simp
  next
    case Id
    then show ?thesis using * by (simp add: prod_encode_eq)
  next
    case Cn
    then show ?thesis
      using * Cn.IH Cn.prems list_decode_encode
      by (smt encode.simps(4) fst_conv list.inj_map_strong prod_encode_eq snd_conv)
  next
    case Pr
    then show ?thesis using * by (simp add: prod_encode_eq)
  next
    case Mn
    then show ?thesis using * by (simp add: prod_encode_eq)
  qed
next
  case Pr
  then obtain z where *: "encode f = prod_encode (4, z)" by simp
  show ?case
    using Pr by (cases f) (simp_all add: * encode_not_Z_or_S prod_encode_eq)
next
  case Mn
  then obtain z where *: "encode f = prod_encode (5, z)" by simp
  show ?case
    using Mn by (cases f) (simp_all add: * encode_not_Z_or_S prod_encode_eq)
qed

definition encode_kind :: "nat \<Rightarrow> nat" where
  "encode_kind e \<equiv> if e = 0 then 0 else if e = 1 then 1 else pdec1 e"

lemma encode_kind_0: "encode_kind (encode Z) = 0"
  unfolding encode_kind_def by simp

lemma encode_kind_1: "encode_kind (encode S) = 1"
  unfolding encode_kind_def by simp

lemma encode_kind_2: "encode_kind (encode (Id m n)) = 2"
  unfolding encode_kind_def
  by (metis encode.simps(1-3) encode_injective fst_conv prod_encode_inverse
    recf.simps(16) recf.simps(8))

lemma encode_kind_3: "encode_kind (encode (Cn n f gs)) = 3"
  unfolding encode_kind_def
  by (metis encode.simps(1,2,4) encode_injective fst_conv prod_encode_inverse
    recf.simps(10) recf.simps(18))

lemma encode_kind_4: "encode_kind (encode (Pr n f g)) = 4"
  unfolding encode_kind_def
  by (metis encode.simps(1,2,5) encode_injective fst_conv prod_encode_inverse
    recf.simps(12) recf.simps(20))

lemma encode_kind_5: "encode_kind (encode (Mn n f)) = 5"
  unfolding encode_kind_def
  by (metis encode.simps(1,2,6) encode_injective fst_conv prod_encode_inverse
    recf.simps(14) recf.simps(22))

lemmas encode_kind_n =
  encode_kind_0 encode_kind_1 encode_kind_2 encode_kind_3 encode_kind_4 encode_kind_5

lemma encode_kind_Cn:
  assumes "encode_kind (encode f) = 3"
  shows "\<exists>n f' gs. f = Cn n f' gs"
  using assms encode_kind_n by (cases f) auto

lemma encode_kind_Pr:
  assumes "encode_kind (encode f) = 4"
  shows "\<exists>n f' g. f = Pr n f' g"
  using assms encode_kind_n by (cases f) auto

lemma encode_kind_Mn:
  assumes "encode_kind (encode f) = 5"
  shows "\<exists>n g. f = Mn n g"
  using assms encode_kind_n by (cases f) auto

lemma pdec2_encode_Id: "pdec2 (encode (Id m n)) = prod_encode (m, n)"
  by simp

lemma pdec2_encode_Pr: "pdec2 (encode (Pr n f g)) = triple_encode n (encode f) (encode g)"
  by simp


subsection \<open>The step function on encoded configurations\label{s:step_enc}\<close>

text \<open>In this section we construct a function @{text "estep :: nat
\<Rightarrow> nat"} that is equivalent to the function @{text "step ::
configuration \<Rightarrow> configuration"} except that it applies to encoded
configurations. We start by defining an encoding for configurations.\<close>

definition encode_frame :: "frame \<Rightarrow> nat" where
  "encode_frame s \<equiv>
    triple_encode (encode (fst s)) (list_encode (fst (snd s))) (list_encode (snd (snd s)))" 

lemma encode_frame:
  "encode_frame (f, xs, ls) = triple_encode (encode f) (list_encode xs) (list_encode ls)"
  unfolding encode_frame_def by simp

abbreviation encode_option :: "nat option \<Rightarrow> nat" where
  "encode_option x \<equiv> if x = None then 0 else Suc (the x)"

definition encode_config :: "configuration \<Rightarrow> nat" where
  "encode_config cfg \<equiv>
     prod_encode (list_encode (map encode_frame (fst cfg)), encode_option (snd cfg))"

lemma encode_config:
  "encode_config (ss, rv) = prod_encode (list_encode (map encode_frame ss), encode_option rv)"
  unfolding encode_config_def by simp

text \<open>Various projections from encoded configurations:\<close>

definition e2stack where "e2stack e \<equiv> pdec1 e"
definition e2rv where "e2rv e \<equiv> pdec2 e"
definition e2tail where "e2tail e \<equiv> e_tl (e2stack e)"
definition e2frame where "e2frame e \<equiv> e_hd (e2stack e)"
definition e2i where "e2i e \<equiv> pdec1 (e2frame e)"
definition e2xs where "e2xs e \<equiv> pdec12 (e2frame e)"
definition e2ls where "e2ls e \<equiv> pdec22 (e2frame e)"
definition e2lenas where "e2lenas e \<equiv> e_length (e2xs e)"
definition e2lenls where "e2lenls e \<equiv> e_length (e2ls e)"

lemma e2rv_rv [simp]:
  "e2rv (encode_config (ss, rv)) = (if rv \<up> then 0 else Suc (the rv))"
  unfolding e2rv_def using encode_config by simp

lemma e2stack_stack [simp]:
  "e2stack (encode_config (ss, rv)) = list_encode (map encode_frame ss)"
  unfolding e2stack_def using encode_config by simp

lemma e2tail_tail [simp]:
  "e2tail (encode_config (s # ss, rv)) = list_encode (map encode_frame ss)"
  unfolding e2tail_def using encode_config by fastforce

lemma e2frame_frame [simp]:
  "e2frame (encode_config (s # ss, rv)) = encode_frame s"
  unfolding e2frame_def using encode_config by fastforce

lemma e2i_f [simp]:
  "e2i (encode_config ((f, xs, ls) # ss, rv)) = encode f"
  unfolding e2i_def using encode_config e2frame_frame encode_frame by force

lemma e2xs_xs [simp]:
  "e2xs (encode_config ((f, xs, ls) # ss, rv)) = list_encode xs"
  using e2xs_def e2frame_frame encode_frame by force

lemma e2ls_ls [simp]:
  "e2ls (encode_config ((f, xs, ls) # ss, rv)) = list_encode ls"
  using e2ls_def e2frame_frame encode_frame by force

lemma e2lenas_lenas [simp]:
  "e2lenas (encode_config ((f, xs, ls) # ss, rv)) = length xs"
  using e2lenas_def e2frame_frame encode_frame by simp

lemma e2lenls_lenls [simp]:
  "e2lenls (encode_config ((f, xs, ls) # ss, rv)) = length ls"
  using e2lenls_def e2frame_frame encode_frame by simp

lemma e2stack_0_iff_Nil:
  assumes "e = encode_config (ss, rv)"
  shows "e2stack e = 0 \<longleftrightarrow>  ss = []"
  using assms
  by (metis list_encode.simps(1) e2stack_stack list_encode_0 map_is_Nil_conv)

lemma e2ls_0_iff_Nil [simp]: "list_decode (e2ls e) = [] \<longleftrightarrow> e2ls e = 0"
  by (metis list_decode.simps(1) list_encode_decode)

text \<open>We now define @{text eterm} piecemeal by considering the more
complicated cases @{text Cn}, @{text Pr}, and @{text Mn} separately.\<close>

definition "estep_Cn e \<equiv>
  if e2lenls e = e_length (pdec222 (e2i e))
  then if e2rv e = 0
       then prod_encode (e_cons (triple_encode (pdec122 (e2i e)) (e2ls e) 0) (e2stack e), 0)
       else prod_encode (e2tail e, e2rv e)
  else if e2rv e = 0
       then if e2lenls e < e_length (pdec222 (e2i e))
            then prod_encode
              (e_cons
                (triple_encode (e_nth (pdec222 (e2i e)) (e2lenls e)) (e2xs e) 0)
                (e2stack e),
               0)
            else prod_encode (e2tail e, e2rv e)
       else prod_encode
         (e_cons
           (triple_encode (e2i e) (e2xs e) (e_snoc (e2ls e) (e2rv e - 1)))
           (e2tail e),
          0)"

lemma estep_Cn:
  assumes "c = (((Cn n f gs, xs, ls) # fs), rv)"
  shows "estep_Cn (encode_config c) = encode_config (step c)"
  using encode_frame by (simp add: assms estep_Cn_def, simp add: encode_config assms)

definition "estep_Pr e \<equiv>
  if e2ls e = 0
  then if e2rv e = 0
       then prod_encode
         (e_cons (triple_encode (pdec122 (e2i e)) (e_tl (e2xs e)) 0) (e2stack e),
          0)
       else prod_encode
         (e_cons (triple_encode (e2i e) (e2xs e) (singleton_encode (e2rv e - 1))) (e2tail e),
          0)
  else if e2lenls e = Suc (e_hd (e2xs e))
       then prod_encode (e2tail e, Suc (e_hd (e2ls e)))
       else if e2rv e = 0
            then prod_encode
              (e_cons
                (triple_encode
                  (pdec222 (e2i e))
                  (e_cons (e2lenls e - 1) (e_cons (e_hd (e2ls e)) (e_tl (e2xs e))))
                  0)
                (e2stack e),
                0)
            else prod_encode
              (e_cons
                (triple_encode (e2i e) (e2xs e) (e_cons (e2rv e - 1) (e2ls e))) (e2tail e),
                0)"

lemma estep_Pr1:
  assumes "c = (((Pr n f g, xs, ls) # fs), rv)"
    and "ls \<noteq> []"
    and "length ls \<noteq> Suc (hd xs)"
    and "rv \<noteq> None"
    and "recfn (length xs) (Pr n f g)"
  shows "estep_Pr (encode_config c) = encode_config (step c)"
proof -
  let ?e = "encode_config c"
  from assms(5) have "length xs > 0" by auto
  then have eq: "hd xs = e_hd (e2xs ?e)"
    using assms e_hd_def by auto
  have "step c = ((Pr n f g, xs, (the rv) # ls) # fs, None)"
      (is "step c = (?t # ?ss, None)")
    using assms by simp
  then have "encode_config (step c) =
      prod_encode (list_encode (map encode_frame (?t # ?ss)), 0)"
    using encode_config by simp
  also have "... =
      prod_encode (e_cons (encode_frame ?t) (list_encode (map encode_frame (?ss))), 0)"
    by simp
  also have "... = prod_encode (e_cons (encode_frame ?t) (e2tail ?e), 0)"
    using assms(1) by simp
  also have "... = prod_encode
      (e_cons
        (triple_encode (e2i ?e) (e2xs ?e) (e_cons (e2rv ?e - 1) (e2ls ?e)))
        (e2tail ?e),
       0)"
    by (simp add: assms encode_frame)
  finally show ?thesis
    using assms eq estep_Pr_def by auto
qed

lemma estep_Pr2:
  assumes "c = (((Pr n f g, xs, ls) # fs), rv)"
    and "ls \<noteq> []"
    and "length ls \<noteq> Suc (hd xs)"
    and "rv = None"
    and "recfn (length xs) (Pr n f g)"
  shows "estep_Pr (encode_config c) = encode_config (step c)"
proof -
  let ?e = "encode_config c"
  from assms(5) have "length xs > 0" by auto
  then have eq: "hd xs = e_hd (e2xs ?e)"
    using assms e_hd_def by auto
  have "step c = ((g, (length ls - 1) # hd ls # tl xs, []) # (Pr n f g, xs, ls) # fs, None)"
      (is "step c = (?t # ?ss, None)")
    using assms by simp
  then have "encode_config (step c) =
      prod_encode (list_encode (map encode_frame (?t # ?ss)), 0)"
    using encode_config by simp
  also have "... =
      prod_encode (e_cons (encode_frame ?t) (list_encode (map encode_frame (?ss))), 0)"
    by simp
  also have "... = prod_encode (e_cons (encode_frame ?t) (e2stack ?e), 0)"
    using assms(1) by simp
  also have "... = prod_encode
    (e_cons
      (triple_encode
        (pdec222 (e2i ?e))
        (e_cons (e2lenls ?e - 1) (e_cons (e_hd (e2ls ?e)) (e_tl (e2xs ?e))))
        0)
      (e2stack ?e),
     0)"
    using assms(1,2) encode_frame[of g "(length ls - 1) # hd ls # tl xs" "[]"]
      pdec2_encode_Pr[of n f g] e2xs_xs e2i_f e2lenls_lenls e2ls_ls e_hd
    by (metis list_encode.simps(1) list.collapse list_decode_encode
      prod_encode_inverse snd_conv)
  finally show ?thesis
    using assms eq estep_Pr_def by auto
qed

lemma estep_Pr3:
  assumes "c = (((Pr n f g, xs, ls) # fs), rv)"
    and "ls \<noteq> []"
    and "length ls = Suc (hd xs)"
    and "recfn (length xs) (Pr n f g)"
  shows "estep_Pr (encode_config c) = encode_config (step c)"
proof -
  let ?e = "encode_config c"
  from assms(4) have "length xs > 0" by auto
  then have "hd xs = e_hd (e2xs ?e)"
    using assms e_hd_def by auto
  then have "(length ls = Suc (hd xs)) = (e2lenls ?e = Suc (e_hd (e2xs ?e)))"
    using assms by simp
  then have *: "estep_Pr ?e = prod_encode (e2tail ?e, Suc (e_hd (e2ls ?e)))"
    using assms estep_Pr_def by auto
  have "step c = (fs, Some (hd ls))"
    using assms(1,2,3) by simp
  then have "encode_config (step c) =
      prod_encode (list_encode (map encode_frame fs), encode_option (Some (hd ls)))"
    using encode_config by simp
  also have "... =
      prod_encode (list_encode (map encode_frame fs), encode_option (Some (e_hd (e2ls ?e))))"
    using assms(1,2) e_hd_def by auto
  also have "... = prod_encode (list_encode (map encode_frame fs), Suc (e_hd (e2ls ?e)))"
    by simp
  also have "... = prod_encode (e2tail ?e, Suc (e_hd (e2ls ?e)))"
    using assms(1) by simp
  finally have "encode_config (step c) = prod_encode (e2tail ?e, Suc (e_hd (e2ls ?e)))" .
  then show ?thesis
    using estep_Pr_def * by presburger
qed

lemma estep_Pr4:
  assumes "c = (((Pr n f g, xs, ls) # fs), rv)" and "ls = []"
  shows "estep_Pr (encode_config c) = encode_config (step c)"
  using encode_frame
  by (simp add: assms estep_Pr_def, simp add: encode_config assms)

lemma estep_Pr:
  assumes "c = (((Pr n f g, xs, ls) # fs), rv)"
    and "recfn (length xs) (Pr n f g)"
  shows "estep_Pr (encode_config c) = encode_config (step c)"
  using assms estep_Pr1 estep_Pr2 estep_Pr3 estep_Pr4 by auto

definition "estep_Mn e \<equiv>
  if e2ls e = 0
  then prod_encode
    (e_cons
      (triple_encode (pdec22 (e2i e)) (e_cons 0 (e2xs e)) 0)
      (e_cons
        (triple_encode (e2i e) (e2xs e) (singleton_encode 0))
        (e2tail e)),
     0)
  else if e2rv e = 1
       then prod_encode (e2tail e, Suc (e_hd (e2ls e)))
       else prod_encode
        (e_cons
          (triple_encode (pdec22 (e2i e)) (e_cons (Suc (e_hd (e2ls e))) (e2xs e)) 0)
          (e_cons
            (triple_encode (e2i e) (e2xs e) (singleton_encode (Suc (e_hd (e2ls e)))))
            (e2tail e)),
        0)"

lemma estep_Mn:
  assumes "c = (((Mn n f, xs, ls) # fs), rv)"
  shows "estep_Mn (encode_config c) = encode_config (step c)"
proof -
  let ?e = "encode_config c"
  consider "ls \<noteq> []" and "rv \<noteq> Some 0" | "ls \<noteq> []" and "rv = Some 0" | "ls = []"
    by auto
  then show ?thesis
  proof (cases)
    case 1
    then have step_c: "step c =
       ((f, (Suc (hd ls)) # xs, []) # (Mn n f, xs, [Suc (hd ls)]) # fs, None)"
        (is "step c = ?cfg")
      using assms by simp
    have "estep_Mn ?e =
      prod_encode
        (e_cons
          (triple_encode (encode f) (e_cons (Suc (hd ls)) (list_encode xs)) 0)
          (e_cons
            (triple_encode (encode (Mn n f)) (list_encode xs) (singleton_encode (Suc (hd ls))))
            (list_encode (map encode_frame fs))),
        0)"
      using 1 assms e_hd_def estep_Mn_def by auto
    also have "... = encode_config ?cfg"
      using encode_config by (simp add: encode_frame)
    finally show ?thesis
      using step_c by simp
  next
    case 2
    have "estep_Mn ?e = prod_encode (e2tail ?e, Suc (e_hd (e2ls ?e)))"
      using 2 assms estep_Mn_def by auto
    also have "... = prod_encode (e2tail ?e, Suc (hd ls))"
      using 2 assms e_hd_def by auto
    also have "... = prod_encode (list_encode (map encode_frame fs), Suc (hd ls))"
      using assms by simp
    also have "... = encode_config (fs, Some (hd ls))"
      using encode_config by simp
    finally show ?thesis
      using 2 assms by simp
  next
    case 3
    then show ?thesis
      using assms encode_frame by (simp add: estep_Mn_def, simp add: encode_config)
  qed
qed

definition "estep e \<equiv>
  if e2stack e = 0 then prod_encode (0, e2rv e)
  else if e2i e = 0 then prod_encode (e2tail e, 1)
  else if e2i e = 1 then prod_encode (e2tail e, Suc (Suc (e_hd (e2xs e))))
  else if encode_kind (e2i e) = 2 then
    prod_encode (e2tail e, Suc (e_nth (e2xs e) (pdec22 (e2i e))))
  else if encode_kind (e2i e) = 3 then estep_Cn e
  else if encode_kind (e2i e) = 4 then estep_Pr e
  else if encode_kind (e2i e) = 5 then estep_Mn e
  else 0"

lemma estep_Z:
  assumes "c = (((Z, xs, ls) # fs), rv)"
  shows "estep (encode_config c) = encode_config (step c)"
  using encode_frame by (simp add: assms estep_def, simp add: encode_config assms)

lemma estep_S:
  assumes "c = (((S, xs, ls) # fs), rv)"
    and "recfn (length xs) (fst (hd (fst c)))"
  shows "estep (encode_config c) = encode_config (step c)"
proof -
  let ?e = "encode_config c"
  from assms have "length xs > 0" by auto
  then have eq: "hd xs = e_hd (e2xs ?e)"
    using assms(1) e_hd_def by auto
  then have "estep ?e = prod_encode (e2tail ?e, Suc (Suc (e_hd (e2xs ?e))))"
    using assms(1) estep_def by simp
  moreover have "step c = (fs, Some (Suc (hd xs)))"
    using assms(1) by simp
  ultimately show ?thesis
    using assms(1) eq estep_def encode_config[of fs "Some (Suc (hd xs))"] by simp
qed

lemma estep_Id:
  assumes "c = (((Id m n, xs, ls) # fs), rv)"
    and "recfn (length xs) (fst (hd (fst c)))"
  shows "estep (encode_config c) = encode_config (step c)"
proof -
  let ?e = "encode_config c"
  from assms have "length xs = m" and "m > 0" by auto
  then have eq: "xs ! n = e_nth (e2xs ?e) n"
    using assms e_hd_def by auto
  moreover have "encode_kind (e2i ?e) = 2"
    using assms(1) encode_kind_2 by auto
  ultimately have "estep ?e =
      prod_encode (e2tail ?e, Suc (e_nth (e2xs ?e) (pdec22 (e2i ?e))))"
    using assms estep_def encode_kind_def by auto
  moreover have "step c = (fs, Some (xs ! n))"
    using assms(1) by simp
  ultimately show ?thesis
    using assms(1) eq encode_config[of fs "Some (xs ! n)"] by simp
qed

lemma estep:
  assumes "valid (fst c)"
  shows "estep (encode_config c) = encode_config (step c)"
proof (cases "fst c")
  case Nil
  then show ?thesis
    using estep_def
    by (metis list_encode.simps(1) e2rv_def e2stack_stack encode_config_def
      map_is_Nil_conv prod.collapse prod_encode_inverse snd_conv step.simps(1))
next
  case (Cons s fs)
  then obtain f xs ls rv where c: "c = ((f, xs, ls) # fs, rv)"
    by (metis prod.exhaust_sel)
  with assms valid_def have lenas: "recfn (length xs) f" by simp
  show ?thesis
  proof (cases f)
    case Z
    then show ?thesis using estep_Z c by simp
  next
    case S
    then show ?thesis using estep_S c lenas by simp
  next
    case Id
    then show ?thesis using estep_Id c lenas by simp
  next
    case Cn
    then show ?thesis
      using estep_Cn c
      by (metis e2i_f e2stack_0_iff_Nil encode.simps(1) encode.simps(2) encode_kind_2
        encode_kind_3 encode_kind_Cn estep_def list.distinct(1) recf.distinct(13)
        recf.distinct(19) recf.distinct(5))
  next
    case Pr
    then show ?thesis
      using estep_Pr c lenas
      by (metis e2i_f e2stack_0_iff_Nil encode.simps(1) encode.simps(2) encode_kind_2
        encode_kind_4 encode_kind_Cn encode_kind_Pr estep_def list.distinct(1) recf.distinct(15)
        recf.distinct(21) recf.distinct(25) recf.distinct(7))
  next
    case Mn
    then show ?thesis
      using estep_Pr c lenas
      by (metis (no_types, lifting) e2i_f e2stack_0_iff_Nil encode.simps(1)
        encode.simps(2) encode_kind_2 encode_kind_5 encode_kind_Cn encode_kind_Mn encode_kind_Pr
        estep_Mn estep_def list.distinct(1) recf.distinct(17) recf.distinct(23)
        recf.distinct(27) recf.distinct(9))
  qed
qed

subsection \<open>The step function as a partial recursive function\label{s:step_recf}\<close>

text \<open>In this section we construct a primitive recursive function
@{term r_step} computing @{term estep}. This will entail defining @{typ
recf}s for many functions defined in the previous section.\<close>

definition "r_e2stack \<equiv> r_pdec1"

lemma r_e2stack_prim: "prim_recfn 1 r_e2stack"
  unfolding r_e2stack_def using r_pdec1_prim by simp

lemma r_e2stack [simp]: "eval r_e2stack [e] \<down>= e2stack e"
  unfolding r_e2stack_def e2stack_def using r_pdec1_prim by simp

definition "r_e2rv \<equiv> r_pdec2"

lemma r_e2rv_prim: "prim_recfn 1 r_e2rv"
  unfolding r_e2rv_def using r_pdec2_prim by simp

lemma r_e2rv [simp]: "eval r_e2rv [e] \<down>= e2rv e"
  unfolding r_e2rv_def e2rv_def using r_pdec2_prim by simp

definition "r_e2tail \<equiv> Cn 1 r_tl [r_e2stack]"

lemma r_e2tail_prim: "prim_recfn 1 r_e2tail"
  unfolding r_e2tail_def using r_e2stack_prim r_tl_prim by simp

lemma r_e2tail [simp]: "eval r_e2tail [e] \<down>= e2tail e"
  unfolding r_e2tail_def e2tail_def using r_e2stack_prim r_tl_prim by simp

definition "r_e2frame \<equiv> Cn 1 r_hd [r_e2stack]"

lemma r_e2frame_prim: "prim_recfn 1 r_e2frame"
  unfolding r_e2frame_def using r_hd_prim r_e2stack_prim by simp

lemma r_e2frame [simp]: "eval r_e2frame [e] \<down>= e2frame e"
  unfolding r_e2frame_def e2frame_def using r_hd_prim r_e2stack_prim by simp

definition "r_e2i \<equiv> Cn 1 r_pdec1 [r_e2frame]"

lemma r_e2i_prim: "prim_recfn 1 r_e2i"
  unfolding r_e2i_def using r_pdec12_prim r_e2frame_prim by simp

lemma r_e2i [simp]: "eval r_e2i [e] \<down>= e2i e"
  unfolding r_e2i_def e2i_def using r_pdec12_prim r_e2frame_prim by simp

definition "r_e2xs \<equiv> Cn 1 r_pdec12 [r_e2frame]"

lemma r_e2xs_prim: "prim_recfn 1 r_e2xs"
  unfolding r_e2xs_def using r_pdec122_prim r_e2frame_prim by simp

lemma r_e2xs [simp]: "eval r_e2xs [e] \<down>= e2xs e"
  unfolding r_e2xs_def e2xs_def using r_pdec122_prim r_e2frame_prim by simp

definition "r_e2ls \<equiv> Cn 1 r_pdec22 [r_e2frame]"

lemma r_e2ls_prim: "prim_recfn 1 r_e2ls"
  unfolding r_e2ls_def using r_pdec222_prim r_e2frame_prim by simp

lemma r_e2ls [simp]: "eval r_e2ls [e] \<down>= e2ls e"
  unfolding r_e2ls_def e2ls_def using r_pdec222_prim r_e2frame_prim by simp

definition "r_e2lenls \<equiv> Cn 1 r_length [r_e2ls]"

lemma r_e2lenls_prim: "prim_recfn 1 r_e2lenls"
  unfolding r_e2lenls_def using r_length_prim r_e2ls_prim by simp

lemma r_e2lenls [simp]: "eval r_e2lenls [e] \<down>= e2lenls e"
  unfolding r_e2lenls_def e2lenls_def using r_length_prim r_e2ls_prim by simp

definition "r_kind \<equiv>
  Cn 1 r_ifz [Id 1 0, Z, Cn 1 r_ifeq [Id 1 0, r_const 1, r_const 1, r_pdec1]]"

lemma r_kind_prim: "prim_recfn 1 r_kind"
  unfolding r_kind_def by simp

lemma r_kind: "eval r_kind [e] \<down>= encode_kind e"
  unfolding r_kind_def encode_kind_def by simp

lemmas helpers_for_r_step_prim =
  r_e2i_prim
  r_e2lenls_prim
  r_e2ls_prim
  r_e2rv_prim
  r_e2xs_prim
  r_e2stack_prim
  r_e2tail_prim
  r_e2frame_prim

text \<open>We define primitive recursive functions @{term r_step_Id}, @{term
r_step_Cn}, @{term r_step_Pr}, and @{term r_step_Mn}. The last three
correspond to @{term estep_Cn}, @{term estep_Pr}, and @{term estep_Mn} from
the previous section.\<close>

definition "r_step_Id \<equiv>
  Cn 1 r_prod_encode [r_e2tail, Cn 1 S [Cn 1 r_nth [r_e2xs, Cn 1 r_pdec22 [r_e2i]]]]"

lemma r_step_Id:
  "eval r_step_Id [e] \<down>= prod_encode (e2tail e, Suc (e_nth (e2xs e) (pdec22 (e2i e))))"
  unfolding r_step_Id_def using helpers_for_r_step_prim by simp

abbreviation r_triple_encode :: "recf \<Rightarrow> recf \<Rightarrow> recf \<Rightarrow> recf" where
  "r_triple_encode x y z \<equiv> Cn 1 r_prod_encode [x, Cn 1 r_prod_encode [y, z]]"

definition "r_step_Cn \<equiv>
  Cn 1 r_ifeq
   [r_e2lenls,
    Cn 1 r_length [Cn 1 r_pdec222 [r_e2i]],
    Cn 1 r_ifz
     [r_e2rv,
      Cn 1 r_prod_encode
       [Cn 1 r_cons [r_triple_encode (Cn 1 r_pdec122 [r_e2i]) r_e2ls Z, r_e2stack],
        Z],
      Cn 1 r_prod_encode [r_e2tail, r_e2rv]],
    Cn 1 r_ifz
     [r_e2rv,
      Cn 1 r_ifless
       [r_e2lenls,
        Cn 1 r_length [Cn 1 r_pdec222 [r_e2i]],
        Cn 1 r_prod_encode
         [Cn 1 r_cons
           [r_triple_encode (Cn 1 r_nth [Cn 1 r_pdec222 [r_e2i], r_e2lenls]) r_e2xs Z,
            r_e2stack],
          Z],
        Cn 1 r_prod_encode [r_e2tail, r_e2rv]],
      Cn 1 r_prod_encode
       [Cn 1 r_cons
         [r_triple_encode r_e2i r_e2xs (Cn 1 r_snoc [r_e2ls, Cn 1 r_dec [r_e2rv]]),
          r_e2tail],
        Z]]]"

lemma r_step_Cn_prim: "prim_recfn 1 r_step_Cn"
  unfolding r_step_Cn_def using helpers_for_r_step_prim by simp

lemma r_step_Cn: "eval r_step_Cn [e] \<down>= estep_Cn e"
  unfolding r_step_Cn_def estep_Cn_def using helpers_for_r_step_prim by simp

definition "r_step_Pr \<equiv>
  Cn 1 r_ifz
   [r_e2ls,
    Cn 1 r_ifz
     [r_e2rv,
      Cn 1 r_prod_encode
       [Cn 1 r_cons
         [r_triple_encode (Cn 1 r_pdec122 [r_e2i]) (Cn 1 r_tl [r_e2xs]) Z,
          r_e2stack],
        Z],
      Cn 1 r_prod_encode
       [Cn 1 r_cons
         [r_triple_encode r_e2i r_e2xs (Cn 1 r_singleton_encode [Cn 1 r_dec [r_e2rv]]),
          r_e2tail],
        Z]],
    Cn 1 r_ifeq
     [r_e2lenls,
      Cn 1 S [Cn 1 r_hd [r_e2xs]],
      Cn 1 r_prod_encode [r_e2tail, Cn 1 S [Cn 1 r_hd [r_e2ls]]],
      Cn 1 r_ifz
        [r_e2rv,
         Cn 1 r_prod_encode
           [Cn 1 r_cons
             [r_triple_encode
               (Cn 1 r_pdec222 [r_e2i])
               (Cn 1 r_cons
                 [Cn 1 r_dec [r_e2lenls],
                  Cn 1 r_cons [Cn 1 r_hd [r_e2ls],
                  Cn 1 r_tl [r_e2xs]]])
               Z,
              r_e2stack],
            Z],
         Cn 1 r_prod_encode
           [Cn 1 r_cons
             [r_triple_encode r_e2i r_e2xs (Cn 1 r_cons [Cn 1 r_dec [r_e2rv], r_e2ls]),
              r_e2tail],
            Z]]]]"

lemma r_step_Pr_prim: "prim_recfn 1 r_step_Pr"
  unfolding r_step_Pr_def using helpers_for_r_step_prim by simp

lemma r_step_Pr: "eval r_step_Pr [e] \<down>= estep_Pr e"
  unfolding r_step_Pr_def estep_Pr_def using helpers_for_r_step_prim by simp

definition "r_step_Mn \<equiv>
  Cn 1 r_ifz
   [r_e2ls,
    Cn 1 r_prod_encode
      [Cn 1 r_cons
        [r_triple_encode (Cn 1 r_pdec22 [r_e2i]) (Cn 1 r_cons [Z, r_e2xs]) Z,
         Cn 1 r_cons
           [r_triple_encode r_e2i r_e2xs (Cn 1 r_singleton_encode [Z]),
            r_e2tail]],
       Z],
    Cn 1 r_ifeq
      [r_e2rv,
       r_const 1,
       Cn 1 r_prod_encode [r_e2tail, Cn 1 S [Cn 1 r_hd [r_e2ls]]],
       Cn 1 r_prod_encode
         [Cn 1 r_cons
           [r_triple_encode
             (Cn 1 r_pdec22 [r_e2i])
             (Cn 1 r_cons [Cn 1 S [Cn 1 r_hd [r_e2ls]], r_e2xs])
             Z,
            Cn 1 r_cons
              [r_triple_encode r_e2i r_e2xs (Cn 1 r_singleton_encode [Cn 1 S [Cn 1 r_hd [r_e2ls]]]),
               r_e2tail]],
          Z]]]"

lemma r_step_Mn_prim: "prim_recfn 1 r_step_Mn"
  unfolding r_step_Mn_def using helpers_for_r_step_prim by simp

lemma r_step_Mn: "eval r_step_Mn [e] \<down>= estep_Mn e"
  unfolding r_step_Mn_def estep_Mn_def using helpers_for_r_step_prim by simp

definition "r_step \<equiv>
  Cn 1 r_ifz
    [r_e2stack,
     Cn 1 r_prod_encode [Z, r_e2rv],
     Cn 1 r_ifz
       [r_e2i,
        Cn 1 r_prod_encode [r_e2tail, r_const 1],
        Cn 1 r_ifeq
          [r_e2i,
           r_const 1,
           Cn 1 r_prod_encode [r_e2tail, Cn 1 S [Cn 1 S [Cn 1 r_hd [r_e2xs]]]],
           Cn 1 r_ifeq
             [Cn 1 r_kind [r_e2i],
              r_const 2,
              Cn 1 r_prod_encode [r_e2tail, Cn 1 S [Cn 1 r_nth [r_e2xs, Cn 1 r_pdec22 [r_e2i]]]],
              Cn 1 r_ifeq
                [Cn 1 r_kind [r_e2i],
                 r_const 3,
                 r_step_Cn,
                 Cn 1 r_ifeq
                   [Cn 1 r_kind [r_e2i],
                    r_const 4,
                    r_step_Pr,
                    Cn 1 r_ifeq
                      [Cn 1 r_kind [r_e2i], r_const 5, r_step_Mn, Z]]]]]]]"

lemma r_step_prim: "prim_recfn 1 r_step"
  unfolding r_step_def
  using r_kind_prim r_step_Mn_prim r_step_Pr_prim r_step_Cn_prim helpers_for_r_step_prim
  by simp

lemma r_step: "eval r_step [e] \<down>= estep e"
  unfolding r_step_def estep_def
  using r_kind_prim r_step_Mn_prim r_step_Pr_prim r_step_Cn_prim helpers_for_r_step_prim
    r_kind r_step_Cn r_step_Pr r_step_Mn
  by simp

theorem r_step_equiv_step:
  assumes "valid (fst c)"
  shows "eval r_step [encode_config c] \<down>= encode_config (step c)"
  using r_step estep assms by simp


subsection \<open>The universal function\label{s:the_universal}\<close>

text \<open>The next function computes the configuration after arbitrarily
many steps.\<close>

definition "r_leap \<equiv>
  Pr 2
   (Cn 2 r_prod_encode
     [Cn 2 r_singleton_encode
       [Cn 2 r_prod_encode [Id 2 0, Cn 2 r_prod_encode [Id 2 1, r_constn 1 0]]],
      r_constn 1 0])
   (Cn 4 r_step [Id 4 1])"

lemma r_leap_prim [simp]: "prim_recfn 3 r_leap"
  unfolding r_leap_def using r_step_prim by simp

lemma r_leap_total: "eval r_leap [t, i, x] \<down>"
  using prim_recfn_total[OF r_leap_prim] by simp

lemma r_leap:
  assumes "i = encode f" and "recfn (e_length x) f"
  shows "eval r_leap [t, i, x] \<down>= encode_config (iterate t step ([(f, list_decode x, [])], None))"
proof (induction t)
  case 0
  then show ?case
    unfolding r_leap_def using r_step_prim assms encode_config encode_frame by simp
next
  case (Suc t)
  let ?c = "([(f, list_decode x, [])], None)"
  let ?tc = "iterate t step ?c"
  have "valid (fst ?c)"
    using valid_def assms by simp
  then have valid: "valid (fst ?tc)"
    using iterate_step_valid by simp
  have "eval r_leap [Suc t, i, x] =
      eval (Cn 4 r_step [Id 4 1]) [t, the (eval r_leap [t, i, x]), i, x]"
    by (smt One_nat_def Suc_eq_plus1 eq_numeral_Suc eval_Pr_converg_Suc list.size(3) list.size(4) nat_1_add_1 pred_numeral_simps(3) r_leap_def r_leap_prim r_leap_total)
  then have "eval r_leap [Suc t, i, x] = eval (Cn 4 r_step [Id 4 1]) [t, encode_config ?tc, i, x]"
    using Suc by simp
  then have "eval r_leap [Suc t, i, x] = eval r_step [encode_config ?tc]"
    using r_step_prim by simp
  then have "eval r_leap [Suc t, i, x] \<down>= encode_config (step ?tc)"
    by (simp add: r_step_equiv_step valid)
  then show ?case by simp
qed

lemma step_leaves_empty_stack_empty:
  assumes "iterate t step ([(f, list_decode x, [])], None) = ([], Some v)"
  shows "iterate (t + t') step ([(f, list_decode x, [])], None) = ([], Some v)"
  using assms by (induction t') simp_all

text \<open>The next function is essentially a convenience wrapper around
@{term r_leap}. It returns zero if the configuration returned by @{term
r_leap} is non-final, and @{term "Suc v"} if the configuration is final with
return value $v$.\<close>

definition "r_result \<equiv>
  Cn 3 r_ifz [Cn 3 r_pdec1 [r_leap], Cn 3 r_pdec2 [r_leap], r_constn 2 0]"

lemma r_result_prim [simp]: "prim_recfn 3 r_result"
  unfolding r_result_def using r_leap_prim by simp

lemma r_result_total: "total r_result"
  using r_result_prim by blast

lemma r_result_empty_stack_None:
  assumes "i = encode f"
    and "recfn (e_length x) f"
    and "iterate t step ([(f, list_decode x, [])], None) = ([], None)"
  shows "eval r_result [t, i, x] \<down>= 0"
  unfolding r_result_def
  using assms r_leap e2stack_0_iff_Nil e2stack_def e2stack_stack r_leap_total r_leap_prim
    e2rv_def e2rv_rv
  by simp

lemma r_result_empty_stack_Some:
  assumes "i = encode f"
    and "recfn (e_length x) f"
    and "iterate t step ([(f, list_decode x, [])], None) = ([], Some v)"
  shows "eval r_result [t, i, x] \<down>= Suc v"
  unfolding r_result_def
  using assms r_leap e2stack_0_iff_Nil e2stack_def e2stack_stack r_leap_total r_leap_prim
    e2rv_def e2rv_rv
  by simp

lemma r_result_empty_stack_stays:
  assumes "i = encode f"
    and "recfn (e_length x) f"
    and "iterate t step ([(f, list_decode x, [])], None) = ([], Some v)"
  shows "eval r_result [t + t', i, x] \<down>= Suc v"
  using assms step_leaves_empty_stack_empty r_result_empty_stack_Some by simp

lemma r_result_nonempty_stack:
  assumes "i = encode f"
    and "recfn (e_length x) f"
    and "fst (iterate t step ([(f, list_decode x, [])], None)) \<noteq> []"
  shows "eval r_result [t, i, x] \<down>= 0"
proof -
  obtain ss rv where "iterate t step ([(f, list_decode x, [])], None) = (ss, rv)"
    by fastforce
  moreover from this assms(3) have "ss \<noteq> []" by simp
  ultimately have "eval r_leap [t, i, x] \<down>= encode_config (ss, rv)"
    using assms r_leap by simp
  then have "eval (Cn 3 r_pdec1 [r_leap]) [t, i, x] \<down>\<noteq> 0"
    using \<open>ss \<noteq> []\<close> r_leap_prim encode_config r_leap_total list_encode_0
    by (auto, blast)
  then show ?thesis unfolding r_result_def using r_leap_prim by auto
qed

lemma r_result_Suc:
  assumes "i = encode f"
    and "recfn (e_length x) f"
    and "eval r_result [t, i, x] \<down>= Suc v"
  shows "iterate t step ([(f, list_decode x, [])], None) = ([], Some v)"
    (is "?cfg = _")
proof (cases "fst ?cfg")
  case Nil
  then show ?thesis
    using assms r_result_empty_stack_None r_result_empty_stack_Some
    by (metis Zero_not_Suc nat.inject option.collapse option.inject prod.exhaust_sel)
next
  case Cons
  then show ?thesis using assms r_result_nonempty_stack by simp
qed

lemma r_result_converg:
  assumes "i = encode f"
    and "recfn (e_length x) f"
    and "eval f (list_decode x) \<down>= v"
  shows "\<exists>t.
    (\<forall>t'\<ge>t. eval r_result [t', i, x] \<down>= Suc v) \<and>
    (\<forall>t'<t. eval r_result [t', i, x] \<down>= 0)"
proof -
  let ?xs = "list_decode x"
  let ?stack = "[(f, ?xs, [])]"
  have "wellf f" using assms(2) by simp
  moreover have "length ?xs = arity f"
    using assms(2) by simp
  ultimately have "correct (?stack, None)"
    using step_correct valid_def by simp
  with assms(3) have "reachable (?stack, None) ([], Some v)"
    by simp
  then obtain t where
    "iterate t step (?stack, None) = ([], Some v)"
    "\<forall>t'<t. fst (iterate t' step (?stack, None)) \<noteq> []"
    using reachable_iterate_step_empty_stack by blast
  then have t:
    "eval r_result [t, i, x] \<down>= Suc v"
    "\<forall>t'<t. eval r_result [t', i, x] \<down>= 0"
    using r_result_empty_stack_Some r_result_nonempty_stack assms(1,2)
    by simp_all
  then have "eval r_result [t + t', i, x] \<down>= Suc v" for t'
    using r_result_empty_stack_stays assms r_result_Suc by simp
  then have "\<forall>t'\<ge>t. eval r_result [t', i, x] \<down>= Suc v"
    using le_Suc_ex by blast
  with t(2) show ?thesis by auto
qed

lemma r_result_diverg:
  assumes "i = encode f"
    and "recfn (e_length x) f"
    and "eval f (list_decode x) \<up>"
  shows "eval r_result [t, i, x] \<down>= 0"
proof -
  let ?xs = "list_decode x"
  let ?stack = "[(f, ?xs, [])]"
  have "recfn (length ?xs) f"
    using assms(2) by auto
  then have "correct (?stack, None)"
    using step_correct valid_def by simp
  with assms(3) have "nonterminating (?stack, None)"
    by simp
  then show ?thesis
    using r_result_nonempty_stack assms(1,2) by simp
qed

text \<open>Now we can define the universal partial recursive function. This
function executes @{term r_result} for increasing time bounds, waits for it
to reach a final configuration, and then extracts its result value. If no
final configuration is reached, the universal function diverges.\<close>

definition "r_univ \<equiv>
  Cn 2 r_dec [Cn 2 r_result [Mn 2 (Cn 3 r_not [r_result]), Id 2 0, Id 2 1]]"

lemma r_univ_recfn [simp]: "recfn 2 r_univ"
  unfolding r_univ_def by simp

theorem r_univ:
  assumes "i = encode f" and "recfn (e_length x) f"
  shows "eval r_univ [i, x] = eval f (list_decode x)"
proof -
  let ?cond = "Cn 3 r_not [r_result]"
  let ?while = "Mn 2 ?cond"
  let ?res = "Cn 2 r_result [?while, Id 2 0, Id 2 1]"
  let ?xs = "list_decode x"
  have *: "eval ?cond [t, i, x] \<down>= (if eval r_result [t, i, x] \<down>= 0 then 1 else 0)" for t
  proof -
    have "eval ?cond [t, i, x] = eval r_not [the (eval r_result [t, i, x])]"
      using r_result_total by simp
    moreover have "eval r_result [t, i, x] \<down>"
      by (simp add: r_result_total)
    ultimately show ?thesis by auto
  qed
  show ?thesis
  proof (cases "eval f ?xs \<up>")
    case True
    then show ?thesis
      unfolding r_univ_def using * r_result_diverg[OF assms] eval_Mn_diverg by simp
  next
    case False
    then obtain v where v: "eval f ?xs \<down>= v" by auto
    then obtain t where t:
      "\<forall>t'\<ge>t. eval r_result [t', i, x] \<down>= Suc v"
      "\<forall>t'<t. eval r_result [t', i, x] \<down>= 0"
      using r_result_converg[OF assms] by blast
    then have
      "\<forall>t'\<ge>t. eval ?cond [t', i, x] \<down>= 0"
      "\<forall>t'<t. eval ?cond [t', i, x] \<down>= 1"
      using * by simp_all
    then have "eval ?while [i, x] \<down>= t"
      using eval_Mn_convergI[of 2 ?cond "[i, x]" t] by simp
    then have "eval ?res [i, x] = eval r_result [t, i, x]"
      by simp
    then have "eval ?res [i, x] \<down>= Suc v"
      using t(1) by simp
    then show ?thesis
      unfolding r_univ_def using v by simp
  qed
qed

theorem r_univ':
  assumes "recfn (e_length x) f"
  shows "eval r_univ [encode f, x] = eval f (list_decode x)"
  using r_univ assms by simp

text \<open>Universal functions for every arity can be built from @{term "r_univ"}.\<close>

definition r_universal :: "nat \<Rightarrow> recf" where
  "r_universal n \<equiv> Cn (Suc n) r_univ [Id (Suc n) 0, r_shift (r_list_encode (n - 1))]"

lemma r_universal_recfn [simp]: "n > 0 \<Longrightarrow> recfn (Suc n) (r_universal n)"
  unfolding r_universal_def by simp

lemma r_universal:
  assumes "recfn n f" and "length xs = n"
  shows "eval (r_universal n) (encode f # xs) = eval f xs"
  unfolding r_universal_def using wellf_arity_nonzero assms r_list_encode r_univ'
  by fastforce

text \<open>We will mostly be concerned with computing unary functions. Hence
we introduce separate functions for this case.\<close>

definition "r_result1 \<equiv>
  Cn 3 r_result [Id 3 0, Id 3 1, Cn 3 r_singleton_encode [Id 3 2]]"

lemma r_result1_prim [simp]: "prim_recfn 3 r_result1"
  unfolding r_result1_def by simp

lemma r_result1_total: "total r_result1"
  using Mn_free_imp_total by simp

lemma r_result1 [simp]:
  "eval r_result1 [t, i, x] = eval r_result [t, i, singleton_encode x]"
  unfolding r_result1_def by simp

text \<open>The following function will be our standard Gödel numbering
of all unary partial recursive functions.\<close>

definition "r_phi \<equiv> r_universal 1"

lemma r_phi_recfn [simp]: "recfn 2 r_phi"
  unfolding r_phi_def by simp

theorem r_phi:
  assumes "i = encode f" and "recfn 1 f"
  shows "eval r_phi [i, x] = eval f [x]"
  unfolding r_phi_def using r_universal assms by force

corollary r_phi':
  assumes "recfn 1 f"
  shows "eval r_phi [encode f, x] = eval f [x]"
  using assms r_phi by simp

lemma r_phi'': "eval r_phi [i, x] = eval r_univ [i, singleton_encode x]"
  unfolding r_universal_def r_phi_def using r_list_encode by simp


section \<open>Applications of the universal function\<close>

text \<open>In this section we shall see some ways @{term r_univ} and @{term r_result} can
be used.\<close>

subsection \<open>Lazy conditional evaluation\<close>

text \<open>With the help of @{term r_univ} we can now define a
\hypertarget{p:r_lifz}{lazy variant} of @{term r_ifz}, in which only one
branch is evaluated.\<close>

definition r_lazyifzero :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> recf" where
  "r_lazyifzero n j\<^sub>1 j\<^sub>2 \<equiv>
     Cn (Suc (Suc n)) r_univ
      [Cn (Suc (Suc n)) r_ifz [Id (Suc (Suc n)) 0, r_constn (Suc n) j\<^sub>1, r_constn (Suc n) j\<^sub>2],
       r_shift (r_list_encode n)]"

lemma r_lazyifzero_recfn: "recfn (Suc (Suc n)) (r_lazyifzero n j\<^sub>1 j\<^sub>2)"
  using r_lazyifzero_def by simp

lemma r_lazyifzero:
  assumes "length xs = Suc n"
    and "j\<^sub>1 = encode f\<^sub>1"
    and "j\<^sub>2 = encode f\<^sub>2"
    and "recfn (Suc n) f\<^sub>1"
    and "recfn (Suc n) f\<^sub>2"
  shows "eval (r_lazyifzero n j\<^sub>1 j\<^sub>2) (c # xs) = (if c = 0 then eval f\<^sub>1 xs else eval f\<^sub>2 xs)"
proof -
  let ?a = "r_constn (Suc n) n"
  let ?b = "Cn (Suc (Suc n)) r_ifz
    [Id (Suc (Suc n)) 0, r_constn (Suc n) j\<^sub>1, r_constn (Suc n) j\<^sub>2]"
  let ?c = "r_shift (r_list_encode n)"
  have "eval ?a (c # xs) \<down>= n"
    using assms(1) by simp
  moreover have "eval ?b (c # xs) \<down>= (if c = 0 then j\<^sub>1 else j\<^sub>2)"
    using assms(1) by simp
  moreover have "eval ?c (c # xs) \<down>= list_encode xs"
    using assms(1) r_list_encode r_shift by simp
  ultimately have "eval (r_lazyifzero n j\<^sub>1 j\<^sub>2) (c # xs) =
      eval r_univ [if c = 0 then j\<^sub>1 else j\<^sub>2, list_encode xs]"
    unfolding r_lazyifzero_def using r_lazyifzero_recfn assms(1) by simp
  then show ?thesis using assms r_univ by simp
qed

definition r_lifz :: "recf \<Rightarrow> recf \<Rightarrow> recf" where
  "r_lifz f g \<equiv> r_lazyifzero (arity f - 1) (encode f) (encode g)"

lemma r_lifz_recfn [simp]:
  assumes "recfn n f" and "recfn n g"
  shows "recfn (Suc n) (r_lifz f g)"
  using assms r_lazyifzero_recfn r_lifz_def wellf_arity_nonzero by auto

lemma r_lifz [simp]:
  assumes "length xs = n" and "recfn n f" and "recfn n g"
  shows "eval (r_lifz f g) (c # xs) = (if c = 0 then eval f xs else eval g xs)"
  using assms r_lazyifzero r_lifz_def wellf_arity_nonzero
  by (metis One_nat_def Suc_pred)


subsection \<open>Enumerating the domains of partial recursive functions\<close>

text \<open>In this section we define a binary function $\mathit{enumdom}$
such that for all $i$, the domain of $\varphi_i$ equals
$\{\mathit{enumdom}(i, x) \mid \mathit{enumdom}(i, x)\!\downarrow\}$. In
other words, the image of $\mathit{enumdom}_i$ is the domain of $\varphi_i$.

First we need some more properties of @{term r_leap} and @{term r_result}.\<close>

lemma r_leap_Suc: "eval r_leap [Suc t, i, x] = eval r_step [the (eval r_leap [t, i, x])]"
proof -
  have "eval r_leap [Suc t, i, x] =
      eval (Cn 4 r_step [Id 4 1]) [t, the (eval r_leap [t, i, x]), i, x]"
    using r_leap_total eval_Pr_converg_Suc r_leap_def
    by (metis length_Cons list.size(3) numeral_2_eq_2 numeral_3_eq_3 r_leap_prim)
  then show ?thesis using r_step_prim by auto
qed

lemma r_leap_Suc_saturating:
  assumes "pdec1 (the (eval r_leap [t, i, x])) = 0"
  shows "eval r_leap [Suc t, i, x] = eval r_leap [t, i, x]"
proof -
  let ?e = "eval r_leap [t, i, x]"
  have "eval r_step [the ?e] \<down>= estep (the ?e)"
    using r_step by simp
  then have "eval r_step [the ?e] \<down>= prod_encode (0, e2rv (the ?e))"
    using estep_def assms by (simp add: e2stack_def)
  then have "eval r_step [the ?e] \<down>= prod_encode (pdec1 (the ?e), pdec2 (the ?e))"
    using assms by (simp add: e2rv_def)
  then have "eval r_step [the ?e] \<down>= the ?e" by simp
  then show ?thesis using r_leap_total r_leap_Suc by simp
qed

lemma r_result_Suc_saturating:
  assumes "eval r_result [t, i, x] \<down>= Suc v"
  shows "eval r_result [Suc t, i, x] \<down>= Suc v"
proof -
  let ?r = "\<lambda>t. eval r_ifz [pdec1 (the (eval r_leap [t, i, x])), pdec2 (the (eval r_leap [t, i, x])), 0]"
  have "?r t \<down>= Suc v"
    using assms unfolding r_result_def using r_leap_total r_leap_prim by simp
  then have "pdec1 (the (eval r_leap [t, i, x])) = 0"
    using option.sel by fastforce
  then have "eval r_leap [Suc t, i, x] = eval r_leap [t, i, x]"
    using r_leap_Suc_saturating by simp
  moreover have "eval r_result [t, i, x] = ?r t"
    unfolding r_result_def using r_leap_total r_leap_prim by simp
  moreover have "eval r_result [Suc t, i, x] = ?r (Suc t)"
    unfolding r_result_def using r_leap_total r_leap_prim by simp
  ultimately have "eval r_result [Suc t, i, x] = eval r_result [t, i, x]"
    by simp
  with assms show ?thesis by simp
qed

lemma r_result_saturating:
  assumes "eval r_result [t, i, x] \<down>= Suc v"
  shows "eval r_result [t + d, i, x] \<down>= Suc v"
  using r_result_Suc_saturating assms by (induction d) simp_all

lemma r_result_converg':
  assumes "eval r_univ [i, x] \<down>= v"
  shows "\<exists>t. (\<forall>t'\<ge>t. eval r_result [t', i, x] \<down>= Suc v) \<and> (\<forall>t'<t. eval r_result [t', i, x] \<down>= 0)"
proof -
  let ?f = "Cn 3 r_not [r_result]"
  let ?m = "Mn 2 ?f"
  have "recfn 2 ?m" by simp
  have eval_m: "eval ?m [i, x] \<down>"
  proof
    assume "eval ?m [i, x] \<up>"
    then have "eval r_univ [i, x] \<up>"
      unfolding r_univ_def by simp
    with assms show False by simp
  qed
  then obtain t where t: "eval ?m [i, x] \<down>= t"
    by auto
  then have f_t: "eval ?f [t, i, x] \<down>= 0" and f_less_t: "\<And>y. y < t \<Longrightarrow> eval ?f [y, i, x] \<down>\<noteq> 0"
    using eval_Mn_convergE[of 2 ?f "[i, x]" t] \<open>recfn 2 ?m\<close>
    by (metis (no_types, lifting) One_nat_def Suc_1 length_Cons list.size(3))+
  have eval_Cn2: "eval (Cn 2 r_result [?m, Id 2 0, Id 2 1]) [i, x] \<down>"
  proof
    assume "eval (Cn 2 r_result [?m, Id 2 0, Id 2 1]) [i, x] \<up>"
    then have "eval r_univ [i, x] \<up>"
      unfolding r_univ_def by simp
    with assms show False by simp
  qed
  have "eval r_result [t, i, x] \<down>= Suc v"
  proof (rule ccontr)
    assume neq_Suc: "\<not> eval r_result [t, i, x] \<down>= Suc v"
    show False
    proof (cases "eval r_result [t, i, x] = None")
      case True
      then show ?thesis using f_t by simp
    next
      case False
      then obtain w where w: "eval r_result [t, i, x] \<down>= w" "w \<noteq> Suc v"
        using neq_Suc by auto
      moreover have "eval r_result [t, i, x] \<down>\<noteq> 0"
        by (rule ccontr; use f_t in auto)
      ultimately have "w \<noteq> 0" by simp
      have "eval (Cn 2 r_result [?m, Id 2 0, Id 2 1]) [i, x] =
          eval r_result [the (eval ?m [i, x]), i, x]"
        using eval_m by simp
      with w t have "eval (Cn 2 r_result [?m, Id 2 0, Id 2 1]) [i, x] \<down>= w"
        by simp
      moreover have "eval r_univ [i, x] =
          eval r_dec [the (eval (Cn 2 r_result [?m, Id 2 0, Id 2 1]) [i, x])]"
        unfolding r_univ_def using eval_Cn2 by simp
      ultimately have "eval r_univ [i, x] = eval r_dec [w]" by simp
      then have "eval r_univ [i, x] \<down>= w - 1" by simp
      with assms \<open>w \<noteq> 0\<close> w show ?thesis by simp
    qed
  qed
  then have "\<forall>t'\<ge>t. eval r_result [t', i, x] \<down>= Suc v"
    using r_result_saturating le_Suc_ex by blast
  moreover have "eval r_result [y, i, x] \<down>= 0" if "y < t" for y
  proof (rule ccontr)
    assume neq0: "eval r_result [y, i, x] \<noteq> Some 0"
    then show False
    proof (cases "eval r_result [y, i, x] = None")
      case True
      then show ?thesis using f_less_t \<open>y < t\<close> by fastforce
    next
      case False
      then obtain v where "eval r_result [y, i, x] \<down>= v" "v \<noteq> 0"
        using neq0 by auto
      then have "eval ?f [y, i, x] \<down>= 0" by simp
      then show ?thesis using f_less_t \<open>y < t\<close> by simp
    qed
  qed
  ultimately show ?thesis by auto
qed

lemma r_result_diverg':
  assumes "eval r_univ [i, x] \<up>"
  shows "eval r_result [t, i, x] \<down>= 0"
proof (rule ccontr)
  let ?f = "Cn 3 r_not [r_result]"
  let ?m = "Mn 2 ?f"
  assume "eval r_result [t, i, x] \<noteq> Some 0"
  with r_result_total have "eval r_result [t, i, x] \<down>\<noteq> 0" by simp
  then have "eval ?f [t, i, x] \<down>= 0" by auto
  moreover have "eval ?f [y, i, x] \<down>" if "y < t" for y
    using  r_result_total by simp
  ultimately have "\<exists>z. eval ?f (z # [i, x]) \<down>= 0 \<and> (\<forall>y<z. eval ?f (y # [i, x]) \<down>)"
    by blast
  then have "eval ?m [i, x] \<down>" by simp
  then have "eval r_univ [i, x] \<down>"
    unfolding r_univ_def using r_result_total by simp
  with assms show False by simp
qed

lemma r_result_bivalent':
  assumes "eval r_univ [i, x] \<down>= v"
  shows "eval r_result [t, i, x] \<down>= Suc v \<or> eval r_result [t, i, x] \<down>= 0"
  using r_result_converg'[OF assms] not_less by blast

lemma r_result_Some':
  assumes "eval r_result [t, i, x] \<down>= Suc v"
  shows "eval r_univ [i, x] \<down>= v"
proof (rule ccontr)
  assume not_v: "\<not> eval r_univ [i, x] \<down>= v"
  show False
  proof (cases "eval r_univ [i, x] \<up>")
    case True
    then show ?thesis 
      using assms r_result_diverg' by simp
  next
    case False
    then obtain w where w: "eval r_univ [i, x] \<down>= w" "w \<noteq> v"
      using not_v by auto
    then have "eval r_result [t, i, x] \<down>= Suc w \<or> eval r_result [t, i, x] \<down>= 0"
      using r_result_bivalent' by simp
    then show ?thesis using assms not_v w by simp
  qed
qed

lemma r_result1_converg':
  assumes "eval r_phi [i, x] \<down>= v"
  shows "\<exists>t.
    (\<forall>t'\<ge>t. eval r_result1 [t', i, x] \<down>= Suc v) \<and>
    (\<forall>t'<t. eval r_result1 [t', i, x] \<down>= 0)"
  using assms r_result1 r_result_converg' r_phi'' by simp

lemma r_result1_diverg':
  assumes "eval r_phi [i, x] \<up>"
  shows "eval r_result1 [t, i, x] \<down>= 0"
  using assms r_result1 r_result_diverg' r_phi'' by simp

lemma r_result1_Some':
  assumes "eval r_result1 [t, i, x] \<down>= Suc v"
  shows "eval r_phi [i, x] \<down>= v"
  using assms r_result1 r_result_Some' r_phi'' by simp

text \<open>The next function performs dovetailing in order to evaluate
$\varphi_i$ for every argument for arbitrarily many steps. Given $i$ and $z$,
the function decodes $z$ into a pair $(x, t$) and outputs zero (meaning
``true'') iff.\ the computation of $\varphi_i$ on input $x$ halts after at most
$t$ steps. Fixing $i$ and varying $z$ will eventually compute $\varphi_i$
for every argument in the domain of $\varphi_i$ sufficiently long for it to
converge.\<close>

definition "r_dovetail \<equiv>
  Cn 2 r_not [Cn 2 r_result1 [Cn 2 r_pdec2 [Id 2 1], Id 2 0, Cn 2 r_pdec1 [Id 2 1]]]"

lemma r_dovetail_prim: "prim_recfn 2 r_dovetail"
  by (simp add: r_dovetail_def)

lemma r_dovetail:
  "eval r_dovetail [i, z] \<down>=
    (if the (eval r_result1 [pdec2 z, i, pdec1 z]) > 0 then 0 else 1)"
  unfolding r_dovetail_def using r_result_total by simp

text \<open>The function $\mathit{enumdom}$ works as follows in order to
enumerate exactly the domain of $\varphi_i$. Given $i$ and $y$ it searches
for the minimum $z \geq y$ for which the dovetail function returns true. This
$z$ is decoded into $(x, t)$ and the $x$ is output. In this way every value
output by $\mathit{enumdom}$ is in the domain of $\varphi_i$ by construction
of @{term r_dovetail}. Conversely an $x$ in the domain will be output for $y
= (x, t)$ where $t$ is such that $\varphi_i$ halts on $x$ within $t$
steps.\<close>

definition "r_dovedelay \<equiv>
  Cn 3 r_and
    [Cn 3 r_dovetail [Id 3 1, Id 3 0],
     Cn 3 r_ifle [Id 3 2, Id 3 0, r_constn 2 0, r_constn 2 1]]"

lemma r_dovedelay_prim: "prim_recfn 3 r_dovedelay"
  unfolding r_dovedelay_def using r_dovetail_prim by simp

lemma r_dovedelay:
  "eval r_dovedelay [z, i, y] \<down>=
    (if the (eval r_result1 [pdec2 z, i, pdec1 z]) > 0 \<and> y \<le> z then 0 else 1)"
  by (simp add: r_dovedelay_def r_dovetail r_dovetail_prim)

definition "r_enumdom \<equiv> Cn 2 r_pdec1 [Mn 2 r_dovedelay]"

lemma r_enumdom_recfn [simp]: "recfn 2 r_enumdom"
  by (simp add: r_enumdom_def r_dovedelay_prim)

lemma r_enumdom [simp]:
  "eval r_enumdom [i, y] =
    (if \<exists>z. eval r_dovedelay [z, i, y] \<down>= 0
     then Some (pdec1 (LEAST z. eval r_dovedelay [z, i, y] \<down>= 0))
     else None)"
proof -
  let ?h = "Mn 2 r_dovedelay"
  have "total r_dovedelay"
    using r_dovedelay_prim by blast
  then have "eval ?h [i, y] =
    (if (\<exists>z. eval r_dovedelay [z, i, y] \<down>= 0)
     then Some (LEAST z. eval r_dovedelay [z, i, y] \<down>= 0)
     else None)"
    using r_dovedelay_prim r_enumdom_recfn eval_Mn_convergI by simp
  then show ?thesis
    unfolding r_enumdom_def using r_dovedelay_prim by simp
qed

text \<open>If @{term i} is the code of the empty function, @{term r_enumdom}
has an empty domain, too.\<close>

lemma r_enumdom_empty_domain:
  assumes "\<And>x. eval r_phi [i, x] \<up>"
  shows "\<And>y. eval r_enumdom [i, y] \<up>"
  using assms r_result1_diverg' r_dovedelay by simp

text \<open>If @{term i} is the code of a function with non-empty domain,
@{term r_enumdom} enumerates its domain.\<close>

lemma r_enumdom_nonempty_domain:
  assumes "eval r_phi [i, x\<^sub>0] \<down>"
  shows "\<And>y. eval r_enumdom [i, y] \<down>"
    and "\<And>x. eval r_phi [i, x] \<down> \<longleftrightarrow> (\<exists>y. eval r_enumdom [i, y] \<down>= x)"
proof -
  show "eval r_enumdom [i, y] \<down>" for y
  proof -
    obtain t where t: "\<forall>t'\<ge>t. the (eval r_result1 [t', i, x\<^sub>0]) > 0"
      using assms r_result1_converg' by fastforce
    let ?z = "prod_encode (x\<^sub>0, max t y)"
    have "y \<le> ?z"
      using le_prod_encode_2 max.bounded_iff by blast
    moreover have "pdec2 ?z \<ge> t" by simp
    ultimately have "the (eval r_result1 [pdec2 ?z, i, pdec1 ?z]) > 0"
      using t by simp
    with \<open>y \<le> ?z\<close> r_dovedelay have "eval r_dovedelay [?z, i, y] \<down>= 0"
      by presburger
    then show "eval r_enumdom [i, y] \<down>"
      using r_enumdom by auto
  qed
  show "eval r_phi [i, x] \<down> = (\<exists>y. eval r_enumdom [i, y] \<down>= x)" for x
  proof
    show "\<exists>y. eval r_enumdom [i, y] \<down>= x" if "eval r_phi [i, x] \<down>" for x
    proof -
      from that obtain v where "eval r_phi [i, x] \<down>= v" by auto
      then obtain t where t: "the (eval r_result1 [t, i, x]) > 0"
        using r_result1_converg' assms
        by (metis Zero_not_Suc dual_order.refl option.sel zero_less_iff_neq_zero)
      let ?y = "prod_encode (x, t)"
      have "eval r_dovedelay [?y, i, ?y] \<down>= 0"
        using r_dovedelay t by simp
      moreover from this have "(LEAST z. eval r_dovedelay [z, i, ?y] \<down>= 0) = ?y"
        using gr_implies_not_zero r_dovedelay by (intro Least_equality; fastforce)
      ultimately have "eval r_enumdom [i, ?y] \<down>= x"
        using r_enumdom by auto
      then show ?thesis by blast
    qed
    show "eval r_phi [i, x] \<down>" if "\<exists>y. eval r_enumdom [i, y] \<down>= x" for x
    proof -
      from that obtain y where y: "eval r_enumdom [i, y] \<down>= x"
        by auto
      then have "eval r_enumdom [i, y] \<down>"
        by simp
      then have
        "\<exists>z. eval r_dovedelay [z, i, y] \<down>= 0" and
        *: "eval r_enumdom [i, y] \<down>= pdec1 (LEAST z. eval r_dovedelay [z, i, y] \<down>= 0)"
          (is "_ \<down>= pdec1 ?z")
        using r_enumdom by metis+
      then have z: "eval r_dovedelay [?z, i, y] \<down>= 0"
        by (meson wellorder_Least_lemma(1))
      have "the (eval r_result1 [pdec2 ?z, i, pdec1 ?z]) > 0"
      proof (rule ccontr)
        assume "\<not> (the (eval r_result1 [pdec2 ?z, i, pdec1 ?z]) > 0)"
        then show False
          using r_dovedelay z by simp
      qed
      then have "eval r_phi [i, pdec1 ?z] \<down>"
        using r_result1_diverg' assms by fastforce
      then show ?thesis using y * by auto
    qed
  qed
qed

text \<open>For every $\varphi_i$ with non-empty domain there is a total
recursive function that enumerates the domain of $\varphi_i$.\<close>

lemma nonempty_domain_enumerable:
  assumes "eval r_phi [i, x\<^sub>0] \<down>"
  shows "\<exists>g. recfn 1 g \<and> total g \<and> (\<forall>x. eval r_phi [i, x] \<down> \<longleftrightarrow> (\<exists>y. eval g [y] \<down>= x))"
proof -
  define g where "g \<equiv> Cn 1 r_enumdom [r_const i, Id 1 0]"
  then have "recfn 1 g" by simp
  moreover from this have "total g"
    using totalI1[of g] g_def assms r_enumdom_nonempty_domain(1) by simp
  moreover have "eval r_phi [i, x] \<down> \<longleftrightarrow> (\<exists>y. eval g [y] \<down>= x)" for x
    unfolding g_def using r_enumdom_nonempty_domain(2)[OF assms] by simp
  ultimately show ?thesis by auto
qed


subsection \<open>Concurrent evaluation of functions\<close>

text \<open>We define a function that simulates two @{typ recf}s
``concurrently'' for the same argument and returns the result of the one
converging first. If both diverge, so does the simulation function.\<close>

definition "r_both \<equiv>
  Cn 4 r_ifz
   [Cn 4 r_result1 [Id 4 0, Id 4 1, Id 4 3],
    Cn 4 r_ifz
     [Cn 4 r_result1 [Id 4 0, Id 4 2, Id 4 3],
      Cn 4 r_prod_encode [r_constn 3 2, r_constn 3 0],
      Cn 4 r_prod_encode
       [r_constn 3 1, Cn 4 r_dec [Cn 4 r_result1 [Id 4 0, Id 4 2, Id 4 3]]]],
    Cn 4 r_prod_encode
     [r_constn 3 0, Cn 4 r_dec [Cn 4 r_result1 [Id 4 0, Id 4 1, Id 4 3]]]]"

lemma r_both_prim [simp]: "prim_recfn 4 r_both"
  unfolding r_both_def by simp

lemma r_both:
  assumes "\<And>x. eval r_phi [i, x] = eval f [x]"
    and "\<And>x. eval r_phi [j, x] = eval g [x]"
  shows "eval f [x] \<up> \<and> eval g [x] \<up> \<Longrightarrow> eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)"
    and "\<lbrakk>eval r_result1 [t, i, x] \<down>= 0; eval r_result1 [t, j, x] \<down>= 0\<rbrakk> \<Longrightarrow>
      eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)"
    and "eval r_result1 [t, i, x] \<down>= Suc v \<Longrightarrow>
      eval r_both [t, i, j, x] \<down>= prod_encode (0, the (eval f [x]))"
    and "\<lbrakk>eval r_result1 [t, i, x] \<down>= 0; eval r_result1 [t, j, x] \<down>= Suc v\<rbrakk> \<Longrightarrow>
      eval r_both [t, i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
proof -
  have r_result_total [simp]: "eval r_result [t, k, x] \<down>" for t k x
    using r_result_total by simp
  {
    assume "eval f [x] \<up> \<and> eval g [x] \<up>"
    then have "eval r_result1 [t, i, x] \<down>= 0" and "eval r_result1 [t, j, x] \<down>= 0"
      using assms r_result1_diverg' by auto
    then show "eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)"
      unfolding r_both_def by simp
  next
    assume "eval r_result1 [t, i, x] \<down>= 0" and "eval r_result1 [t, j, x] \<down>= 0"
    then show "eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)"
      unfolding r_both_def by simp
  next
    assume "eval r_result1 [t, i, x] \<down>= Suc v"
    moreover from this have "eval r_result1 [t, i, x] \<down>= Suc (the (eval f [x]))"
      using assms r_result1_Some' by fastforce
    ultimately show "eval r_both [t, i, j, x] \<down>= prod_encode (0, the (eval f [x]))"
      unfolding r_both_def by auto
  next
    assume "eval r_result1 [t, i, x] \<down>= 0" and "eval r_result1 [t, j, x] \<down>= Suc v"
    moreover from this have "eval r_result1 [t, j, x] \<down>= Suc (the (eval g [x]))"
      using assms r_result1_Some' by fastforce
    ultimately show "eval r_both [t, i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
      unfolding r_both_def by auto
  }
qed

definition "r_parallel \<equiv>
  Cn 3 r_both [Mn 3 (Cn 4 r_le [Cn 4 r_pdec1 [r_both], r_constn 3 1]), Id 3 0, Id 3 1, Id 3 2]"

lemma r_parallel_recfn [simp]: "recfn 3 r_parallel"
  unfolding r_parallel_def by simp

lemma r_parallel:
  assumes "\<And>x. eval r_phi [i, x] = eval f [x]"
    and "\<And>x. eval r_phi [j, x] = eval g [x]"
  shows "eval f [x] \<up> \<and> eval g [x] \<up> \<Longrightarrow> eval r_parallel [i, j, x] \<up>"
    and "eval f [x] \<down> \<and> eval g [x] \<up> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval f [x]))"
    and "eval g [x] \<down> \<and> eval f [x] \<up> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
    and "eval f [x] \<down> \<and> eval g [x] \<down> \<Longrightarrow>
      eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval f [x])) \<or>
      eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
proof -
  let ?cond = "Cn 4 r_le [Cn 4 r_pdec1 [r_both], r_constn 3 1]"
  define m where "m = Mn 3 ?cond"
  then have m: "r_parallel = Cn 3 r_both [m, Id 3 0, Id 3 1, Id 3 2]"
    unfolding r_parallel_def by simp
  from m_def have "recfn 3 m" by simp
  {
    assume "eval f [x] \<up> \<and> eval g [x] \<up>"
    then have "\<forall>t. eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)"
      using assms r_both by simp
    then have "eval ?cond [t, i, j, x] \<down>= 1" for t
      by simp
    then have "eval m [i, j, x] \<up>"
      unfolding m_def using eval_Mn_diverg by simp
    then have "eval (Cn 3 r_both [m, Id 3 0, Id 3 1, Id 3 2]) [i, j, x] \<up>"
      using \<open>recfn 3 m\<close> by simp
    then show "eval r_parallel [i, j, x] \<up>"
      using m by simp
  next
    assume "eval f [x] \<down> \<and> eval g [x] \<down>"
    then obtain vf vg where v: "eval f [x] \<down>= vf" "eval g [x] \<down>= vg"
      by auto
    then obtain tf where tf:
      "\<forall>t\<ge>tf. eval r_result1 [t, i, x] \<down>= Suc vf"
      "\<forall>t<tf. eval r_result1 [t, i, x] \<down>= 0"
      using r_result1_converg' assms by metis
    from v obtain tg where tg:
      "\<forall>t\<ge>tg. eval r_result1 [t, j, x] \<down>= Suc vg"
      "\<forall>t<tg. eval r_result1 [t, j, x] \<down>= 0"
      using r_result1_converg' assms by metis
    show "eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval f [x])) \<or>
      eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
    proof (cases "tf \<le> tg")
      case True
      with tg(2) have j0: "\<forall>t<tf. eval r_result1 [t, j, x] \<down>= 0"
        by simp
      have *: "eval r_both [tf, i, j, x] \<down>= prod_encode (0, the (eval f [x]))"
        using r_both(3) assms tf(1) by simp
      have "eval m [i, j, x] \<down>= tf"
        unfolding m_def
      proof (rule eval_Mn_convergI)
        show "recfn (length [i, j, x]) (Mn 3 ?cond)" by simp
        have "eval (Cn 4 r_pdec1 [r_both]) [tf, i, j, x] \<down>= 0"
          using * by simp
        then show "eval ?cond [tf, i, j, x] \<down>= 0" by simp
        have "eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)" if "t < tf" for t
          using tf(2) r_both(2) assms that j0 by simp
        then have "eval ?cond [t, i, j, x] \<down>= 1" if "t < tf" for t
          using that by simp
        then show "\<And>y. y < tf \<Longrightarrow> eval ?cond [y, i, j, x] \<down>\<noteq> 0" by simp
      qed
      moreover have "eval r_parallel [i, j, x] =
          eval (Cn 3 r_both [m, Id 3 0, Id 3 1, Id 3 2]) [i, j, x]"
        using m by simp
      ultimately have "eval r_parallel [i, j, x] = eval r_both [tf, i, j, x]"
        using \<open>recfn 3 m\<close> by simp
      with * have "eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval f [x]))"
        by simp
      then show ?thesis by simp
    next
      case False
      with tf(2) have i0: "\<forall>t\<le>tg. eval r_result1 [t, i, x] \<down>= 0"
        by simp
      then have *: "eval r_both [tg, i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
        using assms r_both(4) tg(1) by auto
      have "eval m [i, j, x] \<down>= tg"
        unfolding m_def
      proof (rule eval_Mn_convergI)
        show "recfn (length [i, j, x]) (Mn 3 ?cond)" by simp
        have "eval (Cn 4 r_pdec1 [r_both]) [tg, i, j, x] \<down>= 1"
          using * by simp
        then show "eval ?cond [tg, i, j, x] \<down>= 0" by simp
        have "eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)" if "t < tg" for t
          using tg(2) r_both(2) assms that i0 by simp
        then have "eval ?cond [t, i, j, x] \<down>= 1" if "t < tg" for t
          using that by simp
        then show "\<And>y. y < tg \<Longrightarrow> eval ?cond [y, i, j, x] \<down>\<noteq> 0" by simp
      qed
      moreover have "eval r_parallel [i, j, x] =
          eval (Cn 3 r_both [m, Id 3 0, Id 3 1, Id 3 2]) [i, j, x]"
        using m by simp
      ultimately have "eval r_parallel [i, j, x] = eval r_both [tg, i, j, x]"
        using \<open>recfn 3 m\<close> by simp
      with * have "eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
        by simp
      then show ?thesis by simp
    qed
  next
    assume eval_fg: "eval g [x] \<down> \<and> eval f [x] \<up>"
    then have i0: "\<forall>t. eval r_result1 [t, i, x] \<down>= 0"
      using r_result1_diverg' assms by auto
    from eval_fg obtain v where "eval g [x] \<down>= v"
      by auto
    then obtain t\<^sub>0 where t0:
      "\<forall>t\<ge>t\<^sub>0. eval r_result1 [t, j, x] \<down>= Suc v"
      "\<forall>t<t\<^sub>0. eval r_result1 [t, j, x] \<down>= 0"
      using r_result1_converg' assms by metis
    then have *: "eval r_both [t\<^sub>0, i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
      using r_both(4) assms i0 by simp
    have "eval m [i, j, x] \<down>= t\<^sub>0"
      unfolding m_def
    proof (rule eval_Mn_convergI)
      show "recfn (length [i, j, x]) (Mn 3 ?cond)" by simp
      have "eval (Cn 4 r_pdec1 [r_both]) [t\<^sub>0, i, j, x] \<down>= 1"
        using * by simp
      then show "eval ?cond [t\<^sub>0, i, j, x] \<down>= 0" by simp
      have "eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)" if "t < t\<^sub>0" for t
        using t0(2) r_both(2) assms that i0 by simp
      then have "eval ?cond [t, i, j, x] \<down>= 1" if "t < t\<^sub>0" for t
        using that by simp
      then show "\<And>y. y < t\<^sub>0 \<Longrightarrow> eval ?cond [y, i, j, x] \<down>\<noteq> 0" by simp
    qed
    moreover have "eval r_parallel [i, j, x] =
        eval (Cn 3 r_both [m, Id 3 0, Id 3 1, Id 3 2]) [i, j, x]"
      using m by simp
    ultimately have "eval r_parallel [i, j, x] = eval r_both [t\<^sub>0, i, j, x]"
      using \<open>recfn 3 m\<close> by simp
    with * show "eval r_parallel [i, j, x] \<down>= prod_encode (1, the (eval g [x]))"
      by simp
  next
    assume eval_fg: "eval f [x] \<down> \<and> eval g [x] \<up>"
    then have j0: "\<forall>t. eval r_result1 [t, j, x] \<down>= 0"
      using r_result1_diverg' assms by auto
    from eval_fg obtain v where "eval f [x] \<down>= v"
      by auto
    then obtain t\<^sub>0 where t0:
      "\<forall>t\<ge>t\<^sub>0. eval r_result1 [t, i, x] \<down>= Suc v"
      "\<forall>t<t\<^sub>0. eval r_result1 [t, i, x] \<down>= 0"
      using r_result1_converg' assms by metis
    then have *: "eval r_both [t\<^sub>0, i, j, x] \<down>= prod_encode (0, the (eval f [x]))"
      using r_both(3) assms by blast
    have "eval m [i, j, x] \<down>= t\<^sub>0"
      unfolding m_def
    proof (rule eval_Mn_convergI)
      show "recfn (length [i, j, x]) (Mn 3 ?cond)" by simp
      have "eval (Cn 4 r_pdec1 [r_both]) [t\<^sub>0, i, j, x] \<down>= 0"
        using * by simp
      then show "eval ?cond [t\<^sub>0, i, j, x] \<down>= 0"
        by simp
      have "eval r_both [t, i, j, x] \<down>= prod_encode (2, 0)" if "t < t\<^sub>0" for t
        using t0(2) r_both(2) assms that j0 by simp
      then have "eval ?cond [t, i, j, x] \<down>= 1" if "t < t\<^sub>0" for t
        using that by simp
      then show "\<And>y. y < t\<^sub>0 \<Longrightarrow> eval ?cond [y, i, j, x] \<down>\<noteq> 0" by simp
    qed
    moreover have "eval r_parallel [i, j, x] =
        eval (Cn 3 r_both [m, Id 3 0, Id 3 1, Id 3 2]) [i, j, x]"
      using m by simp
    ultimately have "eval r_parallel [i, j, x] = eval r_both [t\<^sub>0, i, j, x]"
      using \<open>recfn 3 m\<close> by simp
    with * show "eval r_parallel [i, j, x] \<down>= prod_encode (0, the (eval f [x]))"
      by simp
  }
qed

end