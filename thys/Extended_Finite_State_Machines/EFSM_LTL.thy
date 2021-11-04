section\<open>LTL for EFSMs\<close>
text\<open>This theory builds off the \texttt{Linear\_Temporal\_Logic\_on\_Streams} theory from the HOL
library and defines functions to ease the expression of LTL properties over EFSMs. Since the LTL
operators effectively act over traces of models we must find a way to express models as streams.\<close>

theory EFSM_LTL
imports "Extended_Finite_State_Machines.EFSM" "HOL-Library.Linear_Temporal_Logic_on_Streams"
begin

text_raw\<open>\snip{statedef}{1}{2}{%\<close>
record state =
  statename :: "nat option"
  datastate :: registers
  action :: action
  "output" :: outputs
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{whitebox}{1}{2}{%\<close>
type_synonym whitebox_trace = "state stream"
text_raw\<open>}%endsnip\<close>

type_synonym property = "whitebox_trace \<Rightarrow> bool"

abbreviation label :: "state \<Rightarrow> String.literal" where
  "label s \<equiv> fst (action s)"

abbreviation inputs :: "state \<Rightarrow> value list" where
  "inputs s \<equiv> snd (action s)"

text_raw\<open>\snip{ltlStep}{1}{2}{%\<close>
fun ltl_step :: "transition_matrix \<Rightarrow> cfstate option \<Rightarrow> registers \<Rightarrow> action \<Rightarrow> (nat option \<times> outputs \<times> registers)" where
  "ltl_step _ None r _ = (None, [], r)" |
  "ltl_step e (Some s) r (l, i) = (let possibilities = possible_steps e s r l i in
                   if possibilities = {||} then (None, [], r)
                   else
                     let (s', t) = Eps (\<lambda>x. x |\<in>| possibilities) in
                     (Some s', (evaluate_outputs t i r), (evaluate_updates t i r))
                  )"
text_raw\<open>}%endsnip\<close>

lemma ltl_step_singleton:
"\<exists>t. possible_steps e n r (fst v) (snd v) = {|(aa, t)|} \<and> evaluate_outputs t (snd v) r  = b \<and> evaluate_updates t (snd v) r = c\<Longrightarrow>
ltl_step e (Some n) r v = (Some aa, b, c)"
  apply (cases v)
  by auto

lemma ltl_step_none: "possible_steps e s r a b = {||} \<Longrightarrow> ltl_step e (Some s) r (a, b) = (None, [], r)"
  by simp

lemma ltl_step_none_2: "possible_steps e s r (fst ie) (snd ie) = {||} \<Longrightarrow> ltl_step e (Some s) r ie = (None, [], r)"
  by (metis ltl_step_none prod.exhaust_sel)

lemma ltl_step_alt: "ltl_step e (Some s) r t = (
  let possibilities = possible_steps e s r (fst t) (snd t) in
  if possibilities = {||} then
    (None, [], r)
  else
  let (s', t') = Eps (\<lambda>x. x |\<in>| possibilities) in
  (Some s', (apply_outputs (Outputs t') (join_ir (snd t) r)), (apply_updates (Updates t') (join_ir (snd t) r) r))
)"
  by (case_tac t, simp add: Let_def)

lemma ltl_step_some:
  assumes "possible_steps e s r l i = {|(s', t)|}"
      and "evaluate_outputs t i r = p"
      and "evaluate_updates t i r = r'"
    shows "ltl_step e (Some s) r (l, i) = (Some s', p, r')"
  by (simp add: assms)

lemma ltl_step_cases:
  assumes invalid: "P (None, [], r)"
      and valid: "\<forall>(s', t) |\<in>| (possible_steps e s r l i). P (Some s', (evaluate_outputs t i r), (evaluate_updates t i r))"
    shows "P (ltl_step e (Some s) r (l, i))"
  apply simp
  apply (case_tac "possible_steps e s r l i")
   apply (simp add: invalid)
  apply simp
  subgoal for x S'
    apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
    apply simp
    apply (insert assms(2))
    apply (simp add: fBall_def Ball_def fmember_def)
    by (metis (mono_tags, lifting) fst_conv prod.case_eq_if snd_conv someI_ex)
  done

text\<open>The \texttt{make\_full\_observation} function behaves similarly to \texttt{observe\_execution}
from the \texttt{EFSM} theory. The main difference in behaviour is what is recorded. While the
observe execution function simply observes an execution of the EFSM to produce the corresponding
output for each action, the intention here is to record every detail of execution, including the
values of internal variables.

Thinking of each action as a step forward in time, there are five components which characterise
a given point in the execution of an EFSM. At each point, the model has a current control state and
data state. Each action has a label and some input parameters, and its execution may produce
some observableoutput. It is therefore sufficient to provide a stream of 5-tuples containing the
current control state, data state, the label and inputs of the action, and computed output. The
make full observation function can then be defined as in Figure 9.1, with an additional
function watch defined on top of this which starts the make full observation off in the
initial control state with the empty data state.

Careful inspection of the definition reveals another way that \texttt{make\_full\_observation}
differs from \texttt{observe\_execution}. Rather than taking a cfstate, it takes a cfstate option.
The reason for this is that we need to make our EFSM models complete. That is, we need them to be
able to respond to every action from every state like a DFA. If a model does not recognise a given
action in a given state, we cannot simply stop processing because we are working with necessarily
infinite traces. Since these traces are generated by observing action sequences, the make full
observation function must keep processing whether there is a viable transition or not.

To support this, the make full observation adds an implicit ``sink state'' to every EFSM it
processes by lifting control flow state indices from \texttt{nat} to \texttt{nat option} such that
state $n$ is seen as state \texttt{Some} $n$. The control flow state \texttt{None} represents a sink
state. If a model is unable to recognise a particular action from its current state, it moves into
the \texttt{None} state. From here, the behaviour is constant for the rest of the time --- the
control flow state remains None; the data state does not change, and no output is produced.\<close>

text_raw\<open>\snip{makeFullObservation}{1}{2}{%\<close>
primcorec make_full_observation :: "transition_matrix \<Rightarrow> cfstate option \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> action stream \<Rightarrow> whitebox_trace" where
  "make_full_observation e s d p i = (
    let (s', o', d') = ltl_step e s d (shd i) in
    \<lparr>statename = s, datastate = d, action=(shd i), output = p\<rparr>##(make_full_observation e s' d' o' (stl i))
  )"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{watch}{1}{2}{%\<close>
abbreviation watch :: "transition_matrix \<Rightarrow> action stream \<Rightarrow> whitebox_trace" where
  "watch e i \<equiv> (make_full_observation e (Some 0) <> [] i)"
text_raw\<open>}%endsnip\<close>

subsection\<open>Expressing Properties\<close>
text\<open>In order to simplify the expression and understanding of properties, this theory defines a
number of named functions which can be used to express certain properties of EFSMs.\<close>

subsubsection\<open>State Equality\<close>
text\<open>The \textsc{state\_eq} takes a cfstate option representing a control flow state index and
returns true if this is the control flow state at the head of the full observation.\<close>

abbreviation state_eq :: "cfstate option \<Rightarrow> whitebox_trace \<Rightarrow> bool" where
  "state_eq v s \<equiv> statename (shd s) = v"

lemma state_eq_holds: "state_eq s = holds (\<lambda>x. statename x = s)"
  apply (rule ext)
  by (simp add: holds_def)

lemma state_eq_None_not_Some: "state_eq None s \<Longrightarrow> \<not> state_eq (Some n) s"
  by simp

subsubsection\<open>Label Equality\<close>
text\<open>The \textsc{label\_eq} function takes a string and returns true if this is equal to the label
at the head of the full observation.\<close>

abbreviation "label_eq v s \<equiv> fst (action (shd s)) = (String.implode v)"

lemma watch_label: "label_eq l (watch e t) = (fst (shd t) = String.implode l)"
  by (simp add: )

subsubsection\<open>Input Equality\<close>
text\<open>The \textsc{input\_eq} function takes a value list and returns true if this is equal to the
input at the head of the full observation.\<close>

abbreviation "input_eq v s \<equiv> inputs (shd s) = v"

subsubsection\<open>Action Equality\<close>
text\<open>The \textsc{action\_eq} function takes a (label, value list) pair and returns true if this is
equal to the action at the head of the full observation. This effectively combines
\texttt{label\_eq} and \texttt{input\_eq} into one function.\<close>

abbreviation "action_eq e \<equiv> label_eq (fst e) aand input_eq (snd e)"

subsubsection\<open>Output Equality\<close>
text\<open>The \textsc{output\_eq} function takes a takes a value option list and returns true if this is
equal to the output at the head of the full observation.\<close>

abbreviation "output_eq v s \<equiv> output (shd s) = v"

text_raw\<open>\snip{ltlVName}{1}{2}{%\<close>
datatype ltl_vname = Ip nat | Op nat | Rg nat
text_raw\<open>}%endsnip\<close>

subsubsection\<open>Checking Arbitrary Expressions\<close>
text\<open>The \textsc{check\_exp} function takes a guard expression and returns true if the guard
expression evaluates to true in the given state.\<close>

type_synonym ltl_gexp = "ltl_vname gexp"

definition join_iro :: "value list \<Rightarrow> registers \<Rightarrow> outputs \<Rightarrow> ltl_vname datastate" where
  "join_iro i r p = (\<lambda>x. case x of
    Rg n \<Rightarrow> r $ n |
    Ip n \<Rightarrow> Some (i ! n) |
    Op n \<Rightarrow> p ! n
  )"

lemma join_iro_R [simp]: "join_iro i r p (Rg n) = r $ n"
  by (simp add: join_iro_def)

abbreviation "check_exp g s \<equiv> (gval g (join_iro (snd (action (shd s))) (datastate (shd s)) (output (shd s))) = trilean.true)"

lemma alw_ev: "alw f = not (ev (\<lambda>s. \<not>f s))"
  by simp

lemma alw_state_eq_smap:
  "alw (state_eq s) ss = alw (\<lambda>ss. shd ss = s) (smap statename ss)"
  apply standard
   apply (simp add: alw_iff_sdrop )
  by (simp add: alw_mono alw_smap )

subsection\<open>Sink State\<close>
text\<open>Once the sink state is entered, it cannot be left and there are no outputs or updates
henceforth.\<close>

lemma shd_state_is_none: "(state_eq None) (make_full_observation e None r p t)"
  by (simp add: )

lemma unfold_observe_none: "make_full_observation e None d p t = (\<lparr>statename = None, datastate = d, action=(shd t), output = p\<rparr>##(make_full_observation e None d [] (stl t)))"
  by (simp add: stream.expand)

lemma once_none_always_none_aux:
  assumes "\<exists> p r i. j = (make_full_observation e None r p) i"
  shows "alw (state_eq None) j"
  using assms apply coinduct
  apply simp
  by fastforce

lemma once_none_always_none: "alw (state_eq None) (make_full_observation e None r p t)"
  using once_none_always_none_aux by blast

lemma once_none_nxt_always_none: "alw (nxt (state_eq None)) (make_full_observation e None r p t)"
  using once_none_always_none
  by (simp add: alw_iff_sdrop del: sdrop.simps)

lemma snth_sconst: "(\<forall>i. s !! i = h) = (s = sconst h)"
  by (metis funpow_code_def id_funpow sdrop_simps(1) sdrop_siterate siterate.simps(1) smap_alt smap_sconst snth.simps(1) stream.map_id)

lemma alw_sconst: "(alw (\<lambda>xs. shd xs = h) t) = (t = sconst h)"
  by (simp add: snth_sconst[symmetric] alw_iff_sdrop)

lemma smap_statename_None: "smap statename (make_full_observation e None r p i) = sconst None"
  by (meson EFSM_LTL.alw_sconst alw_state_eq_smap once_none_always_none)

lemma alw_not_some: "alw (\<lambda>xs. statename (shd xs) \<noteq> Some s) (make_full_observation e None r p t)"
  by (metis (mono_tags, lifting) alw_mono once_none_always_none option.distinct(1) )

lemma state_none: "((state_eq None) impl nxt (state_eq None)) (make_full_observation e s r p t)"
  by (simp add: )

lemma state_none_2:
  "(state_eq None) (make_full_observation e s r p t) \<Longrightarrow>
   (state_eq None) (make_full_observation e s r p (stl t))"
  by (simp add: )

lemma no_output_none_aux:
  assumes "\<exists> p r i. j = (make_full_observation e None r []) i"
  shows "alw (output_eq []) j"
  using assms apply coinduct
  apply simp
  by fastforce

lemma no_output_none: "nxt (alw (output_eq [])) (make_full_observation e None r p t)"
  using no_output_none_aux by auto

lemma nxt_alw: "nxt (alw P) s \<Longrightarrow> alw (nxt P) s"
  by (simp add: alw_iff_sdrop)

lemma no_output_none_nxt: "alw (nxt (output_eq [])) (make_full_observation e None r p t)"
  using nxt_alw no_output_none by blast

lemma no_output_none_if_empty: "alw (output_eq []) (make_full_observation e None r [] t)"
  by (metis (mono_tags, lifting) alw_nxt make_full_observation.simps(1) no_output_none state.select_convs(4))

lemma no_updates_none_aux:
  assumes "\<exists> p i. j = (make_full_observation e None r p) i"
  shows "alw (\<lambda>x. datastate (shd x) = r) j"
  using assms apply coinduct
  by fastforce

lemma no_updates_none: "alw (\<lambda>x. datastate (shd x) = r) (make_full_observation e None r p t)"
  using no_updates_none_aux by blast

lemma action_components: "(label_eq l aand input_eq i) s = (action (shd s) = (String.implode l, i))"
  by (metis fst_conv prod.collapse snd_conv)

end
