(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CIMP_vcg
imports
  CIMP_lang
begin

(*>*)
section\<open> State-based invariants \label{sec:cimp-invariants} \<close>

text\<open>

We provide a simple-minded verification condition generator (VCG) for this language, providing
support for establishing state-based invariants. It is just one way of reasoning about CIMP programs
and is proven sound wrt to the CIMP semantics.

Our approach follows @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80" and "DBLP:journals/toplas/LamportS84"}
(and the later @{cite [cite_macro=citet] "Lamport:2002"}) and closely
related work by @{cite [cite_macro=citet] "AptFrancezDeRoever:1980"},
@{cite [cite_macro=citet] "CousotCousot:1980"} and @{cite
[cite_macro=citet] "DBLP:journals/acta/LevinG81"}, who suggest the
incorporation of a history variable. @{cite [cite_macro=citet]
"CousotCousot:1980"} apparently contains a completeness proof.
Lamport mentions that this technique was well-known in the mid-80s
when he proposed the use of prophecy variables\footnote{@{url
"https://lamport.azurewebsites.net/pubs/pubs.html"}}. See also @{cite
[cite_macro=citet] "deRoeverEtAl:2001"} for an extended discussion of
some of this.

\<close>

declare small_step.intros[intro]

inductive_cases small_step_inv:
  "(\<lbrace>l\<rbrace> Request action val # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> Response action # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> LocalOp R # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> IF b THEN c FI # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(\<lbrace>l\<rbrace> WHILE b DO c OD # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"
  "(LOOP DO c OD # cs, ls) \<rightarrow>\<^bsub>a\<^esub> s'"

lemma small_step_stuck:
  "\<not> ([], s) \<rightarrow>\<^bsub>\<alpha>\<^esub> c'"
by (auto elim: small_step.cases)

declare system_step.intros[intro]

text\<open>

By default we ask the simplifier to rewrite @{const "atS"} using
ambient @{const "AT"} information.

\<close>

lemma atS_state_weak_cong[cong]:
  "AT s p = AT s' p \<Longrightarrow> atS p ls s \<longleftrightarrow> atS p ls s'"
by (auto simp: atS_def)

text\<open>

We provide an incomplete set of basic rules for label sets.

\<close>

lemma atS_simps:
  "\<not>atS p {} s"
  "atS p {l} s \<longleftrightarrow> at p l s"
  "\<lbrakk>at p l s; l \<in> ls\<rbrakk> \<Longrightarrow> atS p ls s"
  "(\<forall>l. at p l s \<longrightarrow> l \<notin> ls) \<Longrightarrow> \<not>atS p ls s"
by (auto simp: atS_def)

lemma atS_mono:
  "\<lbrakk>atS p ls s; ls \<subseteq> ls'\<rbrakk> \<Longrightarrow> atS p ls' s"
by (auto simp: atS_def)

lemma atS_un:
  "atS p (l \<union> l') s \<longleftrightarrow> atS p l s \<or> atS p l' s"
by (auto simp: atS_def)

lemma atLs_disj_union[simp]:
  "(atLs p label0 \<^bold>\<or> atLs p label1) = atLs p (label0 \<union> label1)"
unfolding atLs_def by simp

lemma atLs_insert_disj:
  "atLs p (insert l label0) = (atL p l \<^bold>\<or> atLs p label0)"
by simp

lemma small_step_terminated:
  "s \<rightarrow>\<^bsub>x\<^esub> s' \<Longrightarrow> atCs (fst s) = {} \<Longrightarrow> atCs (fst s') = {}"
by (induct pred: small_step) auto

lemma atC_not_empty:
  "atC c \<noteq> {}"
by (induct c) auto

lemma atCs_empty:
  "atCs cs = {} \<longleftrightarrow> cs = []"
by (induct cs) (auto simp: atC_not_empty)

lemma terminated_no_commands:
  assumes "terminated p sh"
  shows "\<exists>s. GST sh p = ([], s)"
using assms unfolding atLs_def AT_def by (metis atCs_empty prod.collapse singletonD)

lemma terminated_GST_stable:
  assumes "system_step q sh' sh"
  assumes "terminated p sh"
  shows "GST sh p = GST sh' p"
using assms by (auto dest!: terminated_no_commands simp: small_step_stuck elim!: system_step.cases)

lemma terminated_stable:
  assumes "system_step q sh' sh"
  assumes "terminated p sh"
  shows "terminated p sh'"
using assms unfolding atLs_def AT_def
by (fastforce split: if_splits prod.splits
               dest: small_step_terminated
              elim!: system_step.cases)

lemma system_step_pls_nonempty:
  assumes "system_step pls sh' sh"
  shows "pls \<noteq> {}"
using assms by cases simp_all

lemma system_step_no_change:
  assumes "system_step ps sh' sh"
  assumes "p \<notin> ps"
  shows "GST sh' p = GST sh p"
using assms by cases simp_all

lemma initial_stateD:
  assumes "initial_state sys s"
  shows "AT (\<lparr>GST = s, HST = []\<rparr>) = atC \<circ> PGMs sys \<and> INIT sys (\<lparr>GST = s, HST = []\<rparr>)\<down> \<and> (\<forall>p l. \<not>taken p l \<lparr>GST = s, HST = []\<rparr>)"
using assms unfolding initial_state_def split_def o_def LST_def AT_def taken_def by simp

lemma initial_states_initial[iff]:
  assumes "initial_state sys s"
  shows "at p l (\<lparr>GST = s, HST = []\<rparr>) \<longleftrightarrow> l \<in> atC (PGMs sys p)"
using assms unfolding initial_state_def split_def AT_def by simp

definition
  reachable_state :: "('answer, 'location, 'proc, 'question, 'state, 'ext) pre_system_ext
                    \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred"
where
  "reachable_state sys s \<longleftrightarrow> (\<exists>\<sigma> i. prerun sys \<sigma> \<and> \<sigma> i = s)"

lemma reachable_stateE:
  assumes "reachable_state sys sh"
  assumes "\<And>\<sigma> i. prerun sys \<sigma> \<Longrightarrow> P (\<sigma> i)"
  shows "P sh"
using assms unfolding reachable_state_def by blast

lemma prerun_reachable_state:
  assumes "prerun sys \<sigma>"
  shows "reachable_state sys (\<sigma> i)"
using assms unfolding prerun_def LTL.defs system_step_reflclp_def reachable_state_def by auto

lemma reachable_state_induct[consumes 1, case_names init LocalStep CommunicationStep, induct set: reachable_state]:
  assumes r: "reachable_state sys sh"
  assumes i: "\<And>s. initial_state sys s \<Longrightarrow> P \<lparr>GST = s, HST = []\<rparr>"
  assumes l: "\<And>sh ls' p. \<lbrakk>reachable_state sys sh; P sh; GST sh p \<rightarrow>\<^bsub>\<tau>\<^esub> ls'\<rbrakk> \<Longrightarrow> P \<lparr>GST = (GST sh)(p := ls'), HST = HST sh\<rparr>"
  assumes c: "\<And>sh ls1' ls2' p1 p2 \<alpha> \<beta>.
                 \<lbrakk>reachable_state sys sh; P sh;
                 GST sh p1 \<rightarrow>\<^bsub>\<guillemotleft>\<alpha>, \<beta>\<guillemotright>\<^esub> ls1'; GST sh p2 \<rightarrow>\<^bsub>\<guillemotright>\<alpha>, \<beta>\<guillemotleft>\<^esub> ls2'; p1 \<noteq> p2 \<rbrakk>
                    \<Longrightarrow> P \<lparr>GST = (GST sh)(p1 := ls1', p2 := ls2'), HST = HST sh @ [(\<alpha>, \<beta>)]\<rparr>"
  shows "P sh"
using r
proof(rule reachable_stateE)
  fix \<sigma> i assume "prerun sys \<sigma>" show "P (\<sigma> i)"
  proof(induct i)
    case 0 from \<open>prerun sys \<sigma>\<close> show ?case
      unfolding prerun_def by (metis (full_types) i old.unit.exhaust system_state.surjective)
  next
    case (Suc i) with \<open>prerun sys \<sigma>\<close> show ?case
unfolding prerun_def LTL.defs system_step_reflclp_def reachable_state_def
apply clarsimp
apply (drule_tac x=i in spec)
apply (erule disjE; clarsimp)
apply (erule system_step.cases; clarsimp)
 apply (metis (full_types) \<open>prerun sys \<sigma>\<close> l old.unit.exhaust prerun_reachable_state system_state.surjective)
apply (metis (full_types) \<open>prerun sys \<sigma>\<close> c old.unit.exhaust prerun_reachable_state system_state.surjective)
done
  qed
qed

lemma prerun_valid_TrueI:
  shows "sys \<Turnstile>\<^bsub>pre\<^esub> \<langle>True\<rangle>"
unfolding prerun_valid_def by simp

lemma prerun_valid_conjI:
  assumes "sys \<Turnstile>\<^bsub>pre\<^esub> P"
  assumes "sys \<Turnstile>\<^bsub>pre\<^esub> Q"
  shows "sys \<Turnstile>\<^bsub>pre\<^esub> P \<^bold>\<and> Q"
using assms unfolding prerun_valid_def always_def by simp

lemma valid_prerun_lift:
  assumes "sys \<Turnstile>\<^bsub>pre\<^esub> I"
  shows "sys \<Turnstile> \<box>\<lceil>I\<rceil>"
using assms unfolding prerun_valid_def valid_def run_def by blast

lemma prerun_valid_induct:
  assumes "\<And>\<sigma>. prerun sys \<sigma> \<Longrightarrow> \<lceil>I\<rceil> \<sigma>"
  assumes "\<And>\<sigma>. prerun sys \<sigma> \<Longrightarrow> (\<lceil>I\<rceil> \<^bold>\<hookrightarrow> (\<circle>\<lceil>I\<rceil>)) \<sigma>"
  shows "sys \<Turnstile>\<^bsub>pre\<^esub> I"
unfolding prerun_valid_def using assms by (simp add: always_induct)

lemma prerun_validI:
  assumes "\<And>s. reachable_state sys s \<Longrightarrow> I s"
  shows "sys \<Turnstile>\<^bsub>pre\<^esub> I"
unfolding prerun_valid_def using assms by (simp add: alwaysI prerun_reachable_state)

lemma prerun_validE:
  assumes "reachable_state sys s"
  assumes "sys \<Turnstile>\<^bsub>pre\<^esub> I"
  shows "I s"
using assms unfolding prerun_valid_def
by (metis alwaysE reachable_stateE suffix_state_prop)


subsubsection\<open>Relating reachable states to the initial programs \label{sec:cimp-decompose-small-step}\<close>

text\<open>

To usefully reason about the control locations presumably embedded in
the single global invariant, we need to link the programs we have in
reachable state \<open>s\<close> to the programs in the initial states. The
\<open>fragments\<close> function decomposes the program into statements
that can be directly executed (\S\ref{sec:cimp-decompose}). We also
compute the locations we could be at after executing that statement as
a function of the process's local state.

Eliding the bodies of \<open>IF\<close> and \<open>WHILE\<close> statements
yields smaller (but equivalent) proof obligations.

\<close>

type_synonym  ('answer, 'location, 'question, 'state) loc_comp
  = "'state \<Rightarrow> 'location set"

fun lconst :: "'location set \<Rightarrow> ('answer, 'location, 'question, 'state) loc_comp" where
  "lconst lp s = lp"

definition lcond :: "'location set \<Rightarrow> 'location set \<Rightarrow> 'state bexp
                   \<Rightarrow> ('answer, 'location, 'question, 'state) loc_comp" where
  "lcond lp lp' b s = (if b s then lp else lp')"

lemma lcond_split:
  "Q (lcond lp lp' b s) \<longleftrightarrow> (b s \<longrightarrow> Q lp) \<and> (\<not>b s \<longrightarrow> Q lp')"
unfolding lcond_def by (simp split: if_splits)

lemma lcond_split_asm:
  "Q (lcond lp lp' b s) \<longleftrightarrow> \<not> ((b s \<and> \<not>Q lp) \<or> (\<not>b s \<and> \<not> Q lp'))"
unfolding lcond_def by (simp split: if_splits)

lemmas lcond_splits = lcond_split lcond_split_asm

fun
  fragments :: "('answer, 'location, 'question, 'state) com
              \<Rightarrow> 'location set
              \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
               \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "fragments (\<lbrace>l\<rbrace> IF b THEN c FI) aft
       = { (\<lbrace>l\<rbrace> IF b THEN c' FI, lcond (atC c) aft b) |c'. True }
        \<union> fragments c aft"
| "fragments (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI) aft
       = { (\<lbrace>l\<rbrace> IF b THEN c1' ELSE c2' FI, lcond (atC c1) (atC c2) b) |c1' c2'. True }
        \<union> fragments c1 aft \<union> fragments c2 aft"
| "fragments (LOOP DO c OD) aft = fragments c (atC c)"
| "fragments (\<lbrace>l\<rbrace> WHILE b DO c OD) aft
       =  fragments c {l} \<union> { (\<lbrace>l\<rbrace> WHILE b DO c' OD, lcond (atC c) aft b) |c'. True }"
| "fragments (c1;; c2) aft = fragments c1 (atC c2) \<union> fragments c2 aft"
| "fragments (c1 \<oplus> c2) aft = fragments c1 aft \<union> fragments c2 aft"
| "fragments c aft = { (c, lconst aft) }"

fun
  fragmentsL :: "('answer, 'location, 'question, 'state) com list
               \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                 \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "fragmentsL [] = {}"
| "fragmentsL [c] = fragments c {}"
| "fragmentsL (c # c' # cs) = fragments c (atC c') \<union> fragmentsL (c' # cs)"

abbreviation
  fragmentsLS :: "('answer, 'location, 'question, 'state) local_state
               \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                 \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "fragmentsLS s \<equiv> fragmentsL (cPGM s)"

text\<open>

We show that taking system steps preserves fragments.

\<close>

lemma small_step_fragmentsLS:
  assumes "s \<rightarrow>\<^bsub>\<alpha>\<^esub> s'"
  shows "fragmentsLS s' \<subseteq> fragmentsLS s"
using assms by induct (case_tac [!] cs, auto)

lemma reachable_state_fragmentsLS:
  assumes "reachable_state sys sh"
  shows "fragmentsLS (GST sh p) \<subseteq> fragments (PGMs sys p) {}"
using assms
by (induct rule: reachable_state_induct)
   (auto simp: initial_state_def dest: subsetD[OF small_step_fragmentsLS])

inductive
  basic_com :: "('answer, 'location, 'question, 'state) com \<Rightarrow> bool"
where
  "basic_com (\<lbrace>l\<rbrace> Request action val)"
| "basic_com (\<lbrace>l\<rbrace> Response action)"
| "basic_com (\<lbrace>l\<rbrace> LocalOp R)"
| "basic_com (\<lbrace>l\<rbrace> IF b THEN c FI)"
| "basic_com (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI)"
| "basic_com (\<lbrace>l\<rbrace> WHILE b DO c OD)"

lemma fragments_basic_com:
  assumes "(c', aft') \<in> fragments c aft"
  shows "basic_com c'"
using assms by (induct c arbitrary: aft) (auto intro: basic_com.intros)

lemma fragmentsL_basic_com:
  assumes "(c', aft') \<in> fragmentsL cs"
  shows "basic_com c'"
using assms
apply (induct cs)
 apply simp
apply (case_tac cs)
 apply (auto simp: fragments_basic_com)
done

text\<open>

To reason about system transitions we need to identify which basic
statement gets executed next. To that end we factor out the recursive
cases of the @{term "small_step"} semantics into \emph{contexts},
which isolate the \<open>basic_com\<close> commands with immediate
externally-visible behaviour. Note that non-determinism means that
more than one \<open>basic_com\<close> can be enabled at a time.

The representation of evaluation contexts follows @{cite
[cite_macro=citet] "DBLP:journals/jar/Berghofer12"}. This style of
operational semantics was originated by @{cite [cite_macro=citet]
"FelleisenHieb:1992"}.

\<close>

type_synonym ('answer, 'location, 'question, 'state) ctxt
  = "(('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com)
   \<times> (('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com list)"

inductive_set
  ctxt :: "('answer, 'location, 'question, 'state) ctxt set"
where
  C_Hole: "(id, \<langle>[]\<rangle>) \<in> ctxt"
| C_Loop: "(E, fctxt) \<in> ctxt \<Longrightarrow> (\<lambda>c1. LOOP DO E c1 OD, \<lambda>c1. fctxt c1 @ [LOOP DO E c1 OD]) \<in> ctxt"
| C_Seq: "(E, fctxt) \<in> ctxt \<Longrightarrow> (\<lambda>c1. E c1;; c2, \<lambda>c1. fctxt c1 @ [c2]) \<in> ctxt"
| C_Choose1: "(E, fctxt) \<in> ctxt \<Longrightarrow> (\<lambda>c1. E c1 \<oplus> c2, fctxt) \<in> ctxt"
| C_Choose2: "(E, fctxt) \<in> ctxt \<Longrightarrow> (\<lambda>c2. c1 \<oplus> E c2, fctxt) \<in> ctxt"

text\<open>

We can decompose a small step into a context and a @{const "basic_com"}.

\<close>

fun
  decompose_com :: "('answer, 'location, 'question, 'state) com
                      \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                        \<times> ('answer, 'location, 'question, 'state) ctxt ) set"
where
  "decompose_com (LOOP DO c1 OD) = { (c, \<lambda>t. LOOP DO ictxt t OD, \<lambda>t. fctxt t @ [LOOP DO ictxt t OD]) |c fctxt ictxt. (c, ictxt, fctxt) \<in> decompose_com c1 }"
| "decompose_com (c1;; c2) = { (c, \<lambda>t. ictxt t;; c2, \<lambda>t. fctxt t @ [c2]) |c fctxt ictxt. (c, ictxt, fctxt) \<in> decompose_com c1 }"
| "decompose_com (c1 \<oplus> c2) = { (c, \<lambda>t. ictxt t \<oplus> c2, fctxt) |c fctxt ictxt. (c, ictxt, fctxt) \<in> decompose_com c1 }
                           \<union> { (c, \<lambda>t. c1 \<oplus> ictxt t, fctxt) |c fctxt ictxt. (c, ictxt, fctxt) \<in> decompose_com c2 }"
| "decompose_com c = {(c, id, \<langle>[]\<rangle>)}"

definition
  decomposeLS :: "('answer, 'location, 'question, 'state) local_state
               \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                 \<times> (('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com)
                 \<times> (('answer, 'location, 'question, 'state) com \<Rightarrow> ('answer, 'location, 'question, 'state) com list) ) set"
where
  "decomposeLS s = (case cPGM s of c # _ \<Rightarrow> decompose_com c | _ \<Rightarrow> {})"

lemma ctxt_inj:
  assumes "(E, fctxt) \<in> ctxt"
  assumes "E x = E y"
  shows "x = y"
using assms by (induct set: ctxt) auto

lemma decompose_com_non_empty: "decompose_com c \<noteq> {}"
by (induct c) auto

lemma decompose_com_basic_com:
  assumes "(c', ctxts) \<in> decompose_com c"
  shows "basic_com c'"
using assms by (induct c arbitrary: c' ctxts) (auto intro: basic_com.intros)

lemma decomposeLS_basic_com:
  assumes "(c', ctxts) \<in> decomposeLS s"
  shows "basic_com c'"
using assms unfolding decomposeLS_def by (simp add: decompose_com_basic_com split: list.splits)

lemma decompose_com_ctxt:
  assumes "(c', ctxts) \<in> decompose_com c"
  shows "ctxts \<in> ctxt"
using assms by (induct c arbitrary: c' ctxts) (auto intro: ctxt.intros)

lemma decompose_com_ictxt:
  assumes "(c', ictxt, fctxt) \<in> decompose_com c"
  shows "ictxt c' = c"
using assms by (induct c arbitrary: c' ictxt fctxt) auto

lemma decompose_com_small_step:
  assumes as: "(c' # fctxt c' @ cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> s'"
  assumes ds: "(c', ictxt, fctxt) \<in> decompose_com c"
  shows "(c # cs, s) \<rightarrow>\<^bsub>\<alpha>\<^esub> s'"
using decompose_com_ctxt[OF ds] as decompose_com_ictxt[OF ds]
by (induct ictxt fctxt arbitrary: c cs)
   (cases s', fastforce simp: fun_eq_iff dest: ctxt_inj)+

theorem context_decompose:
  "s \<rightarrow>\<^bsub>\<alpha>\<^esub> s' \<longleftrightarrow> (\<exists>(c, ictxt, fctxt) \<in> decomposeLS s.
                     cPGM s = ictxt c # tl (cPGM s)
                   \<and> (c # fctxt c @ tl (cPGM s), cTKN s, cLST s) \<rightarrow>\<^bsub>\<alpha>\<^esub> s'
                   \<and> (\<forall>l\<in>atC c. cTKN s' = Some l))" (is "?lhs = ?rhs")
proof(rule iffI)
  assume ?lhs then show ?rhs
  unfolding decomposeLS_def
  proof(induct rule: small_step.induct)
    case (Choose1 c1 cs s \<alpha> cs' s' c2) then show ?case
      apply clarsimp
      apply (rename_tac c ictxt fctxt)
      apply (rule_tac x="(c, \<lambda>t. ictxt t \<oplus> c2, fctxt)" in bexI)
      apply auto
      done
  next
    case (Choose2 c2 cs s \<alpha> cs' s' c1) then show ?case
      apply clarsimp
      apply (rename_tac c ictxt fctxt)
      apply (rule_tac x="(c, \<lambda>t. c1 \<oplus> ictxt t, fctxt)" in bexI)
      apply auto
      done
  qed fastforce+
next
  assume ?rhs then show ?lhs
    unfolding decomposeLS_def
    by (cases s) (auto split: list.splits dest: decompose_com_small_step)
qed

text\<open>

While we only use this result left-to-right (to decompose a small step
into a basic one), this equivalence shows that we lose no information
in doing so.

Decomposing a compound command preserves @{const \<open>fragments\<close>} too.

\<close>

fun
  loc_compC :: "('answer, 'location, 'question, 'state) com
                            \<Rightarrow> ('answer, 'location, 'question, 'state) com list
                            \<Rightarrow> ('answer, 'location, 'question, 'state) loc_comp"
where
  "loc_compC (\<lbrace>l\<rbrace> IF b THEN c FI) cs = lcond (atC c) (atCs cs) b"
| "loc_compC (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI) cs = lcond (atC c1) (atC c2) b"
| "loc_compC (LOOP DO c OD) cs = lconst (atC c)"
| "loc_compC (\<lbrace>l\<rbrace> WHILE b DO c OD) cs = lcond (atC c) (atCs cs) b"
| "loc_compC c cs = lconst (atCs cs)"

lemma decompose_fragments:
  assumes "(c, ictxt, fctxt) \<in> decompose_com c0"
  shows "(c, loc_compC c (fctxt c @ cs)) \<in> fragments c0 (atCs cs)"
using assms
proof(induct c0 arbitrary: c ictxt fctxt cs)
  case (Loop c01 c ictxt fctxt cs)
  from Loop.prems Loop.hyps(1)[where cs="ictxt c # cs"] show ?case by (auto simp: decompose_com_ictxt)
next
  case (Seq c01 c02 c ictxt fctxt cs)
  from Seq.prems Seq.hyps(1)[where cs="c02 # cs"] show ?case by auto
qed auto

lemma at_decompose:
  assumes "(c, ictxt, fctxt) \<in> decompose_com c0"
  shows "atC c \<subseteq> atC c0"
using assms by (induct c0 arbitrary: c ictxt fctxt; fastforce)

lemma at_decomposeLS:
  assumes "(c, ictxt, fctxt) \<in> decomposeLS s"
  shows "atC c \<subseteq> atCs (cPGM s)"
using assms unfolding decomposeLS_def by (auto simp: at_decompose split: list.splits)

lemma decomposeLS_fragmentsLS:
  assumes "(c, ictxt, fctxt) \<in> decomposeLS s"
  shows "(c, loc_compC c (fctxt c @ tl (cPGM s))) \<in> fragmentsLS s"
using assms
proof(cases "cPGM s")
  case (Cons d ds)
  with assms decompose_fragments[where cs="ds"] show ?thesis
    by (cases ds) (auto simp: decomposeLS_def)
qed (simp add: decomposeLS_def)

lemma small_step_loc_compC:
  assumes "basic_com c"
  assumes "(c # cs, ls) \<rightarrow>\<^bsub>\<alpha>\<^esub> ls'"
  shows "loc_compC c cs (snd ls) = atCs (cPGM ls')"
using assms by (fastforce elim: basic_com.cases elim!: small_step_inv split: lcond_splits)

text\<open>

The headline result allows us to constrain the initial and final states
of a given small step in terms of the original programs, provided the
initial state is reachable.

\<close>

theorem decompose_small_step:
  assumes "GST sh p \<rightarrow>\<^bsub>\<alpha>\<^esub> ps'"
  assumes "reachable_state sys sh"
  obtains c cs aft
    where "(c, aft) \<in> fragments (PGMs sys p) {}"
      and "atC c \<subseteq> atCs (cPGM (GST sh p))"
      and "aft (cLST (GST sh p)) = atCs (cPGM ps')"
      and "(c # cs, cTKN (GST sh p), cLST (GST sh p)) \<rightarrow>\<^bsub>\<alpha>\<^esub> ps'"
      and "\<forall>l\<in>atC c. cTKN ps' = Some l"
using assms
apply -
apply (frule iffD1[OF context_decompose])
apply clarsimp
apply (frule decomposeLS_fragmentsLS)
apply (frule at_decomposeLS)
apply (frule (1) subsetD[OF reachable_state_fragmentsLS])
apply (frule decomposeLS_basic_com)
apply (frule (1) small_step_loc_compC)
apply simp
done

text\<open>

Reasoning by induction over the reachable states
with @{thm [source] "decompose_small_step"} is quite tedious. We
provide a very simple VCG that generates friendlier local proof
obligations in \S\ref{sec:vcg}.

\<close>


subsection\<open>Simple-minded Hoare Logic/VCG for CIMP \label{sec:vcg}\<close>

text\<open>

\label{sec:cimp-vcg}

We do not develop a proper Hoare logic or full VCG for CIMP: this
machinery merely packages up the subgoals that arise from induction
over the reachable states (\S\ref{sec:cimp-invariants}). This is
somewhat in the spirit of @{cite [cite_macro=citet] "Ridge:2009"}.

Note that this approach is not compositional: it consults the original
system to find matching communicating pairs, and \<open>aft\<close>
tracks the labels of possible successor statements. More serious Hoare
logics are provided by @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80" and "DBLP:journals/toplas/LamportS84"
and "CousotCousot89-IC"}.

Intuitively we need to discharge a proof obligation for either @{const
"Request"}s or @{const "Response"}s but not both. Here we choose to
focus on @{const "Request"}s as we expect to have more local
information available about these.

\<close>

inductive
  vcg :: "('answer, 'location, 'proc, 'question, 'state) programs
        \<Rightarrow> 'proc
        \<Rightarrow> ('answer, 'location, 'question, 'state) loc_comp
        \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred
        \<Rightarrow> ('answer, 'location, 'question, 'state) com
        \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) state_pred
        \<Rightarrow> bool" ("_, _, _ \<turnstile>/ \<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>" [11,0,0,0,0,0] 11)
where
  "\<lbrakk> \<And>aft' action' s ps' p's' l' \<beta> s' p'.
      \<lbrakk> pre s; (\<lbrace>l'\<rbrace> Response action', aft') \<in> fragments (coms p') {}; p \<noteq> p';
        ps' \<in> val \<beta> (s\<down> p); (p's', \<beta>) \<in> action' (action (s\<down> p)) (s\<down> p');
        at p l s; at p' l' s;
        AT s' = (AT s)(p := aft (s\<down> p), p' := aft' (s\<down> p'));
        s'\<down> = s\<down>(p := ps', p' := p's');
        taken p l s';
        HST s' = HST s @ [(action (s\<down> p), \<beta>)];
        \<forall>p''\<in>-{p,p'}. GST s' p'' = GST s p''
      \<rbrakk> \<Longrightarrow> post s'
   \<rbrakk> \<Longrightarrow> coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> Request action val \<lbrace>post\<rbrace>"
| "\<lbrakk> \<And>s ps' s'.
      \<lbrakk> pre s; ps' \<in> f (s\<down> p);
        at p l s;
        AT s' = (AT s)(p := aft (s\<down> p));
        s'\<down> = s\<down>(p := ps');
        taken p l s';
        HST s' = HST s;
        \<forall>p''\<in>-{p}. GST s' p'' = GST s p''
      \<rbrakk> \<Longrightarrow> post s'
   \<rbrakk> \<Longrightarrow> coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> LocalOp f \<lbrace>post\<rbrace>"
| "\<lbrakk> \<And>s s'.
      \<lbrakk> pre s;
        at p l s;
        AT s' = (AT s)(p := aft (s\<down> p));
        s'\<down> = s\<down>;
        taken p l s';
        HST s' = HST s;
        \<forall>p''\<in>-{p}. GST s' p'' = GST s p''
      \<rbrakk> \<Longrightarrow> post s'
   \<rbrakk> \<Longrightarrow> coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> IF b THEN t FI \<lbrace>post\<rbrace>"
| "\<lbrakk> \<And>s s'.
      \<lbrakk> pre s;
        at p l s;
        AT s' = (AT s)(p := aft (s\<down> p));
        s'\<down> = s\<down>;
        taken p l s';
        HST s' = HST s;
        \<forall>p''\<in>-{p}. GST s' p'' = GST s p''
      \<rbrakk> \<Longrightarrow> post s'
   \<rbrakk> \<Longrightarrow> coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> IF b THEN t ELSE e FI \<lbrace>post\<rbrace>"
| "\<lbrakk> \<And>s s'.
      \<lbrakk> pre s;
        at p l s;
        AT s' = (AT s)(p := aft (s\<down> p));
        s'\<down> = s\<down>;
        taken p l s';
        HST s' = HST s;
        \<forall>p''\<in>-{p}. GST s' p'' = GST s p''
      \<rbrakk> \<Longrightarrow> post s'
   \<rbrakk> \<Longrightarrow> coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> WHILE b DO c OD \<lbrace>post\<rbrace>"
\<comment> \<open>There are no proof obligations for the following commands, but including them makes some basic rules hold (\S\ref{sec:cimp:vcg_rules}):\<close>
| "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> Response action \<lbrace>post\<rbrace>"
| "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> c1 ;; c2 \<lbrace>post\<rbrace>"
| "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> LOOP DO c OD \<lbrace>post\<rbrace>"
| "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> c1 \<oplus> c2 \<lbrace>post\<rbrace>"

text\<open>

We abbreviate invariance with one-sided validity syntax.

\<close>

abbreviation valid_inv ("_, _, _ \<turnstile>/ \<lbrace>_\<rbrace>/ _" [11,0,0,0,0] 11) where
  "coms, p, aft \<turnstile> \<lbrace>I\<rbrace> c \<equiv> coms, p, aft \<turnstile> \<lbrace>I\<rbrace> c \<lbrace>I\<rbrace>"

inductive_cases vcg_inv:
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> Request action val \<lbrace>post\<rbrace>"
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> LocalOp f \<lbrace>post\<rbrace>"
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> IF b THEN t FI \<lbrace>post\<rbrace>"
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> IF b THEN t ELSE e FI \<lbrace>post\<rbrace>"
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> WHILE b DO c OD \<lbrace>post\<rbrace>"
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> LOOP DO c OD \<lbrace>post\<rbrace>"
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> Response action \<lbrace>post\<rbrace>"
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> c1 ;; c2 \<lbrace>post\<rbrace>"
  "coms, p, aft \<turnstile> \<lbrace>pre\<rbrace> Choose c1 c2 \<lbrace>post\<rbrace>"

text\<open>

We tweak @{const "fragments"} by omitting @{const "Response"}s,
yielding fewer obligations

\<close>

fun
  vcg_fragments' :: "('answer, 'location, 'question, 'state) com
               \<Rightarrow> 'location set
               \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                 \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "vcg_fragments' (\<lbrace>l\<rbrace> Response action) aft = {}"
| "vcg_fragments' (\<lbrace>l\<rbrace> IF b THEN c FI) aft
       = vcg_fragments' c aft
       \<union> { (\<lbrace>l\<rbrace> IF b THEN c' FI, lcond (atC c) aft b) |c'. True }"
| "vcg_fragments' (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI) aft
       = vcg_fragments' c2 aft \<union> vcg_fragments' c1 aft
       \<union> { (\<lbrace>l\<rbrace> IF b THEN c1' ELSE c2' FI, lcond (atC c1) (atC c2) b) |c1' c2'. True }"
| "vcg_fragments' (LOOP DO c OD) aft = vcg_fragments' c (atC c)"
| "vcg_fragments' (\<lbrace>l\<rbrace> WHILE b DO c OD) aft
       = vcg_fragments' c {l} \<union> { (\<lbrace>l\<rbrace> WHILE b DO c' OD, lcond (atC c) aft b) |c'. True }"
| "vcg_fragments' (c1 ;; c2) aft = vcg_fragments' c2 aft \<union> vcg_fragments' c1 (atC c2)"
| "vcg_fragments' (c1 \<oplus> c2) aft = vcg_fragments' c1 aft \<union> vcg_fragments' c2 aft"
| "vcg_fragments' c aft = {(c, lconst aft)}"

abbreviation
  vcg_fragments :: "('answer, 'location, 'question, 'state) com
                  \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                    \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "vcg_fragments c \<equiv> vcg_fragments' c {}"

fun isResponse :: "('answer, 'location, 'question, 'state) com \<Rightarrow> bool" where
  "isResponse (\<lbrace>l\<rbrace> Response action) \<longleftrightarrow> True"
| "isResponse _ \<longleftrightarrow> False"

lemma fragments_vcg_fragments':
  "\<lbrakk> (c, aft) \<in> fragments c' aft'; \<not>isResponse c \<rbrakk> \<Longrightarrow> (c, aft) \<in> vcg_fragments' c' aft'"
by (induct c' arbitrary: aft') auto

lemma vcg_fragments'_fragments:
  "vcg_fragments' c' aft' \<subseteq> fragments c' aft'" 
by (induct c' arbitrary: aft') (auto 10 0)

lemma VCG_step:
  assumes V: "\<And>p. \<forall>(c, aft) \<in> vcg_fragments (PGMs sys p). PGMs sys, p, aft \<turnstile> \<lbrace>pre\<rbrace> c \<lbrace>post\<rbrace>"
  assumes S: "system_step p sh' sh"
  assumes R: "reachable_state sys sh"
  assumes P: "pre sh"
  shows "post sh'"
using S
proof cases
  case LocalStep with P show ?thesis
    apply -
    apply (erule decompose_small_step[OF _ R])
    apply (frule fragments_basic_com)
    apply (erule basic_com.cases)
    apply (fastforce dest!: fragments_vcg_fragments' V[rule_format]
                      elim: vcg_inv elim!: small_step_inv
                      simp: LST_def AT_def taken_def fun_eq_iff)+
    done
next
  case CommunicationStep with P show ?thesis
    apply -
    apply (erule decompose_small_step[OF _ R])
    apply (erule decompose_small_step[OF _ R])
    subgoal for c cs aft c' cs' aft'
    apply (frule fragments_basic_com[where c'=c])
    apply (frule fragments_basic_com[where c'=c'])
    apply (elim basic_com.cases; clarsimp elim!: small_step_inv)
    apply (drule fragments_vcg_fragments')
    apply (fastforce dest!: V[rule_format]
                      elim: vcg_inv elim!: small_step_inv
                      simp: LST_def AT_def taken_def fun_eq_iff)+
    done
    done
qed

text\<open>

The user sees the conclusion of \<open>V\<close> for each element of @{const \<open>vcg_fragments\<close>}.

\<close>

lemma VCG_step_inv_stable:
  assumes V: "\<And>p. \<forall>(c, aft) \<in> vcg_fragments (PGMs sys p). PGMs sys, p, aft \<turnstile> \<lbrace>I\<rbrace> c"
  assumes "prerun sys \<sigma>"
  shows "(\<lceil>I\<rceil> \<^bold>\<hookrightarrow> \<circle>\<lceil>I\<rceil>) \<sigma>"
apply (rule alwaysI)
apply clarsimp
apply (rule nextI)
apply clarsimp
using assms(2) unfolding prerun_def
apply clarsimp
apply (erule_tac i=i in alwaysE)
unfolding system_step_reflclp_def
apply clarsimp
apply (erule disjE; clarsimp)
using VCG_step[where pre=I and post=I] V assms(2) prerun_reachable_state
apply blast
done

lemma VCG:
  assumes I: "\<forall>s. initial_state sys s \<longrightarrow> I (\<lparr>GST = s, HST = []\<rparr>)"
  assumes V: "\<And>p. \<forall>(c, aft) \<in> vcg_fragments (PGMs sys p). PGMs sys, p, aft \<turnstile> \<lbrace>I\<rbrace> c"
  shows "sys \<Turnstile>\<^bsub>pre\<^esub> I"
apply (rule prerun_valid_induct)
 apply (clarsimp simp: prerun_def state_prop_def)
 apply (metis (full_types) I old.unit.exhaust system_state.surjective)
using VCG_step_inv_stable[OF V] apply blast
done

lemmas VCG_valid = valid_prerun_lift[OF VCG, of sys I] for sys I
(*<*)

end
(*>*)
