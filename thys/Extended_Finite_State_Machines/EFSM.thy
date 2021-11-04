section \<open>Extended Finite State Machines\<close>

text\<open>This theory defines extended finite state machines as presented in \cite{foster2018}. States
are indexed by natural numbers, however, since transition matrices are implemented by finite sets,
the number of reachable states in $S$ is necessarily finite. For ease of implementation, we
implicitly make the initial state zero for all EFSMs. This allows EFSMs to be represented purely by
their transition matrix which, in this implementation, is a finite set of tuples of the form
$((s_1, s_2), t)$ in which $s_1$ is the origin state, $s_2$ is the destination state, and $t$ is a
transition.\<close>

theory EFSM
  imports "HOL-Library.FSet" Transition FSet_Utils
begin

declare One_nat_def [simp del]

type_synonym cfstate = nat
type_synonym inputs = "value list"
type_synonym outputs = "value option list"

type_synonym action = "(label \<times> inputs)"
type_synonym execution = "action list"
type_synonym observation = "outputs list"
type_synonym transition_matrix = "((cfstate \<times> cfstate) \<times> transition) fset"

no_notation relcomp (infixr "O" 75) and comp (infixl "o" 55)

type_synonym event = "(label \<times> inputs \<times> value list)"
type_synonym trace = "event list"
type_synonym log = "trace list"

definition Str :: "string \<Rightarrow> value" where
  "Str s \<equiv> value.Str (String.implode s)"

lemma str_not_num: "Str s \<noteq> Num x1"
  by (simp add: Str_def)

definition S :: "transition_matrix \<Rightarrow> nat fset" where
  "S m = (fimage (\<lambda>((s, s'), t). s) m) |\<union>| fimage (\<lambda>((s, s'), t). s') m"

lemma S_ffUnion: "S e = ffUnion (fimage (\<lambda>((s, s'), _). {|s, s'|}) e)"
  unfolding S_def
  by(induct e, auto)

subsection\<open>Possible Steps\<close>
text\<open>From a given state, the possible steps for a given action are those transitions with labels
which correspond to the action label, arities which correspond to the number of inputs, and guards
which are satisfied by those inputs.\<close>

definition possible_steps :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (cfstate \<times> transition) fset" where
  "possible_steps e s r l i = fimage (\<lambda>((origin, dest), t). (dest, t)) (ffilter (\<lambda>((origin, dest), t). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guards t) (join_ir i r)) e)"

lemma possible_steps_finsert:
"possible_steps (finsert ((s, s'), t) e) ss r l i = (
  if s = ss \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guards t) (join_ir i r) then
    finsert (s', t) (possible_steps e s r l i)
  else
    possible_steps e ss r l i
)"
  by (simp add: possible_steps_def ffilter_finsert)


lemma split_origin:
"ffilter (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> can_take_transition t i r) e =
ffilter (\<lambda>((origin, dest), t). Label t = l \<and> can_take_transition t i r) (ffilter (\<lambda>((origin, dest), t). origin = s) e)"
  by auto

lemma split_label:
"ffilter (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> can_take_transition t i r) e =
ffilter (\<lambda>((origin, dest), t). origin = s \<and> can_take_transition t i r) (ffilter (\<lambda>((origin, dest), t). Label t = l) e)"
  by auto

lemma possible_steps_empty_guards_false:
  "\<forall>((s1, s2), t) |\<in>| ffilter (\<lambda>((origin, dest), t). Label t = l) e. \<not>can_take_transition t i r \<Longrightarrow>
  possible_steps e s r l i = {||}"
  apply (simp add: possible_steps_def can_take[symmetric] split_label)
  by (simp add: Abs_ffilter fBall_def Ball_def)

lemma fmember_possible_steps: "(s', t) |\<in>| possible_steps e s r l i = (((s, s'), t) \<in> {((origin, dest), t) \<in> fset e. origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)})"
  apply (simp add: possible_steps_def ffilter_def fimage_def fmember_def Abs_fset_inverse)
  by force

lemma possible_steps_alt_aux:
  "possible_steps e s r l i = {|(d, t)|} \<Longrightarrow>
       ffilter (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)) e = {|((s, d), t)|}"
proof(induct e)
  case empty
  then show ?case
    by (simp add: fempty_not_finsert possible_steps_def)
next
  case (insert x e)
  then show ?case
    apply (case_tac x)
    subgoal for a b 
      apply (case_tac a)
      subgoal for aa _
        apply (simp add: possible_steps_def)
        apply (simp add: ffilter_finsert)
        apply (case_tac "aa = s \<and> Label b = l \<and> length i = Arity b \<and> apply_guards (Guards b) (join_ir i r)")
        by auto
      done
    done
qed

lemma possible_steps_alt: "(possible_steps e s r l i = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r))
     e = {|((s, d), t)|})"
  apply standard
   apply (simp add: possible_steps_alt_aux)
  by (simp add: possible_steps_def)

lemma possible_steps_alt3: "(possible_steps e s r l i = {|(d, t)|}) = (ffilter
     (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> can_take_transition t i r)
     e = {|((s, d), t)|})"
  apply standard
   apply (simp add: possible_steps_alt_aux can_take)
  by (simp add: possible_steps_def can_take)

lemma possible_steps_alt_atom: "(possible_steps e s r l i = {|dt|}) = (ffilter
     (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> can_take_transition t i r)
     e = {|((s, fst dt), snd dt)|})"
  apply (cases dt)
  by (simp add: possible_steps_alt can_take_transition_def can_take_def)

lemma possible_steps_alt2: "(possible_steps e s r l i = {|(d, t)|}) = (
     (ffilter (\<lambda>((origin, dest), t). Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)) (ffilter (\<lambda>((origin, dest), t). origin = s) e) = {|((s, d), t)|}))"
  apply (simp add: possible_steps_alt)
  apply (simp only: filter_filter)
  apply (rule arg_cong [of "(\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r))"])
  by (rule ext, auto)

lemma possible_steps_single_out:
"ffilter (\<lambda>((origin, dest), t). origin = s) e = {|((s, d), t)|} \<Longrightarrow>
Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r) \<Longrightarrow>
possible_steps e s r l i = {|(d, t)|}"
  apply (simp add: possible_steps_alt2 Abs_ffilter)
  by blast

lemma possible_steps_singleton: "(possible_steps e s r l i = {|(d, t)|}) =
    ({((origin, dest), t) \<in> fset e. origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)} = {((s, d), t)})"
  apply (simp add: possible_steps_alt Abs_ffilter Set.filter_def)
  by fast

lemma possible_steps_apply_guards:
  "possible_steps e s r l i = {|(s', t)|} \<Longrightarrow>
   apply_guards (Guards t) (join_ir i r)"
  apply (simp add: possible_steps_singleton)
  by auto

lemma possible_steps_empty:
  "(possible_steps e s r l i = {||}) = (\<forall>((origin, dest), t) \<in> fset e. origin \<noteq> s \<or> Label t \<noteq> l \<or> \<not> can_take_transition t i r)"
  apply (simp add: can_take_transition_def can_take_def)
  apply (simp add: possible_steps_def Abs_ffilter Set.filter_def)
  by auto

lemma singleton_dest:
  assumes "fis_singleton (possible_steps e s r aa b)"
      and "fthe_elem (possible_steps e s r aa b) = (baa, aba)"
    shows "((s, baa), aba) |\<in>| e"
  using assms
  apply (simp add: fis_singleton_fthe_elem)
  using possible_steps_alt_aux by force

lemma no_outgoing_transitions:
"ffilter (\<lambda>((s', _), _). s = s') e = {||} \<Longrightarrow>
possible_steps e s r l i = {||}"
  apply (simp add: possible_steps_def)
  by auto

lemma ffilter_split: "ffilter (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)) e =
                      ffilter (\<lambda>((origin, dest), t). Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)) (ffilter (\<lambda>((origin, dest), t). origin = s) e)"
  by auto

lemma one_outgoing_transition:
  defines "outgoing s \<equiv> (\<lambda>((origin, dest), t). origin = s)"
  assumes prem: "size (ffilter (outgoing s) e) = 1"
  shows "size (possible_steps e s r l i) \<le> 1"
proof-
  have less_eq_1: "\<And>x::nat. (x \<le> 1) = (x = 1 \<or> x = 0)"
    by auto
  have size_empty: "\<And>f. (size f = 0) = (f = {||})"
    subgoal for f
      by (induct f, auto)
    done
  show ?thesis
    using prem
    apply (simp only: possible_steps_def)
    apply (rule fimage_size_le)
    apply (simp only: ffilter_split outgoing_def[symmetric])
    by (metis (no_types, lifting) size_ffilter)
qed

subsection\<open>Choice\<close>
text\<open>Here we define the \texttt{choice} operator which determines whether or not two transitions are
nondeterministic.\<close>

definition choice :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice t t' = (\<exists> i r. apply_guards (Guards t) (join_ir i r) \<and> apply_guards (Guards t') (join_ir i r))"

definition choice_alt :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "choice_alt t t' = (\<exists> i r. apply_guards (Guards t@Guards t') (join_ir i r))"

lemma choice_alt: "choice t t' = choice_alt t t'"
  by (simp add: choice_def choice_alt_def apply_guards_append)

lemma choice_symmetry: "choice x y = choice y x"
  using choice_def by auto

definition deterministic :: "transition_matrix \<Rightarrow> bool" where
  "deterministic e = (\<forall>s r l i. size (possible_steps e s r l i) \<le> 1)"

lemma deterministic_alt_aux: "size (possible_steps e s r l i) \<le> 1 =(
        possible_steps e s r l i = {||} \<or>
        (\<exists>s' t.
            ffilter
             (\<lambda>((origin, dest), t). origin = s \<and> Label t = l \<and> length i = Arity t \<and> apply_guards (Guards t) (join_ir i r)) e =
            {|((s, s'), t)|}))"
  apply (case_tac "size (possible_steps e s r l i) = 0")
   apply (simp add: fset_equiv)
  apply (case_tac "possible_steps e s r l i = {||}")
   apply simp
  apply (simp only: possible_steps_alt[symmetric])
  by (metis le_neq_implies_less le_numeral_extra(4) less_one prod.collapse size_fsingleton)

lemma deterministic_alt: "deterministic e = (
  \<forall>s r l i.
    possible_steps e s r l i = {||} \<or>
    (\<exists>s' t. ffilter (\<lambda>((origin, dest), t). origin = s \<and> (Label t) = l \<and> (length i) = (Arity t) \<and> apply_guards (Guards t) (join_ir i r)) e = {|((s, s'), t)|})
)"
  using deterministic_alt_aux
  by (simp add: deterministic_def)

lemma size_le_1: "size f \<le> 1 = (f = {||} \<or> (\<exists>e. f = {|e|}))"
  apply standard
   apply (metis bot.not_eq_extremum gr_implies_not0 le_neq_implies_less less_one size_fsingleton size_fsubset)
  by auto

lemma ffilter_empty_if: "\<forall>x |\<in>| xs. \<not> P x \<Longrightarrow> ffilter P xs = {||}"
  by auto

lemma empty_ffilter: "ffilter P xs = {||} = (\<forall>x |\<in>| xs. \<not> P x)"
  by auto

lemma all_states_deterministic:
"(\<forall>s l i r.
  ffilter (\<lambda>((origin, dest), t). origin = s \<and> (Label t) = l \<and> can_take_transition t i r) e = {||} \<or>
  (\<exists>x. ffilter (\<lambda>((origin, dest), t). origin = s \<and> (Label t) = l \<and> can_take_transition t i r) e = {|x|})
) \<Longrightarrow> deterministic e"
  unfolding deterministic_def
  apply clarify
  subgoal for s r l i
    apply (erule_tac x=s in allE)
    apply (erule_tac x=l in allE)
    apply (erule_tac x=i in allE)
    apply (erule_tac x=r in allE)
    apply (simp only: size_le_1)
    apply (erule disjE)
     apply (rule_tac disjI1)
     apply (simp add: possible_steps_def can_take_transition_def can_take_def)
    apply (erule exE)
    subgoal for x
      apply (case_tac x)
      subgoal for a b
        apply (case_tac a)
        apply simp
        apply (induct e)
         apply auto[1]
        subgoal for _ _ _ ba
          apply (rule disjI2)
          apply (rule_tac x=ba in exI)
          apply (rule_tac x=b in exI)
          by (simp add: possible_steps_def can_take_transition_def[symmetric] can_take_def[symmetric])
        done
      done
    done
  done

lemma deterministic_finsert:
"\<forall>i r l.
\<forall>((a, b), t) |\<in>| ffilter (\<lambda>((origin, dest), t). origin = s) (finsert ((s, s'), t') e).
Label t = l \<and> can_take_transition t i r \<longrightarrow> \<not> can_take_transition t' i r \<Longrightarrow>
deterministic e \<Longrightarrow>
deterministic (finsert ((s, s'), t') e)"
  apply (simp add: deterministic_def possible_steps_finsert can_take del: size_fset_overloaded_simps)
  apply clarify
  subgoal for r i
    apply (erule_tac x=s in allE)
    apply (erule_tac x=r in allE)
    apply (erule_tac x="Label t'" in allE)
    apply (erule_tac x=i in allE)
    apply (erule_tac x=r in allE)
    apply (erule_tac x=i in allE)
    apply (erule_tac x="Label t'" in allE)
    by auto
  done

lemma ffilter_fBall: "(\<forall>x |\<in>| xs. P x) = (ffilter P xs = xs)"
  by auto

lemma fsubset_if: "\<forall>x. x |\<in>| f1 \<longrightarrow> x |\<in>| f2 \<Longrightarrow> f1 |\<subseteq>| f2"
  by auto

lemma in_possible_steps: "(((s, s'), t)|\<in>|e \<and> Label t = l \<and> can_take_transition t i r) = ((s', t) |\<in>| possible_steps e s r l i)"
  apply (simp add: fmember_possible_steps)
  by (simp add: can_take_def can_take_transition_def fmember.rep_eq)

lemma possible_steps_can_take_transition:
  "(s2, t1) |\<in>| possible_steps e1 s1 r l i \<Longrightarrow> can_take_transition t1 i r"
  using in_possible_steps by blast

lemma not_deterministic:
  "\<exists>s l i r.
    \<exists>d1 d2 t1 t2.
      d1 \<noteq> d2 \<and> t1 \<noteq> t2 \<and>
      ((s, d1), t1) |\<in>| e \<and>
      ((s, d2), t2) |\<in>| e \<and>
      Label t1 = Label t2 \<and>
      can_take_transition t1 i r \<and>
      can_take_transition t2 i r \<Longrightarrow>
  \<not>deterministic e"
  apply (simp add: deterministic_def not_le del: size_fset_overloaded_simps)
  apply clarify
  subgoal for s i r d1 d2 t1 t2
    apply (rule_tac x=s in exI)
    apply (rule_tac x=r in exI)
    apply (rule_tac x="Label t1" in exI)
    apply (rule_tac x=i in exI)
    apply (case_tac "(d1, t1) |\<in>| possible_steps e s r (Label t1) i")
     defer using in_possible_steps apply blast
    apply (case_tac "(d2, t2) |\<in>| possible_steps e s r (Label t1) i")
     apply (metis fempty_iff fsingleton_iff not_le_imp_less prod.inject size_le_1)
    using in_possible_steps by force
  done

lemma not_deterministic_conv:
  "\<not>deterministic e \<Longrightarrow>
  \<exists>s l i r.
    \<exists>d1 d2 t1 t2.
      (d1 \<noteq> d2 \<or> t1 \<noteq> t2) \<and>
      ((s, d1), t1) |\<in>| e \<and>
      ((s, d2), t2) |\<in>| e \<and>
      Label t1 = Label t2 \<and>
      can_take_transition t1 i r \<and>
      can_take_transition t2 i r"
  apply (simp add: deterministic_def not_le del: size_fset_overloaded_simps)
  apply clarify
  subgoal for s r l i
    apply (case_tac "\<exists>e1 e2 f'. e1 \<noteq> e2 \<and> possible_steps e s r l i = finsert e1 (finsert e2 f')")
     defer using size_gt_1 apply blast
    apply (erule exE)+
    subgoal for e1 e2 f'
      apply (case_tac e1, case_tac e2)
      subgoal for a b aa ba
        apply (simp del: size_fset_overloaded_simps)
        apply (rule_tac x=s in exI)
        apply (rule_tac x=i in exI)
        apply (rule_tac x=r in exI)
        apply (rule_tac x=a in exI)
        apply (rule_tac x=aa in exI)
        apply (rule_tac x=b in exI)
        apply (rule_tac x=ba in exI)
        by (metis finsertI1 finsert_commute in_possible_steps)
      done
    done
  done

lemma deterministic_if:
"\<nexists>s l i r.
  \<exists>d1 d2 t1 t2.
    (d1 \<noteq> d2 \<or> t1 \<noteq> t2) \<and>
    ((s, d1), t1) |\<in>| e \<and>
    ((s, d2), t2) |\<in>| e \<and>
    Label t1 = Label t2 \<and>
    can_take_transition t1 i r \<and>
    can_take_transition t2 i r \<Longrightarrow>
  deterministic e"
  using not_deterministic_conv by blast

lemma "\<forall>l i r.
  (\<forall>((s, s'), t) |\<in>| e. Label t = l \<and> can_take_transition t i r \<and>
  (\<nexists>t' s''. ((s, s''), t') |\<in>| e \<and> (s' \<noteq> s'' \<or> t' \<noteq> t) \<and> Label t' = l \<and> can_take_transition t' i r))
 \<Longrightarrow> deterministic e"
  apply (simp add: deterministic_def del: size_fset_overloaded_simps)
  apply (rule allI)+
  apply (simp only: size_le_1 possible_steps_empty)
  apply (case_tac "\<exists>t s'. ((s, s'), t)|\<in>|e \<and> Label t = l \<and> can_take_transition t i r")
   defer using notin_fset apply fastforce
  apply (rule disjI2)
  apply clarify
  apply (rule_tac x="(s', t)" in exI)
  apply standard
   defer apply (meson fempty_fsubsetI finsert_fsubset in_possible_steps)
  apply standard
  apply (case_tac x)
  apply (simp add: in_possible_steps[symmetric])
  apply (erule_tac x="Label t" in allE)
  apply (erule_tac x=i in allE)
  apply (erule_tac x=r in allE)
  apply (erule_tac x="((s, s'), t)" in fBallE)
   defer apply simp
  apply simp
  apply (erule_tac x=b in allE)
  apply simp
  apply (erule_tac x=a in allE)
  by simp

definition "outgoing_transitions e s = ffilter (\<lambda>((o, _), _). o = s) e"

lemma in_outgoing: "((s1, s2), t) |\<in>| outgoing_transitions e s = (((s1, s2), t) |\<in>| e \<and> s1 = s)"
  by (simp add: outgoing_transitions_def)

lemma outgoing_transitions_deterministic:
  "\<forall>s.
    \<forall>((s1, s2), t) |\<in>| outgoing_transitions e s.
      \<forall>((s1', s2'), t') |\<in>| outgoing_transitions e s.
        s2 \<noteq> s2' \<or> t \<noteq> t' \<longrightarrow> Label t = Label t' \<longrightarrow> \<not> choice t t' \<Longrightarrow> deterministic e"
  apply (rule deterministic_if)
  apply simp
  apply (rule allI)
  subgoal for s
    apply (erule_tac x=s in allE)
    apply (simp add: fBall_def Ball_def)
    apply (rule allI)+
    subgoal for i r d1 d2 t1
      apply (erule_tac x=s in allE)
      apply (erule_tac x=d1 in allE)
      apply (erule_tac x=t1 in allE)
      apply (rule impI, rule allI)
      subgoal for t2
        apply (case_tac "((s, d1), t1) \<in> fset (outgoing_transitions e s)")
         apply simp
         apply (erule_tac x=s in allE)
         apply (erule_tac x=d2 in allE)
         apply (erule_tac x=t2 in allE)
         apply (simp add: outgoing_transitions_def choice_def can_take)
         apply (meson fmember_implies_member)
        apply (simp add: outgoing_transitions_def)
        by (meson fmember_implies_member)
      done
    done
  done

lemma outgoing_transitions_deterministic2: "(\<And>s a b ba aa bb bc.
       ((a, b), ba) |\<in>| outgoing_transitions e s \<Longrightarrow>
       ((aa, bb), bc) |\<in>| (outgoing_transitions e s) - {|((a, b), ba)|} \<Longrightarrow> b \<noteq> bb \<or> ba \<noteq> bc \<Longrightarrow> \<not>choice ba bc)
        \<Longrightarrow> deterministic e"
  apply (rule outgoing_transitions_deterministic)
  by blast

lemma outgoing_transitions_fprod_deterministic:
"(\<And>s b ba bb bc.
(((s, b), ba), ((s, bb), bc)) \<in> fset (outgoing_transitions e s) \<times> fset (outgoing_transitions e s)
\<Longrightarrow> b \<noteq> bb \<or> ba \<noteq> bc \<Longrightarrow> Label ba = Label bc \<Longrightarrow> \<not>choice ba bc)
\<Longrightarrow> deterministic e"
  apply (rule outgoing_transitions_deterministic)
  apply clarify
  by (metis SigmaI fmember_implies_member in_outgoing)

text\<open>The \texttt{random\_member} function returns a random member from a finite set, or
\texttt{None}, if the set is empty.\<close>
definition random_member :: "'a fset \<Rightarrow> 'a option" where
  "random_member f = (if f = {||} then None else Some (Eps (\<lambda>x. x |\<in>| f)))"

lemma random_member_nonempty: "s \<noteq> {||} = (random_member s \<noteq> None)"
  by (simp add: random_member_def)

lemma random_member_singleton [simp]: "random_member {|a|} = Some a"
  by (simp add: random_member_def)

lemma random_member_is_member:
  "random_member ss = Some s \<Longrightarrow> s |\<in>| ss"
  apply (simp add: random_member_def)
  by (metis equalsffemptyI option.distinct(1) option.inject verit_sko_ex_indirect)

lemma random_member_None[simp]: "random_member ss = None = (ss = {||})"
  by (simp add: random_member_def)

lemma random_member_empty[simp]: "random_member {||} = None"
  by simp

definition step :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> label \<Rightarrow> inputs \<Rightarrow> (transition \<times> cfstate \<times> outputs \<times> registers) option" where
  "step e s r l i = (case random_member (possible_steps e s r l i) of
      None \<Rightarrow> None |
      Some (s', t) \<Rightarrow>  Some (t, s', evaluate_outputs t i r, evaluate_updates t i r)
  )"

lemma possible_steps_not_empty_iff:
  "step e s r a b \<noteq> None \<Longrightarrow>
   \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s r a b"
  apply (simp add: step_def)
  apply (case_tac "possible_steps e s r a b")
   apply (simp add: random_member_def)
  by auto

lemma step_member: "step e s r l i = Some (t, s', p, r') \<Longrightarrow> (s', t) |\<in>| possible_steps e s r l i"
  apply (simp add: step_def)
  apply (case_tac "random_member (possible_steps e s r l i)")
   apply simp
  subgoal for a by (case_tac a, simp add: random_member_is_member)
  done

lemma step_outputs: "step e s r l i = Some (t, s', p, r') \<Longrightarrow> evaluate_outputs t i r = p"
  apply (simp add: step_def)
  apply (case_tac "random_member (possible_steps e s r l i)")
  by auto

lemma step:
  "possibilities = (possible_steps e s r l i) \<Longrightarrow>
   random_member possibilities = Some (s', t) \<Longrightarrow>
   evaluate_outputs t i r = p \<Longrightarrow>
   evaluate_updates t i r = r' \<Longrightarrow>
   step e s r l i = Some (t, s', p, r')"
  by (simp add: step_def)

lemma step_None: "step e s r l i = None = (possible_steps e s r l i = {||})"
  by (simp add: step_def prod.case_eq_if random_member_def)

lemma step_Some: "step e s r l i = Some (t, s', p, r') =
  (
    random_member (possible_steps e s r l i) = Some (s', t) \<and>
    evaluate_outputs t i r = p \<and>
    evaluate_updates t i r = r'
  )"
  apply (simp add: step_def)
  apply (case_tac "random_member (possible_steps e s r l i)")
   apply simp
  subgoal for a by (case_tac a, auto)
  done

lemma no_possible_steps_1:
  "possible_steps e s r l i = {||} \<Longrightarrow> step e s r l i = None"
  by (simp add: step_def random_member_def)

subsection\<open>Execution Observation\<close>
text\<open>One of the key features of this formalisation of EFSMs is their ability to produce
\emph{outputs}, which represent function return values. When action sequences are executed in an
EFSM, they produce a corresponding \emph{observation}.\<close>

text_raw\<open>\snip{observe}{1}{2}{%\<close>
fun observe_execution :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> outputs list" where
  "observe_execution _ _ _ [] = []" |
  "observe_execution e s r ((l, i)#as)  = (
    let viable = possible_steps e s r l i in
    if viable = {||} then
      []
    else
      let (s', t) = Eps (\<lambda>x. x |\<in>| viable) in
      (evaluate_outputs t i r)#(observe_execution e s' (evaluate_updates t i r) as)
    )"
text_raw\<open>}%endsnip\<close>

lemma observe_execution_step_def: "observe_execution e s r ((l, i)#as)  = (
    case step e s r l i of
      None \<Rightarrow> []|
      Some (t, s', p, r') \<Rightarrow> p#(observe_execution e s' r' as)
    )"
  apply (simp add: step_def)
  apply (case_tac "possible_steps e s r l i")
   apply simp
  subgoal for x S'
    apply (simp add: random_member_def)
    apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
    by simp
  done

lemma observe_execution_first_outputs_equiv:
  "observe_execution e1 s1 r1 ((l, i) # ts) = observe_execution e2 s2 r2 ((l, i) # ts) \<Longrightarrow>
   step e1 s1 r1 l i = Some (t, s', p, r') \<Longrightarrow>
   \<exists>(s2', t2)|\<in>|possible_steps e2 s2 r2 l i. evaluate_outputs t2 i r2 = p"
  apply (simp only: observe_execution_step_def)
  apply (case_tac "step e2 s2 r2 l i")
   apply simp
  subgoal for a
    apply simp
    apply (case_tac a)
    apply clarsimp
    by (meson step_member case_prodI rev_fBexI step_outputs)
  done

lemma observe_execution_step:
  "step e s r (fst h) (snd h) = Some (t, s', p, r') \<Longrightarrow>
   observe_execution e s' r' es = obs \<Longrightarrow>
   observe_execution e s r (h#es) = p#obs"
  apply (cases h, simp add: step_def)
  apply (case_tac "possible_steps e s r a b = {||}")
   apply simp
  subgoal for a b
    apply (case_tac "SOME x. x |\<in>| possible_steps e s r a b")
    by (simp add: random_member_def)
  done

lemma observe_execution_possible_step:
  "possible_steps e s r (fst h) (snd h) = {|(s', t)|} \<Longrightarrow>
   apply_outputs (Outputs t) (join_ir (snd h) r) = p \<Longrightarrow>
   apply_updates (Updates t) (join_ir (snd h) r) r = r' \<Longrightarrow>
   observe_execution e s' r' es = obs \<Longrightarrow>
   observe_execution e s r (h#es) = p#obs"
  by (simp add: observe_execution_step step)

lemma observe_execution_no_possible_step:
  "possible_steps e s r (fst h) (snd h) = {||} \<Longrightarrow>
   observe_execution e s r (h#es) = []"
  by (cases h, simp)

lemma observe_execution_no_possible_steps:
  "possible_steps e1 s1 r1 (fst h) (snd h) = {||} \<Longrightarrow>
   possible_steps e2 s2 r2 (fst h) (snd h) = {||} \<Longrightarrow>
   (observe_execution e1 s1 r1 (h#t)) = (observe_execution e2 s2 r2 (h#t))"
  by (simp add: observe_execution_no_possible_step)

lemma observe_execution_one_possible_step:
  "possible_steps e1 s1 r (fst h) (snd h) = {|(s1', t1)|} \<Longrightarrow>
   possible_steps e2 s2 r (fst h) (snd h) = {|(s2', t2)|} \<Longrightarrow>
   apply_outputs (Outputs t1) (join_ir (snd h) r) = apply_outputs (Outputs t2) (join_ir (snd h) r) \<Longrightarrow>

   apply_updates (Updates t1) (join_ir (snd h) r) r = r' \<Longrightarrow>
   apply_updates (Updates t2) (join_ir (snd h) r) r = r' \<Longrightarrow>
   (observe_execution e1 s1' r' t) = (observe_execution e2 s2' r' t) \<Longrightarrow>
   (observe_execution e1 s1 r (h#t)) = (observe_execution e2 s2 r (h#t))"
  by (simp add: observe_execution_possible_step)

subsubsection\<open>Utilities\<close>
text\<open>Here we define some utility functions to access the various key properties of a given EFSM.\<close>

definition max_reg :: "transition_matrix \<Rightarrow> nat option" where
  "max_reg e = (let maxes = (fimage (\<lambda>(_, t). Transition.max_reg t) e) in if maxes = {||} then None else fMax maxes)"

definition enumerate_ints :: "transition_matrix \<Rightarrow> int set" where
  "enumerate_ints e = \<Union> (image (\<lambda>(_, t). Transition.enumerate_ints t) (fset e))"

definition max_int :: "transition_matrix \<Rightarrow> int" where
  "max_int e = Max (insert 0 (enumerate_ints e))"

definition max_output :: "transition_matrix \<Rightarrow> nat" where
  "max_output e = fMax (fimage (\<lambda>(_, t). length (Outputs t)) e)"

definition all_regs :: "transition_matrix \<Rightarrow> nat set" where
  "all_regs e = \<Union> (image (\<lambda>(_, t). enumerate_regs t) (fset e))"

text_raw\<open>\snip{finiteRegs}{1}{2}{%\<close>
lemma finite_all_regs: "finite (all_regs e)"
text_raw\<open>}%endsnip\<close>
  apply (simp add: all_regs_def enumerate_regs_def)
  apply clarify
  apply standard
   apply (rule finite_UnI)+
  using GExp.finite_enumerate_regs apply blast
  using AExp.finite_enumerate_regs apply blast
   apply (simp add: AExp.finite_enumerate_regs prod.case_eq_if)
  by auto

definition max_input :: "transition_matrix \<Rightarrow> nat option" where
  "max_input e = fMax (fimage (\<lambda>(_, t). Transition.max_input t) e)"

fun maxS :: "transition_matrix \<Rightarrow> nat" where
  "maxS t = (if t = {||} then 0 else fMax ((fimage (\<lambda>((origin, dest), t). origin) t) |\<union>| (fimage (\<lambda>((origin, dest), t). dest) t)))"

subsection\<open>Execution Recognition\<close>
text\<open>The \texttt{recognises} function returns true if the given EFSM recognises a given execution.
That is, the EFSM is able to respond to each event in sequence. There is no restriction on the
outputs produced. When a recognised execution is observed, it produces an accepted trace of the
EFSM.\<close>

text_raw\<open>\snip{recognises}{1}{2}{%\<close>
inductive recognises_execution :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base [simp]: "recognises_execution e s r []" |
  step: "\<exists>(s', T) |\<in>| possible_steps e s r l i.
         recognises_execution e s' (evaluate_updates T i r) t \<Longrightarrow>
         recognises_execution e s r ((l, i)#t)"
text_raw\<open>}%endsnip\<close>

abbreviation "recognises e t \<equiv> recognises_execution e 0 <> t"

definition "E e = {x. recognises e x}"

lemma no_possible_steps_rejects:
  "possible_steps e s r l i = {||} \<Longrightarrow> \<not> recognises_execution e s r ((l, i)#t)"
  apply clarify
  by (rule recognises_execution.cases, auto)

lemma recognises_step_equiv: "recognises_execution e s r ((l, i)#t) =
   (\<exists>(s', T) |\<in>| possible_steps e s r l i. recognises_execution e s' (evaluate_updates T i r) t)"
  apply standard
   apply (rule recognises_execution.cases)
  by (auto simp: recognises_execution.step)

fun recognises_prim :: "transition_matrix \<Rightarrow> nat \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  "recognises_prim e s r [] = True" |
  "recognises_prim e s r ((l, i)#t) = (
    let poss_steps = possible_steps e s r l i in
    (\<exists>(s', T) |\<in>| poss_steps. recognises_prim e s' (evaluate_updates T i r) t)
  )"

lemma recognises_prim [code]: "recognises_execution e s r t = recognises_prim e s r t"
proof(induct t arbitrary: r s)
  case Nil
  then show ?case
    by simp
next
  case (Cons h t)
  then show ?case
    apply (cases h)
    apply simp
    apply standard
     apply (rule recognises_execution.cases, simp)
      apply simp
     apply auto[1]
    using recognises_execution.step by blast
qed

lemma recognises_single_possible_step:
  assumes "possible_steps e s r l i = {|(s', t)|}"
      and "recognises_execution e s' (evaluate_updates t i r) trace"
    shows "recognises_execution e s r ((l, i)#trace)"
  apply (rule recognises_execution.step)
  using assms by auto

lemma recognises_single_possible_step_atomic:
  assumes "possible_steps e s r (fst h) (snd h) = {|(s', t)|}"
      and "recognises_execution e s' (apply_updates (Updates t) (join_ir (snd h) r) r) trace"
    shows "recognises_execution e s r (h#trace)"
  by (metis assms prod.collapse recognises_single_possible_step)

lemma recognises_must_be_possible_step:
  "recognises_execution e s r (h # t) \<Longrightarrow>
   \<exists>aa ba. (aa, ba) |\<in>| possible_steps e s r (fst h) (snd h)"
  using recognises_step_equiv by fastforce

lemma recognises_possible_steps_not_empty:
  "recognises_execution e s r (h#t) \<Longrightarrow> possible_steps e s r (fst h) (snd h) \<noteq> {||}"
  apply (rule recognises_execution.cases)
  by auto

lemma recognises_must_be_step:
  "recognises_execution e s r (h#ts) \<Longrightarrow>
   \<exists>t s' p d'. step e s r (fst h) (snd h) = Some (t, s', p, d')"
  apply (cases h)
  subgoal for a b 
    apply (simp add: recognises_step_equiv step_def)
    apply clarify
    apply (case_tac "(possible_steps e s r a b)")
     apply (simp add: random_member_def)
    apply (simp add: random_member_def)
    subgoal for _ _ x S' apply (case_tac "SOME xa. xa = x \<or> xa |\<in>| S'")
      by simp
    done
  done

lemma recognises_cons_step:
  "recognises_execution e s r (h # t) \<Longrightarrow> step e s r (fst h) (snd h) \<noteq>  None"
  by (simp add: recognises_must_be_step)

lemma no_step_none:
  "step e s r aa ba = None \<Longrightarrow> \<not> recognises_execution e s r ((aa, ba) # p)"
  using recognises_cons_step by fastforce

lemma step_none_rejects:
  "step e s r (fst h) (snd h) = None \<Longrightarrow> \<not> recognises_execution e s r (h#t)"
  using no_step_none surjective_pairing by fastforce

lemma trace_reject:
  "(\<not> recognises_execution e s r ((l, i)#t)) = (possible_steps e s r l i = {||} \<or> (\<forall>(s', T) |\<in>| possible_steps e s r l i. \<not> recognises_execution e s' (evaluate_updates T i r) t))"
  using recognises_prim by fastforce

lemma trace_reject_no_possible_steps_atomic:
  "possible_steps e s r (fst a) (snd a) = {||} \<Longrightarrow> \<not> recognises_execution e s r (a#t)"
  using recognises_possible_steps_not_empty by auto

lemma trace_reject_later:
  "\<forall>(s', T) |\<in>| possible_steps e s r l i. \<not> recognises_execution e s' (evaluate_updates T i r) t \<Longrightarrow>
   \<not> recognises_execution e s r ((l, i)#t)"
  using trace_reject by auto

lemma recognition_prefix_closure: "recognises_execution e s r (t@t') \<Longrightarrow> recognises_execution e s r t"
proof(induct t arbitrary: s r)
  case (Cons a t)
  then show ?case
    apply (cases a, clarsimp)
    apply (rule recognises_execution.cases)
      apply simp
     apply simp
    by (rule recognises_execution.step, auto)
qed auto

lemma rejects_prefix: "\<not> recognises_execution e s r t \<Longrightarrow> \<not> recognises_execution e s r (t @ t')"
  using recognition_prefix_closure by blast

lemma recognises_head: "recognises_execution e s r (h#t) \<Longrightarrow> recognises_execution e s r [h]"
  by (simp add: recognition_prefix_closure)

subsubsection\<open>Trace Acceptance\<close>
text\<open>The \texttt{accepts} function returns true if the given EFSM accepts a given trace. That is,
the EFSM is able to respond to each event in sequence \emph{and} is able to produce the expected
output. Accepted traces represent valid runs of an EFSM.\<close>

text_raw\<open>\snip{accepts}{1}{2}{%\<close>
inductive accepts_trace :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base [simp]: "accepts_trace e s r []" |
  step: "\<exists>(s', T) |\<in>| possible_steps e s r l i.
         evaluate_outputs T i r = map Some p \<and> accepts_trace e s' (evaluate_updates T i r) t \<Longrightarrow>
         accepts_trace e s r ((l, i, p)#t)"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{T}{1}{2}{%\<close>
definition T :: "transition_matrix \<Rightarrow> trace set" where
  "T e = {t. accepts_trace e 0 <> t}"
text_raw\<open>}%endsnip\<close>

abbreviation "rejects_trace e s r t \<equiv> \<not> accepts_trace e s r t"

lemma accepts_trace_step:
  "accepts_trace e s r ((l, i, p)#t) = (\<exists>(s', T) |\<in>| possible_steps e s r l i.
         evaluate_outputs T i r = map Some p \<and>
         accepts_trace e s' (evaluate_updates T i r) t)"
  apply standard
  by (rule accepts_trace.cases, auto simp: accepts_trace.step)

lemma accepts_trace_exists_possible_step:
  "accepts_trace e1 s1 r1 ((aa, b, c) # t) \<Longrightarrow>
       \<exists>(s1', t1)|\<in>|possible_steps e1 s1 r1 aa b.
          evaluate_outputs t1 b r1 = map Some c"
  using accepts_trace_step by auto

lemma rejects_trace_step:
"rejects_trace e s r ((l, i, p)#t) = (
  (\<forall>(s', T) |\<in>| possible_steps e s r l i.  evaluate_outputs T i r \<noteq> map Some p \<or> rejects_trace e s' (evaluate_updates T i r) t)
)"
  apply (simp add: accepts_trace_step)
  by auto

definition accepts_log :: "trace set \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "accepts_log l e = (\<forall>t \<in> l. accepts_trace e 0 <> t)"

text_raw\<open>\snip{prefixClosure}{1}{2}{%\<close>
lemma prefix_closure: "accepts_trace e s r (t@t') \<Longrightarrow> accepts_trace e s r t"
text_raw\<open>}%endsnip\<close>
proof(induct t arbitrary: s r)
next
  case (Cons a t)
  then show ?case
    apply (cases a, clarsimp)
    apply (simp add: accepts_trace_step)
    by auto
qed auto

text\<open>For code generation, it is much more efficient to re-implement the \texttt{accepts\_trace}
function primitively than to use the code generator's default setup for inductive definitions.\<close>
fun accepts_trace_prim :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  "accepts_trace_prim _ _ _ [] = True" |
  "accepts_trace_prim e s r ((l, i, p)#t) = (
    let poss_steps = possible_steps e s r l i in
    if fis_singleton poss_steps then
      let (s', T) = fthe_elem poss_steps in
      if evaluate_outputs T i r = map Some p then
        accepts_trace_prim e s' (evaluate_updates T i r) t
      else False
    else
      (\<exists>(s', T) |\<in>| poss_steps.
         evaluate_outputs T i r = (map Some p) \<and>
         accepts_trace_prim e s' (evaluate_updates T i r) t))"

lemma accepts_trace_prim [code]: "accepts_trace e s r l = accepts_trace_prim e s r l"
proof(induct l arbitrary: s r)
  case (Cons a l)
  then show ?case
    apply (cases a)
    apply (simp add: accepts_trace_step Let_def fis_singleton_alt)
    by auto
qed auto

subsection\<open>EFSM Comparison\<close>
text\<open>Here, we define some different metrics of EFSM equality.\<close>

subsubsection\<open>State Isomporphism\<close>
text\<open>Two EFSMs are isomorphic with respect to states if there exists a bijective function between
the state names of the two EFSMs, i.e. the only difference between the two models is the way the
states are indexed.\<close>

definition isomorphic :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "isomorphic e1 e2 = (\<exists>f. bij f \<and> (\<forall>((s1, s2), t) |\<in>| e1. ((f s1, f s2), t) |\<in>| e2))"

subsubsection\<open>Register Isomporphism\<close>
text\<open>Two EFSMs are isomorphic with respect to registers if there exists a bijective function between
the indices of the registers in the two EFSMs, i.e. the only difference between the two models is
the way the registers are indexed.\<close>
definition rename_regs :: "(nat \<Rightarrow> nat) \<Rightarrow> transition_matrix \<Rightarrow> transition_matrix" where
  "rename_regs f e = fimage (\<lambda>(tf, t). (tf, Transition.rename_regs f t)) e"

definition eq_upto_rename_strong :: "transition_matrix \<Rightarrow> transition_matrix \<Rightarrow> bool" where
  "eq_upto_rename_strong e1 e2 = (\<exists>f. bij f \<and> rename_regs f e1 = e2)"

subsubsection\<open>Trace Simulation\<close>
text\<open>An EFSM, $e_1$ simulates another EFSM $e_2$ if there is a function between the states of the
states of $e_1$ and $e_1$ such that in each state, if $e_1$ can respond to the event and produce
the correct output, so can $e_2$.\<close>

text_raw\<open>\snip{traceSim}{1}{2}{%\<close>
inductive trace_simulation :: "(cfstate \<Rightarrow> cfstate) \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow>
transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> trace \<Rightarrow> bool" where
  base: "s2 = f s1 \<Longrightarrow> trace_simulation f e1 s1 r1 e2 s2 r2 []" |
  step: "s2 = f s1 \<Longrightarrow>
         \<forall>(s1', t1) |\<in>| ffilter (\<lambda>(s1', t1). evaluate_outputs t1 i r1 = map Some o) (possible_steps e1 s1 r1 l i).
           \<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i. evaluate_outputs t2 i r2 = map Some o \<and>
            trace_simulation f e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es \<Longrightarrow>
         trace_simulation f e1 s1 r1 e2 s2 r2 ((l, i, o)#es)"
text_raw\<open>}%endsnip\<close>

lemma trace_simulation_step:
"trace_simulation f e1 s1 r1 e2 s2 r2 ((l, i, o)#es) = (
  (s2 = f s1) \<and> (\<forall>(s1', t1) |\<in>| ffilter (\<lambda>(s1', t1). evaluate_outputs t1 i r1 = map Some o) (possible_steps e1 s1 r1 l i).
         (\<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i. evaluate_outputs t2 i r2 = map Some o \<and>
         trace_simulation f e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es))
)"
  apply standard
   apply (rule trace_simulation.cases, simp+)
  apply (rule trace_simulation.step)
   apply simp
  by blast

lemma trace_simulation_step_none:
  "s2 = f s1 \<Longrightarrow>
   \<nexists>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i. evaluate_outputs t1 i r1 = map Some o \<Longrightarrow>
   trace_simulation f e1 s1 r1 e2 s2 r2 ((l, i, o)#es)"
  apply (rule trace_simulation.step)
   apply simp
  apply (case_tac "ffilter (\<lambda>(s1', t1). evaluate_outputs t1 i r1 = map Some o) (possible_steps e1 s1 r1 l i)")
   apply simp
  by fastforce

definition "trace_simulates e1 e2 = (\<exists>f. \<forall>t. trace_simulation f e1 0 <> e2 0 <> t)"

lemma rejects_trace_simulation:
  "rejects_trace e2 s2 r2 t \<Longrightarrow>
   accepts_trace e1 s1 r1 t \<Longrightarrow>
   \<not>trace_simulation f e1 s1 r1 e2 s2 r2 t"
proof(induct t arbitrary: s1 r1 s2 r2)
  case Nil
  then show ?case
    using accepts_trace.base by blast
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (simp add: rejects_trace_step)
    apply (simp add: accepts_trace_step)
    apply clarify
    apply (rule trace_simulation.cases)
      apply simp
     apply simp
    apply clarsimp
    subgoal for l o _ _ i
      apply (case_tac "ffilter (\<lambda>(s1', t1). evaluate_outputs t1 i r1 = map Some o) (possible_steps e1 s1 r1 l i) = {||}")
       apply auto[1]
      by fastforce
    done
qed

lemma accepts_trace_simulation:
  "accepts_trace e1 s1 r1 t \<Longrightarrow>
   trace_simulation f e1 s1 r1 e2 s2 r2 t \<Longrightarrow>
   accepts_trace e2 s2 r2 t"
  using rejects_trace_simulation by blast

lemma simulates_trace_subset: "trace_simulates e1 e2 \<Longrightarrow> T e1 \<subseteq> T e2"
  using T_def accepts_trace_simulation trace_simulates_def by fastforce

subsubsection\<open>Trace Equivalence\<close>
text\<open>Two EFSMs are trace equivalent if they accept the same traces. This is the intuitive definition
of ``observable equivalence'' between the behaviours of the two models. If two EFSMs are trace
equivalent, there is no trace which can distinguish the two.\<close>

text_raw\<open>\snip{traceEquiv}{1}{2}{%\<close>
definition "trace_equivalent e1 e2 = (T e1 = T e2)"
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{simEquiv}{1}{2}{%\<close>
lemma simulation_implies_trace_equivalent:
  "trace_simulates e1 e2 \<Longrightarrow> trace_simulates e2 e1 \<Longrightarrow> trace_equivalent e1 e2"
text_raw\<open>}%endsnip\<close>
  using simulates_trace_subset trace_equivalent_def by auto

lemma trace_equivalent_reflexive: "trace_equivalent e1 e1"
  by (simp add: trace_equivalent_def)

lemma trace_equivalent_symmetric:
  "trace_equivalent e1 e2 = trace_equivalent e2 e1"
  using trace_equivalent_def by auto

lemma trace_equivalent_transitive:
  "trace_equivalent e1 e2 \<Longrightarrow>
   trace_equivalent e2 e3 \<Longrightarrow>
   trace_equivalent e1 e3"
  by (simp add: trace_equivalent_def)

text\<open>Two EFSMs are trace equivalent if they accept the same traces.\<close>
lemma trace_equivalent:
  "\<forall>t. accepts_trace e1 0 <> t = accepts_trace e2 0 <> t \<Longrightarrow> trace_equivalent e1 e2"
  by (simp add: T_def trace_equivalent_def)

lemma accepts_trace_step_2: "(s2', t2) |\<in>| possible_steps e2 s2 r2 l i \<Longrightarrow>
       accepts_trace e2 s2' (evaluate_updates t2 i r2) t \<Longrightarrow>
       evaluate_outputs t2 i r2 = map Some p \<Longrightarrow>
       accepts_trace e2 s2 r2 ((l, i, p)#t)"
  by (rule accepts_trace.step, auto)

subsubsection\<open>Execution Simulation\<close>
text\<open>Execution simulation is similar to trace simulation but for executions rather than traces.
Execution simulation has no notion of ``expected'' output. It simply requires that the simulating
EFSM must be able to produce equivalent output for each action.\<close>

text_raw\<open>\snip{execSim}{1}{2}{%\<close>
inductive execution_simulation :: "(cfstate \<Rightarrow> cfstate) \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow>
registers \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base: "s2 = f s1 \<Longrightarrow> execution_simulation f e1 s1 r1 e2 s2 r2 []" |
  step: "s2 = f s1 \<Longrightarrow>
         \<forall>(s1', t1) |\<in>| (possible_steps e1 s1 r1 l i).
           \<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i.
            evaluate_outputs t1 i r1 = evaluate_outputs t2 i r2 \<and>
            execution_simulation f e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es \<Longrightarrow>
         execution_simulation f e1 s1 r1 e2 s2 r2 ((l, i)#es)"
text_raw\<open>}%endsnip\<close>

definition "execution_simulates e1 e2 = (\<exists>f. \<forall>t. execution_simulation f e1 0 <> e2 0 <> t)"

lemma execution_simulation_step:
"execution_simulation f e1 s1 r1 e2 s2 r2 ((l, i)#es) =
 (s2 = f s1 \<and>
 (\<forall>(s1', t1) |\<in>| (possible_steps e1 s1 r1 l i).
         (\<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i. evaluate_outputs t1 i r1 = evaluate_outputs t2 i r2 \<and>
         execution_simulation f e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es))
)"
  apply standard
   apply (rule execution_simulation.cases)
     apply simp
    apply simp
   apply simp
  apply (rule execution_simulation.step)
   apply simp
  by blast

text_raw\<open>\snip{execTraceSim}{1}{2}{%\<close>
lemma execution_simulation_trace_simulation:
  "execution_simulation f e1 s1 r1 e2 s2 r2 (map (\<lambda>(l, i, o). (l, i)) t) \<Longrightarrow>
   trace_simulation f e1 s1 r1 e2 s2 r2 t"
text_raw\<open>}%endsnip\<close>
proof(induct t arbitrary: s1 s2 r1 r2)
case Nil
  then show ?case
    apply (rule execution_simulation.cases)
     apply (simp add: trace_simulation.base)
    by simp
next
  case (Cons a t)
  then show ?case
    apply (cases a, clarsimp)
    apply (rule execution_simulation.cases)
      apply simp
     apply simp
    apply (rule trace_simulation.step)
     apply simp
    apply clarsimp
    subgoal for _ _ _ aa ba
      apply (erule_tac x="(aa, ba)" in fBallE)
       apply clarsimp
       apply blast
      by simp
    done
qed

lemma execution_simulates_trace_simulates:
  "execution_simulates e1 e2 \<Longrightarrow> trace_simulates e1 e2"
  apply (simp add: execution_simulates_def trace_simulates_def)
  using execution_simulation_trace_simulation by blast

subsubsection\<open>Executional Equivalence\<close>
text\<open>Two EFSMs are executionally equivalent if there is no execution which can distinguish between
the two. That is, for every execution, they must produce equivalent outputs.\<close>

text_raw\<open>\snip{execEquiv}{1}{2}{%\<close>
inductive executionally_equivalent :: "transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow>
transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base [simp]: "executionally_equivalent e1 s1 r1 e2 s2 r2 []" |
  step: "\<forall>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i.
           \<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i.
             evaluate_outputs t1 i r1 = evaluate_outputs t2 i r2 \<and>
             executionally_equivalent e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es \<Longrightarrow>
         \<forall>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i.
           \<exists>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i.
             evaluate_outputs t1 i r1 = evaluate_outputs t2 i r2 \<and>
             executionally_equivalent e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es \<Longrightarrow>
         executionally_equivalent e1 s1 r1 e2 s2 r2 ((l, i)#es)"
text_raw\<open>}%endsnip\<close>

lemma executionally_equivalent_step:
"executionally_equivalent e1 s1 r1 e2 s2 r2 ((l, i)#es) = (
  (\<forall>(s1', t1) |\<in>| (possible_steps e1 s1 r1 l i). (\<exists>(s2', t2) |\<in>| possible_steps e2 s2 r2 l i. evaluate_outputs t1 i r1 = evaluate_outputs t2 i r2 \<and>
   executionally_equivalent e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es)) \<and>
  (\<forall>(s2', t2) |\<in>| (possible_steps e2 s2 r2 l i). (\<exists>(s1', t1) |\<in>| possible_steps e1 s1 r1 l i. evaluate_outputs t1 i r1 = evaluate_outputs t2 i r2 \<and>
   executionally_equivalent e1 s1' (evaluate_updates t1 i r1) e2 s2' (evaluate_updates t2 i r2) es)))"
  apply standard
   apply (rule executionally_equivalent.cases)
     apply simp
    apply simp
   apply simp
  by (rule executionally_equivalent.step, auto)

lemma execution_end:
  "possible_steps e1 s1 r1 l i = {||} \<Longrightarrow>
   possible_steps e2 s2 r2 l i = {||} \<Longrightarrow>
  executionally_equivalent e1 s1 r1 e2 s2 r2 ((l, i)#es)"
  by (simp add: executionally_equivalent_step)

lemma possible_steps_disparity:
  "possible_steps e1 s1 r1 l i \<noteq> {||} \<Longrightarrow>
   possible_steps e2 s2 r2 l i = {||} \<Longrightarrow>
   \<not>executionally_equivalent e1 s1 r1 e2 s2 r2 ((l, i)#es)"
  by (simp add: executionally_equivalent_step, auto)

lemma executionally_equivalent_acceptance_map:
  "executionally_equivalent e1 s1 r1 e2 s2 r2 (map (\<lambda>(l, i, o). (l, i)) t) \<Longrightarrow>
   accepts_trace e2 s2 r2 t = accepts_trace e1 s1 r1 t"
proof(induct t arbitrary: s1 s2 r1 r2)
  case (Cons a t)
  then show ?case
    apply (cases a, simp)
    apply (rule executionally_equivalent.cases)
      apply simp
     apply simp
    apply clarsimp
    apply standard
    subgoal for i p l
      apply (rule accepts_trace.cases)
        apply simp
       apply simp
      apply clarsimp
      subgoal for aa b
        apply (rule accepts_trace.step)
        apply (erule_tac x="(aa, b)" in fBallE[of "possible_steps e2 s2 r2 l i"])
         defer apply simp
        apply simp
        by blast
      done
    apply (rule accepts_trace.cases)
      apply simp
     apply simp
    apply clarsimp
    subgoal for _ _ _ aa b
      apply (rule accepts_trace.step)
      apply (erule_tac x="(aa, b)" in fBallE)
       defer apply simp
      apply simp
      by fastforce
    done
qed auto

lemma executionally_equivalent_acceptance:
  "\<forall>x. executionally_equivalent e1 s1 r1 e2 s2 r2 x \<Longrightarrow> accepts_trace e1 s1 r1  t \<Longrightarrow> accepts_trace e2 s2 r2 t"
  using executionally_equivalent_acceptance_map by blast

lemma executionally_equivalent_trace_equivalent:
  "\<forall>x. executionally_equivalent e1 0 <> e2 0 <> x \<Longrightarrow> trace_equivalent e1 e2"
  apply (rule trace_equivalent)
  apply clarify
  subgoal for t apply (erule_tac x="map (\<lambda>(l, i, o). (l, i)) t" in allE)
    by (simp add: executionally_equivalent_acceptance_map)
  done

lemma executionally_equivalent_symmetry:
  "executionally_equivalent e1 s1 r1 e2 s2 r2 x \<Longrightarrow>
   executionally_equivalent e2 s2 r2 e1 s1 r1 x"
proof(induct x arbitrary: s1 s2 r1 r2)
  case (Cons a x)
  then show ?case
    apply (cases a, clarsimp)
    apply (simp add: executionally_equivalent_step)
    apply standard
     apply (rule fBallI)
     apply clarsimp
    subgoal for aa b aaa ba
      apply (erule_tac x="(aaa, ba)" in fBallE[of "possible_steps e2 s2 r2 aa b"])
      by (force, simp)
    apply (rule fBallI)
    apply clarsimp
    subgoal for aa b aaa ba
      apply (erule_tac x="(aaa, ba)" in fBallE)
      by (force, simp)
    done
qed auto

lemma executionally_equivalent_transitivity:
  "executionally_equivalent e1 s1 r1 e2 s2 r2 x \<Longrightarrow>
   executionally_equivalent e2 s2 r2 e3 s3 r3 x \<Longrightarrow>
   executionally_equivalent e1 s1 r1 e3 s3 r3 x"
proof(induct x arbitrary: s1 s2 s3 r1 r2 r3)
  case (Cons a x)
  then show ?case
    apply (cases a, clarsimp)
    apply (simp add: executionally_equivalent_step)
    apply clarsimp
    apply standard
     apply (rule fBallI)
     apply clarsimp
    subgoal for aa b ab ba
      apply (erule_tac x="(ab, ba)" in fBallE[of "possible_steps e1 s1 r1 aa b"])
       prefer 2 apply simp
      apply simp
      apply (erule fBexE)
      subgoal for x apply (case_tac x)
        apply simp
        by blast
      done
    apply (rule fBallI)
    apply clarsimp
    subgoal for aa b ab ba
      apply (erule_tac x="(ab, ba)" in fBallE[of "possible_steps e3 s3 r3 aa b"])
       prefer 2 apply simp
      apply simp
      apply (erule fBexE)
      subgoal for x apply (case_tac x)
        apply clarsimp
        subgoal for aaa baa
          apply (erule_tac x="(aaa, baa)" in fBallE[of "possible_steps e2 s2 r2 aa b"])
           prefer 2 apply simp
          apply simp
          by blast
        done
      done
    done
qed auto

subsection\<open>Reachability\<close>
text\<open>Here, we define the function \texttt{visits} which returns true if the given execution
leaves the given EFSM in the given state.\<close>

text_raw\<open>\snip{reachable}{1}{2}{%\<close>
inductive visits :: "cfstate \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base [simp]: "visits s e s r []" |
  step: "\<exists>(s', T) |\<in>| possible_steps e s r l i. visits target e s' (evaluate_updates T i r) t \<Longrightarrow>
         visits target e s r ((l, i)#t)"

definition "reachable s e = (\<exists>t. visits s e 0 <> t)"
text_raw\<open>}%endsnip\<close>

lemma no_further_steps:
  "s \<noteq> s' \<Longrightarrow> \<not> visits s e s' r []"
  apply safe
  apply (rule visits.cases)
  by auto

lemma visits_base: "visits target e s r [] = (s = target)"
  by (metis visits.base no_further_steps)

lemma visits_step:
  "visits target e s r (h#t) = (\<exists>(s', T) |\<in>| possible_steps e s r (fst h) (snd h). visits target e s' (evaluate_updates T (snd h) r) t)"
  apply standard
   apply (rule visits.cases)
     apply simp+
  apply (cases h)
  using visits.step by auto

lemma reachable_initial: "reachable 0 e"
  apply (simp add: reachable_def)
  apply (rule_tac x="[]" in exI)
  by simp

lemma visits_finsert:
  "visits s e s' r t \<Longrightarrow> visits s (finsert ((aa, ba), b) e) s' r t"
proof(induct t arbitrary: s' r)
  case Nil
  then show ?case
    by (simp add: visits_base)
next
  case (Cons a t)
  then show ?case
    apply (simp add: visits_step)
    apply (erule fBexE)
    apply (rule_tac x=x in fBexI)
     apply auto[1]
    by (simp add: possible_steps_finsert)
qed

lemma reachable_finsert:
  "reachable s e \<Longrightarrow> reachable s (finsert ((aa, ba), b) e)"
  apply (simp add: reachable_def)
  by (meson visits_finsert)

lemma reachable_finsert_contra:
  "\<not> reachable s (finsert ((aa, ba), b) e) \<Longrightarrow> \<not>reachable s e"
  using reachable_finsert by blast

lemma visits_empty: "visits s e s' r [] = (s = s')"
  apply standard
  by (rule visits.cases, auto)

definition "remove_state s e = ffilter (\<lambda>((from, to), t). from \<noteq> s \<and> to \<noteq> s) e"

text_raw\<open>\snip{obtainable}{1}{2}{%\<close>
inductive "obtains" :: "cfstate \<Rightarrow> registers \<Rightarrow> transition_matrix \<Rightarrow> cfstate \<Rightarrow> registers \<Rightarrow> execution \<Rightarrow> bool" where
  base [simp]: "obtains s r e s r []" |
  step: "\<exists>(s'', T) |\<in>| possible_steps e s' r' l i. obtains s r e s'' (evaluate_updates T i r') t \<Longrightarrow>
         obtains s r e s' r' ((l, i)#t)"

definition "obtainable s r e = (\<exists>t. obtains s r e 0 <> t)"
text_raw\<open>}%endsnip\<close>

lemma obtains_obtainable:
  "obtains s r e 0 <> t \<Longrightarrow> obtainable s r e"
  apply (simp add: obtainable_def)
  by auto

lemma obtains_base: "obtains s r e s' r' [] = (s = s' \<and> r = r')"
  apply standard
  by (rule obtains.cases, auto)

lemma obtains_step: "obtains s r e s' r' ((l, i)#t) = (\<exists>(s'', T) |\<in>| possible_steps e s' r' l i. obtains s r e s'' (evaluate_updates T i r') t)"
  apply standard
  by (rule obtains.cases, auto simp add: obtains.step)

lemma obtains_recognises:
  "obtains s c e s' r t \<Longrightarrow> recognises_execution e s' r t"
proof(induct t arbitrary: s' r)
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply simp
    apply (rule obtains.cases)
      apply simp
     apply simp
    apply clarsimp
    using recognises_execution.step by fastforce
qed

lemma ex_comm4:
  "(\<exists>c1 s a b. (a, b) \<in> fset (possible_steps e s' r l i) \<and> obtains s c1 e a (evaluate_updates b i r) t) =
   (\<exists>a b s c1. (a, b) \<in> fset (possible_steps e s' r l i) \<and> obtains s c1 e a (evaluate_updates b i r) t)"
  by auto

lemma recognises_execution_obtains:
  "recognises_execution e s' r t \<Longrightarrow> \<exists>c1 s. obtains s c1 e s' r t"
proof(induct t arbitrary: s' r)
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (simp add: obtains_step)
    apply (rule recognises_execution.cases)
      apply simp
     apply simp
    apply clarsimp
    apply (simp add: fBex_def Bex_def ex_comm4)
    subgoal for _ _ aa ba
      apply (rule_tac x=aa in exI)
      apply (rule_tac x=ba in exI)
      apply (simp add: fmember_implies_member)
      by blast
    done  
qed

lemma obtainable_empty_efsm:
  "obtainable s c {||} = (s=0 \<and> c = <>)"
  apply (simp add: obtainable_def)
  apply standard
  apply (metis ffilter_empty no_outgoing_transitions no_step_none obtains.cases obtains_recognises step_None)
  using obtains_base by blast

lemma obtains_visits: "obtains s r e s' r' t \<Longrightarrow> visits s e s' r' t"
proof(induct t arbitrary: s' r')
  case Nil
  then show ?case
    by (simp add: obtains_base)
next
  case (Cons a t)
  then show ?case
    apply (cases a)
    apply (rule obtains.cases)
      apply simp
     apply simp
    apply clarsimp
    apply (rule visits.step)
    by auto
qed

lemma unobtainable_if: "\<not> visits s e s' r' t \<Longrightarrow> \<not> obtains s r e s' r' t"
  using obtains_visits by blast

lemma obtainable_if_unreachable: "\<not>reachable s e \<Longrightarrow> \<not>obtainable s r e"
  by (simp add: reachable_def obtainable_def unobtainable_if)

lemma obtains_step_append:
  "obtains s r e s' r' t \<Longrightarrow>
  (s'', ta) |\<in>| possible_steps e s r l i \<Longrightarrow>
  obtains s'' (evaluate_updates ta i r) e s' r' (t @ [(l, i)])"
proof(induct t arbitrary: s' r')
  case Nil
  then show ?case
    apply (simp add: obtains_base)
    apply (rule obtains.step)
    apply (rule_tac x="(s'', ta)" in fBexI)
    by auto
next
  case (Cons a t)
  then show ?case
    apply simp
    apply (rule obtains.cases)
      apply simp
     apply simp
    apply clarsimp
    apply (rule obtains.step)
    by auto
qed

lemma reachable_if_obtainable_step:
  "obtainable s r e \<Longrightarrow> \<exists>l i t. (s', t) |\<in>| possible_steps e s r l i \<Longrightarrow> reachable s' e"
  apply (simp add: reachable_def obtainable_def)
  apply clarify
  subgoal for t l i
    apply (rule_tac x="t@[(l, i)]" in exI)
    using obtains_step_append unobtainable_if by blast
  done

lemma possible_steps_remove_unreachable:
  "obtainable s r e \<Longrightarrow>
  \<not> reachable s' e \<Longrightarrow>
  possible_steps (remove_state s' e) s r l i = possible_steps e s r l i"
  apply standard
  apply (simp add: fsubset_eq)
   apply (rule fBallI)
   apply clarsimp
   apply (metis ffmember_filter in_possible_steps remove_state_def)
  apply (simp add: fsubset_eq)
   apply (rule fBallI)
  apply clarsimp
  subgoal for a b
    apply (case_tac "a = s'")
    using reachable_if_obtainable_step apply blast
    apply (simp add: remove_state_def)
    by (metis (mono_tags, lifting) ffmember_filter in_possible_steps obtainable_if_unreachable old.prod.case)
  done

text_raw\<open>\snip{removeUnreachableArb}{1}{2}{%\<close>
lemma executionally_equivalent_remove_unreachable_state_arbitrary:
  "obtainable s r e \<Longrightarrow> \<not> reachable s' e \<Longrightarrow> executionally_equivalent e s r (remove_state s' e) s r x"
text_raw\<open>}%endsnip\<close>
proof(induct x arbitrary: s r)
  case (Cons a x)
  then show ?case
    apply (cases a, simp)
    apply (rule executionally_equivalent.step)
    apply (simp add: possible_steps_remove_unreachable)
    apply standard
     apply clarsimp
    subgoal for aa b ab ba
      apply (rule_tac x="(ab, ba)" in fBexI)
       apply (metis (mono_tags, lifting) obtainable_def obtains_step_append case_prodI)
      apply simp
      done
    apply (rule fBallI)
    apply clarsimp
    apply (rule_tac x="(ab, ba)" in fBexI)
     apply simp
     apply (metis obtainable_def obtains_step_append possible_steps_remove_unreachable)
    by (simp add: possible_steps_remove_unreachable)
qed auto

text_raw\<open>\snip{removeUnreachable}{1}{2}{%\<close>
lemma executionally_equivalent_remove_unreachable_state:
  "\<not> reachable s' e \<Longrightarrow> executionally_equivalent e 0 <> (remove_state s' e) 0 <> x"
text_raw\<open>}%endsnip\<close>
  by (meson executionally_equivalent_remove_unreachable_state_arbitrary
      obtains.simps obtains_obtainable)

subsection\<open>Transition Replacement\<close>
text\<open>Here, we define the function \texttt{replace} to replace one transition with another, and prove
some of its properties.\<close>

definition "replace e1 old new = fimage (\<lambda>x. if x = old then new else x) e1"

lemma replace_finsert:
  "replace (finsert ((aaa, baa), b) e1) old new = (if ((aaa, baa), b) = old then (finsert new (replace e1 old new)) else (finsert ((aaa, baa), b) (replace e1 old new)))"
  by (simp add: replace_def)

lemma possible_steps_replace_unchanged:
  "((s, aa), ba) \<noteq> ((s1, s2), t1) \<Longrightarrow>
  (aa, ba) |\<in>| possible_steps e1 s r l i \<Longrightarrow>
  (aa, ba) |\<in>| possible_steps (replace e1 ((s1, s2), t1) ((s1, s2), t2)) s r l i"
  apply (simp add: in_possible_steps[symmetric] replace_def)
  by fastforce

end
