chapter\<open>Models\<close>
text\<open>In this chapter, we present our formalisation of EFSMs from \cite{foster2018}. We first
define transitions, before defining EFSMs as finite sets of transitions between states. Finally,
we provide a framework of function definitions and key lemmas such that LTL properties over EFSMs
can be more easily specified and proven.\<close>

section\<open>Transitions\<close>
text\<open>Here we define the transitions which make up EFSMs. As per \cite{foster2018}, each transition
has a label and an arity and, optionally, guards, outputs, and updates. To implement this, we use
the record type such that each component of the transition can be accessed.\<close>

theory Transition
imports GExp
begin

type_synonym label = String.literal
type_synonym arity = nat
type_synonym guard = "vname gexp"
type_synonym inputs = "value list"
type_synonym outputs = "value option list"
type_synonym output_function = "vname aexp"
type_synonym update_function = "nat \<times> vname aexp"

text_raw\<open>\snip{transitiontype}{1}{2}{%\<close>
record transition =
  Label :: String.literal
  Arity :: nat
  Guards :: "guard list"
  Outputs :: "output_function list"
  Updates :: "update_function list"
text_raw\<open>}%endsnip\<close>

definition same_structure :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "same_structure t1 t2 = (
    Label t1 = Label t2 \<and>
    Arity t1 = Arity t2 \<and>
    length (Outputs t1) = length (Outputs t2)
  )"

definition enumerate_inputs :: "transition \<Rightarrow> nat set" where
  "enumerate_inputs t = (\<Union> (set (map enumerate_gexp_inputs (Guards t)))) \<union>
                        (\<Union> (set (map enumerate_aexp_inputs (Outputs t)))) \<union>
                        (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_inputs u) (Updates t))))"

definition max_input :: "transition \<Rightarrow> nat option" where
  "max_input t = (if enumerate_inputs t = {} then None else Some (Max (enumerate_inputs t)))"

definition total_max_input :: "transition \<Rightarrow> nat" where
  "total_max_input t = (case max_input t of None \<Rightarrow> 0 | Some a \<Rightarrow> a)"

definition enumerate_regs :: "transition \<Rightarrow> nat set" where
  "enumerate_regs t = (\<Union> (set (map GExp.enumerate_regs (Guards t)))) \<union>
                      (\<Union> (set (map AExp.enumerate_regs (Outputs t)))) \<union>
                      (\<Union> (set (map (\<lambda>(_, u). AExp.enumerate_regs u) (Updates t)))) \<union>
                      (\<Union> (set (map (\<lambda>(r, _). AExp.enumerate_regs (V (R r))) (Updates t))))"

definition max_reg :: "transition \<Rightarrow> nat option" where
  "max_reg t = (if enumerate_regs t = {} then None else Some (Max (enumerate_regs t)))"

definition total_max_reg :: "transition \<Rightarrow> nat" where
  "total_max_reg t = (case max_reg t of None \<Rightarrow> 0 | Some a \<Rightarrow> a)"

definition enumerate_ints :: "transition \<Rightarrow> int set" where
  "enumerate_ints t = (\<Union> (set (map enumerate_gexp_ints (Guards t)))) \<union>
                      (\<Union> (set (map enumerate_aexp_ints (Outputs t)))) \<union>
                      (\<Union> (set (map (\<lambda>(_, u). enumerate_aexp_ints u) (Updates t)))) \<union>
                      (\<Union> (set (map (\<lambda>(r, _). enumerate_aexp_ints (V (R r))) (Updates t))))"

definition valid_transition :: "transition \<Rightarrow> bool" where
  "valid_transition t = (\<forall>i \<in> enumerate_inputs t. i < Arity t)"

definition can_take :: "nat \<Rightarrow> vname gexp list \<Rightarrow> inputs \<Rightarrow> registers \<Rightarrow> bool" where
  "can_take a g i r = (length i = a \<and> apply_guards g (join_ir i r))"

lemma can_take_empty [simp]: "length i = a \<Longrightarrow> can_take a [] i c"
  by (simp add: can_take_def)

lemma can_take_subset_append:
  assumes "set (Guards t) \<subseteq> set (Guards t')"
  shows "can_take a (Guards t @ Guards t') i c = can_take a (Guards t') i c"
  using assms
  by (simp add: apply_guards_subset_append can_take_def)

definition "can_take_transition t i r = can_take (Arity t) (Guards t) i r"

lemmas can_take = can_take_def can_take_transition_def

lemma can_take_transition_empty_guard:
  "Guards t = [] \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def Ex_list_of_length)

lemma can_take_subset: "length i = Arity t \<Longrightarrow>
   Arity t = Arity t' \<Longrightarrow>
   set (Guards t') \<subseteq> set (Guards t) \<Longrightarrow>
   can_take_transition t i r \<Longrightarrow>
   can_take_transition t' i r"
  by (simp add: can_take_transition_def can_take_def apply_guards_subset)

lemma valid_list_can_take:
  "\<forall>g \<in> set (Guards t). valid g \<Longrightarrow> \<exists>i. can_take_transition t i c"
  by (simp add: can_take_transition_def can_take_def apply_guards_def valid_def Ex_list_of_length)

lemma cant_take_if:
  "\<exists>g \<in> set (Guards t). gval g (join_ir i r) \<noteq> true \<Longrightarrow>
   \<not> can_take_transition t i r"
  using apply_guards_cons apply_guards_rearrange can_take_def can_take_transition_def by blast

definition apply_outputs :: "'a aexp list \<Rightarrow> 'a datastate \<Rightarrow> value option list" where
  "apply_outputs p s = map (\<lambda>p. aval p s) p"

abbreviation "evaluate_outputs t i r \<equiv> apply_outputs (Outputs t) (join_ir i r)"

lemma apply_outputs_nth:
  "i < length p \<Longrightarrow> apply_outputs p s ! i = aval (p ! i) s"
  by (simp add: apply_outputs_def)

lemmas apply_outputs = datastate apply_outputs_def value_plus_def value_minus_def value_times_def

lemma apply_outputs_empty [simp]: "apply_outputs [] s = []"
  by (simp add: apply_outputs_def)

lemma apply_outputs_preserves_length: "length (apply_outputs p s) = length p"
  by (simp add: apply_outputs_def)

lemma apply_outputs_literal: assumes "P ! r = L v"
      and "r < length P"
    shows "apply_outputs P s ! r = Some v"
  by (simp add: assms apply_outputs_nth)

lemma apply_outputs_register: assumes "r < length P"
  shows "apply_outputs (list_update P r (V (R p))) (join_ir i c) ! r = c $ p"
  by (metis apply_outputs_nth assms aval.simps(2) join_ir_R length_list_update nth_list_update_eq)

lemma apply_outputs_unupdated: assumes "ia \<noteq> r"
      and "ia < length P"
    shows "apply_outputs P j ! ia = apply_outputs (list_update P r v)j ! ia"
  by (metis apply_outputs_nth assms(1) assms(2) length_list_update nth_list_update_neq)

definition apply_updates :: "update_function list \<Rightarrow> vname datastate \<Rightarrow> registers \<Rightarrow> registers" where
  "apply_updates u old = fold (\<lambda>h r. r(fst h $:= aval (snd h) old)) u"

abbreviation "evaluate_updates t i r \<equiv> apply_updates (Updates t) (join_ir i r) r"

lemma apply_updates_cons: "ra \<noteq> r \<Longrightarrow>
       apply_updates u (join_ir ia c) c $ ra = apply_updates ((r, a) # u) (join_ir ia c) c $ ra"
proof(induct u rule: rev_induct)
  case Nil
  then show ?case
    by (simp add: apply_updates_def)
next
  case (snoc u us)
  then show ?case
    apply (cases u)
    apply (simp add: apply_updates_def)
    by (case_tac "ra = aa", auto)
qed

lemma update_twice:
  "apply_updates [(r, a), (r, b)] s regs = regs (r $:= aval b s)"
  by (simp add: apply_updates_def)

lemma r_not_updated_stays_the_same:
  "r \<notin> fst ` set U \<Longrightarrow> apply_updates U c d $ r = d $ r"
  using apply_updates_def
  by (induct U rule: rev_induct, auto)

definition rename_regs :: "(nat \<Rightarrow> nat) \<Rightarrow> transition \<Rightarrow> transition" where
  "rename_regs f t = t\<lparr>
      Guards  := map (GExp.rename_regs f) (Guards t),
      Outputs := map (AExp.rename_regs f) (Outputs t),
      Updates := map (\<lambda>(r, u). (f r, AExp.rename_regs f u)) (Updates t)
    \<rparr>"

definition eq_upto_rename_strong :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "eq_upto_rename_strong t1 t2 = (\<exists>f. bij f \<and> rename_regs f t1 = t2)"

inductive eq_upto_rename :: "transition \<Rightarrow> transition \<Rightarrow> bool" where
  "Label t1 = Label t2 \<Longrightarrow>
   Arity t2 = Arity t2 \<Longrightarrow>
   apply_guards (map (GExp.rename_regs f) (Guards t1)) = apply_guards (Guards t2) \<Longrightarrow>

   apply_outputs (map (AExp.rename_regs f) (Outputs t1)) = apply_outputs (Outputs t2) \<Longrightarrow>

   apply_updates (map (\<lambda>(r, u). (f r, AExp.rename_regs f u)) (Updates t1)) = apply_updates (Updates t2) \<Longrightarrow>

   eq_upto_rename t1 t2"

end
