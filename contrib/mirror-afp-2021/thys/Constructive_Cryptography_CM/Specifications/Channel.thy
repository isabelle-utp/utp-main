theory Channel
  imports
    "../Fused_Resource"
begin

section \<open>Channel specification\<close>

locale ideal_channel =
  fixes 
  (*TODO: decide to either include or exlude this fixation,
    - if it is not included, then the types must be manually stated whenever channel locale is imported (c.f. OTP and DH)
    - also, the WT_intro rules for channel will have an unspecified valid_messages*)
  (*  valid_messages :: "'msg set" and*)
    leak :: "'msg \<Rightarrow> 'leak" and
    editable :: bool
begin


subsection \<open>Data-types for Parties, State, Events, Input, and Output\<close>

datatype party = Alice | Bob

type_synonym s_shell = "party set"
datatype 'msg' s_kernel =  State_Void | State_Store 'msg' | State_Collect 'msg' | State_Collected
type_synonym 'msg' state = "'msg' s_kernel \<times> s_shell"

datatype event = Event_Shell party

datatype iadv_drop = Inp_Drop
datatype iadv_look = Inp_Look
datatype 'msg' iadv_fedit = Inp_Fedit 'msg'
type_synonym 'msg' iadv = "iadv_drop + iadv_look + 'msg' iadv_fedit"

datatype 'msg' iusr_alice = Inp_Send 'msg'
datatype iusr_bob = Inp_Recv
type_synonym 'msg' iusr = "'msg' iusr_alice + iusr_bob"

datatype oadv_drop = Out_Drop
datatype 'leak' oadv_look = Out_Look 'leak'
datatype oadv_fedit = Out_Fedit
type_synonym 'leak' oadv = "oadv_drop + 'leak' oadv_look + oadv_fedit"

datatype ousr_alice = Out_Send
datatype 'msg' ousr_bob = Out_Recv 'msg'
type_synonym 'msg' ousr = "ousr_alice + 'msg' ousr_bob"


subsubsection \<open>Basic lemmas for automated handling of party sets (i.e. @{text s_shell})\<close>

lemma Alice_neq_iff [simp]: "Alice \<noteq> x \<longleftrightarrow> x = Bob"
  by(cases x) simp_all

lemma neq_Alice_iff [simp]: "x \<noteq> Alice \<longleftrightarrow> x = Bob"
  by(cases x) simp_all

lemma Bob_neq_iff [simp]: "Bob \<noteq> x \<longleftrightarrow> x = Alice"
  by(cases x) simp_all

lemma neq_Bob_iff [simp]: "x \<noteq> Bob \<longleftrightarrow> x = Alice"
  by(cases x) simp_all

lemma Alice_in_iff_nonempty: "Alice \<in> A \<longleftrightarrow> A \<noteq> {}" if "Bob \<notin> A"
  using that by(auto)(metis (full_types) party.exhaust)

lemma Bob_in_iff_nonempty: "Bob \<in> A \<longleftrightarrow> A \<noteq> {}" if "Alice \<notin> A"
  using that by(auto)(metis (full_types) party.exhaust)


subsection \<open>Defining the event handler\<close>

fun poke :: "('msg state, event) handler"
  where
    "poke (s_kernel, parties) (Event_Shell party) =
      (if party \<in> parties then 
        return_pmf None 
      else 
        return_spmf (s_kernel, insert party parties))"

lemma poke_alt_def:
  "poke = (\<lambda>(s, ps) e. map_spmf (Pair s) (case e of Event_Shell party \<Rightarrow> if party \<in> ps then return_pmf None else return_spmf (insert party ps)))"
  by(simp add: fun_eq_iff split: event.split)

subsection \<open>Defining the adversary interfaces\<close>

fun iface_drop :: "('msg state, iadv_drop, oadv_drop) oracle'"
  where
    "iface_drop _ _ = return_pmf None"

fun iface_look :: "('msg state, iadv_look, 'leak oadv_look) oracle'"
  where
    "iface_look (State_Store msg, parties) _ =
      return_spmf (Out_Look (leak msg), State_Store msg, parties)"
  | "iface_look _ _ = return_pmf None"

fun iface_fedit :: "('msg state, 'msg iadv_fedit, oadv_fedit) oracle'"
  where
    "iface_fedit (State_Store msg, parties) (Inp_Fedit msg') = 
      (if editable then
        return_spmf (Out_Fedit, State_Collect msg', parties)
      else
        return_spmf (Out_Fedit, State_Collect msg, parties))"
  | "iface_fedit _ _ = return_pmf None"

abbreviation iface_adv :: "('msg state, 'msg iadv, 'leak oadv) oracle'"
  where
    "iface_adv \<equiv> plus_oracle iface_drop (plus_oracle iface_look iface_fedit)"

lemma in_set_spmf_iface_drop: "ys' \<in> set_spmf (iface_drop s x) \<longleftrightarrow> False"
  by simp

lemma in_set_spmf_iface_look: "ys' \<in> set_spmf (iface_look s x) \<longleftrightarrow>
  (\<exists>msg parties. s = (State_Store msg, parties) \<and> ys' = (Out_Look (leak msg), State_Store msg, parties))"
  by(cases "(s, x)" rule: iface_look.cases) simp_all

lemma in_set_spmf_iface_fedit: "ys' \<in> set_spmf (iface_fedit s x) \<longleftrightarrow>
  (\<exists>msg parties msg'. s = (State_Store msg, parties) \<and> x = (Inp_Fedit msg') \<and>
      ys' = (if editable then (Out_Fedit, State_Collect msg', parties) else (Out_Fedit, State_Collect msg, parties)))"
  by(cases "(s, x)" rule: iface_fedit.cases) simp_all

subsection \<open>Defining the user interfaces\<close>

fun iface_alice :: "('msg state, 'msg iusr_alice, ousr_alice) oracle'"
  where
    "iface_alice (State_Void, parties) (Inp_Send msg) = 
      (if Alice \<in> parties then
        return_spmf (Out_Send, State_Store msg, parties)
      else
        return_pmf None)"
  | "iface_alice _ _ = return_pmf None"

fun iface_bob :: "('msg state, iusr_bob, 'msg ousr_bob) oracle'"
  where
    "iface_bob (State_Collect msg, parties) _ = 
      (if Bob \<in> parties then
        return_spmf (Out_Recv msg, State_Collected, parties)
      else
        return_pmf None)"
  | "iface_bob _ _ = return_pmf None"

abbreviation iface_usr :: "('msg state, 'msg iusr, 'msg ousr) oracle'"
  where
    "iface_usr \<equiv> plus_oracle iface_alice iface_bob"

lemma in_set_spmf_iface_alice: "ys' \<in> set_spmf (iface_alice s x) \<longleftrightarrow>
  (\<exists>parties msg. s = (State_Void, parties) \<and> x = Inp_Send msg \<and> Alice \<in> parties \<and> ys' = (Out_Send, State_Store msg, parties))"
  by(cases "(s, x)" rule: iface_alice.cases) simp_all

lemma in_set_spmf_iface_bob: "ys' \<in> set_spmf (iface_bob s x) \<longleftrightarrow>
  (\<exists>msg parties. s = (State_Collect msg, parties) \<and> Bob \<in> parties \<and> ys' = (Out_Recv msg, State_Collected, parties))"
  by(cases "(s, x)" rule: iface_bob.cases) simp_all

subsection \<open>Defining the Fused Resource\<close>

primcorec core :: "('msg state, event, 'msg iadv, 'msg iusr, 'leak oadv, 'msg ousr) core" 
  where
    "cpoke core = poke"
  | "cfunc_adv core = iface_adv"
  | "cfunc_usr core = iface_usr"

sublocale fused_resource core "(State_Void, {})" .


subsubsection \<open>Lemma showing that the resulting resource is well-typed\<close>

lemma WT_core [WT_intro]:
  "WT_core (\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (Inp_Fedit ` valid_messages) UNIV)) (\<I>_uniform (Inp_Send ` valid_messages) UNIV \<oplus>\<^sub>\<I> (\<I>_uniform UNIV (Out_Recv ` valid_messages)))
     (pred_prod (pred_s_kernel (\<lambda>msg. msg \<in> valid_messages)) (\<lambda>_. True)) core"
  apply(rule WT_core.intros)
  subgoal for s e s' by(cases "(s, e)" rule: poke.cases)(auto split: if_split_asm)
  subgoal for s x y s' by(cases "(s, projl (projr x))" rule: iface_look.cases)(auto split: if_split_asm)
  subgoal for s x y s' by(cases "(s, projl x)" rule: iface_alice.cases)(auto split: if_split_asm)
  done

lemma WT_fuse [WT_intro]: 
  assumes [WT_intro]: "WT_rest \<I>_adv_rest \<I>_usr_rest I_rest rest"
    shows  "((\<I>_full \<oplus>\<^sub>\<I> (\<I>_full \<oplus>\<^sub>\<I> \<I>_uniform (Inp_Fedit ` valid_messages) UNIV)) \<oplus>\<^sub>\<I> \<I>_adv_rest) \<oplus>\<^sub>\<I> 
      ((\<I>_uniform (Inp_Send ` valid_messages) UNIV \<oplus>\<^sub>\<I> \<I>_uniform UNIV (Out_Recv ` valid_messages)) \<oplus>\<^sub>\<I> \<I>_usr_rest) \<turnstile>res resource rest \<surd>"
  by(rule WT_intro)+ simp


end

end
