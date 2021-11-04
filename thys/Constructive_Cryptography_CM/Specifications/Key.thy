theory Key
  imports
    "../Fused_Resource"
begin


section \<open>Key specification\<close>

locale ideal_key =
  fixes valid_keys :: "'key set"
begin

subsection \<open>Data-types for Parties, State, Events, Input, and Output\<close>

datatype party = Alice | Bob

type_synonym s_shell = "party set"
datatype 'key' s_kernel = PState_Store | State_Store 'key'
type_synonym 'key' state = "'key' s_kernel \<times> s_shell"

datatype event = Event_Shell party | Event_Kernel

datatype iadv = Inp_Adversary

datatype iusr_alice = Inp_Alice
datatype iusr_bob = Inp_Bob
type_synonym iusr = "iusr_alice + iusr_bob"

datatype oadv = Out_Adversary

datatype 'key' ousr_alice = Out_Alice 'key'
datatype 'key' ousr_bob = Out_Bob 'key'
type_synonym 'key' ousr = "'key' ousr_alice + 'key' ousr_bob"


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

fun poke :: "('key state, event) handler"
  where
    "poke (s_kernel, parties) (Event_Shell party) = 
      (if party \<in> parties then 
        return_pmf None
      else 
        return_spmf (s_kernel, insert party parties))"
  | "poke (PState_Store, s_shell) (Event_Kernel) = do {
      key \<leftarrow> spmf_of_set valid_keys;
      return_spmf (State_Store key, s_shell)  } "
  | "poke _ _ = return_pmf None"

lemma in_set_spmf_poke:
  "s' \<in> set_spmf (poke s x) \<longleftrightarrow>
  (\<exists>s_kernel parties party. s = (s_kernel, parties) \<and> x = Event_Shell party \<and> party \<notin> parties \<and> s' = (s_kernel, insert party parties)) \<or>
  (\<exists>s_shell key. s = (PState_Store, s_shell) \<and> x = Event_Kernel \<and> key \<in> valid_keys \<and> finite valid_keys \<and> s' = (State_Store key, s_shell))"
  by(cases "(s, x)" rule: poke.cases)(auto simp add: set_spmf_of_set)

lemma foldl_poke_invar:
  "\<lbrakk> (s_kernel', parties') \<in> set_spmf (foldl_spmf poke p events); \<forall>(s_kernel, parties)\<in>set_spmf p. set_s_kernel s_kernel \<subseteq> valid_keys \<rbrakk>
  \<Longrightarrow> set_s_kernel s_kernel' \<subseteq> valid_keys"
  by(induction events arbitrary: parties' rule: rev_induct)
    (auto 4 3 simp add: split_def foldl_spmf_append in_set_spmf_poke dest: bspec)

subsection \<open>Defining the adversary interface\<close>

fun iface_adv :: "('key state, iadv, oadv) oracle'"
  where
   "iface_adv state _ = return_spmf (Out_Adversary, state)"


subsection \<open>Defining the user interfaces\<close>

context
begin

private fun iface_usr_func :: "party \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'inp \<Rightarrow> ('wrap_key \<times> 'key state) spmf"
  where
    "iface_usr_func party wrap (State_Store key, parties) inp = 
      (if party \<in> parties then
        return_spmf (wrap key, State_Store key, parties)
      else
        return_pmf None)"
  | "iface_usr_func _ _ _ _ = return_pmf None"

abbreviation iface_alice :: "('key state, iusr_alice, 'key ousr_alice) oracle'"
  where
    "iface_alice \<equiv> iface_usr_func Alice Out_Alice"

abbreviation iface_bob :: "('key state, iusr_bob, 'key ousr_bob) oracle'"
  where
    "iface_bob \<equiv> iface_usr_func Bob Out_Bob"

abbreviation iface_usr :: "('key state, iusr, 'key ousr) oracle'"
  where
    "iface_usr \<equiv> plus_oracle iface_alice iface_bob"

lemma in_set_iface_usr_func [simp]:
  "x \<in> set_spmf (iface_usr_func party wrap state inp) \<longleftrightarrow>
   (\<exists>key parties. state = (State_Store key, parties) \<and> party \<in> parties \<and> x = (wrap key, State_Store key, parties))"
  by(cases "(party, wrap, state, inp)" rule: iface_usr_func.cases) auto

end


subsection \<open>Defining the Fuse Resource\<close>

primcorec core :: "('key state, event, iadv, iusr, oadv,'key ousr) core" 
  where
    "cpoke core = poke"
  | "cfunc_adv core = iface_adv"
  | "cfunc_usr core = iface_usr"

sublocale fused_resource core "(PState_Store, {})" .


subsubsection \<open>Lemma showing that the resulting resource is well-typed\<close>

lemma WT_core [WT_intro]: 
  "WT_core \<I>_full (\<I>_uniform UNIV (Out_Alice ` valid_keys) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (Out_Bob ` valid_keys))
     (pred_prod (pred_s_kernel (\<lambda>key. key \<in> valid_keys)) (\<lambda>_. True)) core"
  apply (rule WT_core.intros)
  subgoal for s e s' by(cases "(s, e)" rule: poke.cases)(auto split: if_split_asm simp add: set_spmf_of_set)
  by auto

lemma WT_fuse [WT_intro]: 
  assumes [WT_intro]: "WT_rest \<I>_adv_rest \<I>_usr_rest I_rest rest"
  shows "(\<I>_full \<oplus>\<^sub>\<I> \<I>_adv_rest) \<oplus>\<^sub>\<I> ((\<I>_uniform UNIV (Out_Alice ` valid_keys) \<oplus>\<^sub>\<I> \<I>_uniform UNIV (Out_Bob ` valid_keys)) \<oplus>\<^sub>\<I> \<I>_usr_rest) \<turnstile>res resource rest \<surd>"
  by(rule WT_intro)+ simp
 
end

end
