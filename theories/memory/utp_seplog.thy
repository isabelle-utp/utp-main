section \<open> Separation Logic \<close>

theory utp_seplog
  imports utp_memory
begin

subsection \<open> Operators \<close>

type_synonym 's spred = "'s mem upred"

definition empty_heap :: "'s spred" ("emp") where [upred_defs]: "emp = (dom\<^sub>u(&hp) =\<^sub>u {}\<^sub>u)"

definition sep_conj :: "'s spred \<Rightarrow> 's spred \<Rightarrow> 's spred" (infixr "\<^bold>*" 35) where
[upred_defs]: "(P \<^bold>* Q) = 
  (\<^bold>\<exists> (h\<^sub>0, h\<^sub>1) \<bullet> \<guillemotleft>fdom(h\<^sub>0) \<inter> fdom(h\<^sub>1) = {}\<guillemotright> \<and> &hp =\<^sub>u \<guillemotleft>h\<^sub>0 + h\<^sub>1\<guillemotright> \<and> P\<lbrakk>\<guillemotleft>h\<^sub>0\<guillemotright>/&hp\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>h\<^sub>1\<guillemotright>/&hp\<rbrakk>)"

definition sep_impl :: "'s spred \<Rightarrow> 's spred \<Rightarrow> 's spred" (infixr "-\<^bold>*" 25) where
[upred_defs]: "(P -\<^bold>* Q) = 
  (\<^bold>\<forall> h\<^sub>0 \<bullet> dom\<^sub>u(\<guillemotleft>h\<^sub>0\<guillemotright>) \<inter>\<^sub>u dom\<^sub>u(&hp) =\<^sub>u {}\<^sub>u \<and> P\<lbrakk>\<guillemotleft>h\<^sub>0\<guillemotright>/&hp\<rbrakk> \<Rightarrow> Q\<lbrakk>&hp + \<guillemotleft>h\<^sub>0\<guillemotright>/&hp\<rbrakk>)"

definition heaplet :: "(addr, 's) uexpr \<Rightarrow> ('a::countable, 's) uexpr \<Rightarrow> 's spred" (infix "\<^bold>\<mapsto>" 70) where
[upred_defs]: "v \<^bold>\<mapsto> e = (dom\<^sub>u(&hp) =\<^sub>u {v \<oplus>\<^sub>p st}\<^sub>u \<and> &hp(v \<oplus>\<^sub>p st)\<^sub>a =\<^sub>u uop to_nat (e \<oplus>\<^sub>p st))"

abbreviation heaplet_min :: "(addr, 's) uexpr \<Rightarrow> ('a::countable, 's) uexpr \<Rightarrow> 's spred" (infix "\<^bold>\<hookrightarrow>" 70) where
"v \<^bold>\<hookrightarrow> e \<equiv> v \<^bold>\<mapsto> e \<^bold>* true"

abbreviation heaplet_ex :: "(addr, 's) uexpr \<Rightarrow> 's spred" ("_ \<^bold>\<mapsto> -" [69] 70) where
"e \<^bold>\<mapsto> - \<equiv> (\<^bold>\<exists> v::nat \<bullet> e \<^bold>\<mapsto> \<guillemotleft>v\<guillemotright>)"

subsection \<open> Algebraic Properties \<close>

lemma sep_conj_comm: "(P \<^bold>* Q) = (Q \<^bold>* P)"
  using ffun_plus_commute by (rel_blast)

lemma sep_conj_assoc: "((P \<^bold>* Q) \<^bold>* R) = (P \<^bold>* (Q \<^bold>* R))"
  apply (rel_auto)
   apply (rename_tac st h0 h1 h2)
   apply (rule_tac x="h1" in exI)
   apply (rule_tac x="h0 + h2" in exI)
  apply (auto simp add: Int_Un_distrib2 add.assoc ffun_plus_commute)
   apply (rename_tac st h0 h1 h2)
  apply (rule_tac x="h0 + h1" in exI)
  apply (rule_tac x="h2" in exI)
  apply (auto simp add: Int_Un_distrib2 add.assoc ffun_plus_commute)
  done

lemma sep_conj_iso: "P \<sqsubseteq> Q \<Longrightarrow> (P \<^bold>* R) \<sqsubseteq> (Q \<^bold>* R)"
  by (rel_auto)

lemma sep_conj_unit: "(emp \<^bold>* P) = P"
  apply (rel_auto)
  apply (metis add.left_neutral bounded_semilattice_sup_bot_class.sup_bot.left_neutral ffun_minus_plus_commute ffun_minus_self ffun_minus_zero lattice_class.inf_sup_absorb)
  using fdom_zero by fastforce

subsection \<open> Locality \<close>

definition local_wrt :: "'s spred \<Rightarrow> 's sprog \<Rightarrow> bool" where
[upred_defs]: "local_wrt p S = (\<forall> q. (S wp\<^sub>D (p \<^bold>* q) \<sqsubseteq> (p \<^bold>* (S wp\<^sub>D q))))"

lemma local_wrt_seq_closed:
  assumes "C is \<^bold>N" "D is \<^bold>N" "local_wrt r C" "local_wrt r D"
  shows "local_wrt r (C ;; D)"
proof -
  obtain c\<^sub>1 C\<^sub>2 where C: "C = c\<^sub>1 \<turnstile>\<^sub>n C\<^sub>2"
    by (metis assms(1) ndesign_form)
  obtain d\<^sub>1 D\<^sub>2 where D: "D = d\<^sub>1 \<turnstile>\<^sub>n D\<^sub>2"
    by (metis assms(2) ndesign_form)
  with assms(3-4) show ?thesis
    apply (simp add: C D local_wrt_def wp)
    apply (auto)
    apply (metis wp_conj)
    apply (metis utp_pred_laws.inf.absorb_iff2 utp_pred_laws.le_infE wp_conj)
    apply (metis utp_pred_laws.inf.absorb_iff2 utp_pred_laws.inf_assoc wp_conj)
    done
qed

lemma local_wrt_heap_lookup: 
  "\<lbrakk> vwb_lens x; x \<sharp> e; st:x \<sharp> p \<rbrakk> \<Longrightarrow> local_wrt p (x := *e)"
  apply (rel_simp)
  apply (rename_tac q st hp0 hp1)
  apply (rule_tac x="hp0" in exI)
  apply (auto)
  done

subsection \<open> Separation Logic Laws \<close>

lemma frame_rule_aux:
  "\<lbrakk> c is \<^bold>N; local_wrt r c; {p} c {q}\<^sub>D \<rbrakk> \<Longrightarrow> {p \<^bold>* r} c {q \<^bold>* r}\<^sub>D"
  apply (simp add: wp_hoare_d_link)
  apply (simp add: local_wrt_def)
  apply (metis (no_types, lifting) dual_order.trans sep_conj_comm sep_conj_iso)
  done

lemma allocation_noninterfering_local:
  "{emp}v := alloc(e){&v \<^bold>\<mapsto> e}\<^sub>D"
  by (rel_auto)

lemma allocation_noninterfering_global:
  "\<lbrakk> vwb_lens x; st:x \<sharp> p \<rbrakk> \<Longrightarrow> {p}x := alloc(e){p \<^bold>* &x \<^bold>\<mapsto> e}\<^sub>D"
  apply (rel_simp)
  apply (rename_tac ok st hp ok' l)
  apply (rule_tac x="hp" in exI)
  apply (rule_tac x="0(l \<mapsto> to_nat (\<lbrakk>e\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> st l)))\<^sub>f" in exI)
  apply (auto)
  done

lemma mutation_local: "{e \<^bold>\<mapsto> -} *e := v {e \<^bold>\<mapsto> v}\<^sub>D"
  by (rel_auto)

lemma mutation_global: "{p \<^bold>* e \<^bold>\<mapsto> -} *e := v {p \<^bold>* e \<^bold>\<mapsto> v}\<^sub>D"
  apply (rel_simp)
  apply (rename_tac st ok' a b x)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="b(\<lbrakk>e\<rbrakk>\<^sub>e st \<mapsto> to_nat (\<lbrakk>v\<rbrakk>\<^sub>e st))\<^sub>f" in exI)
  apply (simp)
  done

lemma deallocation_local:
  "{e \<^bold>\<mapsto> -} dealloc(e) {emp}\<^sub>D"
  by (rel_auto)

lemma deallocation_global:
  "{r \<^bold>* e \<^bold>\<mapsto> -} dealloc(e) {r}\<^sub>D"
  apply (rel_simp)
  apply (rename_tac ok st ok' a b x)
  apply (subgoal_tac "fdom(a) \<lhd>\<^sub>f b = fdom(a) \<lhd>\<^sub>f (fdom(b) \<lhd>\<^sub>f b)")
   apply (simp)
  apply (fastforce)
  done

lemma lookup_global:
  "\<lbrakk> vwb_lens x; x \<sharp> e; x \<sharp> v; st:x \<sharp> r \<rbrakk> \<Longrightarrow> 
    {r \<^bold>* e \<^bold>\<mapsto> v} x := *e {r \<^bold>* (&st:x =\<^sub>u (v \<oplus>\<^sub>p st) \<and> e \<^bold>\<mapsto> v)}\<^sub>D"
  by (rel_simp, metis (full_types) Diff_Diff_Int Diff_insert0 Int_empty_right)
  
end