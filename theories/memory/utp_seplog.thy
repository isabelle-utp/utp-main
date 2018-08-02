section \<open> Separation Logic \<close>

theory utp_seplog
  imports utp_memory
begin

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

lemma sep_conj_comm: "(P \<^bold>* Q) = (Q \<^bold>* P)"
  using ffun_plus_commute by (rel_blast)

lemma sep_conj_assoc: "((P \<^bold>* Q) \<^bold>* R) = (P \<^bold>* (Q \<^bold>* R))"
  apply (rel_auto) oops

lemma sep_conj_unit: "(emp \<^bold>* P) = P"
  apply (rel_auto)
  apply (metis add.left_neutral bounded_semilattice_sup_bot_class.sup_bot.left_neutral ffun_minus_plus_commute ffun_minus_self ffun_minus_zero lattice_class.inf_sup_absorb)
  using fdom_zero by fastforce

lemma allocation_noninterfering_local:
  "\<lbrace>emp\<rbrace>v := alloc(e)\<lbrace>&v \<^bold>\<mapsto> e\<rbrace>\<^sub>u"
  by (rel_auto)

lemma allocation_noninterfering_global:
  "\<lbrakk> vwb_lens x; st:x \<sharp> p \<rbrakk> \<Longrightarrow> \<lbrace>p\<rbrace>x := alloc(e)\<lbrace>p \<^bold>* &x \<^bold>\<mapsto> e\<rbrace>\<^sub>u"
  apply (rel_simp)
  apply (rename_tac st hp l)
  apply (rule_tac x="hp" in exI)
  apply (rule_tac x="0(l \<mapsto> to_nat (\<lbrakk>e\<rbrakk>\<^sub>e (put\<^bsub>x\<^esub> st l)))\<^sub>f" in exI)
  apply (auto)
  done

lemma mutation_local: "\<lbrace>e \<^bold>\<mapsto> -\<rbrace> *e := v \<lbrace>e \<^bold>\<mapsto> v\<rbrace>\<^sub>u"
  by (rel_auto)

lemma mutation_global: "\<lbrace>p \<^bold>* e \<^bold>\<mapsto> -\<rbrace> *e := v \<lbrace>p \<^bold>* e \<^bold>\<mapsto> v\<rbrace>\<^sub>u"
  apply (rel_simp)
  apply (rename_tac st a b x)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="b(\<lbrakk>e\<rbrakk>\<^sub>e st \<mapsto> to_nat (\<lbrakk>v\<rbrakk>\<^sub>e st))\<^sub>f" in exI)
  apply (simp)
  done

lemma deallocation_local:
  "\<lbrace>e \<^bold>\<mapsto> -\<rbrace> dealloc(e) \<lbrace>emp\<rbrace>\<^sub>u"
  by (rel_auto)

lemma deallocation_global:
  "\<lbrace>r \<^bold>* e \<^bold>\<mapsto> -\<rbrace> dealloc(e) \<lbrace>r\<rbrace>\<^sub>u"
  apply (rel_simp)
  apply (rename_tac st a b x)
  apply (subgoal_tac "fdom(a) \<lhd>\<^sub>f b = fdom(a) \<lhd>\<^sub>f (fdom(b) \<lhd>\<^sub>f b)")
   apply (simp)
  apply (fastforce)
  done

lemma lookup_global:
  "\<lbrakk> vwb_lens x; x \<sharp> e; x \<sharp> v; st:x \<sharp> r \<rbrakk> \<Longrightarrow> 
    \<lbrace>r \<^bold>* e \<^bold>\<mapsto> v\<rbrace> x := *e \<lbrace>r \<^bold>* (&st:x =\<^sub>u (v \<oplus>\<^sub>p st) \<and> e \<^bold>\<mapsto> v)\<rbrace>\<^sub>u"
  by (rel_simp, metis (full_types) Diff_Diff_Int Diff_insert0 Int_empty_right)
  
lemma frame_rule:
  "vwb_lens x \<Longrightarrow> \<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>\<^sub>u \<Longrightarrow> \<lbrace>p \<^bold>* r\<rbrace> c \<lbrace>q \<^bold>* r\<rbrace>\<^sub>u"
  apply (rel_simp)
  oops

text \<open> Safety Monotonicity \<close>

definition safety_mono :: "'s sprog \<Rightarrow> bool" where
[upred_defs]: "safety_mono P = (\<forall> s\<^sub>0 s\<^sub>1. \<lbrakk>Dom(P)\<rbrakk>\<^sub>e s\<^sub>0 \<and> s\<^sub>0 \<le> s\<^sub>1 \<longrightarrow> \<lbrakk>Dom(P)\<rbrakk>\<^sub>e s\<^sub>1)"

lemma safety_mono_dealloc: "safety_mono (dealloc(e))"
  by (rel_simp, meson contra_subsetD fsubseteq_dom_subset)

lemma safety_mono_choice: "\<lbrakk> safety_mono P; safety_mono Q \<rbrakk> \<Longrightarrow> safety_mono (P \<sqinter> Q)"
  by (rel_blast)

end