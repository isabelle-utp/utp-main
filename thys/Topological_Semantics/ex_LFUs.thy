theory ex_LFUs
  imports topo_derivative_algebra sse_operation_negative
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Example application: Logics of Formal Undeterminedness (LFUs)\<close>
text\<open>\noindent{The LFUs @{cite LFU} @{cite LFI} are a family of paracomplete logics featuring a 'determinedness'
operator @{text "\<^bold>\<circ>"} that can be used to recover some classical properties of negation (in particular TND).
LFUs behave in a sense dually to LFIs. Both can be semantically embedded as extensions of Boolean algebras.
Here we show how to semantically embed LFUs as derivative algebras.}\<close>

text\<open>\noindent{(We rename (classical) meta-logical negation to avoid terminological confusion)}\<close>
abbreviation cneg::"bool\<Rightarrow>bool" ("\<sim>_" [40]40) where "\<sim>\<phi> \<equiv> \<not>\<phi>" 

text\<open>\noindent{Logical validity can be defined as truth in all worlds/points (i.e. as denoting the top element)}\<close>
abbreviation gtrue::"\<sigma>\<Rightarrow>bool" ("[\<^bold>\<turnstile> _]") where  "[\<^bold>\<turnstile>  A] \<equiv> \<forall>w. A w"   
lemma gtrue_def: "[\<^bold>\<turnstile> A] \<equiv> A \<^bold>\<approx> \<^bold>\<top>"  by (simp add: top_def)

text\<open>\noindent{As for LFIs, we focus on the local (truth-degree preserving) notion of logical consequence.}\<close>
abbreviation conseq_local1::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile> _]") where "[A \<^bold>\<turnstile> B] \<equiv> A \<^bold>\<preceq> B"
abbreviation conseq_local2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile> _]") where "[A\<^sub>1, A\<^sub>2 \<^bold>\<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<preceq> B"
abbreviation conseq_local12::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile> _,_]") where "[A \<^bold>\<turnstile> B\<^sub>1, B\<^sub>2] \<equiv> A \<^bold>\<preceq> B\<^sub>1 \<^bold>\<or> B\<^sub>2"
(*add more as the need arises...*)

text\<open>\noindent{For LFUs we use the interior-based negation previously defined (taking derivative as primitive). }\<close>
definition ineg::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>")  where  "\<^bold>\<not>A \<equiv> \<I>(\<^bold>\<midarrow>A)"
declare ineg_def[conn]

text\<open>\noindent{In terms of the derivative operator the negation looks as follows:}\<close>
lemma ineg_prop: "\<^bold>\<not>A \<^bold>\<approx> \<^bold>\<midarrow>(\<D> A) \<^bold>\<leftharpoonup> A" using Cl_der_def IB_rel Int_br_def eq_ext' pB4 conn by fastforce

text\<open>\noindent{This negation is of course paracomplete.}\<close>
lemma "[\<^bold>\<turnstile> a \<^bold>\<or> \<^bold>\<not>a]" nitpick oops (*countermodel*)

text\<open>\noindent{We define two pairs of in/determinedness operators and show how they relate to each other.}\<close>
abbreviation op_det::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>_" [57]58) where "\<^bold>\<circ>A  \<equiv> \<B>\<^sup>d A"
abbreviation op_ind::"\<sigma>\<Rightarrow>\<sigma>" ("\<bullet>_" [57]58) where "\<bullet>A  \<equiv> \<^bold>\<midarrow>\<^bold>\<circ>A"

lemma op_det_def: "\<^bold>\<circ>a \<^bold>\<approx> a \<^bold>\<or> \<^bold>\<not>a" by (simp add: compl_def diff_def dual_def ineg_def join_def pB1)
lemma Prop1: "\<^bold>\<circ>A \<^bold>\<approx> \<C>\<^sup>f\<^sup>p A" by (metis dimp_def eq_ext' fp3)
lemma Prop2: "Op A \<longleftrightarrow> \<^bold>\<circ>\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<top>" by (metis dual_def dual_symm pB1 pI1 top_def compl_def diff_def)
lemma Prop3: "Op A \<longleftrightarrow> \<bullet>\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<bottom>" by (metis Op_Bzero dual_def dual_symm)
lemma Prop4: "Cl A \<longleftrightarrow> \<^bold>\<circ>A \<^bold>\<approx> \<^bold>\<top>" by (metis Prop1 dimp_def top_def)
lemma Prop5: "Cl A \<longleftrightarrow> \<bullet>A \<^bold>\<approx> \<^bold>\<bottom>" by (simp add: Prop4 bottom_def compl_def top_def)

text\<open>\noindent{Analogously as for LFIs, LFUs provide means for recovering the principle of excluded middle.}\<close>
lemma "[\<Gamma> \<^bold>\<turnstile> \<bullet>a, a \<^bold>\<or> \<^bold>\<not>a]" using IB_rel Int_br_def compl_def diff_def dual_def eq_ext' ineg_def join_def by fastforce
lemma "[\<Gamma>, \<^bold>\<circ>a \<^bold>\<turnstile> a \<^bold>\<or> \<^bold>\<not>a]" using dual_def pB1 unfolding conn by auto

lemma "TNDm(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "ECQ(\<^bold>\<not>)" by (simp add: ECQ_def bottom_def diff_def ineg_prop meet_def)
lemma "Der_3 \<D> \<Longrightarrow> LNC(\<^bold>\<not>)" using ineg_prop ECQ_def ID3 LNC_def dNOR_def unfolding conn by auto
lemma "\<DD> \<D> \<Longrightarrow> DNI(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "\<DD> \<D> \<Longrightarrow> DNE(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "Der_1b \<D> \<Longrightarrow> CoPw(\<^bold>\<not>)" by (smt CoPw_def MONO_ADDIb PD1 compl_def ineg_def monI)
lemma "\<DD> \<D> \<Longrightarrow> CoP1(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "\<DD> \<D> \<Longrightarrow> CoP2(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "\<DD> \<D> \<Longrightarrow> CoP3(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "\<DD> \<D> \<Longrightarrow> DM3(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "Der_1a \<D> \<Longrightarrow> DM4(\<^bold>\<not>)" unfolding Defs using ADDI_a_def ineg_prop compl_def diff_def  join_def meet_def by auto
lemma "Der_3 \<D> \<Longrightarrow> nNor(\<^bold>\<not>)" by (simp add: NOR_def ineg_prop nNor_def bottom_def compl_def diff_def top_def)
lemma "nDNor(\<^bold>\<not>)" by (simp add: bottom_def diff_def ineg_prop nDNor_def top_def)
lemma "Der_1b \<D> \<Longrightarrow> MT0(\<^bold>\<not>)" unfolding Defs by (metis (mono_tags, hide_lams) CD1b Disj_I OpCldual PD1 bottom_def compl_def ineg_def meet_def top_def)
lemma "Der_1b \<D> \<Longrightarrow> Der_3 \<D> \<Longrightarrow> MT1(\<^bold>\<not>)" unfolding Defs by (metis (full_types) NOR_def PD1 bottom_def compl_def diff_def ineg_prop top_def)
lemma "\<DD> \<D> \<Longrightarrow> MT2(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "\<DD> \<D> \<Longrightarrow> MT3(\<^bold>\<not>)" nitpick oops (*countermodel*)

text\<open>\noindent{We show how all local contraposition variants (lCoP) can be recovered using the determinedness operator.
Observe that we can recover in the same way other (weaker) properties: CoP, MT and DNI/DNE (local \& global).}\<close>
lemma "\<DD> \<D> \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma det_lcop1: "[\<^bold>\<circ>a, a \<^bold>\<rightarrow> b \<^bold>\<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" using dual_def pI1 conn by auto 
lemma "\<DD> \<D> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma det_lcop2: "[\<^bold>\<circ>a, a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile> b \<^bold>\<rightarrow> \<^bold>\<not>a]" using dual_def pI1 conn by auto
lemma "\<DD> \<D> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma det_lcop3: "[\<^bold>\<circ>a, \<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" using dual_def pI1 conn by auto
lemma "\<DD> \<D> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma det_lcop4: "[\<^bold>\<circ>a, \<^bold>\<not>a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile> b \<^bold>\<rightarrow> a]" using dual_def pI1 conn by auto

text\<open>\noindent{Disjunctive syllogism (DS).}\<close>
lemma "DS1(\<^bold>\<rightarrow>)(\<^bold>\<not>)" by (simp add: DS1_def diff_def impl_def ineg_prop join_def)
lemma "\<DD> \<D> \<Longrightarrow> DS2(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma det_ds2: "[\<^bold>\<circ>a, \<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile> a \<^bold>\<or> b]" using pB1 dual_def conn by auto

end
