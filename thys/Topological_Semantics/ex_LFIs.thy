theory ex_LFIs
  imports topo_negation_conditions
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Example application: Logics of Formal Inconsistency (LFIs)\<close>
text\<open>\noindent{The LFIs @{cite LFI} @{cite RLFI} are a family of paraconsistent logics featuring a 'consistency'
operator @{text "\<^bold>\<circ>"} that can be used to recover some classical properties of negation (in particular ECQ).
We show how to semantically embed LFIs as extensions of Boolean algebras (here as frontier algebras).}\<close>

text\<open>\noindent{Logical validity can be defined as truth in all worlds/points (i.e. as denoting the top element)}\<close>
abbreviation gtrue::"\<sigma>\<Rightarrow>bool" ("[\<^bold>\<turnstile> _]") where  "[\<^bold>\<turnstile>  A] \<equiv> \<forall>w. A w"   
lemma gtrue_def: "[\<^bold>\<turnstile> A] \<equiv> A \<^bold>\<approx> \<^bold>\<top>"  by (simp add: top_def)

text\<open>\noindent{When defining a logic over an existing algebra we have two choices: a global (truth preserving)
and a local (truth-degree preserving) notion of logical consequence. For LFIs we prefer the latter.}\<close>
abbreviation conseq_global1::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile>\<^sub>g _]") where "[A \<^bold>\<turnstile>\<^sub>g B] \<equiv> [\<^bold>\<turnstile> A] \<longrightarrow> [\<^bold>\<turnstile> B]"
abbreviation conseq_global2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile>\<^sub>g _]") where "[A\<^sub>1, A\<^sub>2 \<^bold>\<turnstile>\<^sub>g B] \<equiv> [\<^bold>\<turnstile> A\<^sub>1] \<and> [\<^bold>\<turnstile> A\<^sub>2] \<longrightarrow> [\<^bold>\<turnstile> B]"
abbreviation conseq_global3::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_,_ \<^bold>\<turnstile>\<^sub>g _]") where "[A\<^sub>1, A\<^sub>2, A\<^sub>3 \<^bold>\<turnstile>\<^sub>g B] \<equiv> [\<^bold>\<turnstile> A\<^sub>1] \<and> [\<^bold>\<turnstile> A\<^sub>2] \<and> [\<^bold>\<turnstile> A\<^sub>3] \<longrightarrow> [\<^bold>\<turnstile> B]"
abbreviation conseq_local1::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_ \<^bold>\<turnstile> _]") where "[A \<^bold>\<turnstile> B] \<equiv> A \<^bold>\<preceq> B"
abbreviation conseq_local2::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_ \<^bold>\<turnstile> _]") where "[A\<^sub>1, A\<^sub>2 \<^bold>\<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<preceq> B"
abbreviation conseq_local3::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>bool" ("[_,_,_ \<^bold>\<turnstile> _]") where "[A\<^sub>1, A\<^sub>2, A\<^sub>3 \<^bold>\<turnstile> B] \<equiv> A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<and> A\<^sub>3 \<^bold>\<preceq> B"
(*add more as the need arises...*)

text\<open>\noindent{For LFIs we use the (paraconsistent) closure-based negation previously defined (taking frontier as primitive). }\<close>
abbreviation cneg::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>") where "\<^bold>\<not>A \<equiv> \<^bold>\<not>\<^sup>CA"

text\<open>\noindent{In terms of the frontier operator the negation looks as follows:}\<close>
lemma "\<^bold>\<not>A \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<or> \<F>(\<^bold>\<midarrow>A)" by (simp add: neg_C_def pC2)
lemma cneg_prop: "Fr_2 \<F> \<Longrightarrow> \<^bold>\<not>A \<^bold>\<approx> \<^bold>\<midarrow>A \<^bold>\<or> \<F>(A)" using pC2 pF2 unfolding conn by blast

text\<open>\noindent{This negation is of course boldly paraconsistent.}\<close>
lemma "[a, \<^bold>\<not>a \<^bold>\<turnstile> b]" nitpick oops (*countermodel*)
lemma "[a, \<^bold>\<not>a \<^bold>\<turnstile> \<^bold>\<not>b]" nitpick oops (*countermodel*)
lemma "[a, \<^bold>\<not>a \<^bold>\<turnstile>\<^sub>g b]" nitpick oops (*countermodel*) 
lemma "[a, \<^bold>\<not>a \<^bold>\<turnstile>\<^sub>g \<^bold>\<not>b]" nitpick oops (*countermodel*)

text\<open>\noindent{We define two pairs of in/consistency operators and show how they relate to each other.
Using LFIs terminology, the minimal logic so encoded corresponds to 'RmbC-ciw' (cf. @{cite RLFI}).}\<close>
abbreviation op_inc_a::"\<sigma>\<Rightarrow>\<sigma>" ("\<bullet>\<^sup>A_" [57]58) where "\<bullet>\<^sup>AA \<equiv> A \<^bold>\<and> \<^bold>\<not>A"
abbreviation op_con_a::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>\<^sup>A_" [57]58) where "\<^bold>\<circ>\<^sup>AA \<equiv> \<^bold>\<midarrow>\<bullet>\<^sup>AA"
abbreviation op_inc_b::"\<sigma>\<Rightarrow>\<sigma>" ("\<bullet>\<^sup>B_" [57]58) where "\<bullet>\<^sup>BA \<equiv> \<B> A"
abbreviation op_con_b::"\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>\<^sup>B_" [57]58) where "\<^bold>\<circ>\<^sup>BA \<equiv> \<B>\<^sup>c A"

text\<open>\noindent{Observe that assumming condition Fr-2 are we allowed to exchange A and B variants.}\<close>
lemma pincAB: "Fr_2 \<F> \<Longrightarrow> \<bullet>\<^sup>AA \<^bold>\<approx> \<bullet>\<^sup>BA" using Br_fr_def Cl_fr_def pF2 conn by auto
lemma pconAB: "Fr_2 \<F> \<Longrightarrow> \<^bold>\<circ>\<^sup>AA \<^bold>\<approx> \<^bold>\<circ>\<^sup>BA" using pincAB unfolding conn by simp

text\<open>\noindent{Variants A and B give us slightly different properties.}\<close>
lemma Prop1: "\<^bold>\<circ>\<^sup>BA \<^bold>\<approx> \<I>\<^sup>f\<^sup>p A" using fp1 unfolding conn equal_op_def by metis
lemma "\<^bold>\<circ>\<^sup>AA \<^bold>\<approx> A \<^bold>\<rightarrow> \<I> A" nitpick oops (*countermodel*)
lemma Prop2: "Cl A \<longleftrightarrow> \<^bold>\<circ>\<^sup>A\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<top>" using pC2 unfolding conn by auto
lemma "Cl A \<longrightarrow> \<^bold>\<circ>\<^sup>B\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*countermodel*)
lemma Prop3: "Cl A \<longleftrightarrow> \<bullet>\<^sup>A\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<bottom>" using Cl_fr_def unfolding conn by auto
lemma "Cl A \<longrightarrow> \<bullet>\<^sup>B\<^bold>\<midarrow>A \<^bold>\<approx> \<^bold>\<bottom>" nitpick oops (*countermodel*)
lemma Prop4: "Op A \<longleftrightarrow> \<^bold>\<circ>\<^sup>BA \<^bold>\<approx> \<^bold>\<top>" using Op_Bzero unfolding conn by simp
lemma "Op A \<longrightarrow> \<^bold>\<circ>\<^sup>AA \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*countermodel*)
lemma Prop5: "Op A \<longleftrightarrow> \<bullet>\<^sup>BA \<^bold>\<approx> \<^bold>\<bottom>" using Op_Bzero by simp
lemma "Op A \<longrightarrow> \<bullet>\<^sup>AA \<^bold>\<approx> \<^bold>\<bottom>" nitpick oops (*countermodel*)

text\<open>\noindent{Importantly, LFIs must satisfy the so-called 'principle of gentle explosion'. Only variant A works here:}\<close>
lemma "[\<^bold>\<circ>\<^sup>Aa, a, \<^bold>\<not>a \<^bold>\<turnstile> b]" using compl_def meet_def by auto
lemma "[\<^bold>\<circ>\<^sup>Aa, a, \<^bold>\<not>a \<^bold>\<turnstile>\<^sub>g b]" using compl_def meet_def by auto
lemma "[\<^bold>\<circ>\<^sup>Ba, a, \<^bold>\<not>a \<^bold>\<turnstile> b]" nitpick oops (*countermodel*)
lemma "[\<^bold>\<circ>\<^sup>Ba, a, \<^bold>\<not>a \<^bold>\<turnstile>\<^sub>g b]" nitpick oops (*countermodel*)

text\<open>\noindent{In what follows we employ the (minimal) A-variant and verify some properties.}\<close>
abbreviation op_inc :: "\<sigma>\<Rightarrow>\<sigma>" ("\<bullet>_" [57]58) where "\<bullet>A  \<equiv> \<bullet>\<^sup>AA"
abbreviation op_con :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<circ>_" [57]58) where "\<^bold>\<circ>A  \<equiv> \<^bold>\<midarrow>\<bullet>A"

lemma "TND(\<^bold>\<not>)" by (simp add: TND_C)
lemma "ECQm(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> LNC(\<^bold>\<not>)" by (simp add: LNC_C PF6)
lemma "\<FF> \<F> \<Longrightarrow> DNI(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "\<FF> \<F> \<Longrightarrow> DNE(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> CoPw(\<^bold>\<not>)" by (simp add: CoPw_C PF6)
lemma "\<FF> \<F> \<Longrightarrow> CoP1(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "\<FF> \<F> \<Longrightarrow> CoP2(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "\<FF> \<F> \<Longrightarrow> CoP3(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> DM3(\<^bold>\<not>)" by (simp add: DM3_C)
lemma "\<FF> \<F> \<Longrightarrow> DM4(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "nNor(\<^bold>\<not>)" by (simp add: nNor_C)
lemma "Fr_3 \<F> \<Longrightarrow> nDNor(\<^bold>\<not>)" by (simp add: nDNor_C)
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> MT0(\<^bold>\<not>)" by (simp add: MT0_C PF6)
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> MT1(\<^bold>\<not>)" by (simp add: MT1_C PF6)
lemma "\<FF> \<F> \<Longrightarrow> MT2(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> MT3(\<^bold>\<not>)" using MT3_C by auto

text\<open>\noindent{We show how all local contraposition variants (lCoP) can be recovered using the consistency operator.
Observe that we can recover in the same way other (weaker) properties: CoP, MT and DNI/DNE (local \& global).}\<close>
lemma "\<FF> \<F> \<Longrightarrow> lCoPw(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma cons_lcop1: "[\<^bold>\<circ>b, a \<^bold>\<rightarrow> b \<^bold>\<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> \<^bold>\<not>a]" using Cl_fr_def conn by auto
lemma "\<FF> \<F> \<Longrightarrow> lCoP1(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma cons_lcop2: "[\<^bold>\<circ>b, a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile> b \<^bold>\<rightarrow> \<^bold>\<not>a]" using Cl_fr_def conn by auto
lemma "\<FF> \<F> \<Longrightarrow> lCoP2(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma cons_lcop3: "[\<^bold>\<circ>b, \<^bold>\<not>a \<^bold>\<rightarrow> b \<^bold>\<turnstile> \<^bold>\<not>b \<^bold>\<rightarrow> a]" using Cl_fr_def conn by auto
lemma "\<FF> \<F> \<Longrightarrow> lCoP3(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma cons_lcop4: "[\<^bold>\<circ>b, \<^bold>\<not>a \<^bold>\<rightarrow> \<^bold>\<not>b \<^bold>\<turnstile> b \<^bold>\<rightarrow> a]" using Cl_fr_def conn by auto
text\<open>\noindent{Disjunctive syllogism (DS).}\<close>
lemma "\<FF> \<F> \<Longrightarrow> DS1(\<^bold>\<rightarrow>)(\<^bold>\<not>)" nitpick oops (*countermodel*)
lemma cons_ds1: "[\<^bold>\<circ>a, a \<^bold>\<or> b \<^bold>\<turnstile> \<^bold>\<not>a \<^bold>\<rightarrow> b]" using conn by auto
lemma "DS2(\<^bold>\<rightarrow>)(\<^bold>\<not>)" by (metis Cl_fr_def DS2_def compl_def impl_def join_def neg_C_def)
text\<open>\noindent{Further properties.}\<close>
lemma "[a \<^bold>\<and> \<^bold>\<not>a \<^bold>\<turnstile> \<^bold>\<not>(\<^bold>\<circ>a)]" by (simp add: pC2 conn)
lemma "\<FF> \<F> \<Longrightarrow> [\<^bold>\<not>(\<^bold>\<circ>a) \<^bold>\<turnstile> a \<^bold>\<and> \<^bold>\<not>a]" nitpick oops (* countermodel found *)
lemma "[\<^bold>\<circ>a \<^bold>\<turnstile> \<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a)]" by (simp add: pC2 conn)
lemma "\<FF> \<F> \<Longrightarrow> [\<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>a) \<^bold>\<turnstile> \<^bold>\<circ>a]" nitpick oops (* countermodel found *)

text\<open>\noindent{The following axioms are commonly employed in the literature on LFIs to obtain stronger logics.
We explore under which conditions they can be assumed while keeping the logic boldly paraconsistent.}\<close>
abbreviation cf where "cf \<equiv> DNE(\<^bold>\<not>)"
abbreviation ce where "ce \<equiv> DNI(\<^bold>\<not>)"
abbreviation ciw where "ciw \<equiv> \<forall>P. [\<^bold>\<turnstile> \<^bold>\<circ>P \<^bold>\<or> \<bullet>P]"
abbreviation ci  where  "ci \<equiv> \<forall>P.  [\<^bold>\<not>(\<^bold>\<circ>P) \<^bold>\<turnstile> \<bullet>P]"
abbreviation cl  where  "cl \<equiv> \<forall>P.  [\<^bold>\<not>(\<bullet>P) \<^bold>\<turnstile> \<^bold>\<circ>P]"
abbreviation ca_conj where "ca_conj \<equiv> \<forall>P Q. [\<^bold>\<circ>P,\<^bold>\<circ>Q \<^bold>\<turnstile> \<^bold>\<circ>(P \<^bold>\<and> Q)]"
abbreviation ca_disj where "ca_disj \<equiv> \<forall>P Q. [\<^bold>\<circ>P,\<^bold>\<circ>Q \<^bold>\<turnstile> \<^bold>\<circ>(P \<^bold>\<or> Q)]"
abbreviation ca_impl where "ca_impl \<equiv> \<forall>P Q. [\<^bold>\<circ>P,\<^bold>\<circ>Q \<^bold>\<turnstile> \<^bold>\<circ>(P \<^bold>\<rightarrow> Q)]"
abbreviation ca where "ca \<equiv> ca_conj \<and> ca_disj \<and> ca_impl"

text\<open>\noindent{cf}\<close>
lemma "\<FF> \<F> \<Longrightarrow> cf" nitpick oops
lemma "\<FF> \<F> \<and> cf \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)
text\<open>\noindent{ce}\<close>
lemma "\<FF> \<F> \<Longrightarrow> ce" nitpick oops
lemma "Fr_1 \<F> \<and> Fr_2 \<F> \<and> Fr_4 \<F> \<and> ce \<and> \<sim>ECQ(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)  
lemma "Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> ce \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)  
lemma "Fr_1a \<F> \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> ce \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)  
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> ce \<longrightarrow> ECQm(\<^bold>\<not>)" unfolding Defs  using CoP1_XCoP CoP1_def2 CoPw_C DNI_def ECQw_def PF6 XCoP_def2 by auto
text\<open>\noindent{ciw}\<close>
lemma ciw by (simp add:conn)
text\<open>\noindent{ci}\<close>
lemma "\<FF> \<F> \<Longrightarrow> ci" nitpick oops
lemma "\<FF> \<F> \<and> ci \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)
text\<open>\noindent{cl}\<close>
lemma "\<FF> \<F> \<Longrightarrow> cl" nitpick oops
lemma "Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cl \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*) 
lemma "Fr_1a \<F> \<and> Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cl \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> cl \<longrightarrow> ECQ(\<^bold>\<not>)" unfolding Defs  by (metis BC_rel Br_Border Br_cl_def bottom_def compl_def eq_ext' meet_def neg_C_def) 
text\<open>\noindent{ca-conj/disj}\<close>
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> ca_conj" using DM3_C DM3_def conn by auto
lemma "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> ca_disj" using ADDI_b_def MONO_ADDIb monI pB1 pincAB unfolding conn by metis
lemma "\<FF> \<F> \<Longrightarrow> ca_impl" nitpick oops
text\<open>\noindent{ca-impl}\<close>
lemma "ca_impl \<and> \<sim>ECQ(\<^bold>\<not>)" (*nitpick[satisfy]*) oops (*cannot find finite model*)
lemma "ca_impl \<longrightarrow> ECQm(\<^bold>\<not>)" oops (*nor proof yet*)
text\<open>\noindent{cf \& ci}\<close>
lemma "Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cf \<and> ci \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)  
lemma "Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cf \<and> ci \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)
lemma "Fr_1b \<F> \<and> Fr_2 \<F> \<and> cf \<and> ci \<and> \<sim>ECQ(\<^bold>\<not>)" (*nitpick[satisfy]*) oops (*cannot find finite model*) 
lemma "\<FF> \<F> \<and> cf \<and> ci \<longrightarrow> ECQm(\<^bold>\<not>)" oops (*nor proof yet*) 
text\<open>\noindent{cf \& cl}\<close>
lemma "Fr_1 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cf \<and> cl \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*) 
lemma "Fr_2 \<F> \<and> Fr_3 \<F> \<and> Fr_4 \<F> \<and> cf \<and> cl \<and> \<sim>ECQm(\<^bold>\<not>)" nitpick[satisfy] oops (*model found*)
lemma "Fr_1b \<F> \<and> Fr_2 \<F> \<and> cf \<and> cl \<longrightarrow> ECQ(\<^bold>\<not>)" unfolding Defs by (smt Br_fr_def Fr_1b_def Prop2 Prop3 pF3 cneg_prop conn) 

end
