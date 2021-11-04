theory topo_alexandrov
   imports sse_operation_positive_quantification
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)


section \<open>Generalized specialization orderings and Alexandrov topologies\<close>

text\<open>\noindent{A topology is called 'Alexandrov' (after the Russian mathematician Pavel Alexandrov) if the intersection
(resp. union) of any (finite or infinite) family of open (resp. closed) sets is open (resp. closed);
in algebraic terms, this means that the set of fixed points of the interior (closure) operation is closed
under infinite meets (joins). Another common algebraic formulation requires the closure (interior) operation
to satisfy the infinitary variants of additivity (multiplicativity), i.e. iADDI (iMULT) as introduced before.

In the literature, the well-known Kuratowski conditions for the closure (resp. interior) operation are assumed,
namely: ADDI, EXP, NOR, IDEM (resp. MULT, dEXP, dNOR, IDEM). This makes both formulations equivalent.
However, this is not the case in general if those conditions become negotiable.}\<close>

text\<open>\noindent{Alexandrov topologies have interesting properties relating them to the semantics of modal logic.
Assuming Kuratowski conditions, Alexandrov topological operations defined on subsets of S are in one-to-one
correspondence with preorders on S; in topological terms, Alexandrov topologies are uniquely determined by
their specialization preorders. Since we do not presuppose any Kuratowski conditions to begin with, the
preorders in question are in general not even transitive. Here we just call them 'specialization relations'.
We will still call (generalized) closure/interior-like operations as such (for lack of a better name).
We explore minimal conditions under which some relevant results for the semantics of modal logic obtain.}\<close>

subsection \<open>Specialization relations\<close>

text\<open>\noindent{Specialization relations (among worlds/points) are particular cases of propositional functions with type @{text "w\<Rightarrow>\<sigma>"}.}\<close>

text\<open>\noindent{Define some relevant properties of relations: }\<close>
abbreviation "serial R  \<equiv> \<forall>x. \<exists>y. R x y"
abbreviation "reflexive R  \<equiv> \<forall>x. R x x"
abbreviation "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation "antisymmetric R  \<equiv> \<forall>x y. R x y \<and> R y x \<longrightarrow> x = y"
abbreviation "symmetric R  \<equiv> \<forall>x y. R x y \<longrightarrow> R y x"

text\<open>\noindent{Closure/interior operations can be derived from an arbitrary relation as operations returning down-/up-sets.}\<close>
definition Cl_rel::"(w\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<C>\<^sub>R") where "\<C>\<^sub>R R \<equiv> \<lambda>A. \<lambda>w. \<exists>v. R w v \<and> A v"
definition Int_rel::"(w\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>\<sigma>)" ("\<I>\<^sub>R") where "\<I>\<^sub>R R \<equiv> \<lambda>A. \<lambda>w. \<forall>v. R w v \<longrightarrow> A v"

text\<open>\noindent{Duality between interior and closure follows directly:}\<close>
lemma dual_rel1: "\<forall>A. (\<C>\<^sub>R R) A \<^bold>\<approx> (\<I>\<^sub>R R)\<^sup>d A" unfolding Cl_rel_def Int_rel_def dual_def conn by simp
lemma dual_rel2: "\<forall>A. (\<I>\<^sub>R R) A \<^bold>\<approx> (\<C>\<^sub>R R)\<^sup>d A" unfolding Cl_rel_def Int_rel_def dual_def conn by simp 

text\<open>\noindent{We explore minimal conditions of the specialization relation under which some operation's conditions obtain.}\<close> 
lemma rC1: "ADDI (\<C>\<^sub>R R)" unfolding Cl_rel_def ADDI_def conn by blast
lemma rC1i:"iADDI (\<C>\<^sub>R R)" by (smt Cl_rel_def Ra_restr_ex iADDI_def supremum_def)
lemma rC2: "reflexive R \<longrightarrow> EXP (\<C>\<^sub>R R)" unfolding EXP_def Cl_rel_def by auto
lemma rC3: "NOR (\<C>\<^sub>R R)" unfolding Cl_rel_def NOR_def conn by blast
lemma rC4: "reflexive R \<and> transitive R \<longrightarrow> IDEM (\<C>\<^sub>R R)" unfolding Cl_rel_def IDEM_def by smt
lemma rC_Barcan: "\<forall>\<pi>. (\<C>\<^sub>R R)(\<^bold>\<exists>x. \<pi> x) \<^bold>\<preceq> (\<^bold>\<exists>x. (\<C>\<^sub>R R)(\<pi> x))" unfolding Cl_rel_def by auto

lemma rI1: "MULT (\<I>\<^sub>R R)" unfolding Int_rel_def MULT_def conn by blast
lemma rI1i:"iMULT (\<I>\<^sub>R R)" by (smt Int_rel_def Ra_restr_all iMULT_def infimum_def)
lemma rI2: "reflexive R \<Longrightarrow> dEXP (\<I>\<^sub>R R)" unfolding Int_rel_def dEXP_def Int_rel_def by auto
lemma rI3: "dNOR (\<I>\<^sub>R R)" unfolding Int_rel_def dNOR_def conn by simp
lemma rI4: "reflexive R \<Longrightarrow> transitive R \<Longrightarrow> IDEM (\<I>\<^sub>R R)" unfolding IDEM_def Int_rel_def by smt
lemma rI_Barcan: "\<forall>\<pi>. (\<^bold>\<forall>x. (\<I>\<^sub>R R)(\<pi> x)) \<^bold>\<preceq> (\<I>\<^sub>R R)(\<^bold>\<forall>x. \<pi> x)" unfolding Int_rel_def by simp

text\<open>\noindent{A specialization relation can be derived from a given operation (intended as a closure-like operation).}\<close>
definition sp_rel::"(\<sigma>\<Rightarrow>\<sigma>)\<Rightarrow>(w\<Rightarrow>\<sigma>)" ("\<R>\<^sup>C") where "\<R>\<^sup>C \<C> \<equiv> \<lambda>w v. \<C> (\<lambda>u. u=v) w"

text\<open>\noindent{Preorder properties of the specialization relation follow directly from the corresponding operation's conditions.}\<close>
lemma sp_rel_reflex: "EXP \<C> \<Longrightarrow> reflexive (\<R>\<^sup>C \<C>)" by (simp add: EXP_def sp_rel_def)
lemma sp_rel_trans: "MONO \<C> \<Longrightarrow> IDEM \<C> \<Longrightarrow> transitive (\<R>\<^sup>C \<C>)" by (smt IDEM_def MONO_def sp_rel_def)

text\<open>\noindent{However, we can obtain finite countermodels for antisymmetry and symmetry given all relevant conditions.
We will revisit this issue later and examine their relation with the topological separation axioms T0 and T1 resp.}\<close>
lemma "iADDI \<C> \<Longrightarrow> EXP \<C> \<Longrightarrow> NOR \<C> \<Longrightarrow> IDEM \<C> \<Longrightarrow> antisymmetric (\<R>\<^sup>C \<C>)" nitpick oops (*counterexample*)
lemma "iADDI \<C> \<Longrightarrow> EXP \<C> \<Longrightarrow> NOR \<C> \<Longrightarrow> IDEM \<C> \<Longrightarrow> symmetric (\<R>\<^sup>C \<C>)" nitpick oops (*counterexample*)


subsection \<open>Alexandrov topology\<close>

text\<open>\noindent{As mentioned previously, Alexandrov closure (and by duality interior) operations correspond to specialization
relations. It is worth mentioning that in Alexandrov topologies every point has a minimal/smallest neighborhood,
namely the set of points related to it by the specialization (aka. accessibility) relation. Alexandrov spaces are
thus also called 'finitely generated'. We examine below  minimal conditions under which these relations obtain.}\<close>

lemma sp_rel_a:   "MONO \<C>  \<Longrightarrow> \<forall>A. (\<C>\<^sub>R (\<R>\<^sup>C \<C>)) A \<^bold>\<preceq> \<C> A" by (smt Cl_rel_def MONO_def sp_rel_def)
lemma sp_rel_b: "iADDI_a \<C> \<Longrightarrow> \<forall>A. (\<C>\<^sub>R (\<R>\<^sup>C \<C>)) A \<^bold>\<succeq> \<C> A"  proof -
  assume iaddia: "iADDI_a \<C>"
  { fix A
    let ?S="\<lambda>B::\<sigma>. \<exists>w::w. A w \<and> B=(\<lambda>u. u=w)"
    have "A \<^bold>\<approx> (\<^bold>\<Or>?S)" using supremum_def by auto
    hence "\<C>(A) \<^bold>\<approx> \<C>(\<^bold>\<Or>?S)" by (smt eq_ext) 
    moreover have "\<^bold>\<Or>Ra[\<C>|?S] \<^bold>\<approx> (\<C>\<^sub>R (\<R>\<^sup>C \<C>)) A" by (smt Cl_rel_def Ra_restr_ex sp_rel_def)
    moreover from iaddia have "\<C>(\<^bold>\<Or>?S) \<^bold>\<preceq> \<^bold>\<Or>Ra[\<C>|?S]" unfolding iADDI_a_def by simp
    ultimately have "\<C> A \<^bold>\<preceq> (\<C>\<^sub>R (\<R>\<^sup>C \<C>)) A" by simp
  } thus ?thesis by simp
qed
lemma sp_rel: "iADDI \<C> \<Longrightarrow> \<forall>A. \<C> A \<^bold>\<approx> (\<C>\<^sub>R (\<R>\<^sup>C \<C>)) A" by (metis MONO_iADDIb iADDI_a_def iADDI_b_def iADDI_def sp_rel_a sp_rel_b)
text\<open>\noindent{It is instructive to expand the definitions in the above lemma:}\<close>
lemma "iADDI \<C> \<Longrightarrow>  \<forall>A. \<forall>w. (\<C> A) w \<longleftrightarrow> (\<exists>v. A v \<and> (\<C> (\<lambda>u. u=v)) w)" using Cl_rel_def sp_rel by fastforce


text\<open>\noindent{We now turn to the more traditional characterization of Alexandrov topologies in terms of closure under
infinite joins/meets.}\<close>

text\<open>\noindent{Fixed points of operations satisfying ADDI (MULT) are not in general closed under infinite joins (meets).
For the given conditions countermodels are expected to be infinite. We (sanity) check that nitpick cannot find any.}\<close>
lemma "ADDI(\<phi>) \<Longrightarrow> supremum_closed (fp \<phi>)" (*nitpick*) oops (*cannot find finite countermodels*)
lemma "MULT(\<phi>) \<Longrightarrow> infimum_closed  (fp \<phi>)" (*nitpick*) oops (*cannot find finite countermodels*)

text\<open>\noindent{By contrast, we can show that this obtains if assuming the corresponding infinitary variants (iADDI/iMULT).}\<close>
lemma "iADDI(\<phi>) \<Longrightarrow> supremum_closed (fp \<phi>)" by (metis (full_types) Ra_restr_ex iADDI_def supremum_def)
lemma "iMULT(\<phi>) \<Longrightarrow> infimum_closed  (fp \<phi>)" by (metis (full_types) Ra_restr_all iMULT_def infimum_def)

text\<open>\noindent{As shown above, closure (interior) operations derived from relations readily satisfy iADDI (iMULT),
being thus closed under infinite joins (meets).}\<close>
lemma "supremum_closed (fp (\<C>\<^sub>R R))" by (smt Cl_rel_def supremum_def)
lemma "infimum_closed  (fp (\<I>\<^sub>R R))" by (smt Int_rel_def infimum_def)


subsection \<open>(Anti)symmetry and the separation axioms T0 and T1\<close>
text\<open>\noindent{We can now revisit the relationship between (anti)symmetry and the separation axioms T1 and T0.}\<close>

text\<open>\noindent{T0: any two distinct points in the space can be separated by an open set (i.e. containing one point and not the other).}\<close>
abbreviation "T0_sep \<C> \<equiv> \<forall>w v. w \<noteq> v \<longrightarrow> (\<exists>G. (fp \<C>\<^sup>d)(G) \<and> (G w \<noteq> G v))"
text\<open>\noindent{T1: any two distinct points can be separated by (two not necessarily disjoint) open sets, i.e. all singletons are closed.}\<close>
abbreviation "T1_sep \<C> \<equiv> \<forall>w. (fp \<C>)(\<lambda>u. u = w)"

text\<open>\noindent{We can (sanity) check that T1 entails T0 but not viceversa.}\<close>
lemma "T0_sep \<C> \<Longrightarrow> T1_sep \<C>" nitpick oops (*counterexample*)
lemma "T1_sep \<C> \<Longrightarrow> T0_sep \<C>" by (smt compl_def dual_def dual_symm)

text\<open>\noindent{Under appropriate conditions, T0-separation corresponds to antisymmetry of the specialization relation (here an ordering).}\<close>
lemma "T0_sep \<C> \<longleftrightarrow> antisymmetric (\<R>\<^sup>C \<C>)" nitpick oops (*counterexample*)
lemma T0_antisymm_a: "MONO \<C> \<Longrightarrow> T0_sep \<C> \<longrightarrow> antisymmetric (\<R>\<^sup>C \<C>)" by (smt Cl_rel_def compl_def dual_def sp_rel_a)
lemma T0_antisymm_b: "EXP \<C> \<Longrightarrow> IDEM \<C> \<Longrightarrow> antisymmetric (\<R>\<^sup>C \<C>) \<longrightarrow> T0_sep \<C>" by (metis (full_types) EXP_dual1 IDEM_def IDEM_dual2 IDEMa_def IDEMb_def compl_def dEXP_def dual_def dual_symm sp_rel_def)
lemma T0_antisymm: "MONO \<C> \<Longrightarrow> EXP \<C> \<Longrightarrow> IDEM \<C> \<Longrightarrow> T0_sep \<C> = antisymmetric (\<R>\<^sup>C \<C>)" by (metis T0_antisymm_a T0_antisymm_b)

text\<open>\noindent{Also, under the appropriate conditions, T1-separation corresponds to symmetry of the specialization relation.}\<close>
lemma T1_symm_a: "T1_sep \<C> \<longrightarrow> symmetric (\<R>\<^sup>C \<C>)" using sp_rel_def by auto
lemma T1_symm_b: "MONO \<C> \<Longrightarrow> EXP \<C> \<Longrightarrow> T0_sep \<C> \<Longrightarrow> symmetric (\<R>\<^sup>C \<C>) \<longrightarrow> T1_sep \<C>" by (metis T0_antisymm_a sp_rel_def sp_rel_reflex)
lemma T1_symm: "MONO \<C> \<Longrightarrow> EXP \<C> \<Longrightarrow> T0_sep \<C> \<Longrightarrow> symmetric (\<R>\<^sup>C \<C>) = T1_sep \<C>" by (metis T1_symm_a T1_symm_b)

end
