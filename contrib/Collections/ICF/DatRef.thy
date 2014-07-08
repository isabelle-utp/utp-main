(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Deprecated: Data Refinement for the While-Combinator} *}
theory DatRef
imports 
  Main 
  "~~/src/HOL/Library/While_Combinator"
begin
text_raw {*\label{thy:DatRef}*}

text {*
  Note that this theory is deprecated. For new developments, the refinement 
  framework (Refine-Monadic entry of the AFP) should be used.
*}

text {*
  In this theory, a data refinement framework for 
  non-deterministic while-loops is developed. The refinement is based on
  showing simulation w.r.t. an abstraction function.
  The case of deterministic while-loops is explicitely handled, to
  support proper code-generation using the While-Combinator.
  
  Note that this theory is deprecated. For new developments, the refinement 
  framework (Refine-Monadic entry of the AFP) should be used.
  *}

(* TODO-LIST and ideas
  - Model nondeterministic algorithms by their step relation, and show refinement stuff for this (more general) model (c.f. dpn-pre^* formalization)
    Then, the nondeterministic while-loop would be a special case.

*)


text {*
  A nondeterministic while-algorithm is described by a set of states, a 
  continuation condition, a step relation, a set of possible initial 
  states and an invariant.
  *}

  -- "Encapsulates a while-algorithm and its invariant "
record 'S while_algo =
  -- "Termination condition"
  wa_cond :: "'S set"
  -- "Step relation (nondeterministic)"
  wa_step :: "('S \<times> 'S) set"
  -- "Initial state (nondeterministic)"
  wa_initial :: "'S set"
  -- "Invariant"
  wa_invar :: "'S set"
  
text {*
  A while-algorithm is called {\em well-defined} iff the invariant holds for 
  all reachable states and the accessible part of the step-relation is
  well-founded.
*}
  -- {* Conditions that must hold for a well-defined while-algorithm *}
locale while_algo =
  fixes WA :: "'S while_algo"

  -- "A step must preserve the invariant"
  assumes step_invar: 
    "\<lbrakk> s\<in>wa_invar WA; s\<in>wa_cond WA; (s,s')\<in>wa_step WA \<rbrakk> \<Longrightarrow> s'\<in>wa_invar WA"
  -- "Initial states must satisfy the invariant"
  assumes initial_invar: "wa_initial WA \<subseteq> wa_invar WA"
  -- "The accessible part of the step relation must be well-founded"
  assumes step_wf: 
    "wf { (s',s). s\<in>wa_invar WA \<and> s\<in>wa_cond WA \<and> (s,s')\<in>wa_step WA }"

text {*
  Next, a refinement relation for while-algorithms is defined.
  Note that the involved while-algorithms are not required to
  be well-defined. Later, some lemmas to transfer well-definedness
  along refinement relations are shown.

  Refinement involves a concrete algorithm, an abstract algorithm and an 
  abstraction function. In essence, a refinement establishes a simulation
  of the concrete algorithm by the abstract algorithm w.r.t. the abstraction 
  function.
*}

locale wa_refine = 
  -- "Concrete algorithm"
  fixes WAC :: "'C while_algo"
  -- "Abstract algorithm"
  fixes WAA :: "'A while_algo"

  -- "Abstraction function"
  fixes \<alpha> :: "'C \<Rightarrow> 'A"

  -- "Condition implemented correctly: The concrete condition must be stronger 
      than the abstract one. Intuitively, this ensures that the concrete loop
      will not run longer than the abstract one that it is simulated by."
  assumes cond_abs: "\<lbrakk> s\<in>wa_invar WAC; s\<in>wa_cond WAC \<rbrakk> \<Longrightarrow> \<alpha> s \<in> wa_cond WAA"

  -- "Step implemented correctly: The abstract step relation must simulate the 
      concrete step relation"
  assumes step_abs: "\<lbrakk> s\<in>wa_invar WAC; s\<in>wa_cond WAC; (s,s')\<in>wa_step WAC \<rbrakk> 
                      \<Longrightarrow> (\<alpha> s, \<alpha> s')\<in>wa_step WAA"
  -- "Initial states implemented correctly: The abstractions of the concrete
      initial states must be abstract initial states."
  assumes initial_abs: "\<alpha> ` wa_initial WAC \<subseteq> wa_initial WAA"
  -- {* Invariant implemented correctly: The concrete invariant must be stronger
        then the abstract invariant.
        Note that, usually, the concrete invariant will be of the 
        form @{term "I_add \<inter> {s. \<alpha> s \<in> wa_invar WAA}"}, where @{term I_add} are
        the additional invariants added by the concrete algorithm.
     *}
  assumes invar_abs: "\<alpha> ` wa_invar WAC \<subseteq> wa_invar WAA"
begin

  lemma initial_abs': "s\<in>wa_initial WAC \<Longrightarrow> \<alpha> s \<in> wa_initial WAA"
    using initial_abs by auto

  lemma invar_abs': "s\<in>wa_invar WAC \<Longrightarrow> \<alpha> s \<in> wa_invar WAA"
    using invar_abs by auto

end

-- {*
  Given a concrete while-algorithm and a well-defined abstract 
  while-algorithm, this lemma shows refinement and 
  well-definedness of the concrete while-algorithm.

  Assuming well-definedness of the abstract algorithm and refinement,
  some proof-obligations for well-definedness of the concrete algorithm can be
  discharged automatically.

  For this purpose, the invariant is split into a concrete and an abstract 
  part. The abstract part claims that the abstraction of a state satisfies 
  the abstract invariant. The concrete part makes some additional claims
  about a valid concrete state. Then, after having shown refinement, the 
  assumptions that the abstract part of the invariant is preserved, can
  be discharged automatically.
*}
lemma wa_refine_intro:
  fixes condc :: "'C set" and 
        stepc :: "('C\<times>'C) set" and 
        initialc :: "'C set" and 
        invar_addc :: "'C set"
  fixes WAA :: "'A while_algo"
  fixes \<alpha> :: "'C \<Rightarrow> 'A"
  assumes "while_algo WAA"

  -- "The concrete step preserves the concrete part of the invariant"
  assumes step_invarc: 
    "!!s s'. \<lbrakk> s\<in>invar_addc; s\<in>condc; \<alpha> s \<in> wa_invar WAA; (s,s')\<in>stepc \<rbrakk> 
              \<Longrightarrow> s'\<in>invar_addc"
  -- "The concrete initial states satisfy the concrete part of the invariant"
  assumes initial_invarc: "initialc \<subseteq> invar_addc"

  -- "Condition implemented correctly"
  assumes cond_abs: 
    "!!s. \<lbrakk> s\<in>invar_addc; \<alpha> s \<in> wa_invar WAA; s\<in>condc \<rbrakk> \<Longrightarrow> \<alpha> s \<in> wa_cond WAA"
  -- "Step implemented correctly"
  assumes step_abs: 
    "!!s s'. \<lbrakk> s\<in>invar_addc; s\<in>condc; \<alpha> s \<in> wa_invar WAA; (s,s')\<in>stepc \<rbrakk> 
             \<Longrightarrow> (\<alpha> s, \<alpha> s')\<in>wa_step WAA"
  -- "Initial states implemented correctly"
  assumes initial_abs: "\<alpha> ` initialc \<subseteq> wa_initial WAA"

  -- "Concrete while-algorithm: The invariant is separated into a concrete and
      an abstract part"
  defines "WAC == \<lparr> 
   wa_cond=condc, 
   wa_step=stepc, 
   wa_initial=initialc, 
   wa_invar=(invar_addc \<inter> {s. \<alpha> s\<in> wa_invar WAA}) \<rparr>"

  shows 
    "while_algo WAC \<and> 
     wa_refine WAC WAA \<alpha>" (is "?T1 \<and> ?T2")
proof
  interpret waa: while_algo WAA by fact
  show G1: "?T1"
    apply (unfold_locales)
    apply (simp_all add: WAC_def)
    apply safe
    apply (blast intro!: step_invarc)

    apply (frule (3) step_abs)
    apply (frule (2) cond_abs)
    apply (erule (2) waa.step_invar)

    apply (erule set_rev_mp[OF _ initial_invarc])

    apply (insert initial_abs waa.initial_invar) [1]
    apply blast

    apply (rule_tac 
      r="inv_image { (s',s). s\<in>wa_invar WAA 
                     \<and> s\<in>wa_cond WAA 
                     \<and> (s,s')\<in>wa_step WAA } \<alpha>" 
      in wf_subset)
    apply (simp add: waa.step_wf)
    apply (auto simp add: cond_abs step_abs) [1]
    done
  show ?T2
    apply (unfold_locales)
    apply (auto simp add: cond_abs step_abs initial_abs WAC_def)
    done
qed

  -- {* After refinement has been shown, this lemma transfers
        the well-definedness property up the refinement chain.
        Like in @{thm [source] wa_refine_intro}, some proof-obligations can
        be discharged by assuming refinement and well-definedness of the 
        abstract algorithm.
    *}
lemma (in wa_refine) wa_intro:
  -- "Concrete part of the invariant"
  fixes addi :: "'C set"
  -- "The abstract algorithm is well-defined"
  assumes "while_algo WAA"
  -- "The invariant can be split into concrete and abstract part"
  assumes icf: "wa_invar WAC = addi \<inter> {s. \<alpha> s \<in> wa_invar WAA}"

  -- "The step-relation preserves the concrete part of the invariant"
  assumes step_addi: 
    "!!s s'. \<lbrakk> s\<in>addi; s\<in>wa_cond WAC; \<alpha> s \<in> wa_invar WAA; 
               (s,s')\<in>wa_step WAC 
             \<rbrakk> \<Longrightarrow> s'\<in>addi"

  -- "The initial states satisfy the concrete part of the invariant"
  assumes initial_addi: "wa_initial WAC \<subseteq> addi"

  shows 
    "while_algo WAC"
proof -
  interpret waa: while_algo WAA by fact
  show ?thesis
    apply (unfold_locales)
    apply (subst icf)
    apply safe
    apply (simp only: icf)
    apply safe
    apply (blast intro!: step_addi)

    apply (frule (2) step_abs)
    apply (frule (1) cond_abs)
    apply (simp only: icf)
    apply clarify
    apply (erule (2) waa.step_invar)

    apply (simp add: icf)
    apply (rule conjI)
    apply (erule set_rev_mp[OF _ initial_addi])
    apply (insert initial_abs waa.initial_invar) [1]
    apply blast

    apply (rule_tac 
      r="inv_image { (s',s). s\<in>wa_invar WAA 
                    \<and> s\<in>wa_cond WAA 
                    \<and> (s,s')\<in>wa_step WAA } \<alpha>" 
      in wf_subset)
    apply (simp add: waa.step_wf)
    apply (auto simp add: cond_abs step_abs icf) [1]
    done
qed

text {*
  A special case of refinement occurs, if the concrete condition implements the
  abstract condition precisely. In this case, the concrete algorithm will run 
  as long as the abstract one that it is simulated by. This allows to 
  transfer properties of the result from the abstract algorithm to the 
  concrete one.
*}

-- "Precise refinement"
locale wa_precise_refine = wa_refine +
  constrains \<alpha> :: "'C \<Rightarrow> 'A"
  assumes cond_precise: 
    "\<forall>s. s\<in>wa_invar WAC \<and> \<alpha> s\<in>wa_cond WAA \<longrightarrow> s\<in>wa_cond WAC"
begin
  -- "Transfer correctness property"
  lemma transfer_correctness:
    assumes A: "\<forall>s. s\<in>wa_invar WAA \<and> s\<notin>wa_cond WAA \<longrightarrow> P s"
    shows "\<forall>sc. sc\<in>wa_invar WAC \<and> sc\<notin>wa_cond WAC \<longrightarrow> P (\<alpha> sc)"
    using A cond_abs invar_abs cond_precise by blast
end
    
text {* Refinement as well as precise refinement is reflexive and transitive *}

lemma wa_ref_refl: "wa_refine WA WA id"
  by (unfold_locales) auto

lemma wa_pref_refl: "wa_precise_refine WA WA id"
  by (unfold_locales) auto

lemma wa_ref_trans: 
  assumes "wa_refine WC WB \<alpha>1"
  assumes "wa_refine WB WA \<alpha>2"
  shows "wa_refine WC WA (\<alpha>2\<circ>\<alpha>1)"
proof -
  interpret r1: wa_refine WC WB \<alpha>1 by fact
  interpret r2: wa_refine WB WA \<alpha>2 by fact

  show ?thesis (* Cool, everything by auto! *)
    apply unfold_locales
    apply (auto simp add: 
      r1.invar_abs' r2.invar_abs'
      r1.cond_abs r2.cond_abs
      r1.step_abs r2.step_abs
      r1.initial_abs' r2.initial_abs')
    done
qed

lemma wa_pref_trans: 
  assumes "wa_precise_refine WC WB \<alpha>1"
  assumes "wa_precise_refine WB WA \<alpha>2"
  shows "wa_precise_refine WC WA (\<alpha>2\<circ>\<alpha>1)"
proof -
  interpret r1: wa_precise_refine WC WB \<alpha>1 by fact
  interpret r2: wa_precise_refine WB WA \<alpha>2 by fact
  
  show ?thesis
    apply intro_locales
    apply (rule wa_ref_trans)
    apply (unfold_locales)
    apply (auto simp add: r1.invar_abs' r2.invar_abs' 
                          r1.cond_precise r2.cond_precise)
    done
qed

text {*
  A well-defined while-algorithm is {\em deterministic}, iff
  the step relation is a function and there is just one 
  initial state. Such an algorithm is suitable for direct implementation 
  by the while-combinator.

  For deterministic while-algorithm, an own record is defined, as well as a
  function that maps it to the corresponding record for non-deterministic
  while algorithms. This makes sense as the step-relation may then be modeled
  as a function, and the initial state may be modeled as a single state rather 
  than a (singleton) set of states.
*}

record 'S det_while_algo =
  -- "Termination condition"
  dwa_cond :: "'S \<Rightarrow> bool"
  -- "Step function"
  dwa_step :: "'S \<Rightarrow> 'S"
  -- "Initial state"
  dwa_initial :: "'S"
  -- "Invariant"
  dwa_invar :: "'S set"
  
  -- "Maps the record for deterministic while-algo to the corresponding record for
      the non-deterministic one"
definition "det_wa_wa DWA == \<lparr> 
  wa_cond={s. dwa_cond DWA s}, 
  wa_step={(s,dwa_step DWA s) | s. True}, 
  wa_initial={dwa_initial DWA},
  wa_invar = dwa_invar DWA\<rparr>"

  -- "Conditions for a deterministic while-algorithm"
locale det_while_algo = 
  fixes WA :: "'S det_while_algo"
  -- "The step preserves the invariant"
  assumes step_invar: 
    "\<lbrakk> s\<in>dwa_invar WA; dwa_cond WA s \<rbrakk> \<Longrightarrow> dwa_step WA s \<in> dwa_invar WA"
  -- "The initial state satisfies the invariant"
  assumes initial_invar: "dwa_initial WA \<in> dwa_invar WA"
  -- "The relation made up by the step-function is well-founded."
  assumes step_wf: 
    "wf { (dwa_step WA s,s) | s. s\<in>dwa_invar WA \<and> dwa_cond WA s }"

begin
  lemma is_while_algo: "while_algo (det_wa_wa WA)"
    apply (unfold_locales)
    apply (auto simp add: det_wa_wa_def step_invar initial_invar)
    apply (insert step_wf)
    apply (erule_tac P=wf in back_subst)
    apply auto
    done

end

lemma det_while_algo_intro:
  assumes "while_algo (det_wa_wa DWA)" 
  shows "det_while_algo DWA"
proof -
  interpret while_algo "(det_wa_wa DWA)" by fact

  show ?thesis using step_invar initial_invar step_wf
    apply (unfold_locales)
    apply (unfold det_wa_wa_def)
    apply auto
    apply (erule_tac P=wf in back_subst)
    apply auto
    done
    
qed

-- "A deterministic while-algorithm is well-defined, if and only if the 
    corresponding non-deterministic while-algorithm is well-defined"
theorem dwa_is_wa: 
  "while_algo (det_wa_wa DWA) \<longleftrightarrow> det_while_algo DWA"
  using det_while_algo_intro det_while_algo.is_while_algo by auto


definition (in det_while_algo) 
  "loop == (while (dwa_cond WA) (dwa_step WA) (dwa_initial WA))"

-- "Proof rule for deterministic while loops"
lemma (in det_while_algo) while_proof:
  assumes inv_imp: "\<And>s. \<lbrakk>s\<in>dwa_invar WA; \<not> dwa_cond WA s\<rbrakk> \<Longrightarrow> Q s"
  shows "Q loop"
  apply (unfold loop_def)
  apply (rule_tac P="\<lambda>x. x\<in>dwa_invar WA" and 
                  r="{ (dwa_step WA s,s) | s. s\<in>dwa_invar WA \<and> dwa_cond WA s }" 
                  in while_rule)
  apply (simp_all add: step_invar initial_invar step_wf inv_imp)
  done

  -- "This version is useful when using transferred correctness lemmas"
lemma (in det_while_algo) while_proof':
  assumes inv_imp: 
    "\<forall>s. s\<in>wa_invar (det_wa_wa WA) \<and> s\<notin>wa_cond (det_wa_wa WA) \<longrightarrow> Q s"
  shows "Q loop"
  using inv_imp
  apply (simp add: det_wa_wa_def)
  apply (blast intro: while_proof)
  done

lemma (in det_while_algo) loop_invar:
  "loop \<in> dwa_invar WA"
  by (rule while_proof) simp


end
