(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{DFS Implementation by Hashset} *}
theory Exploration_DFS
imports Exploration 
begin
text_raw {*\label{thy:Exploration_Example}*}

text {*
  This theory implements the DFS-algorithm by using a hashset to remember the
  explored states. It illustrates how to use data refinement with the Isabelle Collections 
  Framework in a realistic, non-trivial application.
*}

subsection "Definitions"
-- {*
  The concrete algorithm uses a hashset (@{typ [source] "'q hs"}) and a worklist. 
*}
type_synonym 'q hs_dfs_state = "'q hs \<times> 'q list"

-- {* The loop terminates on empty worklist *}
definition hs_dfs_cond :: "'q hs_dfs_state \<Rightarrow> bool" 
  where "hs_dfs_cond S == let (Q,W) = S in W\<noteq>[]"

-- {* Refinement of a DFS-step, using hashset operations *}
definition hs_dfs_step 
  :: "('q::hashable \<Rightarrow> 'q ls) \<Rightarrow> 'q hs_dfs_state \<Rightarrow> 'q hs_dfs_state"
  where "hs_dfs_step post S == let 
    (Q,W) = S; 
    \<sigma>=hd W 
  in
    ls.iteratei (post \<sigma>) (\<lambda>_. True) (\<lambda>x (Q,W). 
      if hs.memb x Q then 
        (Q,W) 
      else (hs.ins x Q,x#W)
      ) 
      (Q, tl W)
  "

-- {* Convert post-function to relation *}
definition hs_R :: "('q \<Rightarrow> 'q ls) \<Rightarrow> ('q\<times>'q) set"
  where "hs_R post == {(q,q'). q'\<in>ls.\<alpha> (post q)}"

-- {* Initial state: Set of initial states in discovered set and on worklist *}
definition hs_dfs_initial :: "'q::hashable hs \<Rightarrow> 'q hs_dfs_state"
  where "hs_dfs_initial \<Sigma>i == (\<Sigma>i,hs.to_list \<Sigma>i)"

-- {* Abstraction mapping to abstract-DFS state *}
definition hs_dfs_\<alpha> :: "'q::hashable hs_dfs_state \<Rightarrow> 'q dfs_state"
  where "hs_dfs_\<alpha> S == let (Q,W)=S in (hs.\<alpha> Q,W)"

(*-- {* Additional invariant on concrete level: The hashset invariant must hold *}
definition hs_dfs_invar_add :: "'q::hashable hs_dfs_state set" 
  where "hs_dfs_invar_add == { (Q,W). hs_invar Q }"*)

-- {* Combined concrete and abstract level invariant *}
definition hs_dfs_invar 
  :: "'q::hashable hs \<Rightarrow> ('q \<Rightarrow> 'q ls) \<Rightarrow> 'q hs_dfs_state set"
  where "hs_dfs_invar \<Sigma>i post ==
    { s. (hs_dfs_\<alpha> s) \<in> dfs_invar (hs.\<alpha> \<Sigma>i) (hs_R post) }"

-- "The deterministic while-algorithm"
definition "hs_dfs_dwa \<Sigma>i post == \<lparr>
  dwa_cond = hs_dfs_cond,
  dwa_step = hs_dfs_step post,
  dwa_initial = hs_dfs_initial \<Sigma>i,
  dwa_invar = hs_dfs_invar \<Sigma>i post
\<rparr>"


-- "Executable DFS-search. Given a set of initial states, and a successor 
      function, this function performs a DFS search to return the set of 
      reachable states."
definition "hs_dfs \<Sigma>i post 
  == fst (while hs_dfs_cond (hs_dfs_step post) (hs_dfs_initial \<Sigma>i))"


subsection "Refinement"

text {* We first show that a concrete step implements its abstract specification, and preserves the
  additional concrete invariant *}
lemma hs_dfs_step_correct:
  (*assumes [simp]: "hs_invar Q"
                  "!!s. ls_invar (post s)"*)
  assumes ne: "hs_dfs_cond (Q,W)"
  shows "(hs_dfs_\<alpha> (Q,W),hs_dfs_\<alpha> (hs_dfs_step post (Q,W)))
         \<in>dfs_step (hs_R post)" (is ?T1)
        (*"(hs_dfs_step post (Q,W)) \<in> hs_dfs_invar_add" (is ?T2)*)
proof -

  from ne obtain \<sigma> Wtl where 
    [simp]: "W=\<sigma>#Wtl" 
    by (cases W) (auto simp add: hs_dfs_cond_def)

  have G: "let (Q',W') = hs_dfs_step post (Q,W) in
    hs.invar Q' \<and> (\<exists>Wn. 
      distinct Wn 
      \<and> set Wn = ls.\<alpha> (post \<sigma>) - hs.\<alpha> Q 
      \<and> W'=Wn@Wtl 
      \<and> hs.\<alpha> Q'=ls.\<alpha> (post \<sigma>) \<union> hs.\<alpha> Q)"
    apply (simp add: hs_dfs_step_def)
    apply (rule_tac 
      I="\<lambda>it (Q',W'). hs.invar Q' \<and> (\<exists>Wn. 
           distinct Wn 
           \<and> set Wn = (ls.\<alpha> (post \<sigma>) - it) - hs.\<alpha> Q 
           \<and> W'=Wn@Wtl 
           \<and> hs.\<alpha> Q'=(ls.\<alpha> (post \<sigma>) - it) \<union> hs.\<alpha> Q)" 
      in ls.iterate_rule_P)
    apply simp
    apply simp
    apply (force split: split_if_asm simp add: hs.correct)
    apply force
    done
  from G show ?T1
    apply (cases "hs_dfs_step post (Q, W)")
    apply (auto simp add: hs_R_def hs_dfs_\<alpha>_def intro!: dfs_step.intros)
    done
  (*from G show ?T2
    apply (cases "hs_dfs_step post (Q, W)")
    apply (auto simp add: hs_dfs_invar_add_def)
    done*)
qed

-- "Prove refinement"
theorem hs_dfs_pref_dfs: 
  (*assumes [simp]: "hs_invar \<Sigma>i"
  assumes [simp]: "!!q. ls_invar (post q)"*)
  shows "wa_precise_refine 
    (det_wa_wa (hs_dfs_dwa \<Sigma>i post)) 
    (dfs_algo (hs.\<alpha> \<Sigma>i) (hs_R post)) 
    hs_dfs_\<alpha>"
  apply (unfold_locales)
  apply (auto simp add: det_wa_wa_def hs_dfs_dwa_def hs_dfs_\<alpha>_def 
                        hs_dfs_cond_def dfs_algo_def dfs_cond_def) [1]
  apply (auto simp add: det_wa_wa_def hs_dfs_dwa_def dfs_algo_def 
                        hs_dfs_invar_def (*hs_dfs_invar_add_def *)
              intro!: hs_dfs_step_correct(1)) [1]
  apply (auto simp add: det_wa_wa_def hs_dfs_dwa_def hs_dfs_\<alpha>_def 
                        hs_dfs_cond_def dfs_algo_def dfs_cond_def
                        hs_dfs_invar_def hs_dfs_step_def hs_dfs_initial_def 
                        hs.to_list_correct 
              intro: dfs_initial.intros
  ) [3]
  done

    -- "Show that concrete algorithm is a while-algo"
theorem hs_dfs_while_algo: 
  assumes finite[simp]: "finite ((hs_R post)\<^sup>* `` hs.\<alpha> \<Sigma>i)"
  shows "while_algo (det_wa_wa (hs_dfs_dwa \<Sigma>i post))"
proof -
  interpret ref: wa_precise_refine 
    "(det_wa_wa (hs_dfs_dwa \<Sigma>i post))" 
    "(dfs_algo (hs.\<alpha> \<Sigma>i) (hs_R post))" 
    "hs_dfs_\<alpha>" 
    using hs_dfs_pref_dfs .
  show ?thesis
    apply (rule ref.wa_intro[where addi=UNIV])
    apply (simp add: dfs_while_algo)
    apply (simp add: det_wa_wa_def hs_dfs_dwa_def hs_dfs_invar_def dfs_algo_def)

    apply (auto simp add: det_wa_wa_def hs_dfs_dwa_def) [1]
    apply simp
    done
qed
    
-- "Show that concrete algo is a deterministic while-algo"
theorems hs_dfs_det_while_algo = det_while_algo_intro[OF hs_dfs_while_algo]

  -- "Transferred correctness theorem"
theorems hs_dfs_invar_final = 
  wa_precise_refine.transfer_correctness[OF
     hs_dfs_pref_dfs dfs_invar_final]

  -- "The executable implementation is correct"
theorem hs_dfs_correct:
  assumes finite[simp]: "finite ((hs_R post)\<^sup>* `` hs.\<alpha> \<Sigma>i)"
  shows "hs.\<alpha> (hs_dfs \<Sigma>i post) = (hs_R post)\<^sup>*``hs.\<alpha> \<Sigma>i" (is ?T1)
proof -
  from hs_dfs_det_while_algo[OF finite] interpret 
    dwa: det_while_algo "(hs_dfs_dwa \<Sigma>i post)" .

  have 
    LC: "(while hs_dfs_cond (hs_dfs_step post) (hs_dfs_initial \<Sigma>i)) = dwa.loop"
    by (unfold dwa.loop_def) (simp add: hs_dfs_dwa_def)

  have "?T1 (*\<and> ?T2*)"
    apply (unfold hs_dfs_def)
    apply (simp only: LC)
    apply (rule dwa.while_proof)
    apply (case_tac s)
    using hs_dfs_invar_final[of \<Sigma>i "post"] (*[of id, simplified]*)
    apply (auto simp add: det_wa_wa_def hs_dfs_dwa_def 
                          dfs_\<alpha>_def hs_dfs_\<alpha>_def) [1]
    done
  thus ?T1  by auto
qed

subsection "Code Generation"
export_code hs_dfs in SML module_name DFS
export_code hs_dfs in OCaml module_name DFS
export_code hs_dfs in Haskell module_name DFS

end
