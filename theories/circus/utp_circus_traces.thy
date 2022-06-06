section \<open> Circus Trace Merge \<close>

theory utp_circus_traces
  imports "UTP1-Stateful-Failures.utp_sf_rdes"
begin

subsection \<open> Function Definition \<close>

fun tr_par ::
  "'\<theta> set \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list set" where
"tr_par cs [] [] = {[]}" |
"tr_par cs (e # t) [] = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs t []))" |
"tr_par cs [] (e # t) = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs [] t))" |
"tr_par cs (e\<^sub>1 # t\<^sub>1) (e\<^sub>2 # t\<^sub>2) =
  (if e\<^sub>1 = e\<^sub>2
    then
      if e\<^sub>1 \<in> cs 
        then {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 t\<^sub>2)
        else
          ({[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))) \<union>
          ({[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))
    else
      if e\<^sub>1 \<in> cs then
        if e\<^sub>2 \<in> cs then {[]}
        else
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2)
      else
        if e\<^sub>2 \<in> cs then
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))
        else
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)) \<union>
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))"

abbreviation tr_inter :: "'\<theta> list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list set" (infixr "|||\<^sub>t" 100) where
"x |||\<^sub>t y \<equiv> tr_par {} x y"

subsection {* Lifted Trace Merge *}

syntax "_utr_par" ::
  "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(_ \<star>\<^bsub>_\<^esub>/ _)" [100, 0, 101] 100)

text {* The function @{const trop} is used to lift ternary operators. *}

translations
  "t1 \<star>\<^bsub>cs\<^esub> t2" == "(CONST bop) (CONST tr_par cs) t1 t2"

subsection {* Trace Merge Lemmas *}

lemma tr_par_empty:
"tr_par cs t1 [] = {takeWhile (\<lambda>x. x \<notin> cs) t1}"
"tr_par cs [] t2 = {takeWhile (\<lambda>x. x \<notin> cs) t2}"
\<comment> \<open> Subgoal 1 \<close>
apply (induct t1; simp)
\<comment> \<open> Subgoal 2 \<close>
apply (induct t2; simp)
done

lemma tr_par_sym:
"tr_par cs t1 t2 = tr_par cs t2 t1"
apply (induct t1 arbitrary: t2)
\<comment> \<open> Subgoal 1 \<close>
apply (simp add: tr_par_empty)
\<comment> \<open> Subgoal 2 \<close>
apply (induct_tac t2)
\<comment> \<open> Subgoal 2.1 \<close>
apply (clarsimp)
\<comment> \<open> Subgoal 2.2 \<close>
apply (clarsimp)
apply (blast)
done

lemma tr_inter_sym: "x |||\<^sub>t y = y |||\<^sub>t x"
  by (simp add: tr_par_sym)
    
lemma trace_merge_nil [simp]: "x \<star>\<^bsub>{}\<^esub> U([]) = {x}\<^sub>u"
  by (pred_auto, simp_all add: tr_par_empty, metis takeWhile_eq_all_conv)

lemma trace_merge_empty [simp]:
  "(U([]) \<star>\<^bsub>cs\<^esub> U([])) = U({[]})"
  by (rel_auto)

lemma trace_merge_single_empty [simp]:
  "a \<in> cs \<Longrightarrow> U([\<guillemotleft>a\<guillemotright>]) \<star>\<^bsub>cs\<^esub> U([]) = U({[]})"
  by (rel_auto)

lemma trace_merge_empty_single [simp]:
  "a \<in> cs \<Longrightarrow> U([]) \<star>\<^bsub>cs\<^esub> U([\<guillemotleft>a\<guillemotright>]) = U({[]})"
  by (rel_auto)
    
lemma trace_merge_commute: "t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 = t\<^sub>2 \<star>\<^bsub>cs\<^esub> t\<^sub>1"
  by (rel_simp, simp add: tr_par_sym)
   
lemma csp_trace_simps [simp]: 
  "U(v + []) = v" "U([] + v) = v"
  "bop (#) x xs ^\<^sub>u ys = bop (#) x (xs ^\<^sub>u ys)"
  by (rel_auto)+

text \<open> Alternative characterisation of traces, adapted from CSP-Prover \<close>

inductive_set
  parx :: "'a set => ('a list * 'a list * 'a list) set"
  for X :: "'a set"

where
parx_nil_nil [intro]: 
  "([], [], []) \<in> parx X" |

parx_Ev_nil [intro]: 
  "[| (u, s, []) \<in> parx X ; a \<notin> X |]
   ==> (a # u, a # s, []) \<in> parx X" |

parx_nil_Ev [intro]: 
  "[| (u, [], t) \<in> parx X ; a \<notin> X |]
   ==> (a # u, [], a # t) \<in> parx X" |

parx_Ev_sync [intro]: 
  "[| (u, s, t) \<in> parx X ; a \<in> X |]
   ==> (a # u, a # s, a # t) \<in> parx X" |

parx_Ev_left [intro]: 
  "[| (u, s, t) \<in> parx X ; a \<notin> X |]
   ==> (a # u, a # s, t) \<in> parx X" |

parx_Ev_right [intro]: 
  "[| (u, s, t) \<in> parx X ; a \<notin> X |]
   ==> (a # u, s, a # t) \<in> parx X"

lemma parx_implies_tr_par: "(t, t\<^sub>1, t\<^sub>2) \<in> parx cs \<Longrightarrow> t \<in> tr_par cs t\<^sub>1 t\<^sub>2"
  apply (induct rule: parx.induct)
       apply (auto)
   apply (case_tac t)
    apply (auto)
  apply (case_tac s)
   apply (auto)
  done

end