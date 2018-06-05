section {* Circus Trace Merge *}

theory utp_circus_traces
  imports "UTP-Stateful-Failures.utp_sf_rdes"
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
      if e\<^sub>1 \<in> cs (* \<and> e\<^sub>2 \<in> cs *)
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
-- {* Subgoal 1 *}
apply (induct t1; simp)
-- {* Subgoal 2 *}
apply (induct t2; simp)
done

lemma tr_par_sym:
"tr_par cs t1 t2 = tr_par cs t2 t1"
apply (induct t1 arbitrary: t2)
-- {* Subgoal 1 *}
apply (simp add: tr_par_empty)
-- {* Subgoal 2 *}
apply (induct_tac t2)
-- {* Subgoal 2.1 *}
apply (clarsimp)
-- {* Subgoal 2.2 *}
apply (clarsimp)
apply (blast)
done

lemma tr_inter_sym: "x |||\<^sub>t y = y |||\<^sub>t x"
  by (simp add: tr_par_sym)
    
lemma trace_merge_nil [simp]: "x \<star>\<^bsub>{}\<^esub> \<langle>\<rangle> = {x}\<^sub>u"
  by (pred_auto, simp_all add: tr_par_empty, metis takeWhile_eq_all_conv)

lemma trace_merge_empty [simp]:
  "(\<langle>\<rangle> \<star>\<^bsub>cs\<^esub> \<langle>\<rangle>) = {\<langle>\<rangle>}\<^sub>u"
  by (rel_auto)

lemma trace_merge_single_empty [simp]:
  "a \<in> cs \<Longrightarrow> \<langle>\<guillemotleft>a\<guillemotright>\<rangle> \<star>\<^bsub>cs\<^esub> \<langle>\<rangle> = {\<langle>\<rangle>}\<^sub>u"
  by (rel_auto)

lemma trace_merge_empty_single [simp]:
  "a \<in> cs \<Longrightarrow> \<langle>\<rangle> \<star>\<^bsub>cs\<^esub> \<langle>\<guillemotleft>a\<guillemotright>\<rangle> = {\<langle>\<rangle>}\<^sub>u"
  by (rel_auto)
    
lemma trace_merge_commute: "t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 = t\<^sub>2 \<star>\<^bsub>cs\<^esub> t\<^sub>1"
  by (rel_simp, simp add: tr_par_sym)
   
lemma csp_trace_simps [simp]: 
  "v ^\<^sub>u \<langle>\<rangle> = v" "\<langle>\<rangle> ^\<^sub>u v = v"
  "v + \<langle>\<rangle> = v" "\<langle>\<rangle> + v = v"
  "bop (op #) x xs ^\<^sub>u ys = bop (op #) x (xs ^\<^sub>u ys)"
  by (rel_auto)+

end