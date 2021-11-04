(* Author: Nan Jiang *)


section \<open>Properties of the kildall's algorithm on the semilattice \<close>

theory Dom_Kildall_Property
imports Dom_Kildall  
begin

lemma sorted_list_len_lt: "x \<subset> y \<Longrightarrow> finite y \<Longrightarrow> length (sorted_list_of_set x) < length (sorted_list_of_set y)" 
proof-
  let ?x = "sorted_list_of_set x"
  let ?y = "sorted_list_of_set y" 
  assume x_y: "x \<subset> y" and fin_y: "finite y" 
  then have card_x_y: "card x < card y" and fin_x: "finite x" 
    by (auto simp add:psubset_card_mono finite_subset)
  with fin_y have "length ?x = card x" and "length ?y = card y" by auto
  with card_x_y show ?thesis by auto
qed

lemma wf_sorted_list: 
  "wf ((\<lambda>(x,y). (sorted_list_of_set x, sorted_list_of_set y)) ` finite_psubset)"
  apply (unfold finite_psubset_def)
  apply (rule wf_measure [THEN wf_subset])
  apply (simp add: measure_def inv_image_def image_def)
  by (auto intro: sorted_list_len_lt)

lemma sorted_list_psub: 
  "sorted w \<longrightarrow>
   w \<noteq> [] \<longrightarrow>
   (sorted_list_of_set (set (tl w)), w) \<in> (\<lambda>(x, y). (sorted_list_of_set x, sorted_list_of_set y)) ` {(A, B). A \<subset> B \<and> finite B}"
proof(intro strip, simp add:image_iff)
  assume sorted_w: "sorted w" and w_n_nil: "w \<noteq> []" 
  let ?a = "set (tl w)" 
  let ?b = "set w" 

  from sorted_w have sorted_tl_w: "sorted (tl w)" and dist: "distinct w" by (induct w) (auto simp add: sorted_wrt_append )  
  with w_n_nil  have a_psub_b: "?a \<subset> ?b" by (induct w)auto
  from sorted_w sorted_tl_w have "w = sorted_list_of_set ?b" and "tl w = sorted_list_of_set (set (tl w))" 
    by (auto simp add: sorted_less_set_eq)
  with a_psub_b show "\<exists>a b. a \<subset> b \<and> finite b \<and> sorted_list_of_set (set (tl w)) = sorted_list_of_set a \<and> w = sorted_list_of_set b"
    by auto  
qed

primrec merges :: "'s binop \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> 's list"
where
  "merges f []      \<tau>s = \<tau>s"
| "merges f (p'#ps) \<tau>s = (let (p,\<tau>) = p' in merges f ps (\<tau>s[p := \<tau> \<squnion>\<^bsub>f\<^esub> \<tau>s!p]))"

locale dom_sl = cfg_doms +
  fixes A and r and f and step and start and n 
  defines "A  \<equiv> ((rev \<circ> sorted_list_of_set) ` (Pow (set (nodes))))" 
  defines "r  \<equiv> nodes_le"
  defines "f  \<equiv> nodes_sup"
  defines "n  \<equiv> (size nodes)"
  defines "step \<equiv> exec" 
  defines "start \<equiv> ([] # (replicate (length (g_V G) - 1) ( (rev[0..<n]))))::state_dom list "

begin 

lemma is_semi: "semilat(A,r,f)" 
  by(insert nodes_semi_is_semilat) (auto simp add:nodes_semi_def A_def r_def f_def)

\<comment>\<open>used by acc\_le\_listI\<close>
lemma Cons_less_Conss [simp]:
  "x#xs [\<sqsubset>\<^sub>r] y#ys = (x \<sqsubset>\<^sub>r y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<or> x = y \<and> xs [\<sqsubset>\<^sub>r] ys)"
proof(unfold lesssub_def, rule iffI)
  assume "x # xs [\<sqsubseteq>\<^bsub>r\<^esub>] y # ys \<and> x # xs \<noteq> y # ys " 
  then have ass1: "x # xs [\<sqsubseteq>\<^bsub>r\<^esub>] y # ys" and ass2:"x # xs \<noteq> y # ys " by auto
  from ass1 have g1: "x \<sqsubseteq>\<^bsub>r\<^esub> y" and g2: "xs [\<sqsubseteq>\<^bsub>r\<^esub>]  ys" by auto

  from ass2 have "x \<noteq> y \<or> x = y \<and> xs \<noteq> ys" by auto
  then show "(x \<sqsubseteq>\<^bsub>r\<^esub> y \<and> x \<noteq> y) \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<or> x = y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<and> xs \<noteq> ys"
  proof
    assume "x \<noteq> y" 
    with g1 g2 have "(x \<sqsubseteq>\<^bsub>r\<^esub> y \<and> x \<noteq> y) \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys " by auto
    then show ?thesis by auto
  next
    assume "x = y \<and> xs \<noteq> ys " 
    then have "x = y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<and> xs \<noteq> ys" using  g2 by auto
    then show ?thesis by auto
  qed
next
  assume  ass:"((x \<sqsubseteq>\<^bsub>r\<^esub> y \<and> x \<noteq> y) \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys) \<or> (x = y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<and> xs \<noteq> ys)"
  from ass show "x # xs [\<sqsubseteq>\<^bsub>r\<^esub>] y # ys \<and> x # xs \<noteq> y # ys"
  proof
    assume "(x \<sqsubseteq>\<^bsub>r\<^esub> y \<and> x \<noteq> y) \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys " 
    then have "x \<sqsubseteq>\<^bsub>r\<^esub> y \<and> x \<noteq> y" and ass1: "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys " by auto
    then have ass2: "x \<sqsubseteq>\<^bsub>r\<^esub> y" and ass3: " x \<noteq> y" by auto
    from ass3 have g2: "x # xs \<noteq> y # ys" by auto
    from ass1 ass2 have g1: "x # xs [\<sqsubseteq>\<^bsub>r\<^esub>] y # ys" by auto
    with g2 show "x # xs [\<sqsubseteq>\<^bsub>r\<^esub>] y # ys \<and> x # xs \<noteq> y # ys" by auto
  next
    assume "x = y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<and> xs \<noteq> ys "
    then have "x = y" and "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys " and " xs \<noteq> ys " by auto
    then have g2: "x # xs \<noteq> y # ys" by auto
   
    from `x = y` have "x \<sqsubseteq>\<^bsub>r\<^esub> y"  by(simp add: lesssub_def lesub_def r_def nodes_le_def )
    with `xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys` have g1: "x # xs [\<sqsubseteq>\<^bsub>r\<^esub>] y # ys" by auto
   with g2 show " x # xs [\<sqsubseteq>\<^bsub>r\<^esub>] y # ys \<and> x # xs \<noteq> y # ys" by auto
  qed
qed

lemma acc_le_listI [intro!]:
  "acc r \<Longrightarrow> acc (Listn.le r) "
  apply (unfold acc_def)
  apply (subgoal_tac "Wellfounded.wf(UN n. {(ys,xs).  size xs = n \<and> size ys = n \<and> xs <_(Listn.le r) ys})")
   apply (erule wf_subset)
   apply (blast intro: lesssub_lengthD)
  apply (rule wf_UN)
   prefer 2
   apply (rename_tac m n)
   apply (case_tac "m=n")
    apply simp
   apply (fast intro!: equals0I dest: not_sym)
  apply (rename_tac n)
  apply (induct_tac n)
   apply (simp add: lesssub_def cong: conj_cong)
  apply (rename_tac k)
  apply (simp add: wf_eq_minimal)
  apply (simp (no_asm) add: length_Suc_conv cong: conj_cong)
  apply clarify
  apply (rename_tac M m)
  apply (case_tac "\<exists>x xs. size xs = k \<and> x#xs \<in> M")
   prefer 2
   apply (erule thin_rl)
   apply (erule thin_rl)
   apply blast
  apply (erule_tac x = "{a. \<exists>xs. size xs = k \<and> a#xs:M}" in allE)
  apply (erule impE)
   apply blast
  apply (thin_tac "\<exists>x xs. P x xs" for P)
  apply clarify
  apply (rename_tac maxA xs)
  apply (erule_tac x = "{ys. size ys = size xs \<and> maxA#ys \<in> M}" in allE)
  apply (erule impE)
   apply blast
  apply clarify
  apply (thin_tac "m \<in> M")
  apply (thin_tac "maxA#xs \<in> M")
  apply (rule bexI)
   prefer 2
   apply assumption
  apply clarify
  apply simp
  apply blast
  done

lemma wf_listn: "wf {(y,x). x \<sqsubset>\<^bsub>Listn.le r\<^esub> y}" 
  by(insert acc_nodes_le acc_le_listI r_def)  (simp add:acc_def)

lemma wf_listn': "wf {(y,x). x [\<sqsubset>\<^sub>r] y}" 
  by (rule wf_listn)

lemma wf_listn_termination_rel: 
  "wf ({(y,x). x \<sqsubset>\<^bsub>Listn.le r\<^esub> y}  <*lex*> (\<lambda>(x, y). (sorted_list_of_set x, sorted_list_of_set y)) ` finite_psubset)"
  by (insert wf_listn wf_sorted_list)  (fastforce dest:wf_lex_prod)

lemma inA_is_sorted: "xs \<in> A \<Longrightarrow> sorted (rev xs)" 
  by (auto simp add:A_def sorted_less_sorted_list_of_set)

lemma list_nA_lt_refl: "xs \<in> list n A \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] xs"
proof
  assume "xs \<in> list n A"
  then have "set xs \<subseteq> A" by (rule listE_set)
  then have "\<forall>i<length xs. xs!i \<in> A" by auto
  then have "\<forall>i<length xs. sorted (rev (xs!i))" by (simp add:inA_is_sorted)
  then show "xs [\<sqsubseteq>\<^bsub>r\<^esub>] xs" by(unfold Listn.le_def lesub_def) 
     (auto simp add:list_all2_conv_all_nth Listn.le_def r_def nodes_le_def) 
qed

lemma nil_inA: "[] \<in> A"
  apply (unfold A_def)
  apply (subgoal_tac "{} \<in> Pow (set nodes)")
  apply (subgoal_tac "[] = (\<lambda>x. rev (sorted_list_of_set x)) {}")
    apply (fastforce intro:rev_image_eqI)
  by auto

lemma upt_n_in_pow_nodes: "{0..<n} \<in> Pow (set nodes)" 
  by(auto simp add:n_def nodes_def verts_set)

lemma rev_all_inA: "rev [0..<n] \<in> A"
proof(unfold A_def,simp)
  let ?f = "\<lambda>x. rev (sorted_list_of_set x)" 
  have "rev [0..<n] =?f {0..<n}" by auto
  with upt_n_in_pow_nodes show "rev [0..<n] \<in> ?f ` Pow (set nodes)" 
    by (fastforce intro: image_eqI)
qed

lemma len_start_is_n: "length start = n" 
  by (insert len_verts_gt0) (auto simp add:start_def n_def nodes_def dest:Suc_pred)

lemma len_start_is_len_verts: "length start = length (g_V G)" 
  using len_verts_gt0 by (simp add:start_def)

lemma start_len_gt_0: "length start > 0" 
  by (insert len_verts_gt0) (simp add:start_def) 

lemma start_subset_A: "set start \<subseteq> A" 
  by(auto simp add:nil_inA rev_all_inA start_def)

lemma start_in_A : "start \<in> (list n A)" 
  by (insert start_subset_A len_start_is_n)(fastforce intro:listI)

lemma sorted_start_nth: "i < n \<Longrightarrow> sorted (rev (start!i))" 
  apply(subgoal_tac "start!i \<in> A")    
  apply (fastforce dest:inA_is_sorted)
  by (auto simp add:start_subset_A  len_start_is_n)

lemma start_nth0_empty: "start!0 = []"
  by (simp add:start_def)

lemma start_nth_lt0_all: "\<forall>p\<in>{1..< length start}. start!p = (rev [0..<n])" 
  by (auto simp add:start_def)
                                                          
lemma in_nodes_lt_n: "x \<in> set (g_V G) \<Longrightarrow> x < n" 
  by (simp add:n_def nodes_def verts_set)

lemma start_nth0_unstable_auxi: "\<not> [0] \<sqsubseteq>\<^bsub>r\<^esub> (rev [0..<n])"  
  by (insert len_verts_gt1 verts_ge_Suc0)
  (auto simp add:r_def lesssub_def lesub_def nodes_le_def n_def nodes_def)
                                                          
lemma start_nth0_unstable: "\<not> stable r step start 0" 
proof(rule notI,auto simp add: start_nth0_empty stable_def step_def exec_def transf_def) 
  assume ass: "\<forall>x\<in>set (sorted_list_of_set (succs 0)). [0] \<sqsubseteq>\<^bsub>r\<^esub> start ! x"
  from succ_of_entry0 obtain s where "s \<in> succs 0" and "s \<noteq> 0 \<and> s \<in> set (g_V G)" using head_is_vert 
    by (auto simp add:succs_def)
  then have "s \<in> set (sorted_list_of_set (succs 0))" 
        and "start!s = (rev [0..<n])" using fin_succs verts_set len_verts_gt0 by (auto simp add:start_def)
  then show False using ass start_nth0_unstable_auxi by auto
qed

lemma start_nth_unstable: 
  assumes "p \<in> {1 ..< length (g_V G)} "
      and "succs p \<noteq> {}"
    shows "\<not> stable r step start p" 
proof (rule notI, unfold stable_def)  
  let ?step_p = "step p (start ! p)"
  let ?rev_all = "rev[0..<length(g_V G)]"
  assume sta: "\<forall>(q, \<tau>)\<in>set ?step_p. \<tau> \<sqsubseteq>\<^bsub>r\<^esub> start ! q"  

  from assms(1) have n_sorted: "\<not> sorted (rev (p # ?rev_all))"    
                 and p:"p \<in> set (g_V G)" and "start!p = ?rev_all" using verts_set by (auto simp add:n_def nodes_def start_def sorted_wrt_append)  
  with sta have step_p: "\<forall>(q, \<tau>)\<in>set ?step_p. sorted (rev (p # ?rev_all)) \<or> (p # ?rev_all = start!q)" 
    by (auto simp add:step_def exec_def transf_def lesssub_def lesub_def r_def nodes_le_def)
  
  from assms(2) fin_succs p obtain a b where a_b: "(a, b) \<in> set ?step_p" by (auto simp add:step_def exec_def transf_def)
  with step_p have "sorted (rev (p # ?rev_all)) \<or> (p # ?rev_all = start!a)" by auto
  with n_sorted have eq_p_cons: "(p # ?rev_all = start!a)" by auto
 
  from p have "\<forall>(q, \<tau>)\<in>set ?step_p. q < n" using succ_in_G fin_succs verts_set n_def nodes_def by (auto simp add:step_def exec_def)
  with a_b have "a < n" using len_start_is_n by auto
  then have "sorted (rev (start!a))" using sorted_start_nth by auto
  with eq_p_cons n_sorted show False  by auto

qed

lemma start_unstable_cond: 
  assumes "succs p \<noteq> {} "
      and "p < length (g_V G)"
    shows "\<not> stable r step start p"  
  using assms start_nth0_unstable start_nth_unstable 
  by(cases "p = 0")  auto

lemma unstable_start: "unstables r step start = sorted_list_of_set ({p. succs p \<noteq> {} \<and> p < length start})"
  using len_start_is_len_verts start_unstable_cond
  by (subgoal_tac "{p. p < length start \<and> \<not> stable r step start p} = {p. succs p \<noteq> {} \<and> p < length start}")
     (auto simp add: unstables_def stable_def step_def exec_def)

lemma nth_merges:
 "\<And>ss. \<lbrakk>p < length ss; ss \<in> list n A; \<forall>(p,t)\<in>set ps. p<n \<and> t\<in>A \<rbrakk> \<Longrightarrow>
  (merges f ps ss)!p = map snd [(p',t') \<leftarrow> ps. p'=p] \<Squnion>\<^bsub>f\<^esub> ss!p"
  (is "\<And>ss. \<lbrakk>_; _; ?steptype ps\<rbrakk> \<Longrightarrow> ?P ss ps")
(*<*)
proof (induct ps)
  show "\<And>ss. ?P ss []" by simp

  fix ss p' ps'
  assume ss: "ss \<in> list n A"
  assume l:  "p < length ss"
  assume "?steptype (p'#ps')"
  then obtain a b where
    p': "p'=(a,b)" and ab: "a<n" "b\<in>A" and ps': "?steptype ps'"
    by (cases p') auto
  assume "\<And>ss. p< length ss \<Longrightarrow> ss \<in> list n A \<Longrightarrow> ?steptype ps' \<Longrightarrow> ?P ss ps'"
  hence IH: "\<And>ss. ss \<in> list n A \<Longrightarrow> p < length ss \<Longrightarrow> ?P ss ps'" using ps' by iprover

  from is_semi have "closed  A f" by (simp add:semilat_def)
  with ss ab
  have "ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a] \<in> list n A" by (simp add:closedD)
  moreover
  with l have "p < length (ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a])" by simp
  ultimately
  have "?P (ss[a := b \<squnion>\<^bsub>f\<^esub> ss!a]) ps'" by (rule IH)
  with p' l
  show "?P ss (p'#ps')" by simp
qed

lemma length_merges [simp]:
  "\<And>ss. size(merges f ps ss) = size ss"
(*<*) by (induct ps, auto) (*>*)

lemma merges_preserves_type_lemma:
shows "\<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A) \<longrightarrow> merges f ps xs \<in> list n A"
  apply(insert is_semi)
  apply (unfold semilat_def)
  apply (unfold closed_def)
  apply (induct ps)
   apply simp
  apply clarsimp  
  done

lemma merges_preserves_type [simp]:
 "\<lbrakk> xs \<in> list n A; \<forall>(p,x) \<in> set ps. p<n \<and> x\<in>A \<rbrakk> \<Longrightarrow> merges f ps xs \<in> list n A"
by (simp only: merges_preserves_type_lemma)

declare sorted_list_of_set_insert[simp del]                                      

lemmas [simp] = Let_def Semilat.le_iff_plus_unchanged [OF Semilat.intro, symmetric]

lemma decomp_propa: "\<And>ss w. 
   (\<forall>(q,t)\<in>set qs. q < size ss \<and> t \<in> A ) \<Longrightarrow> 
   sorted w \<Longrightarrow> 
   set ss \<subseteq> A \<Longrightarrow> 
   propa f qs ss w = (merges f qs ss, (sorted_list_of_set ({q. \<exists>t.(q,t)\<in>set qs \<and> t \<squnion>\<^bsub>f\<^esub> (ss!q) \<noteq> ss!q} \<union> set w)))"
(*<*)
  apply (induct qs)
   apply (fastforce intro:sorted_less_set_eq)
  apply (simp (no_asm))
  apply clarify 
  apply (simp add: sorted_less_sorted_list_of_set Semilat.closed_f[OF Semilat.intro, OF is_semi])
  apply (rule conjI)   
   apply (blast intro: arg_cong)
  apply(simp add: nth_list_update)
  by (auto intro: arg_cong)

lemma distinct_pair_filter_n: "distinct (map fst xs) \<Longrightarrow> a \<notin> set (map fst xs) \<Longrightarrow> (map snd (filter (\<lambda>(x,y). x = a) xs)) = []"
  by (induct xs) (auto simp add: distinct_map_filter image_def)

lemma map_fst: "map fst (map (\<lambda>pc. (pc, x)) xs) =  xs" 
  by (induct xs) auto

lemma distinct_p: "p < n \<longrightarrow> distinct (map fst (step p (ss!p)))" 
proof-
  let ?qs = "step p (ss!p)" 
  have "map fst ?qs = (rev (sorted_list_of_set(succs p)))" 
    using map_fst[of _ "(rev (sorted_list_of_set(succs p)))"] by (auto simp add:step_def exec_def)
  then show ?thesis by auto
qed

lemma distinct_pair_filter: "distinct (map fst xs) \<Longrightarrow> (a,b)\<in> set xs \<Longrightarrow> map snd (filter (\<lambda>x. fst x = a) xs) = [b]"
  apply (induct xs)
   apply simp
  apply (auto simp add: distinct_map_filter image_def)
proof-
  {
    fix xs
    assume "\<forall>x\<in>set xs. a \<noteq> fst x " and " distinct (map fst xs)"
    then show "filter (\<lambda>x. fst x = a) xs = []" by (induct xs)  auto
  }
qed

lemma split_comp_eq_pair: "(\<lambda>x. fst x = a) = (\<lambda>(x,y). x = a)"
  by (rule split_comp_eq)

lemma distinct_pair_filter': "distinct (map fst xs) \<Longrightarrow> (a,b)\<in> set xs \<Longrightarrow> (map snd (filter (\<lambda>(x,y). x = a) xs)) = [b]"
  using distinct_pair_filter by (simp only: split_comp_eq_pair)

lemma merges_property1: 
  fixes ss w qs
  assumes step_bounded_pres: "\<forall>(q, \<tau>) \<in> set qs. q < size ss \<and> \<tau> \<in> A"
      and subset_ss_A:       "set ss \<subseteq> A "
      and len_ss_n:          "length ss = n "
      and dist:              "distinct (map fst qs) "
    shows "\<forall>(q, \<tau>) \<in> set qs. merges f qs ss!q = \<tau> \<squnion>\<^bsub>f\<^esub>ss!q" 
proof
  fix x
  assume "x \<in> set qs"
  from dist have \<tau>: "\<forall>(q, \<tau>) \<in> set qs. (map snd (filter (\<lambda>(x,y). x = q) qs)) = [\<tau>]" using distinct_pair_filter' by fastforce  
  from len_ss_n subset_ss_A have "ss \<in> list n A" by (rule listI)
  with step_bounded_pres have merge_nth: "\<forall>(q, \<tau>) \<in> set qs. (merges f qs ss)!q = map snd [(p',t') \<leftarrow> qs. p'=q] \<Squnion>\<^bsub>f\<^esub> ss!q" 
    by (fastforce intro:nth_merges) \<comment> \<open>use lemma:  listE_length\<close>
  with \<tau> have "\<forall>(q, \<tau>) \<in> set qs. (merges f qs ss)!q = [\<tau>]\<Squnion>\<^bsub>f\<^esub> ss!q" by fastforce
  then show "case x of (q, \<tau>) \<Rightarrow> merges f qs ss ! q = \<tau> \<squnion>\<^bsub>f\<^esub> ss ! q" using `x \<in> set qs` by auto  
qed

lemma propa_property1: 
  fixes ss w qs
  assumes step_bounded_pres: "\<forall>(q, \<tau>) \<in> set qs. q < size ss \<and> \<tau> \<in> A  "
      and sorted_w:          "sorted (w ::nat list)"
      and subset_ss_A:       "set ss \<subseteq> A "
      and len_ss_n:          "length ss = n "
      and dist:              "distinct (map fst qs) "
    shows "\<forall>(q, \<tau>) \<in> set qs. (fst(propa f qs ss w))!q = \<tau> \<squnion>\<^bsub>f\<^esub>ss!q" 
  using assms
  apply (subgoal_tac "fst (propa f qs ss w) = merges f qs ss")
   apply(simp add: merges_property1) 
  by (auto dest:decomp_propa)

lemma merges_property2: 
  fixes ss w qs q
  assumes step_bounded_pres: "\<forall>(q, \<tau>) \<in> set qs. q < size ss \<and> \<tau> \<in> A"
      and subset_ss_A:       "set ss \<subseteq> A"
      and len_ss_n:          "length ss = n "
      and dist:              "distinct (map fst qs) "
      and q_nin:             "q \<notin> set(map fst qs) "
      and q_lt_len_ss:       "q < length ss "
    shows "(merges f qs ss)!q = ss!q" 
proof- 
  from len_ss_n subset_ss_A have "ss \<in> list n A" by (rule listI)
  with step_bounded_pres q_lt_len_ss have merge_nth: "(merges f qs ss)!q = map snd [(p',t') \<leftarrow> qs. p'=q] \<Squnion>\<^bsub>f\<^esub> ss!q" by (fastforce intro:nth_merges)
  from dist have "q \<notin> set(map fst qs) \<Longrightarrow> (map snd (filter (\<lambda>(x,y). x = q) qs)) = []" using distinct_pair_filter_n by fastforce
  with merge_nth q_nin have "(merges f qs ss)!q = []\<Squnion>\<^bsub>f\<^esub> ss!q" by fastforce
  then show "(merges f qs ss)!q =  ss ! q" by auto  
qed

lemma propa_property2: 
  fixes ss w qs q
  assumes step_bounded_pres: "\<forall>(q, \<tau>) \<in> set qs. q < size ss \<and> \<tau> \<in> A"
      and sorted_w:          "sorted (w ::nat list)"
      and subset_ss_A:       "set ss \<subseteq> A"
      and len_ss_n:          "length ss = n "
      and dist:              "distinct (map fst qs) "
      and q_nin:             "q \<notin> set(map fst qs) "
      and q_lt_len_ss:       "q < length ss "
    shows "(fst(propa f qs ss w))!q = ss!q" 
  using assms
  apply (subgoal_tac "fst (propa f qs ss w) = merges f qs ss")
   apply(simp add: merges_property2) 
  by (auto dest:decomp_propa)

lemma merges_incr_lemma:
 "\<forall>xs. xs \<in> list n A \<longrightarrow> distinct (map fst ps) \<longrightarrow> (\<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A) \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] merges f ps xs"
proof(intro strip)
  fix xs
  assume xs_inA: "xs \<in> list n A " 
     and step_bounded_pres: "\<forall>(p, x)\<in>set ps. p < length xs \<and> x \<in> A"
     and dist: "distinct (map fst ps)" 
  then have len_xs_n: "length xs = n" and subset_xs_inA: "set xs \<subseteq> A" by (auto simp add:listE_length)
  with step_bounded_pres dist have merge1: "\<forall>(q, \<tau>) \<in> set ps. (merges f ps xs)!q = \<tau> \<squnion>\<^bsub>f\<^esub>xs!q" 
    using merges_property1 by auto

  from step_bounded_pres dist len_xs_n subset_xs_inA  
  have merge2: "\<And>q. q \<notin> set(map fst ps) \<longrightarrow> q < length xs \<longrightarrow> (merges f ps xs)!q = xs!q" using merges_property2 by auto
  
  have len_eq: "length xs = length (merges f ps xs)" by simp

  have "\<forall>i<length xs. xs!i \<sqsubseteq>\<^bsub>r\<^esub> (merges f ps xs)!i" 
  proof(intro strip)
    fix i
    assume i_lt_len_xs: "i < length xs" 
    with xs_inA have xs_i_inA: "xs!i \<in> A" by auto

    show " xs ! i \<sqsubseteq>\<^bsub>r\<^esub> (merges f ps xs) ! i "
    proof(cases "i \<in> set (map fst ps)")
      case True
      then  obtain s' where s': "(i, s') \<in> set ps" by auto
      with merge1 have merge1': "(merges f ps xs)!i = s' \<squnion>\<^bsub>f\<^esub> xs ! i" by auto
      from s' step_bounded_pres have "s' \<in> A" by auto      
      with xs_i_inA merge1' show ?thesis  by (auto intro: Semilat.ub2[OF Semilat.intro, OF is_semi])
    next
      case False note i_nin = this
      with i_lt_len_xs merge2  have "(merges f ps xs)!i = xs!i" by auto
      with xs_i_inA show ?thesis by (auto simp add:Semilat.refl_r[OF Semilat.intro, OF is_semi])
    qed
  qed
  then have "\<forall>i<length xs. xs!i \<sqsubseteq>\<^bsub>r\<^esub> (merges f ps xs)!i" by auto
  then have "\<forall>i<length xs. lesub (xs!i) r  ((merges f ps xs)!i)" by (auto simp add:lesssub_def lesub_def)
  then have  "\<forall>i<length xs. (\<lambda>x y. lesub x r y) (xs!i)((merges f ps xs)!i)" by simp
  then have nth_lt: "\<And>i. i <length xs \<Longrightarrow>  (\<lambda>x y. lesub x r y) (xs!i)((merges f ps xs)!i)" by simp 
  with len_eq show "xs [\<sqsubseteq>\<^bsub>r\<^esub>] merges f ps xs" 
    by (auto simp only:list_all2_conv_all_nth Listn.le_def lesssub_def lesub_def) 
qed
   
lemma merges_incr:
 "\<lbrakk> xs \<in> list n A; distinct (map fst ps); \<forall>(p,x)\<in>set ps. p<size xs \<and> x \<in> A \<rbrakk> \<Longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] merges f ps xs"
  by (simp add: merges_incr_lemma)

lemma merges_same_conv [rule_format]:
 "(\<forall>xs. xs \<in> list n A \<longrightarrow> distinct (map fst ps) \<longrightarrow>
        (\<forall>(p,x)\<in>set ps. p<size xs \<and> x\<in>A) \<longrightarrow> 
        (merges f ps xs = xs) = (\<forall>(p,x)\<in>set ps. x \<sqsubseteq>\<^bsub>r\<^esub> xs!p))"
  apply (induct_tac ps)
   apply (simp)
  apply clarsimp
  apply (rename_tac p x ps xs)
  apply (rule iffI)
   apply (rule context_conjI)
    apply (subgoal_tac "xs[p := x \<squnion>\<^bsub>f\<^esub> xs!p] [\<sqsubseteq>\<^bsub>r\<^esub>] xs")
     apply (fastforce dest!: le_listD 
            simp add: nth_list_update Semilat.plus_le_conv[OF Semilat.intro,OF is_semi] 
                      Semilat.ub1[OF Semilat.intro,OF is_semi] 
                      Semilat.ub2[OF Semilat.intro,OF is_semi]
Semilat.lub[OF Semilat.intro,OF is_semi] 
 )
    apply (erule subst, rule merges_incr)
      apply (blast intro!: listE_set intro: closedD listE_length [THEN nth_in]
                            Semilat.closed_f[OF Semilat.intro, OF is_semi])
     apply clarify
  apply(intro strip)
  apply auto
   apply (erule allE)
   apply (erule impE)
    apply assumption
   apply (drule bspec)
    apply assumption
   apply (simp add: Semilat.le_iff_plus_unchanged [OF Semilat.intro, OF is_semi, THEN iffD1] list_update_same_conv [THEN iffD2])
   apply blast
  apply (simp add: Semilat.le_iff_plus_unchanged[OF Semilat.intro, OF is_semi, THEN iffD1] list_update_same_conv [THEN iffD2])
  done
(*>*)

lemma list_update_le_listI [rule_format]:
  "set xs \<subseteq> A \<longrightarrow> set ys \<subseteq> A \<longrightarrow> xs [\<sqsubseteq>\<^sub>r] ys \<longrightarrow> p < size xs \<longrightarrow>  
   x \<sqsubseteq>\<^sub>r ys!p \<longrightarrow> semilat(A,r,f) \<longrightarrow> x\<in>A \<longrightarrow> 
   xs[p := x \<squnion>\<^sub>f xs!p] [\<sqsubseteq>\<^sub>r] ys"
(*<*)
  apply (simp only: Listn.le_def lesub_def semilat_def)
  apply (simp add: list_all2_conv_all_nth nth_list_update)
  done

lemma merges_pres_le_ub:
  assumes "set ts \<subseteq> A"  
          "set ss \<subseteq> A"
          "\<forall>(p,t)\<in>set ps. t \<sqsubseteq>\<^bsub>r\<^esub> ts!p \<and> t \<in> A \<and> p < size ts"  
          "ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts"
  shows "merges f ps ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts"
(*<*)
proof -
  { fix t ts ps
    have
    "\<And>qs. \<lbrakk>set ts \<subseteq> A; \<forall>(p,t)\<in>set ps. t \<sqsubseteq>\<^bsub>r\<^esub> ts!p \<and> t \<in> A \<and> p< size ts \<rbrakk> \<Longrightarrow>
          set qs \<subseteq> set ps \<longrightarrow> (\<forall>ss. set ss \<subseteq> A \<longrightarrow> ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts \<longrightarrow> merges f qs ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts)"
    apply (induct_tac qs)
     apply simp
    apply (simp (no_asm_simp))
    apply clarify
    apply simp
    apply (erule allE, erule impE, erule_tac [2] mp)
       apply (drule bspec, assumption)
     apply (simp add: closedD  Semilat.closed_f[OF Semilat.intro, OF is_semi])
    apply (drule bspec, assumption)
      apply (simp ) 
      apply(rule list_update_le_listI)
            apply auto
      apply(insert is_semi)
      apply auto
done 
  } note this [dest]  
  from assms show ?thesis by blast
qed
(*>*)

lemma termination_lemma: 
shows "\<lbrakk>ss \<in> list n A; distinct (map fst qs); \<forall>(q,t)\<in>set qs. q<n \<and> t\<in>A; sorted w; w \<noteq> [] \<rbrakk> \<Longrightarrow> 
        ss [\<sqsubset>\<^sub>r] merges f qs ss \<or> 
        merges f qs ss = ss \<and> 
       (sorted_list_of_set ({q. \<exists>t. (q,t)\<in>set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss!q \<noteq> ss!q} \<union> set (tl w)),w) \<in>
       (\<lambda>x. case x of (x, y) \<Rightarrow> (sorted_list_of_set x, sorted_list_of_set y)) ` {(A, B). A \<subset> B \<and> finite B}"
  apply(insert is_semi)
  apply (unfold lesssub_def)
  apply (simp (no_asm_simp) add: merges_incr)
  apply (rule impI)
  apply (rule merges_same_conv [THEN iffD1, elim_format]) 
      apply assumption+
    defer
    apply (rule sym, assumption)
   defer apply simp
  apply (subgoal_tac "\<forall>q t. \<not>((q, t) \<in> set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss ! q \<noteq> ss ! q)")
   defer
   apply clarsimp
   apply (drule bspec, assumption) 
   apply (drule bspec, assumption)
   apply clarsimp      
  apply(subgoal_tac "{q. \<exists>t. (q, t) \<in> set qs \<and> t \<squnion>\<^bsub>f\<^esub> ss ! q \<noteq> ss ! q} \<union> set (tl w) = set (tl w)")
   apply (auto simp add: sorted_list_psub)
  done

lemma bounded_exec: "bounded step n"
  apply (insert is_semi,unfold semilat_def bounded_def step_def exec_def transf_def )
  by (auto simp add: n_def nodes_def verts_set fin_succs' succ_range)

lemma bounded_exec':
  fixes ss w a b
  assumes w_n_nil: " w \<noteq> [] "
       and step_hdw: " (a, b) \<in> set (step (hd w) (ss ! hd w)) "      
       and w_lt_n:"\<forall>p\<in>set w. p < n "
      shows" a < n"
  using assms 
proof-
  from w_lt_n have "hd w < n" using w_n_nil by auto
  with bounded_exec have "( \<forall>\<tau>. \<forall>(q,\<tau>') \<in> set (step (hd w) \<tau>). q<n)" by (auto simp add:bounded_def)
  with step_hdw show "a < n" by auto
qed

definition "wf_dom ss w \<equiv> 
    (\<forall>\<tau>\<in>set ss. \<tau> \<in> A) \<and> 
    (\<forall>p < n. sorted (rev ( (ss!p))) \<and>
             (ss!p \<noteq> rev [0..< n] \<longrightarrow> (\<forall>x\<in>set ( (ss!p)). x < p)) \<and>
             (ss!p = rev [0..<n] \<longrightarrow>  (\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)) \<and>
             (p \<notin> set w \<longrightarrow> stable r step ss p)) \<and>              
    sorted w \<and> length ss = n \<and> (\<forall>x\<in>set w. x < n) "

lemma wf_dom_w: 
  assumes "wf_dom ss w"
  shows "sorted w" 
  using assms
  by (auto simp add:wf_dom_def)

lemma wf_dom_w2: 
  assumes "wf_dom ss w"
  shows "(\<forall>x\<in>set w. x < n)" 
  using assms
  by (auto simp add:wf_dom_def)

lemma wf_dom_len_eq: 
  assumes "wf_dom ss w"
  shows "(length ss = n)" 
  using assms
  by (auto simp add:wf_dom_def)


lemma  wf_dom_inA: 
  assumes "wf_dom ss w"
  shows "ss \<in> list n A" 
  using assms by (auto simp add:wf_dom_def intro: listI)

lemma wf_dom_le: 
  assumes wf_ss_w: "wf_dom ss w"
  shows "ss [\<sqsubseteq>\<^bsub>r\<^esub>] ss" 
  using assms 
proof-
  from wf_ss_w have  "\<forall>i<length ss. ss!i \<in> A" by (auto simp add:wf_dom_def)
  then have  "\<forall>i<length ss. sorted (rev (ss!i))" by (auto simp add:A_def sorted_less_sorted_list_of_set)
  then show ?thesis 
    by (auto simp add:Listn.le_def lesssub_def lesub_def r_def nodes_le_def intro:list_all2_all_nthI)
qed

lemma pres_transf:  
  "\<forall>ss\<in>A. p < n \<longrightarrow> (\<forall>x<length ss. p > ss!x) \<longrightarrow> transf p ss \<in> A" 
proof(intro strip, unfold transf_def)
  fix ss  
  assume  p_lt_n: "p < n" and p_gt:  "\<forall>x<length ss. ss!x < p" and \<tau>_in_A: "ss \<in> A" 
  then have "set ss \<subseteq> set nodes" by (unfold A_def) (rule inpow_subset_nodes)
  with p_lt_n have p_\<tau>_in: "set (p # ss) \<subseteq> set nodes" by (auto simp add:n_def nodes_def verts_set)
  from \<tau>_in_A have sorted_\<tau>: "sorted (rev ss)" by (simp add:inA_is_sorted)
  with p_gt have "sorted (rev (p # ss))" using Cons_sorted_less_nth by auto
  with p_\<tau>_in show "(p # ss) \<in> A" by (unfold A_def) (fastforce intro: subset_nodes_inpow) 
qed

lemma pres_exec: 
  assumes "(q,\<tau>) \<in> set (step p (ss!p))"
      and "\<forall>n \<in> set (ss!p). p > n"
      and "ss!p \<in> A"
      and "p < n" 
    shows "\<tau> \<in> A "
  using assms
 by (auto simp add:step_def exec_def pres_transf)

lemma wf_hd_neq_all: 
  assumes wf_ss_w: "wf_dom ss w " 
      and w_n_nil: "w \<noteq> [] " 
    shows " ss!(hd w) \<noteq> rev [0..<n]" 
proof(rule ccontr)
  assume "\<not> ss ! hd w \<noteq>  (rev [0..<n])" note x = this
  from wf_ss_w have "\<forall>x\<in> set w. x < n" and "sorted w" by (auto simp add:wf_dom_def)
  then have "hd w < n" and y:"\<forall>x \<in> set w. x \<ge> hd w" using w_n_nil by (induct w) (auto simp add:sorted_wrt_append)
  with wf_ss_w x have  "(\<exists>x\<in> set w. (x,hd w)\<in> g_E G \<and> x < hd w)" by (auto simp add:wf_dom_def)  
  with y show False by auto
qed

lemma pres_wf_exec: 
  fixes ss w a b
  assumes wf_ss_w: "wf_dom ss w "
      and w_n_nil: "w \<noteq> [] "
    shows "\<forall>(q,\<tau>) \<in> set (step (hd w) (ss!(hd w))). \<tau> \<in> A "
  using assms
proof(intro strip, auto)
  fix a b
  assume a_b: "(a, b) \<in> set (step (hd w) (ss ! hd w))"
  from wf_ss_w have sorted_w: "sorted w" and hd_w_lt_n: "hd w < n"  
    and ss_hdw_inA: "ss!hd w \<in> A" using w_n_nil by (auto simp add:wf_dom_def)
  from assms have ss_hd_w_neq_all: "ss!hd w \<noteq> (rev [0..<n])" by (rule wf_hd_neq_all)  
  with wf_ss_w hd_w_lt_n have "\<forall>x\<in>set (ss!hd w). hd w > x" by (auto simp add:wf_dom_def)
  with ss_hdw_inA hd_w_lt_n a_b show "b \<in> A"  using pres_exec by auto
qed

lemma propa_dom_invariant_auxi: 
  assumes wf_a_b: "wf_dom a b" and b_n_nil: "b \<noteq> [] " 
    shows "a!hd b \<noteq> rev [0..<n] \<and>
           sorted (rev (hd b # (a!hd b))) \<and>
           set (hd b # (a!hd b)) \<subseteq> set nodes \<and>
           hd b # (a!hd b) \<in> A \<and>
           (\<forall>(q, \<tau>)\<in>set (step (hd b) (a!hd b)). q < length a \<and> \<tau> \<in> A)" 
  using assms
proof-
  from assms have "a!hd b \<in> (rev \<circ> sorted_list_of_set) ` (Pow (set nodes))"
              and  sorted_hdb: "sorted (rev (a!hd b))" 
              and hd_b_lt_n: "hd b < n" 
              and sorted_b: "sorted b" 
              and len_eq: "length a = n" by (auto simp add:A_def wf_dom_def) 
  then have as_subset_nodes: "set (a!hd b) \<subseteq> set nodes" by (auto simp add:inpow_subset_nodes)
  with n_def verts_set assms nodes_def have hdb_cons_subset_nodes: "set (hd b # (a!hd b)) \<subseteq> set nodes" by (auto simp add:wf_dom_def)
  then have hdb_subset_n: "set (hd b # (a!hd b)) \<subseteq> {0..<n}" using nodes_def verts_set n_def by auto

  from wf_a_b b_n_nil have a_hd_b_neq_all: "a!hd b \<noteq> (rev [0..<n])" using wf_hd_neq_all by auto
  with wf_a_b hd_b_lt_n sorted_hdb have sorted_hd_b_cons: "sorted (rev (hd b # (a!hd b)))" 
    by (fastforce simp add: wf_dom_def dest: Cons_sorted_less)

  from hdb_cons_subset_nodes have  "set ((hd b # (a!hd b))) \<in> Pow (set (g_V G))" by (auto simp add:nodes_def)
  then have pow1: "set ((hd b # (a!hd b))) \<subseteq> set nodes" by (auto simp add:nodes_def)
  from hdb_cons_subset_nodes sorted_hd_b_cons have "hd b # (a!hd b) \<in> (rev \<circ> sorted_list_of_set) ` (Pow (set nodes))"
    by (fastforce intro: subset_nodes_inpow)
  then have hd_b_cons_in_A: "(hd b # (a!hd b)) \<in> A" by (unfold A_def ) (auto simp add:nodes_def)  

  have "(\<forall>p<n. \<forall>\<tau>. \<forall>(q,\<tau>') \<in> set (step p \<tau>). q<n)" 
    using bounded_exec by (auto simp add:bounded_def)
  with hd_b_lt_n have bounded: "\<forall>(q,\<tau>') \<in> set (step (hd b) (a!hd b)). q<n" by auto
  from wf_a_b b_n_nil have pres: "\<forall>(q, \<tau>)\<in>set(step (hd b) (a!hd b)). \<tau> \<in> A" by (rule pres_wf_exec)
  with bounded pres have step_pres_bounded: "\<forall>(q, \<tau>)\<in>set (step (hd b) (a!hd b)). q < length a \<and> \<tau> \<in> A " using  len_eq by auto
  with a_hd_b_neq_all sorted_hd_b_cons hdb_cons_subset_nodes hd_b_cons_in_A  show ?thesis by auto
qed

lemma propa_dom_invariant_aux:
  fixes a b ss w
assumes propa: "propa f (step (hd b) (a ! hd b)) a (tl b) = (ss, w) "    
    and b_n_nil: "b \<noteq> [] " 
    and a_in_A: "\<forall>\<tau>\<in>set a. \<tau> \<in> A"   
    and ass: "\<forall>p<n.
          sorted (rev ( (a ! p))) \<and>
          (a!p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set (a!p). x < p)) \<and>
          (a!p = rev [0..<n] \<longrightarrow> (\<exists>x\<in>set b. (x,p)\<in> g_E G \<and> x < p)) \<and>
          (p \<notin> set b \<longrightarrow> stable r step a p)"
    and sorted_b: "sorted b  "
    and len_eq:  "length a = n  "
    and b_lt_n: "\<forall>x\<in>set b. x < n  "
  shows "(\<forall>\<tau>\<in>set ss. \<tau> \<in> A) \<and>
         (\<forall>p<n.
           sorted (rev ( (ss ! p))) \<and>
           (ss!p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set (ss!p). x < p)) \<and>
           (ss!p = rev [0..<n] \<longrightarrow> (\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)) \<and>
           (p \<notin> set w \<longrightarrow> stable r step ss p)) \<and>
         sorted w \<and> length ss = n \<and> (\<forall>x\<in>set w. x <n)"
  using assms 
proof-
  let ?a_hdb = "a!hd b"
  let ?ss_hdw = "ss!hd w"
  let ?ss_hdb = "ss!hd b" 

  let ?a_hdw = "a!hd w" 

  let ?qs_a = "step (hd b) ?a_hdb" 
  let ?qs_ss = "step (hd w) ?ss_hdw" 
  let ?qs_ss_hdb = "step (hd b) ?ss_hdb" 

  let ?q_a_wl = "{q. \<exists>t.(q,t)\<in>set ?qs_a \<and> t \<squnion>\<^bsub>f\<^esub> (a!q) \<noteq> a!q}"
  let ?q_ss_wl = "{q. \<exists>t.(q,t)\<in>set ?qs_ss \<and> t \<squnion>\<^bsub>f\<^esub> (ss!q) \<noteq> ss!q}" 

  from a_in_A len_eq have a_in_list_nA: "a \<in> list n A" by (auto intro: listI)
  from a_in_A have "\<forall>p< length a. a!p \<in> A" by (auto simp add:A_def)
  then have a_p_subset: "\<forall>p< length a. set (a!p) \<subseteq> set nodes" by (auto simp add:inpow_subset_nodes A_def)

  from a_in_A ass sorted_b len_eq b_lt_n  b_n_nil have wf_a_b: "wf_dom a b" by (auto simp add:wf_dom_def)
  with b_n_nil have a_hd_b_neq_all: "?a_hdb \<noteq> rev [0..<n]" 
                and sorted_hd_b_cons: "sorted (rev (hd b # ?a_hdb))"
                and hd_b_cons_in_nodes: "set (hd b # ?a_hdb) \<subseteq> set nodes" 
                and hd_b_cons_in_A: "hd b # ?a_hdb \<in> A"
                and step_pres_bounded: "(\<forall>(q, \<tau>)\<in>set (step (hd b) ?a_hdb). q < length a \<and> \<tau> \<in> A)" 
    using propa_dom_invariant_auxi
    by auto
  then have hdb_subset_n: "set (hd b # ?a_hdb) \<subseteq> {0..<n}" using nodes_def verts_set n_def by auto
  
  from b_lt_n b_n_nil have hd_b_lt_n: "hd b < n" 
                       and tl_b_lt_n: "\<forall>x\<in> set (tl b). x < n" 
    by (induct b)(auto simp add:wf_dom_def)
  then have dist: "distinct (map fst ?qs_a)" using distinct_p  by auto   

  from b_lt_n len_eq sorted_b have sorted_tl_b: "sorted (tl b)" by (induct b) auto 

  from b_lt_n verts n_def nodes_def verts_set have b_in_verts: "\<forall>x\<in>set b. x \<in> set (g_V G)" by auto
  then have hd_b_in_verts: "hd b \<in> set (g_V G)" using b_n_nil by auto
  then  have fin_succ_hd_b: "finite (succs (hd b))" using fin_succs  by auto    

  have fin_q1: "finite {q. \<exists>t.(q,t)\<in>set ?qs_a}" 
   and fin_q2: "finite ?q_a_wl" by (auto simp add:step_def exec_def image_def)
  then have fin: "finite (?q_a_wl \<union> set (tl b))" by auto 
  
  from a_in_A have set_a: "set a \<subseteq> A" by auto
  with step_pres_bounded sorted_tl_b len_eq dist
  have "\<forall>(q, \<tau>) \<in> set ?qs_a. (fst(propa f ?qs_a a (tl b)))!q = \<tau> \<squnion>\<^bsub>f\<^esub>a!q" by (auto dest:propa_property1)
  with propa have propa_ss1: "\<forall>(q, \<tau>) \<in> set ?qs_a. ss!q = \<tau> \<squnion>\<^bsub>f\<^esub>a!q" by simp  
  then have propa_ss1': "\<forall>(q, \<tau>) \<in> set ?qs_a. ss!q =  (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub>a!q" by (auto simp add:step_def exec_def transf_def)
  then have succ_self_eq: "\<forall>(q, \<tau>) \<in> set ?qs_a. q = hd b \<longrightarrow> ss!q = a!q"    
    by(auto simp add: f_def nodes_sup_def plussub_def inter_sorted_cons[OF sorted_hd_b_cons])    

  have step_hd_b: "\<forall>(q,\<tau>)\<in>set ?qs_a. \<tau> = (hd b # ?a_hdb)"
    by(auto simp add:step_def exec_def transf_def) 

  from step_pres_bounded sorted_tl_b set_a len_eq dist 
  have  "\<And>q. q \<notin> set(map fst ?qs_a) \<Longrightarrow> q < length a \<Longrightarrow> (fst(propa f ?qs_a a (tl b)))!q = a!q" 
    by (auto intro:propa_property2)
  with propa have exec2: "\<And>q. q \<notin> set(map fst ?qs_a) \<Longrightarrow> q < length a \<Longrightarrow> ss!q = a!q" by auto
  then have ss_hd_b_eq_a: "ss!hd b = a!hd b" using hd_b_lt_n len_eq  fin_succ_hd_b succ_self_eq
    by (auto simp add:step_def exec_def)  
  then have hdb_nin_w: "hd b \<notin> ?q_a_wl" using fin_succ_hd_b propa_ss1 by (auto simp add:step_def exec_def)

  from step_pres_bounded sorted_tl_b set_a 
  have "snd (propa f ?qs_a a (tl b)) = (sorted_list_of_set (?q_a_wl \<union> set (tl b)))" 
    by (fastforce dest:decomp_propa)
  with propa have ww: "w = sorted_list_of_set (?q_a_wl \<union> set (tl b))" by simp  
  then have sorted_w:"sorted w" by (simp add:sorted_less_sorted_list_of_set)
  from ww have set_ww: "set w =?q_a_wl \<union> set (tl b)" using fin by auto
  with step_pres_bounded tl_b_lt_n ww fin len_eq have w_lt_n: "(\<forall>x\<in>set w. x < n)" using len_eq by auto
  then have w_set': "\<forall>x\<in>set w. x \<in> {0..<n}" using verts_set len_eq  by auto
  then have w_set: "set w \<subseteq> {0..<n}" by auto

  from sorted_b have hd_b_nin_tl_b: "hd b \<notin> set (tl b) " by (induct b) (auto simp add:sorted_wrt_append)
  with hdb_nin_w ww have "hd b \<notin> set w" using fin by auto 

  from step_pres_bounded sorted_tl_b set_a propa have ss_merge: "ss = merges f ?qs_a a" by (auto dest: decomp_propa)
  from step_pres_bounded a_in_list_nA have "\<forall>(q, \<tau>)\<in>set (step (hd b) (a ! hd b)). q < n \<and> \<tau> \<in> A" using len_eq by simp
  with a_in_list_nA have "merges f ?qs_a a  \<in> list n A"  by (rule merges_preserves_type)
  with ss_merge have ss_in_A: "ss \<in> list n A" by simp
  then have len_ss_n: "length ss = n"  using  len_eq by simp
  with len_eq  have len_ss_n: "length ss = n" by auto

  from ss_in_A have set_ss: "set ss \<subseteq> A " by (rule listE_set)
  then have ss_inA:  "\<forall>\<tau>\<in>set ss. \<tau> \<in> A" by auto
  then have ss_p_subset: "\<forall>p< length ss.  set (ss!p) \<subseteq> set nodes" by (auto simp add:inpow_subset_nodes A_def)

  from w_lt_n len_ss_n have bounded_a: "\<And>a b.  w \<noteq> [] \<Longrightarrow> (a, b) \<in> set ?qs_ss \<Longrightarrow> a < length ss" 
    by (auto simp add:bounded_exec') 

  have sorted_a_hdw_n: "w \<noteq> [] \<longrightarrow> sorted (rev ?a_hdw)" 
    using wf_a_b len_eq w_set' by (auto simp add:wf_dom_def)

  have sorted_ss_hdw_n: "w \<noteq> [] \<longrightarrow> sorted (rev ?ss_hdw)" 
    using ss_in_A inA_is_sorted w_lt_n by auto

  have "w \<noteq> [] \<longrightarrow> (hd w # ?ss_hdw) \<in> A"
  proof
    assume w_n_nil: "w \<noteq> []" 
    with w_lt_n have hd_w_lt_n: "hd w < n" by auto   
    with a_in_A have a_hdw_inA: "?a_hdw \<in> A" using len_eq by auto 
    then have a_hdw_in_nodes: "set ?a_hdw \<subseteq> set nodes" by (unfold A_def )(rule inpow_subset_nodes)

    from hd_w_lt_n have hdw_in_nodes: "hd w \<in> set nodes" using verts_set by (simp add:n_def nodes_def) 
    from sorted_a_hdw_n w_n_nil have sorted_a_hdw: "sorted (rev ?a_hdw)" by auto

    show "(hd w # ?ss_hdw) \<in> A"
    proof(cases "hd w \<in> succs (hd b)")
      case True
      then obtain s where s: "(hd w, s) \<in> set ?qs_a" using fin_succ_hd_b  by (auto simp add:step_def exec_def)
      with step_hd_b have "s = (hd b # ?a_hdb)" by auto
      with s propa_ss1 have ss_hd_w: "?ss_hdw = (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_hdw"  by auto
      with hd_b_cons_in_A a_hdw_inA have "?ss_hdw \<in> A" by (simp add: Semilat.closed_f[OF Semilat.intro, OF is_semi])   
      then have ss_hdw_in_nodes: "set ?ss_hdw \<subseteq> set nodes" 
        by (auto simp add:inpow_subset_nodes A_def)       
      with hdw_in_nodes have hdw_cons_ss_in_nodes: "set (hd w # ?ss_hdw) \<subseteq> set nodes" by auto

      then have in_pow: "set (hd w # ?ss_hdw) \<in> Pow (set (g_V G))" by (auto simp add:nodes_def)
          
      from sorted_a_hdw ss_hd_w sorted_hd_b_cons
      have "sorted (rev ?ss_hdw)" and "set ?ss_hdw = set (hd b # ?a_hdb) \<inter> set ?a_hdw" 
        by (auto simp add:f_def plussub_def nodes_sup_def inter_sorted_correct)
      then have sorted_ss_hdw: "sorted (rev ?ss_hdw)" 
            and ss_hdw_subset_a_hdb_cons: "set ?ss_hdw \<subseteq> set (hd b # ?a_hdb)" 
            and ss_hdw_subset_a_hdw: "set ?ss_hdw \<subseteq> set ?a_hdw" by auto         

      from  sorted_hd_b_cons have "\<forall>x\<in> set (hd b # ?a_hdb). x \<le> hd b" using b_n_nil 
        by (induct b) (auto simp add:sorted_wrt_append)
      with ss_hdw_subset_a_hdb_cons
      have ss_hdw_lt_hdb: "\<forall>x\<in>set ?ss_hdw. x \<le> hd b" using sorted_hd_b_cons by auto                   
      
      have sorted_rev_hdw: "sorted (rev (hd w # ?ss_hdw))" 
      proof(cases "?a_hdw = rev [0..<n]")
        case True
        with wf_a_b have "\<exists>x\<in> set b. (x,hd w)\<in> g_E G \<and> x < hd w" using hd_w_lt_n by (auto simp add:wf_dom_def)
        then obtain prev_hd_w where prev_hd_w_in_b: "prev_hd_w \<in> set b" 
                                and prev_hd_w: "(prev_hd_w, hd w)\<in> g_E G"
                                and prev_hd_w_lt: "prev_hd_w < hd w" by auto


        show ?thesis
        proof(cases "prev_hd_w = hd b")
          case True
          with prev_hd_w_lt have "hd b < hd w" by auto
          with ss_hdw_lt_hdb  have "\<forall>x\<in>set ?ss_hdw. hd w > x" by auto
          with sorted_ss_hdw show ?thesis by (auto simp add:sorted_wrt_append)
        next
          case False
          with prev_hd_w_in_b have "prev_hd_w \<in> set (tl b)" by (induct b) auto
          with ww have prev_hd_w_nin_w: "prev_hd_w \<in> set w" using fin by auto
          from sorted_w have "\<forall>x\<in> set w. x \<ge> hd w" by(induct w) (auto simp add:sorted_wrt_append sorted_less_sorted_list_of_set) 
          with prev_hd_w_lt have "prev_hd_w \<notin> set w" by auto
          with prev_hd_w_nin_w show ?thesis by auto
        qed

      next
        case False
        with wf_a_b have "(\<forall>x\<in>set ?a_hdw. x < hd w)" using hd_w_lt_n by (auto simp add:wf_dom_def)
        with ss_hdw_subset_a_hdw
        have "(\<forall>x\<in>set ?ss_hdw. x < hd w)" by auto
        with sorted_ss_hdw show ?thesis by (auto simp add:sorted_wrt_append)
      qed
      with hdw_cons_ss_in_nodes show "hd w # ?ss_hdw \<in> A" using A_def by (fastforce dest:subset_nodes_inpow)

    next
      case False note hd_w_nin_succ_hdb = this
      then have "hd w \<notin> set (map fst ?qs_a)" using fin_succ_hd_b by (auto simp add:step_def exec_def)
      with exec2 have ss_hd_w_eq_a: "?ss_hdw = ?a_hdw"  using hd_w_lt_n len_ss_n len_eq  by auto
      with a_hdw_in_nodes  sorted_a_hdw have ss_hdw_in_nodes: "set ?ss_hdw \<subseteq> set nodes" 
                                         and sorted_ss_hdw: "sorted (rev ?ss_hdw)" by auto
      with hdw_in_nodes have hdw_cons_in_nodes: "set (hd w # ?ss_hdw) \<subseteq> set nodes" by (auto) 

      from hd_w_nin_succ_hdb ww have hd_w_non: "hd w \<notin>{q. \<exists>t. (q, t) \<in> set ?qs_a \<and> t \<squnion>\<^bsub>f\<^esub> a ! q \<noteq> a ! q}"
        using fin_succ_hd_b by (auto simp add:step_def exec_def )

      from set_ww hd_w_non have hd_w_in_tl_b: "hd w \<in> set (tl b)" using sorted_tl_b `w \<noteq> []` by auto      
        
      have sorted_rev_hdw: "sorted (rev (hd w # ?ss_hdw))"
      proof(cases "?a_hdw = rev [0..<n]")
        case True
        with wf_a_b have "\<exists>x\<in> set b. (x,hd w)\<in> g_E G \<and> x < hd w" using hd_w_lt_n by (auto simp add:wf_dom_def)
        then obtain prev_hd_w where prev_hd_w_in_b: "prev_hd_w \<in> set b" 
                                and prev_hd_w:      "(prev_hd_w, hd w)\<in> g_E G" 
                                and prev_hd_w_lt:   "prev_hd_w < hd w"  by auto
        from ww have "sorted w" by(simp add:sorted_less_sorted_list_of_set)
        then have "\<forall>x\<in> set w. x \<ge> hd w" using w_n_nil by (induct w) (auto simp add:sorted_wrt_append)
        with prev_hd_w_lt have prev_hd_w_nin_w: "prev_hd_w \<notin> set w" using w_n_nil by auto 
        with set_ww have "prev_hd_w \<notin> set (tl b)" by auto
        with prev_hd_w_in_b have "prev_hd_w = hd b" using sorted_b by (induct b) auto
        with prev_hd_w have "(hd b, hd w) \<in> g_E G" by auto 
        with hd_w_nin_succ_hdb show ?thesis by (auto simp add:succs_def)
      next
        case False
        with wf_a_b have a_hdw_lt: "(\<forall>x\<in>set ?a_hdw. x < hd w)" 
                     and "sorted (rev ?a_hdw)" using hd_w_lt_n by (auto simp add:wf_dom_def)
        with ss_hd_w_eq_a have "sorted (rev ?ss_hdw)" by simp
        from ss_hd_w_eq_a  have "?a_hdw =  ?ss_hdw" by auto
        with a_hdw_lt have "\<forall>x\<in>set ?ss_hdw. x < hd w" by auto
        with sorted_ss_hdw show ?thesis by (auto simp add:sorted_wrt_append)
      qed 
      with hdw_cons_in_nodes show " (hd w # ss ! hd w) \<in> A" by (unfold A_def) (rule subset_nodes_inpow)
    qed
  qed   
  then have pres_ss: "\<And>q \<tau>. w \<noteq> [] \<Longrightarrow> (q, \<tau>) \<in> set (step (hd w) ?ss_hdw) \<Longrightarrow> \<tau> \<in> A" 
    by (auto simp add:step_def exec_def transf_def)
 
  have hd_b_ss_sta: "stable r step ss (hd b)" 
  proof(unfold stable_def, clarsimp)
    fix q \<tau>
    assume "(q, \<tau>) \<in> set ?qs_ss_hdb "
    then have "q \<in> succs (hd b)" and  "\<tau> = transf (hd b) ?ss_hdb" using hd_b_lt_n fin_succ_hd_b
      by (auto simp add:step_def exec_def)
    then have \<tau>:"\<tau> =  (hd b # ?a_hdb)" using ss_hd_b_eq_a by (auto simp add:transf_def)  
    from `q \<in> succs (hd b)` hd_b_lt_n have "q\<in> set (g_V G)" using succ_in_G by auto
    then have "q < n" using verts_set by (auto simp add:n_def nodes_def)
    with wf_a_b have a_q_inA: "a!q \<in> A"  by (auto simp add:wf_dom_def)
    from wf_a_b a_hd_b_neq_all hd_b_lt_n have "\<forall>x\<in> set ( (a!hd b)). x < hd b" by (auto simp add:wf_dom_def)
    with sorted_hd_b_cons have "sorted (rev (hd b # ?a_hdb))"  by (auto simp add:sorted_wrt_append)
    from propa_ss1 `(q, \<tau>) \<in> set (step (hd b) (ss ! hd b))`
    have "ss!q = \<tau> \<squnion>\<^bsub>f\<^esub> a ! q" using `ss!hd b = a!hd b` by auto
    with \<tau> have "ss!q =  (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> a ! q" by simp
    with hd_b_cons_in_A a_q_inA have " (hd b # ?a_hdb)\<sqsubseteq>\<^bsub>r\<^esub> ss!q " 
      by (auto simp add: Semilat.ub1[OF Semilat.intro, OF is_semi])
    with \<tau> show "\<tau> \<sqsubseteq>\<^bsub>r\<^esub> ss ! q" by auto
  qed

  have wf_dom_2: "\<forall>p<n.
        sorted (rev (ss ! p)) \<and>
        (ss ! p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set ( (ss ! p)). x < p)) \<and>
        (ss ! p = rev [0..<n] \<longrightarrow> (\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)) \<and>
        (p \<notin> set w \<longrightarrow> stable r step ss p)"
  proof (intro strip)
    fix p
    let ?a_p = "a!p"
    let ?ss_p = "ss!p"

    assume p_lt_n: "p < n" 
    with wf_a_b have a_p_inA: "?a_p \<in> A" 
                 and sorted_a_p: "sorted (rev ?a_p)" 
                 and sta_a_p: "p \<notin> set b \<longrightarrow> stable r step a p" by (auto simp add:wf_dom_def)

    from p_lt_n have "p \<in> set (g_V G)" using verts_set n_def nodes_def by auto
    then have fin_succ_p: "finite (succs p)" using fin_succs by auto

    from set_a p_lt_n have a_p_inA: "?a_p \<in> A" using `length a = n` by (auto simp add:A_def)
    then have "set ?a_p \<subseteq> set nodes" using inpow_subset_nodes by (auto simp add:A_def)
    with p_lt_n have set_p_a_p: "set (p#?a_p) \<subseteq> set nodes" using n_def nodes_def verts_set  by auto

    from p_lt_n len_eq have p_lt_len_a:  "p < length a" by auto
    with ss_inA  have ss_p_in_A: "ss!p \<in> A"  using len_eq len_ss_n by auto
    with p_lt_n have sorted_ss_p: "sorted (rev ?ss_p)" by (auto simp add:A_def sorted_less_sorted_list_of_set)

    have len_ss_eq_a: "length ss = length a" using  len_eq len_ss_n by auto

    have p_nin_w_eq: "p \<notin> set w \<longleftrightarrow> (p \<notin> set b \<or> p = hd b) \<and> (\<forall>s. (p, s) \<in> set ?qs_a \<longrightarrow> s \<squnion>\<^bsub>f\<^esub> ?a_p = ?a_p)"
    proof
      assume "p \<notin> set w" 
      with set_ww have p_nin1: "p \<notin> {q. \<exists>t. (q, t) \<in> set ?qs_a\<and> t \<squnion>\<^bsub>f\<^esub> a ! q \<noteq> a ! q}" 
                   and p_nin2: "p \<notin> set (tl b)" by auto
      from p_nin1 have p_nin: "(\<forall>s. (p, s) \<in> set ?qs_a \<longrightarrow> s \<squnion>\<^bsub>f\<^esub> ?a_p = ?a_p)" by auto
      from p_nin2 have  "p \<notin> set b \<or> p = hd b" by (induct b) auto
      with p_nin show "(p \<notin> set b \<or> p = hd b) \<and> (\<forall>s. (p, s) \<in> set  ?qs_a \<longrightarrow> s \<squnion>\<^bsub>f\<^esub> ?a_p = ?a_p)" by auto
    next
      assume "(p \<notin> set b \<or> p = hd b) \<and> (\<forall>s. (p, s) \<in> set ?qs_a \<longrightarrow> s \<squnion>\<^bsub>f\<^esub> ?a_p = ?a_p)"
      then have p1: "p \<notin> set b \<or> p = hd b" 
            and p2: "\<forall>s. (p, s) \<in> set ?qs_a \<longrightarrow> s \<squnion>\<^bsub>f\<^esub> a ! p = ?a_p" by auto
      from p1 have "p \<notin> set (tl b)" 
      proof
        assume "p \<notin> set b" 
        then show ?thesis by(induct b) auto
      next
        assume "p = hd b" 
        with sorted_b show ?thesis by (induct b) (auto simp add:sorted_wrt_append)
      qed
      with p2 set_ww show "p \<notin> set w" using set_ww by auto
    qed

    have stable_ss_p: "p \<notin> set w \<longrightarrow> w \<noteq> Nil \<longrightarrow> stable r step ss p"
    proof (clarsimp simp add: stable_def split_paired_all)
      fix q \<tau>
      assume p_nin_w: "p \<notin> set w" and w_n_nil: "w \<noteq> Nil" and step_ss_p: "(q, \<tau>) \<in> set (step p ?ss_p) "
      from p_nin_w have p_cond: "(p \<notin> set b \<or> p = hd b) \<and> 
                                 (\<forall>s. (p, s) \<in> set ?qs_a \<longrightarrow>  (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_p = ?a_p)"
        using p_nin_w_eq  by (auto simp add:transf_def step_def exec_def)
      then have p_cond1: "(p \<notin> set b \<or> p = hd b)"
            and p_cond2: "(\<forall>s. (p, s) \<in> set ?qs_a \<longrightarrow>  (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_p = ?a_p)"by auto

      from bounded_a pres_ss w_n_nil have " \<forall>(q, t)\<in>set ?qs_ss. q < length ss \<and> t \<in> A" by auto
      then have "\<forall>(q, t)\<in>set (step (hd w) (ss ! hd w)). q < length ss \<and> (transf (hd w) (ss!hd w)) \<in> A" 
        by (auto simp add:step_def exec_def)         
      
      have ss_a_p_eq: "?ss_p = ?a_p"
      proof(cases "p \<in> succs (hd b)")
        case True note p_in_succ_hd_b = this 
        from `p \<in> succs (hd b)` propa_ss1' have ss_p: "?ss_p =  (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_p" using fin_succ_hd_b
          by (auto simp add:step_def exec_def)
        from p_in_succ_hd_b p_cond2 have " (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_p= ?a_p" using fin_succ_hd_b
          by (auto simp add:step_def exec_def)
        with ss_p show ?thesis by auto
      next
        case False
        then have "p \<notin> {q. \<exists>t. (q, t) \<in> set ?qs_a}" using fin fin_succ_hd_b  by (auto simp add:step_def exec_def)
        then have "p \<notin> set ( map fst ?qs_a)" by auto
        with p_lt_n show ?thesis using exec2 len_eq  by auto
      qed
      
      have "(\<forall>(q, \<tau>)\<in>set (step p ?ss_p). transf p ?ss_p \<sqsubseteq>\<^bsub>r\<^esub> ss ! q) "      
      proof(intro strip, clarsimp)
        fix succ_p z
        let ?a_succ_p = "a!succ_p"
        let ?ss_succ_p = "ss!succ_p"         

        assume "(succ_p, z)  \<in> set (step p ?ss_p)"
        then have succ_p: "succ_p \<in> succs p" using p_lt_n fin_succ_p by (auto simp add:step_def exec_def)
        with p_lt_n have succ_p_lt_n: "succ_p < n" using succ_in_verts  n_def nodes_def verts_set by auto
        with wf_a_b have a_succ_p_inA: "?a_succ_p \<in> A"  by (auto simp add:wf_dom_def)
        from succ_p_lt_n ss_in_A have ss_succ_p_inA: "?ss_succ_p \<in> A" by auto 

        have p_nin_b_ssp: "p \<notin> set b \<Longrightarrow> transf p ?ss_p \<in> A \<and> transf p ?ss_p \<sqsubseteq>\<^sub>r ?a_succ_p"
        proof-
          assume "p \<notin> set b"
          with sta_a_p have "(\<forall>(q,\<tau>) \<in> set (step p ?a_p). \<tau> \<sqsubseteq>\<^sub>r a!q)" by (simp add:stable_def)
          with succ_p have transf_p_succp':"transf p ?a_p \<sqsubseteq>\<^sub>r ?a_succ_p" using fin_succ_p 
            by (auto simp add:stable_def step_def exec_def)
          with ss_a_p_eq have transf_lt_p: "transf p ?ss_p \<sqsubseteq>\<^sub>r ?a_succ_p" by auto
          from transf_p_succp' have "(p# ?a_p) \<sqsubseteq>\<^sub>r ?a_succ_p" by (auto simp add:transf_def)
          then have "sorted (rev (p#?a_p)) \<or> (p#?a_p = ?a_succ_p)" 
            by (auto simp add:step_def exec_def transf_def r_def lesssub_def lesub_def nodes_le_def)
          with set_p_a_p a_succ_p_inA
          have "(p#?a_p) \<in> (rev \<circ> sorted_list_of_set) ` (Pow (set nodes))" using subset_nodes_inpow by (auto simp add:A_def)
          then have "transf p ?a_p \<in> A" using transf_def by (auto simp add:A_def transf_def)
          then show ?thesis using ss_a_p_eq transf_lt_p by auto
        qed
              
        show "transf p ?ss_p \<sqsubseteq>\<^bsub>r\<^esub> ?ss_succ_p"
        proof(cases "p \<in> succs (hd b)")
          case True note p_in_succ_hd_b = this   
          with p_cond have " (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_p =?a_p" using fin_succ_hd_b
            by (auto simp add:step_def exec_def)
          from p_in_succ_hd_b propa_ss1' have ss_p: "?ss_p = (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_p" using fin_succ_hd_b
            by (auto simp add:step_def exec_def)
          then have transf_p2: "transf p ?ss_p = (p # (inter_sorted_rev (hd b # ?a_hdb) ?a_p))" 
            by (auto simp add:f_def plussub_def nodes_sup_def transf_def )
          then show ?thesis 
          proof(cases "succ_p \<in> succs (hd b)")
            case True note succ_p_is_succ_hdb = this
            with propa_ss1 have ss_succ_p: "?ss_succ_p = (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_succ_p" using fin_succ_hd_b
              by (auto simp add:step_def exec_def transf_def)
            with a_succ_p_inA hd_b_cons_in_A  have succ_p1: "(hd b # ?a_hdb) \<sqsubseteq>\<^bsub>r\<^esub>?ss_succ_p" 
                                               and succ_p2: "?a_succ_p\<sqsubseteq>\<^bsub>r\<^esub> ?ss_succ_p "
              by (auto simp add:Semilat.ub1[OF Semilat.intro, OF is_semi]
                                Semilat.ub2[OF Semilat.intro, OF is_semi])           
            show ?thesis 
            proof(cases "p \<in> set b")
              case True note p_in_set_b = this
              then have p_eq_hdb: "p = hd b" using p_cond by auto
              with succ_p have succ_p_is_succ_hdb: "succ_p \<in> succs (hd b)" by auto
              from ss_a_p_eq p_eq_hdb have "(hd b # ?ss_hdb) = hd b # ?a_hdb" by auto
              with succ_p1 have "hd b # ss ! hd b \<sqsubseteq>\<^bsub>r\<^esub> ss ! succ_p" by auto
              with p_eq_hdb show ?thesis by (auto simp add:transf_def)             
            next 
              case False
              then have "transf p ?ss_p \<in> A" and "transf p ?ss_p \<sqsubseteq>\<^sub>r ?a_succ_p" using p_nin_b_ssp by auto                       
              with succ_p2 a_succ_p_inA ss_succ_p_inA  
              show ?thesis by (auto intro: order_trans Semilat.orderI[OF Semilat.intro, OF is_semi])
            qed
          next
            case False note succ_p_n_succ_hdb = this
            with exec2 have ss_succ_p_eq_a: "?ss_succ_p = ?a_succ_p" using fin_succ_hd_b succ_p_lt_n  len_eq 
              by (auto simp add:step_def exec_def)
            show ?thesis 
            proof(cases "p \<in> set b")
              case True
              with p_cond have p_eq_hdb: "p = hd b" by auto
              with succ_p have succ_p_is_succ_hdb: "succ_p \<in> succs (hd b)" by auto
              with succ_p_n_succ_hdb show ?thesis by auto
            next 
              case False
              with sta_a_p have "\<forall>(q,\<tau>) \<in> set (step p ?a_p). \<tau> \<sqsubseteq>\<^sub>r a!q" by (simp add:stable_def)
              with succ_p fin_succ_p have "transf p ?a_p \<sqsubseteq>\<^sub>r ?a_succ_p" 
                by (auto simp add:step_def exec_def)
              with ss_succ_p_eq_a ss_a_p_eq show ?thesis by auto
            qed
          qed
        next
          case False note p_nin_succ_hd_b = this  
          from p_nin_succ_hd_b p_cond have "p \<notin> set b \<or> p = hd b" by auto
          then show ?thesis 
          proof
            assume "p \<notin> set b"
            then have transf_ss_p_inA: "transf p ?ss_p \<in> A" and transf_lt_p: "transf p ?ss_p \<sqsubseteq>\<^sub>r ?a_succ_p" using p_nin_b_ssp by auto  
            show "transf p ?ss_p \<sqsubseteq>\<^bsub>r\<^esub> ?ss_succ_p"
            proof(cases "succ_p \<in> succs (hd b)")
              case True
              with succ_p_lt_n propa_ss1' len_eq  fin_succ_hd_b have "?ss_succ_p = (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_succ_p" 
                by (auto simp add:step_def exec_def)
              with a_succ_p_inA hd_b_cons_in_A have "?a_succ_p \<sqsubseteq>\<^sub>r ?ss_succ_p" 
                by (auto simp add:Semilat.ub2[OF Semilat.intro, OF is_semi])            
              with transf_lt_p transf_ss_p_inA a_succ_p_inA ss_succ_p_inA  
              show ?thesis by (auto intro: order_trans  Semilat.orderI[OF Semilat.intro, OF is_semi])              
            next
              case False
              with succ_p_lt_n exec2 len_eq  fin_succ_hd_b have "?ss_succ_p = ?a_succ_p" 
                by (auto simp add:step_def exec_def)
              with transf_lt_p show ?thesis by auto
              qed
          next
            assume "p = hd b" 
            with hd_b_ss_sta have "(\<forall>(q,\<tau>) \<in> set (step p ?ss_p). \<tau> \<sqsubseteq>\<^sub>r ss!q)" by (simp add:stable_def)
            with succ_p `p = hd b`
            show "transf p ?ss_p \<sqsubseteq>\<^bsub>r\<^esub> ?ss_succ_p" using fin_succ_hd_b
              by (auto simp add:stable_def step_def exec_def transf_def)
          qed
        qed          
      qed
      with step_ss_p show "\<tau> \<sqsubseteq>\<^bsub>r\<^esub> ss ! q" by (auto simp add:step_def exec_def)
    qed

    show "sorted (rev ?ss_p) \<and> 
          (?ss_p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set?ss_p. x < p)) \<and>
          (?ss_p = rev [0..<n] \<longrightarrow> (\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)) \<and>
          (p \<notin> set w \<longrightarrow> stable r step ss p)"  
    proof(cases "w \<noteq> []")
      case True note w_n_nil = this
      show ?thesis
      proof (cases "p \<in> set( map fst (?qs_a))")
        case True
        with propa_ss1 have ss_p: "?ss_p = (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> ?a_p" by (simp add:step_def exec_def transf_def)
        with sorted_hd_b_cons sorted_a_p
        have ss_p_lt_hdb: "set ?ss_p \<subseteq> set (hd b # ?a_hdb)" 
         and ss_p_lt: "set ?ss_p \<subseteq> set ?a_p" 
         and ss_p_inter: "set ?ss_p = set (hd b # ?a_hdb) \<inter> set ?a_p"         
          by (auto simp add:f_def plussub_def nodes_sup_def inter_sorted_correct)
  
        from sorted_hd_b_cons sorted_a_p
        have "inter_sorted_rev (hd b # ?a_hdb) ?a_p = rev (sorted_list_of_set (set (hd b # ?a_hdb) \<inter> set ?a_p))" 
          by (rule inter_sorted_correct_col)
        with ss_p have ss_p2: "?ss_p = (rev (sorted_list_of_set (set (hd b # ?a_hdb) \<inter> set ?a_p)))" 
          by (auto simp add:f_def plussub_def nodes_sup_def)

        show ?thesis
        proof(cases "?a_p \<noteq> (rev [0..<n])")
          case True note a_p_neq_all = this
          then have seta_p_neq_all: "set ?a_p \<noteq> {0..<n}" using sorted_a_p  by (auto intro: sorted_less_rev_set_unique)
          from a_p_neq_all wf_a_b p_lt_n have a_lt_p: "(\<forall>x\<in>set ?a_p. x < p)" using n_def len_eq  by (auto simp add:wf_dom_def)  
          with ss_p_lt have "\<forall>x\<in>set ?ss_p. x < p" by auto
          then have  ss_lt_p: "?ss_p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set ?ss_p. x < p)" by auto
          have "set ?ss_p \<noteq> {0..<n}" 
          proof(rule ccontr)
            assume "\<not> set ?ss_p \<noteq> {0..<n}"            
            with ss_p_lt have cc:  "{0..<n} \<subseteq> set ?a_p" by auto
            from a_in_A p_lt_len_a have " ?a_p \<in> ((rev \<circ> sorted_list_of_set) ` (Pow (set nodes)))" by (auto simp add: A_def)           
            then have ass_set_in_nodes: "set ?a_p \<subseteq> set nodes" by (rule inpow_subset_nodes)
            then have "set ?a_p \<subseteq> {0..<n}" by (auto simp add:nodes_def n_def verts_set) 
            with cc have "set ?a_p = {0..<n}"  by auto
            with seta_p_neq_all show False by auto 
          qed
          then have ss_p_not_all: "?ss_p \<noteq> rev [0..<n]" using  sorted_ss_p by (auto intro: sorted_less_rev_set_unique)
          then have "?ss_p = rev [0..<n] \<longrightarrow>  (\<exists>x\<in>set w. (x,p)\<in> g_E G \<and> x < p)" by auto
          with sorted_ss_p ss_lt_p stable_ss_p w_n_nil show ?thesis by fastforce
        next
          case False 
          then have a_p_all: "?a_p =  (rev [0..<n])"  by auto
          with wf_a_b p_lt_n   have ex_lt_p: " (\<exists>x\<in> set b. (x,p)\<in> g_E G \<and> x < p)" by (auto simp add:wf_dom_def)
  
          have "hd b \<in> set b" using b_n_nil by auto                  
  
          from a_p_all have "set ?a_p = {0..<n}" by auto
          with ss_p_inter have "set ?ss_p \<subseteq> {0..<n}" by auto
          with ss_p2 hdb_subset_n `set ?a_p  = {0..<n}` have "(set (hd b # ?a_hdb) \<inter> set ?a_p) = set (hd b # ?a_hdb)" by auto
  
          with ss_p2 have ss_p3: "?ss_p =  (rev (sorted_list_of_set (set (hd b # ?a_hdb))))" by auto
          from sorted_hd_b_cons have "sorted_list_of_set (set (hd b # ?a_hdb)) = rev (hd b # ?a_hdb)" by (fastforce dest: sorted_less_rev_set_eq)
          with ss_p3 have ss_p_4: "?ss_p = (hd b # ?a_hdb)" by auto          
           
          
          have "(?ss_p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set ?ss_p. x < p)) \<and>
                (?ss_p = rev [0..<n] \<longrightarrow>  (\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)) \<and>
                (p \<notin> set w \<longrightarrow> stable r step ss p)"
          proof(cases "?ss_p \<noteq>  (rev [0..<n])")
            case True note ss_p_n_all = this
            with ss_p_4 show ?thesis
            proof(cases "hd b < p")
              case True
              with ss_p_4 sorted_hd_b_cons have ss_p_lt_p: "\<forall>x\<in>set ( (ss ! p)). x < p" by (auto simp add:sorted_wrt_append)
              with ss_p_4 ss_p_n_all stable_ss_p `w \<noteq> []` show ?thesis by auto
            next
              case False note hd_b_ge_p = this
              from ex_lt_p obtain x where "x\<in> set b " and " (x,p)\<in> g_E G " and "x < p"by auto
              from `x \<in> set b` `x < p` hd_b_ge_p have "tl b \<noteq> []" by (induct b) auto
              with  hd_b_ge_p sorted_b have temp_t: "\<forall>x\<in> set (tl b). x \<ge> p" by (induct b) auto
              with `\<not>hd b < p` have "x \<in> set (tl b)" using `(x,p)\<in> g_E G ` `x \<in> set b` `x < p` by (induct b) auto              
              with `x < p` temp_t have False by auto
              then  show ?thesis by auto
            qed
          next
            case False
            then have "?ss_p =  (rev [0..<n])" by auto 
            with ss_p_4 have hd_b_as1: "(hd b # ?a_hdb) = rev [0..<n]" by auto
            then have "hd (hd b # ?a_hdb) = hd (rev [0..<n])" by auto
            then have hd_b: "hd b = hd (rev [0..<n])" by auto
            have "n > 0 "using n_def nodes_def len_verts_gt0 by auto
            then have last_hd: "last [0..<n] = hd (rev [0..<n])" apply (induct n)  by auto            
            have "last[0..<n] = n - 1" using `n> 0` by auto
            then have "hd (rev [0..<n]) = n - 1" using last_hd by auto
            with hd_b  have hd_b_n_minus1: "hd b = n - 1" by auto
  
            show ?thesis
            proof(cases "hd b < p")
              case True
              with hd_b_n_minus1 p_lt_n  show ?thesis by arith    
            next
              case False
              from ex_lt_p obtain x where x: "x\<in>set b \<and> (x, p) \<in> g_E G \<and> x < p" by auto
              then have "x\<in>set b " and " (x, p) \<in> g_E G " and " x < p"by auto
              from x `\<not>hd b <p` have x_n_hd_b: "x \<noteq> hd b" by auto
              with  `x\<in>set b ` have "tl b \<noteq> []" by (induct b) auto
              with `x\<in>set b ` x_n_hd_b have "x \<in> set (tl b)"  by (induct b) auto
              with ww have "x \<in> set w" using fin by auto
              then show ?thesis using `ss!p =  (rev [0..<n])` `(x, p) \<in> g_E G` `x<p` stable_ss_p `w \<noteq> []` by auto
            qed
          qed
          then show ?thesis using sorted_ss_p by auto
        qed

      next
        case False note p_not_in_succ = this
        with exec2 p_lt_n len_eq have ss_a_p_eq: "ss!p = a!p" by auto
        with ass p_lt_n  wf_a_b
        have cond1: "(?ss_p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set ?ss_p. x < p))" 
          by (auto simp add:wf_dom_def)
  
        show ?thesis
        proof(cases "?a_p \<noteq>  (rev [0..<n])")
          case True
  
          with wf_a_b have "(\<forall>x\<in>set ?a_p. x < p)" using p_lt_n  len_eq  by (auto simp add:wf_dom_def)
          with ss_a_p_eq have "(\<forall>x\<in>set ?ss_p. x < p)" by auto
          with cond1 sorted_ss_p show ?thesis using p_lt_n  len_eq stable_ss_p w_n_nil by auto
        next 
          case False
          then have "?a_p =  (rev [0..<n])" by auto
          from ss_a_p_eq ass p_lt_n  wf_a_b 
          have "?ss_p = rev [0..<n] \<longrightarrow>  (\<exists>x\<in> set b. (x,p)\<in> g_E G \<and> x < p)" by (auto simp add:wf_dom_def)
          with ss_a_p_eq `a!p =  (rev [0..<n])` have hd_b_lt_p: " (\<exists>x\<in> set b. (x,p)\<in> g_E G \<and> x < p)" using len_eq  by auto
          then obtain x where "x\<in> set b " and " (x,p) \<in>  g_E G" and " x < p" by auto
            
                
          from fin_succ_hd_b `(x,p) \<in>  g_E G` p_not_in_succ have "x \<noteq> hd b " by (auto simp add:step_def exec_def succs_def)
          with `x\<in> set b` have "x \<in> set (tl b)" using b_n_nil by (induct b)  auto
  
          with ww have "x \<in> set w" using fin by auto
          with `(x,p) \<in>  g_E G` and ` x < p` have "(\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)" by auto
          with cond1 sorted_ss_p show ?thesis using stable_ss_p w_n_nil by auto  
        qed
      qed
    next
      case False
      then have w_n_nil: "w =[]" by auto 
      with set_ww have "tl b = []" and succ_hd_b_eq: "\<forall>(q, t) \<in> set ?qs_a.  t \<squnion>\<^bsub>f\<^esub> a ! q = a ! q" by auto
      
      from  succ_hd_b_eq propa have "\<forall>p<n. ss!p = a!p"
      proof (intro strip)
        fix p
        assume ass_eq: " \<forall>(q, t)\<in>set ?qs_a. t \<squnion>\<^bsub>f\<^esub> a ! q = a ! q "
           and " propa f ?qs_a a (tl b) = (ss, w) " and p_lt_n: " p < n "
        show "ss ! p = a ! p"
        proof(cases "p \<in> succs (hd b)")
          case True
          with fin_succ_hd_b propa_ss1 have ss_p_eq: "ss!p = transf (hd b) (a!hd b)   \<squnion>\<^bsub>f\<^esub> a ! p"
            by (auto simp add:step_def exec_def)
          with ass_eq `p \<in> succs (hd b)` fin_succ_hd_b have "transf (hd b) (a!hd b) \<squnion>\<^bsub>f\<^esub> a ! p = a ! p" 
            by (auto simp add:step_def exec_def)
          with ss_p_eq show ?thesis by auto
        next
          case False
          with fin_succ_hd_b exec2 p_lt_n n_def len_eq nodes_def  show ?thesis
            by (auto simp add:step_def exec_def)
        qed
      qed
      then have "\<forall>p< length ss. ss!p = a!p" using `length ss = n` by auto
      then have ss_eq_a: "ss = a" using n_def len_eq nodes_def `length ss = n` by (auto simp add:list_eq_iff_nth_eq)
      
      with wf_a_b p_lt_n have 
                              t3: "(?ss_p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set ?ss_p. x < p))" and 
                              t4:  "(?ss_p = rev [0..<n] \<longrightarrow> (\<exists>x\<in>set b. (x, p) \<in> g_E G \<and> x < p))" and 
                              sta_temp: "(p \<notin> set b \<longrightarrow>  stable r step ss p)"  by (auto simp add:wf_dom_def)

      from  `tl b = []`  `b \<noteq> []`   have "p \<notin> set b \<longleftrightarrow> p \<noteq> hd b " by (induct b) auto
      with sta_temp have "p \<noteq> hd b \<longrightarrow> stable r step ss p" by auto
      with hd_b_ss_sta have "stable r step ss p" by auto
      then have sta_temp': "p \<notin> set w \<longrightarrow>  stable r step ss p" using w_n_nil by auto

      have "?ss_p \<noteq> (rev [0..<n])" 
      proof(rule ccontr)
        assume "\<not>?ss_p \<noteq>  (rev [0..<n])"
        then have ss_p_all: "?ss_p =  (rev [0..<n])" by simp
        with `ss = a` have "a!p =  (rev [0..<n])" by auto
        from `?ss_p =  (rev [0..<n])`
        have " ?ss_p = rev [0..<n]" by auto
        with  t4 have "(\<exists>x\<in>set b. (x, p) \<in> g_E G \<and> x < p)" by auto
        then obtain x where x: "x \<in> set b \<and> (x, p) \<in> g_E G \<and> x < p" by auto 
        with `tl b = []`  `b \<noteq> []` have "x =hd b"  by (induct b) auto
        with x have " (hd b, p) \<in> g_E G" and hdb_lt_p: "hd b < p" by auto
        then have "p \<in> succs (hd b)" by (simp add:succs_def)
        with succ_hd_b_eq have transf_hd_b_ap: "transf (hd b) (a!hd b)  \<squnion>\<^bsub>f\<^esub> a ! p = a ! p"  using fin_succ_hd_b 
          by (auto simp add:step_def exec_def)

        have a_p_neq_all: "?a_p \<noteq> (rev [0..<n])" 
        proof(rule ccontr)
          assume "\<not> ?a_p \<noteq>  (rev [0..<n])" 
          then have a_p_all: "?a_p =  (rev [0..<n])" by auto
          then have "transf (hd b) ?a_hdb \<squnion>\<^bsub>f\<^esub> ?a_p =  (hd b # ?a_hdb)  \<squnion>\<^bsub>f\<^esub>  (rev [0..<n])" 
            by (auto simp add:transf_def)
          then have "transf (hd b) ?a_hdb  \<squnion>\<^bsub>f\<^esub>?a_p =  ( (inter_sorted_rev (hd b # ?a_hdb) (rev [0..<n])))" 
            by (auto simp add:f_def plussub_def nodes_sup_def )
          with transf_hd_b_ap a_p_all have "inter_sorted_rev (hd b # ?a_hdb) (rev [0..<n]) = 
                                              (rev [0..<n])"by auto
          then have tx: "inter_sorted_rev (hd b # ?a_hdb) (rev [0..<n]) = (rev [0..<n])" by auto
          from sorted_hd_b_cons have "set (inter_sorted_rev (hd b # ?a_hdb) (rev [0..<n])) \<subseteq>
                                    set (hd b # ?a_hdb)" by (auto simp add: inter_sorted_correct)
          with tx have "set (rev [0..<n]) \<subseteq> set (hd b #  ?a_hdb)" by auto
          then have ty: "{0..<n} \<subseteq> set (hd b # ?a_hdb)"  by auto
         
          from hdb_subset_n ty have "{0..<n} = set (hd b # ?a_hdb)" by auto

          with sorted_hd_b_cons have tz: "hd b # ?a_hdb = rev [0..<n]" by (auto simp add:sorted_less_rev_set_unique)

          from n_def nodes_def len_verts_gt0 verts have "n > 0" by auto
          with tz have tzz: "hd b = n - 1" by (induct n)  auto
          from p_lt_n tzz hdb_lt_p show False by auto
        qed
        with  ss_p_all ss_eq_a show False  by auto
      qed
      with sta_temp' sorted_ss_p t3 show ?thesis by auto
    qed
  qed

  from ss_inA wf_dom_2 sorted_w len_ss_n w_lt_n show ?thesis by auto
qed

lemma propa_dom_invariant_aux':
  fixes a b ss w
assumes propa: "propa f (step (hd b) (a ! hd b)) a (tl b) = (ss, w) "    
    and b_n_nil: "b \<noteq> [] " 
    and a_in_A: "\<forall>\<tau>\<in>set a. \<tau> \<in> A  "   
    and ass: "\<forall>p<length ss0.
          sorted (rev ( (a ! p))) \<and>
          (a ! p \<noteq> rev [0..<length ss0] \<longrightarrow> (\<forall>x\<in>set ( (a ! p)). x < p)) \<and>
          (a ! p = rev [0..<length ss0] \<longrightarrow>  (\<exists>x\<in> set b. (x,p)\<in> g_E G \<and> x < p)) \<and>
          (p \<notin> set b \<longrightarrow> stable r step a p)"
    and sorted_b: "sorted b  "
    and n_len: "n = length ss0  "
    and len_eq:  "length a = length ss0  "
    and b_lt_n: "\<forall>x\<in>set b. x < length ss0  "
  shows "(\<forall>\<tau>\<in>set ss. \<tau> \<in> A) \<and>
         (\<forall>p<length ss0.
           sorted (rev ( (ss ! p))) \<and>
           (ss ! p \<noteq> rev [0..<length ss0] \<longrightarrow> (\<forall>x\<in>set (ss ! p). x < p)) \<and>
           (ss ! p = rev [0..<length ss0] \<longrightarrow>  (\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)) \<and>
           (p \<notin> set w \<longrightarrow> stable r step ss p)) \<and>
         sorted w \<and> length ss = length ss0 \<and> (\<forall>x\<in>set w. x < length ss0) " 
  using assms 
  by (auto dest: propa_dom_invariant_aux)


lemma propa_dom_invariant: 
  assumes wf_ss_w: "wf_dom ss w "
      and w_n_nil: "w \<noteq> []"
      and propa: "propa f (step (hd w) (ss ! hd w)) ss (tl w) = (ss', w') "
    shows "wf_dom ss' w'" 
  using assms 
proof-
  from wf_ss_w have ass:
    "(\<forall>p< n. sorted (rev (ss!p)) \<and>
             (ss!p \<noteq> rev [0..< n] \<longrightarrow> (\<forall>x\<in>set (ss!p). x < p)) \<and>
             (ss!p = rev [0..< n] \<longrightarrow>  (\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)) \<and>
             (p \<notin> set w \<longrightarrow> stable r step ss p)) "
  and sorted_b: "sorted w"
  and a_in_A: "\<forall>\<tau>\<in>set ss. \<tau> \<in> A" 
  and len_eq: "length ss = n"
  and b_lt_n: "(\<forall>x\<in>set w. x < n)"  by (auto simp add:wf_dom_def)
  from propa w_n_nil a_in_A ass sorted_b len_eq b_lt_n 
  show ?thesis by (unfold wf_dom_def) (rule propa_dom_invariant_aux)
qed


lemma step_dom_mono_aux: 
  fixes \<tau> p \<tau>' a b
  assumes sorted: "sorted (rev (transf p  \<tau>)) "
      and a_b_step: "(a, b) \<in> set (step p  \<tau>) " 
      and "\<tau> \<in> A " and " p < n " and " \<tau> \<sqsubseteq>\<^bsub>r\<^esub> \<tau>'" 
    shows "\<exists>\<tau>''. (a, \<tau>'') \<in> set (step p \<tau>') \<and> b \<sqsubseteq>\<^bsub>r\<^esub> \<tau>''"
proof-  
  have step1: "step p \<tau> = map (\<lambda>pc. (pc, (transf  p \<tau>))) (rev (sorted_list_of_set(succs p)))" by (simp add:step_def exec_def)
  from a_b_step have "set (step p \<tau>) \<noteq> {}" by auto
  with step1 have succ_p_n_nil: "(rev (sorted_list_of_set(succs p))) \<noteq> []" by auto

  from `p<n` have "p \<in> set (g_V G)" using n_def nodes_def verts_set len_verts_gt0 by auto
  then have fin: "finite (succs p)" using fin_succs by auto
  with step1  have "\<forall>(x,y)\<in> set (step p \<tau>). x \<in> succs p" 
               and step2: "\<forall>(x,y)\<in> set (step p \<tau>). y = transf p \<tau>" by (auto simp add:step_def exec_def)
  with a_b_step have "a \<in> succs p" by auto
  then have "succs p \<noteq> {}" by auto
  from step2 a_b_step have b:  "b = transf p \<tau>" by auto

  have step2: "step p \<tau>' = map (\<lambda>pc. (pc, (transf  p \<tau>'))) (rev (sorted_list_of_set(succs p)))" by (simp add:step_def exec_def)
  with fin have g1: "\<forall>(x,y)\<in> set (step p \<tau>'). x \<in> succs p" 
                and g2: "\<forall>(x,y)\<in> set (step p \<tau>'). y = transf p \<tau>'" by (auto simp add:step_def exec_def)
  with `a \<in> succs p` have "\<exists>t. (a,t)\<in> set (step p \<tau>')" using fin by (auto simp add:step_def exec_def)
  then obtain t where ex: "(a,t)\<in> set (step p \<tau>')" by auto 
  with g2 have t: "t = transf p \<tau>'" by auto

  from` \<tau> \<sqsubseteq>\<^bsub>r\<^esub> \<tau>'` have g: "sorted (rev \<tau>) \<and> sorted (rev \<tau>')\<and> set \<tau>' \<subseteq> set \<tau> \<or> \<tau> = \<tau>'"
    by (auto simp add:r_def lesssub_def lesub_def nodes_le_def)
  then have subset_p: "set (p#\<tau>') \<subseteq> set (p# \<tau>)" and "set  \<tau>' \<subseteq> set \<tau>" by auto
  from sorted have "\<forall>x\<in> set \<tau>. x < p" and "sorted (rev \<tau>')" using g by (auto simp add:sorted_wrt_append transf_def)
  with `set \<tau>' \<subseteq> set \<tau>` have "\<forall>x\<in> set \<tau>'. x < p" by auto
  with `sorted (rev \<tau>')` have "sorted (rev (p#\<tau>'))" by (auto simp add:sorted_wrt_append)
  with sorted b t subset_p

  have "b \<sqsubseteq>\<^bsub>r\<^esub> t" by (auto simp add:r_def lesssub_def lesub_def nodes_le_def transf_def)
  with ex show ?thesis by auto
qed

lemma step_dom_mono: 
"(\<forall>\<tau> p \<tau>'. \<tau> \<in> A \<and> p<n \<and> \<tau> \<sqsubseteq>\<^sub>r \<tau>' \<longrightarrow> 
           sorted (rev (transf p \<tau>)) \<longrightarrow> 
           set (step p \<tau>) {\<sqsubseteq>\<^bsub>r\<^esub>} set (step p \<tau>'))"
  apply(unfold mono_def lesubstep_type_def)
  by(auto simp add:step_dom_mono_aux n_def nodes_def transf_def)


lemma propa_termination: 
  fixes a b
  assumes wf_a_b: "wf_dom a b" 
      and b_n_nil: "b \<noteq> [] "
    shows "(propa f (step (hd b) (a ! hd b)) a (tl b), a, b) \<in>
           {(ss', ss). ss [\<sqsubset>\<^bsub>r\<^esub>] ss'} <*lex*> 
           (\<lambda>x. case x of (x, y) \<Rightarrow> (sorted_list_of_set x, sorted_list_of_set y)) ` finite_psubset"
proof-
  let ?qs = "(step (hd b) (a ! hd b))"
  from wf_a_b have "\<forall>x\<in>set b. x < n" and n_len: "length a = n"  and sorted_b: "sorted b" 
               and set_a: "set a \<subseteq> A" by (auto simp add:wf_dom_def)
  then have sorted_tl_b: "sorted (tl b)" and hd_b_lt_n: "hd b < n" using b_n_nil by (induct b) (auto simp add:sorted_wrt_append)
  from set_a have a_inA: "a \<in> list n A" using n_len by (auto intro: listI)

  from hd_b_lt_n have dist: "distinct (map fst ?qs)" using distinct_p  by auto   

  from wf_a_b b_n_nil have step_pres_bounded: "\<forall>(q, \<tau>)\<in>set ?qs. q < n \<and> \<tau> \<in> A"
    using propa_dom_invariant_auxi n_len by fastforce  
  with sorted_tl_b set_a n_len
  have propa: "propa f ?qs a (tl b) = (merges f ?qs a, (sorted_list_of_set ({q. \<exists>t.(q,t)\<in>set ?qs \<and> t \<squnion>\<^bsub>f\<^esub> (a!q) \<noteq> a!q} \<union> set(tl b))))" 
    by (auto dest: decomp_propa)
  
  from a_inA step_pres_bounded sorted_b b_n_nil  dist
  have "((merges f ?qs a, (sorted_list_of_set ({q. \<exists>t.(q,t)\<in>set ?qs \<and> t \<squnion>\<^bsub>f\<^esub> (a!q) \<noteq> a!q} \<union> set(tl b)))),(a,b)) \<in>
        {(ss', ss). ss [\<sqsubset>\<^bsub>r\<^esub>] ss'} <*lex*> (\<lambda>x. case x of (x, y) \<Rightarrow> (sorted_list_of_set x, sorted_list_of_set y)) ` finite_psubset"
    by (auto simp add: finite_psubset_def dest: termination_lemma)      
  with propa show ?thesis by auto
qed   

lemma iter_dom_invariant: 
  assumes "wf_dom ss0 w0"
    shows "iter f step ss0 w0 = (ss',w') \<longrightarrow> wf_dom ss' w'" 
  using assms
  apply (unfold iter_def)
  apply(rule_tac  
      P = "(\<lambda>(ss, w). wf_dom ss w )" and
      r = "{(ss',ss). ss [\<sqsubset>\<^sub>r] ss'} <*lex*> (\<lambda>(x,y). (sorted_list_of_set x, sorted_list_of_set y)) ` finite_psubset" 
      in while_rule) 
  \<comment> \<open>Invariant holds initially:\<close>
      apply (clarsimp)

  \<comment> \<open>Invariant is preserved:\<close>
     apply(simp add: wf_dom_def)
     apply clarsimp  
     apply(rule propa_dom_invariant_aux')
            apply assumption+
  \<comment> \<open>Postcondition holds upon termination:\<close>
    apply clarsimp 

  \<comment> \<open>Well-foundedness of the termination relation:\<close>
   apply (simp add: wf_listn_termination_rel) 

  \<comment> \<open>Loop decreases along termination relation:\<close>
   apply clarsimp
   apply (fastforce intro:propa_termination)
  done

lemma propa_dom_invariant_aux2: 
  fixes ss w ssa wa
  assumes wf_dom_ss0_w0: "wf_dom ss0 w0"
      and w_n_nil: "w \<noteq> [] "     
      and propa: "propa f (step (hd w) (ss ! hd w)) ss (tl w) = (ssa, wa) "
      and wf_ss_w: "wf_dom ss w "
      and ss0_lt_ss: "ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ss"
      and sta: " \<forall>ts\<in>list n A. ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ts \<and> (\<forall>p<n. stable r step ts p) \<longrightarrow> ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts"    
    shows "ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ssa \<and> 
           (\<forall>ts\<in>list n A. ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ts \<and> (\<forall>p<n. stable r step ts p) \<longrightarrow> ssa [\<sqsubseteq>\<^bsub>r\<^esub>] ts)"
  using assms
proof-
  let ?ss_hdw = "ss!hd w"
  from wf_dom_ss0_w0 have len_ss0: "length ss0 = n" and "\<forall>x\<in> set ss0. x \<in> A" by (auto simp add:wf_dom_def)
  then have ss0_inA:  "ss0 \<in> list n A"  and set_ss0: "set ss0 \<subseteq> A"by (auto intro:listI)
  then have ss0_nth_inA: "\<forall>i<length ss0. ss0!i \<in> A" by auto
  then have ss0_p_subset: "\<forall>p< length ss0. set (ss0!p) \<subseteq> set nodes" by (auto simp add:inpow_subset_nodes A_def)

  from len_ss0 n_def nodes_def len_verts_gt0 have "0 < length ss0" by auto

  from ss0_lt_ss have "list_all2 (\<lambda>x y. x \<sqsubseteq>\<^sub>r y) ss0 ss" 
    by (auto simp add:lesssub_def lesub_def list_all2_def Listn.le_def)
  then have lt1: "\<forall>p<length ss0. ss0 !p \<sqsubseteq>\<^bsub>r\<^esub> ss!p" by (auto simp add: list_all2_conv_all_nth) 

  from wf_ss_w have  "\<forall>\<tau>\<in>set ss. \<tau> \<in> A" 
                and ass1: "\<forall>p<n. sorted (rev ( (ss ! p))) \<and>
                                (ss!p \<noteq> rev [0..<n] \<longrightarrow> (\<forall>x\<in>set (ss ! p). x < p)) \<and>
                                (ss!p = rev [0..<n] \<longrightarrow>  (\<exists>x\<in> set w. (x,p)\<in> g_E G \<and> x < p)) \<and>
                                (p \<notin> set w \<longrightarrow> stable r step ss p)" 
                and sorted_w: "sorted w" 
                and len_ss: "length ss = n" 
                and w_lt_n: "\<forall>x\<in>set w. x < n  "by (auto simp add:wf_dom_def)
  then have ss_inA: "ss \<in> list n A" and set_ss: "set ss \<subseteq> A" by (auto intro:listI)
  then have ss_nth_inA: "\<forall>i<length ss. ss!i \<in> A"  by auto
  then have ss_p_subset: "\<forall>p< length ss. set (ss!p) \<subseteq> set nodes" by (auto simp add:inpow_subset_nodes A_def)
  then have ss_hdw_nodes: "set ?ss_hdw \<subseteq> set nodes" using w_lt_n w_n_nil len_ss by auto

  let ?qs = "step (hd w) ?ss_hdw"
  from w_lt_n have hd_w_lt_n: "hd w < n" using w_n_nil by auto
  then  have dist: "distinct (map fst ?qs)" using distinct_p by auto

  from ss_nth_inA have ss_hdw_inA: "?ss_hdw \<in> A" using w_lt_n w_n_nil len_ss by auto
  from ass1 have sorted_ss_hdw: "sorted (rev ?ss_hdw)" using w_lt_n w_n_nil  by auto
  
  then have "\<forall>q\<in>succs (hd w). q \<in> set (g_V G)" by (auto simp add:succ_in_G)
  then have hd_w_suc_lt_n: "\<forall>q\<in>succs (hd w). q < n" using n_def verts_set nodes_def by auto

  have hdw_in_nodes:"hd w \<in> set (g_V G)" using verts_set n_def nodes_def w_lt_n w_n_nil by auto
  then have fin_succ_hd_w: "finite (succs (hd w))" using fin_succs by auto

  from sorted_w have sorted_tl_w': "sorted (tl w)" using w_n_nil by (induct w) auto
  from wf_ss_w w_n_nil have ss_hd_w_neq_all: "?ss_hdw \<noteq> (rev [0..<n])" 
                        and sorted_hd_w_ss: "sorted (rev (hd w # ?ss_hdw))"
                        and hdb_subset_nodes: "set (hd w # ?ss_hdw) \<subseteq> set nodes"
                        and hd_w_ss_in_A: " (hd w # ?ss_hdw) \<in> A" 
                        and step_pres_bounded: " \<forall>(q, \<tau>)\<in>set (step (hd w) ?ss_hdw). q < length ss \<and> \<tau> \<in> A" 
    using propa_dom_invariant_auxi by auto
  from ss_hd_w_neq_all have ss_lt_hd_w: "\<forall>x\<in>set ?ss_hdw. x < hd w" using hd_w_lt_n wf_ss_w by (auto simp add:wf_dom_def)

  from wf_ss_w w_n_nil propa have wf_ssa_wa: "wf_dom ssa wa" using propa_dom_invariant by auto
  then have sorted_ssa_p: "\<forall>p<n. sorted (rev (ssa!p))" 
        and len_ssa: "length ssa = n" 
        and "\<forall>x\<in> set ssa. x \<in> A" 
        and sorted_wa: "sorted wa" 
        and len_ssa: "length ssa = n" 
        and wa_lt_n: "\<forall>x\<in> set wa. x < n" 
    by (auto simp add:wf_dom_def)
  then have ssa_inA: "ssa\<in> list n A" and set_ssa: "set ssa \<subseteq> A"by (auto intro:listI)
  then have ssa_nth_inA: "\<forall>i<length ssa. ssa!i \<in> A" by auto
  then have ssa_p_subset: "\<forall>p< length ssa. set (ssa!p) \<subseteq> set nodes" by (auto simp add:inpow_subset_nodes A_def)

  from len_ss0 len_ssa have len_ss0_ssa: "length ss0 = length ssa" by simp
  from len_ss0 len_ss  have len_ss0_ss:  "length ss0 = length ss" by simp  
  have "\<forall>(q, \<tau>)\<in>set ?qs. \<tau> = transf (hd w) (ss!(hd w))" by (simp add:step_def exec_def)
  then have transf_ss_hd_w: "\<forall>(q, \<tau>)\<in>set ?qs. \<tau> =  (hd w # ?ss_hdw)" 
    by (simp add:transf_def) 
  from set_ss step_pres_bounded sorted_tl_w' len_ss dist have "\<forall>(q, \<tau>) \<in> set ?qs. (fst(propa f ?qs ss (tl w)))!q = \<tau> \<squnion>\<^bsub>f\<^esub>ss!q" 
    by (auto dest:propa_property1)
  with propa have propa_ss: "\<forall>(q, \<tau>) \<in> set ?qs. ssa!q = \<tau> \<squnion>\<^bsub>f\<^esub>ss!q" by simp  
  with transf_ss_hd_w have propa_ss1:  "\<forall>(q, \<tau>) \<in> set ?qs. ssa!q =  (hd w # ?ss_hdw) \<squnion>\<^bsub>f\<^esub>ss!q" by auto

  from ss_nth_inA step_pres_bounded have "\<forall>(q, \<tau>) \<in> set ?qs. ss!q \<in> A" using hd_w_suc_lt_n fin_succ_hd_w
    by (auto simp add:step_def exec_def)
  from hd_w_ss_in_A this propa_ss1 have ss_lt_ssa_q: "\<forall>(q, \<tau>) \<in> set ?qs. ss!q \<sqsubseteq>\<^bsub>r\<^esub> ssa!q" 
    by (fastforce dest:Semilat.ub2[OF Semilat.intro, OF is_semi])
  
  from step_pres_bounded sorted_tl_w' set_ss len_ss dist
  have  "\<And>q. q \<notin> set(map fst ?qs) \<Longrightarrow> q < length ss \<Longrightarrow> (fst(propa f ?qs ss (tl w)))!q = ss!q"     
    by (auto intro:propa_property2)
  with propa have exec2: "\<And>q. q \<notin> set(map fst ?qs) \<Longrightarrow> q < length ss \<Longrightarrow> ssa!q = ss!q" by auto
 
  have tran_ss_ssa: "\<forall>p<length ss. ss!p \<sqsubseteq>\<^bsub>r\<^esub> ssa!p" 
  proof(intro strip)
    fix p 
    assume "p < length ss" 
    with ssa_nth_inA have ssa_p_inA: "ssa!p \<in> A" using `length ssa = n` `length ss = n` by auto
    from ss_nth_inA have ss_p_inA: "ss!p \<in> A" using  `length ss = n` `p < length ss` by auto
    
    show " ss ! p \<sqsubseteq>\<^bsub>r\<^esub> ssa ! p" 
    proof(cases "p \<in> succs (hd w)")
      case True
      then show "ss!p \<sqsubseteq>\<^bsub>r\<^esub>  ssa!p" using ss_lt_ssa_q using fin_succ_hd_w by (auto simp add:step_def exec_def)
     next
       case False
       then have "p \<notin> set (map fst ?qs)" using fin_succ_hd_w by (auto simp add:step_def exec_def)
       then show ?thesis using exec2 `p < length ss` using ssa_p_inA ss_p_inA 
         by(auto simp add:step_def exec_def intro: Semilat.orderI[OF Semilat.intro, OF is_semi])
    qed
  qed
  then have "\<forall>p<length ss0. ss ! p \<sqsubseteq>\<^bsub>r\<^esub> ssa ! p" using len_ss0_ss by auto
  with lt1  have "\<forall>p<length ss0. ss0!p \<sqsubseteq>\<^bsub>r\<^esub> ssa!p" using ss0_nth_inA ssa_nth_inA  ss_nth_inA  using len_ss0_ss len_ss0_ssa 
    by (auto intro: order_trans Semilat.orderI[OF Semilat.intro, OF is_semi])
  with len_ss0_ssa
  have g1: "ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ssa" by (auto simp only:Listn.le_def lesssub_def lesub_def intro:list_all2_all_nthI)

  have "(\<forall>ts\<in>list n A. ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ts \<and> (\<forall>p<n. stable r step ts p) \<longrightarrow> ssa [\<sqsubseteq>\<^bsub>r\<^esub>] ts)" 
  proof(intro strip)
    fix ts     
    assume ts_inA: "ts \<in> list n A" and ass: "ss0 [\<sqsubseteq>\<^bsub>r\<^esub>] ts \<and> (\<forall>p<n. stable r step ts p)" 
    let ?ts_hdw = "ts!(hd w)" 

    from ts_inA sta ass have ss_ts: "ss [\<sqsubseteq>\<^bsub>r\<^esub>] ts" and sta_ts: "(\<forall>p<n. stable r step ts p)" by auto 
    then have len_ss_ts: "length ss = length ts" and 
              ss_ts_hdw: "?ss_hdw \<sqsubseteq>\<^bsub>r\<^esub> ?ts_hdw "using le_listD len_ss hd_w_lt_n by auto 
    then have "sorted (rev (?ts_hdw)) \<and> set ?ts_hdw \<subseteq> set ?ss_hdw \<or> ?ss_hdw =?ts_hdw "
      by (auto simp add:r_def lesssub_def lesub_def  nodes_le_def)
    then have sorted_ts_hdw: "sorted (rev (?ts_hdw))" 
          and ts_ss_subset: "set ?ts_hdw \<subseteq> set ?ss_hdw" using sorted_ss_hdw
      by (auto simp add:r_def lesssub_def lesub_def  nodes_le_def)
    then have "\<forall>x\<in> set ?ts_hdw. x < hd w" using ss_lt_hd_w by auto
    with sorted_ts_hdw have sorted_hd_w_ts: "sorted (rev (hd w # ?ts_hdw))" 
      by (auto simp add:sorted_wrt_append)
    with sorted_hd_w_ss ts_ss_subset 
    have "(hd w # ?ss_hdw) \<sqsubseteq>\<^bsub>r\<^esub> (hd w # ?ts_hdw)" 
      by (auto simp add:transf_def lesssub_def lesub_def r_def  nodes_le_def)  
    then have transf_ss_ts: "transf (hd w) ?ss_hdw \<sqsubseteq>\<^bsub>r\<^esub> transf (hd w) ?ts_hdw" by (auto simp add:transf_def)

    from sta_ts hd_w_lt_n have sta_ts_hdw: "stable r step ts (hd w)" by auto

    from ss_hdw_nodes ts_ss_subset have "set ?ts_hdw \<subseteq> set nodes" by auto
    with hd_w_lt_n have hdw_ts_subset_nodes: "set (hd w # ?ts_hdw) \<subseteq> set nodes" using nodes_def n_def verts_set by auto
    with sorted_hd_w_ts have "(hd w # ?ts_hdw) \<in> ( (rev \<circ> sorted_list_of_set) ` (Pow (set nodes)))"
      by (fastforce intro: subset_nodes_inpow)
    then have transf_ts_inA: "(hd w #?ts_hdw) \<in> A" by (simp add:A_def)
    then have sorted_hdw_ts_hdw:  "sorted (rev (hd w # ?ts_hdw))" by (rule inA_is_sorted)   

    have "\<forall>p<length ssa. ssa!p \<sqsubseteq>\<^bsub>r\<^esub> ts!p" 
    proof(intro strip)
      fix p 
      assume p_lt_len_ssa: "p < length ssa"
      then have "p < length ss" and "p < n" using len_ssa len_ss by auto
      with ss_ts have ss_ts_p: "ss!p \<sqsubseteq>\<^bsub>r\<^esub> ts!p " using le_listD by auto  

      show "ssa ! p \<sqsubseteq>\<^bsub>r\<^esub> ts ! p" 
      proof(cases "p \<in> succs (hd w)")
        case True note p_in_succs_hdw = this
        then have "ss!p \<sqsubseteq>\<^bsub>r\<^esub> ssa!p" using ss_lt_ssa_q using fin_succ_hd_w by (auto simp add:step_def exec_def)

        from p_in_succs_hdw have ssa_p: "ssa!p = transf (hd w) (ss!hd w) \<squnion>\<^bsub>f\<^esub>ss!p" using propa_ss fin_succ_hd_w 
          by (auto simp add:step_def exec_def)        

        from sta_ts_hdw have transf_hdw_ts_hdw: "transf (hd w) (ts!hd w) \<sqsubseteq>\<^bsub>r\<^esub> ts!p" using p_in_succs_hdw fin_succ_hd_w
          by (auto simp add:step_def exec_def stable_def)
        then have ts_p_subset: "(hd w # ?ts_hdw) \<sqsubseteq>\<^bsub>r\<^esub> ts!p" by (auto simp add:transf_def)
        then have "(sorted (rev (ts!p)) \<and> set (ts!p)\<subseteq> set (hd w # ?ts_hdw)\<and> sorted (rev (hd w # ?ts_hdw))) \<or> 
                   hd w # ?ts_hdw = ts!p"
          by (auto simp add:r_def lesssub_def lesub_def nodes_le_def)
        then have "sorted (rev (ts!p)) \<and> set (ts!p)\<subseteq> set (hd w # ?ts_hdw)"
        proof
          assume "sorted (rev (ts ! p)) \<and> set (ts ! p) \<subseteq> set (hd w # ts ! hd w) \<and> sorted (rev (hd w # ts ! hd w))" 
          then show ?thesis by auto
        next
          assume " hd w # ts ! hd w = ts ! p"
          with sorted_hdw_ts_hdw show ?thesis by auto
        qed

        then have sorted_ts_p: "sorted (rev (ts!p))" 
              and ts_as_subset: "set (ts!p)\<subseteq> set (hd w # ?ts_hdw)"
          by auto
        with hdw_ts_subset_nodes have "set (ts!p) \<subseteq> set nodes" by auto
        with sorted_ts_p have "(ts!p) \<in> ( (rev \<circ> sorted_list_of_set) ` (Pow (set nodes)))" 
          by (fastforce intro: subset_nodes_inpow)
        then have ts_p_inA: "ts!p \<in> A" by (simp add:A_def)

        from sorted_hdw_ts_hdw have "\<forall>x\<in> set ?ts_hdw. x < hd w" by (auto simp add:sorted_wrt_append)
        with `hd w < n` have "\<forall>x\<in> set ?ts_hdw. x < n" by auto
        then have "set(hd w # ?ts_hdw) \<subseteq> set nodes"using `hd w < n` n_def verts_set nodes_def  by auto
        with sorted_hdw_ts_hdw have "hd w # ?ts_hdw  \<in> ( (rev \<circ> sorted_list_of_set) ` (Pow (set nodes)))" 
          by (fastforce intro: subset_nodes_inpow)
        then have "(hd w # ?ts_hdw) \<in> A" by (auto simp add:A_def)
        then have trans_hdw_ts_inA: "transf (hd w) (ts!hd w) \<in> A"  by (auto simp add:transf_def)

        have transf_hdw_ss_inA: "transf (hd w) ?ss_hdw \<in> A" using hd_w_ss_in_A  by (auto simp add:transf_def)
        have ss_p_inA: "ss!p \<in> A" using `p<length ss` ss_inA by auto
        from transf_ss_ts  transf_hdw_ts_hdw transf_hdw_ss_inA trans_hdw_ts_inA  ts_p_inA  have "transf (hd w) ?ss_hdw \<sqsubseteq>\<^bsub>r\<^esub> ts ! p" 
         by (auto intro: order_trans  Semilat.orderI[OF Semilat.intro, OF is_semi])          
        with `ss!p \<sqsubseteq>\<^bsub>r\<^esub> ts ! p` trans_hdw_ts_inA ss_p_inA transf_hdw_ss_inA ssa_p ts_p_inA
        show "ssa ! p \<sqsubseteq>\<^bsub>r\<^esub> ts ! p" by (auto intro: Semilat.lub[OF Semilat.intro, OF is_semi])
      next
        case False
        then have "p \<notin> set (map fst ?qs)" using fin_succ_hd_w by (auto simp add:step_def exec_def)
        then have "ssa!p = ss!p"using exec2 p_lt_len_ssa len_ss len_ssa
          by(auto simp add:step_def exec_def)    
        with ss_ts_p show ?thesis by auto
      qed
    qed
    with `length ss = length ts` len_ss len_ssa
    show "ssa [\<sqsubseteq>\<^bsub>r\<^esub>] ts" by (auto simp only:Listn.le_def lesssub_def lesub_def intro:list_all2_all_nthI)
  qed
  with g1 show ?thesis by auto
qed

lemma in_list_nA_refl: "ss \<in> list n A  \<Longrightarrow>  ss [\<sqsubseteq>\<^bsub>r\<^esub>] ss"
  apply (unfold Listn.le_def lesssub_def lesub_def)
proof-
  assume "ss \<in> list n A"
  then have "set ss \<subseteq> A" and "length ss = n" by auto
  then have "\<forall>i<n. ss!i \<in> A" by auto
  then have "\<forall>i<length ss. ss!i \<sqsubseteq>\<^bsub>r\<^esub> ss!i" 
    by (auto simp add:r_def lesssub_def lesub_def nodes_le_def ) 
  then show " list_all2 r ss ss" by (auto simp add:lesssub_def lesub_def intro: list_all2_all_nthI)
qed

lemma iter_dom: 
 assumes "wf_dom ss0 w0"
 shows "iter f step ss0 w0 = (ss',w') \<longrightarrow> 
        wf_dom ss' w' \<and> 
        stables r step ss' \<and> 
        ss0 [\<sqsubseteq>\<^sub>r] ss' \<and>
        (\<forall>ts\<in>list n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> ss' [\<sqsubseteq>\<^sub>r] ts)"
  using assms
  apply (unfold iter_def stables_def)
  apply (rule_tac P = "\<lambda>(ss,w). wf_dom ss w \<and> ss0 [\<sqsubseteq>\<^sub>r] ss \<and> (\<forall>ts\<in>list n A. ss0 [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> ss [\<sqsubseteq>\<^sub>r] ts)" 
              and r =  "{(ss',ss). ss [\<sqsubset>\<^sub>r] ss'} <*lex*> (\<lambda>(x,y). (sorted_list_of_set x, sorted_list_of_set y)) ` finite_psubset"  
         in while_rule)

  \<comment> \<open>Invariant holds initially:\<close>
      apply(fastforce simp add: wf_dom_def intro:wf_dom_le)
  
  \<comment> \<open>Invariant is preserved:\<close>
     apply clarsimp
     apply (rule conjI)
      apply(fastforce dest:propa_dom_invariant)
     apply(simp add:stables_def)
     apply (rule propa_dom_invariant_aux2)
          apply assumption+

  \<comment> \<open>Postcondition holds upon termination:\<close>
    apply(clarsimp simp add: stables_def split_paired_all)
    apply(subgoal_tac "length ss0 = n")
     apply(simp add:wf_dom_def)+

  \<comment> \<open>Well-foundedness of the termination relation:\<close>
   apply clarsimp 
   apply(simp add:wf_listn_termination_rel)

  \<comment> \<open>Loop decreases along termination relation:\<close>
  apply clarsimp
  apply (fastforce intro:propa_termination) 
  done   

lemma wf_start: "wf_dom start (unstables r step start)" 
proof-
  let ?w0 = "unstables r step start" 
  have sorted_w: "sorted ?w0" using unstables_def  by (simp add:sorted_less_sorted_list_of_set)
  have w0_lt_n: "\<forall>x\<in>set ?w0. x < n" using unstables_def len_start_is_n by auto 
 
  have neq_all: "\<forall>p < n. start!p \<noteq> rev [0..< n] \<longrightarrow> (\<forall>x\<in>set (start!p). x < p) " 
  proof(intro strip)
    fix p x
    assume p_lt_n: "p < n" and p_neq_all: "start ! p \<noteq> rev [0..< n]" and x_in: "x \<in> set (start ! p)"
    then have "p = 0" using start_nth_lt0_all len_start_is_n by auto
    with start_nth0_empty show "x < p" using x_in by auto
  qed
 
  have eq_all:"(\<forall>p < n. start!p = rev [0..< n] \<longrightarrow> (\<exists>x\<in> set ?w0. (x,p)\<in> g_E G \<and> x < p))"
  proof(intro strip)
    fix p
    assume p_lt_n: "p < n" and p_eq_all: "start ! p = rev [0..< n]" 
    from `p < n` have "p = 0 \<or> p > 0 \<and> p < length start" using len_start_is_n by auto
    with p_eq_all have "p > 0" and p_lt_len_start: "p < length start" using start_nth0_empty n_def nodes_def len_verts_gt0 by auto
    then have "p \<in> set (g_V G) - {0}" using len_start_is_n n_def nodes_def verts_set by auto 
    with dfst obtain prev where "(prev, p) \<in> g_E G" and "prev < p" by auto
    then have "succs prev \<noteq> {}" and "prev < length start" using p_lt_len_start by (auto simp add:succs_def)  
    with unstable_start  have "prev \<in> set ?w0" by auto
    with `(prev, p) \<in> g_E G` `prev < p`
    show "\<exists>x\<in>set (unstables r step start). (x, p) \<in> g_E G \<and> x < p"  by auto     
  qed

  have "\<forall>p<n. (p \<notin> set (unstables r step start)\<longrightarrow> stable r step start p)"
    by (unfold unstables_def) (simp add:n_def start_def nodes_def)
  with sorted_start_nth neq_all eq_all start_subset_A sorted_w len_start_is_n w0_lt_n show ?thesis by (auto simp only:wf_dom_def) 
qed

lemma iter_dom_properties:
 "iter f step start (unstables r step start) = (ss',w') \<longrightarrow> 
  wf_dom ss' w' \<and> 
  stables r step ss' \<and> 
  start [\<sqsubseteq>\<^sub>r] ss' \<and>
  (\<forall>ts\<in>list n A. start [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> ss' [\<sqsubseteq>\<^sub>r] ts)"
  using iter_dom[OF wf_start] by auto

lemma iter_dom_properties2:
 "iter f step start (unstables r step start) = (ss',w') \<longrightarrow> ss' \<in> list n A"
  using iter_dom_properties by (auto simp only:wf_dom_def list_def)

lemma iter_dom_termination: 
  "iter f step start (unstables r step start) = (ss,w) \<longrightarrow> 
   w \<noteq> [] \<longrightarrow>
   propa f (step (hd w) (ss!(hd w))) ss (tl w) = (ss, tl w)"
proof (intro strip)
  assume iter: "iter f step start (unstables r step start) = (ss, w)" and w_n_nil: "w \<noteq> []"
  with iter_dom_properties 
  have stas: "stables r step ss" 
   and wf_ss_w: "wf_dom ss w" 
   and start_le_ss: "start [\<sqsubseteq>\<^sub>r] ss" by auto
  from stas have sta_p: "(\<forall>p < size ss. stable r step ss p)"by (auto simp add:stables_def)

  from wf_ss_w have n_w_sta:  "\<forall>p<n. p \<notin>set w \<longrightarrow>  stable r step ss p" 
                      and len_eq: "length ss = n" 
                      and w_lt_n: "\<forall>x\<in> set w. x < n" 
                      and ss_inA: "\<forall>x\<in>set ss. x \<in>  A" 
                      and sorted_w: "sorted w "  by (auto simp add:wf_dom_def)
  from w_lt_n have hd_w_lt_n: "hd w < n" using w_n_nil by auto 
  then have hd_w_in_verts: "hd w \<in> set (g_V G)" using n_def nodes_def verts_set by auto
  then have fin_succ_hd_w: "finite (succs (hd w))" using fin_succs hd_w_in_verts by auto  

  let ?ss_hdw = "ss!hd w"
  let ?qs = "step (hd w) ?ss_hdw"  

  from hd_w_lt_n have dist: "distinct (map fst ?qs)" using distinct_p by auto

  from wf_ss_w w_n_nil have hdw_ss_subset_nodes: "set (hd w # ?ss_hdw) \<subseteq> set nodes"
                        and sorted_hd_w_ss: "sorted (rev (hd w # ?ss_hdw))" 
                        and hd_w_ss_in_A: " ((hd w # ?ss_hdw)) \<in> A"
                        and step_pres_bounded: "\<forall>(q, \<tau>)\<in>set ?qs. q < length ss \<and> \<tau> \<in> A"
    using propa_dom_invariant_auxi by auto  

  let ?res = "propa f (step (hd w) (ss!(hd w))) ss (tl w) "
  have "propa f (step (hd w) (ss!(hd w))) ss (tl w) = ?res" by simp
  then obtain ss' w' where propa: "propa f (step (hd w) (ss!(hd w))) ss (tl w) = (ss', w')" by (cases ?res) auto

  from sorted_w have sorted_tl_b: "sorted (tl w)" by (induct w) auto
  from ss_inA have set_a: "set ss \<subseteq> A" by auto
  with step_pres_bounded sorted_tl_b len_eq dist have "\<forall>(q, \<tau>) \<in> set ?qs. (fst(propa f ?qs ss (tl w)))!q = \<tau> \<squnion>\<^bsub>f\<^esub>ss!q" 
    by (auto dest:propa_property1)
  with propa have propa_ss1:  "\<forall>(q, \<tau>) \<in> set ?qs. ss'!q =  (hd w # ?ss_hdw) \<squnion>\<^bsub>f\<^esub>ss!q" by (simp add:step_def exec_def transf_def)

  from step_pres_bounded sorted_tl_b set_a  len_eq dist
  have  "\<And>q. q \<notin> set(map fst ?qs) \<Longrightarrow> q < length ss \<Longrightarrow> (fst(propa f ?qs ss (tl w)))!q = ss!q" 
    by (auto intro:propa_property2)
  with propa have g2: "\<And>q. q \<notin> set(map fst ?qs) \<Longrightarrow> q < length ss \<Longrightarrow> ss'!q = ss!q" by auto

  from sorted_w have sorted_tl_w: "sorted (tl w)" by (induct w)  auto
  with step_pres_bounded set_a 
  have fst_propa: "fst (propa f ?qs ss (tl w)) = (merges f ?qs ss)"   
   and snd_propa: "snd (propa f ?qs ss (tl w)) = (sorted_list_of_set ({q. \<exists>t.(q,t)\<in>set ?qs \<and> t \<squnion>\<^bsub>f\<^esub> (ss!q) \<noteq> ss!q} \<union> set (tl w)))"
    using decomp_propa by auto
  with propa have len_ss_eq_ss': "length ss' = length ss" using length_merges by auto

  have ss_ss'_eq:  "\<forall>i<n. (fst (propa f ?qs ss (tl w)))!i = ss!i"
  proof(intro strip)
    fix i 
    assume "i < n" 
    then have i_lt_len_ss: "i < length ss" using `length ss = n` by auto
    show "fst (propa f ?qs ss (tl w)) ! i = ss ! i "
    proof(cases "i \<in> set(map fst ?qs)")
      case True
      assume ass1: "i \<in> set (map fst ?qs)" 
      with propa_ss1 have ss': "ss'!i = (hd w # ?ss_hdw) \<squnion>\<^bsub>f\<^esub>ss!i" by (auto simp add: step_def exec_def)    
      from ass1 have "i \<in> set (g_V G)" using succ_in_G fin_succ_hd_w by (auto simp add:step_def exec_def)
      then have q_lt_len_ss: "i < length ss" using len_eq by (auto simp add:n_def nodes_def verts_set)      
      from hd_w_lt_n len_eq stas have "stable r step ss (hd w)" by (auto simp add:stables_def)
      with ass1 have "(hd w # ?ss_hdw) \<sqsubseteq>\<^sub>r ss!i" by (auto simp add:stables_def stable_def step_def exec_def transf_def)
      then have "set (ss!i) \<subseteq> set (hd w # ?ss_hdw) \<or> (hd w # ?ss_hdw) = ss!i" by (auto simp add:lesssub_def lesub_def r_def nodes_le_def)
      then have set_ss_q_subst_hdw_ss: "set (ss!i) \<subseteq> set (hd w # ?ss_hdw)" by (rule disjE)(auto simp add:lesssub_def lesub_def r_def nodes_le_def)
      then have ss_q: "set (ss!i) \<inter> set (hd w # ?ss_hdw) = set (ss!i)" by auto
      from wf_ss_w q_lt_len_ss have sorted_ss_q: "sorted (rev (ss!i))" by (simp add:wf_dom_def)
      with sorted_hd_w_ss have ss_q': "set (ss'!i) = set (ss!i) \<inter> set (hd w # ?ss_hdw)" 
                           and sorrted_ss_q': "sorted (rev (ss'!i))" using ss'
        by (auto simp add:plussub_def f_def nodes_sup_def inter_sorted_correct) 
      with ss_q sorted_ss_q sorrted_ss_q' show ?thesis using sorted_less_rev_set_unique propa by auto   
    next
      case False note i_nin = this
      from step_pres_bounded sorted_tl_b set_a len_eq dist propa i_lt_len_ss i_nin 
      show ?thesis by (fastforce dest:propa_property2)
    qed
  qed
  with len_ss_eq_ss' have eq_ss: "ss' = ss" using len_eq propa by (auto simp add:list_eq_iff_nth_eq)
  then have qs_empty: "(({q. \<exists>t.(q,t)\<in>set ?qs \<and> t \<squnion>\<^bsub>f\<^esub> (ss!q) \<noteq> ss!q} \<union> set (tl w))) =  (set (tl w))" 
   using propa_ss1 propa transf_def step_def exec_def by fastforce
  with snd_propa have "snd (propa f ?qs ss (tl w)) = sorted_list_of_set (set (tl w))" using sorted_w by auto
  with sorted_tl_w have "snd (propa f ?qs ss (tl w)) = tl w" by (fastforce dest:sorted_less_set_eq)
  with propa have "w' = tl w" by simp
  with eq_ss show "propa f (step (hd w) (ss ! hd w)) ss (tl w) = (ss, tl w)" using propa by auto
qed
  
lemma dom_iter_properties: 
  "iter f step start (unstables r step start) = (ss, w) \<longrightarrow> 
   ss!0 = [] \<and> 
   (\<forall>p<n. p \<noteq> 0 \<longrightarrow> ss!p \<noteq> (rev [0..<n]))"
proof(intro strip)
  assume iter: "iter f step start (unstables r step start) = (ss, w)"
  with iter_dom_properties iter_dom_properties2
  have "wf_dom ss w" 
   and stas: "stables r step ss" 
   and start_le_ss: "start [\<sqsubseteq>\<^sub>r] ss" 
   and ss_inA: "ss \<in> list n A" by auto
  then have len_ss_n: "length ss = n" by auto

  from start_le_ss have "start!0 \<sqsubseteq>\<^sub>r ss!0" using start_len_gt_0
    by (unfold Listn.le_def lesssub_def lesub_def) (auto simp add:lesssub_def lesub_def intro:list_all2_nthD)
  then have ss_0th: "ss!0 = []" by (auto simp add:r_def nodes_le_def lesssub_def lesub_def start_def)
 
  have "(\<forall>p<n. p \<noteq> 0 \<longrightarrow> ss ! p \<noteq>  (rev [0..<n]))"  
  proof(intro strip, rule ccontr)
    fix p
    assume p_lt_n: "p < n" and p_neq_0: "p\<noteq>0" and ss_p_eq_all: "\<not> ss ! p \<noteq> rev [0..<n]"
    with stas len_ss_n  have step_sta: "\<forall>(q,\<tau>) \<in> set (step p (ss!p)). \<tau> \<sqsubseteq>\<^sub>r ss!q" by (simp add: stables_def stable_def)
    from p_lt_n len_start_is_n verts_set have p_is_vert: "p \<in> set (g_V G)" by (auto simp add:n_def nodes_def)
    then have step_p: "\<forall>(q,\<tau>) \<in> set (step p (ss!p)). q \<in> succs p" using fin_succs by (auto simp add:step_def exec_def)

    from p_is_vert p_neq_0 dfst obtain prev where "(prev, p) \<in> g_E G" and prev_lt_p: "prev < p" by auto
    then have prev_lt_n: "prev < n" 
         and prev_p: "p \<in> succs prev" 
         and "prev \<in> set (g_V G)" using p_lt_n tail_is_vert by (auto simp add:succs_def)     
    then have fin_suc_prev : "finite (succs prev)" using fin_succs by auto

    let ?prev_\<tau> = "ss!prev"    

    from prev_lt_n stas `length ss = n` have "stable r step ss prev" by (auto simp add:stables_def)
    then have "\<forall>(q,\<tau>) \<in> set (step prev ?prev_\<tau>). (prev # ?prev_\<tau>) \<sqsubseteq>\<^sub>r ss!q"
      by (auto simp add: stable_def transf_def step_def exec_def)
    with prev_p have "(prev # ?prev_\<tau>) \<sqsubseteq>\<^bsub>r\<^esub> ss ! p" using fin_suc_prev by (auto simp add: stable_def transf_def step_def exec_def)
    with ss_p_eq_all have "sorted (rev (prev # ?prev_\<tau>)) \<and> {0..<n} \<subseteq> set (prev # ?prev_\<tau>) \<or> (prev # ss ! prev) =  (rev [0..<n])"
      by (auto simp add:r_def lesssub_def lesub_def nodes_le_def)
    then have "sorted (rev (prev # ?prev_\<tau>)) \<and> {0..<n} \<subseteq> set (prev # ?prev_\<tau>)" by(rule disjE)  auto
    then have sorted_rev: "sorted (rev (prev # ?prev_\<tau>))" 
          and pres_subset: "{0..<n} \<subseteq> set (prev # ?prev_\<tau>)" by auto    
    then have prev_set: "\<forall>x\<in> set ?prev_\<tau>. x < prev" by (induct ?prev_\<tau>) (auto simp add:sorted_wrt_append)
    
    from p_lt_n prev_lt_p have "prev < n - 1" using n_def nodes_def len_verts_gt0 by auto
    with prev_set have prev_lt_n: "\<forall>x\<in>set(prev # ?prev_\<tau>). x < n - 1" by auto
    from pres_subset have "n - 1 \<in> set (prev # ?prev_\<tau>)" using n_def nodes_def len_verts_gt0 by fastforce
    with prev_lt_n show False by auto
  qed

  with ss_0th show " ss ! 0 = [] \<and> (\<forall>p<n. p \<noteq> 0 \<longrightarrow> ss ! p \<noteq> rev [0..<n])" by auto
qed

lemma dom_iter_properties2: 
  "iter f step start (unstables r step start) = (ss,w) \<longrightarrow> (\<forall>p<n.  ss!p \<noteq> (rev [0..<n]))"
proof(intro strip)
  fix p 
  assume iter: "iter f step start (unstables r step start) = (ss, w)" and p: "p < n"
  show "ss ! p \<noteq> (rev [0..<n])"
  proof(cases "p = 0")
    case True  
    with iter have "ss!p = []" by  (auto simp add:dom_iter_properties)
    then show ?thesis using n_def nodes_def len_verts_gt0 by auto
  next
    case False
    with iter p show ?thesis by (auto simp add:dom_iter_properties)
  qed
qed

lemma kildall_dom_properties:
  "kildall r f step start \<in> list n A \<and> 
   stables r step (kildall r f step start) \<and> 
   start [\<sqsubseteq>\<^sub>r] (kildall r f step start) \<and>
   (\<forall>ts\<in>list n A. start [\<sqsubseteq>\<^sub>r] ts \<and> stables r step ts \<longrightarrow> (kildall r f step start) [\<sqsubseteq>\<^sub>r] ts)"  (is "PROP ?P")
  by (case_tac "iter f step start (unstables r step start)")(simp add: kildall_def iter_dom_properties iter_dom_properties2)

lemma dom_kildall_stables: "stables r step (dom_kildall start)" 
  using kildall_dom_properties 
  by(unfold dom_kildall_def nodes_semi_def) (simp add: r_def f_def step_def)

lemma dom_kildall_entry: "dom_kildall start !0 = []" 
  by (case_tac "iter f step start (unstables r step start)")
     (auto simp add:dom_kildall_def nodes_semi_def dom_iter_properties r_def f_def step_def kildall_def)

lemma zero_dom_zero: "dom i 0 \<longleftrightarrow> i = 0"
  using start_def n_def nodes_def dom_kildall_entry  by (simp add:dom_def)

(*lemma sadom_succs:  "strict_dom i j \<Longrightarrow> j \<in> succs k \<Longrightarrow> strict_dom i k"*)

lemma sdom_dom_succs: "strict_dom i j \<Longrightarrow> j \<in> succs k \<Longrightarrow> dom i k"
proof - 
  assume sdom_i_j: "strict_dom i j" and k_j: "j \<in> succs k" 
  then have j: "j \<in> set (g_V G)" 
        and k: "k \<in> set (g_V G)"  using verts_set succ_in_verts by auto
  then have j_lt_n: "j < n" and k_lt_n: "k < n"  using n_def nodes_def verts_set by auto

  have fin_succs_k: "finite (succs k)" using fin_succs k by auto
  with k_j have k_j2: "j \<in> set (rev (sorted_list_of_set(succs k)))" by auto

  let ?ss0 = "start"
  let ?w0 = "unstables r step start"
  let ?res = "dom_kildall start"

  have dom_kil: "?res = kildall r f step ?ss0" 
    by (auto simp add:dom_kildall_def r_def f_def step_def nodes_semi_def)

  have sorted_unstables: "sorted ?w0" by (auto simp add:unstables_def sorted_less_sorted_list_of_set)
  have ss: "?res = fst (iter f step ?ss0 ?w0)" by (auto simp add:dom_kildall_def kildall_def f_def step_def nodes_semi_def start_def r_def)
  then obtain ww where dom_iter: "iter f step ?ss0 ?w0 = (?res, ww)" by (cases "iter f step ?ss0 ?w0") auto  
  with iter_dom_properties have wf_res: "wf_dom (dom_kildall start) ww" by auto  
  with sdom_i_j have i_dom_j: "i \<in> set (?res!j)" by (auto simp add:strict_dom_def start_def n_def nodes_def)

  from wf_res have len_res: "length ?res = n" by (auto simp add:wf_dom_def)

  show "dom i k" 
  proof(rule ccontr)
    assume ass: "\<not> dom i k" 
    then have i_neq_k: "i \<noteq> k" by (auto simp add:dom_refl)
    with ass have "(\<exists>res. ?res!k = res \<and> i \<notin> set res)" using ass by (auto simp add:dom_def start_def nodes_def n_def)
    then show False
    proof -
      assume "\<exists>res. ?res ! k =  res \<and> i \<notin> set res"
      then obtain rs where k_dom: "?res ! k = rs" and i_notin_rs: "i \<notin> set rs" by auto     

      from iter_dom_properties dom_iter have "(\<forall>p < length ?res. stable r step ?res p)" by (auto simp add:stables_def)
      with k_lt_n have "stable r step ?res k" using len_res by auto      
      with k_dom have aux: "\<forall>(q,\<tau>) \<in> set (map (\<lambda>pc. (pc, (k # rs))) (rev (sorted_list_of_set(succs k)))). \<tau> \<sqsubseteq>\<^sub>r ?res!q"
        by (simp add:stable_def r_def step_def exec_def transf_def)      
      with k_j2 have "(k # rs) \<sqsubseteq>\<^sub>r ?res!j" by auto
      then have "set (?res!j) \<subseteq> set (k # rs) \<or> ?res!j = k#rs" 
        by (auto simp add:lesssub_def lesub_def nodes_semi_def nodes_le_def r_def f_def)
      then have "set (?res!j) \<subseteq> set (k # rs)" by auto        
      with i_dom_j i_neq_k have " i \<in> set rs" by auto
      with i_notin_rs show False by auto
    qed
  qed
qed

lemma adom_succs: "dom i j \<Longrightarrow> i \<noteq> j \<Longrightarrow> j \<in> succs k \<Longrightarrow> dom i k"
  by (auto intro: dom_sdom sdom_dom_succs)

lemma dom_kildall_is_strict: "j < length start \<Longrightarrow> dom_kildall start ! j = res \<Longrightarrow> j \<notin> set res" 
proof -
  assume j_dom: "dom_kildall start ! j = res" and j_lt: "j < length start" 
  from j_dom have iter_fst: "(fst (iter f step start (unstables r step start))) ! j = res" 
    by (auto simp add:dom_kildall_def r_def f_def step_def start_def nodes_semi_def kildall_def)
  then obtain ss w where iter: "iter f step start (unstables r step start) = (ss, w)" by fastforce
  with iter_fst have res: "ss!j = res" by auto
  with dom_iter_properties2 iter have res_neq_all: "res \<noteq> rev [0..<n]" using len_start_is_n  j_lt len_start_is_n by auto

  with iter iter_dom_properties have "\<forall>p < n. (ss!p) \<noteq> rev [0..< n] \<longrightarrow> (\<forall>x\<in>set ( (ss!p)). x < p)" by (auto simp add:wf_dom_def)  
  with j_lt len_start_is_n res res_neq_all have "(\<forall>x\<in>set res. x < j)" by (auto simp add:wf_dom_def) 
  then show "j \<notin> set res" by auto
qed

lemma sdom_asyc: "strict_dom i j \<Longrightarrow> j \<in> set (g_V G) \<Longrightarrow> i \<noteq> j"
proof-
  assume sdom_i_j: "strict_dom i j" and "j \<in> set (g_V G)" 
  then have j_lt: "j < length start" using start_def n_def nodes_def verts_set by auto
  let ?start = " [] # (replicate (length (g_V G) - 1) ( (rev[0..<length(g_V G)])))"
  have eq_start: "?start = start" using n_def nodes_def start_def by simp  
  from sdom_i_j have i_in: "i \<in> set (dom_kildall ?start !j)" by (auto simp add:strict_dom_def)
  from j_lt have j_nin: "j \<notin> set (dom_kildall ?start !j)" using eq_start by (simp add: dom_kildall_is_strict)
  with i_in  show "i \<noteq> j" by auto
qed


lemma propa_dom_invariant_complete:
  fixes i a b ss w 
  assumes b_n_nil: "b \<noteq> [] "
      and propa: "propa f (step (hd b) (a ! hd b)) a (tl b) = (ss, w) "
      and wf_a_b: "wf_dom a b"
      and non_strict: "\<forall>i. i < n \<and>  k \<notin> set (a!i) \<longrightarrow> non_strict_dominate k i "
    shows "wf_dom ss w \<and> (\<forall>i. i < n \<and>  k \<notin> set ( ss ! i) \<longrightarrow> non_strict_dominate k i)"  (is "?PROP ?P")
  using assms
proof-  
  let ?a_hdb = "a!hd b" 
  let ?qs = "step (hd b) (a!hd b)"
  from wf_a_b b_n_nil propa have wf_ss_w: "wf_dom ss w" using propa_dom_invariant by auto
  
  from wf_a_b have "\<forall>\<tau>\<in>set a. \<tau> \<in> A" 
               and sorted_b: "sorted b" 
               and len_a: "length a = n" 
               and b_lt_n: "\<forall>x\<in>set b. x < n  "by (auto simp add:wf_dom_def)
  then have set_a: "set a \<subseteq> A" by (auto intro:listI)
  from sorted_b have sorted_tl_b: "sorted (tl b)" using b_n_nil by (induct b) auto
  from b_lt_n b_n_nil have hd_b_lt_n: "hd b < n" by auto
  with n_def nodes_def verts_set have "hd b \<in> set (g_V G)" using b_n_nil  by auto
  then have fin_succ_hd_b: "finite (succs (hd b))" using fin_succs by auto 

  from wf_a_b b_n_nil have sorted_hd_b_a: "sorted (rev (hd b # ?a_hdb))"
                       and step_pres_bounded: " \<forall>(q, \<tau>)\<in>set (step (hd b) ?a_hdb). q < length a \<and> \<tau> \<in> A" 
    using propa_dom_invariant_auxi by auto 

  from hd_b_lt_n have dist: "distinct (map fst ?qs)" using distinct_p by auto
  with set_a step_pres_bounded sorted_tl_b len_a have "\<forall>(q, \<tau>) \<in> set ?qs. (fst(propa f ?qs a (tl b)))!q = \<tau> \<squnion>\<^bsub>f\<^esub>a!q" 
    by (auto dest:propa_property1)
  with propa have propa_ss1: "\<forall>(q, \<tau>) \<in> set ?qs. ss!q =  (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub>a!q" by (auto simp add:step_def exec_def transf_def)
  
  from step_pres_bounded sorted_tl_b set_a len_a dist
  have  "\<And>q. q \<notin> set(map fst ?qs) \<Longrightarrow> q < length a \<Longrightarrow> (fst(propa f ?qs a (tl b)))!q = a!q" 
    by (auto intro:propa_property2)
  with propa have exec2: "\<And>q. q \<notin> set(map fst ?qs) \<Longrightarrow> q < length a \<Longrightarrow> ss!q = a!q" by auto
 
  have "(\<forall>i. i < n \<and> k \<notin> set ( ss ! i) \<longrightarrow> non_strict_dominate k i)" 
  proof(intro strip)
    fix i
    let ?a_i = "a!i" 
    assume "i < n \<and> k \<notin> set ( ss ! i) "
    then have i_lt_n: "i < n" and k_nin_ss: "k \<notin> set (ss ! i) " by auto
    from non_strict have g: "i < n \<and> a ! i =  ?a_i \<and> k \<notin> set ?a_i \<Longrightarrow> non_strict_dominate k i" by auto 
    have sorted_a_i: "sorted (rev ?a_i)" using wf_a_b i_lt_n by (auto simp add:_wf_dom_def)

    show "non_strict_dominate k i" 
    proof(cases "i \<in> (succs (hd b))")
      case True note i_succ_hdb = this
      with propa_ss1 have ss_i: "ss!i =  (hd b # ?a_hdb) \<squnion>\<^bsub>f\<^esub> a!i" using fin_succ_hd_b by (auto simp add:step_def exec_def)
      then have "ss!i =  (hd b # ?a_hdb ) \<squnion>\<^bsub>f\<^esub> ?a_i" by auto
      with sorted_hd_b_a sorted_a_i have "set (ss!i) = set (hd b # ?a_hdb) \<inter> set ?a_i" 
                                     and ss_i_merge: "ss!i =  ((inter_sorted_rev (hd b # ?a_hdb) ?a_i))" 
        by (auto simp add:inter_sorted_correct f_def nodes_sup_def plussub_def)
      with k_nin_ss have k_nin': "k \<notin> set (hd b # ?a_hdb) \<inter> set ?a_i" by auto

      show ?thesis 
      proof(cases "k \<notin> set ?a_i")
        case True
        then show ?thesis using i_lt_n g by auto
      next 
        case False
        with k_nin' have "k \<notin> set ?a_hdb" and k_neq_hdb: "k \<noteq> hd b" by auto   
        with hd_b_lt_n non_strict have n_k_hdb: "non_strict_dominate k (hd b)" by auto
        from i_succ_hdb have "(hd b, i)\<in> g_E G" by (auto simp add:succs_def)        
        with n_k_hdb k_neq_hdb show ?thesis using non_sdominate_succ by auto
      qed      
    next
      case False      
      with exec2 have "ss!i = a!i" using fin_succ_hd_b len_a i_lt_n by (auto simp add:step_def exec_def)
      with k_nin_ss have "k \<notin> set (a!i)" by auto
      with non_strict show ?thesis using i_lt_n by fastforce
    qed
  qed

  with wf_ss_w show "?PROP ?P" by auto
qed

lemma start_non_sdom: " i < n \<and> start!i =  res \<and> k \<notin> set res \<longrightarrow> non_strict_dominate k i" 
proof(auto)
  assume i_lt_n: "i < n" and k_nin: "k \<notin> set (start ! i)"
  then have reach_i: "reachable i" using n_def nodes_def verts_set len_verts_gt0 reachable by  (simp add:reachable_def)
  then obtain pa where pa_i: "path_entry (g_E G) pa i" using reachable_path_entry by auto

  show "non_strict_dominate k i"
  proof(cases "k \<in> set (g_V G)")
    case True
    then have "k < n" using verts_set by (auto simp add:n_def nodes_def)
    then have k_in_verts: "k \<in> set (g_V G)" and k_in_verts': "k \<in> {0..<n}" using verts_set n_def nodes_def by auto

    show "non_strict_dominate k i"
    proof(cases "i = 0")
      case True then show ?thesis using any_sdominate_0 k_in_verts by auto
    next
      case False
      then have "start!i = (rev [0..<n])" using start_def i_lt_n n_def nodes_def by (simp add:start_def)
      with k_nin k_in_verts' show ?thesis by auto
    qed
  next
    case False note k_nin_verts = this
    have "\<forall>pa. path_entry (g_E G) pa i \<longrightarrow> set pa \<subseteq> set (g_V G)" using path_in_verts nodes_def by auto
    with k_nin_verts have k_nin: "\<forall>pa. path_entry (g_E G) pa i \<longrightarrow> k \<notin> set pa" 
      by (fastforce dest: contra_subsetD) 
    with pa_i have "k \<notin> set pa" by auto
    with pa_i show ?thesis by (auto simp add: non_strict_dominate_def) 
  qed
qed

lemma iter_dom_invariant_complete:
    shows "\<And>res.  iter f step start (unstables r step start) = (ss',w') \<longrightarrow> i < n \<and> ss'!i =  res \<and> k \<notin> set res \<longrightarrow> non_strict_dominate k i" 
  apply (unfold iter_def)  
  apply(rule_tac  
      P = "(\<lambda>(ss, w). wf_dom ss w \<and> (\<forall>i. (\<exists>rs. i < n \<and> ss!i =  rs \<and> k \<notin> set rs) \<longrightarrow> non_strict_dominate k i))" and
      r = "{(ss',ss). ss [\<sqsubset>\<^sub>r] ss'} <*lex*> (\<lambda>(x,y). (sorted_list_of_set x, sorted_list_of_set y)) ` finite_psubset" 
      in while_rule) 
  \<comment> \<open>Invariant holds initially:\<close>
      apply clarsimp
      apply (fastforce simp add:start_non_sdom wf_start)

  \<comment> \<open>Invariant is preserved:\<close>
     apply (fastforce dest:propa_dom_invariant_complete)

  \<comment> \<open>Postcondition holds upon termination:\<close>
    apply clarsimp    

  \<comment> \<open>Well-foundedness of the termination relation:\<close>
   apply (simp add:wf_listn_termination_rel)

  \<comment> \<open>Loop decreases along termination relation:\<close>
  apply clarsimp 
  apply (fastforce dest:propa_termination)
 
  done

end

end



