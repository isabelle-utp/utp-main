
section \<open>A kildall's algorithm for computing dominators\<close>

theory Dom_Kildall
imports Dom_Semi_List Listn "HOL-Library.While_Combinator"
begin

text \<open>A kildall's algorithm for computing dominators. 
      It uses the ideas and the framework of kildall's algorithm implemented in Jinja \cite{Kildall-AFP},
      and modifications are needed to make it work for a fast algorithm for computing dominators\<close>

type_synonym
  's step_type = "nat \<Rightarrow> 's \<Rightarrow> (nat \<times> 's) list"

type_synonym state_dom = "nat list "

primrec  propa :: 
  "'s binop \<Rightarrow> (nat \<times> 's) list \<Rightarrow> 's list \<Rightarrow> nat list \<Rightarrow> 's list * nat list"
where
  "propa f []      \<tau>s wl = (\<tau>s,wl)"
| "propa f (q'# qs) \<tau>s wl = (let (q,\<tau>) = q';
                             u =  (\<tau> \<squnion>\<^bsub>f\<^esub> \<tau>s!q);
                             wl' = (if u = \<tau>s!q then wl 
                                    else sorted_list_of_set (insert q (set wl)))
                         in propa f qs (\<tau>s[q := u]) wl')"

definition  iter :: 
  "'s binop \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat list \<Rightarrow> 's list \<times> nat list"
where
  "iter f step \<tau>s w =
   while (\<lambda>(\<tau>s,w). w \<noteq> [])
         (\<lambda>(\<tau>s,w). let p = hd w
                   in propa f (step p (\<tau>s!p)) \<tau>s (tl w))
         (\<tau>s,w)"

definition stable :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> nat \<Rightarrow> bool"
where
  "stable r step \<tau>s p \<longleftrightarrow> (\<forall>(q,\<tau>) \<in> set (step p (\<tau>s!p)). \<tau> \<sqsubseteq>\<^sub>r \<tau>s!q)"

definition unstables :: "state_dom ord \<Rightarrow>  state_dom step_type \<Rightarrow> state_dom list \<Rightarrow> nat list"
where
  "unstables r step \<tau>s = sorted_list_of_set  {p. p < size \<tau>s \<and> \<not> stable r step \<tau>s p}"

lemma init_worklist_is_sorted: "sorted (unstables r step \<tau>s)"
  by (simp add:sorted_less_sorted_list_of_set unstables_def)

definition  kildall :: "state_dom ord \<Rightarrow>state_dom binop  \<Rightarrow> state_dom step_type \<Rightarrow> state_dom list \<Rightarrow> state_dom list" where
  "kildall r f step \<tau>s = fst(iter f step \<tau>s (unstables r step \<tau>s))"

context cfg_doms

begin

definition transf :: "node \<Rightarrow> state_dom \<Rightarrow> state_dom " where 
"transf n input \<equiv>  (n # input)"

definition exec :: "node \<Rightarrow> state_dom \<Rightarrow> (node \<times> state_dom) list"
  where "exec n xs = map (\<lambda>pc. (pc, (transf n xs))) (rev (sorted_list_of_set(succs n)))"

lemma transf_res_is_rev: "sorted (rev ns) \<Longrightarrow> n > hd ns  \<Longrightarrow> sorted (rev ((transf n ( ns))))"
  by (induct ns) (auto simp add:transf_def sorted_wrt_append) 

abbreviation "start \<equiv>  [] # (replicate (length (g_V G) - 1) ( (rev[0..<length(g_V G)])))"

definition dom_kildall :: "state_dom list \<Rightarrow> state_dom list"
  where "dom_kildall = kildall (fst (snd nodes_semi)) (snd (snd nodes_semi)) exec"

definition dom:: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"dom i j \<equiv>(let res = (dom_kildall start) !j in i \<in> (set res) \<or> i = j )"

lemma dom_refl: "dom i i" 
  by (unfold dom_def) simp

definition strict_dom :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
"strict_dom i j \<equiv> (let res = (dom_kildall start) !j in  i \<in> set res)"


lemma strict_domI1: "(dom_kildall ([] # (replicate (length (g_V G) - 1) ( (rev[0..<length(g_V G)])))))!j =  res \<Longrightarrow> i \<in> set res \<Longrightarrow> strict_dom i j" 
  by (auto simp add:strict_dom_def )

lemma strict_domD: 
  "strict_dom i j \<Longrightarrow> 
  dom_kildall (( [] # (replicate (length (g_V G) - 1) ( (rev[0..<length(g_V G)])))))!j  =  a \<Longrightarrow> 
  i \<in> set a"  
  by (auto simp add:strict_dom_def )

lemma sdom_dom: "strict_dom i j \<Longrightarrow> dom i j"  
  by (unfold strict_dom_def) (auto simp add:dom_def)

lemma not_sdom_not_dom: "\<not>strict_dom i j \<Longrightarrow> i \<noteq> j \<Longrightarrow> \<not>dom i j"  
  by (unfold strict_dom_def) (auto simp add:dom_def)

lemma dom_sdom: "dom i j \<Longrightarrow> i \<noteq> j \<Longrightarrow> strict_dom i j" 
  by (unfold dom_def)  (auto simp add:dom_def strict_dom_def)

end


definition stables :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> 's list \<Rightarrow> bool"
where                                                             
  "stables r step \<tau>s \<longleftrightarrow> (\<forall>p < size \<tau>s. stable r step \<tau>s p)"

definition lesubstep_type :: "(nat \<times> 's) set \<Rightarrow> 's ord \<Rightarrow> (nat \<times> 's) set \<Rightarrow> bool"
    ("(_ /{\<sqsubseteq>\<^bsub>_\<^esub>} _)" [50, 0, 51] 50)
  where "A {\<sqsubseteq>\<^bsub>r\<^esub>} B \<equiv> \<forall>(p,\<tau>) \<in> A. \<exists>\<tau>'. (p,\<tau>') \<in> B \<and> \<tau> \<sqsubseteq>\<^sub>r \<tau>'"

notation (ASCII)
  lesubstep_type  ("(_ /{<='__} _)" [50, 0, 51] 50)

primrec pluslussub :: "'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"  ("(_ /\<Squnion>\<^bsub>_\<^esub> _)" [65, 0, 66] 65)
where
  "pluslussub [] f y = y"
| "pluslussub (x#xs) f y = pluslussub xs f (x \<squnion>\<^sub>f y)"
(*<*)
notation (ASCII)
  pluslussub  ("(_ /++'__ _)" [65, 1000, 66] 65)
(*>*)

definition bounded :: "'s step_type \<Rightarrow> nat \<Rightarrow> bool"
where
  "bounded step n \<longleftrightarrow> (\<forall>p<n. \<forall>\<tau>. \<forall>(q,\<tau>') \<in> set (step p \<tau>). q<n)"

definition pres_type :: "'s step_type \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> bool"
where
  "pres_type step n A \<longleftrightarrow> (\<forall>\<tau>\<in>A. \<forall>p<n. \<forall>(q,\<tau>') \<in> set (step p \<tau>). \<tau>' \<in> A)"

definition mono :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> bool"
where
  "mono r step n A \<longleftrightarrow>
    (\<forall>\<tau> p \<tau>'. \<tau> \<in> A \<and> p<n \<and> \<tau> \<sqsubseteq>\<^sub>r \<tau>' \<longrightarrow> set (step p \<tau>) {\<sqsubseteq>\<^bsub>r\<^esub>} set (step p \<tau>'))"

end