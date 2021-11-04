(*<*)
theory Operational
  imports Typing
begin
  (*>*)

chapter \<open>Operational Semantics\<close>

text \<open> Here we define the operational semantics in terms of a small-step reduction relation. \<close>

section \<open>Reduction Rules\<close>

text \<open> The store for mutable variables \<close>
type_synonym \<delta> = "(u*v) list"

nominal_function update_d :: "\<delta> \<Rightarrow> u \<Rightarrow> v \<Rightarrow> \<delta>" where
  "update_d [] _ _ = []"
| "update_d ((u',v')#\<delta>) u v = (if u = u' then ((u,v)#\<delta>) else ((u',v')# (update_d \<delta> u v)))"
  by(auto,simp add: eqvt_def update_d_graph_aux_def ,metis neq_Nil_conv old.prod.exhaust)
nominal_termination (eqvt) by lexicographic_order

text \<open> Relates constructor to the branch in the case and binding variable and statement \<close>
inductive find_branch :: "dc \<Rightarrow> branch_list  \<Rightarrow> branch_s  \<Rightarrow> bool" where
  find_branch_finalI:  "dc' = dc                                  \<Longrightarrow> find_branch dc' (AS_final (AS_branch dc x s ))  (AS_branch dc x s)"
| find_branch_branch_eqI: "dc' = dc                               \<Longrightarrow> find_branch dc' (AS_cons  (AS_branch dc x s) css)    (AS_branch dc x s)"
| find_branch_branch_neqI:  "\<lbrakk> dc \<noteq> dc'; find_branch dc' css cs \<rbrakk> \<Longrightarrow> find_branch dc' (AS_cons  (AS_branch dc x s) css) cs"
equivariance find_branch
nominal_inductive find_branch .

inductive_cases find_branch_elims[elim!]:
  "find_branch dc (AS_final cs') cs"
  "find_branch dc (AS_cons cs' css) cs"

nominal_function lookup_branch :: "dc \<Rightarrow> branch_list \<Rightarrow> branch_s option" where
  "lookup_branch dc (AS_final (AS_branch dc' x s)) = (if dc = dc' then (Some (AS_branch dc' x s)) else None)"
| "lookup_branch dc (AS_cons (AS_branch dc' x s) css) = (if dc = dc' then (Some (AS_branch dc' x s)) else lookup_branch dc css)"
       apply(auto,simp add: eqvt_def lookup_branch_graph_aux_def)
  by(metis neq_Nil_conv old.prod.exhaust s_branch_s_branch_list.strong_exhaust)
nominal_termination (eqvt) by lexicographic_order

text \<open> Reduction rules \<close>
inductive reduce_stmt :: "\<Phi> \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> bool"  (" _  \<turnstile> \<langle> _ , _\<rangle> \<longrightarrow> \<langle>  _ , _\<rangle>" [50, 50, 50] 50)  where
  reduce_if_trueI:  " \<Phi> \<turnstile> \<langle>\<delta>, AS_if [L_true]\<^sup>v s1 s2\<rangle> \<longrightarrow> \<langle>\<delta>, s1\<rangle> "
| reduce_if_falseI: " \<Phi> \<turnstile> \<langle>\<delta>, AS_if [L_false]\<^sup>v s1 s2\<rangle> \<longrightarrow> \<langle>\<delta>, s2\<rangle> "
| reduce_let_valI:  " \<Phi> \<turnstile> \<langle>\<delta>, AS_let x (AE_val v)  s\<rangle> \<longrightarrow> \<langle>\<delta>, s[x::=v]\<^sub>s\<^sub>v\<rangle>"  
| reduce_let_plusI: " \<Phi> \<turnstile>  \<langle>\<delta>, AS_let x (AE_op Plus ((V_lit (L_num n1))) ((V_lit (L_num n2))))  s\<rangle> \<longrightarrow> 
                           \<langle>\<delta>, AS_let x (AE_val (V_lit (L_num ( (( n1)+(n2)))))) s \<rangle> "  
| reduce_let_leqI:  "b = (if (n1 \<le> n2) then L_true else L_false) \<Longrightarrow> 
             \<Phi>  \<turnstile>  \<langle>\<delta>,  AS_let x  ((AE_op LEq (V_lit (L_num n1)) (V_lit (L_num n2)))) s\<rangle> \<longrightarrow> 
                                                          \<langle>\<delta>, AS_let x  (AE_val (V_lit b)) s\<rangle>"  
| reduce_let_eqI:  "b = (if (n1 = n2) then L_true else L_false) \<Longrightarrow> 
             \<Phi>  \<turnstile>  \<langle>\<delta>,  AS_let x  ((AE_op Eq (V_lit n1) (V_lit n2))) s\<rangle> \<longrightarrow> 
                                                          \<langle>\<delta>, AS_let x  (AE_val (V_lit b)) s\<rangle>"  
| reduce_let_appI:  "Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ z b c \<tau> s'))) = lookup_fun \<Phi> f \<Longrightarrow>  
             \<Phi>  \<turnstile>  \<langle>\<delta>, AS_let x  ((AE_app f v)) s\<rangle> \<longrightarrow> \<langle>\<delta>,  AS_let2 x \<tau>[z::=v]\<^sub>\<tau>\<^sub>v s'[z::=v]\<^sub>s\<^sub>v s\<rangle> "     
| reduce_let_appPI:  "Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ z b c \<tau> s'))) = lookup_fun \<Phi> f \<Longrightarrow>  
             \<Phi>  \<turnstile>  \<langle>\<delta>, AS_let x  ((AE_appP f b' v)) s\<rangle> \<longrightarrow> \<langle>\<delta>,  AS_let2 x \<tau>[bv::=b']\<^sub>\<tau>\<^sub>b[z::=v]\<^sub>\<tau>\<^sub>v s'[bv::=b']\<^sub>s\<^sub>b[z::=v]\<^sub>s\<^sub>v s\<rangle> "  
| reduce_let_fstI:  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x (AE_fst (V_pair v1 v2))  s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let x (AE_val v1)  s\<rangle>"
| reduce_let_sndI:  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x (AE_snd (V_pair v1 v2))  s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let x (AE_val v2)  s\<rangle>"
| reduce_let_concatI:  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x (AE_concat (V_lit (L_bitvec v1))  (V_lit (L_bitvec v2)))  s\<rangle> \<longrightarrow> 
                            \<langle>\<delta>, AS_let x (AE_val (V_lit (L_bitvec (v1@v2))))  s\<rangle>"
| reduce_let_splitI: " split n v (v1 , v2 )  \<Longrightarrow> \<Phi> \<turnstile> \<langle>\<delta>, AS_let x (AE_split (V_lit (L_bitvec v))  (V_lit (L_num n)))  s\<rangle> \<longrightarrow> 
                            \<langle>\<delta>, AS_let x (AE_val (V_pair (V_lit (L_bitvec v1)) (V_lit (L_bitvec v2))))  s\<rangle>"
| reduce_let_lenI:  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x (AE_len (V_lit (L_bitvec v)))  s\<rangle> \<longrightarrow> 
                              \<langle>\<delta>, AS_let x (AE_val (V_lit (L_num (int (List.length v)))))  s\<rangle>"
| reduce_let_mvar:  "(u,v) \<in> set \<delta> \<Longrightarrow>  \<Phi> \<turnstile> \<langle>\<delta>, AS_let x (AE_mvar u)  s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let x (AE_val v) s \<rangle>" 
| reduce_assert1I: "\<Phi> \<turnstile> \<langle>\<delta>, AS_assert c (AS_val v)\<rangle> \<longrightarrow> \<langle>\<delta>, AS_val v\<rangle>" 
| reduce_assert2I:  " \<Phi>  \<turnstile> \<langle>\<delta>, s \<rangle> \<longrightarrow> \<langle> \<delta>', s'\<rangle> \<Longrightarrow> \<Phi>  \<turnstile> \<langle>\<delta>, AS_assert c s\<rangle> \<longrightarrow> \<langle> \<delta>', AS_assert c s'\<rangle>"  
| reduce_varI: "atom u \<sharp> \<delta> \<Longrightarrow>  \<Phi>  \<turnstile>  \<langle>\<delta>, AS_var u \<tau> v s \<rangle> \<longrightarrow> \<langle> ((u,v)#\<delta>) , s\<rangle>"
| reduce_assignI: "  \<Phi>  \<turnstile>  \<langle>\<delta>, AS_assign u v \<rangle> \<longrightarrow> \<langle> update_d \<delta> u v , AS_val (V_lit L_unit)\<rangle>"
| reduce_seq1I: "\<Phi>   \<turnstile>  \<langle>\<delta>, AS_seq (AS_val (V_lit L_unit )) s \<rangle> \<longrightarrow> \<langle>\<delta>, s\<rangle>"
| reduce_seq2I: "\<lbrakk>s1 \<noteq> AS_val v ; \<Phi>  \<turnstile>  \<langle>\<delta>, s1\<rangle> \<longrightarrow> \<langle> \<delta>', s1'\<rangle> \<rbrakk> \<Longrightarrow> 
                          \<Phi>  \<turnstile>  \<langle>\<delta>, AS_seq s1 s2\<rangle> \<longrightarrow> \<langle> \<delta>', AS_seq s1' s2\<rangle>"
| reduce_let2_valI:  "\<Phi>  \<turnstile>  \<langle>\<delta>, AS_let2 x t (AS_val v) s\<rangle> \<longrightarrow> \<langle>\<delta>, s[x::=v]\<^sub>s\<^sub>v\<rangle>" 
| reduce_let2I:  " \<Phi>  \<turnstile> \<langle>\<delta>, s1 \<rangle> \<longrightarrow> \<langle> \<delta>', s1'\<rangle> \<Longrightarrow> \<Phi>  \<turnstile> \<langle>\<delta>, AS_let2 x t s1 s2\<rangle> \<longrightarrow> \<langle> \<delta>', AS_let2 x t s1' s2\<rangle>"  

| reduce_caseI:  "\<lbrakk> Some (AS_branch dc x' s') = lookup_branch dc cs \<rbrakk> \<Longrightarrow>  \<Phi> \<turnstile>  \<langle>\<delta>, AS_match (V_cons tyid dc v) cs\<rangle>  \<longrightarrow> \<langle>\<delta>, s'[x'::=v]\<^sub>s\<^sub>v\<rangle> "
| reduce_whileI: "\<lbrakk> atom x \<sharp> (s1,s2); atom z \<sharp> x \<rbrakk> \<Longrightarrow> 
                    \<Phi>  \<turnstile>  \<langle>\<delta>, AS_while s1 s2 \<rangle> \<longrightarrow> 
            \<langle>\<delta>, AS_let2 x (\<lbrace> z : B_bool | TRUE \<rbrace>) s1 (AS_if (V_var x) (AS_seq s2 (AS_while s1 s2))  (AS_val (V_lit L_unit))) \<rangle>"

equivariance reduce_stmt
nominal_inductive reduce_stmt .

inductive_cases reduce_stmt_elims[elim!]:
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_if (V_lit L_true) s1 s2\<rangle> \<longrightarrow> \<langle>\<delta> , s1\<rangle>"
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_if (V_lit L_false) s1 s2\<rangle> \<longrightarrow> \<langle>\<delta>,s2\<rangle>"
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x (AE_val v)  s\<rangle> \<longrightarrow> \<langle>\<delta>,s'\<rangle>"
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x  (AE_op Plus ((V_lit (L_num n1))) ((V_lit (L_num n2))))  s\<rangle> \<longrightarrow> 
            \<langle>\<delta>, AS_let x  (AE_val (V_lit (L_num ( (( n1)+(n2)))))) s \<rangle>"
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x  ((AE_op LEq (V_lit (L_num n1)) (V_lit (L_num n2)))) s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let x  (AE_val (V_lit b)) s\<rangle>"
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x  ((AE_app f v)) s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let2 x \<tau> (subst_sv s' x v ) s\<rangle> "  
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x  ((AE_len v)) s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let x  v' s\<rangle> "  
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x  ((AE_concat v1 v2)) s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let x  v' s\<rangle> " 
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_seq s1 s2\<rangle> \<longrightarrow> \<langle> \<delta>' ,s'\<rangle>"
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x  ((AE_appP  f b v)) s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let2 x \<tau> (subst_sv s' z v) s\<rangle> "  
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x  ((AE_split v1 v2)) s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let x  v' s\<rangle> " 
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_assert c s \<rangle> \<longrightarrow> \<langle>\<delta>, s'\<rangle> "
  "\<Phi> \<turnstile> \<langle>\<delta>, AS_let x  ((AE_op Eq (V_lit (n1)) (V_lit (n2)))) s\<rangle> \<longrightarrow> \<langle>\<delta>, AS_let x  (AE_val (V_lit b)) s\<rangle>"

inductive reduce_stmt_many :: "\<Phi> \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> bool"    ("_ \<turnstile> \<langle> _ , _\<rangle> \<longrightarrow>\<^sup>* \<langle>  _ , _\<rangle>" [50, 50, 50] 50)  where  
  reduce_stmt_many_oneI:  "\<Phi> \<turnstile> \<langle>\<delta>, s\<rangle> \<longrightarrow> \<langle>\<delta>', s'\<rangle>  \<Longrightarrow> \<Phi> \<turnstile> \<langle>\<delta>  , s\<rangle> \<longrightarrow>\<^sup>* \<langle>\<delta>', s'\<rangle> "
| reduce_stmt_many_manyI:  "\<lbrakk> \<Phi> \<turnstile> \<langle>\<delta>, s\<rangle> \<longrightarrow>   \<langle>\<delta>', s'\<rangle> ; \<Phi> \<turnstile>  \<langle>\<delta>', s'\<rangle> \<longrightarrow>\<^sup>* \<langle>\<delta>'', s''\<rangle> \<rbrakk> \<Longrightarrow> \<Phi> \<turnstile>  \<langle>\<delta>, s\<rangle> \<longrightarrow>\<^sup>* \<langle>\<delta>'', s''\<rangle>"

nominal_function  convert_fds :: "fun_def list \<Rightarrow> (f*fun_def) list" where
  "convert_fds [] = []"
| "convert_fds ((AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s)))#fs) = ((f,AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s)))#convert_fds fs)"
| "convert_fds ((AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s)))#fs) = ((f,AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s)))#convert_fds fs)"
  apply(auto)
  apply (simp add: eqvt_def convert_fds_graph_aux_def )
  using fun_def.exhaust fun_typ.exhaust fun_typ_q.exhaust neq_Nil_conv 
  by metis
nominal_termination (eqvt) by lexicographic_order

nominal_function  convert_tds :: "type_def list \<Rightarrow> (f*type_def) list" where
  "convert_tds [] = []"
| "convert_tds ((AF_typedef s dclist)#fs) = ((s,AF_typedef s dclist)#convert_tds fs)"
| "convert_tds ((AF_typedef_poly s bv dclist)#fs) = ((s,AF_typedef_poly s bv dclist)#convert_tds fs)"
  apply(auto)
  apply (simp add: eqvt_def convert_tds_graph_aux_def )
  by (metis type_def.exhaust neq_Nil_conv)
nominal_termination (eqvt) by lexicographic_order

inductive reduce_prog :: "p \<Rightarrow> v \<Rightarrow> bool" where
  "\<lbrakk> reduce_stmt_many \<Phi> [] s \<delta> (AS_val v) \<rbrakk> \<Longrightarrow>  reduce_prog (AP_prog \<Theta> \<Phi> [] s) v"

section \<open>Reduction Typing\<close>

text \<open> Checks that the store is consistent with @{typ \<Delta>} \<close>
inductive delta_sim :: "\<Theta> \<Rightarrow> \<delta> \<Rightarrow> \<Delta> \<Rightarrow> bool" ( "_  \<turnstile> _ \<sim> _ " [50,50] 50 )  where
  delta_sim_nilI:  "\<Theta> \<turnstile> [] \<sim> []\<^sub>\<Delta> "
| delta_sim_consI: "\<lbrakk> \<Theta> \<turnstile> \<delta> \<sim> \<Delta> ; \<Theta> ; {||} ; GNil \<turnstile> v \<Leftarrow> \<tau> ; u \<notin> fst ` set \<delta>   \<rbrakk> \<Longrightarrow> \<Theta> \<turnstile> ((u,v)#\<delta>) \<sim> ((u,\<tau>)#\<^sub>\<Delta>\<Delta>)" 

equivariance delta_sim
nominal_inductive delta_sim .

inductive_cases delta_sim_elims[elim!]:
  "\<Theta> \<turnstile> [] \<sim> []\<^sub>\<Delta>"
  "\<Theta> \<turnstile> ((u,v)#ds) \<sim> (u,\<tau>) #\<^sub>\<Delta> D"
  "\<Theta> \<turnstile> ((u,v)#ds) \<sim> D"

text \<open>A typing judgement that combines typing of the statement, the store and the condition that definitions are well-typed\<close>
inductive config_type ::  "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<Delta> \<Rightarrow> \<delta> \<Rightarrow> s \<Rightarrow> \<tau> \<Rightarrow>  bool"   ("_ ; _ ; _ \<turnstile> \<langle> _ , _\<rangle> \<Leftarrow> _ " [50, 50, 50] 50)  where 
  config_typeI: "\<lbrakk> \<Theta> ; \<Phi> ; {||} ; GNil ; \<Delta> \<turnstile> s \<Leftarrow> \<tau>; 
                (\<forall> fd \<in> set \<Phi>. \<Theta> ; \<Phi> \<turnstile> fd) ;
                \<Theta>  \<turnstile> \<delta> \<sim> \<Delta> \<rbrakk>
                \<Longrightarrow> \<Theta> ; \<Phi> ; \<Delta> \<turnstile> \<langle> \<delta>  , s\<rangle> \<Leftarrow>  \<tau>"
equivariance config_type
nominal_inductive config_type .

inductive_cases config_type_elims [elim!]:
  " \<Theta> ; \<Phi>  ; \<Delta> \<turnstile> \<langle> \<delta>  , s\<rangle> \<Leftarrow>  \<tau>"

nominal_function \<delta>_of  :: "var_def list \<Rightarrow> \<delta>" where
  "\<delta>_of [] = []"
| "\<delta>_of ((AV_def u t v)#vs) = (u,v) #  (\<delta>_of vs)" 
  apply auto
  using  eqvt_def \<delta>_of_graph_aux_def neq_Nil_conv old.prod.exhaust apply force
  using  eqvt_def \<delta>_of_graph_aux_def neq_Nil_conv old.prod.exhaust 
  by (metis var_def.strong_exhaust)
nominal_termination (eqvt) by lexicographic_order

inductive config_type_prog :: "p \<Rightarrow> \<tau> \<Rightarrow> bool"  (" \<turnstile> \<langle> _\<rangle> \<Leftarrow> _") where
  "\<lbrakk>
  \<Theta> ; \<Phi> ; \<Delta>_of \<G> \<turnstile> \<langle> \<delta>_of \<G>  , s\<rangle> \<Leftarrow>  \<tau>
\<rbrakk> \<Longrightarrow> \<turnstile>  \<langle> AP_prog \<Theta> \<Phi> \<G> s\<rangle> \<Leftarrow> \<tau>"

inductive_cases config_type_prog_elims [elim!]:
  "\<turnstile>  \<langle> AP_prog \<Theta> \<Phi> \<G> s\<rangle> \<Leftarrow> \<tau>"

end
