(*<*)
theory Wellformed
  imports  IVSubst BTVSubst
begin
  (*>*)

chapter \<open>Wellformed Terms\<close>

text \<open>We require that expressions and values are well-formed. This includes a notion
of well-sortedness. We identify a sort with a basic type and
define the judgement as two clusters of mutually recursive
inductive predicates. Some of the proofs are across all of the predicates and
although they seemed at first to be daunting, they have all
worked out well.\<close>

named_theorems ms_wb "Facts for helping with well-sortedness"

section \<open>Definitions\<close>

inductive wfV :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> v \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50] 50)  and
  wfC :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> c \<Rightarrow> bool" (" _ ; _ ; _   \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)  and         
  wfG :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> bool" (" _ ; _  \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50) and
  wfT :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ; _ ; _   \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)  and
  wfTs :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> (string*\<tau>) list \<Rightarrow> bool" (" _ ; _  ; _ \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)  and 
  wfTh :: "\<Theta> \<Rightarrow> bool" ("   \<turnstile>\<^sub>w\<^sub>f _ " [50] 50)  and
  wfB :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> b \<Rightarrow> bool" (" _ ; _  \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50) and
  wfCE :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> ce \<Rightarrow> b \<Rightarrow> bool" ("  _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50] 50) and
  wfTD :: "\<Theta> \<Rightarrow> type_def \<Rightarrow> bool" (" _ \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)          
  where

wfB_intI:  "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_int" 
| wfB_boolI:  "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_bool" 
| wfB_unitI:  "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_unit" 
| wfB_bitvecI:  "\<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_bitvec" 
| wfB_pairI:  "\<lbrakk> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b1 ; \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b2 \<rbrakk> \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_pair b1 b2" 

| wfB_consI:  "\<lbrakk>
   \<turnstile>\<^sub>w\<^sub>f \<Theta>; 
   (AF_typedef s dclist) \<in> set \<Theta> 
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_id s"

| wfB_appI:  "\<lbrakk> 
   \<turnstile>\<^sub>w\<^sub>f \<Theta>; 
   \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b;
   (AF_typedef_poly s bv dclist) \<in> set \<Theta> 
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_app s b"

| wfV_varI: "\<lbrakk> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; Some (b,c) = lookup \<Gamma> x \<rbrakk> \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_var x : b"
| wfV_litI: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_lit l : base_for_lit l"

| wfV_pairI: "\<lbrakk>
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b1 ; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : b2 
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f (V_pair v1 v2) : B_pair b1 b2"

| wfV_consI: "\<lbrakk>   
   AF_typedef s dclist \<in> set \<Theta>;
   (dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist ;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b' 
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_cons s dc v : B_id s"

| wfV_conspI: "\<lbrakk>   
    AF_typedef_poly s bv dclist \<in> set \<Theta>;
    (dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist ;
    \<Theta> ;  \<B>  \<turnstile>\<^sub>w\<^sub>f b;
    atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>, b , v);
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b'[bv::=b]\<^sub>b\<^sub>b 
\<rbrakk> \<Longrightarrow>
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_consp s dc b v : B_app s b"

| wfCE_valI : "\<lbrakk>             
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : b 
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_val v  : b"

| wfCE_plusI: "\<lbrakk>               
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int; 
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int 
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_op Plus v1 v2 : B_int"

| wfCE_leqI:"\<lbrakk>
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int; 
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int 
\<rbrakk> \<Longrightarrow>
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op LEq v1 v2 : B_bool"

| wfCE_eqI:"\<lbrakk>
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b; 
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : b 
\<rbrakk> \<Longrightarrow>
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op Eq v1 v2 : B_bool"

| wfCE_fstI: "\<lbrakk>               
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_pair b1 b2  
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_fst v1 : b1"

| wfCE_sndI: "\<lbrakk>             
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_pair b1 b2  
\<rbrakk> \<Longrightarrow>  
    \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_snd v1 : b2"

| wfCE_concatI: "\<lbrakk> 
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec ; 
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_bitvec 
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_concat v1 v2 : B_bitvec"

| wfCE_lenI: "\<lbrakk>                
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec 
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f CE_len v1 : B_int"

| wfTI : "\<lbrakk> 
    atom z \<sharp>  (\<Theta>, \<B>, \<Gamma>) ; 
    \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b;
    \<Theta>; \<B> ; (z,b,C_true) #\<^sub>\<Gamma> \<Gamma> \<turnstile>\<^sub>w\<^sub>f c 
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>"

| wfC_eqI: "\<lbrakk>  
                \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f e1  : b ; 
                 \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f e2  : b  \<rbrakk> \<Longrightarrow> 
                \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_eq e1 e2" 
| wfC_trueI: " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<Longrightarrow> \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f C_true "
| wfC_falseI: " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma>  \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_false "

| wfC_conjI: "\<lbrakk> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c1 ; \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c2 \<rbrakk> \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_conj c1 c2"
| wfC_disjI: "\<lbrakk> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c1 ; \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c2 \<rbrakk> \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_disj c1 c2"
| wfC_notI: "\<lbrakk>  \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c1  \<rbrakk> \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_not c1"
| wfC_impI: "\<lbrakk>  \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c1 ; 
                \<Theta>; \<B>; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c2 \<rbrakk> \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_imp c1 c2"

| wfG_nilI: " \<turnstile>\<^sub>w\<^sub>f \<Theta>  \<Longrightarrow> \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f GNil"
| wfG_cons1I: "\<lbrakk>  c \<notin> { TRUE, FALSE } ; 
                  \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; 
                  atom x \<sharp> \<Gamma> ; 
                  \<Theta>  ; \<B> ; (x,b,C_true)#\<^sub>\<Gamma>\<Gamma> \<turnstile>\<^sub>w\<^sub>f c ; wfB \<Theta> \<B> b  
               \<rbrakk> \<Longrightarrow>  \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f ((x,b,c)#\<^sub>\<Gamma>\<Gamma>)"
| wfG_cons2I: "\<lbrakk>  c \<in> { TRUE, FALSE } ; 
                  \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; 
                  atom x \<sharp> \<Gamma> ;  
                  wfB \<Theta> \<B> b   
                \<rbrakk> \<Longrightarrow>  \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f ((x,b,c)#\<^sub>\<Gamma>\<Gamma>)"

| wfTh_emptyI: " \<turnstile>\<^sub>w\<^sub>f []"

| wfTh_consI: "\<lbrakk>      
        (name_of_type tdef) \<notin> name_of_type ` set \<Theta> ;
        \<turnstile>\<^sub>w\<^sub>f \<Theta> ; 
       \<Theta> \<turnstile>\<^sub>w\<^sub>f  tdef \<rbrakk>  \<Longrightarrow>  \<turnstile>\<^sub>w\<^sub>f tdef#\<Theta>"

| wfTD_simpleI: "\<lbrakk>
        \<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f lst
      \<rbrakk> \<Longrightarrow> 
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef s lst )"

| wfTD_poly: "\<lbrakk> 
        \<Theta> ; {|bv|} ; GNil \<turnstile>\<^sub>w\<^sub>f lst 
       \<rbrakk> \<Longrightarrow>
      \<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef_poly s bv lst)"

| wfTs_nil: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f []::(string*\<tau>) list"
| wfTs_cons: "\<lbrakk> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau> ; 
                dc \<notin> fst ` set ts;
                \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ts::(string*\<tau>) list \<rbrakk> \<Longrightarrow> \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ((dc,\<tau>)#ts)"

inductive_cases wfC_elims:
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_true"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_false"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_eq e1 e2"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_conj c1 c2"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_disj c1 c2"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_not c1"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f C_imp c1 c2"

inductive_cases wfV_elims:
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_var x : b"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_lit l : b"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_pair v1 v2 : b"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_cons tyid dc v : b"
  "\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f V_consp tyid dc b v : b'"

inductive_cases wfCE_elims:
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_val v : b"
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op Plus v1 v2 : b"
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op LEq v1 v2 : b"
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_fst v1 : b"
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_snd v1 : b"
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_concat v1 v2 : b"
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_len v1 : b"
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op opp v1 v2 : b"
  " \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op Eq v1 v2 : b"

inductive_cases wfT_elims:
  "\<Theta>; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>::\<tau>"
  "\<Theta>; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<lbrace> z : b | c \<rbrace>"

inductive_cases wfG_elims:
  "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f GNil"
  "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (x,b,c)#\<^sub>\<Gamma>\<Gamma>"
  "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (x,b,TRUE)#\<^sub>\<Gamma>\<Gamma>"
  "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f (x,b,FALSE)#\<^sub>\<Gamma>\<Gamma>"

inductive_cases wfTh_elims:
  " \<turnstile>\<^sub>w\<^sub>f []"
  " \<turnstile>\<^sub>w\<^sub>f td#\<Pi>"  

inductive_cases wfTD_elims:
  "\<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef s lst )"  
  "\<Theta> \<turnstile>\<^sub>w\<^sub>f (AF_typedef_poly s bv lst )" 

inductive_cases wfTs_elims:
  "\<Theta>; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f ([]::((string*\<tau>) list))"
  "\<Theta>; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f ((t#ts)::((string*\<tau>) list))"

inductive_cases wfB_elims:
  " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_pair b1 b2" 
  " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_id s"
  " \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f B_app s b"

equivariance wfV 

text \<open>This setup of 'avoiding' is not complete and for some of lemmas, such as weakening,
do it the hard way\<close>
nominal_inductive wfV 
  avoids   wfV_conspI: bv | wfTI: z
proof(goal_cases)
  case (1 s bv dclist \<Theta> dc x b' c \<B> b \<Gamma> v)

  moreover hence "atom bv \<sharp>  V_consp s dc b v" using v.fresh fresh_prodN pure_fresh by metis
  moreover have "atom bv \<sharp> B_app s b" using b.fresh fresh_prodN pure_fresh 1 by metis
  ultimately show ?case using b.fresh v.fresh pure_fresh  fresh_star_def fresh_prodN by fastforce
next
  case (2 s bv dclist \<Theta> dc x b' c \<B> b \<Gamma> v)
  then show ?case by auto
next
  case (3 z \<Gamma> \<Theta> \<B> b c)
  then show ?case using \<tau>.fresh fresh_star_def fresh_prodN by fastforce
next
  case (4 z \<Gamma> \<Theta> \<B> b c)
  then show ?case by auto
qed

inductive 
  wfE :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> e \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50] 50)  and
  wfS :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> s \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50] 50)  and
  wfCS :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow>  tyid \<Rightarrow> string \<Rightarrow> \<tau> \<Rightarrow> branch_s \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _ ; _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50,50,50] 50)  and
  wfCSS :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow>  tyid \<Rightarrow> (string * \<tau>) list \<Rightarrow> branch_list \<Rightarrow> b \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ : _ " [50,50,50,50,50] 50)  and       
  wfPhi :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> bool" (" _  \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50)  and
  wfD :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> bool" (" _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ " [50,50] 50) and       
  wfFTQ :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> fun_typ_q \<Rightarrow> bool"  (" _  ; _ \<turnstile>\<^sub>w\<^sub>f _ " [50] 50) and
  wfFT :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> fun_typ \<Rightarrow> bool"  (" _ ; _ ; _ \<turnstile>\<^sub>w\<^sub>f _ " [50] 50)  where

wfE_valI : "\<lbrakk>
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : b 
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_val v  : b"

| wfE_plusI: "\<lbrakk> 
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int 
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_op Plus v1 v2 : B_int"

| wfE_leqI:"\<lbrakk>   
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_op LEq v1 v2 : B_bool"

| wfE_eqI:"\<lbrakk>   
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : b;
   b \<in> { B_bool, B_int, B_unit }
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_op Eq v1 v2 : B_bool"

| wfE_fstI: "\<lbrakk>  
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_pair b1 b2 
 \<rbrakk> \<Longrightarrow> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_fst v1 : b1"

| wfE_sndI: "\<lbrakk>  
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_pair b1 b2  
\<rbrakk> \<Longrightarrow>  
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_snd v1 : b2"

| wfE_concatI: "\<lbrakk>
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_bitvec 
\<rbrakk> \<Longrightarrow> 
   \<Theta> ; \<Phi> ; \<B> ; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_concat v1 v2 : B_bitvec"

| wfE_splitI: "\<lbrakk>
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int 
\<rbrakk> \<Longrightarrow> 
   \<Theta> ; \<Phi> ; \<B> ; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_split v1 v2 : B_pair B_bitvec B_bitvec"

| wfE_lenI: "\<lbrakk>
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_bitvec 
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f AE_len v1 : B_int"

| wfE_appI:  "\<lbrakk>
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
   Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f ;  
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b
\<rbrakk> \<Longrightarrow>   
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_app f v : b_of \<tau>"

| wfE_appPI:  "\<lbrakk>
    \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
    \<Theta>; \<B>  \<turnstile>\<^sub>w\<^sub>f b'; 
    atom bv \<sharp>  (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, b', v, (b_of \<tau>)[bv::=b']\<^sub>b);
    Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))) = lookup_fun \<Phi> f;  
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : (b[bv::=b']\<^sub>b)
\<rbrakk> \<Longrightarrow>   
    \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f (AE_appP f b' v) : ((b_of \<tau>)[bv::=b']\<^sub>b)"

| wfE_mvarI: "\<lbrakk>  
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
   (u,\<tau>) \<in> setD \<Delta> 
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_mvar u : b_of \<tau>" 

| wfS_valI: "\<lbrakk> 
    \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;  
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b ; 
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> 
\<rbrakk>  \<Longrightarrow> 
    \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f (AS_val v) : b"

| wfS_letI: "\<lbrakk> 
    wfE \<Theta> \<Phi> \<B> \<Gamma> \<Delta>  e b'  ;
    \<Theta> ; \<Phi> ; \<B> ; (x,b',C_true) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b;
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
    atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, e, b)
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f LET x = e IN s : b"

| wfS_assertI: "\<lbrakk> 
    \<Theta> ; \<Phi> ; \<B> ; (x,B_bool,c) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b;
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c ;
    \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
    atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, c, b, s)
\<rbrakk> \<Longrightarrow> 
    \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f ASSERT c IN  s : b"

| wfS_let2I: "\<lbrakk> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>  \<turnstile>\<^sub>w\<^sub>f s1 : b_of \<tau>  ; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>;
   \<Theta> ; \<Phi> ; \<B> ; (x,b_of \<tau>,C_true) #\<^sub>\<Gamma> \<Gamma> ; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b ;
   atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, s1, b,\<tau>)            
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f LET x : \<tau> = s1 IN s2 : b"

| wfS_ifI: "\<lbrakk>  
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : B_bool; 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : b ; 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b 
\<rbrakk> \<Longrightarrow>
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f IF v THEN s1 ELSE s2 : b"

| wfS_varI : "\<lbrakk> 
   wfT \<Theta> \<B> \<Gamma>  \<tau> ;  
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : b_of \<tau>; 
   atom u \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, \<tau>, v, b);
   \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  (u,\<tau>)#\<^sub>\<Delta>\<Delta> \<turnstile>\<^sub>w\<^sub>f s : b 
\<rbrakk> \<Longrightarrow> 
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f VAR u : \<tau> = v IN s : b "

| wfS_assignI: "\<lbrakk> 
   (u,\<tau>) \<in> setD \<Delta> ;   
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;  
   \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v  : b_of \<tau> 
\<rbrakk> \<Longrightarrow>
   \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f u ::= v : B_unit"

| wfS_whileI: "\<lbrakk> 
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : B_bool ; 
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b
\<rbrakk> \<Longrightarrow>  
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f WHILE s1 DO { s2 } : b"

| wfS_seqI: "\<lbrakk>
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 : B_unit ; 
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s2 : b 
\<rbrakk> \<Longrightarrow> 
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f s1 ;; s2 : b"

| wfS_matchI: "\<lbrakk> 
  wfV \<Theta>  \<B> \<Gamma>  v  (B_id tid) ;
  (AF_typedef tid dclist ) \<in> set \<Theta>;
  wfD \<Theta>  \<B> \<Gamma>  \<Delta> ;  
  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
  \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f cs : b 
\<rbrakk> \<Longrightarrow> 
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AS_match v cs : b "

| wfS_branchI: "\<lbrakk> 
  \<Theta> ; \<Phi> ; \<B> ; (x,b_of \<tau>,C_true) #\<^sub>\<Gamma> \<Gamma> ;  \<Delta> \<turnstile>\<^sub>w\<^sub>f s : b ;
  atom x \<sharp> (\<Phi>, \<Theta>, \<B>, \<Gamma>, \<Delta>, \<Gamma>,\<tau>);
  \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> 
\<rbrakk>  \<Longrightarrow> 
  \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  \<Delta> ; tid ; dc ;  \<tau>  \<turnstile>\<^sub>w\<^sub>f  dc x \<Rightarrow> s : b"

| wfS_finalI: "\<lbrakk>       
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b    
 \<rbrakk> \<Longrightarrow>  
  \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  \<Delta> ; tid ; [(dc,t)] \<turnstile>\<^sub>w\<^sub>f AS_final cs  : b "

| wfS_cons: "\<lbrakk>           
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dc ; t  \<turnstile>\<^sub>w\<^sub>f cs : b;
  \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dclist \<turnstile>\<^sub>w\<^sub>f css : b
 \<rbrakk> \<Longrightarrow>  
  \<Theta> ; \<Phi> ; \<B> ; \<Gamma> ;  \<Delta> ; tid ; (dc,t)#dclist \<turnstile>\<^sub>w\<^sub>f AS_cons cs css : b "

| wfD_emptyI: "\<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> \<Longrightarrow> \<Theta>  ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f []\<^sub>\<Delta>"

| wfD_cons: "\<lbrakk> 
  \<Theta>  ; \<B> ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f \<Delta>::\<Delta> ; 
  \<Theta>  ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau>; 
  u \<notin> fst ` setD \<Delta> 
\<rbrakk> \<Longrightarrow> 
  \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ((u,\<tau>) #\<^sub>\<Delta> \<Delta>)"

| wfPhi_emptyI: " \<turnstile>\<^sub>w\<^sub>f \<Theta> \<Longrightarrow> \<Theta> \<turnstile>\<^sub>w\<^sub>f []"

| wfPhi_consI: "\<lbrakk> 
  f \<notin> name_of_fun ` set \<Phi>; 
  \<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f ft;
  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>
\<rbrakk> \<Longrightarrow>  
  \<Theta>  \<turnstile>\<^sub>w\<^sub>f ((AF_fundef f ft)#\<Phi>)"  

| wfFTNone: " \<Theta> ; \<Phi> ; {||} \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>  \<Theta> ; \<Phi> \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_none ft"
| wfFTSome: " \<Theta> ; \<Phi> ; {| bv |} \<turnstile>\<^sub>w\<^sub>f ft \<Longrightarrow>  \<Theta> ; \<Phi> \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_some bv ft"

| wfFTI: "\<lbrakk>
  \<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f b; 
  supp s \<subseteq> {atom x} \<union> supp B ;
  supp c \<subseteq> { atom x } ;
  \<Theta> ; B ; (x,b,c) #\<^sub>\<Gamma> GNil \<turnstile>\<^sub>w\<^sub>f \<tau>;
  \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi>        
\<rbrakk> \<Longrightarrow> 
  \<Theta> ; \<Phi> ; B \<turnstile>\<^sub>w\<^sub>f (AF_fun_typ x b c \<tau> s)"

inductive_cases wfE_elims:
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_val v : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_op Plus v1 v2 : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_op LEq v1 v2 : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_fst v1 : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_snd v1 : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_concat v1 v2 : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_len v1 : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_op opp v1 v2 : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_app f v: b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_appP f b' v: b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_mvar u : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>\<^sub>w\<^sub>f AE_op Eq v1 v2 : b"

inductive_cases wfCS_elims:
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dc ; t \<turnstile>\<^sub>w\<^sub>f (cs::branch_s) : b"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; dc  \<turnstile>\<^sub>w\<^sub>f (cs::branch_list) : b"

inductive_cases wfPhi_elims:
  " \<Theta>  \<turnstile>\<^sub>w\<^sub>f []"
  " \<Theta>  \<turnstile>\<^sub>w\<^sub>f ((AF_fundef f ft)#\<Pi>)"  
  " \<Theta>  \<turnstile>\<^sub>w\<^sub>f (fd#\<Phi>::\<Phi>)"  

declare[[ simproc del: alpha_lst]]

inductive_cases wfFTQ_elims:
  "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_none ft"
  "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_some bv ft"
  "\<Theta> ; \<Phi>  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s)"

inductive_cases wfFT_elims:
  "\<Theta> ; \<Phi> ; \<B>  \<turnstile>\<^sub>w\<^sub>f AF_fun_typ x b c \<tau> s"

declare[[ simproc add: alpha_lst]]

inductive_cases wfD_elims:
  "\<Pi> ; \<B> ; (\<Gamma>::\<Gamma>) \<turnstile>\<^sub>w\<^sub>f []\<^sub>\<Delta>"
  "\<Pi> ; \<B> ; (\<Gamma>::\<Gamma>) \<turnstile>\<^sub>w\<^sub>f (u,\<tau>) #\<^sub>\<Delta> \<Delta>::\<Delta>"

equivariance wfE 

nominal_inductive wfE 
  avoids   wfE_appPI: bv |  wfS_varI: u |  wfS_letI: x | wfS_let2I: x  | wfS_branchI: x | wfS_assertI: x

proof(goal_cases)
  case (1 \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f x b c s)
  moreover hence "atom bv \<sharp>  AE_appP f b' v" using pure_fresh fresh_prodN e.fresh  by auto
  ultimately show ?case using fresh_star_def by fastforce
next
  case (2 \<Theta> \<Phi> \<B> \<Gamma> \<Delta> b' bv v \<tau> f x b c s)
  then show ?case by auto
next
  case (3 \<Phi> \<Theta> \<B> \<Gamma> \<Delta> e b' x s b)
  moreover hence "atom x \<sharp> LET x = e IN s" using  fresh_prodN by auto
  ultimately show ?case using fresh_prodN fresh_star_def by fastforce 
next
  case (4 \<Phi> \<Theta> \<B> \<Gamma> \<Delta> e b' x s b)
  then show ?case by auto
next
  case (5 \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  hence "atom x \<sharp> ASSERT c IN s" using  s_branch_s_branch_list.fresh by auto
  then show ?case using fresh_prodN fresh_star_def 5 by fastforce 
next
  case (6 \<Theta> \<Phi> \<B> x c \<Gamma> \<Delta> s b)
  then show ?case by auto
next
  case (7 \<Phi> \<Theta> \<B> \<Gamma> \<Delta> s1 \<tau> x s2 b)
  hence "atom x \<sharp> \<tau> \<and> atom x \<sharp> s1" using fresh_prodN by metis
  moreover hence "atom x \<sharp> LET x : \<tau> = s1 IN s2" 
    using  s_branch_s_branch_list.fresh(3)[of "atom x" x "\<tau>" s1 s2 ] fresh_prodN by simp
  ultimately show ?case using fresh_prodN fresh_star_def 7 by fastforce 
next
  case (8 \<Phi> \<Theta> \<B> \<Gamma> \<Delta> s1 \<tau> x s2 b)
  then show ?case by auto
next
  case (9 \<Theta> \<B> \<Gamma> \<tau> v u \<Phi> \<Delta> b s)
  moreover hence " atom u \<sharp> AS_var u \<tau> v s" using fresh_prodN s_branch_s_branch_list.fresh by simp
  ultimately show ?case using fresh_star_def fresh_prodN s_branch_s_branch_list.fresh by fastforce
next
  case (10 \<Theta> \<B> \<Gamma> \<tau> v u \<Phi> \<Delta> b s)
  then show ?case by auto
next
  case (11 \<Phi> \<Theta> \<B> x \<tau> \<Gamma> \<Delta> s b tid dc)
  moreover have "atom x \<sharp> (dc x \<Rightarrow> s)" using pure_fresh  s_branch_s_branch_list.fresh by auto
  ultimately show ?case using fresh_prodN fresh_star_def pure_fresh by fastforce 
next
  case (12 \<Phi> \<Theta> \<B> x \<tau> \<Gamma> \<Delta> s b tid dc)
  then show ?case by auto
qed

inductive  wfVDs :: "var_def list \<Rightarrow> bool" where

wfVDs_nilI: "wfVDs []"

| wfVDs_consI: "\<lbrakk>
   atom u \<sharp> ts;
   wfV ([]::\<Theta>) {||}  GNil  v  (b_of \<tau>);
   wfT ([]::\<Theta>)  {||}  GNil  \<tau>;
   wfVDs ts
\<rbrakk> \<Longrightarrow> wfVDs  ((AV_def u \<tau> v)#ts)"

equivariance wfVDs 
nominal_inductive wfVDs .  

end