(*<*)
theory Typing
  imports  RCLogic WellformedL
begin
  (*>*)

chapter \<open>Type System\<close>

text \<open>The MiniSail type system. We define subtyping judgement first and then typing judgement
for the term forms\<close>

section \<open>Subtyping\<close>

text \<open> Subtyping is defined on top of refinement constraint logic (RCL). 
A subtyping check is converted into an RCL validity check. \<close>

inductive subtype :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<tau> \<Rightarrow> \<tau> \<Rightarrow> bool"  ("_ ; _ ; _  \<turnstile> _ \<lesssim> _" [50, 50, 50] 50) where
  subtype_baseI: "\<lbrakk>  
   atom x \<sharp> (\<Theta>, \<B>, \<Gamma>, z,c,z',c') ; 
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<lbrace> z : b | c \<rbrace>;  
   \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f  \<lbrace> z' : b | c' \<rbrace>;                    
   \<Theta>; \<B> ; (x,b, c[z::=[x]\<^sup>v]\<^sub>v) #\<^sub>\<Gamma> \<Gamma> \<Turnstile> c'[z'::=[x]\<^sup>v]\<^sub>v  
\<rbrakk> \<Longrightarrow>  
   \<Theta>; \<B>; \<Gamma> \<turnstile>  \<lbrace> z : b | c \<rbrace> \<lesssim>  \<lbrace> z' : b | c' \<rbrace>"

equivariance subtype
nominal_inductive subtype 
  avoids subtype_baseI: x
proof(goal_cases)
  case (1 \<Theta> \<B> \<Gamma> z b c z' c' x)
  then show ?case using  fresh_star_def 1 by force
next
  case (2 \<Theta> \<B> \<Gamma> z b c z' c' x)
  then show ?case by auto
qed

inductive_cases subtype_elims: 
  "\<Theta>; \<B>; \<Gamma> \<turnstile> \<lbrace> z : b | c \<rbrace> \<lesssim>  \<lbrace> z' : b | c' \<rbrace>"
  "\<Theta>; \<B>; \<Gamma> \<turnstile> \<tau>\<^sub>1 \<lesssim>  \<tau>\<^sub>2"

section \<open>Literals\<close>

text \<open>The type synthesised has the constraint that z equates to the literal\<close>

inductive infer_l  :: "l \<Rightarrow> \<tau> \<Rightarrow> bool" (" \<turnstile> _ \<Rightarrow> _" [50, 50] 50) where
  infer_trueI:   " \<turnstile> L_true  \<Rightarrow> \<lbrace> z : B_bool | [[z]\<^sup>v]\<^sup>c\<^sup>e ==  [[L_true]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>"
| infer_falseI: " \<turnstile> L_false \<Rightarrow> \<lbrace> z : B_bool | [[z]\<^sup>v]\<^sup>c\<^sup>e == [[L_false]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>"
| infer_natI:   " \<turnstile> L_num n \<Rightarrow> \<lbrace> z : B_int  | [[z]\<^sup>v]\<^sup>c\<^sup>e == [[L_num n]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>"
| infer_unitI:  " \<turnstile> L_unit  \<Rightarrow> \<lbrace> z : B_unit | [[z]\<^sup>v]\<^sup>c\<^sup>e == [[L_unit]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>"
| infer_bitvecI:  " \<turnstile> L_bitvec bv \<Rightarrow> \<lbrace> z : B_bitvec | [[z]\<^sup>v]\<^sup>c\<^sup>e ==  [[L_bitvec bv]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>"

nominal_inductive infer_l  .
equivariance infer_l 

inductive_cases infer_l_elims[elim!]:
  "\<turnstile> L_true \<Rightarrow> \<tau>"
  "\<turnstile> L_false \<Rightarrow> \<tau>"
  "\<turnstile> L_num n \<Rightarrow> \<tau>"
  "\<turnstile> L_unit \<Rightarrow> \<tau>"
  "\<turnstile> L_bitvec x \<Rightarrow> \<tau>"
  "\<turnstile> l \<Rightarrow> \<tau>"

lemma infer_l_form2[simp]:
  shows "\<exists>z. \<turnstile> l \<Rightarrow> (\<lbrace> z : base_for_lit l | [[z]\<^sup>v]\<^sup>c\<^sup>e == [[l]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>)"
proof (nominal_induct l rule: l.strong_induct)
  case (L_num x)
  then show ?case using infer_l.intros base_for_lit.simps has_fresh_z by metis
next
  case L_true
  then show ?case using infer_l.intros base_for_lit.simps has_fresh_z by metis
next
  case L_false
  then show ?case using infer_l.intros base_for_lit.simps has_fresh_z by metis
next
  case L_unit
  then show ?case using infer_l.intros base_for_lit.simps has_fresh_z by metis
next
  case (L_bitvec x)
  then show ?case using infer_l.intros base_for_lit.simps has_fresh_z by metis
qed

section \<open>Values\<close>

inductive infer_v :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> v \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ; _ ; _ \<turnstile> _ \<Rightarrow> _" [50, 50, 50] 50) where

infer_v_varI: "\<lbrakk>
      \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; 
      Some (b,c) = lookup \<Gamma> x; 
      atom z \<sharp> x ; atom z \<sharp>  (\<Theta>, \<B>, \<Gamma>) 
\<rbrakk> \<Longrightarrow> 
      \<Theta>; \<B>; \<Gamma> \<turnstile> [x]\<^sup>v \<Rightarrow> \<lbrace> z : b | [[z]\<^sup>v]\<^sup>c\<^sup>e == [[x]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>"

| infer_v_litI: "\<lbrakk>
      \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; 
      \<turnstile> l \<Rightarrow> \<tau> 
\<rbrakk> \<Longrightarrow> 
      \<Theta>; \<B>; \<Gamma> \<turnstile> [l]\<^sup>v \<Rightarrow> \<tau>"

| infer_v_pairI: "\<lbrakk> 
      atom z \<sharp> (v1, v2); atom z \<sharp>  (\<Theta>, \<B>, \<Gamma>) ;
      \<Theta>; \<B>; \<Gamma> \<turnstile> (v1::v) \<Rightarrow> t1 ; 
      \<Theta>; \<B> ;  \<Gamma> \<turnstile> (v2::v) \<Rightarrow> t2
\<rbrakk> \<Longrightarrow> 
      \<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v1 v2 \<Rightarrow> (\<lbrace> z : B_pair (b_of t1) (b_of t2)  | [[z]\<^sup>v]\<^sup>c\<^sup>e == [[v1,v2]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>) "

| infer_v_consI: "\<lbrakk> 
      AF_typedef s dclist \<in> set \<Theta>;
      (dc, tc) \<in> set dclist ; 
      \<Theta>;  \<B>; \<Gamma> \<turnstile> v \<Rightarrow> tv ; 
      \<Theta>; \<B>; \<Gamma> \<turnstile> tv \<lesssim> tc ;
      atom z \<sharp> v ;  atom z \<sharp> (\<Theta>, \<B>, \<Gamma>) 
\<rbrakk> \<Longrightarrow> 
      \<Theta>;  \<B>; \<Gamma>  \<turnstile> V_cons s dc v \<Rightarrow> (\<lbrace> z : B_id s |  [[z]\<^sup>v]\<^sup>c\<^sup>e == [ V_cons s dc v ]\<^sup>c\<^sup>e \<rbrace>)"

| infer_v_conspI: "\<lbrakk> 
      AF_typedef_poly s bv dclist \<in> set \<Theta>;
      (dc, tc) \<in> set dclist ; 
      \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> tv; 
      \<Theta>; \<B>; \<Gamma> \<turnstile> tv \<lesssim> tc[bv::=b]\<^sub>\<tau>\<^sub>b ;
      atom z \<sharp> (\<Theta>, \<B>, \<Gamma>, v, b);
      atom bv \<sharp> (\<Theta>, \<B>, \<Gamma>, v, b);
      \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b
\<rbrakk> \<Longrightarrow> 
      \<Theta>; \<B>; \<Gamma> \<turnstile> V_consp s dc b v \<Rightarrow> (\<lbrace> z : B_app s b |  [[z]\<^sup>v]\<^sup>c\<^sup>e == (CE_val (V_consp s dc b v)) \<rbrace>)"

equivariance infer_v
nominal_inductive infer_v
  avoids infer_v_conspI: bv and z | infer_v_varI: z | infer_v_pairI: z | infer_v_consI:  z 
proof(goal_cases)
  case (1 \<Theta> \<B> \<Gamma> b c x z)
  hence "atom z \<sharp> \<lbrace> z : b  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" using \<tau>.fresh by simp
  then show ?case unfolding fresh_star_def using 1 by simp
next
  case (2 \<Theta> \<B> \<Gamma> b c x z)
  then show ?case by auto
next
  case (3 z v1 v2 \<Theta> \<B> \<Gamma> t1 t2)
  hence "atom z \<sharp> \<lbrace> z : [ b_of t1 , b_of t2 ]\<^sup>b  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ v1 , v2 ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrace>" using \<tau>.fresh by simp
  then show ?case unfolding fresh_star_def using 3 by simp
next
  case (4 z v1 v2 \<Theta> \<B> \<Gamma> t1 t2)
  then show ?case by auto
next
  case (5 s dclist \<Theta> dc tc \<B> \<Gamma> v tv z)
  hence "atom z \<sharp> \<lbrace> z : B_id s  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ V_cons s dc v ]\<^sup>c\<^sup>e  \<rbrace>" using \<tau>.fresh b.fresh pure_fresh by auto
  moreover have "atom z \<sharp> V_cons s dc v" using v.fresh 5 using v.fresh fresh_prodN pure_fresh  by metis
  then show ?case unfolding fresh_star_def using 5 by simp
next
  case (6 s dclist \<Theta> dc tc \<B> \<Gamma> v tv z)
  then show ?case by auto
next
  case (7 s bv dclist \<Theta> dc tc \<B> \<Gamma> v tv b z)
  hence "atom bv \<sharp> V_consp s dc b v" using v.fresh fresh_prodN pure_fresh by metis
  moreover then have "atom bv \<sharp> \<lbrace> z : B_id s  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ V_consp s dc b v ]\<^sup>c\<^sup>e  \<rbrace>" 
    using \<tau>.fresh ce.fresh v.fresh by auto
  moreover have "atom z \<sharp> V_consp s dc b v" using v.fresh fresh_prodN pure_fresh 7 by metis
  moreover then have "atom z \<sharp> \<lbrace> z : B_id s  | [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ V_consp s dc b v ]\<^sup>c\<^sup>e  \<rbrace>" 
    using \<tau>.fresh ce.fresh v.fresh by auto
  ultimately show ?case using fresh_star_def 7 by force
next
  case (8 s bv dclist \<Theta> dc tc \<B> \<Gamma> v tv b z)
  then show ?case by auto
qed

inductive_cases infer_v_elims[elim!]:
  "\<Theta>; \<B>; \<Gamma> \<turnstile> V_var x \<Rightarrow> \<tau>"
  "\<Theta>; \<B>; \<Gamma> \<turnstile> V_lit l \<Rightarrow> \<tau>"
  "\<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v1 v2 \<Rightarrow> \<tau>"
  "\<Theta>; \<B>; \<Gamma> \<turnstile> V_cons s dc v \<Rightarrow> \<tau>"
  "\<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v1 v2 \<Rightarrow> (\<lbrace> z : b |  c  \<rbrace>) "
  "\<Theta>; \<B>; \<Gamma> \<turnstile> V_pair v1 v2 \<Rightarrow> (\<lbrace> z : [ b1 , b2 ]\<^sup>b |  [[z]\<^sup>v]\<^sup>c\<^sup>e == [[v1,v2]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>) "
  "\<Theta>; \<B>; \<Gamma> \<turnstile> V_consp s dc b v  \<Rightarrow> \<tau> "

inductive check_v :: "\<Theta> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> v \<Rightarrow> \<tau> \<Rightarrow> bool"  ("_ ; _ ; _  \<turnstile> _ \<Leftarrow> _" [50, 50, 50] 50) where
  check_v_subtypeI:  "\<lbrakk>  \<Theta>; \<B>; \<Gamma> \<turnstile> \<tau>1 \<lesssim> \<tau>2; \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>1 \<rbrakk> \<Longrightarrow> \<Theta>; \<B> ;  \<Gamma> \<turnstile>  v \<Leftarrow> \<tau>2"
equivariance check_v
nominal_inductive check_v  .

inductive_cases check_v_elims[elim!]:
  "\<Theta>; \<B> ; \<Gamma> \<turnstile> v \<Leftarrow> \<tau>"

section \<open>Expressions\<close>

text \<open> Type synthesis for expressions \<close>

inductive infer_e :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> e \<Rightarrow> \<tau> \<Rightarrow> bool"  ("_ ; _ ; _ ; _ ; _  \<turnstile> _ \<Rightarrow> _" [50, 50, 50,50] 50) where

infer_e_valI:  "\<lbrakk>
         (\<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>) ; 
         (\<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>)) ; 
         (\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>) \<rbrakk> \<Longrightarrow> 
         \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_val v) \<Rightarrow> \<tau>"

| infer_e_plusI: "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : B_int | c1 \<rbrace> ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile>  v2 \<Rightarrow> \<lbrace> z2 : B_int | c2 \<rbrace>;
        atom z3 \<sharp> (AE_op Plus v1 v2); atom z3 \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_op Plus v1 v2 \<Rightarrow> \<lbrace> z3 : B_int | [[z3]\<^sup>v]\<^sup>c\<^sup>e == (CE_op Plus [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace>"

| infer_e_leqI: "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : B_int | c1 \<rbrace> ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v2 \<Rightarrow> \<lbrace> z2 : B_int | c2 \<rbrace>;
        atom z3 \<sharp> (AE_op LEq v1 v2); atom z3 \<sharp> \<Gamma>  
\<rbrakk> \<Longrightarrow> 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_op LEq v1 v2 \<Rightarrow>  \<lbrace> z3 : B_bool | [[z3]\<^sup>v]\<^sup>c\<^sup>e == (CE_op LEq [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace>"

| infer_e_eqI: "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>; 
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : b | c1 \<rbrace> ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v2 \<Rightarrow> \<lbrace> z2 : b | c2 \<rbrace>;     
        atom z3 \<sharp> (AE_op Eq v1 v2); atom z3 \<sharp> \<Gamma>  ;
        b \<in> { B_bool, B_int, B_unit }
\<rbrakk> \<Longrightarrow> 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_op Eq v1 v2 \<Rightarrow>  \<lbrace> z3 : B_bool | [[z3]\<^sup>v]\<^sup>c\<^sup>e == (CE_op Eq [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace>"

| infer_e_appI: "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        Some (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau>' s'))) = lookup_fun \<Phi> f;        
        \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace>  x : b | c \<rbrace>; 
        atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>,v , \<tau>);
        \<tau>'[x::=v]\<^sub>v = \<tau> 
\<rbrakk> \<Longrightarrow>
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_app f v \<Rightarrow> \<tau>"

| infer_e_appPI: "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f b' ; 
        Some (AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau>' s'))) = lookup_fun \<Phi> f;       
        \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace>  x : b[bv::=b']\<^sub>b | c[bv::=b']\<^sub>b \<rbrace>; atom x \<sharp> \<Gamma>;
        (\<tau>'[bv::=b']\<^sub>b[x::=v]\<^sub>v) = \<tau> ;
        atom bv \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, b', v, \<tau>)
\<rbrakk> \<Longrightarrow>
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_appP f b' v \<Rightarrow> \<tau>"

| infer_e_fstI:  "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> z' : [b1,b2]\<^sup>b | c \<rbrace>;
        atom z \<sharp> AE_fst v ; atom z \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_fst v \<Rightarrow> \<lbrace> z : b1 | [[z]\<^sup>v]\<^sup>c\<^sup>e == ((CE_fst [v]\<^sup>c\<^sup>e)) \<rbrace>"

| infer_e_sndI: "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> z' : [ b1, b2]\<^sup>b | c \<rbrace>;
        atom z \<sharp> AE_snd v ; atom z \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow>  
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_snd v \<Rightarrow> \<lbrace> z : b2 | [[z]\<^sup>v]\<^sup>c\<^sup>e == ((CE_snd [v]\<^sup>c\<^sup>e))  \<rbrace>"

| infer_e_lenI: "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<lbrace> z' : B_bitvec | c \<rbrace>;
        atom z \<sharp> AE_len v ; atom z \<sharp> \<Gamma>\<rbrakk> \<Longrightarrow>  
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_len v \<Rightarrow> \<lbrace> z : B_int | [[z]\<^sup>v]\<^sup>c\<^sup>e == ((CE_len [v]\<^sup>c\<^sup>e))  \<rbrace>"

| infer_e_mvarI: "\<lbrakk>  
        \<Theta>; \<B> \<turnstile>\<^sub>w\<^sub>f \<Gamma> ; 
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta>;
        (u,\<tau>) \<in> setD \<Delta> \<rbrakk> \<Longrightarrow> 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>  AE_mvar u \<Rightarrow> \<tau>"

| infer_e_concatI: "\<lbrakk> 
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>) ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : B_bitvec | c1 \<rbrace> ; 
        \<Theta>; \<B>; \<Gamma> \<turnstile>  v2 \<Rightarrow> \<lbrace> z2 : B_bitvec | c2 \<rbrace>;
        atom z3 \<sharp> (AE_concat v1 v2); atom z3 \<sharp> \<Gamma> \<rbrakk> \<Longrightarrow> 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_concat  v1 v2 \<Rightarrow> \<lbrace> z3 : B_bitvec | [[z3]\<^sup>v]\<^sup>c\<^sup>e == (CE_concat [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace>"

| infer_e_splitI: "\<lbrakk>
        \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;
        \<Theta> \<turnstile>\<^sub>w\<^sub>f (\<Phi>::\<Phi>);
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v1 \<Rightarrow> \<lbrace> z1 : B_bitvec | c1 \<rbrace> ;
        \<Theta> ; \<B> ; \<Gamma> \<turnstile> v2 \<Leftarrow> \<lbrace> z2 : B_int | (CE_op LEq (CE_val (V_lit (L_num 0))) (CE_val (V_var z2))) == (CE_val (V_lit L_true)) AND 
                                         (CE_op LEq (CE_val (V_var z2)) (CE_len (CE_val (v1)))) == (CE_val (V_lit L_true)) \<rbrace>;
        atom z1 \<sharp> (AE_split v1 v2); atom z1 \<sharp> \<Gamma>;
        atom z2 \<sharp> (AE_split v1 v2); atom z2 \<sharp> \<Gamma>;
        atom z3 \<sharp> (AE_split v1 v2); atom z3 \<sharp> \<Gamma>
\<rbrakk> \<Longrightarrow> 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_split  v1 v2) \<Rightarrow> \<lbrace> z3 : B_pair B_bitvec B_bitvec  | 
                      ((CE_val v1) == (CE_concat (CE_fst (CE_val (V_var z3))) (CE_snd (CE_val (V_var z3)))))
                  AND (((CE_len (CE_fst (CE_val (V_var z3))))) == (CE_val ( v2))) \<rbrace>"

equivariance infer_e
nominal_inductive infer_e 
  avoids  infer_e_appI: x |infer_e_appPI: bv |  infer_e_splitI: z3 and z1 and z2 
proof(goal_cases)
  case (1 \<Theta> \<B> \<Gamma> \<Delta> \<Phi> f x b c \<tau>' s' v \<tau>)
  moreover hence "atom x \<sharp> [ f  v  ]\<^sup>e" using fresh_prodN pure_fresh e.fresh by force
  ultimately show ?case unfolding fresh_star_def using fresh_prodN e.fresh pure_fresh by simp
next
  case (2 \<Theta> \<B> \<Gamma> \<Delta> \<Phi> f x b c \<tau>' s' v \<tau>)
  then show ?case by auto
next
  case (3 \<Theta> \<B> \<Gamma> \<Delta> \<Phi> b' f bv x b c \<tau>' s' v \<tau>)
  moreover hence "atom bv \<sharp> AE_appP f b' v"  using fresh_prodN pure_fresh e.fresh by force
  ultimately show ?case unfolding fresh_star_def using fresh_prodN  e.fresh pure_fresh fresh_Pair by auto
next
  case (4 \<Theta> \<B> \<Gamma> \<Delta> \<Phi> b' f bv x b c \<tau>' s' v \<tau>)
  then show ?case by auto
next
  case (5 \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 z3)
  have "atom z3 \<sharp> \<lbrace> z3 : [ B_bitvec , B_bitvec ]\<^sup>b  | [ v1 ]\<^sup>c\<^sup>e  ==  [ [#1[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e @@ [#2[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e   AND  [| [#1[ [ z3 ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e  ==  [ v2 ]\<^sup>c\<^sup>e   \<rbrace>"
    using \<tau>.fresh by simp
  then show ?case unfolding fresh_star_def fresh_prod7 using wfG_fresh_x2 5 by auto
next
  case (6 \<Theta> \<B> \<Gamma> \<Delta> \<Phi> v1 z1 c1 v2 z2 z3)
  then show ?case by auto
qed

inductive_cases infer_e_elims[elim!]:
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op Plus v1 v2) \<Rightarrow> \<lbrace> z3 : B_int | [[z3]\<^sup>v]\<^sup>c\<^sup>e == (CE_op Plus [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op LEq v1 v2) \<Rightarrow> \<lbrace> z3 : B_bool | [[z3]\<^sup>v]\<^sup>c\<^sup>e == (CE_op LEq [v1]\<^sup>c\<^sup>e [v2]\<^sup>c\<^sup>e) \<rbrace>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op Plus v1 v2) \<Rightarrow> \<lbrace> z3 : B_int | c \<rbrace>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op Plus v1 v2) \<Rightarrow> \<lbrace> z3 : b | c \<rbrace>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op LEq v1 v2) \<Rightarrow> \<lbrace> z3 : b | c \<rbrace>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_app f v ) \<Rightarrow> \<tau>"     
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_val v) \<Rightarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_fst v) \<Rightarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_snd v) \<Rightarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_mvar u) \<Rightarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op Plus v1 v2) \<Rightarrow> \<tau>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op LEq v1 v2) \<Rightarrow> \<tau>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op LEq v1 v2) \<Rightarrow> \<lbrace> z3 : B_bool | c \<rbrace>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_app f v )  \<Rightarrow> \<tau>[x::=v]\<^sub>\<tau>\<^sub>v"  
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op opp v1 v2) \<Rightarrow>  \<tau>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_len v) \<Rightarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_len v) \<Rightarrow> \<lbrace> z : B_int | [[z]\<^sup>v]\<^sup>c\<^sup>e == ((CE_len [v]\<^sup>c\<^sup>e))\<rbrace> "
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_concat v1 v2 \<Rightarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_concat v1 v2 \<Rightarrow> (\<lbrace> z : b |  c  \<rbrace>) "
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_concat v1 v2 \<Rightarrow> (\<lbrace> z : B_bitvec |  [[z]\<^sup>v]\<^sup>c\<^sup>e == (CE_concat [v1]\<^sup>c\<^sup>e [v1]\<^sup>c\<^sup>e) \<rbrace>) "
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_appP f b v )  \<Rightarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AE_split v1 v2 \<Rightarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op Eq v1 v2) \<Rightarrow> \<lbrace> z3 : b | c \<rbrace>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op Eq v1 v2) \<Rightarrow> \<lbrace> z3 : B_bool | c \<rbrace>" 
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AE_op Eq v1 v2) \<Rightarrow> \<tau>" 
nominal_termination (eqvt)  by lexicographic_order

section \<open>Statements\<close>

inductive check_s ::  "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta> \<Rightarrow> s \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ; _ ; _ ; _ ; _  \<turnstile> _ \<Leftarrow> _" [50, 50, 50,50,50] 50) and
  check_branch_s ::  "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta>  \<Rightarrow> tyid \<Rightarrow> string \<Rightarrow> \<tau> \<Rightarrow> v \<Rightarrow> branch_s \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ;  _ ; _ ; _ ; _ ; _ ; _ ; _ ; _ \<turnstile> _ \<Leftarrow> _" [50, 50, 50,50,50] 50) and
  check_branch_list ::  "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> \<B> \<Rightarrow> \<Gamma> \<Rightarrow> \<Delta>  \<Rightarrow> tyid \<Rightarrow> (string * \<tau>) list \<Rightarrow> v \<Rightarrow> branch_list \<Rightarrow> \<tau> \<Rightarrow> bool" (" _ ;  _ ; _ ; _ ; _ ; _ ; _ ; _ \<turnstile> _ \<Leftarrow> _" [50, 50, 50,50,50] 50) where 
  check_valI:  "\<lbrakk> 
       \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ;   
       \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
       \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Rightarrow> \<tau>'; 
       \<Theta>; \<B>; \<Gamma> \<turnstile> \<tau>' \<lesssim> \<tau> \<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AS_val v) \<Leftarrow> \<tau>"

| check_letI: "\<lbrakk>
       atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, e, \<tau>);  
       atom z \<sharp> (x, \<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, e, \<tau>, s);  
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> e \<Rightarrow> \<lbrace> z : b | c \<rbrace> ; 
       \<Theta>; \<Phi> ; \<B> ; ((x,b,c[z::=V_var x]\<^sub>v)#\<^sub>\<Gamma>\<Gamma>) ; \<Delta> \<turnstile> s \<Leftarrow> \<tau> 
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AS_let x e s) \<Leftarrow> \<tau>"

| check_assertI: "\<lbrakk>
       atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, c, \<tau>, s);  
       \<Theta>; \<Phi> ; \<B> ; ((x,B_bool,c)#\<^sub>\<Gamma>\<Gamma>) ; \<Delta> \<turnstile> s \<Leftarrow> \<tau> ;
       \<Theta>; \<B>; \<Gamma>  \<Turnstile> c;
       \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> 
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (AS_assert c s) \<Leftarrow> \<tau>"

|check_branch_s_branchI: "\<lbrakk> 
       \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
        \<turnstile>\<^sub>w\<^sub>f \<Theta> ; 
       \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<tau> ;
       \<Theta> ; {||} ; GNil \<turnstile>\<^sub>w\<^sub>f const;
       atom x \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, tid, cons , const, v, \<tau>);
       \<Theta>; \<Phi>; \<B>; ((x,b_of const,  ([v]\<^sup>c\<^sup>e == [ V_cons tid cons [x]\<^sup>v]\<^sup>c\<^sup>e ) AND (c_of const x))#\<^sub>\<Gamma>\<Gamma>) ; \<Delta> \<turnstile> s \<Leftarrow> \<tau>  
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; cons ; const ; v \<turnstile> (AS_branch cons x s) \<Leftarrow> \<tau>"

|check_branch_list_consI: "\<lbrakk> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>; tid; cons; const; v \<turnstile> cs \<Leftarrow> \<tau> ; 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>; tid; dclist; v \<turnstile> css \<Leftarrow> \<tau>  
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; (cons,const)#dclist ; v \<turnstile> AS_cons cs css \<Leftarrow> \<tau>"

|check_branch_list_finalI: "\<lbrakk> 
       \<Theta>; \<Phi>;\<B>; \<Gamma>; \<Delta>; tid ; cons ; const ; v \<turnstile> cs \<Leftarrow> \<tau>  
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> ; tid ; [(cons,const)] ; v \<turnstile> AS_final cs  \<Leftarrow> \<tau>"

| check_ifI: "\<lbrakk> 
       atom z \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, v , s1 , s2 , \<tau> ); 
       (\<Theta>; \<B>; \<Gamma> \<turnstile> v \<Leftarrow> (\<lbrace> z : B_bool | TRUE \<rbrace>)) ; 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> s1 \<Leftarrow> (\<lbrace> z : b_of \<tau> | ([v]\<^sup>c\<^sup>e == [[L_true]\<^sup>v]\<^sup>c\<^sup>e) IMP (c_of \<tau> z) \<rbrace>) ;
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> s2 \<Leftarrow> (\<lbrace> z : b_of \<tau> | ([v]\<^sup>c\<^sup>e == [[L_false]\<^sup>v]\<^sup>c\<^sup>e) IMP (c_of \<tau> z) \<rbrace>) 
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> IF v THEN s1 ELSE s2 \<Leftarrow> \<tau>"

| check_let2I: "\<lbrakk>    
       atom x \<sharp> (\<Theta>, \<Phi>, \<B>, G, \<Delta>, t, s1, \<tau>) ;     
       \<Theta>; \<Phi> ; \<B> ; G; \<Delta> \<turnstile> s1 \<Leftarrow> t; 
       \<Theta>; \<Phi> ; \<B> ; ((x,b_of t,c_of t x)#\<^sub>\<Gamma>G) ; \<Delta> \<turnstile> s2 \<Leftarrow> \<tau> 
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi> ; \<B> ; G ; \<Delta> \<turnstile> (LET x : t  = s1 IN s2) \<Leftarrow> \<tau>"

| check_varI: "\<lbrakk> 
       atom u \<sharp> (\<Theta>, \<Phi>, \<B>, \<Gamma>, \<Delta>, \<tau>', v, \<tau>) ; 
       \<Theta>; \<B>; \<Gamma> \<turnstile>  v \<Leftarrow> \<tau>'; 
       \<Theta>; \<Phi>; \<B>; \<Gamma> ; ((u,\<tau>') #\<^sub>\<Delta> \<Delta>)  \<turnstile> s \<Leftarrow> \<tau> 
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> (VAR u : \<tau>' = v  IN s) \<Leftarrow> \<tau>"

| check_assignI: "\<lbrakk> 
       \<Theta> \<turnstile>\<^sub>w\<^sub>f \<Phi> ;
       \<Theta>; \<B>; \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Delta> ; 
       (u,\<tau>) \<in> setD \<Delta> ; 
       \<Theta>; \<B>; \<Gamma> \<turnstile>  v \<Leftarrow> \<tau>;
       \<Theta>; \<B>; \<Gamma> \<turnstile> (\<lbrace> z : B_unit | TRUE \<rbrace>) \<lesssim> \<tau>'  
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile>  (u ::= v) \<Leftarrow> \<tau>'" 

| check_whileI: "\<lbrakk> 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> s1 \<Leftarrow> \<lbrace> z : B_bool | TRUE \<rbrace>; 
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> s2 \<Leftarrow> \<lbrace> z : B_unit | TRUE \<rbrace>;
        \<Theta>; \<B>; \<Gamma> \<turnstile> (\<lbrace> z : B_unit | TRUE \<rbrace>) \<lesssim> \<tau>' 
\<rbrakk> \<Longrightarrow>  
        \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> WHILE s1 DO { s2 } \<Leftarrow> \<tau>'"

| check_seqI: "\<lbrakk> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> s1 \<Leftarrow> \<lbrace> z : B_unit | TRUE \<rbrace>; 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> s2 \<Leftarrow> \<tau> 
\<rbrakk> \<Longrightarrow> 
       \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> s1 ;; s2 \<Leftarrow> \<tau>"

| check_caseI: "\<lbrakk> 
      \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>; tid ; dclist ; v \<turnstile>  cs \<Leftarrow> \<tau> ;  
       (AF_typedef tid dclist ) \<in> set \<Theta> ;                 
       \<Theta>; \<B>; \<Gamma> \<turnstile> v \<Leftarrow> \<lbrace> z : B_id tid | TRUE \<rbrace>;
       \<turnstile>\<^sub>w\<^sub>f \<Theta>  
\<rbrakk> \<Longrightarrow>
      \<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_match v cs \<Leftarrow> \<tau>"

equivariance check_s

text \<open>We only need avoidance for cases where a variable is added to a context\<close>
nominal_inductive check_s 
  avoids check_letI: x and z  |  check_branch_s_branchI: x | check_let2I: x  | check_varI: u | check_ifI: z | check_assertI: x
proof(goal_cases)
  case (1 x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> e \<tau> z s b c)
  hence "atom x \<sharp> AS_let x e s" using s_branch_s_branch_list.fresh(2) by auto 
  moreover have "atom z \<sharp> AS_let x e s" using s_branch_s_branch_list.fresh(2) 1 fresh_prod8 by auto
  then show ?case using fresh_star_def 1 by force
next
  case (3 x \<Theta> \<Phi> \<B> \<Gamma> \<Delta> c \<tau> s)
  hence "atom x \<sharp> AS_assert c s" using fresh_prodN s_branch_s_branch_list.fresh pure_fresh  by auto 
  then show ?case using fresh_star_def 3 by force
next
  case (5 \<Theta> \<B> \<Gamma> \<Delta> \<tau> const x \<Phi> tid cons v s)
  hence "atom x \<sharp> AS_branch cons x s" using fresh_prodN s_branch_s_branch_list.fresh pure_fresh  by auto 
  then show ?case using fresh_star_def 5 by force
next
  case (7 z \<Theta> \<Phi> \<B> \<Gamma> \<Delta> v s1 s2 \<tau>)
  hence "atom z \<sharp> AS_if v s1 s2 " using s_branch_s_branch_list.fresh by auto
  then show ?case using 7 fresh_prodN fresh_star_def by fastforce
next
  case (9 x \<Theta> \<Phi> \<B> G \<Delta> t s1 \<tau> s2)
  hence "atom x \<sharp> AS_let2 x t s1 s2" using s_branch_s_branch_list.fresh by auto
  thus ?case  using fresh_star_def 9 by force
next
  case (11 u \<Theta> \<Phi> \<B> \<Gamma> \<Delta> \<tau>' v \<tau> s)
  hence "atom u \<sharp> AS_var u \<tau>' v s" using s_branch_s_branch_list.fresh by auto
  then show ?case  using fresh_star_def 11 by force

qed(auto+)

inductive_cases check_s_elims[elim!]:
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_val v \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_let x e s \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_if v s1 s2 \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_let2 x t s1 s2 \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_while s1 s2 \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_var u t v s \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_seq s1 s2 \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_assign u v \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_match v cs \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta> \<turnstile> AS_assert c s \<Leftarrow> \<tau>"

inductive_cases check_branch_s_elims[elim!]:
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>; tid ; dclist ; v \<turnstile> (AS_final cs) \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>; tid ; dclist ; v \<turnstile> (AS_cons cs css) \<Leftarrow> \<tau>"
  "\<Theta>; \<Phi>; \<B>; \<Gamma>; \<Delta>; tid ; cons ; const ; v \<turnstile> (AS_branch dc x s ) \<Leftarrow> \<tau>"

section \<open>Programs\<close>

text \<open>Type check function bodies\<close>

inductive check_funtyp :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow>  \<B> \<Rightarrow> fun_typ \<Rightarrow> bool" ( " _ ; _ ; _ \<turnstile> _ " ) where
  check_funtypI: "\<lbrakk>
  atom x \<sharp> (\<Theta>, \<Phi>, B , b );
  \<Theta>; \<Phi> ;  B ; ((x,b,c) #\<^sub>\<Gamma> GNil) ; []\<^sub>\<Delta> \<turnstile> s \<Leftarrow> \<tau>
\<rbrakk>  \<Longrightarrow> 
  \<Theta>; \<Phi> ; B \<turnstile> (AF_fun_typ x b c \<tau> s)"

equivariance check_funtyp
nominal_inductive check_funtyp
  avoids check_funtypI: x
proof(goal_cases)
  case (1 x \<Theta> \<Phi> B b c s \<tau>  )
  hence "atom x \<sharp> (AF_fun_typ x b c \<tau> s)"  using fun_def.fresh fun_typ_q.fresh fun_typ.fresh by simp
  then show ?case using fresh_star_def 1 fresh_prodN by fastforce
next
  case (2 \<Theta> \<Phi> x b c s \<tau> f)
  then show ?case by auto
qed

inductive check_funtypq :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> fun_typ_q \<Rightarrow> bool"  ( " _ ; _ \<turnstile> _ " ) where 
  check_fundefq_simpleI: "\<lbrakk>
  \<Theta>; \<Phi> ; {||} \<turnstile> (AF_fun_typ x b c t s)
\<rbrakk>  \<Longrightarrow> 
  \<Theta>; \<Phi> \<turnstile> ((AF_fun_typ_none (AF_fun_typ x b c t s)))"

|check_funtypq_polyI: "\<lbrakk>
  atom bv \<sharp> (\<Theta>, \<Phi>, (AF_fun_typ x b c t s));
  \<Theta>; \<Phi>; {|bv|} \<turnstile> (AF_fun_typ x b c t s)
\<rbrakk>  \<Longrightarrow> 
  \<Theta>; \<Phi> \<turnstile> (AF_fun_typ_some bv (AF_fun_typ x b c t s))"

equivariance check_funtypq
nominal_inductive check_funtypq
  avoids check_funtypq_polyI: bv
proof(goal_cases)
  case (1 bv \<Theta> \<Phi> x b c t s )
  hence "atom bv \<sharp> (AF_fun_typ_some bv (AF_fun_typ x b c t s))"  using fun_def.fresh fun_typ_q.fresh fun_typ.fresh by simp
  thus ?case using fresh_star_def 1 fresh_prodN by fastforce
next
  case (2 bv \<Theta> \<Phi> ft )
  then show ?case by auto
qed

inductive check_fundef :: "\<Theta> \<Rightarrow> \<Phi> \<Rightarrow> fun_def \<Rightarrow> bool" ( " _ ; _ \<turnstile> _ " ) where
  check_fundefI: "\<lbrakk>
  \<Theta>; \<Phi> \<turnstile> ft 
\<rbrakk>  \<Longrightarrow> 
  \<Theta>; \<Phi> \<turnstile> (AF_fundef f ft)"

equivariance check_fundef
nominal_inductive check_fundef .

text \<open>Temporarily remove this simproc as it produces untidy eliminations\<close>
declare[[ simproc del: alpha_lst]]

inductive_cases check_funtyp_elims[elim!]:
  "check_funtyp \<Theta> \<Phi> B ft"

inductive_cases check_funtypq_elims[elim!]:
  "check_funtypq \<Theta> \<Phi> (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))"
  "check_funtypq \<Theta> \<Phi> (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s))"

inductive_cases check_fundef_elims[elim!]:
  "check_fundef \<Theta> \<Phi> (AF_fundef f ftq)"

declare[[ simproc add: alpha_lst]]

nominal_function \<Delta>_of :: "var_def list \<Rightarrow> \<Delta>" where
  "\<Delta>_of [] = DNil"
| "\<Delta>_of ((AV_def u t v)#vs) = (u,t) #\<^sub>\<Delta>  (\<Delta>_of vs)" 
  apply auto
  using  eqvt_def \<Delta>_of_graph_aux_def neq_Nil_conv old.prod.exhaust apply force
  using  eqvt_def \<Delta>_of_graph_aux_def neq_Nil_conv old.prod.exhaust 
  by (metis var_def.strong_exhaust)
nominal_termination (eqvt) by lexicographic_order

inductive check_prog :: "p \<Rightarrow> \<tau> \<Rightarrow> bool" ( "\<turnstile> _ \<Leftarrow> _")  where 
  "\<lbrakk>
   \<Theta>; \<Phi>; {||}; GNil ; \<Delta>_of \<G> \<turnstile> s \<Leftarrow> \<tau>
\<rbrakk> \<Longrightarrow>  \<turnstile> (AP_prog \<Theta> \<Phi> \<G> s) \<Leftarrow> \<tau>"

inductive_cases check_prog_elims[elim!]:
  "\<turnstile> (AP_prog \<Theta> \<Phi> \<G> s) \<Leftarrow> \<tau>"

end