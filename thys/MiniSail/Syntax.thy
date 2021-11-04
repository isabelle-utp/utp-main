(*<*)
theory Syntax
  imports "Nominal2.Nominal2" "Nominal-Utils"
begin
  (*>*)

chapter \<open>Syntax\<close>

text \<open>Syntax of MiniSail programs and the contexts we use in judgements.\<close>

section \<open>Program Syntax\<close>

subsection \<open>AST Datatypes\<close>

type_synonym num_nat = nat

atom_decl x  (* Immutable variables*)
atom_decl u  (* Mutable variables *)
atom_decl bv  (* Basic-type variables *)

type_synonym f = string  (* Function name *)
type_synonym dc = string (* Data constructor *)
type_synonym tyid = string

text \<open>Basic types. Types without refinement constraints\<close>
nominal_datatype "b" =  
  B_int | B_bool | B_id tyid 
| B_pair b b  ("[ _ , _ ]\<^sup>b")
| B_unit | B_bitvec | B_var bv
| B_app tyid b

nominal_datatype bit = BitOne | BitZero

text  \<open> Literals \<close>
nominal_datatype "l" = 
  L_num "int" | L_true | L_false | L_unit  | L_bitvec "bit list"

text  \<open> Values. We include a type identifier, tyid, in the literal for constructors 
to make typing and well-formedness checking easier \<close>

nominal_datatype "v" = 
  V_lit "l"        ( "[ _ ]\<^sup>v")
  | V_var "x"        ( "[ _ ]\<^sup>v")
  | V_pair "v" "v"   ( "[ _ , _ ]\<^sup>v")
  | V_cons tyid dc "v" 
  | V_consp tyid dc b "v" 

text \<open> Binary Operations \<close>
nominal_datatype "opp" = Plus ( "plus") | LEq ("leq") | Eq ("eq")

text \<open> Expressions \<close>
nominal_datatype "e" = 
  AE_val "v"           ( "[ _ ]\<^sup>e"       )
  | AE_app "f" "v"       ( "[ _ ( _ ) ]\<^sup>e" )
  | AE_appP  "f" "b" "v" ( "[_ [ _ ] ( _ )]\<^sup>e" )
  | AE_op "opp" "v" "v"  ( "[ _ _ _ ]\<^sup>e"  )
  | AE_concat v v        ( "[ _ @@ _ ]\<^sup>e" )
  | AE_fst "v"           ( "[#1_ ]\<^sup>e"    )
  | AE_snd "v"           ( "[#2_ ]\<^sup>e"     )
  | AE_mvar "u"          ( "[ _ ]\<^sup>e"      )
  | AE_len "v"           ( "[| _ |]\<^sup>e"    )
  | AE_split "v" "v"     ( "[ _ / _ ]\<^sup>e"  )

text \<open> Expressions for constraints\<close>
nominal_datatype "ce" = 
  CE_val "v"           ( "[ _ ]\<^sup>c\<^sup>e"      )
  | CE_op "opp" "ce" "ce"  ( "[ _ _ _ ]\<^sup>c\<^sup>e"  )
  | CE_concat ce ce        ( "[ _ @@ _ ]\<^sup>c\<^sup>e" )
  | CE_fst "ce"           ( "[#1_]\<^sup>c\<^sup>e"      )
  | CE_snd "ce"           ( "[#2_]\<^sup>c\<^sup>e"      )
  | CE_len "ce"           ( "[| _ |]\<^sup>c\<^sup>e"    )

text  \<open> Constraints \<close>
nominal_datatype "c" = 
  C_true          ( "TRUE" [] 50 )
  | C_false         ( "FALSE" [] 50 )
  | C_conj "c" "c"  ("_  AND  _ " [50, 50] 50) 
  | C_disj "c" "c"  ("_ OR _ " [50,50] 50)
  | C_not "c"       ( "\<not> _ " [] 50 )
  | C_imp "c" "c"   ("_  IMP  _ " [50, 50] 50) 
  | C_eq "ce" "ce"  ("_  ==  _ " [50, 50] 50) 

text  \<open> Refined types \<close>
nominal_datatype "\<tau>" = 
  T_refined_type  x::x b c::c   binds x in c   ("\<lbrace> _ : _  | _ \<rbrace>" [50, 50] 1000)

text \<open> Statements \<close>

nominal_datatype 
  s = 
  AS_val v                             ( "[_]\<^sup>s")                  
  | AS_let x::x  e s::s binds x in s     ( "(LET _ = _ IN _)")
  | AS_let2 x::x \<tau>  s s::s binds x in s  ( "(LET _ : _ = _ IN _)")
  | AS_if v s s                          ( "(IF _ THEN _ ELSE _)" [0, 61, 0] 61)
  | AS_var u::u \<tau> v s::s  binds u in s   ( "(VAR _ : _ = _ IN _)")
  | AS_assign u  v                       ( "(_ ::= _)")
  | AS_match v branch_list               ( "(MATCH _ WITH { _ })")
  | AS_while s s                         ( "(WHILE _ DO { _ } )" [0, 0] 61)     
  | AS_seq s s                           ( "( _ ;; _ )"  [1000, 61] 61)
  | AS_assert c s                        ( "(ASSERT _ IN _ )" )
    and branch_s = 
    AS_branch dc x::x s::s binds x in s  ( "( _ _ \<Rightarrow> _ )")   
    and branch_list = 
    AS_final  branch_s                   ( "{ _ }" )
  | AS_cons  branch_s branch_list        ( "( _ | _  )")

text \<open> Function and union type definitions \<close>

nominal_datatype "fun_typ"  =
  AF_fun_typ x::x "b" c::c \<tau>::\<tau> s::s binds x in c \<tau> s

nominal_datatype "fun_typ_q" = 
  AF_fun_typ_some bv::bv ft::fun_typ binds bv in ft
  | AF_fun_typ_none fun_typ

nominal_datatype "fun_def" =  AF_fundef f fun_typ_q 

nominal_datatype "type_def" = 
  AF_typedef string "(string * \<tau>) list"
  |  AF_typedef_poly string bv::bv dclist::"(string * \<tau>) list"  binds bv in dclist

lemma check_typedef_poly:
  "AF_typedef_poly ''option'' bv [ (''None'', \<lbrace> zz : B_unit | TRUE \<rbrace>), (''Some'', \<lbrace> zz : B_var bv | TRUE \<rbrace>) ] = 
    AF_typedef_poly ''option'' bv2 [ (''None'', \<lbrace> zz : B_unit | TRUE \<rbrace>), (''Some'', \<lbrace> zz : B_var bv2 | TRUE \<rbrace>) ]"
  by auto

nominal_datatype "var_def" =  AV_def u \<tau> v

text  \<open> Programs \<close> 
nominal_datatype "p" = 
  AP_prog "type_def list" "fun_def list" "var_def list" "s" ("PROG _ _ _ _")

declare l.supp [simp] v.supp [simp]  e.supp [simp] s_branch_s_branch_list.supp [simp]  \<tau>.supp [simp] c.supp [simp] b.supp[simp]

subsection \<open>Lemmas\<close>

text \<open>These lemmas deal primarily with freshness and alpha-equivalence\<close>

subsubsection \<open>Atoms\<close>

lemma x_not_in_u_atoms[simp]:
  fixes u::u and x::x and us::"u set"
  shows "atom x \<notin> atom`us"
  by (simp add: image_iff)

lemma x_fresh_u[simp]:
  fixes u::u and x::x
  shows "atom x \<sharp> u"
  by auto

lemma x_not_in_b_set[simp]:
  fixes  x::x and bs::"bv fset"
  shows "atom x \<notin> supp bs"
  by(induct bs,auto, simp add: supp_finsert supp_at_base)

lemma x_fresh_b[simp]:
  fixes  x::x and b::b
  shows "atom x \<sharp> b"
  apply (induct b rule: b.induct, auto simp: pure_supp)
  using pure_supp fresh_def by blast+

lemma x_fresh_bv[simp]:
  fixes  x::x and bv::bv
  shows "atom x \<sharp> bv"
  using fresh_def supp_at_base by auto

lemma u_not_in_x_atoms[simp]:
  fixes u::u and x::x and xs::"x set"
  shows "atom u \<notin> atom`xs"
  by (simp add: image_iff)

lemma bv_not_in_x_atoms[simp]:
  fixes bv::bv and x::x and xs::"x set"
  shows "atom bv \<notin> atom`xs"
  by (simp add: image_iff)

lemma u_not_in_b_atoms[simp]:
  fixes b :: b and u::u
  shows "atom u \<notin> supp b"
  by (induct b rule: b.induct,auto simp: pure_supp supp_at_base)

lemma u_not_in_b_set[simp]:
  fixes  u::u and bs::"bv fset"
  shows "atom u \<notin> supp bs"
  by(induct bs, auto simp add: supp_at_base supp_finsert)

lemma u_fresh_b[simp]:
  fixes  x::u and b::b
  shows "atom x \<sharp> b"
  by(induct b rule: b.induct, auto simp: pure_fresh )

lemma supp_b_v_disjoint:
  fixes x::x and bv::bv
  shows "supp (V_var x) \<inter> supp (B_var bv) = {}" 
  by (simp add: supp_at_base)

lemma supp_b_u_disjoint[simp]:
  fixes b::b and u::u
  shows "supp u \<inter> supp b = {}" 
  by(nominal_induct b rule:b.strong_induct,(auto simp add: pure_supp b.supp supp_at_base)+)

lemma u_fresh_bv[simp]:
  fixes  u::u and b::bv
  shows "atom u \<sharp> b"
  using fresh_at_base by simp

subsubsection \<open>Basic Types\<close>

nominal_function b_of :: "\<tau> \<Rightarrow> b" where
  "b_of \<lbrace> z : b | c \<rbrace> = b"
     apply(auto,simp add: eqvt_def b_of_graph_aux_def )
  by (meson \<tau>.exhaust)
nominal_termination (eqvt)  by lexicographic_order

lemma supp_b_empty[simp]:
  fixes b :: b and x::x
  shows "atom x \<notin> supp b"
  by (induct b rule: b.induct, auto simp: pure_supp supp_at_base x_not_in_b_set)

lemma flip_b_id[simp]:
  fixes x::x and b::b
  shows "(x \<leftrightarrow> x') \<bullet> b = b"
  by(rule flip_fresh_fresh, auto simp add: fresh_def)

lemma flip_x_b_cancel[simp]:
  fixes x::x and y::x  and b::b and bv::bv
  shows "(x \<leftrightarrow> y) \<bullet> b = b" and "(x \<leftrightarrow> y) \<bullet> bv = bv"
  using flip_b_id  apply simp
  by (metis b.eq_iff(7) b.perm_simps(7) flip_b_id)

lemma flip_bv_x_cancel[simp]:
  fixes bv::bv and z::bv and x::x
  shows "(bv \<leftrightarrow> z) \<bullet> x = x" using flip_fresh_fresh[of bv x z] fresh_at_base by auto

lemma flip_bv_u_cancel[simp]:
  fixes bv::bv and z::bv and x::u
  shows "(bv \<leftrightarrow> z) \<bullet> x = x" using flip_fresh_fresh[of bv x z] fresh_at_base by auto

subsubsection \<open>Literals\<close>

lemma supp_bitvec_empty:
  fixes bv::"bit list"
  shows "supp bv = {}"
proof(induct bv)
  case Nil
  then show ?case using supp_Nil by auto
next
  case (Cons a bv)
  then show ?case using supp_Cons  bit.supp
    by (metis (mono_tags, hide_lams) bit.strong_exhaust l.supp(5) sup_bot.right_neutral)
qed

lemma bitvec_pure[simp]:
  fixes bv::"bit list" and x::x
  shows "atom x \<sharp> bv" using fresh_def supp_bitvec_empty by auto

lemma supp_l_empty[simp]:
  fixes l:: l
  shows "supp (V_lit l) = {}"
  by(nominal_induct l rule: l.strong_induct,
      auto simp add: l.strong_exhaust pure_supp v.fv_defs supp_bitvec_empty)

lemma type_l_nosupp[simp]:
  fixes x::x and l::l
  shows "atom x \<notin> supp (\<lbrace> z : b  |  [[z]\<^sup>v]\<^sup>c\<^sup>e ==  [[l]\<^sup>v]\<^sup>c\<^sup>e \<rbrace>)"
  using supp_at_base supp_l_empty ce.supp(1) c.supp \<tau>.supp by force

lemma flip_bitvec0:
  fixes x::"bit list"
  assumes "atom c \<sharp> (z, x, z')"
  shows "(z \<leftrightarrow> c) \<bullet> x = (z' \<leftrightarrow> c) \<bullet> x"
proof - 
  have "atom z \<sharp> x" and "atom z' \<sharp> x"
    using flip_fresh_fresh assms supp_bitvec_empty fresh_def by blast+
  moreover have "atom c \<sharp> x" using  supp_bitvec_empty fresh_def by auto
  ultimately show ?thesis  using assms flip_fresh_fresh by metis
qed

lemma flip_bitvec:
  assumes "atom c \<sharp> (z, L_bitvec x, z')"
  shows "(z \<leftrightarrow> c) \<bullet> x = (z' \<leftrightarrow> c) \<bullet> x"
proof - 
  have "atom z \<sharp> x" and "atom z' \<sharp> x"
    using flip_fresh_fresh assms supp_bitvec_empty fresh_def by blast+
  moreover have "atom c \<sharp> x" using  supp_bitvec_empty fresh_def by auto
  ultimately show ?thesis  using assms flip_fresh_fresh by metis
qed

lemma type_l_eq:
  shows "\<lbrace> z : b  |  [[z]\<^sup>v]\<^sup>c\<^sup>e == [V_lit l]\<^sup>c\<^sup>e \<rbrace> = (\<lbrace> z' : b  |  [[z']\<^sup>v]\<^sup>c\<^sup>e == [V_lit l]\<^sup>c\<^sup>e \<rbrace>)"
  by(auto,nominal_induct l rule: l.strong_induct,auto, metis permute_pure, auto simp add: flip_bitvec)

lemma flip_l_eq:
  fixes x::l
  shows "(z \<leftrightarrow> c) \<bullet> x = (z' \<leftrightarrow> c) \<bullet> x"
proof - 
  have "atom z \<sharp> x" and "atom c \<sharp> x" and "atom z' \<sharp> x"
    using flip_fresh_fresh fresh_def supp_l_empty by fastforce+
  thus ?thesis using flip_fresh_fresh by metis
qed

lemma flip_l_eq1:
  fixes x::l
  assumes  "(z \<leftrightarrow> c) \<bullet> x = (z' \<leftrightarrow> c) \<bullet> x'"
  shows "x' = x"
proof - 
  have "atom z \<sharp> x" and "atom c \<sharp> x'" and "atom c \<sharp> x" and "atom z' \<sharp> x'"
    using flip_fresh_fresh fresh_def supp_l_empty by fastforce+
  thus ?thesis using flip_fresh_fresh assms by metis
qed

subsubsection \<open>Types\<close>

lemma flip_base_eq:
  fixes b::b and x::x and y::x                      
  shows "(x \<leftrightarrow> y) \<bullet> b = b"
  using b.fresh  by (simp add: flip_fresh_fresh fresh_def)

text \<open> Obtain an alpha-equivalent type where the bound variable is fresh in some term t \<close>
lemma has_fresh_z0:
  fixes t::"'b::fs"
  shows "\<exists>z. atom z \<sharp> (c',t) \<and> (\<lbrace>z' : b | c' \<rbrace>) = (\<lbrace> z : b | (z \<leftrightarrow> z' ) \<bullet> c' \<rbrace>)"
proof -
  obtain z::x where fr: "atom z \<sharp> (c',t)" using obtain_fresh by blast
  moreover hence "(\<lbrace> z' : b | c' \<rbrace>) = (\<lbrace> z : b | (z \<leftrightarrow> z') \<bullet> c' \<rbrace>)"  
    using \<tau>.eq_iff Abs1_eq_iff
    by (metis flip_commute flip_fresh_fresh fresh_PairD(1))
  ultimately show ?thesis by fastforce
qed

lemma has_fresh_z:
  fixes t::"'b::fs"
  shows "\<exists>z b c. atom z \<sharp> t \<and> \<tau> = \<lbrace> z : b | c \<rbrace>"
proof -
  obtain z' and b and c' where teq: "\<tau> =  (\<lbrace> z' : b | c' \<rbrace>)" using \<tau>.exhaust by blast
  obtain z::x where fr: "atom z \<sharp> (t,c')" using obtain_fresh by blast
  hence "(\<lbrace> z' : b | c' \<rbrace>) = (\<lbrace> z : b | (z \<leftrightarrow> z') \<bullet> c' \<rbrace>)"  using \<tau>.eq_iff Abs1_eq_iff
      flip_commute flip_fresh_fresh fresh_PairD(1)  by (metis fresh_PairD(2))
  hence "atom z \<sharp> t \<and> \<tau> = (\<lbrace> z : b | (z \<leftrightarrow> z') \<bullet> c' \<rbrace>)" using fr teq by force
  thus ?thesis using teq fr by fast
qed

lemma obtain_fresh_z:
  fixes t::"'b::fs"
  obtains z and b and c where "atom z \<sharp> t \<and> \<tau> = \<lbrace> z : b | c \<rbrace>"
  using has_fresh_z by blast

lemma has_fresh_z2:
  fixes t::"'b::fs"
  shows "\<exists>z c. atom z \<sharp> t \<and> \<tau> = \<lbrace> z : b_of \<tau> | c \<rbrace>" 
proof -
  obtain z and b and c where "atom z \<sharp> t \<and> \<tau> = \<lbrace> z : b | c \<rbrace>" using obtain_fresh_z by metis
  moreover then have "b_of \<tau> = b" using \<tau>.eq_iff by simp
  ultimately show ?thesis using obtain_fresh_z \<tau>.eq_iff by auto
qed

lemma obtain_fresh_z2:
  fixes t::"'b::fs"
  obtains z and  c where "atom z \<sharp> t \<and> \<tau> = \<lbrace> z : b_of \<tau> | c \<rbrace>"
  using has_fresh_z2 by blast

subsubsection \<open>Values\<close>

lemma u_notin_supp_v[simp]:
  fixes u::u and v::v
  shows "atom u \<notin> supp v" 
proof(nominal_induct v rule: v.strong_induct)
  case (V_lit l)
  then show ?case  using supp_l_empty by auto
next
  case (V_var x)
  then show ?case 
    by (simp add: supp_at_base)
next
  case (V_pair v1 v2)
  then show ?case by auto
next
  case (V_cons tyid list v)
  then show ?case using pure_supp by auto
next
  case (V_consp tyid list b v)
  then show ?case using pure_supp by auto
qed

lemma u_fresh_xv[simp]:
  fixes u::u and x::x and v::v
  shows "atom u \<sharp>  (x,v)"
proof - 
  have "atom u \<sharp> x" using fresh_def by fastforce
  moreover have "atom u \<sharp> v" using fresh_def u_notin_supp_v by metis
  ultimately show ?thesis using fresh_prod2 by auto
qed

text \<open> Part of an effort to make the proofs across inductive cases more uniform by distilling 
the non-uniform parts into lemmas like this\<close>
lemma v_flip_eq:
  fixes v::v and va::v and x::x and c::x
  assumes "atom c \<sharp> (v, va)" and "atom c \<sharp> (x, xa, v, va)" and "(x \<leftrightarrow> c) \<bullet> v = (xa \<leftrightarrow> c) \<bullet> va" 
  shows "((v = V_lit l \<longrightarrow> (\<exists>l'. va = V_lit l' \<and>  (x \<leftrightarrow> c) \<bullet> l = (xa \<leftrightarrow> c) \<bullet> l'))) \<and>
         ((v = V_var y \<longrightarrow> (\<exists>y'. va = V_var y' \<and>  (x \<leftrightarrow> c) \<bullet> y = (xa \<leftrightarrow> c) \<bullet> y'))) \<and>
         ((v = V_pair vone vtwo \<longrightarrow> (\<exists>v1' v2'. va = V_pair v1' v2' \<and>  (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1' \<and>  (x \<leftrightarrow> c) \<bullet> vtwo = (xa \<leftrightarrow> c) \<bullet> v2'))) \<and>
         ((v = V_cons tyid dc vone \<longrightarrow> (\<exists>v1'. va = V_cons tyid dc v1'\<and>  (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1'))) \<and>
         ((v = V_consp tyid dc b vone \<longrightarrow> (\<exists>v1'. va = V_consp tyid dc b v1'\<and>  (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1')))" 
  using assms proof(nominal_induct v rule:v.strong_induct)
  case (V_lit l)
  then show ?case  using assms v.perm_simps 
      empty_iff flip_def fresh_def fresh_permute_iff supp_l_empty swap_fresh_fresh v.fresh 
    by (metis permute_swap_cancel2 v.distinct)
next
  case (V_var x)
  then show ?case  using assms v.perm_simps 
      empty_iff flip_def fresh_def fresh_permute_iff supp_l_empty swap_fresh_fresh v.fresh 
    by (metis permute_swap_cancel2 v.distinct)
next
  case (V_pair v1 v2)
  have " (V_pair v1 v2 = V_pair vone vtwo \<longrightarrow> (\<exists>v1' v2'. va = V_pair v1' v2' \<and> (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1' \<and> (x \<leftrightarrow> c) \<bullet> vtwo = (xa \<leftrightarrow> c) \<bullet> v2'))" proof
    assume "V_pair v1 v2= V_pair vone vtwo"    
    thus  "(\<exists>v1' v2'. va = V_pair v1' v2' \<and> (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1' \<and> (x \<leftrightarrow> c) \<bullet> vtwo = (xa \<leftrightarrow> c) \<bullet> v2')"
      using V_pair assms 
      by (metis (no_types, hide_lams) flip_def permute_swap_cancel v.perm_simps(3)) 
  qed
  thus ?case using V_pair by auto
next
  case (V_cons tyid dc v1)
  have " (V_cons tyid dc v1 = V_cons tyid dc vone \<longrightarrow> (\<exists> v1'. va = V_cons tyid dc  v1' \<and> (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1'))" proof
    assume as: "V_cons tyid dc v1 = V_cons tyid dc  vone"    
    hence "(x \<leftrightarrow> c) \<bullet>  (V_cons tyid dc  vone) =  V_cons tyid dc ((x \<leftrightarrow> c) \<bullet> vone)" proof -
      have "(x \<leftrightarrow> c)  \<bullet> dc = dc" using pure_permute_id  by metis
      moreover have "(x \<leftrightarrow> c)  \<bullet> tyid = tyid" using pure_permute_id  by metis
      ultimately show ?thesis using v.perm_simps(4) by simp
    qed
    then obtain v1' where "(xa \<leftrightarrow> c) \<bullet> va = V_cons tyid dc v1' \<and> (x \<leftrightarrow> c) \<bullet> vone = v1'" using assms V_cons
      using as by fastforce
    hence " va = V_cons tyid dc ((xa \<leftrightarrow> c) \<bullet> v1') \<and> (x \<leftrightarrow> c) \<bullet> vone = v1'" using permute_flip_cancel empty_iff flip_def fresh_def supp_b_empty swap_fresh_fresh
      by (metis pure_fresh v.perm_simps(4))

    thus  "(\<exists>v1'. va = V_cons tyid dc  v1' \<and> (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1')"
      using V_cons assms by simp     
  qed
  thus ?case using V_cons by auto
next
  case (V_consp tyid dc b v1)
  have " (V_consp tyid dc b v1 = V_consp tyid dc b vone \<longrightarrow> (\<exists> v1'. va = V_consp tyid dc  b v1' \<and> (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1'))" proof
    assume as: "V_consp tyid dc b v1 = V_consp tyid dc b vone"    
    hence "(x \<leftrightarrow> c) \<bullet>  (V_consp tyid dc  b vone) =  V_consp tyid dc b ((x \<leftrightarrow> c) \<bullet> vone)" proof -
      have "(x \<leftrightarrow> c)  \<bullet> dc = dc" using pure_permute_id  by metis
      moreover have "(x \<leftrightarrow> c)  \<bullet> tyid = tyid" using pure_permute_id  by metis
      ultimately show ?thesis using v.perm_simps(4) by simp
    qed
    then obtain v1' where "(xa \<leftrightarrow> c) \<bullet> va = V_consp tyid dc b v1' \<and> (x \<leftrightarrow> c) \<bullet> vone = v1'" using assms V_consp
      using as by fastforce
    hence " va = V_consp tyid dc b ((xa \<leftrightarrow> c) \<bullet> v1') \<and> (x \<leftrightarrow> c) \<bullet> vone = v1'" using permute_flip_cancel empty_iff flip_def fresh_def supp_b_empty swap_fresh_fresh
        pure_fresh v.perm_simps 
      by (metis (mono_tags, hide_lams))   
    thus   "(\<exists>v1'. va = V_consp tyid dc  b v1' \<and> (x \<leftrightarrow> c) \<bullet> vone = (xa \<leftrightarrow> c) \<bullet> v1')"
      using V_consp assms by simp     
  qed
  thus ?case using V_consp by auto
qed

lemma flip_eq:
  fixes x::x and xa::x and s::"'a::fs" and sa::"'a::fs"
  assumes "(\<forall>c. atom c \<sharp> (s, sa) \<longrightarrow> atom c \<sharp> (x, xa, s, sa) \<longrightarrow> (x \<leftrightarrow> c) \<bullet> s = (xa \<leftrightarrow> c) \<bullet> sa)" and "x \<noteq> xa"
  shows "(x \<leftrightarrow> xa) \<bullet> s = sa" 
proof - 
  have  " ([[atom x]]lst. s = [[atom xa]]lst. sa)" using assms Abs1_eq_iff_all by simp
  hence  "(xa = x \<and> sa = s \<or> xa \<noteq> x \<and> sa = (xa \<leftrightarrow> x) \<bullet> s \<and> atom xa \<sharp> s)" using assms Abs1_eq_iff[of xa sa x s] by simp
  thus ?thesis using assms
    by (metis flip_commute)
qed

lemma  swap_v_supp:
  fixes v::v and d::x and z::x
  assumes "atom d \<sharp> v"
  shows "supp ((z \<leftrightarrow> d ) \<bullet> v) \<subseteq> supp v - { atom z } \<union> { atom d}"
  using assms
proof(nominal_induct v rule:v.strong_induct)
  case (V_lit l)
  then show ?case using l.supp by (metis supp_l_empty empty_subsetI l.strong_exhaust pure_supp supp_eqvt v.supp)
next
  case (V_var x)
  hence "d \<noteq> x" using fresh_def by fastforce
  thus ?case apply(cases "z = x")  using   supp_at_base V_var \<open>d\<noteq>x\<close> by fastforce+
next
  case (V_cons tyid dc v)
  show ?case using v.supp(4) pure_supp 
    using V_cons.hyps V_cons.prems fresh_def by auto
next
  case (V_consp tyid dc b v)
  show ?case using v.supp(4) pure_supp 
    using V_consp.hyps V_consp.prems fresh_def by auto
qed(force+)

subsubsection \<open>Expressions\<close>

lemma  swap_e_supp:
  fixes e::e and d::x and z::x
  assumes "atom d \<sharp> e"
  shows "supp ((z \<leftrightarrow> d ) \<bullet> e) \<subseteq> supp e - { atom z } \<union> { atom d}"
  using assms
proof(nominal_induct e rule:e.strong_induct)
  case (AE_val v)
  then show ?case using swap_v_supp by simp
next
  case (AE_app f v)
  then show ?case using swap_v_supp  by (simp add: pure_supp)
next
  case (AE_appP b f v)
  hence df: "atom d \<sharp> v" using fresh_def e.supp by force
  have  "supp ((z \<leftrightarrow> d ) \<bullet> (AE_appP b f v)) =  supp (AE_appP b f ((z \<leftrightarrow> d ) \<bullet> v))" using  e.supp 
    by (metis b.eq_iff(3) b.perm_simps(3) e.perm_simps(3) flip_b_id)
  also have "... = supp b \<union> supp f \<union> supp ((z \<leftrightarrow> d ) \<bullet> v)" using e.supp by auto
  also have "... \<subseteq>  supp b \<union> supp f \<union> supp v  - { atom z } \<union> { atom d}" using swap_v_supp[OF df] pure_supp  by auto
  finally show ?case using e.supp by auto
next
  case (AE_op opp v1 v2)
  hence df: "atom d \<sharp> v1 \<and> atom d \<sharp> v2" using fresh_def e.supp by force
  have "((z \<leftrightarrow> d ) \<bullet> (AE_op opp v1 v2)) = AE_op opp ((z \<leftrightarrow> d ) \<bullet> v1) ((z \<leftrightarrow> d ) \<bullet> v2)" using
      e.perm_simps flip_commute opp.perm_simps AE_op opp.strong_exhaust  pure_supp
    by (metis (full_types))

  hence "supp ((z \<leftrightarrow> d) \<bullet> AE_op opp v1 v2) = supp (AE_op opp ((z \<leftrightarrow> d) \<bullet>v1)  ((z \<leftrightarrow> d) \<bullet>v2))" by simp
  also have "... = supp  ((z \<leftrightarrow> d) \<bullet>v1) \<union> supp  ((z \<leftrightarrow> d) \<bullet>v2)" using e.supp 
    by (metis (mono_tags, hide_lams) opp.strong_exhaust opp.supp sup_bot.left_neutral)
  also have "... \<subseteq> (supp v1 -  { atom z } \<union> { atom d}) \<union>  (supp v2 - { atom z } \<union> { atom d})" using swap_v_supp AE_op df by blast
  finally show ?case using e.supp opp.supp by blast
next
  case (AE_fst v)
  then show ?case   using swap_v_supp by auto
next
  case (AE_snd v)
  then show ?case   using swap_v_supp by auto
next
  case (AE_mvar u)
  then show ?case using 
      Diff_empty Diff_insert0 Un_upper1 atom_x_sort flip_def flip_fresh_fresh fresh_def set_eq_subset supp_eqvt swap_set_in_eq 
    by (metis sort_of_atom_eq)
next 
  case (AE_len v)
  then show ?case   using swap_v_supp by auto
next
  case (AE_concat v1 v2)
  then show ?case   using swap_v_supp by auto
next
  case (AE_split v1 v2)
  then show ?case   using swap_v_supp by auto
qed

lemma  swap_ce_supp:
  fixes e::ce and d::x and z::x
  assumes "atom d \<sharp> e"
  shows "supp ((z \<leftrightarrow> d ) \<bullet> e) \<subseteq> supp e - { atom z } \<union> { atom d}"
  using assms
proof(nominal_induct e rule:ce.strong_induct)
  case (CE_val v)
  then show ?case using swap_v_supp ce.fresh ce.supp by simp
next
  case (CE_op opp v1 v2)
  hence df: "atom d \<sharp> v1 \<and> atom d \<sharp> v2" using fresh_def e.supp by force
  have "((z \<leftrightarrow> d ) \<bullet> (CE_op opp v1 v2)) = CE_op opp ((z \<leftrightarrow> d ) \<bullet> v1) ((z \<leftrightarrow> d ) \<bullet> v2)" using
      ce.perm_simps flip_commute opp.perm_simps CE_op opp.strong_exhaust x_fresh_b pure_supp 
    by (metis (full_types))

  hence "supp ((z \<leftrightarrow> d) \<bullet> CE_op opp v1 v2) = supp (CE_op opp ((z \<leftrightarrow> d) \<bullet>v1)  ((z \<leftrightarrow> d) \<bullet>v2))" by simp
  also have "... = supp  ((z \<leftrightarrow> d) \<bullet>v1) \<union> supp  ((z \<leftrightarrow> d) \<bullet>v2)" using ce.supp 
    by (metis (mono_tags, hide_lams) opp.strong_exhaust opp.supp sup_bot.left_neutral)
  also have "... \<subseteq> (supp v1 -  { atom z } \<union> { atom d}) \<union>  (supp v2 - { atom z } \<union> { atom d})" using swap_v_supp CE_op df by blast
  finally show ?case using ce.supp opp.supp by blast
next
  case (CE_fst v)
  then show ?case   using ce.supp ce.fresh swap_v_supp by auto
next
  case (CE_snd v)
  then show ?case   using ce.supp ce.fresh swap_v_supp by auto
next
  case (CE_len v)
  then show ?case   using ce.supp ce.fresh swap_v_supp by auto
next
  case (CE_concat v1 v2)
  then show ?case using ce.supp ce.fresh swap_v_supp ce.perm_simps 
  proof -
    have "\<forall>x v xa. \<not> atom (x::x) \<sharp> (v::v) \<or> supp ((xa \<leftrightarrow> x) \<bullet> v) \<subseteq> supp v - {atom xa} \<union> {atom x}"
      by (meson swap_v_supp) (* 0.0 ms *)
    then show ?thesis
      using CE_concat ce.supp by auto
  qed
qed

lemma  swap_c_supp:
  fixes c::c and d::x and z::x
  assumes "atom d \<sharp> c"
  shows "supp ((z \<leftrightarrow> d ) \<bullet> c) \<subseteq> supp c - { atom z } \<union> { atom d}"
  using assms
proof(nominal_induct c rule:c.strong_induct)
  case (C_eq e1 e2)
  then show ?case using swap_ce_supp by auto
qed(auto+)

lemma type_e_eq:
  assumes "atom z \<sharp> e" and "atom z' \<sharp> e"
  shows "\<lbrace> z : b  |  [[z]\<^sup>v]\<^sup>c\<^sup>e == e \<rbrace> = (\<lbrace> z' : b  |  [[z']\<^sup>v]\<^sup>c\<^sup>e ==  e \<rbrace>)"
  by (auto,metis (full_types) assms(1) assms(2) flip_fresh_fresh fresh_PairD(1) fresh_PairD(2))

lemma type_e_eq2:
  assumes "atom z \<sharp> e" and "atom z' \<sharp> e" and "b=b'"
  shows "\<lbrace> z : b  |  [[z]\<^sup>v]\<^sup>c\<^sup>e == e \<rbrace> = (\<lbrace> z' : b'  |  [[z']\<^sup>v]\<^sup>c\<^sup>e == e \<rbrace>)"
  using assms type_e_eq by fast

lemma e_flip_eq:
  fixes e::e and ea::e
  assumes "atom c \<sharp> (e, ea)" and "atom c \<sharp> (x, xa, e, ea)" and "(x \<leftrightarrow> c) \<bullet> e = (xa \<leftrightarrow> c) \<bullet> ea" 
  shows "(e = AE_val w \<longrightarrow> (\<exists>w'. ea = AE_val w' \<and> (x \<leftrightarrow> c) \<bullet> w = (xa \<leftrightarrow> c) \<bullet> w')) \<or> 
         (e = AE_op opp v1 v2 \<longrightarrow> (\<exists>v1' v2'. ea = AS_op opp v1' v2' \<and> (x \<leftrightarrow> c) \<bullet> v1 = (xa \<leftrightarrow> c) \<bullet> v1') \<and> (x \<leftrightarrow> c) \<bullet> v2 = (xa \<leftrightarrow> c) \<bullet> v2') \<or> 
         (e = AE_fst v \<longrightarrow> (\<exists>v'. ea = AE_fst v' \<and> (x \<leftrightarrow> c) \<bullet> v = (xa \<leftrightarrow> c) \<bullet> v')) \<or> 
         (e = AE_snd v \<longrightarrow> (\<exists>v'. ea = AE_snd v' \<and> (x \<leftrightarrow> c) \<bullet> v = (xa \<leftrightarrow> c) \<bullet> v')) \<or> 
         (e = AE_len v \<longrightarrow> (\<exists>v'. ea = AE_len v' \<and> (x \<leftrightarrow> c) \<bullet> v = (xa \<leftrightarrow> c) \<bullet> v')) \<or> 
         (e = AE_concat v1 v2 \<longrightarrow> (\<exists>v1' v2'. ea = AS_concat v1' v2' \<and> (x \<leftrightarrow> c) \<bullet> v1 = (xa \<leftrightarrow> c) \<bullet> v1') \<and> (x \<leftrightarrow> c) \<bullet> v2 = (xa \<leftrightarrow> c) \<bullet> v2') \<or> 
         (e = AE_app f v \<longrightarrow> (\<exists>v'. ea = AE_app f  v' \<and> (x \<leftrightarrow> c) \<bullet> v = (xa \<leftrightarrow> c) \<bullet> v'))"
  by (metis assms e.perm_simps permute_flip_cancel2)

lemma fresh_opp_all:
  fixes opp::opp
  shows "z \<sharp> opp"
  using e.fresh opp.exhaust opp.fresh  by metis

lemma fresh_e_opp_all:
  shows "(z \<sharp> v1 \<and> z \<sharp> v2) = z \<sharp> AE_op opp v1 v2"
  using e.fresh opp.exhaust opp.fresh fresh_opp_all by simp

lemma fresh_e_opp:
  fixes z::x
  assumes "atom z \<sharp> v1 \<and> atom z \<sharp> v2"
  shows "atom z \<sharp> AE_op opp v1 v2"
  using e.fresh opp.exhaust opp.fresh opp.supp  by (metis assms)

subsubsection \<open>Statements\<close>

lemma branch_s_flip_eq:
  fixes v::v and va::v
  assumes "atom c \<sharp> (v, va)" and "atom c \<sharp> (x, xa, v, va)" and "(x \<leftrightarrow> c) \<bullet> s = (xa \<leftrightarrow> c) \<bullet> sa" 
  shows "(s = AS_val w \<longrightarrow> (\<exists>w'. sa = AS_val w' \<and> (x \<leftrightarrow> c) \<bullet> w = (xa \<leftrightarrow> c) \<bullet> w')) \<or> 
         (s = AS_seq s1 s2 \<longrightarrow> (\<exists>s1' s2'. sa = AS_seq s1' s2' \<and> (x \<leftrightarrow> c) \<bullet> s1 = (xa \<leftrightarrow> c) \<bullet> s1') \<and> (x \<leftrightarrow> c) \<bullet> s2 = (xa \<leftrightarrow> c) \<bullet> s2') \<or> 
         (s = AS_if v s1 s2 \<longrightarrow> (\<exists>v' s1' s2'. sa = AS_if seq s1' s2' \<and> (x \<leftrightarrow> c) \<bullet> s1 = (xa \<leftrightarrow> c) \<bullet> s1') \<and> (x \<leftrightarrow> c) \<bullet> s2 = (xa \<leftrightarrow> c) \<bullet> s2' \<and> (x \<leftrightarrow> c) \<bullet> c = (xa \<leftrightarrow> c) \<bullet> v')"
  by (metis assms s_branch_s_branch_list.perm_simps permute_flip_cancel2)

section \<open>Context Syntax\<close>

subsection \<open>Datatypes\<close>

text \<open>Type and function/type definition contexts\<close>
type_synonym \<Phi> = "fun_def list"
type_synonym \<Theta> = "type_def list"
type_synonym \<B> = "bv fset"

datatype \<Gamma> = 
  GNil
  | GCons "x*b*c" \<Gamma>  (infixr "#\<^sub>\<Gamma>" 65)

datatype \<Delta> = 
  DNil  ("[]\<^sub>\<Delta>")
  | DCons "u*\<tau>" \<Delta>  (infixr "#\<^sub>\<Delta>" 65)

subsection \<open>Functions and Lemmas\<close>

lemma \<Gamma>_induct [case_names GNil GCons] : "P GNil \<Longrightarrow> (\<And>x b c \<Gamma>'. P \<Gamma>' \<Longrightarrow> P ((x,b,c) #\<^sub>\<Gamma> \<Gamma>')) \<Longrightarrow> P \<Gamma>"
proof(induct \<Gamma> rule:\<Gamma>.induct)
  case GNil
  then show ?case by auto 
next
  case (GCons x1 x2)
  then obtain x and b and c where "x1=(x,b,c)"  using prod_cases3 by blast
  then show ?case using GCons by presburger
qed

instantiation \<Delta> ::  pt
begin

primrec permute_\<Delta>
  where
    DNil_eqvt:  "p \<bullet> DNil = DNil"
  | DCons_eqvt: "p \<bullet> (x #\<^sub>\<Delta> xs) = p \<bullet> x #\<^sub>\<Delta> p \<bullet> (xs::\<Delta>)"

instance  by standard (induct_tac [!] x, simp_all)
end

lemmas [eqvt] =  permute_\<Delta>.simps 

lemma \<Delta>_induct [case_names DNil DCons] : "P DNil \<Longrightarrow> (\<And>u t \<Delta>'. P \<Delta>' \<Longrightarrow> P ((u,t) #\<^sub>\<Delta> \<Delta>')) \<Longrightarrow> P \<Delta>"
proof(induct \<Delta> rule: \<Delta>.induct)
  case DNil
  then show ?case by auto 
next
  case (DCons x1 x2)
  then obtain u and t  where "x1=(u,t)"  by fastforce
  then show ?case using DCons by presburger
qed

lemma \<Phi>_induct [case_names PNil PConsNone PConsSome] : "P [] \<Longrightarrow> (\<And>f x b c \<tau> s' \<Phi>'. P \<Phi>' \<Longrightarrow> P ((AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s'))) # \<Phi>')) \<Longrightarrow>
                                                                  (\<And>f bv x b c \<tau> s' \<Phi>'. P \<Phi>' \<Longrightarrow> P ((AF_fundef f (AF_fun_typ_some bv (AF_fun_typ x b c \<tau> s'))) # \<Phi>'))  \<Longrightarrow> P \<Phi>"
proof(induct \<Phi> rule: list.induct)
  case Nil
  then show ?case by auto 
next
  case (Cons x1 x2)
  then obtain f and t where ft: "x1 = (AF_fundef f t)" 
    by (meson fun_def.exhaust)
  then show ?case proof(nominal_induct t rule:fun_typ_q.strong_induct)
    case (AF_fun_typ_some bv ft)
    then show ?case using Cons ft 
      by (metis fun_typ.exhaust)
  next
    case (AF_fun_typ_none ft)
    then show ?case using Cons ft 
      by (metis fun_typ.exhaust)
  qed
qed

lemma \<Theta>_induct [case_names TNil AF_typedef AF_typedef_poly] : "P [] \<Longrightarrow> (\<And>tid dclist \<Theta>'. P \<Theta>' \<Longrightarrow> P ((AF_typedef tid dclist) # \<Theta>')) \<Longrightarrow>
                                                                  (\<And>tid bv dclist \<Theta>'. P \<Theta>' \<Longrightarrow> P ((AF_typedef_poly tid bv dclist ) # \<Theta>'))  \<Longrightarrow> P \<Theta>"
proof(induct \<Theta> rule: list.induct)
  case Nil
  then show ?case by auto
next
  case (Cons td T)
  show ?case by(cases td rule: type_def.exhaust, (simp add: Cons)+)
qed

instantiation \<Gamma> ::  pt
begin

primrec permute_\<Gamma>
  where
    GNil_eqvt:  "p \<bullet> GNil = GNil"
  | GCons_eqvt: "p \<bullet> (x #\<^sub>\<Gamma> xs) = p \<bullet> x #\<^sub>\<Gamma> p \<bullet> (xs::\<Gamma>)"

instance by standard (induct_tac [!] x, simp_all)
end

lemmas [eqvt] =  permute_\<Gamma>.simps 

lemma G_cons_eqvt[simp]:
  fixes \<Gamma>::\<Gamma>
  shows "p \<bullet> ((x,b,c) #\<^sub>\<Gamma> \<Gamma>) = ((p \<bullet> x,  p \<bullet> b , p \<bullet> c) #\<^sub>\<Gamma> (p \<bullet> \<Gamma> ))" (is "?A = ?B" )
  using Cons_eqvt triple_eqvt  supp_b_empty by simp

lemma G_cons_flip[simp]:
  fixes  x::x and \<Gamma>::\<Gamma>
  shows  "(x\<leftrightarrow>x') \<bullet> ((x'',b,c) #\<^sub>\<Gamma> \<Gamma>) = (((x\<leftrightarrow>x') \<bullet> x'',  b , (x\<leftrightarrow>x') \<bullet> c) #\<^sub>\<Gamma> ((x\<leftrightarrow>x') \<bullet> \<Gamma> ))" 
  using Cons_eqvt triple_eqvt  supp_b_empty by auto

lemma G_cons_flip_fresh[simp]:
  fixes  x::x and \<Gamma>::\<Gamma> 
  assumes  "atom x \<sharp> (c,\<Gamma>)" and "atom x' \<sharp> (c,\<Gamma>)" 
  shows  "(x\<leftrightarrow>x') \<bullet> ((x',b,c) #\<^sub>\<Gamma> \<Gamma>) = ((x,  b , c) #\<^sub>\<Gamma> \<Gamma> )" 
  using G_cons_flip flip_fresh_fresh assms by force

lemma G_cons_flip_fresh2[simp]:
  fixes  x::x and \<Gamma>::\<Gamma> 
  assumes  "atom x \<sharp> (c,\<Gamma>)" and "atom x' \<sharp> (c,\<Gamma>)" 
  shows  "(x\<leftrightarrow>x') \<bullet> ((x,b,c) #\<^sub>\<Gamma> \<Gamma>) = ((x',  b , c) #\<^sub>\<Gamma> \<Gamma> )" 
  using G_cons_flip flip_fresh_fresh assms by force

lemma G_cons_flip_fresh3[simp]:
  fixes  x::x and \<Gamma>::\<Gamma> 
  assumes  "atom x \<sharp> \<Gamma>" and "atom x' \<sharp> \<Gamma>" 
  shows  "(x\<leftrightarrow>x') \<bullet> ((x',b,c) #\<^sub>\<Gamma> \<Gamma>) = ((x,  b , (x\<leftrightarrow>x') \<bullet> c) #\<^sub>\<Gamma> \<Gamma> )" 
  using G_cons_flip flip_fresh_fresh assms by force

lemma neq_GNil_conv: "(xs \<noteq> GNil) = (\<exists>y ys. xs = y #\<^sub>\<Gamma> ys)"
  by (induct xs) auto

nominal_function toList :: "\<Gamma> \<Rightarrow> (x*b*c) list" where
  "toList GNil = []"
| "toList (GCons xbc G) = xbc#(toList G)"
       apply (auto, simp add: eqvt_def toList_graph_aux_def )
  using neq_GNil_conv surj_pair by metis
nominal_termination (eqvt)
  by lexicographic_order

nominal_function toSet :: "\<Gamma> \<Rightarrow> (x*b*c) set" where
  "toSet GNil = {}"
| "toSet (GCons xbc G) = {xbc} \<union> (toSet G)"
       apply (auto,simp add: eqvt_def toSet_graph_aux_def )
  using neq_GNil_conv surj_pair by metis
nominal_termination (eqvt)
  by lexicographic_order

nominal_function append_g :: "\<Gamma> \<Rightarrow> \<Gamma> \<Rightarrow> \<Gamma>" (infixr "@" 65) where
  "append_g GNil g = g"
| "append_g (xbc #\<^sub>\<Gamma> g1) g2 = (xbc #\<^sub>\<Gamma> (g1@g2))"
       apply (auto,simp add: eqvt_def append_g_graph_aux_def )
  using neq_GNil_conv surj_pair by metis
nominal_termination (eqvt) by lexicographic_order

nominal_function dom  ::  "\<Gamma> \<Rightarrow> x set"  where
  "dom \<Gamma> = (fst` (toSet \<Gamma>))"
     apply auto
  unfolding  eqvt_def dom_graph_aux_def lfp_eqvt toSet.eqvt by simp
nominal_termination (eqvt) by lexicographic_order

text \<open> Use of this is sometimes mixed in with use of freshness and support for the context however it makes it clear
that for immutable variables, the context is `self-supporting'\<close>

nominal_function atom_dom  ::  "\<Gamma> \<Rightarrow> atom set"  where
  "atom_dom \<Gamma>  = atom`(dom  \<Gamma>)"
     apply auto
  unfolding  eqvt_def atom_dom_graph_aux_def lfp_eqvt toSet.eqvt by simp
nominal_termination (eqvt) by lexicographic_order

subsection \<open>Immutable Variable Context Lemmas\<close>

lemma append_GNil[simp]:
  "GNil @ G = G"
  by simp

lemma append_g_toSetU [simp]: "toSet (G1@G2) = toSet G1 \<union> toSet G2"
  by(induct G1, auto+)

lemma supp_GNil: 
  shows "supp GNil = {}"
  by (simp add: supp_def)

lemma supp_GCons: 
  fixes xs::\<Gamma>
  shows "supp (x #\<^sub>\<Gamma> xs) = supp x \<union> supp xs"
  by (simp add: supp_def Collect_imp_eq Collect_neg_eq)

lemma atom_dom_eq[simp]: 
  fixes G::\<Gamma>
  shows  "atom_dom ((x, b, c) #\<^sub>\<Gamma> G) = atom_dom ((x, b, c') #\<^sub>\<Gamma> G)" 
  using atom_dom.simps toSet.simps by simp

lemma dom_append[simp]:
  "atom_dom (\<Gamma>@\<Gamma>') = atom_dom \<Gamma> \<union> atom_dom \<Gamma>'"
  using image_Un append_g_toSetU atom_dom.simps dom.simps by metis

lemma dom_cons[simp]:
  "atom_dom ((x,b,c) #\<^sub>\<Gamma> G) = { atom x } \<union> atom_dom G"
  using image_Un append_g_toSetU atom_dom.simps by auto

lemma fresh_GNil[ms_fresh]: 
  shows "a \<sharp> GNil"
  by (simp add: fresh_def supp_GNil)

lemma fresh_GCons[ms_fresh]: 
  fixes xs::\<Gamma>
  shows "a \<sharp> (x #\<^sub>\<Gamma> xs) \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> xs"
  by (simp add: fresh_def supp_GCons)

lemma dom_supp_g[simp]:
  "atom_dom G \<subseteq> supp G"
  apply(induct G rule: \<Gamma>_induct,simp)
  using supp_at_base supp_Pair atom_dom.simps supp_GCons by fastforce

lemma fresh_append_g[ms_fresh]:
  fixes xs::\<Gamma>
  shows "a \<sharp> (xs @ ys) \<longleftrightarrow> a \<sharp> xs \<and> a \<sharp> ys"
  by (induct xs) (simp_all add: fresh_GNil fresh_GCons)

lemma append_g_assoc:
  fixes xs::\<Gamma> 
  shows  "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by (induct xs) simp_all

lemma append_g_inside:
  fixes xs::\<Gamma> 
  shows "xs @ (x #\<^sub>\<Gamma> ys) = (xs @ (x #\<^sub>\<Gamma> GNil)) @ ys"
  by(induct xs,auto+)

lemma finite_\<Gamma>:
  "finite (toSet \<Gamma>)" 
  by(induct \<Gamma> rule: \<Gamma>_induct,auto)

lemma supp_\<Gamma>:
  "supp \<Gamma> = supp (toSet \<Gamma>)"
proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case using supp_GNil toSet.simps
    by (simp add: supp_set_empty)
next
  case (GCons x b c \<Gamma>')
  then show ?case using  supp_GCons toSet.simps finite_\<Gamma> supp_of_finite_union 
    using supp_of_finite_insert by fastforce
qed

lemma supp_of_subset:
  fixes G::"('a::fs set)"
  assumes "finite G" and "finite G'" and "G \<subseteq> G'" 
  shows "supp G \<subseteq> supp G'"
  using supp_of_finite_sets assms  by (metis subset_Un_eq supp_of_finite_union)

lemma supp_weakening:
  assumes "toSet G \<subseteq> toSet G'"
  shows "supp G \<subseteq> supp G'"
  using supp_\<Gamma> finite_\<Gamma> by (simp add: supp_of_subset assms)

lemma fresh_weakening[ms_fresh]:
  assumes "toSet G \<subseteq> toSet G'" and "x \<sharp> G'" 
  shows "x \<sharp> G"
proof(rule ccontr)
  assume "\<not> x \<sharp> G"
  hence "x \<in> supp G" using fresh_def by auto
  hence "x \<in> supp G'" using supp_weakening assms by auto
  thus False using fresh_def assms by auto
qed

instance \<Gamma> :: fs
  by (standard, induct_tac x, simp_all add: supp_GNil supp_GCons  finite_supp)

lemma fresh_gamma_elem:
  fixes \<Gamma>::\<Gamma>
  assumes "a \<sharp> \<Gamma>"
    and "e \<in> toSet \<Gamma>"
  shows "a \<sharp> e"
  using assms by(induct \<Gamma>,auto simp add: fresh_GCons)

lemma fresh_gamma_append:
  fixes xs::\<Gamma>
  shows "a \<sharp> (xs @ ys) \<longleftrightarrow> a \<sharp> xs \<and> a \<sharp> ys"
  by (induct xs, simp_all add: fresh_GNil fresh_GCons)

lemma supp_triple[simp]:
  shows "supp (x, y, z) = supp x \<union> supp y \<union> supp z"
proof -
  have "supp (x,y,z) = supp (x,(y,z))"  by auto
  hence "supp (x,y,z) = supp x \<union> (supp y  \<union> supp z)" using supp_Pair by metis
  thus ?thesis by auto
qed

lemma supp_append_g:
  fixes xs::\<Gamma>
  shows "supp (xs @ ys) = supp xs \<union> supp ys"
  by(induct xs,auto simp add: supp_GNil supp_GCons )

lemma fresh_in_g[simp]:
  fixes \<Gamma>::\<Gamma> and x'::x
  shows "atom x' \<sharp> \<Gamma>' @ (x, b0, c0) #\<^sub>\<Gamma> \<Gamma> = (atom x' \<notin> supp \<Gamma>' \<union> supp x \<union> supp b0 \<union> supp c0 \<union> supp \<Gamma>)"
proof - 
  have  "atom x' \<sharp> \<Gamma>' @ (x, b0, c0) #\<^sub>\<Gamma> \<Gamma> = (atom x' \<notin> supp (\<Gamma>' @((x,b0,c0) #\<^sub>\<Gamma> \<Gamma>)))"
    using fresh_def by auto
  also have "... = (atom x' \<notin> supp \<Gamma>' \<union> supp ((x,b0,c0) #\<^sub>\<Gamma> \<Gamma>))" using supp_append_g by fast
  also have "... = (atom x' \<notin> supp \<Gamma>' \<union> supp x \<union> supp b0 \<union> supp c0 \<union> supp \<Gamma>)" using supp_GCons supp_append_g supp_triple  by auto
  finally show ?thesis by fast
qed

lemma fresh_suffix[ms_fresh]:
  fixes \<Gamma>::\<Gamma>
  assumes "atom x \<sharp> \<Gamma>'@\<Gamma>"
  shows "atom x \<sharp> \<Gamma>"
  using assms by(induct  \<Gamma>' rule: \<Gamma>_induct, auto simp add: append_g.simps fresh_GCons)

lemma not_GCons_self [simp]:
  fixes xs::\<Gamma>
  shows "xs \<noteq> x #\<^sub>\<Gamma> xs"
  by (induct xs) auto

lemma not_GCons_self2 [simp]: 
  fixes xs::\<Gamma>
  shows "x #\<^sub>\<Gamma> xs \<noteq> xs"
  by (rule not_GCons_self [symmetric])

lemma fresh_restrict:
  fixes y::x and \<Gamma>::\<Gamma>
  assumes  "atom y \<sharp>  (\<Gamma>' @ (x, b, c) #\<^sub>\<Gamma> \<Gamma>)"
  shows "atom y \<sharp> (\<Gamma>'@\<Gamma>)"
  using assms by(induct \<Gamma>' rule: \<Gamma>_induct, auto simp add:fresh_GCons fresh_GNil  )

lemma fresh_dom_free:
  assumes "atom x \<sharp> \<Gamma>" 
  shows "(x,b,c) \<notin> toSet \<Gamma>"
  using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  hence "x\<noteq>x'" using fresh_def fresh_GCons fresh_Pair supp_at_base by blast
  moreover have "atom x \<sharp> \<Gamma>'" using fresh_GCons GCons by auto
  ultimately show ?case using toSet.simps GCons by auto
qed

lemma \<Gamma>_set_intros: "x \<in> toSet ( x #\<^sub>\<Gamma> xs)" and "y \<in> toSet xs \<Longrightarrow> y \<in> toSet (x #\<^sub>\<Gamma> xs)"
  by simp+

lemma fresh_dom_free2:
  assumes "atom x \<notin> atom_dom \<Gamma>" 
  shows "(x,b,c) \<notin> toSet \<Gamma>"
  using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  hence "x\<noteq>x'" using fresh_def fresh_GCons fresh_Pair supp_at_base by auto
  moreover have "atom x \<notin> atom_dom \<Gamma>'" using fresh_GCons GCons by auto
  ultimately show ?case using toSet.simps GCons by auto
qed

subsection \<open>Mutable Variable Context Lemmas\<close>

lemma supp_DNil: 
  shows "supp DNil = {}"
  by (simp add: supp_def)

lemma supp_DCons: 
  fixes xs::\<Delta>
  shows "supp (x #\<^sub>\<Delta> xs) = supp x \<union> supp xs"
  by (simp add: supp_def Collect_imp_eq Collect_neg_eq)

lemma fresh_DNil[ms_fresh]:
  shows "a \<sharp> DNil"
  by (simp add: fresh_def supp_DNil)

lemma fresh_DCons[ms_fresh]: 
  fixes xs::\<Delta>
  shows "a \<sharp> (x #\<^sub>\<Delta> xs) \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> xs"
  by (simp add: fresh_def supp_DCons)

instance \<Delta> :: fs
  by (standard, induct_tac x, simp_all add: supp_DNil supp_DCons  finite_supp)

subsection \<open>Lookup Functions\<close>

nominal_function lookup :: "\<Gamma> \<Rightarrow> x \<Rightarrow> (b*c) option" where
  "lookup GNil x = None"
| "lookup ((x,b,c)#\<^sub>\<Gamma>G) y = (if x=y then Some (b,c) else lookup G y)"
  by (auto,simp add: eqvt_def lookup_graph_aux_def, metis neq_GNil_conv surj_pair)
nominal_termination (eqvt) by lexicographic_order

nominal_function replace_in_g :: "\<Gamma> \<Rightarrow> x \<Rightarrow> c \<Rightarrow> \<Gamma>"  ("_[_\<longmapsto>_]" [1000,0,0] 200) where
  "replace_in_g GNil _ _ = GNil"
| "replace_in_g ((x,b,c)#\<^sub>\<Gamma>G) x' c' = (if x=x' then ((x,b,c')#\<^sub>\<Gamma>G) else (x,b,c)#\<^sub>\<Gamma>(replace_in_g G x' c'))"
       apply(auto,simp add: eqvt_def replace_in_g_graph_aux_def)
  using surj_pair \<Gamma>.exhaust by metis
nominal_termination (eqvt) by lexicographic_order

text \<open> Functions for looking up data-constructors in the Pi context \<close> 

nominal_function lookup_fun :: "\<Phi> \<Rightarrow> f  \<Rightarrow> fun_def option" where
  "lookup_fun [] g = None"
|  "lookup_fun ((AF_fundef f ft)#\<Pi>) g = (if (f=g) then Some (AF_fundef f ft) else lookup_fun \<Pi> g)"
       apply(auto,simp add: eqvt_def lookup_fun_graph_aux_def )
  by (metis fun_def.exhaust neq_Nil_conv)
nominal_termination (eqvt)  by lexicographic_order

nominal_function lookup_td :: "\<Theta> \<Rightarrow> string  \<Rightarrow> type_def option" where
  "lookup_td [] g = None"
|  "lookup_td ((AF_typedef s lst ) # (\<Theta>::\<Theta>)) g = (if (s = g) then Some (AF_typedef s lst ) else lookup_td \<Theta> g)"
|  "lookup_td ((AF_typedef_poly s bv lst ) # (\<Theta>::\<Theta>)) g = (if (s = g) then Some (AF_typedef_poly s bv lst ) else lookup_td \<Theta> g)"
          apply(auto,simp add: eqvt_def lookup_td_graph_aux_def )
  by (metis type_def.exhaust neq_Nil_conv)
nominal_termination (eqvt)  by lexicographic_order

nominal_function name_of_type  ::"type_def \<Rightarrow> f "  where
  "name_of_type (AF_typedef f _ ) = f"
| "name_of_type (AF_typedef_poly f _ _) = f"
       apply(auto,simp add: eqvt_def name_of_type_graph_aux_def )
  using type_def.exhaust by blast
nominal_termination (eqvt)  by lexicographic_order

nominal_function name_of_fun  ::"fun_def \<Rightarrow> f "  where
  "name_of_fun  (AF_fundef f ft) = f"
     apply(auto,simp add: eqvt_def name_of_fun_graph_aux_def )
  using fun_def.exhaust by blast
nominal_termination (eqvt)  by lexicographic_order

nominal_function remove2 :: "'a::pt \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove2 x [] = []" |
  "remove2 x (y # xs) = (if x = y then xs else y # remove2 x xs)"
  by (simp add: eqvt_def remove2_graph_aux_def,auto+,meson list.exhaust)
nominal_termination (eqvt)  by lexicographic_order

nominal_function base_for_lit :: "l \<Rightarrow> b" where
  "base_for_lit (L_true) = B_bool "
| "base_for_lit (L_false) = B_bool "
| "base_for_lit (L_num n) = B_int "
| "base_for_lit (L_unit) = B_unit " 
| "base_for_lit (L_bitvec v) = B_bitvec"
                   apply (auto simp: eqvt_def base_for_lit_graph_aux_def )
  using l.strong_exhaust by blast
nominal_termination (eqvt) by lexicographic_order

lemma neq_DNil_conv: "(xs \<noteq> DNil) = (\<exists>y ys. xs = y #\<^sub>\<Delta> ys)"
  by (induct xs) auto

nominal_function setD :: "\<Delta> \<Rightarrow> (u*\<tau>) set" where
  "setD DNil = {}"
| "setD (DCons xbc G) = {xbc} \<union> (setD G)"
       apply (auto,simp add: eqvt_def setD_graph_aux_def )
  using neq_DNil_conv surj_pair by metis
nominal_termination (eqvt) by lexicographic_order

lemma eqvt_triple:
  fixes y::"'a::at" and ya::"'a::at" and xa::"'c::at" and va::"'d::fs" and s::s and sa::s and f::"s*'c*'d \<Rightarrow> s"
  assumes "atom y \<sharp> (xa, va)" and "atom ya \<sharp> (xa, va)" and 
    "\<forall>c. atom c \<sharp> (s, sa) \<longrightarrow> atom c \<sharp> (y, ya, s, sa) \<longrightarrow> (y \<leftrightarrow> c) \<bullet> s = (ya \<leftrightarrow> c) \<bullet> sa"
    and "eqvt_at f (s,xa,va)" and "eqvt_at f (sa,xa,va)" and
    "atom c \<sharp> (s, va, xa, sa)" and "atom c \<sharp> (y, ya, f (s, xa, va), f (sa, xa, va))"
  shows "(y \<leftrightarrow> c) \<bullet> f (s, xa, va) =  (ya \<leftrightarrow> c) \<bullet> f (sa, xa, va)"
proof -
  have " (y \<leftrightarrow> c) \<bullet> f (s, xa, va) = f ( (y \<leftrightarrow> c) \<bullet> (s,xa,va))" using assms eqvt_at_def by metis
  also have "... = f ( (y \<leftrightarrow> c) \<bullet> s, (y \<leftrightarrow> c) \<bullet> xa ,(y \<leftrightarrow> c) \<bullet> va)" by auto
  also have "... = f ( (ya \<leftrightarrow> c) \<bullet> sa, (ya \<leftrightarrow> c) \<bullet> xa ,(ya \<leftrightarrow> c) \<bullet> va)" proof - 
    have " (y \<leftrightarrow> c) \<bullet> s = (ya \<leftrightarrow> c) \<bullet> sa" using assms Abs1_eq_iff_all by auto
    moreover have  "((y \<leftrightarrow> c) \<bullet> xa) =  ((ya \<leftrightarrow> c) \<bullet> xa)" using assms flip_fresh_fresh fresh_prodN by metis
    moreover have  "((y \<leftrightarrow> c) \<bullet> va) =  ((ya \<leftrightarrow> c) \<bullet> va)" using assms flip_fresh_fresh fresh_prodN by metis
    ultimately show ?thesis by auto
  qed
  also have "... =  f ( (ya \<leftrightarrow> c) \<bullet> (sa,xa,va))" by auto
  finally show ?thesis using assms eqvt_at_def by metis
qed

section \<open>Functions for bit list/vectors\<close>

inductive split :: "int \<Rightarrow> bit list \<Rightarrow> bit list * bit list \<Rightarrow> bool" where
  "split 0 xs ([], xs)"
| "split m xs (ys,zs) \<Longrightarrow> split (m+1) (x#xs) ((x # ys), zs)"
equivariance split
nominal_inductive split .

lemma split_concat:
  assumes "split n v (v1,v2)"
  shows "v = append v1 v2"
  using assms proof(induct "(v1,v2)" arbitrary: v1 v2 rule: split.inducts)
  case 1
  then show ?case by auto
next
  case (2 m xs ys zs x)
  then show ?case by auto
qed

lemma split_n:
  assumes "split n v (v1,v2)"
  shows "0 \<le> n \<and> n \<le> int (length v)"
  using assms proof(induct rule: split.inducts)
  case (1 xs)
  then show ?case by auto
next
  case (2 m xs ys zs x)
  then show ?case by auto
qed

lemma split_length:
  assumes "split n v (v1,v2)"
  shows "n = int (length v1)"
  using assms proof(induct  "(v1,v2)" arbitrary: v1 v2 rule: split.inducts)
  case (1 xs)
  then show ?case by auto
next
  case (2 m xs ys zs x)
  then show ?case by auto
qed

lemma obtain_split:
  assumes "0 \<le> n" and "n \<le> int (length bv)" 
  shows "\<exists> bv1 bv2. split n bv (bv1 , bv2)" 
  using assms proof(induct bv arbitrary: n)
  case Nil
  then show ?case using split.intros by auto
next
  case (Cons b bv)
  show ?case proof(cases "n = 0")
    case True
    then show ?thesis using split.intros by auto
  next
    case False
    then obtain m where m:"n=m+1" using Cons 
      by (metis add.commute add_minus_cancel)
    moreover have "0 \<le> m" using False m Cons by linarith
    then obtain bv1 and bv2 where "split m bv (bv1 , bv2)" using Cons m by force
    hence "split n (b # bv) ((b#bv1), bv2)" using m split.intros by auto
    then show ?thesis by auto
  qed
qed

end