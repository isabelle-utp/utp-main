(*<*)
theory IVSubst
  imports  Syntax
begin
  (*>*)

chapter \<open>Immutable Variable Substitution\<close>

text \<open>Substitution involving immutable variables. We define a class and instances for all
of the term forms\<close>

section \<open>Class\<close>

class has_subst_v = fs +
  fixes subst_v :: "'a::fs \<Rightarrow> x \<Rightarrow> v \<Rightarrow> 'a::fs"   ("_[_::=_]\<^sub>v" [1000,50,50] 1000)
  assumes fresh_subst_v_if:  "y \<sharp> (subst_v a x v)  \<longleftrightarrow> (atom x \<sharp> a \<and> y \<sharp> a) \<or> (y \<sharp> v \<and> (y \<sharp> a \<or> y = atom x))" 
    and    forget_subst_v[simp]:  "atom x \<sharp> a \<Longrightarrow> subst_v a  x v = a"
    and    subst_v_id[simp]:      "subst_v a x (V_var x) = a"
    and    eqvt[simp,eqvt]:       "(p::perm) \<bullet> (subst_v a x v) = (subst_v  (p \<bullet> a) (p \<bullet>x) (p \<bullet>v))"
    and    flip_subst_v[simp]:    "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c[z::=[x]\<^sup>v]\<^sub>v"
    and    subst_v_simple_commute[simp]: "atom x \<sharp> c \<Longrightarrow>(c[z::=[x]\<^sup>v]\<^sub>v)[x::=b]\<^sub>v = c[z::=b]\<^sub>v" 
begin

lemma subst_v_flip_eq_one:
  fixes z1::x and z2::x and x1::x and x2::x  
  assumes "[[atom z1]]lst. c1 = [[atom z2]]lst. c2" 
    and "atom x1 \<sharp> (z1,z2,c1,c2)"
  shows "(c1[z1::=[x1]\<^sup>v]\<^sub>v) = (c2[z2::=[x1]\<^sup>v]\<^sub>v)"
proof -  
  have "(c1[z1::=[x1]\<^sup>v]\<^sub>v) = (x1 \<leftrightarrow> z1) \<bullet> c1" using assms flip_subst_v by auto
  moreover have  "(c2[z2::=[x1]\<^sup>v]\<^sub>v) = (x1 \<leftrightarrow> z2) \<bullet> c2" using assms flip_subst_v by auto
  ultimately show ?thesis using Abs1_eq_iff_all(3)[of z1 c1 z2 c2 z1]  assms 
    by (metis Abs1_eq_iff_fresh(3) flip_commute)
qed

lemma subst_v_flip_eq_two:
  fixes z1::x and z2::x and x1::x and x2::x 
  assumes "[[atom z1]]lst. c1 = [[atom z2]]lst. c2" 
  shows "(c1[z1::=b]\<^sub>v) = (c2[z2::=b]\<^sub>v)"
proof -
  obtain x::x where *:"atom x \<sharp> (z1,z2,c1,c2)" using obtain_fresh by metis
  hence "(c1[z1::=[x]\<^sup>v]\<^sub>v) = (c2[z2::=[x]\<^sup>v]\<^sub>v)" using subst_v_flip_eq_one[OF assms, of x] by metis
  hence "(c1[z1::=[x]\<^sup>v]\<^sub>v)[x::=b]\<^sub>v = (c2[z2::=[x]\<^sup>v]\<^sub>v)[x::=b]\<^sub>v" by auto
  thus ?thesis using subst_v_simple_commute * fresh_prod4 by metis
qed

lemma subst_v_flip_eq_three:
  assumes "[[atom z1]]lst. c1 = [[atom z1']]lst. c1'"  and "atom x \<sharp> c1" and "atom x' \<sharp> (x,z1,z1', c1, c1')"
  shows   "(x \<leftrightarrow> x') \<bullet> (c1[z1::=[x]\<^sup>v]\<^sub>v) =  c1'[z1'::=[x']\<^sup>v]\<^sub>v" 
proof -
  have "atom x' \<sharp> c1[z1::=[x]\<^sup>v]\<^sub>v" using assms fresh_subst_v_if by simp
  hence "(x \<leftrightarrow> x') \<bullet> (c1[z1::=[x]\<^sup>v]\<^sub>v) = c1[z1::=[x]\<^sup>v]\<^sub>v[x::=[x']\<^sup>v]\<^sub>v" using flip_subst_v[of x' "c1[z1::=[x]\<^sup>v]\<^sub>v" x] flip_commute by metis
  also have "... = c1[z1::=[x']\<^sup>v]\<^sub>v" using subst_v_simple_commute fresh_prod4 assms by auto
  also have "... = c1'[z1'::=[x']\<^sup>v]\<^sub>v" using subst_v_flip_eq_one[of z1 c1 z1' c1' x'] using  assms by auto
  finally show ?thesis by auto
qed

end

section \<open>Values\<close>

nominal_function 
  subst_vv :: "v \<Rightarrow> x \<Rightarrow> v \<Rightarrow> v" where
  "subst_vv (V_lit l) x v = V_lit l"
| "subst_vv (V_var y) x v = (if x = y then v else V_var y)"
| "subst_vv (V_cons tyid c v') x v  = V_cons tyid c (subst_vv v' x v)"
| "subst_vv (V_consp tyid c b v') x v  = V_consp tyid c b (subst_vv v' x v)"
| "subst_vv (V_pair v1 v2) x v = V_pair (subst_vv v1 x v ) (subst_vv v2 x v )"
  by(auto simp: eqvt_def subst_vv_graph_aux_def, metis v.strong_exhaust)
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_vv_abbrev :: "v \<Rightarrow> x \<Rightarrow> v \<Rightarrow> v" ("_[_::=_]\<^sub>v\<^sub>v" [1000,50,50] 1000)
  where 
    "v[x::=v']\<^sub>v\<^sub>v  \<equiv> subst_vv v x v'" 

lemma fresh_subst_vv_if [simp]:
  "j \<sharp> t[i::=x]\<^sub>v\<^sub>v  = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"
  using supp_l_empty apply (induct t rule: v.induct,auto simp add: subst_vv.simps fresh_def, auto)
  by (simp add: supp_at_base |metis b.supp supp_b_empty  )+

lemma forget_subst_vv [simp]: "atom a \<sharp> tm \<Longrightarrow> tm[a::=x]\<^sub>v\<^sub>v = tm"
  by (induct tm rule: v.induct) (simp_all add: fresh_at_base)

lemma subst_vv_id [simp]: "tm[a::=V_var a]\<^sub>v\<^sub>v  = tm"
  by (induct tm rule: v.induct) simp_all

lemma subst_vv_commute [simp]:
  "atom j \<sharp> tm \<Longrightarrow> tm[i::=t]\<^sub>v\<^sub>v[j::=u]\<^sub>v\<^sub>v = tm[i::=t[j::=u]\<^sub>v\<^sub>v]\<^sub>v\<^sub>v "
  by (induct tm rule: v.induct) (auto simp: fresh_Pair)

lemma subst_vv_commute_full [simp]:
  "atom j \<sharp> t \<Longrightarrow> atom i \<sharp> u \<Longrightarrow> i \<noteq> j \<Longrightarrow> tm[i::=t]\<^sub>v\<^sub>v[j::=u]\<^sub>v\<^sub>v = tm[j::=u]\<^sub>v\<^sub>v[i::=t]\<^sub>v\<^sub>v"
  by (induct tm rule: v.induct) auto

lemma subst_vv_var_flip[simp]:
  fixes v::v
  assumes "atom y \<sharp> v"
  shows "(y \<leftrightarrow> x) \<bullet> v = v [x::=V_var y]\<^sub>v\<^sub>v"
  using assms apply(induct v rule:v.induct)
      apply auto
  using  l.fresh l.perm_simps l.strong_exhaust supp_l_empty permute_pure permute_list.simps fresh_def flip_fresh_fresh apply fastforce
  using permute_pure apply blast+
  done

instantiation v :: has_subst_v
begin

definition 
  "subst_v = subst_vv"

instance proof
  fix j::atom and i::x and  x::v and t::v
  show  "(j \<sharp> subst_v t i x) = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"
    using fresh_subst_vv_if[of j t i x] subst_v_v_def by metis

  fix a::x and tm::v and x::v
  show "atom a \<sharp> tm \<Longrightarrow> subst_v tm a x  = tm"
    using forget_subst_vv subst_v_v_def by simp

  fix a::x and tm::v
  show "subst_v tm a (V_var a) = tm" using subst_vv_id  subst_v_v_def by simp

  fix p::perm and x1::x and v::v and t1::v
  show "p \<bullet> subst_v t1 x1 v  = subst_v  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    using   subst_v_v_def by simp

  fix x::x and c::v and z::x
  show "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c[z::=[x]\<^sup>v]\<^sub>v"
    using  subst_v_v_def by simp

  fix x::x and c::v and z::x
  show  "atom x \<sharp> c \<Longrightarrow> c[z::=[x]\<^sup>v]\<^sub>v[x::=v]\<^sub>v = c[z::=v]\<^sub>v"
    using  subst_v_v_def by simp
qed

end

section \<open>Expressions\<close>

nominal_function subst_ev :: "e \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> e" where
  "subst_ev  ( (AE_val v') ) x v = ( (AE_val (subst_vv v' x v)) )"
| "subst_ev  ( (AE_app f v') ) x v  = ( (AE_app f (subst_vv v' x v )) )"                
| "subst_ev  ( (AE_appP f b v') ) x v = ( (AE_appP f b (subst_vv v' x v )) )"   
| "subst_ev  ( (AE_op opp v1 v2) ) x v  = ( (AE_op opp (subst_vv v1 x v ) (subst_vv v2 x v )) )"
| "subst_ev  [#1 v']\<^sup>e x v = [#1 (subst_vv v' x v )]\<^sup>e"
| "subst_ev  [#2 v']\<^sup>e x v = [#2 (subst_vv v' x v )]\<^sup>e"
| "subst_ev  ( (AE_mvar u)) x v = AE_mvar u"
| "subst_ev  [| v' |]\<^sup>e x v = [| (subst_vv  v' x v ) |]\<^sup>e"
| "subst_ev  ( AE_concat v1 v2) x v = AE_concat (subst_vv v1 x v ) (subst_vv v2 x v )"
| "subst_ev  ( AE_split v1 v2) x v = AE_split (subst_vv v1 x v ) (subst_vv v2 x v )"
  by(simp add: eqvt_def subst_ev_graph_aux_def,auto)(meson e.strong_exhaust)

nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_ev_abbrev :: "e \<Rightarrow> x \<Rightarrow> v \<Rightarrow> e" ("_[_::=_]\<^sub>e\<^sub>v" [1000,50,50] 500)
  where 
    "e[x::=v']\<^sub>e\<^sub>v  \<equiv> subst_ev e x v' " 

lemma size_subst_ev [simp]: "size ( subst_ev A i x) = size A"
  apply (nominal_induct A avoiding: i x rule: e.strong_induct) 
  by auto

lemma forget_subst_ev [simp]: "atom a \<sharp> A \<Longrightarrow> subst_ev A a x  = A"
  apply (nominal_induct A avoiding: a x rule: e.strong_induct) 
  by (auto simp: fresh_at_base)

lemma subst_ev_id [simp]: "subst_ev A a (V_var a)  = A"
  by (nominal_induct A avoiding: a rule: e.strong_induct) (auto simp: fresh_at_base)

lemma fresh_subst_ev_if [simp]:
  "j \<sharp> (subst_ev A i x ) = ((atom i \<sharp> A \<and> j \<sharp> A) \<or> (j \<sharp> x \<and> (j \<sharp> A \<or> j = atom i)))"
  apply (induct A rule: e.induct)
  unfolding subst_ev.simps fresh_subst_vv_if apply auto+
  using pure_fresh fresh_opp_all apply metis+
  done

lemma subst_ev_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (A[i::=t]\<^sub>e\<^sub>v)[j::=u]\<^sub>e\<^sub>v = A[i::=t[j::=u]\<^sub>v\<^sub>v]\<^sub>e\<^sub>v"
  by (nominal_induct A avoiding: i j t u rule: e.strong_induct) (auto simp: fresh_at_base)

lemma subst_ev_var_flip[simp]:
  fixes e::e and y::x and x::x
  assumes "atom y \<sharp> e"
  shows "(y \<leftrightarrow> x) \<bullet> e = e [x::=V_var y]\<^sub>e\<^sub>v"
  using assms apply(nominal_induct e rule:e.strong_induct)
           apply (simp add: subst_v_v_def)  
          apply (metis (mono_tags, lifting) b.eq_iff b.perm_simps e.fresh e.perm_simps flip_b_id subst_ev.simps subst_vv_var_flip)
         apply (metis (mono_tags, lifting) b.eq_iff b.perm_simps e.fresh e.perm_simps flip_b_id subst_ev.simps subst_vv_var_flip)
  subgoal for x
    apply (rule_tac y=x in  opp.strong_exhaust)
    using  subst_vv_var_flip flip_def by (simp add: flip_def permute_pure)+
  using  subst_vv_var_flip flip_def by (simp add: flip_def permute_pure)+

lemma subst_ev_flip:
  fixes e::e and ea::e and c::x
  assumes "atom c \<sharp> (e, ea)" and "atom c \<sharp> (x, xa, e, ea)" and "(x \<leftrightarrow> c) \<bullet> e = (xa \<leftrightarrow> c) \<bullet> ea" 
  shows "e[x::=v']\<^sub>e\<^sub>v = ea[xa::=v']\<^sub>e\<^sub>v"
proof -
  have "e[x::=v']\<^sub>e\<^sub>v = (e[x::=V_var c]\<^sub>e\<^sub>v)[c::=v']\<^sub>e\<^sub>v" using subst_ev_commute assms by simp
  also have "...  = ((c \<leftrightarrow> x) \<bullet> e)[c::=v']\<^sub>e\<^sub>v" using subst_ev_var_flip assms by simp
  also have "... = ((c \<leftrightarrow> xa) \<bullet> ea)[c::=v']\<^sub>e\<^sub>v" using assms flip_commute by metis
  also have "... = ea[xa::=v']\<^sub>e\<^sub>v"  using subst_ev_var_flip assms  by simp
  finally show ?thesis by auto
qed

lemma subst_ev_var[simp]:
  "(AE_val (V_var x))[x::=[z]\<^sup>v]\<^sub>e\<^sub>v = AE_val (V_var z)"
  by auto

instantiation e :: has_subst_v
begin

definition 
  "subst_v = subst_ev"

instance proof
  fix j::atom and i::x and  x::v and t::e
  show  "(j \<sharp> subst_v t i x) = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"
    using fresh_subst_ev_if[of j t i x] subst_v_e_def by metis

  fix a::x and tm::e and x::v
  show "atom a \<sharp> tm \<Longrightarrow> subst_v tm a x  = tm"
    using forget_subst_ev subst_v_e_def by simp

  fix a::x and tm::e
  show "subst_v tm a (V_var a) = tm" using subst_ev_id  subst_v_e_def by simp

  fix p::perm and x1::x and v::v and t1::e
  show "p \<bullet> subst_v t1 x1 v  = subst_v  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    using subst_ev_commute  subst_v_e_def by simp

  fix x::x and c::e and z::x
  show "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c[z::=[x]\<^sup>v]\<^sub>v"
    using  subst_v_e_def by simp

  fix x::x and c::e and z::x
  show  "atom x \<sharp> c \<Longrightarrow> c[z::=[x]\<^sup>v]\<^sub>v[x::=v]\<^sub>v = c[z::=v]\<^sub>v"
    using  subst_v_e_def by simp
qed
end

lemma subst_ev_commute_full:
  fixes e::e and w::v and v::v
  assumes "atom z \<sharp> v" and "atom x \<sharp> w" and "x \<noteq> z"
  shows "subst_ev  (e[z::=w]\<^sub>e\<^sub>v) x v = subst_ev  (e[x::=v]\<^sub>e\<^sub>v) z w" 
  using assms by(nominal_induct e rule: e.strong_induct,simp+)

lemma subst_ev_v_flip1[simp]:
  fixes e::e
  assumes "atom z1 \<sharp> (z,e)" and "atom z1' \<sharp> (z,e)"
  shows"(z1 \<leftrightarrow> z1') \<bullet> e[z::=v]\<^sub>e\<^sub>v =  e[z::= ((z1 \<leftrightarrow> z1') \<bullet> v)]\<^sub>e\<^sub>v"
  using assms proof(nominal_induct e rule:e.strong_induct)
qed  (simp add: flip_def fresh_Pair swap_fresh_fresh)+

section \<open>Expressions in Constraints\<close>

nominal_function subst_cev :: "ce \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> ce" where
  "subst_cev ( (CE_val v') ) x v = ( (CE_val (subst_vv  v' x v )) )" 
| "subst_cev ( (CE_op opp v1 v2) ) x v = ( (CE_op opp (subst_cev  v1 x v ) (subst_cev v2 x v )) )"
| "subst_cev ( (CE_fst v')) x v = CE_fst (subst_cev  v' x v )"
| "subst_cev ( (CE_snd v')) x v = CE_snd (subst_cev  v' x v )"
| "subst_cev ( (CE_len v')) x v = CE_len (subst_cev  v' x v )"
| "subst_cev ( CE_concat v1 v2) x v = CE_concat (subst_cev v1 x v ) (subst_cev v2 x v )"
                      apply (simp add: eqvt_def subst_cev_graph_aux_def,auto)
  by (meson ce.strong_exhaust)

nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_cev_abbrev :: "ce \<Rightarrow> x \<Rightarrow> v \<Rightarrow> ce" ("_[_::=_]\<^sub>c\<^sub>e\<^sub>v" [1000,50,50] 500)
  where 
    "e[x::=v']\<^sub>c\<^sub>e\<^sub>v  \<equiv> subst_cev  e x v'" 

lemma size_subst_cev [simp]: "size ( subst_cev A i x ) = size A"
  by (nominal_induct A avoiding: i x rule: ce.strong_induct,auto) 

lemma forget_subst_cev [simp]: "atom a \<sharp> A \<Longrightarrow> subst_cev A a x  = A"
  by (nominal_induct A avoiding: a x rule: ce.strong_induct, auto simp: fresh_at_base)

lemma subst_cev_id [simp]: "subst_cev A a (V_var a)  = A"
  by (nominal_induct A avoiding: a rule: ce.strong_induct) (auto simp: fresh_at_base)

lemma fresh_subst_cev_if [simp]:
  "j \<sharp> (subst_cev A i x ) = ((atom i \<sharp> A \<and> j \<sharp> A) \<or> (j \<sharp> x \<and> (j \<sharp> A \<or> j = atom i)))"
proof(nominal_induct A avoiding: i x rule: ce.strong_induct)
  case (CE_op opp v1 v2)
  then show ?case  using fresh_subst_vv_if subst_ev.simps e.supp pure_fresh opp.fresh 
      fresh_e_opp 
    using fresh_opp_all by auto
qed(auto)+

lemma subst_cev_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (subst_cev (subst_cev A i t ) j u) = subst_cev A i (subst_vv t j u )"
  by (nominal_induct A avoiding: i j t u rule: ce.strong_induct) (auto simp: fresh_at_base)

lemma subst_cev_var_flip[simp]:
  fixes e::ce and y::x and x::x
  assumes "atom y \<sharp> e"
  shows "(y \<leftrightarrow> x) \<bullet> e = e [x::=V_var y]\<^sub>c\<^sub>e\<^sub>v"
  using assms proof(nominal_induct e rule:ce.strong_induct)
  case (CE_val v)
  then show ?case using subst_vv_var_flip by auto
next
  case (CE_op opp v1 v2)
  hence yf: "atom y \<sharp> v1 \<and> atom y \<sharp> v2" using ce.fresh by blast
  have " (y \<leftrightarrow> x) \<bullet> (CE_op opp v1 v2 ) = CE_op ((y \<leftrightarrow> x) \<bullet> opp) ( (y \<leftrightarrow> x) \<bullet> v1 ) ( (y \<leftrightarrow> x) \<bullet> v2)" 
    using opp.perm_simps ce.perm_simps permute_pure ce.fresh opp.strong_exhaust by presburger
  also have "... = CE_op ((y \<leftrightarrow> x) \<bullet> opp) (v1[x::=V_var y]\<^sub>c\<^sub>e\<^sub>v) (v2 [x::=V_var y]\<^sub>c\<^sub>e\<^sub>v)" using yf 
    by (simp add: CE_op.hyps(1) CE_op.hyps(2))
  finally show ?case using subst_cev.simps  opp.perm_simps  opp.strong_exhaust 
    by (metis (full_types))
qed( (auto simp add: permute_pure subst_vv_var_flip)+)

lemma subst_cev_flip:
  fixes e::ce and ea::ce and c::x
  assumes "atom c \<sharp> (e, ea)" and "atom c \<sharp> (x, xa, e, ea)" and "(x \<leftrightarrow> c) \<bullet> e = (xa \<leftrightarrow> c) \<bullet> ea" 
  shows "e[x::=v']\<^sub>c\<^sub>e\<^sub>v = ea[xa::=v']\<^sub>c\<^sub>e\<^sub>v"
proof -
  have "e[x::=v']\<^sub>c\<^sub>e\<^sub>v = (e[x::=V_var c]\<^sub>c\<^sub>e\<^sub>v)[c::=v']\<^sub>c\<^sub>e\<^sub>v" using subst_ev_commute assms by simp
  also have "...  = ((c \<leftrightarrow> x) \<bullet> e)[c::=v']\<^sub>c\<^sub>e\<^sub>v" using subst_ev_var_flip assms by simp
  also have "... = ((c \<leftrightarrow> xa) \<bullet> ea)[c::=v']\<^sub>c\<^sub>e\<^sub>v" using assms flip_commute by metis
  also have "... = ea[xa::=v']\<^sub>c\<^sub>e\<^sub>v"  using subst_ev_var_flip assms  by simp
  finally show ?thesis by auto
qed

lemma subst_cev_var[simp]:
  fixes z::x and x::x
  shows  "[[x]\<^sup>v]\<^sup>c\<^sup>e [x::=[z]\<^sup>v]\<^sub>c\<^sub>e\<^sub>v = [[z]\<^sup>v]\<^sup>c\<^sup>e"
  by auto

instantiation ce :: has_subst_v
begin

definition 
  "subst_v = subst_cev"

instance proof
  fix j::atom and i::x and  x::v and t::ce
  show  "(j \<sharp> subst_v t i x) = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"
    using fresh_subst_cev_if[of j t i x] subst_v_ce_def by metis

  fix a::x and tm::ce and x::v
  show "atom a \<sharp> tm \<Longrightarrow> subst_v tm a x  = tm"
    using forget_subst_cev subst_v_ce_def by simp

  fix a::x and tm::ce
  show "subst_v tm a (V_var a) = tm" using subst_cev_id  subst_v_ce_def by simp

  fix p::perm and x1::x and v::v and t1::ce
  show "p \<bullet> subst_v t1 x1 v  = subst_v  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    using subst_cev_commute  subst_v_ce_def by simp

  fix x::x and c::ce and z::x 
  show "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c [z::=V_var x]\<^sub>v"
    using  subst_v_ce_def by simp

  fix x::x and c::ce and z::x
  show  "atom x \<sharp> c \<Longrightarrow> c [z::=V_var x]\<^sub>v[x::=v]\<^sub>v = c[z::=v]\<^sub>v"
    using  subst_v_ce_def by simp
qed

end

lemma subst_cev_commute_full:
  fixes e::ce and w::v and v::v
  assumes "atom z \<sharp> v" and "atom x \<sharp> w" and "x \<noteq> z"
  shows "subst_cev (e[z::=w]\<^sub>c\<^sub>e\<^sub>v) x v  = subst_cev (e[x::=v]\<^sub>c\<^sub>e\<^sub>v) z w " 
  using assms by(nominal_induct e rule: ce.strong_induct,simp+)


lemma subst_cev_v_flip1[simp]:
  fixes e::ce
  assumes "atom z1 \<sharp> (z,e)" and "atom z1' \<sharp> (z,e)"
  shows"(z1 \<leftrightarrow> z1') \<bullet> e[z::=v]\<^sub>c\<^sub>e\<^sub>v =  e[z::= ((z1 \<leftrightarrow> z1') \<bullet> v)]\<^sub>c\<^sub>e\<^sub>v"
  using assms apply(nominal_induct e rule:ce.strong_induct)
  by (simp add: flip_def fresh_Pair swap_fresh_fresh)+

section \<open>Constraints\<close>

nominal_function subst_cv :: "c \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> c" where
  "subst_cv (C_true) x v = C_true"
|  "subst_cv (C_false) x v = C_false"
|  "subst_cv (C_conj c1 c2) x v = C_conj (subst_cv c1 x v ) (subst_cv c2 x v )"
|  "subst_cv (C_disj c1 c2) x v = C_disj (subst_cv c1 x v ) (subst_cv c2 x v )"
|  "subst_cv (C_imp c1 c2) x v = C_imp (subst_cv c1 x v ) (subst_cv c2 x v )"
|  "subst_cv (e1 == e2) x v = ((subst_cev e1 x v ) == (subst_cev e2 x v ))"
|  "subst_cv (C_not c) x v = C_not (subst_cv c x v )"
                      apply (simp add: eqvt_def subst_cv_graph_aux_def,auto)
  using c.strong_exhaust by metis
nominal_termination (eqvt)  by lexicographic_order

abbreviation 
  subst_cv_abbrev :: "c \<Rightarrow> x \<Rightarrow> v \<Rightarrow> c" ("_[_::=_]\<^sub>c\<^sub>v" [1000,50,50] 1000)
  where 
    "c[x::=v']\<^sub>c\<^sub>v  \<equiv> subst_cv c x v'" 

lemma size_subst_cv [simp]: "size ( subst_cv A i x ) = size A"
  by (nominal_induct A avoiding: i x rule: c.strong_induct,auto) 

lemma forget_subst_cv [simp]: "atom a \<sharp> A \<Longrightarrow> subst_cv A a x  = A"
  by (nominal_induct A avoiding: a x rule: c.strong_induct, auto simp: fresh_at_base)

lemma subst_cv_id [simp]: "subst_cv A a (V_var a)  = A"
  by (nominal_induct A avoiding: a rule: c.strong_induct) (auto simp: fresh_at_base)

lemma fresh_subst_cv_if [simp]:
  "j \<sharp> (subst_cv A i x ) \<longleftrightarrow> (atom i \<sharp> A \<and> j \<sharp> A) \<or> (j \<sharp> x \<and> (j \<sharp> A \<or> j = atom i))"
  by (nominal_induct A avoiding: i x rule: c.strong_induct, (auto simp add: pure_fresh)+)

lemma subst_cv_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (subst_cv (subst_cv A i t ) j u ) = subst_cv A i (subst_vv t j u )"
  by (nominal_induct A avoiding: i j t u rule: c.strong_induct) (auto simp: fresh_at_base)

lemma let_s_size [simp]: "size s \<le> size (AS_let x e s)"
  apply (nominal_induct s avoiding: e x rule: s_branch_s_branch_list.strong_induct(1)) 
              apply auto
  done

lemma subst_cv_var_flip[simp]:
  fixes c::c
  assumes "atom y \<sharp> c"
  shows "(y \<leftrightarrow> x) \<bullet> c = c[x::=V_var y]\<^sub>c\<^sub>v"
  using assms by(nominal_induct c rule:c.strong_induct,(simp add: flip_subst_v subst_v_ce_def)+)

instantiation c :: has_subst_v
begin

definition 
  "subst_v = subst_cv"

instance proof
  fix j::atom and i::x and  x::v and t::c
  show  "(j \<sharp> subst_v t i x) = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"
    using fresh_subst_cv_if[of j t i x] subst_v_c_def by metis

  fix a::x and tm::c and x::v
  show "atom a \<sharp> tm \<Longrightarrow> subst_v tm a x  = tm"
    using forget_subst_cv subst_v_c_def by simp

  fix a::x and tm::c
  show "subst_v tm a (V_var a) = tm" using subst_cv_id  subst_v_c_def by simp

  fix p::perm and x1::x and v::v and t1::c
  show "p \<bullet> subst_v t1 x1 v  = subst_v  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    using subst_cv_commute  subst_v_c_def by simp

  fix x::x and c::c and z::x
  show "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c[z::=[x]\<^sup>v]\<^sub>v"
    using subst_cv_var_flip subst_v_c_def by simp

  fix x::x and c::c and z::x
  show  "atom x \<sharp> c \<Longrightarrow> c[z::=[x]\<^sup>v]\<^sub>v[x::=v]\<^sub>v = c[z::=v]\<^sub>v"
    using subst_cv_var_flip subst_v_c_def by simp
qed

end

lemma subst_cv_var_flip1[simp]:
  fixes c::c
  assumes "atom y \<sharp> c"
  shows "(x \<leftrightarrow> y) \<bullet> c = c[x::=V_var y]\<^sub>c\<^sub>v"
  using subst_cv_var_flip flip_commute 
  by (metis assms)

lemma subst_cv_v_flip3[simp]:
  fixes c::c
  assumes "atom z1 \<sharp> c" and "atom z1' \<sharp> c"
  shows"(z1 \<leftrightarrow> z1') \<bullet> c[z::=[z1]\<^sup>v]\<^sub>c\<^sub>v =  c[z::=[z1']\<^sup>v]\<^sub>c\<^sub>v"
proof - 
  consider "z1' = z" | "z1 = z" | "atom z1 \<sharp> z \<and> atom z1' \<sharp> z" by force
  then show ?thesis proof(cases)
    case 1
    then show ?thesis using 1 assms by auto
  next
    case 2
    then show ?thesis using 2 assms by auto
  next
    case 3
    then show ?thesis using assms by auto
  qed
qed

lemma subst_cv_v_flip[simp]:
  fixes c::c
  assumes "atom x \<sharp> c"
  shows "((x \<leftrightarrow> z) \<bullet> c)[x::=v]\<^sub>c\<^sub>v = c [z::=v]\<^sub>c\<^sub>v"
  using assms subst_v_c_def by auto

lemma subst_cv_commute_full:
  fixes c::c
  assumes "atom z \<sharp> v" and "atom x \<sharp> w" and "x\<noteq>z"
  shows "(c[z::=w]\<^sub>c\<^sub>v)[x::=v]\<^sub>c\<^sub>v = (c[x::=v]\<^sub>c\<^sub>v)[z::=w]\<^sub>c\<^sub>v" 
  using assms proof(nominal_induct c rule: c.strong_induct)
  case (C_eq e1 e2)
  then show ?case using subst_cev_commute_full by simp
qed(force+)

lemma subst_cv_eq[simp]:
  assumes  "atom z1 \<sharp> e1" 
  shows "(CE_val (V_var z1)  ==  e1 )[z1::=[x]\<^sup>v]\<^sub>c\<^sub>v = (CE_val (V_var x)  ==  e1 )" (is "?A = ?B")
proof -
  have "?A = (((CE_val (V_var z1))[z1::=[x]\<^sup>v]\<^sub>c\<^sub>e\<^sub>v) == e1)" using subst_cv.simps assms by simp
  thus ?thesis by simp
qed

section \<open>Variable Context\<close>

text \<open>The idea of this substitution is to remove x from the context. We really want to add the condition 
that x is fresh in v but this causes problems with proofs.\<close>

nominal_function subst_gv :: "\<Gamma> \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> \<Gamma>" where
  "subst_gv GNil  x v = GNil"
| "subst_gv ((y,b,c) #\<^sub>\<Gamma> \<Gamma>) x v  = (if x = y then \<Gamma> else ((y,b,c[x::=v]\<^sub>c\<^sub>v)#\<^sub>\<Gamma> (subst_gv  \<Gamma> x v )))"
proof(goal_cases)
  case 1
  then show ?case  by(simp add: eqvt_def subst_gv_graph_aux_def )
next
  case (3 P x)
  then show ?case by (metis neq_GNil_conv prod_cases3)
qed(fast+)
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_gv_abbrev :: "\<Gamma> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<Gamma>" ("_[_::=_]\<^sub>\<Gamma>\<^sub>v" [1000,50,50] 1000)
  where 
    "g[x::=v]\<^sub>\<Gamma>\<^sub>v  \<equiv> subst_gv g x v" 

lemma size_subst_gv [simp]: "size ( subst_gv G i x ) \<le> size G"
  by (induct G,auto) 

lemma forget_subst_gv [simp]: "atom a \<sharp> G \<Longrightarrow> subst_gv G a x = G"
  apply (induct G ,auto) 
  using fresh_GCons fresh_PairD(1) not_self_fresh apply blast
   apply (simp add: fresh_GCons)+
  done

lemma fresh_subst_gv: "atom a \<sharp> G \<Longrightarrow> atom a \<sharp> v \<Longrightarrow> atom a \<sharp> subst_gv G x v"
proof(induct G)
  case GNil
  then show ?case by auto
next
  case (GCons xbc G)
  obtain x' and b' and c' where xbc: "xbc = (x',b',c')" using prod_cases3 by blast
  show ?case proof(cases "x=x'")
    case True
    have "atom a \<sharp> G" using GCons fresh_GCons by blast
    thus ?thesis using subst_gv.simps(2)[of  x' b' c' G] GCons xbc True by presburger
  next
    case False
    then show ?thesis using subst_gv.simps(2)[of  x' b' c' G] GCons xbc False fresh_GCons by simp
  qed
qed

lemma subst_gv_flip: 
  fixes x::x and xa::x and z::x and c::c and b::b and \<Gamma>::\<Gamma>
  assumes "atom xa \<sharp> ((x, b, c[z::=[x]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>)"  and "atom xa \<sharp> \<Gamma>" and "atom x \<sharp> \<Gamma>" and "atom x \<sharp> (z, c)" and "atom xa \<sharp> (z, c)"
  shows "(x \<leftrightarrow> xa) \<bullet>  ((x, b, c[z::=[x]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) = (xa, b, c[z::=V_var xa]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>"
proof -
  have  "(x \<leftrightarrow> xa) \<bullet>  ((x, b, c[z::=[x]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) =  (( (x \<leftrightarrow> xa) \<bullet>  x, b, (x \<leftrightarrow> xa) \<bullet>  c[z::=[x]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> ((x \<leftrightarrow> xa) \<bullet>  \<Gamma>))" 
    using subst Cons_eqvt flip_fresh_fresh using G_cons_flip by simp
  also have "... = ((xa, b, (x \<leftrightarrow> xa) \<bullet> c[z::=[x]\<^sup>v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> ((x \<leftrightarrow> xa) \<bullet>  \<Gamma>))" using assms by fastforce
  also have "... =  ((xa, b,  c[z::=V_var xa]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> ((x \<leftrightarrow> xa) \<bullet>  \<Gamma>))" using assms subst_cv_var_flip by fastforce
  also have "... =  ((xa, b,  c[z::=V_var xa]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> \<Gamma>)"  using assms flip_fresh_fresh by blast 
  finally show ?thesis by simp
qed

section \<open>Types\<close>

nominal_function subst_tv :: "\<tau> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<tau>" where
  "atom z \<sharp> (x,v) \<Longrightarrow> subst_tv  \<lbrace> z : b | c \<rbrace> x v  = \<lbrace> z : b | c[x::=v]\<^sub>c\<^sub>v \<rbrace>"
     apply (simp add: eqvt_def subst_tv_graph_aux_def )
    apply auto
  subgoal for P a aa b
    apply(rule_tac y=a and c="(aa,b)" in \<tau>.strong_exhaust)
    by (auto simp: eqvt_at_def fresh_star_def fresh_Pair fresh_at_base) 
  apply (auto simp: eqvt_at_def fresh_star_def fresh_Pair fresh_at_base)
proof -
  fix z :: x and c :: c and za :: x and xa :: x and va :: v and ca :: c and cb :: x
  assume a1: "atom za \<sharp> va"  and  a2: "atom z \<sharp> va" and a3: "\<forall>cb. atom cb \<sharp> c \<and> atom cb \<sharp> ca \<longrightarrow> cb \<noteq> z \<and> cb \<noteq> za \<longrightarrow> c[z::=V_var cb]\<^sub>c\<^sub>v = ca[za::=V_var cb]\<^sub>c\<^sub>v"
  assume a4: "atom cb \<sharp> c" and a5: "atom cb \<sharp> ca" and a6: "cb \<noteq> z" and a7: "cb \<noteq> za" and "atom cb \<sharp> va" and a8: "za \<noteq> xa" and a9: "z \<noteq> xa"
  assume a10:"cb \<noteq> xa"
  note assms = a10 a9 a8 a7 a6 a5 a4 a3 a2 a1 

  have "c[z::=V_var cb]\<^sub>c\<^sub>v = ca[za::=V_var cb]\<^sub>c\<^sub>v" using assms  by auto
  hence "c[z::=V_var cb]\<^sub>c\<^sub>v[xa::=va]\<^sub>c\<^sub>v = ca[za::=V_var cb]\<^sub>c\<^sub>v[xa::=va]\<^sub>c\<^sub>v" by simp
  moreover have "c[z::=V_var cb]\<^sub>c\<^sub>v[xa::=va]\<^sub>c\<^sub>v = c[xa::=va]\<^sub>c\<^sub>v[z::=V_var cb]\<^sub>c\<^sub>v" using   subst_cv_commute_full[of z va xa "V_var cb" ]  assms fresh_def v.supp by fastforce
  moreover  have "ca[za::=V_var cb]\<^sub>c\<^sub>v[xa::=va]\<^sub>c\<^sub>v = ca[xa::=va]\<^sub>c\<^sub>v[za::=V_var cb]\<^sub>c\<^sub>v" 
    using   subst_cv_commute_full[of za va xa "V_var cb" ]  assms fresh_def v.supp by fastforce

  ultimately show "c[xa::=va]\<^sub>c\<^sub>v[z::=V_var cb]\<^sub>c\<^sub>v = ca[xa::=va]\<^sub>c\<^sub>v[za::=V_var cb]\<^sub>c\<^sub>v" by simp
qed

nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_tv_abbrev :: "\<tau> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<tau>" ("_[_::=_]\<^sub>\<tau>\<^sub>v" [1000,50,50] 1000)
  where 
    "t[x::=v]\<^sub>\<tau>\<^sub>v  \<equiv> subst_tv t x v" 

lemma size_subst_tv [simp]: "size ( subst_tv A i x ) = size A"
proof (nominal_induct A avoiding: i x  rule: \<tau>.strong_induct)
  case (T_refined_type x' b' c')
  then show ?case by auto
qed

lemma forget_subst_tv [simp]: "atom a \<sharp> A \<Longrightarrow> subst_tv A a x  = A"
  apply (nominal_induct A avoiding: a x rule: \<tau>.strong_induct) 
  apply(auto simp: fresh_at_base)
  done

lemma subst_tv_id [simp]: "subst_tv A a (V_var a) = A"
  by (nominal_induct A avoiding: a rule: \<tau>.strong_induct) (auto simp: fresh_at_base)

lemma fresh_subst_tv_if [simp]:
  "j \<sharp> (subst_tv A i x ) \<longleftrightarrow> (atom i \<sharp> A \<and> j \<sharp> A) \<or> (j \<sharp> x \<and> (j \<sharp> A \<or> j = atom i))"
  apply (nominal_induct A avoiding: i x rule: \<tau>.strong_induct)
  using fresh_def supp_b_empty x_fresh_b by auto

lemma subst_tv_commute [simp]:
  "atom y \<sharp> \<tau> \<Longrightarrow> (\<tau>[x::= t]\<^sub>\<tau>\<^sub>v)[y::=v]\<^sub>\<tau>\<^sub>v = \<tau>[x::= t[y::=v]\<^sub>v\<^sub>v]\<^sub>\<tau>\<^sub>v "
  by (nominal_induct \<tau> avoiding: x y t v rule: \<tau>.strong_induct) (auto simp: fresh_at_base)

lemma subst_tv_var_flip [simp]:
  fixes x::x and xa::x and \<tau>::\<tau>
  assumes "atom xa \<sharp> \<tau>"
  shows "(x \<leftrightarrow> xa) \<bullet> \<tau> = \<tau>[x::=V_var xa]\<^sub>\<tau>\<^sub>v"
proof - 
  obtain z::x and b and c where zbc: "atom z \<sharp> (x,xa, V_var xa) \<and> \<tau> = \<lbrace> z : b | c \<rbrace>" 
    using obtain_fresh_z   by (metis prod.inject subst_tv.cases)
  hence "atom xa \<notin> supp c - { atom z }" using \<tau>.supp[of z b c] fresh_def supp_b_empty assms 
    by  auto
  moreover have "xa \<noteq> z" using zbc fresh_prod3 by force
  ultimately have xaf: "atom xa \<sharp> c" using fresh_def by auto
  have "(x \<leftrightarrow> xa) \<bullet> \<tau> = \<lbrace> z : b | (x \<leftrightarrow> xa) \<bullet> c \<rbrace>" 
    by (metis \<tau>.perm_simps empty_iff flip_at_base_simps(3) flip_fresh_fresh fresh_PairD(1) fresh_PairD(2) fresh_def not_self_fresh supp_b_empty v.fresh(2) zbc)
  also have "... =  \<lbrace> z : b | c[x::=V_var xa]\<^sub>c\<^sub>v \<rbrace>"  using subst_cv_v_flip xaf  
    by (metis permute_flip_cancel permute_flip_cancel2 subst_cv_var_flip)
  finally show ?thesis using subst_tv.simps zbc 
    using fresh_PairD(1) not_self_fresh by force
qed

instantiation \<tau> :: has_subst_v
begin

definition 
  "subst_v = subst_tv"

instance proof
  fix j::atom and i::x and  x::v and t::\<tau>
  show  "(j \<sharp> subst_v t i x) = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"

  proof(nominal_induct t avoiding: i x rule:\<tau>.strong_induct)
    case (T_refined_type z b c)
    hence " j \<sharp> \<lbrace> z : b  | c \<rbrace>[i::=x]\<^sub>v  =  j \<sharp> \<lbrace> z : b  | c[i::=x]\<^sub>c\<^sub>v \<rbrace>" using subst_tv.simps subst_v_\<tau>_def fresh_Pair by simp
    also have "...  = (atom i \<sharp> \<lbrace> z : b  | c \<rbrace> \<and> j \<sharp> \<lbrace> z : b  | c \<rbrace> \<or> j \<sharp> x \<and> (j \<sharp> \<lbrace> z : b  | c \<rbrace> \<or> j = atom i))" 
      unfolding \<tau>.fresh using subst_v_c_def fresh_subst_v_if 
      using T_refined_type.hyps(1) T_refined_type.hyps(2) x_fresh_b by auto
    finally show ?case by auto
  qed

  fix a::x and tm::\<tau> and x::v
  show "atom a \<sharp> tm \<Longrightarrow> subst_v tm a x  = tm"
    apply(nominal_induct tm avoiding: a x rule:\<tau>.strong_induct)
    using subst_v_c_def forget_subst_v subst_tv.simps subst_v_\<tau>_def fresh_Pair by simp

  fix a::x and tm::\<tau>
  show "subst_v tm a (V_var a) = tm"     
    apply(nominal_induct tm avoiding: a rule:\<tau>.strong_induct)
    using subst_v_c_def forget_subst_v subst_tv.simps subst_v_\<tau>_def fresh_Pair by simp

  fix p::perm and x1::x and v::v and t1::\<tau>
  show "p \<bullet> subst_v t1 x1 v  = subst_v  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    apply(nominal_induct tm avoiding: a x rule:\<tau>.strong_induct)
    using subst_v_c_def forget_subst_v subst_tv.simps subst_v_\<tau>_def fresh_Pair by simp

  fix x::x and c::\<tau> and z::x
  show "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c[z::=[x]\<^sup>v]\<^sub>v" 
    apply(nominal_induct c avoiding: z x rule:\<tau>.strong_induct)
    using subst_v_c_def flip_subst_v subst_tv.simps subst_v_\<tau>_def fresh_Pair by auto

  fix x::x and c::\<tau> and z::x
  show  "atom x \<sharp> c \<Longrightarrow> c[z::=[x]\<^sup>v]\<^sub>v[x::=v]\<^sub>v = c[z::=v]\<^sub>v"
    apply(nominal_induct c avoiding:  x v z rule:\<tau>.strong_induct)
    using subst_v_c_def  subst_tv.simps subst_v_\<tau>_def fresh_Pair 
    by (metis flip_commute subst_tv_commute subst_tv_var_flip subst_v_\<tau>_def subst_vv.simps(2))
qed

end

lemma subst_tv_commute_full:
  fixes c::\<tau>
  assumes "atom z \<sharp> v" and "atom x \<sharp> w" and "x\<noteq>z"
  shows "(c[z::=w]\<^sub>\<tau>\<^sub>v)[x::=v]\<^sub>\<tau>\<^sub>v = (c[x::=v]\<^sub>\<tau>\<^sub>v)[z::=w]\<^sub>\<tau>\<^sub>v" 
  using assms proof(nominal_induct c avoiding: x v z w rule: \<tau>.strong_induct)
  case (T_refined_type x1a x2a x3a)
  then show ?case using subst_cv_commute_full by simp
qed

lemma type_eq_subst_eq:
  fixes v::v and c1::c
  assumes "\<lbrace> z1 : b1  |  c1 \<rbrace> = \<lbrace> z2 : b2  |  c2 \<rbrace>"
  shows "c1[z1::=v]\<^sub>c\<^sub>v = c2[z2::=v]\<^sub>c\<^sub>v"
  using subst_v_flip_eq_two[of z1 c1 z2 c2 v] \<tau>.eq_iff assms subst_v_c_def by simp

text \<open>Extract constraint from a type. We cannot just project out the constraint as this would
mean alpha-equivalent types give different answers \<close>

nominal_function c_of :: "\<tau> \<Rightarrow> x \<Rightarrow> c" where
  "atom z \<sharp> x \<Longrightarrow> c_of (T_refined_type z b c) x = c[z::=[x]\<^sup>v]\<^sub>c\<^sub>v"
proof(goal_cases)
  case 1
  then show ?case using eqvt_def c_of_graph_aux_def by force
next
  case (2 x y)
  then show ?case using eqvt_def c_of_graph_aux_def by force
next
  case (3 P x)
  then obtain x1::\<tau> and x2::x where *:"x = (x1,x2)" by force
  obtain z' and b' and c' where "x1 = \<lbrace> z' : b' | c' \<rbrace> \<and> atom z' \<sharp> x2" using obtain_fresh_z by metis
  then show ?case  using 3 * by auto
next
  case (4 z1 x1 b1 c1 z2 x2 b2 c2)
  then show ?case using subst_v_flip_eq_two \<tau>.eq_iff   by (metis prod.inject type_eq_subst_eq)
qed

nominal_termination (eqvt) by lexicographic_order

lemma c_of_eq:
  shows  "c_of \<lbrace> x : b | c \<rbrace> x = c"
proof(nominal_induct "\<lbrace> x : b | c \<rbrace>" avoiding: x rule: \<tau>.strong_induct)
  case (T_refined_type x' c') 
  moreover hence "c_of \<lbrace> x' : b | c' \<rbrace> x = c'[x'::=V_var x]\<^sub>c\<^sub>v" using c_of.simps by auto
  moreover have "\<lbrace> x' : b  | c' \<rbrace> = \<lbrace> x : b  | c \<rbrace>" using T_refined_type  \<tau>.eq_iff by metis
  moreover have "c'[x'::=V_var x]\<^sub>c\<^sub>v = c" using  T_refined_type Abs1_eq_iff flip_subst_v subst_v_c_def 
    by (metis subst_cv_id)
  ultimately show ?case by auto
qed

lemma obtain_fresh_z_c_of:
  fixes t::"'b::fs"
  obtains z  where "atom z \<sharp> t \<and> \<tau> = \<lbrace> z : b_of \<tau> | c_of \<tau> z \<rbrace>"
proof - 
  obtain z and c where "atom z \<sharp> t \<and> \<tau> = \<lbrace> z : b_of \<tau> | c \<rbrace>" using obtain_fresh_z2 by metis
  moreover hence "c = c_of \<tau> z" using c_of.simps using c_of_eq by metis
  ultimately show ?thesis 
    using that by auto
qed

lemma c_of_fresh:
  fixes x::x
  assumes  "atom x \<sharp> (t,z)" 
  shows "atom x \<sharp> c_of t z" 
proof -
  obtain z' and c' where z:"t = \<lbrace> z' : b_of t | c' \<rbrace> \<and> atom z' \<sharp> (x,z)" using obtain_fresh_z_c_of by metis
  hence *:"c_of t z = c'[z'::=V_var z]\<^sub>c\<^sub>v" using c_of.simps fresh_Pair by metis
  have "(atom x \<sharp> c' \<or> atom x \<in> set [atom z']) \<and> atom x \<sharp> b_of t" using \<tau>.fresh assms z fresh_Pair by metis
  hence "atom x \<sharp> c'" using fresh_Pair z fresh_at_base(2) by fastforce
  moreover have "atom x \<sharp> V_var z" using assms fresh_Pair v.fresh by metis
  ultimately show ?thesis using assms fresh_subst_v_if[of "atom x" c' z' "V_var z"] subst_v_c_def * by metis
qed

lemma c_of_switch:
  fixes z::x
  assumes "atom z \<sharp> t" 
  shows "(c_of t z)[z::=V_var x]\<^sub>c\<^sub>v = c_of t x"
proof -  
  obtain z' and c' where z:"t = \<lbrace> z' : b_of t | c' \<rbrace> \<and> atom z' \<sharp> (x,z)" using obtain_fresh_z_c_of by metis
  hence "(atom z \<sharp> c' \<or> atom z \<in> set [atom z']) \<and> atom z \<sharp> b_of t" using \<tau>.fresh[of "atom z" z' "b_of t" c'] assms by metis
  moreover have " atom z \<notin> set [atom z']" using z fresh_Pair by force
  ultimately have  **:"atom z \<sharp> c'" using fresh_Pair z fresh_at_base(2) by metis

  have "(c_of t z)[z::=V_var x]\<^sub>c\<^sub>v = c'[z'::=V_var z]\<^sub>c\<^sub>v[z::=V_var x]\<^sub>c\<^sub>v"  using c_of.simps fresh_Pair  z by metis
  also have "... = c'[z'::=V_var x]\<^sub>c\<^sub>v"  using subst_v_simple_commute subst_v_c_def assms c_of.simps z  ** by metis
  finally show ?thesis using c_of.simps[of z' x "b_of t" c']  fresh_Pair z by metis
qed

lemma type_eq_subst_eq1:
  fixes v::v and c1::c
  assumes "\<lbrace> z1 : b1  |  c1 \<rbrace> = (\<lbrace> z2 : b2  |  c2 \<rbrace>)" and "atom z1 \<sharp> c2" 
  shows "c1[z1::=v]\<^sub>c\<^sub>v = c2[z2::=v]\<^sub>c\<^sub>v" and "b1=b2" and " c1 = (z1 \<leftrightarrow> z2) \<bullet> c2"
proof -
  show "c1[z1::=v]\<^sub>c\<^sub>v = c2[z2::=v]\<^sub>c\<^sub>v" using type_eq_subst_eq assms by blast
  show "b1=b2" using \<tau>.eq_iff assms by blast
  have "z1 = z2 \<and> c1 = c2 \<or> z1 \<noteq> z2 \<and> c1 = (z1 \<leftrightarrow> z2) \<bullet> c2 \<and> atom z1 \<sharp> c2" 
    using \<tau>.eq_iff Abs1_eq_iff[of z1 c1 z2 c2] assms by blast 
  thus  "c1 = (z1 \<leftrightarrow> z2) \<bullet> c2" by auto
qed

lemma type_eq_subst_eq2:
  fixes v::v and c1::c
  assumes "\<lbrace> z1 : b1  |  c1 \<rbrace> = (\<lbrace> z2 : b2  |  c2 \<rbrace>)" 
  shows "c1[z1::=v]\<^sub>c\<^sub>v = c2[z2::=v]\<^sub>c\<^sub>v" and "b1=b2" and "[[atom z1]]lst. c1 = [[atom z2]]lst. c2"
proof -
  show "c1[z1::=v]\<^sub>c\<^sub>v = c2[z2::=v]\<^sub>c\<^sub>v" using type_eq_subst_eq assms by blast
  show "b1=b2" using \<tau>.eq_iff assms by blast
  show  "[[atom z1]]lst. c1 = [[atom z2]]lst. c2" 
    using \<tau>.eq_iff assms by auto
qed

lemma type_eq_subst_eq3:
  fixes v::v and c1::c
  assumes "\<lbrace> z1 : b1  |  c1 \<rbrace> = (\<lbrace> z2 : b2  |  c2 \<rbrace>)" and "atom z1 \<sharp> c2" 
  shows "c1 = c2[z2::=V_var z1]\<^sub>c\<^sub>v" and "b1=b2"
  using type_eq_subst_eq1 assms  subst_v_c_def 
  by (metis subst_cv_var_flip)+

lemma type_eq_flip:
  assumes "atom x \<sharp> c"
  shows "\<lbrace> z : b  | c \<rbrace> = \<lbrace> x : b | (x \<leftrightarrow> z ) \<bullet> c \<rbrace>"
  using \<tau>.eq_iff Abs1_eq_iff assms 
  by (metis (no_types, lifting) flip_fresh_fresh)

lemma c_of_true:
  "c_of \<lbrace> z' : B_bool  | TRUE \<rbrace> x = C_true"
proof(nominal_induct "\<lbrace> z' : B_bool  | TRUE \<rbrace>" avoiding: x rule:\<tau>.strong_induct)
  case (T_refined_type x1a x3a)
  hence "\<lbrace> z' : B_bool  | TRUE \<rbrace> = \<lbrace> x1a : B_bool  | x3a \<rbrace>" using \<tau>.eq_iff by metis
  then show ?case using subst_cv.simps c_of.simps T_refined_type 
      type_eq_subst_eq3 
    by (metis type_eq_subst_eq)
qed

lemma type_eq_subst:
  assumes "atom x \<sharp> c"
  shows "\<lbrace> z : b  | c \<rbrace> = \<lbrace> x : b | c[z::=[x]\<^sup>v]\<^sub>c\<^sub>v \<rbrace>"
  using \<tau>.eq_iff Abs1_eq_iff assms 
  using subst_cv_var_flip type_eq_flip by auto

lemma type_e_subst_fresh:
  fixes x::x and z::x
  assumes "atom z \<sharp> (x,v)" and "atom x \<sharp> e" 
  shows "\<lbrace> z : b  | CE_val (V_var z)  ==  e  \<rbrace>[x::=v]\<^sub>\<tau>\<^sub>v = \<lbrace> z : b  | CE_val (V_var z)  ==  e  \<rbrace>"
  using assms subst_tv.simps subst_cv.simps forget_subst_cev by simp

lemma type_v_subst_fresh:
  fixes x::x and z::x
  assumes "atom z \<sharp> (x,v)" and "atom x \<sharp> v'" 
  shows "\<lbrace> z : b  | CE_val (V_var z)  ==  CE_val v'  \<rbrace>[x::=v]\<^sub>\<tau>\<^sub>v = \<lbrace> z : b  | CE_val (V_var z)  ==  CE_val v'  \<rbrace>"
  using assms subst_tv.simps subst_cv.simps  by simp

lemma subst_tbase_eq:
  "b_of \<tau> = b_of \<tau>[x::=v]\<^sub>\<tau>\<^sub>v"
proof -
  obtain z and b and c where zbc: "\<tau> = \<lbrace> z:b|c\<rbrace> \<and> atom z \<sharp> (x,v)" using \<tau>.exhaust
    by (metis prod.inject subst_tv.cases)
  hence "b_of \<lbrace> z:b|c\<rbrace> = b_of \<lbrace> z:b|c\<rbrace>[x::=v]\<^sub>\<tau>\<^sub>v" using subst_tv.simps by simp
  thus ?thesis using zbc by blast
qed

lemma subst_tv_if:
  assumes "atom z1 \<sharp> (x,v)" and "atom z' \<sharp> (x,v)" 
  shows "\<lbrace> z1 : b  | CE_val (v'[x::=v]\<^sub>v\<^sub>v)  ==  CE_val (V_lit l)   IMP  (c'[x::=v]\<^sub>c\<^sub>v)[z'::=[z1]\<^sup>v]\<^sub>c\<^sub>v  \<rbrace> = 
         \<lbrace> z1 : b  | CE_val v'           ==  CE_val (V_lit l)   IMP  c'[z'::=[z1]\<^sup>v]\<^sub>c\<^sub>v  \<rbrace>[x::=v]\<^sub>\<tau>\<^sub>v" 
  using subst_cv_commute_full[of z' v x "V_var z1" c']  subst_tv.simps subst_vv.simps(1) subst_ev.simps  subst_cv.simps assms 
  by simp

lemma subst_tv_tid:
  assumes "atom za \<sharp> (x,v)"
  shows "\<lbrace> za : B_id tid  | TRUE \<rbrace> = \<lbrace> za : B_id tid   | TRUE \<rbrace>[x::=v]\<^sub>\<tau>\<^sub>v"
  using assms subst_tv.simps subst_cv.simps by presburger


lemma b_of_subst:
  "b_of (\<tau>[x::=v]\<^sub>\<tau>\<^sub>v) = b_of \<tau>"
proof -
  obtain z b c where *:"\<tau> = \<lbrace> z : b | c \<rbrace> \<and> atom z \<sharp> (x,v)" using obtain_fresh_z by metis
  thus ?thesis  using subst_tv.simps * by auto 
qed

lemma subst_tv_flip:
  assumes "\<tau>'[x::=v]\<^sub>\<tau>\<^sub>v = \<tau>" and "atom x \<sharp> (v,\<tau>)" and "atom x' \<sharp> (v,\<tau>)"
  shows "((x' \<leftrightarrow> x) \<bullet> \<tau>')[x'::=v]\<^sub>\<tau>\<^sub>v = \<tau>"
proof -
  have "(x' \<leftrightarrow> x) \<bullet> v = v \<and> (x' \<leftrightarrow> x) \<bullet> \<tau> = \<tau>" using assms flip_fresh_fresh by auto
  thus ?thesis using subst_tv.eqvt[of  "(x' \<leftrightarrow> x)"  \<tau>' x v ] assms by auto
qed

lemma subst_cv_true:
  "\<lbrace> z : B_id tid  | TRUE \<rbrace> = \<lbrace> z : B_id tid  | TRUE \<rbrace>[x::=v]\<^sub>\<tau>\<^sub>v" 
proof -
  obtain za::x where "atom za \<sharp> (x,v)" using obtain_fresh by auto
  hence "\<lbrace> z : B_id tid   | TRUE \<rbrace> = \<lbrace> za: B_id tid | TRUE \<rbrace>" using \<tau>.eq_iff Abs1_eq_iff by fastforce
  moreover have  "\<lbrace> za : B_id tid   | TRUE \<rbrace> = \<lbrace> za : B_id tid   | TRUE \<rbrace>[x::=v]\<^sub>\<tau>\<^sub>v"  
    using subst_cv.simps subst_tv.simps  by (simp add: \<open>atom za \<sharp> (x, v)\<close>)
  ultimately show ?thesis by argo
qed

lemma t_eq_supp:
  assumes "(\<lbrace> z : b | c \<rbrace>) = (\<lbrace>  z1 : b1 | c1 \<rbrace>)"
  shows "supp c - { atom z } = supp c1 - { atom z1 }"
proof - 
  have "supp c - { atom z } \<union> supp b = supp c1 - { atom z1 } \<union> supp b1" using \<tau>.supp assms
    by (metis list.set(1) list.simps(15) sup_bot.right_neutral supp_b_empty)
  moreover have "supp b = supp b1" using assms  \<tau>.eq_iff by simp
  moreover have "atom z1 \<notin> supp b1 \<and> atom z \<notin> supp b" using  supp_b_empty by simp
  ultimately show ?thesis
    by (metis \<tau>.eq_iff \<tau>.supp assms b.supp(1) list.set(1) list.set(2) sup_bot.right_neutral)
qed

lemma fresh_t_eq: 
  fixes x::x
  assumes  "(\<lbrace> z : b  | c \<rbrace>) = (\<lbrace> zz : b | cc \<rbrace>)" and "atom x \<sharp> c" and "x \<noteq> zz"
  shows "atom x \<sharp> cc"
proof - 
  have "supp c - { atom z } \<union> supp b = supp cc - { atom zz } \<union> supp b" using \<tau>.supp assms
    by (metis list.set(1) list.simps(15) sup_bot.right_neutral supp_b_empty)
  moreover have "atom x \<notin> supp c" using assms fresh_def by blast
  ultimately have "atom x \<notin> supp cc - { atom zz } \<union> supp b" by force
  hence "atom x \<notin> supp cc" using assms by simp
  thus ?thesis using fresh_def by auto
qed

section \<open>Mutable Variable Context\<close>

nominal_function subst_dv :: "\<Delta> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<Delta>" where
  "subst_dv  DNil x v = DNil"
| "subst_dv ((u,t) #\<^sub>\<Delta> \<Delta>) x v  = ((u,t[x::=v]\<^sub>\<tau>\<^sub>v) #\<^sub>\<Delta> (subst_dv \<Delta> x v ))"
       apply (simp add: eqvt_def subst_dv_graph_aux_def,auto )
  using delete_aux.elims by (metis \<Delta>.exhaust surj_pair)
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_dv_abbrev :: "\<Delta> \<Rightarrow> x \<Rightarrow> v \<Rightarrow> \<Delta>" ("_[_::=_]\<^sub>\<Delta>\<^sub>v" [1000,50,50] 1000)
  where 
    "\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v  \<equiv> subst_dv \<Delta> x v " 

nominal_function dmap :: "(u*\<tau> \<Rightarrow> u*\<tau>) \<Rightarrow> \<Delta> \<Rightarrow> \<Delta>" where
  "dmap f DNil  = DNil"
| "dmap  f ((u,t)#\<^sub>\<Delta>\<Delta>)  = (f (u,t) #\<^sub>\<Delta> (dmap f \<Delta> ))"
       apply (simp add: eqvt_def dmap_graph_aux_def,auto )
  using delete_aux.elims by (metis \<Delta>.exhaust surj_pair)
nominal_termination (eqvt) by lexicographic_order

lemma subst_dv_iff:
  "\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v = dmap (\<lambda>(u,t). (u, t[x::=v]\<^sub>\<tau>\<^sub>v)) \<Delta>"
  by(induct \<Delta>, auto)

lemma size_subst_dv [simp]: "size ( subst_dv G i x) \<le> size G"
  by (induct G,auto) 

lemma forget_subst_dv [simp]: "atom a \<sharp> G \<Longrightarrow> subst_dv G a x = G"
  apply (induct G ,auto) 
  using fresh_DCons fresh_PairD(1) not_self_fresh apply fastforce
  apply (simp add: fresh_DCons)+
  done

lemma subst_dv_member:
  assumes "(u,\<tau>) \<in> setD \<Delta>"
  shows  "(u, \<tau>[x::=v]\<^sub>\<tau>\<^sub>v) \<in> setD (\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v)"
  using assms  by(induct \<Delta> rule: \<Delta>_induct,auto)

lemma fresh_subst_dv:
  fixes x::x
  assumes "atom xa \<sharp> \<Delta>" and "atom xa \<sharp> v"
  shows "atom xa \<sharp>\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v" 
  using assms proof(induct \<Delta> rule:\<Delta>_induct)
  case DNil
  then show ?case by auto
next
  case (DCons u t  \<Delta>)
  then show ?case using subst_dv.simps  subst_v_\<tau>_def fresh_DCons fresh_Pair by simp
qed

lemma fresh_subst_dv_if:
  fixes j::atom and i::x and  x::v and t::\<Delta>
  assumes "j \<sharp> t \<and> j \<sharp> x" 
  shows  "(j \<sharp> subst_dv t i x)"
  using assms proof(induct t rule: \<Delta>_induct)
  case DNil
  then show ?case using subst_gv.simps fresh_GNil by auto
next
  case (DCons u' t'  D')
  then show ?case unfolding subst_dv.simps using fresh_DCons fresh_subst_tv_if fresh_Pair by metis
qed

section \<open>Statements\<close>

text \<open> Using ideas from proofs at top of AFP/Launchbury/Substitution.thy.
       Subproofs borrowed from there; hence the apply style proofs. \<close>

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (case_sum (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined))")
  subst_sv :: "s \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> s"
  and subst_branchv :: "branch_s \<Rightarrow> x \<Rightarrow> v  \<Rightarrow> branch_s" 
  and subst_branchlv :: "branch_list \<Rightarrow> x \<Rightarrow> v \<Rightarrow> branch_list" where
  "subst_sv ( (AS_val v') ) x v = (AS_val (subst_vv v' x v  ))"
| "atom y \<sharp> (x,v) \<Longrightarrow> subst_sv  (AS_let y  e s) x v = (AS_let y  (e[x::=v]\<^sub>e\<^sub>v) (subst_sv s x v ))"  
| "atom y \<sharp> (x,v) \<Longrightarrow> subst_sv (AS_let2 y t s1 s2) x v = (AS_let2 y (t[x::=v]\<^sub>\<tau>\<^sub>v) (subst_sv s1 x v ) (subst_sv s2 x v ))"  
| " subst_sv (AS_match v'  cs) x v = AS_match  (v'[x::=v]\<^sub>v\<^sub>v)  (subst_branchlv cs x v )"
| "subst_sv (AS_assign y v') x v = AS_assign y (subst_vv v' x v )"
| "subst_sv ( (AS_if v' s1 s2) ) x v = (AS_if (subst_vv v' x v ) (subst_sv s1 x v ) (subst_sv s2 x v ) )"  
| "atom u \<sharp> (x,v) \<Longrightarrow> subst_sv (AS_var u \<tau> v' s) x v = AS_var u (subst_tv \<tau> x v ) (subst_vv v' x v ) (subst_sv s x v ) "
| "subst_sv (AS_while s1 s2) x v = AS_while (subst_sv s1 x v ) (subst_sv s2 x v )"
| "subst_sv (AS_seq s1 s2) x v = AS_seq (subst_sv s1 x v ) (subst_sv s2 x v )" 
| "subst_sv (AS_assert c s) x v = AS_assert (subst_cv c x v) (subst_sv s x v)"
| "atom x1 \<sharp> (x,v) \<Longrightarrow>  subst_branchv (AS_branch dc x1 s1 ) x v  = AS_branch dc x1 (subst_sv s1 x v )" 

| "subst_branchlv (AS_final cs) x v = AS_final (subst_branchv  cs x v )"
| "subst_branchlv (AS_cons cs css) x v = AS_cons (subst_branchv cs x v ) (subst_branchlv css x v )"
                      apply (auto,simp add: eqvt_def subst_sv_subst_branchv_subst_branchlv_graph_aux_def )
proof(goal_cases)

  have eqvt_at_proj: "\<And> s xa va . eqvt_at subst_sv_subst_branchv_subst_branchlv_sumC (Inl (s, xa, va)) \<Longrightarrow> 
           eqvt_at (\<lambda>a. projl (subst_sv_subst_branchv_subst_branchlv_sumC (Inl a))) (s, xa, va)"
    apply(simp add: eqvt_at_def)
    apply(rule)
    apply(subst Projl_permute)
     apply(thin_tac _)+
     apply (simp add: subst_sv_subst_branchv_subst_branchlv_sumC_def)
     apply (simp add: THE_default_def)
     apply (case_tac "Ex1 (subst_sv_subst_branchv_subst_branchlv_graph (Inl (s,xa,va)))")
      apply simp
      apply(auto)[1]
      apply (erule_tac x="x" in allE)
      apply simp
      apply(cases rule: subst_sv_subst_branchv_subst_branchlv_graph.cases)    
                   apply(assumption)
                  apply(rule_tac x="Sum_Type.projl x" in exI,clarify,rule the1_equality,blast,simp (no_asm) only: sum.sel)+
        apply blast +

    apply(simp)+      
    done

  {
    case (1 P x')    
    then show ?case proof(cases x')
      case (Inl a) thus P 
      proof(cases a)
        case (fields aa bb cc)
        thus P using Inl 1 s_branch_s_branch_list.strong_exhaust fresh_star_insert by metis
      qed
    next
      case (Inr b) thus P
      proof(cases b)
        case (Inl a) thus P proof(cases a)
          case (fields aa bb cc)
          then show ?thesis  using Inr Inl 1 s_branch_s_branch_list.strong_exhaust fresh_star_insert by metis
        qed
      next
        case Inr2: (Inr b) thus P proof(cases b)
          case (fields aa bb cc)
          then show ?thesis  using Inr Inr2 1 s_branch_s_branch_list.strong_exhaust fresh_star_insert by metis
        qed
      qed
    qed
  next
    case (2 y s ya xa va sa c)
    thus ?case using eqvt_triple eqvt_at_proj by blast
  next
    case (3 y s2 ya xa va s1a s2a c)
    thus ?case using eqvt_triple eqvt_at_proj by blast
  next
    case (4 u xa va s ua sa c)
    moreover have "atom u \<sharp> (xa, va) \<and> atom ua \<sharp> (xa, va)" 
      using fresh_Pair u_fresh_xv by auto
    ultimately show ?case using eqvt_triple[of u xa va ua s sa]  subst_sv_def eqvt_at_proj by metis
  next
    case (5 x1 s1 x1a xa va s1a c)
    thus ?case using eqvt_triple eqvt_at_proj by blast
  }
qed
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_sv_abbrev :: "s \<Rightarrow> x \<Rightarrow> v \<Rightarrow> s" ("_[_::=_]\<^sub>s\<^sub>v" [1000,50,50] 1000)
  where 
    "s[x::=v]\<^sub>s\<^sub>v  \<equiv> subst_sv s x v" 

abbreviation 
  subst_branchv_abbrev :: "branch_s \<Rightarrow> x \<Rightarrow> v \<Rightarrow> branch_s" ("_[_::=_]\<^sub>s\<^sub>v" [1000,50,50] 1000)
  where 
    "s[x::=v]\<^sub>s\<^sub>v  \<equiv> subst_branchv s x v" 

lemma size_subst_sv [simp]:  "size (subst_sv A i x ) = size A" and  "size (subst_branchv B i x ) = size B"  and  "size (subst_branchlv C i x ) = size C"
  by(nominal_induct A and B and C avoiding: i x rule: s_branch_s_branch_list.strong_induct,auto)

lemma forget_subst_sv [simp]: shows  "atom a \<sharp> A \<Longrightarrow> subst_sv A a x = A" and "atom a \<sharp> B \<Longrightarrow> subst_branchv B a x = B" and "atom a \<sharp> C \<Longrightarrow> subst_branchlv C a x  = C"
  by (nominal_induct A and B and C avoiding: a x rule: s_branch_s_branch_list.strong_induct,auto simp: fresh_at_base)

lemma subst_sv_id [simp]: "subst_sv A a (V_var a) = A" and "subst_branchv B a (V_var a) = B" and  "subst_branchlv C a (V_var a)  = C"
proof(nominal_induct A and B and C avoiding: a  rule: s_branch_s_branch_list.strong_induct) 
  case (AS_let x option e s)
  then show ?case 
    by (metis (no_types, lifting) fresh_Pair not_None_eq subst_ev_id subst_sv.simps(2) subst_sv.simps(3) subst_tv_id v.fresh(2))
next
  case (AS_match v branch_s)
  then show ?case using fresh_Pair not_None_eq subst_ev_id subst_sv.simps subst_sv.simps subst_tv_id v.fresh subst_vv_id
    by metis 
qed(auto)+ 

lemma fresh_subst_sv_if_rl:
  shows 
    "(atom x \<sharp> s \<and> j \<sharp> s) \<or> (j \<sharp> v \<and> (j \<sharp> s \<or> j = atom x)) \<Longrightarrow> j \<sharp> (subst_sv s x v )" and
    "(atom x \<sharp> cs \<and> j \<sharp> cs) \<or> (j \<sharp> v \<and> (j \<sharp> cs \<or> j = atom x)) \<Longrightarrow> j \<sharp> (subst_branchv cs x v)" and
    "(atom x \<sharp> css \<and> j \<sharp> css) \<or> (j \<sharp> v \<and> (j \<sharp> css \<or> j = atom x)) \<Longrightarrow> j \<sharp> (subst_branchlv css x v )" 
    apply(nominal_induct s and cs and css avoiding: v x rule: s_branch_s_branch_list.strong_induct)
  using pure_fresh by force+

lemma fresh_subst_sv_if_lr:
  shows  "j \<sharp> (subst_sv s x v) \<Longrightarrow> (atom x \<sharp> s \<and> j \<sharp> s) \<or> (j \<sharp> v \<and> (j \<sharp> s \<or> j = atom x))" and
    "j \<sharp> (subst_branchv cs x v) \<Longrightarrow> (atom x \<sharp> cs \<and> j \<sharp> cs) \<or> (j \<sharp> v \<and> (j \<sharp> cs \<or> j = atom x))" and       
    "j \<sharp> (subst_branchlv css x v ) \<Longrightarrow> (atom x \<sharp> css \<and> j \<sharp> css) \<or> (j \<sharp> v \<and> (j \<sharp> css \<or> j = atom x))"
proof(nominal_induct s and cs and css avoiding: v x rule: s_branch_s_branch_list.strong_induct)
  case (AS_branch list x s )
  then show ?case using s_branch_s_branch_list.fresh fresh_Pair list.distinct(1) list.set_cases pure_fresh set_ConsD subst_branchv.simps by metis
next
  case (AS_let y e s')
  thus ?case proof(cases "atom x \<sharp>  (AS_let y e s')")
    case True
    hence "subst_sv (AS_let y  e s') x v  =  (AS_let y e s')" using forget_subst_sv by simp
    hence "j \<sharp>  (AS_let y  e s')" using AS_let by argo
    then show ?thesis using True by blast
  next
    case False
    have "subst_sv (AS_let y  e s') x v  = AS_let y  (e[x::=v]\<^sub>e\<^sub>v) (s'[x::=v]\<^sub>s\<^sub>v)" using subst_sv.simps(2) AS_let by force
    hence "((j \<sharp> s'[x::=v]\<^sub>s\<^sub>v \<or> j \<in> set [atom y]) \<and> j \<sharp> None \<and> j \<sharp> e[x::=v]\<^sub>e\<^sub>v)" using s_branch_s_branch_list.fresh AS_let 
      by (simp add: fresh_None)
    then show ?thesis using  AS_let  fresh_None fresh_subst_ev_if list.discI list.set_cases s_branch_s_branch_list.fresh set_ConsD 
      by metis
  qed
next
  case (AS_let2 y \<tau> s1 s2)
  thus ?case proof(cases "atom x \<sharp>  (AS_let2 y \<tau> s1 s2)")
    case True
    hence "subst_sv  (AS_let2 y \<tau> s1 s2)  x v =  (AS_let2 y \<tau> s1 s2)" using forget_subst_sv by simp
    hence "j \<sharp>  (AS_let2 y \<tau> s1 s2)" using AS_let2 by argo
    then show ?thesis using True by blast
  next
    case False
    have "subst_sv (AS_let2 y \<tau> s1 s2) x v  = AS_let2 y (\<tau>[x::=v]\<^sub>\<tau>\<^sub>v) (s1[x::=v]\<^sub>s\<^sub>v) (s2[x::=v]\<^sub>s\<^sub>v)" using subst_sv.simps AS_let2 by force
    then show ?thesis using  AS_let2
        fresh_subst_tv_if list.discI list.set_cases s_branch_s_branch_list.fresh(4) set_ConsD by auto
  qed
qed(auto)+

lemma fresh_subst_sv_if[simp]:
  fixes x::x and v::v
  shows "j \<sharp> (subst_sv s x v) \<longleftrightarrow> (atom x \<sharp> s \<and> j \<sharp> s) \<or> (j \<sharp> v \<and> (j \<sharp> s \<or> j = atom x))" and
    "j \<sharp> (subst_branchv cs x v) \<longleftrightarrow> (atom x \<sharp> cs \<and> j \<sharp> cs) \<or> (j \<sharp> v \<and> (j \<sharp> cs \<or> j = atom x))"
  using fresh_subst_sv_if_lr fresh_subst_sv_if_rl by metis+

lemma subst_sv_commute [simp]:
  fixes A::s and t::v and j::x and i::x
  shows  "atom j \<sharp> A \<Longrightarrow> (subst_sv (subst_sv A i t)  j u ) = subst_sv A i (subst_vv t j u )" and
    "atom j \<sharp> B \<Longrightarrow> (subst_branchv  (subst_branchv B i t ) j u ) = subst_branchv B i (subst_vv t j u )" and
    "atom j \<sharp> C \<Longrightarrow> (subst_branchlv  (subst_branchlv C i t) j u ) = subst_branchlv C i (subst_vv t j u   ) "
    apply(nominal_induct A and B and C avoiding: i j t u rule: s_branch_s_branch_list.strong_induct) 
  by(auto simp: fresh_at_base)

lemma c_eq_perm:
  assumes "( (atom z)  \<rightleftharpoons> (atom z') )  \<bullet> c = c'" and "atom z'  \<sharp> c"
  shows "\<lbrace> z : b | c \<rbrace> = \<lbrace> z' : b | c' \<rbrace>"
  using \<tau>.eq_iff Abs1_eq_iff(3) 
  by (metis Nominal2_Base.swap_commute assms(1) assms(2) flip_def swap_fresh_fresh)

lemma subst_sv_flip:
  fixes s::s and sa::s and v'::v
  assumes "atom c \<sharp> (s, sa)" and "atom c \<sharp> (v',x, xa, s, sa)" "atom x \<sharp> v'" and "atom xa \<sharp> v'" and "(x \<leftrightarrow> c) \<bullet> s = (xa \<leftrightarrow> c) \<bullet> sa" 
  shows "s[x::=v']\<^sub>s\<^sub>v = sa[xa::=v']\<^sub>s\<^sub>v"
proof - 
  have "atom x \<sharp> (s[x::=v']\<^sub>s\<^sub>v)" and xafr: "atom xa \<sharp> (sa[xa::=v']\<^sub>s\<^sub>v)" 
    and  "atom c \<sharp> ( s[x::=v']\<^sub>s\<^sub>v, sa[xa::=v']\<^sub>s\<^sub>v)" using assms using  fresh_subst_sv_if assms  by( blast+ ,force)

  hence "s[x::=v']\<^sub>s\<^sub>v = (x \<leftrightarrow> c) \<bullet> (s[x::=v']\<^sub>s\<^sub>v)"  by (simp add: flip_fresh_fresh fresh_Pair)
  also have " ... = ((x \<leftrightarrow> c) \<bullet> s)[ ((x \<leftrightarrow> c) \<bullet> x) ::= ((x \<leftrightarrow> c) \<bullet> v') ]\<^sub>s\<^sub>v" using subst_sv_subst_branchv_subst_branchlv.eqvt  by blast
  also have "... = ((xa \<leftrightarrow> c) \<bullet> sa)[ ((x \<leftrightarrow> c) \<bullet> x) ::= ((x \<leftrightarrow> c) \<bullet> v') ]\<^sub>s\<^sub>v" using assms by presburger
  also have "... = ((xa \<leftrightarrow> c) \<bullet> sa)[ ((xa \<leftrightarrow> c) \<bullet> xa) ::= ((xa \<leftrightarrow> c) \<bullet> v') ]\<^sub>s\<^sub>v" using assms 
    by (metis flip_at_simps(1) flip_fresh_fresh fresh_PairD(1))
  also have "... =  (xa \<leftrightarrow> c) \<bullet> (sa[xa::=v']\<^sub>s\<^sub>v)" using subst_sv_subst_branchv_subst_branchlv.eqvt  by presburger
  also have "... = sa[xa::=v']\<^sub>s\<^sub>v" using xafr assms by (simp add: flip_fresh_fresh fresh_Pair)
  finally show ?thesis by simp
qed

lemma if_type_eq:
  fixes \<Gamma>::\<Gamma> and v::v and z1::x
  assumes "atom z1' \<sharp> (v, ca, (x, b, c) #\<^sub>\<Gamma> \<Gamma>,  (CE_val v  ==  CE_val (V_lit ll) IMP  ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v ))" and "atom z1 \<sharp> v" 
    and "atom z1 \<sharp> (za,ca)" and "atom z1' \<sharp> (za,ca)"
  shows "(\<lbrace> z1' : ba  | CE_val v  ==  CE_val (V_lit ll)   IMP  ca[za::=[z1']\<^sup>v]\<^sub>c\<^sub>v  \<rbrace>) = \<lbrace> z1 : ba  | CE_val v  ==  CE_val (V_lit ll) IMP  ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v  \<rbrace>"
proof -
  have "atom z1' \<sharp> (CE_val v  ==  CE_val (V_lit ll) IMP  ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v )" using assms fresh_prod4 by blast
  moreover hence "(CE_val v  ==  CE_val (V_lit ll)   IMP  ca[za::=[z1']\<^sup>v]\<^sub>c\<^sub>v) = (z1' \<leftrightarrow> z1) \<bullet> (CE_val v  ==  CE_val (V_lit ll)   IMP  ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v )"
  proof -
    have "(z1' \<leftrightarrow> z1) \<bullet> (CE_val v  ==  CE_val (V_lit ll)   IMP  ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v ) = ( (z1' \<leftrightarrow> z1) \<bullet> (CE_val v  ==  CE_val (V_lit ll)) IMP  ((z1' \<leftrightarrow> z1) \<bullet> ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v ))"
      by auto
    also have "... = ((CE_val v  ==  CE_val (V_lit ll))   IMP  ((z1' \<leftrightarrow> z1) \<bullet> ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v ))"
      using \<open>atom z1 \<sharp> v\<close> assms 
      by (metis (mono_tags) \<open>atom z1' \<sharp> (CE_val v == CE_val (V_lit ll) IMP ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v )\<close> c.fresh(6) c.fresh(7) ce.fresh(1) flip_at_simps(2) flip_fresh_fresh fresh_at_base_permute_iff fresh_def supp_l_empty v.fresh(1))
    also have "... =  ((CE_val v  ==  CE_val (V_lit ll))   IMP  (ca[za::=[z1']\<^sup>v]\<^sub>c\<^sub>v ))"
      using assms   by fastforce
    finally show ?thesis by auto
  qed
  ultimately show ?thesis    
    using \<tau>.eq_iff Abs1_eq_iff(3)[of z1' "CE_val v  ==  CE_val (V_lit ll) IMP  ca[za::=[z1']\<^sup>v]\<^sub>c\<^sub>v" 
        z1 "CE_val v  ==  CE_val (V_lit ll)   IMP ca[za::=[z1]\<^sup>v]\<^sub>c\<^sub>v"] by blast
qed 

lemma subst_sv_var_flip:
  fixes x::x and s::s and z::x
  shows "atom x \<sharp> s \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> s) = s[z::=[x]\<^sup>v]\<^sub>s\<^sub>v" and 
    "atom x \<sharp> cs \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> cs) = subst_branchv cs z [x]\<^sup>v" and
    "atom x \<sharp> css \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> css) = subst_branchlv css z [x]\<^sup>v"
    apply(nominal_induct s and cs and css avoiding: z x rule: s_branch_s_branch_list.strong_induct)
  using [[simproc del: alpha_lst]]
              apply (auto  ) (* This unpacks subst, perm *)
  using  subst_tv_var_flip  flip_fresh_fresh v.fresh s_branch_s_branch_list.fresh 
    subst_v_\<tau>_def subst_v_v_def subst_vv_var_flip subst_v_e_def subst_ev_var_flip pure_fresh   apply auto 
     defer 1 (* Sometimes defering hard goals to the end makes it easier to finish *)
  using x_fresh_u   apply blast (* Next two involve u and flipping with x *)
    defer 1
  using x_fresh_u   apply blast
   defer 1
  using x_fresh_u Abs1_eq_iff'(3) flip_fresh_fresh 
   apply (simp add: subst_v_c_def)
  using x_fresh_u Abs1_eq_iff'(3) flip_fresh_fresh  
  by (simp add: flip_fresh_fresh)

instantiation s :: has_subst_v
begin

definition 
  "subst_v = subst_sv"

instance proof
  fix j::atom and i::x and  x::v and t::s
  show  "(j \<sharp> subst_v t i x) = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"
    using fresh_subst_sv_if subst_v_s_def by auto

  fix a::x and tm::s and x::v
  show "atom a \<sharp> tm \<Longrightarrow> subst_v tm a x  = tm"
    using forget_subst_sv subst_v_s_def by simp

  fix a::x and tm::s
  show "subst_v tm a (V_var a) = tm" using subst_sv_id  subst_v_s_def by simp

  fix p::perm and x1::x and v::v and t1::s
  show "p \<bullet> subst_v t1 x1 v  = subst_v  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    using subst_sv_commute  subst_v_s_def by simp

  fix x::x and c::s and z::x
  show "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c[z::=[x]\<^sup>v]\<^sub>v"
    using subst_sv_var_flip subst_v_s_def by simp

  fix x::x and c::s and z::x
  show  "atom x \<sharp> c \<Longrightarrow> c[z::=[x]\<^sup>v]\<^sub>v[x::=v]\<^sub>v = c[z::=v]\<^sub>v"
    using subst_sv_var_flip subst_v_s_def by simp
qed
end

section \<open>Type Definition\<close>

nominal_function subst_ft_v :: "fun_typ \<Rightarrow> x \<Rightarrow> v \<Rightarrow> fun_typ" where
  "atom z \<sharp> (x,v) \<Longrightarrow> subst_ft_v ( AF_fun_typ z b c t (s::s)) x v = AF_fun_typ z b c[x::=v]\<^sub>c\<^sub>v t[x::=v]\<^sub>\<tau>\<^sub>v s[x::=v]\<^sub>s\<^sub>v"
     apply(simp add: eqvt_def subst_ft_v_graph_aux_def )
    apply(simp add:fun_typ.strong_exhaust )
   apply(auto) 
    apply(rule_tac y=a and c="(aa,b)" in fun_typ.strong_exhaust)
    apply (auto simp: eqvt_at_def fresh_star_def fresh_Pair fresh_at_base)

proof(goal_cases)
  case (1 z xa va c t s za ca ta sa cb)
  hence  "c[z::=[ cb ]\<^sup>v]\<^sub>c\<^sub>v = ca[za::=[ cb ]\<^sup>v]\<^sub>c\<^sub>v" 
    by (metis flip_commute subst_cv_var_flip)
  hence  "c[z::=[ cb ]\<^sup>v]\<^sub>c\<^sub>v[xa::=va]\<^sub>c\<^sub>v = ca[za::=[ cb ]\<^sup>v]\<^sub>c\<^sub>v[xa::=va]\<^sub>c\<^sub>v" by auto
  then show ?case using subst_cv_commute atom_eq_iff fresh_atom fresh_atom_at_base subst_cv_commute_full v.fresh 
    using 1 subst_cv_var_flip  flip_commute by metis
next
  case (2 z xa va c t s za ca ta sa cb)
  hence  "t[z::=[ cb ]\<^sup>v]\<^sub>\<tau>\<^sub>v = ta[za::=[ cb ]\<^sup>v]\<^sub>\<tau>\<^sub>v" by metis
  hence  "t[z::=[ cb ]\<^sup>v]\<^sub>\<tau>\<^sub>v[xa::=va]\<^sub>\<tau>\<^sub>v = ta[za::=[ cb ]\<^sup>v]\<^sub>\<tau>\<^sub>v[xa::=va]\<^sub>\<tau>\<^sub>v" by auto
  then show ?case using subst_tv_commute_full 2 
    by (metis atom_eq_iff fresh_atom fresh_atom_at_base v.fresh(2))
qed

nominal_termination (eqvt) by lexicographic_order

nominal_function subst_ftq_v :: "fun_typ_q \<Rightarrow> x \<Rightarrow> v \<Rightarrow> fun_typ_q" where
  "atom bv \<sharp> (x,v) \<Longrightarrow> subst_ftq_v (AF_fun_typ_some bv ft) x v = (AF_fun_typ_some bv (subst_ft_v ft x v))" 
|  "subst_ftq_v (AF_fun_typ_none  ft) x v = (AF_fun_typ_none (subst_ft_v ft x v))" 
       apply(simp add: eqvt_def subst_ftq_v_graph_aux_def )
      apply(simp add:fun_typ_q.strong_exhaust )
     apply(auto) 
   apply(rule_tac y=a and c="(aa,b)" in fun_typ_q.strong_exhaust)
    apply (auto simp: eqvt_at_def fresh_star_def fresh_Pair fresh_at_base)
proof(goal_cases)
  case (1 bv ft bva fta xa va c)
  then show ?case using subst_ft_v.simps  by (simp add: flip_fresh_fresh)
qed
nominal_termination (eqvt) by lexicographic_order

lemma size_subst_ft[simp]:  "size (subst_ft_v A x v) = size A" 
  by(nominal_induct A  avoiding: x v rule: fun_typ.strong_induct,auto)

lemma forget_subst_ft [simp]: shows  "atom x \<sharp> A \<Longrightarrow> subst_ft_v A x a = A" 
  by (nominal_induct A  avoiding: a x rule: fun_typ.strong_induct,auto simp: fresh_at_base)

lemma subst_ft_id [simp]: "subst_ft_v A a (V_var a)  = A"
  by(nominal_induct A  avoiding: a  rule: fun_typ.strong_induct,auto) 

instantiation fun_typ :: has_subst_v
begin

definition 
  "subst_v = subst_ft_v"

instance proof

  fix j::atom and i::x and  x::v and t::fun_typ
  show  "(j \<sharp> subst_v t i x) = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"
    apply(nominal_induct t avoiding: i x rule:fun_typ.strong_induct)
    apply(simp only: subst_v_fun_typ_def subst_ft_v.simps )
    using fun_typ.fresh fresh_subst_v_if apply simp
    by auto

  fix a::x and tm::fun_typ and x::v
  show "atom a \<sharp> tm \<Longrightarrow> subst_v tm a x  = tm"
  proof(nominal_induct tm avoiding: a x rule:fun_typ.strong_induct)
    case (AF_fun_typ x1a x2a x3a x4a x5a)
    then show ?case unfolding subst_ft_v.simps subst_v_fun_typ_def fun_typ.fresh  using forget_subst_v subst_ft_v.simps subst_v_c_def forget_subst_sv subst_v_\<tau>_def by fastforce
  qed

  fix a::x and tm::fun_typ
  show "subst_v tm a (V_var a) = tm" 
  proof(nominal_induct tm avoiding: a x rule:fun_typ.strong_induct)
    case (AF_fun_typ x1a x2a x3a x4a x5a)
    then show ?case unfolding subst_ft_v.simps subst_v_fun_typ_def fun_typ.fresh  using forget_subst_v subst_ft_v.simps subst_v_c_def forget_subst_sv subst_v_\<tau>_def by fastforce
  qed

  fix p::perm and x1::x and v::v and t1::fun_typ
  show "p \<bullet> subst_v t1 x1 v  = subst_v  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
  proof(nominal_induct t1 avoiding: x1 v rule:fun_typ.strong_induct)
    case (AF_fun_typ x1a x2a x3a x4a x5a)
    then show ?case unfolding subst_ft_v.simps subst_v_fun_typ_def fun_typ.fresh  using forget_subst_v subst_ft_v.simps subst_v_c_def forget_subst_sv subst_v_\<tau>_def by fastforce
  qed

  fix x::x and c::fun_typ and z::x
  show "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c[z::=[x]\<^sup>v]\<^sub>v"
    apply(nominal_induct c avoiding: x z rule:fun_typ.strong_induct)
    by (auto simp add: subst_v_c_def subst_v_s_def subst_v_\<tau>_def subst_v_fun_typ_def)

  fix x::x and c::fun_typ and z::x
  show  "atom x \<sharp> c \<Longrightarrow> c[z::=[x]\<^sup>v]\<^sub>v[x::=v]\<^sub>v = c[z::=v]\<^sub>v"
    apply(nominal_induct c avoiding: z x v rule:fun_typ.strong_induct)
    apply auto
    by (auto simp add: subst_v_c_def subst_v_s_def subst_v_\<tau>_def subst_v_fun_typ_def )
qed
end

instantiation fun_typ_q :: has_subst_v
begin

definition 
  "subst_v = subst_ftq_v"

instance proof
  fix j::atom and i::x and  x::v and t::fun_typ_q
  show  "(j \<sharp> subst_v t i x) = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))"
    apply(nominal_induct t avoiding: i x rule:fun_typ_q.strong_induct,auto)
                   apply(auto simp add: subst_v_fun_typ_def subst_v_s_def subst_v_\<tau>_def subst_v_fun_typ_q_def fresh_subst_v_if )    
    by (metis (no_types) fresh_subst_v_if subst_v_fun_typ_def)+

  fix i::x and t::fun_typ_q and x::v
  show "atom i \<sharp> t \<Longrightarrow> subst_v t i x  = t"
    apply(nominal_induct t avoiding: i x rule:fun_typ_q.strong_induct,auto)
    by(auto simp add: subst_v_fun_typ_def subst_v_s_def subst_v_\<tau>_def subst_v_fun_typ_q_def fresh_subst_v_if )    

  fix i::x and t::fun_typ_q
  show "subst_v t i (V_var i) = t" using subst_cv_id  subst_v_fun_typ_def  
    apply(nominal_induct t avoiding: i x rule:fun_typ_q.strong_induct,auto)
    by(auto simp add: subst_v_fun_typ_def subst_v_s_def subst_v_\<tau>_def subst_v_fun_typ_q_def fresh_subst_v_if )  

  fix p::perm and x1::x and v::v and t1::fun_typ_q
  show "p \<bullet> subst_v t1 x1 v  = subst_v  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    apply(nominal_induct t1 avoiding: v x1 rule:fun_typ_q.strong_induct,auto)
    by(auto simp add: subst_v_fun_typ_def subst_v_s_def subst_v_\<tau>_def subst_v_fun_typ_q_def fresh_subst_v_if )  

  fix x::x and c::fun_typ_q and z::x
  show "atom x \<sharp> c \<Longrightarrow> ((x \<leftrightarrow> z) \<bullet> c) = c[z::=[x]\<^sup>v]\<^sub>v"
    apply(nominal_induct c avoiding: x z rule:fun_typ_q.strong_induct,auto)
    by(auto simp add: subst_v_fun_typ_def subst_v_s_def subst_v_\<tau>_def subst_v_fun_typ_q_def fresh_subst_v_if )  

  fix x::x and c::fun_typ_q and z::x
  show  "atom x \<sharp> c \<Longrightarrow> c[z::=[x]\<^sup>v]\<^sub>v[x::=v]\<^sub>v = c[z::=v]\<^sub>v"
    apply(nominal_induct c avoiding: z x v rule:fun_typ_q.strong_induct,auto)
     apply(auto simp add: subst_v_fun_typ_def subst_v_s_def subst_v_\<tau>_def subst_v_fun_typ_q_def fresh_subst_v_if )  
    by (metis subst_v_fun_typ_def flip_bv_x_cancel subst_ft_v.eqvt subst_v_simple_commute v.perm_simps )+
qed

end

section \<open>Variable Context\<close>

lemma subst_dv_fst_eq:
  "fst ` setD (\<Delta>[x::=v]\<^sub>\<Delta>\<^sub>v) = fst ` setD \<Delta>" 
  by(induct \<Delta> rule: \<Delta>_induct,simp,force)

lemma subst_gv_member_iff:
  fixes x'::x and x::x and v::v and c'::c
  assumes "(x',b',c') \<in> toSet \<Gamma>" and "atom x \<notin> atom_dom \<Gamma>" 
  shows "(x',b',c'[x::=v]\<^sub>c\<^sub>v) \<in> toSet \<Gamma>[x::=v]\<^sub>\<Gamma>\<^sub>v"
proof -
  have "x' \<noteq> x" using assms fresh_dom_free2 by metis
  then show ?thesis  using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
    case GNil
    then show ?case by auto
  next
    case (GCons x1 b1 c1 \<Gamma>')
    show ?case proof(cases "(x',b',c') = (x1,b1,c1)")
      case True
      hence "((x1, b1, c1) #\<^sub>\<Gamma> \<Gamma>')[x::=v]\<^sub>\<Gamma>\<^sub>v = ((x1, b1, c1[x::=v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v))"  using subst_gv.simps  \<open>x'\<noteq>x\<close> by auto
      then show ?thesis using True by auto
    next
      case False
      have "x1\<noteq>x" using fresh_def fresh_GCons fresh_Pair supp_at_base GCons fresh_dom_free2 by auto
      hence "(x', b', c') \<in> toSet \<Gamma>'" using GCons False toSet.simps by auto
      moreover have "atom x \<notin> atom_dom \<Gamma>'" using fresh_GCons GCons dom.simps toSet.simps by simp
      ultimately have  "(x', b', c'[x::=v]\<^sub>c\<^sub>v) \<in> toSet \<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v" using GCons by auto
      hence "(x', b', c'[x::=v]\<^sub>c\<^sub>v) \<in> toSet ((x1, b1, c1[x::=v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v))" by auto
      then show ?thesis using subst_gv.simps \<open>x1\<noteq>x\<close> by auto
    qed
  qed
qed

lemma fresh_subst_gv_if:
  fixes j::atom and i::x and  x::v and t::\<Gamma>
  assumes "j \<sharp> t \<and> j \<sharp> x" 
  shows  "(j \<sharp> subst_gv t i x)"
  using assms proof(induct t rule: \<Gamma>_induct)
  case GNil
  then show ?case using subst_gv.simps fresh_GNil by auto
next
  case (GCons x' b' c' \<Gamma>')
  then show ?case unfolding subst_gv.simps using fresh_GCons fresh_subst_cv_if by auto
qed

section \<open>Lookup\<close>

lemma set_GConsD: "y \<in> toSet (x #\<^sub>\<Gamma> xs) \<Longrightarrow> y=x \<or> y \<in> toSet xs"
  by auto

lemma  subst_g_assoc_cons:
  assumes "x \<noteq> x'"
  shows "(((x', b', c') #\<^sub>\<Gamma> \<Gamma>')[x::=v]\<^sub>\<Gamma>\<^sub>v @ G) = ((x', b', c'[x::=v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v) @ G))"
  using subst_gv.simps append_g.simps assms by auto

end