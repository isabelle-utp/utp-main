(*<*)
theory BTVSubst
  imports Syntax
begin
  (*>*)
chapter \<open>Basic Type Variable Substitution\<close>

section \<open>Class\<close>

class has_subst_b = fs +
  fixes subst_b :: "'a::fs \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> 'a::fs" ("_[_::=_]\<^sub>b" [1000,50,50] 1000)

assumes fresh_subst_if:  "j \<sharp> (t[i::=x]\<^sub>b )  \<longleftrightarrow> (atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))" 
  and    forget_subst[simp]:  "atom a \<sharp> tm \<Longrightarrow> tm[a::=x]\<^sub>b  = tm"
  and    subst_id[simp]:      "tm[a::=(B_var a)]\<^sub>b  = tm"
  and    eqvt[simp,eqvt]:          "(p::perm) \<bullet> (subst_b t1 x1 v ) = (subst_b (p \<bullet>t1) (p \<bullet>x1) (p \<bullet>v) )"
  and    flip_subst[simp]:    "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
  and    flip_subst_subst[simp]: "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
begin

lemmas flip_subst_b = flip_subst_subst

lemma subst_b_simple_commute:
  fixes x::bv
  assumes "atom x \<sharp> c" 
  shows "(c[z::=B_var x]\<^sub>b)[x::=b]\<^sub>b = c[z::=b]\<^sub>b" 
proof - 
  have "(c[z::=B_var x]\<^sub>b)[x::=b]\<^sub>b = (( x \<leftrightarrow> z) \<bullet> c)[x::=b]\<^sub>b" using flip_subst assms by simp
  thus ?thesis using flip_subst_subst assms by simp
qed

lemma subst_b_flip_eq_one:
  fixes z1::bv and z2::bv and x1::bv and x2::bv  
  assumes "[[atom z1]]lst. c1 = [[atom z2]]lst. c2" 
    and "atom x1 \<sharp> (z1,z2,c1,c2)"
  shows "(c1[z1::=B_var x1]\<^sub>b) = (c2[z2::=B_var x1]\<^sub>b)"
proof -  
  have "(c1[z1::=B_var x1]\<^sub>b) = (x1 \<leftrightarrow> z1) \<bullet> c1" using assms flip_subst by auto
  moreover have  "(c2[z2::=B_var x1]\<^sub>b) = (x1 \<leftrightarrow> z2) \<bullet> c2" using assms flip_subst by auto
  ultimately show ?thesis using Abs1_eq_iff_all(3)[of z1 c1 z2 c2 z1]  assms 
    by (metis Abs1_eq_iff_fresh(3) flip_commute)
qed

lemma subst_b_flip_eq_two:
  fixes z1::bv and z2::bv and x1::bv and x2::bv  
  assumes "[[atom z1]]lst. c1 = [[atom z2]]lst. c2" 
  shows "(c1[z1::=b]\<^sub>b) = (c2[z2::=b]\<^sub>b)"
proof -
  obtain x::bv where *:"atom x \<sharp> (z1,z2,c1,c2)" using obtain_fresh by metis
  hence "(c1[z1::=B_var x]\<^sub>b) = (c2[z2::=B_var x]\<^sub>b)" using subst_b_flip_eq_one[OF assms, of x] by metis
  hence "(c1[z1::=B_var x]\<^sub>b)[x::=b]\<^sub>b = (c2[z2::=B_var x]\<^sub>b)[x::=b]\<^sub>b" by auto
  thus ?thesis using subst_b_simple_commute * fresh_prod4 by metis
qed

lemma subst_b_fresh_x:
  fixes tm::"'a::fs" and x::x
  shows "atom x \<sharp> tm = atom x \<sharp> tm[bv::=b']\<^sub>b"
  using fresh_subst_if[of "atom x" tm bv b'] using x_fresh_b by auto

lemma subst_b_x_flip[simp]:
  fixes x'::x and x::x and bv::bv 
  shows "((x' \<leftrightarrow> x) \<bullet> tm)[bv::=b']\<^sub>b = (x' \<leftrightarrow> x) \<bullet> (tm[bv::=b']\<^sub>b)"
proof - 
  have "(x' \<leftrightarrow> x) \<bullet> bv = bv" using pure_supp flip_fresh_fresh by force
  moreover have "(x' \<leftrightarrow> x) \<bullet> b' = b'" using x_fresh_b flip_fresh_fresh by auto
  ultimately show ?thesis using eqvt by simp
qed

end

section \<open>Base Type\<close>

nominal_function subst_bb :: "b \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> b" where
  "subst_bb  (B_var bv2) bv1 b  = (if bv1 = bv2 then b else (B_var bv2))"
| "subst_bb  B_int bv1 b  = B_int"
| "subst_bb B_bool bv1 b = B_bool"
| "subst_bb (B_id s) bv1 b = B_id s "
| "subst_bb (B_pair b1 b2) bv1 b = B_pair (subst_bb b1 bv1 b) (subst_bb b2 bv1 b)"
| "subst_bb B_unit bv1 b = B_unit  "
| "subst_bb B_bitvec bv1 b = B_bitvec "
| "subst_bb (B_app s b2) bv1 b = B_app s (subst_bb b2 bv1 b)"
                      apply (simp add: eqvt_def subst_bb_graph_aux_def )
                      apply (simp add: eqvt_def subst_bb_graph_aux_def )
  by (auto,meson b.strong_exhaust)
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_bb_abbrev :: "b \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> b" ("_[_::=_]\<^sub>b\<^sub>b" [1000,50,50] 1000)
  where 
    "b[bv::=b']\<^sub>b\<^sub>b  \<equiv> subst_bb b bv b' " 

instantiation b :: has_subst_b
begin
definition "subst_b = subst_bb"

instance proof
  fix j::atom and i::bv and  x::b and t::b
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  proof (induct t rule: b.induct)
    case (B_id x)
    then show ?case using subst_bb.simps fresh_def pure_fresh subst_b_b_def by auto
  next
    case (B_var x)
    then show ?case using subst_bb.simps fresh_def pure_fresh subst_b_b_def by auto
  next
    case (B_app x1 x2)
    then show ?case using subst_bb.simps fresh_def pure_fresh subst_b_b_def by auto
  qed(auto simp add: subst_bb.simps fresh_def pure_fresh subst_b_b_def)+

  fix a::bv and tm::b and x::b
  show "atom a \<sharp> tm \<Longrightarrow> tm[a::=x]\<^sub>b = tm"
    by (induct tm rule: b.induct, auto simp add: fresh_at_base subst_bb.simps subst_b_b_def)

  fix a::bv and tm::b
  show "subst_b tm a (B_var a) = tm" using subst_bb.simps  subst_b_b_def 
    by (induct tm rule: b.induct, auto simp add: fresh_at_base subst_bb.simps subst_b_b_def)

  fix p::perm and x1::bv and v::b and t1::b
  show "p \<bullet> subst_b t1 x1 v  = subst_b  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    by (induct tm rule: b.induct, auto simp add: fresh_at_base subst_bb.simps subst_b_b_def)

  fix  bv::bv and c::b and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    by (induct c rule: b.induct,  (auto simp add: fresh_at_base subst_bb.simps subst_b_b_def permute_pure pure_supp )+)

  fix bv::bv and c::b and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
    by (induct c rule: b.induct,  (auto simp add: fresh_at_base subst_bb.simps subst_b_b_def permute_pure pure_supp )+)
qed
end

lemma subst_bb_inject:
  assumes "b1 = b2[bv::=b]\<^sub>b\<^sub>b" and "b2 \<noteq> B_var bv" 
  shows 
    "b1 = B_int \<Longrightarrow> b2 = B_int" and 
    "b1 = B_bool \<Longrightarrow> b2 = B_bool" and 
    "b1 = B_unit \<Longrightarrow> b2 = B_unit" and 
    "b1 = B_bitvec \<Longrightarrow> b2 = B_bitvec" and 
    "b1 = B_pair b11 b12 \<Longrightarrow> (\<exists>b11' b12' . b11 = b11'[bv::=b]\<^sub>b\<^sub>b \<and> b12 = b12'[bv::=b]\<^sub>b\<^sub>b \<and> b2 = B_pair b11' b12')" and
    "b1 = B_var bv' \<Longrightarrow> b2 = B_var bv'" and
    "b1 = B_id tyid  \<Longrightarrow> b2 = B_id tyid" and
    "b1 = B_app tyid b11 \<Longrightarrow> (\<exists>b11'. b11= b11'[bv::=b]\<^sub>b\<^sub>b \<and> b2 = B_app tyid b11')"
  using assms by(nominal_induct b2 rule:b.strong_induct,auto+)

lemma flip_b_subst4:
  fixes b1::b and bv1::bv and c::bv and b::b
  assumes "atom c \<sharp> (b1,bv1)" 
  shows "b1[bv1::=b]\<^sub>b\<^sub>b = ((bv1 \<leftrightarrow> c) \<bullet> b1)[c ::= b]\<^sub>b\<^sub>b" 
  using assms proof(nominal_induct b1 rule: b.strong_induct)
  case B_int
  then show ?case using subst_bb.simps b.perm_simps by auto
next
  case B_bool
  then show ?case using subst_bb.simps b.perm_simps by auto
next
  case (B_id x)
  hence "atom bv1 \<sharp> x \<and> atom c \<sharp> x" using fresh_def  pure_supp by auto
  hence "((bv1 \<leftrightarrow> c) \<bullet> B_id x) = B_id x" using fresh_Pair b.fresh(3) flip_fresh_fresh b.perm_simps fresh_def pure_supp by metis
  then show ?case using subst_bb.simps by simp
next
  case (B_pair x1 x2)
  hence "x1[bv1::=b]\<^sub>b\<^sub>b = ((bv1 \<leftrightarrow> c) \<bullet> x1)[c::=b]\<^sub>b\<^sub>b" using  b.perm_simps(4) b.fresh(4) fresh_Pair  by metis
  moreover have  "x2[bv1::=b]\<^sub>b\<^sub>b = ((bv1 \<leftrightarrow> c) \<bullet> x2)[c::=b]\<^sub>b\<^sub>b" using  b.perm_simps(4) b.fresh(4) fresh_Pair B_pair by metis
  ultimately  show ?case using subst_bb.simps(5) b.perm_simps(4) b.fresh(4) fresh_Pair by auto
next
  case B_unit
  then show ?case using subst_bb.simps b.perm_simps by auto
next
  case B_bitvec
  then show ?case using subst_bb.simps b.perm_simps by auto
next
  case (B_var x)
  then show ?case proof(cases "x=bv1")
    case True
    then show ?thesis using B_var subst_bb.simps b.perm_simps by simp
  next
    case False
    moreover have "x\<noteq>c" using B_var b.fresh fresh_def supp_at_base fresh_Pair by fastforce
    ultimately show ?thesis using B_var subst_bb.simps(1) b.perm_simps(7) by simp
  qed
next
  case (B_app x1 x2)
  hence "x2[bv1::=b]\<^sub>b\<^sub>b = ((bv1 \<leftrightarrow> c) \<bullet> x2)[c::=b]\<^sub>b\<^sub>b" using  b.perm_simps b.fresh fresh_Pair  by metis 
  thus ?case using subst_bb.simps b.perm_simps b.fresh fresh_Pair B_app 
    by (simp add: permute_pure)
qed

lemma subst_bb_flip_sym:
  fixes b1::b and b2::b
  assumes "atom c \<sharp> b" and "atom c \<sharp> (bv1,bv2, b1, b2)" and "(bv1 \<leftrightarrow> c) \<bullet> b1 = (bv2 \<leftrightarrow> c) \<bullet> b2" 
  shows "b1[bv1::=b]\<^sub>b\<^sub>b = b2[bv2::=b]\<^sub>b\<^sub>b"
  using assms  flip_b_subst4[of c b1 bv1 b]   flip_b_subst4[of c b2 bv2 b] fresh_prod4 fresh_Pair by simp

section \<open>Value\<close>

nominal_function subst_vb :: "v \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> v" where
  "subst_vb (V_lit l) x v = V_lit l"
| "subst_vb (V_var y) x v = V_var y"
| "subst_vb (V_cons tyid c v') x v  = V_cons tyid c (subst_vb v' x v)"
| "subst_vb (V_consp tyid c b v') x v  = V_consp tyid c (subst_bb b x v) (subst_vb v' x v)"
| "subst_vb (V_pair v1 v2) x v = V_pair (subst_vb v1 x v ) (subst_vb v2 x v )"
                   apply (simp add: eqvt_def subst_vb_graph_aux_def)
                  apply auto
  using v.strong_exhaust by meson
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_vb_abbrev :: "v \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> v" ("_[_::=_]\<^sub>v\<^sub>b" [1000,50,50] 500)
  where 
    "e[bv::=b]\<^sub>v\<^sub>b  \<equiv> subst_vb e bv b" 

instantiation v :: has_subst_b
begin
definition "subst_b = subst_vb"

instance proof
  fix j::atom and i::bv and  x::b and t::v
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  proof (induct t rule: v.induct)
    case (V_lit l)
    have "j \<sharp> subst_b (V_lit l) i x = j \<sharp> (V_lit l)"  using subst_vb.simps fresh_def pure_fresh 
        subst_b_v_def v.supp  v.fresh has_subst_b_class.fresh_subst_if subst_b_b_def subst_b_v_def by auto
    also have "... = True" using fresh_at_base v.fresh l.fresh supp_l_empty fresh_def by metis      
    moreover have "(atom i \<sharp>  (V_lit l) \<and> j \<sharp>  (V_lit l) \<or> j \<sharp> x \<and> (j \<sharp>  (V_lit l) \<or> j = atom i)) = True" using fresh_at_base v.fresh l.fresh supp_l_empty fresh_def by metis
    ultimately show ?case by simp
  next
    case (V_var y)
    then show ?case using  subst_b_v_def subst_vb.simps pure_fresh by force   
  next
    case (V_pair x1a x2a)
    then show ?case using subst_b_v_def subst_vb.simps by auto  
  next
    case (V_cons x1a x2a x3)       
    then show ?case using V_cons subst_b_v_def subst_vb.simps pure_fresh by force
  next
    case (V_consp x1a x2a x3 x4)
    then show ?case using  subst_b_v_def subst_vb.simps pure_fresh  has_subst_b_class.fresh_subst_if subst_b_b_def subst_b_v_def by fastforce
  qed

  fix a::bv and tm::v and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x = tm"
    apply(induct tm rule: v.induct)
        apply(auto simp add: fresh_at_base subst_vb.simps subst_b_v_def)
    using has_subst_b_class.fresh_subst_if  subst_b_b_def e.fresh 
    using has_subst_b_class.forget_subst by fastforce

  fix a::bv and tm::v
  show "subst_b tm a (B_var a) = tm" using subst_bb.simps  subst_b_b_def 
    apply (induct tm rule: v.induct)
        apply(auto simp add: fresh_at_base subst_vb.simps subst_b_v_def)
    using has_subst_b_class.fresh_subst_if  subst_b_b_def e.fresh 
    using has_subst_b_class.subst_id by metis

  fix p::perm and x1::bv and v::b and t1::v
  show "p \<bullet> subst_b t1 x1 v  = subst_b  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    apply(induct tm rule: v.induct)
        apply(auto simp add: fresh_at_base subst_bb.simps subst_b_b_def )
    using has_subst_b_class.eqvt  subst_b_b_def e.fresh 
    using has_subst_b_class.eqvt 
    by (simp add: subst_b_v_def)+

  fix  bv::bv and c::v and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    apply (induct c rule: v.induct,  (auto simp add: fresh_at_base  subst_vb.simps subst_b_v_def permute_pure pure_supp )+)
     apply (metis flip_fresh_fresh flip_l_eq permute_flip_cancel2)
    using  fresh_at_base flip_fresh_fresh[of bv  x z] 
    apply (simp add: flip_fresh_fresh)
    using subst_b_b_def by argo

  fix bv::bv and c::v and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
    apply (induct c rule: v.induct,  (auto simp add: fresh_at_base  subst_vb.simps subst_b_v_def permute_pure pure_supp )+)
     apply (metis flip_fresh_fresh flip_l_eq permute_flip_cancel2)
    using  fresh_at_base flip_fresh_fresh[of bv  x z] 
    apply (simp add: flip_fresh_fresh)
    using     subst_b_b_def  flip_subst_subst by fastforce

qed
end

section \<open>Constraints Expressions\<close>

nominal_function subst_ceb :: "ce \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> ce" where
  "subst_ceb  ( (CE_val v') ) bv b = ( CE_val (subst_vb v' bv b) )"
| "subst_ceb  ( (CE_op opp v1 v2) ) bv b = ( (CE_op opp (subst_ceb v1 bv b)(subst_ceb v2 bv b)) )"
| "subst_ceb  ( (CE_fst v')) bv b = CE_fst (subst_ceb v' bv b)"
| "subst_ceb  ( (CE_snd v')) bv b = CE_snd (subst_ceb v' bv b)"
| "subst_ceb  ( (CE_len v')) bv b = CE_len (subst_ceb v' bv b)"
| "subst_ceb  ( CE_concat v1 v2) bv b = CE_concat (subst_ceb v1 bv b) (subst_ceb v2 bv b)"
                      apply (simp add: eqvt_def subst_ceb_graph_aux_def)
                      apply auto
  by (meson ce.strong_exhaust)
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_ceb_abbrev :: "ce \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> ce" ("_[_::=_]\<^sub>c\<^sub>e\<^sub>b" [1000,50,50] 500)
  where 
    "ce[bv::=b]\<^sub>c\<^sub>e\<^sub>b  \<equiv> subst_ceb ce bv b" 

instantiation ce :: has_subst_b
begin
definition "subst_b = subst_ceb"

instance proof
  fix j::atom and i::bv and  x::b and t::ce
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  proof (induct t rule: ce.induct)
    case (CE_val v)
    then show ?case using subst_ceb.simps fresh_def pure_fresh subst_b_ce_def ce.supp v.supp  ce.fresh has_subst_b_class.fresh_subst_if subst_b_b_def subst_b_v_def
      by metis
  next
    case (CE_op opp v1 v2)    

    have "(j \<sharp> v1[i::=x]\<^sub>c\<^sub>e\<^sub>b \<and> j \<sharp> v2[i::=x]\<^sub>c\<^sub>e\<^sub>b) = ((atom i \<sharp> v1 \<and> atom i \<sharp> v2) \<and> j \<sharp> v1 \<and> j \<sharp> v2 \<or> j \<sharp> x \<and> (j \<sharp> v1 \<and> j \<sharp> v2 \<or> j = atom i))"
      using has_subst_b_class.fresh_subst_if subst_b_v_def 
      using CE_op.hyps(1) CE_op.hyps(2) subst_b_ce_def by auto

    thus ?case  unfolding subst_ceb.simps subst_b_ce_def ce.fresh 
      using fresh_def pure_fresh opp.fresh subst_b_v_def  opp.exhaust fresh_e_opp_all
      by (metis (full_types))      
  next
    case (CE_concat x1a x2)
    then show ?case  using subst_ceb.simps  subst_b_ce_def e.supp v.supp  has_subst_b_class.fresh_subst_if subst_b_v_def  ce.fresh by force
  next
    case (CE_fst x)
    then show ?case using subst_ceb.simps  subst_b_ce_def e.supp v.supp  has_subst_b_class.fresh_subst_if subst_b_v_def  ce.fresh by metis

  next
    case (CE_snd x)
    then show ?case using subst_ceb.simps  subst_b_ce_def e.supp v.supp  has_subst_b_class.fresh_subst_if subst_b_v_def  ce.fresh by metis
  next
    case (CE_len x)
    then show ?case using subst_ceb.simps  subst_b_ce_def e.supp v.supp  has_subst_b_class.fresh_subst_if subst_b_v_def  ce.fresh by metis
  qed

  fix a::bv and tm::ce and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x = tm"
    apply(induct tm rule: ce.induct)
         apply( auto simp add: fresh_at_base subst_ceb.simps subst_b_ce_def)
    using has_subst_b_class.fresh_subst_if  subst_b_b_def e.fresh 
    using has_subst_b_class.forget_subst subst_b_v_def apply metis+
    done

  fix a::bv and tm::ce
  show "subst_b tm a (B_var a) = tm" using subst_bb.simps  subst_b_b_def 
    apply (induct tm rule: ce.induct)
         apply(auto simp add: fresh_at_base subst_ceb.simps subst_b_ce_def)
    using has_subst_b_class.fresh_subst_if  subst_b_b_def e.fresh 
    using has_subst_b_class.subst_id subst_b_v_def apply metis+
    done

  fix p::perm and x1::bv and v::b and t1::ce
  show "p \<bullet> subst_b t1 x1 v  = subst_b  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    apply(induct tm rule: ce.induct)
         apply( auto simp add: fresh_at_base subst_bb.simps subst_b_b_def )
    using has_subst_b_class.eqvt  subst_b_b_def ce.fresh 
    using has_subst_b_class.eqvt 
    by (simp add: subst_b_ce_def)+

  fix  bv::bv and c::ce and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    apply (induct c rule: ce.induct,  (auto simp add: fresh_at_base  subst_ceb.simps subst_b_ce_def permute_pure pure_supp )+)
    using  flip_fresh_fresh flip_l_eq permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_v_def apply metis
    using  flip_fresh_fresh flip_l_eq permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_v_def 
    by (simp add: flip_fresh_fresh fresh_opp_all)  

  fix bv::bv and c::ce and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
  proof (induct c rule: ce.induct)
    case (CE_val x)
    then show ?case using flip_subst_subst subst_b_v_def subst_ceb.simps  using subst_b_ce_def by fastforce
  next
    case (CE_op x1a x2 x3)
    then show ?case unfolding subst_ceb.simps subst_b_ce_def ce.perm_simps using flip_subst_subst subst_b_v_def  opp.perm_simps opp.strong_exhaust 
      by (metis (full_types) ce.fresh(2))
  next
    case (CE_concat x1a x2)
    then show ?case using flip_subst_subst subst_b_v_def subst_ceb.simps  using subst_b_ce_def by fastforce
  next
    case (CE_fst x)
    then show ?case using flip_subst_subst subst_b_v_def subst_ceb.simps  using subst_b_ce_def by fastforce
  next
    case (CE_snd x)
    then show ?case using flip_subst_subst subst_b_v_def subst_ceb.simps  using subst_b_ce_def by fastforce
  next
    case (CE_len x)
    then show ?case using flip_subst_subst subst_b_v_def subst_ceb.simps  using subst_b_ce_def by fastforce
  qed
qed
end

section \<open>Constraints\<close>

nominal_function subst_cb :: "c \<Rightarrow> bv \<Rightarrow> b  \<Rightarrow> c" where
  "subst_cb (C_true) x v = C_true"
|  "subst_cb (C_false) x v = C_false"
|  "subst_cb (C_conj c1 c2) x v = C_conj (subst_cb c1 x v ) (subst_cb c2 x v )"
|  "subst_cb (C_disj c1 c2) x v = C_disj (subst_cb c1 x v ) (subst_cb c2 x v )"
|  "subst_cb (C_imp c1 c2) x v = C_imp (subst_cb c1 x v ) (subst_cb c2 x v )"
|  "subst_cb (C_eq e1 e2) x v = C_eq (subst_ceb e1 x v ) (subst_ceb e2 x v )"
|  "subst_cb (C_not c) x v = C_not (subst_cb c x v )"
                      apply (simp add: eqvt_def subst_cb_graph_aux_def)
                      apply auto 
  using c.strong_exhaust apply metis
  done
nominal_termination (eqvt)  by lexicographic_order

abbreviation 
  subst_cb_abbrev :: "c \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> c" ("_[_::=_]\<^sub>c\<^sub>b" [1000,50,50] 500)
  where 
    "c[bv::=b]\<^sub>c\<^sub>b  \<equiv> subst_cb c bv b" 

instantiation c :: has_subst_b
begin
definition "subst_b = subst_cb"

instance proof
  fix j::atom and i::bv and  x::b and t::c
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
    by (induct t rule: c.induct, unfold subst_cb.simps subst_b_c_def c.fresh,
        (metis has_subst_b_class.fresh_subst_if subst_b_ce_def c.fresh)+
        )

  fix a::bv and tm::c and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x = tm"
    by(induct tm rule: c.induct, unfold subst_cb.simps subst_b_c_def c.fresh,
        (metis has_subst_b_class.forget_subst subst_b_ce_def)+)

  fix a::bv and tm::c
  show "subst_b tm a (B_var a) = tm" using subst_bb.simps  subst_b_c_def 
    by(induct tm rule: c.induct, unfold subst_cb.simps subst_b_c_def c.fresh,
        (metis has_subst_b_class.subst_id subst_b_ce_def)+)

  fix p::perm and x1::bv and v::b and t1::c
  show "p \<bullet> subst_b t1 x1 v  = subst_b  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    apply(induct tm rule: c.induct,unfold subst_cb.simps subst_b_c_def c.fresh)
    by( auto simp add: fresh_at_base subst_bb.simps subst_b_b_def )

  fix  bv::bv and c::c and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    apply (induct c rule: c.induct,  (auto simp add: fresh_at_base  subst_cb.simps subst_b_c_def permute_pure pure_supp )+)
    using  flip_fresh_fresh flip_l_eq permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_ce_def apply metis
    using  flip_fresh_fresh flip_l_eq permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_ce_def 
    apply (metis opp.perm_simps(2) opp.strong_exhaust)+
    done

  fix bv::bv and c::c and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
    apply (induct c rule: c.induct,  (auto simp add: fresh_at_base  subst_cb.simps subst_b_c_def permute_pure pure_supp )+)
    using flip_fresh_fresh flip_l_eq permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_ce_def 
    using flip_subst_subst apply fastforce
    using  flip_fresh_fresh flip_l_eq permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_ce_def 
      opp.perm_simps(2) opp.strong_exhaust 
  proof -
    fix x1a :: ce and x2 :: ce
    assume a1: "atom bv \<sharp> x2"
    then have "((bv \<leftrightarrow> z) \<bullet> x2)[bv::=v]\<^sub>b = x2[z::=v]\<^sub>b"
      by (metis flip_subst_subst) (* 0.0 ms *)
    then show "x2[z::=B_var bv]\<^sub>b[bv::=v]\<^sub>c\<^sub>e\<^sub>b = x2[z::=v]\<^sub>c\<^sub>e\<^sub>b"
      using a1 by (simp add: subst_b_ce_def) (* 0.0 ms *)
  qed

qed
end

section \<open>Types\<close>

nominal_function subst_tb :: "\<tau> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<tau>" where
  "subst_tb  (\<lbrace> z : b2 | c \<rbrace>) bv1 b1 = \<lbrace> z : b2[bv1::=b1]\<^sub>b\<^sub>b | c[bv1::=b1]\<^sub>c\<^sub>b \<rbrace>"
proof(goal_cases)
  case 1
  then show ?case using eqvt_def subst_tb_graph_aux_def by force
next
  case (2 x y)
  then show ?case by auto
next
  case (3 P x)
  then show ?case using eqvt_def subst_tb_graph_aux_def \<tau>.strong_exhaust 
    by (metis b_of.cases prod_cases3)
next
  case (4 z' b2' c' bv1' b1' z b2 c bv1 b1)
  show ?case unfolding \<tau>.eq_iff proof
    have *:"[[atom z']]lst. c' = [[atom z]]lst. c" using  \<tau>.eq_iff 4 by auto
    show "[[atom z']]lst. c'[bv1'::=b1']\<^sub>c\<^sub>b = [[atom z]]lst. c[bv1::=b1]\<^sub>c\<^sub>b" 
    proof(subst Abs1_eq_iff_all(3),rule,rule,rule)
      fix ca::x
      assume "atom ca \<sharp> z" and 1:"atom ca \<sharp> (z', z, c'[bv1'::=b1']\<^sub>c\<^sub>b, c[bv1::=b1]\<^sub>c\<^sub>b)" 
      hence 2:"atom ca \<sharp> (c',c)" using fresh_subst_if subst_b_c_def fresh_Pair fresh_prod4 fresh_at_base subst_b_fresh_x by metis
      hence "(z' \<leftrightarrow> ca) \<bullet> c' = (z \<leftrightarrow> ca) \<bullet> c"  using 1 2 * Abs1_eq_iff_all(3) by auto
      hence "((z' \<leftrightarrow> ca) \<bullet> c')[bv1'::=b1']\<^sub>c\<^sub>b = ((z \<leftrightarrow> ca) \<bullet> c)[bv1'::=b1']\<^sub>c\<^sub>b" by auto      
      hence "(z' \<leftrightarrow> ca) \<bullet> c'[(z' \<leftrightarrow> ca) \<bullet> bv1'::=(z' \<leftrightarrow> ca) \<bullet> b1']\<^sub>c\<^sub>b = (z \<leftrightarrow> ca) \<bullet> c[(z \<leftrightarrow> ca) \<bullet> bv1'::=(z \<leftrightarrow> ca) \<bullet> b1']\<^sub>c\<^sub>b" by auto  
      thus "(z' \<leftrightarrow> ca) \<bullet> c'[bv1'::=b1']\<^sub>c\<^sub>b = (z \<leftrightarrow> ca) \<bullet> c[bv1::=b1]\<^sub>c\<^sub>b" using  4  flip_x_b_cancel by simp
    qed
    show "b2'[bv1'::=b1']\<^sub>b\<^sub>b = b2[bv1::=b1]\<^sub>b\<^sub>b" using 4 by simp
  qed
qed

nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_tb_abbrev :: "\<tau> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<tau>" ("_[_::=_]\<^sub>\<tau>\<^sub>b" [1000,50,50] 1000)
  where 
    "t[bv::=b']\<^sub>\<tau>\<^sub>b  \<equiv> subst_tb t bv b' " 

instantiation \<tau> :: has_subst_b
begin
definition "subst_b = subst_tb"

instance proof
  fix j::atom and i::bv and  x::b and t::\<tau>
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  proof (nominal_induct t avoiding: i x j rule: \<tau>.strong_induct)
    case (T_refined_type z b c)
    then show ?case
      unfolding subst_b_\<tau>_def  subst_tb.simps \<tau>.fresh
      using fresh_subst_if[of j b i x ] subst_b_b_def subst_b_c_def
      by (metis has_subst_b_class.fresh_subst_if list.distinct(1) list.set_cases not_self_fresh set_ConsD)
  qed

  fix a::bv and tm::\<tau> and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x  = tm"
  proof (nominal_induct tm avoiding: a x rule: \<tau>.strong_induct)
    case (T_refined_type xx bb cc )
    moreover hence "atom a \<sharp> bb \<and> atom a \<sharp> cc" using \<tau>.fresh by auto
    ultimately show   ?case  
      unfolding  subst_b_\<tau>_def subst_tb.simps 
      using forget_subst subst_b_b_def subst_b_c_def forget_subst \<tau>.fresh by metis
  qed

  fix a::bv and tm::\<tau>
  show "subst_b tm a (B_var a) = tm" 
  proof (nominal_induct tm rule: \<tau>.strong_induct)
    case (T_refined_type xx bb cc)
    thus  ?case  
      unfolding  subst_b_\<tau>_def subst_tb.simps 
      using subst_id subst_b_b_def subst_b_c_def by metis
  qed

  fix p::perm and x1::bv and v::b and t1::\<tau>
  show "p \<bullet> subst_b t1 x1 v = subst_b (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v) " 
    by (induct tm rule: \<tau>.induct, auto simp add: fresh_at_base subst_tb.simps subst_b_\<tau>_def subst_bb.simps subst_b_b_def)

  fix  bv::bv and c::\<tau> and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    apply (induct c rule: \<tau>.induct,  (auto simp add: fresh_at_base  subst_ceb.simps subst_b_ce_def permute_pure pure_supp )+)
    using  flip_fresh_fresh permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_c_def  subst_b_b_def 
    by (simp add: flip_fresh_fresh subst_b_\<tau>_def)

  fix bv::bv and c::\<tau> and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
  proof (induct c rule: \<tau>.induct)
    case (T_refined_type x1a x2a x3a)
    hence "atom bv \<sharp> x2a \<and> atom bv \<sharp> x3a \<and> atom bv \<sharp> x1a" using fresh_at_base \<tau>.fresh by simp
    then show ?case 
      unfolding subst_tb.simps subst_b_\<tau>_def \<tau>.perm_simps 
      using fresh_at_base flip_fresh_fresh[of bv x1a z] flip_subst_subst subst_b_b_def  subst_b_c_def T_refined_type 
    proof -
      have "atom z \<sharp> x1a"
        by (metis b.fresh(7) fresh_at_base(2) x_fresh_b) (* 0.0 ms *)
      then show "\<lbrace> (bv \<leftrightarrow> z) \<bullet> x1a : ((bv \<leftrightarrow> z) \<bullet> x2a)[bv::=v]\<^sub>b\<^sub>b | ((bv \<leftrightarrow> z) \<bullet> x3a)[bv::=v]\<^sub>c\<^sub>b \<rbrace> = \<lbrace> x1a : x2a[z::=v]\<^sub>b\<^sub>b | x3a[z::=v]\<^sub>c\<^sub>b \<rbrace>"
        by (metis \<open>\<lbrakk>atom bv \<sharp> x1a; atom z \<sharp> x1a\<rbrakk> \<Longrightarrow> (bv \<leftrightarrow> z) \<bullet> x1a = x1a\<close> \<open>atom bv \<sharp> x2a \<and> atom bv \<sharp> x3a \<and> atom bv \<sharp> x1a\<close> flip_subst_subst subst_b_b_def subst_b_c_def) (* 78 ms *)
    qed 
  qed

qed
end

lemma subst_bb_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (subst_bb (subst_bb A i t ) j u ) = subst_bb A i (subst_bb t j u) "
  by (nominal_induct A avoiding: i j t u rule: b.strong_induct) (auto simp: fresh_at_base)

lemma subst_vb_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (subst_vb  (subst_vb A i t )) j u = subst_vb A i (subst_bb t j u ) "
  by (nominal_induct A avoiding: i j t u rule: v.strong_induct) (auto simp: fresh_at_base)

lemma subst_ceb_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (subst_ceb  (subst_ceb A i t )) j u = subst_ceb A i (subst_bb t j u ) "
  by (nominal_induct A avoiding: i j t u rule: ce.strong_induct) (auto simp: fresh_at_base)

lemma subst_cb_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (subst_cb  (subst_cb A i t )) j u = subst_cb A i (subst_bb t j u ) "
  by (nominal_induct A avoiding: i j t u rule: c.strong_induct) (auto simp: fresh_at_base)

lemma subst_tb_commute [simp]:
  "atom j \<sharp> A \<Longrightarrow> (subst_tb  (subst_tb A i t )) j u = subst_tb A i (subst_bb t j u ) "
proof (nominal_induct A avoiding: i j t u rule: \<tau>.strong_induct)
  case (T_refined_type z b c)
  then show ?case using subst_tb.simps subst_bb_commute subst_cb_commute by simp
qed

section \<open>Expressions\<close>

nominal_function subst_eb :: "e \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> e" where
  "subst_eb ( (AE_val v')) bv b  = ( AE_val (subst_vb v' bv b))"
| "subst_eb ( (AE_app f v') ) bv b = ( (AE_app f (subst_vb v' bv b)) )"                
| "subst_eb ( (AE_appP f b' v') ) bv b = ( (AE_appP f (b'[bv::=b]\<^sub>b\<^sub>b) (subst_vb v' bv b)))"   
| "subst_eb ( (AE_op opp v1 v2) ) bv b = ( (AE_op opp (subst_vb v1 bv b) (subst_vb v2 bv b)) )"
| "subst_eb ( (AE_fst v')) bv b = AE_fst (subst_vb v' bv b)"
| "subst_eb ( (AE_snd v')) bv b = AE_snd (subst_vb v' bv b)"
| "subst_eb ( (AE_mvar u)) bv b = AE_mvar u"
| "subst_eb ( (AE_len v')) bv b = AE_len (subst_vb v' bv b)"
| "subst_eb ( AE_concat v1 v2) bv b = AE_concat (subst_vb v1 bv b) (subst_vb v2 bv b)"
| "subst_eb ( AE_split v1 v2) bv b = AE_split (subst_vb v1 bv b) (subst_vb v2 bv b)"
                      apply (simp add: eqvt_def subst_eb_graph_aux_def)
                      apply auto
  by (meson e.strong_exhaust)
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_eb_abbrev :: "e \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> e" ("_[_::=_]\<^sub>e\<^sub>b" [1000,50,50] 500)
  where 
    "e[bv::=b]\<^sub>e\<^sub>b  \<equiv> subst_eb e bv b" 

instantiation e :: has_subst_b
begin
definition "subst_b = subst_eb"

instance proof
  fix j::atom and i::bv and  x::b and t::e
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  proof (induct t rule: e.induct)
    case (AE_val v)
    then show ?case using subst_eb.simps fresh_def pure_fresh subst_b_e_def e.supp v.supp  
        e.fresh has_subst_b_class.fresh_subst_if subst_b_e_def subst_b_v_def
      by metis
  next
    case (AE_app f v)
    then show ?case using subst_eb.simps fresh_def pure_fresh subst_b_e_def 
        e.supp v.supp  has_subst_b_class.fresh_subst_if subst_b_v_def 
      by (metis (mono_tags, hide_lams) e.fresh(2))
  next
    case (AE_appP f b' v)
    then show ?case unfolding subst_eb.simps   subst_b_e_def e.fresh using
        fresh_def pure_fresh subst_b_e_def e.supp v.supp
        e.fresh has_subst_b_class.fresh_subst_if subst_b_b_def subst_vb_def   by (metis subst_b_v_def)
  next
    case (AE_op opp v1 v2)
    then show ?case unfolding subst_eb.simps   subst_b_e_def e.fresh using
        fresh_def pure_fresh subst_b_e_def e.supp v.supp fresh_e_opp_all
        e.fresh has_subst_b_class.fresh_subst_if subst_b_b_def subst_vb_def   by (metis subst_b_v_def)  
  next
    case (AE_concat x1a x2)
    then show ?case using subst_eb.simps fresh_def pure_fresh subst_b_e_def e.supp v.supp  
        has_subst_b_class.fresh_subst_if subst_b_v_def 
      by (metis subst_vb.simps(5))
  next
    case (AE_split x1a x2)
    then show ?case using subst_eb.simps fresh_def pure_fresh subst_b_e_def e.supp v.supp  
        has_subst_b_class.fresh_subst_if subst_b_v_def 
      by (metis subst_vb.simps(5))
  next
    case (AE_fst x)
    then show ?case using subst_eb.simps fresh_def pure_fresh subst_b_e_def e.supp v.supp  has_subst_b_class.fresh_subst_if subst_b_v_def  by metis
  next
    case (AE_snd x)
    then show ?case using subst_eb.simps fresh_def pure_fresh subst_b_e_def e.supp v.supp using  has_subst_b_class.fresh_subst_if subst_b_v_def  by metis
  next
    case (AE_mvar x)
    then show ?case using subst_eb.simps fresh_def pure_fresh subst_b_e_def e.supp v.supp  by auto
  next
    case (AE_len x)
    then show ?case using subst_eb.simps fresh_def pure_fresh subst_b_e_def e.supp v.supp   using  has_subst_b_class.fresh_subst_if subst_b_v_def  by metis
  qed

  fix a::bv and tm::e and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x = tm"
    apply(induct tm rule: e.induct)
             apply( auto simp add: fresh_at_base subst_eb.simps subst_b_e_def)
    using has_subst_b_class.fresh_subst_if  subst_b_b_def e.fresh 
    using has_subst_b_class.forget_subst subst_b_v_def apply metis+
    done

  fix a::bv and tm::e
  show "subst_b tm a (B_var a) = tm" using subst_bb.simps  subst_b_b_def 
    apply (induct tm rule: e.induct)
             apply(auto simp add: fresh_at_base subst_eb.simps subst_b_e_def)
    using has_subst_b_class.fresh_subst_if  subst_b_b_def e.fresh 
    using has_subst_b_class.subst_id subst_b_v_def apply metis+
    done

  fix p::perm and x1::bv and v::b and t1::e
  show "p \<bullet> subst_b t1 x1 v  = subst_b  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
    apply(induct tm rule: e.induct)
             apply( auto simp add: fresh_at_base subst_bb.simps subst_b_b_def )
    using has_subst_b_class.eqvt  subst_b_b_def e.fresh 
    using has_subst_b_class.eqvt 
    by (simp add: subst_b_e_def)+

  fix  bv::bv and c::e and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    apply (induct c rule: e.induct)
             apply(auto simp add: fresh_at_base  subst_eb.simps subst_b_e_def subst_b_v_def  permute_pure pure_supp )
    using  flip_fresh_fresh permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_v_def  subst_b_b_def 
      flip_fresh_fresh subst_b_\<tau>_def apply metis
    apply (metis (full_types) opp.perm_simps  opp.strong_exhaust)
    done

  fix bv::bv and c::e and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
    apply (induct c rule: e.induct)
             apply(auto simp add: fresh_at_base  subst_eb.simps subst_b_e_def subst_b_v_def  permute_pure pure_supp )
    using  flip_fresh_fresh permute_flip_cancel2 has_subst_b_class.flip_subst subst_b_v_def  subst_b_b_def 
      flip_fresh_fresh subst_b_\<tau>_def apply simp

    apply (metis (full_types) opp.perm_simps  opp.strong_exhaust)
    done
qed
end

section \<open>Statements\<close>

nominal_function (default "case_sum (\<lambda>x. Inl undefined) (case_sum (\<lambda>x. Inl undefined) (\<lambda>x. Inr undefined))")
  subst_sb :: "s \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> s"
  and subst_branchb :: "branch_s \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> branch_s" 
  and subst_branchlb :: "branch_list \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> branch_list"
  where
    "subst_sb (AS_val v') bv b         = (AS_val (subst_vb v' bv b))"
  | "subst_sb  (AS_let y  e s)  bv b   = (AS_let y  (e[bv::=b]\<^sub>e\<^sub>b) (subst_sb s bv b ))"  
  | "subst_sb (AS_let2 y t s1 s2) bv b = (AS_let2 y (subst_tb t bv b) (subst_sb s1 bv b ) (subst_sb s2 bv b))"  
  | "subst_sb (AS_match v'  cs) bv b   = AS_match  (subst_vb v' bv b)  (subst_branchlb cs bv b)"
  | "subst_sb  (AS_assign y v') bv b   = AS_assign y (subst_vb v' bv b)"
  | "subst_sb  (AS_if v' s1 s2) bv b   = (AS_if (subst_vb v' bv b) (subst_sb s1 bv b ) (subst_sb s2 bv b ) )"  
  | "subst_sb  (AS_var u \<tau> v' s) bv b  = AS_var u (subst_tb  \<tau> bv b)  (subst_vb v' bv b) (subst_sb s bv b )"
  | "subst_sb  (AS_while s1 s2) bv b   = AS_while (subst_sb s1 bv b  ) (subst_sb s2 bv b )"
  | "subst_sb  (AS_seq s1 s2)  bv b    = AS_seq (subst_sb s1 bv b ) (subst_sb s2 bv b )"
  | "subst_sb  (AS_assert c s)  bv b   = AS_assert (subst_cb c bv b ) (subst_sb s bv b )"

| "subst_branchb (AS_branch dc x1 s') bv b = AS_branch dc x1 (subst_sb s' bv b)"

| "subst_branchlb  (AS_final sb)  bv b     = AS_final (subst_branchb sb bv b )"
| "subst_branchlb  (AS_cons sb ssb) bv b   = AS_cons (subst_branchb sb bv b) (subst_branchlb ssb bv b)"

                      apply (simp add: eqvt_def subst_sb_subst_branchb_subst_branchlb_graph_aux_def )                    
                      apply (auto,metis s_branch_s_branch_list.exhaust s_branch_s_branch_list.exhaust(2) old.sum.exhaust surj_pair)

proof(goal_cases)

  have eqvt_at_proj: "\<And> s xa va . eqvt_at subst_sb_subst_branchb_subst_branchlb_sumC (Inl (s, xa, va)) \<Longrightarrow> 
           eqvt_at (\<lambda>a. projl (subst_sb_subst_branchb_subst_branchlb_sumC (Inl a))) (s, xa, va)"
    apply(simp only: eqvt_at_def)
    apply(rule)
    apply(subst Projl_permute)
     apply(thin_tac _)+
     apply(simp add: subst_sb_subst_branchb_subst_branchlb_sumC_def)
     apply(simp add: THE_default_def)
     apply(case_tac "Ex1 (subst_sb_subst_branchb_subst_branchlb_graph (Inl (s,xa,va)))")
      apply simp
      apply(auto)[1]
      apply(erule_tac x="x" in allE)
      apply simp
      apply(cases rule: subst_sb_subst_branchb_subst_branchlb_graph.cases)    
                   apply(assumption)
                  apply(rule_tac x="Sum_Type.projl x" in exI,clarify,rule the1_equality,blast,simp (no_asm) only: sum.sel)+
        apply(blast)+
    apply(simp)+      
    done
  {
    case (1 y s bv b ya sa c)
    moreover have  "atom y \<sharp> (bv, b) \<and> atom ya \<sharp> (bv, b)" using x_fresh_b x_fresh_bv fresh_Pair by simp  
    ultimately show ?case 
      using eqvt_triple eqvt_at_proj by metis
  next
    case (2 y s1 s2 bv b ya s2a c)
    moreover have  "atom y \<sharp> (bv, b) \<and> atom ya \<sharp> (bv, b)" using x_fresh_b x_fresh_bv   fresh_Pair by simp
    ultimately show ?case 
      using eqvt_triple eqvt_at_proj by metis
  next
    case (3 u s bv b ua sa c)
    moreover have  "atom u \<sharp> (bv, b) \<and> atom ua \<sharp> (bv, b)" using x_fresh_b x_fresh_bv   fresh_Pair by simp
    ultimately show ?case using eqvt_triple eqvt_at_proj by metis
  next
    case (4 x1 s' bv b x1a s'a c)
    moreover have  "atom x1 \<sharp> (bv, b) \<and> atom x1a \<sharp> (bv, b)" using x_fresh_b x_fresh_bv   fresh_Pair by simp
    ultimately show ?case using eqvt_triple eqvt_at_proj by metis
  }
qed

nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_sb_abbrev :: "s \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> s" ("_[_::=_]\<^sub>s\<^sub>b" [1000,50,50] 1000)
  where 
    "b[bv::=b']\<^sub>s\<^sub>b  \<equiv> subst_sb b bv b'" 

lemma fresh_subst_sb_if [simp]: 
  "(j \<sharp> (subst_sb A i x  ))  = ((atom i \<sharp> A \<and> j \<sharp> A) \<or> (j \<sharp> x \<and> (j \<sharp> A \<or> j = atom i)))" and
  "(j \<sharp> (subst_branchb B i x  ))  = ((atom i \<sharp> B \<and> j \<sharp> B) \<or> (j \<sharp> x \<and> (j \<sharp> B \<or> j = atom i)))"  and
  "(j \<sharp> (subst_branchlb C i x  ))  = ((atom i \<sharp> C \<and> j \<sharp> C) \<or> (j \<sharp> x \<and> (j \<sharp> C \<or> j = atom i)))"  
proof (nominal_induct A and B and C avoiding: i x rule: s_branch_s_branch_list.strong_induct)
  case (AS_branch x1 x2 x3)
  have " (j \<sharp> subst_branchb (AS_branch x1 x2 x3) i x ) =  (j \<sharp> (AS_branch x1 x2 (subst_sb x3 i x)))" by auto
  also have "... = ((j \<sharp> x3[i::=x]\<^sub>s\<^sub>b \<or> j \<in> set [atom x2]) \<and> j \<sharp> x1)" using s_branch_s_branch_list.fresh by auto
  also have "...  = ((atom i \<sharp> AS_branch x1 x2 x3 \<and> j \<sharp> AS_branch x1 x2 x3) \<or> j \<sharp> x \<and> (j \<sharp> AS_branch x1 x2 x3 \<or> j = atom i))"  
    using subst_branchb.simps(1) s_branch_s_branch_list.fresh(1)  fresh_at_base has_subst_b_class.fresh_subst_if list.distinct list.set_cases set_ConsD subst_b_\<tau>_def 
      v.fresh AS_branch
  proof -
    have f1: "\<forall>cs b. atom (b::bv) \<sharp> (cs::char list)" using pure_fresh by auto

    then have "j \<sharp> x \<and> atom i = j \<longrightarrow> ((j \<sharp> x3[i::=x]\<^sub>s\<^sub>b \<or> j \<in> set [atom x2]) \<and> j \<sharp> x1) = (atom i \<sharp> AS_branch x1 x2 x3 \<and> j \<sharp> AS_branch x1 x2 x3 \<or> j \<sharp> x \<and> (j \<sharp> AS_branch x1 x2 x3 \<or> j = atom i))"
      by (metis (full_types) AS_branch.hyps(3))
    then have "j \<sharp> x \<longrightarrow> ((j \<sharp> x3[i::=x]\<^sub>s\<^sub>b \<or> j \<in> set [atom x2]) \<and> j \<sharp> x1) = (atom i \<sharp> AS_branch x1 x2 x3 \<and> j \<sharp> AS_branch x1 x2 x3 \<or> j \<sharp> x \<and> (j \<sharp> AS_branch x1 x2 x3 \<or> j = atom i))"
      using  AS_branch.hyps s_branch_s_branch_list.fresh by metis
    moreover
    { assume "\<not> j \<sharp> x"
      have ?thesis
        using f1 AS_branch.hyps(2) AS_branch.hyps(3) by force  }
    ultimately show ?thesis
      by satx 
  qed   
  finally show ?case by auto  
next
  case (AS_cons cs css i x)
  show ?case 
    unfolding subst_branchlb.simps s_branch_s_branch_list.fresh 
    using AS_cons by auto
next
  case (AS_val xx)
  then show ?case using  subst_sb.simps(1) s_branch_s_branch_list.fresh has_subst_b_class.fresh_subst_if subst_b_b_def subst_b_v_def by metis
next
  case (AS_let x1 x2 x3)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh  fresh_at_base has_subst_b_class.fresh_subst_if list.distinct list.set_cases set_ConsD subst_b_e_def 
    by fastforce
next
  case (AS_let2 x1 x2 x3 x4)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh  fresh_at_base has_subst_b_class.fresh_subst_if list.distinct list.set_cases set_ConsD subst_b_\<tau>_def
    by fastforce
next
  case (AS_if x1 x2 x3)
  then show ?case unfolding   subst_sb.simps s_branch_s_branch_list.fresh using
      has_subst_b_class.fresh_subst_if  subst_b_v_def   by metis
next
  case (AS_var u t v s)

  have "(((atom i \<sharp> s \<and> j \<sharp> s \<or> j \<sharp> x \<and> (j \<sharp> s \<or> j = atom i)) \<or> j \<in> set [atom u]) \<and> j \<sharp> t[i::=x]\<^sub>\<tau>\<^sub>b \<and> j \<sharp> v[i::=x]\<^sub>v\<^sub>b) = 
          (((atom i \<sharp> s \<and> j \<sharp> s \<or> j \<sharp> x \<and> (j \<sharp> s \<or> j = atom i)) \<or> j \<in> set [atom u]) \<and> 
                    ((atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))) \<and>
                    ((atom i \<sharp> v \<and> j \<sharp> v \<or> j \<sharp> x \<and> (j \<sharp> v \<or> j = atom i))))" 
    using    has_subst_b_class.fresh_subst_if  subst_b_v_def  subst_b_\<tau>_def by metis
  also have "... =  (((atom i \<sharp> s \<or> atom i \<in> set [atom u]) \<and> atom i \<sharp> t \<and> atom i \<sharp> v) \<and> 
               (j \<sharp> s \<or> j \<in> set [atom u]) \<and> j \<sharp> t \<and> j \<sharp> v \<or> j \<sharp> x \<and> ((j \<sharp> s \<or> j \<in> set [atom u]) \<and> j \<sharp> t \<and> j \<sharp> v \<or> j = atom i))" 
    using u_fresh_b by auto
  finally show ?case using  subst_sb.simps s_branch_s_branch_list.fresh AS_var 
    by simp
next
  case (AS_assign u v )
  then show ?case unfolding   subst_sb.simps s_branch_s_branch_list.fresh using
      has_subst_b_class.fresh_subst_if  subst_b_v_def by force
next
  case (AS_match v cs)
  have " j \<sharp> (AS_match v cs)[i::=x]\<^sub>s\<^sub>b = j \<sharp> (AS_match (subst_vb v i x) (subst_branchlb cs i x ))" using subst_sb.simps by auto
  also have "... = (j \<sharp> (subst_vb v i x) \<and> j \<sharp> (subst_branchlb cs i x ))" using s_branch_s_branch_list.fresh by simp
  also have "... = (j \<sharp> (subst_vb v i x) \<and> ((atom i \<sharp> cs \<and> j \<sharp> cs) \<or> j \<sharp> x \<and> (j \<sharp> cs \<or> j = atom i)))" using  AS_match[of i x] by auto
  also have "... =  (atom i \<sharp> AS_match v cs \<and> j \<sharp> AS_match v cs \<or> j \<sharp> x \<and> (j \<sharp> AS_match v cs \<or> j = atom i))" 
    by (metis (no_types) s_branch_s_branch_list.fresh has_subst_b_class.fresh_subst_if subst_b_v_def) (* 93 ms *)  
  finally show ?case by auto
next
  case (AS_while x1 x2)
  then show ?case by auto
next
  case (AS_seq x1 x2)
  then show ?case by auto
next
  case (AS_assert x1 x2)
  then show ?case unfolding subst_sb.simps  s_branch_s_branch_list.fresh 
    using  fresh_at_base has_subst_b_class.fresh_subst_if list.distinct list.set_cases set_ConsD subst_b_e_def 
    by (metis subst_b_c_def)   
qed(auto+)

lemma 
  forget_subst_sb[simp]: "atom a \<sharp> A \<Longrightarrow> subst_sb A a x = A" and
  forget_subst_branchb [simp]: "atom a \<sharp> B \<Longrightarrow> subst_branchb B a x = B" and 
  forget_subst_branchlb[simp]: "atom a \<sharp> C \<Longrightarrow> subst_branchlb C a x = C"
proof (nominal_induct A and B and C avoiding: a x rule: s_branch_s_branch_list.strong_induct)
  case (AS_let x1 x2 x3)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_let2 x1 x2 x3 x4)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_\<tau>_def by force
next
  case (AS_var x1 x2 x3 x4)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def  using subst_b_\<tau>_def 
  proof -
    have f1: "(atom a \<sharp> x4 \<or> atom a \<in> set [atom x1]) \<and> atom a \<sharp> x2 \<and> atom a \<sharp> x3"
      using AS_var.prems s_branch_s_branch_list.fresh  by simp
    then have "atom a \<sharp> x4"
      by (metis (no_types) "Nominal-Utils.fresh_star_singleton" AS_var.hyps(1) empty_set fresh_star_def list.simps(15) not_self_fresh) (* 46 ms *)
    then show ?thesis
      using f1 by (metis AS_var.hyps(3) has_subst_b_class.forget_subst subst_b_\<tau>_def subst_b_v_def subst_sb.simps(7)) (* 62 ms *)
  qed
next
  case (AS_branch x1 x2 x3)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_cons x1 x2 x3 x4)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_val x)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_if x1 x2 x3)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_assign x1 x2)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_match x1 x2)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_while x1 x2)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_seq x1 x2)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def by force
next
  case (AS_assert c s)
  then show ?case unfolding  subst_sb.simps using
      s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.forget_subst subst_b_v_def  subst_b_c_def subst_cb.simps  by force
qed(auto+)

lemma   subst_sb_id: "subst_sb A a (B_var a) = A" and
  subst_branchb_id [simp]: "subst_branchb B a (B_var a) = B" and
  subst_branchlb_id: "subst_branchlb C a (B_var a) = C"
proof(nominal_induct A and B and C avoiding: a  rule: s_branch_s_branch_list.strong_induct)
  case (AS_branch x1 x2 x3)
  then show ?case  using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def 
    by simp
next
  case (AS_cons x1 x2 )
  then show ?case  using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def by simp
next
  case (AS_val x)
  then show ?case  using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def by metis
next
  case (AS_if x1 x2 x3)
  then show ?case  using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def by metis
next
  case (AS_assign x1 x2)
  then show ?case  using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def by metis
next
  case (AS_match x1 x2)
  then show ?case  using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def by metis
next
  case (AS_while x1 x2)
  then show ?case  using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def by metis
next
  case (AS_seq x1 x2)
  then show ?case  using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def by metis
next
  case (AS_let x1 x2 x3)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_e_def has_subst_b_class.subst_id by metis
next
  case (AS_let2 x1 x2 x3 x4)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id by metis
next
  case (AS_var x1 x2 x3 x4)
  then show ?case using subst_sb.simps s_branch_s_branch_list.fresh subst_b_\<tau>_def has_subst_b_class.subst_id subst_b_v_def by metis
next
  case (AS_assert c s )
  then show ?case unfolding subst_sb.simps using s_branch_s_branch_list.fresh subst_b_c_def has_subst_b_class.subst_id by metis
qed (auto)

lemma flip_subst_s:
  fixes  bv::bv and s::s and cs::branch_s and z::bv
  shows   "atom bv \<sharp> s \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> s) = s[z::=B_var bv]\<^sub>s\<^sub>b"  and
    "atom bv \<sharp> cs \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> cs) = subst_branchb  cs z (B_var bv) " and
    "atom bv \<sharp> css \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> css) = subst_branchlb css z (B_var bv) "

proof(nominal_induct s and cs and css  rule: s_branch_s_branch_list.strong_induct)
  case (AS_branch x1 x2 x3)
  hence "((bv \<leftrightarrow> z) \<bullet> x1) = x1"  using pure_fresh fresh_at_base flip_fresh_fresh  by metis
  moreover have "((bv \<leftrightarrow> z) \<bullet> x2) = x2" using  fresh_at_base flip_fresh_fresh[of bv x2 z] AS_branch  by auto
  ultimately show ?case unfolding  s_branch_s_branch_list.perm_simps subst_branchb.simps using s_branch_s_branch_list.fresh(1) AS_branch by auto
next
  case (AS_cons x1 x2 )
  hence "((bv \<leftrightarrow> z) \<bullet> x1) =  subst_branchb x1 z (B_var bv)"  using pure_fresh fresh_at_base flip_fresh_fresh  s_branch_s_branch_list.fresh(13)  by metis
  moreover have "((bv \<leftrightarrow> z) \<bullet> x2) =  subst_branchlb x2 z (B_var bv)" using  fresh_at_base flip_fresh_fresh[of bv x2 z] AS_cons s_branch_s_branch_list.fresh by metis
  ultimately show ?case unfolding  s_branch_s_branch_list.perm_simps subst_branchb.simps using s_branch_s_branch_list.fresh(1) AS_cons by auto
next
  case (AS_val x)
  then show ?case unfolding  s_branch_s_branch_list.perm_simps subst_branchb.simps using flip_subst subst_b_v_def by simp
next
  case (AS_let x1 x2 x3)
  moreover hence "((bv \<leftrightarrow> z) \<bullet> x1) = x1" using fresh_at_base flip_fresh_fresh[of bv x1 z]  by auto
  ultimately show ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def s_branch_s_branch_list.fresh by auto 
next
  case (AS_let2 x1 x2 x3 x4)
  moreover hence "((bv \<leftrightarrow> z) \<bullet> x1) = x1" using fresh_at_base flip_fresh_fresh[of bv x1 z]  by auto
  ultimately show ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst s_branch_s_branch_list.fresh(5) subst_b_\<tau>_def by auto
next
  case (AS_if x1 x2 x3) 
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh by auto
next
  case (AS_var x1 x2 x3 x4)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def subst_b_\<tau>_def s_branch_s_branch_list.fresh fresh_at_base flip_fresh_fresh[of bv x1 z] by auto
next
  case (AS_assign x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh fresh_at_base flip_fresh_fresh[of bv x1 z] by auto
next
  case (AS_match x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh by auto
next
  case (AS_while x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh by auto
next
  case (AS_seq x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh by auto
next
  case (AS_assert x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_c_def subst_b_v_def s_branch_s_branch_list.fresh by simp
qed(auto)

lemma flip_subst_subst_s:
  fixes  bv::bv and s::s and cs::branch_s and z::bv
  shows   "atom bv \<sharp> s \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> s)[bv::=v]\<^sub>s\<^sub>b = s[z::=v]\<^sub>s\<^sub>b"    and
    "atom bv \<sharp> cs \<Longrightarrow> subst_branchb ((bv \<leftrightarrow> z) \<bullet> cs) bv v = subst_branchb cs z v" and
    "atom bv \<sharp> css \<Longrightarrow> subst_branchlb ((bv \<leftrightarrow> z) \<bullet> css) bv v = subst_branchlb  css z v " 
proof(nominal_induct s  and cs and css rule: s_branch_s_branch_list.strong_induct)
  case (AS_branch x1 x2 x3)
  hence "((bv \<leftrightarrow> z) \<bullet> x1) = x1"  using pure_fresh fresh_at_base flip_fresh_fresh  by metis
  moreover have "((bv \<leftrightarrow> z) \<bullet> x2) = x2" using  fresh_at_base flip_fresh_fresh[of bv x2 z] AS_branch  by auto
  ultimately show ?case unfolding  s_branch_s_branch_list.perm_simps subst_branchb.simps using s_branch_s_branch_list.fresh(1) AS_branch by auto
next
  case (AS_cons x1 x2 )
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_branchlb.simps
    using s_branch_s_branch_list.fresh(1) AS_cons by auto

next
  case (AS_val x)
  then show ?case unfolding  s_branch_s_branch_list.perm_simps subst_branchb.simps using flip_subst subst_b_v_def by simp
next
  case (AS_let x1 x2 x3)
  moreover hence "((bv \<leftrightarrow> z) \<bullet> x1) = x1" using fresh_at_base flip_fresh_fresh[of bv x1 z]  by auto
  ultimately show ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst_subst subst_b_e_def s_branch_s_branch_list.fresh by force
next
  case (AS_let2 x1 x2 x3 x4)
  moreover hence "((bv \<leftrightarrow> z) \<bullet> x1) = x1" using fresh_at_base flip_fresh_fresh[of bv x1 z]  by auto
  ultimately show ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst s_branch_s_branch_list.fresh(5) subst_b_\<tau>_def by auto
next
  case (AS_if x1 x2 x3) 
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh by auto
next
  case (AS_var x1 x2 x3 x4)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def subst_b_\<tau>_def s_branch_s_branch_list.fresh fresh_at_base flip_fresh_fresh[of bv x1 z] by auto
next
  case (AS_assign x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh fresh_at_base flip_fresh_fresh[of bv x1 z] by auto
next
  case (AS_match x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh by auto
next
  case (AS_while x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh by auto
next
  case (AS_seq x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_v_def s_branch_s_branch_list.fresh by auto
next
  case (AS_assert x1 x2)
  thus ?case 
    unfolding  s_branch_s_branch_list.perm_simps subst_sb.simps 
    using flip_subst subst_b_e_def subst_b_c_def s_branch_s_branch_list.fresh by auto
qed(auto)

instantiation s :: has_subst_b
begin
definition "subst_b = (\<lambda>s bv b. subst_sb s bv b)"

instance proof
  fix j::atom and i::bv and  x::b and t::s
  show  "j \<sharp> subst_b t i x = ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i)))" 
    using fresh_subst_sb_if subst_b_s_def by metis

  fix a::bv and tm::s and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x = tm" using subst_b_s_def forget_subst_sb by metis

  fix a::bv and tm::s
  show "subst_b tm a (B_var a) = tm" using subst_b_s_def  subst_sb_id   by metis

  fix p::perm and x1::bv and v::b and t1::s
  show "p \<bullet> subst_b t1 x1 v  = subst_b  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" using subst_b_s_def subst_sb_subst_branchb_subst_branchlb.eqvt by metis

  fix  bv::bv and c::s and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    using subst_b_s_def flip_subst_s by metis

  fix bv::bv and c::s and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
    using flip_subst_subst_s subst_b_s_def by metis
qed
end

section \<open>Function Type\<close>

nominal_function subst_ft_b :: "fun_typ \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> fun_typ" where
  "subst_ft_b ( AF_fun_typ z b c t (s::s)) x v = AF_fun_typ z (subst_bb b x v) (subst_cb c x v) t[x::=v]\<^sub>\<tau>\<^sub>b s[x::=v]\<^sub>s\<^sub>b"
     apply(simp add: eqvt_def subst_ft_b_graph_aux_def )
    apply(simp add:fun_typ.strong_exhaust,auto )
  apply(rule_tac y=a and c="(a,b)" in fun_typ.strong_exhaust)
  apply (auto simp: eqvt_at_def fresh_star_def fresh_Pair fresh_at_base)
  done

nominal_termination (eqvt) by lexicographic_order

nominal_function subst_ftq_b :: "fun_typ_q \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> fun_typ_q" where
  "atom bv \<sharp> (x,v) \<Longrightarrow>  subst_ftq_b (AF_fun_typ_some bv ft) x v = (AF_fun_typ_some bv (subst_ft_b ft x v))" 
|  "subst_ftq_b (AF_fun_typ_none  ft) x v = (AF_fun_typ_none (subst_ft_b ft x v))" 
       apply(simp add: eqvt_def subst_ftq_b_graph_aux_def )
      apply(simp add:fun_typ_q.strong_exhaust,auto )
  apply(rule_tac y=a and c="(aa,b)" in fun_typ_q.strong_exhaust)
  by (auto simp: eqvt_at_def fresh_star_def fresh_Pair fresh_at_base)
nominal_termination (eqvt) by lexicographic_order

instantiation fun_typ :: has_subst_b
begin
definition "subst_b = subst_ft_b"

text \<open>Note: Using just simp in the second apply unpacks and gives a single goal
whereas auto gives 43 non-intuitive goals. These goals are easier to solve 
and tedious, however they that it clear if a mistake is made in the definition of the function. 
For example, I saw that one of the goals was 
going through with metis and the next wasn't. 
It turned out the definition of the function itself was wrong\<close>

instance proof
  fix j::atom and i::bv and  x::b and t::fun_typ
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
    apply(nominal_induct t avoiding: i x rule:fun_typ.strong_induct)
    apply(auto simp add: subst_b_fun_typ_def )       
    by(metis fresh_subst_if subst_b_s_def subst_b_\<tau>_def subst_b_b_def subst_b_c_def)+

  fix a::bv and tm::fun_typ and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x  = tm"
    apply (nominal_induct tm avoiding: a x rule: fun_typ.strong_induct)
    apply(simp add: subst_b_fun_typ_def Abs1_eq_iff')
    using subst_b_b_def  subst_b_fun_typ_def subst_b_\<tau>_def subst_b_c_def subst_b_s_def
      forget_subst fresh_at_base list.set_cases neq_Nil_conv set_ConsD
      subst_ft_b.simps  by metis

  fix a::bv and tm::fun_typ
  show "subst_b tm a (B_var a) = tm" 
    apply (nominal_induct tm rule: fun_typ.strong_induct)
    apply(simp add: subst_b_fun_typ_def Abs1_eq_iff',auto)
    using subst_b_b_def  subst_b_fun_typ_def subst_b_\<tau>_def subst_b_c_def subst_b_s_def
      forget_subst fresh_at_base list.set_cases neq_Nil_conv set_ConsD
      subst_ft_b.simps 
    by (metis has_subst_b_class.subst_id)+

  fix p::perm and x1::bv and v::b and t1::fun_typ
  show "p \<bullet> subst_b t1 x1 v = subst_b (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v) " 
    apply (nominal_induct t1 avoiding: x1 v rule: fun_typ.strong_induct)
    by(auto simp add: subst_b_fun_typ_def Abs1_eq_iff' fun_typ.perm_simps)

  fix  bv::bv and c::fun_typ and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    apply (nominal_induct c avoiding: z bv rule: fun_typ.strong_induct)
    by(auto simp add: subst_b_fun_typ_def Abs1_eq_iff' fun_typ.perm_simps subst_b_b_def subst_b_c_def  subst_b_\<tau>_def  subst_b_s_def)

  fix bv::bv and c::fun_typ and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
    apply (nominal_induct c avoiding:  bv v z rule: fun_typ.strong_induct)
    apply(auto simp add: subst_b_fun_typ_def Abs1_eq_iff' fun_typ.perm_simps subst_b_b_def subst_b_c_def  subst_b_\<tau>_def  subst_b_s_def flip_subst_subst flip_subst)
    using  subst_b_fun_typ_def Abs1_eq_iff' fun_typ.perm_simps subst_b_b_def subst_b_c_def  subst_b_\<tau>_def  subst_b_s_def flip_subst_subst flip_subst 
    using flip_subst_s(1) flip_subst_subst_s(1) by auto
qed
end

instantiation fun_typ_q :: has_subst_b
begin
definition "subst_b = subst_ftq_b"

instance proof
  fix j::atom and i::bv and  x::b and t::fun_typ_q
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
    apply (nominal_induct t avoiding: i x j rule: fun_typ_q.strong_induct,auto simp add: subst_b_fun_typ_q_def subst_ftq_b.simps)
    using  fresh_subst_if subst_b_fun_typ_q_def subst_b_s_def subst_b_\<tau>_def subst_b_b_def subst_b_c_def subst_b_fun_typ_def apply metis+
    done

  fix a::bv and t::fun_typ_q and x::b
  show "atom a \<sharp> t \<Longrightarrow> subst_b t a x  = t"
    apply (nominal_induct t avoiding: a x  rule: fun_typ_q.strong_induct)
     apply(auto simp add: subst_b_fun_typ_q_def subst_ftq_b.simps Abs1_eq_iff') 
    using  forget_subst subst_b_fun_typ_q_def subst_b_s_def subst_b_\<tau>_def subst_b_b_def subst_b_c_def subst_b_fun_typ_def eqvt by metis+

  fix p::perm and x1::bv and v::b and t::fun_typ_q
  show "p \<bullet> subst_b t x1 v = subst_b (p \<bullet> t) (p \<bullet> x1) (p \<bullet> v) " 
    apply (nominal_induct t avoiding: x1 v  rule: fun_typ_q.strong_induct)
    by(auto simp add: subst_b_fun_typ_q_def subst_ftq_b.simps Abs1_eq_iff') 

  fix a::bv and tm::fun_typ_q
  show "subst_b tm a (B_var a) = tm" 
    apply (nominal_induct tm avoiding: a rule: fun_typ_q.strong_induct)
     apply(auto simp add: subst_b_fun_typ_q_def subst_ftq_b.simps Abs1_eq_iff')
    using subst_id subst_b_b_def  subst_b_fun_typ_def subst_b_\<tau>_def subst_b_c_def subst_b_s_def
      forget_subst fresh_at_base list.set_cases neq_Nil_conv set_ConsD
      subst_ft_b.simps by metis+

  fix  bv::bv and c::fun_typ_q and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
    apply (nominal_induct c avoiding: z bv  rule: fun_typ_q.strong_induct)
     apply(auto simp add: subst_b_fun_typ_q_def subst_ftq_b.simps Abs1_eq_iff') 
    using  forget_subst subst_b_fun_typ_q_def subst_b_s_def subst_b_\<tau>_def subst_b_b_def subst_b_c_def subst_b_fun_typ_def eqvt by metis+

  fix bv::bv and c::fun_typ_q and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
    apply (nominal_induct c avoiding: z v bv  rule: fun_typ_q.strong_induct)
     apply(auto simp add: subst_b_fun_typ_q_def subst_ftq_b.simps Abs1_eq_iff') 
    using  flip_subst flip_subst_subst forget_subst subst_b_fun_typ_q_def subst_b_s_def subst_b_\<tau>_def subst_b_b_def subst_b_c_def subst_b_fun_typ_def eqvt by metis+

qed
end

section \<open>Contexts\<close>

subsection \<open>Immutable Variables\<close>
nominal_function subst_gb :: "\<Gamma> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<Gamma>" where
  "subst_gb GNil _ _  = GNil"
| "subst_gb ((y,b',c)#\<^sub>\<Gamma>\<Gamma>) bv b = ((y,b'[bv::=b]\<^sub>b\<^sub>b,c[bv::=b]\<^sub>c\<^sub>b)#\<^sub>\<Gamma> (subst_gb \<Gamma> bv b))"
       apply (simp add: eqvt_def subst_gb_graph_aux_def )+
     apply auto
  apply (insert \<Gamma>.exhaust neq_GNil_conv, force)
  done
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_gb_abbrev :: "\<Gamma> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<Gamma>" ("_[_::=_]\<^sub>\<Gamma>\<^sub>b" [1000,50,50] 1000)
  where 
    "g[bv::=b']\<^sub>\<Gamma>\<^sub>b  \<equiv> subst_gb g bv b'" 

instantiation \<Gamma> :: has_subst_b
begin
definition "subst_b = subst_gb"

instance proof
  fix j::atom and i::bv and  x::b and t::\<Gamma>
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  proof(induct t rule: \<Gamma>_induct)
    case GNil
    then show ?case using fresh_GNil  subst_gb.simps  fresh_def pure_fresh subst_b_\<Gamma>_def has_subst_b_class.fresh_subst_if fresh_GNil fresh_GCons by metis
  next
    case (GCons x' b' c' \<Gamma>')
    have *: "atom i \<sharp> x' " using  fresh_at_base by simp

    have "j \<sharp> subst_b ((x', b', c') #\<^sub>\<Gamma> \<Gamma>') i x = j \<sharp> ((x', b'[i::=x]\<^sub>b\<^sub>b, c'[i::=x]\<^sub>c\<^sub>b) #\<^sub>\<Gamma> (subst_b \<Gamma>' i x))" using subst_gb.simps  subst_b_\<Gamma>_def by auto
    also have "... = (j \<sharp> ((x', b'[i::=x]\<^sub>b\<^sub>b, c'[i::=x]\<^sub>c\<^sub>b)) \<and> (j \<sharp>  (subst_b \<Gamma>' i x)))" using fresh_GCons by auto
    also have "... = (((j  \<sharp> x') \<and> (j  \<sharp> b'[i::=x]\<^sub>b\<^sub>b) \<and> (j  \<sharp> c'[i::=x]\<^sub>c\<^sub>b)) \<and> (j \<sharp>  (subst_b \<Gamma>' i x)))"  by auto
    also have "... = (((j  \<sharp> x') \<and> ((atom i \<sharp> b' \<and> j \<sharp> b' \<or> j \<sharp> x \<and> (j \<sharp> b' \<or> j = atom i))) \<and> 
                                   ((atom i \<sharp> c' \<and> j \<sharp> c' \<or> j \<sharp> x \<and> (j \<sharp> c' \<or> j = atom i))) \<and> 
                                   ((atom i \<sharp> \<Gamma>' \<and> j \<sharp> \<Gamma>' \<or> j \<sharp> x \<and> (j \<sharp> \<Gamma>' \<or> j = atom i)))))" 
      using fresh_subst_if[of j b' i x] fresh_subst_if[of j c' i x] GCons subst_b_b_def  subst_b_c_def  by simp
    also have "... = ((atom i \<sharp> (x', b', c') #\<^sub>\<Gamma> \<Gamma>' \<and> j \<sharp> (x', b', c') #\<^sub>\<Gamma> \<Gamma>') \<or> (j \<sharp> x \<and> (j \<sharp> (x', b', c') #\<^sub>\<Gamma> \<Gamma>' \<or> j = atom i)))" using * fresh_GCons fresh_prod3 by metis

    finally show ?case  by auto
  qed

  fix a::bv and tm::\<Gamma> and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x = tm"
  proof (induct tm rule: \<Gamma>_induct)
    case GNil
    then show ?case using  subst_gb.simps subst_b_\<Gamma>_def by auto
  next
    case (GCons x' b' c' \<Gamma>')
    have *:"b'[a::=x]\<^sub>b\<^sub>b = b' \<and> c'[a::=x]\<^sub>c\<^sub>b = c'" using GCons fresh_GCons[of "atom a"] fresh_prod3[of "atom a"] has_subst_b_class.forget_subst  subst_b_b_def subst_b_c_def by metis
    have "subst_b ((x', b', c') #\<^sub>\<Gamma> \<Gamma>') a x = ((x', b'[a::=x]\<^sub>b\<^sub>b, c'[a::=x]\<^sub>c\<^sub>b) #\<^sub>\<Gamma> (subst_b \<Gamma>' a x))" using  subst_b_\<Gamma>_def subst_gb.simps by auto
    also have "... = ((x', b', c') #\<^sub>\<Gamma> \<Gamma>')" using * GCons  fresh_GCons[of "atom a"]  by auto 
    finally show ?case using   has_subst_b_class.forget_subst fresh_GCons fresh_prod3 GCons subst_b_\<Gamma>_def has_subst_b_class.forget_subst[of a b' x] fresh_prod3[of "atom a"] by argo
  qed

  fix a::bv and tm::\<Gamma>
  show "subst_b tm a (B_var a) = tm"
  proof(induct tm rule: \<Gamma>_induct)
    case GNil
    then show ?case using  subst_gb.simps subst_b_\<Gamma>_def by auto
  next
    case (GCons x' b' c' \<Gamma>')
    then show ?case using    has_subst_b_class.subst_id  subst_b_\<Gamma>_def subst_b_b_def subst_b_c_def subst_gb.simps by metis
  qed

  fix p::perm and x1::bv and v::b and t1::\<Gamma>
  show "p \<bullet> subst_b t1 x1 v  = subst_b  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
  proof (induct tm rule: \<Gamma>_induct)
    case GNil
    then show ?case using subst_b_\<Gamma>_def subst_gb.simps by simp
  next
    case (GCons x' b' c' \<Gamma>')
    then show ?case using subst_b_\<Gamma>_def subst_gb.simps has_subst_b_class.eqvt by argo
  qed

  fix  bv::bv and c::\<Gamma> and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
  proof (induct c rule: \<Gamma>_induct)
    case GNil
    then show ?case using subst_b_\<Gamma>_def subst_gb.simps by auto
  next
    case (GCons x b c \<Gamma>')   
    have *:"(bv \<leftrightarrow> z) \<bullet> (x, b, c) = (x, (bv \<leftrightarrow> z) \<bullet> b, (bv \<leftrightarrow> z) \<bullet> c)" using flip_bv_x_cancel by auto
    then show ?case 
      unfolding subst_gb.simps subst_b_\<Gamma>_def permute_\<Gamma>.simps  * 
      using GCons subst_b_\<Gamma>_def subst_gb.simps flip_subst subst_b_b_def subst_b_c_def fresh_GCons by auto
  qed

  fix bv::bv and c::\<Gamma> and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
  proof (induct c rule: \<Gamma>_induct)
    case GNil
    then show ?case using subst_b_\<Gamma>_def subst_gb.simps by auto
  next
    case (GCons x b c \<Gamma>')   
    have *:"(bv \<leftrightarrow> z) \<bullet> (x, b, c) = (x, (bv \<leftrightarrow> z) \<bullet> b, (bv \<leftrightarrow> z) \<bullet> c)" using flip_bv_x_cancel by auto
    then show ?case 
      unfolding subst_gb.simps subst_b_\<Gamma>_def permute_\<Gamma>.simps  * 
      using GCons subst_b_\<Gamma>_def subst_gb.simps flip_subst subst_b_b_def subst_b_c_def fresh_GCons by auto
  qed
qed
end

lemma subst_b_base_for_lit:
  "(base_for_lit l)[bv::=b]\<^sub>b\<^sub>b = base_for_lit l"
  using base_for_lit.simps l.strong_exhaust 
  by (metis subst_bb.simps(2) subst_bb.simps(3) subst_bb.simps(6) subst_bb.simps(7))

lemma subst_b_lookup:
  assumes "Some (b, c) = lookup \<Gamma> x"
  shows " Some (b[bv::=b']\<^sub>b\<^sub>b, c[bv::=b']\<^sub>c\<^sub>b) = lookup \<Gamma>[bv::=b']\<^sub>\<Gamma>\<^sub>b x"
  using assms by(induct \<Gamma> rule: \<Gamma>_induct, auto)

lemma subst_g_b_x_fresh:
  fixes x::x and b::b and \<Gamma>::\<Gamma> and bv::bv
  assumes "atom x \<sharp> \<Gamma>"
  shows  "atom x \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b"
  using subst_b_fresh_x subst_b_\<Gamma>_def assms by metis

subsection \<open>Mutable Variables\<close>

nominal_function subst_db :: "\<Delta> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<Delta>" where
  "subst_db []\<^sub>\<Delta> _ _  = []\<^sub>\<Delta>"
| "subst_db  ((u,t) #\<^sub>\<Delta> \<Delta>) bv b = ((u,t[bv::=b]\<^sub>\<tau>\<^sub>b) #\<^sub>\<Delta> (subst_db \<Delta> bv b))"
       apply (simp add: eqvt_def subst_db_graph_aux_def,auto )
  using list.exhaust delete_aux.elims
  using neq_DNil_conv by fastforce
nominal_termination (eqvt) by lexicographic_order

abbreviation 
  subst_db_abbrev :: "\<Delta> \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> \<Delta>" ("_[_::=_]\<^sub>\<Delta>\<^sub>b" [1000,50,50] 1000)
  where 
    "\<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b  \<equiv> subst_db \<Delta> bv b" 

instantiation \<Delta> :: has_subst_b
begin
definition "subst_b = subst_db"

instance proof
  fix j::atom and i::bv and  x::b and t::\<Delta>
  show  "j \<sharp> subst_b t i x = (atom i \<sharp> t \<and> j \<sharp> t \<or> j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))"
  proof(induct t rule: \<Delta>_induct)
    case DNil
    then show ?case using fresh_DNil  subst_db.simps  fresh_def pure_fresh subst_b_\<Delta>_def has_subst_b_class.fresh_subst_if fresh_DNil fresh_DCons by metis
  next
    case (DCons u t \<Gamma>')
    have "j \<sharp> subst_b ((u, t) #\<^sub>\<Delta> \<Gamma>') i x = j \<sharp> ((u, t[i::=x]\<^sub>\<tau>\<^sub>b) #\<^sub>\<Delta> (subst_b \<Gamma>' i x))" using subst_db.simps  subst_b_\<Delta>_def by auto
    also have "... = (j \<sharp> ((u, t[i::=x]\<^sub>\<tau>\<^sub>b)) \<and> (j \<sharp>  (subst_b \<Gamma>' i x)))" using fresh_DCons by auto
    also have "... = (((j  \<sharp> u) \<and> (j  \<sharp> t[i::=x]\<^sub>\<tau>\<^sub>b)) \<and> (j \<sharp>  (subst_b \<Gamma>' i x)))"  by auto
    also have "... =   ((j  \<sharp> u) \<and>  ((atom i \<sharp> t \<and> j \<sharp> t) \<or> (j \<sharp> x \<and> (j \<sharp> t \<or> j = atom i))) \<and> (atom i \<sharp> \<Gamma>' \<and> j \<sharp> \<Gamma>' \<or> j \<sharp> x \<and> (j \<sharp> \<Gamma>' \<or> j = atom i)))" 
      using has_subst_b_class.fresh_subst_if[of j t i x] subst_b_\<tau>_def DCons  subst_b_\<Delta>_def by auto
    also have "... = (atom i \<sharp> (u, t) #\<^sub>\<Delta> \<Gamma>' \<and> j \<sharp> (u, t) #\<^sub>\<Delta> \<Gamma>' \<or> j \<sharp> x \<and> (j \<sharp> (u, t) #\<^sub>\<Delta> \<Gamma>' \<or> j = atom i))" 
      using DCons subst_db.simps(2)  has_subst_b_class.fresh_subst_if fresh_DCons subst_b_\<Delta>_def  pure_fresh fresh_at_base by auto
    finally show ?case  by auto
  qed

  fix a::bv and tm::\<Delta> and x::b
  show "atom a \<sharp> tm \<Longrightarrow> subst_b tm a x = tm"
  proof (induct tm rule: \<Delta>_induct)
    case DNil
    then show ?case using  subst_db.simps subst_b_\<Delta>_def by auto
  next
    case (DCons u t \<Gamma>')
    have *:"t[a::=x]\<^sub>\<tau>\<^sub>b = t" using DCons fresh_DCons[of "atom a"] fresh_prod2[of "atom a"] has_subst_b_class.forget_subst  subst_b_\<tau>_def by metis
    have "subst_b ((u,t) #\<^sub>\<Delta> \<Gamma>') a x = ((u,t[a::=x]\<^sub>\<tau>\<^sub>b) #\<^sub>\<Delta> (subst_b \<Gamma>' a x))" using  subst_b_\<Delta>_def subst_db.simps by auto
    also have "... = ((u, t) #\<^sub>\<Delta> \<Gamma>')" using * DCons  fresh_DCons[of "atom a"]  by auto 
    finally show ?case using   
        has_subst_b_class.forget_subst fresh_DCons fresh_prod3 
        DCons subst_b_\<Delta>_def has_subst_b_class.forget_subst[of a t x] fresh_prod3[of "atom a"] by argo
  qed

  fix a::bv and tm::\<Delta>
  show "subst_b tm a (B_var a) = tm"
  proof(induct tm rule: \<Delta>_induct)
    case DNil
    then show ?case using  subst_db.simps subst_b_\<Delta>_def by auto
  next
    case (DCons u t  \<Gamma>')
    then show ?case using    has_subst_b_class.subst_id  subst_b_\<Delta>_def subst_b_\<tau>_def subst_db.simps by metis
  qed

  fix p::perm and x1::bv and v::b and t1::\<Delta>
  show "p \<bullet> subst_b t1 x1 v  = subst_b  (p \<bullet> t1) (p \<bullet> x1) (p \<bullet> v)" 
  proof (induct tm rule: \<Delta>_induct)
    case DNil
    then show ?case using subst_b_\<Delta>_def subst_db.simps by simp
  next
    case (DCons x' b' \<Gamma>')
    then show ?case  by argo
  qed

  fix  bv::bv and c::\<Delta> and z::bv
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c) = c[z::=B_var bv]\<^sub>b"
  proof (induct c rule: \<Delta>_induct)
    case DNil
    then show ?case using subst_b_\<Delta>_def subst_db.simps by auto
  next
    case (DCons u t')
    then show ?case 
      unfolding subst_db.simps subst_b_\<Delta>_def permute_\<Delta>.simps  
      using DCons subst_b_\<Delta>_def subst_db.simps flip_subst subst_b_\<tau>_def flip_fresh_fresh fresh_at_base fresh_DCons flip_bv_u_cancel by simp
  qed

  fix bv::bv and c::\<Delta> and z::bv and v::b
  show "atom bv \<sharp> c \<Longrightarrow> ((bv \<leftrightarrow> z) \<bullet> c)[bv::=v]\<^sub>b = c[z::=v]\<^sub>b"
  proof (induct c rule: \<Delta>_induct)
    case DNil
    then show ?case using subst_b_\<Delta>_def subst_db.simps by auto
  next
    case (DCons u t')
    then show ?case 
      unfolding subst_db.simps subst_b_\<Delta>_def permute_\<Delta>.simps  
      using DCons subst_b_\<Delta>_def subst_db.simps flip_subst subst_b_\<tau>_def flip_fresh_fresh fresh_at_base fresh_DCons flip_bv_u_cancel by simp
  qed
qed
end

lemma subst_d_b_member:
  assumes "(u, \<tau>) \<in> setD \<Delta>" 
  shows  "(u, \<tau>[bv::=b]\<^sub>\<tau>\<^sub>b) \<in> setD \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b" 
  using assms  by (induct \<Delta>,auto)

lemmas ms_fresh_all = e.fresh s_branch_s_branch_list.fresh \<tau>.fresh c.fresh ce.fresh v.fresh l.fresh fresh_at_base opp.fresh pure_fresh ms_fresh

lemmas fresh_intros[intro] = fresh_GNil x_not_in_b_set x_not_in_u_atoms x_fresh_b u_not_in_x_atoms bv_not_in_x_atoms u_not_in_b_atoms

lemmas subst_b_simps = subst_tb.simps subst_cb.simps subst_ceb.simps subst_vb.simps subst_bb.simps  subst_eb.simps subst_branchb.simps subst_sb.simps

lemma subst_d_b_x_fresh:
  fixes x::x and b::b and \<Delta>::\<Delta> and bv::bv
  assumes "atom x \<sharp> \<Delta>"
  shows  "atom x \<sharp> \<Delta>[bv::=b]\<^sub>\<Delta>\<^sub>b"
  using subst_b_fresh_x subst_b_\<Delta>_def assms by metis

lemma subst_b_fresh_x:
  fixes  x::x
  shows "atom x \<sharp> v \<Longrightarrow> atom x \<sharp> v[bv::=b']\<^sub>v\<^sub>b" and
    "atom x \<sharp> ce \<Longrightarrow> atom x \<sharp> ce[bv::=b']\<^sub>c\<^sub>e\<^sub>b" and
    "atom x \<sharp> e \<Longrightarrow> atom x \<sharp> e[bv::=b']\<^sub>e\<^sub>b" and
    "atom x \<sharp> c \<Longrightarrow> atom x \<sharp> c[bv::=b']\<^sub>c\<^sub>b" and
    "atom x \<sharp> t \<Longrightarrow> atom x \<sharp> t[bv::=b']\<^sub>\<tau>\<^sub>b" and
    "atom x \<sharp> d \<Longrightarrow> atom x \<sharp> d[bv::=b']\<^sub>\<Delta>\<^sub>b" and
    "atom x \<sharp> g \<Longrightarrow> atom x \<sharp> g[bv::=b']\<^sub>\<Gamma>\<^sub>b" and
    "atom x \<sharp> s \<Longrightarrow> atom x \<sharp> s[bv::=b']\<^sub>s\<^sub>b"
  using fresh_subst_if x_fresh_b subst_b_v_def subst_b_ce_def subst_b_e_def subst_b_c_def subst_b_\<tau>_def subst_b_s_def subst_g_b_x_fresh subst_d_b_x_fresh 
  by metis+

lemma subst_b_fresh_u_cls:
  fixes tm::"'a::has_subst_b" and x::u
  shows "atom x \<sharp> tm = atom x \<sharp> tm[bv::=b']\<^sub>b"
  using fresh_subst_if[of "atom x" tm bv b'] using u_fresh_b by auto

lemma subst_g_b_u_fresh:
  fixes x::u and b::b and \<Gamma>::\<Gamma> and bv::bv
  assumes "atom x \<sharp> \<Gamma>"
  shows  "atom x \<sharp> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b"
  using subst_b_fresh_u_cls subst_b_\<Gamma>_def assms by metis

lemma subst_d_b_u_fresh:
  fixes x::u and b::b and \<Gamma>::\<Delta> and bv::bv
  assumes "atom x \<sharp> \<Gamma>"
  shows  "atom x \<sharp> \<Gamma>[bv::=b]\<^sub>\<Delta>\<^sub>b"
  using subst_b_fresh_u_cls subst_b_\<Delta>_def assms by metis

lemma subst_b_fresh_u:
  fixes  x::u
  shows "atom x \<sharp> v \<Longrightarrow> atom x \<sharp> v[bv::=b']\<^sub>v\<^sub>b" and
    "atom x \<sharp> ce \<Longrightarrow> atom x \<sharp> ce[bv::=b']\<^sub>c\<^sub>e\<^sub>b" and
    "atom x \<sharp> e \<Longrightarrow> atom x \<sharp> e[bv::=b']\<^sub>e\<^sub>b" and
    "atom x \<sharp> c \<Longrightarrow> atom x \<sharp> c[bv::=b']\<^sub>c\<^sub>b" and
    "atom x \<sharp> t \<Longrightarrow> atom x \<sharp> t[bv::=b']\<^sub>\<tau>\<^sub>b" and
    "atom x \<sharp> d \<Longrightarrow> atom x \<sharp> d[bv::=b']\<^sub>\<Delta>\<^sub>b" and
    "atom x \<sharp> g \<Longrightarrow> atom x \<sharp> g[bv::=b']\<^sub>\<Gamma>\<^sub>b" and
    "atom x \<sharp> s \<Longrightarrow> atom x \<sharp> s[bv::=b']\<^sub>s\<^sub>b"
  using fresh_subst_if u_fresh_b subst_b_v_def subst_b_ce_def subst_b_e_def subst_b_c_def subst_b_\<tau>_def subst_b_s_def subst_g_b_u_fresh subst_d_b_u_fresh 
  by metis+

lemma subst_db_u_fresh:
  fixes u::u and b::b and D::\<Delta>
  assumes "atom u \<sharp> D"
  shows  "atom u \<sharp> D[bv::=b]\<^sub>\<Delta>\<^sub>b"
  using assms proof(induct D rule: \<Delta>_induct)
  case DNil
  then show ?case by auto
next
  case (DCons u' t' D')
  then show ?case using subst_db.simps fresh_def fresh_DCons fresh_subst_if subst_b_\<tau>_def 
    by (metis fresh_Pair u_not_in_b_atoms)
qed

lemma flip_bt_subst4:
  fixes t::\<tau> and bv::bv 
  assumes "atom bv \<sharp> t" 
  shows "t[bv'::=b]\<^sub>\<tau>\<^sub>b = ((bv' \<leftrightarrow> bv) \<bullet> t)[bv::=b]\<^sub>\<tau>\<^sub>b" 
  using flip_subst_subst[OF assms,of bv' b] 
  by (simp add: flip_commute subst_b_\<tau>_def)

lemma subst_bt_flip_sym:
  fixes t1::\<tau> and t2::\<tau>
  assumes "atom bv \<sharp> b" and "atom bv \<sharp> (bv1, bv2, t1, t2)" and "(bv1 \<leftrightarrow> bv) \<bullet> t1 = (bv2 \<leftrightarrow> bv) \<bullet> t2"
  shows " t1[bv1::=b]\<^sub>\<tau>\<^sub>b = t2[bv2::=b]\<^sub>\<tau>\<^sub>b"
  using assms  flip_bt_subst4[of bv t1 bv1 b ]   flip_bt_subst4 fresh_prod4 fresh_Pair by metis

end