(*<*)
theory SyntaxL
  imports Syntax IVSubst
begin
  (*>*)

chapter \<open>Syntax Lemmas\<close>

section \<open>Support, lookup and contexts\<close>

lemma supp_v_tau [simp]:
  assumes "atom z \<sharp> v"
  shows "supp (\<lbrace> z : b | CE_val (V_var z)  ==  CE_val v  \<rbrace>) = supp v \<union> supp b" 
  using assms \<tau>.supp c.supp ce.supp 
  by (simp add: fresh_def supp_at_base)

lemma supp_v_var_tau [simp]:
  assumes "z \<noteq> x"
  shows  "supp (\<lbrace> z : b | CE_val (V_var z)  ==  CE_val (V_var x)  \<rbrace>) = { atom x } \<union> supp b"
  using supp_v_tau assms
  using supp_at_base by fastforce

text \<open> Sometimes we need to work with a version of a binder where the variable is fresh 
in something else, such as  a bigger context. I think these could be generated automatically \<close>

lemma obtain_fresh_fun_def:
  fixes t::"'b::fs" 
  shows  "\<exists>y::x. atom y \<sharp> (s,c,\<tau>,t) \<and> (AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))  = AF_fundef f (AF_fun_typ_none (AF_fun_typ y b ((y \<leftrightarrow> x) \<bullet> c ) ((y \<leftrightarrow> x) \<bullet> \<tau>) ((y \<leftrightarrow> x) \<bullet> s))))"
proof -
  obtain y::x where y: "atom y \<sharp> (s,c,\<tau>,t)" using obtain_fresh by blast
  moreover have "AF_fundef f (AF_fun_typ_none (AF_fun_typ y b ((y \<leftrightarrow> x) \<bullet> c ) ((y \<leftrightarrow> x) \<bullet> \<tau>) ((y \<leftrightarrow> x) \<bullet> s))) =  (AF_fundef f (AF_fun_typ_none (AF_fun_typ  x b c \<tau> s)))" 
  proof(cases "x=y")
    case True
    then show ?thesis  using fun_def.eq_iff Abs1_eq_iff(3)  flip_commute flip_fresh_fresh fresh_PairD by auto
  next
    case False

    have  "(AF_fun_typ y b ((y \<leftrightarrow> x) \<bullet> c) ((y \<leftrightarrow> x) \<bullet> \<tau>) ((y \<leftrightarrow> x) \<bullet> s)) =(AF_fun_typ x b c \<tau> s)" proof(subst fun_typ.eq_iff, subst Abs1_eq_iff(3))
      show  \<open>(y = x \<and> (((y \<leftrightarrow> x) \<bullet> c, (y \<leftrightarrow> x) \<bullet> \<tau>), (y \<leftrightarrow> x) \<bullet> s) = ((c, \<tau>), s) \<or>
         y \<noteq> x \<and> (((y \<leftrightarrow> x) \<bullet> c, (y \<leftrightarrow> x) \<bullet> \<tau>), (y \<leftrightarrow> x) \<bullet> s) = (y \<leftrightarrow> x) \<bullet> ((c, \<tau>), s) \<and> atom y \<sharp> ((c, \<tau>), s)) \<and>
         b = b\<close> using False flip_commute flip_fresh_fresh fresh_PairD y by auto
    qed
    thus ?thesis by metis
  qed
  ultimately show  ?thesis using y fresh_Pair by metis
qed

lemma lookup_fun_member:
  assumes "Some (AF_fundef f ft) = lookup_fun \<Phi> f"
  shows "AF_fundef f ft \<in> set \<Phi>"
  using assms proof (induct \<Phi>)
  case Nil
  then show ?case by auto
next
  case (Cons a \<Phi>)
  then show ?case using lookup_fun.simps
    by (metis fun_def.exhaust insert_iff list.simps(15) option.inject)
qed

lemma rig_dom_eq:
  "dom (G[x \<longmapsto> c]) = dom G"
proof(induct G rule: \<Gamma>.induct)
  case GNil
  then show ?case using replace_in_g.simps by presburger
next
  case (GCons xbc \<Gamma>')
  obtain x' and b' and c' where xbc: "xbc=(x',b',c')" using prod_cases3 by blast
  then show ?case using replace_in_g.simps GCons by simp
qed

lemma lookup_in_rig_eq:
  assumes "Some (b,c) = lookup \<Gamma> x" 
  shows "Some (b,c') = lookup (\<Gamma>[x\<longmapsto>c']) x"
  using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x b c \<Gamma>')
  then show ?case using replace_in_g.simps lookup.simps by auto
qed

lemma lookup_in_rig_neq:
  assumes "Some (b,c) = lookup \<Gamma> y" and "x\<noteq>y"
  shows "Some (b,c) = lookup (\<Gamma>[x\<longmapsto>c']) y"
  using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  then show ?case using replace_in_g.simps lookup.simps by auto
qed

lemma lookup_in_rig:
  assumes "Some (b,c) = lookup \<Gamma> y" 
  shows "\<exists>c''. Some (b,c'') = lookup (\<Gamma>[x\<longmapsto>c']) y"
proof(cases "x=y")
  case True
  then show ?thesis using lookup_in_rig_eq using assms by blast
next
  case False
  then show ?thesis using lookup_in_rig_neq using assms by blast
qed

lemma lookup_inside[simp]:
  assumes "x \<notin> fst ` toSet \<Gamma>'"
  shows "Some (b1,c1) = lookup (\<Gamma>'@(x,b1,c1)#\<^sub>\<Gamma>\<Gamma>) x"
  using assms by(induct \<Gamma>',auto)

lemma lookup_inside2:
  assumes "Some (b1,c1) = lookup (\<Gamma>'@((x,b0,c0)#\<^sub>\<Gamma>\<Gamma>)) y" and "x\<noteq>y"
  shows "Some (b1,c1) = lookup (\<Gamma>'@((x,b0,c0')#\<^sub>\<Gamma>\<Gamma>)) y" 
  using assms by(induct \<Gamma>' rule: \<Gamma>.induct,auto+)

fun tail:: "'a list \<Rightarrow> 'a list" where
  "tail [] = []"
| "tail (x#xs) = xs"

lemma lookup_options:
  assumes "Some (b,c) = lookup (xt#\<^sub>\<Gamma>G) x"
  shows  "((x,b,c) = xt) \<or> (Some (b,c) = lookup G x)"
  by (metis assms lookup.simps(2) option.inject surj_pair)

lemma lookup_x:
  assumes "Some (b,c) = lookup G x"
  shows "x \<in> fst ` toSet G"
  using assms
  by(induct "G" rule: \<Gamma>.induct ,auto+)

lemma GCons_eq_appendI:
  fixes xs1::\<Gamma>
  shows "[| x #\<^sub>\<Gamma> xs1 = ys; xs = xs1 @ zs |] ==> x #\<^sub>\<Gamma> xs = ys @ zs"
  by (drule sym) simp

lemma split_G: "x : toSet xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x #\<^sub>\<Gamma> zs"
proof (induct xs)
  case GNil thus ?case by simp
next
  case GCons thus ?case using  GCons_eq_appendI 
    by (metis Un_iff append_g.simps(1) singletonD toSet.simps(2))
qed

lemma lookup_not_empty:
  assumes "Some \<tau> = lookup G x"
  shows "G \<noteq> GNil"
  using assms by auto

lemma lookup_in_g:
  assumes "Some (b,c) = lookup \<Gamma> x"
  shows "(x,b,c) \<in> toSet \<Gamma>"
  using assms apply(induct \<Gamma>, simp)
  using lookup_options by fastforce

lemma lookup_split:
  fixes \<Gamma>::\<Gamma>
  assumes "Some (b,c) = lookup \<Gamma> x"
  shows "\<exists>G G' . \<Gamma> =  G'@(x,b,c)#\<^sub>\<Gamma>G"
  by (meson assms(1) lookup_in_g split_G)

lemma toSet_splitU[simp]:
  "(x',b',c') \<in> toSet (\<Gamma>' @ (x, b, c) #\<^sub>\<Gamma> \<Gamma>) \<longleftrightarrow> (x',b',c') \<in> (toSet \<Gamma>' \<union> {(x, b, c)} \<union> toSet \<Gamma>)"
  using append_g_toSetU toSet.simps by auto

lemma toSet_splitP[simp]:
  "(\<forall>(x', b', c')\<in>toSet (\<Gamma>' @ (x, b, c) #\<^sub>\<Gamma> \<Gamma>). P x' b' c') \<longleftrightarrow> (\<forall> (x', b', c')\<in>toSet \<Gamma>'. P x' b' c') \<and> P x b c \<and> (\<forall> (x', b', c')\<in>toSet \<Gamma>. P x' b' c')"  (is "?A \<longleftrightarrow> ?B")
  using toSet_splitU by force

lemma lookup_restrict:
  assumes "Some (b',c') = lookup (\<Gamma>'@(x,b,c)#\<^sub>\<Gamma>\<Gamma>) y" and "x \<noteq> y" 
  shows "Some (b',c') = lookup (\<Gamma>'@\<Gamma>) y"
  using assms  proof(induct \<Gamma>' rule:\<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x1 b1 c1 \<Gamma>')
  then show ?case by auto
qed

lemma supp_list_member:
  fixes x::"'a::fs" and l::"'a list"
  assumes "x \<in> set l"
  shows "supp x \<subseteq> supp l"
  using assms apply(induct l, auto)
  using supp_Cons by auto

lemma GNil_append:
  assumes "GNil = G1@G2"
  shows "G1 = GNil \<and> G2 = GNil"
proof(rule ccontr)
  assume "\<not> (G1 = GNil \<and> G2 = GNil)"
  hence "G1@G2 \<noteq> GNil" using append_g.simps   by (metis \<Gamma>.distinct(1) \<Gamma>.exhaust)
  thus False using assms by auto
qed

lemma GCons_eq_append_conv:
  fixes xs::\<Gamma>
  shows "x#\<^sub>\<Gamma>xs = ys@zs = (ys = GNil \<and> x#\<^sub>\<Gamma>xs = zs \<or> (\<exists>ys'. x#\<^sub>\<Gamma>ys' = ys \<and> xs = ys'@zs))"
  by(cases ys) auto

lemma dclist_distinct_unique:
  assumes  "(dc, const) \<in> set dclist2" and  "(cons, const1) \<in> set dclist2" and "dc=cons" and  "distinct (List.map fst dclist2)"
  shows "(const) = const1"
proof -
  have  "(cons, const) = (dc, const1)" 
    using assms     by (metis (no_types, lifting) assms(3) assms(4) distinct.simps(1) distinct.simps(2) empty_iff insert_iff list.set(1) list.simps(15) list.simps(8) list.simps(9) map_of_eq_Some_iff)
  thus ?thesis by auto
qed

lemma fresh_d_fst_d:
  assumes "atom u \<sharp> \<delta>"
  shows  "u \<notin> fst ` set \<delta>"
  using assms proof(induct \<delta>)
  case Nil
  then show ?case by auto
next
  case (Cons ut \<delta>')
  obtain u' and t' where *:"ut = (u',t') " by fastforce
  hence "atom u \<sharp> ut \<and> atom u \<sharp> \<delta>'" using fresh_Cons Cons by auto
  moreover hence "atom u \<sharp> fst ut" using * fresh_Pair[of "atom u" u' t'] Cons by auto
  ultimately show ?case using Cons by auto
qed

lemma bv_not_in_bset_supp:
  fixes bv::bv
  assumes "bv |\<notin>| B"
  shows "atom bv \<notin> supp B"
proof - 
  have *:"supp B = fset (fimage atom B)"
    by (metis fimage.rep_eq finite_fset supp_finite_set_at_base supp_fset)
  thus ?thesis using assms 
    using notin_fset by fastforce
qed

lemma u_fresh_d:
  assumes "atom u \<sharp> D"
  shows "u \<notin> fst ` setD D"
  using assms proof(induct D rule: \<Delta>_induct)
  case DNil
  then show ?case by auto
next
  case (DCons u' t' \<Delta>')
  then show ?case unfolding setD.simps 
    using fresh_DCons fresh_Pair  by (simp add: fresh_Pair fresh_at_base(2))
qed

section \<open>Type Definitions\<close>

lemma exist_fresh_bv:
  fixes tm::"'a::fs"
  shows  "\<exists>bva2 dclist2. AF_typedef_poly tyid bva dclist = AF_typedef_poly tyid bva2 dclist2 \<and> 
             atom bva2 \<sharp> tm" 
proof -
  obtain bva2::bv where *:"atom bva2 \<sharp> (bva, dclist,tyid,tm)" using obtain_fresh by metis
  moreover hence "bva2 \<noteq> bva" using fresh_at_base by auto
  moreover have " dclist = (bva \<leftrightarrow> bva2) \<bullet> (bva2 \<leftrightarrow> bva) \<bullet> dclist" by simp
  moreover have "atom bva \<sharp> (bva2 \<leftrightarrow> bva) \<bullet> dclist" proof -
    have "atom bva2 \<sharp> dclist" using * fresh_prodN by auto
    hence "atom ((bva2 \<leftrightarrow> bva) \<bullet> bva2) \<sharp> (bva2 \<leftrightarrow> bva) \<bullet> dclist" using fresh_eqvt True_eqvt 
    proof -
      have "(bva2 \<leftrightarrow> bva) \<bullet> atom bva2 \<sharp> (bva2 \<leftrightarrow> bva) \<bullet> dclist"
        by (metis True_eqvt \<open>atom bva2 \<sharp> dclist\<close> fresh_eqvt) (* 62 ms *)
      then show ?thesis
        by simp (* 125 ms *)
    qed
    thus ?thesis by auto
  qed
  ultimately have "AF_typedef_poly tyid bva dclist = AF_typedef_poly tyid bva2 ((bva2 \<leftrightarrow> bva ) \<bullet> dclist)"    
    unfolding type_def.eq_iff   Abs1_eq_iff by metis
  thus ?thesis using * fresh_prodN by metis
qed

lemma obtain_fresh_bv:
  fixes tm::"'a::fs"
  obtains bva2::bv and  dclist2 where "AF_typedef_poly tyid bva dclist = AF_typedef_poly tyid bva2 dclist2 \<and> 
             atom bva2 \<sharp> tm" 
  using exist_fresh_bv by metis

section \<open>Function Definitions\<close>

lemma fun_typ_flip:
  fixes bv1::bv and c::bv
  shows   "(bv1 \<leftrightarrow> c) \<bullet> AF_fun_typ x1 b1 c1 \<tau>1 s1 = AF_fun_typ x1 ((bv1 \<leftrightarrow> c) \<bullet> b1) ((bv1 \<leftrightarrow> c) \<bullet> c1) ((bv1 \<leftrightarrow> c) \<bullet> \<tau>1) ((bv1 \<leftrightarrow> c) \<bullet> s1)"
  using fun_typ.perm_simps flip_fresh_fresh supp_at_base  fresh_def
    flip_fresh_fresh fresh_def supp_at_base 
  by (simp add: flip_fresh_fresh)

lemma fun_def_eq:
  assumes  "AF_fundef fa (AF_fun_typ_none (AF_fun_typ xa ba ca \<tau>a sa)) = AF_fundef f (AF_fun_typ_none (AF_fun_typ x b c \<tau> s))"
  shows "f = fa" and "b = ba" and "[[atom xa]]lst. sa = [[atom x]]lst. s" and "[[atom xa]]lst. \<tau>a = [[atom x]]lst. \<tau>" and
    " [[atom xa]]lst. ca = [[atom x]]lst. c"
  using fun_def.eq_iff fun_typ_q.eq_iff fun_typ.eq_iff lst_snd lst_fst  using assms apply metis
  using fun_def.eq_iff fun_typ_q.eq_iff fun_typ.eq_iff lst_snd lst_fst  using assms apply metis
proof - 
  have "([[atom xa]]lst. ((ca, \<tau>a), sa) = [[atom x]]lst. ((c, \<tau>), s))" using assms  fun_def.eq_iff fun_typ_q.eq_iff  fun_typ.eq_iff by auto
  thus "[[atom xa]]lst. sa = [[atom x]]lst. s" and "[[atom xa]]lst. \<tau>a = [[atom x]]lst. \<tau>" and
    " [[atom xa]]lst. ca = [[atom x]]lst. c" using lst_snd lst_fst by metis+
qed

lemma fun_arg_unique_aux: 
  assumes "AF_fun_typ x1 b1 c1 \<tau>1' s1' = AF_fun_typ x2 b2 c2 \<tau>2' s2'"
  shows "\<lbrace> x1 : b1 | c1 \<rbrace> = \<lbrace> x2 : b2 | c2\<rbrace>"
proof - 
  have " ([[atom x1]]lst. c1 = [[atom x2]]lst. c2)" using fun_def_eq assms by metis
  moreover have "b1 = b2" using fun_typ.eq_iff assms  by metis
  ultimately show ?thesis using \<tau>.eq_iff by fast
qed

lemma fresh_x_neq:
  fixes x::x and y::x
  shows "atom x \<sharp> y = (x \<noteq> y)"
  using fresh_at_base  fresh_def by auto

lemma obtain_fresh_z3:
  fixes tm::"'b::fs"
  obtains z::x where "\<lbrace> x : b  | c \<rbrace> =  \<lbrace> z : b  | c[x::=V_var z]\<^sub>c\<^sub>v \<rbrace> \<and>  atom z \<sharp> tm \<and> atom z \<sharp> (x,c)" 
proof -
  obtain z::x and c'::c where z:"\<lbrace> x : b  | c \<rbrace> =  \<lbrace> z : b | c' \<rbrace> \<and>  atom z \<sharp> (tm,x,c)" using obtain_fresh_z2 b_of.simps by metis
  hence "c' = c[x::=V_var z]\<^sub>c\<^sub>v" proof - 
    have "([[atom z]]lst. c' = [[atom x]]lst. c)" using z \<tau>.eq_iff by metis
    hence "c' = (z \<leftrightarrow> x) \<bullet> c" using Abs1_eq_iff[of z c' x c]  fresh_x_neq  fresh_prodN by fastforce
    also have "... = c[x::=V_var z]\<^sub>c\<^sub>v"
      using subst_v_c_def  flip_subst_v[of z c x] z fresh_prod3 by metis
    finally show ?thesis by auto
  qed
  thus ?thesis using z fresh_prodN that by metis
qed

lemma u_fresh_v:
  fixes u::u and t::v
  shows "atom u \<sharp> t" 
  by(nominal_induct t rule:v.strong_induct,auto)

lemma u_fresh_ce:
  fixes u::u and t::ce
  shows "atom u \<sharp> t" 
  apply(nominal_induct t rule:ce.strong_induct)
  using  u_fresh_v pure_fresh 
       apply (auto simp add:  opp.fresh ce.fresh opp.fresh opp.exhaust)
  unfolding ce.fresh opp.fresh opp.exhaust  by (simp add: fresh_opp_all)

lemma u_fresh_c:
  fixes u::u and t::c
  shows "atom u \<sharp> t" 
  by(nominal_induct t rule:c.strong_induct,auto simp add: c.fresh u_fresh_ce)

lemma u_fresh_g:
  fixes u::u and t::\<Gamma>
  shows "atom u \<sharp> t" 
  by(induct t rule:\<Gamma>_induct, auto simp add: u_fresh_b u_fresh_c  fresh_GCons fresh_GNil)

lemma u_fresh_t:
  fixes u::u and t::\<tau>
  shows "atom u \<sharp> t" 
  by(nominal_induct t rule:\<tau>.strong_induct,auto simp add: \<tau>.fresh u_fresh_c u_fresh_b)

lemma b_of_c_of_eq:
  assumes "atom z \<sharp> \<tau>" 
  shows "\<lbrace> z : b_of \<tau> |  c_of \<tau> z \<rbrace> = \<tau>" 
  using assms proof(nominal_induct \<tau> avoiding: z rule: \<tau>.strong_induct)
  case (T_refined_type x1a x2a x3a)

  hence " \<lbrace> z : b_of \<lbrace> x1a : x2a  | x3a \<rbrace>  | c_of \<lbrace> x1a : x2a  | x3a \<rbrace> z \<rbrace> = \<lbrace> z : x2a | x3a[x1a::=V_var z]\<^sub>c\<^sub>v \<rbrace>" 
    using b_of.simps c_of.simps c_of_eq by auto
  moreover have "\<lbrace> z : x2a | x3a[x1a::=V_var z]\<^sub>c\<^sub>v \<rbrace> = \<lbrace> x1a : x2a  | x3a \<rbrace>" using T_refined_type \<tau>.fresh by auto
  ultimately show  ?case by auto
qed

lemma fresh_d_not_in:
  assumes "atom u2 \<sharp> \<Delta>'" 
  shows   "u2 \<notin> fst ` setD \<Delta>'" 
  using assms proof(induct \<Delta>' rule: \<Delta>_induct)
  case DNil
  then show ?case by simp
next
  case (DCons u t \<Delta>')
  hence *: "atom u2 \<sharp> \<Delta>' \<and> atom u2 \<sharp> (u,t)" 
    by (simp add: fresh_def supp_DCons)
  hence "u2 \<notin> fst ` setD \<Delta>'" using DCons by auto
  moreover have "u2 \<noteq> u" using * fresh_Pair 
    by (metis eq_fst_iff not_self_fresh)
  ultimately  show ?case by simp
qed

end