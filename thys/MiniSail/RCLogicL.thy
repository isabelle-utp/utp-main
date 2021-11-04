(*<*)
theory RCLogicL
  imports RCLogic WellformedL
begin
  (*>*)

hide_const Syntax.dom

chapter \<open>Refinement Constraint Logic Lemmas\<close>

section \<open>Lemmas\<close>

lemma wfI_domi:
  assumes "\<Theta> ; \<Gamma> \<turnstile> i"
  shows "fst ` toSet \<Gamma> \<subseteq> dom i"
  using wfI_def toSet.simps assms by fastforce

lemma wfI_lookup:
  fixes G::\<Gamma> and b::b
  assumes "Some (b,c) = lookup G x" and "P ; G \<turnstile> i" and "Some s = i x" and "P ; B \<turnstile>\<^sub>w\<^sub>f G"
  shows "P \<turnstile> s : b"
proof -
  have "(x,b,c) \<in> toSet G" using lookup.simps assms
    using lookup_in_g by blast
  then obtain s' where *:"Some s' = i x \<and> wfRCV P s' b" using wfI_def assms by auto
  hence "s' = s" using assms  by (metis option.inject)
  thus ?thesis using * by auto
qed

lemma wfI_restrict_weakening:
  assumes "wfI \<Theta> \<Gamma>' i'" and "i =  restrict_map i' (fst `toSet \<Gamma>)" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'"
  shows  "\<Theta> ; \<Gamma> \<turnstile> i"
proof -
  { fix x
    assume "x \<in> toSet \<Gamma>"
    have "case x of (x, b, c) \<Rightarrow> \<exists>s. Some s = i x \<and> \<Theta> \<turnstile> s : b" using assms wfI_def
    proof -
      have "case x of (x, b, c) \<Rightarrow> \<exists>s. Some s = i' x \<and> \<Theta> \<turnstile> s : b"
        using \<open>x \<in> toSet \<Gamma>\<close>  assms wfI_def by auto
      then have "\<exists>s. Some s = i (fst x) \<and> wfRCV \<Theta> s (fst (snd x))"
        by (simp add: \<open>x \<in> toSet \<Gamma>\<close> assms(2) case_prod_unfold)
      then show ?thesis
        by (simp add: case_prod_unfold)
    qed
  }
  thus ?thesis using wfI_def assms by auto
qed

lemma wfI_suffix:
  fixes G::\<Gamma>
  assumes "wfI P (G'@G) i" and "P ; B \<turnstile>\<^sub>w\<^sub>f G"
  shows "P ; G \<turnstile> i"
  using wfI_def append_g.simps assms toSet.simps by simp

lemma wfI_replace_inside:
  assumes "wfI \<Theta> (\<Gamma>' @ (x, b, c) #\<^sub>\<Gamma> \<Gamma>) i"
  shows  "wfI \<Theta> (\<Gamma>' @ (x, b, c') #\<^sub>\<Gamma> \<Gamma>) i"
  using wfI_def toSet_splitP assms by simp

section \<open>Existence of evaluation\<close>

lemma eval_l_base:
  "\<Theta> \<turnstile> \<lbrakk> l \<rbrakk>  : (base_for_lit l)"
  apply(nominal_induct l rule:l.strong_induct)
  using wfRCV.intros eval_l.simps  base_for_lit.simps by auto+

lemma obtain_fresh_bv_dclist:
  fixes tm::"'a::fs"
  assumes "(dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist" 
  obtains bv1::bv and dclist1 x1 b1 c1 where "AF_typedef_poly tyid bv dclist =  AF_typedef_poly tyid bv1 dclist1 
      \<and> (dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1 \<and> atom bv1 \<sharp> tm" 
proof - 
  obtain bv1 dclist1 where "AF_typedef_poly tyid bv dclist =  AF_typedef_poly tyid bv1 dclist1 \<and> atom bv1 \<sharp> tm" 
    using obtain_fresh_bv by metis
  moreover hence "[[atom bv]]lst. dclist = [[atom bv1]]lst. dclist1" using type_def.eq_iff by metis
  moreover then obtain x1 b1 c1 where "(dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1" using td_lookup_eq_iff assms by metis
  ultimately show ?thesis  using that by blast
qed

lemma obtain_fresh_bv_dclist_b_iff:
  fixes tm::"'a::fs"
  assumes "(dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist" and "AF_typedef_poly tyid bv dclist \<in> set P" and "\<turnstile>\<^sub>w\<^sub>f P"
  obtains bv1::bv and dclist1 x1 b1 c1 where "AF_typedef_poly tyid bv dclist =  AF_typedef_poly tyid bv1 dclist1 
      \<and> (dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1 \<and> atom bv1 \<sharp> tm \<and> b[bv::=b']\<^sub>b\<^sub>b=b1[bv1::=b']\<^sub>b\<^sub>b" 
proof - 
  obtain bv1 dclist1 x1 b1 c1 where *:"AF_typedef_poly tyid bv dclist =  AF_typedef_poly tyid bv1 dclist1 \<and> atom bv1 \<sharp> tm
    \<and> (dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1" using obtain_fresh_bv_dclist assms by metis

  hence "AF_typedef_poly tyid bv1 dclist1 \<in> set P" using assms by metis

  hence "b[bv::=b']\<^sub>b\<^sub>b = b1[bv1::=b']\<^sub>b\<^sub>b" 
    using  wfTh_typedef_poly_b_eq_iff[OF assms(2) assms(1) _ _ assms(3),of bv1 dclist1 x1 b1 c1 b']  * by metis

  from this that show ?thesis using * by metis  
qed

lemma eval_v_exist:
  fixes \<Gamma>::\<Gamma> and v::v and b::b
  assumes "P ; \<Gamma>  \<turnstile> i" and "P ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b"
  shows "\<exists>s. i \<lbrakk> v \<rbrakk> ~  s \<and> P \<turnstile> s : b "
  using assms proof(nominal_induct v  arbitrary: b rule:v.strong_induct)
  case (V_lit x)
  then show ?case using eval_l_base eval_v.intros eval_l.simps wfV_elims rcl_val.supp pure_supp by metis
next
  case (V_var x)
  then obtain c where  *:"Some (b,c) = lookup \<Gamma> x" using wfV_elims by metis
  hence "x \<in> fst ` toSet \<Gamma>"  using lookup_x by blast
  hence "x \<in> dom i" using wfI_domi using assms by blast
  then obtain s where "i x = Some s" by auto
  moreover hence "P \<turnstile> s : b" using wfRCV.intros wfI_lookup * V_var
    by (metis wfV_wf)

  ultimately show ?case using eval_v.intros rcl_val.supp b.supp  by metis
next
  case (V_pair v1 v2)
  then  obtain b1 and b2 where *:"P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b1 \<and>  P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : b2 \<and> b = B_pair b1 b2" using wfV_elims by metis
  then obtain s1 and s2 where "eval_v i v1 s1 \<and> wfRCV P s1 b1 \<and> eval_v i v2 s2 \<and> wfRCV P s2 b2" using V_pair by metis
  thus   ?case using eval_v.intros wfRCV.intros * by metis
next
  case (V_cons tyid dc v)
  then obtain  s and  b'::b and dclist and x::x and c::c where "(wfV P  B  \<Gamma> v  b') \<and> i \<lbrakk> v \<rbrakk> ~  s \<and> P \<turnstile> s : b' \<and> b = B_id tyid \<and>
                 AF_typedef tyid dclist \<in> set P \<and> (dc, \<lbrace> x : b'  | c \<rbrace>) \<in> set dclist" using  wfV_elims(4) by metis
  then show ?case using eval_v.intros(4) wfRCV.intros(5) V_cons by metis
next
  case (V_consp tyid dc b' v)

  obtain  b'a::b and bv and dclist and x::x and c::c where *:"(wfV P  B  \<Gamma> v  b'a[bv::=b']\<^sub>b\<^sub>b) \<and> b = B_app tyid b' \<and>
                 AF_typedef_poly tyid bv dclist \<in> set P \<and> (dc, \<lbrace> x : b'a  | c \<rbrace>) \<in> set dclist \<and> 
           atom bv \<sharp> (P, B_app tyid b',B) " using  wf_strong_elim(1)[OF V_consp(3)] by metis

  then obtain s where **:"i \<lbrakk> v \<rbrakk> ~ s  \<and>  P  \<turnstile> s : b'a[bv::=b']\<^sub>b\<^sub>b" using V_consp by auto

  have " \<turnstile>\<^sub>w\<^sub>f P" using wfX_wfY V_consp  by metis
  then obtain bv1::bv and dclist1 x1 b1 c1 where 3:"AF_typedef_poly tyid bv dclist =  AF_typedef_poly tyid bv1 dclist1 
      \<and> (dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1 \<and> atom bv1 \<sharp>  (P, SConsp tyid dc b' s, B_app tyid b')
          \<and> b'a[bv::=b']\<^sub>b\<^sub>b = b1[bv1::=b']\<^sub>b\<^sub>b" 
    using  *  obtain_fresh_bv_dclist_b_iff by blast

  have " i \<lbrakk> V_consp tyid dc b' v \<rbrakk> ~ SConsp tyid dc b' s" using  eval_v.intros  by (simp add: "**")

  moreover have " P  \<turnstile>  SConsp tyid dc b' s : B_app tyid b'" proof
    show \<open>AF_typedef_poly tyid bv1 dclist1 \<in> set P\<close> using 3 * by metis
    show \<open>(dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist1\<close> using 3 by auto 
    thus \<open>atom bv1 \<sharp> (P, SConsp tyid dc b' s, B_app tyid b')\<close> using * 3 fresh_prodN by metis
    show \<open> P  \<turnstile> s : b1[bv1::=b']\<^sub>b\<^sub>b\<close> using  3 ** by auto
  qed

  ultimately show ?case using eval_v.intros wfRCV.intros V_consp * by auto
qed

lemma eval_v_uniqueness:
  fixes v::v
  assumes "i \<lbrakk> v \<rbrakk> ~  s" and "i \<lbrakk> v \<rbrakk> ~  s'"
  shows "s=s'"
  using assms proof(nominal_induct v arbitrary: s s' rule:v.strong_induct)
  case (V_lit x)
  then show ?case using eval_v_elims eval_l.simps by metis
next
  case (V_var x)
  then show ?case using eval_v_elims   by (metis option.inject)
next
  case (V_pair v1 v2)
  obtain s1 and s2 where s:"i \<lbrakk> v1 \<rbrakk> ~ s1  \<and> i \<lbrakk> v2 \<rbrakk> ~ s2 \<and> s = SPair s1 s2" using eval_v_elims V_pair by metis
  obtain s1' and s2' where s':"i \<lbrakk> v1 \<rbrakk> ~ s1'  \<and> i \<lbrakk> v2 \<rbrakk> ~ s2' \<and> s' = SPair s1' s2'"  using eval_v_elims V_pair by metis
  then show ?case using eval_v_elims  using V_pair s s' by auto
next
  case (V_cons tyid dc v1)
  obtain sv1 where 1:"i \<lbrakk> v1 \<rbrakk> ~ sv1 \<and> s = SCons tyid dc sv1" using eval_v_elims V_cons by metis
  moreover obtain sv2 where 2:"i \<lbrakk> v1 \<rbrakk> ~ sv2 \<and> s' = SCons tyid dc sv2" using eval_v_elims V_cons by metis
  ultimately have "sv1 = sv2" using V_cons by auto
  then show ?case  using 1 2 by auto 
next
  case (V_consp tyid dc b v1)
  then show ?case using eval_v_elims  by metis

qed

lemma eval_v_base:
  fixes \<Gamma>::\<Gamma> and v::v and b::b
  assumes "P ; \<Gamma>  \<turnstile> i" and "P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b" and "i \<lbrakk> v \<rbrakk> ~  s"
  shows "P \<turnstile> s : b"
  using eval_v_exist eval_v_uniqueness assms by metis

lemma eval_e_uniqueness:
  fixes e::ce
  assumes "i \<lbrakk> e \<rbrakk> ~ s" and "i \<lbrakk> e \<rbrakk> ~ s'"
  shows "s=s'"
  using assms proof(nominal_induct e arbitrary: s s' rule:ce.strong_induct)
  case (CE_val x)
  then show ?case using eval_v_uniqueness eval_e_elims by metis
next
  case (CE_op opp x1 x2)
  consider "opp = Plus" | "opp = LEq" | "opp = Eq" using opp.exhaust by metis
  thus  ?case proof(cases)
    case 1
    hence a1:"eval_e i (CE_op Plus x1 x2) s" and a2:"eval_e i (CE_op Plus x1 x2) s'" using CE_op by auto
    then show ?thesis using   eval_e_elims(2)[OF a1] eval_e_elims(2)[OF a2]
        CE_op eval_e_plusI 
      by (metis rcl_val.eq_iff(2))
  next
    case 2
    hence a1:"eval_e i (CE_op LEq x1 x2) s" and a2:"eval_e i (CE_op LEq x1 x2) s'" using CE_op by auto
    then show ?thesis using eval_v_uniqueness  eval_e_elims(3)[OF a1] eval_e_elims(3)[OF a2]
        CE_op eval_e_plusI 
      by (metis rcl_val.eq_iff(2))
  next
    case 3
    hence a1:"eval_e i (CE_op Eq x1 x2) s" and a2:"eval_e i (CE_op Eq x1 x2) s'" using CE_op by auto
    then show ?thesis using eval_v_uniqueness  eval_e_elims(4)[OF a1] eval_e_elims(4)[OF a2]
        CE_op eval_e_plusI 
      by (metis rcl_val.eq_iff(2))
  qed
next
  case (CE_concat x1 x2)
  hence a1:"eval_e i (CE_concat x1 x2) s" and a2:"eval_e i (CE_concat x1 x2) s'" using CE_concat by auto
  show ?case using  eval_e_elims(7)[OF a1] eval_e_elims(7)[OF a2] CE_concat eval_e_concatI rcl_val.eq_iff 
  proof -
    assume "\<And>P. (\<And>bv1 bv2. \<lbrakk>s' = SBitvec (bv1 @ bv2); i \<lbrakk> x1 \<rbrakk> ~ SBitvec bv1 ; i \<lbrakk> x2 \<rbrakk> ~ SBitvec bv2 \<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
    obtain bbs :: "bit list" and bbsa :: "bit list" where
      "i \<lbrakk> x2 \<rbrakk> ~ SBitvec bbs \<and> i \<lbrakk> x1 \<rbrakk> ~ SBitvec bbsa \<and> SBitvec (bbsa @ bbs) = s'"
      by (metis \<open>\<And>P. (\<And>bv1 bv2. \<lbrakk>s' = SBitvec (bv1 @ bv2); i \<lbrakk> x1 \<rbrakk> ~ SBitvec bv1 ; i \<lbrakk> x2 \<rbrakk> ~ SBitvec bv2 \<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P\<close>) (* 93 ms *)
    then have "s' = s"
      by (metis (no_types) \<open>\<And>P. (\<And>bv1 bv2. \<lbrakk>s = SBitvec (bv1 @ bv2); i \<lbrakk> x1 \<rbrakk> ~ SBitvec bv1 ; i \<lbrakk> x2 \<rbrakk> ~ SBitvec bv2 \<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P\<close> \<open>\<And>s' s. \<lbrakk>i \<lbrakk> x1 \<rbrakk> ~ s ; i \<lbrakk> x1 \<rbrakk> ~ s' \<rbrakk> \<Longrightarrow> s = s'\<close> \<open>\<And>s' s. \<lbrakk>i \<lbrakk> x2 \<rbrakk> ~ s ; i \<lbrakk> x2 \<rbrakk> ~ s' \<rbrakk> \<Longrightarrow> s = s'\<close> rcl_val.eq_iff(1)) (* 125 ms *)
    then show ?thesis
      by metis (* 0.0 ms *)
  qed
next
  case (CE_fst x)
  then show ?case using eval_v_uniqueness  by (meson eval_e_elims rcl_val.eq_iff)
next
  case (CE_snd x)
  then show ?case using eval_v_uniqueness  by (meson eval_e_elims rcl_val.eq_iff)
next
  case (CE_len x)
  then show ?case using  eval_e_elims rcl_val.eq_iff 
  proof -
    obtain bbs :: "rcl_val \<Rightarrow> ce \<Rightarrow> (x \<Rightarrow> rcl_val option) \<Rightarrow> bit list" where
      "\<forall>x0 x1 x2. (\<exists>v3. x0 = SNum (int (length v3)) \<and> x2 \<lbrakk> x1 \<rbrakk> ~ SBitvec v3 ) = (x0 = SNum (int (length (bbs x0 x1 x2))) \<and> x2 \<lbrakk> x1 \<rbrakk> ~ SBitvec (bbs x0 x1 x2) )"
      by moura (* 0.0 ms *)
    then have "\<forall>f c r. \<not> f \<lbrakk> [| c |]\<^sup>c\<^sup>e \<rbrakk> ~ r \<or> r = SNum (int (length (bbs r c f))) \<and> f \<lbrakk> c \<rbrakk> ~ SBitvec (bbs r c f)"
      by (meson eval_e_elims(8)) (* 46 ms *)
    then show ?thesis
      by (metis (no_types) CE_len.hyps CE_len.prems(1) CE_len.prems(2) rcl_val.eq_iff(1)) (* 31 ms *)
  qed

qed

lemma wfV_eval_bitvec:
  fixes v::v
  assumes  "P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : B_bitvec" and "P ; \<Gamma>  \<turnstile> i"
  shows "\<exists>bv. eval_v i v (SBitvec bv)"
proof -
  obtain s where "i \<lbrakk> v \<rbrakk> ~  s \<and> wfRCV P s B_bitvec" using eval_v_exist assms by metis
  moreover then obtain bv where "s = SBitvec bv" using wfRCV_elims(1)[of P s] by metis
  ultimately show  ?thesis by metis
qed

lemma wfV_eval_pair:
  fixes v::v
  assumes  "P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : B_pair b1 b2" and "P ; \<Gamma>  \<turnstile> i"
  shows "\<exists>s1 s2. eval_v i v (SPair s1 s2)"
proof -
  obtain s  where "i \<lbrakk> v \<rbrakk> ~  s \<and> wfRCV P s (B_pair b1 b2)" using eval_v_exist assms by metis
  moreover then obtain s1 and s2 where "s = SPair s1 s2" using wfRCV_elims(2)[of P s] by metis
  ultimately show  ?thesis by metis
qed

lemma wfV_eval_int:
  fixes v::v
  assumes  "P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : B_int" and "P ; \<Gamma>  \<turnstile> i"
  shows "\<exists>n. eval_v i v (SNum n)"
proof -
  obtain s  where "i \<lbrakk> v \<rbrakk> ~  s \<and> wfRCV P s (B_int)" using eval_v_exist assms by metis
  moreover then obtain n where "s = SNum n" using wfRCV_elims(3)[of P s] by metis
  ultimately show  ?thesis by metis
qed

text \<open>Well sorted value with a well sorted valuation evaluates\<close>
lemma wfI_wfV_eval_v:
  fixes v::v and b::b
  assumes "\<Theta> ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b" and "wfI \<Theta>  \<Gamma> i"
  shows "\<exists>s. i \<lbrakk> v \<rbrakk> ~  s \<and> \<Theta> \<turnstile> s : b"
  using eval_v_exist assms by auto

lemma wfI_wfCE_eval_e:
  fixes e::ce and b::b
  assumes "wfCE P B G e b" and "P ; G \<turnstile> i" 
  shows "\<exists>s. i \<lbrakk> e \<rbrakk> ~ s \<and> P \<turnstile> s : b"
  using assms proof(nominal_induct e arbitrary:  b  rule: ce.strong_induct)
  case (CE_val v)
  obtain s where "i \<lbrakk> v \<rbrakk> ~ s \<and> P \<turnstile> s : b" using wfI_wfV_eval_v[of P B G v b i]  assms wfCE_elims(1)  [of P B G v b] CE_val  by auto
  then show ?case using CE_val   eval_e.intros(1)[of i v s ] by auto
next
  case (CE_op opp v1 v2)

  consider "opp =Plus" | "opp=LEq" | "opp=Eq" using opp.exhaust by auto

  thus ?case proof(cases)
    case 1
    hence  "wfCE P  B G v1 B_int \<and> wfCE P  B G v2 B_int" using wfCE_elims(2) CE_op

      by blast
    then obtain s1 and s2 where *: "eval_e i v1 s1 \<and> wfRCV P s1 B_int \<and> eval_e i v2 s2 \<and> wfRCV P s2 B_int"
      using wfI_wfV_eval_v  CE_op by metis
    then obtain n1 and n2 where **:"s2=SNum n2 \<and> s1 = SNum n1"  using wfRCV_elims  by meson
    hence "eval_e i (CE_op Plus v1 v2) (SNum (n1+n2))" using eval_e_plusI * ** by simp
    moreover have "wfRCV P (SNum (n1+n2)) B_int" using wfRCV.intros by auto
    ultimately show ?thesis using 1
      using CE_op.prems(1) wfCE_elims(2) by blast
  next
    case 2
    hence  "wfCE P  B G v1 B_int \<and> wfCE P  B G v2 B_int" using wfCE_elims(3) CE_op
      by blast
    then obtain s1 and s2 where *: "eval_e i v1 s1 \<and> wfRCV P s1 B_int \<and> eval_e i v2 s2 \<and> wfRCV P s2 B_int"
      using wfI_wfV_eval_v  CE_op by metis
    then obtain n1 and n2 where **:"s2=SNum n2 \<and> s1 = SNum n1"  using wfRCV_elims  by meson
    hence "eval_e i (CE_op LEq v1 v2) (SBool (n1 \<le> n2))" using eval_e_leqI * ** by simp
    moreover have "wfRCV P (SBool (n1\<le>n2)) B_bool" using wfRCV.intros by auto
    ultimately show ?thesis using 2
      using CE_op.prems wfCE_elims by metis
  next
    case 3
    then  obtain b2 where "wfCE P  B G v1 b2 \<and> wfCE P  B G v2 b2" using wfCE_elims(9) CE_op
      by blast
    then obtain s1 and s2 where *: "eval_e i v1 s1 \<and> wfRCV P s1 b2 \<and> eval_e i v2 s2 \<and> wfRCV P s2 b2"
      using wfI_wfV_eval_v  CE_op by metis
    hence "eval_e i (CE_op Eq v1 v2) (SBool (s1 = s2))" using eval_e_leqI *  
      by (simp add: eval_e_eqI)
    moreover have "wfRCV P (SBool (s1 = s2)) B_bool" using wfRCV.intros by auto
    ultimately show ?thesis using 3
      using CE_op.prems wfCE_elims by metis
  qed
next
  case (CE_concat v1 v2)
  then obtain s1 and s2 where *:"b = B_bitvec \<and> eval_e i v1 s1 \<and> eval_e i v2 s2 \<and>
      wfRCV P s1 B_bitvec \<and> wfRCV P s2 B_bitvec" using  
    CE_concat 
    by (meson wfCE_elims(6))
  thus ?case using  eval_e_concatI wfRCV.intros(1) wfRCV_elims 
  proof -
    obtain bbs :: "type_def list \<Rightarrow> rcl_val \<Rightarrow> bit list" where
      "\<forall>ts s. \<not> ts \<turnstile> s : B_bitvec \<or> s = SBitvec (bbs ts s)"
      using wfRCV_elims(1) by moura (* 156 ms *)
    then show ?thesis
      by (metis (no_types) "local.*" wfRCV_BBitvecI eval_e_concatI) (* 78 ms *)
  qed
next
  case (CE_fst v1)
  thus ?case using  eval_e_fstI  wfRCV.intros wfCE_elims wfI_wfV_eval_v
    by (metis wfRCV_elims(2) rcl_val.eq_iff(4))
next
  case (CE_snd v1)
  thus ?case using  eval_e_sndI  wfRCV.intros wfCE_elims wfI_wfV_eval_v
    by (metis wfRCV_elims(2) rcl_val.eq_iff(4))
next
  case (CE_len x)
  thus ?case using  eval_e_lenI  wfRCV.intros wfCE_elims wfI_wfV_eval_v wfV_eval_bitvec 
    by (metis wfRCV_elims(1))
qed

lemma eval_e_exist:
  fixes \<Gamma>::\<Gamma> and e::ce
  assumes "P ; \<Gamma>  \<turnstile> i" and "P ;  B ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f e : b"
  shows "\<exists>s. i \<lbrakk> e \<rbrakk> ~ s"
  using assms proof(nominal_induct e arbitrary: b rule:ce.strong_induct)
  case (CE_val v)
  then show ?case using eval_v_exist wfCE_elims eval_e.intros by metis
next
  case (CE_op op v1 v2)

  show ?case proof(rule opp.exhaust)
    assume \<open>op = Plus\<close>
    hence "P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int \<and> P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int \<and> b = B_int" using wfCE_elims CE_op by metis
    then obtain n1 and n2 where "eval_e i v1 (SNum n1) \<and> eval_e i v2 (SNum n2)" using CE_op eval_v_exist wfV_eval_int 
      by (metis wfI_wfCE_eval_e wfRCV_elims(3))
    then show \<open>\<exists>a. eval_e i (CE_op op v1 v2) a\<close> using eval_e_plusI[of i v1 _ v2] \<open>op=Plus\<close> by auto
  next
    assume \<open>op = LEq\<close>
    hence "P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : B_int \<and> P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : B_int \<and> b = B_bool" using wfCE_elims CE_op by metis
    then obtain n1 and n2 where "eval_e i v1 (SNum n1) \<and> eval_e i v2 (SNum n2)" using CE_op eval_v_exist wfV_eval_int 
      by (metis wfI_wfCE_eval_e wfRCV_elims(3))
    then show \<open>\<exists>a. eval_e i (CE_op op v1 v2) a\<close> using eval_e_leqI[of i v1 _ v2] eval_v_exist \<open>op=LEq\<close> CE_op by auto
  next
    assume \<open>op = Eq\<close>
    then obtain b1 where  "P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b1 \<and> P ;  B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v2 : b1 \<and> b = B_bool" using wfCE_elims CE_op by metis
    then obtain s1 and s2 where "eval_e i v1 s1 \<and> eval_e i v2 s2" using CE_op eval_v_exist wfV_eval_int 
      by (metis wfI_wfCE_eval_e wfRCV_elims(3))
    then show \<open>\<exists>a. eval_e i (CE_op op v1 v2) a\<close> using eval_e_eqI[of i v1 _ v2] eval_v_exist \<open>op=Eq\<close> CE_op by auto
  qed
next
  case (CE_concat v1 v2)
  then obtain bv1 and bv2 where "eval_e i v1 (SBitvec bv1) \<and> eval_e i v2 (SBitvec bv2)"
    using wfV_eval_bitvec  wfCE_elims(6) 
    by (meson eval_e_elims(7) wfI_wfCE_eval_e)
  then show ?case using  eval_e.intros by metis
next
  case (CE_fst ce)
  then obtain b2 where b:"P ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : B_pair b b2" using wfCE_elims by metis
  then obtain s where s:"i \<lbrakk> ce \<rbrakk> ~ s" using CE_fst by auto
  then obtain s1 and s2 where "s = (SPair s1 s2)" using eval_e_elims(4)  CE_fst wfI_wfCE_eval_e[of P B \<Gamma> ce "B_pair b b2" i,OF b] wfRCV_elims(2)[of P s b b2]    
    by (metis eval_e_uniqueness)
  then show ?case using s eval_e.intros by metis
next
  case (CE_snd ce)
  then obtain b1 where b:"P ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : B_pair b1 b" using wfCE_elims by metis
  then obtain s where s:"i \<lbrakk> ce \<rbrakk> ~ s" using CE_snd by auto
  then obtain s1 and s2 where "s = (SPair s1 s2)" 
    using eval_e_elims(5)  CE_snd wfI_wfCE_eval_e[of P B \<Gamma> ce "B_pair b1 b" i,OF b] wfRCV_elims(2)[of P s b b1]    
      eval_e_uniqueness 
    by (metis wfRCV_elims(2))
  then show ?case using s eval_e.intros by metis
next
  case (CE_len v1)
  then obtain bv1  where "eval_e i v1 (SBitvec bv1)"
    using wfV_eval_bitvec  CE_len  wfCE_elims eval_e_uniqueness 
    by (metis eval_e_elims(7) wfCE_concatI wfI_wfCE_eval_e)
  then show ?case using  eval_e.intros by metis
qed

lemma eval_c_exist:
  fixes \<Gamma>::\<Gamma> and c::c
  assumes "P ; \<Gamma>  \<turnstile> i" and "P ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f c"
  shows "\<exists>s. i \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(nominal_induct c  rule: c.strong_induct)
  case C_true
  then show ?case using eval_c.intros wfC_elims by metis
next
  case C_false
  then show ?case using eval_c.intros wfC_elims by metis
next
  case (C_conj c1 c2)
  then show ?case using eval_c.intros wfC_elims by metis
next
  case (C_disj x1 x2)
  then show ?case using eval_c.intros wfC_elims by metis
next
  case (C_not x)
  then show ?case using eval_c.intros wfC_elims by metis
next
  case (C_imp x1 x2)
  then show ?case using eval_c.intros eval_e_exist wfC_elims by metis
next
  case (C_eq x1 x2)
  then show ?case using eval_c.intros eval_e_exist wfC_elims by metis
qed

lemma eval_c_uniqueness:
  fixes c::c
  assumes "i \<lbrakk> c \<rbrakk> ~ s" and "i \<lbrakk> c \<rbrakk> ~ s'"
  shows "s=s'"
  using assms proof(nominal_induct c arbitrary: s s' rule:c.strong_induct)
  case C_true
  then show ?case using eval_c_elims by metis
next
  case C_false
  then show ?case using eval_c_elims by metis
next
  case (C_conj x1 x2)
  then show ?case using  eval_c_elims(3) by (metis (full_types))
next
  case (C_disj x1 x2)
  then show ?case using eval_c_elims(4)  by (metis (full_types))
next
  case (C_not x)
  then show ?case using eval_c_elims(6)  by (metis (full_types))
next
  case (C_imp x1 x2)
  then show ?case using eval_c_elims(5)  by (metis (full_types))
next
  case (C_eq x1 x2)
  then show ?case using eval_e_uniqueness eval_c_elims(7) by metis
qed

lemma wfI_wfC_eval_c:
  fixes c::c
  assumes "wfC P B G c" and "P ; G \<turnstile> i"
  shows "\<exists>s. i \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(nominal_induct c  rule: c.strong_induct)
qed(metis wfC_elims wfI_wfCE_eval_e eval_c.intros)+

section \<open>Satisfiability\<close>

lemma satis_reflI:
  fixes c::c
  assumes "i \<Turnstile> ((x, b, c) #\<^sub>\<Gamma> G)"
  shows "i \<Turnstile> c"
  using assms by auto

lemma is_satis_mp:
  fixes c1::c and c2::c
  assumes "i \<Turnstile> (c1 IMP c2)" and "i \<Turnstile> c1"
  shows "i \<Turnstile> c2"
  using assms proof -
  have "eval_c i (c1 IMP c2) True" using is_satis.simps  using assms by blast
  then obtain b1 and b2 where "True = (b1 \<longrightarrow> b2) \<and> eval_c i c1 b1 \<and> eval_c i c2 b2"
    using eval_c_elims(5) by metis
  moreover have "eval_c i c1 True" using is_satis.simps  using assms by blast
  moreover have "b1 = True" using calculation eval_c_uniqueness  by blast
  ultimately have "eval_c i c2 True" by auto
  thus ?thesis using is_satis.intros by auto
qed

lemma is_satis_imp:
  fixes c1::c and c2::c
  assumes "i \<Turnstile> c1 \<longrightarrow> i \<Turnstile> c2" and "i \<lbrakk> c1 \<rbrakk> ~ b1" and "i \<lbrakk> c2 \<rbrakk> ~ b2"
  shows "i \<Turnstile> (c1 IMP c2)"
proof(cases b1)
  case True
  hence "i \<Turnstile> c2" using assms is_satis.simps by simp
  hence "b2 = True" using is_satis.simps assms
    using eval_c_uniqueness by blast
  then show ?thesis using eval_c_impI is_satis.simps assms by force
next
  case False
  then show ?thesis using assms eval_c_impI is_satis.simps by metis
qed

lemma is_satis_iff:
  "i \<Turnstile> G  = (\<forall>x b c. (x,b,c) \<in> toSet G \<longrightarrow> i \<Turnstile> c)"
  by(induct G,auto)

lemma is_satis_g_append:
  "i \<Turnstile> (G1@G2) = (i \<Turnstile>  G1 \<and> i \<Turnstile>  G2)"
  using is_satis_g.simps  is_satis_iff by auto

section \<open>Substitution for Evaluation\<close>

lemma eval_v_i_upd:
  fixes v::v
  assumes "atom x \<sharp> v" and "i \<lbrakk> v \<rbrakk> ~  s'"
  shows "eval_v ((i ( x \<mapsto>s))) v s' "
  using assms proof(nominal_induct v arbitrary: s' rule:v.strong_induct)
  case (V_lit x)
  then show ?case  by (metis eval_v_elims(1) eval_v_litI)
next
  case (V_var y)
  then obtain s where *: "Some s = i y \<and> s=s'" using eval_v_elims by metis
  moreover have "x \<noteq> y" using \<open>atom x \<sharp> V_var y\<close> v.supp by simp
  ultimately have "(i ( x \<mapsto>s)) y = Some s"
    by (simp add: \<open>Some s = i y \<and> s = s'\<close>)
  then show ?case using eval_v_varI *  \<open>x \<noteq> y\<close>
    by (simp add: eval_v.eval_v_varI)
next
  case (V_pair v1 v2)
  hence "atom x \<sharp> v1 \<and> atom x \<sharp> v2" using v.supp by simp
  moreover obtain s1 and s2 where *: "eval_v i v1 s1 \<and> eval_v i v2 s2 \<and> s' = SPair s1 s2" using eval_v_elims V_pair by metis
  ultimately have "eval_v ((i ( x \<mapsto>s))) v1 s1 \<and> eval_v ((i ( x \<mapsto>s))) v2 s2" using V_pair by blast
  thus ?case using eval_v_pairI * by meson
next
  case (V_cons tyid dc v1)
  hence "atom x \<sharp> v1" using v.supp by simp
  moreover obtain s1 where *: "eval_v i v1 s1 \<and> s' = SCons tyid dc s1" using eval_v_elims V_cons by metis
  ultimately have "eval_v ((i ( x \<mapsto>s))) v1 s1" using V_cons by blast
  thus ?case using eval_v_consI * by meson
next
  case (V_consp tyid dc b1 v1)

  hence "atom x \<sharp> v1" using v.supp by simp
  moreover obtain s1 where *: "eval_v i v1 s1 \<and> s' = SConsp tyid dc b1 s1" using eval_v_elims V_consp by metis
  ultimately have "eval_v ((i ( x \<mapsto>s))) v1 s1" using V_consp by blast
  thus ?case using eval_v_conspI * by meson
qed

lemma eval_e_i_upd:
  fixes e::ce
  assumes "i \<lbrakk> e \<rbrakk> ~ s'" and "atom x \<sharp> e"
  shows " (i ( x \<mapsto>s)) \<lbrakk> e \<rbrakk> ~ s'"
  using assms apply(induct rule: eval_e.induct) using eval_v_i_upd eval_e_elims
  by (meson ce.fresh eval_e.intros)+

lemma eval_c_i_upd:
  fixes c::c
  assumes "i \<lbrakk> c \<rbrakk> ~ s'" and "atom x \<sharp> c"
  shows "((i ( x \<mapsto>s))) \<lbrakk> c \<rbrakk> ~ s' "
  using assms proof(induct rule:eval_c.induct)
  case (eval_c_eqI i e1 sv1 e2 sv2)
  then show ?case using RCLogic.eval_c_eqI eval_e_i_upd c.fresh by metis
qed(simp add: eval_c.intros)+

lemma subst_v_eval_v[simp]:
  fixes v::v and v'::v
  assumes "i \<lbrakk> v \<rbrakk> ~  s" and "i \<lbrakk> (v'[x::=v]\<^sub>v\<^sub>v) \<rbrakk> ~ s'"
  shows "(i ( x \<mapsto> s )) \<lbrakk> v' \<rbrakk> ~ s'"
  using assms proof(nominal_induct v' arbitrary: s' rule:v.strong_induct)
  case (V_lit x)
  then show ?case using subst_vv.simps
    by (metis eval_v_elims(1) eval_v_litI)
next
  case (V_var x')
  then show ?case proof(cases "x=x'")
    case True
    hence "(V_var x')[x::=v]\<^sub>v\<^sub>v = v" using subst_vv.simps by auto
    then show ?thesis using V_var eval_v_elims eval_v_varI eval_v_uniqueness True
      by (simp add: eval_v.eval_v_varI)
  next
    case False
    hence "atom x \<sharp> (V_var x')" by simp
    then show ?thesis using eval_v_i_upd False V_var by fastforce
  qed
next
  case (V_pair v1 v2)
  then obtain s1 and s2 where *:"eval_v i (v1[x::=v]\<^sub>v\<^sub>v) s1 \<and> eval_v i (v2[x::=v]\<^sub>v\<^sub>v) s2 \<and> s' = SPair s1 s2" using V_pair eval_v_elims subst_vv.simps by metis
  hence "(i ( x \<mapsto> s )) \<lbrakk> v1 \<rbrakk> ~ s1 \<and> (i ( x \<mapsto> s )) \<lbrakk> v2 \<rbrakk> ~ s2" using V_pair by metis
  thus  ?case  using eval_v_pairI subst_vv.simps * V_pair by metis
next
  case (V_cons tyid dc v1)
  then obtain s1 where "eval_v i (v1[x::=v]\<^sub>v\<^sub>v) s1" using eval_v_elims subst_vv.simps by metis
  thus ?case  using eval_v_consI V_cons
    by (metis eval_v_elims subst_vv.simps)
next
  case (V_consp tyid dc b1 v1)

  then obtain s1 where *:"eval_v i (v1[x::=v]\<^sub>v\<^sub>v) s1 \<and> s' = SConsp tyid dc b1 s1" using eval_v_elims subst_vv.simps by metis
  hence "i ( x \<mapsto> s ) \<lbrakk> v1 \<rbrakk> ~ s1" using V_consp by metis
  thus ?case  using * eval_v_conspI by metis 
qed

lemma subst_e_eval_v[simp]:
  fixes y::x and e::ce and v::v and e'::ce
  assumes  "i \<lbrakk> e' \<rbrakk> ~  s'" and "e'=(e[y::=v]\<^sub>c\<^sub>e\<^sub>v)" and "i \<lbrakk> v \<rbrakk> ~  s"
  shows "(i ( y \<mapsto> s )) \<lbrakk> e \<rbrakk> ~ s'"
  using assms proof(induct arbitrary: e rule: eval_e.induct)
  case (eval_e_valI i v1 sv)
  then obtain v1' where *:"e = CE_val v1' \<and> v1 = v1'[y::=v]\<^sub>v\<^sub>v"
    using assms by(nominal_induct e rule:ce.strong_induct,simp+)
  hence "eval_v i (v1'[y::=v]\<^sub>v\<^sub>v) sv" using eval_e_valI by simp
  hence "eval_v (i ( y \<mapsto> s )) v1' sv" using subst_v_eval_v eval_e_valI by simp
  then show ?case using RCLogic.eval_e_valI * by meson
next
  case (eval_e_plusI i v1 n1 v2 n2)
  then obtain v1' and v2' where *:"e = CE_op Plus v1' v2' \<and> v1 = v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v \<and> v2 = v2'[y::=v]\<^sub>c\<^sub>e\<^sub>v"
    using assms by(nominal_induct e rule:ce.strong_induct,simp+)
  hence "eval_e i (v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SNum n1) \<and> eval_e i (v2'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SNum n2)" using eval_e_plusI by simp
  hence "eval_e (i ( y \<mapsto> s )) v1' (SNum n1) \<and>  eval_e (i ( y \<mapsto> s )) v2' (SNum n2)" using subst_v_eval_v eval_e_plusI 
    using "local.*" by blast
  then show ?case using RCLogic.eval_e_plusI * by meson
next
  case (eval_e_leqI i v1 n1 v2 n2)
  then obtain v1' and v2' where *:"e = CE_op LEq v1' v2' \<and> v1 = v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v \<and> v2 = v2'[y::=v]\<^sub>c\<^sub>e\<^sub>v"
    using assms by(nominal_induct e rule:ce.strong_induct,simp+)
  hence "eval_e i (v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SNum n1) \<and> eval_e i (v2'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SNum n2)" using eval_e_leqI by simp
  hence "eval_e (i ( y \<mapsto> s )) v1' (SNum n1) \<and>  eval_e (i ( y \<mapsto> s )) v2' (SNum n2)" using subst_v_eval_v eval_e_leqI 
    using * by blast
  then show ?case using RCLogic.eval_e_leqI * by meson
next
  case (eval_e_eqI i v1 n1 v2 n2)
  then obtain v1' and v2' where *:"e = CE_op Eq v1' v2' \<and> v1 = v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v \<and> v2 = v2'[y::=v]\<^sub>c\<^sub>e\<^sub>v"
    using assms by(nominal_induct e rule:ce.strong_induct,simp+)
  hence "eval_e i (v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v) n1 \<and> eval_e i (v2'[y::=v]\<^sub>c\<^sub>e\<^sub>v) n2" using eval_e_eqI by simp
  hence "eval_e (i ( y \<mapsto> s )) v1' n1 \<and>  eval_e (i ( y \<mapsto> s )) v2' n2" using subst_v_eval_v eval_e_eqI 
    using * by blast
  then show ?case using RCLogic.eval_e_eqI * by meson
next
  case (eval_e_fstI i v1 s1 s2)
  then obtain v1' and v2' where *:"e = CE_fst v1' \<and> v1 = v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v"
    using assms by(nominal_induct e rule:ce.strong_induct,simp+)
  hence "eval_e i (v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SPair s1 s2)" using eval_e_fstI by simp
  hence "eval_e (i ( y \<mapsto> s )) v1' (SPair s1 s2)" using eval_e_fstI * by metis
  then show ?case using RCLogic.eval_e_fstI * by meson
next
  case (eval_e_sndI i v1 s1 s2)
  then obtain v1' and v2' where *:"e = CE_snd v1' \<and> v1 = v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v"
    using assms by(nominal_induct e rule:ce.strong_induct,simp+)
  hence "eval_e i (v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SPair s1 s2)" using eval_e_sndI by simp
  hence "eval_e (i ( y \<mapsto> s )) v1' (SPair s1 s2)" using subst_v_eval_v eval_e_sndI * by blast
  then show ?case using RCLogic.eval_e_sndI * by meson
next
  case (eval_e_concatI i v1 bv1 v2 bv2)
  then obtain v1' and v2' where *:"e = CE_concat v1' v2' \<and> v1 = v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v \<and> v2 = v2'[y::=v]\<^sub>c\<^sub>e\<^sub>v"
    using assms by(nominal_induct e rule:ce.strong_induct,simp+)
  hence "eval_e i (v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SBitvec bv1) \<and> eval_e i (v2'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SBitvec bv2)" using eval_e_concatI by simp
  moreover hence "eval_e (i ( y \<mapsto> s )) v1' (SBitvec bv1) \<and>  eval_e (i ( y \<mapsto> s )) v2' (SBitvec bv2)" 
    using subst_v_eval_v eval_e_concatI * by blast
  ultimately show ?case using RCLogic.eval_e_concatI * eval_v_uniqueness  by (metis eval_e_concatI.hyps(1))
next
  case (eval_e_lenI i v1 bv)
  then obtain v1' where *:"e = CE_len v1' \<and> v1 = v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v"
    using assms by(nominal_induct e rule:ce.strong_induct,simp+)
  hence "eval_e i (v1'[y::=v]\<^sub>c\<^sub>e\<^sub>v) (SBitvec bv)" using eval_e_lenI by simp
  hence "eval_e (i ( y \<mapsto> s )) v1' (SBitvec bv)" using subst_v_eval_v eval_e_lenI * by blast
  then show ?case using RCLogic.eval_e_lenI * by meson
qed

lemma subst_c_eval_v[simp]:
  fixes v::v and c :: c
  assumes "i \<lbrakk> v \<rbrakk> ~  s" and "i \<lbrakk> c[x::=v]\<^sub>c\<^sub>v \<rbrakk> ~ s1" and
    "(i ( x \<mapsto> s)) \<lbrakk> c \<rbrakk> ~ s2"
  shows "s1 = s2"
  using assms proof(nominal_induct c arbitrary: s1 s2 rule: c.strong_induct)
  case C_true
  hence "s1 = True \<and> s2 = True" using eval_c_elims subst_cv.simps  by auto
  then show ?case by auto
next
  case C_false
  hence "s1 = False \<and> s2 = False" using eval_c_elims subst_cv.simps by metis
  then show ?case by auto
next
  case (C_conj c1 c2)
  hence *:"eval_c i (c1[x::=v]\<^sub>c\<^sub>v AND c2[x::=v]\<^sub>c\<^sub>v) s1" using subst_cv.simps by auto
  then obtain s11 and s12 where "(s1 = (s11 \<and> s12)) \<and> eval_c i c1[x::=v]\<^sub>c\<^sub>v s11 \<and> eval_c i c2[x::=v]\<^sub>c\<^sub>v s12" using
      eval_c_elims(3) by metis
  moreover obtain   s21 and s22 where "eval_c  (i ( x \<mapsto> s)) c1 s21 \<and> eval_c  (i ( x \<mapsto> s)) c2 s22 \<and> (s2 = (s21 \<and> s22))" using
      eval_c_elims(3) C_conj by metis
  ultimately show ?case using C_conj  by (meson eval_c_elims)
next
  case (C_disj c1 c2)
  hence *:"eval_c i (c1[x::=v]\<^sub>c\<^sub>v OR c2[x::=v]\<^sub>c\<^sub>v) s1" using subst_cv.simps by auto
  then obtain s11 and s12 where "(s1 = (s11 \<or> s12)) \<and> eval_c i c1[x::=v]\<^sub>c\<^sub>v s11 \<and> eval_c i c2[x::=v]\<^sub>c\<^sub>v s12" using
      eval_c_elims(4) by metis
  moreover obtain   s21 and s22 where "eval_c  (i ( x \<mapsto> s)) c1 s21 \<and> eval_c  (i ( x \<mapsto> s)) c2 s22 \<and> (s2 = (s21 \<or> s22))" using
      eval_c_elims(4) C_disj by metis
  ultimately show ?case using C_disj  by (meson eval_c_elims)
next
  case (C_not c1)
  then obtain s11 where "(s1 = (\<not> s11)) \<and> eval_c i c1[x::=v]\<^sub>c\<^sub>v s11" using
      eval_c_elims(6)  by (metis subst_cv.simps(7))
  moreover obtain   s21 where "eval_c  (i ( x \<mapsto> s)) c1 s21 \<and> (s2 = (\<not>s21))" using
      eval_c_elims(6) C_not by metis
  ultimately show ?case using C_not  by (meson eval_c_elims)
next
  case (C_imp c1 c2)
  hence *:"eval_c i (c1[x::=v]\<^sub>c\<^sub>v IMP c2[x::=v]\<^sub>c\<^sub>v) s1" using subst_cv.simps by auto
  then obtain s11 and s12 where "(s1 = (s11 \<longrightarrow> s12)) \<and> eval_c i c1[x::=v]\<^sub>c\<^sub>v s11 \<and> eval_c i c2[x::=v]\<^sub>c\<^sub>v s12" using
      eval_c_elims(5) by metis
  moreover obtain   s21 and s22 where "eval_c  (i ( x \<mapsto> s)) c1 s21 \<and> eval_c  (i ( x \<mapsto> s)) c2 s22 \<and> (s2 = (s21 \<longrightarrow> s22))" using
      eval_c_elims(5) C_imp by metis
  ultimately show ?case using C_imp  by (meson eval_c_elims)
next
  case (C_eq e1 e2)
  hence *:"eval_c i (e1[x::=v]\<^sub>c\<^sub>e\<^sub>v == e2[x::=v]\<^sub>c\<^sub>e\<^sub>v) s1" using subst_cv.simps by auto
  then obtain s11 and s12 where "(s1 = (s11 = s12)) \<and> eval_e i (e1[x::=v]\<^sub>c\<^sub>e\<^sub>v) s11 \<and> eval_e i (e2[x::=v]\<^sub>c\<^sub>e\<^sub>v) s12" using
      eval_c_elims(7) by metis
  moreover obtain   s21 and s22 where "eval_e  (i ( x \<mapsto> s)) e1 s21 \<and> eval_e  (i ( x \<mapsto> s)) e2 s22 \<and> (s2 = (s21 = s22))" using
      eval_c_elims(7) C_eq by metis
  ultimately show ?case using C_eq subst_e_eval_v  by (metis eval_e_uniqueness)
qed

lemma wfI_upd:
  assumes  "wfI \<Theta> \<Gamma> i" and "wfRCV \<Theta> s b" and "wfG \<Theta> B ((x, b, c) #\<^sub>\<Gamma> \<Gamma>)"
  shows "wfI \<Theta> ((x, b, c) #\<^sub>\<Gamma> \<Gamma>) (i(x \<mapsto> s))"
proof(subst wfI_def,rule)
  fix xa
  assume as:"xa \<in> toSet ((x, b, c) #\<^sub>\<Gamma> \<Gamma>)"

  then obtain x1::x and b1::b and c1::c where xa: "xa = (x1,b1,c1)" using toSet.simps
    using prod_cases3 by blast

  have "\<exists>sa. Some sa = (i(x \<mapsto> s)) x1 \<and> wfRCV \<Theta> sa b1" proof(cases "x=x1")
    case True
    hence "b=b1" using as xa wfG_unique assms by metis
    hence "Some s = (i(x \<mapsto> s)) x1 \<and> wfRCV \<Theta> s b1" using assms True by simp
    then show ?thesis by auto
  next
    case False
    hence "(x1,b1,c1) \<in> toSet \<Gamma>" using xa as by auto
    then obtain sa where "Some sa = i x1 \<and> wfRCV \<Theta> sa b1" using assms wfI_def as xa by auto
    hence "Some sa = (i(x \<mapsto> s)) x1 \<and> wfRCV \<Theta> sa b1" using False by auto
    then show ?thesis by auto
  qed

  thus  "case xa of (xa, ba, ca) \<Rightarrow> \<exists>sa. Some sa = (i(x \<mapsto> s)) xa \<and> wfRCV \<Theta> sa ba" using xa by auto
qed

lemma wfI_upd_full:
  fixes v::v
  assumes  "wfI \<Theta> G i" and "G =  ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)@\<Gamma>)" and "wfRCV \<Theta> s b" and "wfG \<Theta> B  (\<Gamma>'@((x,b,c)#\<^sub>\<Gamma>\<Gamma>))" and "\<Theta> ; B  ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b"
  shows "wfI \<Theta>  (\<Gamma>'@((x,b,c)#\<^sub>\<Gamma>\<Gamma>)) (i(x \<mapsto> s))"
proof(subst wfI_def,rule)
  fix xa
  assume as:"xa \<in> toSet (\<Gamma>'@((x,b,c)#\<^sub>\<Gamma>\<Gamma>))"

  then obtain x1::x and b1::b and c1::c where xa: "xa = (x1,b1,c1)" using toSet.simps
    using prod_cases3 by blast

  have "\<exists>sa. Some sa = (i(x \<mapsto> s)) x1 \<and> wfRCV \<Theta> sa b1"
  proof(cases "x=x1")
    case True
    hence "b=b1" using as xa wfG_unique_full assms by metis
    hence "Some s = (i(x \<mapsto> s)) x1 \<and> wfRCV \<Theta> s b1" using assms True by simp
    then show ?thesis by auto
  next
    case False
    hence "(x1,b1,c1) \<in> toSet (\<Gamma>'@\<Gamma>)" using as xa by auto
    then obtain c1' where  "(x1,b1,c1') \<in> toSet (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v@\<Gamma>)" using xa as wfG_member_subst assms  False by metis
    then obtain sa where "Some sa = i x1 \<and> wfRCV \<Theta> sa b1" using assms wfI_def as xa by blast
    hence "Some sa = (i(x \<mapsto> s)) x1 \<and> wfRCV \<Theta> sa b1" using False by auto
    then show ?thesis by auto
  qed

  thus  "case xa of (xa, ba, ca) \<Rightarrow> \<exists>sa. Some sa = (i(x \<mapsto> s)) xa \<and> wfRCV \<Theta> sa ba" using xa by auto
qed

lemma subst_c_satis[simp]:
  fixes v::v
  assumes "i \<lbrakk> v \<rbrakk> ~  s" and "wfC \<Theta> B ((x,b,c')#\<^sub>\<Gamma>\<Gamma>) c" and "wfI \<Theta> \<Gamma> i" and  "\<Theta> ; B  ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b"
  shows "i \<Turnstile> (c[x::=v]\<^sub>c\<^sub>v) \<longleftrightarrow> (i ( x \<mapsto> s)) \<Turnstile> c"
proof -
  have "wfI \<Theta> ((x, b, c') #\<^sub>\<Gamma> \<Gamma>) (i(x \<mapsto> s))" using wfI_upd assms wfC_wf eval_v_base by blast
  then obtain s1 where s1:"eval_c (i(x \<mapsto> s)) c s1"  using  eval_c_exist[of \<Theta> "((x,b,c')#\<^sub>\<Gamma>\<Gamma>)" "(i ( x \<mapsto> s))" B c ] assms by auto

  have "\<Theta> ; B  ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c[x::=v]\<^sub>c\<^sub>v" using wf_subst1(2)[OF assms(2) _ assms(4) , of GNil x   ] subst_gv.simps by simp
  then obtain s2 where s2:"eval_c i c[x::=v]\<^sub>c\<^sub>v s2" using eval_c_exist[of \<Theta> "\<Gamma>" "i" B "c[x::=v]\<^sub>c\<^sub>v"  ] assms by auto

  show ?thesis using s1 s2 subst_c_eval_v[OF assms(1) s2 s1] is_satis.cases
    using eval_c_uniqueness is_satis.simps by auto
qed

text \<open> Key theorem telling us we can replace a substitution with an update to the valuation \<close>
lemma subst_c_satis_full:
  fixes v::v and \<Gamma>'::\<Gamma>
  assumes "i \<lbrakk> v \<rbrakk> ~  s" and "wfC \<Theta> B  (\<Gamma>'@((x,b,c')#\<^sub>\<Gamma>\<Gamma>)) c" and "wfI \<Theta>  ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)@\<Gamma>) i" and  "\<Theta> ; B  ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : b"
  shows "i \<Turnstile> (c[x::=v]\<^sub>c\<^sub>v) \<longleftrightarrow> (i ( x \<mapsto> s)) \<Turnstile> c"
proof -
  have "wfI \<Theta> (\<Gamma>'@((x, b, c')) #\<^sub>\<Gamma> \<Gamma>) (i(x \<mapsto> s))" using wfI_upd_full assms wfC_wf eval_v_base wfI_suffix wfI_def wfV_wf by fast
  then obtain s1 where s1:"eval_c (i(x \<mapsto> s)) c s1" using  eval_c_exist[of \<Theta> "(\<Gamma>'@(x,b,c')#\<^sub>\<Gamma>\<Gamma>)" "(i ( x \<mapsto> s))" B c ] assms by auto

  have "\<Theta> ; B ; ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)@\<Gamma>) \<turnstile>\<^sub>w\<^sub>f c[x::=v]\<^sub>c\<^sub>v" using wbc_subst assms by auto

  then obtain s2 where s2:"eval_c i c[x::=v]\<^sub>c\<^sub>v s2" using eval_c_exist[of \<Theta> "((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v)@\<Gamma>)" "i" B "c[x::=v]\<^sub>c\<^sub>v" ] assms by auto

  show ?thesis using s1 s2 subst_c_eval_v[OF assms(1) s2 s1] is_satis.cases
    using eval_c_uniqueness is_satis.simps by auto
qed

section \<open>Validity\<close>

lemma validI[intro]:
  fixes c::c
  assumes  "wfC P B G c" and "\<forall>i. P ; G \<turnstile> i \<and> i \<Turnstile> G \<longrightarrow> i \<Turnstile> c"
  shows "P ; B ; G \<Turnstile> c"
  using assms valid.simps by presburger

lemma valid_g_wf:
  fixes c::c and G::\<Gamma>
  assumes "P ; B ; G \<Turnstile> c"
  shows "P ; B \<turnstile>\<^sub>w\<^sub>f G"
  using assms wfC_wf valid.simps by blast

lemma valid_reflI [intro]:
  fixes b::b
  assumes  "P ; B ; ((x,b,c1)#\<^sub>\<Gamma>G) \<turnstile>\<^sub>w\<^sub>f c1" and "c1 = c2"
  shows "P ; B ; ((x,b,c1)#\<^sub>\<Gamma>G) \<Turnstile> c2"
  using satis_reflI assms by simp

subsection \<open>Weakening and Strengthening\<close>

text \<open> Adding to the domain of a valuation doesn't change the result \<close>

lemma eval_v_weakening:
  fixes c::v and B::"bv fset"
  assumes "i = i'|` d" and "supp c \<subseteq> atom ` d \<union> supp B "  and "i \<lbrakk> c \<rbrakk> ~ s"
  shows "i' \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(nominal_induct c arbitrary:s rule: v.strong_induct)
  case (V_lit x)
  then show ?case using eval_v_elims eval_v_litI by metis
next
  case (V_var x)
  have "atom x \<in> atom ` d" using x_not_in_b_set[of x B] assms v.supp(2) supp_at_base 
  proof -
    show ?thesis
      by (metis UnE V_var.prems(2) \<open>atom x \<notin> supp B\<close> singletonI subset_iff supp_at_base v.supp(2)) (* 46 ms *)
  qed 
  moreover have "Some s = i x" using assms eval_v_elims(2) 
    using V_var.prems(3) by blast
  hence "Some s= i' x" using assms insert_subset restrict_in  
  proof -
    show ?thesis
      by (metis (no_types) \<open>i = i' |` d\<close> \<open>Some s = i x\<close> atom_eq_iff calculation imageE restrict_in) (* 31 ms *)
  qed
  thus ?case using eval_v.eval_v_varI by simp

next
  case (V_pair v1 v2)
  then show ?case using eval_v_elims(3) eval_v_pairI v.supp
    by (metis assms le_sup_iff)
next
  case (V_cons dc v1)
  then show ?case using eval_v_elims(4) eval_v_consI v.supp
    by (metis assms le_sup_iff)
next
  case (V_consp tyid dc b1 v1)

  then obtain sv1 where *:"i \<lbrakk> v1 \<rbrakk> ~ sv1 \<and> s = SConsp tyid dc b1 sv1" using eval_v_elims by metis
  hence "i' \<lbrakk> v1 \<rbrakk> ~ sv1" using V_consp by auto 
  then show ?case using * eval_v_conspI v.supp eval_v.simps  assms le_sup_iff by metis
qed

lemma eval_v_restrict:
  fixes c::v and B::"bv fset"
  assumes "i = i' |` d" and "supp c \<subseteq> atom ` d \<union> supp B "  and "i' \<lbrakk> c \<rbrakk> ~ s"
  shows "i \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(nominal_induct c arbitrary:s rule: v.strong_induct)
  case (V_lit x)
  then show ?case using eval_v_elims eval_v_litI by metis
next
  case (V_var x)
  have "atom x \<in> atom ` d" using x_not_in_b_set[of x B] assms v.supp(2) supp_at_base 
  proof -
    show ?thesis
      by (metis UnE V_var.prems(2) \<open>atom x \<notin> supp B\<close> singletonI subset_iff supp_at_base v.supp(2)) (* 46 ms *)
  qed 
  moreover have "Some s = i' x" using assms eval_v_elims(2) 
    using V_var.prems(3) by blast
  hence "Some s= i x" using assms insert_subset restrict_in  
  proof -
    show ?thesis
      by (metis (no_types) \<open>i = i' |` d\<close> \<open>Some s = i' x\<close> atom_eq_iff calculation imageE restrict_in) (* 31 ms *)
  qed
  thus ?case using eval_v.eval_v_varI by simp
next
  case (V_pair v1 v2)
  then show ?case using eval_v_elims(3) eval_v_pairI v.supp
    by (metis assms le_sup_iff)
next
  case (V_cons dc v1)
  then show ?case using eval_v_elims(4) eval_v_consI v.supp
    by (metis assms le_sup_iff)
next
  case (V_consp tyid dc b1 v1)
  then obtain sv1 where *:"i' \<lbrakk> v1 \<rbrakk> ~ sv1 \<and> s = SConsp tyid dc b1 sv1" using eval_v_elims by metis
  hence "i \<lbrakk> v1 \<rbrakk> ~ sv1" using V_consp by auto 
  then show ?case using * eval_v_conspI v.supp eval_v.simps  assms le_sup_iff by metis
qed

lemma eval_e_weakening:
  fixes e::ce and B::"bv fset"
  assumes  "i \<lbrakk> e \<rbrakk> ~ s" and "i = i' |` d" and "supp e \<subseteq> atom ` d \<union> supp B "
  shows "i' \<lbrakk> e \<rbrakk> ~ s"
  using assms proof(induct rule: eval_e.induct)
  case (eval_e_valI i v sv)
  then show ?case using ce.supp eval_e.intros
    using eval_v_weakening by auto
next
  case (eval_e_plusI i v1 n1 v2 n2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_weakening by auto
next
  case (eval_e_leqI i v1 n1 v2 n2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_weakening by auto
next
  case (eval_e_eqI i v1 n1 v2 n2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_weakening by auto
next
  case (eval_e_fstI i v v1 v2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_weakening by metis
next
  case (eval_e_sndI i v v1 v2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_weakening by metis
next
  case (eval_e_concatI i v1 bv2 v2 bv1)
  then show ?case using ce.supp eval_e.intros
    using eval_v_weakening by auto
next
  case (eval_e_lenI i v bv)
  then show ?case using ce.supp eval_e.intros
    using eval_v_weakening by auto
qed

lemma eval_e_restrict :
  fixes e::ce and B::"bv fset"
  assumes  "i' \<lbrakk> e \<rbrakk> ~ s" and "i = i' |` d" and "supp e \<subseteq> atom ` d \<union> supp B "
  shows "i \<lbrakk> e \<rbrakk> ~ s"
  using assms proof(induct rule: eval_e.induct)
  case (eval_e_valI i v sv)
  then show ?case using ce.supp eval_e.intros
    using eval_v_restrict by auto
next
  case (eval_e_plusI i v1 n1 v2 n2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_restrict by auto
next
  case (eval_e_leqI i v1 n1 v2 n2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_restrict by auto
next
  case (eval_e_eqI i v1 n1 v2 n2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_restrict by auto
next
  case (eval_e_fstI i v v1 v2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_restrict by metis
next
  case (eval_e_sndI i v v1 v2)
  then show ?case using ce.supp eval_e.intros
    using eval_v_restrict by metis
next
  case (eval_e_concatI i v1 bv2 v2 bv1)
  then show ?case using ce.supp eval_e.intros
    using eval_v_restrict by auto
next
  case (eval_e_lenI i v bv)
  then show ?case using ce.supp eval_e.intros
    using eval_v_restrict by auto
qed

lemma eval_c_i_weakening:
  fixes c::c and B::"bv fset"
  assumes  "i \<lbrakk> c \<rbrakk> ~ s" and "i = i' |` d" and "supp c \<subseteq> atom ` d \<union> supp B"
  shows "i' \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(induct rule:eval_c.induct)
  case (eval_c_eqI i e1 sv1 e2 sv2)
  then show ?case  using eval_c.intros eval_e_weakening by auto
qed(auto simp add: eval_c.intros)+

lemma eval_c_i_restrict:
  fixes c::c and B::"bv fset"
  assumes  "i' \<lbrakk> c \<rbrakk> ~ s" and "i = i' |` d" and "supp c \<subseteq> atom ` d \<union> supp B"
  shows "i \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(induct rule:eval_c.induct)
  case (eval_c_eqI i e1 sv1 e2 sv2)
  then show ?case  using eval_c.intros eval_e_restrict by auto
qed(auto simp add: eval_c.intros)+

lemma is_satis_i_weakening:
  fixes c::c and B::"bv fset"
  assumes "i = i' |` d" and "supp c \<subseteq> atom ` d  \<union> supp B " and  "i \<Turnstile> c"
  shows "i' \<Turnstile> c"
  using is_satis.simps eval_c_i_weakening[OF _ assms(1) assms(2) ]
  using assms(3) by auto

lemma is_satis_i_restrict:
  fixes c::c and B::"bv fset"
  assumes "i = i' |` d" and "supp c \<subseteq> atom ` d  \<union> supp B" and  "i' \<Turnstile> c"
  shows "i \<Turnstile> c"
  using is_satis.simps eval_c_i_restrict[OF _ assms(1) assms(2) ]
  using assms(3) by auto

lemma is_satis_g_restrict1:
  fixes \<Gamma>'::\<Gamma> and  \<Gamma>::\<Gamma>
  assumes "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "i \<Turnstile> \<Gamma>'"
  shows "i \<Turnstile> \<Gamma>"
  using assms proof(induct \<Gamma> rule: \<Gamma>.induct)
  case GNil
  then show ?case by auto
next
  case (GCons xbc G)
  obtain x and b and c::c where xbc: "xbc=(x,b,c)"
    using prod_cases3 by blast
  hence "i \<Turnstile> G" using GCons by auto
  moreover have "i \<Turnstile> c" using GCons
      is_satis_iff toSet.simps  subset_iff
    using xbc by blast
  ultimately show ?case using is_satis_g.simps GCons
    by (simp add: xbc)
qed

lemma is_satis_g_restrict2:
  fixes \<Gamma>'::\<Gamma> and  \<Gamma>::\<Gamma>
  assumes "i \<Turnstile> \<Gamma>" and  "i' = i |` d" and "atom_dom \<Gamma> \<subseteq> atom ` d" and "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
  shows "i' \<Turnstile> \<Gamma>"
  using assms proof(induct \<Gamma> rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x b c G)

  hence "i' \<Turnstile> G" proof -
    have "i \<Turnstile> G" using GCons  by simp
    moreover have "atom_dom G \<subseteq> atom ` d" using  GCons by simp
    ultimately show ?thesis using GCons wfG_cons2 by blast
  qed

  moreover have "i' \<Turnstile> c" proof -
    have "i \<Turnstile> c" using GCons  by auto
    moreover have "\<Theta> ; B ; (x, b, TRUE) #\<^sub>\<Gamma> G   \<turnstile>\<^sub>w\<^sub>f c"  using wfG_wfC GCons by simp
    moreover hence "supp c \<subseteq> atom ` d \<union> supp B" using wfC_supp GCons atom_dom_eq by blast
    ultimately show ?thesis using is_satis_i_restrict[of i' i d c] GCons by simp
  qed

  ultimately show ?case by auto
qed

lemma is_satis_g_restrict:
  fixes \<Gamma>'::\<Gamma> and \<Gamma>::\<Gamma>
  assumes "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "i' \<Turnstile> \<Gamma>'" and  "i =   i' |` (fst ` toSet \<Gamma>)"  and "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f \<Gamma>"
  shows "i \<Turnstile> \<Gamma>"
  using assms is_satis_g_restrict1[OF assms(1) assms(2)] is_satis_g_restrict2[OF _ assms(3)] by simp

subsection \<open>Updating valuation\<close>

lemma is_satis_c_i_upd:
  fixes c::c
  assumes "atom x \<sharp> c" and "i \<Turnstile> c"
  shows "((i ( x \<mapsto>s))) \<Turnstile> c"
  using assms eval_c_i_upd is_satis.simps by simp

lemma is_satis_g_i_upd:
  fixes G::\<Gamma>
  assumes "atom x \<sharp> G"  and "i \<Turnstile> G"
  shows "((i ( x \<mapsto>s))) \<Turnstile> G"
  using assms proof(induct G rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' G')

  hence *:"atom x \<sharp> G' \<and> atom x \<sharp> c'"
    using fresh_def fresh_GCons GCons  by force
  moreover hence "is_satis ((i ( x \<mapsto>s))) c'"
    using is_satis_c_i_upd GCons is_satis_g.simps by auto
  moreover have " is_satis_g (i(x \<mapsto> s)) G'" using GCons * by fastforce
  ultimately show ?case
    using GCons is_satis_g.simps(2) by metis
qed

lemma valid_weakening:
  assumes "\<Theta> ; B ; \<Gamma> \<Turnstile> c" and "toSet \<Gamma> \<subseteq> toSet \<Gamma>'" and "wfG \<Theta> B  \<Gamma>'"
  shows  "\<Theta> ; B ; \<Gamma>' \<Turnstile> c"
proof -
  have "wfC \<Theta> B  \<Gamma> c" using assms valid.simps by auto
  hence sp: "supp c \<subseteq> atom `(fst `toSet \<Gamma>) \<union> supp B" using wfX_wfY wfG_elims
    using atom_dom.simps dom.simps wf_supp(2) by metis
  have wfg: "wfG \<Theta> B  \<Gamma>" using assms valid.simps wfC_wf by auto

  moreover have a1: "(\<forall>i. wfI \<Theta> \<Gamma>' i \<and> i \<Turnstile> \<Gamma>' \<longrightarrow> i \<Turnstile> c)" proof(rule allI, rule impI)
    fix i
    assume as: "wfI \<Theta> \<Gamma>' i \<and> i \<Turnstile> \<Gamma>'"
    hence as1: "fst ` toSet \<Gamma> \<subseteq> dom i" using assms wfI_domi by blast
    obtain i' where idash: "i' =  restrict_map i (fst `toSet \<Gamma>)" by blast
    hence as2: "dom i' = (fst `toSet \<Gamma>)"  using dom_restrict as1 by auto

    have id2: "\<Theta> ; \<Gamma> \<turnstile> i' \<and> i' \<Turnstile> \<Gamma>" proof -
      have "wfI \<Theta>  \<Gamma> i'" using as2 wfI_restrict_weakening[of \<Theta> \<Gamma>' i i' \<Gamma>] as  assms
        using idash by blast
      moreover have "i' \<Turnstile> \<Gamma>" using is_satis_g_restrict[OF assms(2)] wfg as idash by auto
      ultimately show ?thesis using idash by auto
    qed
    hence "i' \<Turnstile> c" using assms valid.simps by auto
    thus  "i \<Turnstile> c" using assms valid.simps is_satis_i_weakening  idash sp by blast
  qed
  moreover have "wfC \<Theta> B \<Gamma>' c" using wf_weakening assms valid.simps
    by (meson  wfg)
  ultimately show  ?thesis using assms valid.simps by auto
qed

lemma is_satis_g_suffix:
  fixes G::\<Gamma>
  assumes "i \<Turnstile> (G'@G)"
  shows "i \<Turnstile> G"
  using assms proof(induct G' rule:\<Gamma>.induct)
  case GNil
  then show ?case by auto
next
  case (GCons xbc x2)
  obtain x and b and c::c where xbc: "xbc=(x,b,c)"
    using prod_cases3 by blast
  hence " i \<Turnstile> (xbc #\<^sub>\<Gamma> (x2 @ G))" using append_g.simps GCons by fastforce
  then show ?case using is_satis_g.simps GCons xbc by blast
qed

lemma wfG_inside_valid2:
  fixes x::x and \<Gamma>::\<Gamma> and c0::c and c0'::c
  assumes "wfG \<Theta> B  (\<Gamma>'@((x,b0,c0')#\<^sub>\<Gamma>\<Gamma>))" and
    "\<Theta> ; B ; \<Gamma>'@(x,b0,c0)#\<^sub>\<Gamma>\<Gamma> \<Turnstile> c0'"
  shows "wfG \<Theta> B  (\<Gamma>'@((x,b0,c0)#\<^sub>\<Gamma>\<Gamma>))"
proof -
  have "wfG \<Theta>  B  (\<Gamma>'@(x,b0,c0)#\<^sub>\<Gamma>\<Gamma>)" using valid.simps wfC_wf assms by auto
  thus ?thesis using wfG_replace_inside_full assms by auto
qed

lemma valid_trans:
  assumes   " \<Theta> ; \<B> ; \<Gamma> \<Turnstile> c0[z::=v]\<^sub>v"  and " \<Theta> ; \<B> ; (z,b,c0)#\<^sub>\<Gamma>\<Gamma> \<Turnstile> c1" and "atom z \<sharp> \<Gamma>" and "wfV \<Theta> \<B> \<Gamma> v b" 
  shows " \<Theta> ; \<B> ; \<Gamma> \<Turnstile> c1[z::=v]\<^sub>v"
proof - 
  have *:"wfC \<Theta> \<B> ((z,b,c0)#\<^sub>\<Gamma>\<Gamma>) c1" using valid.simps assms by auto
  hence "wfC \<Theta> \<B> \<Gamma> (c1[z::=v]\<^sub>v)" using wf_subst1(2)[OF * , of GNil ]  assms subst_gv.simps subst_v_c_def by force

  moreover have "\<forall>i. wfI  \<Theta> \<Gamma>   i \<and> is_satis_g i \<Gamma> \<longrightarrow> is_satis i (c1[z::=v]\<^sub>v)" 
  proof(rule,rule)
    fix i
    assume  as: "wfI  \<Theta> \<Gamma>   i \<and> is_satis_g i \<Gamma>"
    then obtain sv where sv: "eval_v i v sv \<and> wfRCV \<Theta> sv b" using eval_v_exist assms by metis
    hence "is_satis i (c0[z::=v]\<^sub>v)" using assms valid.simps as by metis
    hence "is_satis (i(z \<mapsto> sv))  c0" using subst_c_satis sv as assms valid.simps wfC_wf wfG_elim2 subst_v_c_def by metis
    moreover have "is_satis_g  (i(z \<mapsto> sv)) \<Gamma>" 
      using is_satis_g_i_upd  assms  by (simp add: as)
    ultimately have "is_satis_g  (i(z \<mapsto> sv)) ((z,b,c0)#\<^sub>\<Gamma>\<Gamma>)" 
      using is_satis_g.simps by simp
    moreover have "wfI \<Theta> ((z,b,c0)#\<^sub>\<Gamma>\<Gamma>) (i(z \<mapsto> sv))" using as wfI_upd sv assms valid.simps wfC_wf by metis
    ultimately have "is_satis (i(z \<mapsto> sv)) c1" using assms valid.simps by auto
    thus "is_satis i (c1[z::=v]\<^sub>v)" using subst_c_satis sv as assms valid.simps wfC_wf wfG_elim2 subst_v_c_def by metis
  qed

  ultimately show ?thesis using valid.simps by auto
qed

lemma valid_trans_full:
  assumes  "\<Theta> ; \<B> ; ((x, b, c1[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) \<Turnstile> c2[z2::=V_var x]\<^sub>v" and
    "\<Theta> ; \<B> ; ((x, b, c2[z2::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) \<Turnstile> c3[z3::=V_var x]\<^sub>v" 
  shows  "\<Theta> ; \<B> ; ((x, b, c1[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) \<Turnstile> c3[z3::=V_var x]\<^sub>v"
  unfolding valid.simps proof
  show "\<Theta> ; \<B> ; (x, b, c1[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>   \<turnstile>\<^sub>w\<^sub>f c3[z3::=V_var x]\<^sub>v" using wf_trans valid.simps assms by metis

  show "\<forall>i.  ( wfI  \<Theta> ((x, b, c1[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>) i \<and>  (is_satis_g i ((x, b, c1[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>))  \<longrightarrow>  (is_satis i (c3[z3::=V_var x]\<^sub>v)) ) "
  proof(rule,rule)
    fix i
    assume as: "\<Theta> ; (x, b, c1[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma> \<turnstile> i \<and>  i \<Turnstile> (x, b, c1[z1::=V_var x]\<^sub>v) #\<^sub>\<Gamma> \<Gamma>" 
    have "i \<Turnstile> c2[z2::=V_var x]\<^sub>v" using is_satis_g.simps as assms by simp
    moreover have  "i \<Turnstile> \<Gamma>"  using is_satis_g.simps as by simp
    ultimately show "i \<Turnstile> c3[z3::=V_var x]\<^sub>v " using assms is_satis_g.simps valid.simps 
      by (metis append_g.simps(1) as wfI_replace_inside)
  qed
qed

lemma eval_v_weakening_x:
  fixes c::v
  assumes  "i' \<lbrakk> c \<rbrakk> ~ s" and "atom x \<sharp> c" and "i = i' (x \<mapsto> s')"
  shows "i \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(induct rule: eval_v.induct)
  case (eval_v_litI i l)
  then show ?case using eval_v.intros by auto
next
  case (eval_v_varI sv i1 x1)
  hence "x \<noteq> x1" using v.fresh fresh_at_base by auto
  hence "i x1 = Some sv" using eval_v_varI by simp
  then show ?case  using eval_v.intros by auto
next
  case (eval_v_pairI i v1 s1 v2 s2)
  then show ?case  using eval_v.intros by auto
next
  case (eval_v_consI i v s tyid dc)
  then show ?case  using eval_v.intros by auto
next
  case (eval_v_conspI i v s tyid dc b)
  then show ?case  using eval_v.intros by auto
qed

lemma eval_e_weakening_x:
  fixes c::ce
  assumes  "i' \<lbrakk> c \<rbrakk> ~ s" and "atom x \<sharp> c" and "i = i' (x \<mapsto> s')"
  shows "i \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(induct rule: eval_e.induct)
  case (eval_e_valI i v sv)
  then show ?case using  eval_v_weakening_x eval_e.intros  ce.fresh by metis
next
  case (eval_e_plusI i v1 n1 v2 n2)
  then show ?case using  eval_v_weakening_x eval_e.intros  ce.fresh by metis
next
  case (eval_e_leqI i v1 n1 v2 n2)
  then show ?case using  eval_v_weakening_x eval_e.intros  ce.fresh by metis
next
  case (eval_e_eqI i v1 n1 v2 n2)
  then show ?case using  eval_v_weakening_x eval_e.intros  ce.fresh by metis
next
  case (eval_e_fstI i v v1 v2)
  then show ?case using  eval_v_weakening_x eval_e.intros  ce.fresh by metis
next
  case (eval_e_sndI i v v1 v2)
  then show ?case using  eval_v_weakening_x eval_e.intros  ce.fresh by metis
next
  case (eval_e_concatI i v1 bv1 v2 bv2)
  then show ?case using  eval_v_weakening_x eval_e.intros  ce.fresh by metis
next
  case (eval_e_lenI i v bv)
  then show ?case using  eval_v_weakening_x eval_e.intros  ce.fresh by metis
qed

lemma eval_c_weakening_x:
  fixes c::c
  assumes  "i' \<lbrakk> c \<rbrakk> ~ s" and "atom x \<sharp> c" and "i = i' (x \<mapsto> s')"
  shows "i \<lbrakk> c \<rbrakk> ~ s"
  using assms proof(induct rule: eval_c.induct)
  case (eval_c_trueI i)
  then show ?case using eval_c.intros by auto
next
  case (eval_c_falseI i)
  then show ?case using eval_c.intros by auto
next
  case (eval_c_conjI i c1 b1 c2 b2)
  then show ?case using eval_c.intros by auto
next
  case (eval_c_disjI i c1 b1 c2 b2)
  then show ?case using eval_c.intros by auto
next
  case (eval_c_impI i c1 b1 c2 b2)
  then show ?case using eval_c.intros by auto
next
  case (eval_c_notI i c b)
  then show ?case using eval_c.intros by auto
next
  case (eval_c_eqI i e1 sv1 e2 sv2)
  then show ?case using eval_e_weakening_x c.fresh eval_c.intros by metis
qed

lemma is_satis_weakening_x:
  fixes c::c
  assumes "i' \<Turnstile> c" and "atom x \<sharp> c" and "i = i' (x \<mapsto> s)"
  shows "i \<Turnstile> c"
  using eval_c_weakening_x assms is_satis.simps by simp

lemma is_satis_g_weakening_x:
  fixes G::\<Gamma>
  assumes "i' \<Turnstile> G" and "atom x \<sharp> G" and "i = i' (x \<mapsto> s)"
  shows "i \<Turnstile> G"
  using assms proof(induct G rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>')
  hence "atom x \<sharp> c'" using fresh_GCons fresh_prodN by simp
  moreover hence "i \<Turnstile> c'"  using is_satis_weakening_x  is_satis_g.simps(2) GCons by metis
  then show ?case using   is_satis_g.simps(2)[of i x' b' c' \<Gamma>'] GCons fresh_GCons by simp
qed

section \<open>Base Type Substitution\<close>

text \<open>The idea of boxing is to take an smt val and its base type and at nodes in the smt val that correspond to type variables we
wrap them in an SUt smt val node. Another way of looking at it is that s' where the node for the base type variable is an 'any node'.
It is needed to prove subst\_b\_valid - the base-type variable substitution lemma for validity.

The first @{text "rcl_val"} is the expanded form (has type with base-variables replaced with base-type terms)
 ; the second is its corresponding form

We only have one variable so we need to ensure that in all of the  @{text "bs_boxed_BVarI"} cases, the s has the same
  base type.

For example is an SMT value is (SPair (SInt 1) (SBool true)) and it has sort (BPair (BVar x) BBool)[x::=BInt] then 
the boxed version is SPair (SUt (SInt 1)) (SBool true) and is has sort (BPair (BVar x) BBool). We need to do this 
so that we can obtain from a valuation i, that gives values like the first smt value, to a valuation i' that gives values like
the second.
\<close>

inductive  boxed_b :: "\<Theta> \<Rightarrow> rcl_val \<Rightarrow> b \<Rightarrow> bv \<Rightarrow> b \<Rightarrow> rcl_val \<Rightarrow> bool"   ( " _  \<turnstile> _ ~ _ [ _ ::= _ ] \<setminus> _ " [50,50] 50) where    
  boxed_b_BVar1I:  "\<lbrakk> bv = bv' ;  wfRCV P s b \<rbrakk> \<Longrightarrow> boxed_b P s (B_var bv') bv b (SUt s)"
| boxed_b_BVar2I:  "\<lbrakk> bv \<noteq> bv'; wfRCV P s  (B_var bv')  \<rbrakk> \<Longrightarrow> boxed_b P s (B_var bv') bv b s"
| boxed_b_BIntI:"wfRCV P s B_int \<Longrightarrow> boxed_b P s B_int _ _ s"
| boxed_b_BBoolI:"wfRCV P s B_bool \<Longrightarrow> boxed_b P s B_bool _ _ s "
| boxed_b_BUnitI:"wfRCV P s B_unit \<Longrightarrow> boxed_b P s B_unit _ _ s"
| boxed_b_BPairI:"\<lbrakk> boxed_b P s1 b1 bv b s1' ; boxed_b P s2 b2 bv b s2' \<rbrakk> \<Longrightarrow> boxed_b P (SPair s1 s2) (B_pair b1 b2) bv b (SPair s1' s2')"

| boxed_b_BConsI:"\<lbrakk>  
      AF_typedef tyid dclist \<in> set P;
      (dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist ;
      boxed_b P s1 b bv b' s1'
      \<rbrakk> \<Longrightarrow>  
     boxed_b P (SCons tyid dc s1) (B_id tyid) bv b' (SCons tyid dc s1')"

| boxed_b_BConspI:"\<lbrakk>  AF_typedef_poly tyid bva dclist \<in> set P;
      atom bva \<sharp> (b1,bv,b',s1,s1');
      (dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist ;
      boxed_b P s1 (b[bva::=b1]\<^sub>b\<^sub>b) bv b' s1' 
      \<rbrakk> \<Longrightarrow>  
      boxed_b P (SConsp tyid dc b1[bv::=b']\<^sub>b\<^sub>b s1) (B_app tyid b1) bv b' (SConsp tyid dc b1 s1')"

| boxed_b_Bbitvec: "wfRCV P s B_bitvec \<Longrightarrow> boxed_b P s B_bitvec bv b s"

equivariance boxed_b 
nominal_inductive boxed_b .

inductive_cases boxed_b_elims:
  "boxed_b P s (B_var bv) bv' b s'"
  "boxed_b P s B_int bv b s'"
  "boxed_b P s B_bool bv b s'"
  "boxed_b P s B_unit bv b s'"
  "boxed_b P s (B_pair b1 b2) bv b s'"
  "boxed_b P s (B_id dc) bv b s'"
  "boxed_b P s B_bitvec bv b s'"
  "boxed_b P s (B_app dc b') bv b s'"

lemma boxed_b_wfRCV:
  assumes  "boxed_b P s b bv b' s'" (*and "supp s = {}"*) and "\<turnstile>\<^sub>w\<^sub>f P"
  shows "wfRCV P s b[bv::=b']\<^sub>b\<^sub>b \<and> wfRCV P s' b"
  using assms proof(induct rule: boxed_b.inducts)
  case (boxed_b_BVar1I bv bv' P s b )
  then show ?case using wfRCV.intros by auto
next
  case (boxed_b_BVar2I bv bv' P s )
  then show ?case using wfRCV.intros   by auto
next
  case (boxed_b_BPairI P s1 b1 bv b s1' s2 b2 s2')
  then show ?case using wfRCV.intros rcl_val.supp by simp
next
  case (boxed_b_BConsI tyid dclist P dc x b c s1 bv b' s1')
  hence "supp b = {}" using wfTh_supp_b by metis
  hence "b [ bv ::= b' ]\<^sub>b\<^sub>b = b" using fresh_def subst_b_b_def forget_subst[of "bv" b b'] by auto
  hence " P  \<turnstile> SCons tyid dc s1 : (B_id tyid)" using  wfRCV.intros rcl_val.supp subst_bb.simps boxed_b_BConsI by metis
  moreover have "P  \<turnstile> SCons tyid dc s1' : B_id tyid" using boxed_b_BConsI  
    using  wfRCV.intros rcl_val.supp subst_bb.simps boxed_b_BConsI by metis
  ultimately show ?case using subst_bb.simps by metis
next
  case (boxed_b_BConspI tyid bva dclist P b1 bv b' s1 s1' dc x b c)

  obtain bva2 and dclist2 where *:"AF_typedef_poly tyid bva dclist = AF_typedef_poly tyid bva2 dclist2 \<and> 
             atom bva2 \<sharp> (bv,(P, SConsp tyid dc b1[bv::=b']\<^sub>b\<^sub>b s1, B_app tyid b1[bv::=b']\<^sub>b\<^sub>b))" 
    using  obtain_fresh_bv by metis

  then obtain x2 and b2 and c2 where **:\<open>(dc, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2\<close>  
    using boxed_b_BConspI td_lookup_eq_iff type_def.eq_iff by metis

  have  "P  \<turnstile> SConsp tyid dc b1[bv::=b']\<^sub>b\<^sub>b s1 : (B_app tyid b1[bv::=b']\<^sub>b\<^sub>b)" proof
    show 1: \<open>AF_typedef_poly tyid bva2 dclist2 \<in> set P\<close> using boxed_b_BConspI * by auto
    show 2: \<open>(dc, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2\<close> using boxed_b_BConspI using ** by simp

    hence "atom bv \<sharp> b2" proof -
      have "supp b2 \<subseteq> { atom bva2 }" using wfTh_poly_supp_b 1 2 boxed_b_BConspI by auto
      moreover have "bv \<noteq> bva2" using  * fresh_Pair fresh_at_base by metis
      ultimately show  ?thesis  using fresh_def by force
    qed
    moreover have "b[bva::=b1]\<^sub>b\<^sub>b = b2[bva2::=b1]\<^sub>b\<^sub>b"  using wfTh_typedef_poly_b_eq_iff * 2 boxed_b_BConspI by metis
    ultimately show \<open> P  \<turnstile> s1 : b2[bva2::=b1[bv::=b']\<^sub>b\<^sub>b]\<^sub>b\<^sub>b\<close> using boxed_b_BConspI subst_b_b_def subst_bb_commute by auto
    show "atom bva2 \<sharp> (P, SConsp tyid dc b1[bv::=b']\<^sub>b\<^sub>b s1, B_app tyid b1[bv::=b']\<^sub>b\<^sub>b)" using * fresh_Pair by metis
  qed

  moreover have "P  \<turnstile> SConsp tyid dc b1 s1' : B_app tyid b1" proof
    show \<open>AF_typedef_poly tyid bva dclist \<in> set P\<close> using boxed_b_BConspI by auto
    show \<open>(dc, \<lbrace> x : b  | c \<rbrace>) \<in> set dclist\<close> using boxed_b_BConspI by auto
    show \<open> P  \<turnstile> s1' : b[bva::=b1]\<^sub>b\<^sub>b\<close> using boxed_b_BConspI by auto
    have "atom bva \<sharp> P" using boxed_b_BConspI wfTh_fresh by metis
    thus  "atom bva \<sharp> (P, SConsp tyid dc b1 s1', B_app tyid b1)" using boxed_b_BConspI rcl_val.fresh b.fresh pure_fresh fresh_prodN by metis
  qed

  ultimately show ?case using subst_bb.simps  by simp
qed(auto)+

lemma subst_b_var:
  assumes  "B_var bv2 = b[bv::=b']\<^sub>b\<^sub>b"
  shows  "(b = B_var bv \<and> b' = B_var bv2) \<or> (b=B_var bv2 \<and> bv \<noteq> bv2)"
  using assms by(nominal_induct b rule: b.strong_induct,auto+)

text \<open>Here the valuation i' is the conv wrap version of i. For every x in G, i' x is the conv wrap version of i x.
The next lemma for a clearer explanation of what this is. i produces values of sort b[bv::=b'] and i' produces values of sort b\<close>

inductive boxed_i :: "\<Theta> \<Rightarrow> \<Gamma> \<Rightarrow> b \<Rightarrow> bv \<Rightarrow> valuation \<Rightarrow> valuation \<Rightarrow> bool"  ( " _  ; _ ; _ , _ \<turnstile> _ \<approx> _" [50,50] 50) where
  boxed_i_GNilI:  "\<Theta> ; GNil ; b , bv  \<turnstile> i \<approx> i"
| boxed_i_GConsI: "\<lbrakk> Some s = i x;  boxed_b \<Theta> s b bv b' s' ;  \<Theta> ; \<Gamma> ; b' , bv \<turnstile> i \<approx> i' \<rbrakk> \<Longrightarrow> \<Theta> ; ((x,b,c)#\<^sub>\<Gamma>\<Gamma>) ; b' , bv \<turnstile> i \<approx> (i'(x \<mapsto> s'))"
equivariance boxed_i
nominal_inductive boxed_i .

inductive_cases boxed_i_elims:
  "\<Theta> ;GNil ; b , bv \<turnstile> i \<approx> i'"
  "\<Theta> ; ((x,b,c)#\<^sub>\<Gamma>\<Gamma>) ; b' , bv \<turnstile> i \<approx> i'"

lemma wfRCV_poly_elims:
  fixes tm::"'a::fs" and b::b
  assumes "T  \<turnstile> SConsp typid dc bdc s : b" 
  obtains bva dclist x1 b1 c1 where "b = B_app typid bdc \<and>
    AF_typedef_poly typid bva dclist \<in> set T \<and> (dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist \<and>  T  \<turnstile> s : b1[bva::=bdc]\<^sub>b\<^sub>b \<and> atom bva \<sharp> tm" 
  using assms proof(nominal_induct "SConsp typid dc bdc s" b avoiding: tm rule:wfRCV.strong_induct)
  case (wfRCV_BConsPI bv dclist \<Theta> x b c)
  then show ?case by simp
qed

lemma boxed_b_ex:
  assumes "wfRCV T s b[bv::=b']\<^sub>b\<^sub>b" and "wfTh T"
  shows "\<exists>s'. boxed_b T s b bv b' s'"
  using assms proof(nominal_induct s arbitrary: b rule: rcl_val.strong_induct)
  case (SBitvec x)
  have *:"b[bv::=b']\<^sub>b\<^sub>b = B_bitvec" using wfRCV_elims(9)[OF SBitvec(1)] by metis
  show ?case proof (cases "b = B_var bv")
    case True
    moreover have "T  \<turnstile> SBitvec x : B_bitvec" using wfRCV.intros by simp
    moreover hence "b' = B_bitvec" using True SBitvec subst_bb.simps * by simp
    ultimately show ?thesis using boxed_b.intros  wfRCV.intros by metis
  next
    case False
    hence "b = B_bitvec" using subst_bb_inject *  by metis  
    then show ?thesis using * SBitvec boxed_b.intros by metis
  qed
next
  case (SNum x)
  have *:"b[bv::=b']\<^sub>b\<^sub>b = B_int" using wfRCV_elims(10)[OF SNum(1)] by metis
  show ?case proof (cases "b = B_var bv")
    case True
    moreover have "T  \<turnstile> SNum x : B_int" using wfRCV.intros by simp
    moreover hence "b' = B_int" using True SNum subst_bb.simps(1) * by simp
    ultimately show ?thesis using boxed_b_BVar1I  wfRCV.intros by metis
  next
    case False
    hence "b = B_int" using subst_bb_inject(1) *  by metis  
    then show ?thesis using * SNum boxed_b_BIntI by metis
  qed
next
  case (SBool x)
  have *:"b[bv::=b']\<^sub>b\<^sub>b = B_bool" using wfRCV_elims(11)[OF SBool(1)] by metis
  show ?case proof (cases "b = B_var bv")
    case True
    moreover have "T  \<turnstile> SBool x : B_bool" using wfRCV.intros by simp
    moreover hence "b' = B_bool" using True SBool subst_bb.simps * by simp
    ultimately show ?thesis using boxed_b.intros  wfRCV.intros by metis
  next
    case False
    hence "b = B_bool" using subst_bb_inject *  by metis  
    then show ?thesis using * SBool boxed_b.intros by metis
  qed
next
  case (SPair s1 s2)
  then obtain b1 and b2 where *:"b[bv::=b']\<^sub>b\<^sub>b = B_pair b1 b2 \<and> wfRCV T s1 b1 \<and> wfRCV T s2 b2" using wfRCV_elims(12)  by metis
  show ?case proof (cases "b = B_var bv")
    case True
    moreover have "T  \<turnstile> SPair s1 s2 : B_pair b1 b2" using wfRCV.intros * by simp
    moreover hence "b' = B_pair b1 b2" using True SPair subst_bb.simps(1) * by simp
    ultimately show ?thesis using boxed_b_BVar1I by metis
  next
    case False
    then obtain b1' and b2' where "b = B_pair b1' b2' \<and> b1=b1'[bv::=b']\<^sub>b\<^sub>b \<and> b2=b2'[bv::=b']\<^sub>b\<^sub>b" using subst_bb_inject(5)[OF _ False ] * by metis
    then show ?thesis using *  SPair boxed_b_BPairI by blast
  qed
next
  case (SCons tyid dc s1)
  have *:"b[bv::=b']\<^sub>b\<^sub>b = B_id tyid" using wfRCV_elims(13)[OF SCons(2)] by metis
  show ?case proof (cases "b = B_var bv")
    case True
    moreover have "T  \<turnstile> SCons tyid dc s1 : B_id tyid" using wfRCV.intros 
      using "local.*" SCons.prems by auto
    moreover hence "b' =  B_id tyid" using True SCons subst_bb.simps(1) * by simp
    ultimately show ?thesis using boxed_b_BVar1I  wfRCV.intros by metis
  next
    case False
    then obtain b1' where beq: "b = B_id tyid" using subst_bb_inject *  by metis  
    then obtain b2 dclist x c where **:"AF_typedef tyid dclist \<in> set T \<and> (dc, \<lbrace> x : b2  | c \<rbrace>) \<in> set dclist \<and> wfRCV T s1 b2" using wfRCV_elims(13)  * SCons by metis
    then have "atom bv \<sharp> b2" using \<open>wfTh T\<close> wfTh_lookup_supp_empty[of tyid dclist T dc "\<lbrace> x : b2  | c \<rbrace>"] \<tau>.fresh fresh_def by auto
    then have "b2 = b2[ bv ::= b']\<^sub>b\<^sub>b" using forget_subst subst_b_b_def by metis
    then obtain s1' where s1:"T  \<turnstile> s1 ~ b2 [ bv ::= b' ] \<setminus> s1'" using SCons ** by metis

    have "T  \<turnstile> SCons tyid dc s1 ~ (B_id tyid) [ bv ::= b' ] \<setminus> SCons tyid dc s1'" proof(rule boxed_b_BConsI)
      show "AF_typedef tyid dclist \<in> set T" using ** by auto
      show "(dc, \<lbrace> x : b2  | c \<rbrace>) \<in> set dclist" using ** by auto
      show "T  \<turnstile> s1 ~ b2 [ bv ::= b' ] \<setminus> s1' " using s1 ** by auto

    qed
    thus ?thesis using beq by metis
  qed
next
  case (SConsp typid dc bdc s)

  obtain bva dclist x1 b1 c1 where **:"b[bv::=b']\<^sub>b\<^sub>b = B_app typid bdc \<and>
    AF_typedef_poly typid bva dclist \<in> set T \<and> (dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist \<and>  T  \<turnstile> s : b1[bva::=bdc]\<^sub>b\<^sub>b \<and> atom bva \<sharp> bv"
    using wfRCV_poly_elims[OF SConsp(2)]  by metis

  then have *:"B_app typid bdc = b[bv::=b']\<^sub>b\<^sub>b" using wfRCV_elims(14)[OF SConsp(2)] by metis
  show ?case proof (cases "b = B_var bv")
    case True
    moreover have "T  \<turnstile> SConsp typid dc bdc s  : B_app typid bdc" using wfRCV.intros 
      using "local.*" SConsp.prems(1) by auto
    moreover hence "b' = B_app typid bdc" using True SConsp subst_bb.simps * by simp
    ultimately show ?thesis using boxed_b.intros  wfRCV.intros by metis
  next
    case False
    then obtain bdc' where bdc: "b = B_app typid bdc' \<and> bdc = bdc'[bv::=b']\<^sub>b\<^sub>b" using * subst_bb_inject(8)[OF *] by metis
        (*hence beq:"b = B_app typid bdc" using subst_bb_inject *  sory (* going to be like the above as bdc is closed *)*)
    have "atom bv \<sharp> b1" proof -
      have "supp b1 \<subseteq> { atom bva }" using wfTh_poly_supp_b ** SConsp by metis
      moreover have "bv \<noteq> bva" using ** by auto
      ultimately show ?thesis using fresh_def by force
    qed      
    have "T  \<turnstile> s : b1[bva::=bdc]\<^sub>b\<^sub>b" using ** by auto
    moreover have "b1[bva::=bdc']\<^sub>b\<^sub>b[bv::=b']\<^sub>b\<^sub>b = b1[bva::=bdc]\<^sub>b\<^sub>b" using bdc subst_bb_commute \<open>atom bv \<sharp> b1\<close> by auto
    ultimately  obtain s' where s':"T  \<turnstile> s ~ b1[bva::=bdc']\<^sub>b\<^sub>b [ bv ::= b' ] \<setminus> s'" 
      using SConsp(1)[of "b1[bva::=bdc']\<^sub>b\<^sub>b"] bdc SConsp by metis
    have "T  \<turnstile> SConsp typid dc bdc'[bv::=b']\<^sub>b\<^sub>b s ~ (B_app typid bdc') [ bv ::= b' ] \<setminus> SConsp typid dc bdc' s'" 
    proof - 

      obtain bva3 and dclist3 where 3:"AF_typedef_poly typid bva3 dclist3 =  AF_typedef_poly typid bva dclist \<and> 
            atom bva3 \<sharp> (bdc', bv, b', s, s')" using obtain_fresh_bv  by metis
      then obtain x3 b3 c3 where 4:"(dc, \<lbrace> x3 : b3  | c3 \<rbrace>) \<in> set dclist3" 
        using boxed_b_BConspI td_lookup_eq_iff type_def.eq_iff 
        by (metis "**")

      show ?thesis proof
        show \<open>AF_typedef_poly typid bva3 dclist3 \<in> set T\<close> using 3 ** by metis 
        show \<open>atom bva3 \<sharp> (bdc', bv, b', s, s')\<close> using 3 by metis
        show 4:\<open>(dc, \<lbrace> x3 : b3  | c3 \<rbrace>) \<in> set dclist3\<close> using 4 by auto
        have "b3[bva3::=bdc']\<^sub>b\<^sub>b = b1[bva::=bdc']\<^sub>b\<^sub>b" proof(rule wfTh_typedef_poly_b_eq_iff)
          show \<open>AF_typedef_poly typid bva3 dclist3 \<in> set T\<close> using 3 ** by metis
          show \<open>(dc, \<lbrace> x3 : b3  | c3 \<rbrace>) \<in> set dclist3\<close> using 4 by auto
          show \<open>AF_typedef_poly typid bva dclist \<in> set T\<close> using ** by auto
          show \<open>(dc, \<lbrace> x1 : b1  | c1 \<rbrace>) \<in> set dclist\<close> using ** by auto
        qed(simp add: ** SConsp)
        thus  \<open> T  \<turnstile> s ~ b3[bva3::=bdc']\<^sub>b\<^sub>b [ bv ::= b' ] \<setminus> s' \<close> using s' by auto
      qed
    qed
    then show ?thesis using bdc by auto

  qed
next 
  case SUnit
  have *:"b[bv::=b']\<^sub>b\<^sub>b = B_unit" using wfRCV_elims SUnit by metis
  show ?case proof (cases "b = B_var bv")
    case True
    moreover have "T  \<turnstile> SUnit : B_unit" using wfRCV.intros by simp
    moreover hence "b' = B_unit" using True SUnit subst_bb.simps * by simp
    ultimately show ?thesis using boxed_b.intros  wfRCV.intros by metis
  next
    case False
    hence "b = B_unit" using subst_bb_inject *  by metis  
    then show ?thesis using * SUnit boxed_b.intros by metis
  qed
next
  case (SUt x) 
  then obtain bv' where *:"b[bv::=b']\<^sub>b\<^sub>b= B_var bv'" using wfRCV_elims by metis
  show ?case proof (cases "b = B_var bv")
    case True
    then show ?thesis using boxed_b_BVar1I 
      using "local.*" wfRCV_BVarI by fastforce
  next
    case False
    then show ?thesis using boxed_b_BVar1I  boxed_b_BVar2I
      using "local.*" wfRCV_BVarI    by (metis subst_b_var)
  qed
qed

lemma boxed_i_ex:
  assumes "wfI T \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b i" and "wfTh T"
  shows  "\<exists>i'. T ; \<Gamma> ; b , bv \<turnstile> i \<approx> i'"
  using assms proof(induct \<Gamma> arbitrary: i rule:\<Gamma>_induct)
  case GNil
  then show ?case using boxed_i_GNilI by metis
next
  case (GCons x' b' c' \<Gamma>')
  then obtain s where 1:"Some s = i x' \<and> wfRCV T s b'[bv::=b]\<^sub>b\<^sub>b" using wfI_def subst_gb.simps by auto
  then obtain s' where 2: "boxed_b T s b' bv b s'" using boxed_b_ex GCons by metis
  then obtain i' where 3: "boxed_i T \<Gamma>' b bv i  i'" using GCons wfI_def subst_gb.simps by force
  have "boxed_i T ((x', b', c') #\<^sub>\<Gamma> \<Gamma>') b bv i  (i'(x' \<mapsto> s'))" proof
    show "Some s = i x'" using 1 by auto
    show "boxed_b T s b' bv b s'" using 2 by auto
    show "T  ; \<Gamma>' ; b , bv \<turnstile> i \<approx> i'"  using  "3" by auto
  qed
  thus ?case by auto
qed

lemma  boxed_b_eq:
  assumes "boxed_b \<Theta> s1 b bv b' s1'" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "wfTh \<Theta> \<Longrightarrow> boxed_b \<Theta> s2 b bv b' s2' \<Longrightarrow> ( s1 = s2 ) = ( s1' = s2' )"
  using assms proof(induct arbitrary: s2 s2'  rule: boxed_b.inducts )
  case (boxed_b_BVar1I bv bv'  P s b )  
  then show ?case 
    using boxed_b_elims(1) rcl_val.eq_iff by metis
next
  case (boxed_b_BVar2I bv bv' P s b)
  then show ?case using boxed_b_elims(1) by metis
next
  case (boxed_b_BIntI P s uu uv)
  hence "s2 = s2'" using boxed_b_elims by metis
  then show ?case by auto
next
  case (boxed_b_BBoolI P s uw ux)
  hence "s2 = s2'" using boxed_b_elims by metis
  then show ?case by auto
next
  case (boxed_b_BUnitI P s uy uz)
  hence "s2 = s2'" using boxed_b_elims by metis
  then show ?case by auto
next
  case (boxed_b_BPairI P s1 b1 bv b s1' s2a b2 s2a')
  then show ?case
    by (metis boxed_b_elims(5) rcl_val.eq_iff(4))
next
  case (boxed_b_BConsI tyid dclist P dc x b c s1 bv b' s1')
  obtain s22 and s22' dclist2 dc2 x2 b2 c2 where *:"s2 = SCons tyid dc2 s22 \<and> s2' = SCons tyid dc2 s22' \<and> boxed_b P s22 b2 bv b' s22' 
      \<and> AF_typedef tyid dclist2 \<in> set P \<and> (dc2, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2" using boxed_b_elims(6)[OF boxed_b_BConsI(6)] by metis
  show ?case proof(cases "dc = dc2")
    case True
    hence "b = b2"  using wfTh_ctor_unique \<tau>.eq_iff wfTh_dclist_unique wf boxed_b_BConsI * by metis
    then show ?thesis using boxed_b_BConsI True * by auto
  next
    case False
    then show ?thesis using * boxed_b_BConsI by simp
  qed      
next
  case (boxed_b_Bbitvec P s bv b)
  hence "s2 = s2'" using boxed_b_elims by metis
  then show ?case by auto
next
  case (boxed_b_BConspI tyid bva dclist P b1 bv b' s1 s1' dc x b c)
  obtain bva2 s22  s22' dclist2 dc2 x2 b2 c2 where *:"
     s2 = SConsp tyid dc2 b1[bv::=b']\<^sub>b\<^sub>b s22 \<and> 
     s2' = SConsp tyid dc2 b1 s22' \<and> 
     boxed_b P s22 b2[bva2::=b1]\<^sub>b\<^sub>b  bv b' s22'  \<and> 
     AF_typedef_poly tyid bva2 dclist2 \<in> set P \<and> (dc2, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2" using boxed_b_elims(8)[OF boxed_b_BConspI(7)] by metis
  show ?case proof(cases "dc = dc2")
    case True
    hence "AF_typedef_poly tyid bva2 dclist2 \<in> set P \<and> (dc, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist2" using * by auto
    hence "b[bva::=b1]\<^sub>b\<^sub>b = b2[bva2::=b1]\<^sub>b\<^sub>b"  using wfTh_typedef_poly_b_eq_iff[OF boxed_b_BConspI(1) boxed_b_BConspI(3)] * boxed_b_BConspI by metis
    then show ?thesis using boxed_b_BConspI True * by auto
  next
    case False
    then show ?thesis using * boxed_b_BConspI by simp
  qed    
qed

lemma bs_boxed_var:
  assumes "boxed_i \<Theta> \<Gamma> b' bv i i'"
  shows "Some (b,c) = lookup \<Gamma> x \<Longrightarrow> Some s = i x \<Longrightarrow> Some s' = i' x \<Longrightarrow> boxed_b \<Theta> s b bv b' s'"
  using assms proof(induct rule: boxed_i.inducts)
  case (boxed_i_GNilI T i)
  then show ?case using lookup.simps by auto
next
  case (boxed_i_GConsI s i x1 \<Theta> b1 bv b' s'  \<Gamma> i' c)
  show ?case proof (cases "x=x1")
    case True
    then show ?thesis using boxed_i_GConsI
        fun_upd_same lookup.simps(2) option.inject prod.inject by metis
  next
    case False
    then show ?thesis using boxed_i_GConsI
        fun_upd_same lookup.simps option.inject prod.inject by auto
  qed
qed

lemma eval_l_boxed_b:
  assumes  "\<lbrakk> l \<rbrakk> = s"
  shows   "boxed_b \<Theta> s (base_for_lit l) bv b' s"
  using assms proof(nominal_induct l arbitrary: s  rule:l.strong_induct)
qed(auto simp add:  boxed_b.intros wfRCV.intros )+

lemma boxed_i_eval_v_boxed_b:
  fixes v::v
  assumes "boxed_i \<Theta> \<Gamma> b' bv i i'" and "i \<lbrakk> v[bv::=b']\<^sub>v\<^sub>b \<rbrakk> ~  s" and  "i' \<lbrakk> v \<rbrakk> ~ s'" and "wfV \<Theta> B \<Gamma> v b"  and "wfI \<Theta>  \<Gamma> i'"
  shows "boxed_b \<Theta> s b bv b' s'"
  using assms proof(nominal_induct v arbitrary: s s' b  rule:v.strong_induct)
  case (V_lit l)
  hence "\<lbrakk> l \<rbrakk> = s \<and> \<lbrakk> l \<rbrakk> = s'" using eval_v_elims by auto
  moreover have "b = base_for_lit l" using wfV_elims(2) V_lit  by metis
  ultimately show ?case using V_lit using  eval_l_boxed_b subst_b_base_for_lit by metis
next
  case (V_var x)   (* look at defn of bs_boxed *)
  hence "Some s = i x \<and> Some s' = i' x" using eval_v_elims subst_vb.simps  by metis
  moreover obtain c1  where bc:"Some (b,c1) = lookup \<Gamma> x" using wfV_elims V_var by metis
  ultimately show ?case using bs_boxed_var V_var by metis

next
  case (V_pair v1 v2)
  then obtain b1 and b2 where b:"b=B_pair b1 b2" using wfV_elims subst_vb.simps  by metis
  obtain s1 and s2 where s: "eval_v i (v1[bv::=b']\<^sub>v\<^sub>b) s1 \<and> eval_v i (v2[bv::=b']\<^sub>v\<^sub>b) s2 \<and> s = SPair s1 s2" using eval_v_elims V_pair subst_vb.simps by metis
  obtain s1' and s2' where s': "eval_v i' v1 s1' \<and> eval_v i' v2 s2' \<and> s' = SPair s1' s2'" using eval_v_elims V_pair  by metis
  have  "boxed_b  \<Theta> (SPair s1 s2) (B_pair b1 b2)  bv b' (SPair s1' s2') " proof(rule boxed_b_BPairI)
    show "boxed_b \<Theta> s1 b1 bv b' s1'" using V_pair eval_v_elims wfV_elims b s s' b.eq_iff by metis
    show "boxed_b \<Theta> s2 b2 bv b' s2'" using V_pair eval_v_elims wfV_elims b s s' b.eq_iff by metis
  qed
  then show ?case using s s' b by auto
next
  case (V_cons tyid dc v1)

  obtain dclist x b1 c where *: "b = B_id tyid \<and> AF_typedef tyid dclist \<in> set \<Theta> \<and> (dc, \<lbrace> x : b1  | c \<rbrace>) \<in> set dclist \<and>  \<Theta> ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b1"
    using wfV_elims(4)[OF V_cons(5)] V_cons by metis
  obtain s2 where s2: "s = SCons tyid dc s2 \<and>  i \<lbrakk> (v1[bv::=b']\<^sub>v\<^sub>b) \<rbrakk> ~ s2" using eval_v_elims V_cons subst_vb.simps by metis
  obtain s2' where s2': "s' = SCons tyid dc s2' \<and>  i' \<lbrakk> v1 \<rbrakk> ~ s2'" using eval_v_elims V_cons by metis
  have sp: "supp \<lbrace> x : b1  | c \<rbrace> = {}" using wfTh_lookup_supp_empty * wfX_wfY by metis

  have "boxed_b \<Theta> (SCons tyid dc s2) (B_id tyid) bv b' (SCons tyid dc s2')"
  proof(rule boxed_b_BConsI)
    show 1:"AF_typedef tyid dclist \<in> set \<Theta>" using * by auto
    show 2:"(dc, \<lbrace> x : b1  | c \<rbrace>) \<in> set dclist" using * by auto
    have bvf:"atom bv \<sharp> b1" using sp  \<tau>.fresh fresh_def by auto    
    show "\<Theta>  \<turnstile> s2 ~ b1 [ bv ::= b' ] \<setminus> s2'" using V_cons s2 s2' * by metis
  qed
  then show ?case using * s2 s2' by simp
next
  case (V_consp tyid dc b1 v1)

  obtain bv2 dclist x2 b2 c2 where *: "b = B_app tyid b1 \<and> AF_typedef_poly tyid bv2 dclist \<in> set \<Theta> \<and> 
       (dc, \<lbrace> x2 : b2  | c2 \<rbrace>) \<in> set dclist \<and>  \<Theta> ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v1 : b2[bv2::=b1]\<^sub>b\<^sub>b"
    using wf_strong_elim(1)[OF V_consp (5)] by metis

  obtain s2 where s2: "s = SConsp tyid dc b1[bv::=b']\<^sub>b\<^sub>b s2 \<and>  i \<lbrakk> (v1[bv::=b']\<^sub>v\<^sub>b) \<rbrakk> ~ s2" 
    using eval_v_elims V_consp subst_vb.simps by metis

  obtain s2' where s2': "s' = SConsp tyid dc b1 s2' \<and>  i' \<lbrakk> v1 \<rbrakk> ~ s2'" 
    using eval_v_elims V_consp by metis

  have "\<turnstile>\<^sub>w\<^sub>f \<Theta>" using V_consp wfX_wfY by metis
  then obtain bv3::bv and dclist3 x3 b3 c3 where **:" AF_typedef_poly tyid bv2 dclist =  AF_typedef_poly tyid bv3 dclist3 \<and>
        (dc, \<lbrace> x3 : b3  | c3 \<rbrace>) \<in> set dclist3 \<and> atom bv3 \<sharp> (b1, bv, b', s2, s2') \<and> b2[bv2::=b1]\<^sub>b\<^sub>b = b3[bv3::=b1]\<^sub>b\<^sub>b"
    using * obtain_fresh_bv_dclist_b_iff[where tm="(b1, bv, b', s2, s2')"] by metis

  have "boxed_b \<Theta> (SConsp tyid dc b1[bv::=b']\<^sub>b\<^sub>b s2) (B_app tyid b1) bv b' (SConsp tyid dc b1 s2')"
  proof(rule boxed_b_BConspI[of tyid bv3 dclist3 \<Theta>, where x=x3 and b=b3 and c=c3])
    show 1:"AF_typedef_poly tyid bv3 dclist3 \<in> set \<Theta>" using * ** by auto
    show 2:"(dc, \<lbrace> x3 : b3  | c3 \<rbrace>) \<in> set dclist3" using ** by auto
    show "atom bv3 \<sharp> (b1, bv, b', s2, s2')" using ** by auto  
    show " \<Theta>  \<turnstile> s2 ~ b3[bv3::=b1]\<^sub>b\<^sub>b [ bv ::= b' ] \<setminus> s2'" using V_consp s2 s2' * ** by metis
  qed
  then show ?case using * s2 s2' by simp
qed

lemma boxed_b_eq_eq:
  assumes  "boxed_b \<Theta> n1 b1 bv b' n1'" and "boxed_b \<Theta> n2 b1 bv b' n2'" and "s = SBool (n1 = n2)" and  "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
    "s' = SBool (n1' = n2')"
  shows  "s=s'" 
  using boxed_b_eq assms by auto

lemma boxed_i_eval_ce_boxed_b:
  fixes e::ce
  assumes "i' \<lbrakk> e \<rbrakk> ~  s'" and "i \<lbrakk> e[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ s" and "wfCE \<Theta> B \<Gamma> e b" and "boxed_i \<Theta> \<Gamma> b' bv i i'" and "wfI \<Theta> \<Gamma> i'"
  shows "boxed_b \<Theta> s b bv b' s'"
  using assms proof(nominal_induct e arbitrary: s s' b b' rule: ce.strong_induct)
  case (CE_val x)
  then show ?case using boxed_i_eval_v_boxed_b eval_e_elims wfCE_elims subst_ceb.simps by metis
next
  case (CE_op opp v1 v2)

  show ?case proof(rule opp.exhaust)
    assume \<open>opp = Plus\<close>
    have 1:"wfCE \<Theta> B \<Gamma> v1 (B_int)" using wfCE_elims CE_op  \<open>opp = Plus\<close>  by metis
    have 2:"wfCE \<Theta> B \<Gamma> v2 (B_int)" using wfCE_elims CE_op  \<open>opp = Plus\<close> by metis
    have *:"b = B_int" using CE_op wfCE_elims 
      by (metis \<open>opp = plus\<close>)

    obtain n1 and n2 where n:"s = SNum (n1 + n2) \<and> i \<lbrakk> v1[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SNum n1 \<and> i \<lbrakk> v2[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SNum n2" using eval_e_elims CE_op subst_ceb.simps \<open>opp = plus\<close>  by metis
    obtain n1' and n2' where n':"s' = SNum (n1' + n2') \<and> i' \<lbrakk> v1 \<rbrakk> ~ SNum n1' \<and> i' \<lbrakk> v2 \<rbrakk> ~ SNum n2'" using eval_e_elims Plus CE_op \<open>opp = plus\<close> by metis

    have "boxed_b \<Theta> (SNum n1) B_int bv b' (SNum n1')" using boxed_i_eval_v_boxed_b 1 2 n n' CE_op \<open>opp = plus\<close> by metis
    moreover have "boxed_b \<Theta> (SNum n2) B_int bv b' (SNum n2')" using boxed_i_eval_v_boxed_b 1 2 n n' CE_op by metis
    ultimately have "s=s'" using n' n boxed_b_elims(2)
      by (metis rcl_val.eq_iff(2))
    thus ?thesis using  * n n' boxed_b_BIntI CE_op wfRCV.intros Plus by simp
  next
    assume \<open>opp = LEq\<close>
    have 1:"wfCE \<Theta> B \<Gamma> v1 (B_int)" using wfCE_elims CE_op  \<open>opp = LEq\<close>  by metis
    have 2:"wfCE \<Theta> B \<Gamma> v2 (B_int)" using wfCE_elims CE_op  \<open>opp = LEq\<close> by metis
    hence *:"b = B_bool" using CE_op wfCE_elims \<open>opp = LEq\<close>   by metis
    obtain n1 and n2 where n:"s = SBool (n1 \<le> n2) \<and> i \<lbrakk> v1[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SNum n1 \<and> i \<lbrakk> v2[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SNum n2" using eval_e_elims subst_ceb.simps CE_op \<open>opp = LEq\<close> by metis
    obtain n1' and n2' where n':"s' = SBool (n1' \<le> n2') \<and> i' \<lbrakk> v1 \<rbrakk> ~ SNum n1' \<and> i' \<lbrakk> v2 \<rbrakk> ~ SNum n2'" using eval_e_elims CE_op \<open>opp = LEq\<close>  by metis

    have "boxed_b \<Theta> (SNum n1) B_int bv b' (SNum n1')" using boxed_i_eval_v_boxed_b 1 2 n n' CE_op by metis
    moreover have "boxed_b \<Theta> (SNum n2) B_int bv b' (SNum n2')" using boxed_i_eval_v_boxed_b 1 2 n n' CE_op by metis
    ultimately have "s=s'" using n' n boxed_b_elims(2)
      by (metis rcl_val.eq_iff(2))
    thus ?thesis using  * n n' boxed_b_BBoolI CE_op wfRCV.intros \<open>opp = LEq\<close> by simp
  next
    assume \<open>opp = Eq\<close>
    obtain b1 where b1:"wfCE \<Theta> B \<Gamma> v1 b1 \<and> wfCE \<Theta> B \<Gamma> v2 b1" using wfCE_elims CE_op  \<open>opp = Eq\<close>  by metis

    hence *:"b = B_bool" using CE_op wfCE_elims \<open>opp = Eq\<close>   by metis
    obtain n1 and n2 where n:"s = SBool (n1 = n2) \<and> i \<lbrakk> v1[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ n1 \<and> i \<lbrakk> v2[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ n2" using eval_e_elims subst_ceb.simps CE_op \<open>opp = Eq\<close> by metis
    obtain n1' and n2' where n':"s' = SBool (n1' = n2') \<and> i' \<lbrakk> v1 \<rbrakk> ~ n1' \<and> i' \<lbrakk> v2 \<rbrakk> ~ n2'" using eval_e_elims CE_op \<open>opp = Eq\<close>  by metis

    have "boxed_b \<Theta> n1 b1 bv b' n1'" using boxed_i_eval_v_boxed_b b1  n n' CE_op by metis
    moreover have "boxed_b \<Theta> n2 b1 bv b' n2'" using boxed_i_eval_v_boxed_b b1  n n' CE_op by metis
    moreover have "\<turnstile>\<^sub>w\<^sub>f \<Theta>" using b1 wfX_wfY by metis
    ultimately have "s=s'" using n' n boxed_b_elims
        boxed_b_eq_eq by metis
    thus ?thesis using  * n n' boxed_b_BBoolI CE_op wfRCV.intros \<open>opp = Eq\<close> by simp
  qed

next
  case (CE_concat v1 v2)

  obtain bv1 and bv2 where s : "s = SBitvec (bv1 @ bv2) \<and> (i \<lbrakk> v1[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SBitvec bv1)  \<and> i \<lbrakk> v2[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SBitvec bv2"
    using eval_e_elims(7) subst_ceb.simps CE_concat.prems(2) eval_e_elims(6) subst_ceb.simps(6) by metis
  obtain bv1' and bv2' where s' : "s' = SBitvec (bv1' @ bv2') \<and> i' \<lbrakk> v1 \<rbrakk> ~ SBitvec bv1'  \<and> i' \<lbrakk> v2 \<rbrakk> ~ SBitvec bv2'"
    using eval_e_elims(7) CE_concat by metis

  then show ?case using boxed_i_eval_v_boxed_b wfCE_elims s s' CE_concat   
    by (metis CE_concat.prems(3) assms assms(5) wfRCV_BBitvecI boxed_b_Bbitvec boxed_b_elims(7) eval_e_concatI eval_e_uniqueness)
next
  case (CE_fst ce)
  obtain  s2 where 1:"i \<lbrakk> ce[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SPair s s2" using CE_fst eval_e_elims subst_ceb.simps by metis
  obtain  s2' where 2:"i' \<lbrakk> ce \<rbrakk> ~ SPair s' s2'" using CE_fst eval_e_elims by metis
  obtain b2 where 3:"wfCE \<Theta> B \<Gamma> ce (B_pair b b2)" using wfCE_elims(4) CE_fst by metis

  have "boxed_b \<Theta> (SPair s s2) (B_pair b b2) bv b' (SPair s' s2')" 
    using 1 2 3 CE_fst boxed_i_eval_v_boxed_b boxed_b_BPairI by auto
  thus ?case using boxed_b_elims(5) by force
next
  case (CE_snd v)
  obtain s1  where 1:"i \<lbrakk> v[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SPair s1 s" using CE_snd eval_e_elims subst_ceb.simps by metis
  obtain s1' where 2:"i' \<lbrakk> v \<rbrakk> ~ SPair s1' s'" using CE_snd eval_e_elims by metis
  obtain b1 where 3:"wfCE \<Theta> B \<Gamma> v (B_pair b1 b )" using wfCE_elims(5) CE_snd by metis

  have "boxed_b \<Theta> (SPair s1 s ) (B_pair b1 b ) bv b' (SPair s1' s')" using 1 2 3 CE_snd boxed_i_eval_v_boxed_b by simp
  thus ?case using boxed_b_elims(5) by force
next
  case (CE_len v)
  obtain s1 where s: "i \<lbrakk> v[bv::=b']\<^sub>c\<^sub>e\<^sub>b \<rbrakk> ~ SBitvec s1" using CE_len eval_e_elims subst_ceb.simps by metis
  obtain s1' where s': "i' \<lbrakk> v \<rbrakk> ~ SBitvec s1'" using CE_len eval_e_elims by metis

  have "\<Theta> ; B ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f v : B_bitvec \<and> b = B_int"  using wfCE_elims CE_len by metis
  then show ?case using boxed_i_eval_v_boxed_b s s' CE_len 
    by (metis boxed_b_BIntI boxed_b_elims(7) eval_e_lenI eval_e_uniqueness subst_ceb.simps(5) wfI_wfCE_eval_e)
qed

lemma eval_c_eq_bs_boxed:
  fixes c::c
  assumes "i \<lbrakk> c[bv::=b]\<^sub>c\<^sub>b \<rbrakk> ~ s" and "i' \<lbrakk> c \<rbrakk> ~ s'" and "wfC \<Theta> B \<Gamma> c" and "wfI \<Theta> \<Gamma> i'" and "\<Theta> ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> i "
    and "boxed_i \<Theta> \<Gamma> b bv i i'"
  shows "s = s'"
  using assms proof(nominal_induct c arbitrary: s s'  rule:c.strong_induct)
  case C_true
  then show ?case using eval_c_elims subst_cb.simps by metis
next
  case C_false
  then show ?case using eval_c_elims  subst_cb.simps by metis
next
  case (C_conj c1 c2)
  obtain s1 and s2 where 1: "eval_c i (c1[bv::=b]\<^sub>c\<^sub>b) s1 \<and> eval_c i (c2[bv::=b]\<^sub>c\<^sub>b) s2 \<and> s = (s1\<and>s2)" using C_conj eval_c_elims(3) subst_cb.simps(3) by metis
  obtain s1' and s2' where 2:"eval_c i' c1 s1' \<and> eval_c i' c2 s2' \<and> s' = (s1'\<and>s2')" using C_conj eval_c_elims(3) by metis
  then show ?case using 1 2 wfC_elims C_conj by metis
next
  case (C_disj c1 c2)

  obtain s1 and s2 where 1: "eval_c i (c1[bv::=b]\<^sub>c\<^sub>b) s1 \<and> eval_c i (c2[bv::=b]\<^sub>c\<^sub>b) s2 \<and> s = (s1\<or>s2)" using C_disj eval_c_elims(4) subst_cb.simps(4) by metis
  obtain s1' and s2' where 2:"eval_c i' c1 s1' \<and> eval_c i' c2 s2' \<and> s' = (s1'\<or>s2')" using C_disj eval_c_elims(4) by metis
  then show ?case using 1 2 wfC_elims C_disj by metis
next
  case (C_not c)
  obtain s1::bool  where 1: "(i \<lbrakk> c[bv::=b]\<^sub>c\<^sub>b \<rbrakk> ~ s1) \<and> (s = (\<not> s1))" using  C_not eval_c_elims(6) subst_cb.simps(7)  by metis
  obtain s1'::bool where 2: "(i' \<lbrakk> c \<rbrakk> ~ s1') \<and> (s' = (\<not> s1'))" using C_not eval_c_elims(6) by metis
  then show ?case using 1 2 wfC_elims C_not by metis
next
  case (C_imp c1 c2)
  obtain s1 and s2 where 1: "eval_c i (c1[bv::=b]\<^sub>c\<^sub>b) s1 \<and> eval_c i (c2[bv::=b]\<^sub>c\<^sub>b) s2 \<and> s = (s1 \<longrightarrow> s2)" using C_imp eval_c_elims(5) subst_cb.simps(5) by metis
  obtain s1' and s2' where 2:"eval_c i' c1 s1' \<and> eval_c i' c2 s2' \<and> s' = (s1' \<longrightarrow> s2')" using C_imp eval_c_elims(5) by metis
  then show ?case using 1 2 wfC_elims C_imp by metis
next
  case (C_eq e1 e2)
  obtain be where be: "wfCE \<Theta> B \<Gamma> e1 be \<and> wfCE \<Theta> B \<Gamma> e2 be" using C_eq wfC_elims by metis
  obtain s1 and s2 where 1: "eval_e i (e1[bv::=b]\<^sub>c\<^sub>e\<^sub>b) s1 \<and> eval_e i (e2[bv::=b]\<^sub>c\<^sub>e\<^sub>b) s2 \<and> s = (s1 = s2)" using C_eq eval_c_elims(7) subst_cb.simps(6) by metis
  obtain s1' and s2' where 2:"eval_e i' e1 s1' \<and> eval_e i' e2 s2' \<and> s' = (s1' = s2' )" using C_eq eval_c_elims(7) by metis
  have "\<turnstile>\<^sub>w\<^sub>f \<Theta>" using C_eq wfX_wfY by metis
  moreover have "\<Theta> ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<turnstile> i " using C_eq by auto
  ultimately show ?case using boxed_b_eq[of \<Theta> s1 be bv b s1' s2 s2'] 1 2 boxed_i_eval_ce_boxed_b  C_eq wfC_elims subst_cb.simps 1 2 be by auto
qed

lemma is_satis_bs_boxed:
  fixes c::c
  assumes  "boxed_i \<Theta> \<Gamma> b bv i i'" and "wfC \<Theta> B \<Gamma> c" and "wfI \<Theta> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b i" and "\<Theta> ; \<Gamma> \<turnstile> i'"
    and  "(i \<Turnstile> c[bv::=b]\<^sub>c\<^sub>b)"
  shows "(i' \<Turnstile> c)"
proof -
  have "eval_c i (c[bv::=b]\<^sub>c\<^sub>b) True" using is_satis.simps assms by auto
  moreover obtain s where "i' \<lbrakk> c \<rbrakk> ~ s" using eval_c_exist assms by metis
  ultimately show ?thesis using eval_c_eq_bs_boxed assms is_satis.simps by metis
qed

lemma is_satis_bs_boxed_rev:
  fixes c::c
  assumes  "boxed_i \<Theta> \<Gamma> b bv i i'" and "wfC \<Theta> B \<Gamma> c" and "wfI \<Theta> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b i" and "\<Theta> ; \<Gamma> \<turnstile> i'" and  "wfC \<Theta> {||} \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b (c[bv::=b]\<^sub>c\<^sub>b)"
    and  "(i' \<Turnstile> c)"
  shows "(i \<Turnstile> c[bv::=b]\<^sub>c\<^sub>b)"
proof -
  have "eval_c i' c True" using is_satis.simps assms by auto
  moreover obtain s where "i \<lbrakk> c[bv::=b]\<^sub>c\<^sub>b \<rbrakk> ~ s" using eval_c_exist assms by metis
  ultimately show ?thesis using eval_c_eq_bs_boxed assms is_satis.simps by metis
qed

lemma bs_boxed_wfi_aux:
  fixes b::b and bv::bv and \<Theta>::\<Theta> and B::\<B>
  assumes   "boxed_i \<Theta> \<Gamma> b bv i i'" and "wfI \<Theta> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b i" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>" and "wfG \<Theta> B  \<Gamma>"
  shows "\<Theta> ; \<Gamma> \<turnstile> i'"
  using assms proof(induct rule: boxed_i.inducts)
  case (boxed_i_GNilI T i)
  then show ?case using wfI_def by auto
next
  case (boxed_i_GConsI s i x1 T b1 bv b s' G i' c1)
  {
    fix x2 b2 c2
    assume as : "(x2,b2,c2) \<in> toSet ((x1, b1, c1) #\<^sub>\<Gamma> G)"

    then consider (hd) "(x2,b2,c2) = (x1, b1, c1)" | (tail) "(x2,b2,c2) \<in> toSet G" using toSet.simps by auto
    hence "\<exists>s. Some s = (i'(x1 \<mapsto> s')) x2 \<and> wfRCV T s b2" proof(cases)
      case hd
      hence "b1=b2" by auto
      moreover have "(x2,b2[bv::=b]\<^sub>b\<^sub>b,c2[bv::=b]\<^sub>c\<^sub>b) \<in> toSet ((x1, b1, c1) #\<^sub>\<Gamma> G)[bv::=b]\<^sub>\<Gamma>\<^sub>b"  using hd subst_gb.simps by simp
      moreover hence "wfRCV T s b2[bv::=b]\<^sub>b\<^sub>b" using wfI_def boxed_i_GConsI hd
      proof -
        obtain ss :: "b \<Rightarrow> x \<Rightarrow> (x \<Rightarrow> rcl_val option) \<Rightarrow> type_def list \<Rightarrow> rcl_val" where
          "\<forall>x1a x2a x3 x4. (\<exists>v5. Some v5 = x3 x2a \<and> wfRCV x4 v5 x1a) = (Some (ss x1a x2a x3 x4) = x3 x2a \<and> wfRCV x4 (ss x1a x2a x3 x4) x1a)"
          by moura (* 0.0 ms *)
        then have f1: "Some (ss b2[bv::=b]\<^sub>b\<^sub>b x1 i T) = i x1 \<and> wfRCV T (ss b2[bv::=b]\<^sub>b\<^sub>b x1 i T) b2[bv::=b]\<^sub>b\<^sub>b"
          using boxed_i_GConsI.prems(1) hd wfI_def by auto (* 31 ms *)
        then have "ss b2[bv::=b]\<^sub>b\<^sub>b x1 i T = s"
          by (metis (no_types) boxed_i_GConsI.hyps(1) option.inject) (* 0.0 ms *)
        then show ?thesis
          using f1 by blast (* 0.0 ms *)
      qed
      ultimately have "wfRCV T s' b2" using boxed_i_GConsI boxed_b_wfRCV by metis

      then show ?thesis using hd by simp
    next
      case tail
      hence "wfI T G i'" using boxed_i_GConsI wfI_suffix wfG_suffix subst_gb.simps
        by (metis (no_types, lifting) Un_iff toSet.simps(2) wfG_cons2 wfI_def)
      then show ?thesis using wfI_def[of T G i'] tail
        using boxed_i_GConsI.prems(3) split_G wfG_cons_fresh2 by fastforce
    qed
  }
  thus ?case using wfI_def by fast

qed

lemma is_satis_g_bs_boxed_aux:
  fixes G::\<Gamma>
  assumes  "boxed_i \<Theta> G1 b bv i i'" and "wfI \<Theta> G1[bv::=b]\<^sub>\<Gamma>\<^sub>b i" and "wfI \<Theta> G1 i'"  and "G1 = (G2@G)" and  "wfG \<Theta> B G1"
    and "(i \<Turnstile> G[bv::=b]\<^sub>\<Gamma>\<^sub>b) "
  shows  "(i' \<Turnstile> G)"
  using assms proof(induct G arbitrary: G2 rule: \<Gamma>_induct)
  case GNil
  then show ?case by auto
next
  case (GCons x' b' c' \<Gamma>' G2)
  show ?case proof(subst is_satis_g.simps,rule)
    have *:"wfC \<Theta> B G1 c'" using GCons wfG_wfC_inside by force
    show "i' \<Turnstile> c'" using is_satis_bs_boxed[OF assms(1) * ] GCons by auto
    obtain G3 where "G1 = G3 @ \<Gamma>'" using GCons append_g.simps
      by (metis append_g_assoc)
    then show "i' \<Turnstile> \<Gamma>'" using GCons append_g.simps by simp
  qed
qed

lemma is_satis_g_bs_boxed:
  fixes G::\<Gamma>
  assumes  "boxed_i \<Theta> G b bv i i'" and "wfI \<Theta> G[bv::=b]\<^sub>\<Gamma>\<^sub>b i" and "wfI \<Theta> G i'"  and "wfG \<Theta> B G"
    and "(i \<Turnstile> G[bv::=b]\<^sub>\<Gamma>\<^sub>b) "
  shows  "(i' \<Turnstile> G)"
  using is_satis_g_bs_boxed_aux assms
  by (metis (full_types) append_g.simps(1))

lemma subst_b_valid:
  fixes s::s and b::b
  assumes "\<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f b"  and "B = {|bv|}" and "\<Theta> ; {|bv|} ;\<Gamma>  \<Turnstile> c"
  shows "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b  \<Turnstile> c[bv::=b]\<^sub>c\<^sub>b "
proof(rule validI)

  show **:"\<Theta> ; {||} ;  \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b   \<turnstile>\<^sub>w\<^sub>f c[bv::=b]\<^sub>c\<^sub>b " using assms valid.simps wf_b_subst subst_gb.simps by metis
  show "\<forall>i. (wfI \<Theta>  \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b i \<and> i \<Turnstile> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b) \<longrightarrow> i \<Turnstile> c[bv::=b]\<^sub>c\<^sub>b "
  proof(rule,rule)
    fix i
    assume *:"wfI \<Theta>  \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b i \<and> i \<Turnstile> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b"

    obtain i' where idash: "boxed_i \<Theta> \<Gamma> b bv i i'" using boxed_i_ex wfX_wfY assms * by fastforce

    have wfc: "\<Theta> ; {|bv|} ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c" using valid.simps assms by simp
    have wfg: "\<Theta> ; {|bv|} \<turnstile>\<^sub>w\<^sub>f \<Gamma>" using valid.simps wfX_wfY assms by metis
    hence wfi: "wfI \<Theta> \<Gamma> i'" using idash * bs_boxed_wfi_aux subst_gb.simps wfX_wfY by metis
    moreover have "i' \<Turnstile>  \<Gamma>" proof (rule is_satis_g_bs_boxed[OF idash ] wfX_wfY(2)[OF wfc])
      show "wfI \<Theta> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b i" using subst_gb.simps * by simp
      show "wfI \<Theta> \<Gamma> i'" using wfi by auto
      show "\<Theta> ; B  \<turnstile>\<^sub>w\<^sub>f \<Gamma> " using wfg assms by auto
      show "i \<Turnstile> \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b" using subst_gb.simps * by simp
    qed
    ultimately have ic:"i' \<Turnstile> c" using assms valid_def   using valid.simps by blast

    show  "i \<Turnstile> c[bv::=b]\<^sub>c\<^sub>b" proof(rule is_satis_bs_boxed_rev)
      show "\<Theta>  ; \<Gamma> ; b , bv \<turnstile> i \<approx> i'" using idash by auto
      show "\<Theta> ; B ; \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c " using wfc assms by auto
      show "\<Theta> ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b \<turnstile> i" using subst_gb.simps * by simp
      show "\<Theta> ; \<Gamma> \<turnstile> i'" using wfi by auto
      show "\<Theta> ; {||} ; \<Gamma>[bv::=b]\<^sub>\<Gamma>\<^sub>b   \<turnstile>\<^sub>w\<^sub>f c[bv::=b]\<^sub>c\<^sub>b " using ** by auto
      show "i' \<Turnstile> c" using ic by auto
    qed

  qed
qed

section \<open>Expression Operator Lemmas\<close>

lemma is_satis_len_imp:
  assumes "i \<Turnstile> (CE_val (V_var x)  ==  CE_val (V_lit (L_num (int (length v)))) )" (is "is_satis i ?c1")
  shows "i \<Turnstile> (CE_val (V_var x)  ==  CE_len [V_lit (L_bitvec v)]\<^sup>c\<^sup>e)"
proof -
  have *:"eval_c i ?c1 True" using assms is_satis.simps by blast
  then have  "eval_e i (CE_val (V_lit (L_num (int (length v))))) (SNum (int (length v)))"
    using eval_e_elims(1) eval_v_elims eval_l.simps  by (metis eval_e.intros(1) eval_v_litI)
  hence "eval_e i (CE_val (V_var x)) (SNum (int (length v)))" using eval_c_elims(7)[OF *]
    by (metis eval_e_elims(1) eval_v_elims(1))
  moreover have "eval_e i (CE_len [V_lit (L_bitvec v)]\<^sup>c\<^sup>e) (SNum (int (length v)))"
    using eval_e_elims(7) eval_v_elims eval_l.simps  by (metis eval_e.intros eval_v_litI)
  ultimately show ?thesis using eval_c.intros is_satis.simps by fastforce
qed

lemma is_satis_plus_imp:
  assumes "i \<Turnstile> (CE_val (V_var x) ==  CE_val (V_lit (L_num (n1+n2))))" (is "is_satis i ?c1")
  shows   "i \<Turnstile> (CE_val (V_var x)  ==  CE_op Plus ([V_lit (L_num n1)]\<^sup>c\<^sup>e) ([V_lit (L_num n2)]\<^sup>c\<^sup>e))"
proof -
  have *:"eval_c i ?c1 True" using assms is_satis.simps by blast
  then have  "eval_e i (CE_val (V_lit (L_num (n1+n2)))) (SNum (n1+n2))"
    using eval_e_elims(1) eval_v_elims eval_l.simps  by (metis eval_e.intros(1) eval_v_litI)
  hence "eval_e i (CE_val (V_var x)) (SNum (n1+n2))" using eval_c_elims(7)[OF *]
    by (metis eval_e_elims(1) eval_v_elims(1))
  moreover have "eval_e i (CE_op Plus ([V_lit (L_num n1)]\<^sup>c\<^sup>e) ([V_lit (L_num n2)]\<^sup>c\<^sup>e)) (SNum (n1+n2))"
    using eval_e_elims(7) eval_v_elims eval_l.simps  by (metis eval_e.intros eval_v_litI)
  ultimately show ?thesis using eval_c.intros is_satis.simps by fastforce
qed

lemma is_satis_leq_imp:
  assumes "i \<Turnstile> (CE_val (V_var x) ==  CE_val (V_lit (if (n1 \<le> n2) then L_true else L_false)))" (is "is_satis i ?c1")
  shows   "i \<Turnstile> (CE_val (V_var x)  ==  CE_op LEq [(V_lit (L_num n1))]\<^sup>c\<^sup>e [(V_lit (L_num n2))]\<^sup>c\<^sup>e)"
proof -
  have *:"eval_c i ?c1 True" using assms is_satis.simps by blast
  then have  "eval_e i (CE_val (V_lit ((if (n1 \<le> n2) then L_true else L_false)))) (SBool (n1\<le>n2))"
    using eval_e_elims(1) eval_v_elims eval_l.simps
    by (metis (full_types) eval_e.intros(1) eval_v_litI)
  hence "eval_e i (CE_val (V_var x)) (SBool (n1\<le>n2))" using eval_c_elims(7)[OF *]
    by (metis eval_e_elims(1) eval_v_elims(1))
  moreover have "eval_e i (CE_op LEq [(V_lit (L_num n1))]\<^sup>c\<^sup>e [(V_lit (L_num n2) )]\<^sup>c\<^sup>e) (SBool (n1\<le>n2))"
    using eval_e_elims(3) eval_v_elims eval_l.simps  by (metis eval_e.intros eval_v_litI)
  ultimately show ?thesis using eval_c.intros is_satis.simps by fastforce
qed

lemma eval_lit_inj:
  fixes n1::l and n2::l
  assumes "\<lbrakk> n1  \<rbrakk> = s" and "\<lbrakk> n2 \<rbrakk> = s" 
  shows "n1=n2" 
  using assms proof(nominal_induct s rule: rcl_val.strong_induct)
  case (SBitvec x)
  then show ?case using eval_l.simps 
    by (metis l.strong_exhaust rcl_val.distinct rcl_val.eq_iff)
next
  case (SNum x)
  then show ?case using eval_l.simps 
    by (metis l.strong_exhaust rcl_val.distinct rcl_val.eq_iff)
next
  case (SBool x)
  then show ?case using eval_l.simps 
    by (metis l.strong_exhaust rcl_val.distinct rcl_val.eq_iff)
next
  case (SPair x1a x2a)
  then show ?case using eval_l.simps 
    by (metis l.strong_exhaust rcl_val.distinct rcl_val.eq_iff)
next
  case (SCons x1a x2a x3a)
  then show ?case using eval_l.simps 
    by (metis l.strong_exhaust rcl_val.distinct rcl_val.eq_iff)
next
  case (SConsp x1a x2a x3a x4)
  then show ?case using eval_l.simps 
    by (metis l.strong_exhaust rcl_val.distinct rcl_val.eq_iff)
next
  case SUnit
  then show ?case using eval_l.simps 
    by (metis l.strong_exhaust rcl_val.distinct rcl_val.eq_iff)
next
  case (SUt x)
  then show ?case using eval_l.simps 
    by (metis l.strong_exhaust rcl_val.distinct rcl_val.eq_iff)
qed

lemma eval_e_lit_inj:
  fixes n1::l and n2::l
  assumes "i \<lbrakk> [ [ n1 ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ s" and "i \<lbrakk> [ [ n2 ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ s" 
  shows "n1=n2" 
  using eval_lit_inj assms eval_e_elims eval_v_elims by metis

lemma is_satis_eq_imp:
  assumes "i \<Turnstile> (CE_val (V_var x) ==  CE_val (V_lit (if (n1 =  n2) then L_true else L_false)))" (is "is_satis i ?c1")
  shows   "i \<Turnstile> (CE_val (V_var x)  ==  CE_op Eq [(V_lit (n1))]\<^sup>c\<^sup>e [(V_lit (n2))]\<^sup>c\<^sup>e)"
proof -
  have *:"eval_c i ?c1 True" using assms is_satis.simps by blast
  then have  "eval_e i (CE_val (V_lit ((if (n1=n2) then L_true else L_false)))) (SBool (n1=n2))"
    using eval_e_elims(1) eval_v_elims eval_l.simps
    by (metis (full_types) eval_e.intros(1) eval_v_litI)
  hence "eval_e i (CE_val (V_var x)) (SBool (n1=n2))" using eval_c_elims(7)[OF *]
    by (metis eval_e_elims(1) eval_v_elims(1))
  moreover have "eval_e i (CE_op Eq [(V_lit (n1))]\<^sup>c\<^sup>e [(V_lit (n2) )]\<^sup>c\<^sup>e) (SBool (n1=n2))"
  proof -
    obtain s1 and s2 where *:"i \<lbrakk> [ [ n1 ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ s1  \<and> i \<lbrakk> [ [ n2 ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ s2" using eval_l.simps eval_e.intros eval_v_litI by metis
    moreover have " SBool (n1 = n2)  =  SBool (s1 = s2)" proof(cases "n1=n2")
      case True
      then show ?thesis using * 
        by (simp add: calculation eval_e_uniqueness)
    next
      case False
      then show ?thesis using *  eval_e_lit_inj by auto
    qed
    ultimately show ?thesis using eval_e_eqI[of i "[(V_lit (n1))]\<^sup>c\<^sup>e"  s1 "[(V_lit (n2))]\<^sup>c\<^sup>e" s2 ] by auto
  qed
  ultimately show ?thesis using eval_c.intros is_satis.simps by fastforce
qed

lemma valid_eq_e:
  assumes "\<forall>i s1 s2. wfG P \<B> GNil \<and> wfI P GNil i \<and> eval_e i e1 s1 \<and> eval_e i e2 s2 \<longrightarrow> s1 = s2"   
    and "wfCE P  \<B> GNil e1 b" and "wfCE P \<B> GNil e2 b" 
  shows "P ; \<B> ; (x, b , CE_val (V_var x)  ==  e1 )#\<^sub>\<Gamma> GNil \<Turnstile>  CE_val (V_var x)  ==  e2"
  unfolding valid.simps
proof(intro conjI)
  show \<open> P ; \<B> ; (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e1 ) #\<^sub>\<Gamma> GNil   \<turnstile>\<^sub>w\<^sub>f [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e2  \<close> 
    using assms wf_intros wfX_wfY  b.eq_iff fresh_GNil wfC_e_eq2 wfV_elims  by meson
  show \<open>\<forall>i.  ((P ; (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e1 ) #\<^sub>\<Gamma> GNil \<turnstile> i) \<and>  (i \<Turnstile> (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e1 ) #\<^sub>\<Gamma> GNil)  \<longrightarrow>
             (i \<Turnstile> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e2)) \<close> proof(rule+)
    fix i
    assume as:"P ; (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e1 ) #\<^sub>\<Gamma> GNil \<turnstile> i \<and>  i \<Turnstile> (x, b, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e1 ) #\<^sub>\<Gamma> GNil"

    have *: "P ; GNil \<turnstile> i " using wfI_def by auto

    then obtain s1 where s1:"eval_e i e1 s1" using assms eval_e_exist  by metis
    obtain s2 where s2:"eval_e i e2 s2" using assms eval_e_exist  * by metis
    moreover have "i x = Some s1" proof -
      have "i \<Turnstile> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e1" using as is_satis_g.simps by auto
      thus ?thesis using s1 
        by (metis eval_c_elims(7) eval_e_elims(1) eval_e_uniqueness eval_v_elims(2) is_satis.cases)
    qed
    moreover have "s1 = s2" using s1 s2 * assms wfG_nilI wfX_wfY by metis

    ultimately show "i \<lbrakk> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  e2  \<rbrakk> ~ True" 
      using eval_c.intros eval_e.intros eval_v.intros 
    proof -
      have "i \<lbrakk> e2 \<rbrakk> ~ s1"
        by (metis \<open>s1 = s2\<close> s2) (* 0.0 ms *)
      then show ?thesis
        by (metis (full_types) \<open>i x = Some s1\<close> eval_c_eqI eval_e_valI eval_v_varI) (* 31 ms *)
    qed
  qed
qed

lemma valid_len:
  assumes " \<turnstile>\<^sub>w\<^sub>f \<Theta>" 
  shows  "\<Theta> ; \<B> ; (x, B_int, [[x]\<^sup>v]\<^sup>c\<^sup>e  ==  [[ L_num (int (length v)) ]\<^sup>v]\<^sup>c\<^sup>e) #\<^sub>\<Gamma> GNil  \<Turnstile> [[x]\<^sup>v]\<^sup>c\<^sup>e  ==  CE_len [[ L_bitvec v ]\<^sup>v]\<^sup>c\<^sup>e"  (is "\<Theta> ; \<B> ; ?G \<Turnstile> ?c" )
proof - 
  have *:"\<Theta>  \<turnstile>\<^sub>w\<^sub>f ([]::\<Phi>)  \<and>  \<Theta> ; \<B> ; GNil  \<turnstile>\<^sub>w\<^sub>f []\<^sub>\<Delta> " using assms wfG_nilI wfD_emptyI wfPhi_emptyI by auto

  moreover  hence "\<Theta>  ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f CE_val (V_lit (L_num (int (length v)))) : B_int" 
    using wfCE_valI * wfV_litI base_for_lit.simps 
    by (metis wfE_valI wfX_wfY)

  moreover have "\<Theta>  ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f CE_len [(V_lit (L_bitvec v))]\<^sup>c\<^sup>e : B_int"       
    using wfE_valI * wfV_litI base_for_lit.simps  wfE_valI wfX_wfY wfCE_valI
    by (metis wfCE_lenI)
  moreover have "atom x \<sharp> GNil" by auto
  ultimately have "\<Theta> ; \<B> ; ?G \<turnstile>\<^sub>w\<^sub>f ?c" using wfC_e_eq2 assms by simp
  moreover have "(\<forall>i. wfI \<Theta> ?G i \<and> is_satis_g i ?G \<longrightarrow> is_satis i ?c)" using is_satis_len_imp by auto
  ultimately show ?thesis using valid.simps by auto
qed

lemma valid_arith_bop:
  assumes "wfG \<Theta> \<B>  \<Gamma>" and "opp = Plus \<and> ll = (L_num (n1+n2)) \<or> (opp = LEq \<and> ll = ( if n1\<le>n2 then L_true else L_false))"  
    and "(opp = Plus \<longrightarrow> b = B_int) \<and> (opp = LEq \<longrightarrow> b = B_bool)" and
    "atom x \<sharp> \<Gamma>" 
  shows   "\<Theta>; \<B> ; (x, b, (CE_val (V_var x)  ==  CE_val (V_lit (ll)) )) #\<^sub>\<Gamma> \<Gamma>  
                          \<Turnstile> (CE_val (V_var x)  ==  CE_op opp ([V_lit (L_num n1)]\<^sup>c\<^sup>e) ([V_lit (L_num n2)]\<^sup>c\<^sup>e ))" (is "\<Theta> ; \<B> ; ?G \<Turnstile> ?c")
proof -
  have "wfC \<Theta> \<B> ?G ?c" proof(rule wfC_e_eq2)
    show "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_val (V_lit ll) : b" using wfCE_valI wfV_litI assms base_for_lit.simps by metis
    show "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op opp ([V_lit (L_num n1)]\<^sup>c\<^sup>e) ([V_lit (L_num n2)]\<^sup>c\<^sup>e) : b " 
      using wfCE_plusI wfCE_leqI   wfCE_eqI wfV_litI wfCE_valI base_for_lit.simps assms  by metis
    show "\<turnstile>\<^sub>w\<^sub>f \<Theta>" using assms wfX_wfY by auto 
    show "atom x \<sharp> \<Gamma>" using assms by auto
  qed

  moreover have "\<forall>i. wfI \<Theta> ?G i \<and> is_satis_g i ?G \<longrightarrow> is_satis i ?c" proof(rule allI , rule impI)
    fix i
    assume "wfI \<Theta> ?G i \<and> is_satis_g i ?G" 

    hence "is_satis i  ((CE_val (V_var x)  ==  CE_val (V_lit (ll)) ))"   by auto
    thus  "is_satis i ((CE_val (V_var x)  ==  CE_op opp ([V_lit (L_num n1)]\<^sup>c\<^sup>e) ([V_lit (L_num n2)]\<^sup>c\<^sup>e)))" 
      using is_satis_plus_imp assms opp.exhaust is_satis_leq_imp by auto
  qed
  ultimately show ?thesis using valid.simps by metis
qed

lemma valid_eq_bop:
  assumes "wfG \<Theta> \<B>  \<Gamma>" and  "atom x \<sharp> \<Gamma>"  and  "base_for_lit l1 = base_for_lit l2"
  shows   "\<Theta>; \<B> ; (x, B_bool, (CE_val (V_var x)  ==  CE_val (V_lit (if l1 = l2 then L_true else L_false)) )) #\<^sub>\<Gamma> \<Gamma>  
                          \<Turnstile> (CE_val (V_var x)  ==  CE_op Eq ([V_lit (l1)]\<^sup>c\<^sup>e) ([V_lit (l2)]\<^sup>c\<^sup>e ))" (is "\<Theta> ; \<B> ; ?G \<Turnstile> ?c")
proof -
  let ?ll = "(if l1 = l2 then L_true else L_false)"
  have "wfC \<Theta> \<B> ?G ?c" proof(rule wfC_e_eq2)
    show "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_val (V_lit ?ll) : B_bool" using wfCE_valI wfV_litI assms base_for_lit.simps by metis
    show "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f CE_op Eq ([V_lit (l1)]\<^sup>c\<^sup>e) ([V_lit (l2)]\<^sup>c\<^sup>e) : B_bool " 
      using wfCE_eqI wfCE_leqI   wfCE_eqI wfV_litI wfCE_valI base_for_lit.simps assms by metis
    show "\<turnstile>\<^sub>w\<^sub>f \<Theta>" using assms wfX_wfY by auto 
    show "atom x \<sharp> \<Gamma>" using assms by auto
  qed

  moreover have "\<forall>i. wfI \<Theta> ?G i \<and> is_satis_g i ?G \<longrightarrow> is_satis i ?c" proof(rule allI , rule impI)
    fix i
    assume "wfI \<Theta> ?G i \<and> is_satis_g i ?G" 

    hence "is_satis i  ((CE_val (V_var x)  ==  CE_val (V_lit (?ll)) ))"   by auto
    thus  "is_satis i ((CE_val (V_var x)  ==  CE_op Eq ([V_lit (l1)]\<^sup>c\<^sup>e) ([V_lit (l2)]\<^sup>c\<^sup>e)))" 
      using is_satis_eq_imp assms  by auto
  qed
  ultimately show ?thesis using valid.simps by metis
qed

lemma valid_fst:
  fixes x::x and v\<^sub>1::v and v\<^sub>2::v
  assumes   "wfTh \<Theta>" and "wfV \<Theta> \<B> GNil (V_pair v\<^sub>1 v\<^sub>2) (B_pair b\<^sub>1 b\<^sub>2)"
  shows "\<Theta> ; \<B> ; (x, b\<^sub>1, [[x]\<^sup>v]\<^sup>c\<^sup>e  ==  [v\<^sub>1]\<^sup>c\<^sup>e) #\<^sub>\<Gamma> GNil  \<Turnstile> [[x]\<^sup>v]\<^sup>c\<^sup>e  ==  [#1[[v\<^sub>1,v\<^sub>2]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e" 
proof(rule valid_eq_e)
  show \<open>\<forall>i s1 s2.  (\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f GNil)  \<and>  (\<Theta> ; GNil \<turnstile> i) \<and> (i \<lbrakk> [ v\<^sub>1 ]\<^sup>c\<^sup>e \<rbrakk> ~ s1)  \<and> (i \<lbrakk> [#1[[ v\<^sub>1 , v\<^sub>2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e \<rbrakk> ~ s2)  \<longrightarrow> s1 = s2\<close> 
  proof(rule+)
    fix i s1 s2 
    assume as:"\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f GNil  \<and>  \<Theta> ; GNil \<turnstile> i \<and> (i \<lbrakk> [ v\<^sub>1 ]\<^sup>c\<^sup>e \<rbrakk> ~ s1)  \<and> (i \<lbrakk> [#1[[ v\<^sub>1 , v\<^sub>2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e \<rbrakk> ~ s2)"
    then obtain s2' where *:"i \<lbrakk> [ v\<^sub>1 , v\<^sub>2 ]\<^sup>v \<rbrakk> ~ SPair s2 s2'" 
      using eval_e_elims(5)[of i "[[ v\<^sub>1 , v\<^sub>2 ]\<^sup>v]\<^sup>c\<^sup>e" s2] eval_e_elims 
      by meson
    then have " i \<lbrakk> v\<^sub>1 \<rbrakk> ~ s2" using eval_v_elims(3)[OF *] by auto
    then show "s1 = s2" using eval_v_uniqueness as 
      using eval_e_uniqueness eval_e_valI by blast
  qed

  show \<open>  \<Theta> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f [ v\<^sub>1 ]\<^sup>c\<^sup>e : b\<^sub>1 \<close> using assms 
    by (metis b.eq_iff(4) wfV_elims(3) wfV_wfCE)
  show \<open>  \<Theta> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f [#1[[ v\<^sub>1 , v\<^sub>2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e : b\<^sub>1 \<close> using assms using wfCE_fstI 
    using wfCE_valI by blast
qed

lemma valid_snd: 
  fixes x::x and v\<^sub>1::v and v\<^sub>2::v
  assumes   "wfTh \<Theta>" and "wfV \<Theta> \<B> GNil (V_pair v\<^sub>1 v\<^sub>2) (B_pair b\<^sub>1 b\<^sub>2)"
  shows "\<Theta> ; \<B> ; (x, b\<^sub>2, [[x]\<^sup>v]\<^sup>c\<^sup>e  ==  [v\<^sub>2]\<^sup>c\<^sup>e) #\<^sub>\<Gamma> GNil  \<Turnstile> [[x]\<^sup>v]\<^sup>c\<^sup>e  ==  [#2[[v\<^sub>1,v\<^sub>2]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e" 
proof(rule valid_eq_e)
  show \<open>\<forall>i s1 s2.  (\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f GNil)  \<and>  (\<Theta> ; GNil \<turnstile> i) \<and> (i \<lbrakk> [ v\<^sub>2 ]\<^sup>c\<^sup>e \<rbrakk> ~ s1)  \<and> 
(i \<lbrakk> [#2[[ v\<^sub>1 , v\<^sub>2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e \<rbrakk> ~ s2)  \<longrightarrow> s1 = s2\<close> 
  proof(rule+)
    fix i s1 s2 
    assume as:"\<Theta> ; \<B>  \<turnstile>\<^sub>w\<^sub>f GNil  \<and>  \<Theta> ; GNil \<turnstile> i \<and> (i \<lbrakk> [ v\<^sub>2 ]\<^sup>c\<^sup>e \<rbrakk> ~ s1)  \<and> (i \<lbrakk> [#2[[ v\<^sub>1 , v\<^sub>2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e \<rbrakk> ~ s2)"
    then obtain s2' where *:"i \<lbrakk> [ v\<^sub>1 , v\<^sub>2 ]\<^sup>v \<rbrakk> ~ SPair s2' s2" 
      using eval_e_elims(5)[of i "[[ v\<^sub>1 , v\<^sub>2 ]\<^sup>v]\<^sup>c\<^sup>e" s2] eval_e_elims 
      by meson
    then have " i \<lbrakk> v\<^sub>2 \<rbrakk> ~ s2" using eval_v_elims(3)[OF *] by auto
    then show "s1 = s2" using eval_v_uniqueness as 
      using eval_e_uniqueness eval_e_valI by blast
  qed

  show \<open>  \<Theta> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f [ v\<^sub>2 ]\<^sup>c\<^sup>e : b\<^sub>2 \<close> using assms 
    by (metis b.eq_iff wfV_elims wfV_wfCE)
  show \<open>  \<Theta> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f [#2[[ v\<^sub>1 , v\<^sub>2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e : b\<^sub>2 \<close> using assms using wfCE_sndI wfCE_valI by blast
qed

lemma valid_concat:
  fixes v1::"bit list" and v2::"bit list"
  assumes " \<turnstile>\<^sub>w\<^sub>f \<Pi>" 
  shows "\<Pi> ; \<B> ; (x, B_bitvec, (CE_val (V_var x)  ==  CE_val (V_lit (L_bitvec (v1@ v2))))) #\<^sub>\<Gamma> GNil \<Turnstile>
            (CE_val (V_var x)  ==  CE_concat ([V_lit (L_bitvec v1)]\<^sup>c\<^sup>e ) ([V_lit (L_bitvec v2)]\<^sup>c\<^sup>e) )"
proof(rule valid_eq_e)                         
  show \<open>\<forall>i s1 s2.  ((\<Pi> ; \<B>  \<turnstile>\<^sub>w\<^sub>f GNil)  \<and>  (\<Pi> ; GNil \<turnstile> i) \<and> 
            (i \<lbrakk> [ [ L_bitvec (v1 @ v2) ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ s1)  \<and> (i \<lbrakk> [[[ L_bitvec v1 ]\<^sup>v]\<^sup>c\<^sup>e  @@ [[ L_bitvec v2 ]\<^sup>v]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  \<rbrakk> ~ s2)  \<longrightarrow>
           s1 = s2)\<close> 
  proof(rule+)
    fix i s1 s2 
    assume as: "(\<Pi> ; \<B>  \<turnstile>\<^sub>w\<^sub>f GNil)  \<and>  (\<Pi> ; GNil \<turnstile> i) \<and> (i \<lbrakk> [ [ L_bitvec (v1 @ v2) ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ s1)  \<and> 
            (i \<lbrakk> [[[ L_bitvec v1 ]\<^sup>v]\<^sup>c\<^sup>e @@ [[ L_bitvec v2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e  \<rbrakk> ~ s2) "

    hence *: "i \<lbrakk> [[[ L_bitvec v1 ]\<^sup>v]\<^sup>c\<^sup>e @@ [[ L_bitvec v2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e  \<rbrakk> ~ s2"  by auto
    obtain bv1 bv2 where s2:"s2 = SBitvec (bv1 @ bv2) \<and> i \<lbrakk> [ L_bitvec v1 ]\<^sup>v \<rbrakk> ~ SBitvec bv1  \<and> (i \<lbrakk> [ L_bitvec v2 ]\<^sup>v \<rbrakk> ~ SBitvec bv2)" 
      using eval_e_elims(7)[OF *] eval_e_elims(1) by metis
    hence "v1 = bv1 \<and> v2 = bv2" using eval_v_elims(1) eval_l.simps(5) by force
    moreover then have "s1 = SBitvec  (bv1 @ bv2)" using s2 using eval_v_elims(1) eval_l.simps(5) 
      by (metis as eval_e_elims(1))

    then show "s1 = s2" using s2 by auto
  qed  

  show \<open>  \<Pi> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f [ [ L_bitvec (v1 @ v2) ]\<^sup>v ]\<^sup>c\<^sup>e : B_bitvec \<close> 
    by (metis assms base_for_lit.simps(5) wfG_nilI wfV_litI wfV_wfCE)
  show \<open>  \<Pi> ; \<B> ; GNil \<turnstile>\<^sub>w\<^sub>f [[[ L_bitvec v1 ]\<^sup>v]\<^sup>c\<^sup>e @@ [[ L_bitvec v2 ]\<^sup>v]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e  : B_bitvec \<close> 
    by (metis assms base_for_lit.simps(5) wfCE_concatI wfG_nilI wfV_litI wfCE_valI)
qed

lemma valid_ce_eq:
  fixes ce::ce
  assumes  "\<Theta> ; \<B> ; \<Gamma> \<turnstile>\<^sub>w\<^sub>f ce : b"
  shows \<open>\<Theta> ; \<B> ; \<Gamma>  \<Turnstile> ce  ==  ce \<close>
  unfolding valid.simps proof 
  show \<open> \<Theta> ; \<B> ; \<Gamma>   \<turnstile>\<^sub>w\<^sub>f ce  ==  ce  \<close> using assms wfC_eqI by auto
  show \<open>\<forall>i.  \<Theta> ; \<Gamma> \<turnstile> i \<and>  i \<Turnstile> \<Gamma>  \<longrightarrow>  i \<Turnstile> ce  ==  ce  \<close> proof(rule+)
    fix i
    assume "\<Theta> ; \<Gamma> \<turnstile> i \<and>  i \<Turnstile> \<Gamma>"
    then obtain s where "i\<lbrakk> ce \<rbrakk> ~ s" using assms eval_e_exist by metis
    then show "i \<lbrakk> ce  ==  ce  \<rbrakk> ~ True " using eval_c_eqI by metis
  qed
qed

lemma valid_eq_imp:
  fixes c1::c and c2::c
  assumes " \<Theta> ; \<B> ; (x, b, c2) #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c1 IMP c2"
  shows  " \<Theta> ; \<B> ; (x, b, c2) #\<^sub>\<Gamma> \<Gamma>  \<Turnstile>  c1   IMP  c2 "
proof -
  have "\<forall>i.  (\<Theta> ; (x, b, c2) #\<^sub>\<Gamma> \<Gamma> \<turnstile> i \<and>  i \<Turnstile> (x, b, c2) #\<^sub>\<Gamma> \<Gamma>)  \<longrightarrow>  i \<Turnstile> ( c1  IMP  c2 )"
  proof(rule,rule)
    fix i
    assume as:"\<Theta> ; (x, b, c2) #\<^sub>\<Gamma> \<Gamma> \<turnstile> i \<and>  i \<Turnstile> (x, b, c2) #\<^sub>\<Gamma> \<Gamma>"

    have "\<Theta> ; \<B> ; (x, b, c2) #\<^sub>\<Gamma> \<Gamma>  \<turnstile>\<^sub>w\<^sub>f c1" using wfC_elims assms by metis

    then obtain sc where "i \<lbrakk> c1 \<rbrakk> ~ sc" using eval_c_exist assms as by metis
    moreover have  "i \<lbrakk> c2 \<rbrakk> ~ True" using as is_satis_g.simps is_satis.simps by auto

    ultimately have "i \<lbrakk> c1  IMP  c2 \<rbrakk> ~ True" using eval_c_impI by metis

    thus  "i \<Turnstile> c1  IMP  c2" using is_satis.simps by auto
  qed
  thus ?thesis using assms by auto
qed

lemma valid_range:
  assumes "0 \<le> n \<and> n \<le> m" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "\<Theta> ; {||} ; (x, B_int  , (C_eq (CE_val (V_var x)) (CE_val (V_lit (L_num n))))) #\<^sub>\<Gamma>  GNil \<Turnstile> 
                              (C_eq (CE_op LEq (CE_val (V_var x)) (CE_val (V_lit (L_num m))))  [[ L_true ]\<^sup>v ]\<^sup>c\<^sup>e) AND
                             (C_eq (CE_op LEq (CE_val (V_lit (L_num 0))) (CE_val (V_var x)))  [[ L_true ]\<^sup>v ]\<^sup>c\<^sup>e)"
    (is "\<Theta> ; {||} ; ?G \<Turnstile> ?c1 AND ?c2")
proof(rule validI)
  have wfg: " \<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f (x, B_int, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> GNil " 
    using assms base_for_lit.simps wfG_nilI wfV_litI fresh_GNil wfB_intI wfC_v_eq wfG_cons1I wfG_cons2I by metis

  show "\<Theta> ; {||} ; ?G  \<turnstile>\<^sub>w\<^sub>f ?c1 AND ?c2" 
    using wfC_conjI wfC_eqI wfCE_leqI wfCE_valI wfV_varI wfg lookup.simps base_for_lit.simps wfV_litI wfB_intI wfB_boolI 
    by metis

  show "\<forall>i.  \<Theta> ; ?G \<turnstile> i \<and>  i \<Turnstile> ?G  \<longrightarrow> i \<Turnstile> ?c1 AND ?c2" proof(rule,rule)
    fix i
    assume a:"\<Theta> ; ?G \<turnstile> i \<and>  i \<Turnstile> ?G"
    hence *:"i \<lbrakk> V_var x \<rbrakk> ~ SNum n" 
    proof - 
      obtain sv where sv: "i x = Some sv \<and> \<Theta> \<turnstile> sv : B_int" using a wfI_def by force
      have "i \<lbrakk>  (C_eq (CE_val (V_var x)) (CE_val (V_lit (L_num n)))) \<rbrakk> ~ True" 
        using a is_satis_g.simps 
        using is_satis.cases by blast
      hence "i x = Some(SNum n)" using sv 
        by (metis eval_c_elims(7) eval_e_elims(1) eval_l.simps(3) eval_v_elims(1) eval_v_elims(2))
      thus ?thesis using eval_v_varI by auto
    qed

    show "i \<Turnstile> ?c1 AND ?c2" 
    proof - 
      have "i \<lbrakk> ?c1 \<rbrakk> ~ True" 
      proof -
        have "i \<lbrakk> [ leq [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e [ [ L_num m ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e\<rbrakk> ~ SBool True" 
          using eval_e_leqI assms eval_v_litI eval_l.simps * 
          by (metis (full_types) eval_e_valI)
        moreover have "i \<lbrakk>  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk> ~ SBool True" 
          using eval_v_litI eval_e_valI eval_l.simps by metis
        ultimately show ?thesis using  eval_c_eqI by metis
      qed

      moreover have "i \<lbrakk> ?c2 \<rbrakk> ~ True" 
      proof -
        have "i \<lbrakk> [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e \<rbrakk> ~ SBool True"
          using eval_e_leqI assms eval_v_litI eval_l.simps * 
          by (metis (full_types) eval_e_valI)
        moreover have "i \<lbrakk>  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk> ~ SBool True" 
          using eval_v_litI eval_e_valI eval_l.simps by metis
        ultimately show ?thesis using  eval_c_eqI by metis
      qed      
      ultimately show ?thesis using eval_c_conjI is_satis.simps by metis
    qed
  qed
qed

lemma valid_range_length:
  fixes \<Gamma>::\<Gamma>
  assumes "0 \<le> n \<and> n \<le> int (length v)" and " \<Theta> ; {||} \<turnstile>\<^sub>w\<^sub>f \<Gamma>" and "atom x \<sharp> \<Gamma>"
  shows "\<Theta> ; {||} ; (x, B_int  , (C_eq (CE_val (V_var x)) (CE_val (V_lit (L_num n))))) #\<^sub>\<Gamma>  \<Gamma> \<Turnstile> 
                     (C_eq (CE_op LEq (CE_val (V_lit (L_num 0))) (CE_val (V_var x)))  [[ L_true ]\<^sup>v ]\<^sup>c\<^sup>e) AND  
                     (C_eq (CE_op LEq (CE_val (V_var x)) ([| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ))  [[ L_true ]\<^sup>v ]\<^sup>c\<^sup>e)
                            "
    (is "\<Theta> ; {||} ; ?G \<Turnstile> ?c1 AND ?c2")
proof(rule validI)
  have wfg: " \<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f (x, B_int, [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e ) #\<^sub>\<Gamma> \<Gamma> " apply(rule  wfG_cons1I)
    apply simp
    using assms apply simp+
    using assms base_for_lit.simps wfG_nilI wfV_litI  wfB_intI wfC_v_eq  wfB_intI wfX_wfY assms by metis+

  show "\<Theta> ; {||} ; ?G  \<turnstile>\<^sub>w\<^sub>f ?c1 AND ?c2" 
    using wfC_conjI wfC_eqI wfCE_leqI wfCE_valI wfV_varI wfg lookup.simps base_for_lit.simps wfV_litI wfB_intI wfB_boolI     
    by (metis (full_types) wfCE_lenI)

  show "\<forall>i.  \<Theta> ; ?G \<turnstile> i \<and>  i \<Turnstile> ?G  \<longrightarrow> i \<Turnstile> ?c1 AND ?c2" proof(rule,rule)
    fix i
    assume a:"\<Theta> ; ?G \<turnstile> i \<and>  i \<Turnstile> ?G"
    hence *:"i \<lbrakk> V_var x \<rbrakk> ~ SNum n" 
    proof - 
      obtain sv where sv: "i x = Some sv \<and> \<Theta> \<turnstile> sv : B_int" using a wfI_def by force
      have "i \<lbrakk>  (C_eq (CE_val (V_var x)) (CE_val (V_lit (L_num n)))) \<rbrakk> ~ True" 
        using a is_satis_g.simps 
        using is_satis.cases by blast
      hence "i x = Some(SNum n)" using sv 
        by (metis eval_c_elims(7) eval_e_elims(1) eval_l.simps(3) eval_v_elims(1) eval_v_elims(2))
      thus ?thesis using eval_v_varI by auto
    qed

    show "i \<Turnstile> ?c1 AND ?c2" 
    proof - 
      have "i \<lbrakk> ?c2 \<rbrakk> ~ True" 
      proof -
        have "i \<lbrakk> [ leq [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e [| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e\<rbrakk> ~ SBool True" 
          using eval_e_leqI assms eval_v_litI eval_l.simps * 
          by (metis (full_types) eval_e_lenI eval_e_valI)        
        moreover have "i \<lbrakk>  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk> ~ SBool True" 
          using eval_v_litI eval_e_valI eval_l.simps by metis
        ultimately show ?thesis using  eval_c_eqI by metis
      qed

      moreover have "i \<lbrakk> ?c1 \<rbrakk> ~ True" 
      proof -
        have "i \<lbrakk> [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e \<rbrakk> ~ SBool True"
          using eval_e_leqI assms eval_v_litI eval_l.simps * 
          by (metis (full_types) eval_e_valI)
        moreover have "i \<lbrakk>  [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk> ~ SBool True" 
          using eval_v_litI eval_e_valI eval_l.simps by metis
        ultimately show ?thesis using  eval_c_eqI by metis
      qed      
      ultimately show ?thesis using eval_c_conjI is_satis.simps by metis
    qed
  qed
qed

lemma valid_range_length_inv_gnil:
  fixes \<Gamma>::\<Gamma>
  assumes  "\<turnstile>\<^sub>w\<^sub>f \<Theta> "
    and  "\<Theta> ; {||} ; (x, B_int  , (C_eq (CE_val (V_var x)) (CE_val (V_lit (L_num n))))) #\<^sub>\<Gamma>  GNil \<Turnstile> 
                     (C_eq (CE_op LEq (CE_val (V_lit (L_num 0))) (CE_val (V_var x)))  [[ L_true ]\<^sup>v ]\<^sup>c\<^sup>e) AND  
                     (C_eq (CE_op LEq (CE_val (V_var x)) ([| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ))  [[ L_true ]\<^sup>v ]\<^sup>c\<^sup>e)
                            "
    (is "\<Theta> ; {||} ; ?G \<Turnstile> ?c1 AND ?c2")
  shows "0 \<le> n \<and> n \<le> int (length v)" 
proof -
  have *:"\<forall>i.  \<Theta> ; ?G \<turnstile> i \<and>  i \<Turnstile> ?G  \<longrightarrow> i \<Turnstile> ?c1 AND ?c2" using assms valid.simps by simp

  obtain i where i: "i x = Some (SNum n)" by auto
  have "\<Theta> ; ?G \<turnstile> i \<and>  i \<Turnstile> ?G" proof 
    show  "\<Theta> ; ?G \<turnstile> i" unfolding wfI_def using wfRCV_BIntI i * by auto
    have "i \<lbrakk> ([ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e )  \<rbrakk> ~ True" 
      using * eval_c.intros(7) eval_e.intros eval_v.intros  eval_l.simps 
      by (metis (full_types) i)
    thus  "i \<Turnstile> ?G" unfolding  is_satis_g.simps is_satis.simps by auto
  qed     
  hence **:"i \<Turnstile> ?c1 AND ?c2" using * by auto

  hence  1: "i \<lbrakk> ?c1 \<rbrakk> ~ True" using eval_c_elims(3) is_satis.simps 
    by fastforce
  then obtain sv1 and sv2 where "(sv1 = sv2) = True \<and> i \<lbrakk> [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e \<rbrakk> ~ sv1 \<and> i \<lbrakk> [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk>  ~ sv2" 
    using eval_c_elims(7) by metis
  hence "sv1 = SBool True" using eval_e_elims eval_v_elims eval_l.simps i by metis
  obtain n1 and n2 where "SBool True = SBool (n1 \<le> n2) \<and> (i \<lbrakk> [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ SNum n1)  \<and> (i \<lbrakk> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ SNum n2)" 
    using eval_e_elims(3)[of i " [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e" "[ [ x ]\<^sup>v ]\<^sup>c\<^sup>e "  "SBool True"] 
    using \<open>(sv1 = sv2) = True \<and> i \<lbrakk> [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e \<rbrakk> ~ sv1 \<and> i \<lbrakk> [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ sv2\<close> \<open>sv1 = SBool True\<close> by fastforce
  moreover hence "n1 = 0" and "n2 = n"  using eval_e_elims eval_v_elims i 
    apply (metis eval_l.simps(3) rcl_val.eq_iff(2))
    using eval_e_elims eval_v_elims i 
    by (metis calculation option.inject rcl_val.eq_iff(2))
  ultimately have  le1: "0 \<le> n " by simp

  hence  2: "i \<lbrakk> ?c2 \<rbrakk> ~ True" using ** eval_c_elims(3) is_satis.simps 
    by fastforce
  then obtain sv1 and sv2 where sv: "(sv1 = sv2) = True \<and> i \<lbrakk> [ leq [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  [| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e   \<rbrakk> ~ sv1 \<and> i \<lbrakk> [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk>  ~ sv2" 
    using eval_c_elims(7) by metis
  hence "sv1 = SBool True" using eval_e_elims eval_v_elims eval_l.simps i by metis
  obtain n1 and n2 where ***:"SBool True = SBool (n1 \<le> n2) \<and>  (i \<lbrakk> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ SNum n1) \<and> (i \<lbrakk> [| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e  \<rbrakk> ~ SNum n2)" 
    using eval_e_elims(3) 
    using sv \<open>sv1 = SBool True\<close> by metis
  moreover hence "n1 = n" using eval_e_elims(1)[of i] eval_v_elims(2)[of i x "SNum n1"] i by auto
  moreover  have "n2 = int (length v)"  using eval_e_elims(8) eval_v_elims(1) eval_l.simps i    
    by (metis "***" eval_e_elims(1) rcl_val.eq_iff(1) rcl_val.eq_iff(2))    
  ultimately have  le2: "n \<le> int (length v) " by simp

  show ?thesis using le1 le2 by auto
qed

lemma wfI_cons:  
  fixes i::valuation and \<Gamma>::\<Gamma>
  assumes "i' \<Turnstile> \<Gamma>" and "\<Theta> ; \<Gamma> \<turnstile> i'" and "i = i' ( x \<mapsto> s)" and "\<Theta>  \<turnstile> s : b" and "atom x \<sharp> \<Gamma>"
  shows "\<Theta> ; (x,b,c) #\<^sub>\<Gamma> \<Gamma> \<turnstile> i"  
  unfolding wfI_def proof - 
  {  
    fix x' b' c' 
    assume "(x',b',c') \<in> toSet ((x, b, c) #\<^sub>\<Gamma> \<Gamma>)"
    then consider "(x',b',c') = (x,b,c)" | "(x',b',c') \<in> toSet \<Gamma>" using toSet.simps by auto
    then have "\<exists>s. Some s = i x' \<and>  \<Theta>  \<turnstile> s : b'" proof(cases)
      case 1
      then show ?thesis using assms by auto
    next
      case 2
      then obtain s where s:"Some s = i' x' \<and> \<Theta>  \<turnstile> s : b'" using assms wfI_def by auto
      moreover have "x' \<noteq> x" using assms 2 fresh_dom_free by auto
      ultimately have "Some s = i x'" using assms by auto
      then show ?thesis using s  wfI_def by auto
    qed
  }
  thus "\<forall>(x, b, c)\<in>toSet ((x, b, c) #\<^sub>\<Gamma> \<Gamma>). \<exists>s. Some s = i x \<and>  \<Theta>  \<turnstile> s : b" by auto
qed

lemma valid_range_length_inv:
  fixes \<Gamma>::\<Gamma>
  assumes  "\<Theta> ; B \<turnstile>\<^sub>w\<^sub>f \<Gamma> " and "atom x \<sharp> \<Gamma>" and "\<exists>i. i \<Turnstile> \<Gamma> \<and> \<Theta> ; \<Gamma> \<turnstile> i"
    and  "\<Theta> ; B ; (x, B_int  , (C_eq (CE_val (V_var x)) (CE_val (V_lit (L_num n))))) #\<^sub>\<Gamma>  \<Gamma> \<Turnstile> 
                     (C_eq (CE_op LEq (CE_val (V_lit (L_num 0))) (CE_val (V_var x)))  [[ L_true ]\<^sup>v ]\<^sup>c\<^sup>e) AND  
                     (C_eq (CE_op LEq (CE_val (V_var x)) ([| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ))  [[ L_true ]\<^sup>v ]\<^sup>c\<^sup>e)
                            "
    (is "\<Theta> ; ?B ; ?G \<Turnstile> ?c1 AND ?c2")
  shows "0 \<le> n \<and> n \<le> int (length v)" 
proof -
  have *:"\<forall>i.  \<Theta> ; ?G \<turnstile> i \<and>  i \<Turnstile> ?G  \<longrightarrow> i \<Turnstile> ?c1 AND ?c2" using assms valid.simps by simp

  obtain i' where idash: "is_satis_g i' \<Gamma> \<and> \<Theta> ; \<Gamma> \<turnstile> i'" using assms by auto
  obtain i where i: "i = i' ( x \<mapsto> SNum n)" by auto
  hence ix: "i x = Some (SNum n)" by auto
  have "\<Theta> ; ?G \<turnstile> i \<and>  i \<Turnstile> ?G" proof 
    show  "\<Theta> ; ?G \<turnstile> i" using wfI_cons i idash ix wfRCV_BIntI assms by simp

    have **:"i \<lbrakk> ([ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e )  \<rbrakk> ~ True" 
      using * eval_c.intros(7) eval_e.intros eval_v.intros  eval_l.simps i 
      by (metis (full_types) ix)

    show  "i \<Turnstile> ?G" unfolding  is_satis_g.simps proof 
      show \<open> i \<Turnstile> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e  \<close> using ** is_satis.simps by auto
      show \<open> i \<Turnstile> \<Gamma> \<close> using idash i assms is_satis_g_i_upd by metis
    qed
  qed     
  hence **:"i \<Turnstile> ?c1 AND ?c2" using * by auto

  hence  1: "i \<lbrakk> ?c1 \<rbrakk> ~ True" using eval_c_elims(3) is_satis.simps 
    by fastforce
  then obtain sv1 and sv2 where "(sv1 = sv2) = True \<and> i \<lbrakk> [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e \<rbrakk> ~ sv1 \<and> i \<lbrakk> [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk>  ~ sv2" 
    using eval_c_elims(7) by metis
  hence "sv1 = SBool True" using eval_e_elims eval_v_elims eval_l.simps i by metis
  obtain n1 and n2 where "SBool True = SBool (n1 \<le> n2) \<and> (i \<lbrakk> [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ SNum n1)  \<and> (i \<lbrakk> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ SNum n2)" 
    using eval_e_elims(3)[of i " [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e" "[ [ x ]\<^sup>v ]\<^sup>c\<^sup>e "  "SBool True"] 
    using \<open>(sv1 = sv2) = True \<and> i \<lbrakk> [ leq [ [ L_num 0 ]\<^sup>v ]\<^sup>c\<^sup>e [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e \<rbrakk> ~ sv1 \<and> i \<lbrakk> [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ sv2\<close> \<open>sv1 = SBool True\<close> by fastforce
  moreover hence "n1 = 0" and "n2 = n"  using eval_e_elims eval_v_elims i 
    apply (metis eval_l.simps(3) rcl_val.eq_iff(2))
    using eval_e_elims eval_v_elims i 
      calculation option.inject rcl_val.eq_iff(2)
    by (metis ix)
  ultimately have  le1: "0 \<le> n " by simp

  hence  2: "i \<lbrakk> ?c2 \<rbrakk> ~ True" using ** eval_c_elims(3) is_satis.simps 
    by fastforce
  then obtain sv1 and sv2 where sv: "(sv1 = sv2) = True \<and> i \<lbrakk> [ leq [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e  [| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e   \<rbrakk> ~ sv1 \<and> i \<lbrakk> [ [ L_true ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk>  ~ sv2" 
    using eval_c_elims(7) by metis
  hence "sv1 = SBool True" using eval_e_elims eval_v_elims eval_l.simps i by metis
  obtain n1 and n2 where ***:"SBool True = SBool (n1 \<le> n2) \<and>  (i \<lbrakk> [ [ x ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ SNum n1) \<and> (i \<lbrakk> [| [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e  \<rbrakk> ~ SNum n2)" 
    using eval_e_elims(3) 
    using sv \<open>sv1 = SBool True\<close> by metis
  moreover hence "n1 = n" using eval_e_elims(1)[of i] eval_v_elims(2)[of i x "SNum n1"] i by auto
  moreover  have "n2 = int (length v)"  using eval_e_elims(8) eval_v_elims(1) eval_l.simps i    
    by (metis "***" eval_e_elims(1) rcl_val.eq_iff(1) rcl_val.eq_iff(2))    
  ultimately have  le2: "n \<le> int (length v) " by simp

  show ?thesis using le1 le2 by auto
qed

lemma eval_c_conj2I[intro]: 
  assumes "i \<lbrakk> c1 \<rbrakk> ~ True" and "i \<lbrakk> c2 \<rbrakk> ~ True"
  shows "i \<lbrakk> (C_conj c1 c2) \<rbrakk> ~  True"
  using assms eval_c_conjI by metis

lemma valid_split:
  assumes "split n v (v1,v2)" and "\<turnstile>\<^sub>w\<^sub>f \<Theta>"
  shows "\<Theta> ; {||} ; (z , [B_bitvec , B_bitvec ]\<^sup>b ,  [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ [ L_bitvec  v1 ]\<^sup>v , [ L_bitvec  v2 ]\<^sup>v ]\<^sup>v ]\<^sup>c\<^sup>e) #\<^sub>\<Gamma> GNil  
\<Turnstile>  ([ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [#1[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e @@ [#2[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e)   AND  ([| [#1[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e  ==  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e)"
    (is "\<Theta> ;  {||} ;  ?G \<Turnstile> ?c1 AND ?c2")
  unfolding valid.simps proof

  have wfg: " \<Theta> ; {||}  \<turnstile>\<^sub>w\<^sub>f (z, [B_bitvec , B_bitvec ]\<^sup>b ,  [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ [ L_bitvec  v1 ]\<^sup>v , [ L_bitvec  v2 ]\<^sup>v ]\<^sup>v ]\<^sup>c\<^sup>e) #\<^sub>\<Gamma> GNil" 
    using wf_intros assms base_for_lit.simps  fresh_GNil wfC_v_eq  wfG_intros2 by metis   

  show "\<Theta> ; {||} ; ?G  \<turnstile>\<^sub>w\<^sub>f ?c1 AND ?c2" 
    apply(rule wfC_conjI)
    apply(rule wfC_eqI)
    apply(rule wfCE_valI)
    apply(rule wfV_litI)
    using wf_intros wfg lookup.simps base_for_lit.simps wfC_v_eq 
    apply (metis )+
    done

  have len:"int (length v1) = n" using assms split_length by auto

  show "\<forall>i. \<Theta> ; ?G \<turnstile> i \<and> i \<Turnstile> ?G \<longrightarrow> i \<Turnstile> (?c1 AND ?c2)" 
  proof(rule,rule)
    fix i
    assume a:"\<Theta> ; ?G \<turnstile> i \<and> i \<Turnstile> ?G"
    hence "i \<lbrakk> [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e  ==  [ [ [ L_bitvec v1 ]\<^sup>v , [ L_bitvec v2 ]\<^sup>v ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ True" 
      using is_satis_g.simps is_satis.simps by simp
    then obtain sv where "i \<lbrakk> [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ sv \<and> i \<lbrakk>  [ [ [ L_bitvec v1 ]\<^sup>v , [ L_bitvec v2 ]\<^sup>v ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ sv" 
      using eval_c_elims by metis
    hence "i  \<lbrakk> [ [ z ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ (SPair (SBitvec v1) (SBitvec v2))" using eval_c_eqI eval_v.intros eval_l.simps 
      by (metis eval_e_elims(1) eval_v_uniqueness)
    hence b:"i z = Some (SPair (SBitvec v1) (SBitvec v2))" using a eval_e_elims eval_v_elims by metis

    have v1: "i \<lbrakk> [#1[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e \<rbrakk> ~ SBitvec v1 " 
      using eval_e_fstI eval_e_valI eval_v_varI b by metis
    have v2: "i \<lbrakk> [#2[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e \<rbrakk> ~ SBitvec v2" 
      using eval_e_sndI eval_e_valI eval_v_varI b by metis

    have "i \<lbrakk> [ [ L_bitvec v ]\<^sup>v ]\<^sup>c\<^sup>e \<rbrakk> ~ SBitvec v" using eval_e.intros eval_v.intros eval_l.simps by metis
    moreover have "i \<lbrakk>  [ [#1[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e @@ [#2[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e ]\<^sup>c\<^sup>e  \<rbrakk> ~ SBitvec v" 
      using assms split_concat v1 v2 eval_e_concatI by metis
    moreover have "i \<lbrakk>  [| [#1[ [ z ]\<^sup>v ]\<^sup>c\<^sup>e]\<^sup>c\<^sup>e |]\<^sup>c\<^sup>e \<rbrakk> ~ SNum (int (length v1))" 
      using v1 eval_e_lenI by auto
    moreover have "i \<lbrakk>  [ [ L_num n ]\<^sup>v ]\<^sup>c\<^sup>e  \<rbrakk> ~ SNum n" using eval_e.intros eval_v.intros eval_l.simps by metis
    ultimately show  "i \<Turnstile> ?c1 AND ?c2" using is_satis.intros eval_c_conj2I eval_c_eqI len by metis
  qed
qed


lemma is_satis_eq:
  assumes "wfI \<Theta> G i" and "wfCE \<Theta> \<B> G e b"
  shows "is_satis i (e == e)"
proof(rule)
  obtain s where "eval_e i e s" using eval_e_exist assms by metis
  thus "eval_c i (e  ==  e ) True" using eval_c_eqI by metis
qed

lemma is_satis_g_i_upd2:
  assumes "eval_v i v s" and "is_satis ((i ( x \<mapsto> s))) c0" and "atom x \<sharp> G" and "wfG \<Theta> \<B> (G3@((x,b,c0)#\<^sub>\<Gamma>G))" and "wfV \<Theta> \<B> G v b" and "wfI \<Theta> (G3[x::=v]\<^sub>\<Gamma>\<^sub>v@G) i" 
    and  "is_satis_g i (G3[x::=v]\<^sub>\<Gamma>\<^sub>v@G)"
  shows "is_satis_g (i ( x \<mapsto> s)) (G3@((x,b,c0)#\<^sub>\<Gamma>G))"
  using assms proof(induct G3 rule: \<Gamma>_induct)
  case GNil
  hence "is_satis_g (i(x \<mapsto> s)) G" using is_satis_g_i_upd by auto
  then show ?case using GNil using is_satis_g.simps append_g.simps by metis
next
  case (GCons x' b' c' \<Gamma>')
  hence "x\<noteq>x'" using wfG_cons_append  by metis
  hence "is_satis_g i (((x', b', c'[x::=v]\<^sub>c\<^sub>v) #\<^sub>\<Gamma> (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v) @ G))" using subst_gv.simps GCons by auto
  hence *:"is_satis i c'[x::=v]\<^sub>c\<^sub>v \<and> is_satis_g i ((\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v) @ G)" using subst_gv.simps by auto

  have "is_satis_g (i(x \<mapsto> s)) ((x', b', c') #\<^sub>\<Gamma> (\<Gamma>'@  (x, b, c0) #\<^sub>\<Gamma> G))" proof(subst is_satis_g.simps,rule)
    show "is_satis (i(x \<mapsto> s)) c'" proof(subst subst_c_satis_full[symmetric])
      show \<open>eval_v i v s\<close> using GCons by auto
      show \<open> \<Theta> ; \<B> ; ((x', b', c') #\<^sub>\<Gamma>\<Gamma>')@(x, b, c0) #\<^sub>\<Gamma> G \<turnstile>\<^sub>w\<^sub>f c' \<close> using GCons wfC_refl by auto
      show \<open>wfI \<Theta> ((((x', b', c') #\<^sub>\<Gamma> \<Gamma>')[x::=v]\<^sub>\<Gamma>\<^sub>v) @ G) i\<close> using GCons  by auto
      show \<open> \<Theta> ; \<B> ; G \<turnstile>\<^sub>w\<^sub>f v : b \<close> using GCons by auto
      show \<open>is_satis i c'[x::=v]\<^sub>c\<^sub>v\<close> using * by auto
    qed
    show "is_satis_g (i(x \<mapsto> s)) (\<Gamma>' @ (x, b, c0) #\<^sub>\<Gamma> G)" proof(rule  GCons(1))
      show \<open>eval_v i v s\<close> using GCons by auto
      show \<open>is_satis (i(x \<mapsto> s)) c0\<close> using GCons by metis
      show \<open>atom x \<sharp> G\<close> using GCons by auto
      show \<open> \<Theta> ; \<B>\<turnstile>\<^sub>w\<^sub>f \<Gamma>' @ (x, b, c0) #\<^sub>\<Gamma> G \<close> using GCons wfG_elims append_g.simps by metis
      show \<open>is_satis_g i (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v @ G)\<close> using * by auto
      show "wfI \<Theta> (\<Gamma>'[x::=v]\<^sub>\<Gamma>\<^sub>v @ G) i" using GCons wfI_def subst_g_assoc_cons \<open>x\<noteq>x'\<close> by auto
      show "\<Theta> ; \<B> ; G \<turnstile>\<^sub>w\<^sub>f v : b "  using GCons by auto
    qed
  qed
  moreover have "((x', b', c') #\<^sub>\<Gamma> \<Gamma>' @ (x, b, c0) #\<^sub>\<Gamma> G) = (((x', b', c') #\<^sub>\<Gamma> \<Gamma>') @ (x, b, c0) #\<^sub>\<Gamma> G)" by auto
  ultimately show ?case using GCons by metis
qed


end