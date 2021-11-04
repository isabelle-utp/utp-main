section \<open>FIN is a proper subset of CP\label{s:fin_cp}\<close>

theory CP_FIN_NUM
  imports Inductive_Inference_Basics
begin

text \<open>Let $S$ be a FIN strategy for a non-empty class $U$. Let $T$ be a
strategy that hypothesizes an arbitrary function from $U$ while $S$ outputs
``don't know'' and the hypothesis of $S$ otherwise. Then $T$ is a CP strategy
for $U$.\<close>

lemma nonempty_FIN_wrt_impl_CP:
  assumes "U \<noteq> {}" and "U \<in> FIN_wrt \<psi>"
  shows "U \<in> CP_wrt \<psi>"
proof -
  obtain s where "learn_fin \<psi> U s"
    using assms(2) FIN_wrt_def  by auto
  then have env: "environment \<psi> U s" and
    fin: "\<And>f. f \<in> U \<Longrightarrow>
      \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i)"
    using learn_finE by auto
  from assms(1) obtain f\<^sub>0 where "f\<^sub>0 \<in> U"
    by auto
  with fin obtain i\<^sub>0 where "\<psi> i\<^sub>0 = f\<^sub>0"
    by blast
  define t where "t x \<equiv>
    (if s x \<up> then None else if s x \<down>= 0 then Some i\<^sub>0 else Some (the (s x) - 1))"
    for x
  have "t \<in> \<P>"
  proof -
    from env obtain rs where rs: "recfn 1 rs" "\<And>x. eval rs [x] = s x"
      by auto
    define rt where "rt = Cn 1 r_ifz [rs, r_const i\<^sub>0, Cn 1 r_dec [rs]]"
    then have "recfn 1 rt"
      using rs(1) by simp
    then have "eval rt [x] \<down>= (if s x \<down>= 0 then i\<^sub>0 else (the (s x)) - 1)" if "s x \<down>" for x
      using rs rt_def that by auto
    moreover have "eval rt [x] \<up>" if "eval rs [x] \<up>" for x
      using rs rt_def that by simp
    ultimately have "eval rt [x] = t x" for x
      using rs(2) t_def by simp
    with \<open>recfn 1 rt\<close> show ?thesis by auto
  qed
  have "learn_cp \<psi> U t"
  proof (rule learn_cpI)
    show "environment \<psi> U t"
      using env t_def \<open>t \<in> \<P>\<close> by simp
    show "\<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. t (f \<triangleright> n) \<down>= i)" if "f \<in> U" for f
    proof -
      from that fin obtain i n\<^sub>0 where
        i: "\<psi> i = f" "\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0" "\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i"
        by blast
      moreover have "\<forall>n\<ge>n\<^sub>0. t (f \<triangleright> n) \<down>= i"
        using that t_def i(3) by simp
      ultimately show ?thesis by auto
    qed
    show "\<psi> (the (t (f \<triangleright> n))) \<in> U" if "f \<in> U" for f n
      using \<open>\<psi> i\<^sub>0 = f\<^sub>0\<close> \<open>f\<^sub>0 \<in> U\<close> t_def fin env that
      by (metis (no_types, lifting) diff_Suc_1 not_less option.sel)
  qed
  then show ?thesis using CP_wrt_def env by auto
qed

lemma FIN_wrt_impl_CP:
  assumes "U \<in> FIN_wrt \<psi>"
  shows "U \<in> CP_wrt \<psi>"
proof (cases "U = {}")
  case True
  then have "\<psi> \<in> \<P>\<^sup>2 \<Longrightarrow> U \<in> CP_wrt \<psi>"
    using CP_wrt_def learn_cpI[of \<psi> "{}" "\<lambda>x. Some 0"] const_in_Prim1 by auto
  moreover have "\<psi> \<in> \<P>\<^sup>2"
    using assms FIN_wrt_def learn_finE by auto
  ultimately show "U \<in> CP_wrt \<psi>" by simp
next
  case False
  with nonempty_FIN_wrt_impl_CP assms show ?thesis
    by simp
qed

corollary FIN_subseteq_CP: "FIN \<subseteq> CP"
proof
  fix U
  assume "U \<in> FIN"
  then have "\<exists>\<psi>. U \<in> FIN_wrt \<psi>"
    using FIN_def FIN_wrt_def by auto
  then have "\<exists>\<psi>. U \<in> CP_wrt \<psi>"
    using FIN_wrt_impl_CP by auto
  then show "U \<in> CP"
    by (simp add: CP_def CP_wrt_def)
qed

text \<open>In order to show the \emph{proper} inclusion, we show @{term
"U\<^sub>0 \<in> CP - FIN"}. A CP strategy for @{term "U\<^sub>0"} simply
hypothesizes the function in @{term U0} with the longest prefix of $f^n$ not
ending in zero. For that we define a function computing the index of the
rightmost non-zero value in a list, returning the length of the list if there
is no such value.\<close>

definition findr :: partial1 where
  "findr e \<equiv>
    if \<exists>i<e_length e. e_nth e i \<noteq> 0
    then Some (GREATEST i. i < e_length e \<and> e_nth e i \<noteq> 0)
    else Some (e_length e)"

lemma findr_total: "findr e \<down>"
  unfolding findr_def by simp

lemma findr_ex:
  assumes "\<exists>i<e_length e. e_nth e i \<noteq> 0"
  shows "the (findr e) < e_length e"
    and "e_nth e (the (findr e)) \<noteq> 0"
    and "\<forall>i. the (findr e) < i \<and> i < e_length e \<longrightarrow> e_nth e i = 0"
proof -
  let ?P = "\<lambda>i. i < e_length e \<and> e_nth e i \<noteq> 0"
  from assms have "\<exists>i. ?P i" by simp
  then have "?P (Greatest ?P)"
    using GreatestI_ex_nat[of ?P "e_length e"] by fastforce
  moreover have *: "findr e = Some (Greatest ?P)"
    using assms findr_def by simp
  ultimately show "the (findr e) < e_length e" and "e_nth e (the (findr e)) \<noteq> 0"
    by fastforce+
  show "\<forall>i. the (findr e) < i \<and> i < e_length e \<longrightarrow> e_nth e i = 0"
    using * Greatest_le_nat[of ?P _ "e_length e"] by fastforce
qed

definition "r_findr \<equiv>
  let g =
    Cn 3 r_ifz
     [Cn 3 r_nth [Id 3 2, Id 3 0],
      Cn 3 r_ifeq [Id 3 0, Id 3 1, Cn 3 S [Id 3 0], Id 3 1],
      Id 3 0]
  in Cn 1 (Pr 1 Z g) [Cn 1 r_length [Id 1 0], Id 1 0]"

lemma r_findr_prim [simp]: "prim_recfn 1 r_findr"
  unfolding r_findr_def by simp

lemma r_findr [simp]: "eval r_findr [e] = findr e"
proof -
  define g where "g =
    Cn 3 r_ifz
     [Cn 3 r_nth [Id 3 2, Id 3 0],
      Cn 3 r_ifeq [Id 3 0, Id 3 1, Cn 3 S [Id 3 0], Id 3 1],
      Id 3 0]"
  then have "recfn 3 g"
    by simp
  with g_def have g: "eval g [j, r, e] \<down>=
      (if e_nth e j \<noteq> 0 then j else if j = r then Suc j else r)" for j r e
    by simp
  let ?h = "Pr 1 Z g"
  have "recfn 2 ?h"
    by (simp add: \<open>recfn 3 g\<close>)
  let ?P = "\<lambda>e j i. i < j \<and> e_nth e i \<noteq> 0"
  let ?G = "\<lambda>e j. Greatest (?P e j)"
  have h: "eval ?h [j, e] =
    (if \<forall>i<j. e_nth e i = 0 then Some j else Some (?G e j))" for j e
  proof (induction j)
    case 0
    then show ?case using \<open>recfn 2 ?h\<close> by auto
  next
    case (Suc j)
    then have "eval ?h [Suc j, e] = eval g [j, the (eval ?h [j, e]), e]"
      using \<open>recfn 2 ?h\<close> by auto
    then have "eval ?h [Suc j, e] =
        eval g [j, if \<forall>i<j. e_nth e i = 0 then j else ?G e j, e]"
      using Suc by auto
    then have *: "eval ?h [Suc j, e] \<down>=
      (if e_nth e j \<noteq> 0 then j
       else if j = (if \<forall>i<j. e_nth e i = 0 then j else ?G e j)
            then Suc j
            else (if \<forall>i<j. e_nth e i = 0 then j else ?G e j))"
      using g by simp
    show ?case
    proof (cases "\<forall>i<Suc j. e_nth e i = 0")
      case True
      then show ?thesis using * by simp
    next
      case False
      then have ex: "\<exists>i<Suc j. e_nth e i \<noteq> 0"
        by auto
      show ?thesis
      proof (cases "e_nth e j = 0")
        case True
        then have ex': "\<exists>i<j. e_nth e i \<noteq> 0"
          using ex less_Suc_eq by fastforce
        then have "(if \<forall>i<j. e_nth e i = 0 then j else ?G e j) = ?G e j"
          by metis
        moreover have "?G e j < j"
          using ex' GreatestI_nat[of "?P e j"] less_imp_le_nat by blast
        ultimately have "eval ?h [Suc j, e] \<down>= ?G e j"
          using * True by simp
        moreover have "?G e j = ?G e (Suc j)"
          using True by (metis less_SucI less_Suc_eq)
        ultimately show ?thesis using ex by metis
      next
        case False
        then have "eval ?h [Suc j, e] \<down>= j"
          using * by simp
        moreover have "?G e (Suc j) = j"
          using ex False Greatest_equality[of "?P e (Suc j)"] by simp
        ultimately show ?thesis using ex by simp
      qed
    qed
  qed
  let ?hh = "Cn 1 ?h [Cn 1 r_length [Id 1 0], Id 1 0]"
  have "recfn 1 ?hh"
    using \<open>recfn 2 ?h\<close> by simp
  with h have hh: "eval ?hh [e] \<down>=
      (if \<forall>i<e_length e. e_nth e i = 0 then e_length e else ?G e (e_length e))" for e
    by auto
  then have "eval ?hh [e] = findr e" for e
    unfolding findr_def by auto
  moreover have "total ?hh"
    using hh totalI1 \<open>recfn 1 ?hh\<close> by simp
  ultimately show ?thesis
    using \<open>recfn 1 ?hh\<close> g_def r_findr_def findr_def by metis
qed

lemma U0_in_CP: "U\<^sub>0 \<in> CP"
proof -
  define s where
    "s \<equiv> \<lambda>x. if findr x \<down>= e_length x then Some 0 else Some (e_take (Suc (the (findr x))) x)"
  have "s \<in> \<P>"
  proof -
    define r where
      "r \<equiv> Cn 1 r_ifeq [r_findr, r_length, Z, Cn 1 r_take [Cn 1 S [r_findr], Id 1 0]]"
    then have "\<And>x. eval r [x] = s x"
      using s_def findr_total by fastforce
    moreover have "recfn 1 r"
      using r_def by simp
    ultimately show ?thesis by auto
  qed
  moreover have "learn_cp prenum U\<^sub>0 s"
  proof (rule learn_cpI)
    show "environment prenum U\<^sub>0 s"
      using \<open>s \<in> \<P>\<close> s_def prenum_in_R2 U0_in_NUM by auto
    show "\<exists>i. prenum i = f \<and> (\<forall>\<^sup>\<infinity>n. s (f \<triangleright> n) \<down>= i)" if "f \<in> U\<^sub>0" for f
    proof (cases "f = (\<lambda>_. Some 0)")
      case True
      then have "s (f \<triangleright> n) \<down>= 0" for n
        using findr_def s_def by simp
      then have "\<forall>n\<ge>0. s (f \<triangleright> n) \<down>= 0" by simp
      moreover have "prenum 0 = f"
        using True by auto
      ultimately show ?thesis by auto
    next
      case False
      then obtain ws where ws: "length ws > 0" "last ws \<noteq> 0" "f = ws \<odot> 0\<^sup>\<infinity>"
        using U0_def \<open>f \<in> U\<^sub>0\<close> almost0_canonical by blast
      let ?m = "length ws - 1"
      let ?i = "list_encode ws"
      have "prenum ?i = f"
        using ws by auto
      moreover have "s (f \<triangleright> n) \<down>= ?i" if "n \<ge> ?m" for n
      proof -
        have "e_nth (f \<triangleright> n) ?m \<noteq> 0"
          using ws that by (simp add: last_conv_nth)
        then have "\<exists>k<Suc n. e_nth (f \<triangleright> n) k \<noteq> 0"
          using le_imp_less_Suc that by blast
        moreover have
          "(GREATEST k. k < e_length (f \<triangleright> n) \<and> e_nth (f \<triangleright> n) k \<noteq> 0) = ?m"
        proof (rule Greatest_equality)
          show "?m < e_length (f \<triangleright> n) \<and> e_nth (f \<triangleright> n) ?m \<noteq> 0"
            using \<open>e_nth (f \<triangleright> n) ?m \<noteq> 0\<close> that by auto
          show "\<And>y. y < e_length (f \<triangleright> n) \<and> e_nth (f \<triangleright> n) y \<noteq> 0 \<Longrightarrow> y \<le> ?m"
            using ws less_Suc_eq_le by fastforce
        qed
        ultimately have "findr (f \<triangleright> n) \<down>= ?m"
          using that findr_def by simp
        moreover have "?m < e_length (f \<triangleright> n)"
          using that by simp
        ultimately have "s (f \<triangleright> n) \<down>= e_take (Suc ?m) (f \<triangleright> n)"
          using s_def by simp
        moreover have "e_take (Suc ?m) (f \<triangleright> n) = list_encode ws"
        proof -
          have "take (Suc ?m) (prefix f n) = prefix f ?m"
            using take_prefix[of f ?m n] ws that by (simp add: almost0_in_R1)
          then have "take (Suc ?m) (prefix f n) = ws"
            using ws prefixI by auto
          then show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis by auto
    qed
    show "\<And>f n. f \<in> U\<^sub>0 \<Longrightarrow> prenum (the (s (f \<triangleright> n))) \<in> U\<^sub>0"
      using U0_def by fastforce
  qed
  ultimately show ?thesis using CP_def by blast
qed

text \<open>As a bit of an interlude, we can now show that CP is not
closed under the subset relation. This works by removing functions from
@{term "U\<^sub>0"} in a ``noncomputable'' way such that a strategy cannot ensure
that every intermediate hypothesis is in that new class.\<close>

lemma CP_not_closed_subseteq: "\<exists>V U. V \<subseteq> U \<and> U \<in> CP \<and> V \<notin> CP"
proof -
  \<comment> \<open>The numbering $g\in\mathcal{R}^2$ enumerates all
  functions $i0^\infty \in U_0$.\<close>
  define g where "g \<equiv> \<lambda>i. [i] \<odot>  0\<^sup>\<infinity>"
  have g_inj: "i = j" if "g i = g j" for i j
  proof -
    have "g i 0 \<down>= i" and "g j 0 \<down>= j"
      by (simp_all add: g_def)
    with that show "i = j"
      by (metis option.inject)
  qed

  \<comment> \<open>Define a class $V$. If the strategy $\varphi_i$ learns
  $g_i$, it outputs a hypothesis for $g_i$ on some shortest prefix $g_i^m$.
  Then the function $g_i^m10^\infty$ is included in the class $V$; otherwise
  $g_i$ is included.\<close>
  define V where "V \<equiv>
    {if learn_lim \<phi> {g i} (\<phi> i)
     then (prefix (g i) (LEAST n. \<phi> (the (\<phi> i ((g i) \<triangleright> n))) = g i)) @ [1] \<odot> 0\<^sup>\<infinity>
     else g i |
     i. i \<in> UNIV}"
  have "V \<notin> CP_wrt \<phi>"
  proof
    \<comment> \<open>Assuming $V \in CP_\varphi$, there is a CP strategy
    $\varphi_i$ for $V$.\<close>
    assume "V \<in> CP_wrt \<phi>"
    then obtain s where s: "s \<in> \<P>" "learn_cp \<phi> V s"
      using CP_wrt_def learn_cpE(1) by auto
    then obtain i where i: "\<phi> i = s"
      using phi_universal by auto

    show False
    proof (cases "learn_lim \<phi> {g i} (\<phi> i)")
      case learn: True
      \<comment> \<open>If $\varphi_i$ learns $g_i$, it hypothesizes $g_i$ on
      some shortest prefix $g_i^m$. Thus it hypothesizes $g_i$ on some prefix
      of $g_i^m10^\infty \in V$, too. But $g_i$ is not a class-preserving
      hypothesis because $g_i \notin V$.\<close>
      let ?P = "\<lambda>n. \<phi> (the (\<phi> i ((g i) \<triangleright>  n))) = g i"
      let ?m = "Least ?P"
      have "\<exists>n. ?P n"
        using i s by (meson learn infinite_hyp_wrong_not_Lim insertI1 lessI)
      then have "?P ?m"
        using LeastI_ex[of ?P] by simp
      define h where "h = (prefix (g i) ?m) @ [1] \<odot> 0\<^sup>\<infinity>"
      then have "h \<in> V"
        using V_def learn by auto
      have "(g i) \<triangleright>  ?m = h \<triangleright>  ?m"
      proof -
        have "prefix (g i) ?m = prefix h ?m"
          unfolding h_def by (simp add: prefix_prepend_less)
        then show ?thesis by auto
      qed
      then have "\<phi> (the (\<phi> i (h \<triangleright>  ?m))) = g i"
        using \<open>?P ?m\<close> by simp
      moreover have "g i \<notin> V"
      proof
        assume "g i \<in> V"
        then obtain j where j: "g i =
          (if learn_lim \<phi> {g j} (\<phi> j)
           then (prefix (g j) (LEAST n. \<phi> (the (\<phi> j ((g j) \<triangleright>  n))) = g j)) @ [1] \<odot> 0\<^sup>\<infinity>
           else g j)"
          using V_def by auto
        show False
        proof (cases "learn_lim \<phi> {g j} (\<phi> j)")
          case True
          then have "g i =
              (prefix (g j) (LEAST n. \<phi> (the (\<phi> j ((g j) \<triangleright>  n))) = g j)) @ [1] \<odot> 0\<^sup>\<infinity>"
              (is "g i = ?vs @ [1] \<odot> 0\<^sup>\<infinity>")
            using j by simp
          moreover have len: "length ?vs > 0" by simp
          ultimately have "g i (length ?vs) \<down>= 1"
            by (simp add: prepend_associative)
          moreover have "g i (length ?vs) \<down>= 0"
            using g_def len by simp
          ultimately show ?thesis by simp
        next
          case False
          then show ?thesis
            using j g_inj learn by auto
        qed
      qed
      ultimately have "\<phi> (the (\<phi> i (h \<triangleright>  ?m))) \<notin> V" by simp
      then have "\<not> learn_cp \<phi> V (\<phi> i)"
        using \<open>h \<in> V\<close> learn_cpE(3) by auto
      then show ?thesis by (simp add: i s(2))
    next
      \<comment> \<open>If $\varphi_i$ does not learn $g_i$, then $g_i\in V$.
      Hence $\varphi_i$ does not learn $V$.\<close>
      case False
      then have "g i \<in> V"
        using V_def by auto
      with False have "\<not> learn_lim \<phi> V (\<phi> i)"
        using learn_lim_closed_subseteq by auto
      then show ?thesis
        using s(2) i by (simp add: learn_cp_def)
    qed
  qed
  then have "V \<notin> CP"
    using CP_wrt_phi by simp
  moreover have "V \<subseteq> U\<^sub>0"
    using V_def g_def U0_def by auto
  ultimately show ?thesis using U0_in_CP by auto
qed

text \<open>Continuing with the main result of this section, we show that
@{term "U\<^sub>0"} cannot be learned finitely. Any FIN strategy would have
to output a hypothesis for the constant zero function on some prefix. But
@{term "U\<^sub>0"} contains infinitely many other functions starting with
the same prefix, which the strategy then would not learn finitely.\<close>

lemma U0_not_in_FIN: "U\<^sub>0 \<notin> FIN"
proof
  assume "U\<^sub>0 \<in> FIN"
  then obtain \<psi> s where "learn_fin \<psi> U\<^sub>0 s"
    using FIN_def by blast
  with learn_finE have cp: "\<And>f. f \<in> U\<^sub>0 \<Longrightarrow>
      \<exists>i n\<^sub>0. \<psi> i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i)"
    by simp_all

  define z where "z = [] \<odot> 0\<^sup>\<infinity>"
  then have "z \<in> U\<^sub>0"
    using U0_def by auto
  with cp obtain i n\<^sub>0 where i: "\<psi> i = z" and n0: "\<forall>n\<ge>n\<^sub>0. s (z \<triangleright> n) \<down>= Suc i"
    by blast

  define w where "w = replicate (Suc n\<^sub>0) 0 @ [1] \<odot> 0\<^sup>\<infinity>"
  then have "prefix w n\<^sub>0 = replicate (Suc n\<^sub>0) 0"
    by (simp add: prefix_prepend_less)
  moreover have "prefix z n\<^sub>0 = replicate (Suc n\<^sub>0) 0"
    using prefixI[of "replicate (Suc n\<^sub>0) 0" z] less_Suc_eq_0_disj unfolding z_def
    by fastforce
  ultimately have "z \<triangleright>  n\<^sub>0 = w \<triangleright> n\<^sub>0"
    by (simp add: init_prefixE)
  with n0 have *: "s (w \<triangleright> n\<^sub>0) \<down>= Suc i" by auto

  have "w \<in> U\<^sub>0" using w_def U0_def by auto
  with cp obtain i' n\<^sub>0' where i': "\<psi> i' = w"
    and n0': "\<forall>n<n\<^sub>0'. s (w \<triangleright> n) \<down>= 0" "\<forall>n\<ge>n\<^sub>0'. s (w \<triangleright> n) \<down>= Suc i'"
    by blast

  have "i \<noteq> i'"
  proof
    assume "i = i'"
    then have "w = z"
      using i i' by simp
    have "w (Suc n\<^sub>0) \<down>= 1"
      using w_def prepend[of "replicate (Suc n\<^sub>0) 0 @ [1]" "0\<^sup>\<infinity>" "Suc n\<^sub>0"]
      by (metis length_append_singleton length_replicate lessI nth_append_length)
    moreover have "z (Suc n\<^sub>0) \<down>= 0"
      using z_def by simp
    ultimately show False
      using \<open>w = z\<close> by simp
  qed
  then have "s (w \<triangleright> n\<^sub>0) \<down>\<noteq> Suc i"
    using n0' by (cases "n\<^sub>0 < n\<^sub>0'") simp_all
  with * show False by simp
qed

theorem FIN_subset_CP: "FIN \<subset> CP"
  using U0_in_CP U0_not_in_FIN FIN_subseteq_CP by auto


section \<open>NUM and FIN are incomparable\label{s:num_fin}\<close>

text \<open>The class $V_0$ of all total recursive functions $f$ where $f(0)$
is a Gödel number of $f$ can be learned finitely by always hypothesizing
$f(0)$. The class is not in NUM and therefore serves to separate NUM and
FIN.\<close>

definition V0 :: "partial1 set" ("V\<^sub>0") where
  "V\<^sub>0 = {f. f \<in> \<R> \<and> \<phi> (the (f 0)) = f}"

lemma V0_altdef: "V\<^sub>0 = {[i] \<odot> f| i f. f \<in> \<R> \<and> \<phi> i = [i] \<odot> f}"
  (is "V\<^sub>0 = ?W")
proof
  show "V\<^sub>0 \<subseteq> ?W"
  proof
    fix f
    assume "f \<in> V\<^sub>0"
    then have "f \<in> \<R>"
      unfolding V0_def by simp
    then obtain i where i: "f 0 \<down>= i" by fastforce
    define g where "g = (\<lambda>x. f (x + 1))"
    then have "g \<in> \<R>"
      using skip_R1[OF \<open>f \<in> \<R>\<close>] by blast
    moreover have "[i] \<odot> g = f"
      using g_def i by auto
    moreover have "\<phi> i = f"
      using \<open>f \<in> V\<^sub>0\<close> V0_def i by force
    ultimately show "f \<in> ?W" by auto
  qed
  show "?W \<subseteq> V\<^sub>0"
  proof
    fix g
    assume "g \<in> ?W"
    then have "\<phi> (the (g 0)) = g" by auto
    moreover have "g \<in> \<R>"
      using prepend_in_R1 \<open>g \<in> ?W\<close> by auto
    ultimately show "g \<in> V\<^sub>0"
      by (simp add: V0_def)
  qed
qed

lemma V0_in_FIN: "V\<^sub>0 \<in> FIN"
proof -
  define s where "s = (\<lambda>x. Some (Suc (e_hd x)))"
  have "s \<in> \<P>"
  proof -
    define r where "r = Cn 1 S [r_hd]"
    then have "recfn 1 r" by simp
    moreover have "eval r [x] \<down>= Suc (e_hd x)" for x
      unfolding r_def by simp
    ultimately show ?thesis
      using s_def by blast
  qed
  have s: "s (f \<triangleright> n) \<down>= Suc (the (f 0))" for f n
    unfolding s_def by simp
  have "learn_fin \<phi> V\<^sub>0 s"
  proof (rule learn_finI)
    show "environment \<phi> V\<^sub>0 s"
      using s_def \<open>s \<in> \<P>\<close> phi_in_P2 V0_def by auto
    show "\<exists>i n\<^sub>0. \<phi> i = f \<and> (\<forall>n<n\<^sub>0. s (f \<triangleright> n) \<down>= 0) \<and> (\<forall>n\<ge>n\<^sub>0. s (f \<triangleright> n) \<down>= Suc i)"
        if "f \<in> V\<^sub>0" for f
      using that V0_def s by auto
  qed
  then show ?thesis using FIN_def by auto
qed

text \<open>To every @{term "f \<in> \<R>"} a number can be prepended that is
a Gödel number of the resulting function. Such a function is then in $V_0$.

If $V_0$ was in NUM, it would be embedded in a total numbering. Shifting this
numbering to the left, essentially discarding the values at point $0$, would
yield a total numbering for @{term "\<R>"}, which contradicts @{thm[source]
R1_not_in_NUM}. This proves @{prop "V\<^sub>0 \<notin> NUM"}.\<close>

lemma prepend_goedel:
  assumes "f \<in> \<R>"
  shows "\<exists>i. \<phi> i = [i] \<odot> f"
proof -
  obtain r where r: "recfn 1 r" "total r" "\<And>x. eval r [x] = f x"
    using assms by auto
  define r_psi where "r_psi = Cn 2 r_ifz [Id 2 1, Id 2 0, Cn 2 r [Cn 2 r_dec [Id 2 1]]]"
  then have "recfn 2 r_psi"
    using r(1) by simp
  have "eval r_psi [i, x] = (if x = 0 then Some i else f (x - 1))" for i x
  proof -
    have "eval (Cn 2 r [Cn 2 r_dec [Id 2 1]]) [i, x] = f (x - 1)"
      using r by simp
    then have "eval r_psi [i, x] = eval r_ifz [x, i, the (f (x - 1))]"
      unfolding r_psi_def using \<open>recfn 2 r_psi\<close> r R1_imp_total1[OF assms] by auto
    then show ?thesis
      using assms by simp
  qed
  with \<open>recfn 2 r_psi\<close> have "(\<lambda>i x. if x = 0 then Some i else f (x - 1)) \<in> \<P>\<^sup>2"
    by auto
  with kleene_fixed_point obtain i where
    "\<phi> i = (\<lambda>x. if x = 0 then Some i else f (x - 1))"
    by blast
  then have "\<phi> i = [i] \<odot> f" by auto
  then show ?thesis by auto
qed

lemma V0_in_FIN_minus_NUM: "V\<^sub>0 \<in> FIN - NUM"
proof -
  have "V\<^sub>0 \<notin> NUM"
  proof
    assume "V\<^sub>0 \<in> NUM"
    then obtain \<psi> where \<psi>: "\<psi> \<in> \<R>\<^sup>2" "\<And>f. f \<in> V\<^sub>0 \<Longrightarrow> \<exists>i. \<psi> i = f"
      by auto
    define \<psi>' where "\<psi>' i x = \<psi> i (Suc x)" for i x
    have "\<psi>' \<in> \<R>\<^sup>2"
    proof
      from \<psi>(1) obtain r_psi where
        r_psi: "recfn 2 r_psi" "total r_psi" "\<And>i x. eval r_psi [i, x] = \<psi> i x"
        by blast
      define r_psi' where "r_psi' = Cn 2 r_psi [Id 2 0, Cn 2 S [Id 2 1]]"
      then have "recfn 2 r_psi'" and "\<And>i x. eval r_psi' [i, x] = \<psi>' i x"
        unfolding r_psi'_def \<psi>'_def using r_psi by simp_all
      then show "\<psi>' \<in> \<P>\<^sup>2" by blast
      show "total2 \<psi>'"
        using \<psi>'_def \<psi>(1) by (simp add: total2I)
    qed
    have "\<exists>i. \<psi>' i = f" if "f \<in> \<R>" for f
    proof -
      from that obtain j where j: "\<phi> j = [j] \<odot> f"
        using prepend_goedel by auto
      then have "\<phi> j \<in> V\<^sub>0"
        using that V0_altdef by auto
      with \<psi> obtain i where "\<psi> i = \<phi> j" by auto
      then have "\<psi>' i = f"
        using \<psi>'_def j by (auto simp add: prepend_at_ge)
      then show ?thesis by auto
    qed
    with \<open>\<psi>' \<in> \<R>\<^sup>2\<close> have "\<R> \<in> NUM" by auto
    with R1_not_in_NUM show False by simp
  qed
  then show ?thesis
    using V0_in_FIN by auto
qed

corollary FIN_not_subseteq_NUM: "\<not> FIN \<subseteq> NUM"
  using V0_in_FIN_minus_NUM by auto


section \<open>NUM and CP are incomparable\label{s:num_cp}\<close>

text \<open>There are FIN classes outside of NUM, and CP encompasses FIN.
Hence there are CP classes outside of NUM, too.\<close>

theorem CP_not_subseteq_NUM: "\<not> CP \<subseteq> NUM"
  using FIN_subseteq_CP FIN_not_subseteq_NUM by blast

text \<open>Conversely there is a subclass of @{term "U\<^sub>0"} that
is in NUM but cannot be learned in a class-preserving way. The following
proof is due to Jantke and Beick~\cite{jb-cpnii-81}. The idea is to
diagonalize against all strategies, that is, all partial recursive
functions.\<close>

theorem NUM_not_subseteq_CP: "\<not> NUM \<subseteq> CP"
proof-
  \<comment> \<open>Define a family of functions $f_k$.\<close>
  define f where "f \<equiv> \<lambda>k. [k] \<odot> 0\<^sup>\<infinity>"
  then have "f k \<in> \<R>" for k
    using almost0_in_R1 by auto

  \<comment> \<open>If the strategy $\varphi_k$ learns $f_k$ it hypothesizes
  $f_k$ for some shortest prefix $f_k^{a_k}$. Define functions $f'_k =
  k0^{a_k}10^\infty$.\<close>
  define a where
    "a \<equiv> \<lambda>k. LEAST x. (\<phi> (the ((\<phi> k) ((f k) \<triangleright> x)))) = f k"
  define f' where "f' \<equiv> \<lambda>k. (k # (replicate (a k) 0) @ [1]) \<odot> 0\<^sup>\<infinity>"
  then have "f' k \<in> \<R>" for k
    using almost0_in_R1 by auto

  \<comment> \<open>Although $f_k$ and $f'_k$ differ, they share the prefix of length $a_k + 1$.\<close>
  have init_eq: "(f' k) \<triangleright> (a k) = (f k) \<triangleright> (a k)" for k
  proof (rule init_eqI)
    fix x assume "x \<le> a k"
    then show "f' k x = f k x"
      by (cases "x = 0") (simp_all add: nth_append f'_def f_def)
  qed
  have "f k \<noteq> f' k" for k
  proof -
    have "f k (Suc (a k)) \<down>= 0" using f_def by auto
    moreover have "f' k (Suc (a k)) \<down>= 1"
      using f'_def prepend[of "(k # (replicate (a k) 0) @ [1])" "0\<^sup>\<infinity>" "Suc (a k)"]
      by (metis length_Cons length_append_singleton length_replicate lessI nth_Cons_Suc
        nth_append_length)
    ultimately show ?thesis by auto
  qed

  \<comment> \<open>The separating class $U$ contains $f'_k$ if $\varphi_k$
  learns $f_k$; otherwise it contains $f_k$.\<close>
  define U where
    "U \<equiv> {if learn_lim \<phi> {f k} (\<phi> k) then f' k else f k |k. k \<in> UNIV}"
  have "U \<notin> CP"
  proof
    assume "U \<in> CP"
    have "\<exists>k. learn_cp \<phi> U (\<phi> k)"
    proof -
      have "\<exists>\<psi> s. learn_cp \<psi> U s"
        using CP_def \<open>U \<in> CP\<close> by auto
      then obtain s where s: "learn_cp \<phi> U s"
        using learn_cp_wrt_goedel[OF goedel_numbering_phi] by blast
      then obtain k where "\<phi> k = s"
        using phi_universal learn_cp_def learn_lim_def by auto
      then show ?thesis using s by auto
    qed
    then obtain k where k: "learn_cp \<phi> U (\<phi> k)" by auto
    then have learn: "learn_lim \<phi> U (\<phi> k)"
      using learn_cp_def by simp
    \<comment> \<open>If $f_k$ was in $U$, $\varphi_k$ would learn it. But then,
    by definition of $U$, $f_k$ would not be in $U$. Hence $f_k \notin U$.\<close>
    have "f k \<notin> U"
    proof
      assume "f k \<in> U"
      then obtain m where m: "f k = (if learn_lim \<phi> {f m} (\<phi> m) then f' m else f m)"
        using U_def by auto
      have "f k 0 \<down>= m"
        using f_def f'_def m by simp
      moreover have "f k 0 \<down>= k" by (simp add: f_def)
      ultimately have "m = k" by simp
      with m have "f k = (if learn_lim \<phi> {f k} (\<phi> k) then f' k else f k)"
        by auto
      moreover have "learn_lim \<phi> {f k} (\<phi> k)"
        using \<open>f k \<in> U\<close> learn_lim_closed_subseteq[OF learn] by simp
      ultimately have "f k = f' k"
        by simp
      then show False
        using \<open>f k \<noteq> f' k\<close> by simp
    qed
    then have "f' k \<in> U" using U_def by fastforce
    then have in_U: "\<forall>n. \<phi> (the ((\<phi> k) ((f' k) \<triangleright> n))) \<in> U"
      using learn_cpE(3)[OF k] by simp

    \<comment> \<open>Since $f'_k \in U$, the strategy $\varphi_k$ learns $f_k$.
    Then $a_k$ is well-defined, $f'^{a_k} = f^{a_k}$, and $\varphi_k$
    hypothesizes $f_k$ on $f'^{a_k}$, which is not a class-preserving
    hypothesis.\<close>
    have "learn_lim \<phi> {f k} (\<phi> k)" using U_def \<open>f k \<notin> U\<close> by fastforce
    then have "\<exists>i n\<^sub>0. \<phi> i = f k \<and> (\<forall>n\<ge>n\<^sub>0. \<phi> k ((f k) \<triangleright> n) \<down>= i)"
      using learn_limE(2) by simp
    then obtain i n\<^sub>0 where "\<phi> i = f k \<and> (\<forall>n\<ge>n\<^sub>0. \<phi> k ((f k) \<triangleright> n) \<down>= i)"
      by auto
    then have "\<phi> (the (\<phi> k ((f k) \<triangleright> (a k)))) = f k"
      using a_def LeastI[of "\<lambda>x. (\<phi> (the ((\<phi> k) ((f k) \<triangleright> x)))) = f k" n\<^sub>0]
      by simp
    then have "\<phi> (the ((\<phi> k) ((f' k) \<triangleright> (a k)))) = f k"
      using init_eq by simp
    then show False
      using \<open>f k \<notin> U\<close> in_U by metis
  qed
  moreover have "U \<in> NUM"
    using NUM_closed_subseteq[OF U0_in_NUM, of U] f_def f'_def U0_def U_def
    by fastforce
  ultimately show ?thesis by auto
qed


section \<open>NUM is a proper subset of TOTAL\label{s:num_total}\<close>

text \<open>A NUM class $U$ is embedded in a total numbering @{term \<psi>}.
The strategy $S$ with $S(f^n) = \min \{i \mid \forall k \le n: \psi_i(k) =
f(k)\}$ for $f \in U$ converges to the least index of $f$ in @{term \<psi>},
and thus learns $f$ in the limit. Moreover it will be a TOTAL strategy
because @{term \<psi>} contains only total functions. This shows @{prop "NUM
\<subseteq> TOTAL"}.\<close>

text \<open>First we define, for every hypothesis space $\psi$, a
function that tries to determine for a given list $e$ and index $i$ whether
$e$ is a prefix of $\psi_i$. In other words it tries to decide whether $i$ is
a consistent hypothesis for $e$. ``Tries'' refers to the fact that the
function will diverge if $\psi_i(x)\uparrow$ for any $x \le |e|$. We start
with a version that checks the list only up to a given length.\<close>

definition r_consist_upto :: "recf \<Rightarrow> recf" where
  "r_consist_upto r_psi \<equiv>
    let g = Cn 4 r_ifeq
      [Cn 4 r_psi [Id 4 2, Id 4 0], Cn 4 r_nth [Id 4 3, Id 4 0], Id 4 1, r_constn 3 1]
    in Pr 2 (r_constn 1 0) g"

lemma r_consist_upto_recfn: "recfn 2 r_psi \<Longrightarrow> recfn 3 (r_consist_upto r_psi)"
  using r_consist_upto_def by simp

lemma r_consist_upto:
  assumes "recfn 2 r_psi"
  shows "\<forall>k<j. eval r_psi [i, k] \<down> \<Longrightarrow>
      eval (r_consist_upto r_psi) [j, i, e] =
        (if \<forall>k<j. eval r_psi [i, k] \<down>= e_nth e k then Some 0 else Some 1)"
    and "\<not> (\<forall>k<j. eval r_psi [i, k] \<down>) \<Longrightarrow> eval (r_consist_upto r_psi) [j, i, e] \<up>"
proof -
  define g where "g =
    Cn 4 r_ifeq
     [Cn 4 r_psi [Id 4 2, Id 4 0], Cn 4 r_nth [Id 4 3, Id 4 0], Id 4 1, r_constn 3 1]"
  then have "recfn 4 g"
    using assms by simp
  moreover have "eval (Cn 4 r_nth [Id 4 3, Id 4 0]) [j, r, i, e] \<down>= e_nth e j" for j r i e
    by simp
  moreover have "eval (r_constn 3 1) [j, r, i, e] \<down>= 1" for j r i e
    by simp
  moreover have "eval (Cn 4 r_psi [Id 4 2, Id 4 0]) [j, r, i, e] = eval r_psi [i, j]" for j r i e
    using assms(1) by simp
  ultimately have g: "eval g [j, r, i, e] =
    (if eval r_psi [i, j] \<up> then None
     else if eval r_psi [i, j] \<down>= e_nth e j then Some r else Some 1)"
    for j r i e
    using \<open>recfn 4 g\<close> g_def assms by auto
  have goal1: "\<forall>k<j. eval r_psi [i, k] \<down> \<Longrightarrow>
    eval (r_consist_upto r_psi) [j, i, e] =
      (if \<forall>k<j. eval r_psi [i, k] \<down>= e_nth e k then Some 0 else Some 1)"
    for j i e
  proof (induction j)
    case 0
    then show ?case
      using r_consist_upto_def r_consist_upto_recfn assms eval_Pr_0 by simp
  next
    case (Suc j)
    then have "eval (r_consist_upto r_psi) [Suc j, i, e] =
        eval g [j, the (eval (r_consist_upto r_psi) [j, i, e]), i, e]"
      using assms eval_Pr_converg_Suc g_def r_consist_upto_def r_consist_upto_recfn
      by simp
    also have "... = eval g [j, if \<forall>k<j. eval r_psi [i, k] \<down>= e_nth e k then 0 else 1, i, e]"
      using Suc by auto
    also have "... \<down>= (if eval r_psi [i, j] \<down>= e_nth e j
        then if \<forall>k<j. eval r_psi [i, k] \<down>= e_nth e k then 0 else 1 else 1)"
      using g by (simp add: Suc.prems)
    also have "... \<down>= (if \<forall>k<Suc j. eval r_psi [i, k] \<down>= e_nth e k then 0 else 1)"
      by (simp add: less_Suc_eq)
    finally show ?case by simp
  qed
  then show "\<forall>k<j. eval r_psi [i, k] \<down> \<Longrightarrow>
    eval (r_consist_upto r_psi) [j, i, e] =
    (if \<forall>k<j. eval r_psi [i, k] \<down>= e_nth e k then Some 0 else Some 1)"
    by simp
  show "\<not> (\<forall>k<j. eval r_psi [i, k] \<down>) \<Longrightarrow> eval (r_consist_upto r_psi) [j, i, e] \<up>"
  proof -
    assume "\<not> (\<forall>k<j. eval r_psi [i, k] \<down>)"
    then have "\<exists>k<j. eval r_psi [i, k] \<up>" by simp
    let ?P = "\<lambda>k. k < j \<and> eval r_psi [i, k] \<up>"
    define kmin where "kmin = Least ?P"
    then have "?P kmin"
      using LeastI_ex[of ?P] \<open>\<exists>k<j. eval r_psi [i, k] \<up>\<close> by auto
    from kmin_def have "\<And>k. k < kmin \<Longrightarrow> \<not> ?P k"
      using kmin_def not_less_Least[of _ ?P] by blast
    then have "\<forall>k < kmin. eval r_psi [i, k] \<down>"
      using \<open>?P kmin\<close> by simp
    then have "eval (r_consist_upto r_psi) [kmin, i, e] =
        (if \<forall>k<kmin. eval r_psi [i, k] \<down>= e_nth e k then Some 0 else Some 1)"
      using goal1 by simp
    moreover have "eval r_psi [i, kmin] \<up>"
      using \<open>?P kmin\<close> by simp
    ultimately have "eval (r_consist_upto r_psi) [Suc kmin, i, e] \<up>"
      using r_consist_upto_def g assms by simp
    moreover have "j \<ge> kmin"
      using \<open>?P kmin\<close> by simp
    ultimately show "eval (r_consist_upto r_psi) [j, i, e] \<up>"
      using r_consist_upto_def r_consist_upto_recfn \<open>?P kmin\<close> eval_Pr_converg_le assms
      by (metis (full_types) Suc_leI length_Cons list.size(3) numeral_2_eq_2 numeral_3_eq_3)
  qed
qed

text \<open>The next function provides the consistency decision functions we
need.\<close>

definition consistent :: "partial2 \<Rightarrow> partial2" where
  "consistent \<psi> i e \<equiv>
    if \<forall>k<e_length e. \<psi> i k \<down>
    then if \<forall>k<e_length e. \<psi> i k \<down>= e_nth e k
         then Some 0 else Some 1
    else None"

text \<open>Given $i$ and $e$, @{term "consistent \<psi>"} decides whether $e$
is a prefix of $\psi_i$, provided $\psi_i$ is defined for the length of
$e$.\<close>

definition r_consistent :: "recf \<Rightarrow> recf" where
  "r_consistent r_psi \<equiv>
     Cn 2 (r_consist_upto r_psi) [Cn 2 r_length [Id 2 1], Id 2 0, Id 2 1]"

lemma r_consistent_recfn [simp]: "recfn 2 r_psi \<Longrightarrow> recfn 2 (r_consistent r_psi)"
  using r_consistent_def r_consist_upto_recfn by simp

lemma r_consistent_converg:
  assumes "recfn 2 r_psi" and "\<forall>k<e_length e. eval r_psi [i, k] \<down>"
  shows "eval (r_consistent r_psi) [i, e] \<down>=
    (if \<forall>k<e_length e. eval r_psi [i, k] \<down>= e_nth e k then 0 else 1)"
proof -
  have "eval (r_consistent r_psi) [i, e] = eval (r_consist_upto r_psi) [e_length e, i, e]"
    using r_consistent_def r_consist_upto_recfn assms(1) by simp
  then show ?thesis using assms r_consist_upto(1) by simp
qed

lemma r_consistent_diverg:
  assumes "recfn 2 r_psi" and "\<exists>k<e_length e. eval r_psi [i, k] \<up>"
  shows "eval (r_consistent r_psi) [i, e] \<up>"
  unfolding r_consistent_def
  using r_consist_upto_recfn[OF assms(1)] r_consist_upto[OF assms(1)] assms(2)
  by simp

lemma r_consistent:
  assumes "recfn 2 r_psi" and "\<forall>x y. eval r_psi [x, y] = \<psi> x y"
  shows "eval (r_consistent r_psi) [i, e] = consistent \<psi> i e"
proof (cases "\<forall>k<e_length e. \<psi> i k \<down>")
  case True
  then have "\<forall>k<e_length e. eval r_psi [i, k] \<down>"
    using assms by simp
  then show ?thesis
    unfolding consistent_def using True by (simp add: assms r_consistent_converg)
next
  case False
  then have "consistent \<psi> i e \<up>"
    unfolding consistent_def by auto
  moreover have "eval (r_consistent r_psi) [i, e] \<up>"
    using r_consistent_diverg[OF assms(1)] assms False by simp
  ultimately show ?thesis by simp
qed

lemma consistent_in_P2:
  assumes "\<psi> \<in> \<P>\<^sup>2"
  shows "consistent \<psi> \<in> \<P>\<^sup>2"
  using assms r_consistent P2E[OF assms(1)] P2I r_consistent_recfn by metis

lemma consistent_for_R2:
  assumes "\<psi> \<in> \<R>\<^sup>2"
  shows "consistent \<psi> i e =
    (if \<forall>j<e_length e. \<psi> i j \<down>= e_nth e j then Some 0 else Some 1)"
  using assms by (simp add: consistent_def)

lemma consistent_init:
  assumes "\<psi> \<in> \<R>\<^sup>2" and "f \<in> \<R>"
  shows "consistent \<psi> i (f \<triangleright> n) = (if \<psi> i \<triangleright> n = f \<triangleright> n then Some 0 else Some 1)"
  using consistent_def[of _ _ "init f n"] assms  init_eq_iff_eq_upto by simp

lemma consistent_in_R2:
  assumes "\<psi> \<in> \<R>\<^sup>2"
  shows "consistent \<psi> \<in> \<R>\<^sup>2"
  using total2I consistent_in_P2 consistent_for_R2[OF assms] P2_total_imp_R2 R2_imp_P2 assms
  by (metis option.simps(3))

text \<open>For total hypothesis spaces the next function computes the
minimum hypothesis consistent with a given prefix. It diverges if no such
hypothesis exists.\<close>

definition min_cons_hyp :: "partial2 \<Rightarrow> partial1" where
  "min_cons_hyp \<psi> e \<equiv>
    if \<exists>i. consistent \<psi> i e \<down>= 0 then Some (LEAST i. consistent \<psi> i e \<down>= 0) else None"

lemma min_cons_hyp_in_P1:
  assumes "\<psi> \<in> \<R>\<^sup>2"
  shows "min_cons_hyp \<psi> \<in> \<P>"
proof -
  from assms consistent_in_R2 obtain rc where
    rc: "recfn 2 rc" "total rc" "\<And>i e. eval rc [i, e] = consistent \<psi> i e"
    using R2E[of "consistent \<psi>"] by metis
  define r where "r = Mn 1 rc"
  then have "recfn 1 r"
    using rc(1) by simp
  moreover from this have "eval r [e] = min_cons_hyp \<psi> e" for e
    using r_def eval_Mn'[of 1 rc "[e]"] rc min_cons_hyp_def assms
    by (auto simp add: consistent_in_R2)
  ultimately show ?thesis by auto
qed

text \<open>The function @{term "min_cons_hyp \<psi>"} is a strategy for
learning all NUM classes embedded in @{term \<psi>}. It is an example of an
``identification-by-enumeration'' strategy.\<close>

lemma NUM_imp_learn_total:
  assumes "\<psi> \<in> \<R>\<^sup>2" and "U \<in> NUM_wrt \<psi>"
  shows "learn_total \<psi> U (min_cons_hyp \<psi>)"
proof (rule learn_totalI)
  have ex_psi_i_f: "\<exists>i. \<psi> i = f" if "f \<in> U" for f
    using assms that NUM_wrt_def by simp
  moreover have consistent_eq_0: "consistent \<psi> i ((\<psi> i) \<triangleright> n) \<down>= 0" for i n
    using assms by (simp add: consistent_init)
  ultimately have "\<And>f n. f \<in> U \<Longrightarrow> min_cons_hyp \<psi> (f \<triangleright> n) \<down>"
    using min_cons_hyp_def assms(1) by fastforce
  then show env: "environment \<psi> U (min_cons_hyp \<psi>)"
    using assms NUM_wrt_def min_cons_hyp_in_P1 NUM_E(1) NUM_I by auto

  show "\<And>f n. f \<in> U \<Longrightarrow> \<psi> (the (min_cons_hyp \<psi> (f \<triangleright> n))) \<in> \<R>"
    using assms by (simp)

  show "\<exists>i. \<psi> i = f \<and> (\<forall>\<^sup>\<infinity>n. min_cons_hyp \<psi> (f \<triangleright> n) \<down>= i)" if "f \<in> U" for f
  proof -
    from that env have "f \<in> \<R>" by auto

    let ?P = "\<lambda>i. \<psi> i = f"
    define imin where "imin \<equiv> Least ?P"
    with ex_psi_i_f that have imin: "?P imin" "\<And>j. ?P j \<Longrightarrow> j \<ge> imin"
      using LeastI_ex[of ?P] Least_le[of ?P] by simp_all
    then have f_neq: "\<psi> i \<noteq> f" if "i < imin" for i
      using leD that by auto

    let ?Q = "\<lambda>i n. \<psi> i \<triangleright> n \<noteq> f \<triangleright> n"
    define nu :: "nat \<Rightarrow> nat" where "nu = (\<lambda>i. SOME n. ?Q i n)"
    have nu_neq: "\<psi> i \<triangleright> (nu i) \<noteq> f \<triangleright> (nu i)" if "i < imin" for i
    proof -
      from assms have "\<psi> i \<in> \<R>" by simp
      moreover from assms imin(1) have "f \<in> \<R>" by auto
      moreover have "f \<noteq> \<psi> i"
        using that f_neq by auto
      ultimately have "\<exists>n. f \<triangleright> n \<noteq> (\<psi> i) \<triangleright> n"
        using neq_fun_neq_init by simp
      then show "?Q i (nu i)"
        unfolding nu_def using someI_ex[of "\<lambda>n. ?Q i n"] by metis
    qed

    have "\<exists>n\<^sub>0. \<forall>n\<ge>n\<^sub>0. min_cons_hyp \<psi> (f \<triangleright> n) \<down>= imin"
    proof (cases "imin = 0")
      case True
      then have "\<forall>n. min_cons_hyp \<psi> (f \<triangleright> n) \<down>= imin"
        using consistent_eq_0 assms(1) imin(1) min_cons_hyp_def by auto
      then show ?thesis by simp
    next
      case False
      define n\<^sub>0 where "n\<^sub>0 = Max (set (map nu [0..<imin]))" (is "_ = Max ?N")
      have "nu i \<le> n\<^sub>0" if "i < imin" for i
      proof -
        have "finite ?N"
          using n\<^sub>0_def by simp
        moreover have "?N \<noteq> {}"
          using False n\<^sub>0_def by simp
        moreover have "nu i \<in> ?N"
          using that by simp
        ultimately show ?thesis
          using that Max_ge n\<^sub>0_def by blast
      qed
      then have "\<psi> i \<triangleright> n\<^sub>0 \<noteq> f \<triangleright> n\<^sub>0" if "i < imin" for i
        using nu_neq neq_init_forall_ge that by blast
      then have *: "\<psi> i \<triangleright> n \<noteq> f \<triangleright> n" if "i < imin" and "n \<ge> n\<^sub>0" for i n
        using nu_neq neq_init_forall_ge that by blast

      have "\<psi> imin \<triangleright> n = f \<triangleright> n" for n
        using imin(1) by simp
      moreover have "(consistent \<psi> i (f \<triangleright> n) \<down>= 0) = (\<psi> i \<triangleright> n = f \<triangleright> n)" for i n
        by (simp add: \<open>f \<in> \<R>\<close> assms(1) consistent_init)
      ultimately have "min_cons_hyp \<psi> (f \<triangleright> n) \<down>= (LEAST i. \<psi> i \<triangleright> n = f \<triangleright> n)" for n
        using min_cons_hyp_def[of \<psi> "f \<triangleright> n"] by auto
      moreover have "(LEAST i. \<psi> i \<triangleright> n = f \<triangleright> n) = imin" if "n \<ge> n\<^sub>0" for n
      proof (rule Least_equality)
        show "\<psi> imin \<triangleright> n = f \<triangleright> n"
          using imin(1) by simp
        show "\<And>y. \<psi> y \<triangleright> n = f \<triangleright> n \<Longrightarrow> imin \<le> y"
          using imin * leI that by blast
      qed
      ultimately have "min_cons_hyp \<psi> (f \<triangleright> n) \<down>= imin" if "n \<ge> n\<^sub>0" for n
        using that by blast
      then show ?thesis by auto
    qed
    with imin(1) show ?thesis by auto
  qed
qed

corollary NUM_subseteq_TOTAL: "NUM \<subseteq> TOTAL"
proof
  fix U
  assume "U \<in> NUM"
  then have "\<exists>\<psi>\<in>\<R>\<^sup>2. \<forall>f\<in>U. \<exists>i. \<psi> i = f" by auto
  then have "\<exists>\<psi>\<in>\<R>\<^sup>2. U \<in> NUM_wrt \<psi>"
    using NUM_wrt_def by simp
  then have "\<exists>\<psi> s. learn_total \<psi> U s"
    using NUM_imp_learn_total by auto
  then show "U \<in> TOTAL"
    using TOTAL_def by auto
qed

text \<open>The class @{term V0} is in @{term "TOTAL - NUM"}. \<close>

theorem NUM_subset_TOTAL: "NUM \<subset> TOTAL"
  using CP_subseteq_TOTAL FIN_not_subseteq_NUM FIN_subseteq_CP NUM_subseteq_TOTAL
  by auto

end