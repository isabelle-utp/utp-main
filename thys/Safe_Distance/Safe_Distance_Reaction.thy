\<^marker>\<open>creator "Albert Rizaldi" "Fabian Immler\<close>

section \<open>Safe Distance with Reaction Time\<close>

theory Safe_Distance_Reaction
imports
  Safe_Distance
begin

subsection \<open>Normal Safe Distance\<close>
                                    
locale safe_distance_normal = safe_distance +
  fixes \<delta> :: real
  assumes pos_react: "0 < \<delta>"
begin

sublocale ego2: braking_movement a\<^sub>e v\<^sub>e "(ego.q \<delta>)" ..

lemma ego2_s_init: "ego2.s 0 = ego.q \<delta>" unfolding ego2.s_def by auto

definition \<tau> :: "real \<Rightarrow> real" where
  "\<tau> t = t - \<delta>"

definition \<tau>' :: "real \<Rightarrow> real" where
  "\<tau>' t = 1"

lemma \<tau>_continuous[continuous_intros]: "continuous_on T \<tau>"
  unfolding \<tau>_def by (auto intro: continuous_intros)

lemma isCont_\<tau>[continuous_intros]: "isCont \<tau> x"
  using \<tau>_continuous[of UNIV] by (auto simp: continuous_on_eq_continuous_at)

lemma del_has_vector_derivative[derivative_intros]: "(\<tau> has_vector_derivative \<tau>' t) (at t within u)"
  by (auto simp: \<tau>_def[abs_def] \<tau>'_def has_vector_derivative_def algebra_simps
           intro!: derivative_eq_intros)
                                                             
lemma del_has_real_derivative[derivative_intros]: "(\<tau> has_real_derivative \<tau>' t) (at t within u)"
  using del_has_vector_derivative
  by (simp add:has_field_derivative_iff_has_vector_derivative)

lemma delay_image: "\<tau> ` {\<delta>..} = {0..}"
proof (rule subset_antisym, unfold image_def, unfold \<tau>_def)
  show "{y. \<exists>x\<in>{\<delta>..}. y = x - \<delta>} \<subseteq> {0..}" by auto
next
  show "{0..} \<subseteq> {y. \<exists>x\<in>{\<delta>..}. y = x - \<delta>}"
  proof (rule subsetI)
    fix a
    assume "(a::real) \<in> {0..}"
    hence "0 \<le> a" by simp
    hence "\<exists>x\<in>{\<delta>..}. a = x - \<delta>" using bexI[where x = "a + \<delta>"] by auto
    thus "a \<in> {y. \<exists>x\<in>{\<delta>..}. y = x - \<delta>}" by auto
  qed
qed

lemma s_delayed_has_real_derivative[derivative_intros]:
  assumes "\<delta> \<le> t"
  shows "((ego2.s \<circ> \<tau>) has_field_derivative ego2.s' (t - \<delta>) * \<tau>' t) (at t within {\<delta>..})"
proof (rule DERIV_image_chain)
  from assms have 0: "0 \<le> t - \<delta>" by simp
  from ego2.t_stop_nonneg have 1: "v\<^sub>e / a\<^sub>e \<le> 0" unfolding ego2.t_stop_def by simp
  from ego2.decel have 2: "a\<^sub>e \<noteq> 0" by simp
  show "(ego2.s has_real_derivative ego2.s' (t - \<delta>)) (at (\<tau> t) within \<tau> ` {\<delta>..})"
  using ego2.s_has_real_derivative[OF 0 1 2] sym[OF delay_image]
  unfolding \<tau>_def by simp
next
  from del_has_real_derivative show "(\<tau> has_real_derivative \<tau>' t) (at t within {\<delta>..})" 
  by auto
qed

lemma s_delayed_has_real_derivative' [derivative_intros]:
  assumes "\<delta> \<le> t"
  shows "((ego2.s \<circ> \<tau>) has_field_derivative (ego2.s' \<circ> \<tau>) t) (at t within {\<delta>..})"
proof -
  from s_delayed_has_real_derivative[OF assms] have
  "((ego2.s \<circ> \<tau>) has_field_derivative ego2.s' (t - \<delta>) * \<tau>' t) (at t within {\<delta>..})"
  by auto
  hence "((ego2.s \<circ> \<tau>) has_field_derivative ego2.s' (t - \<delta>) * 1) (at t within {\<delta>..})"
  using \<tau>'_def[of t] by metis
  hence "((ego2.s \<circ> \<tau>) has_field_derivative ego2.s' (t - \<delta>)) (at t within {\<delta>..})"
  by (simp add:algebra_simps)  
  thus ?thesis unfolding comp_def \<tau>_def by auto
qed

lemma s_delayed_has_vector_derivative' [derivative_intros]:
  assumes "\<delta> \<le> t"
  shows "((ego2.s \<circ> \<tau>) has_vector_derivative (ego2.s' \<circ> \<tau>) t) (at t within {\<delta>..})"
  using s_delayed_has_real_derivative'[OF assms]
  by (simp add:has_field_derivative_iff_has_vector_derivative)
  
definition u :: "real \<Rightarrow> real" where
  "u t = (     if t \<le> 0 then s\<^sub>e
          else if t \<le> \<delta> then ego.q t 
          else          (ego2.s \<circ> \<tau>) t)"

lemma init_u: "t \<le> 0 \<Longrightarrow> u t = s\<^sub>e" unfolding u_def by auto

lemma u_delta: "u \<delta> = ego2.s 0"
proof -  
  have "u \<delta> = ego.q \<delta>" using pos_react unfolding u_def by auto
  also have "... = ego2.s 0" unfolding ego2.s_def by auto
  finally show "u \<delta> = ego2.s 0" .
qed

lemma q_delta: "ego.q \<delta> = ego2.s 0" using u_delta pos_react unfolding u_def by auto

definition u' :: "real \<Rightarrow> real" where
  "u' t = (if t \<le> \<delta> then ego.q' t else ego2.s' (t - \<delta>))"

lemma u'_delta: "u' \<delta> = ego2.s' 0"
proof -
  have "u' \<delta> = ego.q' \<delta>" unfolding u'_def by auto
  also have "... = v\<^sub>e" unfolding ego2.q'_def by simp
  also have "... = ego2.p' 0" unfolding ego2.p'_def by simp
  also have "... = ego2.s' 0" using ego2.t_stop_nonneg unfolding ego2.s'_def by auto 
  finally show "u' \<delta> = ego.s' 0" .
qed

lemma q'_delta: "ego.q' \<delta> = ego2.s' 0" using u'_delta unfolding u'_def by auto

lemma u_has_real_derivative[derivative_intros]:
  assumes nonneg_t: "t \<ge> 0"
  shows "(u has_real_derivative u' t) (at t within {0..})"
proof -
  from pos_react have "0 \<le> \<delta>" by simp

  have temp: "((\<lambda>t. if t \<in> {0 .. \<delta>} then ego.q t else (ego2.s \<circ> \<tau>) t) has_real_derivative
    (if t \<in> {0..\<delta>} then ego.q' t else (ego2.s' \<circ> \<tau>) t)) (at t within {0..})" (is "(?f1 has_real_derivative ?f2) (?net)")
    unfolding u_def[abs_def] u'_def 
      has_field_derivative_iff_has_vector_derivative
    apply (rule has_vector_derivative_If_within_closures[where T = "{\<delta>..}"])
    using \<open>0 \<le> \<delta>\<close> q_delta q'_delta ego.s_has_vector_derivative[OF assms] ego.decel ego.t_stop_nonneg 
    s_delayed_has_vector_derivative'[of "t"] \<tau>_def
    unfolding comp_def
    by (auto simp: assms  max_def insert_absorb   
      intro!: ego.q_has_vector_derivative)
  show ?thesis
    unfolding has_vector_derivative_def has_field_derivative_iff_has_vector_derivative
      u'_def u_def[abs_def] 
    proof (rule has_derivative_transform[where f="(\<lambda>t. if t \<in> {0..\<delta>} then ego.q t else (ego2.s \<circ> \<tau>) t)"])
      from nonneg_t show " t \<in> {0..}" by auto
    next
      fix x
      assume "(x::real) \<in> {0..}"
      hence  "x \<le> \<delta> \<longleftrightarrow> x \<in> {0 .. \<delta>}" by simp
      thus  " (if x \<le> 0 then s\<^sub>e else if x \<le> \<delta> then ego.q x else (ego2.s \<circ> \<tau>) x) =
         (if x \<in> {0..\<delta>} then ego.q x else (ego2.s \<circ> \<tau>) x)" using pos_react unfolding ego.q_def by auto
    next
      from temp have "(?f1 has_vector_derivative ?f2) ?net"
      using has_field_derivative_iff_has_vector_derivative by auto      
      moreover with assms have "t \<in> {0 .. \<delta>} \<longleftrightarrow> t \<le> \<delta>" by auto
      ultimately show " ((\<lambda>t. if t \<in> {0..\<delta>} then ego.q t else (ego2.s \<circ> \<tau>) t) has_derivative
              (\<lambda>x. x *\<^sub>R (if t \<le> \<delta> then ego2.q' t else ego2.s' (t - \<delta>)))) (at t within {0..})" 
      unfolding comp_def \<tau>_def has_vector_derivative_def by auto
    qed 
qed

definition t_stop :: real where 
  "t_stop = ego2.t_stop + \<delta>"

lemma t_stop_nonneg: "0 \<le> t_stop"
  unfolding t_stop_def
  using ego2.t_stop_nonneg pos_react
  by auto

lemma t_stop_pos: "0 < t_stop"
  unfolding t_stop_def
  using ego2.t_stop_nonneg pos_react
  by auto

lemma t_stop_zero:
  assumes "t_stop \<le> x"
  assumes "x \<le> \<delta>"
  shows "v\<^sub>e = 0"
  using assms unfolding t_stop_def using ego2.t_stop_nonneg pos_react ego2.t_stop_zero by auto

lemma u'_stop_zero: "u' t_stop = 0" 
  unfolding u'_def t_stop_def ego2.q'_def ego2.s'_def
  using ego2.t_stop_nonneg ego2.p'_stop_zero decelerate_ego ego2.t_stop_zero by auto

definition u_max :: real where 
  "u_max = u (ego2.t_stop + \<delta>)"

lemma u_max_eq: "u_max = ego.q \<delta> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2"
proof (cases "ego2.t_stop = 0")
  assume "ego2.t_stop = 0"
  hence "v\<^sub>e = 0" using ego2.t_stop_zero by simp
  with \<open>ego2.t_stop = 0\<close> show "u_max = ego.q \<delta> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2"  unfolding u_max_def u_def using pos_react by auto
next
  assume "ego2.t_stop \<noteq> 0"
  hence "u_max = (ego2.s \<circ> \<tau>) (ego2.t_stop + \<delta>)" 
    unfolding u_max_def u_def  using ego2.t_stop_nonneg pos_react by auto 
  moreover have "... = ego2.s ego2.t_stop" unfolding comp_def \<tau>_def by auto
  moreover have "... = ego2.p_max" 
    unfolding ego2.s_def ego2.p_max_def using \<open>ego2.t_stop \<noteq> 0\<close> ego2.t_stop_nonneg by auto
  moreover have "... = ego.q \<delta> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2" using ego2.p_max_eq .
  ultimately show ?thesis by auto
qed

lemma u_mono: 
  assumes "x \<le> y" "y \<le> t_stop" 
  shows "u x \<le> u y"
proof -
  have "y \<le> 0 \<or> (0 < y \<and> y \<le> \<delta>) \<or> \<delta> < y" by auto

  moreover
  { assume "y \<le> 0"
    with assms have "x \<le> 0" by auto
    with \<open>y \<le> 0\<close> have "u x \<le> u y" unfolding u_def by auto }

  moreover
  { assume "0 < y \<and> y \<le> \<delta>"
    with assms have "x \<le> \<delta>" by auto
    hence "u x \<le> u y" 
    proof (cases "x \<le> 0")
      assume "x \<le> 0"
      with \<open>x \<le> \<delta>\<close> and \<open>0 < y \<and> y \<le> \<delta>\<close> show "u x \<le> u y"  unfolding u_def using ego.q_min by auto
    next
      assume "\<not> x \<le> 0"
      with \<open>0 < y \<and> y \<le> \<delta>\<close> and assms show "u x \<le> u y" 
        unfolding u_def  using ego.q_mono by auto
    qed }
  
  moreover
  { assume "\<delta> < y"
    have "u x \<le> u y"
    proof (cases "\<delta> < x")
      assume "\<delta> < x" 
      with pos_react have "\<not> x \<le> 0" by auto
      moreover from \<open>\<delta> < y\<close> and pos_react have "\<not> y \<le> 0" by auto
      ultimately show "u x \<le> u y"  unfolding u_def comp_def 
        using assms ego2.s_mono[of "x - \<delta>" "y - \<delta>"] \<open>\<delta> < y\<close> \<open>\<delta> < x\<close> by (auto simp:\<tau>_def)
    next
      assume "\<not> \<delta> < x"
      hence "x \<le> \<delta>" by simp
      hence "u x \<le> ego.q \<delta>" unfolding u_def using pos_react nonneg_vel_ego
        by (auto simp add:ego.q_def mult_left_mono)
      also have "... = ego2.s (\<tau> \<delta>)" unfolding ego2.s_def unfolding \<tau>_def by auto
      also have "... \<le> ego2.s (\<tau> y)" unfolding \<tau>_def using \<open>\<delta> < y\<close> by (auto simp add:ego2.s_mono)
      also have "... = u y" unfolding u_def using \<open>\<delta> < y\<close> pos_react by auto     
      ultimately show "u x \<le> u y" by auto
    qed }
  
  ultimately show "u x \<le> u y" by auto
qed

lemma u_antimono: "x \<le> y \<Longrightarrow> t_stop \<le> x \<Longrightarrow> u y \<le> u x"
proof -
  assume 1: "x \<le> y"
  assume 2: "t_stop \<le> x"
  hence "\<delta> \<le> x" unfolding \<tau>_def t_stop_def using pos_react ego2.t_stop_nonneg by auto
  with 1 have "\<delta> \<le> y" by auto
  from 1 and 2 have 3: "t_stop \<le> y" by auto
  show "u y \<le> u x"
  proof (cases "x \<noteq> \<delta> \<and> y \<noteq> \<delta>")
    assume "x \<noteq> \<delta> \<and> y \<noteq> \<delta>"
    hence "x \<noteq> \<delta>" and "y \<noteq> \<delta>" by auto
    have "u y \<le> (ego2.s \<circ> \<tau>) y" unfolding u_def using \<open>\<delta> \<le> y\<close> \<open>y \<noteq> \<delta>\<close> pos_react by auto
    also have "... \<le> (ego2.s \<circ> \<tau>) x" unfolding comp_def
    proof (intro ego2.s_antimono)
      show "\<tau> x \<le> \<tau> y" unfolding \<tau>_def using \<open>x \<le> y\<close> by auto
    next
      show "ego2.t_stop \<le> \<tau> x" unfolding \<tau>_def using \<open>t_stop \<le> x\<close> by (auto simp: t_stop_def)
    qed
    also have "... \<le> u x" unfolding u_def using \<open>\<delta> \<le> x\<close>\<open>x \<noteq> \<delta>\<close> pos_react by auto
    ultimately show "u y \<le> u x" by auto
  next
    assume "\<not> (x \<noteq> \<delta> \<and> y \<noteq> \<delta>)"
    have "x \<noteq> \<delta> \<longrightarrow> y \<noteq> \<delta>"
    proof (rule impI; erule contrapos_pp[where Q="\<not> x = \<delta>"])
      assume "\<not> y \<noteq> \<delta>"
      hence "y = \<delta>" by simp
      with \<open>t_stop \<le> y\<close> have "ego2.t_stop = 0" unfolding t_stop_def 
        using ego2.t_stop_nonneg by auto
      with \<open>t_stop \<le> x\<close> have "x = \<delta>" unfolding t_stop_def using \<open>x \<le> y\<close> \<open>y = \<delta>\<close> by auto
      thus "\<not> x \<noteq> \<delta>" by auto
    qed
    with \<open>\<not> (x \<noteq> \<delta> \<and> y \<noteq> \<delta>)\<close> have "(x = \<delta> \<and> y = \<delta>) \<or> (x = \<delta>)" by auto
    
    moreover
    { assume "x = \<delta> \<and> y = \<delta>"
      hence "x = \<delta>" and "y = \<delta>" by auto
      hence "u y \<le> ego.q \<delta>" unfolding u_def using pos_react by auto
      also have "... \<le> u x" unfolding u_def using \<open>x = \<delta>\<close> pos_react by auto
      ultimately have "u y \<le> u x" by auto }

    moreover
    { assume "x = \<delta>" 
      hence "ego2.t_stop = 0" using \<open>t_stop \<le> x\<close> ego2.t_stop_nonneg by (auto simp:t_stop_def)
      hence "v\<^sub>e = 0" by (rule ego2.t_stop_zero)
      hence "u y \<le> ego.q \<delta>"
        using pos_react \<open>x = \<delta>\<close> \<open>x \<le> y\<close> \<open>v\<^sub>e = 0\<close>
        unfolding u_def comp_def \<tau>_def ego2.s_def ego2.p_def ego2.p_max_def ego2.t_stop_def 
        by auto
      also have "... \<le> u x" using \<open>x = \<delta>\<close> pos_react unfolding u_def by auto       
      ultimately have "u y \<le> u x" by auto }

    ultimately show ?thesis by auto
  qed
qed

lemma u_max: "u x \<le> u_max" 
  unfolding u_max_def using t_stop_def        
  by (cases "x \<le> t_stop") (auto intro: u_mono u_antimono)

lemma u_eq_u_stop: "NO_MATCH t_stop x \<Longrightarrow> x \<ge> t_stop \<Longrightarrow> u x = u_max"
proof -
  assume "t_stop \<le> x"
  with t_stop_pos have "0 < x" by auto
  from \<open>t_stop \<le> x\<close> have "\<delta> \<le> x" unfolding t_stop_def using ego2.t_stop_nonneg by auto
  show  "u x = u_max"
  proof (cases "x \<le> \<delta>")
    assume "x \<le> \<delta>" 
    with \<open>t_stop \<le> x\<close> have "v\<^sub>e = 0" by (rule t_stop_zero)
    also have "x = \<delta>" using \<open>x \<le> \<delta>\<close> and \<open>\<delta> \<le> x\<close> by auto
    ultimately have "u x = ego.q \<delta>" unfolding u_def using pos_react by auto
    also have "... = u_max" unfolding u_max_eq using \<open>v\<^sub>e = 0\<close> by auto
    ultimately show "u x = u_max" by simp
  next
    assume "\<not> x \<le> \<delta>"
    hence "\<delta> < x" by auto
    hence "u x = (ego2.s \<circ> \<tau>) x" unfolding u_def using pos_react by auto
    also have "... = ego2.s ego2.t_stop" 
      proof (unfold comp_def; unfold \<tau>_def; intro order.antisym)
        have "x - \<delta> \<ge> ego2.t_stop" using \<open>t_stop \<le> x\<close> unfolding t_stop_def by auto
        thus "ego2.s (x - \<delta>) \<le> ego2.s ego2.t_stop" by (rule ego2.s_antimono) simp
      next
        have "x - \<delta> \<ge> ego2.t_stop" using \<open>t_stop \<le> x\<close> unfolding t_stop_def by auto
        thus "ego2.s ego2.t_stop \<le> ego2.s (x - \<delta>)" using ego2.t_stop_nonneg by (rule ego2.s_mono)
      qed
    also have "... = u_max" unfolding u_max_eq ego2.s_t_stop ego2.p_max_eq by auto
    ultimately show "u x = u_max" by auto
  qed
qed

lemma at_least_delta:
  assumes "x \<le> \<delta>"
  assumes "t_stop \<le> x"
  shows "ego.q x = ego2.s (x - \<delta>)"
  using assms ego2.t_stop_nonneg 
  unfolding t_stop_def ego2.s_def less_eq_real_def by auto

lemma continuous_on_u[continuous_intros]: "continuous_on T u"
  unfolding u_def[abs_def]
  using t_stop_nonneg pos_react at_least_delta
  proof (intro continuous_on_subset[where t=T and s = "{..0} \<union> ({0..\<delta>} \<union> ({\<delta> .. t_stop} \<union> {t_stop ..}))"] continuous_on_If continuous_intros)
    fix x
    assume " \<not> x \<le> \<delta>"
    assume "x \<in> {0..\<delta>}"
    hence "0 \<le> x" and "x \<le> \<delta>" by auto
    thus "ego.q x = (ego2.s \<circ> \<tau>) x" 
      unfolding comp_def \<tau>_def ego2.s_def 
      using \<open>\<not> x \<le> \<delta>\<close> by auto
  next
    fix x
    assume "x \<in> {\<delta>..t_stop} \<union> {t_stop..}"
    hence "\<delta> \<le> x" unfolding t_stop_def using pos_react ego.t_stop_nonneg by auto
    also assume "x \<le> \<delta>"
    ultimately have "x = \<delta>" by auto
    thus "ego.q x = (ego2.s \<circ> \<tau>) x" unfolding comp_def \<tau>_def ego2.s_def by auto
  next
    fix t::real
    assume "t \<in> {.. 0}"
    hence "t \<le> 0" by auto
    also assume "\<not> t \<le> 0"
    ultimately have "t = 0" by auto
    hence "s\<^sub>e = ego.q t" unfolding ego.q_def by auto
    with pos_react \<open>t = 0\<close> show "s\<^sub>e = (if t \<le> \<delta> then ego.q t else (ego2.s \<circ> \<tau>) t)" by auto
  next
    fix t::real
    assume "t \<in> {0..\<delta>} \<union> ({\<delta>..t_stop} \<union> {t_stop..})"
    hence "0 \<le> t" using pos_react ego2.t_stop_nonneg by (auto simp: t_stop_def)
    also assume "t \<le> 0"
    ultimately have "t = 0" by auto
    hence " s\<^sub>e = (if t \<le> \<delta> then ego.q t else (ego2.s \<circ> \<tau>) t)" using pos_react ego.init_q by auto
    thus "s\<^sub>e = (if t \<le> \<delta> then ego.q t else (ego2.s \<circ> \<tau>) t)" by auto
  next
    show "T \<subseteq> {..0} \<union> ({0..\<delta>} \<union> ({\<delta>..t_stop} \<union> {t_stop..}))" by auto  
  qed

lemma isCont_u[continuous_intros]: "isCont u x"
  using continuous_on_u[of UNIV]
  by (auto simp:continuous_on_eq_continuous_at)

definition collision_react :: "real set \<Rightarrow> bool" where
  "collision_react time_set \<equiv> (\<exists>t\<in>time_set. u t = other.s t )"

abbreviation no_collision_react :: "real set \<Rightarrow> bool" where
  "no_collision_react time_set \<equiv> \<not> collision_react time_set"

lemma no_collision_reactI:
  assumes "\<And>t. t \<in> S \<Longrightarrow> u t \<noteq> other.s t"
  shows "no_collision_react S"
  using assms
  unfolding collision_react_def
  by blast

lemma no_collision_union:
  assumes "no_collision_react S"
  assumes "no_collision_react T"
  shows "no_collision_react (S \<union> T)"
  using assms
  unfolding collision_react_def
  by auto

lemma collision_trim_subset:
  assumes "collision_react S"
  assumes "no_collision_react T"
  assumes "T \<subseteq> S"
  shows "collision_react (S - T)"
  using assms
  unfolding collision_react_def by auto

theorem cond_1r : "u_max < s\<^sub>o \<Longrightarrow> no_collision_react {0..}"
proof (rule no_collision_reactI, simp)
  fix t :: real
  assume "0 \<le> t"
  have "u t \<le> u_max" by (rule u_max)
  also assume "... < s\<^sub>o"
  also have "... = other.s 0"
    by (simp add: other.init_s)
  also have "... \<le> other.s t"
    using \<open>0 \<le> t\<close> hyps
    by (intro other.s_mono) auto
  finally show "u t \<noteq> other.s t"
    by simp
qed

definition safe_distance_1r :: real where 
  "safe_distance_1r = v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2"

lemma sd_1r_eq: "(s\<^sub>o - s\<^sub>e > safe_distance_1r) = (u_max < s\<^sub>o)"
proof -
  have "(s\<^sub>o - s\<^sub>e > safe_distance_1r) = (s\<^sub>o - s\<^sub>e > v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2)" unfolding safe_distance_1r_def by auto
  moreover have "... = (s\<^sub>e + v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2 < s\<^sub>o)" by auto
  ultimately show ?thesis using u_max_eq ego.q_def by auto
qed

lemma sd_1r_correct:
  assumes "s\<^sub>o - s\<^sub>e > safe_distance_1r"
  shows "no_collision_react {0..}"
proof -
  from assms have "u_max < s\<^sub>o" using sd_1r_eq by auto
  thus ?thesis by (rule cond_1r)
qed

lemma u_other_strict_ivt:
  assumes "u t > other.s t"
  shows "collision_react {0..<t}"
proof cases
  assume "0 \<le> t"
  with assms in_front
  have "\<exists>x\<ge>0. x \<le> t \<and> other.s x - u x = 0"
    by (intro IVT2) (auto simp: init_u other.init_s continuous_diff isCont_u other.isCont_s)
  then show ?thesis
    using assms
    by (auto simp add: algebra_simps collision_react_def Bex_def order.order_iff_strict)
qed(insert assms hyps, auto simp: collision_react_def init_u other.init_s)

lemma collision_react_subset: "collision_react s \<Longrightarrow> s \<subseteq> t \<Longrightarrow> collision_react t"
  by (auto simp:collision_react_def) 

lemma u_other_ivt:
  assumes "u t \<ge> other.s t"
  shows "collision_react {0 .. t}"
proof cases
  assume "u t > other.s t"
  from u_other_strict_ivt[OF this]
  show ?thesis
    by (rule collision_react_subset) auto
qed (insert hyps assms; cases "t \<ge> 0"; force simp: collision_react_def init_u other.init_s)

theorem cond_2r:
  assumes "u_max \<ge> other.s_stop"
  shows "collision_react {0 ..}"
  using assms
  apply(intro collision_react_subset[where t="{0..}" and s ="{0 .. max t_stop other.t_stop}"])
   apply(intro u_other_ivt[where t ="max t_stop other.t_stop"])
   apply(auto simp: u_eq_u_stop other.s_eq_s_stop)
  done

definition ego_other2 :: "real \<Rightarrow> real" where
  "ego_other2 t = other.s t - u t"

lemma continuous_on_ego_other2[continuous_intros]: "continuous_on T ego_other2"
  unfolding ego_other2_def[abs_def]
  by (intro continuous_intros)

lemma isCont_ego_other2[continuous_intros]: "isCont ego_other2 x"
  using continuous_on_ego_other2[of UNIV]
  by (auto simp: continuous_on_eq_continuous_at)

definition ego_other2' :: "real \<Rightarrow> real" where
  "ego_other2' t  = other.s' t - u' t"

lemma ego_other2_has_real_derivative[derivative_intros]: 
  assumes "0 \<le> t"
  shows "(ego_other2 has_real_derivative ego_other2' t) (at t within {0..})"
  using assms other.t_stop_nonneg decelerate_other
  unfolding other.t_stop_def
  by (auto simp: ego_other2_def[abs_def] ego_other2'_def  algebra_simps
           intro!: derivative_eq_intros)

theorem cond_3r_1:
  assumes "u \<delta> \<ge> other.s \<delta>"
  shows "collision_react {0 .. \<delta>}"
  proof (unfold collision_react_def) 
  have 1: "\<exists>t\<ge>0. t \<le> \<delta> \<and> ego_other2 t = 0"
    proof (intro IVT2)
      show "ego_other2 \<delta> \<le> 0" unfolding ego_other2_def using assms by auto
    next
      show "0 \<le> ego_other2 0" unfolding ego_other2_def 
        using other.init_s[of 0] init_u[of 0] in_front by auto
    next
      show "0 \<le> \<delta>" using pos_react by auto
    next
      show "\<forall>t. 0 \<le> t \<and> t \<le> \<delta> \<longrightarrow> isCont ego_other2 t" 
        using isCont_ego_other2 by auto
    qed
    then obtain t where "0 \<le> t \<and> t \<le> \<delta> \<and> ego_other2 t = 0" by auto
    hence "t \<in> {0 .. \<delta>}" and "u t = other.s t" unfolding ego_other2_def by auto
    thus "\<exists>t\<in>{0..\<delta>}. u t = other.s t" by (intro bexI)    
  qed

definition distance0 :: real where 
  "distance0 =  v\<^sub>e * \<delta> - v\<^sub>o * \<delta> - a\<^sub>o * \<delta>\<^sup>2 / 2"

definition distance0_2 :: real where 
  "distance0_2 = v\<^sub>e * \<delta> + 1 / 2 * v\<^sub>o\<^sup>2 / a\<^sub>o"

theorem cond_3r_1':
  assumes "s\<^sub>o - s\<^sub>e \<le> distance0"
  assumes "\<delta> \<le> other.t_stop"
  shows "collision_react {0 .. \<delta>}"
proof -
  from assms have "u \<delta> \<ge> other.s \<delta>" unfolding distance0_def other.s_def
    other.p_def u_def ego.q_def using pos_react by auto
  thus ?thesis using cond_3r_1 by auto
qed

theorem distance0_2_eq:
  assumes "\<delta> > other.t_stop"
  shows "(u \<delta> < other.s \<delta>) = (s\<^sub>o - s\<^sub>e > distance0_2)"
proof -
  from assms have "(u \<delta> < other.s \<delta>) = (ego.q \<delta> < other.p_max)"
    using u_def other.s_def pos_react by auto
  also have "... = (s\<^sub>e + v\<^sub>e * \<delta> < s\<^sub>o + v\<^sub>o * (- v\<^sub>o / a\<^sub>o) + 1 / 2 * a\<^sub>o * (- v\<^sub>o / a\<^sub>o)\<^sup>2)"
    using ego.q_def other.p_max_def other.p_def other.t_stop_def by auto
  also have "... = (v\<^sub>e * \<delta> - v\<^sub>o * (- v\<^sub>o / a\<^sub>o) - 1 / 2 * a\<^sub>o * (- v\<^sub>o / a\<^sub>o)\<^sup>2 < s\<^sub>o - s\<^sub>e)" by linarith
  also have "... = (v\<^sub>e * \<delta> + v\<^sub>o\<^sup>2 / a\<^sub>o - 1 / 2 * v\<^sub>o\<^sup>2 / a\<^sub>o < s\<^sub>o - s\<^sub>e)"
    using other.p_def other.p_max_def other.p_max_eq other.t_stop_def by auto
  also have "... = (v\<^sub>e * \<delta> + 1 / 2 * v\<^sub>o\<^sup>2 / a\<^sub>o < s\<^sub>o - s\<^sub>e)" by linarith
  thus ?thesis using distance0_2_def by (simp add: calculation)
qed

theorem cond_3r_1'_2:
  assumes "s\<^sub>o - s\<^sub>e \<le> distance0_2"
  assumes "\<delta> > other.t_stop"
  shows "collision_react {0 .. \<delta>}"
proof -
  from assms distance0_2_eq have "u \<delta> \<ge> other.s \<delta>" unfolding distance0_def other.s_def
    other.p_def u_def ego.q_def using pos_react by auto
  thus ?thesis using cond_3r_1 by auto
qed

definition safe_distance_3r :: real where
  "safe_distance_3r = v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e - v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2"

lemma distance0_at_most_sd3r:
  "distance0 \<le> safe_distance_3r"
  unfolding distance0_def safe_distance_3r_def using nonneg_vel_ego decelerate_ego
  by (auto simp add:field_simps)

definition safe_distance_4r :: real where 
  "safe_distance_4r = (v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) - v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2 + v\<^sub>e * \<delta>"

lemma distance0_at_most_sd4r:
  assumes "a\<^sub>o > a\<^sub>e"
  shows "distance0 \<le> safe_distance_4r"
proof -
  from assms have "a\<^sub>o \<ge> a\<^sub>e" by auto
  have "0 \<le> (v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / (2 * a\<^sub>o - 2 * a\<^sub>e)"
    by (rule divide_nonneg_nonneg) (auto simp add:assms \<open>a\<^sub>e \<le> a\<^sub>o\<close>)
  thus ?thesis unfolding distance0_def safe_distance_4r_def
    by auto
qed

definition safe_distance_2r :: real where 
  "safe_distance_2r = v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o"

lemma vo_start_geq_ve:
  assumes "\<delta> \<le> other.t_stop"
  assumes "other.s' \<delta> \<ge> v\<^sub>e"
  shows "u \<delta> < other.s \<delta>"
proof -
    from assms have "v\<^sub>e \<le> v\<^sub>o + a\<^sub>o * \<delta>" unfolding other.s'_def other.p'_def by auto
    with  mult_right_mono[OF this, of "\<delta>"] have "v\<^sub>e * \<delta> \<le> v\<^sub>o * \<delta> + a\<^sub>o * \<delta>\<^sup>2" (is "?l0 \<le> ?r0")
      using pos_react by (auto simp add:field_simps power_def)
    hence "s\<^sub>e + ?l0 \<le> s\<^sub>e + ?r0" by auto
    also have "... < s\<^sub>o + ?r0" using in_front by auto
    also have "... < s\<^sub>o + v\<^sub>o * \<delta> + a\<^sub>o * \<delta>\<^sup>2 / 2" using decelerate_other pos_react by auto
    finally show ?thesis using pos_react assms(1)
      unfolding u_def ego.q_def other.s_def other.t_stop_def other.p_def by auto
qed

theorem so_star_stop_leq_se_stop:
  assumes "\<delta> \<le> other.t_stop"
  assumes "other.s' \<delta> < v\<^sub>e"
  assumes "\<not> (a\<^sub>o > a\<^sub>e \<and> other.s' \<delta> < v\<^sub>e \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> < 0)"
  shows "0 \<le> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2 + (v\<^sub>o + a\<^sub>o * \<delta>)\<^sup>2 / a\<^sub>o / 2"
proof -
  consider "v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> \<ge> 0" | "\<not> (v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> \<ge> 0)" by auto
  thus ?thesis
  proof (cases)
    case 1
    hence "v\<^sub>e - a\<^sub>e / a\<^sub>o * (v\<^sub>o + a\<^sub>o * \<delta>) \<ge> 0" unfolding other.s'_def other.p'_def
      by (auto simp add:assms(1))
    hence "v\<^sub>e - a\<^sub>e / a\<^sub>o * v\<^sub>o - a\<^sub>e * \<delta> \<ge> 0" (is "?l0 \<ge> 0") using decelerate_other
      by (auto simp add:field_simps)
    hence "?l0 / a\<^sub>e \<le> 0" using divide_right_mono_neg[OF \<open>?l0 \<ge> 0\<close>] decelerate_ego by auto
    hence "0 \<ge> v\<^sub>e / a\<^sub>e - v\<^sub>o / a\<^sub>o - \<delta>" using decelerate_ego by (auto simp add:field_simps)
    hence *: "- v\<^sub>e / a\<^sub>e \<ge> - (v\<^sub>o + a\<^sub>o * \<delta>) / a\<^sub>o" using decelerate_other by (auto simp add:field_simps)
    from assms have **: "v\<^sub>o + a\<^sub>o * \<delta> \<le> v\<^sub>e" unfolding other.s'_def other.p'_def by auto
    have vo_star_nneg: "v\<^sub>o + a\<^sub>o * \<delta> \<ge> 0"
    proof -
      from assms(1) have "- v\<^sub>o \<le> a\<^sub>o * \<delta>" unfolding other.t_stop_def using decelerate_other
        by (auto simp add:field_simps)
      thus ?thesis by auto
    qed
    from mult_mono[OF * ** _ \<open>0 \<le> v\<^sub>o + a\<^sub>o * \<delta>\<close>]
    have "- (v\<^sub>o + a\<^sub>o * \<delta>) / a\<^sub>o * (v\<^sub>o + a\<^sub>o * \<delta>) \<le> - v\<^sub>e / a\<^sub>e * v\<^sub>e" using nonneg_vel_ego decelerate_ego
      by (auto simp add:field_simps)
    hence "- (v\<^sub>o + a\<^sub>o * \<delta>)\<^sup>2 / a\<^sub>o \<le> - v\<^sub>e\<^sup>2 / a\<^sub>e " by (auto simp add: field_simps power_def)
    thus ?thesis by (auto simp add:field_simps)
  next
    case 2
    with assms have "a\<^sub>o \<le> a\<^sub>e" by auto
    from assms(2) have "(v\<^sub>o + a\<^sub>o * \<delta>) \<le> v\<^sub>e" unfolding other.s'_def using assms unfolding other.p'_def
      by auto
    have vo_star_nneg: "v\<^sub>o + a\<^sub>o * \<delta> \<ge> 0"
    proof -
      from assms(1) have "- v\<^sub>o \<le> a\<^sub>o * \<delta>" unfolding other.t_stop_def using decelerate_other
        by (auto simp add:field_simps)
      thus ?thesis by auto
    qed
    with mult_mono[OF \<open>v\<^sub>o + a\<^sub>o * \<delta> \<le> v\<^sub>e\<close> \<open>v\<^sub>o + a\<^sub>o * \<delta> \<le> v\<^sub>e\<close>] have *: "(v\<^sub>o + a\<^sub>o * \<delta>)\<^sup>2 \<le> v\<^sub>e\<^sup>2"
      using nonneg_vel_ego by (auto simp add:power_def)
    from \<open>a\<^sub>o \<le> a\<^sub>e\<close> have "- 1 /a\<^sub>o \<le> - 1 / a\<^sub>e" using decelerate_ego decelerate_other
      by (auto simp add:field_simps)
    from mult_mono[OF * this] have "(v\<^sub>o + a\<^sub>o * \<delta>)\<^sup>2 * (- 1 / a\<^sub>o) \<le> v\<^sub>e\<^sup>2 * (- 1 / a\<^sub>e)"
      using nonneg_vel_ego decelerate_other by (auto simp add:field_simps)
    then show ?thesis by auto
  qed
qed

theorem distance0_at_most_distance2r:
  assumes "\<delta> \<le> other.t_stop"
  assumes "other.s' \<delta> < v\<^sub>e"
  assumes "\<not> (a\<^sub>o > a\<^sub>e \<and> other.s' \<delta> < v\<^sub>e \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> < 0)"
  shows "distance0 \<le> safe_distance_2r"
proof -
  from so_star_stop_leq_se_stop[OF assms] have " 0 \<le> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2 + (v\<^sub>o + a\<^sub>o * \<delta>)\<^sup>2 / a\<^sub>o / 2 " (is "0 \<le> ?term")
    by auto
  have "safe_distance_2r = v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o" unfolding safe_distance_2r_def by auto
  also have "... = v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + (v\<^sub>o + a\<^sub>o * \<delta>)\<^sup>2 / 2 / a\<^sub>o - v\<^sub>o * \<delta> - a\<^sub>o * \<delta>\<^sup>2 / 2"
    using decelerate_other by (auto simp add:field_simps power_def)
  also have "... = v\<^sub>e * \<delta> - v\<^sub>o * \<delta> - a\<^sub>o * \<delta>\<^sup>2 / 2 + ?term" (is "_ = ?left + ?term")
    by (auto simp add:field_simps)
  finally have "safe_distance_2r = distance0 + ?term" unfolding distance0_def by auto
  with \<open>0 \<le> ?term\<close> show "distance0 \<le> safe_distance_2r" by auto
qed

theorem dist0_sd2r_1:
  assumes "\<delta> \<le> other.t_stop"
  assumes "\<not> (a\<^sub>o > a\<^sub>e \<and> other.s' \<delta> < v\<^sub>e \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> < 0)"
  assumes "s\<^sub>o - s\<^sub>e > safe_distance_2r"
  shows "s\<^sub>o - s\<^sub>e > distance0"
proof (cases "other.s' \<delta> \<ge> v\<^sub>e")
  assume "v\<^sub>e \<le> other.s' \<delta>"
  from vo_start_geq_ve[OF assms(1) this] have "u \<delta> < other.s \<delta>" by auto
  thus ?thesis unfolding distance0_def u_def using pos_react assms(1) unfolding ego.q_def
    other.s_def other.p_def by auto
next
  assume "\<not> v\<^sub>e \<le> other.s' \<delta>"
  hence "v\<^sub>e > other.s' \<delta>" by auto
  from distance0_at_most_distance2r[OF assms(1) this assms(2)] have "distance0 \<le> safe_distance_2r"
    by auto
  with assms(3) show ?thesis by auto
qed

theorem sd2r_eq:
  assumes "\<delta> > other.t_stop"
  shows "(u_max < other.s \<delta>) = (s\<^sub>o - s\<^sub>e > safe_distance_2r)"
proof -
  from assms have "(u_max < other.s \<delta>) = (ego2.s (- v\<^sub>e / a\<^sub>e) < other.p_max)"
    using u_max_def ego2.t_stop_def u_def other.s_def \<tau>_def pos_react ego2.p_max_eq ego2.s_t_stop u_max_eq by auto
  also have "... = (s\<^sub>e + v\<^sub>e * \<delta> + v\<^sub>e * (- v\<^sub>e / a\<^sub>e) + 1 / 2 * a\<^sub>e * (- v\<^sub>e / a\<^sub>e)\<^sup>2 < s\<^sub>o + v\<^sub>o * (- v\<^sub>o / a\<^sub>o) + 1 / 2 * a\<^sub>o * (- v\<^sub>o / a\<^sub>o)\<^sup>2)"
    using ego2.s_def ego2.p_def ego.q_def other.p_max_def other.p_def other.t_stop_def ego2.p_max_def ego2.s_t_stop ego2.t_stop_def by auto
  also have "... = (v\<^sub>e * \<delta> + v\<^sub>e * (- v\<^sub>e / a\<^sub>e) + 1 / 2 * a\<^sub>e * (- v\<^sub>e / a\<^sub>e)\<^sup>2 - v\<^sub>o * (- v\<^sub>o / a\<^sub>o) - 1 / 2 * a\<^sub>o * (- v\<^sub>o / a\<^sub>o)\<^sup>2 < s\<^sub>o  - s\<^sub>e)" by linarith
  also have "... = (v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / a\<^sub>e + 1 / 2 * v\<^sub>e\<^sup>2 / a\<^sub>e + v\<^sub>o\<^sup>2 / a\<^sub>o - 1 / 2 * v\<^sub>o\<^sup>2 / a\<^sub>o < s\<^sub>o  - s\<^sub>e)"
    using ego2.p_def ego2.p_max_def ego2.p_max_eq ego2.t_stop_def other.p_def other.p_max_def other.p_max_eq other.t_stop_def by auto
  also have "... = (v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o  < s\<^sub>o - s\<^sub>e)" by linarith
  thus ?thesis using distance0_2_def by (simp add: calculation safe_distance_2r_def)
qed

theorem dist0_sd2r_2:
  assumes "\<delta> > - v\<^sub>o / a\<^sub>o"
  assumes "s\<^sub>o - s\<^sub>e > safe_distance_2r"
  shows "s\<^sub>o - s\<^sub>e > distance0_2"
proof -
  have "- v\<^sub>e\<^sup>2 / 2 / a\<^sub>e \<ge> 0" using zero_le_power2 hyps(3) divide_nonneg_neg by (auto simp add:field_simps)
  hence "v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o \<ge> v\<^sub>e * \<delta> + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o" by simp
  hence "safe_distance_2r \<ge> distance0_2" using safe_distance_2r_def distance0_2_def by auto
  thus ?thesis using assms(2) by linarith
qed
end

subsection \<open>Safe Distance Delta\<close>

locale safe_distance_no_collsion_delta = safe_distance_normal +
  assumes no_collision_delta: "u \<delta> < other.s \<delta>"
begin

sublocale delayed_safe_distance: safe_distance a\<^sub>e v\<^sub>e "ego.q \<delta>" a\<^sub>o "other.s' \<delta>" "other.s \<delta>"
  proof (unfold_locales)
    from nonneg_vel_ego show "0 \<le> v\<^sub>e" by auto
  next
    from nonneg_vel_other show "0 \<le> other.s' \<delta>" unfolding other.s'_def other.p'_def other.t_stop_def
      using decelerate_other by (auto simp add: field_split_simps)
  next
    from decelerate_ego show "a\<^sub>e < 0" by auto
  next
    from decelerate_other show "a\<^sub>o < 0" by auto
  next
    from no_collision_delta show "ego.q \<delta> < other.s \<delta>" unfolding u_def using pos_react by auto
  qed

lemma no_collision_react_initially_strict:
  assumes "s\<^sub>o \<le> u_max"
  assumes "u_max < other.s_stop"
  shows "no_collision_react {0 <..< \<delta>}"
proof (rule no_collision_reactI)
  fix t::real
  assume "t \<in> {0 <..< \<delta>}" 
  show "u t \<noteq> other.s t"
  proof (rule ccontr)
    assume "\<not> u t \<noteq> other.s t"
    hence "ego_other2 t = 0" unfolding ego_other2_def by auto
    from \<open>t \<in> {0 <..< \<delta>}\<close> have "ego_other2 t = other.s t - ego.q t" 
      unfolding ego_other2_def u_def using ego.init_q by auto
    have "\<delta> \<le> other.t_stop \<or> other.t_stop < \<delta>" by auto
    
    moreover
    { assume le_t_stop: "\<delta> \<le> other.t_stop"
      with \<open>ego_other2 t = other.s t - ego.q t\<close> have "ego_other2 t = other.p t - ego.q t"
        unfolding other.s_def using \<open>t \<in> {0 <..< \<delta>}\<close> by auto
      with \<open>ego_other2 t = 0\<close> have "other.p t - ego.q t = 0" by auto
      hence eq: "(s\<^sub>o- s\<^sub>e) + (v\<^sub>o - v\<^sub>e) * t + (1/2 * a\<^sub>o) * t\<^sup>2 = 0"
        unfolding other.p_def ego.q_def by (auto simp: algebra_simps)
      define p where "p \<equiv> \<lambda>x. (1/2 * a\<^sub>o) * x\<^sup>2 + (v\<^sub>o - v\<^sub>e) * x + (s\<^sub>o - s\<^sub>e)"
      have "0 < 1/2 * a\<^sub>o"
      proof (intro p_convex[where p=p and b="v\<^sub>o - v\<^sub>e" and c="s\<^sub>o - s\<^sub>e"])
          show "0 < t" using \<open>t \<in> {0 <..< \<delta>}\<close> by auto
        next
          show "t < \<delta>" using  \<open>t \<in> {0 <..< \<delta>}\<close> by auto
        next
          show "p t < p 0" unfolding p_def using eq in_front by (auto simp: algebra_simps)
        next
          from eq have "p t = 0" unfolding p_def by auto
          also have "... < p \<delta>"  using no_collision_delta pos_react le_t_stop             
            unfolding p_def u_def other.s_def ego.q_def other.p_def by (auto simp:algebra_simps)
          finally have "p t < p \<delta>" by simp
          thus "p t \<le> p \<delta>" by auto
        next
          show "p = (\<lambda>x. 1 / 2 * a\<^sub>o * x\<^sup>2 + (v\<^sub>o - v\<^sub>e) * x + (s\<^sub>o - s\<^sub>e))" unfolding p_def
          by (rule refl)
      qed
      hence "0 < a\<^sub>o" by auto
      with decelerate_other have False by simp }

    moreover
    { assume gt_t_stop: "\<delta> > other.t_stop"
      have t_lt_t_stop: "t < other.t_stop"
      proof (rule ccontr)
        assume "\<not> t < other.t_stop"
        hence "other.t_stop \<le> t" by simp
        from \<open>ego_other2 t = 0\<close> have "ego.q t = other.p_max"
          unfolding ego_other2_def u_def other.s_def comp_def \<tau>_def other.p_max_def
          using \<open>t \<in> {0 <..< \<delta>}\<close> \<open>other.t_stop \<le> t\<close> gt_t_stop by (auto split:if_splits)
        have "ego.q t = u t" unfolding u_def using \<open>t \<in> {0 <..< \<delta>}\<close> by auto
        also have "... \<le> u_max" using u_max by auto
        also have "... < other.p_max" using assms(2) other.s_t_stop by auto
        finally have "ego.q t < other.p_max" by auto
        with \<open>ego.q t = other.p_max\<close> show False by auto  
      qed
      
      with \<open>ego_other2 t = other.s t - ego.q t\<close> have "ego_other2 t = other.p t - ego.q t"
        unfolding other.s_def using \<open>t \<in> {0 <..< \<delta>}\<close> by auto
      with \<open>ego_other2 t = 0\<close> have "other.p t - ego.q t = 0" by auto
      hence eq: "(s\<^sub>o- s\<^sub>e) + (v\<^sub>o - v\<^sub>e) * t + (1/2 * a\<^sub>o) * t\<^sup>2 = 0"
        unfolding other.p_def ego.q_def by (auto simp: algebra_simps)
      define p where "p \<equiv> \<lambda>x. (1/2 * a\<^sub>o) * x\<^sup>2 + (v\<^sub>o - v\<^sub>e) * x + (s\<^sub>o - s\<^sub>e)"
      have "0 < 1/2 * a\<^sub>o"
      proof (intro p_convex[where p=p and b="v\<^sub>o - v\<^sub>e" and c="s\<^sub>o - s\<^sub>e"])
          show "0 < t" using \<open>t \<in> {0 <..< \<delta>}\<close> by auto
        next
          show "t < other.t_stop" using t_lt_t_stop by auto
        next
          show "p t < p 0" unfolding p_def using eq in_front by (auto simp: algebra_simps)
        next
          from eq have zero: "p t = 0" unfolding p_def by auto
          have eq: "p other.t_stop = ego_other2 other.t_stop" 
            unfolding ego_other2_def other.s_t_stop u_def ego.q_def 
                      other.s_def other.p_def p_def
            using \<open>\<delta> > other.t_stop\<close> other.t_stop_nonneg other.t_stop_def
            by (auto simp: diff_divide_distrib left_diff_distrib')
          have "u other.t_stop \<le> u_max" using u_max by auto
          also have "... < other.s_stop" using assms by auto
          finally have "0 \<le> other.s_stop - u other.t_stop" by auto
          hence "0 \<le> ego_other2 other.t_stop" unfolding ego_other2_def by auto
          hence "0 \<le> p other.t_stop" using eq by auto
          with zero show "p t \<le> p other.t_stop" by auto
        next
          show "p = (\<lambda>x. 1 / 2 * a\<^sub>o * x\<^sup>2 + (v\<^sub>o - v\<^sub>e) * x + (s\<^sub>o - s\<^sub>e))"
          unfolding p_def by (rule refl)
      qed 
      hence False using decelerate_other by auto }

     ultimately show False by auto
  qed
qed

lemma no_collision_react_initially:
  assumes "s\<^sub>o \<le> u_max"
  assumes "u_max < other.s_stop"
  shows "no_collision_react {0 .. \<delta>}"
proof -
  have "no_collision_react {0 <..< \<delta>}" by (rule no_collision_react_initially_strict[OF assms])
  have "u 0 \<noteq> other.s 0" using init_u other.init_s in_front by auto
  hence "no_collision_react {0}" unfolding collision_react_def by auto
  with \<open>no_collision_react {0 <..< \<delta>}\<close> have "no_collision_react ({0} \<union> {0 <..< \<delta>})"
    using no_collision_union[of "{0}" "{0 <..< \<delta>}"] by auto
  moreover have "{0} \<union> {0 <..< \<delta>} = {0 ..< \<delta>}" using pos_react by auto
  ultimately have "no_collision_react {0 ..< \<delta>}" by auto

  have "u \<delta> \<noteq> other.s \<delta>" using no_collision_delta by auto
  hence "no_collision_react {\<delta>}" unfolding collision_react_def by auto
  with \<open>no_collision_react {0 ..< \<delta>}\<close> have "no_collision_react ({\<delta>} \<union> {0 ..< \<delta>})"
    using no_collision_union[of "{\<delta>}" "{0 ..< \<delta>}"] by auto
  moreover have "{\<delta>} \<union> {0 ..< \<delta>} = {0 .. \<delta>}" using pos_react by auto
  ultimately show "no_collision_react {0 .. \<delta>}" by auto
qed

lemma collision_after_delta:
  assumes "s\<^sub>o \<le> u_max"
  assumes "u_max < other.s_stop"
  shows "collision_react {0 ..} \<longleftrightarrow> collision_react {\<delta>..}" 
proof
  assume "collision_react {0 ..}"
  have "no_collision_react {0 .. \<delta>}" by (rule no_collision_react_initially[OF assms])
  with \<open>collision_react {0..}\<close> have "collision_react ({0..} - {0 .. \<delta>})"
  using pos_react by (auto intro: collision_trim_subset)
  
  moreover have "{0..} - {0 .. \<delta>} = {\<delta> <..}" using pos_react by auto
  ultimately have "collision_react {\<delta> <..}" by auto
  thus "collision_react {\<delta> ..}" by (auto intro:collision_react_subset)
next
  assume "collision_react {\<delta>..}"
  moreover have "{\<delta>..} \<subseteq> {0 ..}" using pos_react by auto
  ultimately show "collision_react {0 ..}" by (rule collision_react_subset)
qed

lemma collision_react_strict:
  assumes "s\<^sub>o \<le> u_max"
  assumes "u_max < other.s_stop"
  shows "collision_react {\<delta> ..} \<longleftrightarrow> collision_react {\<delta> <..}"
proof
  assume asm: "collision_react {\<delta> ..}"
  have "no_collision_react {\<delta>}" using no_collision_delta unfolding collision_react_def by auto
  moreover have "{\<delta> <..} \<subseteq> {\<delta> ..}" by auto
  ultimately have "collision_react ({\<delta> ..} - {\<delta>})" using asm collision_trim_subset by simp
  moreover have "{\<delta> <..} = {\<delta> ..} - {\<delta>}" by auto
  ultimately show "collision_react {\<delta> <..}" by auto
next
  assume "collision_react {\<delta> <..}"
  thus "collision_react {\<delta> ..}" 
    using collision_react_subset[where t="{\<delta> ..}" and s="{\<delta> <..}"] by fastforce
qed

lemma delayed_other_s_stop_eq: "delayed_safe_distance.other.s_stop = other.s_stop"
proof (unfold other.s_t_stop; unfold delayed_safe_distance.other.s_t_stop; unfold movement.p_max_eq)
  have "\<delta> \<le> other.t_stop \<or> other.t_stop < \<delta>" by auto

  moreover
  { assume "\<delta> \<le> other.t_stop"
    hence "other.s \<delta> - (other.s' \<delta>)\<^sup>2 / a\<^sub>o / 2 = s\<^sub>o - v\<^sub>o\<^sup>2 / a\<^sub>o / 2"
    unfolding other.s_def other.s'_def
    using  pos_react decelerate_other
    by (auto simp add: other.p_def other.p'_def power2_eq_square field_split_simps) }

  moreover
  { assume "other.t_stop < \<delta>"
    hence "other.s \<delta> - (other.s' \<delta>)\<^sup>2 / a\<^sub>o / 2 = s\<^sub>o - v\<^sub>o\<^sup>2 / a\<^sub>o / 2"
    unfolding other.s_def other.s'_def other.p_max_eq
    using pos_react decelerate_other 
    by (auto) }

  ultimately show "other.s \<delta> - (other.s' \<delta>)\<^sup>2 / a\<^sub>o / 2 = s\<^sub>o - v\<^sub>o\<^sup>2 / a\<^sub>o / 2" by auto
qed

lemma delayed_cond3':
  assumes "other.s \<delta> \<le> u_max" 
  assumes "u_max < other.s_stop"
  shows "delayed_safe_distance.collision {0 ..} \<longleftrightarrow>  
          (a\<^sub>o > a\<^sub>e \<and> other.s' \<delta> < v\<^sub>e \<and> other.s \<delta> - ego.q \<delta> \<le> delayed_safe_distance.snd_safe_distance \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> < 0)"
  proof (rule delayed_safe_distance.cond_3')
    have "other.s \<delta> \<le> u_max" using \<open>other.s \<delta> \<le> u_max\<close> . 
    also have "... = ego2.s_stop" unfolding u_max_eq ego2.s_t_stop ego2.p_max_eq by (rule refl)
    finally show "other.s \<delta> \<le> ego2.s_stop" by auto
  next
    have "ego2.s_stop = u_max" unfolding ego2.s_t_stop ego2.p_max_eq u_max_eq by (rule refl)
    also have "... < other.s_stop" using assms by auto
    also have "... \<le> delayed_safe_distance.other.s_stop" using delayed_other_s_stop_eq by auto
    finally show "ego2.s_stop < delayed_safe_distance.other.s_stop" by auto
  qed

lemma delayed_other_t_stop_eq:
  assumes "\<delta> \<le> other.t_stop"
  shows "delayed_safe_distance.other.t_stop + \<delta> = other.t_stop"
  using assms decelerate_other
  unfolding delayed_safe_distance.other.t_stop_def other.t_stop_def other.s'_def
            movement.t_stop_def other.p'_def
  by (auto simp add: field_split_simps)

lemma delayed_other_s_eq:
  assumes "0 \<le> t"
  shows "delayed_safe_distance.other.s t = other.s (t + \<delta>)"
proof (cases "\<delta> \<le> other.t_stop")
  assume 1: "\<delta> \<le> other.t_stop"
  have "t + \<delta> \<le> other.t_stop \<or> other.t_stop < t + \<delta>" by auto
  moreover
  { assume "t + \<delta> \<le> other.t_stop"
    hence "delayed_safe_distance.other.s t = delayed_safe_distance.other.p t"    
      using delayed_other_t_stop_eq [OF 1] assms
      unfolding delayed_safe_distance.other.s_def by auto 
    
    also have "... = other.p (t + \<delta>)" 
      unfolding movement.p_def other.s_def other.s'_def other.p'_def
      using pos_react 1 
      by (auto simp add: power2_eq_square field_split_simps)
      
    also have "... = other.s (t + \<delta>)"
      unfolding other.s_def 
      using assms pos_react \<open>t + \<delta> \<le> other.t_stop\<close> by auto

    finally have "delayed_safe_distance.other.s t = other.s (t + \<delta>)" by auto }

  moreover
  { assume "other.t_stop < t + \<delta>"
    hence "delayed_safe_distance.other.s t = delayed_safe_distance.other.p_max"
      using delayed_other_t_stop_eq [OF 1] assms delayed_safe_distance.other.t_stop_nonneg
      unfolding delayed_safe_distance.other.s_def by auto
    
    also have "... = other.p_max" 
      unfolding movement.p_max_eq other.s_def other.s'_def other.p_def other.p'_def
      using pos_react 1 decelerate_other 
      by (auto simp add: power2_eq_square field_split_simps)

    also have "... = other.s (t + \<delta>)"
      unfolding other.s_def
      using assms pos_react \<open>other.t_stop < t + \<delta>\<close> by auto

    finally have "delayed_safe_distance.other.s t = other.s (t + \<delta>)" by auto }

  ultimately show ?thesis by auto
next
  assume "\<not> \<delta> \<le> other.t_stop"
  hence "other.t_stop < \<delta>" by auto
  hence "other.s' \<delta> = 0" and "other.s \<delta> = other.p_max" 
    unfolding other.s'_def other.s_def using pos_react by auto
  hence "delayed_safe_distance.other.s t = delayed_safe_distance.other.p_max"
    unfolding delayed_safe_distance.other.s_def using assms decelerate_other 
    by (auto simp add:movement.p_max_eq movement.p_def movement.t_stop_def)
  also have "... = other.p_max" 
    unfolding movement.p_max_eq using \<open>other.s' \<delta> = 0\<close> \<open>other.s \<delta> = other.p_max\<close>
    using other.p_max_eq by auto
  also have "... = other.s (t + \<delta>)" 
    unfolding other.s_def using pos_react assms \<open>other.t_stop < \<delta>\<close> by auto
  finally show "delayed_safe_distance.other.s t = other.s (t + \<delta>)" by auto
qed

lemma translate_collision_range:
  assumes "s\<^sub>o \<le> u_max"
  assumes "u_max < other.s_stop"
  shows "delayed_safe_distance.collision {0 ..} \<longleftrightarrow> collision_react {\<delta> ..}"
proof 
  assume "delayed_safe_distance.collision {0 ..}" 
  then obtain t where eq: "ego2.s t = delayed_safe_distance.other.s t" and "0 \<le> t"
    unfolding delayed_safe_distance.collision_def by auto

  have "ego2.s t = (ego2.s \<circ> \<tau>) (t + \<delta>)" unfolding comp_def \<tau>_def by auto
  also have "... = u (t + \<delta>)" unfolding u_def using \<open>0 \<le> t\<close> pos_react 
    by (auto simp: \<tau>_def ego2.init_s)
  finally have left:"ego2.s t = u (t + \<delta>)" by auto

  have right: "delayed_safe_distance.other.s t = other.s (t + \<delta>)"
    using delayed_other_s_eq pos_react \<open>0 \<le> t\<close> by auto

  with eq and left have "u (t + \<delta>) = other.s (t + \<delta>)" by auto
  moreover have "\<delta> \<le> t + \<delta>" using \<open>0 \<le> t\<close> by auto
  ultimately show "collision_react {\<delta> ..}" unfolding collision_react_def by auto
next
  assume "collision_react {\<delta> ..}"
  hence "collision_react {\<delta> <..}" using collision_react_strict[OF assms] by simp
  then obtain t where eq: "u t = other.s t" and "\<delta> < t"
    unfolding collision_react_def by auto
  moreover hence "u t = (ego2.s \<circ> \<tau>) t" unfolding u_def using pos_react by auto
  moreover have "other.s t = delayed_safe_distance.other.s (t - \<delta>)"
    using delayed_other_s_eq \<open>\<delta> < t\<close> by auto
  ultimately have "ego2.s (t - \<delta>) = delayed_safe_distance.other.s (t - \<delta>)"
    unfolding comp_def \<tau>_def by auto
  with \<open>\<delta> < t\<close> show "delayed_safe_distance.collision {0 ..}" 
    unfolding delayed_safe_distance.collision_def by auto
qed

theorem cond_3r_2:
  assumes "s\<^sub>o \<le> u_max"
  assumes "u_max < other.s_stop"
  assumes "other.s \<delta> \<le> u_max"
  shows "collision_react {0 ..} \<longleftrightarrow> 
         (a\<^sub>o > a\<^sub>e \<and> other.s' \<delta> < v\<^sub>e \<and> other.s \<delta> -  ego.q \<delta> \<le> delayed_safe_distance.snd_safe_distance \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> < 0)"
proof -
  have "collision_react {0 ..} \<longleftrightarrow> collision_react {\<delta> ..}" by (rule collision_after_delta[OF assms(1) assms(2)])
  also have "... \<longleftrightarrow> delayed_safe_distance.collision {0 ..}" by (simp add: translate_collision_range[OF assms(1) assms(2)])
  also have "... \<longleftrightarrow>  (a\<^sub>o > a\<^sub>e \<and> other.s' \<delta> < v\<^sub>e \<and> other.s \<delta> -  ego.q \<delta> \<le> delayed_safe_distance.snd_safe_distance \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> < 0)"
    by (rule delayed_cond3'[OF assms(3) assms(2)])
  finally show "collision_react {0 ..} \<longleftrightarrow>  (a\<^sub>o > a\<^sub>e \<and> other.s' \<delta> < v\<^sub>e \<and> other.s \<delta> -  ego.q \<delta> \<le> delayed_safe_distance.snd_safe_distance \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> < 0)"
    by auto
qed

lemma sd_2r_correct_for_3r_2:
  assumes "s\<^sub>o - s\<^sub>e > safe_distance_2r"
  assumes "other.s \<delta> \<le> u_max"
  assumes "\<not> (a\<^sub>o > a\<^sub>e \<and> other.s' \<delta> < v\<^sub>e \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * other.s' \<delta> < 0)"
  shows "no_collision_react {0..}"
proof -
  from assms have "s\<^sub>o - s\<^sub>e > v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o" unfolding safe_distance_2r_def by auto
  hence "s\<^sub>o - v\<^sub>o\<^sup>2 / 2 / a\<^sub>o > s\<^sub>e + v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e" by auto
  hence "s\<^sub>o - v\<^sub>o\<^sup>2 / a\<^sub>o + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o > s\<^sub>e + v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e" by auto
  hence "s\<^sub>o + v\<^sub>o * (- v\<^sub>o / a\<^sub>o) + 1/2 * a\<^sub>o * (-v\<^sub>o / a\<^sub>o)\<^sup>2 > s\<^sub>e + v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e"
    using other.p_def other.p_max_def other.p_max_eq other.t_stop_def by auto
  hence "other.s_stop > u_max" unfolding other.s_def using u_max_eq other.t_stop_def
    using ego.q_def other.p_def other.p_max_def other.s_def other.s_t_stop by auto
  thus ?thesis
    using assms(2) assms(3) collision_after_delta cond_1r delayed_cond3' translate_collision_range by linarith
qed

lemma sd2_at_most_sd4:
  assumes "a\<^sub>o > a\<^sub>e"
  shows "safe_distance_2r \<le> safe_distance_4r"
proof -
  have "a\<^sub>o \<noteq> 0" and "a\<^sub>e \<noteq> 0" and "a\<^sub>o - a\<^sub>e \<noteq> 0" and "0 < 2 * (a\<^sub>o - a\<^sub>e)" using hyps assms(1) by auto
  have "0 \<le> (- v\<^sub>e * a\<^sub>o + v\<^sub>o * a\<^sub>e + a\<^sub>o * a\<^sub>e * \<delta>) * (- v\<^sub>e * a\<^sub>o + v\<^sub>o * a\<^sub>e + a\<^sub>o * a\<^sub>e * \<delta>)"
    (is "0 \<le> (?l1 + ?l2 + ?l3) * ?r") by auto
  also have "... = v\<^sub>e\<^sup>2 * a\<^sub>o\<^sup>2 + v\<^sub>o\<^sup>2 * a\<^sub>e\<^sup>2 + a\<^sub>o\<^sup>2 * a\<^sub>e\<^sup>2 * \<delta>\<^sup>2 - 2 * v\<^sub>e * a\<^sub>o * v\<^sub>o * a\<^sub>e - 2 * a\<^sub>o\<^sup>2 * a\<^sub>e * \<delta> * v\<^sub>e + 2 * a\<^sub>o * a\<^sub>e\<^sup>2 * \<delta> * v\<^sub>o"
    (is "?lhs = ?rhs")
    by (auto simp add:algebra_simps power_def)
  finally have "0 \<le> ?rhs" by auto
  hence "(- v\<^sub>e\<^sup>2 * a\<^sub>o / a\<^sub>e - v\<^sub>o\<^sup>2 * a\<^sub>e / a\<^sub>o) * (a\<^sub>o * a\<^sub>e) \<le> (a\<^sub>o * a\<^sub>e * \<delta>\<^sup>2 - 2 * v\<^sub>e * v\<^sub>o - 2 * a\<^sub>o * \<delta> * v\<^sub>e + 2 * a\<^sub>e * \<delta> * v\<^sub>o) * (a\<^sub>o * a\<^sub>e)"
    by (auto simp add: algebra_simps power_def)
  hence "2 * v\<^sub>e * \<delta> * (a\<^sub>o - a\<^sub>e) - v\<^sub>e\<^sup>2 * a\<^sub>o / a\<^sub>e + v\<^sub>e\<^sup>2 + v\<^sub>o\<^sup>2 - v\<^sub>o\<^sup>2 * a\<^sub>e / a\<^sub>o \<le> v\<^sub>o\<^sup>2 + a\<^sub>o\<^sup>2 * \<delta>\<^sup>2 + v\<^sub>e\<^sup>2 + 2 * v\<^sub>o * \<delta> * a\<^sub>o - 2 * v\<^sub>e * v\<^sub>o - 2 * a\<^sub>o * \<delta> * v\<^sub>e - 2 * v\<^sub>o * \<delta> * a\<^sub>o + 2 * a\<^sub>e * \<delta> * v\<^sub>o - a\<^sub>o\<^sup>2 * \<delta>\<^sup>2 + a\<^sub>o * a\<^sub>e * \<delta>\<^sup>2 + 2 * v\<^sub>e * \<delta> * (a\<^sub>o - a\<^sub>e)"
    by (auto simp add: ego2.decel other.decel)
  hence "2 * v\<^sub>e * \<delta> * (a\<^sub>o - a\<^sub>e) - v\<^sub>e\<^sup>2 * a\<^sub>o / a\<^sub>e + v\<^sub>e\<^sup>2 + v\<^sub>o\<^sup>2 - v\<^sub>o\<^sup>2 * a\<^sub>e / a\<^sub>o \<le> (v\<^sub>o + \<delta> * a\<^sub>o - v\<^sub>e)\<^sup>2 - 2 * v\<^sub>o * \<delta> * a\<^sub>o + 2 * a\<^sub>e * \<delta> * v\<^sub>o - a\<^sub>o\<^sup>2 * \<delta>\<^sup>2 + a\<^sub>o * a\<^sub>e * \<delta>\<^sup>2 + 2 * v\<^sub>e * \<delta> * (a\<^sub>o - a\<^sub>e)"
    by (auto simp add: algebra_simps power_def)
  hence "v\<^sub>e * \<delta> * 2 * (a\<^sub>o - a\<^sub>e) - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e * 2 * a\<^sub>o + v\<^sub>e\<^sup>2 / 2 / a\<^sub>e * 2 * a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o * 2 * a\<^sub>o - v\<^sub>o\<^sup>2 / 2 / a\<^sub>o * 2 * a\<^sub>e \<le> (v\<^sub>o + \<delta> * a\<^sub>o - v\<^sub>e)\<^sup>2 - v\<^sub>o * \<delta> * 2 * a\<^sub>o - v\<^sub>o * \<delta> * 2 * -a\<^sub>e - a\<^sub>o * \<delta>\<^sup>2 / 2 * 2 * a\<^sub>o - a\<^sub>o * \<delta>\<^sup>2 / 2 * 2 * -a\<^sub>e + v\<^sub>e * \<delta> * 2 * (a\<^sub>o - a\<^sub>e)"
    (is "?lhs1 \<le> ?rhs1")
    by (simp add: \<open>a\<^sub>o \<noteq> 0\<close> \<open>a\<^sub>e \<noteq> 0\<close> power2_eq_square algebra_simps)
  hence "v\<^sub>e * \<delta> * 2 * (a\<^sub>o - a\<^sub>e) - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e * 2 * (a\<^sub>o - a\<^sub>e) + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o * 2 * (a\<^sub>o - a\<^sub>e) \<le> (v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) * 2 * (a\<^sub>o - a\<^sub>e) - v\<^sub>o * \<delta> * 2 * (a\<^sub>o - a\<^sub>e) - a\<^sub>o * \<delta>\<^sup>2 / 2 * 2 * (a\<^sub>o - a\<^sub>e) + v\<^sub>e * \<delta> * 2 *(a\<^sub>o - a\<^sub>e)"
    (is "?lhs2 \<le> ?rhs2")
  proof -
    assume "?lhs1 \<le> ?rhs1"
    have "?lhs1 = ?lhs2" by (auto simp add:field_simps)
    moreover
    have "?rhs1 = ?rhs2" using \<open>a\<^sub>o - a\<^sub>e \<noteq> 0\<close> by (auto simp add:field_simps)
    ultimately show ?thesis using \<open>?lhs1 \<le> ?rhs1\<close> by auto
  qed
  hence "(v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o) * 2 * (a\<^sub>o - a\<^sub>e) \<le> ((v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) - v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2 + v\<^sub>e * \<delta>) * 2 *(a\<^sub>o - a\<^sub>e)"
    by (simp add: algebra_simps)
  hence "v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o \<le> (v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) - v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2 + v\<^sub>e * \<delta>"
    using \<open>a\<^sub>o > a\<^sub>e\<close> mult_le_cancel_iff1[OF \<open>0 < 2 * (a\<^sub>o - a\<^sub>e)\<close>, of "(v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o)"
    "(v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) - v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2 + v\<^sub>e * \<delta>"] semiring_normalization_rules(18)
    by (metis (no_types, lifting))
  thus ?thesis using safe_distance_2r_def safe_distance_4r_def by auto
qed

lemma sd_4r_correct:
  assumes "s\<^sub>o - s\<^sub>e > safe_distance_4r"
  assumes "other.s \<delta> \<le> u_max"
  assumes "\<delta> \<le> other.t_stop"
  assumes "a\<^sub>o > a\<^sub>e"
  shows "no_collision_react {0..}"
proof -
  from assms have "s\<^sub>o - s\<^sub>e > (v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) - v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2 + v\<^sub>e * \<delta>"
    unfolding safe_distance_4r_def by auto
  hence "s\<^sub>o + v\<^sub>o * \<delta> + 1/2 * a\<^sub>o * \<delta>\<^sup>2 - s\<^sub>e - v\<^sub>e * \<delta> > (v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e)" by linarith
  hence "other.s \<delta> -  ego.q \<delta> > (other.s' \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e)"
    using assms(3) ego.q_def other.p_def other.s_def other.p'_def other.s'_def pos_react by auto
  hence "other.s \<delta> -  ego.q \<delta> > delayed_safe_distance.snd_safe_distance"
    by (simp add: delayed_safe_distance.snd_safe_distance_def)
  hence c: "\<not> (other.s \<delta> -  ego.q \<delta> \<le> delayed_safe_distance.snd_safe_distance)" by linarith
  have "u_max < other.s_stop"
    unfolding u_max_eq other.s_t_stop other.p_max_eq ego.q_def using assms(1) sd2_at_most_sd4[OF assms(4)]
    unfolding safe_distance_4r_def safe_distance_2r_def by auto
  consider "s\<^sub>o \<le> u_max" | "s\<^sub>o > u_max" by linarith
  thus ?thesis
  proof (cases)
    case 1
    from cond_3r_2[OF this \<open>u_max < other.s_stop\<close> assms(2)]  show ?thesis
      using c by auto
  next
    case 2
    then show ?thesis using cond_1r by auto
  qed
qed

text \<open>Irrelevant, this Safe Distance is unreachable in the checker.\<close>
definition safe_distance_5r :: real where 
  "safe_distance_5r = v\<^sub>e\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o + v\<^sub>e * \<delta>"

lemma sd_5r_correct:
  assumes "s\<^sub>o - s\<^sub>e > safe_distance_5r"
  assumes "u_max < other.s_stop"
  assumes "other.s \<delta> \<le> u_max"
  assumes "\<delta> > other.t_stop"
  shows "no_collision_react {0..}"
proof -
  from assms have "s\<^sub>o - s\<^sub>e > v\<^sub>e\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o + v\<^sub>e * \<delta>"
    unfolding safe_distance_5r_def by auto
  hence "s\<^sub>o + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o - s\<^sub>e - v\<^sub>e * \<delta> > (0 - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e)"
    using assms(2-4) unfolding other.s_def other.s_t_stop
    apply (auto simp: movement.p_t_stop split: if_splits)
    using cond_1r cond_2r other.s_t_stop by linarith+
  hence "other.s \<delta> -  ego.q \<delta> > (other.s' \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e)"
    using assms(2) assms(3) assms(4) other.s_def other.s_t_stop by auto
  hence "other.s \<delta> -  ego.q \<delta> > delayed_safe_distance.snd_safe_distance"
    by (simp add: delayed_safe_distance.snd_safe_distance_def)
  hence "\<not> (other.s \<delta> -  ego.q \<delta> \<le> delayed_safe_distance.snd_safe_distance)" by linarith
  thus ?thesis using assms(2) assms(3) cond_1r cond_3r_2 by linarith
qed

lemma translate_no_collision_range:
  "delayed_safe_distance.no_collision {0 ..} \<longleftrightarrow> no_collision_react {\<delta> ..}"  
proof
  assume left: "delayed_safe_distance.no_collision {0 ..}" 
  show "no_collision_react {\<delta> ..}" 
  proof (unfold collision_react_def; simp; rule ballI)
    fix t::real  
    assume "t \<in> {\<delta> ..}"
    hence "\<delta> \<le> t" by simp
    with pos_react have "0 \<le> t - \<delta>" by simp
    with left have ineq: "ego2.s (t - \<delta>) \<noteq> delayed_safe_distance.other.s (t - \<delta>)"
      unfolding delayed_safe_distance.collision_def by auto
    have "ego2.s (t - \<delta>) = (ego2.s \<circ> \<tau>) t" unfolding comp_def \<tau>_def by auto
    also have "... = u t" unfolding u_def using \<open>\<delta> \<le> t\<close> pos_react 
      by (auto simp: \<tau>_def ego2.init_s)
    finally have "ego2.s (t - \<delta>) = u t" by auto

    moreover have "delayed_safe_distance.other.s (t - \<delta>) = other.s t"
      using delayed_other_s_eq pos_react \<open>\<delta> \<le> t\<close> by auto
  
    ultimately show "u t \<noteq> other.s t" using ineq by auto
  qed
next
  assume right: "no_collision_react {\<delta> ..}"
  show "delayed_safe_distance.no_collision {0 ..}"
  proof (unfold delayed_safe_distance.collision_def; simp; rule ballI)
    fix t ::real
    assume "t \<in> {0 ..}"
    hence "0 \<le> t" by auto
    hence "\<delta> \<le> t + \<delta>" by auto
    with right have ineq: "u (t + \<delta>) \<noteq> other.s (t + \<delta>)" unfolding collision_react_def by auto
            
    have "u (t + \<delta>) = ego2.s t" unfolding u_def comp_def \<tau>_def 
      using \<open>0 \<le> t\<close> pos_react \<open>\<delta> \<le> t+ \<delta>\<close> by (auto simp add:ego2.init_s)
    moreover have "other.s (t + \<delta>) = delayed_safe_distance.other.s t"
      using delayed_other_s_eq[of t] using \<open>0 \<le> t\<close> by auto
    ultimately show "ego2.s t \<noteq> delayed_safe_distance.other.s t" using ineq by auto
  qed
qed

lemma delayed_cond1:
  assumes "other.s \<delta> > u_max"
  shows "delayed_safe_distance.no_collision {0 ..}"
proof -
  have "ego2.s_stop = u_max"  unfolding ego2.s_t_stop ego2.p_max_eq u_max_eq by auto
  also have "... < other.s \<delta>" using assms by simp
  finally have "ego2.s_stop < other.s \<delta>" by auto
  thus "delayed_safe_distance.no_collision {0 ..}" by (simp add: delayed_safe_distance.cond_1)
qed

theorem cond_3r_3:
  assumes "s\<^sub>o \<le> u_max"
  assumes "u_max < other.s_stop"
  assumes "other.s \<delta> > u_max"
  shows "no_collision_react {0 ..}"
proof -
  have eq: "{0 ..} = {0 .. \<delta>} \<union> {\<delta> ..}" using pos_react by auto
  show ?thesis unfolding eq 
  proof (intro no_collision_union)
    show "no_collision_react {0 .. \<delta>}" by (rule no_collision_react_initially[OF assms(1) assms(2)])  
  next
    have "delayed_safe_distance.no_collision {0 ..}" by (rule delayed_cond1[OF assms(3)])
    with translate_no_collision_range show "no_collision_react {\<delta> ..}" by auto
  qed
qed

lemma sd_2r_correct_for_3r_3:
  assumes "s\<^sub>o - s\<^sub>e > safe_distance_2r"
  assumes "other.s \<delta> > u_max"
  shows "no_collision_react {0..}"
proof -
  from assms have "s\<^sub>o - s\<^sub>e > v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o" unfolding safe_distance_2r_def by auto
  hence "s\<^sub>o - v\<^sub>o\<^sup>2 / 2 / a\<^sub>o > s\<^sub>e + v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e" by auto
  hence "s\<^sub>o - v\<^sub>o\<^sup>2 / a\<^sub>o + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o > s\<^sub>e + v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e" by auto
  hence "s\<^sub>o + v\<^sub>o * (- v\<^sub>o / a\<^sub>o) + 1/2 * a\<^sub>o * (-v\<^sub>o / a\<^sub>o)\<^sup>2 > s\<^sub>e + v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e"
    using other.p_def other.p_max_def other.p_max_eq other.t_stop_def by auto
  hence "other.s_stop > u_max" unfolding other.s_def using u_max_eq other.t_stop_def
    using ego.q_def other.p_def other.p_max_def other.s_def other.s_t_stop by auto
  thus ?thesis
    using assms(2) cond_1r cond_3r_3 by linarith
qed

lemma sd_3r_correct:
  assumes "s\<^sub>o - s\<^sub>e > safe_distance_3r"
  assumes "\<delta> \<le> other.t_stop"
  shows "no_collision_react {0 ..}"
proof -
  from assms have "s\<^sub>o - s\<^sub>e > v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e - v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2" unfolding safe_distance_3r_def by auto
  hence "s\<^sub>o + v\<^sub>o * \<delta> + 1/2 * a\<^sub>o * \<delta>\<^sup>2 > s\<^sub>e + v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e" by auto
  hence "other.s \<delta> > u_max" using other.s_def u_max_eq assms(2) ego.q_def other.p_def pos_react by auto
  thus ?thesis using cond_1r cond_3r_3 delayed_other_s_stop_eq delayed_safe_distance.other.s0_le_s_stop by linarith
qed

lemma sd_2_at_least_sd_3:
  assumes "\<delta> \<le> other.t_stop"
  shows "safe_distance_3r \<ge> safe_distance_2r"
proof -
  from assms have "\<delta> = other.t_stop \<or> \<delta> < other.t_stop" by auto
  then have "safe_distance_3r = safe_distance_2r \<or> safe_distance_3r > safe_distance_2r"
  proof (rule Meson.disj_forward)
      assume "\<delta> = other.t_stop"
      hence "\<delta> = - v\<^sub>o / a\<^sub>o" unfolding other.t_stop_def by auto
      hence "- v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2 = - v\<^sub>o  * other.t_stop - 1/2 * a\<^sub>o * other.t_stop\<^sup>2" by (simp add: movement.t_stop_def)
      thus "safe_distance_3r = safe_distance_2r"
        using other.p_def other.p_max_def other.p_max_eq safe_distance_2r_def safe_distance_3r_def by auto
    next
      assume "\<delta> < other.t_stop"
      hence "\<delta> < - v\<^sub>o / a\<^sub>o" unfolding other.t_stop_def by auto
      hence "0 < v\<^sub>o + a\<^sub>o * \<delta>"
        using other.decel other.p'_def other.p'_pos_iff by auto
      hence "0 < v\<^sub>o + 1/2 * a\<^sub>o * (\<delta> + other.t_stop)" by (auto simp add:field_simps other.t_stop_def)
      hence "0 > v\<^sub>o * (\<delta> - other.t_stop) + 1/2 * a\<^sub>o * (\<delta> + other.t_stop) * (\<delta> - other.t_stop)"
        using \<open>\<delta> < other.t_stop\<close>  mult_less_cancel_left_neg[where c="\<delta> - other.t_stop" and a ="v\<^sub>o + 1 / 2 * a\<^sub>o * (\<delta> + other.t_stop)" and b="0"]
        by (auto simp add: field_simps)
      hence " (\<delta> + other.t_stop) * (\<delta> - other.t_stop) = (\<delta>\<^sup>2 - other.t_stop\<^sup>2)"
        by (simp add: power2_eq_square square_diff_square_factored)
      hence "0 > v\<^sub>o * (\<delta> - other.t_stop) + 1/2 * a\<^sub>o * (\<delta>\<^sup>2 - other.t_stop\<^sup>2)"
        by (metis (no_types, hide_lams) \<open>v\<^sub>o * (\<delta> - other.t_stop) + 1 / 2 * a\<^sub>o * (\<delta> + other.t_stop) * (\<delta> - other.t_stop) < 0\<close> divide_divide_eq_left divide_divide_eq_right times_divide_eq_left)
      hence "0 > v\<^sub>o * \<delta> - v\<^sub>o * other.t_stop  + 1/2 * a\<^sub>o * \<delta>\<^sup>2 -  1/2 * a\<^sub>o * other.t_stop\<^sup>2 "
        by (simp add: right_diff_distrib)
      hence "- v\<^sub>o * \<delta> - 1/2 * a\<^sub>o * \<delta>\<^sup>2 > - v\<^sub>o  * (- v\<^sub>o / a\<^sub>o) - 1/2 * a\<^sub>o * (- v\<^sub>o / a\<^sub>o)\<^sup>2"
        unfolding movement.t_stop_def by argo
      thus "safe_distance_3r > safe_distance_2r"
        using other.p_def other.p_max_def other.p_max_eq other.t_stop_def safe_distance_2r_def safe_distance_3r_def by auto
  qed
  thus ?thesis by auto
qed
end

subsection \<open>Checker Design\<close>

text \<open>
  We define two checkers for different cases: 
  \<^item> one checker for the case that \<open>\<delta> \<le> other.t_stop (other.t_stop = - v\<^sub>o / a\<^sub>o)\<close>
  \<^item> a second checker for the case that \<open>\<delta> > other.t_stop\<close>
\<close>

definition check_precond_r1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<longleftrightarrow> s\<^sub>o > s\<^sub>e \<and> 0 \<le> v\<^sub>e \<and> 0 \<le> v\<^sub>o \<and> a\<^sub>e < 0 \<and> a\<^sub>o < 0 \<and> 0 < \<delta> \<and> \<delta> \<le> - v\<^sub>o / a\<^sub>o"

definition safe_distance0 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where 
  "safe_distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = v\<^sub>e * \<delta> - v\<^sub>o * \<delta> - a\<^sub>o * \<delta>\<^sup>2 / 2"

definition safe_distance_1r :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where 
  "safe_distance_1r a\<^sub>e v\<^sub>e \<delta> = v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / a\<^sub>e / 2"

definition safe_distance_2r :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where 
  "safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e + v\<^sub>o\<^sup>2 / 2 / a\<^sub>o"

definition safe_distance_4r :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = (v\<^sub>o + a\<^sub>o * \<delta> - v\<^sub>e)\<^sup>2 / 2 / (a\<^sub>o - a\<^sub>e) - v\<^sub>o * \<delta> - 1 / 2 * a\<^sub>o * \<delta>\<^sup>2 + v\<^sub>e * \<delta>"

definition safe_distance_3r :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where 
  "safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = v\<^sub>e * \<delta> - v\<^sub>e\<^sup>2 / 2 / a\<^sub>e - v\<^sub>o * \<delta> - 1 / 2 * a\<^sub>o * \<delta>\<^sup>2"

definition checker_r1 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "checker_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<equiv> 
    let distance      = s\<^sub>o - s\<^sub>e;
				precond       = check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>;
        vo_star       = v\<^sub>o + a\<^sub>o * \<delta>;
        t_stop_o_star = - vo_star / a\<^sub>o;
        t_stop_e      = - v\<^sub>e / a\<^sub>e;
        safe_dist0    = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>;
        safe_dist1    = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>;
        safe_dist2    = safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>;
        safe_dist3    = safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>
    in
      if \<not> precond then False
      else if distance > safe_dist0 \<or> distance > safe_dist3 then True
      else if (a\<^sub>o > a\<^sub>e \<and> vo_star < v\<^sub>e \<and> t_stop_e < t_stop_o_star) then distance > safe_dist2
      else distance > safe_dist1"

theorem checker_r1_correctness:
  "(checker_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<longleftrightarrow> check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> 
   safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..})"
proof
  assume asm: "checker_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
  have pre: "check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
  proof (rule ccontr)
    assume "\<not> check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
    with asm show "False" unfolding checker_r1_def Let_def by auto
  qed
  from pre have sdn': "safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>"
    by (unfold_locales) (auto simp add: check_precond_r1_def)
  interpret sdn: safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
    rewrites "sdn.distance0 = safe_distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>" and
             "sdn.safe_distance_1r = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>" and
             "sdn.safe_distance_2r = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>" and
             "sdn.safe_distance_4r = safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>" and
             "sdn.safe_distance_3r = safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
  proof -
    from sdn' show "safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>" by auto
  next
    show "safe_distance_normal.distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta> "
      unfolding safe_distance_normal.distance0_def[OF sdn'] safe_distance0_def by auto
  next
    show "safe_distance_normal.safe_distance_1r a\<^sub>e v\<^sub>e \<delta> = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>"
      unfolding safe_distance_normal.safe_distance_1r_def[OF sdn'] safe_distance_1r_def by auto
  next
    show "safe_distance_normal.safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
      unfolding safe_distance_normal.safe_distance_2r_def[OF sdn'] safe_distance_2r_def by auto
  next
    show "safe_distance_normal.safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> "
      unfolding safe_distance_normal.safe_distance_4r_def[OF sdn'] safe_distance_4r_def by auto
  next
    show "safe_distance_normal.safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
      unfolding safe_distance_normal.safe_distance_3r_def[OF sdn'] safe_distance_3r_def by auto
  qed
  have "0 < \<delta>" and "\<delta> \<le> - v\<^sub>o / a\<^sub>o" using pre unfolding check_precond_r1_def by auto
  define so_delta where "so_delta = s\<^sub>o + v\<^sub>o * \<delta> + a\<^sub>o * \<delta>\<^sup>2 / 2"
  define q_e_delta where "q_e_delta \<equiv> s\<^sub>e + v\<^sub>e * \<delta>"
  define u_stop_e where "u_stop_e \<equiv> q_e_delta - v\<^sub>e\<^sup>2 / (2 * a\<^sub>e)"
  define vo_star where "vo_star = v\<^sub>o + a\<^sub>o * \<delta>"
  define t_stop_o_star where "t_stop_o_star \<equiv> - vo_star / a\<^sub>o"
  define t_stop_e where "t_stop_e = - v\<^sub>e / a\<^sub>e"
  define distance where "distance \<equiv> s\<^sub>o - s\<^sub>e"
  define distance0 where "distance0 = safe_distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
  define safe_dist0 where "safe_dist0 = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>"
  define safe_dist2 where "safe_dist2 \<equiv> safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
  define safe_dist1 where "safe_dist1 \<equiv> safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
  define safe_dist3 where "safe_dist3 = safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
  note abb = so_delta_def q_e_delta_def u_stop_e_def vo_star_def t_stop_o_star_def t_stop_e_def
             distance_def safe_dist2_def safe_dist1_def safe_dist0_def safe_dist3_def distance0_def
  consider "distance > safe_dist0" | "distance > safe_dist3" | "distance \<le> safe_dist0 \<and> distance \<le> safe_dist3"
    by linarith
  hence "sdn.no_collision_react {0..}"
  proof (cases)
    case 1
    then show ?thesis using sdn.sd_1r_correct unfolding  abb by auto
  next
    case 2
    hence pre2: "distance > distance0" using sdn.distance0_at_most_sd3r unfolding abb by auto
    hence "sdn.u \<delta> < sdn.other.s \<delta>" using pre unfolding sdn.u_def sdn.ego.q_def
      sdn.other.s_def sdn.other.t_stop_def sdn.other.p_def abb check_precond_r1_def sdn.distance0_def
      by auto
    from pre interpret sdr: safe_distance_no_collsion_delta a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
      by (unfold_locales) (auto simp add:check_precond_r1_def \<open>sdn.u \<delta> < sdn.other.s \<delta>\<close>)
    show ?thesis using sdr.sd_3r_correct 2 pre unfolding check_precond_r1_def abb sdn.other.t_stop_def
      by auto
  next
    case 3
    hence "distance \<le> safe_dist3" by auto
    hence "sdn.other.s \<delta> \<le> sdn.u_max" using pre unfolding check_precond_r1_def sdn.other.s_def sdn.other.t_stop_def
      sdn.other.p_def sdn.u_max_eq sdn.ego.q_def abb sdn.safe_distance_3r_def by auto
    have " (a\<^sub>o > a\<^sub>e \<and> vo_star < v\<^sub>e \<and> t_stop_e < t_stop_o_star) \<or> \<not>  (a\<^sub>o > a\<^sub>e \<and> vo_star < v\<^sub>e \<and> t_stop_e < t_stop_o_star) "
      by auto
    moreover
    { assume cond: "(a\<^sub>o > a\<^sub>e \<and> vo_star < v\<^sub>e \<and> t_stop_e < t_stop_o_star)"
      with 3 pre have "distance > safe_dist2" using asm unfolding checker_r1_def
          Let_def abb by auto
      with sdn.distance0_at_most_sd4r have "distance > distance0" unfolding abb using cond by auto
      hence "sdn.u \<delta> < sdn.other.s \<delta>" using pre unfolding sdn.u_def sdn.ego.q_def
          sdn.other.s_def sdn.other.t_stop_def sdn.other.p_def abb check_precond_r1_def sdn.distance0_def
        by auto
      from pre interpret sdr: safe_distance_no_collsion_delta a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
        by (unfold_locales) (auto simp add:check_precond_r1_def \<open>sdn.u \<delta> < sdn.other.s \<delta>\<close>)
      from sdr.sd_4r_correct[OF _ \<open>sdn.other.s \<delta> \<le> sdn.u_max\<close>] \<open>distance > safe_dist2\<close>
        have ?thesis using pre cond  unfolding check_precond_r1_def sdn.other.t_stop_def abb by auto }
    moreover
    { assume not_cond: "\<not>  (a\<^sub>o > a\<^sub>e \<and> vo_star < v\<^sub>e \<and> t_stop_e < t_stop_o_star)"
      with 3 pre have "distance > safe_dist1" using asm unfolding checker_r1_def
        Let_def abb by auto
      with sdn.dist0_sd2r_1 have "distance > distance0" using pre not_cond unfolding check_precond_r1_def
        sdn.other.t_stop_def sdn.other.s'_def sdn.other.p'_def abb by (auto simp add:field_simps)
      hence "sdn.u \<delta> < sdn.other.s \<delta>" using pre unfolding sdn.u_def sdn.ego.q_def
          sdn.other.s_def sdn.other.t_stop_def sdn.other.p_def abb check_precond_r1_def sdn.distance0_def
        by auto
      from pre interpret sdr: safe_distance_no_collsion_delta a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
        by (unfold_locales) (auto simp add:check_precond_r1_def \<open>sdn.u \<delta> < sdn.other.s \<delta>\<close>)
      from sdr.sd_2r_correct_for_3r_2[OF _ \<open>sdn.other.s \<delta> \<le> sdn.u_max\<close>] not_cond \<open>distance > safe_dist1\<close>
        have ?thesis using pre unfolding abb sdn.other.s'_def check_precond_r1_def sdn.other.t_stop_def sdn.other.p'_def
        by (auto simp add:field_simps) }
    ultimately show ?thesis by auto
  qed
  with pre show " check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> sdn.no_collision_react {0..}" by auto
next
  assume "check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..}"
  hence pre: "check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>" and as2: "safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..}"
  by auto
  show "checker_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> "
  proof (rule ccontr)
    assume as1: "\<not> checker_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
    from pre have "0 < \<delta>" and "\<delta> \<le> - v\<^sub>o / a\<^sub>o" unfolding check_precond_r1_def by auto
    define so_delta where "so_delta = s\<^sub>o + v\<^sub>o * \<delta> + a\<^sub>o * \<delta>\<^sup>2 / 2"
    define q_e_delta where "q_e_delta \<equiv> s\<^sub>e + v\<^sub>e * \<delta>"
    define u_stop_e where "u_stop_e \<equiv> q_e_delta - v\<^sub>e\<^sup>2 / (2 * a\<^sub>e)"
    define vo_star where "vo_star \<equiv> v\<^sub>o + a\<^sub>o * \<delta>"
    define t_stop_o_star where "t_stop_o_star \<equiv> - vo_star / a\<^sub>o"
    define t_stop_e where "t_stop_e \<equiv> - v\<^sub>e / a\<^sub>e"
    define distance where "distance \<equiv> s\<^sub>o - s\<^sub>e"
    define distance0 where "distance0 \<equiv> safe_distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
    define safe_dist0 where "safe_dist0 \<equiv> safe_distance_1r a\<^sub>e v\<^sub>e \<delta>"
    define safe_dist2 where "safe_dist2 \<equiv> safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
    define safe_dist1 where "safe_dist1 \<equiv> safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
    define safe_dist3 where "safe_dist3 \<equiv> safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
    note abb = so_delta_def q_e_delta_def u_stop_e_def vo_star_def t_stop_o_star_def t_stop_e_def
               distance_def safe_dist2_def safe_dist1_def safe_dist0_def safe_dist3_def distance0_def
    from pre have sdn': "safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>"
      by (unfold_locales) (auto simp add: check_precond_r1_def)
    interpret sdn: safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
      rewrites "sdn.distance0 = safe_distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>" and
               "sdn.safe_distance_1r = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>" and
               "sdn.safe_distance_2r = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>" and
               "sdn.safe_distance_4r = safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>" and
               "sdn.safe_distance_3r = safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
    proof -
      from sdn' show "safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>" by auto
    next
      show "safe_distance_normal.distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance0 v\<^sub>e a\<^sub>o v\<^sub>o \<delta> "
        unfolding safe_distance_normal.distance0_def[OF sdn'] safe_distance0_def by auto
    next
      show "safe_distance_normal.safe_distance_1r a\<^sub>e v\<^sub>e \<delta> = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>"
        unfolding safe_distance_normal.safe_distance_1r_def[OF sdn'] safe_distance_1r_def by auto
    next
      show "safe_distance_normal.safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
        unfolding safe_distance_normal.safe_distance_2r_def[OF sdn'] safe_distance_2r_def by auto
    next
      show "safe_distance_normal.safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> "
        unfolding safe_distance_normal.safe_distance_4r_def[OF sdn'] safe_distance_4r_def by auto
    next
      show "safe_distance_normal.safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
        unfolding safe_distance_normal.safe_distance_3r_def[OF sdn'] safe_distance_3r_def by auto
    qed
    have "\<not> distance > distance0 \<or>  distance > distance0" by auto
    moreover
    { assume "\<not> distance > distance0"
      hence "distance \<le> distance0" by auto
      with sdn.cond_3r_1' have "sdn.collision_react {0..\<delta>}" using pre unfolding check_precond_r1_def abb
        sdn.other.t_stop_def by auto
      with sdn.collision_react_subset have "sdn.collision_react {0..}" by auto
      with as2 have "False" by auto }
    moreover
    { assume if2: "distance > distance0"
      have "\<not> (distance > safe_dist0 \<or> distance > safe_dist3)"
      proof (rule ccontr)
        assume "\<not> \<not> (safe_dist0 < distance \<or> safe_dist3 < distance)"
        hence "(safe_dist0 < distance \<or> safe_dist3 < distance)" by auto
        with as1 show "False" using pre if2 unfolding checker_r1_def Let_def abb
          by auto
      qed
      hence if31: "distance \<le> safe_dist0" and if32: "distance \<le> safe_dist3" by auto
      have "sdn.u \<delta> < sdn.other.s \<delta>" using if2 pre unfolding sdn.u_def sdn.ego.q_def
          sdn.other.s_def sdn.other.t_stop_def sdn.other.p_def abb check_precond_r1_def sdn.distance0_def
          by auto
      from pre interpret sdr: safe_distance_no_collsion_delta a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
        by (unfold_locales) (auto simp add:check_precond_r1_def \<open>sdn.u \<delta> < sdn.other.s \<delta>\<close>)
      have " s\<^sub>o \<le> sdn.u_max" using if31 unfolding sdn.u_max_eq sdn.ego.q_def abb
        sdn.safe_distance_1r_def by auto
      have "sdn.other.s \<delta> \<le> sdn.u_max" using if32 pre unfolding sdn.other.s_def check_precond_r1_def
        sdn.other.t_stop_def sdn.other.p_def sdn.u_max_eq sdn.ego.q_def abb sdn.safe_distance_3r_def
        by auto
      consider "(a\<^sub>o > a\<^sub>e \<and> vo_star < v\<^sub>e \<and> t_stop_e < t_stop_o_star)" |
               "\<not> (a\<^sub>o > a\<^sub>e \<and> vo_star < v\<^sub>e \<and> t_stop_e < t_stop_o_star)" by auto
      hence "False"
      proof (cases)
        case 1
        hence rest_conjunct:"(a\<^sub>e < a\<^sub>o \<and> sdn.other.s' \<delta> < v\<^sub>e \<and> v\<^sub>e - a\<^sub>e / a\<^sub>o * sdn.other.s' \<delta> < 0)"
          using pre unfolding check_precond_r1_def unfolding sdn.other.s'_def sdn.other.t_stop_def
          sdn.other.p'_def abb by (auto simp add:field_simps)
        from 1 have "distance \<le> safe_dist2" using as1 pre if2 if31 if32 unfolding checker_r1_def
          Let_def abb by auto
        hence cond_f: "sdn.other.s \<delta> - sdn.ego.q \<delta> \<le> sdr.delayed_safe_distance.snd_safe_distance"
          using pre unfolding check_precond_r1_def sdn.other.s_def sdn.other.t_stop_def sdn.other.p_def
          sdn.ego.q_def sdr.delayed_safe_distance.snd_safe_distance_def using sdn.other.s'_def[of "\<delta>"]
          unfolding sdn.other.t_stop_def sdn.other.p'_def abb sdn.safe_distance_4r_def
          by auto
        have "distance > safe_dist1 \<or> distance \<le> safe_dist1" by auto
        moreover
        { assume "distance > safe_dist1"
          hence "sdn.u_max < sdn.other.s_stop" unfolding sdn.u_max_eq sdn.ego.q_def sdn.other.s_t_stop
              sdn.other.p_max_eq abb sdn.safe_distance_2r_def by (auto simp add:field_simps)
          from sdr.cond_3r_2[OF \<open>s\<^sub>o \<le> sdn.u_max\<close> this \<open>sdn.other.s \<delta> \<le> sdn.u_max\<close>]
          have "sdn.collision_react {0..}" using cond_f rest_conjunct by auto
          with as2 have "False" by auto }
        moreover
        { assume "distance \<le> safe_dist1"
          hence "sdn.u_max \<ge> sdn.other.s_stop" unfolding sdn.u_max_eq sdn.ego.q_def sdn.other.s_t_stop
              sdn.other.p_max_eq abb sdn.safe_distance_2r_def by (auto simp add:field_simps)
          with sdn.cond_2r[OF this] have "sdn.collision_react {0..}" by auto
          with as2 have "False" by auto }
        ultimately show ?thesis by auto
      next
        case 2
        hence "distance \<le> safe_dist1" using as1 pre if2 if31 if32 unfolding checker_r1_def
          Let_def abb by auto
        hence "sdn.u_max \<ge> sdn.other.s_stop" unfolding sdn.u_max_eq sdn.ego.q_def sdn.other.s_t_stop
          sdn.other.p_max_eq abb sdn.safe_distance_2r_def by (auto simp add:field_simps)
        with sdn.cond_2r[OF this] have "sdn.collision_react {0..}" by auto
        with as2 show "False" by auto
      qed }
    ultimately show "False" by auto
  qed
qed

definition check_precond_r2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where 
  "check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<longleftrightarrow> s\<^sub>o > s\<^sub>e \<and> 0 \<le> v\<^sub>e \<and> 0 \<le> v\<^sub>o \<and> a\<^sub>e < 0 \<and> a\<^sub>o < 0 \<and> 0 < \<delta> \<and> \<delta> > - v\<^sub>o / a\<^sub>o"

definition safe_distance0_2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where 
  "safe_distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = v\<^sub>e * \<delta> + 1 / 2 * v\<^sub>o\<^sup>2 / a\<^sub>o"

definition checker_r2 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "checker_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<equiv> 
    let distance   = s\<^sub>o - s\<^sub>e;
				precond    = check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>;
        safe_dist0 = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>;
        safe_dist1 = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> 
    in
      if \<not> precond then False
      else if distance > safe_dist0 then True
      else distance > safe_dist1"

theorem checker_r2_correctness:
  "(checker_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<longleftrightarrow> check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> 
    safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..})"
proof
  assume asm: "checker_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
  have pre: "check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
  proof (rule ccontr)
    assume "\<not> check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
      with asm show "False" unfolding checker_r2_def Let_def by auto
    qed
      from pre have sdn': "safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>"
    by (unfold_locales) (auto simp add: check_precond_r2_def)
  interpret sdn: safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
    rewrites "sdn.distance0_2 = safe_distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>" and
             "sdn.safe_distance_1r = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>" and
             "sdn.safe_distance_2r = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
  proof -
    from sdn' show "safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>" by auto
  next
    show "safe_distance_normal.distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
      unfolding safe_distance_normal.distance0_2_def[OF sdn'] safe_distance0_2_def by auto
  next
    show "safe_distance_normal.safe_distance_1r a\<^sub>e v\<^sub>e \<delta> = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>"
      unfolding safe_distance_normal.safe_distance_1r_def[OF sdn'] safe_distance_1r_def by auto
  next
    show "safe_distance_normal.safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
      unfolding safe_distance_normal.safe_distance_2r_def[OF sdn'] safe_distance_2r_def by auto
  qed
  have "0 < \<delta>" and "\<delta> > - v\<^sub>o / a\<^sub>o" using pre unfolding check_precond_r2_def by auto
  define distance where "distance \<equiv> s\<^sub>o - s\<^sub>e"
  define distance0_2 where "distance0_2 = safe_distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
  define safe_dist0 where "safe_dist0 = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>"
  define safe_dist1 where "safe_dist1 \<equiv> safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
  note abb = distance_def safe_dist1_def safe_dist0_def distance0_2_def
  consider "distance > safe_dist0" | "distance \<le> safe_dist0"
    by linarith
  hence "sdn.no_collision_react {0..}"
  proof (cases)
    case 1
    then show ?thesis using sdn.sd_1r_correct unfolding abb by auto
  next
    case 2
    hence "(s\<^sub>o \<le> sdn.u_max)" using distance_def safe_dist0_def sdn.sd_1r_eq by linarith
    with 2 pre have "distance > safe_dist1" using asm unfolding checker_r2_def Let_def abb by auto
    with sdn.dist0_sd2r_2 have "distance > distance0_2" using abb \<open>- v\<^sub>o / a\<^sub>o < \<delta>\<close> by auto
    hence "sdn.u \<delta> < sdn.other.s \<delta>" using abb sdn.distance0_2_eq \<open>\<delta> > - v\<^sub>o / a\<^sub>o\<close> sdn.other.t_stop_def by auto
    have "sdn.u_max < sdn.other.s \<delta>" using abb sdn.sd2r_eq  \<open>\<delta> > - v\<^sub>o / a\<^sub>o\<close> sdn.other.t_stop_def \<open>distance > safe_dist1\<close> by auto
    from pre interpret sdr: safe_distance_no_collsion_delta a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
        by (unfold_locales) (auto simp add:check_precond_r2_def \<open>sdn.u \<delta> < sdn.other.s \<delta>\<close>)
    from sdr.sd_2r_correct_for_3r_3[OF] \<open>distance > safe_dist1\<close> \<open>sdn.u \<delta> < sdn.other.s \<delta>\<close> \<open>sdn.u_max < sdn.other.s \<delta>\<close>
       show ?thesis using pre unfolding abb sdn.other.s'_def check_precond_r2_def sdn.other.t_stop_def sdn.other.p'_def
            by (auto simp add:field_simps)
  qed
  with pre show " check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> sdn.no_collision_react {0..}" by auto
next
  assume "check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..}"
  hence pre: "check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>" and as2: "safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..}"
    by auto
  show "checker_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
  proof (rule ccontr)
    assume as1: "\<not> checker_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
    from pre have "0 < \<delta>" and "\<delta> > - v\<^sub>o / a\<^sub>o" unfolding check_precond_r2_def by auto
    define distance where "distance \<equiv> s\<^sub>o - s\<^sub>e"
    define distance0_2 where "distance0_2 = safe_distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
    define safe_dist0 where "safe_dist0 = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>"
    define safe_dist1 where "safe_dist1 \<equiv> safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
    note abb = distance_def safe_dist1_def safe_dist0_def distance0_2_def
    from pre have sdn': "safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>"
      by (unfold_locales) (auto simp add: check_precond_r2_def)
   interpret sdn: safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
    rewrites "sdn.distance0_2 = safe_distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>" and
             "sdn.safe_distance_1r = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>" and
             "sdn.safe_distance_2r = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
    proof -
      from sdn' show "safe_distance_normal a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>" by auto
    next
      show "safe_distance_normal.distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance0_2 v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
        unfolding safe_distance_normal.distance0_2_def[OF sdn'] safe_distance0_2_def by auto
    next
      show "safe_distance_normal.safe_distance_1r a\<^sub>e v\<^sub>e \<delta> = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>"
        unfolding safe_distance_normal.safe_distance_1r_def[OF sdn'] safe_distance_1r_def by auto
    next
      show "safe_distance_normal.safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>"
        unfolding safe_distance_normal.safe_distance_2r_def[OF sdn'] safe_distance_2r_def by auto
    qed
    have "\<not> distance > distance0_2 \<or>  distance > distance0_2" by auto
    moreover
    { assume "\<not> distance > distance0_2"
      hence "distance \<le> distance0_2" by auto
      with sdn.cond_3r_1'_2 have "sdn.collision_react {0..\<delta>}" using pre unfolding check_precond_r2_def abb sdn.other.t_stop_def by auto
      with sdn.collision_react_subset have "sdn.collision_react {0..}" by auto
      with as2 have "False" by auto }
    moreover
    { assume if2: "distance > distance0_2"
      have "\<not> (distance > safe_dist0)"
      proof (rule ccontr)
        assume "\<not> \<not> (safe_dist0 < distance)"
        hence "(safe_dist0 < distance)" by auto
        with as1 show "False" using pre if2 unfolding checker_r2_def Let_def abb by auto
      qed
      hence if3: "distance \<le> safe_dist0" by auto
      with pre have "distance \<le> safe_dist1" using as1 unfolding checker_r2_def Let_def abb by auto

      have "sdn.u \<delta> < sdn.other.s \<delta>" using abb if2 sdn.distance0_2_eq \<open>\<delta> > - v\<^sub>o / a\<^sub>o\<close> sdn.other.t_stop_def by auto
      from pre interpret sdr: safe_distance_no_collsion_delta a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta>
          by (unfold_locales) (auto simp add:check_precond_r2_def \<open>sdn.u \<delta> < sdn.other.s \<delta>\<close>)
      have "sdn.u_max \<ge> sdn.other.s \<delta>" using abb sdn.sd2r_eq  \<open>\<delta> > - v\<^sub>o / a\<^sub>o\<close> sdn.other.t_stop_def \<open>distance \<le> safe_dist1\<close> by auto
      with \<open>\<delta> > - v\<^sub>o / a\<^sub>o\<close> have "sdn.u_max \<ge> sdn.other.s_stop"
        using sdn.other.s_mono sdn.other.t_stop_nonneg sdn.other.p_t_stop sdn.other.p_zero sdn.other.t_stop_def
        apply (auto simp: sdn.other.s_def movement.t_stop_def split: if_splits)
        using sdn.other.p_zero by auto
      hence "sdn.collision_react {0..}" using sdn.cond_2r by auto
      with as2 have "False" by auto }
    ultimately show "False" by auto
  qed
qed

text \<open>Combine the two checkers into one.\<close>

definition check_precond_r :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where 
  "check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<longleftrightarrow> s\<^sub>o > s\<^sub>e \<and> 0 \<le> v\<^sub>e \<and> 0 \<le> v\<^sub>o \<and> a\<^sub>e < 0 \<and> a\<^sub>o < 0 \<and> 0 < \<delta>"

definition checker_r :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<equiv> 
    let distance      = s\<^sub>o - s\<^sub>e;
				precond       = check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>;
        vo_star       = v\<^sub>o + a\<^sub>o * \<delta>;
        t_stop_o_star = -vo_star / a\<^sub>o;
        t_stop_e      = -v\<^sub>e / a\<^sub>e;
        t_stop_o      = -v\<^sub>o / a\<^sub>o;
        safe_dist0    = safe_distance_1r a\<^sub>e v\<^sub>e \<delta>;
        safe_dist1    = safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>;
        safe_dist2    = safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>;
        safe_dist3    = safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta> 
    in
      if \<not> precond then False
      else if distance > safe_dist0 then True
      else if \<delta> \<le> t_stop_o \<and> distance > safe_dist3 then True
      else if \<delta> \<le> t_stop_o \<and> (a\<^sub>o > a\<^sub>e \<and> vo_star < v\<^sub>e \<and> t_stop_e < t_stop_o_star) then distance > safe_dist2
      else distance > safe_dist1"

theorem checker_eq_1:
  "checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> \<delta> \<le> - v\<^sub>o / a\<^sub>o  \<longleftrightarrow> checker_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
proof -
  have "checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> \<delta> \<le> - v\<^sub>o / a\<^sub>o \<longleftrightarrow> check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>
    \<and> (s\<^sub>o - s\<^sub>e > safe_distance_1r a\<^sub>e v\<^sub>e \<delta>
        \<or> s\<^sub>o - s\<^sub>e > safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>
        \<or> (((a\<^sub>o > a\<^sub>e \<and> v\<^sub>o + a\<^sub>o * \<delta> < v\<^sub>e \<and> - v\<^sub>e / a\<^sub>e < - (v\<^sub>o + a\<^sub>o * \<delta>) / a\<^sub>o) \<longrightarrow> s\<^sub>o - s\<^sub>e > safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>)
            \<and> (\<not> (a\<^sub>o > a\<^sub>e \<and> v\<^sub>o + a\<^sub>o * \<delta> < v\<^sub>e \<and> - v\<^sub>e / a\<^sub>e < - (v\<^sub>o + a\<^sub>o * \<delta>) / a\<^sub>o) \<longrightarrow> s\<^sub>o - s\<^sub>e > safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>)))
    \<and> \<delta> \<le> - v\<^sub>o / a\<^sub>o" using checker_r_def by metis
  also have "... \<longleftrightarrow> check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>
    \<and> (s\<^sub>o - s\<^sub>e > safe_distance_1r a\<^sub>e v\<^sub>e \<delta>
        \<or> s\<^sub>o - s\<^sub>e > safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>
        \<or> (((a\<^sub>o > a\<^sub>e \<and> v\<^sub>o + a\<^sub>o * \<delta> < v\<^sub>e \<and> - v\<^sub>e / a\<^sub>e < - (v\<^sub>o + a\<^sub>o * \<delta>) / a\<^sub>o) \<longrightarrow> s\<^sub>o - s\<^sub>e > safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>)
            \<and> (\<not> (a\<^sub>o > a\<^sub>e \<and> v\<^sub>o + a\<^sub>o * \<delta> < v\<^sub>e \<and> - v\<^sub>e / a\<^sub>e < - (v\<^sub>o + a\<^sub>o * \<delta>) / a\<^sub>o) \<longrightarrow> s\<^sub>o - s\<^sub>e > safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>)))"
    by (auto simp add:check_precond_r_def check_precond_r1_def)
  also have "... \<longleftrightarrow> checker_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>" by (metis checker_r1_def)
  finally show ?thesis by auto
qed

theorem checker_eq_2:
  "checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> \<delta> > - v\<^sub>o / a\<^sub>o \<longleftrightarrow> checker_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>"
proof -
  have "checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> \<delta> > - v\<^sub>o / a\<^sub>o \<longleftrightarrow> check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> (\<not> check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<or>
   s\<^sub>o - s\<^sub>e > safe_distance_1r a\<^sub>e v\<^sub>e \<delta> \<or>
   (\<delta> \<le> - v\<^sub>o / a\<^sub>o \<and> s\<^sub>o - s\<^sub>e > safe_distance_3r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>) \<or>
   (\<delta> \<le> - v\<^sub>o / a\<^sub>o \<and> a\<^sub>o > a\<^sub>e \<and> v\<^sub>o + a\<^sub>o * \<delta> < v\<^sub>e \<and> - v\<^sub>e / a\<^sub>e < - (v\<^sub>o + a\<^sub>o * \<delta>) / a\<^sub>o \<and> s\<^sub>o - s\<^sub>e > safe_distance_4r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>) \<or>
   s\<^sub>o - s\<^sub>e > safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>) \<and> \<delta> > - v\<^sub>o / a\<^sub>o" unfolding checker_r_def Let_def if_splits by auto
  also have
   "... \<longleftrightarrow> check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>
   \<and> (s\<^sub>o - s\<^sub>e > safe_distance_1r a\<^sub>e v\<^sub>e \<delta> \<or> s\<^sub>o - s\<^sub>e > safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>)
   \<and> \<delta> > - v\<^sub>o / a\<^sub>o"  by (auto simp add:HOL.disjE)
  also have
    "... \<longleftrightarrow> check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>
   \<and> (s\<^sub>o - s\<^sub>e > safe_distance_1r a\<^sub>e v\<^sub>e \<delta> \<or> s\<^sub>o - s\<^sub>e > safe_distance_2r a\<^sub>e v\<^sub>e a\<^sub>o v\<^sub>o \<delta>)"
    by (auto simp add:check_precond_r_def check_precond_r2_def)
  also have "... \<longleftrightarrow> checker_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>" by (auto simp add:checker_r2_def Let_def if_splits)
  thus ?thesis using calculation by auto
qed

theorem checker_r_correctness:
  "(checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<longleftrightarrow> check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..})"
proof -
  have "checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<longleftrightarrow> (checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> \<delta> \<le> - v\<^sub>o / a\<^sub>o) \<or> (checker_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> \<delta> > - v\<^sub>o / a\<^sub>o)" by auto
  also have "... \<longleftrightarrow> checker_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<or> checker_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta>" using checker_eq_1 checker_eq_2 by auto
  also have "... \<longleftrightarrow> (check_precond_r1 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..})
      \<or> (check_precond_r2 s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..})"
    using checker_r1_correctness checker_r2_correctness by auto
  also have "... \<longleftrightarrow> (\<delta> \<le> - v\<^sub>o / a\<^sub>o \<and> check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..})
      \<or> (\<delta> > - v\<^sub>o / a\<^sub>o \<and> check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..})"
    by (auto simp add:check_precond_r_def check_precond_r1_def check_precond_r2_def)
  also have "... \<longleftrightarrow> check_precond_r s\<^sub>e v\<^sub>e a\<^sub>e s\<^sub>o v\<^sub>o a\<^sub>o \<delta> \<and> safe_distance_normal.no_collision_react a\<^sub>e v\<^sub>e s\<^sub>e a\<^sub>o v\<^sub>o s\<^sub>o \<delta> {0..}"
    by auto
  finally show ?thesis by auto
qed

end