section \<open> Autonomous Marine Vehicle \<close>

text \<open> This theory accompanies the paper "Towards Deductive Verification of Control Algorithms for 
  Autonomous Marine Vehicles" by Simon Foster, Mario Gleirscher, and Radu Calinescu.

  CC-NC-BY 4.0, Simon Foster. This version & any derivatives are for NON-MILITARY USE ONLY. \<close>

theory AMV
  imports "UTP-dL.utp_hyprog"
begin

subsection \<open> Preliminaries \<close>

no_notation (ASCII)
  comp  (infixl "o" 55)

lemma self_dot [simp]: "\<parallel>v\<parallel> * \<parallel>v\<parallel> = v \<bullet> v"
  by (metis norm_cauchy_schwarz_eq)

lemma orth_mag [simp]: "a \<bullet> b = \<parallel>a\<parallel> * \<parallel>b\<parallel> \<Longrightarrow> \<parallel>a + b\<parallel> = \<parallel>a\<parallel> + \<parallel>b\<parallel>"
  by (simp add: norm_cauchy_schwarz_eq norm_triangle_eq)

lemma orth_mag' [simp]: "b \<bullet> a = \<parallel>b\<parallel> * \<parallel>a\<parallel> \<Longrightarrow> \<parallel>a + b\<parallel> = \<parallel>a\<parallel> + \<parallel>b\<parallel>"
  by (simp add: norm_cauchy_schwarz_eq norm_triangle_eq)

lemma "a \<noteq> 0 \<Longrightarrow> \<parallel>sgn a\<parallel> = 1"
  by (simp add: norm_sgn)

lemma "a \<noteq> 0 \<Longrightarrow> sgn a \<bullet> sgn a = 1"
  by (meson norm_eq_1 norm_sgn)

lemma sgn_self_dot:
  assumes "a \<noteq> 0"
  shows "(sgn a) \<bullet> (sgn a) = 1"
  by (meson assms norm_eq_1 norm_sgn)

lemma "a \<noteq> 0 \<Longrightarrow> (a / \<parallel>a\<parallel>) \<bullet> (a / \<parallel>a\<parallel>) = 1"
  by simp

lemma "\<lbrakk> a \<ge> 0; a\<^sup>2 = b \<rbrakk> \<Longrightarrow> a = sqrt(b)"
  by (simp add: real_sqrt_unique)


lemma 
  assumes "(a::'a::ordered_euclidean_space) \<noteq> 0"
  shows "a \<bullet> b / \<parallel>a\<parallel> = sgn a \<bullet> b"
  by (simp add: divide_inverse_commute sgn_div_norm)

lemma "v \<noteq> 0 \<Longrightarrow> arccos(v \<bullet> v / (\<parallel>v\<parallel> * \<parallel>v\<parallel>)) = 0"
  by (simp)

declare num1_eq1 [simp del]

lemma exhaust_2':
  fixes x :: 2
  shows "x = 0 \<or> x = 1"
  using exhaust_2 by fastforce

lemma forall_2': "(\<forall>i::2. P i) \<longleftrightarrow> P 0 \<and> P 1"
  by (metis exhaust_2')

declare UNIV_1 [simp del]
declare UNIV_2 [simp del]

lemma UNIV_1 [simp]: "(UNIV :: 1 set) = {0}"
  by (metis UNIV_1 num1_eq1)

lemma UNIV_2 [simp]: "(UNIV :: 2 set) = {0,1}"
  by (simp add: UNIV_eq_I exhaust_2')

subsection \<open> Vector Theorems and Simplifications \<close>

lemma vec_norm: "\<parallel>\<^bold>[[x, y]\<^bold>]\<parallel> = sqrt(x\<^sup>2 + y\<^sup>2)"
  by (simp add: norm_vec_def)

lemma vec_simps [simp]: 
  "k *\<^sub>R \<^bold>[[x, y]\<^bold>] = \<^bold>[[k *\<^sub>R x, k *\<^sub>R y]\<^bold>]"
  "\<^bold>[[x\<^sub>1::real, y\<^sub>1]\<^bold>] \<bullet> \<^bold>[[x\<^sub>2, y\<^sub>2]\<^bold>] = x\<^sub>1 * x\<^sub>2 + y\<^sub>1 * y\<^sub>2"
  "\<^bold>[[x\<^sub>1, y\<^sub>1]\<^bold>] + \<^bold>[[x\<^sub>2, y\<^sub>2]\<^bold>] = \<^bold>[[x\<^sub>1 + x\<^sub>2, y\<^sub>1 + y\<^sub>2]\<^bold>]"
  "\<^bold>[[x\<^sub>1, y\<^sub>1]\<^bold>] - \<^bold>[[x\<^sub>2, y\<^sub>2]\<^bold>] = \<^bold>[[x\<^sub>1 - x\<^sub>2, y\<^sub>1 - y\<^sub>2]\<^bold>]"
  "\<^bold>[[0, 0]\<^bold>] = 0"
     apply (subst scaleR_Mat, simp_all)
  apply (simp add: inner_vec_def)
    apply (subst plus_Mat, simp_all)
   apply (subst minus_Mat, simp_all)
   apply (simp add: matrix_eq_iff nat_of_num1_def forall_2')
  done

lemma orient_vec_mag_1 [simp]: "\<parallel>\<^bold>[[sin \<theta> :: real, cos \<theta>]\<^bold>]\<parallel> = 1"
  by (simp add: vec_norm)

lemma orient_vec_mag_n [simp]: 
  assumes "n \<ge> 0"
  shows "\<parallel>\<^bold>[[n * sin \<theta> :: real, n * cos \<theta>]\<^bold>]\<parallel> = n" (is "?P = ?Q")
proof -
  have "?P = \<parallel>\<^bold>[[n *\<^sub>R sin \<theta> :: real, n *\<^sub>R cos \<theta>]\<^bold>]\<parallel>"
    by (metis real_scaleR_def)
  also have "... = \<parallel>n *\<^sub>R \<^bold>[[sin \<theta> :: real, cos \<theta>]\<^bold>]\<parallel>"
    by simp
  also have "... = \<parallel>n\<parallel> * \<parallel>\<^bold>[[sin \<theta> :: real, cos \<theta>]\<^bold>]\<parallel>"
    by (metis norm_scaleR real_norm_def)
  also from assms have "... = n"
    by simp
  finally show ?thesis .
qed

lemma sin_cos_self_dot [simp]: "\<^bold>[[sin(\<theta>::real), cos(\<theta>)]\<^bold>] \<bullet> \<^bold>[[sin(\<theta>), cos(\<theta>)]\<^bold>] = 1"
  by (simp, metis power2_eq_square sin_cos_squared_add)

lemma vector_2_cases [cases type]: 
  fixes x
  assumes "\<And> x\<^sub>1 x\<^sub>2. x = \<^bold>[[x\<^sub>1, x\<^sub>2]\<^bold>] \<Longrightarrow> P"
  shows "P"
proof -
  have "x = \<^bold>[[x 1 0, x 1 1]\<^bold>]"
    by (simp add: matrix_eq_iff nat_of_num1_def forall_2')
  thus ?thesis
    using assms by metis
qed

lemma cos_r1:
  assumes "- 1 \<le> y" "y < 1"
  shows "0 < arccos y"
proof -
  have "arccos 1 < arccos y"
    by (rule arccos_less_arccos, simp_all add: assms)
  thus ?thesis
    by simp
qed

lemma cos_r2:
  assumes "0 < x" "x \<le> 1"
  shows "arccos x * 2 < pi"
proof -
  have "arccos x < arccos 0"
    by (rule arccos_less_arccos, simp_all add: assms)
  thus ?thesis
    by simp
qed


lemma vec_2_eq_iff [simp]: "\<^bold>[[x\<^sub>1, y\<^sub>1]\<^bold>] = \<^bold>[[x\<^sub>2, y\<^sub>2]\<^bold>] \<longleftrightarrow> (x\<^sub>1 = x\<^sub>2 \<and> y\<^sub>1 = y\<^sub>2)"
  by (auto simp add: Mat_eq_iff')

lemma vec_2_eq_zero_off [simp]: "\<^bold>[[x, y]\<^bold>] = 0 \<longleftrightarrow> (x = 0 \<and> y = 0)"
  by (subst vec_simps(5) [THEN sym], simp only: vec_2_eq_iff)

subsection \<open> Angle Calculations \<close>

abbreviation "angOfVec \<equiv> vangle \<^bold>[[0::real,100]\<^bold>]"

abbreviation "\<phi>\<^sub>m\<^sub>a\<^sub>x \<equiv> pi / 3"      

definition angDiff :: "real \<Rightarrow> real \<Rightarrow> bool \<Rightarrow> real" where
"angDiff \<phi>\<^sub>A \<phi>\<^sub>B rotRestr \<equiv>
  let dphi =
  (if (abs(\<phi>\<^sub>A - \<phi>\<^sub>B) <= pi) then
    \<phi>\<^sub>A - \<phi>\<^sub>B
  else
    -sgn(\<phi>\<^sub>A - \<phi>\<^sub>B) * (2 * pi - abs(\<phi>\<^sub>A - \<phi>\<^sub>B)))
  in 
  if (rotRestr) then
    -sgn(dphi) * min(abs(dphi)) \<phi>\<^sub>m\<^sub>a\<^sub>x
  else dphi"

lemma "angOfVec (Matrix[[0,1]]) = 0" \<comment> \<open> 0 degree angOfVector \<close>
  by (simp add: vangle_def vec_norm)

lemma "angOfVec (Matrix[[1,0]]) = pi / 2" \<comment> \<open> 90 degree angOfVector \<close>
  by (simp add: vangle_def)

lemma arccos_inv_sqrt2: "arccos (1 / sqrt 2) = pi / 4"
  by (smt arccos_cos arccos_minus_1 arcsin_minus_1 arcsin_plus_arccos arctan arctan_less_pi4_pos arctan_one arctan_zero_zero cos_45 eq_divide_eq mult_cancel_left1 real_div_sqrt real_divide_square_eq)

lemma "angOfVec (Matrix[[1,1]]) = pi / 4" \<comment> \<open> 45 degree angOfVector \<close>
  by (simp add: vangle_def arccos_inv_sqrt2 vec_norm)

lemma "angDiff (pi/2) (pi/4) False = pi/4"
  by (simp add: angDiff_def)

lemma "angDiff (pi) (pi/4) False = 3 / 4 * pi"
  by (simp add: angDiff_def)

subsection \<open> AMV Constants \<close>

abbreviation "m \<equiv> 12"            \<comment> \<open> Mass \<close>
abbreviation "S \<equiv> 1.5"           \<comment> \<open> Maximum speed \<close>
abbreviation "f\<^sub>m\<^sub>a\<^sub>x \<equiv> 9 * 9.80665" \<comment> \<open> Maximum force \<close>
abbreviation "\<phi>\<^sub>\<epsilon> \<equiv> 0.001"        \<comment> \<open> Angular tolerance \<close>
abbreviation "s\<^sub>\<epsilon> \<equiv> 0.001"        \<comment> \<open> Linear tolerance \<close>

abbreviation "kp\<^sub>g\<^sub>v \<equiv> 5"
abbreviation "kp\<^sub>g\<^sub>r \<equiv> 5"

definition "(\<epsilon>::real) \<equiv> 0.1"

lemma [simp]: "\<epsilon> > 0"
  by (simp add: \<epsilon>_def)

subsection \<open> AMV State Space \<close>

text \<open> Continuous state space type. \<close>

type_synonym 'a AMVc = 
  "real vec[2] \<times> real vec[2] \<times> real vec[2] \<times> real \<times> real \<times> real \<times> 'a"

text \<open> Discrete state space type. \<close>

datatype OPMode = OCM | HCM | MOM

alphabet 'a::executable_euclidean_space AMVs = "'a AMVc hybs" +
  nextWP  :: "real vec[2]"
  obsReg  :: "(real vec[2]) set"
  rs  :: "real"
  rh :: "real"
  ft      :: "real"
  fl      :: "real"
  f       :: "real vec[2]"
  mode    :: OPMode

declare hybs.splits [alpha_splits del]
declare hybs.splits [alpha_splits]

translations
  (type) "AMVc" <= (type) "real vec[2] \<times> real vec['a] \<times> real vec['b] \<times> real \<times> real \<times> real"

text \<open> Variables as lenses. This boilerplate should be automatically generated
  in the future. \<close>

abbreviation "w\<^sub>x \<equiv> mat_lens 0 0 ;\<^sub>L nextWP"
abbreviation "w\<^sub>y \<equiv> mat_lens 0 1 ;\<^sub>L nextWP"

abbreviation p :: "real vec[2] \<Longrightarrow> 'a AMVc" where "p \<equiv> fst\<^sub>L"
abbreviation v :: "real vec[2] \<Longrightarrow> 'a AMVc" where "v \<equiv> fst\<^sub>L ;\<^sub>L snd\<^sub>L"
abbreviation a :: "real vec[2] \<Longrightarrow> 'a AMVc" where "a \<equiv> fst\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"
abbreviation \<phi> :: "real \<Longrightarrow> 'a AMVc" where "\<phi> \<equiv> fst\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"
abbreviation s :: "real \<Longrightarrow> 'a AMVc" where "s \<equiv> fst\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"
abbreviation t :: "real \<Longrightarrow> 'a AMVc" where "t \<equiv> fst\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"
abbreviation old :: "real AMVc \<Longrightarrow> real AMVc AMVc" where "old \<equiv> snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"

abbreviation p\<^sub>x :: "real \<Longrightarrow> 'a AMVc" where "p\<^sub>x \<equiv> mat_lens 0 0 ;\<^sub>L fst\<^sub>L"
abbreviation p\<^sub>y :: "real \<Longrightarrow> 'a AMVc" where "p\<^sub>y \<equiv> mat_lens 0 1 ;\<^sub>L fst\<^sub>L"

abbreviation v\<^sub>x :: "real \<Longrightarrow> 'a AMVc" where "v\<^sub>x \<equiv> mat_lens 0 0 ;\<^sub>L fst\<^sub>L ;\<^sub>L snd\<^sub>L"
abbreviation v\<^sub>y :: "real \<Longrightarrow> 'a AMVc" where "v\<^sub>y \<equiv> mat_lens 0 1 ;\<^sub>L fst\<^sub>L ;\<^sub>L snd\<^sub>L"

abbreviation a\<^sub>x :: "real \<Longrightarrow> 'a AMVc" where "a\<^sub>x \<equiv> mat_lens 0 0 ;\<^sub>L fst\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"
abbreviation a\<^sub>y :: "real \<Longrightarrow> 'a AMVc" where "a\<^sub>y \<equiv> mat_lens 0 1 ;\<^sub>L fst\<^sub>L ;\<^sub>L snd\<^sub>L ;\<^sub>L snd\<^sub>L"

abbreviation \<phi>\<^sub>A\<^sub>V :: "(real, 'a::executable_euclidean_space AMVs) uexpr" where "\<phi>\<^sub>A\<^sub>V \<equiv> U(angOfVec &\<^bold>c:v)"
abbreviation \<phi>\<^sub>W\<^sub>P :: "(real, 'a::executable_euclidean_space AMVs) uexpr" where "\<phi>\<^sub>W\<^sub>P \<equiv> U(angOfVec (&\<^bold>c:v - &nextWP))"

subsection \<open> AMV Hybrid Model \<close>

abbreviation "\<omega> \<equiv> U(arccos((v + a) \<bullet> v / (\<parallel>v + a\<parallel> * \<parallel>v\<parallel>)) \<triangleleft> \<not> \<parallel>v\<parallel> = 0 \<triangleright> 0)"

subsubsection \<open> AMV Dynamics \<close>

text \<open> Shows the derivative of each continuous variable. \<close>

abbreviation "dyn\<^sub>A\<^sub>V \<equiv>
  [ p \<mapsto>\<^sub>s v
  , v \<mapsto>\<^sub>s a
  , a \<mapsto>\<^sub>s 0
  , \<phi> \<mapsto>\<^sub>s \<omega>
  , s \<mapsto>\<^sub>s (v \<bullet> a) / s \<triangleleft> \<not> s = 0 \<triangleright> \<parallel>a\<parallel> 
  , t \<mapsto>\<^sub>s 1 
  , old \<mapsto>\<^sub>s 0 ]"

abbreviation 
  "ax\<^sub>A\<^sub>V \<equiv> U(&\<^bold>c:t < \<epsilon> \<and> &\<^bold>c:s *\<^sub>R \<^bold>[[sin(&\<^bold>c:\<phi>),cos(&\<^bold>c:\<phi>)]\<^bold>] = &\<^bold>c:v 
           \<and> 0 \<le> &\<^bold>c:s \<and> &\<^bold>c:s \<le> S)"

abbreviation "ODE \<equiv> ode dyn\<^sub>A\<^sub>V ax\<^sub>A\<^sub>V"

abbreviation "Dynamics \<equiv> \<^bold>c:t := 0 ;; ODE"

subsubsection \<open> Last Response Engine \<close>

abbreviation "steerToWP \<equiv> rh := angOfVec(nextWP - &\<^bold>c:p)" \<comment> \<open> Calculation of heading \<close>

abbreviation 
  "LRE \<equiv> ((mode = HCM) \<longrightarrow>\<^sub>r rs := 0.1 ;; steerToWP)
       \<sqinter> ((mode = OCM) \<longrightarrow>\<^sub>r II)
       \<sqinter> ((mode = MOM) \<longrightarrow>\<^sub>r 
             rs := 1 ;; 
             steerToWP ;; 
             if (\<exists> o. o \<in> obsReg \<and> \<parallel>&\<^bold>c:p - \<guillemotleft>o\<guillemotright>\<parallel> \<le> 7.5) then mode := HCM ;; rs := 0.1 fi
          )"

subsubsection \<open> Autopilot \<close>

abbreviation "AP \<equiv> 
  if \<parallel>rs - &\<^bold>c:s\<parallel> > s\<^sub>\<epsilon>
    then ft := sgn(rs - &\<^bold>c:s)*min(kp\<^sub>g\<^sub>v * \<parallel>rs - &\<^bold>c:s\<parallel>) f\<^sub>m\<^sub>a\<^sub>x
    else ft := 0 fi ;; 
  if \<parallel>rh - &\<^bold>c:\<phi>\<parallel> > \<phi>\<^sub>\<epsilon>
    then fl := sgn(rh - &\<^bold>c:\<phi>)*min(kp\<^sub>g\<^sub>r * \<parallel>rh - &\<^bold>c:\<phi>\<parallel>) f\<^sub>m\<^sub>a\<^sub>x
    else fl := 0 fi ;;
  f := fl *\<^sub>R \<^bold>[[cos(&\<^bold>c:\<phi>), sin(&\<^bold>c:\<phi>)]\<^bold>] 
     + ft *\<^sub>R \<^bold>[[sin(&\<^bold>c:\<phi>), cos(&\<^bold>c:\<phi>)]\<^bold>] ;;
  \<^bold>c:a := f /\<^sub>R m"

subsubsection \<open> AMV System \<close>

abbreviation "AUV \<equiv> (LRE ;; AP ;; Dynamics)\<^sup>\<star>"

subsection \<open> Structural Properties \<close>

lemma LRE_nmods_cont: "LRE nmods \<^bold>c"
  apply (rule nmods_via_wp, simp_all add: wp usubst unrest, rel_auto)
  using OPMode.exhaust by blast

lemma AP_nmods_pos: "AP nmods &\<^bold>c:p"
  by (simp add: closure unrest)

lemma AP_nmods_vel: "AP nmods &\<^bold>c:v"
  by (simp add: closure unrest)

lemma AP_nmods_speed: "AP nmods &\<^bold>c:s"
  by (rule nmods_via_wp, simp_all add: wp usubst, rel_simp)

lemma AP_nmods_phi: "AP nmods &\<^bold>c:\<phi>"
  by (rule nmods_via_wp, simp_all add: wp usubst, rel_simp)

lemma "AP nmods &\<^bold>c:v"
  by (simp add: closure unrest)

lemma "LRE nmods &\<^bold>c:v"
   by (simp_all add: closure unrest)

lemma axAV_LRE_inv: "\<^bold>{ax\<^sub>A\<^sub>V\<^bold>}LRE\<^bold>{ax\<^sub>A\<^sub>V\<^bold>}"
  apply (rule nmods_invariant[of _ "\<^bold>c"])
   apply (rule nmods_via_wp, simp_all add: wp usubst unrest)
  apply (rel_simp)
  using OPMode.exhaust by auto

subsection \<open> Invariants \<close>

lemma time_pos:
"\<^bold>{&\<^bold>c:t \<ge> 0\<^bold>}
  ode dyn\<^sub>A\<^sub>V U(&\<^bold>c:a = 0 \<and> &\<^bold>c:v > 0)
 \<^bold>{&\<^bold>c:t \<ge> 0\<^bold>}"
  by dInduct

lemma "\<^bold>{&\<^bold>c:s = \<parallel>&\<^bold>c:v\<parallel>\<^bold>}ODE\<^bold>{&\<^bold>c:s = \<parallel>&\<^bold>c:v\<parallel>\<^bold>}"
  by (rule dWeakening, rel_simp')
  
lemma "\<^bold>{rs = &\<^bold>c:s \<and> rh = &\<^bold>c:\<phi>\<^bold>}AP\<^bold>{&\<^bold>c:a = 0\<^bold>}"
  by (hoare_auto)

lemma AP_no_accel: "\<^bold>{&\<^bold>c:s \<in> {rs - s\<^sub>\<epsilon>..rs + s\<^sub>\<epsilon>} \<and> rh = &\<^bold>c:\<phi>\<^bold>}AP\<^bold>{&\<^bold>c:a = 0\<^bold>}"
proof -
  have "\<^bold>{\<parallel>rs - &\<^bold>c:s\<parallel> \<le> s\<^sub>\<epsilon> \<and> rh = &\<^bold>c:\<phi>\<^bold>}AP\<^bold>{&\<^bold>c:a = 0\<^bold>}"
    by (hoare_auto)
  thus ?thesis
    apply (rule hoare_r_conseq)
    apply (rel_simp')
     apply (simp add: abs_diff_le_iff[THEN sym] abs_minus_commute)
    apply (rel_simp')
    done
qed

lemma "\<^bold>{rs < &\<^bold>c:s - s\<^sub>\<epsilon> \<and> rh = &\<^bold>c:\<phi>\<^bold>}AP\<^bold>{\<parallel>&\<^bold>c:a\<parallel> > 0\<^bold>}"
  using sin_zero_abs_cos_one by (hoare_auto, fastforce)

declare vec_simps [simp del]

lemma collinear_AP: 
  "\<^bold>{&\<^bold>c:s \<ge> 0 \<and> rs \<ge> &\<^bold>c:s \<and> &\<^bold>c:v = &\<^bold>c:s *\<^sub>R \<^bold>[[sin(&\<^bold>c:\<phi>),cos(&\<^bold>c:\<phi>)]\<^bold>] \<and> \<parallel>rh - &\<^bold>c:\<phi>\<parallel> < \<phi>\<^sub>\<epsilon>\<^bold>}
   AP
   \<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel>\<^bold>}"
  by (hoare_auto)

declare vec_simps [simp]

text \<open> If the LRE is in MOM, the way point is in the north-east quadrant wrt. the AMV, and there
  are no nearby obstacles, then the LRE will stay in MOM and request maximum velocity and heading
  within the north-east quadrant. \<close>

lemma LRE_quad1_heading:
  "\<^bold>{mode = MOM \<and> w\<^sub>x > &\<^bold>c:p\<^sub>x \<and> w\<^sub>y > &\<^bold>c:p\<^sub>y \<and> (\<forall> o. o \<in> obsReg \<Rightarrow> \<parallel>&\<^bold>c:p - \<guillemotleft>o\<guillemotright>\<parallel> > 7.5)\<^bold>}
  LRE
  \<^bold>{mode = MOM \<and> rs = 1 \<and> rh \<in> {0<..<pi / 2}\<^bold>}"
  apply (hoare_auto)
   apply (rename_tac p w r)
   apply (case_tac p rule: vector_2_cases)
   apply (simp)
   apply (case_tac w rule: vector_2_cases)
   apply (simp)
   apply (auto simp add: vangle_def vec_norm)
  apply (rule cos_r1)
   apply (rename_tac x\<^sub>1 x\<^sub>2 x\<^sub>1' x\<^sub>2')
   apply (subgoal_tac "0 \<le> (100 * x\<^sub>2' - 100 * x\<^sub>2)")
  apply (subgoal_tac "0 \<le> (100 * sqrt ((x\<^sub>1' - x\<^sub>1)\<^sup>2 + (x\<^sub>2' - x\<^sub>2)\<^sup>2))")
  apply (smt divide_nonneg_nonneg mult_nonneg_nonneg norm_ge_zero vec_simps(2) vec_simps(4))
    apply (simp_all add: vec_simps)
  apply (subst divide_less_eq_1_pos)
  apply (simp_all)
  apply (simp add: sum_power2_gt_zero_iff)
  apply (smt sqrt_le_D zero_less_power)
   apply (rename_tac p w r)
   apply (case_tac p rule: vector_2_cases)
   apply (simp)
   apply (case_tac w rule: vector_2_cases)
   apply (simp)
   apply (auto simp add: vangle_def)
  apply (rule cos_r2)
    apply (simp_all add: vec_norm)
   apply (rename_tac x\<^sub>1 x\<^sub>2 x\<^sub>1' x\<^sub>2')
   apply (subgoal_tac "0 < (100 * x\<^sub>2' - 100 * x\<^sub>2)")
  apply (subgoal_tac "0 < (100 * sqrt ((x\<^sub>1' - x\<^sub>1)\<^sup>2 + (x\<^sub>2' - x\<^sub>2)\<^sup>2))")
  apply simp
  apply (simp add: power2_eq_square sum_squares_gt_zero_iff)
    apply (simp_all)
  apply (smt divide_le_eq_1_pos real_le_rsqrt zero_less_power)
  done

lemma "\<^bold>{mode = MOM \<and> (\<exists> o. o \<in> obsReg \<and> \<parallel>&\<^bold>c:p - \<guillemotleft>o\<guillemotright>\<parallel> \<le> 7.5) \<and> 
        \<parallel>angOfVec(nextWP - &\<^bold>c:p) - &\<^bold>c:\<phi>\<parallel> < \<phi>\<^sub>\<epsilon>\<^bold>}
        LRE
       \<^bold>{mode = HCM \<and> rs = 0.1 \<and> \<parallel>rh - &\<^bold>c:\<phi>\<parallel> < \<phi>\<^sub>\<epsilon>\<^bold>}"
  by (hoare_auto)

lemma 
  "\<^bold>{rs = &\<^bold>c:s \<and> &\<^bold>c:\<phi> = 0 \<and> rh = pi\<^bold>}
    AP
   \<^bold>{&\<^bold>c:a = \<^bold>[[kp\<^sub>g\<^sub>r * pi / m, 0]\<^bold>]\<^bold>}"
proof -
  have 1: "(kp\<^sub>g\<^sub>r * pi) < (1765197 / 20000)"
    by (approximation 20)
  show ?thesis 
    using 1 apply (rel_simp, simp add: min_absorb1)
    using pi_gt3 by auto
qed

lemma [usubst]: "bounded_linear (get\<^bsub>x\<^esub>) \<Longrightarrow> \<langle>\<sigma>(old \<mapsto>\<^sub>s 0)\<rangle>\<^sub>s (x ;\<^sub>L old) = 0"
  apply (rel_simp)
  using linear_simps(3) by blast

lemma "\<^bold>{&\<^bold>c:t = 0 \<and> &\<^bold>c:v = &\<^bold>c:old:v\<^bold>}ODE\<^bold>{&\<^bold>c:v = &\<^bold>c:old:v + &\<^bold>c:t *\<^sub>R &\<^bold>c:a\<^bold>}"
proof -
  have 1: "\<^bold>{&\<^bold>c:v = &\<^bold>c:old:v + &\<^bold>c:t *\<^sub>R &\<^bold>c:a\<^bold>}ODE\<^bold>{&\<^bold>c:v = &\<^bold>c:old:v + &\<^bold>c:t *\<^sub>R &\<^bold>c:a\<^bold>}"
    by (dInduct, rel_simp)
  thus ?thesis
    by (rule hoare_r_conseq) (rel_simp'+)
qed

text \<open> If the AMV is accelerating in the same direction as the velocity, then it will continue
  to do so. \<close>

lemma collinear_vector_accel:
  "\<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel>\<^bold>}
    ODE
   \<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel>\<^bold>}"
proof -
  have "\<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v \<ge> 0 \<and> (&\<^bold>c:a \<bullet> &\<^bold>c:v)\<^sup>2 = (&\<^bold>c:a \<bullet> &\<^bold>c:a) * (&\<^bold>c:v \<bullet> &\<^bold>c:v)\<^bold>}
        ODE
       \<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v \<ge> 0 \<and> (&\<^bold>c:a \<bullet> &\<^bold>c:v)\<^sup>2 = (&\<^bold>c:a \<bullet> &\<^bold>c:a) * (&\<^bold>c:v \<bullet> &\<^bold>c:v)\<^bold>}"
    apply (rule dCut_split)
    apply (dInduct)
     apply (rel_simp)
    apply (dInduct)
     apply (rel_simp)
    using inner_commute by blast
  hence "\<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v \<ge> 0 \<and> &\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel>\<^bold>}
          ODE
         \<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v \<ge> 0 \<and> &\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel>\<^bold>}"
    apply (rule hoare_r_conseq)
    apply (rel_auto')
    apply (simp add: power2_norm_eq_inner power_mult_distrib)
    apply (smt norm_eq_square power2_norm_eq_inner real_sqrt_abs real_sqrt_mult)
    done

  thus ?thesis
    by (rule hoare_r_conseq) (rel_auto')
qed

text \<open> Collinearity of the acceleration and velocity implies no rotational velocity \<close>

lemma "`&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel> \<Rightarrow> \<omega> \<oplus>\<^sub>p \<^bold>c = 0`"
  apply (rel_simp)
  apply (drule sym)
  apply (simp add: algebra_simps)
  by (smt inner_gt_zero_iff mult_nonneg_nonneg norm_ge_zero)

lemma "\<^bold>{(&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel> \<and> &\<^bold>c:s = \<parallel>&\<^bold>c:v\<parallel>) \<and> &\<^bold>c:t \<ge> 0 \<and> &\<^bold>c:t < \<epsilon> \<and> 
        &\<^bold>c:v = &\<^bold>c:t *\<^sub>R &\<^bold>c:a + &\<^bold>c:old:v \<and>
        &\<^bold>c:p = (&\<^bold>c:t\<^sup>2 * \<guillemotleft>0.5\<guillemotright>) *\<^sub>R &\<^bold>c:a + &\<^bold>c:t *\<^sub>R &\<^bold>c:old:v + &\<^bold>c:old:p\<^bold>}
        ODE
       \<^bold>{&\<^bold>c:t \<ge> 0 \<and> &\<^bold>c:t < \<epsilon> \<and> 
        &\<^bold>c:v = &\<^bold>c:t *\<^sub>R &\<^bold>c:a + &\<^bold>c:old:v \<and>
        &\<^bold>c:p = (&\<^bold>c:t\<^sup>2 * \<guillemotleft>0.5\<guillemotright>) *\<^sub>R &\<^bold>c:a + &\<^bold>c:t *\<^sub>R &\<^bold>c:old:v + &\<^bold>c:old:p\<^bold>}"
  apply (rule dCut_split')
   apply (rule dCut_split)
    apply (fact collinear_vector_accel)
   apply (rule dWeakening, rel_simp')
   apply (rule dCut_split)
   apply (dInduct)
  apply (rule dCut_split)
   apply (rule dWeakening, rel_simp')
  apply (rule dCut_split)
  apply (dInduct)
   apply (rel_simp)
  apply (dInduct)
  apply (rel_simp)
  done
  
lemma "\<^bold>{&\<^bold>c:a = 0 \<and> &\<^bold>c:v = \<guillemotleft>V\<guillemotright>\<^bold>}ODE\<^bold>{&\<^bold>c:a = 0 \<and> &\<^bold>c:v = \<guillemotleft>V\<guillemotright>\<^bold>}"
  apply (rule dCut_split)
   apply (dInduct)
  apply (dInduct)
  apply (rel_simp)
  done

declare eq_divide_eq_numeral1 [simp del]

lemma [simp]: "sqrt (1/100) = 1/10"
  by (rule real_sqrt_unique, simp_all add: field_simps)

lemma [simp]: "sqrt (9 / 64) = 0.375"
  by (rule real_sqrt_unique, simp_all add: field_simps)

text \<open> If the AMV is on course then the calculate acceleration vector is always
  collinear with the velocity vector. \<close>

lemma "\<^bold>{&\<^bold>c:s \<ge> 0 \<and> rs > &\<^bold>c:s \<and> &\<^bold>c:\<phi> = pi / 2 \<and> rh = pi / 2 
        \<and> &\<^bold>c:v = &\<^bold>c:s *\<^sub>R \<^bold>[[sin(&\<^bold>c:\<phi>),cos(&\<^bold>c:\<phi>)]\<^bold>]\<^bold>}
        AP
       \<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel>\<^bold>}"
  apply (hoare_auto)
  apply (rename_tac s rs)
  apply (simp add: vec_norm)
  done

declare vec_simps [simp del]

lemma vs1: "\<^bold>[[k * x, k * y]\<^bold>] = k *\<^sub>R \<^bold>[[x, y]\<^bold>]"
  by (simp add: vec_simps(1))

lemma "\<^bold>{&\<^bold>c:s \<ge> 0 \<and> rs > &\<^bold>c:s \<and> \<parallel>rh - &\<^bold>c:\<phi>\<parallel> < \<phi>\<^sub>\<epsilon>
        \<and> &\<^bold>c:v = &\<^bold>c:s *\<^sub>R \<^bold>[[sin(&\<^bold>c:\<phi>),cos(&\<^bold>c:\<phi>)]\<^bold>]\<^bold>}
        AP
       \<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel>\<^bold>}"
  by (hoare_auto)

text \<open> If the AMV is accelerating towards its orientation then the speed increases. \<close>

lemma 
  "\<^bold>{(&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel> \<and> (&\<^bold>c:a \<bullet> &\<^bold>c:a) > 0) \<and> &\<^bold>c:s \<ge> &\<^bold>c:old:s\<^bold>}
    ODE
   \<^bold>{&\<^bold>c:s \<ge> &\<^bold>c:old:s\<^bold>}"
  apply (rule dCut_split')
  apply (rule dCut_split)
   apply (fact collinear_vector_accel) 
   apply (dInduct)
   apply (rel_simp)
  apply (dInduct)
  apply (rel_simp)
  apply (simp add: inner_commute)
  done

lemma no_turn_no_accel:
"\<^bold>{&\<^bold>c:\<phi> = \<guillemotleft>X\<guillemotright>\<^bold>}
  ode dyn\<^sub>A\<^sub>V U(&\<^bold>c:a = 0 \<and> &\<^bold>c:v > 0)
 \<^bold>{&\<^bold>c:\<phi> = \<guillemotleft>X\<guillemotright>\<^bold>}"
  by (dInduct, rel_simp)

lemma no_turn_when_straight:
 "\<^bold>{&\<^bold>c:a \<bullet> &\<^bold>c:v = \<parallel>&\<^bold>c:a\<parallel> * \<parallel>&\<^bold>c:v\<parallel> \<and> &\<^bold>c:\<phi> = \<guillemotleft>X\<guillemotright>\<^bold>}
   ODE
  \<^bold>{&\<^bold>c:\<phi> = \<guillemotleft>X\<guillemotright>\<^bold>}"
  apply (rule dCut_split', fact collinear_vector_accel)
  apply (dInduct_auto)
  apply (smt norm_ge_zero)+
  done

text \<open> Link with CyPhyCircus. Differentiation on a domain. Unit vector d? DAEs via unknowns in ODE? \<close>


lemma [usubst]: "\<langle>\<sigma>(v \<mapsto>\<^sub>s &a)\<rangle>\<^sub>s v\<^sub>x = &a\<^sub>x"
  by (rel_simp)

lemma [usubst]: "\<langle>\<sigma>(v \<mapsto>\<^sub>s &a)\<rangle>\<^sub>s v\<^sub>y = &a\<^sub>y"
  by (rel_simp)

lemma translational_speed:
"\<^bold>{[&\<^bold>c:s\<^sup>2 =\<^sub>P (&\<^bold>c:v \<bullet> &\<^bold>c:v)]\<^sub>P\<^bold>}
  ode dyn\<^sub>A\<^sub>V U(&\<^bold>c:s \<noteq> 0)
 \<^bold>{[&\<^bold>c:s\<^sup>2 =\<^sub>P (&\<^bold>c:v \<bullet> &\<^bold>c:v)]\<^sub>P\<^bold>}"
  apply (dInduct)
  apply (rel_simp)
  apply (simp add: inner_commute)
  done

lemma translational_prop:
"\<^bold>{&\<^bold>c:s\<^sup>2 = (&\<^bold>c:v \<bullet> &\<^bold>c:v)\<^bold>}
  ode dyn\<^sub>A\<^sub>V U(&\<^bold>c:s > 0)
 \<^bold>{&\<^bold>c:s\<^sup>2 = (&\<^bold>c:v \<bullet> &\<^bold>c:v)\<^bold>}"
  by (dInduct, rel_simp, simp add: inner_commute)

lemma "`(&\<^bold>c:s > 0 \<and> [&\<^bold>c:s\<^sup>2 =\<^sub>P (&\<^bold>c:v \<bullet> &\<^bold>c:v)]\<^sub>P) \<Rightarrow> &\<^bold>c:s = \<parallel>&\<^bold>c:v\<parallel>`"
  apply (simp add: hyprop_pred_def)
  apply (rel_simp)
  by (metis less_eq_real_def norm_eq_square)

end