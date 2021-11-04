(* Copyright 2021 (C) Mihails Milehins *)

section\<open>
Construction of integer numbers, rational numbers and real numbers
\<close>
theory CZH_Sets_ZQR
  imports
    "HOL-Library.Rewrite"
    CZH_Sets_NOP
    CZH_Sets_VNHS
    HOL_CContinuum
begin



subsection\<open>Background\<close>


text\<open>

The set of real numbers \<open>\<real>\<^sub>\<circ>\<close> is defined in a way such that it agrees 
with the set of natural numbers \<^const>\<open>\<omega>\<close>. However, otherwise, 
real numbers are allowed to be arbitrary sets 
in \<^term>\<open>Vset (\<omega> + \<omega>)\<close>.\footnote{
The idea itself is not new, e.g., see \cite{chen_hotg_2021}.
}
Integer and rational numbers are exposed via canonical injections into
the set of real numbers from the types \<^typ>\<open>int\<close> and \<^typ>\<open>rat\<close>, respectively.
Lastly, common operations on the real, integer and rational numbers
are defined and some of their main properties are exposed. 

The primary reference for this section is the textbook
\<open>The Real Numbers and Real Analysis\<close> by E. Bloch
\cite{bloch_real_2010}. Nonetheless, it is not claimed that the exposition of 
the subject presented in this section is entirely congruent with the exposition
in the aforementioned reference.

\<close>

declare One_nat_def[simp del]

named_theorems vnumber_simps

lemmas [vnumber_simps] =  
  Collect_mem_eq Ball_def[symmetric] Bex_def[symmetric] vsubset_eq[symmetric]


text\<open>
Supplementary material for the evaluation of the upper bound of the
cardinality of the continuum.
\<close>

lemma inj_image_ord_of_nat: "inj (image ord_of_nat)"
  by (intro injI) (simp add: inj_image_eq_iff inj_ord_of_nat)

lemma vlepoll_VPow_omega_if_vreal_lepoll_real:
  assumes "x \<lesssim> (UNIV::real set)" 
  shows "set x \<lesssim>\<^sub>\<circ> VPow \<omega>"
proof-
  note x = assms
  also from real_lepoll_natnat have "\<dots> \<lesssim> (UNIV::nat set set)"
    unfolding Pow_UNIV by simp
  also from inj_image_ord_of_nat have "\<dots> \<lesssim> Pow (elts \<omega>)"
    unfolding lepoll_def by auto
  also from down have "\<dots> \<lesssim> elts (VPow \<omega>)"
    unfolding lepoll_def
    by (intro exI[of _ set] conjI inj_onI) (auto simp: elts_VPow)
  finally show "set x \<lesssim>\<^sub>\<circ> VPow \<omega>" by simp
qed



subsection\<open>Real numbers\<close>


subsubsection\<open>Definition\<close>

abbreviation real :: "nat \<Rightarrow> real"
  where "real \<equiv> of_nat"

definition nat_of_real :: "real \<Rightarrow> nat"
  where "nat_of_real = inv_into UNIV real"

definition vreal_of_real_impl :: "real \<Rightarrow> V"
  where "vreal_of_real_impl = (SOME V_of::real\<Rightarrow>V. inj V_of)"

lemma inj_vreal_of_real_impl: "inj vreal_of_real_impl" 
  unfolding vreal_of_real_impl_def 
  by (metis embeddable_class.ex_inj verit_sko_ex')

lemma inj_on_inv_vreal_of_real_impl: 
  "inj_on (inv vreal_of_real_impl) (range vreal_of_real_impl)"
  by (intro inj_onI) (fastforce intro: inv_into_injective)

lemma range_vreal_of_real_impl_vlepoll_VPow_omega: 
  "set (range vreal_of_real_impl) \<lesssim>\<^sub>\<circ> VPow \<omega>"
proof-
  have "range vreal_of_real_impl \<lesssim> (UNIV::real set)"
    unfolding lepoll_def by (auto intro: inj_on_inv_vreal_of_real_impl)
  from vlepoll_VPow_omega_if_vreal_lepoll_real[OF this] show ?thesis .
qed

definition vreal_impl :: V
  where "vreal_impl =
    (
      SOME y. 
        range vreal_of_real_impl \<approx> elts y \<and>
        vdisjnt y \<omega> \<and>
        y \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)
    )"

lemma vreal_impl_eqpoll: "range vreal_of_real_impl \<approx> elts vreal_impl" 
  and vreal_impl_vdisjnt: "vdisjnt vreal_impl \<omega>"
  and vreal_impl_in_Vset_ss_omega: "vreal_impl \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
proof-
  from Ord_\<omega> have VPow_in_Vset: "VPow \<omega> \<in>\<^sub>\<circ> Vset (succ (succ \<omega>))"
    by (intro Ord_VPow_in_Vset_succI) 
      (auto simp: less_TC_succ Ord_iff_rank VsetI)
  have [simp]: "small (range vreal_of_real_impl)" by simp
  then obtain x where x: "range vreal_of_real_impl = elts x"
    unfolding small_iff by clarsimp
  from range_vreal_of_real_impl_vlepoll_VPow_omega[unfolded x] have 
    "x \<lesssim>\<^sub>\<circ> VPow \<omega>" 
    by simp
  then obtain f where "v11 f" and "\<D>\<^sub>\<circ> f = x" and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> VPow \<omega>" by auto
  moreover have O\<omega>2: "Ord (succ (succ \<omega>))" by auto
  ultimately have x_Rf: "x \<approx>\<^sub>\<circ> \<R>\<^sub>\<circ> f" and "\<R>\<^sub>\<circ> f \<in>\<^sub>\<circ> Vset (succ (succ \<omega>))"
    by (auto intro: VPow_in_Vset)
  then have "\<omega> \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> f \<in>\<^sub>\<circ> Vset (succ (succ \<omega>))" and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> \<omega> \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
    by (auto simp: VPow_in_Vset VPow_in_Vset_revD vunion_in_VsetI)
  from Ord_ex_eqpoll_vdisjnt[OF O\<omega>2 this(2,1)] obtain z
    where Rf_z: "\<R>\<^sub>\<circ> f \<approx>\<^sub>\<circ> z" 
      and "vdisjnt z (\<omega> \<union>\<^sub>\<circ> \<R>\<^sub>\<circ> f)"
      and z: "z \<subseteq>\<^sub>\<circ> Vset (succ (succ (succ \<omega>)))"
    by auto
  then have vdisjnt_z\<omega>: "vdisjnt z \<omega>" 
    and z_ssss\<omega>: "z \<in>\<^sub>\<circ> Vset (succ (succ (succ (succ \<omega>))))"    
    by 
      (
        auto simp: 
          vdisjnt_vunion_right vsubset_in_VsetI Ord_succ Ord_Vset_in_Vset_succI
      )
  have "Limit (\<omega> + \<omega>)" by simp
  then have "succ (succ (succ (succ \<omega>))) \<in>\<^sub>\<circ> \<omega> + \<omega>"
    by (metis Limit_def add.right_neutral add_mem_right_cancel Limit_omega)
  then have "Vset (succ (succ (succ (succ \<omega>)))) \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
    by (simp add: Vset_in_mono)
  with z z_ssss\<omega> have "z \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)" by auto
  moreover from x_Rf Rf_z have "range vreal_of_real_impl \<approx> elts z"
    unfolding x by (auto intro: eqpoll_trans)
  ultimately show "range vreal_of_real_impl \<approx> elts vreal_impl" 
    and "vdisjnt vreal_impl \<omega>"
    and "vreal_impl \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
    using vdisjnt_z\<omega> 
    unfolding vreal_impl_def
    by (metis (mono_tags, lifting) verit_sko_ex')+
qed

definition vreal_of_real_impl' :: "V \<Rightarrow> V"
  where "vreal_of_real_impl' = 
    (SOME f. bij_betw f (range vreal_of_real_impl) (elts vreal_impl))"

lemma vreal_of_real_impl'_bij_betw: 
  "bij_betw vreal_of_real_impl' (range vreal_of_real_impl) (elts vreal_impl)"
proof-
  from eqpoll_def obtain f where f: 
    "bij_betw f (range vreal_of_real_impl) (elts vreal_impl)"
    by (auto intro: vreal_impl_eqpoll)
  then show ?thesis unfolding vreal_of_real_impl'_def by (metis verit_sko_ex')
qed

definition vreal_of_real_impl'' :: "real \<Rightarrow> V"
  where "vreal_of_real_impl'' = vreal_of_real_impl' \<circ> vreal_of_real_impl"

lemma vreal_of_real_impl'': "disjnt (range vreal_of_real_impl'') (elts \<omega>)"
proof-
  from comp_apply vreal_impl_vdisjnt vreal_of_real_impl'_bij_betw have 
    "vreal_of_real_impl'' y \<notin>\<^sub>\<circ> \<omega>" for y
    unfolding vreal_of_real_impl''_def by fastforce
  then show ?thesis unfolding disjnt_iff by clarsimp
qed

lemma inj_vreal_of_real_impl'': "inj vreal_of_real_impl''"
  unfolding vreal_of_real_impl''_def 
  by 
    (
      meson 
        bij_betwE 
        comp_inj_on 
        inj_vreal_of_real_impl 
        vreal_of_real_impl'_bij_betw
    )


text\<open>Main definitions.\<close>

definition vreal_of_real :: "real \<Rightarrow> V"
  where "vreal_of_real x = 
    (if x \<in> \<nat> then (nat_of_real x)\<^sub>\<nat> else vreal_of_real_impl'' x)"

notation vreal_of_real (\<open>_\<^sub>\<real>\<close> [1000] 999)

declare [[coercion "vreal_of_real :: real \<Rightarrow> V"]]

definition vreal :: V (\<open>\<real>\<^sub>\<circ>\<close>)
  where "vreal = set (range vreal_of_real)"

definition real_of_vreal :: "V \<Rightarrow> real"
  where "real_of_vreal = inv_into UNIV vreal_of_real"


text\<open>Rules.\<close>

lemma vreal_of_real_in_vrealI[intro, simp]: "a\<^sub>\<real> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
  by (simp add: vreal_def)

lemma vreal_of_real_in_vrealE[elim]:
  assumes "a \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  obtains b where "b\<^sub>\<real> = a"
  using assms unfolding vreal_def by auto


text\<open>Elementary properties.\<close>

lemma vnat_eq_vreal: "x\<^sub>\<nat> = x\<^sub>\<real>" by (simp add: nat_of_real_def vreal_of_real_def)

lemma omega_vsubset_vreal: "\<omega> \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ>"
proof
  fix x assume "x \<in>\<^sub>\<circ> \<omega>"
  with nat_of_omega obtain y where x_def: "x = y\<^sub>\<nat>" by auto
  then have "vreal_of_real (real y) = (nat_of_real (real y))\<^sub>\<nat>" 
    unfolding vreal_of_real_def by simp
  moreover have "(nat_of_real (real y))\<^sub>\<nat> = x"
    by (simp add: nat_of_real_def x_def)
  ultimately show "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" unfolding vreal_def by clarsimp
qed

lemma inj_vreal_of_real: "inj vreal_of_real"
proof
  fix x y assume prems: "vreal_of_real x = vreal_of_real y"
  consider 
    (xy) \<open>x \<in> \<nat> \<and> y \<in> \<nat>\<close> | 
    (x_ny) \<open>x \<in> \<nat> \<and> y \<notin> \<nat>\<close> | 
    (nx_y) \<open>x \<notin> \<nat> \<and> y \<in> \<nat>\<close> | 
    (nxy) \<open>x \<notin> \<nat> \<and> y \<notin> \<nat>\<close>  
    by auto 
  then show "x = y"
  proof cases
    case xy
    then have "(nat_of_real x)\<^sub>\<nat> = (nat_of_real y)\<^sub>\<nat>"
      using vreal_of_real_def prems by simp
    then show ?thesis
      by (metis Nats_def f_inv_into_f nat_of_real_def ord_of_nat_inject xy)
  next
    case x_ny
    with prems have eq: "(nat_of_real x)\<^sub>\<nat> = vreal_of_real_impl'' y"
      unfolding vreal_of_real_def by simp
    have "vreal_of_real_impl'' y \<notin>\<^sub>\<circ> \<omega>"
      by (meson disjnt_iff rangeI vreal_of_real_impl'')
    then show ?thesis unfolding eq[symmetric] by auto
  next
    case nx_y
    with prems have eq: "(nat_of_real y)\<^sub>\<nat> = vreal_of_real_impl'' x"
      unfolding vreal_of_real_def by simp
    have "vreal_of_real_impl'' x \<notin>\<^sub>\<circ> \<omega>"
      by (meson disjnt_iff rangeI vreal_of_real_impl'')
    then show ?thesis unfolding eq[symmetric] by auto
  next
    case nxy
    then have "x \<notin> \<nat>" and "y \<notin> \<nat>" by auto
    with prems 
    have "vreal_of_real_impl'' x = vreal_of_real_impl'' y"
      unfolding vreal_of_real_def by simp
    then show ?thesis by (meson inj_def inj_vreal_of_real_impl'')
  qed
qed

lemma vreal_in_Vset_\<omega>2: "\<real>\<^sub>\<circ> \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
  unfolding vreal_def
proof-
  have "set (range vreal_of_real) \<subseteq>\<^sub>\<circ> set (range vreal_of_real_impl'') \<union>\<^sub>\<circ> \<omega>"
    unfolding vreal_of_real_def by auto
  moreover from vreal_of_real_impl'_bij_betw have 
    "set (range vreal_of_real_impl'') \<subseteq>\<^sub>\<circ> vreal_impl"
    unfolding vreal_of_real_impl''_def by fastforce
  ultimately show "set (range vreal_of_real) \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
    using Ord_\<omega> Ord_add 
    by 
      ( 
        auto simp: 
          Ord_iff_rank 
          Ord_VsetI
          vreal_impl_in_Vset_ss_omega 
          vsubset_in_VsetI 
          vunion_in_VsetI
      )
qed

lemma real_of_vreal_vreal_of_real[simp]: "real_of_vreal (a\<^sub>\<real>) = a"
  by (simp add: inj_vreal_of_real real_of_vreal_def)


subsubsection\<open>Transfer rules\<close>

definition cr_vreal :: "V \<Rightarrow> real \<Rightarrow> bool"
  where "cr_vreal a b \<longleftrightarrow> (a = vreal_of_real b)"

lemma cr_vreal_right_total[transfer_rule]: "right_total cr_vreal"
  unfolding cr_vreal_def right_total_def by simp

lemma cr_vreal_bi_uniqie[transfer_rule]: "bi_unique cr_vreal"
  unfolding cr_vreal_def bi_unique_def
  by (simp add: inj_eq inj_vreal_of_real)

lemma cr_vreal_transfer_domain_rule[transfer_domain_rule]: 
  "Domainp cr_vreal = (\<lambda>x. x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>)"
  unfolding cr_vreal_def by force

lemma vreal_transfer[transfer_rule]: 
  "(rel_set cr_vreal) (elts \<real>\<^sub>\<circ>) (UNIV::real set)"
  unfolding cr_vreal_def rel_set_def by auto

lemma vreal_of_real_transfer[transfer_rule]: "cr_vreal (vreal_of_real a) a"
  unfolding cr_vreal_def by auto


subsubsection\<open>Constants and operations\<close>


text\<open>Auxiliary.\<close>

lemma vreal_fsingleton_in_fproduct_vreal: "[a\<^sub>\<real>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 1\<^sub>\<nat>" by auto

lemma vreal_fpair_in_fproduct_vreal: "[a\<^sub>\<real>, b\<^sub>\<real>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" by force


text\<open>Zero.\<close>

lemma vreal_zero: "0\<^sub>\<real> = (0::V)" 
  by (simp add: ord_of_nat_vempty vnat_eq_vreal)


text\<open>One.\<close>

lemma vreal_one: "1\<^sub>\<real> = (1::V)" 
  by (simp add: ord_of_nat_vone vnat_eq_vreal)


text\<open>Addition.\<close>

definition vreal_plus :: V 
  where "vreal_plus = 
    (\<lambda>x\<in>\<^sub>\<circ>\<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (real_of_vreal (x\<lparr>0\<^sub>\<nat>\<rparr>) + real_of_vreal (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<real>)"

abbreviation vreal_plus_app :: "V \<Rightarrow> V \<Rightarrow> V" (infixl "+\<^sub>\<real>" 65)
  where "vreal_plus_app a b \<equiv> vreal_plus\<lparr>a, b\<rparr>\<^sub>\<bullet>"
notation vreal_plus_app (infixl "+\<^sub>\<real>" 65)

lemma vreal_plus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vreal ===> cr_vreal ===> cr_vreal) 
    (+\<^sub>\<real>) (+)"
  using vreal_fpair_in_fproduct_vreal 
  by (intro rel_funI, unfold vreal_plus_def cr_vreal_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Multiplication.\<close>

definition vreal_mult :: V 
  where "vreal_mult = 
    (\<lambda>x\<in>\<^sub>\<circ>\<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (real_of_vreal (x\<lparr>0\<^sub>\<nat>\<rparr>) * real_of_vreal (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<real>)"

abbreviation vreal_mult_app (infixl "*\<^sub>\<real>" 70) 
  where "vreal_mult_app a b \<equiv> vreal_mult\<lparr>a, b\<rparr>\<^sub>\<bullet>"
notation vreal_mult_app (infixl "*\<^sub>\<real>" 70)

lemma vreal_mult_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vreal ===> cr_vreal ===> cr_vreal) (*\<^sub>\<real>) (*)"
  using vreal_fpair_in_fproduct_vreal 
  by (intro rel_funI, unfold vreal_mult_def cr_vreal_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Unary minus.\<close>

definition vreal_uminus :: V 
  where "vreal_uminus = (\<lambda>x\<in>\<^sub>\<circ>\<real>\<^sub>\<circ>. (uminus (real_of_vreal x))\<^sub>\<real>)"

abbreviation vreal_uminus_app (\<open>-\<^sub>\<real> _\<close> [81] 80) 
  where "-\<^sub>\<real> a \<equiv> vreal_uminus\<lparr>a\<rparr>"

lemma vreal_uminus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vreal ===> cr_vreal) (vreal_uminus_app) (uminus)"
  using vreal_fsingleton_in_fproduct_vreal
  by (intro rel_funI, unfold vreal_uminus_def cr_vreal_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Multiplicative inverse.\<close>

definition vreal_inverse :: V 
  where "vreal_inverse = (\<lambda>x\<in>\<^sub>\<circ>\<real>\<^sub>\<circ>. (inverse (real_of_vreal x))\<^sub>\<real>)"

abbreviation vreal_inverse_app (\<open>(_\<inverse>\<^sub>\<real>)\<close> [1000] 999) 
  where "a\<inverse>\<^sub>\<real> \<equiv> vreal_inverse\<lparr>a\<rparr>"

lemma vreal_inverse_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vreal ===> cr_vreal) (vreal_inverse_app) (inverse)"
  using vreal_fsingleton_in_fproduct_vreal 
  by (intro rel_funI, unfold vreal_inverse_def cr_vreal_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Order.\<close>

definition vreal_le :: V 
  where "vreal_le =
    set {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> real_of_vreal a \<le> real_of_vreal b}"

abbreviation vreal_le' (\<open>(_/ \<le>\<^sub>\<real> _)\<close>  [51, 51] 50)
  where "a \<le>\<^sub>\<real> b \<equiv> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> vreal_le"

lemma small_vreal_le[simp]: 
  "small 
    {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> real_of_vreal a \<le> real_of_vreal b}"
proof-
  have small: "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>}" by simp
  show ?thesis by (rule smaller_than_small[OF small]) auto
qed

lemma vreal_le_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(cr_vreal ===> cr_vreal ===> (=)) vreal_le' (\<le>)"
  using vreal_fsingleton_in_fproduct_vreal 
  by (intro rel_funI, unfold cr_scalar_def cr_vreal_def vreal_le_def)
    (auto simp: nat_omega_simps)


text\<open>Strict order.\<close>

definition vreal_ls :: V 
  where "vreal_ls =
    set {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> real_of_vreal a < real_of_vreal b}"

abbreviation vreal_ls' (\<open>(_/ <\<^sub>\<real> _)\<close> [51, 51] 50)
  where "a <\<^sub>\<real> b \<equiv> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> vreal_ls"

lemma small_vreal_ls[simp]: 
  "small 
    {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> real_of_vreal a < real_of_vreal b}"
proof-
  have small: "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>}" by simp
  show ?thesis by (rule smaller_than_small[OF small]) auto
qed

lemma vreal_ls_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(cr_vreal ===> cr_vreal ===> (=)) vreal_ls' (<)"
  by (intro rel_funI, unfold cr_scalar_def cr_vreal_def vreal_ls_def)
    (auto simp: nat_omega_simps)
  

text\<open>Subtraction.\<close>

definition vreal_minus :: V 
  where "vreal_minus =
    (\<lambda>x\<in>\<^sub>\<circ>\<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (real_of_vreal (x\<lparr>0\<^sub>\<nat>\<rparr>) - real_of_vreal (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<real>)"

abbreviation vreal_minus_app (infixl "-\<^sub>\<real>" 65) 
  where "vreal_minus_app a b \<equiv> vreal_minus\<lparr>a, b\<rparr>\<^sub>\<bullet>"

lemma vreal_minus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vreal ===> cr_vreal ===> cr_vreal) (-\<^sub>\<real>) (-)"
  using vreal_fpair_in_fproduct_vreal 
  by (intro rel_funI, unfold vreal_minus_def cr_vreal_def cr_scalar_def) 
    (simp add: nat_omega_simps)


subsubsection\<open>Axioms of an ordered field with the least upper bound property.\<close>


text\<open>
The exposition follows the Definitions 2.2.1 and 2.2.3 from 
the textbook \<open>The Real Numbers and Real Analysis\<close> by E. Bloch
\cite{bloch_real_2010}.
\<close>

lemma vreal_zero_closed: "0\<^sub>\<real> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
proof-
  have "(0::real) \<in> UNIV" by simp
  from this[untransferred] show ?thesis.
qed

lemma vreal_one_closed: "1\<^sub>\<real> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
proof-
  have "(1::real) \<in> UNIV" by simp
  from this[untransferred] show ?thesis.
qed

lemma vreal_plus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
  shows "x +\<^sub>\<real> y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
proof-
  have "x' + y' \<in> UNIV" for x' y' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vreal_uminus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "-\<^sub>\<real> x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
proof-
  have "-x' \<in> UNIV" for x' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vreal_mult_closed:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
  shows "x *\<^sub>\<real> y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
proof-
  have "x' * y' \<in> UNIV" for x' y' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vreal_inverse_closed: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "x\<inverse>\<^sub>\<real> \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
proof-    
  have "inverse x' \<in> UNIV" for x' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Associative Law for Addition: Definition 2.2.1.a.\<close>

lemma vreal_assoc_law_addition: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
  shows "(x +\<^sub>\<real> y) +\<^sub>\<real> z = x +\<^sub>\<real> (y +\<^sub>\<real> z)"
proof-
  have "(x' + y') + z' = x' + (y' + z')" for x' y' z' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Commutative Law for Addition: Definition 2.2.1.b.\<close>

lemma vreal_commutative_law_addition:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
  shows "x +\<^sub>\<real> y = y +\<^sub>\<real> x"
proof-
  have "(x' + y') = y' + x' " for x' y' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Identity Law for Addition: Definition 2.2.1.c.\<close>

lemma vreal_identity_law_addition:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "x +\<^sub>\<real> 0\<^sub>\<real> = x"
proof-
  have "x' + 0 = x'" for x' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Inverses Law for Addition: Definition 2.2.1.d.\<close>

lemma vreal_inverses_law_addition:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "x +\<^sub>\<real> (-\<^sub>\<real> x) = 0\<^sub>\<real>"
proof-
  have "x' + (-x') = 0" for x' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Associative Law for Multiplication: Definition 2.2.1.e.\<close>

lemma vreal_assoc_law_multiplication: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "(x *\<^sub>\<real> y) *\<^sub>\<real> z = x *\<^sub>\<real> (y *\<^sub>\<real> z)"
proof-
  have "(x' * y') * z' = x' * (y' * z')" for x' y' z' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Commutative Law for Multiplication: Definition 2.2.1.f.\<close>

lemma vreal_commutative_law_multiplication:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
  shows "x *\<^sub>\<real> y = y *\<^sub>\<real> x"
proof-
  have "(x' * y') = y' * x' " for x' y' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Identity Law for Multiplication: Definition 2.2.1.g.\<close>

lemma vreal_identity_law_multiplication:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "x *\<^sub>\<real> 1\<^sub>\<real> = x"
proof-
  have "x' * 1 = x'" for x' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Inverses Law for Multiplication: Definition 2.2.1.h.\<close>

lemma vreal_inverses_law_multiplication:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "x \<noteq> 0\<^sub>\<real>" 
  shows "x *\<^sub>\<real> x\<inverse>\<^sub>\<real> = 1\<^sub>\<real>"
proof-
  have "x' \<noteq> 0 \<Longrightarrow> x' * inverse x' = 1" for x' :: real by simp  
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Distributive Law: Definition 2.2.1.i.\<close>

lemma vreal_distributive_law:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "x *\<^sub>\<real> (y +\<^sub>\<real> z) = x *\<^sub>\<real> y +\<^sub>\<real> x *\<^sub>\<real> z"
proof-
  have "x' * (y' + z') = (x' * y') + (x' * z')" for x' y' z' :: real 
    by (simp add: field_simps)
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Trichotomy Law: Definition 2.2.1.j.\<close>

lemma vreal_trichotomy_law:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows 
    "(x <\<^sub>\<real> y \<and> ~(x = y) \<and> ~(y <\<^sub>\<real> x)) \<or> 
    (~(x <\<^sub>\<real> y) \<and> x = y \<and> ~(y <\<^sub>\<real> x)) \<or>
    (~(x <\<^sub>\<real> y) \<and> ~(x = y) \<and> y <\<^sub>\<real> x)"
proof-
  have "(x' < y' \<and> ~(x' = y') \<and> ~(y' < x')) \<or> 
    (~(x' < y') \<and> x' = y' \<and> ~(y' < x')) \<or>
    (~(x' < y') \<and> ~(x' = y') \<and> y' < x')"
    for x' y' z' :: real 
    by auto
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Transitive Law: Definition 2.2.1.k.\<close>

lemma vreal_transitive_law:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
    and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
    and "z \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
    and "x <\<^sub>\<real> y" and "y <\<^sub>\<real> z"
  shows "x <\<^sub>\<real> z"
proof-
  have "x' < y' \<Longrightarrow> y' < z' \<Longrightarrow> x' < z'" for x' y' z' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Addition Law of Order: Definition 2.2.1.l.\<close>

lemma vreal_addition_law_of_order:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "x <\<^sub>\<real> y"
  shows "x +\<^sub>\<real> z <\<^sub>\<real> y +\<^sub>\<real> z"
proof-
  have "x' < y' \<Longrightarrow> x' + z' < y' + z'" for x' y' z' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Multiplication Law of Order: Definition 2.2.1.m.\<close>

lemma vreal_multiplication_law_of_order:
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
    and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
    and "z \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
    and "x <\<^sub>\<real> y" 
    and "0\<^sub>\<real> <\<^sub>\<real> z"
  shows "x *\<^sub>\<real> z <\<^sub>\<real> y *\<^sub>\<real> z"
proof-
  have "x' < y' \<Longrightarrow> 0 < z' \<Longrightarrow> x' * z' < y' * z'" for x' y' z' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Non-Triviality: Definition 2.2.1.n.\<close>

lemma vreal_non_triviality: "0\<^sub>\<real> \<noteq> 1\<^sub>\<real>"
proof-
  have "0 \<noteq> (1::real)" by simp
  from this[untransferred] show ?thesis.
qed


text\<open>Least upper bound property: Definition 2.2.3.\<close>

lemma least_upper_bound_property:
  defines "vreal_ub S M \<equiv> (S \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ> \<and> M \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> \<and> (\<forall>x\<in>\<^sub>\<circ>S. x \<le>\<^sub>\<real> M))"
  assumes "A \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "A \<noteq> 0" and "\<exists>M. vreal_ub A M"
  obtains M where "vreal_ub A M" and "\<And>T. vreal_ub A T \<Longrightarrow> M \<le>\<^sub>\<real> T"
proof-
  note complete_real = 
    complete_real[
      untransferred, of \<open>elts A\<close>, unfolded vnumber_simps, OF assms(2)
      ]
  from assms obtain x where "x \<in>\<^sub>\<circ> A" by force
  moreover with assms have "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" by auto
  ultimately have 1: "\<exists>x\<in>\<^sub>\<circ>\<real>\<^sub>\<circ>. x \<in>\<^sub>\<circ> A" by auto
  from assms have 2: "\<exists>x\<in>\<^sub>\<circ>\<real>\<^sub>\<circ>. \<forall>y\<in>\<^sub>\<circ>A. y \<le>\<^sub>\<real> x" by auto
  from complete_real[OF 1 2] 
    obtain M
      where "M \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
        and "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<le>\<^sub>\<real> M" 
        and [simp]: "\<And>T. T \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> \<Longrightarrow> (\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> x \<le>\<^sub>\<real> T) \<Longrightarrow> M \<le>\<^sub>\<real> T"
    by force
  with assms(2) have "vreal_ub A M" unfolding vreal_ub_def by simp
  moreover have "vreal_ub A T \<Longrightarrow> M \<le>\<^sub>\<real> T" for T unfolding vreal_ub_def by simp
  ultimately show ?thesis using that by auto
qed


subsubsection\<open>Fundamental properties of other operations\<close>


text\<open>Minus.\<close>

lemma vreal_minus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "x -\<^sub>\<real> y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
proof-
  have "x' - y' \<in> UNIV" for x' y' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vreal_minus_eq_plus_uminus: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  shows "x -\<^sub>\<real> y = x +\<^sub>\<real> (-\<^sub>\<real> y)"
proof-
  have "x' - y' = x' + (-y')" for x' y' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Unary minus.\<close>

lemma vreal_uminus_uminus: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
  shows "x = -\<^sub>\<real> (-\<^sub>\<real> x)"
proof-
  have "x' = -(-x')" for x' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Multiplicative inverse.\<close>

lemma vreal_inverse_inverse: 
  assumes "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
  shows "x = (x\<inverse>\<^sub>\<real>)\<inverse>\<^sub>\<real>"
proof-
  have "x' = inverse (inverse x')" for x' :: real by simp
  from this[untransferred, OF assms] show ?thesis.
qed


subsubsection\<open>Further properties\<close>


text\<open>Addition.\<close>

global_interpretation vreal_plus: binop_onto \<open>\<real>\<^sub>\<circ>\<close> vreal_plus
proof-
  have binop: "binop \<real>\<^sub>\<circ> vreal_plus"
  proof(intro binopI nopI)
    show vsv: "vsv vreal_plus" unfolding vreal_plus_def by auto
    interpret vsv vreal_plus by (rule vsv)
    show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
    show dom: "\<D>\<^sub>\<circ> vreal_plus = \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" unfolding vreal_plus_def by simp
    show "\<R>\<^sub>\<circ> vreal_plus \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ>"
    proof(intro vsubsetI)
      fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_plus"
      then obtain ab where "ab \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" and y_def: "y = vreal_plus\<lparr>ab\<rparr>" 
        unfolding dom[symmetric] by force
      then obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
        by blast
      then show "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" by (simp add: vreal_plus_closed y_def)
    qed
  qed
  interpret binop \<open>\<real>\<^sub>\<circ>\<close> vreal_plus by (rule binop)
  show "binop_onto \<real>\<^sub>\<circ> vreal_plus"
  proof(intro binop_ontoI')
    show "binop \<real>\<^sub>\<circ> vreal_plus" by (rule binop_axioms)
    show "\<real>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_plus"
    proof(intro vsubsetI)
      fix y assume prems: "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
      moreover from vreal_zero vreal_zero_closed have "0 \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" by auto
      ultimately have "y +\<^sub>\<real> 0 \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_plus" by auto
      moreover from prems vreal_identity_law_addition have "y = y +\<^sub>\<real> 0" 
        by (simp add: vreal_zero)
      ultimately show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_plus" by simp
    qed
  qed
qed


text\<open>Unary minus.\<close>

global_interpretation vreal_uminus: v11 vreal_uminus
  rewrites "\<D>\<^sub>\<circ> vreal_uminus = \<real>\<^sub>\<circ>"
    and "\<R>\<^sub>\<circ> vreal_uminus = \<real>\<^sub>\<circ>"
proof-
  show v11: "v11 vreal_uminus" 
  proof(intro v11I)
    show vsv: "vsv vreal_uminus" unfolding vreal_uminus_def by simp
    interpret vsv vreal_uminus by (rule vsv)
    show "vsv (vreal_uminus\<inverse>\<^sub>\<circ>)"
    proof(intro vsvI)
      show "vbrelation (vreal_uminus\<inverse>\<^sub>\<circ>)" by clarsimp
      fix a b c
      assume prems: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vreal_uminus\<inverse>\<^sub>\<circ>" "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> vreal_uminus\<inverse>\<^sub>\<circ>"
      then have ba: "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> vreal_uminus" and ca: "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> vreal_uminus" 
        by auto
      then have b: "b \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and c: "c \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
        by (simp_all add: VLambda_iff2 vreal_uminus_def)
      from ba ca have "a = -\<^sub>\<real> b" "a = -\<^sub>\<real> c" by simp_all
      with ba ca b c show "b = c"  by (metis vreal_uminus_uminus)
    qed
  qed
  interpret v11 vreal_uminus by (rule v11)
  show dom: "\<D>\<^sub>\<circ> vreal_uminus = \<real>\<^sub>\<circ>" unfolding vreal_uminus_def by simp
  have "\<R>\<^sub>\<circ> vreal_uminus \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  proof(intro vsubsetI)
    fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_uminus"
    then obtain x where "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and y_def: "y = -\<^sub>\<real> x" 
      unfolding dom[symmetric] by force
    then show "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" by (simp add: vreal_uminus_closed)
  qed
  moreover have "\<real>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_uminus"
    by (intro vsubsetI) 
      (metis dom vdomain_atD vreal_uminus_closed vreal_uminus_uminus)
  ultimately show "\<R>\<^sub>\<circ> vreal_uminus = \<real>\<^sub>\<circ>" by simp
qed


text\<open>Multiplication.\<close>

global_interpretation vreal_mult: binop_onto \<open>\<real>\<^sub>\<circ>\<close> vreal_mult
proof-
  have binop: "binop \<real>\<^sub>\<circ> vreal_mult"
  proof(intro binopI nopI)
    show vsv: "vsv vreal_mult" unfolding vreal_mult_def by auto
    interpret vsv vreal_mult by (rule vsv)
    show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
    show dom: "\<D>\<^sub>\<circ> vreal_mult = \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" unfolding vreal_mult_def by simp
    show "\<R>\<^sub>\<circ> vreal_mult \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ>"
    proof(intro vsubsetI)
      fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_mult"
      then obtain ab where "ab \<in>\<^sub>\<circ> \<real>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" and y_def: "y = vreal_mult\<lparr>ab\<rparr>" 
        unfolding dom[symmetric] by force
      then obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
        by blast
      then show "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" by (simp add: vreal_mult_closed y_def)
    qed
  qed
  interpret binop \<open>\<real>\<^sub>\<circ>\<close> vreal_mult by (rule binop)
  show "binop_onto \<real>\<^sub>\<circ> vreal_mult"
  proof(intro binop_ontoI')
    show "binop \<real>\<^sub>\<circ> vreal_mult" by (rule binop_axioms)
    show "\<real>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_mult"
    proof(intro vsubsetI)
      fix y assume prems: "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>"
      moreover from vreal_one vreal_one_closed have "1 \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" by auto
      ultimately have "y *\<^sub>\<real> 1 \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_mult" by auto
      moreover from prems vreal_identity_law_multiplication have "y = y *\<^sub>\<real> 1" 
        by (simp add: vreal_one)
      ultimately show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_mult" by simp
    qed
  qed
qed


text\<open>Multiplicative inverse.\<close>

global_interpretation vreal_inverse: v11 vreal_inverse
  rewrites "\<D>\<^sub>\<circ> vreal_inverse = \<real>\<^sub>\<circ>"
    and "\<R>\<^sub>\<circ> vreal_inverse = \<real>\<^sub>\<circ>"
proof-
  show v11: "v11 vreal_inverse" 
  proof(intro v11I)
    show vsv: "vsv vreal_inverse" unfolding vreal_inverse_def by simp
    interpret vsv vreal_inverse by (rule vsv)
    show "vsv (vreal_inverse\<inverse>\<^sub>\<circ>)"
    proof(intro vsvI)
      show "vbrelation (vreal_inverse\<inverse>\<^sub>\<circ>)" by clarsimp
      fix a b c
      assume prems: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vreal_inverse\<inverse>\<^sub>\<circ>" "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> vreal_inverse\<inverse>\<^sub>\<circ>"
      then have ba: "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> vreal_inverse" and ca: "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> vreal_inverse" 
        by auto
      then have b: "b \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and c: "c \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" 
        by (simp_all add: VLambda_iff2 vreal_inverse_def)
      from ba ca have "a = b\<inverse>\<^sub>\<real>" "a = c\<inverse>\<^sub>\<real>" by simp_all
      with ba ca b c show "b = c"  by (metis vreal_inverse_inverse)
    qed
  qed
  interpret v11 vreal_inverse by (rule v11)
  show dom: "\<D>\<^sub>\<circ> vreal_inverse = \<real>\<^sub>\<circ>" unfolding vreal_inverse_def by simp
  have "\<R>\<^sub>\<circ> vreal_inverse \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  proof(intro vsubsetI)
    fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_inverse"
    then obtain x where "x \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" and y_def: "y = x\<inverse>\<^sub>\<real>" 
      unfolding dom[symmetric] by force
    then show "y \<in>\<^sub>\<circ> \<real>\<^sub>\<circ>" by (simp add: vreal_inverse_closed)
  qed
  moreover have "\<real>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vreal_inverse"
    by (intro vsubsetI) 
      (metis dom vdomain_atD vreal_inverse_closed vreal_inverse_inverse)
  ultimately show "\<R>\<^sub>\<circ> vreal_inverse = \<real>\<^sub>\<circ>" by simp
qed



subsection\<open>Integer numbers\<close>


subsubsection\<open>Definition\<close>

definition vint_of_int :: "int \<Rightarrow> V"
  where "vint_of_int = vreal_of_real"

notation vint_of_int (\<open>_\<^sub>\<int>\<close> [999] 999)

declare [[coercion "vint_of_int :: int \<Rightarrow> V"]]

definition vint :: V (\<open>\<int>\<^sub>\<circ>\<close>)
  where "vint = set (range vint_of_int)"

definition int_of_vint :: "V \<Rightarrow> int"
  where "int_of_vint = inv_into UNIV vint_of_int"


text\<open>Rules.\<close>

lemma vint_of_int_in_vintI[intro, simp]: "a\<^sub>\<int> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" by (simp add: vint_def)

lemma vint_of_int_in_vintE[elim]:
  assumes "a \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  obtains b where "b\<^sub>\<int> = a"
  using assms unfolding vint_def by auto


subsubsection\<open>Elementary properties\<close>

lemma vint_vsubset_vreal: "\<int>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  unfolding vint_def vint_of_int_def vreal_def using image_cong by auto

lemma inj_vint_of_int: "inj vint_of_int"
  using inj_vreal_of_real 
  unfolding vint_of_int_def inj_def of_int_eq_iff
  by force

lemma vint_in_Vset_\<omega>2: "\<int>\<^sub>\<circ> \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
  using vint_vsubset_vreal vreal_in_Vset_\<omega>2 by auto

lemma int_of_vint_vint_of_int[simp]: "int_of_vint (a\<^sub>\<int>) = a"
  by (simp add: inj_vint_of_int int_of_vint_def)


text\<open>Transfer rules.\<close>

definition cr_vint :: "V \<Rightarrow> int \<Rightarrow> bool"
  where "cr_vint a b \<longleftrightarrow> (a = vint_of_int b)"

lemma cr_vint_right_total[transfer_rule]: "right_total cr_vint"
  unfolding cr_vint_def right_total_def by simp

lemma cr_vint_bi_unqie[transfer_rule]: "bi_unique cr_vint"
  unfolding cr_vint_def bi_unique_def
  by (simp add: inj_eq inj_vint_of_int)

lemma cr_vint_transfer_domain_rule[transfer_domain_rule]: 
  "Domainp cr_vint = (\<lambda>x. x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>)"
  unfolding cr_vint_def by force

lemma vint_transfer[transfer_rule]: 
  "(rel_set cr_vint) (elts \<int>\<^sub>\<circ>) (UNIV::int set)"
  unfolding cr_vint_def rel_set_def by auto

lemma vint_of_int_transfer[transfer_rule]: "cr_vint (vint_of_int a) a"
  unfolding cr_vint_def by auto


subsubsection\<open>Constants and operations\<close>


text\<open>Auxiliary.\<close>

lemma vint_fsingleton_in_fproduct_vint: "[a\<^sub>\<int>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 1\<^sub>\<nat>" by auto

lemma vint_fpair_in_fproduct_vint: "[a\<^sub>\<int>, b\<^sub>\<int>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" by force


text\<open>Zero.\<close>

lemma vint_zero: "0\<^sub>\<int> = (0::V)" by (simp add: vint_of_int_def vreal_zero)


text\<open>One.\<close>

lemma vint_one: "1\<^sub>\<int> = (1::V)" by (simp add: vreal_one vint_of_int_def)
  

text\<open>Addition.\<close>

definition vint_plus :: V 
  where "vint_plus = 
    (\<lambda>x\<in>\<^sub>\<circ>\<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (int_of_vint (x\<lparr>0\<^sub>\<nat>\<rparr>) + int_of_vint (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<int>)"

abbreviation vint_plus_app (infixl "+\<^sub>\<int>" 65) 
  where "vint_plus_app a b \<equiv> vint_plus\<lparr>a, b\<rparr>\<^sub>\<bullet>"

lemma vint_plus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vint ===> cr_vint ===> cr_vint) (+\<^sub>\<int>) (+)"
  using vint_fpair_in_fproduct_vint
  by (intro rel_funI, unfold vint_plus_def cr_vint_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Multiplication.\<close>

definition vint_mult :: V 
  where "vint_mult = 
    (\<lambda>x\<in>\<^sub>\<circ>\<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (int_of_vint (x\<lparr>0\<^sub>\<nat>\<rparr>) * int_of_vint (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<int>)"

abbreviation vint_mult_app (infixl "*\<^sub>\<int>" 65) 
  where "vint_mult_app a b \<equiv> vint_mult\<lparr>a, b\<rparr>\<^sub>\<bullet>"

lemma vint_mult_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vint ===> cr_vint ===> cr_vint) (*\<^sub>\<int>) (*)"
  using vint_fpair_in_fproduct_vint
  by (intro rel_funI, unfold vint_mult_def cr_vint_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Unary minus.\<close>

definition vint_uminus :: V 
  where "vint_uminus = (\<lambda>x\<in>\<^sub>\<circ>\<int>\<^sub>\<circ>. (uminus (int_of_vint x))\<^sub>\<int>)"

abbreviation vint_uminus_app ("-\<^sub>\<int> _" [81] 80) 
  where "-\<^sub>\<int> a \<equiv> vint_uminus\<lparr>a\<rparr>"

lemma vint_uminus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vint ===> cr_vint) (vint_uminus_app) (uminus)"
  using vint_fsingleton_in_fproduct_vint 
  by (intro rel_funI, unfold vint_uminus_def cr_vint_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Order.\<close>

definition vint_le :: V 
  where "vint_le =
    set {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> int_of_vint a \<le> int_of_vint b}"

abbreviation vint_le' ("(_/ \<le>\<^sub>\<int> _)"  [51, 51] 50)
  where "a \<le>\<^sub>\<int> b \<equiv> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> vint_le"

lemma small_vint_le[simp]: 
  "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> int_of_vint a \<le> int_of_vint b}"
proof-
  have small: "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>}" by simp
  show ?thesis by (rule smaller_than_small[OF small]) auto
qed

lemma vint_le_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(cr_vint ===> cr_vint ===> (=)) vint_le' (\<le>)"
  using vint_fsingleton_in_fproduct_vint 
  by (intro rel_funI, unfold cr_scalar_def cr_vint_def vint_le_def)
    (auto simp: nat_omega_simps)


text\<open>Strict order.\<close>

definition vint_ls :: V 
  where "vint_ls =
    set {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> int_of_vint a < int_of_vint b}"

abbreviation vint_ls' ("(_/ <\<^sub>\<int> _)"  [51, 51] 50)
  where "a <\<^sub>\<int> b \<equiv> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> vint_ls"

lemma small_vint_ls[simp]: 
  "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> int_of_vint a < int_of_vint b}"
proof-
  have small: "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>}" by simp
  show ?thesis by (rule smaller_than_small[OF small]) auto
qed

lemma vint_ls_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(cr_vint ===> cr_vint ===> (=)) vint_ls' (<)"
  using vint_fsingleton_in_fproduct_vint 
  by (intro rel_funI, unfold cr_scalar_def cr_vint_def vint_ls_def)
    (auto simp: nat_omega_simps)


text\<open>Subtraction.\<close>

definition vint_minus :: V 
  where "vint_minus = 
    (\<lambda>x\<in>\<^sub>\<circ>\<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (int_of_vint (x\<lparr>0\<^sub>\<nat>\<rparr>) - int_of_vint (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<int>)"

abbreviation vint_minus_app (infixl "-\<^sub>\<int>" 65) 
  where "vint_minus_app a b \<equiv> vint_minus\<lparr>a, b\<rparr>\<^sub>\<bullet>"

lemma vint_minus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vint ===> cr_vint ===> cr_vint) 
    (-\<^sub>\<int>) (-)"
  using vint_fpair_in_fproduct_vint
  by (intro rel_funI, unfold vint_minus_def cr_vint_def cr_scalar_def) 
    (simp add: nat_omega_simps)


subsubsection\<open>Axioms of a well ordered integral domain\<close>


text\<open>The exposition follows Definition 1.4.1 from the textbook 
\<open>The Real Numbers and Real Analysis\<close> by E. Bloch
\cite{bloch_real_2010}.\<close>

lemma vint_zero_closed: "0\<^sub>\<int> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" by auto

lemma vint_one_closed: "1\<^sub>\<int> \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" by auto

lemma vint_plus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  shows "x +\<^sub>\<int> y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
proof-
  have "x' + y' \<in> UNIV" for x' y' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vint_mult_closed:
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
  shows "x *\<^sub>\<int> y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
proof-
  have "(x'::int) * y' \<in> UNIV" for x' y' by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vint_uminus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  shows "-\<^sub>\<int> x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
proof-
  have "(-x'::int) \<in> UNIV" for x' by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Associative Law for Addition: Definition 1.4.1.a.\<close>

lemma vint_assoc_law_addition: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"  
  shows "(x +\<^sub>\<int> y) +\<^sub>\<int> z = x +\<^sub>\<int> (y +\<^sub>\<int> z)"
proof-
  have "(x' + y') + z' = x' + (y' + z')" for x' y' z' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Commutative Law for Addition: Definition 1.4.1.b.\<close>

lemma vint_commutative_law_addition: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"    
  shows "x +\<^sub>\<int> y = y +\<^sub>\<int> x"
proof-
  have "x' + y' = y' + x'" for x' y' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Identity Law for Addition: Definition 1.4.1.c.\<close>

lemma vint_identity_law_addition: 
  assumes [simp]: "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  shows "x +\<^sub>\<int> 0\<^sub>\<int> = x"
proof-
  have "x' + 0 = x'" for x' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Inverses Law for Addition: Definition 1.4.1.d.\<close>

lemma vint_inverses_law_addition: 
  assumes [simp]: "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  shows "x +\<^sub>\<int> (-\<^sub>\<int> x) = 0\<^sub>\<int>"
proof-
  have "x' + (-x') = 0" for x' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Associative Law for Multiplication: Definition 1.4.1.e.\<close>

lemma vint_assoc_law_multiplication: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"  
  shows "(x *\<^sub>\<int> y) *\<^sub>\<int> z = x *\<^sub>\<int> (y *\<^sub>\<int> z)"
proof-
  have "(x' * y') * z' = x' * (y' * z')" for x' y' z' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Commutative Law for Multiplication: Definition 1.4.1.f.\<close>

lemma vint_commutative_law_multiplication: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
  shows "x *\<^sub>\<int> y = y *\<^sub>\<int> x"
proof-
  have "x' * y' = y' * x'" for x' y' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Identity Law for multiplication: Definition 1.4.1.g.\<close>

lemma vint_identity_law_multiplication: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  shows "x *\<^sub>\<int> 1\<^sub>\<int> = x"
proof-
  have "x' * 1 = x'" for x' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Distributive Law for Multiplication: Definition 1.4.1.h.\<close>

lemma vint_distributive_law: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"  
  shows "x *\<^sub>\<int> (y +\<^sub>\<int> z) = (x *\<^sub>\<int> y) +\<^sub>\<int> (x *\<^sub>\<int> z)"
proof-
  have "x' * (y' + z') = (x' * y') + (x' * z')" for x' y' z' :: int 
    by (simp add: algebra_simps)
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>No Zero Divisors Law: Definition 1.4.1.i.\<close>

lemma vint_no_zero_divisors_law: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "x *\<^sub>\<int> y = 0\<^sub>\<int>"
  shows "x = 0\<^sub>\<int> \<or> y = 0\<^sub>\<int>" 
proof-
  have "x' * y' = 0 \<Longrightarrow> x' = 0 \<or> y' = 0" for x' y' z' :: int 
    by (simp add: algebra_simps)
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Trichotomy Law: Definition 1.4.1.j\<close>

lemma vint_trichotomy_law:
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  shows 
    "(x <\<^sub>\<int> y \<and> ~(x = y) \<and> ~(y <\<^sub>\<int> x)) \<or> 
    (~(x <\<^sub>\<int> y) \<and> x = y \<and> ~(y <\<^sub>\<int> x)) \<or>
    (~(x <\<^sub>\<int> y) \<and> ~(x = y) \<and> y <\<^sub>\<int> x)"
proof-
  have
    "(x' < y' \<and> ~(x' = y') \<and> ~(y' < x')) \<or> 
    (~(x' < y') \<and> x' = y' \<and> ~(y' < x')) \<or>
    (~(x' < y') \<and> ~(x' = y') \<and> y' < x')"
    for x' y' z' :: int
    by auto
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Transitive Law: Definition 1.4.1.k\<close>

lemma vint_transitive_law:
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
    and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
    and "z \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
    and "x <\<^sub>\<int> y" 
    and "y <\<^sub>\<int> z"
  shows "x <\<^sub>\<int> z"
proof-
  have "x' < y' \<Longrightarrow> y' < z' \<Longrightarrow> x' < z'" for x' y' z' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Addition Law of Order: Definition 1.4.1.l\<close>

lemma vint_addition_law_of_order:
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "x <\<^sub>\<int> y"
  shows "x +\<^sub>\<int> z <\<^sub>\<int> y +\<^sub>\<int> z"
proof-
  have "x' < y' \<Longrightarrow> x' + z' < y' + z'" for x' y' z' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Multiplication Law of Order: Definition 1.4.1.m\<close>

lemma vint_multiplication_law_of_order:
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
    and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
    and "z \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
    and "x <\<^sub>\<int> y"
    and "0\<^sub>\<int> <\<^sub>\<int> z"
  shows "x *\<^sub>\<int> z <\<^sub>\<int> y *\<^sub>\<int> z"
proof-
  have "x' < y' \<Longrightarrow> 0 < z' \<Longrightarrow> x' * z' < y' * z'" for x' y' z' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Non-Triviality: Definition 1.4.1.n\<close>

lemma vint_non_triviality: "0\<^sub>\<int> \<noteq> 1\<^sub>\<int>"
proof-
  have "0 \<noteq> (1::int)" by simp
  from this[untransferred] show ?thesis.
qed


text\<open>Well-Ordering Principle.\<close>

lemma well_ordering_principle:
  assumes "A \<subseteq>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
    and "a \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
    and "A \<noteq> 0" 
    and "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> a <\<^sub>\<int> x"
  obtains b where "b \<in>\<^sub>\<circ> A" and "\<And>x. x \<in>\<^sub>\<circ> A \<Longrightarrow> b \<le>\<^sub>\<int> x"
proof-
  {
    fix A' and a' :: int assume prems: "A' \<noteq> {}" "x \<in> A' \<Longrightarrow> a' < x" for x
    then obtain a'' where a'': "a'' \<in> A'" by auto
    from wfE_min[OF wf_int_ge_less_than[of a'], OF a''] obtain b'
      where b'_A': "b' \<in> A'" 
        and yb': "(y, b') \<in> int_ge_less_than a' \<Longrightarrow> y \<notin> A'" 
      for y
      by auto
    moreover from prems b'_A' yb' have "\<And>x. x \<in> A' \<Longrightarrow> b' \<le> x" 
      unfolding int_ge_less_than_def by fastforce
    with b'_A' have "\<exists>b. b \<in> A' \<and> (\<forall>x. x \<in> A' \<longrightarrow> b \<le> x)" by blast
  }
  note real_wo = this
  from real_wo[
      untransferred, of \<open>elts A\<close>, unfolded vnumber_simps, OF assms(1,2)
      ]
  obtain b 
    where "b \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
      and "b \<in>\<^sub>\<circ> A" 
      and "\<And>x. x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> \<Longrightarrow> x \<in>\<^sub>\<circ> A \<Longrightarrow> b \<le>\<^sub>\<int> x"
    by (auto simp: assms(3,4))
  with assms that show ?thesis unfolding vsubset_iff by simp
qed


subsubsection\<open>Fundamental properties of other operations\<close>


text\<open>Minus.\<close>

lemma vint_minus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  shows "x -\<^sub>\<int> y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
proof-
  have "x' - y' \<in> UNIV" for x' y' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vint_minus_eq_plus_uminus: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  shows "x -\<^sub>\<int> y = x +\<^sub>\<int> (-\<^sub>\<int> y)"
proof-
  have "x' - y' = x' + (-y')" for x' y' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Unary minus.\<close>

lemma vint_uminus_uminus: 
  assumes "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
  shows "x = -\<^sub>\<int> (-\<^sub>\<int> x)"
proof-
  have "x' = -(-x')" for x' :: int by simp
  from this[untransferred, OF assms] show ?thesis.
qed


subsubsection\<open>Further properties\<close>


text\<open>Addition.\<close>

global_interpretation vint_plus: binop_onto \<open>\<int>\<^sub>\<circ>\<close> vint_plus
proof-
  have binop: "binop \<int>\<^sub>\<circ> vint_plus"
  proof(intro binopI nopI)
    show vsv: "vsv vint_plus" unfolding vint_plus_def by auto
    interpret vsv vint_plus by (rule vsv)
    show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
    show dom: "\<D>\<^sub>\<circ> vint_plus = \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" unfolding vint_plus_def by simp
    show "\<R>\<^sub>\<circ> vint_plus \<subseteq>\<^sub>\<circ> \<int>\<^sub>\<circ>"
    proof(intro vsubsetI)
      fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_plus"
      then obtain ab where "ab \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" and y_def: "y = vint_plus\<lparr>ab\<rparr>" 
        unfolding dom[symmetric] by force
      then obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
        by blast
      then show "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" by (simp add: vint_plus_closed y_def)
    qed
  qed
  interpret binop \<open>\<int>\<^sub>\<circ>\<close> vint_plus by (rule binop)
  show "binop_onto \<int>\<^sub>\<circ> vint_plus"
  proof(intro binop_ontoI')
    show "binop \<int>\<^sub>\<circ> vint_plus" by (rule binop_axioms)
    show "\<int>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_plus"
    proof(intro vsubsetI)
      fix y assume prems: "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
      moreover from vint_zero vint_zero_closed have "0 \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" by auto
      ultimately have "y +\<^sub>\<int> 0 \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_plus" by auto
      moreover from prems vint_identity_law_addition have "y = y +\<^sub>\<int> 0" 
        by (simp add: vint_zero)
      ultimately show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_plus" by simp
    qed
  qed
qed


text\<open>Unary minus.\<close>

global_interpretation vint_uminus: v11 vint_uminus
  rewrites "\<D>\<^sub>\<circ> vint_uminus = \<int>\<^sub>\<circ>"
    and "\<R>\<^sub>\<circ> vint_uminus = \<int>\<^sub>\<circ>"
proof-
  show v11: "v11 vint_uminus" 
  proof(intro v11I)
    show vsv: "vsv vint_uminus" unfolding vint_uminus_def by simp
    interpret vsv vint_uminus by (rule vsv)
    show "vsv (vint_uminus\<inverse>\<^sub>\<circ>)"
    proof(intro vsvI)
      show "vbrelation (vint_uminus\<inverse>\<^sub>\<circ>)" by clarsimp
      fix a b c
      assume prems: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vint_uminus\<inverse>\<^sub>\<circ>" "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> vint_uminus\<inverse>\<^sub>\<circ>"
      then have ba: "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> vint_uminus" and ca: "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> vint_uminus" 
        by auto
      then have b: "b \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and c: "c \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" 
        by (simp_all add: VLambda_iff2 vint_uminus_def)
      from ba ca have "a = -\<^sub>\<int> b" "a = -\<^sub>\<int> c" by simp_all
      with ba ca b c show "b = c"  by (metis vint_uminus_uminus)
    qed
  qed
  interpret v11 vint_uminus by (rule v11)
  show dom: "\<D>\<^sub>\<circ> vint_uminus = \<int>\<^sub>\<circ>" unfolding vint_uminus_def by simp
  have "\<R>\<^sub>\<circ> vint_uminus \<subseteq>\<^sub>\<circ> \<int>\<^sub>\<circ>"
  proof(intro vsubsetI)
    fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_uminus"
    then obtain x where "x \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and y_def: "y = -\<^sub>\<int> x" 
      unfolding dom[symmetric] by force
    then show "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" by (simp add: vint_uminus_closed)
  qed
  moreover have "\<int>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_uminus"
    by (intro vsubsetI) 
      (metis dom vdomain_atD vint_uminus_closed vint_uminus_uminus)
  ultimately show "\<R>\<^sub>\<circ> vint_uminus = \<int>\<^sub>\<circ>" by simp
qed


text\<open>Multiplication.\<close>

global_interpretation vint_mult: binop_onto \<open>\<int>\<^sub>\<circ>\<close> vint_mult
proof-
  have binop: "binop \<int>\<^sub>\<circ> vint_mult"
  proof(intro binopI nopI)
    show vsv: "vsv vint_mult" unfolding vint_mult_def by auto
    interpret vsv vint_mult by (rule vsv)
    show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
    show dom: "\<D>\<^sub>\<circ> vint_mult = \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" unfolding vint_mult_def by simp
    show "\<R>\<^sub>\<circ> vint_mult \<subseteq>\<^sub>\<circ> \<int>\<^sub>\<circ>"
    proof(intro vsubsetI)
      fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_mult"
      then obtain ab where "ab \<in>\<^sub>\<circ> \<int>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" and y_def: "y = vint_mult\<lparr>ab\<rparr>" 
        unfolding dom[symmetric] by force
      then obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
        by blast
      then show "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" by (simp add: vint_mult_closed y_def)
    qed
  qed
  interpret binop \<open>\<int>\<^sub>\<circ>\<close> vint_mult by (rule binop)
  show "binop_onto \<int>\<^sub>\<circ> vint_mult"
  proof(intro binop_ontoI')
    show "binop \<int>\<^sub>\<circ> vint_mult" by (rule binop_axioms)
    show "\<int>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_mult"
    proof(intro vsubsetI)
      fix y assume prems: "y \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>"
      moreover from vint_one vint_one_closed have 0: "1 \<in>\<^sub>\<circ> \<int>\<^sub>\<circ>" by auto
      ultimately have "y *\<^sub>\<int> 1 \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_mult" by auto
      moreover from prems vint_identity_law_multiplication have "y = y *\<^sub>\<int> 1" 
        by (simp add: vint_one)
      ultimately show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vint_mult" by simp
    qed
  qed
qed



subsection\<open>Rational numbers\<close>


subsubsection\<open>Definition\<close>

definition vrat_of_rat :: "rat \<Rightarrow> V"
  where "vrat_of_rat x = vreal_of_real (real_of_rat x)"

notation vrat_of_rat (\<open>_\<^sub>\<rat>\<close> [999] 999)

declare [[coercion "vrat_of_rat :: rat \<Rightarrow> V"]]

definition vrat :: V (\<open>\<rat>\<^sub>\<circ>\<close>)
  where "vrat = set (range vrat_of_rat)"

definition rat_of_vrat :: "V \<Rightarrow> rat"
  where "rat_of_vrat = inv_into UNIV vrat_of_rat"


text\<open>Rules.\<close>

lemma vrat_of_rat_in_vratI[intro, simp]: "a\<^sub>\<rat> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" by (simp add: vrat_def)

lemma vrat_of_rat_in_vratE[elim]:
  assumes "a \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  obtains b where "b\<^sub>\<rat> = a"
  using assms unfolding vrat_def by auto


subsubsection\<open>Elementary properties\<close>

lemma vrat_vsubset_vreal: "\<rat>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<real>\<^sub>\<circ>"
  unfolding vrat_def vrat_of_rat_def vreal_def using image_cong by auto

lemma vrat_in_Vset_\<omega>2: "\<rat>\<^sub>\<circ> \<in>\<^sub>\<circ> Vset (\<omega> + \<omega>)"
  using vrat_vsubset_vreal vreal_in_Vset_\<omega>2 by auto

lemma inj_vrat_of_rat: "inj vrat_of_rat"
  using inj_vreal_of_real 
  unfolding vrat_of_rat_def inj_def of_rat_eq_iff
  by force

lemma rat_of_vrat_vrat_of_rat[simp]: "rat_of_vrat (a\<^sub>\<rat>) = a"
  by (simp add: inj_vrat_of_rat rat_of_vrat_def)


text\<open>Transfer rules.\<close>

definition cr_vrat :: "V \<Rightarrow> rat \<Rightarrow> bool"
  where "cr_vrat a b \<longleftrightarrow> (a = vrat_of_rat b)"

lemma cr_vrat_right_total[transfer_rule]: "right_total cr_vrat"
  unfolding cr_vrat_def right_total_def by simp

lemma cr_vrat_bi_unqie[transfer_rule]: "bi_unique cr_vrat"
  unfolding cr_vrat_def bi_unique_def
  by (simp add: inj_eq inj_vrat_of_rat)

lemma cr_vrat_transfer_domain_rule[transfer_domain_rule]: 
  "Domainp cr_vrat = (\<lambda>x. x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>)"
  unfolding cr_vrat_def by force

lemma vrat_transfer[transfer_rule]: 
  "(rel_set cr_vrat) (elts \<rat>\<^sub>\<circ>) (UNIV::rat set)"
  unfolding cr_vrat_def rel_set_def by auto

lemma vrat_of_rat_transfer[transfer_rule]: "cr_vrat (vrat_of_rat a) a"
  unfolding cr_vrat_def by auto


subsubsection\<open>Operations\<close>

lemma vrat_fsingleton_in_fproduct_vrat: "[a\<^sub>\<rat>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 1\<^sub>\<nat>" by auto

lemma vrat_fpair_in_fproduct_vrat: "[a\<^sub>\<rat>, b\<^sub>\<rat>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" by force


text\<open>Zero.\<close>

lemma vrat_zero: "0\<^sub>\<rat> = (0::V)" by (simp add: vrat_of_rat_def vreal_zero)


text\<open>One.\<close>

lemma vrat_one: "1\<^sub>\<rat> = (1::V)" by (simp add: vreal_one vrat_of_rat_def)
  

text\<open>Addition.\<close>

definition vrat_plus :: V 
  where "vrat_plus = 
    (\<lambda>x\<in>\<^sub>\<circ>\<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (rat_of_vrat (x\<lparr>0\<^sub>\<nat>\<rparr>) + rat_of_vrat (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<rat>)"

abbreviation vrat_plus_app (infixl "+\<^sub>\<rat>" 65) 
  where "vrat_plus_app a b \<equiv> vrat_plus\<lparr>a, b\<rparr>\<^sub>\<bullet>"

lemma vrat_plus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vrat ===> cr_vrat ===> cr_vrat) (+\<^sub>\<rat>) (+)"
  using vrat_fpair_in_fproduct_vrat
  by (intro rel_funI, unfold vrat_plus_def cr_vrat_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Multiplication.\<close>

definition vrat_mult :: V 
  where "vrat_mult =
    (\<lambda>x\<in>\<^sub>\<circ>\<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (rat_of_vrat (x\<lparr>0\<^sub>\<nat>\<rparr>) * rat_of_vrat (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<rat>)"

abbreviation vrat_mult_app (infixl "*\<^sub>\<rat>" 65) 
  where "vrat_mult_app a b \<equiv> vrat_mult\<lparr>a, b\<rparr>\<^sub>\<bullet>"

lemma vrat_mult_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vrat ===> cr_vrat ===> cr_vrat) (*\<^sub>\<rat>) (*)"
  using vrat_fpair_in_fproduct_vrat
  by (intro rel_funI, unfold vrat_mult_def cr_vrat_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Unary minus.\<close>

definition vrat_uminus :: V 
  where "vrat_uminus = (\<lambda>x\<in>\<^sub>\<circ>\<rat>\<^sub>\<circ>. (uminus (rat_of_vrat x))\<^sub>\<rat>)"

abbreviation vrat_uminus_app ("-\<^sub>\<rat> _" [81] 80) 
  where "-\<^sub>\<rat> a \<equiv> vrat_uminus\<lparr>a\<rparr>"

lemma vrat_uminus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vrat ===> cr_vrat) (vrat_uminus_app) (uminus)"
  using vrat_fsingleton_in_fproduct_vrat 
  by (intro rel_funI, unfold vrat_uminus_def cr_vrat_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Multiplicative inverse.\<close>

definition vrat_inverse :: V 
  where "vrat_inverse = (\<lambda>x\<in>\<^sub>\<circ>\<rat>\<^sub>\<circ>. (inverse (rat_of_vrat x))\<^sub>\<rat>)"

abbreviation vrat_inverse_app ("(_\<inverse>\<^sub>\<rat>)" [1000] 999) 
  where "a\<inverse>\<^sub>\<rat> \<equiv> vrat_inverse\<lparr>a\<rparr>"

lemma vrat_inverse_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vrat ===> cr_vrat) (vrat_inverse_app) (inverse)"
  using vrat_fsingleton_in_fproduct_vrat 
  by (intro rel_funI, unfold vrat_inverse_def cr_vrat_def cr_scalar_def) 
    (simp add: nat_omega_simps)


text\<open>Order.\<close>

definition vrat_le :: V 
  where "vrat_le =
    set {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> rat_of_vrat a \<le> rat_of_vrat b}"

abbreviation vrat_le' ("(_/ \<le>\<^sub>\<rat> _)"  [51, 51] 50)
  where "a \<le>\<^sub>\<rat> b \<equiv> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> vrat_le"

lemma small_vrat_le[simp]: 
  "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> rat_of_vrat a \<le> rat_of_vrat b}"
proof-
  have small: "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>}" by simp
  show ?thesis by (rule smaller_than_small[OF small]) auto
qed

lemma vrat_le_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(cr_vrat ===> cr_vrat ===> (=)) vrat_le' (\<le>)"
  using vrat_fsingleton_in_fproduct_vrat 
  by (intro rel_funI, unfold cr_scalar_def cr_vrat_def vrat_le_def)
    (auto simp: nat_omega_simps)


text\<open>Strict order.\<close>

definition vrat_ls :: V 
  where "vrat_ls =
    set {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> rat_of_vrat a < rat_of_vrat b}"

abbreviation vrat_ls' ("(_/ <\<^sub>\<rat> _)"  [51, 51] 50)
  where "a <\<^sub>\<rat> b \<equiv> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> vrat_ls"

lemma small_vrat_ls[simp]: 
  "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat> \<and> rat_of_vrat a < rat_of_vrat b}"
proof-
  have small: "small {[a, b]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>}" by simp
  show ?thesis by (rule smaller_than_small[OF small]) auto
qed

lemma vrat_ls_transfer[transfer_rule]:
  includes lifting_syntax
  shows "(cr_vrat ===> cr_vrat ===> (=)) vrat_ls' (<)"
  by (intro rel_funI, unfold cr_scalar_def cr_vrat_def vrat_ls_def)
    (auto simp: nat_omega_simps)
  

text\<open>Subtraction.\<close>

definition vrat_minus :: V 
  where "vrat_minus = 
    (\<lambda>x\<in>\<^sub>\<circ>\<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>. (rat_of_vrat (x\<lparr>0\<^sub>\<nat>\<rparr>) - rat_of_vrat (x\<lparr>1\<^sub>\<nat>\<rparr>))\<^sub>\<rat>)"

abbreviation vrat_minus_app (infixl "-\<^sub>\<rat>" 65) 
  where "vrat_minus_app a b \<equiv> vrat_minus\<lparr>a, b\<rparr>\<^sub>\<bullet>"

lemma vrat_minus_transfer[transfer_rule]: 
  includes lifting_syntax
  shows "(cr_vrat ===> cr_vrat ===> cr_vrat)
    (-\<^sub>\<rat>) (-)"
  using vrat_fpair_in_fproduct_vrat 
  by (intro rel_funI, unfold vrat_minus_def cr_vrat_def cr_scalar_def) 
    (simp add: nat_omega_simps)


subsubsection\<open>Axioms of an ordered field\<close>


text\<open>The exposition follows Theorem 1.5.5 from the textbook
\<open>The Real Numbers and Real Analysis\<close> by E. Bloch
\cite{bloch_real_2010}.\<close>

lemma vrat_zero_closed: "0\<^sub>\<rat> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" by auto

lemma vrat_one_closed: "1\<^sub>\<rat> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" by auto

lemma vrat_plus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows "x +\<^sub>\<rat> y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
proof-
  have "x' + y' \<in> UNIV" for x' y' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vrat_mult_closed:
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
  shows "x *\<^sub>\<rat> y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
proof-
  have "(x'::rat) * y' \<in> UNIV" for x' y' by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vrat_uminus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows "-\<^sub>\<rat> x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
proof-
  have "(-x'::rat) \<in> UNIV" for x' by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vrat_inverse_closed: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows "x\<inverse>\<^sub>\<rat> \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
proof-
  have "inverse (x'::rat) \<in> UNIV" for x' by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Associative Law for Addition: Theorem 1.5.5.1.\<close>

lemma vrat_assoc_law_addition: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"  
  shows "(x +\<^sub>\<rat> y) +\<^sub>\<rat> z = x +\<^sub>\<rat> (y +\<^sub>\<rat> z)"
proof-
  have "(x' + y') + z' = x' + (y' + z')" for x' y' z' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Commutative Law for Addition: Theorem 1.5.5.2.\<close>

lemma vrat_commutative_law_addition: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"    
  shows "x +\<^sub>\<rat> y = y +\<^sub>\<rat> x"
proof-
  have "x' + y' = y' + x'" for x' y' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Identity Law for Addition: Theorem 1.5.5.3.\<close>

lemma vrat_identity_law_addition: 
  assumes [simp]: "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows "x +\<^sub>\<rat> 0\<^sub>\<rat> = x"
proof-
  have "x' + 0 = x'" for x' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Inverses Law for Addition: Theorem 1.5.5.4.\<close>

lemma vrat_inverses_law_addition: 
  assumes [simp]: "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows "x +\<^sub>\<rat> (-\<^sub>\<rat> x) = 0\<^sub>\<rat>"
proof-
  have "x' + (-x') = 0" for x' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Associative Law for Multiplication: Theorem 1.5.5.5.\<close>

lemma vrat_assoc_law_multiplication: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"  
  shows "(x *\<^sub>\<rat> y) *\<^sub>\<rat> z = x *\<^sub>\<rat> (y *\<^sub>\<rat> z)"
proof-
  have "(x' * y') * z' = x' * (y' * z')" for x' y' z' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Commutative Law for Multiplication: Theorem 1.5.5.6.\<close>

lemma vrat_commutative_law_multiplication: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
  shows "x *\<^sub>\<rat> y = y *\<^sub>\<rat> x"
proof-
  have "x' * y' = y' * x'" for x' y' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Identity Law for multiplication: Theorem 1.5.5.7.\<close>

lemma vrat_identity_law_multiplication: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows "x *\<^sub>\<rat> 1\<^sub>\<rat> = x"
proof-
  have "x' * 1 = x'" for x' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Inverses Law for Multiplication: Definition 2.2.1.8.\<close>

lemma vrat_inverses_law_multiplication:
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "x \<noteq> 0\<^sub>\<rat>" 
  shows "x *\<^sub>\<rat> x\<inverse>\<^sub>\<rat> = 1\<^sub>\<rat>"
proof-
  have "x' \<noteq> 0 \<Longrightarrow> x' * inverse x' = 1" for x' :: rat by simp  
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Distributive Law for Multiplication: Theorem 1.5.5.9.\<close>

lemma vrat_distributive_law: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"  
  shows "x *\<^sub>\<rat> (y +\<^sub>\<rat> z) = (x *\<^sub>\<rat> y) +\<^sub>\<rat> (x *\<^sub>\<rat> z)"
proof-
  have "x' * (y' + z') = (x' * y') + (x' * z')" for x' y' z' :: rat 
    by (simp add: algebra_simps)
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Trichotomy Law: Theorem 1.5.5.10.\<close>

lemma vrat_trichotomy_law:
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows 
    "(x <\<^sub>\<rat> y \<and> ~(x = y) \<and> ~(y <\<^sub>\<rat> x)) \<or> 
    (~(x <\<^sub>\<rat> y) \<and> x = y \<and> ~(y <\<^sub>\<rat> x)) \<or>
    (~(x <\<^sub>\<rat> y) \<and> ~(x = y) \<and> y <\<^sub>\<rat> x)"
proof-
  have
    "(x' < y' \<and> ~(x' = y') \<and> ~(y' < x')) \<or> 
    (~(x' < y') \<and> x' = y' \<and> ~(y' < x')) \<or>
    (~(x' < y') \<and> ~(x' = y') \<and> y' < x')"
    for x' y' z' :: rat
    by auto
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Transitive Law: Theorem 1.5.5.11.\<close>

lemma vrat_transitive_law:
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
    and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
    and "z \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
    and "x <\<^sub>\<rat> y" 
    and "y <\<^sub>\<rat> z"
  shows "x <\<^sub>\<rat> z"
proof-
  have "x' < y' \<Longrightarrow> y' < z' \<Longrightarrow> x' < z'" for x' y' z' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Addition Law of Order: Theorem 1.5.5.12.\<close>

lemma vrat_addition_law_of_order:
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "z \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "x <\<^sub>\<rat> y"
  shows "x +\<^sub>\<rat> z <\<^sub>\<rat> y +\<^sub>\<rat> z"
proof-
  have "x' < y' \<Longrightarrow> x' + z' < y' + z'" for x' y' z' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Multiplication Law of Order: Theorem 1.5.5.13.\<close>

lemma vrat_multiplication_law_of_order:
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
    and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
    and "z \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
    and "x <\<^sub>\<rat> y"
    and "0\<^sub>\<rat> <\<^sub>\<rat> z"
  shows "x *\<^sub>\<rat> z <\<^sub>\<rat> y *\<^sub>\<rat> z"
proof-
  have "x' < y' \<Longrightarrow> 0 < z' \<Longrightarrow> x' * z' < y' * z'" for x' y' z' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Non-Triviality: Theorem 1.5.5.14.\<close>

lemma vrat_non_triviality: "0\<^sub>\<rat> \<noteq> 1\<^sub>\<rat>"
proof-
  have "0 \<noteq> (1::rat)" by simp
  from this[untransferred] show ?thesis.
qed


subsubsection\<open>Fundamental properties of other operations\<close>


text\<open>Minus.\<close>

lemma vrat_minus_closed: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows "x -\<^sub>\<rat> y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
proof-
  have "x' - y' \<in> UNIV" for x' y' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed

lemma vrat_minus_eq_plus_uminus: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  shows "x -\<^sub>\<rat> y = x +\<^sub>\<rat> (-\<^sub>\<rat> y)"
proof-
  have "x' - y' = x' + (-y')" for x' y' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Unary minus.\<close>

lemma vrat_uminus_uminus: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
  shows "x = -\<^sub>\<rat> (-\<^sub>\<rat> x)"
proof-
  have "x' = -(-x')" for x' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


text\<open>Multiplicative inverse.\<close>

lemma vrat_inverse_inverse: 
  assumes "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
  shows "x = (x\<inverse>\<^sub>\<rat>)\<inverse>\<^sub>\<rat>"
proof-
  have "x' = inverse (inverse x')" for x' :: rat by simp
  from this[untransferred, OF assms] show ?thesis.
qed


subsubsection\<open>Further properties\<close>


text\<open>Addition.\<close>

global_interpretation vrat_plus: binop_onto \<open>\<rat>\<^sub>\<circ>\<close> vrat_plus
proof-
  have binop: "binop \<rat>\<^sub>\<circ> vrat_plus"
  proof(intro binopI nopI)
    show vsv: "vsv vrat_plus" unfolding vrat_plus_def by auto
    interpret vsv vrat_plus by (rule vsv)
    show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
    show dom: "\<D>\<^sub>\<circ> vrat_plus = \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" unfolding vrat_plus_def by simp
    show "\<R>\<^sub>\<circ> vrat_plus \<subseteq>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
    proof(intro vsubsetI)
      fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_plus"
      then obtain ab where "ab \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" and y_def: "y = vrat_plus\<lparr>ab\<rparr>" 
        unfolding dom[symmetric] by force
      then obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
        by blast
      then show "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" by (simp add: vrat_plus_closed y_def)
    qed
  qed
  interpret binop \<open>\<rat>\<^sub>\<circ>\<close> vrat_plus by (rule binop)
  show "binop_onto \<rat>\<^sub>\<circ> vrat_plus"
  proof(intro binop_ontoI')
    show "binop \<rat>\<^sub>\<circ> vrat_plus" by (rule binop_axioms)
    show "\<rat>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_plus"
    proof(intro vsubsetI)
      fix y assume prems: "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
      moreover from vrat_zero vrat_zero_closed have 0: "0 \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
        by auto
      ultimately have "y +\<^sub>\<rat> 0 \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_plus" by auto
      moreover from prems vrat_identity_law_addition have "y = y +\<^sub>\<rat> 0" 
        by (simp add: vrat_zero)
      ultimately show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_plus" by simp
    qed
  qed
qed


text\<open>Unary minus.\<close>

global_interpretation vrat_uminus: v11 vrat_uminus
  rewrites "\<D>\<^sub>\<circ> vrat_uminus = \<rat>\<^sub>\<circ>"
    and "\<R>\<^sub>\<circ> vrat_uminus = \<rat>\<^sub>\<circ>"
proof-
  show v11: "v11 vrat_uminus" 
  proof(intro v11I)
    show vsv: "vsv vrat_uminus" unfolding vrat_uminus_def by simp
    interpret vsv vrat_uminus by (rule vsv)
    show "vsv (vrat_uminus\<inverse>\<^sub>\<circ>)"
    proof(intro vsvI)
      show "vbrelation (vrat_uminus\<inverse>\<^sub>\<circ>)" by clarsimp
      fix a b c
      assume prems: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vrat_uminus\<inverse>\<^sub>\<circ>" "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> vrat_uminus\<inverse>\<^sub>\<circ>"
      then have ba: "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> vrat_uminus" and ca: "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> vrat_uminus" 
        by auto
      then have b: "b \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and c: "c \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
        by (simp_all add: VLambda_iff2 vrat_uminus_def)
      from ba ca have "a = -\<^sub>\<rat> b" "a = -\<^sub>\<rat> c" by simp_all
      with ba ca b c show "b = c"  by (metis vrat_uminus_uminus)
    qed
  qed
  interpret v11 vrat_uminus by (rule v11)
  show dom: "\<D>\<^sub>\<circ> vrat_uminus = \<rat>\<^sub>\<circ>" unfolding vrat_uminus_def by simp
  have "\<R>\<^sub>\<circ> vrat_uminus \<subseteq>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  proof(intro vsubsetI)
    fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_uminus"
    then obtain x where "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and y_def: "y = -\<^sub>\<rat> x" 
      unfolding dom[symmetric] by force
    then show "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" by (simp add: vrat_uminus_closed)
  qed
  moreover have "\<rat>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_uminus"
    by (intro vsubsetI) 
      (metis dom vdomain_atD vrat_uminus_closed vrat_uminus_uminus)
  ultimately show "\<R>\<^sub>\<circ> vrat_uminus = \<rat>\<^sub>\<circ>" by simp
qed


text\<open>Multiplication.\<close>

global_interpretation vrat_mult: binop_onto \<open>\<rat>\<^sub>\<circ>\<close> vrat_mult
proof-
  have binop: "binop \<rat>\<^sub>\<circ> vrat_mult"
  proof(intro binopI nopI)
    show vsv: "vsv vrat_mult" unfolding vrat_mult_def by auto
    interpret vsv vrat_mult by (rule vsv)
    show "2\<^sub>\<nat> \<in>\<^sub>\<circ> \<omega>" by simp
    show dom: "\<D>\<^sub>\<circ> vrat_mult = \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" unfolding vrat_mult_def by simp
    show "\<R>\<^sub>\<circ> vrat_mult \<subseteq>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
    proof(intro vsubsetI)
      fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_mult"
      then obtain ab where "ab \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ> ^\<^sub>\<times> 2\<^sub>\<nat>" and y_def: "y = vrat_mult\<lparr>ab\<rparr>" 
        unfolding dom[symmetric] by force
      then obtain a b 
        where ab_def: "ab = [a, b]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
        by blast
      then show "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" by (simp add: vrat_mult_closed y_def)
    qed
  qed
  interpret binop \<open>\<rat>\<^sub>\<circ>\<close> vrat_mult by (rule binop)
  show "binop_onto \<rat>\<^sub>\<circ> vrat_mult"
  proof(intro binop_ontoI')
    show "binop \<rat>\<^sub>\<circ> vrat_mult" by (rule binop_axioms)
    show "\<rat>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_mult"
    proof(intro vsubsetI)
      fix y assume prems: "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
      moreover from vrat_one vrat_one_closed have "1 \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" by auto
      ultimately have "y *\<^sub>\<rat> 1 \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_mult" by auto
      moreover from prems vrat_identity_law_multiplication have "y = y *\<^sub>\<rat> 1" 
        by (simp add: vrat_one)
      ultimately show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_mult" by simp
    qed
  qed
qed


text\<open>Multiplicative inverse.\<close>

global_interpretation vrat_inverse: v11 vrat_inverse
  rewrites "\<D>\<^sub>\<circ> vrat_inverse = \<rat>\<^sub>\<circ>"
    and "\<R>\<^sub>\<circ> vrat_inverse = \<rat>\<^sub>\<circ>"
proof-
  show v11: "v11 vrat_inverse" 
  proof(intro v11I)
    show vsv: "vsv vrat_inverse" unfolding vrat_inverse_def by simp
    interpret vsv vrat_inverse by (rule vsv)
    show "vsv (vrat_inverse\<inverse>\<^sub>\<circ>)"
    proof(intro vsvI)
      show "vbrelation (vrat_inverse\<inverse>\<^sub>\<circ>)" by clarsimp
      fix a b c
      assume prems: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> vrat_inverse\<inverse>\<^sub>\<circ>" "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> vrat_inverse\<inverse>\<^sub>\<circ>"
      then have ba: "\<langle>b, a\<rangle> \<in>\<^sub>\<circ> vrat_inverse" and ca: "\<langle>c, a\<rangle> \<in>\<^sub>\<circ> vrat_inverse" 
        by auto
      then have b: "b \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and c: "c \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" 
        by (simp_all add: VLambda_iff2 vrat_inverse_def)
      from ba ca have "a = b\<inverse>\<^sub>\<rat>" "a = c\<inverse>\<^sub>\<rat>" by simp_all
      with ba ca b c show "b = c"  by (metis vrat_inverse_inverse)
    qed
  qed
  interpret v11 vrat_inverse by (rule v11)
  show dom: "\<D>\<^sub>\<circ> vrat_inverse = \<rat>\<^sub>\<circ>" unfolding vrat_inverse_def by simp
  have "\<R>\<^sub>\<circ> vrat_inverse \<subseteq>\<^sub>\<circ> \<rat>\<^sub>\<circ>"
  proof(intro vsubsetI)
    fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_inverse"
    then obtain x where "x \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" and y_def: "y = x\<inverse>\<^sub>\<rat>" 
      unfolding dom[symmetric] by force
    then show "y \<in>\<^sub>\<circ> \<rat>\<^sub>\<circ>" by (simp add: vrat_inverse_closed)
  qed
  moreover have "\<rat>\<^sub>\<circ> \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> vrat_inverse"
    by (intro vsubsetI) 
      (metis dom vdomain_atD vrat_inverse_closed vrat_inverse_inverse)
  ultimately show "\<R>\<^sub>\<circ> vrat_inverse = \<rat>\<^sub>\<circ>" by simp
qed



subsection\<open>Upper bound on the cardinality of the continuum for \<^typ>\<open>V\<close>\<close>

lemma inj_on_inv_vreal_of_real: "inj_on (inv vreal_of_real) (elts \<real>\<^sub>\<circ>)"
  by (intro inj_onI) (fastforce intro: inv_into_injective)

lemma vreal_vlepoll_VPow_omega: "\<real>\<^sub>\<circ> \<lesssim>\<^sub>\<circ> VPow \<omega>"
proof-
  have "elts \<real>\<^sub>\<circ> \<lesssim> (UNIV::real set)"
    unfolding lepoll_def by (auto intro: inj_on_inv_vreal_of_real)
  from vlepoll_VPow_omega_if_vreal_lepoll_real[OF this] show ?thesis by simp
qed

text\<open>\newpage\<close>

end