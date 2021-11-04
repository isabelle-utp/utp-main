section \<open> Algebraic Laws \<close>

theory ISQ_Algebra
  imports ISQ_Proof
begin

subsection \<open> Quantity Scale \<close>

lemma scaleQ_add_right: "a *\<^sub>Q x + y = (a *\<^sub>Q x) + (a *\<^sub>Q y)"
  by (si_simp add: distrib_left)

lemma scaleQ_add_left: "a + b *\<^sub>Q x = (a *\<^sub>Q x) + (b *\<^sub>Q x)"
  by (si_simp add: distrib_right)

lemma scaleQ_scaleQ [simp]: "a *\<^sub>Q b *\<^sub>Q x = a \<cdot> b *\<^sub>Q x"
  by si_simp

lemma scaleQ_one [simp]: "1 *\<^sub>Q x = x"
  by si_simp

lemma scaleQ_zero [simp]: "0 *\<^sub>Q x = 0"
  by si_simp

lemma scaleQ_inv: "-a *\<^sub>Q x = a *\<^sub>Q -x"
  by si_calc

lemma scaleQ_as_qprod: "a *\<^sub>Q x \<cong>\<^sub>Q (a *\<^sub>Q \<one>) \<^bold>\<cdot> x"
  by si_simp

lemma mult_scaleQ_left [simp]: "(a *\<^sub>Q x) \<^bold>\<cdot> y = a *\<^sub>Q x \<^bold>\<cdot> y"
  by si_simp

lemma mult_scaleQ_right [simp]: "x \<^bold>\<cdot> (a *\<^sub>Q y) = a *\<^sub>Q x \<^bold>\<cdot> y"
  by si_simp

subsection \<open> Field Laws \<close>

lemma qtimes_commute: "x \<^bold>\<cdot> y \<cong>\<^sub>Q y \<^bold>\<cdot> x"
  by si_calc

lemma qtimes_assoc: "(x \<^bold>\<cdot> y) \<^bold>\<cdot> z  \<cong>\<^sub>Q  x \<^bold>\<cdot> (y \<^bold>\<cdot> z)"
  by (si_calc)

lemma qtimes_left_unit: "\<one> \<^bold>\<cdot> x \<cong>\<^sub>Q x"
  by (si_calc)

lemma qtimes_right_unit: "x \<^bold>\<cdot> \<one> \<cong>\<^sub>Q x"
  by (si_calc)

text\<open>The following weak congruences will allow for replacing equivalences in contexts
     built from product and inverse. \<close>

lemma qtimes_weak_cong_left:
  assumes "x \<cong>\<^sub>Q y"
  shows  "x\<^bold>\<cdot>z \<cong>\<^sub>Q y\<^bold>\<cdot>z"
  using assms by si_simp

lemma qtimes_weak_cong_right:
  assumes "x \<cong>\<^sub>Q y"
  shows  "z\<^bold>\<cdot>x \<cong>\<^sub>Q z\<^bold>\<cdot>y"
  using assms by si_calc

lemma qinverse_weak_cong:
  assumes "x \<cong>\<^sub>Q y"
  shows   "x\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q y\<^sup>-\<^sup>\<one>"
  using assms by si_calc

lemma scaleQ_cong:
  assumes "y \<cong>\<^sub>Q z"
  shows "x *\<^sub>Q y \<cong>\<^sub>Q x *\<^sub>Q z"
  using assms by si_calc

lemma qinverse_qinverse: "x\<^sup>-\<^sup>\<one>\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q x"
  by si_calc

lemma qinverse_nonzero_iff_nonzero: "x\<^sup>-\<^sup>\<one> = 0 \<longleftrightarrow> x = 0"
  by (auto, si_calc+)

lemma qinverse_qtimes: "(x \<^bold>\<cdot> y)\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q x\<^sup>-\<^sup>\<one> \<^bold>\<cdot> y\<^sup>-\<^sup>\<one>"
  by (si_simp add: inverse_distrib)

lemma qinverse_qdivide: "(x \<^bold>/ y)\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q y \<^bold>/ x"
  by si_simp

lemma qtimes_cancel: "x \<noteq> 0 \<Longrightarrow> x \<^bold>/ x \<cong>\<^sub>Q \<one>"
  by si_calc

end
