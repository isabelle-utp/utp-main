(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory Projective_Measurements imports 
  Linear_Algebra_Complements


begin
  

section \<open>Projective measurements\<close>

text \<open>In this part we define projective measurements, also refered to as von Neumann measurements. 
  The latter are characterized by a set of orthogonal projectors, which are used to compute the 
probabilities of measure outcomes and to represent the state of the system after the measurement.\<close> 

text \<open>The state of the system (a density operator in this case) after a measurement is represented by 
the \verb+density_collapse+ function.\<close>

subsection \<open>First definitions\<close>

text \<open>We begin by defining a type synonym for couples of measurement values (reals) and the 
associated projectors (complex matrices).\<close>

type_synonym measure_outcome = "real \<times> complex Matrix.mat"

text \<open>The corresponding values and projectors are retrieved thanks to \verb+meas_outcome_val+ 
and \verb+meas_outcome_prj+.\<close>

definition meas_outcome_val::"measure_outcome \<Rightarrow> real" where
"meas_outcome_val Mi = fst Mi"

definition meas_outcome_prj::"measure_outcome \<Rightarrow> complex Matrix.mat" where
"meas_outcome_prj Mi = snd Mi"

text \<open>We define a predicate for projective measurements. A projective measurement is characterized 
by the number $p$ of possible measure outcomes, and a function $M$ mapping outcome $i$ to the 
corresponding \verb+measure_outcome+.\<close>

definition (in cpx_sq_mat) proj_measurement::"nat \<Rightarrow> (nat \<Rightarrow> measure_outcome) \<Rightarrow> bool" where
  "proj_measurement n M \<longleftrightarrow> 
    (inj_on (\<lambda>i. meas_outcome_val (M i)) {..< n}) \<and> 
    (\<forall>j < n. meas_outcome_prj (M j) \<in> fc_mats \<and> 
    projector (meas_outcome_prj (M j))) \<and> 
    (\<forall> i < n. \<forall> j < n. i \<noteq> j \<longrightarrow> 
      meas_outcome_prj (M i) * meas_outcome_prj (M j) = 0\<^sub>m dimR dimR) \<and>
    sum_mat (\<lambda>j. meas_outcome_prj (M j)) {..< n} = 1\<^sub>m dimR"

lemma (in cpx_sq_mat) proj_measurement_inj:
  assumes "proj_measurement p M"
  shows "inj_on (\<lambda>i. meas_outcome_val (M i)) {..< p}" using assms 
  unfolding proj_measurement_def by simp

lemma (in cpx_sq_mat) proj_measurement_carrier:
  assumes "proj_measurement p M"
  and "i < p"
  shows "meas_outcome_prj (M i) \<in> fc_mats" using assms 
  unfolding proj_measurement_def by simp

lemma (in cpx_sq_mat) proj_measurement_ortho:
  assumes "proj_measurement p M"
and "i < p"
and "j < p"
and "i\<noteq> j"
shows "meas_outcome_prj (M i) * meas_outcome_prj (M j) = 0\<^sub>m dimR dimR" using assms 
  unfolding proj_measurement_def by simp

lemma (in cpx_sq_mat) proj_measurement_id:
  assumes "proj_measurement p M"
  shows "sum_mat (\<lambda>j. meas_outcome_prj (M j)) {..< p} = 1\<^sub>m dimR" using assms
  unfolding proj_measurement_def by simp

lemma (in cpx_sq_mat) proj_measurement_square:
  assumes "proj_measurement p M"
and "i < p"
shows "meas_outcome_prj (M i) \<in> fc_mats" using assms unfolding proj_measurement_def by simp

lemma (in cpx_sq_mat) proj_measurement_proj:
  assumes "proj_measurement p M"
and "i < p"
shows "projector (meas_outcome_prj (M i))" using assms unfolding proj_measurement_def by simp

text \<open>We define the probability of obtaining a measurement outcome: this is a positive number and
the sum over all the measurement outcomes is 1.\<close>

definition (in cpx_sq_mat) meas_outcome_prob :: "complex Matrix.mat \<Rightarrow> 
  (nat \<Rightarrow> real \<times> complex Matrix.mat) \<Rightarrow> nat \<Rightarrow> complex" where
"meas_outcome_prob R M i = Complex_Matrix.trace (R* (meas_outcome_prj (M i)))"

lemma (in cpx_sq_mat) meas_outcome_prob_real:
assumes "R\<in> fc_mats"
  and "density_operator R"
  and "proj_measurement n M"
  and "i < n"
shows "meas_outcome_prob R M i \<in> \<real>" 
proof -
  have "complex_of_real (Re (Complex_Matrix.trace (R * meas_outcome_prj (M i)))) = 
    Complex_Matrix.trace (R * meas_outcome_prj (M i))" 
  proof (rule trace_proj_pos_real)
    show "R \<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
    show "Complex_Matrix.positive R" using assms unfolding density_operator_def by simp
    show "projector (meas_outcome_prj (M i))" using assms proj_measurement_proj by simp
    show "meas_outcome_prj (M i) \<in> carrier_mat dimR dimR" using assms proj_measurement_carrier
        fc_mats_carrier dim_eq by simp
  qed
  thus ?thesis unfolding meas_outcome_prob_def by (metis Reals_of_real)
qed

lemma (in cpx_sq_mat) meas_outcome_prob_pos:
  assumes "R\<in> fc_mats"
  and "density_operator R"
  and "proj_measurement n M"
  and "i < n"
shows "0 \<le> meas_outcome_prob R M i" unfolding meas_outcome_prob_def
proof (rule positive_proj_trace)
  show "R \<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
  show "Complex_Matrix.positive R" using assms unfolding density_operator_def by simp
  show "projector (meas_outcome_prj (M i))" using assms proj_measurement_proj by simp
  show "meas_outcome_prj (M i) \<in> carrier_mat dimR dimR" using assms proj_measurement_carrier
      fc_mats_carrier dim_eq by simp
qed

lemma (in cpx_sq_mat) meas_outcome_prob_sum:
  assumes "density_operator R"
  and "R\<in> fc_mats"
  and" proj_measurement n M"
shows "(\<Sum> j \<in> {..< n}. meas_outcome_prob R M j) = 1"  
proof -
  have "(\<Sum> j \<in> {..< n}. Complex_Matrix.trace (R* (meas_outcome_prj (M j)))) = 
    Complex_Matrix.trace (sum_mat (\<lambda>j. R* (meas_outcome_prj (M j))) {..< n})" 
  proof (rule trace_sum_mat[symmetric], auto)
    fix j
    assume "j < n"
    thus "R * meas_outcome_prj (M j) \<in> fc_mats" using cpx_sq_mat_mult assms 
      unfolding proj_measurement_def by simp
  qed
  also have "... = Complex_Matrix.trace (R * (sum_mat (\<lambda>j. (meas_outcome_prj (M j))) {..< n}))" 
  proof -
    have "sum_mat (\<lambda>j. R* (meas_outcome_prj (M j))) {..< n} = 
      R * (sum_mat (\<lambda>j. (meas_outcome_prj (M j))) {..< n})"
    proof (rule mult_sum_mat_distrib_left, (auto simp add: assms))
      fix j
      assume "j < n"
      thus "meas_outcome_prj (M j) \<in> fc_mats" using assms unfolding proj_measurement_def by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = Complex_Matrix.trace (R * 1\<^sub>m dimR)" using assms unfolding proj_measurement_def 
    by simp
  also have "... = Complex_Matrix.trace R" using assms by (simp add: fc_mats_carrier dim_eq)
  also have "... = 1" using assms unfolding density_operator_def by simp
  finally show ?thesis unfolding meas_outcome_prob_def .
qed

text \<open>We introduce the maximally mixed density operator. Intuitively, this density operator 
corresponds to a uniform distribution of the states of an orthonormal basis.
This operator will be used to define the density operator after a measurement for the measure 
outcome probabilities equal to zero.\<close>

definition max_mix_density :: "nat \<Rightarrow> complex Matrix.mat" where
"max_mix_density n = ((1::real)/ n)  \<cdot>\<^sub>m (1\<^sub>m n)"

lemma max_mix_density_carrier:
  shows "max_mix_density n \<in> carrier_mat n n" unfolding max_mix_density_def by simp

lemma max_mix_is_density: 
  assumes "0 < n"
  shows "density_operator (max_mix_density n)" unfolding density_operator_def max_mix_density_def
proof
  have "Complex_Matrix.trace (complex_of_real ((1::real)/n) \<cdot>\<^sub>m 1\<^sub>m n) = 
    (complex_of_real ((1::real)/n)) *  (Complex_Matrix.trace ((1\<^sub>m n)::complex Matrix.mat))" 
    using one_carrier_mat trace_smult[of "(1\<^sub>m n)::complex Matrix.mat"] by blast
  also have "... = (complex_of_real ((1::real)/n))  * (real n)"  using trace_1[of n] by simp
  also have "... = 1" using assms by simp
  finally show "Complex_Matrix.trace (complex_of_real ((1::real)/n) \<cdot>\<^sub>m 1\<^sub>m n) =  1" .
next
  show "Complex_Matrix.positive (complex_of_real (1 / real n) \<cdot>\<^sub>m 1\<^sub>m n)" 
    by (rule positive_smult, (auto simp add: positive_one))
qed
  
lemma (in cpx_sq_mat) max_mix_density_square:
  shows "max_mix_density dimR \<in> fc_mats" unfolding max_mix_density_def 
  using fc_mats_carrier dim_eq by simp

text \<open>Given a measurement outcome, \verb+density_collapse+ represents the resulting density 
operator. In practice only the measure outcomes with nonzero probabilities are of interest; we 
(arbitrarily) collapse the density operator for zero-probability outcomes to the maximally mixed 
density operator.\<close>

definition density_collapse ::"complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
"density_collapse R P = (if ((Complex_Matrix.trace (R * P)) = 0) then (max_mix_density (dim_row R)) 
    else ((1::real)/ ((Complex_Matrix.trace (R * P)))) \<cdot>\<^sub>m (P * R * P))"

lemma  density_collapse_carrier:
  assumes "0 < dim_row R"
  and "P \<in> carrier_mat n n"
  and "R \<in> carrier_mat n n"
shows "(density_collapse R P) \<in> carrier_mat n n"
proof (cases "(Complex_Matrix.trace (R * P)) = 0")
  case True
  hence "density_collapse R P = max_mix_density (dim_row R)" unfolding density_collapse_def by simp
  then show ?thesis using max_mix_is_density assms max_mix_density_carrier by auto 
next
  case False
  hence "density_collapse R P = complex_of_real 1 / Complex_Matrix.trace (R * P) \<cdot>\<^sub>m (P * R * P)" 
    unfolding density_collapse_def by simp
  thus ?thesis using assms by auto
qed

lemma  density_collapse_operator:
  assumes "projector P"
  and "density_operator R"
  and "0 < dim_row R"
  and "P \<in> carrier_mat n n"
  and "R \<in> carrier_mat n n"
shows "density_operator (density_collapse R P)"
proof (cases "(Complex_Matrix.trace (R * P)) = 0")
  case True
  hence "density_collapse R P = max_mix_density (dim_row R)" unfolding density_collapse_def by simp
  then show ?thesis using max_mix_is_density assms by simp
next
  case False
  show ?thesis unfolding density_operator_def
  proof (intro conjI)
    have "Complex_Matrix.positive ((1 / (Complex_Matrix.trace (R * P))) \<cdot>\<^sub>m (P * R * P))"
    proof (rule positive_smult)
      show "P * R * P \<in> carrier_mat n n" using assms by simp
      have "Complex_Matrix.positive R" using assms unfolding density_operator_def by simp
      hence "0 \<le> (Complex_Matrix.trace (R * P))" using  positive_proj_trace[of P R n] assms 
          False by auto
      hence "0 \<le> Re (Complex_Matrix.trace (R * P))" by simp
      hence "0 \<le> 1/(Re (Complex_Matrix.trace (R * P)))" by simp
      have "Re (Complex_Matrix.trace (R * P)) = Complex_Matrix.trace (R * P)" 
        using assms \<open>Complex_Matrix.positive R\<close> trace_proj_pos_real by simp
      hence inv: "1/ (Complex_Matrix.trace (R * P)) = 1/(Re (Complex_Matrix.trace (R * P)))" by simp
      thus "0 \<le> 1/ (Complex_Matrix.trace (R * P))" 
        using \<open>0 \<le> 1/(Re (Complex_Matrix.trace (R * P)))\<close> by (simp add: inv) 
      show "Complex_Matrix.positive (P * R * P)" using assms 
          positive_close_under_left_right_mult_adjoint[of P n R]
        by (simp add: \<open>Complex_Matrix.positive R\<close> hermitian_def projector_def)
    qed
    thus "Complex_Matrix.positive (density_collapse R P)" using False 
      unfolding density_collapse_def by simp
  next
    have "Complex_Matrix.trace (density_collapse R P) = 
      Complex_Matrix.trace ((1/ (Complex_Matrix.trace (R * P))) \<cdot>\<^sub>m (P * R * P))" 
      using False unfolding density_collapse_def by simp
    also have "... = 1/ (Complex_Matrix.trace (R * P)) * Complex_Matrix.trace (P * R * P)" 
      using trace_smult[of "P * R * P" n] assms by simp
    also have "... = 1/ (Complex_Matrix.trace (R * P)) * Complex_Matrix.trace (R * P)" 
      using projector_collapse_trace assms by simp
    also have "... = 1" using False by simp
    finally show "Complex_Matrix.trace (density_collapse R P) = 1" .
  qed
qed


subsection \<open>Measurements with observables\<close>

text \<open>It is standard in quantum mechanics to represent projective measurements with so-called 
\emph{observables}. These are Hermitian matrices which encode projective measurements as follows: 
the eigenvalues of an observable represent the possible projective measurement outcomes, and the 
associated projectors are the projectors onto the corresponding eigenspaces. The results in this 
part are based on the spectral theorem, which states that any Hermitian matrix admits an 
orthonormal basis consisting of eigenvectors of the matrix.\<close>


subsubsection \<open>On the diagonal elements of a matrix\<close>

text \<open>We begin by introducing definitions that will be used on the diagonalized version of a 
Hermitian matrix.\<close>

definition diag_elems where
"diag_elems B = {B$$(i,i) |i. i < dim_row B}"

text \<open>Relationship between \verb+diag_elems+ and the list \verb+diag_mat+\<close>

lemma diag_elems_set_diag_mat:
  shows "diag_elems B = set (diag_mat B)" unfolding diag_mat_def diag_elems_def 
proof
  show "{B $$ (i, i) |i. i < dim_row B} \<subseteq> set (map (\<lambda>i. B $$ (i, i)) [0..<dim_row B])"
  proof
    fix x
    assume "x \<in> {B $$ (i, i) |i. i < dim_row B}"
    hence "\<exists>i < dim_row B. x = B $$(i,i)" by auto
    from this obtain i where "i < dim_row B" and "x = B $$(i,i)" by auto
    thus "x \<in> set (map (\<lambda>i. B $$ (i, i)) [0..<dim_row B])" by auto
  qed
next
  show "set (map (\<lambda>i. B $$ (i, i)) [0..<dim_row B]) \<subseteq> {B $$ (i, i) |i. i < dim_row B}"
  proof
    fix x
    assume "x \<in> set (map (\<lambda>i. B $$ (i, i)) [0..<dim_row B])"
    thus "x \<in> {B $$ (i, i) |i. i < dim_row B}" by auto
  qed
qed

lemma diag_elems_finite[simp]:
  shows "finite (diag_elems B)" unfolding diag_elems_def by simp

lemma diag_elems_mem[simp]:
  assumes "i < dim_row B"
  shows "B $$(i,i) \<in> diag_elems B" using assms unfolding diag_elems_def by auto

text \<open>When $x$ is a diagonal element of $B$,  \verb+diag_elem_indices+ returns the set of diagonal
indices of $B$ with value $x$.\<close>

definition diag_elem_indices where
"diag_elem_indices x B = {i|i. i < dim_row B \<and> B $$ (i,i) = x}"

lemma diag_elem_indices_elem:
  assumes "a \<in> diag_elem_indices x B"
  shows "a < dim_row B \<and> B$$(a,a) = x" using assms unfolding diag_elem_indices_def by simp

lemma diag_elem_indices_itself:
  assumes "i < dim_row B"
  shows "i \<in> diag_elem_indices (B $$(i,i)) B" using assms unfolding diag_elem_indices_def by simp

lemma diag_elem_indices_finite:
  shows "finite (diag_elem_indices x B)" unfolding diag_elem_indices_def by simp

text \<open>We can therefore partition the diagonal indices of a matrix $B$ depending on the value
of the diagonal elements. If $B$ admits $p$ elements on its diagonal, then we define bijections 
between its set of diagonal elements and the initial segment $[0..p-1]$.\<close>

definition dist_el_card where 
"dist_el_card B = card (diag_elems B)"

definition diag_idx_to_el where
"diag_idx_to_el B = (SOME h. bij_betw h {..< dist_el_card B} (diag_elems B))"

definition diag_el_to_idx where
"diag_el_to_idx B = inv_into {..< dist_el_card B} (diag_idx_to_el B)"

lemma diag_idx_to_el_bij:
  shows "bij_betw (diag_idx_to_el B) {..< dist_el_card B} (diag_elems B)"
proof -
  let ?V = "SOME h. bij_betw h {..< dist_el_card B} (diag_elems B)"
  have vprop: "bij_betw ?V {..< dist_el_card B} (diag_elems B)" using 
      someI_ex[of "\<lambda>h. bij_betw h {..< dist_el_card B} (diag_elems B)"]
     diag_elems_finite  unfolding dist_el_card_def using bij_betw_from_nat_into_finite by blast
  show ?thesis by (simp add:diag_idx_to_el_def vprop)
qed

lemma diag_el_to_idx_bij:
  shows "bij_betw (diag_el_to_idx B) (diag_elems B) {..< dist_el_card B}" 
  unfolding diag_el_to_idx_def 
proof (rule bij_betw_inv_into_subset[of _ _ "diag_elems B"], (simp add: diag_idx_to_el_bij)+)
  show "diag_idx_to_el B ` {..<dist_el_card B} = diag_elems B" 
    by (simp add: diag_idx_to_el_bij bij_betw_imp_surj_on)
qed

lemma diag_idx_to_el_less_inj:
  assumes "i < dist_el_card B"
and "j < dist_el_card B"
  and "diag_idx_to_el B i = diag_idx_to_el B j"
shows "i = j"
proof -
  have "i \<in> {..< dist_el_card B}" using assms by simp
  moreover have "j\<in> {..< dist_el_card B}" using assms by simp
  moreover have "inj_on (diag_idx_to_el B) {..<dist_el_card B}" 
    using diag_idx_to_el_bij[of B] 
    unfolding bij_betw_def by simp
  ultimately show ?thesis by (meson assms(3) inj_on_contraD) 
qed

lemma diag_idx_to_el_less_surj:
  assumes "x\<in> diag_elems B"
shows "\<exists>k \<in> {..< dist_el_card B}. x = diag_idx_to_el B k"
proof -
  have "diag_idx_to_el B ` {..<dist_el_card B} = diag_elems B" 
    using diag_idx_to_el_bij[of B] unfolding bij_betw_def by simp
  thus ?thesis using assms by auto
qed

lemma diag_idx_to_el_img:
  assumes "k < dist_el_card B"
shows "diag_idx_to_el B k \<in> diag_elems B"
proof -
  have "diag_idx_to_el B ` {..<dist_el_card B} = diag_elems B" 
    using diag_idx_to_el_bij[of B] unfolding bij_betw_def by simp
  thus ?thesis using assms by auto
qed

lemma diag_elems_real:
  fixes B::"complex Matrix.mat"
  assumes "\<forall>i < dim_row B. B$$(i,i) \<in> Reals"
  shows "diag_elems B \<subseteq> Reals" 
proof
  fix x
  assume "x\<in> diag_elems B"
  hence "\<exists>i < dim_row B. x = B $$(i,i)" using assms unfolding diag_elems_def by auto
  from this obtain i where "i < dim_row B" "x = B $$ (i,i)" by auto
  thus "x \<in> Reals" using assms by simp
qed

lemma diag_elems_Re:
  fixes B::"complex Matrix.mat"
  assumes "\<forall>i < (dim_row B). B$$(i,i) \<in> Reals"
  shows "{Re x|x. x\<in> diag_elems B} = diag_elems B"
proof
  show "{complex_of_real (Re x) |x. x \<in> diag_elems B} \<subseteq> diag_elems B" 
  proof 
    fix x
    assume "x \<in> {complex_of_real (Re x) |x. x \<in> diag_elems B}"
    hence "\<exists>y \<in> diag_elems B. x = Re y" by auto
    from this obtain y where "y\<in> diag_elems B" and "x = Re y" by auto
    hence "y = x" using assms diag_elems_real[of B] by auto
    thus "x\<in> diag_elems B" using \<open>y\<in> diag_elems B\<close> by simp
  qed
  show "diag_elems B \<subseteq> {complex_of_real (Re x) |x. x \<in> diag_elems B}" 
  proof
    fix x
    assume "x \<in> diag_elems B"
    hence "Re x = x" using assms diag_elems_real[of B] by auto
    thus "x\<in> {complex_of_real (Re x) |x. x \<in> diag_elems B}" using \<open>x\<in> diag_elems B\<close> by force
  qed
qed

lemma  diag_idx_to_el_real:
  fixes B::"complex Matrix.mat"
  assumes "\<forall>i < dim_row B. B$$(i,i) \<in> Reals"
and "i < dist_el_card B"
shows "Re (diag_idx_to_el B i) = diag_idx_to_el B i"
proof -
  have "diag_idx_to_el B i \<in> diag_elems B" using diag_idx_to_el_img[of i B] assms by simp
  hence "diag_idx_to_el B i \<in> Reals" using diag_elems_real[of B] assms by auto
  thus ?thesis by simp
qed

lemma diag_elem_indices_empty:
  assumes "B \<in> carrier_mat dimR dimC"
  and "i < (dist_el_card B)"
and "j < (dist_el_card B)"
and "i\<noteq> j"
shows "diag_elem_indices (diag_idx_to_el B i) B \<inter> 
  (diag_elem_indices (diag_idx_to_el B j) B) = {}"
proof (rule ccontr)
  assume "diag_elem_indices (diag_idx_to_el B i) B \<inter> 
    diag_elem_indices (diag_idx_to_el B j) B \<noteq> {}"
  hence "\<exists>x. x\<in> diag_elem_indices (diag_idx_to_el B i) B \<inter> 
    diag_elem_indices (diag_idx_to_el B j) B" by auto
  from this obtain x where 
    xprop: "x\<in> diag_elem_indices (diag_idx_to_el B i) B \<inter> 
    diag_elem_indices (diag_idx_to_el B j) B" by auto
  hence "B $$ (x,x) = (diag_idx_to_el B i)" 
    using diag_elem_indices_elem[of x "diag_idx_to_el B i"] by simp
  moreover have "B $$ (x,x) = (diag_idx_to_el B j)" 
    using diag_elem_indices_elem[of x "diag_idx_to_el B j"] xprop by simp
  ultimately have "diag_idx_to_el B i = diag_idx_to_el B j" by simp
  hence "i = j" using diag_idx_to_el_less_inj assms by auto
  thus False using assms by simp
qed

lemma (in cpx_sq_mat) diag_elem_indices_disjoint:
  assumes "B\<in> carrier_mat dimR dimC"
  shows "disjoint_family_on (\<lambda>n. diag_elem_indices (diag_idx_to_el B n) B) 
    {..<dist_el_card B}" unfolding disjoint_family_on_def 
proof (intro ballI impI)
  fix p m
  assume "m\<in> {..< dist_el_card B}" and "p\<in> {..< dist_el_card B}" and "m\<noteq> p"      
  thus "diag_elem_indices (diag_idx_to_el B m) B \<inter> 
    diag_elem_indices (diag_idx_to_el B p) B = {}" 
    using diag_elem_indices_empty  assms fc_mats_carrier by simp
qed

lemma diag_elem_indices_union:
  assumes "B\<in> carrier_mat dimR dimC"
  shows "(\<Union> i \<in> {..< dist_el_card B}. diag_elem_indices (diag_idx_to_el B i) B) = 
    {..< dimR}"
proof
  show "(\<Union>i<dist_el_card B. diag_elem_indices (diag_idx_to_el B i) B) \<subseteq> {..<dimR}"
  proof
    fix x 
    assume "x \<in> (\<Union>i<dist_el_card B. diag_elem_indices (diag_idx_to_el B i) B)"
    hence "\<exists>i < dist_el_card B. x\<in> diag_elem_indices (diag_idx_to_el B i) B" by auto
    from this obtain i where "i < dist_el_card B" 
      "x\<in> diag_elem_indices (diag_idx_to_el B i) B" by auto
    hence "x < dimR" using diag_elem_indices_elem[of x _ B] assms by simp
    thus "x \<in> {..< dimR}" by auto
  qed
next
  show "{..<dimR} \<subseteq> (\<Union>i<dist_el_card B. diag_elem_indices (diag_idx_to_el B i) B)"
  proof
    fix j
    assume "j\<in> {..< dimR}"
    hence "j < dim_row B" using assms by simp
    hence "B$$(j,j) \<in> diag_elems B" by simp
    hence "\<exists>k \<in> {..< dist_el_card B}. B$$(j,j) = diag_idx_to_el B k" 
      using diag_idx_to_el_less_surj[of "B $$(j,j)"] by simp
    from this obtain k where kprop: "k \<in> {..< dist_el_card B}" 
      "B$$(j,j) = diag_idx_to_el B k" by auto
    hence "j \<in> diag_elem_indices (diag_idx_to_el B k) B" using \<open>j < dim_row B\<close> 
        diag_elem_indices_itself by fastforce 
    thus "j \<in> (\<Union>i<dist_el_card B. diag_elem_indices (diag_idx_to_el B i) B)" 
      using kprop by auto
  qed
qed


subsubsection \<open>Construction of measurement outcomes\<close>

text \<open>The construction of a projective measurement for a hermitian matrix $A$ is based on the Schur
decomposition $A = U*B*U^\dagger$, where $B$ is diagonal and $U$ is unitary. The columns of $U$ are
normalized and pairwise orthogonal; they are used to construct the projectors associated with
a measurement value\<close>

definition (in cpx_sq_mat) project_vecs where
"project_vecs (f::nat \<Rightarrow> complex Matrix.vec) N = sum_mat (\<lambda>i. rank_1_proj (f i)) N"

lemma (in cpx_sq_mat) project_vecs_dim:
  assumes "\<forall>i \<in> N. dim_vec (f i) = dimR"
  shows "project_vecs f N \<in> fc_mats" 
proof -
  have "project_vecs f N \<in> carrier_mat dimR dimC" unfolding project_vecs_def 
  proof (rule sum_mat_carrier)
    show "\<And>i. i \<in> N \<Longrightarrow> rank_1_proj (f i) \<in> fc_mats" using assms fc_mats_carrier rank_1_proj_dim
      dim_eq rank_1_proj_carrier by fastforce
  qed
  thus ?thesis using fc_mats_carrier by simp
qed

definition (in cpx_sq_mat) mk_meas_outcome where
"mk_meas_outcome B U = (\<lambda>i. (Re (diag_idx_to_el B i), 
  project_vecs (\<lambda>i. zero_col U i) (diag_elem_indices (diag_idx_to_el B i) B)))"

lemma (in cpx_sq_mat) mk_meas_outcome_carrier:
  assumes "Complex_Matrix.unitary U"
  and "U \<in> fc_mats"
  and "B\<in> fc_mats"
shows "meas_outcome_prj ((mk_meas_outcome B U) j) \<in> fc_mats"
proof -
  have "project_vecs (\<lambda>i. zero_col U i) (diag_elem_indices (diag_idx_to_el B j) B) \<in> fc_mats" 
    using project_vecs_dim by (simp add: assms(2) zero_col_dim)
  thus ?thesis unfolding mk_meas_outcome_def meas_outcome_prj_def by simp
qed

lemma (in cpx_sq_mat) mk_meas_outcome_sum_id:
  assumes "Complex_Matrix.unitary U"
  and "U \<in> fc_mats"
  and "B\<in> fc_mats"
shows "sum_mat (\<lambda>j. meas_outcome_prj ((mk_meas_outcome B U) j)) 
  {..<(dist_el_card B)} = 1\<^sub>m dimR"
proof -
  have "sum_mat (\<lambda>j. meas_outcome_prj ((mk_meas_outcome B U) j)) {..<(dist_el_card B)} =
    sum_mat (\<lambda>j. project_vecs (\<lambda>i. zero_col U i) (diag_elem_indices (diag_idx_to_el B j) B)) 
    {..<(dist_el_card B)}"
    unfolding mk_meas_outcome_def meas_outcome_prj_def by simp
  also have "... = sum_mat (\<lambda>i. rank_1_proj (zero_col U i)) 
    (\<Union>j<dist_el_card B. diag_elem_indices (diag_idx_to_el B j) B)" 
    unfolding project_vecs_def sum_mat_def
  proof (rule disj_family_sum_with[symmetric])
    show "\<forall>j. rank_1_proj (zero_col U j) \<in> fc_mats" using zero_col_dim fc_mats_carrier dim_eq
      by (metis assms(2) rank_1_proj_carrier)
    show "finite {..<dist_el_card B}" by simp 
    show "\<And>i. i \<in> {..<dist_el_card B} \<Longrightarrow> finite (diag_elem_indices (diag_idx_to_el B i) B)" 
      using diag_elem_indices_finite by simp
    show "disjoint_family_on (\<lambda>n. diag_elem_indices (diag_idx_to_el B n) B) 
      {..<dist_el_card B}" 
      unfolding disjoint_family_on_def 
    proof (intro ballI impI)
      fix p m
      assume "m\<in> {..< dist_el_card B}" and "p\<in> {..< dist_el_card B}" and "m\<noteq> p"      
      thus "diag_elem_indices (diag_idx_to_el B m) B \<inter> 
        diag_elem_indices (diag_idx_to_el B p) B = {}" 
        using diag_elem_indices_empty  assms fc_mats_carrier by simp
    qed
  qed
  also have "... = sum_mat (\<lambda>i. rank_1_proj (zero_col U i)) {..< dimR}" 
    using diag_elem_indices_union[of B] assms fc_mats_carrier by simp
  also have "... = sum_mat (\<lambda>i. rank_1_proj (Matrix.col U i)) {..< dimR}"
  proof (rule sum_mat_cong, simp)
    show "\<And>i. i \<in> {..<dimR} \<Longrightarrow> rank_1_proj (zero_col U i) \<in> fc_mats" using dim_eq
      by (metis assms(2) local.fc_mats_carrier rank_1_proj_carrier zero_col_dim)
    thus "\<And>i. i \<in> {..<dimR} \<Longrightarrow> rank_1_proj (Matrix.col U i) \<in> fc_mats" using dim_eq
      by (metis lessThan_iff zero_col_col)
    show "\<And>i. i \<in> {..<dimR} \<Longrightarrow> rank_1_proj (zero_col U i) = rank_1_proj (Matrix.col U i)"
      by (simp add: zero_col_col) 
  qed
  also have "... = 1\<^sub>m dimR" using sum_rank_1_proj_unitary assms by simp
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) make_meas_outcome_prj_ortho:
  assumes "Complex_Matrix.unitary U"
  and "U \<in> fc_mats"
  and "B\<in> fc_mats"
  and "i < dist_el_card B"
  and "j < dist_el_card B"
  and "i \<noteq> j"
shows "meas_outcome_prj ((mk_meas_outcome B U) i) * 
  meas_outcome_prj ((mk_meas_outcome B U) j) = 0\<^sub>m dimR dimR" 
proof -
  define Pi where "Pi = sum_mat (\<lambda>k. rank_1_proj (zero_col U k)) 
    (diag_elem_indices (diag_idx_to_el B i) B)" 
  have sneqi: "meas_outcome_prj (mk_meas_outcome B U i) = Pi" 
    unfolding mk_meas_outcome_def project_vecs_def Pi_def meas_outcome_prj_def by simp
  define Pj where "Pj = sum_mat (\<lambda>k. rank_1_proj (zero_col U k)) 
    (diag_elem_indices (diag_idx_to_el B j) B)" 
  have sneqj: "meas_outcome_prj (mk_meas_outcome B U j) = Pj"      
    unfolding mk_meas_outcome_def project_vecs_def Pj_def meas_outcome_prj_def by simp
  have "Pi * Pj = 0\<^sub>m dimR dimR" unfolding Pi_def
  proof (rule sum_mat_left_ortho_zero)
    show "finite (diag_elem_indices (diag_idx_to_el B i) B)"
      using diag_elem_indices_finite[of _ B] by simp
    show km: "\<And>k. k \<in> diag_elem_indices (diag_idx_to_el B i) B \<Longrightarrow> 
      rank_1_proj (zero_col U k) \<in> fc_mats" using zero_col_dim assms fc_mats_carrier dim_eq 
      by (metis rank_1_proj_carrier) 
    show "Pj \<in> fc_mats" using sneqj assms mk_meas_outcome_carrier by auto
    show "\<And>k. k \<in> diag_elem_indices (diag_idx_to_el B i) B \<Longrightarrow> 
      rank_1_proj (zero_col U k) * Pj = 0\<^sub>m dimR dimR"
    proof -
      fix k
      assume "k \<in> diag_elem_indices (diag_idx_to_el B i) B"
      show "rank_1_proj (zero_col U k) * Pj = 0\<^sub>m dimR dimR" unfolding Pj_def
      proof (rule sum_mat_right_ortho_zero)
        show "finite (diag_elem_indices (diag_idx_to_el B j) B)"
          using diag_elem_indices_finite[of _ B] by simp
        show "\<And>i. i \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow> 
          rank_1_proj (zero_col U i) \<in> fc_mats" using zero_col_dim assms fc_mats_carrier dim_eq 
          by (metis rank_1_proj_carrier) 
        show "rank_1_proj (zero_col U k) \<in> fc_mats"
          by (simp add: km \<open>k \<in> diag_elem_indices (diag_idx_to_el B i) B\<close>) 
        show "\<And>i. i \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow>
         rank_1_proj (zero_col U k) * rank_1_proj (zero_col U i) = 0\<^sub>m dimR dimR"
        proof -
          fix m
          assume "m \<in> diag_elem_indices (diag_idx_to_el B j) B"
          hence "m \<noteq> k" using \<open>k \<in> diag_elem_indices (diag_idx_to_el B i) B\<close> 
            diag_elem_indices_disjoint[of B] fc_mats_carrier assms unfolding disjoint_family_on_def by auto
          have "\<And>i. i \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow> i < dimR" 
            using diag_elem_indices_elem fc_mats_carrier assms dim_eq by (metis carrier_matD(1)) 
          hence "m < dimR" using \<open>m \<in> diag_elem_indices (diag_idx_to_el B j) B\<close> by simp
          have "\<And>k. k \<in> diag_elem_indices (diag_idx_to_el B i) B \<Longrightarrow> k < dimR" 
            using diag_elem_indices_elem fc_mats_carrier assms dim_eq by (metis carrier_matD(1)) 
          hence "k < dimR" using \<open>k \<in> diag_elem_indices (diag_idx_to_el B i) B\<close> by simp
          show "rank_1_proj (zero_col U k) * rank_1_proj (zero_col U m) = 0\<^sub>m dimR dimR"
            using rank_1_proj_unitary_ne[of U k m] assms \<open>m < dimR\<close> \<open>k < dimR\<close>
            by (metis \<open>m \<noteq> k\<close> zero_col_col)
        qed
      qed
    qed
  qed
  thus ?thesis using sneqi sneqj by simp
qed

lemma (in cpx_sq_mat) make_meas_outcome_prjectors:
  assumes "Complex_Matrix.unitary U"
  and "U \<in> fc_mats"
  and "B\<in> fc_mats"
  and "j < dist_el_card B"
shows "projector (meas_outcome_prj ((mk_meas_outcome B U) j))" unfolding projector_def
proof
  define Pj where "Pj = sum_mat (\<lambda>i. rank_1_proj (zero_col U i)) 
  (diag_elem_indices (diag_idx_to_el B j) B)" 
  have sneq: "meas_outcome_prj (mk_meas_outcome B U j) = Pj"      
    unfolding mk_meas_outcome_def project_vecs_def Pj_def meas_outcome_prj_def by simp
  moreover have "hermitian Pj" unfolding Pj_def
  proof (rule sum_mat_hermitian)
    show "finite (diag_elem_indices (diag_idx_to_el B j) B)" 
      using diag_elem_indices_finite[of _ B] by simp
    show "\<forall>i\<in>diag_elem_indices (diag_idx_to_el B j) B. hermitian (rank_1_proj (zero_col U i))" 
      using rank_1_proj_hermitian by simp
    show "\<forall>i\<in>diag_elem_indices (diag_idx_to_el B j) B. rank_1_proj (zero_col U i) \<in> fc_mats"
      using zero_col_dim fc_mats_carrier dim_eq by (metis assms(2) rank_1_proj_carrier)
  qed
  ultimately show "hermitian (meas_outcome_prj (mk_meas_outcome B U j))" by simp
  have "Pj * Pj = Pj" unfolding Pj_def
  proof (rule sum_mat_ortho_square)
    show "finite (diag_elem_indices (diag_idx_to_el B j) B)" 
      using diag_elem_indices_finite[of _ B] by simp
    show "\<And>i. i \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow>
         rank_1_proj (zero_col U i) * rank_1_proj (zero_col U i) = rank_1_proj (zero_col U i)"
    proof -
      fix i
      assume imem: "i\<in> diag_elem_indices (diag_idx_to_el B j) B"
      hence "i < dimR" using diag_elem_indices_elem fc_mats_carrier assms dim_eq
        by (metis carrier_matD(1)) 
      hence "zero_col U i = Matrix.col U i" using zero_col_col[of i] by simp
      hence "rank_1_proj (zero_col U i) = rank_1_proj (Matrix.col U i)" by simp
      moreover have "rank_1_proj (Matrix.col U i) * rank_1_proj (Matrix.col U i) = 
        rank_1_proj (Matrix.col U i)"  by (rule rank_1_proj_unitary_eq, (auto simp add: assms \<open>i < dimR\<close>))
      ultimately show "rank_1_proj (zero_col U i) * rank_1_proj (zero_col U i) = 
        rank_1_proj (zero_col U i)" by simp
    qed
    show "\<And>i. i \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow> 
      rank_1_proj (zero_col U i) \<in> fc_mats" 
      using zero_col_dim assms fc_mats_carrier dim_eq by (metis rank_1_proj_carrier) 
    have "\<And>i. i \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow> i < dimR" 
        using diag_elem_indices_elem fc_mats_carrier assms dim_eq by (metis carrier_matD(1)) 
    thus "\<And>i ja.
       i \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow>
       ja \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow>
       i \<noteq> ja \<Longrightarrow> rank_1_proj (zero_col U i) * rank_1_proj (zero_col U ja) = 0\<^sub>m dimR dimR" 
      using rank_1_proj_unitary_ne by (simp add: assms(1) assms(2) zero_col_col)
  qed
  thus "meas_outcome_prj (mk_meas_outcome B U j) * 
    meas_outcome_prj (mk_meas_outcome B U j) = 
    meas_outcome_prj (mk_meas_outcome B U j)" 
    using sneq by simp
qed

lemma (in cpx_sq_mat) mk_meas_outcome_fst_inj:
  assumes "\<forall>i < (dim_row B). B$$(i,i) \<in> Reals"
  shows "inj_on (\<lambda>i. meas_outcome_val ((mk_meas_outcome B U) i)) {..<dist_el_card B}" 
    unfolding inj_on_def
proof (intro ballI impI)
  fix x y
  assume  "x \<in> {..<dist_el_card B}" and "y \<in> {..<dist_el_card B}" 
    and "meas_outcome_val (mk_meas_outcome B U x) = 
    meas_outcome_val (mk_meas_outcome B U y)" note xy = this
  hence "diag_idx_to_el B x = Re (diag_idx_to_el B x)" 
    using assms diag_idx_to_el_real by simp
  also have "... = Re (diag_idx_to_el B y)" using xy 
    unfolding mk_meas_outcome_def meas_outcome_val_def by simp
  also have "... = diag_idx_to_el B y" using assms diag_idx_to_el_real xy by simp
  finally have "diag_idx_to_el B x = diag_idx_to_el B y" .
  thus "x = y " using diag_idx_to_el_less_inj xy by simp
qed

lemma (in cpx_sq_mat) mk_meas_outcome_fst_bij:
  assumes "\<forall>i < (dim_row B). B$$(i,i) \<in> Reals"
  shows "bij_betw (\<lambda>i. meas_outcome_val ((mk_meas_outcome B U) i)) {..< dist_el_card B} 
    {Re x|x. x\<in> diag_elems B}" 
  unfolding bij_betw_def
proof
  have "inj_on (\<lambda>x. (meas_outcome_val (mk_meas_outcome B U x))) {..<dist_el_card B}"
    using assms mk_meas_outcome_fst_inj by simp
  moreover have  "{Re x|x. x\<in> diag_elems B} = diag_elems B" using diag_elems_Re[of B] assms by simp
  ultimately show "inj_on (\<lambda>x. meas_outcome_val (mk_meas_outcome B U x)) 
    {..<dist_el_card B}" by simp
  show "(\<lambda>i. meas_outcome_val (mk_meas_outcome B U i)) ` {..<dist_el_card B} = 
    {Re x |x. x \<in> diag_elems B}" unfolding meas_outcome_val_def mk_meas_outcome_def
  proof
    show "(\<lambda>i. fst (Re (diag_idx_to_el B i), project_vecs (zero_col U) 
      (diag_elem_indices (diag_idx_to_el B i) B))) ` {..<dist_el_card B} \<subseteq> 
      {Re x |x. x \<in> diag_elems B}"
      using diag_idx_to_el_bij[of B] bij_betw_apply by fastforce
    show "{Re x |x. x \<in> diag_elems B}
    \<subseteq> (\<lambda>i. fst (Re (diag_idx_to_el B i), 
      project_vecs (zero_col U) (diag_elem_indices (diag_idx_to_el B i) B))) ` 
      {..<dist_el_card B}" using diag_idx_to_el_less_surj by fastforce
  qed
qed


subsubsection \<open>Projective measurement associated with an observable\<close>

definition eigvals where
"eigvals M = (SOME as. char_poly M = (\<Prod>a\<leftarrow>as. [:- a, 1:]) \<and> length as = dim_row M)"

lemma eigvals_poly_length:
  assumes "(M::complex Matrix.mat) \<in> carrier_mat n n"
  shows "char_poly M = (\<Prod>a\<leftarrow>(eigvals M). [:- a, 1:]) \<and> length (eigvals M) = dim_row M"
proof -
  let ?V = "SOME as. char_poly M = (\<Prod>a\<leftarrow>as. [:- a, 1:]) \<and> length as = dim_row M"
  have vprop: "char_poly M = (\<Prod>a\<leftarrow>?V. [:- a, 1:]) \<and> length ?V = dim_row M" using 
      someI_ex[of "\<lambda>as. char_poly M = (\<Prod>a\<leftarrow>as. [:- a, 1:]) \<and> length as = dim_row M"]
     complex_mat_char_poly_factorizable assms  by blast
  show ?thesis by (metis (no_types) eigvals_def vprop)
qed

text \<open>We define the spectrum of a matrix $A$: this is its set of eigenvalues; its elements are
roots of the characteristic polynomial of $A$.\<close>

definition spectrum where
"spectrum M = set (eigvals M)"

lemma spectrum_finite:
  shows "finite (spectrum M)" unfolding spectrum_def by simp

lemma spectrum_char_poly_root: 
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
and "k \<in> spectrum A"
shows "poly (char_poly A) k = 0" using eigvals_poly_length[of A n] assms
  unfolding spectrum_def  eigenvalue_root_char_poly
  by (simp add: linear_poly_root)

lemma spectrum_eigenvalues:
  fixes A::"complex Matrix.mat"
  assumes "A\<in> carrier_mat n n"
and "k\<in> spectrum A"
shows "eigenvalue A k" using eigenvalue_root_char_poly[of A n k] 
    spectrum_char_poly_root[of A n k] assms by simp

text \<open>The main result that is used to construct a projective measurement for a Hermitian matrix
is that it is always possible to decompose it as $A = U*B*U^\dagger$, where $B$ is diagonal and
only contains real elements, and $U$ is unitary.\<close>

definition hermitian_decomp where
"hermitian_decomp A B U \<equiv> similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> diagonal_mat B \<and> 
    diag_mat B = (eigvals A) \<and> unitary U \<and> (\<forall>i < dim_row B. B$$(i, i) \<in> Reals)"

lemma hermitian_decomp_sim: 
  assumes "hermitian_decomp A B U"
  shows "similar_mat_wit A B U (Complex_Matrix.adjoint U)" using assms 
  unfolding hermitian_decomp_def by simp

lemma hermitian_decomp_diag_mat: 
  assumes "hermitian_decomp A B U"
  shows "diagonal_mat B" using assms 
  unfolding hermitian_decomp_def by simp

lemma hermitian_decomp_eigenvalues: 
  assumes "hermitian_decomp A B U"
  shows "diag_mat B = (eigvals A)" using assms 
  unfolding hermitian_decomp_def by simp

lemma hermitian_decomp_unitary: 
  assumes "hermitian_decomp A B U"
  shows "unitary U" using assms 
  unfolding hermitian_decomp_def by simp

lemma hermitian_decomp_real_eigvals: 
  assumes "hermitian_decomp A B U"
  shows "\<forall>i < dim_row B. B$$(i, i) \<in> Reals" using assms 
  unfolding hermitian_decomp_def by simp

lemma hermitian_decomp_dim_carrier: 
  assumes "hermitian_decomp A B U"
  shows "B \<in> carrier_mat (dim_row A) (dim_col A)" using assms 
  unfolding hermitian_decomp_def similar_mat_wit_def
  by (metis (full_types) index_mult_mat(3) index_one_mat(3) insert_subset)

lemma similar_mat_wit_dim_row:
  assumes "similar_mat_wit A B Q R"
  shows "dim_row B = dim_row A" using assms Let_def unfolding  similar_mat_wit_def
  by (meson carrier_matD(1) insert_subset)

lemma (in cpx_sq_mat) hermitian_schur_decomp:
  assumes "hermitian A"
  and "A\<in> fc_mats"
obtains B U where "hermitian_decomp A B U" 
proof -
  {
    have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> (eigvals A). [:- e, 1:])" 
      using assms fc_mats_carrier eigvals_poly_length dim_eq by auto
    obtain B U Q where us: "unitary_schur_decomposition A (eigvals A) = (B,U,Q)" 
      by (cases "unitary_schur_decomposition A (eigvals A)")
    hence pr: "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> diagonal_mat B \<and> 
      diag_mat B = (eigvals A) \<and> unitary U \<and> (\<forall>i < dimR. B$$(i, i) \<in> Reals)" 
      using hermitian_eigenvalue_real assms fc_mats_carrier es dim_eq by auto
    moreover have "dim_row B = dimR" using assms fc_mats_carrier dim_eq similar_mat_wit_dim_row[of A]  
        pr by auto
    ultimately have "hermitian_decomp A B U" unfolding hermitian_decomp_def by simp
    hence "\<exists> B U. hermitian_decomp A B U" by auto
  }
  thus ?thesis using that by auto 
qed

lemma (in cpx_sq_mat) hermitian_spectrum_real:
  assumes "A \<in> fc_mats"
  and "hermitian A"
  and "a \<in> spectrum A"
shows "a \<in> Reals" 
proof -
  obtain B U where bu: "hermitian_decomp A B U"  using assms hermitian_schur_decomp by auto
  hence dimB: "B \<in> carrier_mat dimR dimR" using assms fc_mats_carrier 
      dim_eq hermitian_decomp_dim_carrier[of A] by simp
  hence  Bii: "\<And>i. i < dimR \<Longrightarrow> B$$(i, i) \<in> Reals" using hermitian_decomp_real_eigvals[of A B U]
      bu assms fc_mats_carrier by simp
  have  "diag_mat B = (eigvals A)" using bu hermitian_decomp_eigenvalues[of A B] by simp    
  hence "a \<in> set (diag_mat B)" using assms unfolding spectrum_def by simp
  hence "\<exists>i < length (diag_mat B). a = diag_mat B ! i" by (metis in_set_conv_nth)
  from this obtain i where "i < length (diag_mat B)" and "a = diag_mat B ! i" by auto
  hence "a = B $$ (i,i)" unfolding diag_mat_def by simp
  moreover have  "i < dimR" using dimB \<open>i < length (diag_mat B)\<close> unfolding diag_mat_def by simp
  ultimately show ?thesis using  Bii by simp
qed

lemma (in cpx_sq_mat) spectrum_ne:
  assumes "A\<in> fc_mats"
and "hermitian A" 
shows "spectrum A \<noteq> {}" 
proof -
  obtain B U where bu: "hermitian_decomp A B U"  using assms hermitian_schur_decomp by auto
  hence dimB: "B \<in> carrier_mat dimR dimR" using assms fc_mats_carrier 
      dim_eq hermitian_decomp_dim_carrier[of A] by simp
  have  "diag_mat B = (eigvals A)" using bu hermitian_decomp_eigenvalues[of A B] by simp 
  have "B$$(0,0) \<in> set (diag_mat B)" using dimB npos unfolding diag_mat_def by simp
  hence "set (diag_mat B) \<noteq> {}" by auto
  thus ?thesis unfolding spectrum_def using \<open>diag_mat B = eigvals A\<close> by auto
qed

lemma  unitary_hermitian_eigenvalues:
  fixes U::"complex Matrix.mat"
  assumes "unitary U"
  and "hermitian U"
  and "U \<in> carrier_mat n n"
  and "0 < n"
  and "k \<in> spectrum U"
shows "k \<in> {-1, 1}" 
proof -
  have "cpx_sq_mat n n (carrier_mat n n)" by (unfold_locales, (simp add: assms)+)
  have "eigenvalue U k" using spectrum_eigenvalues assms by simp
  have "k \<in> Reals" using assms \<open>cpx_sq_mat n n (carrier_mat n n)\<close> 
      cpx_sq_mat.hermitian_spectrum_real by simp
  hence "conjugate k = k" by (simp add: Reals_cnj_iff) 
  hence "k\<^sup>2 = 1" using unitary_eigenvalues_norm_square[of U n k] assms
    by (simp add: \<open>eigenvalue U k\<close> power2_eq_square)
  thus ?thesis using power2_eq_1_iff by auto 
qed

lemma  unitary_hermitian_Re_spectrum:
  fixes U::"complex Matrix.mat"
  assumes "unitary U"
  and "hermitian U"
  and "U \<in> carrier_mat n n"
  and "0 < n"
  shows "{Re x|x. x\<in> spectrum U} \<subseteq> {-1,1}"
proof
  fix y
  assume "y\<in> {Re x|x. x\<in> spectrum U}"
  hence "\<exists>x \<in> spectrum U. y = Re x" by auto
  from this obtain x where "x\<in> spectrum U" and "y = Re x" by auto
  hence "x\<in> {-1,1}" using unitary_hermitian_eigenvalues assms by simp
  thus "y \<in> {-1, 1}" using \<open>y = Re x\<close> by auto 
qed

text \<open>The projective measurement associated with matrix $M$ is obtained from its Schur 
decomposition, by considering the number of distinct elements on the resulting diagonal matrix
and constructing the projectors associated with each of them.\<close>

type_synonym proj_meas_rep = "nat \<times> (nat \<Rightarrow> measure_outcome)"

definition proj_meas_size::"proj_meas_rep \<Rightarrow> nat" where
"proj_meas_size P = fst P"

definition proj_meas_outcomes::"proj_meas_rep \<Rightarrow> (nat \<Rightarrow> measure_outcome)" where
"proj_meas_outcomes P = snd P"

definition (in cpx_sq_mat) make_pm::"complex Matrix.mat \<Rightarrow> proj_meas_rep" where
"make_pm A = (let (B,U,_) = unitary_schur_decomposition A (eigvals A) in 
  (dist_el_card B, mk_meas_outcome B U))"

lemma (in cpx_sq_mat) make_pm_decomp:
  shows "make_pm A = (proj_meas_size (make_pm A), proj_meas_outcomes (make_pm A))" 
  unfolding proj_meas_size_def proj_meas_outcomes_def by simp

lemma (in cpx_sq_mat) make_pm_proj_measurement:
  assumes "A \<in> fc_mats"
  and "hermitian A"
  and "make_pm A = (n, M)"
shows "proj_measurement n M" 
proof -
  have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> (eigvals A). [:- e, 1:])" 
    using assms fc_mats_carrier eigvals_poly_length dim_eq by auto
  obtain B U Q where us: "unitary_schur_decomposition A (eigvals A) = (B,U,Q)" 
    by (cases "unitary_schur_decomposition A (eigvals A)", auto)
  then have "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> diagonal_mat B \<and> 
    diag_mat B = (eigvals A) \<and> unitary U \<and> (\<forall>i < dimR. B$$(i, i) \<in> Reals)" 
    using hermitian_eigenvalue_real assms fc_mats_carrier es dim_eq by auto
  hence A: "A = U * B * (Complex_Matrix.adjoint U)" and dB: "diagonal_mat B"
    and Bii: "\<And>i. i < dimR \<Longrightarrow> B$$(i, i) \<in> Reals"
    and dimB: "B \<in> carrier_mat dimR dimR" and dimP: "U \<in> carrier_mat dimR dimR" and 
    dimaP: "Complex_Matrix.adjoint U \<in> carrier_mat dimR dimR" and unit: "unitary U"
    unfolding similar_mat_wit_def Let_def using assms fc_mats_carrier by auto
  hence mpeq: "make_pm A = (dist_el_card B, mk_meas_outcome B U)" using us Let_def 
    unfolding make_pm_def by simp
  hence "n = dist_el_card B" using assms by simp
  have "M = mk_meas_outcome B U" using assms mpeq by simp
  show ?thesis unfolding proj_measurement_def
  proof (intro conjI)
    show "inj_on (\<lambda>i. meas_outcome_val (M i)) {..<n}" 
        using mk_meas_outcome_fst_inj[of B U] 
        \<open>n = dist_el_card B\<close> \<open>M = mk_meas_outcome B U\<close> Bii fc_mats_carrier dimB by auto 
    show "\<forall>j<n. meas_outcome_prj (M j) \<in> fc_mats \<and> projector (meas_outcome_prj (M j))" 
    proof (intro allI impI conjI)
      fix j
      assume "j < n"
      show "meas_outcome_prj (M j) \<in> fc_mats" using \<open>M = mk_meas_outcome B U\<close> assms 
          fc_mats_carrier \<open>j < n\<close> \<open>n = dist_el_card B\<close> dim_eq mk_meas_outcome_carrier 
          dimB dimP unit by blast
      show "projector (meas_outcome_prj (M j))" using make_meas_outcome_prjectors 
          \<open>M = mk_meas_outcome B U\<close>  
          fc_mats_carrier \<open>n = dist_el_card B\<close> unit \<open>j < n\<close> dimB dimP dim_eq by blast
    qed
    show "\<forall>i<n. \<forall>j<n. i \<noteq> j \<longrightarrow> meas_outcome_prj (M i) * meas_outcome_prj (M j) = 
      0\<^sub>m dimR dimR"
    proof (intro allI impI)
      fix i
      fix j
      assume "i < n" and "j < n" and "i\<noteq> j"
      thus "meas_outcome_prj (M i) * meas_outcome_prj (M j) = 0\<^sub>m dimR dimR"
        using make_meas_outcome_prj_ortho[of U B i j] assms dimB dimP fc_mats_carrier dim_eq
        by (simp add: \<open>M = mk_meas_outcome B U\<close> \<open>n = dist_el_card B\<close> unit)
    qed
    show "sum_mat (\<lambda>j. meas_outcome_prj (M j)) {..<n} = 1\<^sub>m dimR" using 
        mk_meas_outcome_sum_id 
        \<open>M = mk_meas_outcome B U\<close> fc_mats_carrier dim_eq \<open>n = dist_el_card B\<close> unit  dimB dimP 
      by blast
  qed
qed

lemma (in cpx_sq_mat) make_pm_proj_measurement':
  assumes "A\<in> fc_mats"
  and "hermitian A"
shows "proj_measurement (proj_meas_size (make_pm A)) (proj_meas_outcomes (make_pm A))" 
  unfolding proj_meas_size_def proj_meas_outcomes_def
  by (rule make_pm_proj_measurement[of A], (simp add: assms)+)

lemma (in cpx_sq_mat) make_pm_projectors:
  assumes "A\<in> fc_mats"
  and "hermitian A"
and "i < proj_meas_size (make_pm A)"
shows "projector (meas_outcome_prj (proj_meas_outcomes (make_pm A) i))"
proof -
  have "proj_measurement (proj_meas_size (make_pm A)) (proj_meas_outcomes (make_pm A))" 
    using assms make_pm_proj_measurement' by simp
  thus ?thesis using proj_measurement_proj assms by simp
qed

lemma (in cpx_sq_mat) make_pm_square:
  assumes "A\<in> fc_mats"
  and "hermitian A"
and "i < proj_meas_size (make_pm A)"
shows "meas_outcome_prj (proj_meas_outcomes (make_pm A) i) \<in> fc_mats"
proof -
  have "proj_measurement (proj_meas_size (make_pm A)) (proj_meas_outcomes (make_pm A))" 
    using assms make_pm_proj_measurement' by simp
  thus ?thesis using proj_measurement_square assms by simp
qed


subsubsection \<open>Properties on the spectrum of a  Hermitian matrix\<close>

lemma (in cpx_sq_mat) hermitian_schur_decomp':
  assumes "hermitian A"
  and "A\<in> fc_mats"
obtains B U where "hermitian_decomp A B U \<and> 
  make_pm A = (dist_el_card B, mk_meas_outcome B U)"
proof -
  {
    have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> (eigvals A). [:- e, 1:])" 
      using assms fc_mats_carrier eigvals_poly_length dim_eq by auto
    obtain B U Q where us: "unitary_schur_decomposition A (eigvals A) = (B,U,Q)" 
      by (cases "unitary_schur_decomposition A (eigvals A)")
    hence pr: "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> diagonal_mat B \<and> 
      diag_mat B = (eigvals A) \<and> unitary U \<and> (\<forall>i < dimR. B$$(i, i) \<in> Reals)" 
      using hermitian_eigenvalue_real assms fc_mats_carrier es dim_eq by auto
    moreover have "dim_row B = dimR" using assms fc_mats_carrier dim_eq similar_mat_wit_dim_row[of A]  
        pr by auto
    ultimately have "hermitian_decomp A B U" unfolding hermitian_decomp_def by simp
    moreover have  "make_pm A = (dist_el_card B, mk_meas_outcome B U)" using us Let_def 
      unfolding make_pm_def hermitian_decomp_def by simp
    ultimately have "\<exists> B U. hermitian_decomp A B U \<and> 
      make_pm A = (dist_el_card B, mk_meas_outcome B U)"  by auto
  }
  thus ?thesis using that  by auto 
qed

lemma (in cpx_sq_mat) spectrum_meas_outcome_val_eq: 
  assumes "hermitian A" 
  and "A \<in> fc_mats"
and "make_pm A = (p, M)"
shows "spectrum A = (\<lambda>i. meas_outcome_val (M i)) `{..< p}" 
proof -
  obtain B U where bu: "hermitian_decomp A B U \<and> 
    make_pm A = (dist_el_card B, mk_meas_outcome B U)" 
    using assms hermitian_schur_decomp'[OF assms(1)] by auto
  hence "p = dist_el_card B" using assms by simp
  have dimB: "B \<in> carrier_mat dimR dimR" using hermitian_decomp_dim_carrier[of A] dim_eq bu assms 
      fc_mats_carrier  by auto
  have Bvals: "diag_mat B = eigvals A" using bu hermitian_decomp_eigenvalues[of A B U] by simp
  have Bii: "\<And>i. i < dimR \<Longrightarrow> B$$(i, i) \<in> Reals" using bu hermitian_decomp_real_eigvals[of A B U] 
      dimB by simp
  have "diag_elems B = set (eigvals A)" using dimB Bvals diag_elems_set_diag_mat[of B] by simp
  have "M = mk_meas_outcome B U" using assms bu by simp  
  {
    fix i
    assume "i < p"
    have "meas_outcome_val (M i) = Re (diag_idx_to_el B i)" 
      using \<open>M = mk_meas_outcome B U\<close> 
      unfolding meas_outcome_val_def mk_meas_outcome_def by simp
    also have "... = diag_idx_to_el B i" using diag_idx_to_el_real dimB \<open>i < p\<close> 
        \<open>p = dist_el_card B\<close> Bii by simp
    finally have "meas_outcome_val (M i) = diag_idx_to_el B i" .
  } note eq = this
  have "bij_betw (diag_idx_to_el B) {..<dist_el_card B} (diag_elems B)" 
    using diag_idx_to_el_bij[of B] by simp
  hence "diag_idx_to_el B ` {..< p} = diag_elems B" using \<open>p = dist_el_card B\<close> 
    unfolding bij_betw_def by simp
  thus ?thesis using eq \<open>diag_elems B = set (eigvals A)\<close> unfolding spectrum_def by auto
qed

lemma (in cpx_sq_mat) spectrum_meas_outcome_val_eq': 
  assumes "hermitian A" 
  and "A \<in> fc_mats"
and "make_pm A = (p, M)"
shows "{Re x|x. x\<in> spectrum A} = (\<lambda>i. meas_outcome_val (M i)) `{..< p}" 
proof
  show "{Re x |x. x \<in> spectrum A} \<subseteq> (\<lambda>i. meas_outcome_val (M i)) ` {..<p}" 
    using spectrum_meas_outcome_val_eq assms by force
  show "(\<lambda>i. meas_outcome_val (M i)) ` {..<p} \<subseteq> {Re x |x. x \<in> spectrum A}" 
    using spectrum_meas_outcome_val_eq assms by force
qed

lemma (in cpx_sq_mat) make_pm_eigenvalues:
  assumes "A\<in> fc_mats"
  and "hermitian A"
and "i < proj_meas_size (make_pm A)"
shows "meas_outcome_val (proj_meas_outcomes (make_pm A) i) \<in> spectrum A" 
  using spectrum_meas_outcome_val_eq[of A] assms make_pm_decomp by auto

lemma (in cpx_sq_mat) make_pm_spectrum:
  assumes "A\<in> fc_mats"
  and "hermitian A"
  and "make_pm A = (p,M)"
shows "(\<lambda>i. meas_outcome_val (proj_meas_outcomes (make_pm A) i)) ` {..< p} = spectrum A" 
proof
  show "(\<lambda>x. complex_of_real (meas_outcome_val (proj_meas_outcomes (make_pm A) x))) ` {..<p} \<subseteq> 
    spectrum A"
    using assms make_pm_eigenvalues make_pm_decomp
    by (metis (mono_tags, lifting) Pair_inject image_subsetI lessThan_iff)
  show "spectrum A \<subseteq> 
    (\<lambda>x. complex_of_real (meas_outcome_val (proj_meas_outcomes (make_pm A) x))) ` {..<p}"
    by (metis Pair_inject assms equalityE  make_pm_decomp spectrum_meas_outcome_val_eq)
qed

lemma (in cpx_sq_mat) spectrum_size:
  assumes "hermitian A"
  and "A\<in> fc_mats"
and "make_pm A = (p, M)"
shows "p = card (spectrum A)"
proof -
  obtain B U where bu: "hermitian_decomp A B U \<and> 
    make_pm A = (dist_el_card B, mk_meas_outcome B U)" 
    using assms hermitian_schur_decomp'[OF assms(1)] by auto
  hence "p = dist_el_card B" using assms by simp
  have "spectrum A = set (diag_mat B)" using bu hermitian_decomp_eigenvalues[of A B U] 
    unfolding spectrum_def by simp
  also have "... = diag_elems B" using diag_elems_set_diag_mat[of B] by simp
  finally have "spectrum A = diag_elems B" .
  thus ?thesis using \<open>p = dist_el_card B\<close> unfolding dist_el_card_def by simp
qed

lemma (in cpx_sq_mat) spectrum_size':
  assumes "hermitian A"
and "A\<in> fc_mats"
shows "proj_meas_size (make_pm A) = card (spectrum A)" using spectrum_size 
  unfolding proj_meas_size_def
  by (metis assms fst_conv surj_pair)

lemma (in cpx_sq_mat) make_pm_projectors':
  assumes "hermitian A"
  and "A \<in> fc_mats"
  and "a<card (spectrum A)"
shows "projector (meas_outcome_prj (proj_meas_outcomes (make_pm A) a))" 
  by (rule make_pm_projectors, (simp add: assms spectrum_size')+)

lemma (in cpx_sq_mat) meas_outcome_prj_carrier:
  assumes "hermitian A"
  and "A \<in> fc_mats"
  and "a<card (spectrum A)"
shows "meas_outcome_prj (proj_meas_outcomes (make_pm A) a) \<in> fc_mats" 
proof (rule proj_measurement_square)
  show "proj_measurement (proj_meas_size (make_pm A)) (proj_meas_outcomes (make_pm A))"
    using make_pm_proj_measurement' assms by simp
  show "a < proj_meas_size (make_pm A)" using assms 
      spectrum_size[of _ "proj_meas_size (make_pm A)"] make_pm_decomp[of A] by simp
qed

lemma (in cpx_sq_mat) meas_outcome_prj_trace_real:
  assumes "hermitian A"
  and "density_operator R"
  and "R \<in> fc_mats"
  and "A\<in> fc_mats"
  and "a<card (spectrum A)"
shows "Re (Complex_Matrix.trace (R * meas_outcome_prj (proj_meas_outcomes (make_pm A) a))) =
  Complex_Matrix.trace (R * meas_outcome_prj (proj_meas_outcomes (make_pm A) a))" 
proof (rule trace_proj_pos_real)
  show "R \<in> carrier_mat dimR dimR" using fc_mats_carrier assms dim_eq by simp
  show "Complex_Matrix.positive R" using assms unfolding density_operator_def by simp
  show "projector (meas_outcome_prj (proj_meas_outcomes (make_pm A) a))" using assms 
      make_pm_projectors' by simp
  show "meas_outcome_prj (proj_meas_outcomes (make_pm A) a) \<in> carrier_mat dimR dimR" 
    using meas_outcome_prj_carrier assms 
    dim_eq fc_mats_carrier by simp
qed

lemma (in cpx_sq_mat) sum_over_spectrum:
  assumes "A\<in> fc_mats"
and "hermitian A"
and "make_pm A = (p, M)"
shows "(\<Sum> y \<in> spectrum A. f y) =  (\<Sum> i < p. f (meas_outcome_val (M i)))"
proof (rule sum.reindex_cong)
show "spectrum A =(\<lambda>x. (meas_outcome_val (M x)))` {..< p}" 
    using spectrum_meas_outcome_val_eq assms by simp
  show "inj_on (\<lambda>x. complex_of_real (meas_outcome_val (M x))) {..<p}"
  proof -
    have "inj_on (\<lambda>x. (meas_outcome_val (M x))) {..<p}" 
        using make_pm_proj_measurement[of A p M] assms proj_measurement_inj by simp
    thus ?thesis by (simp add: inj_on_def) 
  qed
qed simp

lemma (in cpx_sq_mat) sum_over_spectrum':
  assumes "A\<in> fc_mats"
and "hermitian A"
and "make_pm A = (p, M)"
shows "(\<Sum> y \<in> {Re x|x. x \<in> spectrum A}. f y) =  (\<Sum> i < p. f (meas_outcome_val (M i)))"
proof (rule sum.reindex_cong)
  show "{Re x|x. x \<in> spectrum A} =(\<lambda>x. (meas_outcome_val (M x)))` {..< p}" 
    using spectrum_meas_outcome_val_eq' assms by simp
  show "inj_on (\<lambda>x. (meas_outcome_val (M x))) {..<p}" using make_pm_proj_measurement[of A p M]
        assms proj_measurement_inj by simp
qed simp

text \<open>When a matrix $A$ is decomposed into a projective measurement $\{(\lambda_a, \pi_a)\}$, it 
can be recovered by the formula $A = \sum \lambda_a \pi_a$.\<close>

lemma (in cpx_sq_mat) make_pm_sum:
  assumes "A \<in> fc_mats"
  and "hermitian A"
  and "make_pm A = (p, M)"
shows "sum_mat (\<lambda>i.  (meas_outcome_val (M i)) \<cdot>\<^sub>m meas_outcome_prj (M i)) {..< p} = A" 
proof -
  have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> (eigvals A). [:- e, 1:])" 
    using assms fc_mats_carrier eigvals_poly_length dim_eq by auto
  obtain B U Q where us: "unitary_schur_decomposition A (eigvals A) = (B,U,Q)" 
    by (cases "unitary_schur_decomposition A (eigvals A)", auto)
  then have "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> diagonal_mat B \<and> 
    diag_mat B = (eigvals A) 
    \<and> unitary U \<and> (\<forall>i < dimR. B$$(i, i) \<in> Reals)" 
    using hermitian_eigenvalue_real assms fc_mats_carrier es dim_eq by auto
  hence A: "A = U * B * (Complex_Matrix.adjoint U)" and dB: "diagonal_mat B"
    and Bii: "\<And>i. i < dimR \<Longrightarrow> B$$(i, i) \<in> Reals"
    and dimB: "B \<in> carrier_mat dimR dimR" and dimP: "U \<in> carrier_mat dimR dimR" and 
    dimaP: "Complex_Matrix.adjoint U \<in> carrier_mat dimR dimR" and unit: "unitary U"
    unfolding similar_mat_wit_def Let_def using assms fc_mats_carrier by auto
  hence mpeq: "make_pm A = (dist_el_card B, mk_meas_outcome B U)" using us Let_def 
    unfolding make_pm_def by simp
  hence "p = dist_el_card B" using assms by simp
  have "M = mk_meas_outcome B U" using assms mpeq by simp
  have "sum_mat (\<lambda>i. meas_outcome_val (M i) \<cdot>\<^sub>m meas_outcome_prj (M i)) {..< p} = 
    sum_mat (\<lambda>j. Re (diag_idx_to_el B j)\<cdot>\<^sub>m project_vecs (\<lambda>i. zero_col U i) 
    (diag_elem_indices (diag_idx_to_el B j) B)) {..<(dist_el_card B)}" 
    using \<open>p = dist_el_card B\<close> 
    \<open>M = mk_meas_outcome B U\<close> unfolding meas_outcome_val_def meas_outcome_prj_def 
      mk_meas_outcome_def by simp
  also have "... = sum_mat
     (\<lambda>j. sum_mat (\<lambda>i. (Re (diag_idx_to_el B j)) \<cdot>\<^sub>m rank_1_proj (zero_col U i)) 
    (diag_elem_indices (diag_idx_to_el B j) B)) {..<dist_el_card B}"  
    unfolding project_vecs_def
  proof (rule sum_mat_cong)
    show "finite {..<dist_el_card B}" by simp
    show "\<And>i. i \<in> {..<dist_el_card B} \<Longrightarrow>
         complex_of_real (Re (diag_idx_to_el B i)) \<cdot>\<^sub>m
         sum_mat (\<lambda>i. rank_1_proj (zero_col U i)) (diag_elem_indices (diag_idx_to_el B i) B)
         \<in> fc_mats" using assms fc_mats_carrier dimP project_vecs_def project_vecs_dim zero_col_dim 
        dim_eq by auto
    show "\<And>i. i \<in> {..<dist_el_card B} \<Longrightarrow>
         sum_mat (\<lambda>ia. complex_of_real (Re (diag_idx_to_el B i)) \<cdot>\<^sub>m rank_1_proj (zero_col U ia))
          (diag_elem_indices (diag_idx_to_el B i) B) \<in> fc_mats" using assms fc_mats_carrier dimP 
      project_vecs_def project_vecs_dim zero_col_dim dim_eq
      by (metis (no_types, lifting) rank_1_proj_carrier cpx_sq_mat_smult sum_mat_carrier)
    show "\<And>j. j \<in> {..<dist_el_card B} \<Longrightarrow>
          (Re (diag_idx_to_el B j)) \<cdot>\<^sub>m  sum_mat (\<lambda>i. rank_1_proj (zero_col U i)) 
        (diag_elem_indices (diag_idx_to_el B j) B) =
         sum_mat (\<lambda>i. complex_of_real (Re (diag_idx_to_el B j)) \<cdot>\<^sub>m rank_1_proj (zero_col U i))
          (diag_elem_indices (diag_idx_to_el B j) B)"
    proof -
      fix j
      assume "j \<in> {..<dist_el_card B}"
      show " (Re (diag_idx_to_el B j)) \<cdot>\<^sub>m sum_mat (\<lambda>i. rank_1_proj (zero_col U i)) 
         (diag_elem_indices (diag_idx_to_el B j) B) =
        sum_mat (\<lambda>i. (Re (diag_idx_to_el B j)) \<cdot>\<^sub>m rank_1_proj (zero_col U i))
          (diag_elem_indices (diag_idx_to_el B j) B)" 
      proof (rule smult_sum_mat)
        show "finite (diag_elem_indices (diag_idx_to_el B j) B)" 
          using diag_elem_indices_finite[of _ B] by simp
        show "\<And>i. i \<in> diag_elem_indices (diag_idx_to_el B j) B \<Longrightarrow> 
          rank_1_proj (zero_col U i) \<in> fc_mats" 
          using dim_eq by (metis dimP local.fc_mats_carrier rank_1_proj_carrier zero_col_dim)
      qed
    qed
  qed
  also have "... = sum_mat
     (\<lambda>j. sum_mat (\<lambda>ia. (diag_mat B ! ia) \<cdot>\<^sub>m rank_1_proj (zero_col U ia)) 
    (diag_elem_indices (diag_idx_to_el B j) B)) {..<dist_el_card B}"    
  proof (rule sum_mat_cong)
    show "finite {..<dist_el_card B}" by simp
    show "\<And>i. i \<in> {..<dist_el_card B} \<Longrightarrow>
         sum_mat (\<lambda>ia. complex_of_real (Re (diag_idx_to_el B i)) \<cdot>\<^sub>m rank_1_proj (zero_col U ia))
          (diag_elem_indices (diag_idx_to_el B i) B) \<in> fc_mats" using assms fc_mats_carrier dimP 
      project_vecs_def project_vecs_dim zero_col_dim dim_eq
      by (metis (no_types, lifting) rank_1_proj_carrier cpx_sq_mat_smult sum_mat_carrier)
    show "\<And>i. i \<in> {..<dist_el_card B} \<Longrightarrow>
         local.sum_mat (\<lambda>ia.  (diag_mat B ! ia) \<cdot>\<^sub>m rank_1_proj (zero_col U ia))
          (diag_elem_indices (diag_idx_to_el B i) B) \<in> fc_mats" using assms fc_mats_carrier dimP 
      project_vecs_def project_vecs_dim zero_col_dim dim_eq
      by (metis (no_types, lifting) rank_1_proj_carrier cpx_sq_mat_smult sum_mat_carrier)
    show "\<And>i. i \<in> {..<dist_el_card B} \<Longrightarrow>
         sum_mat (\<lambda>ia. (Re (diag_idx_to_el B i)) \<cdot>\<^sub>m rank_1_proj (zero_col U ia))
          (diag_elem_indices (diag_idx_to_el B i) B) =
         sum_mat (\<lambda>ia. (diag_mat B ! ia) \<cdot>\<^sub>m rank_1_proj (zero_col U ia))
          (diag_elem_indices (diag_idx_to_el B i) B)"
    proof -
      fix i
      assume "i\<in> {..< dist_el_card B}"
      show "sum_mat (\<lambda>ia. (Re (diag_idx_to_el B i)) \<cdot>\<^sub>m rank_1_proj (zero_col U ia))
          (diag_elem_indices (diag_idx_to_el B i) B) =
         sum_mat (\<lambda>ia. (diag_mat B ! ia) \<cdot>\<^sub>m rank_1_proj (zero_col U ia))
          (diag_elem_indices (diag_idx_to_el B i) B)"
      proof (rule sum_mat_cong)
        show "finite (diag_elem_indices (diag_idx_to_el B i) B)" 
          using diag_elem_indices_finite[of _ B] by simp
        show "\<And>ia. ia \<in> diag_elem_indices (diag_idx_to_el B i) B \<Longrightarrow> 
          (Re (diag_idx_to_el B i)) \<cdot>\<^sub>m rank_1_proj (zero_col U ia) \<in> fc_mats"
          using assms fc_mats_carrier dimP project_vecs_def project_vecs_dim zero_col_dim dim_eq 
          by (metis (no_types, lifting) rank_1_proj_carrier cpx_sq_mat_smult)
        show "\<And>ia. ia \<in> diag_elem_indices (diag_idx_to_el B i) B \<Longrightarrow> 
          (diag_mat B !ia) \<cdot>\<^sub>m rank_1_proj (zero_col U ia) \<in> fc_mats"
          using assms fc_mats_carrier dimP project_vecs_def project_vecs_dim zero_col_dim dim_eq 
          by (metis (no_types, lifting) rank_1_proj_carrier cpx_sq_mat_smult)
        show "\<And>ia. ia \<in> diag_elem_indices (diag_idx_to_el B i) B \<Longrightarrow>
          (Re (diag_idx_to_el B i)) \<cdot>\<^sub>m rank_1_proj (zero_col U ia) =
          (diag_mat B ! ia) \<cdot>\<^sub>m rank_1_proj (zero_col U ia)"
        proof -
          fix ia
          assume ia: "ia \<in> diag_elem_indices (diag_idx_to_el B i) B"
          hence "ia < dim_row B" using diag_elem_indices_elem[of ia _ B]  by simp
          have "Re (diag_idx_to_el B i) = Re (B $$ (ia, ia))" 
            using diag_elem_indices_elem[of ia _ B] ia by simp
          also have "... = B $$ (ia, ia)" using Bii using \<open>ia < dim_row B\<close> dimB of_real_Re by blast 
          also have "... = diag_mat B ! ia" using \<open>ia < dim_row B\<close> unfolding diag_mat_def by simp
          finally have "Re (diag_idx_to_el B i) = diag_mat B ! ia" .
          thus "(Re (diag_idx_to_el B i)) \<cdot>\<^sub>m rank_1_proj (zero_col U ia) =
            (diag_mat B ! ia) \<cdot>\<^sub>m rank_1_proj (zero_col U ia)" by simp
        qed
      qed
    qed
  qed
  also have "... = sum_mat 
    (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m rank_1_proj (zero_col U i)) 
    (\<Union>j<dist_el_card B. diag_elem_indices (diag_idx_to_el B j) B)" 
    unfolding project_vecs_def sum_mat_def     
  proof (rule disj_family_sum_with[symmetric])
    show "finite {..<dist_el_card B}" by simp
    show "\<forall>j. (diag_mat B ! j) \<cdot>\<^sub>m rank_1_proj (zero_col U j) \<in> fc_mats" using assms fc_mats_carrier dimP 
      project_vecs_def project_vecs_dim zero_col_dim dim_eq
      by (metis (no_types, lifting) rank_1_proj_carrier cpx_sq_mat_smult)
    show "\<And>i. i \<in> {..<dist_el_card B} \<Longrightarrow> finite (diag_elem_indices (diag_idx_to_el B i) B)"
      by (simp add: diag_elem_indices_finite)
    show "disjoint_family_on (\<lambda>n. diag_elem_indices (diag_idx_to_el B n) B) 
      {..<dist_el_card B}"
      using diag_elem_indices_disjoint[of B] dimB dim_eq by simp
  qed
  also have "... = sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>m rank_1_proj (zero_col U i)) {..< dimR}" 
    using diag_elem_indices_union[of B] dimB dim_eq by simp
  also have "... = sum_mat (\<lambda>i. (diag_mat B ! i) \<cdot>\<^sub>mrank_1_proj (Matrix.col U i)) {..< dimR}"
  proof (rule sum_mat_cong, simp)
    show res: "\<And>i. i \<in> {..<dimR} \<Longrightarrow> (diag_mat B ! i) \<cdot>\<^sub>m rank_1_proj (zero_col U i) \<in> fc_mats"
      using assms fc_mats_carrier dimP project_vecs_def project_vecs_dim zero_col_dim dim_eq
          by (metis (no_types, lifting) rank_1_proj_carrier cpx_sq_mat_smult)
    show "\<And>i. i \<in> {..<dimR} \<Longrightarrow> (diag_mat B ! i) \<cdot>\<^sub>m rank_1_proj (Matrix.col U i) \<in> fc_mats"
      using assms fc_mats_carrier dimP project_vecs_def  project_vecs_dim zero_col_dim
      by (metis res lessThan_iff zero_col_col)  
    show "\<And>i. i \<in> {..<dimR} \<Longrightarrow> (diag_mat B ! i) \<cdot>\<^sub>m rank_1_proj (zero_col U i) = 
      (diag_mat B ! i) \<cdot>\<^sub>m rank_1_proj (Matrix.col U i)"
      by (simp add: zero_col_col) 
  qed
  also have "... = U * B * Complex_Matrix.adjoint U" 
  proof (rule weighted_sum_rank_1_proj_unitary)
    show "diagonal_mat B" using dB .
    show "Complex_Matrix.unitary U" using unit .
    show "U \<in> fc_mats" using fc_mats_carrier dim_eq dimP by simp
    show "B\<in> fc_mats" using fc_mats_carrier dim_eq dimB by simp
  qed
  also have "... = A" using A by simp
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) trace_hermitian_pos_real:
  fixes f::"'a \<Rightarrow> real"
  assumes "hermitian A"
  and "Complex_Matrix.positive R"
  and "A \<in> fc_mats"
  and "R \<in> fc_mats"
shows "Complex_Matrix.trace (R * A) = 
  Re (Complex_Matrix.trace (R * A))"
proof -
  define prj_mems where "prj_mems = make_pm A"
  define p where "p = proj_meas_size prj_mems"
  define meas where "meas = proj_meas_outcomes prj_mems"
  have tre: "Complex_Matrix.trace (R * A) = 
    Complex_Matrix.trace (R * 
    sum_mat (\<lambda>i. (meas_outcome_val (meas i)) \<cdot>\<^sub>m meas_outcome_prj (meas i)) {..< p})"
    using make_pm_sum assms meas_def p_def proj_meas_size_def proj_meas_outcomes_def prj_mems_def 
      meas_outcome_val_def meas_outcome_prj_def by auto 
  also have "... = Re (Complex_Matrix.trace (R * 
    sum_mat (\<lambda>i. (meas_outcome_val (meas i)) \<cdot>\<^sub>m meas_outcome_prj (meas i)) {..< p}))"
  proof (rule trace_sum_mat_proj_pos_real, (auto simp add: assms))
    fix i
    assume "i < p" 
    thus "projector (meas_outcome_prj (meas i))" using make_pm_projectors assms 
      unfolding p_def meas_def prj_mems_def by simp
    show "meas_outcome_prj (meas i) \<in> fc_mats" using make_pm_square assms \<open>i < p\<close>
      unfolding p_def meas_def prj_mems_def by simp
  qed
  also have "... = Re (Complex_Matrix.trace (R * A))" using tre by simp
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) hermitian_Re_spectrum:
  assumes "hermitian A"
and "A\<in> fc_mats"
and "{Re x |x. x \<in> spectrum A} = {a,b}"
shows "spectrum A = {complex_of_real a, complex_of_real b}"
proof
  have ar: "\<And>(a::complex). a \<in> spectrum A \<Longrightarrow> Re a = a" using hermitian_spectrum_real assms by simp
  show "spectrum A \<subseteq> {complex_of_real a, complex_of_real b}" 
  proof
    fix x
    assume "x\<in> spectrum A" 
    hence "Re x = x" using ar by simp
    have "Re x \<in> {a,b}" using \<open>x\<in> spectrum A\<close> assms by blast
    thus "x \<in> {complex_of_real a, complex_of_real b}" using \<open>Re x = x\<close> by auto
  qed
  show "{complex_of_real a, complex_of_real b} \<subseteq> spectrum A"
  proof
    fix x
    assume "x \<in> {complex_of_real a, complex_of_real b}"
    hence "x \<in> {complex_of_real (Re x) |x. x \<in> spectrum A}" using assms
    proof -
      have "\<And>r. r \<notin> {a, b} \<or> (\<exists>c. r = Re c \<and> c \<in> spectrum A)"
        using \<open>{Re x |x. x \<in> spectrum A} = {a, b}\<close> by blast
      then show ?thesis
        using \<open>x \<in> {complex_of_real a, complex_of_real b}\<close> by blast
    qed
    thus "x\<in> spectrum A" using ar by auto
  qed
qed


subsubsection \<open>Similar properties for eigenvalues rather than spectrum indices\<close>

text \<open>In this part we go the other way round: given an eigenvalue of $A$, \verb+spectrum_to_pm_idx+ 
permits to retrieve its index in the associated projective measurement\<close>

definition (in cpx_sq_mat) spectrum_to_pm_idx
  where "spectrum_to_pm_idx A x = (let (B,U,_) = unitary_schur_decomposition A (eigvals A) in 
    diag_el_to_idx B x)"

lemma (in cpx_sq_mat) spectrum_to_pm_idx_bij:
assumes "hermitian A"
  and "A\<in> fc_mats"
shows "bij_betw (spectrum_to_pm_idx A) (spectrum A) {..< card (spectrum A)}"
proof -
  define p where "p = proj_meas_size (make_pm A)"
  define M where "M = proj_meas_outcomes (make_pm A)"
  have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> (eigvals A). [:- e, 1:])" 
      using assms fc_mats_carrier eigvals_poly_length dim_eq by auto
  obtain B U Q where us: "unitary_schur_decomposition A (eigvals A) = (B,U,Q)" 
    by (cases "unitary_schur_decomposition A (eigvals A)")
  hence pr: "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> 
      diag_mat B = (eigvals A)" 
      using hermitian_eigenvalue_real assms fc_mats_carrier es dim_eq by auto
  have "(p,M) = make_pm A" unfolding p_def M_def using make_pm_decomp by simp
  hence "p = dist_el_card B" using assms us unfolding make_pm_def by simp
  have dimB: "B \<in> carrier_mat dimR dimR" using  dim_eq pr assms 
      fc_mats_carrier unfolding similar_mat_wit_def  by auto
  have Bvals: "diag_mat B = eigvals A" using pr hermitian_decomp_eigenvalues[of A B U] by simp
  have "diag_elems B = spectrum A" unfolding spectrum_def using dimB Bvals 
      diag_elems_set_diag_mat[of B] by simp
  moreover have "dist_el_card B = card (spectrum A)" using spectrum_size[of A p M] assms 
      \<open>(p,M) = make_pm A\<close> \<open>p = dist_el_card B\<close> by simp 
  ultimately show "bij_betw (spectrum_to_pm_idx A) (spectrum A) {..< card (spectrum A)}" 
    using diag_el_to_idx_bij us unfolding spectrum_to_pm_idx_def Let_def
    by (metis (mono_tags, lifting) bij_betw_cong case_prod_conv)
qed

lemma (in cpx_sq_mat) spectrum_to_pm_idx_lt_card:
assumes "A\<in> fc_mats"
  and "hermitian A"
and "a\<in> spectrum A"
shows "spectrum_to_pm_idx A a < card (spectrum A)" using spectrum_to_pm_idx_bij[of A] assms
  by (meson bij_betw_apply lessThan_iff)

lemma (in cpx_sq_mat) spectrum_to_pm_idx_inj:
assumes "hermitian A"
  and "A\<in> fc_mats"
shows "inj_on (spectrum_to_pm_idx A) (spectrum A)" using assms spectrum_to_pm_idx_bij
  unfolding bij_betw_def by simp

lemma (in cpx_sq_mat) spectrum_meas_outcome_val_inv:
assumes "A\<in> fc_mats"
  and "hermitian A"
and "make_pm A = (p,M)"
and "i < p"
shows "spectrum_to_pm_idx A (meas_outcome_val (M i)) = i"
proof -
  have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> (eigvals A). [:- e, 1:])" 
      using assms fc_mats_carrier eigvals_poly_length dim_eq by auto
  obtain B U Q where us: "unitary_schur_decomposition A (eigvals A) = (B,U,Q)" 
      by (cases "unitary_schur_decomposition A (eigvals A)")
  hence pr: "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> 
    diag_mat B = (eigvals A) \<and>  (\<forall>i < dimR. B$$(i, i) \<in> Reals)" 
    using hermitian_eigenvalue_real assms fc_mats_carrier es dim_eq by auto
  have "dim_row B = dimR" using assms fc_mats_carrier dim_eq similar_mat_wit_dim_row[of A]  
      pr by auto
  hence "(p,M) = (dist_el_card B, mk_meas_outcome B U)" using assms us 
    unfolding make_pm_def by simp
  hence "M = mk_meas_outcome B U" by simp
  have "meas_outcome_val (M i) = Re (diag_idx_to_el B i)" 
    using \<open>M = mk_meas_outcome B U\<close> unfolding mk_meas_outcome_def 
      meas_outcome_val_def by simp
  also have "... = diag_idx_to_el B i" using pr
    \<open>(p, M) = (dist_el_card B, mk_meas_outcome B U)\<close> \<open>dim_row B = dimR\<close> assms 
    diag_idx_to_el_real by auto 
  finally have "meas_outcome_val (M i) = diag_idx_to_el B i" .
  hence "spectrum_to_pm_idx A (meas_outcome_val (M i)) = 
    spectrum_to_pm_idx A (diag_idx_to_el B i)" by simp
  also have "... = diag_el_to_idx B (diag_idx_to_el B i)" unfolding spectrum_to_pm_idx_def 
    using us by simp
  also have "... = i" using assms unfolding diag_el_to_idx_def
    using \<open>(p, M) = (dist_el_card B, mk_meas_outcome B U)\<close> bij_betw_inv_into_left 
      diag_idx_to_el_bij by fastforce
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) meas_outcome_val_spectrum_inv:
  assumes "A\<in> fc_mats"
  and "hermitian A"
and "x\<in> spectrum A"
and "make_pm A = (p,M)"
shows "meas_outcome_val (M (spectrum_to_pm_idx A x)) = x"
proof -
  have es: "char_poly A = (\<Prod> (e :: complex) \<leftarrow> (eigvals A). [:- e, 1:])" 
      using assms fc_mats_carrier eigvals_poly_length dim_eq by auto
  obtain B U Q where us: "unitary_schur_decomposition A (eigvals A) = (B,U,Q)" 
      by (cases "unitary_schur_decomposition A (eigvals A)")
    hence pr: "similar_mat_wit A B U (Complex_Matrix.adjoint U) \<and> diagonal_mat B \<and> 
      diag_mat B = (eigvals A) \<and> unitary U \<and> (\<forall>i < dimR. B$$(i, i) \<in> Reals)" 
      using hermitian_eigenvalue_real assms fc_mats_carrier es dim_eq by auto
    have "dim_row B = dimR" using assms fc_mats_carrier dim_eq similar_mat_wit_dim_row[of A]  
        pr by auto
    hence "(p,M) = (dist_el_card B, mk_meas_outcome B U)" using assms us 
      unfolding make_pm_def by simp
    hence "M = mk_meas_outcome B U" by simp
  have  "diag_mat B = (eigvals A)" using pr by simp
  hence "x \<in> set (diag_mat B)" using \<open>diag_mat B = eigvals A\<close> assms unfolding spectrum_def by simp
  hence "x \<in> diag_elems B" using diag_elems_set_diag_mat[of B] by simp
  hence "diag_idx_to_el B (diag_el_to_idx B x) = x" unfolding diag_el_to_idx_def
    by (meson bij_betw_inv_into_right diag_idx_to_el_bij) 
  moreover have "spectrum_to_pm_idx A x = diag_el_to_idx B x" unfolding spectrum_to_pm_idx_def 
    using us by simp
  moreover have "meas_outcome_val (M (spectrum_to_pm_idx A x)) = 
    Re (diag_idx_to_el B (diag_el_to_idx B x))" using \<open>M = mk_meas_outcome B U\<close> 
    unfolding mk_meas_outcome_def meas_outcome_val_def  by (simp add: calculation(2))
  ultimately show ?thesis by simp
qed
  
definition (in cpx_sq_mat) eigen_projector where
"eigen_projector A a = 
  meas_outcome_prj ((proj_meas_outcomes (make_pm A)) (spectrum_to_pm_idx A a))"

lemma (in cpx_sq_mat) eigen_projector_carrier:
  assumes "A\<in> fc_mats"
  and "a\<in> spectrum A"
  and "hermitian A"
shows "eigen_projector A a \<in> fc_mats" unfolding eigen_projector_def 
  using meas_outcome_prj_carrier[of A "spectrum_to_pm_idx A a"] 
    spectrum_to_pm_idx_lt_card[of A a] assms by simp

text \<open>We obtain the following result, which is similar to \verb+make_pm_sum+ but with a sum on 
the elements of the spectrum of Hermitian matrix $A$, which is a more standard statement of the 
spectral decomposition theorem.\<close>

lemma (in cpx_sq_mat) make_pm_sum':
  assumes "A \<in> fc_mats"
  and "hermitian A"
shows "sum_mat (\<lambda>a.  a \<cdot>\<^sub>m (eigen_projector A a)) (spectrum A) = A" 
proof -
  define p where "p = proj_meas_size (make_pm A)"
  define M where "M = proj_meas_outcomes (make_pm A)"
  have "(p,M) = make_pm A" unfolding p_def M_def using make_pm_decomp by simp
  define g where 
    "g = (\<lambda>i. (if i < p 
      then complex_of_real (meas_outcome_val (M i)) \<cdot>\<^sub>m meas_outcome_prj (M i) 
      else (0\<^sub>m dimR dimC)))"
  have g: "\<forall>x. g x \<in> fc_mats"
  proof
    fix x
    show "g x \<in> fc_mats"
    proof (cases "x < p")
      case True
      hence "(meas_outcome_val (M x)) \<cdot>\<^sub>m meas_outcome_prj (M x) \<in> fc_mats" 
        using meas_outcome_prj_carrier
        spectrum_size assms cpx_sq_mat_smult make_pm_proj_measurement proj_measurement_square 
        \<open>(p,M) = make_pm A\<close> by metis
      then show ?thesis unfolding g_def using True by simp
    next
      case False
      then show ?thesis unfolding g_def using zero_mem by simp
    qed
  qed
  define h where "h = (\<lambda>a. (if a \<in> (spectrum A) then a \<cdot>\<^sub>m eigen_projector A a else (0\<^sub>m dimR dimC)))"
  have h: "\<forall>x. h x \<in> fc_mats"
  proof
    fix x
    show "h x \<in> fc_mats"
    proof (cases "x\<in> spectrum A")
    case True
      then show ?thesis unfolding h_def using eigen_projector_carrier[of A x] assms True
        by (simp add: cpx_sq_mat_smult)
    next
    case False
      then show ?thesis unfolding h_def using zero_mem by simp
    qed
  qed
  have "inj_on (spectrum_to_pm_idx A) (spectrum A)" using assms spectrum_to_pm_idx_inj by simp
  moreover have "{..<p} = spectrum_to_pm_idx A ` spectrum A" using \<open>(p,M) = make_pm A\<close>
    spectrum_to_pm_idx_bij spectrum_size unfolding bij_betw_def
    by (metis assms(1) assms(2)) 
  moreover have "\<And>x. x \<in> spectrum A \<Longrightarrow> g (spectrum_to_pm_idx A x) = h x" 
  proof -
    fix a
    assume "a \<in> spectrum A"
    hence "Re a = a" using hermitian_spectrum_real assms by simp 
    have "spectrum_to_pm_idx A a < p" using spectrum_to_pm_idx_lt_card[of A] spectrum_size assms 
      \<open>a \<in> spectrum A\<close> \<open>(p,M) = make_pm A\<close> by metis
    have "g (spectrum_to_pm_idx A a) = 
      (meas_outcome_val (M (spectrum_to_pm_idx A a))) \<cdot>\<^sub>m 
      meas_outcome_prj (M (spectrum_to_pm_idx A a))"
      using \<open>spectrum_to_pm_idx A a < p\<close> unfolding g_def by simp
    also have "... = a \<cdot>\<^sub>m meas_outcome_prj (M (spectrum_to_pm_idx A a))" 
      using meas_outcome_val_spectrum_inv[of A "Re a"] \<open>Re a = a\<close> assms \<open>a \<in> spectrum A\<close> 
        \<open>(p,M) = make_pm A\<close> by metis
    also have "... = h a" using \<open>a \<in> spectrum A\<close> unfolding eigen_projector_def M_def h_def by simp
    finally show "g (spectrum_to_pm_idx A a) = h a" .
  qed
  ultimately have "sum_mat h (spectrum A) = 
    sum_mat g (spectrum_to_pm_idx A ` spectrum A)" unfolding sum_mat_def
    using   sum_with_reindex_cong[symmetric, of g h "spectrum_to_pm_idx A" "spectrum A" "{..< p}"] 
      g h by simp
  also have "... = sum_mat g {..< p}" using \<open>{..<p} = spectrum_to_pm_idx A ` spectrum A\<close> by simp
  also have "... = sum_mat (\<lambda>i. (meas_outcome_val (M i)) \<cdot>\<^sub>m meas_outcome_prj (M i)) {..<p}"
  proof (rule sum_mat_cong, simp)
    fix i
    assume "i \<in> {..< p}"
    hence "i < p" by simp
    show "g i \<in> fc_mats" using g by simp
    show "g i = (meas_outcome_val (M i)) \<cdot>\<^sub>m meas_outcome_prj (M i)" unfolding g_def 
      using \<open>i < p\<close> by simp
    show "(meas_outcome_val (M i)) \<cdot>\<^sub>m meas_outcome_prj (M i) \<in> fc_mats" 
      using meas_outcome_prj_carrier spectrum_size assms cpx_sq_mat_smult 
        make_pm_proj_measurement proj_measurement_square \<open>i < p\<close> \<open>(p,M) = make_pm A\<close> by metis
  qed
  also have "... = A" using make_pm_sum assms \<open>(p,M) = make_pm A\<close> unfolding g_def by simp
  finally have "sum_mat h (spectrum A) = A" .
  moreover have "sum_mat h (spectrum A) = sum_mat (\<lambda>a.  a \<cdot>\<^sub>m (eigen_projector A a)) (spectrum A)"
  proof (rule sum_mat_cong)
    show "finite (spectrum A)" using spectrum_finite[of A] by simp
    fix i
    assume "i\<in> spectrum A"
    thus "h i = i \<cdot>\<^sub>m eigen_projector A i" unfolding h_def by simp
    show "h i \<in> fc_mats" using h by simp
    show "i \<cdot>\<^sub>m eigen_projector A i \<in> fc_mats" using eigen_projector_carrier[of A i] assms 
        \<open>i\<in> spectrum A\<close> by (metis \<open>h i = i \<cdot>\<^sub>m eigen_projector A i\<close> h)
  qed
  ultimately show ?thesis by simp
qed



end