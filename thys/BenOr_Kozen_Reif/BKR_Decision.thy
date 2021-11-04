theory BKR_Decision
  imports BKR_Algorithm
    "Berlekamp_Zassenhaus.Factorize_Rat_Poly"
    "Algebraic_Numbers.Real_Roots"
    "BKR_Proofs"
    "HOL.Deriv"
begin

section "Algorithm"

subsection "Parsing"
  (* Formula type *)
datatype 'a fml =
  And "'a fml" "'a fml"
  | Or "'a fml" "'a fml"
  | Gt 'a   (* 'a > 0 *)
  | Geq 'a  (* 'a \<ge> 0 *)
  | Lt 'a   (* 'a < 0 *)
  | Leq 'a  (* 'a \<le> 0 *)
  | Eq 'a   (* 'a = 0 *)
  | Neq 'a  (* 'a \<noteq> 0 *)

(* Evaluating a formula over a lookup semantics where 'a is nat *)
primrec lookup_sem :: "nat fml \<Rightarrow> ('a::linordered_field list) \<Rightarrow> bool"
  where
    "lookup_sem (And l r) ls = (lookup_sem l ls \<and> lookup_sem r ls)"
  | "lookup_sem (Or l r) ls = (lookup_sem l ls \<or> lookup_sem r ls)"
  | "lookup_sem (Gt p) ls = (ls ! p > 0)"  
  | "lookup_sem (Geq p) ls = (ls ! p \<ge> 0)" 
  | "lookup_sem (Lt p) ls = (ls ! p < 0)" 
  | "lookup_sem (Leq p) ls = (ls ! p \<le> 0)" 
  | "lookup_sem (Eq p) ls = (ls ! p = 0)" 
  | "lookup_sem (Neq p) ls = (ls ! p \<noteq> 0)" 

(* (compute) all polynomials mentioned in a formula *)
primrec poly_list :: "'a fml \<Rightarrow> 'a list"
  where
    "poly_list (And l r) = poly_list l @ poly_list r"  
  | "poly_list (Or l r) = poly_list l @ poly_list r"  
  | "poly_list (Gt p) = [p]"
  | "poly_list (Geq p) = [p]"
  | "poly_list (Lt p) = [p]"
  | "poly_list (Leq p) = [p]"
  | "poly_list (Eq p) = [p]"
  | "poly_list (Neq p) = [p]"

primrec index_of_aux :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat" where
  "index_of_aux [] y n = n"
| "index_of_aux (x#xs) y n =
  (if x = y then n else index_of_aux xs y (n+1))"

definition index_of :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "index_of xs y = index_of_aux xs y 0"

definition convert :: "'a fml \<Rightarrow> (nat fml \<times> 'a list)"
  where
    "convert fml = (
    let ps = remdups (poly_list fml)
    in
    (map_fml (index_of ps) fml, ps)
  )"


subsection "Factoring"

(* Makes sure the result of factorize_rat_poly is monic *)
definition factorize_rat_poly_monic :: "rat poly \<Rightarrow> (rat \<times> (rat poly \<times> nat) list)"
  where
    "factorize_rat_poly_monic p = (
    let (c,fs) =  factorize_rat_poly p ;
        lcs = prod_list (map (\<lambda>(f,i). (lead_coeff f) ^ Suc i) fs) ;
        fs = map (\<lambda>(f,i). (normalize f, i)) fs
    in
    (c * lcs,fs)
  )"

(* Factoring an input list of polynomials *)
definition factorize_polys :: "rat poly list \<Rightarrow> (rat poly list \<times> (rat \<times> (nat \<times> nat) list) list)"
  where
    "factorize_polys ps = (
    let fact_ps = map factorize_rat_poly_monic ps;
        factors = remdups (map fst (concat (map snd fact_ps))) ;
        data = map (\<lambda>(c,fs). (c, map (\<lambda>(f,pow). (index_of factors f, pow) ) fs)) fact_ps
    in
      (factors,data)
  )"

(* After turning a polynomial into factors,
  this turns a sign condition on the factors
  into a sign condition for the polynomial *)
definition undo_factorize :: "rat \<times> (nat \<times> nat) list \<Rightarrow> rat list \<Rightarrow> rat"
  where
    "undo_factorize cfs signs =
   squash
    (case cfs of (c,fs) \<Rightarrow>
    (c * prod_list (map (\<lambda>(f,pow). (signs ! f) ^ Suc pow) fs)))
  "

definition undo_factorize_polys :: "(rat \<times> (nat \<times> nat) list) list \<Rightarrow> rat list \<Rightarrow> rat list"
  where
    "undo_factorize_polys ls signs = map (\<lambda>l. undo_factorize l signs) ls"

subsection "Auxiliary Polynomial"
definition crb:: "real poly \<Rightarrow> int" where
  "crb p = ceiling (2 + max_list_non_empty (map (\<lambda> i. norm (coeff p i)) [0 ..< degree p]) 
    / norm (lead_coeff p))"

(* Because we are using prod_list instead of lcm, it's important that this is called 
    when ps is pairwise coprime. *)
definition coprime_r :: "real poly list \<Rightarrow> real poly"
  where
    "coprime_r ps = pderiv (prod_list ps) * ([:-(crb (prod_list ps)),1:]) * ([:(crb (prod_list ps)),1:])"


subsection "Setting Up the Procedure"
  (* 0 indexed *)
definition insertAt :: "nat \<Rightarrow> 'a  \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insertAt n x ls = take n ls @ x # (drop n ls)"

(* 0 indexed *)
definition removeAt :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "removeAt n ls = take n ls @ (drop (n+1) ls)"

definition find_sgas_aux:: "real poly list \<Rightarrow> rat list list"
  where "find_sgas_aux in_list =
  concat (map (\<lambda>i.
    map (\<lambda>v. insertAt i 0 v) (find_consistent_signs_at_roots (in_list ! i) (removeAt i in_list))
  ) [0..<length in_list])"

(* For an input list of real polynomials, apply BKR to all positions *)
definition find_sgas :: "real poly list \<Rightarrow> rat list list"
  where
    "find_sgas ps = ( 
    let r = coprime_r ps in
    find_consistent_signs_at_roots r ps @ find_sgas_aux ps
  )"

(* Putting the sign condition preprocessing together with BKR *)
definition find_consistent_signs :: "rat poly list \<Rightarrow> rat list list"
  where
    "find_consistent_signs ps = (
     let (fs,data) = factorize_polys ps;
         sgas = find_sgas (map (map_poly of_rat) fs);
         rsgas = map (undo_factorize_polys data) sgas
    in
    (if fs = [] then [(map (\<lambda>x. if poly x 0 < 0 then -1 else if poly x 0 = 0 then 0 else 1) ps)] else rsgas)
  )"


subsection "Deciding Univariate Problems"
definition decide_universal :: "rat poly fml \<Rightarrow> bool"
  where [code]:
    "decide_universal fml = (
    let (fml_struct,polys) = convert fml;
        conds = find_consistent_signs polys
    in
     list_all (lookup_sem fml_struct) conds
  )"

definition decide_existential :: "rat poly fml \<Rightarrow> bool"
  where [code]:
    "decide_existential fml = (
    let (fml_struct,polys) = convert fml;
        conds = find_consistent_signs polys
    in
      find (lookup_sem fml_struct) conds \<noteq> None
  )"

section "Proofs"
subsection "Parsing and Semantics"
  (* Evaluating a formula where 'a is a real poly *)
primrec real_sem :: "real poly fml \<Rightarrow> real \<Rightarrow> bool"
  where
    "real_sem (And l r) x = (real_sem l x \<and> real_sem r x)"
  | "real_sem (Or l r) x = (real_sem l x \<or> real_sem r x)"
  | "real_sem (Gt p) x = (poly p x > 0)" 
  | "real_sem (Geq p) x = (poly p x \<ge> 0)" 
  | "real_sem (Lt p) x = (poly p x < 0)" 
  | "real_sem (Leq p) x = (poly p x \<le> 0)" 
  | "real_sem (Eq p) x = (poly p x = 0)" 
  | "real_sem (Neq p) x = (poly p x \<noteq> 0)" 

(* Evaluating a formula where 'a is a rat poly *)
primrec fml_sem :: "rat poly fml \<Rightarrow> real \<Rightarrow> bool"
  where
    "fml_sem (And l r) x = (fml_sem l x \<and> fml_sem r x)"
  | "fml_sem (Or l r) x = (fml_sem l x \<or> fml_sem r x)"
  | "fml_sem (Gt p) x = (rpoly p x > 0)" 
  | "fml_sem (Geq p) x = (rpoly p x \<ge> 0)" 
  | "fml_sem (Lt p) x = (rpoly p x < 0)" 
  | "fml_sem (Leq p) x = (rpoly p x \<le> 0)" 
  | "fml_sem (Eq p) x = (rpoly p x = 0)" 
  | "fml_sem (Neq p) x = (rpoly p x \<noteq> 0)" 

lemma poly_list_set_fml:
  shows "set (poly_list fml) = set_fml fml"
  apply (induction) by auto

lemma convert_semantics_lem:
  assumes "\<And>p. p \<in> set (poly_list fml) \<Longrightarrow>
    ls ! (index_of ps p) = rpoly p x"
  shows "fml_sem fml x = lookup_sem (map_fml (index_of ps) fml) ls"
  using assms apply (induct fml)
  by auto

lemma index_of_aux_more:
  shows "index_of_aux ls p n \<ge> n"
  apply (induct ls arbitrary: n)
  apply auto
  using Suc_leD by blast

lemma index_of_aux_lookup:
  assumes "p \<in> set ls"
  shows "(index_of_aux ls p n) - n < length ls"
    "ls ! ((index_of_aux ls p n) - n) = p"
  using assms apply (induct ls arbitrary: n)
  apply auto
  apply (metis Suc_diff_Suc index_of_aux_more lessI less_Suc_eq_0_disj less_le_trans)
  by (metis Suc_diff_Suc index_of_aux_more lessI less_le_trans nth_Cons_Suc)

lemma index_of_lookup:
  assumes "p \<in> set ls"
  shows "index_of ls p < length ls"
    "ls ! (index_of ls p) = p"
  apply (metis assms index_of_aux_lookup(1) index_of_def minus_nat.diff_0)
  by (metis assms index_of_aux_lookup(2) index_of_def minus_nat.diff_0)

lemma convert_semantics:
  shows "fml_sem fml x = lookup_sem (fst (convert fml)) (map (\<lambda>p. rpoly p x) (snd (convert fml)))"
  unfolding convert_def Let_def apply simp
  apply (intro convert_semantics_lem)
  by (simp add: index_of_lookup(1) index_of_lookup(2))

lemma convert_closed:
  shows "\<And>i. i \<in> set_fml (fst (convert fml)) \<Longrightarrow> i < length (snd (convert fml))"
  unfolding convert_def Let_def
  apply (auto simp add: fml.set_map)
  by (simp add: index_of_lookup(1) poly_list_set_fml)

(* Rational sign vector of polynomials qs with rational coefficients at x *)
definition sign_vec::"rat poly list \<Rightarrow> real \<Rightarrow> rat list"
  where "sign_vec qs x \<equiv>
    map (squash \<circ> (\<lambda>p. rpoly p x)) qs"

(* The set of all rational sign vectors for qs wrt the set S
  When S = UNIV, then this quantifies over all reals *)
definition consistent_sign_vectors::"rat poly list \<Rightarrow> real set \<Rightarrow> rat list set"
  where "consistent_sign_vectors qs S = (sign_vec qs) ` S"

lemma sign_vec_semantics:
  assumes "\<And>i. i \<in> set_fml fml \<Longrightarrow> i < length ls"
  shows "lookup_sem fml (map (\<lambda>p. rpoly p x) ls) = lookup_sem fml (sign_vec ls x)"
  using assms apply (induction)
  by (auto simp add: sign_vec_def squash_def)

(* The universal and existential decision procedure is easy if we know the consistent sign vectors *)
lemma universal_lookup_sem:
  assumes "\<And>i. i \<in> set_fml fml \<Longrightarrow> i < length qs"
  assumes "set signs = consistent_sign_vectors qs UNIV"
  shows "(\<forall>x::real. lookup_sem fml (map (\<lambda>p. rpoly p x) qs)) \<longleftrightarrow>
    list_all (lookup_sem fml) signs"
  using assms(2) unfolding consistent_sign_vectors_def list_all_iff
  by (simp add: assms(1) sign_vec_semantics)

lemma existential_lookup_sem:
  assumes "\<And>i. i \<in> set_fml fml \<Longrightarrow> i < length qs"
  assumes "set signs = consistent_sign_vectors qs UNIV"
  shows "(\<exists>x::real. lookup_sem fml (map (\<lambda>p. rpoly p x) qs)) \<longleftrightarrow>
    find (lookup_sem fml) signs \<noteq> None"
  using assms(2) unfolding consistent_sign_vectors_def find_None_iff
  by (simp add: assms(1) sign_vec_semantics)

subsection "Factoring Lemmas"
  (*definition real_factorize_list:: "rat poly list \<Rightarrow> real poly list"
where "real_factorize_list qs = map (map_poly of_rat) (fst(factorize_polys qs))"
*)
interpretation of_rat_poly_hom: map_poly_comm_semiring_hom of_rat..
interpretation of_rat_poly_hom: map_poly_comm_ring_hom of_rat..
interpretation of_rat_poly_hom: map_poly_idom_hom of_rat..

lemma finite_prod_map_of_rat_poly_hom:
  shows "poly (real_of_rat_poly (\<Prod>(a,b)\<in>s. f a b)) y = (\<Prod>(a,b)\<in>s. poly (real_of_rat_poly (f a b)) y)"
  apply (simp add: of_rat_poly_hom.hom_prod poly_prod)
  by (simp add: case_prod_app prod.case_distrib)

lemma sign_vec_index_of:
  assumes "f \<in> set ftrs"
  shows "sign_vec ftrs x ! (index_of ftrs f) = squash (rpoly f x)"
  by (simp add: assms index_of_lookup(1) index_of_lookup(2) sign_vec_def)

lemma squash_idem:
  shows "squash (squash x) = squash x"
  unfolding squash_def by auto

lemma squash_mult:
  shows "squash ((a::real) * b) = squash a * squash b"
  unfolding squash_def apply auto
  using less_not_sym mult_neg_neg apply blast
  using mult_less_0_iff by blast

lemma squash_prod_list:
  shows "squash (prod_list (ls::real list)) = prod_list (map squash ls)"
  apply (induction ls)
  unfolding squash_def apply auto
  apply (simp add: mult_less_0_iff)
  by (simp add: zero_less_mult_iff)

lemma squash_pow:
  shows "squash ((x::real) ^ (y::nat)) = (squash x) ^ y"
  unfolding squash_def apply auto
  by (auto simp add: zero_less_power_eq)

lemma squash_real_of_rat[simp]:
  shows "squash (real_of_rat x) = squash x"
  unfolding squash_def by auto

lemma factorize_rat_poly_monic_irreducible_monic:
  assumes "factorize_rat_poly_monic f = (c,fs)"
  assumes "(fi,i) \<in> set fs"
  shows "irreducible fi \<and> monic fi"
proof -
  obtain c' fs' where cfs: "factorize_rat_poly f = (c',fs')"
    by (meson surj_pair)
  then have fs: "fs = map (\<lambda>(f,i). (normalize f, i)) fs'"
    using factorize_rat_poly_monic_def assms by auto
  obtain "fi'" where "(fi',i) \<in> set fs'" "fi = normalize fi'"
    using assms(2) unfolding fs by auto
  thus ?thesis using factorize_rat_poly irreducible_normalize_iff
    by (metis cfs monic_normalize not_irreducible_zero)
qed

lemma square_free_normalize:
  assumes "square_free p"
  shows "square_free (normalize p)"
  by (metis assms square_free_multD(3) unit_factor_mult_normalize)

lemma coprime_normalize:
  assumes "coprime a b"
  shows "coprime (normalize a) b"
  using assms by auto

lemma undo_normalize:
  shows "a = Polynomial.smult (unit_factor (lead_coeff a)) (normalize a)"
  by (metis add.right_neutral mult_pCons_right mult_zero_right normalize_mult_unit_factor pCons_0_hom.hom_zero unit_factor_poly_def)

lemma finite_smult_distr:
  assumes "distinct fs"
  shows "(\<Prod>(x,y)\<in>set fs. Polynomial.smult ((f x y)::rat) (g x y)) = 
    Polynomial.smult (\<Prod>(x,y)\<in>set fs. f x y) (\<Prod>(x,y)\<in>set fs. g x y)"
  using assms
proof (induction fs)
  case Nil
  then show ?case by auto
next
  case (Cons a fs)
  then show ?case apply auto
    using mult.commute mult_smult_right prod.case_distrib smult_smult split_cong split_conv
    by (simp add: Groups.mult_ac(2) split_beta)
qed

lemma normalize_coprime_degree:
  assumes "normalize (f::rat poly) = normalize g"
  assumes "coprime f g"
  shows "degree f = 0"
proof -
  have "f dvd g" by (simp add: assms(1) associatedD2) 
  then have "f dvd 1"
    using assms(2) associatedD1 by auto
  thus ?thesis
    using Missing_Polynomial_Factorial.is_unit_field_poly by blast
qed

lemma factorize_rat_poly_monic_square_free_factorization:
  assumes res: "factorize_rat_poly_monic f = (c,fs)"
  shows "square_free_factorization f (c,fs)"
proof (unfold square_free_factorization_def split, intro conjI impI allI)
  obtain c' fs' where cfs: "factorize_rat_poly f = (c',fs')"
    by (meson surj_pair)
  then have fs: "fs = map (\<lambda>(f,i). (normalize f, i)) fs'"
    using factorize_rat_poly_monic_def assms by auto
  have sq: "square_free_factorization f (c',fs')"
    using cfs factorize_rat_poly(1) by blast
  obtain lcs where lcs: "lcs = prod_list (map (\<lambda>(f,i). lead_coeff f ^ Suc i) fs')" by force
  have c: "c = c' * lcs"  using assms unfolding factorize_rat_poly_monic_def cfs Let_def lcs by auto
  show "f = 0 \<Longrightarrow> c = 0" using c cfs by auto                       
  show "f = 0 \<Longrightarrow> fs = []" using fs cfs by auto
  have dist: "distinct fs'" using sq square_free_factorizationD(5) by blast
  show dist2: "distinct fs" unfolding fs
    unfolding distinct_conv_nth apply auto
  proof -
    fix i j
    assume ij: "i < length fs'" "j < length fs'" "i \<noteq> j"
    assume eq: "(case fs' ! i of
            (f, x) \<Rightarrow> (normalize f, x)) =
           (case fs' ! j of
            (f, x) \<Rightarrow> (normalize f, x))"
    obtain f a where fa: "fs' ! i = (f,a)" by force
    obtain g where g: "fs' ! j = (g,a)" "normalize f = normalize g"
      using eq fa  apply auto
      by (metis case_prod_conv prod.collapse prod.inject)
    have "f \<noteq> g" using dist ij fa g
      using nth_eq_iff_index_eq by fastforce
    then have "coprime f g"
      using square_free_factorizationD(3)[OF sq, of f a g a] fa g ij
      apply auto
      using nth_mem by force
    then have "degree f = 0"
      by (simp add: g(2) normalize_coprime_degree)
    thus False
      using fa ij(1) nth_mem sq square_free_factorizationD'(3) by fastforce 
  qed
  have ceq: "c = c' * (\<Prod>(a, i)\<in>set fs'. (lead_coeff a) ^ Suc i)" using c lcs
    by (simp add: dist prod.distinct_set_conv_list) 
  have fseq: " (\<Prod>(a, i)\<in>set fs. a ^ Suc i) =  (\<Prod>(a, i)\<in>set fs'. (normalize a) ^ Suc i)"
    apply (subst prod.distinct_set_conv_list[OF dist])
    apply (subst prod.distinct_set_conv_list[OF dist2])
    unfolding fs apply (auto simp add: o_def )
    by (metis (no_types, lifting) case_prod_conv old.prod.exhaust)

  have "f = Polynomial.smult c' (\<Prod>(a, i)\<in>set fs'. a ^ Suc i)"  using sq square_free_factorizationD(1) by blast
  moreover have "... =  Polynomial.smult c' (\<Prod>(a, i)\<in>set fs'. (Polynomial.smult ((unit_factor (lead_coeff a))) (normalize a)) ^ Suc i)"
    apply (subst undo_normalize[symmetric]) by auto
  moreover have "... =  Polynomial.smult c'
    (\<Prod>(a, i)\<in>set fs'. (Polynomial.smult ((lead_coeff a) ^ Suc i) ((normalize a) ^ Suc i)))"
    apply (subst smult_power) by auto
  moreover have "... =  Polynomial.smult c'
    (Polynomial.smult (\<Prod>(a, i)\<in>set fs'. ((lead_coeff a) ^ Suc i))
        (\<Prod>(a, i)\<in>set fs'. (normalize a) ^ Suc i))"
    apply (subst finite_smult_distr) by (auto simp add: dist)
  moreover have "... =  Polynomial.smult (c' * (\<Prod>(a, i)\<in>set fs'. (lead_coeff a) ^ Suc i))
        (\<Prod>(a, i)\<in>set fs'. (normalize a) ^ Suc i)"
    using smult_smult by blast
  moreover have "... = Polynomial.smult c  (\<Prod>(a, i)\<in>set fs. a ^ Suc i)"
    unfolding ceq fseq by auto
  ultimately show "f =  Polynomial.smult c  (\<Prod>(a, i)\<in>set fs. a ^ Suc i)" by auto
  fix a i
  assume ai: "(a,i) \<in> set fs"
  obtain a' where a': "(a',i) \<in> set fs'" "a = normalize a'" using ai unfolding fs by auto
  show "square_free a" using square_free_normalize a'
    using sq square_free_factorizationD(2) by blast
  show "0 < degree a" using degree_normalize a'
    using sq square_free_factorizationD'(3) by fastforce
  fix  b j
  assume bj: "(b,j) \<in> set fs" "(a,i) \<noteq> (b,j)"
  obtain b' where b': "(b',j) \<in> set fs'" "b = normalize b'" using bj unfolding fs by auto
  show "algebraic_semidom_class.coprime a b" using a' b' apply auto
    using bj(2) sq square_free_factorizationD(3) by fastforce
qed  

lemma undo_factorize_correct:
  assumes "factorize_rat_poly_monic p = (c,fs)"
  assumes "\<And>f p. (f,p) \<in> set fs \<Longrightarrow> f \<in> set ftrs"
  shows "undo_factorize (c,map (\<lambda>(f,pow). (index_of ftrs f, pow)) fs) (sign_vec ftrs x) = squash (rpoly p x)"
proof -
  have p: "p = smult c (\<Prod>(a, i)\<in> set fs. a ^ Suc i)"
    using assms(1) factorize_rat_poly_monic_square_free_factorization square_free_factorizationD(1) by blast
  have fs: "distinct fs"
    using assms(1) factorize_rat_poly_monic_square_free_factorization square_free_factorizationD(5) by blast
  have "rpoly p x = ((real_of_rat c) * rpoly (\<Prod>(a, i)\<in> set fs. a ^ Suc i) x)"
    using p by (simp add: of_rat_hom.map_poly_hom_smult)
  moreover have "... = ((real_of_rat c) * rpoly (\<Prod>ai\<in> set fs. case ai of (a,i) \<Rightarrow> a ^ Suc i) x)"
    by blast
  moreover have "... = ((real_of_rat c) * (\<Prod>ai\<in> set fs. case ai of (a,i) \<Rightarrow> rpoly (a ^ Suc i) x))"
    by (simp add: finite_prod_map_of_rat_poly_hom)
  moreover have "... = ((real_of_rat c) * (\<Prod>ai\<in> set fs. case ai of (a,i) \<Rightarrow> (rpoly a x) ^ Suc i))"
    by (metis (mono_tags, lifting) of_rat_poly_hom.hom_power poly_hom.hom_power split_cong)
  moreover have "...  = ((real_of_rat c) * (prod_list (map (\<lambda>ai. case ai of (a,i) \<Rightarrow> (rpoly a x) ^ Suc i) fs)))"
    by (simp add: fs prod.distinct_set_conv_list)
  ultimately have "rpoly p x = ((real_of_rat c) * (prod_list (map (\<lambda>ai. case ai of (a,i) \<Rightarrow> (rpoly a x) ^ Suc i) fs)))" by auto

  then have "squash (rpoly p x) = squash c * prod_list (map squash (map (\<lambda>ai. case ai of (a,i) \<Rightarrow> (rpoly a x) ^ Suc i) fs))"
    by (auto simp add: squash_mult squash_prod_list o_def)
  moreover have "... = squash c * prod_list (map (\<lambda>ai. case ai of (a,i) \<Rightarrow> squash ((rpoly a x) ^ Suc i)) fs)"
    apply (simp add: o_def)
    by (simp add: prod.case_distrib)
  ultimately have rp:"squash(rpoly p x) = squash c * prod_list (map (\<lambda>ai. case ai of (a,i) \<Rightarrow> squash (rpoly a x) ^ Suc i) fs)"
    using squash_pow
    by presburger
  have "undo_factorize
     (c, map (\<lambda>(f, pow).(index_of ftrs f, pow)) fs) (sign_vec ftrs x) =
    squash
     (c * (\<Prod>xa\<leftarrow>fs. case xa of (f, y) \<Rightarrow> sign_vec ftrs x ! index_of ftrs f ^ Suc y))"
    unfolding undo_factorize_def apply (auto simp add: o_def)
    by (metis (mono_tags, lifting) case_prod_conv old.prod.exhaust)
  moreover have "... =  squash
     (c * (\<Prod>xa\<leftarrow>fs. case xa of (f, y) \<Rightarrow> (squash (rpoly f x)) ^ Suc y))"
    using assms(2) sign_vec_index_of
      map_eq_conv split_cong
    apply (auto) 
    by (smt map_eq_conv split_cong)
  ultimately show ?thesis using rp
    by (metis (mono_tags, lifting) of_rat_hom.hom_mult squash_idem squash_mult squash_real_of_rat)
qed

lemma length_sign_vec[simp]:
  shows "length (sign_vec ps x) = length ps" unfolding sign_vec_def by auto

lemma factorize_polys_has_factors:
  assumes "factorize_polys ps = (ftrs,data)"
  assumes "p \<in> set ps"
  assumes "factorize_rat_poly_monic p = (c,fs)"
  shows "set (map fst fs) \<subseteq> set ftrs"
  using assms unfolding factorize_polys_def Let_def apply auto
  by (metis UN_iff fst_conv image_eqI snd_conv)

lemma factorize_polys_undo_factorize_polys:
  assumes "factorize_polys ps = (ftrs,data)"
  shows "undo_factorize_polys data (sign_vec ftrs x) = sign_vec ps x"
  unfolding list_eq_iff_nth_eq undo_factorize_polys_def apply auto
proof -
  show leq:"length data = length ps"
    using assms unfolding factorize_polys_def by (auto simp add: Let_def)
  fix i
  assume il:"i < length data"
  obtain c fs where cfs: "factorize_rat_poly_monic (ps ! i) = (c,fs)"
    by (meson surj_pair)
  then have fsts:"set (map fst fs) \<subseteq> set ftrs"
    using assms factorize_polys_has_factors il leq nth_mem by fastforce
  have *:"data ! i = (c,map (\<lambda>(f,pow). (index_of ftrs f, pow)) fs)"
    using assms unfolding factorize_polys_def
    using cfs il by (auto simp add: Let_def cfs)
  have "undo_factorize (data ! i) (sign_vec ftrs x) = squash (rpoly (ps ! i) x)" unfolding *
    apply (subst  undo_factorize_correct[of "ps ! i"])
    apply (auto simp add: cfs)
    using fsts by auto
  thus "undo_factorize (data ! i) (sign_vec ftrs x) =  sign_vec ps x ! i" 
    using leq il sign_vec_def by auto
qed

lemma factorize_polys_irreducible_monic:
  assumes "factorize_polys ps = (fs,data)"
  shows "distinct fs" "\<And>f. f \<in> set fs \<Longrightarrow> irreducible f \<and> monic f"
  using assms unfolding factorize_polys_def Let_def apply auto
  using factorize_rat_poly_monic_irreducible_monic
  apply (metis prod.collapse) 
  using factorize_rat_poly_monic_irreducible_monic
  by (metis prod.collapse)

lemma factorize_polys_square_free:
  assumes "factorize_polys ps = (fs,data)"
  shows "\<And>f. f \<in> set fs \<Longrightarrow> square_free f"
  using assms factorize_polys_irreducible_monic(2) irreducible_imp_square_free by blast

lemma irreducible_monic_coprime:
  assumes f: "monic f" "irreducible (f::rat poly)" 
  assumes g: "monic g" "irreducible (g::rat poly)"
  assumes "f \<noteq> g"
  shows "coprime f g"
  by (metis (no_types, lifting) assms(5) coprime_0(2) coprime_def' f(1) f(2) g(1) g(2) irreducible_normalized_divisors normalize_dvd_iff normalize_idem normalize_monic)

lemma factorize_polys_coprime:
  assumes "factorize_polys ps = (fs,data)"
  shows "\<And>f g. f \<in> set fs \<Longrightarrow> g \<in> set fs \<Longrightarrow> f \<noteq> g \<Longrightarrow> coprime f g"
  using assms factorize_polys_irreducible_monic(2) irreducible_monic_coprime by auto

lemma coprime_rat_poly_real_poly:
  assumes "coprime p (q::rat poly)"
  shows "coprime (real_of_rat_poly p) ((real_of_rat_poly q)::real poly)"
  by (metis assms gcd_dvd_1 of_rat_hom.map_poly_gcd of_rat_poly_hom.hom_dvd_1)

lemma coprime_rat_poly_iff_coprimereal_poly:
  shows "coprime p (q::rat poly) \<longleftrightarrow> coprime (real_of_rat_poly p) ((real_of_rat_poly q)::real poly)"
proof -
  have forward: "coprime p (q::rat poly) \<longrightarrow> coprime (real_of_rat_poly p) ((real_of_rat_poly q)::real poly)"
    using coprime_rat_poly_real_poly by auto
  have backward: "coprime (real_of_rat_poly p) ((real_of_rat_poly q)::real poly) \<Longrightarrow> coprime p (q::rat poly)"
  proof -
    assume copr_real: "comm_monoid_mult_class.coprime (real_of_rat_poly p) (real_of_rat_poly q)"
    have "degree (gcd p (q::rat poly)) > 0 \<Longrightarrow> False" 
    proof -
      assume deg: "degree (gcd p (q::rat poly)) > 0"
      then have "\<exists>y. y dvd p \<and> y dvd q \<and> degree y > 0"
        by blast
      then obtain y where yprop: "y dvd p \<and> y dvd q \<and> degree y > 0"
        by auto
      then have "(real_of_rat_poly y) dvd (real_of_rat_poly p) \<and>
        (real_of_rat_poly y ) dvd (real_of_rat_poly q) \<and> degree y > 0"
        by simp
      then show "False" 
        using copr_real apply (auto)
        by fastforce 
    qed
    then show "comm_monoid_mult_class.coprime p (q::rat poly)" 
      using comm_monoid_gcd_class.gcd_dvd_1
      by (metis Missing_Polynomial_Factorial.is_unit_field_poly copr_real gcd_zero_iff' neq0_conv of_rat_poly_hom.hom_zero)
  qed
  show ?thesis
    using forward backward by auto
qed

lemma factorize_polys_map_distinct:
  assumes "factorize_polys ps = (fs,data)"
  assumes "fss =  map real_of_rat_poly fs"
  shows "distinct fss"
  using factorize_polys_irreducible_monic[OF assms(1)]
  unfolding assms(2) 
  apply (simp add: distinct_conv_nth)
  by (metis of_rat_eq_iff of_rat_hom.coeff_map_poly_hom poly_eqI)

lemma factorize_polys_map_square_free:
  assumes "factorize_polys ps = (fs,data)"
  assumes "fss =  map real_of_rat_poly fs"
  shows "\<And>f. f \<in> set fss \<Longrightarrow> square_free f"
  using factorize_polys_square_free[OF assms(1)]
  using assms(2) field_hom_0'.square_free_map_poly of_rat_hom.field_hom_0'_axioms by auto 

lemma factorize_polys_map_coprime:
  assumes "factorize_polys ps = (fs,data)"
  assumes "fss =  map real_of_rat_poly fs"
  shows "\<And>f g. f \<in> set fss \<Longrightarrow> g \<in> set fss \<Longrightarrow> f \<noteq> g \<Longrightarrow> coprime f g"
  using factorize_polys_coprime[OF assms(1)] coprime_rat_poly_real_poly unfolding assms(2)
  by auto

lemma coprime_prod_list:
  assumes "\<And>p. p \<in> set ps \<Longrightarrow> p \<noteq> 0"
  assumes "coprime (prod_list ps) (q::real poly)"  
  shows "\<And>p. p \<in> set ps \<Longrightarrow> coprime p q"
proof -
  fix p
  assume "p \<in> set ps"
  then obtain r where r: "prod_list ps = r * p"
    using remove1_retains_prod by blast
  show "coprime p q"
    apply (rule coprime_prod[of r 1])
    using assms r apply auto
    by blast
qed

(* basically copied from square_free_factorizationD' *)
lemma factorize_polys_square_free_prod_list:
  assumes "factorize_polys ps = (fs,data)"
  shows "square_free (prod_list fs)"
proof (rule square_freeI)
  from factorize_polys_coprime[OF assms]
  have coprime: "\<And>p q. p \<in> set fs \<Longrightarrow> q \<in> set fs \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q" .
  from factorize_polys_square_free[OF assms]
  have sq: "\<And>p. p \<in> set fs \<Longrightarrow> square_free p" .
  thus "prod_list fs \<noteq> 0" unfolding prod_list_zero_iff
    using square_free_def by blast
  fix q
  assume "degree q > 0" "q * q dvd prod_list fs"
  from irreducible\<^sub>d_factor[OF this(1)] this(2) obtain q where 
    irr: "irreducible q" and dvd: "q * q dvd prod_list fs" unfolding dvd_def by auto
  hence dvd': "q dvd prod_list fs" unfolding dvd_def by auto
  from irreducible_dvd_prod_list[OF irr dvd'] obtain b where 
    mem: "b \<in> set fs" and dvd1: "q dvd b" by auto
  from dvd1 obtain k where b: "b = q * k" unfolding dvd_def by auto
  from split_list[OF mem] b obtain bs1 bs2 where bs: "fs = bs1 @ b # bs2" by auto
  from irr have q0: "q \<noteq> 0" and dq: "degree q > 0" unfolding irreducible\<^sub>d_def by auto
  have "square_free (q * k)" using sq b mem by auto
  from this[unfolded square_free_def, THEN conjunct2, rule_format, OF dq] 
  have qk: "\<not> q dvd k" by simp
  from dvd[unfolded bs b] have "q * q dvd q * (k * prod_list (bs1 @ bs2))"
    by (auto simp: ac_simps)
  with q0 have "q dvd k * prod_list (bs1 @ bs2)" by auto
  with irr qk have "q dvd prod_list (bs1 @ bs2)" by auto
  from irreducible_dvd_prod_list[OF irr this] obtain b' where 
    mem': "b' \<in> set (bs1 @ bs2)" and dvd2: "q dvd b'" by fastforce
  from dvd1 dvd2 have "q dvd gcd b b'" by auto
  with dq is_unit_iff_degree[OF q0] have cop: "\<not> coprime b b'" by force
  from mem' have "b' \<in> set fs" unfolding bs by auto
  have b': "b' = b" using coprime
    using \<open>b' \<in> set fs\<close> cop mem by blast
  with mem' bs factorize_polys_irreducible_monic(1)[OF assms] show False by auto
qed

lemma factorize_polys_map_square_free_prod_list:
  assumes "factorize_polys ps = (fs,data)"
  assumes "fss =  map real_of_rat_poly fs"
  shows "square_free (prod_list fss)"
  using  factorize_polys_square_free_prod_list[OF assms(1)] unfolding assms(2)
  by (simp add: of_rat_hom.square_free_map_poly)

lemma factorize_polys_map_coprime_pderiv:
  assumes "factorize_polys ps = (fs,data)"
  assumes "fss = map real_of_rat_poly fs"
  shows "\<And>f. f \<in> set fss \<Longrightarrow> coprime f (pderiv (prod_list fss))"
proof -
  fix f
  assume f: "f \<in> set fss"
  from factorize_polys_map_square_free[OF assms]
  have sq: "\<And>p. p \<in> set fss \<Longrightarrow> square_free p" .
  have z: "\<And>p. p \<in> set fss \<Longrightarrow> p \<noteq> 0" using sq square_free_def by blast
  have c: "coprime (prod_list fss) (pderiv (prod_list fss))"
    apply (simp add: separable_def[symmetric] square_free_iff_separable[symmetric])
    using factorize_polys_map_square_free_prod_list[OF assms] .
  from coprime_prod_list[OF z c f]
  show "coprime f (pderiv (prod_list fss))" by auto
qed

definition pairwise_coprime_list:: "rat poly list \<Rightarrow> bool"
  where "pairwise_coprime_list qs = 
    (\<forall>m < length qs. \<forall> n < length qs.
     m \<noteq> n \<longrightarrow> coprime (qs ! n) (qs ! m))"

(* Restating factorize_polys_map_coprime to match later definitions *)
lemma coprime_factorize:
  fixes qs:: "rat poly list"
  shows "pairwise_coprime_list (fst(factorize_polys qs))"
proof -
  let ?fs = "fst(factorize_polys qs)"
  have "(\<forall>m < length ?fs. \<forall> n < length ?fs.
     m \<noteq> n \<longrightarrow> coprime (?fs ! n) (?fs ! m))"
  proof clarsimp 
    fix m n
    assume "m < length (fst (factorize_polys qs))"
    assume "n < length (fst (factorize_polys qs))"
    assume "m \<noteq> n"
    show " algebraic_semidom_class.coprime (fst (factorize_polys qs) ! n)
            (fst (factorize_polys qs) ! m)"
      by (metis \<open>m < length (fst (factorize_polys qs))\<close> \<open>m \<noteq> n\<close> \<open>n < length (fst (factorize_polys qs))\<close> coprime_iff_coprime distinct_conv_nth factorize_polys_coprime factorize_polys_def factorize_polys_irreducible_monic(1) fstI nth_mem)
  qed
  then show ?thesis unfolding pairwise_coprime_list_def by auto
qed

lemma squarefree_factorization_degree:
  assumes "square_free_factorization p (c,fs)"
  shows "degree p = sum_list (map (\<lambda>(f,c). (c+1) * degree f) fs)"
proof -
  have "p =
    Polynomial.smult c
     (\<Prod>(a, i)\<in>set fs. a ^ Suc i)" using assms unfolding square_free_factorization_def
    by blast
  then have "degree p = degree (\<Prod>(a, i)\<in>set fs. a ^ Suc i)"
    using assms square_free_factorizationD(4) by fastforce
  also have "... = degree (prod_list (map (\<lambda>(f,c). f ^ Suc c) fs))"
    by (metis assms prod.distinct_set_conv_list square_free_factorizationD(5))
  also have "... = (\<Sum>(a, i)\<leftarrow>fs. degree (a ^ Suc i))"
    apply (subst degree_prod_list_eq)
    apply (auto simp add: o_def)
    using assms degree_0 square_free_factorizationD(2) apply blast
    using assms degree_0 square_free_factorizationD(2) apply blast
    by (simp add: prod.case_distrib)
  ultimately show ?thesis
    by (smt Polynomial.degree_power_eq add.commute assms degree_0 map_eq_conv plus_1_eq_Suc split_cong square_free_factorizationD(2))  
qed

subsection "Auxiliary Polynomial Lemmas"
definition roots_of_coprime_r:: "real poly list \<Rightarrow> real set"
  where "roots_of_coprime_r qs = {x. poly (coprime_r qs) x = 0}"

lemma crb_lem_pos: 
  fixes x:: "real"
  fixes p:: "real poly"
  assumes x: "poly p x = 0" 
  assumes p: "p \<noteq> 0" 
  shows "x < crb p"
  using cauchy_root_bound[of p x] apply (auto)
  unfolding crb_def apply (auto)
  using p x 
  by linarith 

lemma crb_lem_neg: 
  fixes x:: "real"
  fixes p:: "real poly"
  assumes x: "poly p x = 0" 
  assumes p: "p \<noteq> 0" 
  shows "x > -crb p"
  using cauchy_root_bound[of p x] apply (auto)
  unfolding crb_def apply (auto)
  using p x by linarith 

(* Show that the product of the polynomial list is 0 at x iff there is a polynomial 
  in the list that is 0 at x *)
lemma prod_zero:
  shows "\<forall>x . poly (prod_list (qs:: rat poly list)) x = 0 \<longleftrightarrow> (\<exists>q \<in> set (qs). poly q x = 0)" 
  apply auto
  using poly_prod_list_zero_iff apply blast
  using poly_prod_list_zero_iff by blast

lemma coprime_r_zero1: "poly (coprime_r qs) (crb (prod_list qs)) = 0"
  by (simp add: coprime_r_def) 

lemma coprime_r_zero2: "poly (coprime_r qs) (-crb (prod_list qs)) = 0"
  by (simp add: coprime_r_def) 

lemma coprime_mult:
  fixes a:: "real poly"
  fixes b:: "real poly"
  fixes c:: "real poly"
  assumes "algebraic_semidom_class.coprime a b"
  assumes "algebraic_semidom_class.coprime a c"
  shows "algebraic_semidom_class.coprime a (b*c)"
  using assms(1) assms(2) by auto

(* Will be needed when we call the BKR roots on coprime_r *)
lemma coprime_r_coprime_prop:
  fixes ps:: "rat poly list"
  assumes "factorize_polys ps = (fs,data)"
  assumes "fss = map real_of_rat_poly fs"
  shows "\<And>f. f \<in> set fss \<Longrightarrow> coprime f (coprime_r fss)"
proof clarsimp 
  fix f:: "real poly"
  assume f_in: "f \<in> set fss"
  have nonz_prod: "prod_list fss \<noteq> 0" using factorize_polys_map_square_free apply (auto)
    using assms(1) assms(2) square_free_def by fastforce 
  have nonz_f: "f \<noteq> 0" using f_in factorize_polys_map_square_free apply (auto)
    using assms(1) assms(2) square_free_def by fastforce 
  have copr_pderiv: "algebraic_semidom_class.coprime f (pderiv (prod_list fss))" using factorize_polys_map_coprime_pderiv
    apply (auto)
    using f_in assms(1) assms(2) by auto 
  have z_iff: "\<forall>x. poly f x = 0 \<longrightarrow> poly (prod_list fss) x = 0"
    using f_in apply (auto)
    using poly_prod_list_zero_iff by blast 
  let ?inf_p = "[:-(crb (prod_list fss)),1:]::real poly"
  have copr_inf: "algebraic_semidom_class.coprime f ([:-(crb (prod_list fss)),1:])"
  proof - 
    have zero_prop: "\<forall>x. poly ?inf_p x = 0 \<longleftrightarrow> x = crb (prod_list fss)" 
      by auto
    have  "poly (prod_list fss) (crb (prod_list fss)) \<noteq> 0"
    proof -
      have h: "\<forall>x. poly (prod_list fss) x = 0 \<longrightarrow> x < (crb (prod_list fss))"
        using nonz_prod crb_lem_pos[where p = "prod_list fss"] 
        by auto
      then  show ?thesis by auto
    qed
    then have nonzero: "poly f (crb (prod_list fss)) \<noteq> 0"
      using z_iff by auto
    then have "\<not>(\<exists>x. poly f x = 0 \<and> poly ?inf_p x = 0)"
      by simp
    have is_unit_gcd: "is_unit (gcd ?inf_p f)"
      using prime_elem_imp_gcd_eq  prime_elem_iff_irreducible linear_irreducible_field
      apply (auto) using nonzero
    proof -
      have f1: "\<forall>x0. - (x0::real) = - 1 * x0"
        by simp
      have "(1::real) \<noteq> 0"
        by auto
      then have "is_unit (gcd (pCons (- 1 * real_of_int (crb (prod_list fss))) 1) f)"
        using f1 by (metis (no_types) is_unit_gcd nonzero one_poly_eq_simps(1) poly_eq_0_iff_dvd prime_elem_imp_coprime prime_elem_linear_field_poly)
      then show "degree (gcd (pCons (- real_of_int (crb (prod_list fss))) 1) f) = 0"
        by simp
    qed 
    then show ?thesis
      using is_unit_gcd
      by (metis gcd.commute gcd_eq_1_imp_coprime is_unit_gcd_iff) 
  qed
  let ?ninf_p = "[:(crb (prod_list fss)),1:]::real poly"
  have copr_neg_inf: "algebraic_semidom_class.coprime f ([:(crb (prod_list fss)),1:])"
  proof - 
    have h: "\<forall>x. poly f x = 0 \<longrightarrow> poly (prod_list fss) x = 0"
      using f_in apply (auto)
      using poly_prod_list_zero_iff by blast 
    have zero_prop: "\<forall>x. poly ?ninf_p x = 0 \<longleftrightarrow> x = -crb (prod_list fss)" 
      by auto
    have  "poly (prod_list fss) (-crb (prod_list fss)) \<noteq> 0"
    proof  -
      have h: "\<forall>x. poly (prod_list fss) x = 0 \<longrightarrow> x > (-crb (prod_list fss))"
        using nonz_prod crb_lem_neg[where p = "prod_list fss"] 
        by auto
      then  show ?thesis by auto
    qed
    then have nonzero: "poly f (-crb (prod_list fss)) \<noteq> 0"
      using z_iff by auto
    then have "\<not>(\<exists>x. poly f x = 0 \<and> poly ?ninf_p x = 0)"
      using zero_prop by auto
    have is_unit_gcd: "is_unit (gcd ?ninf_p f)"
      using prime_elem_imp_gcd_eq  prime_elem_iff_irreducible linear_irreducible_field
      apply (auto) using nonzero
    proof -
      have f1: "(1::real) \<noteq> 0"
        by auto
      have "\<not> pCons (real_of_int (crb (prod_list fss))) 1 dvd f"
        using nonzero by auto
      then show "degree (gcd (pCons (real_of_int (crb (prod_list fss))) 1) f) = 0"
        using f1 by (metis (no_types) Missing_Polynomial_Factorial.is_unit_field_poly coprime_imp_gcd_eq_1 is_unit_gcd_iff one_poly_eq_simps(1) prime_elem_imp_coprime prime_elem_linear_field_poly)
    qed
    then show ?thesis 
      using is_unit_gcd
      by (metis gcd.commute gcd_eq_1_imp_coprime is_unit_gcd_iff) 
  qed
  show "algebraic_semidom_class.coprime f (coprime_r fss)" 
    using copr_pderiv coprime_mult unfolding coprime_r_def
    using copr_inf copr_neg_inf by blast 
qed

lemma coprime_r_nonzero:
  fixes ps:: "rat poly list"
  assumes "factorize_polys ps = (fs,data)"
  assumes nonempty_fs: "fs \<noteq> []"
  assumes fss_is: "fss = map real_of_rat_poly fs"
  shows "(coprime_r fss) \<noteq> 0"
proof - 
  have nonempty_fss: "fss \<noteq> []" using nonempty_fs fss_is by auto
  have deg_f: "\<forall>f \<in> set (fs). degree f > 0"
    using factorize_polys_irreducible_monic 
    apply (auto)
    using assms(1) irreducible_degree_field by blast
  then have deg_fss: "\<forall>f \<in> set (fss). degree f > 0"
    using fss_is by simp 
  then have fss_nonz: "\<forall>f \<in> set (fss). f \<noteq> 0"
    by auto
  have "fss \<noteq> [] \<longrightarrow> ((\<forall>f \<in> set (fss). (degree f > 0 \<and> f \<noteq> 0)) \<longrightarrow> degree (prod_list fss) > 0)"
  proof (induct fss)
    case Nil
    then show ?case
      by blast 
  next
    case (Cons a fss)
    show ?case 
    proof clarsimp 
      assume z_lt: "0 < degree a"
      assume anonz: "a \<noteq> 0"
      assume fnonz: "\<forall>f\<in>set fss. 0 < degree f \<and> f \<noteq> 0"
      have h: "degree (a * prod_list fss) = degree a + degree (prod_list fss) "
        using degree_mult_eq[where p = "a", where q = "prod_list fss"] anonz fnonz 
        by auto
      then show "0 < degree (a * prod_list fss)"
        using z_lt Cons.hyps by auto
    qed
  qed
  then have "degree (prod_list fss) > 0"
    using nonempty_fss deg_fss fss_nonz by auto
  then have pderiv_nonzero: "pderiv (prod_list fss) \<noteq> 0"
    by (simp add: pderiv_eq_0_iff)
  have "(([:-(crb (prod_list fss)),1:]) * ([:(crb (prod_list fss)),1:])) \<noteq> 0"
    by auto
  then show ?thesis using pderiv_nonzero
    unfolding coprime_r_def apply (auto)
    by (metis offset_poly_eq_0_lemma right_minus_eq synthetic_div_unique_lemma) 
qed

lemma Rolle_pderiv:
  fixes q:: "real poly"
  fixes x1 x2:: "real"
  shows "(x1 < x2 \<and> poly q x1 = 0 \<and> poly q x2 = 0) \<longrightarrow> (\<exists>w. x1 < w \<and> w < x2 \<and> poly (pderiv q) w = 0)"
  using Rolle_deriv apply (auto)
  by (metis DERIV_unique Rolle continuous_at_imp_continuous_on poly_DERIV poly_differentiable poly_isCont) 

lemma coprime_r_roots_prop: 
  fixes qs:: "real poly list"
  assumes pairwise_rel_prime: "\<forall>q1 q2. (q1 \<noteq> q2 \<and> (List.member qs q1) \<and> (List.member qs q2))\<longrightarrow> coprime q1 q2"
  shows "\<forall>x1. \<forall>x2. ((x1 < x2 \<and> (\<exists>q1 \<in> set (qs). (poly q1 x1) = 0) \<and> (\<exists>q2\<in> set(qs). (poly q2 x2) = 0)) \<longrightarrow> (\<exists>q. x1 < q \<and> q < x2 \<and> poly (coprime_r qs) q = 0))"
proof clarsimp
  fix x1:: "real"
  fix x2:: "real"
  fix q1:: "real poly"
  fix q2:: "real poly"
  assume "x1 < x2"
  assume q1_in: "q1 \<in> set qs"
  assume q1_0: "poly q1 x1 = 0"
  assume q2_in: "q2 \<in> set qs"
  assume q2_0: "poly q2 x2 = 0"
  have prod_z_x1: "poly (prod_list qs) x1 = 0" using q1_in q1_0
    using poly_prod_list_zero_iff by blast  
  have prod_z_x2: "poly (prod_list qs) x2 = 0" using q2_in q2_0 
    using poly_prod_list_zero_iff by blast 
  have "\<exists>w>x1. w < x2 \<and> poly (pderiv (prod_list qs)) w = 0" 
    using Rolle_pderiv[where q = "prod_list qs"] prod_z_x1 prod_z_x2
    using \<open>x1 < x2\<close> by blast
  then obtain w where w_def: "w > x1 \<and>w < x2 \<and> poly (pderiv (prod_list qs)) w = 0"
    by auto
  then have "poly (coprime_r qs) w = 0"
    unfolding coprime_r_def
    by simp 
  then show "\<exists>q>x1. q < x2 \<and> poly (coprime_r qs) q = 0"
    using w_def by blast 
qed

subsection "Setting Up the Procedure: Lemmas"
definition has_no_zeros::"rat list \<Rightarrow> bool"
  where "has_no_zeros l = (0 \<notin> set l)"

lemma hnz_prop: "has_no_zeros l \<longleftrightarrow> \<not>(\<exists>k < length l. l ! k = 0)"
  unfolding has_no_zeros_def
  by (simp add: in_set_conv_nth)

definition cast_rat_list:: "rat poly list \<Rightarrow> real poly list"
  where "cast_rat_list qs = map real_of_rat_poly qs"

definition consistent_sign_vectors_r::"real poly list \<Rightarrow> real set \<Rightarrow> rat list set"
  where "consistent_sign_vectors_r qs S = (signs_at qs) ` S"

lemma consistent_sign_vectors_consistent_sign_vectors_r:
  shows"consistent_sign_vectors_r (cast_rat_list qs) S = consistent_sign_vectors qs S"
  unfolding consistent_sign_vectors_r_def cast_rat_list_def consistent_sign_vectors_def
    sign_vec_def signs_at_def
  by auto

(* Relies on coprime_rat_poly_real_poly *)
lemma coprime_over_reals_coprime_over_rats:
  fixes qs:: "rat poly list"
  assumes csa_in: "csa \<in> (consistent_sign_vectors qs UNIV)"
  assumes p1p2: "p1\<noteq>p2 \<and> p1 < length csa \<and> p2 < length csa \<and> csa ! p1 = 0 \<and> csa ! p2 = 0"
  shows "\<not> algebraic_semidom_class.coprime (nth qs p1) (nth qs p2) "
proof - 
  have isx: "\<exists>(x::real). csa = (sign_vec qs x)" 
    using csa_in unfolding consistent_sign_vectors_def by auto
  then obtain x where havex: "csa = (sign_vec qs x)" by auto
  then have expolys: "poly (real_of_rat_poly (nth qs p1)) x = 0 \<and> poly (real_of_rat_poly (nth qs p2)) x = 0"
    using havex unfolding sign_vec_def squash_def
    by (smt class_field.neg_1_not_0 length_map map_map nth_map one_neq_zero p1p2)
  then have "\<not> coprime (real_of_rat_poly (nth qs p1)) ((real_of_rat_poly (nth qs p2))::real poly)"
    apply (auto) using coprime_poly_0 
    by blast 
  then show ?thesis
    using coprime_rat_poly_real_poly by auto
qed

(* This and the following lemma are designed to show that if you have two sgas that aren't the same, 
   there's a 0 in between! The proof uses IVT. It hones in on the component that's changed sign 
   (either from 1 to {0, -1} or from -1 to {0, 1}) *)
lemma zero_above: 
  fixes qs:: "rat poly list"
  fixes x1:: "real"
  assumes hnz: "has_no_zeros (sign_vec qs x1)"
  shows "(\<forall> x2 > x1. ((sign_vec qs x1) \<noteq> (sign_vec qs x2)) \<longrightarrow> 
  (\<exists>(r::real) > x1. (r \<le> x2 \<and> (\<exists> q \<in> set(qs). rpoly q r = 0))))"
proof clarsimp 
  fix x2
  assume x1_lt: "x1 < x2"
  assume diff_sign_vec: "sign_vec qs x1 \<noteq> sign_vec qs x2"
  then have "\<exists>q \<in> set qs. squash (rpoly q x1) \<noteq> squash (rpoly q x2)"
    unfolding sign_vec_def
    by simp 
  then obtain q where q_prop: "q \<in> set qs \<and> squash (rpoly q x1) \<noteq> squash (rpoly q x2)"
    by auto
  then have q_in: "q \<in> set qs" by auto
  have poss1: "squash (rpoly q x1) = -1 \<and> squash (rpoly q x2) = 1 \<longrightarrow> (\<exists>r>x1. r \<le> x2 \<and> (\<exists>q\<in>set qs. rpoly q r = 0))"
    using poly_IVT_pos[of x1 x2] using x1_lt unfolding squash_def apply (auto)
    using q_prop by fastforce 
  have poss2: "squash (rpoly q x1) = 1 \<and> squash (rpoly q x2) = -1 \<longrightarrow> (\<exists>r>x1. r \<le> x2 \<and> (\<exists>q\<in>set qs. rpoly q r = 0))"
    using poly_IVT_neg[of x1 x2] using x1_lt unfolding squash_def apply (auto)
    using q_prop by fastforce 
  have poss3: "squash (rpoly q x2) = 0 \<longrightarrow> (\<exists>r>x1. r \<le> x2 \<and> (\<exists>q\<in>set qs. rpoly q r = 0))"
    using x1_lt unfolding squash_def apply (auto)
    using q_prop by blast
  have "(q \<in> set qs \<and> rpoly q x1 = 0) \<longrightarrow> \<not>has_no_zeros (sign_vec qs x1)"
    unfolding has_no_zeros_def sign_vec_def apply auto
    by (smt image_iff squash_def)
  have not_poss4: "squash (rpoly q x1) \<noteq> 0" 
    using hnz q_in unfolding squash_def
    using \<open>q \<in> set qs \<and> rpoly q x1 = 0 \<longrightarrow> \<not> has_no_zeros (sign_vec qs x1)\<close> by auto 
  then show "\<exists>r>x1. r \<le> x2 \<and> (\<exists>q\<in>set qs. rpoly q r = 0)"
    using q_prop poss1 poss2 poss3 not_poss4 
    apply (auto)
     apply (meson squash_def)
      apply (metis squash_def)
       apply (metis squash_def) by (meson squash_def)
qed

lemma zero_below: 
  fixes qs:: "rat poly list"
  fixes x1:: "real"
  assumes hnz: "has_no_zeros (sign_vec qs x1)"
  shows "\<forall>x2 < x1. ((sign_vec qs x1) \<noteq> (sign_vec qs x2)) \<longrightarrow> 
  (\<exists>(r::real) < x1. (r \<ge> x2 \<and> (\<exists> q \<in> set(qs). rpoly q r = 0)))"
proof clarsimp 
  fix x2
  assume x1_gt: "x2 < x1"
  assume diff_sign_vec: "sign_vec qs x1 \<noteq> sign_vec qs x2"
  then have "\<exists>q \<in> set qs. squash (rpoly q x1) \<noteq> squash (rpoly q x2)"
    unfolding sign_vec_def
    by simp 
  then obtain q where q_prop: "q \<in> set qs \<and> squash (rpoly q x1) \<noteq> squash (rpoly q x2)"
    by auto
  then have q_in: "q \<in> set qs" by auto
  have poss1: "squash (rpoly q x1) = -1 \<and> squash (rpoly q x2) = 1 \<longrightarrow> (\<exists>r<x1. (r \<ge> x2 \<and> (\<exists> q \<in> set(qs). rpoly q r = 0)))"
    using poly_IVT_neg[of x2 x1] using x1_gt unfolding squash_def apply (auto)
    using q_prop by fastforce 
  have poss2: "squash (rpoly q x1) = 1 \<and> squash (rpoly q x2) = -1 \<longrightarrow> (\<exists>r<x1. (r \<ge> x2 \<and> (\<exists> q \<in> set(qs). rpoly q r = 0)))"
    using poly_IVT_pos[of x2 x1] using x1_gt unfolding squash_def apply (auto)
    using q_prop by fastforce 
  have poss3: "squash (rpoly q x2) = 0 \<longrightarrow> (\<exists>r<x1. (r \<ge> x2 \<and> (\<exists> q \<in> set(qs). rpoly q r = 0)))"
    using x1_gt unfolding squash_def apply (auto)
    using q_prop by blast
  have "(q \<in> set qs \<and> rpoly q x1 = 0) \<longrightarrow> \<not>has_no_zeros (sign_vec qs x1)"
    unfolding has_no_zeros_def sign_vec_def apply auto
    using image_iff squash_def
    by (smt image_iff squash_def)
  have not_poss4: "squash (rpoly q x1) \<noteq> 0" 
    using hnz q_in unfolding squash_def
    using \<open>q \<in> set qs \<and> rpoly q x1 = 0 \<longrightarrow> \<not> has_no_zeros (sign_vec qs x1)\<close> by auto 
  then show "(\<exists>r<x1. (r \<ge> x2 \<and> (\<exists> q \<in> set(qs). rpoly q r = 0)))"
    using q_prop poss1 poss2 poss3 not_poss4 apply (auto)
    apply (meson squash_def)
     apply (metis squash_def)
      apply (metis squash_def)
       by (meson squash_def)
qed

lemma sorted_list_lemma:
  fixes l:: "real list"
  fixes a b:: "real"
  fixes n:: "nat"
  assumes "a < b"
  assumes "(n + 1) < length l"
  assumes strict_sort: "strict_sorted l"
  assumes lt_a: "(l ! n) < a"
  assumes b_lt: "b < (l ! (n+1))"
  shows "\<not>(\<exists>(x::real). (List.member l x \<and> a \<le> x \<and> x \<le> b))"
proof -
  have sorted_hyp_var: "\<forall>q1 < length l. \<forall>q2 < length l. (q1 < q2 \<longrightarrow>
     (l ! q1) < (l ! q2))" 
    apply (auto)
    by (metis (no_types, lifting) strict_sort sorted_wrt_iff_nth_less strict_sorted_sorted_wrt) 
  then have sorted_hyp_var2:  "\<forall>q1 < length l. \<forall>q2 < length l. ((l ! q1) < (l ! q2)) \<longrightarrow> q1 < q2"
    using linorder_neqE_nat
    by (metis Groups.add_ac(2) add_mono_thms_linordered_field(5) less_irrefl) 
  have "(\<exists>(x::real). (List.member l x \<and> a \<le> x \<and> x \<le> b)) \<Longrightarrow> False"
  proof -
    assume "(\<exists>(x::real). (List.member l x \<and> a \<le> x \<and> x \<le> b))"
    then obtain x where x_prop: "List.member l x \<and> a \<le> x \<and> x \<le> b" by auto
    then have l_prop: "List.member l x \<and> (l ! n) < x \<and> x < (l ! (n+1))"
      using lt_a b_lt by auto
    have nth_l: "l ! n < x" using l_prop by auto
    have np1th_l: "x < l ! (n+1)" using l_prop by auto
    have "\<exists>k. k < length l \<and> nth l k = x" using l_prop
      by (meson in_set_member index_of_lookup(1) index_of_lookup(2))
    then obtain k where k_prop: "k < length l \<and> nth l k = x" by auto
    have n_lt: "n < k"
      using nth_l sorted_hyp_var k_prop add_lessD1 assms(2) linorder_neqE_nat nat_SN.gt_trans
      by (meson sorted_hyp_var2)
    have k_gt: "k < n + 1" 
      using sorted_hyp_var np1th_l k_prop
      using assms(2) sorted_hyp_var2 by blast 
    show False 
      using n_lt k_gt by auto
  qed
  then show ?thesis by auto
qed

(* This lemma shows that any zero of coprime_r is either between two roots or it's smaller than the 
least root (neg inf) or it's greater than the biggest root (pos inf). *)
lemma roots_of_coprime_r_location_property: 
  fixes qs:: "rat poly list"
  fixes sga:: "rat list"
  fixes zer_list
  assumes pairwise_rel_prime: "pairwise_coprime_list qs"
  assumes all_squarefree: "\<And>q. q \<in> set qs \<Longrightarrow> rsquarefree q"
  assumes x1_prop: "sga = sign_vec qs x1"
  assumes hnz: "has_no_zeros sga"
  assumes zer_list_prop: "zer_list = sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (rpoly q x = 0))}"
  shows "zer_list \<noteq> [] \<longrightarrow> ((x1 < (zer_list ! 0)) \<or> (x1 > (zer_list ! (length zer_list - 1)) \<or>
    (\<exists> n < (length zer_list - 1). x1 > (zer_list ! n) \<and> x1 < (zer_list ! (n+1)))))"
proof - 
  let ?zer_list = "sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (rpoly q x = 0))} :: real list"
  show ?thesis 
  proof -
    have "((\<forall>q. (List.member qs q) \<longrightarrow> q \<noteq> 0) \<and> has_no_zeros (sign_vec qs x1)) \<Longrightarrow> \<not> List.member ?zer_list x1"
    proof (induct qs)
      case Nil
      then show ?case  apply (auto)
        by (simp add: member_rec(2)) 
    next
      case (Cons a qs)
      then show ?case 
      proof clarsimp 
        assume imp: "((\<forall>q. List.member qs q \<longrightarrow> q \<noteq> 0) \<and>
     has_no_zeros (sign_vec qs x1) \<Longrightarrow>
     \<not> List.member (sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0})
         x1)"
        assume nonz: "\<forall>q. List.member (a # qs) q \<longrightarrow> q \<noteq> 0"
        assume hnz: " has_no_zeros (sign_vec (a # qs) x1)"
        assume mem_list: "List.member
     (sorted_list_of_set {x. rpoly a x = 0 \<or> (\<exists>q\<in>set qs. rpoly q x = 0)})
     x1"
        have "has_no_zeros (sign_vec (a # qs) x1) \<Longrightarrow> has_no_zeros (sign_vec qs x1)"
        proof - 
          assume hnz: "has_no_zeros (sign_vec (a # qs) x1)"
          have same_vec: "sign_vec (a # qs) x1 = ((if rpoly a x1 > 0 then 1 else if rpoly a x1 = 0 then 0 else -1) # sign_vec (qs) x1)"
            unfolding sign_vec_def squash_def by auto
          have "has_no_zeros ((if rpoly a x1 > 0 then 1 else if rpoly a x1 = 0 then 0 else -1) # sign_vec (qs) x1)
            \<Longrightarrow>  has_no_zeros (sign_vec (qs) x1)"
            by (simp add: has_no_zeros_def)
          then show "has_no_zeros (sign_vec qs x1)" using hnz same_vec by auto
        qed
        then have nmem: "\<not> List.member (sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0}) x1"
          using hnz nonz imp apply (auto)
          by (simp add: member_rec(1))
        have "\<forall>q \<in>set qs. q \<noteq> 0"
          using nonz using in_set_member apply (auto) by fastforce 
        then have "\<forall>q \<in>set qs. finite {x. rpoly q x = 0}"
          by (simp add: poly_roots_finite)
        then have fin_set: "finite {x. \<exists>q\<in>set qs. rpoly q x = 0}"
          by auto
        have not_in: "x1 \<notin> {x. \<exists>q\<in>set qs. rpoly q x = 0}" using fin_set nmem set_sorted_list_of_set
            all_squarefree
          apply (auto)
          by (simp add: List.member_def \<open>finite {x. \<exists>q\<in>set qs. rpoly q x = 0}\<close>)
        have x1_in: "x1 \<in> {x. rpoly a x = 0 \<or> (\<exists>q\<in>set qs. rpoly q x = 0)}"
          using mem_list sorted_list_of_set 
        proof -
          have f1: "\<forall>r R. ((r::real) \<in> R \<or> \<not> List.member (sorted_list_of_set R) r) \<or> infinite R"
            by (metis in_set_member set_sorted_list_of_set)
          have "finite {r. rpoly a (r::real) = 0}"
            by (metis (full_types) List.finite_set member_rec(1) nonz real_roots_of_rat_poly(1))
          then show ?thesis
            using f1 \<open>finite {x. \<exists>q\<in>set qs. rpoly q x = 0}\<close> mem_list by fastforce
        qed
        have "rpoly a x1 \<noteq> 0" using hnz 
          unfolding has_no_zeros_def sign_vec_def squash_def by auto
        then show "False" using not_in x1_in 
          by auto
      qed
    qed
    then have non_mem: "\<not> List.member ?zer_list x1"
      using all_squarefree unfolding rsquarefree_def hnz apply (auto)
      using hnz x1_prop
      by (simp add: in_set_member) 
    have "?zer_list \<noteq> [] \<Longrightarrow> ((x1 \<ge> (?zer_list ! 0)) \<and> (x1 \<le> (?zer_list ! (length ?zer_list - 1))))
\<Longrightarrow> (\<exists> n < (length ?zer_list - 1). x1 > (?zer_list ! n) \<and> x1 < (?zer_list ! (n+1)))"
    proof - 
      assume "?zer_list \<noteq> []"
      assume x1_asm: "(x1 \<ge> (?zer_list ! 0)) \<and> (x1 \<le> (?zer_list ! (length ?zer_list - 1)))"
      have nm1: "x1 \<noteq> ?zer_list ! 0" using non_mem
        using \<open>sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0} \<noteq> []\<close> in_set_member
        by (metis (no_types, lifting) in_set_conv_nth length_greater_0_conv)
      have nm2: "x1 \<noteq> ?zer_list ! (length ?zer_list -1)" using non_mem
        by (metis (no_types, lifting) One_nat_def \<open>sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0} \<noteq> []\<close> diff_Suc_less in_set_member length_greater_0_conv nth_mem) 
      then have x_asm_var: "x1 > (?zer_list ! 0) \<and> x1 < ?zer_list ! (length ?zer_list -1)"
        using x1_asm nm1 nm2 by auto
      have "(\<forall>n. (n < (length ?zer_list - 1) \<and>  x1 \<ge> (?zer_list ! n) \<longrightarrow> x1 \<ge> (?zer_list ! (n+1)))) \<Longrightarrow> False"
      proof - 
        assume assump: "(\<forall>n. (n < (length ?zer_list - 1) \<and>  x1 \<ge> (?zer_list ! n) \<longrightarrow> x1 \<ge> (?zer_list ! (n+1))))"
        have zer_case: "x1 \<ge> ?zer_list ! 0" using x_asm_var by auto
        have all_n: "\<And> n. (n < (length ?zer_list - 1) \<longrightarrow> x1 \<ge> ?zer_list ! n) "
        proof -
          fix n
          show n_lt: "(n < (length ?zer_list - 1) \<longrightarrow> x1 \<ge> ?zer_list ! n)"
          proof (induct n)
            case 0
            then show ?case using zer_case
              by blast 
          next
            case (Suc n)
            then show ?case 
              using assump
              using Suc_eq_plus1 Suc_lessD by presburger 
          qed
        qed
        have "(length ?zer_list - 2) \<le> length ?zer_list -1"
          using diff_le_mono2 one_le_numeral by blast 
        have "x1 \<ge> ?zer_list ! (length ?zer_list - 1)"
        proof -
          have h1: "length ?zer_list = 1 \<longrightarrow> x1 \<ge> ?zer_list ! (length ?zer_list - 1)"
            using assump zer_case by auto
          have h2: "length ?zer_list > 1 \<longrightarrow> x1 \<ge> ?zer_list ! (length ?zer_list - 1)"
            using all_n assump apply (auto)
            by (metis (mono_tags, lifting) Suc_diff_Suc lessI) 
          then show ?thesis using h1 h2 apply (auto)
            using zer_case by blast
        qed
        then show False using all_n x_asm_var  
          by linarith 
      qed
      then show ?thesis
        using x1_asm
        by (smt One_nat_def Suc_pred \<open>sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0} \<noteq> []\<close> in_set_member length_greater_0_conv less_SucI non_mem nth_mem) 
    qed
    then have h1: "(?zer_list \<noteq> [] \<and> (x1 \<ge> (?zer_list ! 0)) \<and> (x1 \<le> (?zer_list ! (length ?zer_list - 1))) \<Longrightarrow>
      (\<exists> n < (length ?zer_list - 1). x1 > (?zer_list ! n) \<and> x1 < (?zer_list ! (n+1))))"
      by blast
    then show ?thesis apply (auto)
      using zer_list_prop not_less
      by auto 
  qed
qed

(* This lemma is essentially saying that the zeros of coprime_r capture all relevant sample points.
From roots_of_coprime_r_location_property, we know that any zero of coprime_r is either between two 
  roots, or it's smaller than the least root (neg inf), or it's greater than the biggest root (pos inf).
Then, since the polynomials have constant signs within those intervals, the zeros of coprime_r 
  capture all the relevant information.
*)
lemma roots_of_coprime_r_capture_sgas_without_zeros: 
  fixes qs:: "rat poly list"
  fixes sga:: "rat list"
  assumes pairwise_rel_prime: "pairwise_coprime_list qs"
  assumes all_squarefree: "\<And>q. q \<in> set qs \<Longrightarrow> rsquarefree q"
  assumes ex_x1: "sga = sign_vec qs x1"
  assumes hnz: "has_no_zeros sga"
  shows "(\<exists>w \<in> (roots_of_coprime_r (cast_rat_list qs)). sga = (sign_vec qs w))"
proof - 
  obtain x1 where x1_prop: "sga = (sign_vec qs x1)" using ex_x1 by auto
  let ?zer_list = "sorted_list_of_set {(x::real). (\<exists>q \<in> set(qs). (rpoly q x = 0))} :: real list"
  have strict_sorted_h: "strict_sorted ?zer_list" using sorted_sorted_list_of_set
      strict_sorted_iff by auto
  then have sorted_hyp: "\<forall>q < length ?zer_list. (q + 1 < length ?zer_list) \<longrightarrow>
     (?zer_list ! q) < (?zer_list ! (q +1))" 
    apply (auto) using lessI sorted_wrt_iff_nth_less strict_sorted_sorted_wrt
    by (metis (no_types, lifting) length_sorted_list_of_set strict_sorted_h)  
  then have sorted_hyp_var: "\<forall>q1 < length ?zer_list. \<forall>q2 < length ?zer_list. (q1 < q2 \<longrightarrow>
     (?zer_list ! q1) < (?zer_list ! q2))"
    by (metis (no_types, lifting) sorted_wrt_iff_nth_less strict_sorted_h strict_sorted_sorted_wrt) 
  then have sorted_hyp_var2: "\<forall>q1 < length ?zer_list. ((?zer_list ! q1)::real) \<le> (?zer_list ! (length ?zer_list - 1))"
    apply (auto)
    by (smt (z3) Suc_pred diff_less gr_implies_not0 less_SucE zero_less_Suc) 
  have nonz_q: "\<forall>q \<in>set qs. q \<noteq> 0"
    using all_squarefree unfolding rsquarefree_def using in_set_member by auto 
  then have "\<forall>q \<in>set qs. finite {x. rpoly q x = 0}"
    by (simp add: poly_roots_finite)
  then have fin_set: "finite {x. \<exists>q\<in>set qs. rpoly q x = 0}"
    by auto
  have x1_and_roots: "?zer_list \<noteq> [] \<longrightarrow> ((x1 < (?zer_list ! 0)) \<or> (x1 > (?zer_list ! (length ?zer_list - 1)) \<or>
    (\<exists> n < (length ?zer_list - 1). x1 > (?zer_list ! n) \<and> x1 < (?zer_list ! (n+1)))))" 
    using roots_of_coprime_r_location_property x1_prop assms by auto
  have x2gt: "\<forall>x2>x1. sign_vec qs x1 \<noteq> sign_vec qs x2 \<longrightarrow> (\<exists>r>x1. r \<le> x2 \<and> (\<exists>q\<in>set qs. rpoly q r = 0))" 
    using hnz x1_prop zero_above[of qs x1] by auto
  have x2lt: "\<forall>x2<x1. sign_vec qs x1 \<noteq> sign_vec qs x2 \<longrightarrow> (\<exists>r<x1. x2 \<le> r \<and> (\<exists>q\<in>set qs. rpoly q r = 0))"
    using hnz x1_prop zero_below[of qs x1] by (auto) 
  have triv_neg_inf_h: "?zer_list = [] \<Longrightarrow>  sga = (sign_vec qs (-crb (prod_list (cast_rat_list qs))))" 
  proof -
    assume empty_zer: "(?zer_list:: real list) = []"
    let ?zer_set = "{x. \<exists>q\<in>set qs. rpoly q x = 0}:: real set"
    have fin_zer: "finite ?zer_set" using fin_set by auto
    have "finite ?zer_set \<Longrightarrow> (sorted_list_of_set ?zer_set = []) = (?zer_set = {})" 
      using fin_zer sorted_list_of_set_eq_Nil_iff[where A = "?zer_set"]  by auto
    then have "(sorted_list_of_set ?zer_set = []) = (?zer_set = {})"
      using fin_zer by auto
    then have nozers: "?zer_set = {}"
      using empty_zer by auto
    then have "\<not>(\<exists>(r::real). (\<exists>(q::rat poly)\<in>set qs. rpoly q r = 0))"
      using nozers by auto
    then have "\<forall>y. sign_vec qs x1 = sign_vec qs y"
    proof -
      fix y
      have gt_prop: "x1 > y \<longrightarrow> sign_vec qs x1 = sign_vec qs y"
        using hnz x1_prop zero_below[of qs x1] apply (auto)
        using \<open>\<nexists>r. \<exists>q\<in>set qs. rpoly q r = 0\<close> by blast
      have lt_prop: "x1 < y \<longrightarrow> sign_vec qs x1 = sign_vec qs y"
        using zero_above[of qs x1] apply (auto)
        using \<open>\<nexists>r. \<exists>q\<in>set qs. rpoly q r = 0\<close> x2gt by blast 
      show ?thesis using gt_prop lt_prop apply (auto)
        apply (metis \<open>\<nexists>r. \<exists>q\<in>set qs. rpoly q r = 0\<close> linorder_neqE_linordered_idom x2gt x2lt)
        using x2gt x2lt apply (auto)
        apply (metis \<open>\<nexists>r. \<exists>q\<in>set qs. rpoly q r = 0\<close> linorder_neqE_linordered_idom)
        apply (metis \<open>\<nexists>r. \<exists>q\<in>set qs. rpoly q r = 0\<close> linorder_neqE_linordered_idom)
        by (metis \<open>\<nexists>r. \<exists>q\<in>set qs. rpoly q r = 0\<close> linorder_neqE_linordered_idom)
    qed
    then show ?thesis
      by (simp add: x1_prop) 
  qed
  have neg_inf_h: "?zer_list \<noteq>[] \<Longrightarrow> (x1 < (?zer_list ! 0) \<Longrightarrow> sga = (sign_vec qs (-crb (prod_list (cast_rat_list qs)))))" 
  proof - 
    let ?neg_crb = "-crb (prod_list (cast_rat_list qs))"
    assume len_nontriv: "?zer_list \<noteq>[]"
    assume x1_lt: "x1 < ?zer_list ! 0"
    have r_gt: "\<forall>r. (\<exists>q\<in>set qs. rpoly q r = 0) \<longrightarrow> r \<ge> (?zer_list ! 0)"
    proof clarsimp 
      fix q::"rat poly"
      fix r:: "real"
      assume q_in: "q \<in> set qs" 
      assume "rpoly q r = 0"
      then have "r \<in>  {x. \<exists>q\<in>set qs. rpoly q x = 0}" using q_in by auto
      then have "List.member (sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0}) r" 
        using  in_set_member set_sorted_list_of_set fin_set apply (auto)
        by (smt \<open>r \<in> {x. \<exists>q\<in>set qs. rpoly q x = 0}\<close> fin_set in_set_member set_sorted_list_of_set) 
      then show "sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0} ! 0 \<le> r"
        using sorted_hyp_var
        by (metis (no_types, lifting) gr_implies_not0 in_set_conv_nth in_set_member not_less sorted_iff_nth_mono sorted_sorted_list_of_set) 
    qed
    have prod_zer: "\<forall>x. (\<exists>q\<in>set qs. rpoly q x = 0) \<longrightarrow> (poly (prod_list (cast_rat_list qs)) x) = 0"
      using prod_list_zero_iff[where xs = "(cast_rat_list qs)"] unfolding cast_rat_list_def
      apply (auto)
      using nonz_q apply blast
      by (metis (no_types, hide_lams) image_eqI list.set_map of_rat_poly_hom.prod_list_map_hom poly_prod_list_zero_iff) 
    have "?zer_list \<noteq>[] \<longrightarrow> List.member (sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0})
     (?zer_list ! 0)" 
      using nth_Cons_0 apply (auto)
      by (meson gr0I in_set_member length_0_conv nth_mem) 
    then have "?zer_list \<noteq>[] \<longrightarrow> (?zer_list ! 0)
   \<in> {x. \<exists>q\<in>set qs. rpoly q x = 0}"
      using in_set_member[where x = "(sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0} ! 0)",
          where xs = "sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0}"]
          set_sorted_list_of_set fin_set
      by blast 
    then have "?zer_list \<noteq>[] \<longrightarrow> (\<exists>q\<in>set qs. rpoly q (?zer_list ! 0) = 0)"
      by blast
    then have poly_zer: "?zer_list \<noteq>[] \<longrightarrow> (poly (prod_list (cast_rat_list qs)) (?zer_list ! 0)) = 0" 
      using prod_zer by auto
    have "\<forall>q. List.member (cast_rat_list qs) q \<longrightarrow>q \<noteq> 0" using nonz_q
      unfolding cast_rat_list_def using in_set_member imageE image_set map_poly_zero of_rat_eq_0_iff
      by smt
    then have "(prod_list (cast_rat_list qs)) \<noteq> 0"
      using prod_list_zero_iff in_set_member apply (auto)
      by fastforce 
    then have crb_lt: "?zer_list \<noteq>[] \<longrightarrow> ?neg_crb < ?zer_list ! 0"
      using crb_lem_neg[where p = "(prod_list (cast_rat_list qs))", where x = "sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0} ! 0"] apply (auto) 
      using poly_zer
      by blast 
    have crb_gt_x1: "?zer_list \<noteq>[] \<longrightarrow> (?neg_crb > x1 \<longrightarrow> (sga \<noteq> (sign_vec qs ?neg_crb)) \<longrightarrow> (\<exists>r>x1. r \<le> ?neg_crb \<and> (\<exists>q\<in>set qs. rpoly q r = 0)))"
      using x2gt apply (auto)
      using crb_lt r_gt x1_prop by fastforce 
    have crb_lt_x1: "?neg_crb < x1 \<longrightarrow> (sga \<noteq> (sign_vec qs ?neg_crb)) \<longrightarrow> (\<exists>r<x1. ?neg_crb \<le> r \<and> (\<exists>q\<in>set qs. rpoly q r = 0))"
      using x2lt apply (auto)
      using x1_lt r_gt x1_prop by fastforce  
    show ?thesis using len_nontriv crb_gt_x1 crb_lt_x1  x1_lt crb_lt r_gt  apply (auto)
      using x1_prop by blast 
  qed
  have pos_inf_h: "?zer_list \<noteq> [] \<Longrightarrow> (x1 > (?zer_list ! (length ?zer_list - 1)) \<Longrightarrow> sga = (sign_vec qs (crb (prod_list (cast_rat_list qs)))))" 
  proof - 
    let ?pos_crb = "crb (prod_list (cast_rat_list qs))"
    assume len_nontriv: "?zer_list \<noteq>[]"
    assume x1_lt: "x1 > ?zer_list ! (length ?zer_list - 1)"
    have r_gt: "\<And>r. (\<exists>q\<in>set qs. rpoly q r = 0) \<Longrightarrow> r \<le> (?zer_list ! (length ?zer_list - 1))"
    proof - 
      fix r:: "real"
      assume q_in: "(\<exists>q\<in>set qs. rpoly q r = 0)" 
      then obtain q::"rat poly" where q_prop: "q \<in> set qs \<and> rpoly q r = 0" by auto
      then have "r \<in>  {x. \<exists>q\<in>set qs. rpoly q x = 0}" using q_in by auto
      then have "List.member (sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0}) r" 
        using in_set_member set_sorted_list_of_set fin_set by smt    
      then have "\<exists>n < (length ?zer_list). r = ?zer_list ! n"
        by (metis (no_types, lifting) in_set_conv_nth in_set_member)
      then obtain n where n_prop: "n < length ?zer_list \<and> r = ?zer_list ! n"
        by auto
      then show "r \<le> (?zer_list ! (length ?zer_list - 1))"
      proof - 
        have "\<forall>q1. q1 < length ?zer_list \<longrightarrow> (?zer_list ! q1) \<le> (?zer_list ! (length ?zer_list - 1:: nat))"
          using sorted_hyp_var2 by auto
        then have "(?zer_list ! n) \<le> (?zer_list ! (length ?zer_list - 1))"
          using n_prop by auto
        then show ?thesis using n_prop by auto
      qed
    qed
    have prod_zer: "\<forall>x. (\<exists>q\<in>set qs. rpoly q x = 0) \<longrightarrow> (poly (prod_list (cast_rat_list qs)) x) = 0"
      using prod_list_zero_iff[where xs = "(cast_rat_list qs)"] unfolding cast_rat_list_def
      apply (auto)
      using nonz_q apply blast
      by (metis (no_types, hide_lams) image_eqI list.set_map of_rat_poly_hom.prod_list_map_hom poly_prod_list_zero_iff) 
    have "?zer_list \<noteq>[] \<longrightarrow> List.member (sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0})
     (?zer_list ! (length ?zer_list -1))" 
      using nth_Cons_0 apply (auto)
      by (metis (no_types, lifting) diff_less in_set_conv_nth in_set_member length_greater_0_conv length_sorted_list_of_set zero_less_Suc) 
    then have "?zer_list \<noteq>[] \<longrightarrow> (?zer_list ! (length ?zer_list -1))
   \<in> {x. \<exists>q\<in>set qs. rpoly q x = 0}"
      using in_set_member[where x = "(sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0} ! (length ?zer_list -1))",
          where xs = "sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0}"]
          set_sorted_list_of_set fin_set
      by blast 
    then have "?zer_list \<noteq>[] \<longrightarrow> (\<exists>q\<in>set qs. rpoly q (?zer_list ! (length ?zer_list -1)) = 0)"
      by blast
    then have poly_zer: "?zer_list \<noteq>[] \<longrightarrow> (poly (prod_list (cast_rat_list qs)) (?zer_list ! (length ?zer_list -1))) = 0" 
      using prod_zer by auto
    have "\<forall>q. List.member (cast_rat_list qs) q \<longrightarrow>q \<noteq> 0" using nonz_q
      unfolding cast_rat_list_def using in_set_member imageE image_set map_poly_zero of_rat_eq_0_iff
      by smt 
    then have "(prod_list (cast_rat_list qs)) \<noteq> 0"
      using prod_list_zero_iff in_set_member apply (auto)
      by fastforce 
    then have crb_lt: "?zer_list \<noteq>[] \<longrightarrow> ?pos_crb > ?zer_list ! (length ?zer_list -1)"
      using crb_lem_pos[where p = "(prod_list (cast_rat_list qs))", where x = "sorted_list_of_set {x. \<exists>q\<in>set qs. rpoly q x = 0} ! (length ?zer_list -1)"] apply (auto) 
      using poly_zer
      by simp 
    have crb_gt_x1: "?zer_list \<noteq>[] \<longrightarrow> ((?pos_crb::real) > (x1::real) \<longrightarrow> (sga \<noteq> (sign_vec (qs::rat poly list) (?pos_crb::real))) \<longrightarrow> (\<exists>(r::real)<x1. r \<ge> ?pos_crb \<and> (\<exists>(q::rat poly)\<in>set qs. rpoly q r = 0)))"
      using x2gt apply (auto)
      using crb_lt r_gt x1_prop 
      using x1_lt by fastforce 
    have crb_lt_x1: "?pos_crb < x1 \<longrightarrow> (sga \<noteq> (sign_vec qs ?pos_crb)) \<longrightarrow> (\<exists>r>x1. ?pos_crb \<ge> r \<and> (\<exists>q\<in>set qs. poly (real_of_rat_poly q) r = 0))"
      using x2lt apply (auto)
      using x1_lt r_gt x1_prop
      by (meson \<open>prod_list (cast_rat_list qs) \<noteq> 0\<close> crb_lem_pos not_less prod_zer) 
    show ?thesis using len_nontriv crb_gt_x1 crb_lt_x1  x1_lt crb_lt r_gt  apply (auto)
      using x1_prop
      by blast
  qed
  have between_h: "(\<exists> n < (length ?zer_list - 1). x1 > (?zer_list ! n) \<and> x1 < (?zer_list ! (n+1))) \<Longrightarrow> (\<exists>w \<in> (roots_of_coprime_r (cast_rat_list qs)). sga = (sign_vec qs w))"
  proof - 
    assume "(\<exists> n < (length ?zer_list - 1). x1 > (?zer_list ! n) \<and> x1 < (?zer_list ! (n+1)))"
    then obtain n where n_prop: "n < (length ?zer_list - 1) \<and> x1 > (?zer_list ! n) \<and> x1 < (?zer_list ! (n+1))"
      by auto
    have "\<forall>q1 q2. (q1 \<noteq> q2 \<and> (List.member (cast_rat_list qs) q1) \<and> (List.member (cast_rat_list qs) q2))\<longrightarrow> coprime q1 q2"
      using pairwise_rel_prime coprime_rat_poly_iff_coprimereal_poly
      unfolding pairwise_coprime_list_def
      by (smt cast_rat_list_def imageE image_set in_set_conv_nth in_set_member)
    then have all_prop: "\<forall>x1. \<forall>x2. ((x1 < x2 \<and> (\<exists>q1 \<in> set (cast_rat_list(qs)). (poly q1 x1) = 0) \<and> (\<exists>q2\<in> set((cast_rat_list(qs))). (poly q2 x2) = 0)) \<longrightarrow> (\<exists>q. x1 < q \<and> q < x2 \<and> poly (coprime_r (cast_rat_list qs)) q = 0))"
      using coprime_r_roots_prop 
      by auto
    have exq1: "(\<exists>q1 \<in> set (cast_rat_list(qs)). (poly q1 (?zer_list ! n)) = 0)"
      unfolding cast_rat_list_def using n_prop apply (auto)
      by (smt (verit, ccfv_SIG) One_nat_def Suc_eq_plus1 Suc_lessD fin_set length_sorted_list_of_set less_diff_conv mem_Collect_eq nth_mem set_sorted_list_of_set)    
    have exq2: "(\<exists>q2 \<in> set (cast_rat_list(qs)). (poly q2 (?zer_list ! (n+1))) = 0)"
      unfolding cast_rat_list_def using n_prop One_nat_def Suc_eq_plus1 fin_set less_diff_conv mem_Collect_eq nth_mem set_sorted_list_of_set
      by (smt (verit, ccfv_SIG) image_eqI set_map)
    have n_prop2: "(((?zer_list ! n) < (?zer_list ! (n+1)) \<and> (\<exists>q1 \<in> set (cast_rat_list(qs)). (poly q1 (?zer_list ! n)) = 0) \<and> (\<exists>q2\<in> set((cast_rat_list(qs))). (poly q2 (?zer_list ! (n+1))) = 0)))"
      using exq1 exq2 sorted_hyp n_prop by auto
    then have "(\<exists>q. (?zer_list ! n) < q \<and> q < (?zer_list ! (n+1)) \<and> poly (coprime_r (cast_rat_list qs)) q = 0)" 
      using all_prop n_prop2 by auto
    then  have "\<exists>w \<in> (roots_of_coprime_r (cast_rat_list qs)). (?zer_list ! n) < w \<and> w < (?zer_list ! (n+1))"
      apply (auto)
      using roots_of_coprime_r_def by auto 
    then obtain w where w_prop: "w \<in> (roots_of_coprime_r (cast_rat_list qs)) \<and> (?zer_list ! n) < w \<and> w < (?zer_list ! (n+1))" by auto
    have n_lt1: "n < length ?zer_list" using n_prop
      using add_lessD1 less_diff_conv by blast
    have n_lt2: "n + 1 < length ?zer_list" using n_prop
      using less_diff_conv by blast 
    have sorted_hyp_var3: "?zer_list ! n  < ?zer_list ! (n + 1)" using sorted_hyp 
        n_lt1 n_lt2  by auto 
    then have helper: "w > x1 \<longrightarrow> \<not>(\<exists>(x::real). (List.member ?zer_list x \<and> x1 \<le> x \<and> x \<le> w))"
      using n_prop w_prop x1_prop strict_sorted_h sorted_list_lemma[where n = "n", where l = ?zer_list, where a = "x1", where b = "w"] sorted_hyp_var3 
      by auto
    have no_root1: "w > x1 \<Longrightarrow> \<not>(\<exists>r>x1. r \<le> w \<and> (\<exists>q\<in>set qs. rpoly q r = 0))"
    proof - 
      assume "w > x1"
      then have nex: "\<not>(\<exists>(x::real). (List.member ?zer_list x \<and> x1 \<le> x \<and> x \<le> w))"
        using helper by auto
      have "(\<exists>r>x1. r \<le> w \<and> (\<exists>q\<in>set qs. rpoly q r = 0)) \<Longrightarrow> False"
      proof -
        assume "(\<exists>r>x1. r \<le> w \<and> (\<exists>q\<in>set qs. rpoly q r = 0))"
        then obtain r where r_prop: "r > x1 \<and>r \<le> w \<and>(\<exists>q\<in>set qs. rpoly q r = 0)" by auto
        then have "List.member ?zer_list r \<and>x1 \<le> r \<and>x1 \<le> w "
          by (smt fin_set in_set_member mem_Collect_eq set_sorted_list_of_set)
        then show ?thesis using nex r_prop
          by blast 
      qed
      then show ?thesis by auto
    qed
    have helper2: "w < x1 \<longrightarrow> \<not>(\<exists>(x::real). (List.member ?zer_list x \<and> w \<le> x \<and> x \<le> x1))"
      using n_prop w_prop x1_prop strict_sorted_h sorted_list_lemma[where n = "n", where l = ?zer_list, where a = "w", where b = "x1"] sorted_hyp_var3 
      by auto
    have no_root2: "w < x1 \<Longrightarrow> \<not>(\<exists>r<x1. w \<le> r \<and> (\<exists>q\<in>set qs. rpoly q r = 0))" 
    proof - 
      assume "w < x1"
      then have nex: "\<not>(\<exists>(x::real). (List.member ?zer_list x \<and>  w \<le> x \<and> x \<le> x1))"
        using helper2 by auto
      have "(\<exists>r<x1. w \<le> r \<and> (\<exists>q\<in>set qs. rpoly q r = 0)) \<Longrightarrow> False"
      proof -
        assume "(\<exists>r<x1. w \<le> r\<and> (\<exists>q\<in>set qs. rpoly q r = 0))"
        then obtain r where r_prop: "r < x1 \<and> w \<le> r \<and>(\<exists>q\<in>set qs. rpoly q r = 0)" by auto
        then have "List.member ?zer_list r \<and> w \<le> r \<and> r \<le> x1 "
          by (smt fin_set in_set_member mem_Collect_eq set_sorted_list_of_set) 
        then show ?thesis using nex r_prop
          by blast 
      qed
      then show ?thesis by auto
    qed
    then have w_gt: "w > x1 \<longrightarrow> (sign_vec qs x1) = (sign_vec qs w)"
      using no_root1 n_prop x2gt by auto
    have w_lt: "w < x1 \<longrightarrow> (sign_vec qs x1)  = (sign_vec qs w)" 
      using no_root2 n_prop x2lt  by auto
    then have "sga = (sign_vec qs w)" using w_gt w_lt x1_prop by auto
    then show "(\<exists>w \<in> (roots_of_coprime_r (cast_rat_list qs)). sga = (sign_vec qs w))"
      using w_prop by auto
  qed
  show ?thesis using triv_neg_inf_h neg_inf_h pos_inf_h between_h x1_and_roots
    by (metis (mono_tags, lifting) coprime_r_zero1 coprime_r_zero2 mem_Collect_eq roots_of_coprime_r_def) 
qed

(* This lemma heavily relies on the main BKR_Proofs result and also the lemma named
  roots_of_coprime_r_capture_sgas_without_zeros *)
lemma find_csas_lemma_nozeros:
  fixes qs:: "rat poly list"
  assumes fs: "factorize_polys qs = (fs,data)"
  assumes "fs \<noteq> []"
  shows "(csa \<in> (consistent_sign_vectors fs UNIV) \<and> has_no_zeros csa) \<longleftrightarrow> 
    csa \<in> set (find_consistent_signs_at_roots (coprime_r (cast_rat_list fs))  (cast_rat_list fs))"
proof -
  let ?new_l = "cast_rat_list fs"
  let ?copr = "coprime_r ?new_l"
  have copr_nonz: "?copr \<noteq> 0"
    using coprime_r_nonzero[OF assms(1-2)] unfolding cast_rat_list_def by auto
  have nontriv_list: "0 < length ?new_l"
    using assms cast_rat_list_def by (auto)
  have pairwise_cp: "(\<And>q. q \<in> set ?new_l \<Longrightarrow>
       algebraic_semidom_class.coprime ?copr q)" using coprime_r_coprime_prop[OF assms(1)]
    apply (auto)
    by (metis cast_rat_list_def comm_monoid_mult_class.coprime_commute coprime_iff_coprime list.set_map) 
  have set_fsga: "set(find_consistent_signs_at_roots ?copr ?new_l) = set(characterize_consistent_signs_at_roots ?copr ?new_l)"
    using find_consistent_signs_at_roots[OF copr_nonz pairwise_cp] by auto
  then have csa_in_hyp: "csa \<in> set (find_consistent_signs_at_roots ?copr ?new_l)
      \<longleftrightarrow> csa \<in> set(characterize_consistent_signs_at_roots ?copr ?new_l)" by auto
  have forward: "(csa \<in> (consistent_sign_vectors fs UNIV) \<and> has_no_zeros csa)
     \<Longrightarrow> csa \<in> set(characterize_consistent_signs_at_roots ?copr ?new_l)"
  proof - 
    assume csa_in: "(csa \<in> (consistent_sign_vectors fs UNIV) \<and> has_no_zeros csa)"
    have fin: "finite {x. poly (coprime_r (cast_rat_list fs)) x = 0}"
      using copr_nonz poly_roots_finite
      by (simp add: poly_roots_finite fs)
    have pcl: "pairwise_coprime_list fs"
      using coprime_factorize fs
      by (metis fst_conv)
    have sqf: "\<And>q. q \<in> set fs \<Longrightarrow> rsquarefree q"
      using factorize_polys_square_free[OF assms(1)]
      by (metis square_free_rsquarefree) 
    obtain x1 where x1:"csa = sign_vec fs x1"
      using consistent_sign_vectors_def csa_in by auto 
    have hnz: "has_no_zeros csa" using csa_in by auto
    obtain w where w_prop: "w\<in>roots_of_coprime_r (cast_rat_list fs)" "csa = sign_vec fs w"
      using roots_of_coprime_r_capture_sgas_without_zeros[OF pcl sqf x1 hnz]
      by auto
    have w_root: "poly (coprime_r (cast_rat_list fs)) w = 0"
      using w_prop
      by (simp add: roots_of_coprime_r_def) 
    then have "w \<in> {x. poly (coprime_r (cast_rat_list fs)) x = 0}"
      by auto
    then have w_ins: "w \<in> set (characterize_root_list_p (coprime_r (cast_rat_list fs)))"
      using fin set_sorted_list_of_set[where A="{x. poly (coprime_r (cast_rat_list fs)) x = 0}"]
      unfolding characterize_root_list_p_def
      by auto
    have "map ((\<lambda>x. if 0 < x then 1 else if x < 0 then - 1 else 0) \<circ> (\<lambda>p. rpoly p w)) fs =
          map ((\<lambda>x. if 0 < x then 1 else - 1) \<circ> (\<lambda>p. rpoly p w)) fs"
    proof - 
      have "\<not>(\<exists>x \<in> set fs. rpoly x w = 0)"
      proof clarsimp 
        fix x
        assume x_in: "x \<in> set fs"
        assume x_zer: "rpoly x w = 0"
        then have "\<exists>k < length fs. nth fs k = x" 
          using x_in
          by (simp add: in_set_conv_nth) 
        then obtain k where k_prop: "k < length fs \<and> fs ! k = x"
          by auto
        then have "(sign_vec fs w) ! k = 0" using x_zer apply (auto) 
          unfolding sign_vec_def squash_def by auto
        then have "\<not> (has_no_zeros (sign_vec fs w))"
          apply (auto)
          by (simp add: hnz_prop k_prop)
        then show False using hnz unfolding sign_vec_def squash_def
          using \<open>\<not> has_no_zeros (sign_vec fs w)\<close> w_prop(2) by blast
      qed
      then show ?thesis using hnz unfolding sign_vec_def squash_def by auto
    qed
    then have "map ((\<lambda>x. if 0 < x then 1 else if x < 0 then - 1 else 0) \<circ> (\<lambda>p. rpoly p w)) fs =
    map (\<lambda>q. if 0 < poly q w then 1 else - 1)
     (cast_rat_list fs)" 
      unfolding cast_rat_list_def by auto
    then have "csa = map (\<lambda>q. if 0 < poly q w then 1 else - 1)
             (cast_rat_list fs)"
      by (simp add: comp_def sign_vec_def squash_def w_prop(2))    
    then show ?thesis unfolding characterize_consistent_signs_at_roots_def  
      apply (auto) unfolding signs_at_def using w_ins w_prop
      using consistent_sign_vectors_consistent_sign_vectors_r consistent_sign_vectors_def consistent_sign_vectors_r_def signs_at_def by force
  qed
  have backward: "csa \<in> set(characterize_consistent_signs_at_roots ?copr ?new_l) \<Longrightarrow>
    (csa \<in> (consistent_sign_vectors fs UNIV) \<and> has_no_zeros csa)"
  proof - 
    assume csa_in: "csa \<in> set(characterize_consistent_signs_at_roots ?copr ?new_l)"
    have csa_in_old_set: "csa \<in> set (characterize_consistent_signs_at_roots_copr ?copr ?new_l)"
      using csa_list_copr_rel copr_nonz csa_in find_consistent_signs_at_roots_copr pairwise_cp set_fsga by auto 
    have "\<forall>(x::real). \<forall> (l::real poly list). rec_list True (\<lambda>h T. If (h = 0) False)
          (map (\<lambda>q. if 0 < poly q x then (1::rat) else (-1::rat))
            l)" 
    proof clarsimp  
      fix x::"real"
      fix l::"real poly list"
      show " rec_list True (\<lambda>h T. If (h = 0) False)
            (map (\<lambda>q. if 0 < poly q x then (1::rat) else (-1::rat)) l) "
      proof (induct l)
        case Nil
        then show ?case
          by simp 
      next
        case (Cons a l)
        then show ?case by auto
      qed
    qed
    then have "\<forall>x. rec_list True (\<lambda>h T. If (h = 0) False)
          (map (\<lambda>q. if 0 < poly q x then (1::rat) else - 1)
            (cast_rat_list fs))" 
      by auto
    then have hnz: "has_no_zeros csa" 
      using csa_in_old_set
      unfolding characterize_consistent_signs_at_roots_copr_def consistent_sign_vec_copr_def 
      apply (auto) unfolding has_no_zeros_def  
      by auto
    have "\<exists>w \<in> set(characterize_root_list_p ?copr). csa = consistent_sign_vec_copr ?new_l w" 
      using csa_in_old_set using characterize_consistent_signs_at_roots_copr_def by auto
    then obtain w where w_prop: "w \<in> set (characterize_root_list_p ?copr) \<and> csa = consistent_sign_vec_copr ?new_l w"
      by auto
    then have "poly ?copr w = 0" unfolding characterize_root_list_p_def
      by (simp add: copr_nonz poly_roots_finite)
    then have copr_prop: "\<forall>p \<in> set(?new_l). poly p w \<noteq> 0"
      using w_prop coprime_r_coprime_prop apply (auto)
      by (meson coprime_poly_0 in_set_member pairwise_cp) 
    then have "consistent_sign_vec_copr ?new_l w = sign_vec fs w"
      unfolding sign_vec_def squash_def consistent_sign_vec_copr_def
        cast_rat_list_def by auto
    then show ?thesis using hnz w_prop apply (auto)
      using consistent_sign_vectors_def by blast 
  qed
  have "(csa \<in> (consistent_sign_vectors fs UNIV) \<and> has_no_zeros csa)
     \<longleftrightarrow> csa \<in> set(characterize_consistent_signs_at_roots ?copr ?new_l)"
    using forward backward by blast
  then show ?thesis using  csa_in_hyp by auto
qed

lemma range_eq: 
  fixes a
  fixes b
  shows "a = b \<longrightarrow> range a = range b"
  by simp

lemma removeAt_distinct:
  shows "distinct fss \<Longrightarrow> distinct (removeAt i fss)"
  unfolding removeAt_def
  by (simp add: set_take_disj_set_drop_if_distinct)

lemma consistent_signs_atw:
  assumes "\<And>p. p \<in> set fs \<Longrightarrow> poly p x \<noteq> 0"
  shows "consistent_sign_vec_copr fs x = signs_at fs x"
  unfolding consistent_sign_vec_copr_def signs_at_def squash_def o_def
  by (simp add: assms)

(* This could be an alternate (equivalent) definition *)
lemma characterize_consistent_signs_at_roots_rw:
  assumes "p \<noteq> 0"
  assumes copr: "\<And>q. q \<in> set fs \<Longrightarrow> coprime p q"
  shows "set (characterize_consistent_signs_at_roots p fs) =
    consistent_sign_vectors_r fs ({x. poly p x = 0})"
  by (simp add: assms(1) characterize_consistent_signs_at_roots_def consistent_sign_vectors_r_def poly_roots_finite characterize_root_list_p_def)

lemma signs_at_insert:
  assumes "i \<le> length qs"
  shows "insertAt i (squash (poly p x)) (signs_at qs x) =
    signs_at (insertAt i p qs) x"
  unfolding insertAt_def signs_at_def o_def using assms take_map apply auto
  apply (subst drop_map) by simp

lemma length_removeAt:
  assumes "i < length ls"
  shows "length (removeAt i ls) = length ls - 1"
  unfolding removeAt_def using assms by auto

lemma insertAt_removeAt:
  assumes "i < length ls"
  shows "insertAt i (ls!i) (removeAt i ls) = ls"
  unfolding insertAt_def removeAt_def using assms apply auto
  by (simp add: Cons_nth_drop_Suc)

lemma insertAt_nth:
  assumes "i \<le> length ls"
  shows "insertAt i n ls ! i = n"
  unfolding insertAt_def using assms
  by (simp add: nth_append_take)

lemma length_signs_at[simp]:
  shows "length (signs_at qs x) = length qs"
  unfolding signs_at_def by auto

lemma find_csa_at_index:
  assumes "i < length fss"
  assumes "\<And>p q. p \<in> set fss \<Longrightarrow> q \<in> set fss \<Longrightarrow> p \<noteq> q \<Longrightarrow> coprime p q"
  assumes "\<And>p. p \<in> set fss \<Longrightarrow> p \<noteq> 0"
  assumes "distinct fss"
  shows "
  set (map (\<lambda>v. insertAt i 0 v) (find_consistent_signs_at_roots (fss ! i) (removeAt i fss))) =
    {v \<in> consistent_sign_vectors_r fss UNIV. v ! i = 0}"
proof -
  from removeAt_distinct[OF assms(4)]
  have neq: "fss ! i \<noteq> 0" using assms by simp
  have cop: "\<And>q. q \<in> set (removeAt i fss) \<Longrightarrow> coprime (fss ! i) q" using assms
    unfolding removeAt_def 
    apply auto
    using dual_order.strict_trans find_first_unique image_iff less_imp_le_nat less_not_refl nth_image nth_mem
    apply (smt atLeastLessThan_iff dual_order.strict_trans find_first_unique image_iff less_imp_le_nat less_not_refl nth_image nth_mem) 
      by (metis Cons_nth_drop_Suc distinct.simps(2) distinct_drop in_set_dropD nth_mem)
  from find_consistent_signs_at_roots[OF neq] 
  have "set (find_consistent_signs_at_roots (fss ! i) (removeAt i fss)) =
        set (characterize_consistent_signs_at_roots (fss ! i) (removeAt i fss))"
    using cop by auto
  then have eq:  "set (map (insertAt i 0)
          (find_consistent_signs_at_roots (fss ! i)
            (removeAt i fss))) = insertAt i 0 ` set (characterize_consistent_signs_at_roots (fss ! i) (removeAt i fss)) "
    by simp
  from characterize_consistent_signs_at_roots_rw[OF neq cop]
  have eq2: "set (characterize_consistent_signs_at_roots (fss ! i) (removeAt i fss)) = consistent_sign_vectors_r (removeAt i fss)  {x. poly (fss ! i) x = 0}" .
  have ile: "i \<le> length (removeAt i fss)"
    using  length_removeAt[OF assms(1)] assms(1) by linarith
  have 1: "\<And>xb. poly (fss ! i) xb = 0 \<Longrightarrow>
          insertAt i 0 (signs_at (removeAt i fss) xb) \<in> range (signs_at fss)"
  proof -
    fix x
    assume "poly (fss ! i) x = 0"
    then have "insertAt i 0 (signs_at (removeAt i fss) x) =
        insertAt i (squash (poly (fss ! i) x)) (signs_at (removeAt i fss) x)" by (auto simp add: squash_def)
    also have "... =  signs_at (insertAt i (fss ! i)  (removeAt i fss)) x" 
      apply (intro signs_at_insert)
      using  length_removeAt[OF assms(1)]
      using assms(1) by linarith
    also have "... = signs_at fss x" unfolding insertAt_removeAt[OF assms(1)] by auto
    ultimately have *:"insertAt i 0 (signs_at (removeAt i fss) x) = signs_at fss x" by auto
    thus "insertAt i 0 (signs_at (removeAt i fss) x) \<in> range (signs_at fss)" by auto
  qed
  have 2: "\<And>xa. signs_at fss xa ! i = 0 \<Longrightarrow>
          i \<le> length (removeAt i fss) \<Longrightarrow>
          signs_at fss xa
          \<in> insertAt i 0 `
             signs_at (removeAt i fss) `
             {x. poly (fss ! i) x = 0}"
  proof -
    fix x
    assume "signs_at fss x ! i = 0"
    then have z:"poly (fss ! i) x = 0" unfolding signs_at_def o_def squash_def
      by (smt assms(1) class_field.zero_not_one nth_map zero_neq_neg_one)
    then have "insertAt i 0 (signs_at (removeAt i fss) x) =
      insertAt i (squash (poly (fss ! i) x)) (signs_at (removeAt i fss) x)" by (auto simp add: squash_def)
    also have "... =  signs_at (insertAt i (fss ! i)  (removeAt i fss)) x" 
      apply (intro signs_at_insert)
      using  length_removeAt[OF assms(1)]
      using assms(1) by linarith
    also have "... = signs_at fss x" unfolding insertAt_removeAt[OF assms(1)] by auto
    ultimately have *:"insertAt i 0 (signs_at (removeAt i fss) x) = signs_at fss x" by auto
    thus "signs_at fss x \<in> insertAt i 0 ` signs_at (removeAt i fss) ` {x. poly (fss ! i) x = 0}"
      using z
      by (metis (mono_tags, lifting) mem_Collect_eq rev_image_eqI)
  qed
  have "insertAt i 0 ` consistent_sign_vectors_r (removeAt i fss)  {x. poly (fss ! i) x = 0} =
         {v \<in> consistent_sign_vectors_r fss UNIV. v ! i = 0}"
    unfolding consistent_sign_vectors_r_def
    apply (auto simp add: 1)
    apply (subst insertAt_nth)
    using ile by (auto simp add: 2)
  thus ?thesis unfolding eq eq2 .
qed

lemma in_set_concat_map:
  assumes "i < length ls"
  assumes "x \<in> set (f (ls ! i))"
  shows "x \<in> set (concat (map f ls))"
  using assms by auto

lemma find_csas_lemma_onezero_gen:
  fixes qs:: "rat poly list"
  assumes fs: "factorize_polys qs = (fs,data)"
  assumes fss: "fss = cast_rat_list fs"
  shows "(csa \<in> (consistent_sign_vectors_r fss UNIV) \<and> \<not>(has_no_zeros csa))
    \<longleftrightarrow>  csa \<in> set (find_sgas_aux fss)"
proof -
  have a:"(\<And>p q. p \<in> set fss \<Longrightarrow>
          q \<in> set fss \<Longrightarrow>
          p \<noteq> q \<Longrightarrow> coprime p
           q)"
    using cast_rat_list_def factorize_polys_map_coprime fs fss by blast 
  have b:"(\<And>p. p \<in> set fss \<Longrightarrow> p \<noteq> 0)"
    using factorize_polys_map_square_free_prod_list semidom_class.prod_list_zero_iff square_free_def
    using cast_rat_list_def fs fss by blast
  have c:"distinct fss"
    using factorize_polys_map_distinct[OF assms(1)] assms(2) unfolding cast_rat_list_def
    by auto
  have forwards: "csa \<in> (consistent_sign_vectors_r fss UNIV) \<Longrightarrow>
    \<not> (has_no_zeros csa)
    \<Longrightarrow> csa \<in> set (find_sgas_aux fss)"
    unfolding find_sgas_aux_def
  proof -
    assume csa: "csa \<in> (consistent_sign_vectors_r fss UNIV)"
    assume hnz: "\<not>(has_no_zeros csa)"
    then obtain i where i: "i < length csa" "csa ! i = 0" unfolding hnz_prop by auto
    then have cin: "csa \<in> {v \<in> consistent_sign_vectors_r fss UNIV. v ! i = 0}" using csa by auto
    have 1:"i < length fss" using i csa unfolding consistent_sign_vectors_r_def by auto
    from find_csa_at_index[OF 1 a b c]
    have eq: "set (map (\<lambda>v. insertAt i 0 v) (find_consistent_signs_at_roots (fss ! i) (removeAt i fss))) =
      {v \<in> consistent_sign_vectors_r fss UNIV. v ! i = 0}" by auto
    show "csa \<in> set (concat (map (\<lambda>i. map (insertAt i 0) (find_consistent_signs_at_roots (fss ! i) (removeAt i fss))) [0..<length fss]))"
      using cin i unfolding eq[symmetric]
      apply (intro  in_set_concat_map[of i])
      using 1 by auto      
  qed
  have backwards: "csa \<in> set (find_sgas_aux fss) \<Longrightarrow>
    \<not> (has_no_zeros csa) \<and> csa \<in> (consistent_sign_vectors_r fss UNIV)"
  proof -
    assume *: "csa \<in> set (find_sgas_aux fss)"
    then obtain i where i: "i < length fss"
      "csa \<in> set (map (\<lambda>v. insertAt i 0 v) (find_consistent_signs_at_roots (fss ! i) (removeAt i fss)))"
      unfolding find_sgas_aux_def
      by auto
    from find_csa_at_index[OF i(1) a b c]
    have eq: "set (map (\<lambda>v. insertAt i 0 v) (find_consistent_signs_at_roots (fss ! i) (removeAt i fss))) =
      {v \<in> consistent_sign_vectors_r fss UNIV. v ! i = 0}" by auto
    have *: "csa \<in> {v \<in> consistent_sign_vectors_r fss UNIV. v ! i = 0}" using i eq by auto
    then have "length csa = length fss" unfolding consistent_sign_vectors_r_def by auto
    thus ?thesis unfolding has_no_zeros_def using * apply (auto simp add:in_set_conv_nth)
      using i(1) by auto
  qed
  show ?thesis
    using  forwards backwards by blast
qed

lemma mem_append: "List.member (l1@l2) m \<longleftrightarrow> (List.member l1 m \<or> List.member l2 m)"
  by (simp add: List.member_def)

lemma same_sign_cond_rationals_reals:
  fixes qs:: "rat poly list"
  assumes lenh: "length (fst(factorize_polys qs)) > 0"
  shows "set(find_sgas (map (map_poly of_rat) (fst(factorize_polys qs)))) = consistent_sign_vectors (fst(factorize_polys qs)) UNIV"
proof - 
  let ?ftrs = "(fst(factorize_polys qs))"
  have pairwise_rel_prime: "pairwise_coprime_list (fst(factorize_polys qs))"
    using factorize_polys_coprime
    by (simp add: coprime_factorize) 
  have all_squarefree:"\<forall>q. (List.member (fst(factorize_polys qs)) q) \<longrightarrow> (rsquarefree q)"
    using factorize_polys_square_free
    by (metis in_set_member prod.collapse square_free_rsquarefree) 
  have allnonzero: "\<forall>q. (List.member ?ftrs q) \<longrightarrow> q \<noteq> 0"
    using all_squarefree apply (auto)
    using rsquarefree_def by blast 
  have h1: "\<forall> csa. (csa \<in> (consistent_sign_vectors ?ftrs UNIV) \<and> \<not> (has_no_zeros csa))
    \<longleftrightarrow>  csa \<in> set (find_sgas_aux (cast_rat_list ?ftrs))"
    using lenh find_csas_lemma_onezero_gen pairwise_rel_prime allnonzero
    by (metis consistent_sign_vectors_consistent_sign_vectors_r eq_fst_iff) 
  have h2: "\<forall>csa. (csa \<in> (consistent_sign_vectors ?ftrs UNIV) \<and> has_no_zeros csa) \<longleftrightarrow> 
    List.member (find_consistent_signs_at_roots (coprime_r (cast_rat_list ?ftrs)) (cast_rat_list ?ftrs)) csa"
    using lenh find_csas_lemma_nozeros pairwise_rel_prime allnonzero
    by (metis in_set_member length_greater_0_conv prod.collapse)
  have h3: "\<forall> csa. List.member (find_sgas (map (map_poly of_rat) ?ftrs)) csa \<longleftrightarrow> 
      ((List.member (find_sgas_aux (cast_rat_list ?ftrs)) csa) \<or>  (List.member (find_consistent_signs_at_roots (coprime_r (cast_rat_list ?ftrs)) (cast_rat_list ?ftrs)) csa))"
    unfolding find_sgas_def cast_rat_list_def using mem_append
    by metis 
  have h4: "\<forall> csa. List.member (find_sgas (map (map_poly of_rat) ?ftrs)) csa \<longleftrightarrow>
   ((csa \<in> (consistent_sign_vectors ?ftrs UNIV) \<and> has_no_zeros csa) \<or>  (csa \<in> (consistent_sign_vectors ?ftrs UNIV) \<and> \<not> (has_no_zeros csa)))"
    using h1 h2 h3  apply (auto) apply (simp add: in_set_member) by (simp add: in_set_member)  
  have h5: "\<forall>csa. (csa \<in> (consistent_sign_vectors ?ftrs UNIV) \<and> has_no_zeros csa) \<or>  (csa \<in> (consistent_sign_vectors ?ftrs UNIV) \<and> \<not> (has_no_zeros csa))
    \<longleftrightarrow> csa \<in> (consistent_sign_vectors ?ftrs UNIV)"
    by auto 
  then have "\<forall> csa. List.member (find_sgas (map (map_poly of_rat) ?ftrs)) csa \<longleftrightarrow> csa \<in> (consistent_sign_vectors ?ftrs UNIV)"
    using h4
    by blast 
  then show ?thesis using in_set_member apply (auto)
    apply (simp add: in_set_member)
    by (simp add: in_set_member)
qed

lemma factorize_polys_undo_factorize_polys_set:
  assumes "factorize_polys ps = (ftrs,data)"
  assumes "sgas =  find_sgas (map (map_poly of_rat) ftrs)"
  assumes sgas_set: "set (sgas) = consistent_sign_vectors ftrs UNIV"
  shows "set (map (undo_factorize_polys data) sgas) = consistent_sign_vectors ps UNIV"
proof -
  have h: "\<forall>x. undo_factorize_polys data (sign_vec ftrs x) = sign_vec ps x" 
    using factorize_polys_undo_factorize_polys
    by (simp add: assms(1)) 
  have h1: "\<forall>x. sign_vec ps x \<in> set (map (undo_factorize_polys data) sgas)"
    using sgas_set
    by (metis UNIV_I consistent_sign_vectors_def h image_eqI image_set) 
  then have subset_h: "consistent_sign_vectors ps UNIV \<subseteq> set (map (undo_factorize_polys data) sgas)"
    unfolding consistent_sign_vectors_def by auto
  have supset_h:  "consistent_sign_vectors ps UNIV \<supseteq> set (map (undo_factorize_polys data) sgas)"
  proof - 
    have "\<forall> ele. ele \<in> set (map (undo_factorize_polys data) sgas) \<longrightarrow>
       (\<exists>n < length sgas. ele = (undo_factorize_polys data (nth sgas n)))"
      using index_of_lookup(1) index_of_lookup(2) by fastforce
    then have "\<forall> ele. ele \<in> set (map (undo_factorize_polys data) sgas) \<longrightarrow>
       (\<exists>x. ele = (undo_factorize_polys data (sign_vec ftrs x)))"
      using sgas_set apply (auto)  using consistent_sign_vectors_def by auto 
    then show ?thesis using h
      using consistent_sign_vectors_def by auto
  qed
  show ?thesis using subset_h supset_h
    by blast 
qed

lemma main_step_aux1:
  fixes qs:: "rat poly list"
  assumes empty: "(fst(factorize_polys qs)) = []"
  shows "set (find_consistent_signs qs) =  consistent_sign_vectors qs UNIV"
proof -
  have set_eq: "set (find_consistent_signs qs) = {(map (\<lambda>x. if poly x 0 < 0 then -1 else if poly x 0 = 0 then 0 else 1) qs)}"
    using empty unfolding find_consistent_signs_def apply (auto)
    apply (metis fst_conv) 
    by (metis prod.collapse) 
  have deg_q_prop: "fst(factorize_polys qs) = [] \<Longrightarrow> (\<forall>q \<in>set(qs). degree q = 0)"
    apply (rule ccontr)
  proof clarsimp
    fix q
    assume *:"fst(factorize_polys qs) = []"
    assume q: "q \<in> set qs" "0 < degree q"
    obtain arb where "factorize_rat_poly_monic q = (arb,[])"
      using * q unfolding factorize_polys_def apply (auto simp add:Let_def)
      by (metis prod.collapse)
    from squarefree_factorization_degree[OF factorize_rat_poly_monic_square_free_factorization[OF this]]
    have "degree q = 0" by auto
    thus False using q by auto
  qed
  have deg_q_cons: "(\<forall>q \<in>set(qs). degree q = 0) \<Longrightarrow> (consistent_sign_vectors qs UNIV =  {(map (\<lambda>x. if poly x 0 < 0 then -1 else if poly x 0 = 0 then 0 else 1) qs)})"
  proof - 
    assume deg_z: "(\<forall>q \<in>set(qs). degree q = 0)"
    then have "\<forall>q \<in>set(qs). \<forall>x y. poly q x = poly q y"
      apply (auto)
      by (meson constant_def constant_degree) 
    then have csv: "consistent_sign_vectors qs UNIV = {sign_vec qs 0}"
      unfolding consistent_sign_vectors_def sign_vec_def apply (auto) 
      apply (metis deg_z degree_0_id of_rat_hom.map_poly_hom_coeff_lift poly_0_coeff_0 poly_const_conv squash_real_of_rat)
      by (metis (mono_tags, lifting) class_semiring.add.one_closed comp_def image_iff list.map_cong0 of_rat_hom.poly_map_poly_0)
    have "sign_vec qs 0 = (map (\<lambda>x. if poly x 0 < 0 then -1 else if poly x 0 = 0 then 0 else 1) qs)"
      unfolding sign_vec_def squash_def by auto
    then show "consistent_sign_vectors qs UNIV =  {(map (\<lambda>x. if poly x 0 < 0 then -1 else if poly x 0 = 0 then 0 else 1) qs)}"
      using csv by auto
  qed
  then show ?thesis
    using deg_q_prop deg_q_cons set_eq
    by (simp add: empty) 
qed

lemma main_step_aux2:
  fixes qs:: "rat poly list"
  assumes lenh: "length (fst(factorize_polys qs)) > 0"
  shows "set (find_consistent_signs qs) =  consistent_sign_vectors qs UNIV"
proof - 
  let ?fs = "fst(factorize_polys qs)"
  let ?data = "snd(factorize_polys qs)"
  let ?sgas = "find_sgas (map (map_poly of_rat) ?fs)"
  have h0: "set (?sgas) = consistent_sign_vectors ?fs UNIV" 
    using lenh same_sign_cond_rationals_reals coprime_factorize by auto
  then have h1: "set (map (undo_factorize_polys ?data) ?sgas) = consistent_sign_vectors qs UNIV"
    using factorize_polys_undo_factorize_polys_set
    by simp
  then show ?thesis using lenh apply (auto)
    apply (smt case_prod_unfold find_consistent_signs_def h1 main_step_aux1) 
     by (simp add: find_consistent_signs_def prod.case_eq_if)
qed

lemma main_step:
  fixes qs:: "rat poly list"
  shows "set (find_consistent_signs qs) =  consistent_sign_vectors qs UNIV"
  using main_step_aux1 main_step_aux2 by auto

subsection "Decision Procedure: Main Lemmas"

lemma decide_univ_lem_helper:
  assumes "(fml_struct,polys) = convert fml"
  shows "(\<forall>x::real. lookup_sem fml_struct (map (\<lambda>p. rpoly p x) polys)) \<longleftrightarrow>
    (decide_universal fml)"
  using universal_lookup_sem main_step unfolding decide_universal_def apply (auto)
  apply (metis assms convert_closed fst_conv snd_conv)
  by (metis (full_types) assms convert_closed fst_conv snd_conv)

lemma decide_exis_lem_helper:
  assumes "(fml_struct,polys) = convert fml"
  shows "(\<exists>x::real. lookup_sem fml_struct (map (\<lambda>p. rpoly p x) polys)) \<longleftrightarrow>
    (decide_existential fml)"
  using existential_lookup_sem main_step unfolding decide_existential_def apply (auto)
  apply (metis assms convert_closed fst_conv snd_conv)
  by (metis (full_types) assms convert_closed fst_conv snd_conv)

theorem decision_procedure:
  shows "(\<forall>x::real. fml_sem fml x) \<longleftrightarrow> (decide_universal fml)"
    "\<exists>x::real. fml_sem fml x \<longleftrightarrow> (decide_existential fml)" 
  using  convert_semantics_lem decide_univ_lem_helper apply (auto)
  apply (simp add: convert_semantics)   
  apply (metis convert_def convert_semantics fst_conv snd_conv)  
  using convert_semantics_lem 
  by (metis convert_def convert_semantics decide_exis_lem_helper fst_conv snd_conv)

end