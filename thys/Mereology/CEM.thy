section \<open> Closed Extensional Mereology \<close>

(*<*)
theory CEM
  imports CM EM
begin
(*>*)

text \<open> Closed extensional mereology combines closed mereology with extensional mereology.\footnote{
See @{cite "varzi_parts_1996"} p. 263 and @{cite "casati_parts_1999"} p. 43.} \<close>  

locale CEM = CM + EM

text \<open> Likewise, closed minimal mereology combines closed mereology with minimal mereology.\footnote{
See @{cite "casati_parts_1999"} p. 43.} \<close>

locale CMM = CM + MM

text \<open> But famously closed minimal mereology and closed extensional mereology are the same theory,
because in closed minimal mereology product closure and weak supplementation entail strong
supplementation.\footnote{See @{cite "simons_parts:_1987"} p. 31 and @{cite "casati_parts_1999"} p. 44.} \<close>

sublocale CMM \<subseteq> CEM
proof
  fix x y
  show strong_supplementation: "\<not> P x y \<Longrightarrow> (\<exists> z. P z x \<and> \<not> O z y)"
  proof -
    assume "\<not> P x y"
    show "\<exists> z. P z x \<and> \<not> O z y"
    proof cases
      assume "O x y"
      with `\<not> P x y` have "\<not> P x y \<and> O x y"..
      hence "PP (x \<otimes> y) x" by (rule nonpart_implies_proper_product)
      hence "\<exists> z. P z x \<and> \<not> O z (x \<otimes> y)" by (rule weak_supplementation)
      then obtain z where z: "P z x \<and> \<not> O z (x \<otimes> y)"..
      hence "\<not> O z y" by (rule disjoint_from_second_factor)
      moreover from z have "P z x"..
      hence  "P z x \<and> \<not> O z y"
        using `\<not> O z y`..
      thus "\<exists> z. P z x \<and> \<not> O z y"..
    next
      assume "\<not> O x y"
      with part_reflexivity have "P x x \<and> \<not> O x y"..
      thus "(\<exists> z. P z x \<and> \<not> O z y)"..
    qed
  qed
qed

sublocale CEM \<subseteq> CMM..

subsection \<open> Sums \<close>

context CEM
begin

lemma sum_intro:
   "(\<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y)) \<Longrightarrow> x \<oplus> y = z"
proof -
  assume sum: "\<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y)"
  hence "(THE v. \<forall> w. O w v \<longleftrightarrow> (O w x \<or> O w y)) = z"
  proof (rule the_equality)
    fix a
    assume a: "\<forall> w. O w a \<longleftrightarrow> (O w x \<or> O w y)"
    have "\<forall> w. O w a \<longleftrightarrow> O w z"
    proof
      fix w
      from sum have "O w z \<longleftrightarrow> (O w x \<or> O w y)"..
      moreover from a have "O w a \<longleftrightarrow> (O w x \<or> O w y)"..
      ultimately show "O w a \<longleftrightarrow> O w z" by (rule ssubst)
      qed
      with overlap_extensionality show "a = z"..
  qed
  thus "x \<oplus> y = z"
    using sum_eq by (rule subst)
qed

lemma sum_idempotence: "x \<oplus> x = x"
proof -
  have "\<forall> w. O w x \<longleftrightarrow> (O w x \<or> O w x)"
  proof
    fix w
    show "O w x \<longleftrightarrow> (O w x \<or> O w x)"
    proof (rule iffI)
      assume "O w x"
      thus "O w x \<or> O w x"..
    next
      assume "O w x \<or> O w x"
      thus "O w x" by (rule disjE)
    qed
  qed
  thus "x \<oplus> x = x" by (rule sum_intro)
qed

lemma part_sum_identity: "P y x \<Longrightarrow> x \<oplus> y = x"
proof -
  assume "P y x"
  have "\<forall> w. O w x \<longleftrightarrow> (O w x \<or> O w y)"
  proof
    fix w
    show "O w x \<longleftrightarrow> (O w x \<or> O w y)"
    proof
      assume "O w x"
      thus "O w x \<or> O w y"..
    next
      assume "O w x \<or> O w y"
      thus "O w x"
      proof
        assume "O w x"
        thus "O w x".
      next
        assume "O w y"
        with `P y x` show "O w x" 
          by (rule overlap_monotonicity)
      qed
    qed
  qed
  thus "x \<oplus> y = x" by (rule sum_intro)
qed

lemma sum_character: "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)"
proof -
  from sum_closure have "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))".
  then obtain a where a: "\<forall> w. O w a \<longleftrightarrow> (O w x \<or> O w y)"..
  hence "x \<oplus> y = a" by (rule sum_intro)
  thus "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)"
    using a by (rule ssubst)
qed

lemma sum_overlap: "O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)" 
  using sum_character..

lemma sum_part_character:  
  "P w (x \<oplus> y) \<longleftrightarrow> (\<forall> v. O v w \<longrightarrow> O v x \<or> O v y)"
proof
  assume "P w (x \<oplus> y)"
  show "\<forall> v. O v w \<longrightarrow> O v x \<or> O v y"
  proof
    fix v
    show "O v w \<longrightarrow> O v x \<or> O v y"
    proof
      assume "O v w"    
      with `P w (x \<oplus> y)` have "O v (x \<oplus> y)"
        by (rule overlap_monotonicity)
      with sum_overlap show "O v x \<or> O v y"..
    qed
  qed
next
  assume right: "\<forall> v. O v w \<longrightarrow> O v x \<or> O v y"
  have "\<forall> v. O v w \<longrightarrow> O v (x \<oplus> y)"
  proof
    fix v
    from right have "O v w \<longrightarrow> O v x \<or> O v y"..
    with sum_overlap show "O v w \<longrightarrow> O v (x \<oplus> y)" 
      by (rule ssubst)
  qed
  with part_overlap_eq show "P w (x \<oplus> y)"..
qed

lemma sum_commutativity: "x \<oplus> y = y \<oplus> x"
proof -
  from sum_character have "\<forall> w. O w (y \<oplus> x) \<longleftrightarrow> O w y \<or> O w x".
  hence "\<forall> w. O w (y \<oplus> x) \<longleftrightarrow> O w x \<or> O w y" by metis
  thus "x \<oplus> y = y \<oplus> x" by (rule sum_intro)
qed

lemma first_summand_overlap: "O z x \<Longrightarrow> O z (x \<oplus> y)"
proof -
  assume "O z x"
  hence "O z x \<or> O z y"..
  with sum_overlap show "O z (x \<oplus> y)"..
qed

lemma first_summand_disjointness: "\<not> O z (x \<oplus> y) \<Longrightarrow> \<not> O z x"
proof -
  assume "\<not> O z (x \<oplus> y)"
  show "\<not> O z x"
  proof
    assume "O z x"
    hence "O z (x \<oplus> y)" by (rule first_summand_overlap)
    with `\<not> O z (x \<oplus> y)` show "False"..
  qed
qed

lemma first_summand_in_sum: "P x (x \<oplus> y)"
proof -
  have "\<forall> w. O w x \<longrightarrow> O w (x \<oplus> y)"
  proof
    fix w
    show "O w x \<longrightarrow> O w (x \<oplus> y)"
    proof
      assume "O w x"
      thus "O w (x \<oplus> y)"
        by (rule first_summand_overlap)
    qed
  qed
  with part_overlap_eq show "P x (x \<oplus> y)"..
qed

lemma common_first_summand: "P x (x \<oplus> y) \<and> P x (x \<oplus> z)"
proof
  from first_summand_in_sum show "P x (x \<oplus> y)".
  from first_summand_in_sum show "P x (x \<oplus> z)".
qed

lemma common_first_summand_overlap: "O (x \<oplus> y) (x \<oplus> z)"
proof -
  from first_summand_in_sum have "P x (x \<oplus> y)".
  moreover from first_summand_in_sum have "P x (x \<oplus> z)".
  ultimately have "P x (x \<oplus> y) \<and> P x (x \<oplus> z)"..
  hence "\<exists> v. P v (x \<oplus> y) \<and> P v (x \<oplus> z)"..
  with overlap_eq show ?thesis..
qed

lemma second_summand_overlap: "O z y \<Longrightarrow> O z (x \<oplus> y)"
proof -
  assume "O z y"
  from sum_character have "O z (x \<oplus> y) \<longleftrightarrow> (O z x \<or> O z y)"..
  moreover from `O z y` have "O z x \<or> O z y"..
  ultimately show "O z (x \<oplus> y)"..
qed

lemma second_summand_disjointness: "\<not> O z (x \<oplus> y) \<Longrightarrow> \<not> O z y"
proof -
  assume "\<not> O z (x \<oplus> y)"
  show "\<not> O z y"
  proof
    assume  "O z y"
    hence "O z (x \<oplus> y)" 
      by (rule second_summand_overlap)
    with `\<not> O z (x \<oplus> y)` show False..
  qed
qed

lemma second_summand_in_sum: "P y (x \<oplus> y)"
proof -
  have "\<forall> w. O w y \<longrightarrow> O w (x \<oplus> y)"
  proof
    fix w
    show "O w y \<longrightarrow> O w (x \<oplus> y)"
    proof
      assume "O w y"
      thus "O w (x \<oplus> y)"
        by (rule second_summand_overlap)
    qed
  qed
  with part_overlap_eq show "P y (x \<oplus> y)"..
qed

lemma second_summands_in_sums: "P y (x \<oplus> y) \<and> P v (z \<oplus> v)"
proof
  show "P y (x \<oplus> y)" using second_summand_in_sum.
  show "P v (z \<oplus> v)" using second_summand_in_sum.
qed

lemma disjoint_from_sum: "\<not> O z (x \<oplus> y) \<longleftrightarrow> \<not> O z x \<and> \<not> O z y"
proof -
  from sum_character have "O z (x \<oplus> y) \<longleftrightarrow> (O z x \<or> O z y)"..
  thus ?thesis by simp
qed

lemma summands_part_implies_sum_part: 
  "P x z \<and> P y z \<Longrightarrow> P (x \<oplus> y) z"
proof -
  assume antecedent: "P x z \<and> P y z"
  have "\<forall> w. O w (x \<oplus> y) \<longrightarrow> O w z"
  proof
    fix w
    have w: "O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)"
      using sum_character..
    show "O w (x \<oplus> y) \<longrightarrow> O w z"
    proof
      assume "O w (x \<oplus> y)"
      with w have "O w x \<or> O w y"..
      thus "O w z"
      proof
        from antecedent have "P x z"..
        moreover assume "O w x"
        ultimately show "O w z"
          by (rule overlap_monotonicity)
      next
        from antecedent have "P y z"..
        moreover assume "O w y"
        ultimately show "O w z"
          by (rule overlap_monotonicity)
      qed
    qed
  qed
  with part_overlap_eq show "P (x \<oplus> y) z"..
qed

lemma sum_part_implies_summands_part: 
  "P (x \<oplus> y) z \<Longrightarrow> P x z \<and> P y z"
proof -
  assume antecedent: "P (x \<oplus> y) z"
  show "P x z \<and> P y z"
  proof
    from first_summand_in_sum show "P x z"
      using antecedent by (rule part_transitivity)
  next
    from second_summand_in_sum show "P y z"
      using antecedent by (rule part_transitivity)
  qed
qed

lemma in_second_summand: "P z (x \<oplus> y) \<and> \<not> O z x \<Longrightarrow> P z y"
proof -
  assume antecedent: "P z (x \<oplus> y) \<and> \<not> O z x"
  hence "P z (x \<oplus> y)"..
  show "P z y"
  proof (rule ccontr)
    assume "\<not> P z y"
    hence "\<exists> v. P v z \<and> \<not> O v y"
      by (rule strong_supplementation)
    then obtain v where v: "P v z \<and> \<not> O v y"..
    hence "\<not> O v y"..
    from v have "P v z"..
    hence "P v (x \<oplus> y)"
      using `P z (x \<oplus> y)` by (rule part_transitivity)
    hence "O v (x \<oplus> y)" by (rule part_implies_overlap)
    from sum_character have "O v (x \<oplus> y) \<longleftrightarrow> O v x \<or> O v y"..
    hence "O v x \<or> O v y" using `O v (x \<oplus> y)`..
    thus "False"
    proof (rule disjE)
      from antecedent have "\<not> O z x"..
      moreover assume "O v x"
      hence "O x v" by (rule overlap_symmetry)
      with `P v z` have "O x z"
        by (rule overlap_monotonicity)
      hence "O z x" by (rule overlap_symmetry)
      ultimately show "False"..
    next
      assume "O v y"
      with `\<not> O v y` show "False"..
    qed
  qed
qed

lemma disjoint_second_summands:
  "P v (x \<oplus> y) \<and> P v (x \<oplus> z) \<Longrightarrow> \<not> O y z \<Longrightarrow> P v x"
proof -
  assume antecedent: "P v (x \<oplus> y) \<and> P v (x \<oplus> z)"
  hence "P v (x \<oplus> z)"..
  assume "\<not> O y z"
  show "P v x"
  proof (rule ccontr)
    assume "\<not> P v x"
    hence "\<exists> w. P w v \<and> \<not> O w x" by (rule strong_supplementation)
    then obtain w where w: "P w v \<and> \<not> O w x"..
    hence "\<not> O w x"..
    from w have "P w v"..
    moreover from antecedent have "P v (x \<oplus> z)"..
    ultimately have "P w (x \<oplus> z)" by (rule part_transitivity)
    hence "P w (x \<oplus> z) \<and> \<not> O w x" using `\<not> O w x`.. 
    hence "P w z" by (rule in_second_summand)
    from antecedent have "P v (x \<oplus> y)"..
    with `P w v` have "P w (x \<oplus> y)" by (rule part_transitivity)
    hence "P w (x \<oplus> y) \<and> \<not> O w x" using `\<not> O w x`..
    hence "P w y" by (rule in_second_summand)
    hence "P w y \<and> P w z" using `P w z`..
    hence "\<exists> w. P w y \<and> P w z"..
    with overlap_eq have "O y z"..
    with `\<not> O y z` show "False"..
  qed
qed

lemma right_associated_sum:
  "O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> O w x \<or> (O w y \<or> O w z)"
proof -
  from sum_character have "O w (y \<oplus> z) \<longleftrightarrow> O w y \<or> O w z"..
  moreover from sum_character have
    "O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> (O w x \<or> O w (y \<oplus> z))"..
  ultimately show ?thesis
    by (rule subst)
qed

lemma left_associated_sum: 
  "O w ((x \<oplus> y) \<oplus> z) \<longleftrightarrow> (O w x \<or> O w y) \<or> O w z"
proof -
  from sum_character have "O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)"..
  moreover from sum_character have
    "O w ((x \<oplus> y) \<oplus> z) \<longleftrightarrow> O w (x \<oplus> y) \<or> O w z"..
  ultimately show ?thesis
    by (rule subst)
qed

theorem sum_associativity: "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
proof -
  have  "\<forall> w. O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> O w ((x \<oplus> y) \<oplus> z)"
  proof
    fix w
    have "O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> (O w x \<or> O w y) \<or> O w z"
      using right_associated_sum by simp
    with left_associated_sum show 
      "O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> O w ((x \<oplus> y) \<oplus> z)" by (rule ssubst)
  qed
  with overlap_extensionality show "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"..
qed

subsection \<open> Distributivity \<close>

text \<open> The proofs in this section are adapted from @{cite "pietruszczak_metamereology_2018"} pp. 102-4.  \<close>

lemma common_summand_in_product: "P x ((x \<oplus> y) \<otimes> (x \<oplus> z))"
    using common_first_summand by (rule common_part_in_product)

lemma product_in_first_summand:
  "\<not> O y z \<Longrightarrow> P ((x \<oplus> y) \<otimes> (x \<oplus> z)) x"
proof -
  assume "\<not> O y z"
  have "\<forall> v. P v ((x \<oplus> y) \<otimes> (x \<oplus> z)) \<longrightarrow> P v x"
  proof
    fix v
    show "P v ((x \<oplus> y) \<otimes> (x \<oplus> z)) \<longrightarrow> P v x"
    proof
      assume "P v ((x \<oplus> y) \<otimes> (x \<oplus> z))"
      with common_first_summand_overlap have 
        "P v (x \<oplus> y) \<and> P v (x \<oplus> z)" by (rule product_part_in_factors)
      thus "P v x" using `\<not> O y z`  by (rule disjoint_second_summands)
    qed
  qed
  hence "P ((x \<oplus> y) \<otimes> (x \<oplus> z)) ((x \<oplus> y) \<otimes> (x \<oplus> z)) \<longrightarrow> 
    P ((x \<oplus> y) \<otimes> (x \<oplus> z)) x"..
  thus "P ((x \<oplus> y) \<otimes> (x \<oplus> z)) x" using part_reflexivity..
qed
  
lemma product_is_first_summand: 
  "\<not> O y z \<Longrightarrow> (x \<oplus> y) \<otimes> (x \<oplus> z) = x"
proof -
  assume "\<not> O y z"
  hence "P ((x \<oplus> y) \<otimes> (x \<oplus> z)) x"
    by (rule product_in_first_summand)
  thus "(x \<oplus> y) \<otimes> (x \<oplus> z) = x"
    using common_summand_in_product
    by (rule part_antisymmetry)
qed

lemma sum_over_product_left: "O y z \<Longrightarrow> P (x \<oplus> (y \<otimes> z)) ((x \<oplus> y) \<otimes> (x \<oplus> z))"
proof -
  assume "O y z"
  hence "P (y \<otimes> z) ((x \<oplus> y) \<otimes> (x \<oplus> z))" using second_summands_in_sums
    by (rule part_product_in_whole_product)
  with common_summand_in_product have
    "P x ((x \<oplus> y) \<otimes> (x \<oplus> z)) \<and> P (y \<otimes> z) ((x \<oplus> y) \<otimes> (x \<oplus> z))"..
  thus "P (x \<oplus> (y \<otimes> z)) ((x \<oplus> y) \<otimes> (x \<oplus> z))"
    by (rule summands_part_implies_sum_part)
qed

lemma sum_over_product_right: 
  "O y z \<Longrightarrow> P ((x \<oplus> y) \<otimes> (x \<oplus> z)) (x \<oplus> (y \<otimes> z))"
proof -
  assume "O y z"
  show "P ((x \<oplus> y) \<otimes> (x \<oplus> z)) (x \<oplus> (y \<otimes> z))"
  proof (rule ccontr)
    assume "\<not> P ((x \<oplus> y) \<otimes> (x \<oplus> z)) (x \<oplus> (y \<otimes> z))"
    hence "\<exists> v. P v ((x \<oplus> y) \<otimes> (x \<oplus> z)) \<and> \<not> O v (x \<oplus> (y \<otimes> z))"
      by (rule strong_supplementation)
    then obtain v where v: 
      "P v ((x \<oplus> y) \<otimes> (x \<oplus> z)) \<and> \<not> O v (x \<oplus> (y \<otimes> z))"..
    hence " \<not> O v (x \<oplus> (y \<otimes> z))"..
    with disjoint_from_sum have vd: "\<not> O v x \<and> \<not> O v (y \<otimes> z)"..
    hence "\<not> O v (y \<otimes> z)"..
    from vd have "\<not> O v x"..
    from v have "P v ((x \<oplus> y) \<otimes> (x \<oplus> z))"..
    with common_first_summand_overlap have 
      vs: "P v (x \<oplus> y) \<and> P v (x \<oplus> z)" by (rule product_part_in_factors)
    hence "P v (x \<oplus> y)"..
    hence "P v (x \<oplus> y) \<and> \<not> O v x" using `\<not> O v x`..
    hence "P v y" by (rule in_second_summand)
    moreover from vs have "P v (x \<oplus> z)"..
    hence "P v (x \<oplus> z) \<and> \<not> O v x" using `\<not> O v x`..
    hence "P v z" by (rule in_second_summand)
    ultimately have "P v y \<and> P v z"..    
    hence "P v (y \<otimes> z)" by (rule common_part_in_product)
    hence "O v (y \<otimes> z)" by (rule part_implies_overlap)
    with `\<not> O v (y \<otimes> z)` show "False"..
  qed
qed

text \<open> Sums distribute over products. \<close>

theorem sum_over_product: 
    "O y z \<Longrightarrow> x \<oplus> (y \<otimes> z) = (x \<oplus> y) \<otimes> (x \<oplus> z)"
proof -
  assume "O y z"
  hence "P (x \<oplus> (y \<otimes> z)) ((x \<oplus> y) \<otimes> (x \<oplus> z))"
    by (rule sum_over_product_left)
  moreover have "P ((x \<oplus> y) \<otimes> (x \<oplus> z)) (x \<oplus> (y \<otimes> z))"
    using `O y z` by (rule sum_over_product_right)
  ultimately show "x \<oplus> (y \<otimes> z) = (x \<oplus> y) \<otimes> (x \<oplus> z)"
    by (rule part_antisymmetry)
qed

lemma product_in_factor_by_sum:
  "O x y \<Longrightarrow> P (x \<otimes> y) (x \<otimes> (y \<oplus> z))"
proof -
  assume "O x y"
  hence "P (x \<otimes> y) x" 
    by (rule product_in_first_factor)
  moreover have "P (x \<otimes> y) y" 
    using `O x y` by (rule product_in_second_factor)
  hence "P (x \<otimes> y) (y \<oplus> z)" 
    using first_summand_in_sum by (rule part_transitivity)
  with `P (x \<otimes> y) x` have "P (x \<otimes> y) x \<and> P (x \<otimes> y) (y \<oplus> z)"..
  thus "P (x \<otimes> y) (x \<otimes> (y \<oplus> z))" 
    by (rule common_part_in_product)
qed

lemma product_of_first_summand:
  "O x y \<Longrightarrow> \<not> O x z \<Longrightarrow> P (x \<otimes> (y \<oplus> z)) (x \<otimes> y)"
proof -
  assume "O x y"
  hence "O x (y \<oplus> z)"
    by (rule first_summand_overlap)
  assume "\<not> O x z"
  show "P (x \<otimes> (y \<oplus> z)) (x \<otimes> y)"
  proof (rule ccontr)
    assume "\<not> P (x \<otimes> (y \<oplus> z)) (x \<otimes> y)"
    hence "\<exists> v. P v (x \<otimes> (y \<oplus> z)) \<and> \<not> O v (x \<otimes> y)"
      by (rule strong_supplementation)
    then obtain v where v: "P v (x \<otimes> (y \<oplus> z)) \<and> \<not> O v (x \<otimes> y)"..
    hence "P v (x \<otimes> (y \<oplus> z))"..
    with `O x (y \<oplus> z)` have "P v x \<and> P v (y \<oplus> z)"
      by (rule product_part_in_factors)
    hence "P v x"..
    moreover from v have "\<not> O v (x \<otimes> y)"..
    ultimately have  "P v x \<and> \<not> O v (x \<otimes> y)"..
    hence "\<not> O v y" by (rule disjoint_from_second_factor)
    from `P v x \<and> P v (y \<oplus> z)` have "P v (y \<oplus> z)"..
    hence "P v (y \<oplus> z) \<and> \<not> O v y" using `\<not> O v y`..
    hence "P v z" by (rule in_second_summand)
    with `P v x` have "P v x \<and> P v z"..
    hence "\<exists> v. P v x \<and> P v z"..
    with overlap_eq have "O x z"..
    with `\<not> O x z` show "False"..
  qed
qed

theorem disjoint_product_over_sum: 
  "O x y \<Longrightarrow> \<not> O x z \<Longrightarrow> x \<otimes> (y \<oplus> z) = x \<otimes> y"
proof -
  assume "O x y"
  moreover assume "\<not> O x z"
  ultimately have "P (x \<otimes> (y \<oplus> z)) (x \<otimes> y)" 
    by (rule product_of_first_summand)
  moreover have "P (x \<otimes> y)(x \<otimes> (y \<oplus> z))"
    using `O x y` by (rule product_in_factor_by_sum)
  ultimately show "x \<otimes> (y \<oplus> z) = x \<otimes> y"
    by (rule part_antisymmetry)
qed

lemma product_over_sum_left:
  "O x y \<and> O x z \<Longrightarrow> P (x \<otimes> (y \<oplus> z))((x \<otimes> y) \<oplus> (x \<otimes> z))"
proof -
  assume "O x y \<and> O x z"
  hence "O x y"..
  hence "O x (y \<oplus> z)" by (rule first_summand_overlap)
  show "P (x \<otimes> (y \<oplus> z))((x \<otimes> y) \<oplus> (x \<otimes> z))"
  proof (rule ccontr)
    assume "\<not> P (x \<otimes> (y \<oplus> z))((x \<otimes> y) \<oplus> (x \<otimes> z))"
    hence "\<exists> v. P v (x \<otimes> (y \<oplus> z)) \<and> \<not> O v ((x \<otimes> y) \<oplus> (x \<otimes> z))"
      by (rule strong_supplementation)
    then obtain v where v: 
      "P v (x \<otimes> (y \<oplus> z)) \<and> \<not> O v ((x \<otimes> y) \<oplus> (x \<otimes> z))"..
    hence "\<not> O v ((x \<otimes> y) \<oplus> (x \<otimes> z))"..
    with disjoint_from_sum have oxyz:
      "\<not> O v (x \<otimes> y) \<and> \<not> O v (x \<otimes> z)"..
    from v have "P v (x \<otimes> (y \<oplus> z))"..
    with `O x (y \<oplus> z)` have pxyz: "P v x \<and> P v (y \<oplus> z)"
      by (rule product_part_in_factors)
    hence "P v x"..
    moreover from oxyz have "\<not> O v (x \<otimes> y)"..
    ultimately have "P v x \<and> \<not> O v (x \<otimes> y)"..
    hence "\<not> O v y" by (rule disjoint_from_second_factor)
    from oxyz have "\<not> O v (x \<otimes> z)"..
    with `P v x` have "P v x \<and> \<not> O v (x \<otimes> z)"..
    hence "\<not> O v z" by (rule disjoint_from_second_factor)
    with `\<not> O v y` have "\<not> O v y \<and> \<not> O v z"..
    with disjoint_from_sum have "\<not> O v (y \<oplus> z)"..
    from pxyz have "P v (y \<oplus> z)"..
    hence "O v (y \<oplus> z)" by (rule part_implies_overlap)
    with `\<not> O v (y \<oplus> z)` show "False"..
  qed
qed

lemma product_over_sum_right:
  "O x y \<and> O x z \<Longrightarrow> P((x \<otimes> y) \<oplus> (x \<otimes> z))(x \<otimes> (y \<oplus> z))" 
proof -
  assume antecedent: "O x y \<and> O x z"
  have "P (x \<otimes> y) (x \<otimes> (y \<oplus> z)) \<and> P (x \<otimes> z) (x \<otimes> (y \<oplus> z))"
  proof
    from antecedent have "O x y"..
    thus "P (x \<otimes> y) (x \<otimes> (y \<oplus> z))"
      by (rule  product_in_factor_by_sum)
  next
    from antecedent have "O x z"..
    hence "P (x \<otimes> z) (x \<otimes> (z \<oplus> y))"
      by (rule  product_in_factor_by_sum)
    with sum_commutativity show "P (x \<otimes> z) (x \<otimes> (y \<oplus> z))"
      by (rule subst)
  qed
  thus "P((x \<otimes> y) \<oplus> (x \<otimes> z))(x \<otimes> (y \<oplus> z))"
    by (rule summands_part_implies_sum_part)
qed

theorem product_over_sum: 
  "O x y \<and> O x z \<Longrightarrow> x \<otimes> (y \<oplus> z) = (x \<otimes> y) \<oplus> (x \<otimes> z)"
proof -
  assume antecedent: "O x y \<and> O x z"
  hence "P (x \<otimes> (y \<oplus> z))((x \<otimes> y) \<oplus> (x \<otimes> z))"
    by (rule product_over_sum_left)
  moreover have "P((x \<otimes> y) \<oplus> (x \<otimes> z))(x \<otimes> (y \<oplus> z))"
    using antecedent by (rule product_over_sum_right)
  ultimately show "x \<otimes> (y \<oplus> z) = (x \<otimes> y) \<oplus> (x \<otimes> z)"
    by (rule part_antisymmetry)
qed

lemma joint_identical_sums: 
  "v \<oplus> w = x \<oplus> y \<Longrightarrow> O x v \<and> O x w \<Longrightarrow> ((x \<otimes> v) \<oplus> (x \<otimes> w)) = x"
proof -
  assume "v \<oplus> w = x \<oplus> y"
  moreover assume "O x v \<and> O x w"
  hence "x \<otimes> (v \<oplus> w) = x \<otimes> v \<oplus> x \<otimes> w"
    by (rule product_over_sum)
  ultimately have "x \<otimes> (x \<oplus> y) = x \<otimes> v \<oplus> x \<otimes> w" by (rule subst)
  moreover have "(x \<otimes> (x \<oplus> y)) = x" using first_summand_in_sum
    by (rule part_product_identity)
  ultimately show "((x \<otimes> v) \<oplus> (x \<otimes> w)) = x" by (rule subst)
qed

lemma disjoint_identical_sums: 
  "v \<oplus> w = x \<oplus> y \<Longrightarrow> \<not> O y v \<and> \<not> O w x \<Longrightarrow> x = v \<and> y = w"
proof -
  assume identical: "v \<oplus> w = x \<oplus> y"
  assume disjoint: "\<not> O y v \<and> \<not> O w x"
  show "x = v \<and> y = w"
  proof
    from disjoint have "\<not> O y v"..
    hence "(x \<oplus> y) \<otimes> (x \<oplus> v) = x"
      by (rule product_is_first_summand)
    with identical have "(v \<oplus> w) \<otimes> (x \<oplus> v) = x"
      by (rule ssubst)
    moreover from disjoint have "\<not> O w x"..
    hence "(v \<oplus> w) \<otimes> (v \<oplus> x) = v"
      by (rule product_is_first_summand)
    with sum_commutativity have "(v \<oplus> w) \<otimes> (x \<oplus> v) = v" 
      by (rule subst)
    ultimately show "x = v" by (rule subst)
  next
    from disjoint have "\<not> O w x"..
    hence "(y \<oplus> w) \<otimes> (y \<oplus> x) = y"
      by (rule product_is_first_summand)
    moreover from disjoint have "\<not> O y v"..
    hence "(w \<oplus> y) \<otimes> (w \<oplus> v) = w"
      by (rule product_is_first_summand)
    with sum_commutativity have "(w \<oplus> y) \<otimes> (v \<oplus> w) = w" 
      by (rule subst)
    with identical have "(w \<oplus> y) \<otimes> (x \<oplus> y) = w" 
      by (rule subst)
    with sum_commutativity have "(w \<oplus> y) \<otimes> (y \<oplus> x) = w" 
      by (rule subst)
    with sum_commutativity have "(y \<oplus> w) \<otimes> (y \<oplus> x) = w" 
      by (rule subst)
    ultimately show "y = w" 
      by (rule subst)
  qed
qed

end

subsection \<open> Differences \<close>

locale CEMD = CEM + CMD
begin

lemma plus_minus: "PP y x \<Longrightarrow> y \<oplus> (x \<ominus> y) = x"
proof -
  assume "PP y x"
  hence "\<exists> z. P z x \<and> \<not> O z y" by (rule weak_supplementation)
  hence xmy:"\<forall> w. P w (x \<ominus> y) \<longleftrightarrow> (P w x \<and> \<not> O w y)"
    by (rule difference_character)
  have "\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w (x \<ominus> y))"
  proof
    fix w
    from xmy have w: "P w (x \<ominus> y) \<longleftrightarrow> (P w x \<and> \<not> O w y)"..
    show "O w x \<longleftrightarrow> (O w y \<or> O w (x \<ominus> y))"
    proof
      assume "O w x"
      with overlap_eq have "\<exists> v. P v w \<and> P v x"..
      then obtain v where v: "P v w \<and> P v x"..
      hence "P v w"..
      from v have "P v x"..
      show "O w y \<or> O w (x \<ominus> y)"
      proof cases
        assume "O v y"
        hence "O y v" by (rule overlap_symmetry)
        with `P v w` have "O y w" by (rule overlap_monotonicity)
        hence "O w y" by (rule overlap_symmetry)
        thus "O w y \<or> O w (x \<ominus> y)"..
      next
        from xmy have "P v (x \<ominus> y) \<longleftrightarrow> (P v x \<and> \<not> O v y)"..
        moreover assume "\<not> O v y"
        with `P v x` have  "P v x \<and> \<not> O v y"..
        ultimately have "P v (x \<ominus> y)"..
        with `P v w` have "P v w \<and> P v (x \<ominus> y)"..
        hence "\<exists> v. P v w \<and> P v (x \<ominus> y)"..
        with overlap_eq have "O w (x \<ominus> y)"..
        thus "O w y \<or> O w (x \<ominus> y)"..
      qed
    next
      assume "O w y \<or> O w (x \<ominus> y)"
      thus "O w x"
      proof
        from `PP y x` have "P y x"
          by (rule proper_implies_part)
        moreover assume "O w y"
        ultimately show "O w x"
          by (rule overlap_monotonicity)
      next
        assume "O w (x \<ominus> y)"
        with overlap_eq have "\<exists> v. P v w \<and> P v (x \<ominus> y)"..
        then obtain v where v: "P v w \<and> P v (x \<ominus> y)"..
        hence "P v w"..
        from xmy have "P v (x \<ominus> y) \<longleftrightarrow> (P v x \<and> \<not> O v y)"..
        moreover from v have "P v (x \<ominus> y)"..
        ultimately have "P v x \<and> \<not> O v y"..
        hence "P v x"..
        with `P v w` have "P v w \<and> P v x"..
        hence "\<exists> v. P v w \<and> P v x"..
        with overlap_eq show "O w x"..
      qed
    qed
  qed
  thus "y \<oplus> (x \<ominus> y) = x"
    by (rule sum_intro)
qed

end

subsection \<open> The Universe \<close>

locale CEMU = CEM + CMU
begin

lemma something_disjoint: "x \<noteq> u \<Longrightarrow> (\<exists> v. \<not> O v x)"
proof -
  assume "x \<noteq> u"
  with universe_character have "P x u \<and> x \<noteq> u"..
  with nip_eq have "PP x u"..
  hence "\<exists> v. P v u \<and> \<not> O v x"
    by (rule weak_supplementation)
  then obtain v where "P v u \<and> \<not> O v x"..
  hence "\<not> O v x"..
  thus "\<exists> v. \<not> O v x"..
qed

lemma overlaps_universe: "O x u"
proof -
  from universe_character have "P x u".
  thus "O x u" by (rule part_implies_overlap)
qed

lemma universe_absorbing: "x \<oplus> u = u"
proof -
  from universe_character have "P (x \<oplus> u) u".
  thus "x \<oplus> u = u" using second_summand_in_sum
    by (rule part_antisymmetry)
qed

lemma second_summand_not_universe: "x \<oplus> y \<noteq> u \<Longrightarrow> y \<noteq> u"
proof -
  assume antecedent: "x \<oplus> y \<noteq> u"
  show "y \<noteq> u"
  proof
    assume "y = u"
    hence "x \<oplus> u \<noteq> u" using antecedent by (rule subst)
    thus "False" using universe_absorbing..
  qed
qed

lemma first_summand_not_universe: "x \<oplus> y \<noteq> u \<Longrightarrow> x \<noteq> u"
proof -
  assume "x \<oplus> y \<noteq> u"
  with sum_commutativity have "y \<oplus> x \<noteq> u" by (rule subst)
  thus "x \<noteq> u" by (rule second_summand_not_universe)
qed

end

subsection \<open> Complements \<close>

locale CEMC = CEM + CMC + 
  assumes universe_eq: "u = (THE x. \<forall> y. P y x)"
begin

lemma complement_sum_character: "\<forall> y. P y (x \<oplus> (\<midarrow>x))"
proof
  fix y
  have "\<forall> v. O v y \<longrightarrow> O v x \<or> O v (\<midarrow>x)"
  proof
    fix v
    show "O v y \<longrightarrow> O v x \<or> O v (\<midarrow>x)"
    proof
      assume "O v y"
      show "O v x \<or> O v (\<midarrow>x)"
        using or_complement_overlap..
    qed
  qed
  with sum_part_character show "P y (x \<oplus> (\<midarrow>x))"..
qed

lemma universe_closure: "\<exists> x. \<forall> y. P y x"
  using complement_sum_character by (rule exI)

end

sublocale CEMC \<subseteq> CEMU
proof
  show "u = (THE z. \<forall>w. P w z)" using universe_eq.
  show "\<exists> x. \<forall> y. P y x" using universe_closure.
qed

sublocale CEMC \<subseteq> CEMD
proof
qed

context CEMC
begin

corollary universe_is_complement_sum: "u = x \<oplus> (\<midarrow>x)"
  using complement_sum_character by (rule universe_intro)

lemma strong_complement_character: 
  "x \<noteq> u \<Longrightarrow> (\<forall> v. P v (\<midarrow>x) \<longleftrightarrow> \<not> O v x)"
proof -
  assume "x \<noteq> u"
  hence "\<exists> v. \<not> O v x" by (rule something_disjoint)
  thus "\<forall> v. P v (\<midarrow>x) \<longleftrightarrow> \<not> O v x" by (rule complement_character)
qed

lemma complement_part_not_part: "x \<noteq> u \<Longrightarrow> P y (\<midarrow>x) \<Longrightarrow> \<not> P y x"
proof -
  assume "x \<noteq> u"
  hence "\<forall> w. P w (\<midarrow>x) \<longleftrightarrow> \<not> O w x"
    by (rule strong_complement_character)
  hence y: "P y (\<midarrow>x) \<longleftrightarrow> \<not> O y x"..
  moreover assume "P y (\<midarrow>x)"
  ultimately have "\<not> O y x"..
  thus "\<not> P y x" 
    by (rule disjoint_implies_not_part)
qed

lemma complement_involution: "x \<noteq> u \<Longrightarrow> x = \<midarrow>(\<midarrow>x)"
proof -
  assume "x \<noteq> u"
  have "\<not> P u x"
  proof
    assume "P u x"
    with universe_character have "x = u"
      by (rule part_antisymmetry)
    with `x \<noteq> u` show "False"..
  qed
  hence "\<exists> v. P v u \<and> \<not> O v x"
    by (rule strong_supplementation)
  then obtain v where v: "P v u \<and> \<not> O v x"..
  hence "\<not> O v x"..
  hence "\<exists> v. \<not> O v x"..
  hence notx: "\<forall> w. P w (\<midarrow>x) \<longleftrightarrow> \<not> O w x"
    by (rule complement_character)
  have "\<midarrow>x \<noteq> u"
  proof
    assume "\<midarrow>x = u"
    hence "\<forall> w. P w u \<longleftrightarrow> \<not> O w x" using notx by (rule subst)
    hence "P x u \<longleftrightarrow> \<not> O x x"..
    hence "\<not> O x x" using universe_character..
    thus "False" using overlap_reflexivity..
  qed  
  have "\<not> P u (\<midarrow>x)"
  proof
    assume "P u (\<midarrow>x)"
    with universe_character have "\<midarrow>x = u"
      by (rule part_antisymmetry)
    with `\<midarrow>x \<noteq> u` show "False"..
  qed
  hence "\<exists> v. P v u \<and> \<not> O v (\<midarrow>x)"
    by (rule strong_supplementation)
  then obtain w where w: "P w u \<and> \<not> O w (\<midarrow>x)"..
  hence "\<not> O w (\<midarrow>x)"..
  hence "\<exists> v. \<not> O v (\<midarrow>x)"..
  hence notnotx: "\<forall> w. P w (\<midarrow>(\<midarrow>x)) \<longleftrightarrow> \<not> O w (\<midarrow>x)"
    by (rule complement_character)
  hence "P x (\<midarrow>(\<midarrow>x)) \<longleftrightarrow> \<not> O x (\<midarrow>x)"..
  moreover have "\<not> O x (\<midarrow>x)"
  proof
    assume "O x (\<midarrow>x)"
    with overlap_eq have "\<exists> s. P s x \<and> P s (\<midarrow>x)"..
    then obtain s where s: "P s x \<and> P s (\<midarrow>x)"..
    hence "P s x"..
    hence "O s x" by (rule part_implies_overlap)
    from notx have "P s (\<midarrow>x) \<longleftrightarrow> \<not> O s x"..
    moreover from s have "P s (\<midarrow>x)"..     
    ultimately have "\<not> O s x"..
    thus "False" using `O s x`..
  qed
  ultimately have "P x (\<midarrow>(\<midarrow>x))"..
  moreover have "P (\<midarrow>(\<midarrow>x)) x"
  proof (rule ccontr)
    assume "\<not> P (\<midarrow>(\<midarrow>x)) x"
    hence "\<exists> s. P s (\<midarrow>(\<midarrow>x)) \<and> \<not> O s x"
      by (rule strong_supplementation)
    then obtain s where s: "P s (\<midarrow>(\<midarrow>x)) \<and> \<not> O s x"..
    hence "\<not> O s x"..
    from notnotx have "P s (\<midarrow>(\<midarrow>x)) \<longleftrightarrow> (\<not> O s (\<midarrow>x))"..
    moreover from s have "P s (\<midarrow>(\<midarrow>x))"..
    ultimately have "\<not> O s (\<midarrow>x)"..
    from or_complement_overlap have "O s x \<or> O s (\<midarrow>x)"..
    thus "False"
    proof
      assume "O s x"
      with `\<not> O s x` show "False"..
    next
      assume "O s (\<midarrow>x)"
      with `\<not> O s (\<midarrow>x )` show "False"..
    qed
  qed 
  ultimately show "x = \<midarrow>(\<midarrow>x)"
    by (rule part_antisymmetry)
qed

lemma part_complement_reversal: "y \<noteq> u \<Longrightarrow> P x y \<Longrightarrow> P (\<midarrow>y) (\<midarrow>x)"
proof - 
  assume "y \<noteq> u"
  hence ny: "\<forall> w. P w (\<midarrow>y) \<longleftrightarrow> \<not> O w y"
    by (rule strong_complement_character)
  assume "P x y"
  have "x \<noteq> u"
  proof
    assume "x = u"
    hence "P u y" using `P x y` by (rule subst)
    with universe_character have "y = u"
      by (rule part_antisymmetry)
    with `y \<noteq> u` show "False"..
  qed
  hence "\<forall> w. P w (\<midarrow>x) \<longleftrightarrow> \<not> O w x"
    by (rule strong_complement_character)
  hence "P (\<midarrow>y) (\<midarrow>x) \<longleftrightarrow> \<not> O (\<midarrow>y) x"..
  moreover have "\<not> O (\<midarrow>y) x"
  proof
    assume "O (\<midarrow>y) x"
    with overlap_eq have "\<exists> v. P v (\<midarrow>y) \<and> P v x"..
    then obtain v where v: "P v (\<midarrow>y) \<and> P v x"..
    hence "P v (\<midarrow>y)"..
    from ny have "P v (\<midarrow>y) \<longleftrightarrow> \<not> O v y"..
    hence "\<not> O v y" using `P v (\<midarrow>y)`..
    moreover from v have "P v x"..
    hence "P v y" using `P x y`
      by (rule part_transitivity)
    hence "O v y" 
      by (rule part_implies_overlap)
    ultimately show "False"..
  qed
  ultimately show "P (\<midarrow>y) (\<midarrow>x)"..
qed

lemma complements_overlap: "x \<oplus> y \<noteq> u \<Longrightarrow> O(\<midarrow>x)(\<midarrow>y)"
proof -
  assume "x \<oplus> y \<noteq> u"
  hence "\<exists> z. \<not> O z (x \<oplus> y)"
    by (rule something_disjoint)
  then obtain z where z:"\<not> O z (x \<oplus> y)"..
  hence "\<not> O z x" by (rule first_summand_disjointness)
  hence "P z (\<midarrow>x)" by (rule complement_part)
  moreover from z have "\<not> O z y" 
    by (rule second_summand_disjointness)
  hence "P z (\<midarrow>y)" by (rule complement_part)
  ultimately show "O(\<midarrow>x)(\<midarrow>y)"
    by (rule overlap_intro)
qed

lemma sum_complement_in_complement_product: 
  "x \<oplus> y \<noteq> u \<Longrightarrow> P(\<midarrow>(x \<oplus> y))(\<midarrow>x \<otimes> \<midarrow>y)"
proof -
  assume "x \<oplus> y \<noteq> u"
  hence "O (\<midarrow>x) (\<midarrow>y)"
    by (rule complements_overlap)
  hence "\<forall> w. P w (\<midarrow>x \<otimes> \<midarrow>y) \<longleftrightarrow> (P w (\<midarrow>x) \<and> P w (\<midarrow>y))"
    by (rule product_character)
  hence "P(\<midarrow>(x \<oplus> y))(\<midarrow>x \<otimes> \<midarrow>y)\<longleftrightarrow>(P(\<midarrow>(x \<oplus> y))(\<midarrow>x) \<and> P(\<midarrow>(x \<oplus> y))(\<midarrow>y))"..
  moreover have "P (\<midarrow>(x \<oplus> y))(\<midarrow>x) \<and> P (\<midarrow>(x \<oplus> y))(\<midarrow>y)"
  proof
    show "P (\<midarrow>(x \<oplus> y))(\<midarrow>x)" using `x \<oplus> y \<noteq> u` first_summand_in_sum
      by (rule part_complement_reversal)
  next
    show  "P (\<midarrow>(x \<oplus> y))(\<midarrow>y)" using `x \<oplus> y \<noteq> u` second_summand_in_sum
      by (rule part_complement_reversal)
  qed
  ultimately show "P (\<midarrow>(x \<oplus> y))(\<midarrow>x \<otimes> \<midarrow>y)"..
qed

lemma complement_product_in_sum_complement: 
  "x \<oplus> y \<noteq> u \<Longrightarrow> P(\<midarrow>x \<otimes> \<midarrow>y)(\<midarrow>(x \<oplus> y))"
proof -
  assume "x \<oplus> y \<noteq> u"
  hence "\<forall>w. P w (\<midarrow>(x \<oplus> y)) \<longleftrightarrow> \<not> O w (x \<oplus> y)"
    by (rule strong_complement_character)
  hence "P (\<midarrow>x \<otimes> \<midarrow>y) (\<midarrow>(x \<oplus> y)) \<longleftrightarrow> (\<not> O (\<midarrow>x \<otimes> \<midarrow>y) (x \<oplus> y))"..
  moreover have "\<not> O (\<midarrow>x \<otimes> \<midarrow>y) (x \<oplus> y)"
  proof
    have "O(\<midarrow>x)(\<midarrow>y)" using `x \<oplus> y \<noteq> u` by (rule complements_overlap)
    hence p: "\<forall> v. P v ((\<midarrow>x) \<otimes> (\<midarrow>y)) \<longleftrightarrow> (P v (\<midarrow>x) \<and> P v (\<midarrow>y))" 
      by (rule product_character)
    have "O(\<midarrow>x \<otimes> \<midarrow>y)(x \<oplus> y) \<longleftrightarrow> (O(\<midarrow>x \<otimes> \<midarrow>y) x \<or> O(\<midarrow>x \<otimes> \<midarrow>y)y)"
      using sum_character..
    moreover assume "O (\<midarrow>x \<otimes> \<midarrow>y)(x \<oplus> y)"
    ultimately have "O (\<midarrow>x \<otimes> \<midarrow>y) x \<or> O (\<midarrow>x \<otimes> \<midarrow>y) y"..
    thus "False"
    proof
      assume "O (\<midarrow>x \<otimes> \<midarrow>y) x"
      with overlap_eq have "\<exists> v. P v (\<midarrow>x \<otimes> \<midarrow>y) \<and> P v x"..
      then obtain v where v: "P v (\<midarrow>x \<otimes> \<midarrow>y) \<and> P v x"..
      hence "P v (\<midarrow>x \<otimes> \<midarrow>y)"..
      from p have "P v ((\<midarrow>x) \<otimes> (\<midarrow>y)) \<longleftrightarrow> (P v (\<midarrow>x) \<and> P v (\<midarrow>y))"..
      hence "P v (\<midarrow>x) \<and> P v (\<midarrow>y)" using `P v (\<midarrow>x \<otimes> \<midarrow>y)`..
      hence "P v (\<midarrow>x)"..
      have "x \<noteq> u" using `x \<oplus> y \<noteq> u`
        by (rule first_summand_not_universe)
      hence "\<forall>w. P w (\<midarrow>x) \<longleftrightarrow> \<not> O w x"
        by (rule strong_complement_character)
      hence "P v (\<midarrow>x) \<longleftrightarrow> \<not> O v x"..
      hence "\<not> O v x" using `P v (\<midarrow>x)`..
      moreover from v have "P v x"..
      hence "O v x" by (rule part_implies_overlap)
      ultimately show "False"..
    next 
      assume "O (\<midarrow>x \<otimes> \<midarrow>y) y"
      with overlap_eq have "\<exists> v. P v (\<midarrow>x \<otimes> \<midarrow>y) \<and> P v y"..
      then obtain v where v: "P v (\<midarrow>x \<otimes> \<midarrow>y) \<and> P v y"..
      hence "P v (\<midarrow>x \<otimes> \<midarrow>y)"..
      from p have "P v ((\<midarrow>x) \<otimes> (\<midarrow>y)) \<longleftrightarrow> (P v (\<midarrow>x) \<and> P v (\<midarrow>y))"..
      hence "P v (\<midarrow>x) \<and> P v (\<midarrow>y)" using `P v (\<midarrow>x \<otimes> \<midarrow>y)`..
      hence "P v (\<midarrow>y)"..
      have "y \<noteq> u" using `x \<oplus> y \<noteq> u`
        by (rule second_summand_not_universe)
      hence "\<forall>w. P w (\<midarrow>y) \<longleftrightarrow> \<not> O w y"
        by (rule strong_complement_character)
      hence "P v (\<midarrow>y) \<longleftrightarrow> \<not> O v y"..
      hence "\<not> O v y" using `P v (\<midarrow>y)`..
      moreover from v have "P v y"..
      hence "O v y" by (rule part_implies_overlap)
      ultimately show "False"..
    qed
  qed
  ultimately show "P (\<midarrow>x \<otimes> \<midarrow>y) (\<midarrow>(x \<oplus> y))"..
qed

theorem sum_complement_is_complements_product:
  "x \<oplus> y \<noteq> u \<Longrightarrow> \<midarrow>(x \<oplus> y) = (\<midarrow>x \<otimes> \<midarrow>y)"
proof -
  assume "x \<oplus> y \<noteq> u"
  show "\<midarrow>(x \<oplus> y) = (\<midarrow>x \<otimes> \<midarrow>y)"
  proof (rule part_antisymmetry)
    show "P (\<midarrow> (x \<oplus> y)) (\<midarrow> x \<otimes> \<midarrow> y)" using  `x \<oplus> y \<noteq> u`
      by (rule sum_complement_in_complement_product)
    show "P (\<midarrow> x \<otimes> \<midarrow> y) (\<midarrow> (x \<oplus> y))" using `x \<oplus> y \<noteq> u`
      by (rule complement_product_in_sum_complement)
  qed
qed

lemma complement_sum_in_product_complement: 
  "O x y \<Longrightarrow> x \<noteq> u \<Longrightarrow> y \<noteq> u \<Longrightarrow> P ((\<midarrow>x) \<oplus> (\<midarrow>y))(\<midarrow>(x \<otimes> y))"
proof -
  assume "O x y"
  assume "x \<noteq> u"
  assume "y \<noteq> u"
  have "x \<otimes> y \<noteq> u"
  proof
    assume "x \<otimes> y = u"
    with `O x y` have "x = u"
      by (rule product_universe_implies_factor_universe)
    with `x \<noteq> u` show "False"..
  qed
  hence notxty: "\<forall> w. P w (\<midarrow>(x \<otimes> y)) \<longleftrightarrow> \<not> O w (x \<otimes> y)"
    by (rule strong_complement_character)
  hence "P((\<midarrow>x)\<oplus>(\<midarrow>y))(\<midarrow>(x \<otimes> y)) \<longleftrightarrow> \<not>O((\<midarrow>x)\<oplus>(\<midarrow>y))(x \<otimes> y)"..
  moreover have "\<not> O ((\<midarrow>x) \<oplus> (\<midarrow>y)) (x \<otimes> y)"
  proof
    from sum_character have 
      "\<forall> w. O w ((\<midarrow>x) \<oplus> (\<midarrow>y)) \<longleftrightarrow> (O w (\<midarrow>x) \<or> O w (\<midarrow>y))".
    hence "O(x \<otimes> y)((\<midarrow>x)\<oplus>(\<midarrow>y)) \<longleftrightarrow> (O(x \<otimes> y)(\<midarrow>x) \<or> O(x \<otimes> y)(\<midarrow>y))"..
    moreover assume "O ((\<midarrow>x) \<oplus> (\<midarrow>y)) (x \<otimes> y)"
    hence "O (x \<otimes> y) ((\<midarrow>x) \<oplus> (\<midarrow>y))" by (rule overlap_symmetry)
    ultimately have "O (x \<otimes> y) (\<midarrow>x) \<or> O (x \<otimes> y) (\<midarrow>y)"..
    thus False
    proof
      assume "O (x \<otimes> y)(\<midarrow>x)"
      with overlap_eq have "\<exists> v. P v (x \<otimes> y) \<and> P v (\<midarrow>x)"..
      then obtain v where v: "P v (x \<otimes> y) \<and> P v (\<midarrow>x)"..
      hence "P v (\<midarrow>x)"..
      with `x \<noteq> u` have "\<not> P v x"
        by (rule complement_part_not_part)
      moreover from v have "P v (x \<otimes> y)"..
      with `O x y` have "P v x" by (rule product_part_in_first_factor)
      ultimately show "False"..
    next 
      assume "O (x \<otimes> y) (\<midarrow>y)"
      with overlap_eq have "\<exists> v. P v (x \<otimes> y) \<and> P v (\<midarrow>y)"..
      then obtain v where v: "P v (x \<otimes> y) \<and> P v (\<midarrow>y)"..
      hence "P v (\<midarrow>y)"..
      with `y \<noteq> u` have "\<not> P v y" 
        by (rule complement_part_not_part)
      moreover from v have "P v (x \<otimes> y)"..
      with `O x y` have "P v y" by (rule product_part_in_second_factor)
      ultimately show "False"..
    qed
  qed
  ultimately show "P ((\<midarrow>x) \<oplus> (\<midarrow>y))(\<midarrow>(x \<otimes> y))"..
qed

lemma product_complement_in_complements_sum:  
  "x \<noteq> u \<Longrightarrow> y \<noteq> u \<Longrightarrow> P(\<midarrow>(x \<otimes> y))((\<midarrow>x) \<oplus> (\<midarrow>y))"
proof -
  assume "x \<noteq> u"
  hence "x = \<midarrow>(\<midarrow>x)"
    by (rule complement_involution)
  assume "y \<noteq> u"
  hence "y = \<midarrow>(\<midarrow>y)"
    by (rule complement_involution)
  show "P (\<midarrow>(x \<otimes> y))((\<midarrow>x) \<oplus> (\<midarrow>y))"
  proof cases
    assume "\<midarrow>x \<oplus> \<midarrow>y = u"
    thus "P (\<midarrow>(x \<otimes> y))((\<midarrow>x) \<oplus> (\<midarrow>y))"
      using universe_character by (rule ssubst)
  next
    assume "\<midarrow>x \<oplus> \<midarrow>y \<noteq> u"
    hence "\<midarrow>x \<oplus> \<midarrow>y = \<midarrow>(\<midarrow>(\<midarrow>x \<oplus> \<midarrow> y))"
      by (rule complement_involution)
    moreover have "\<midarrow>(\<midarrow>x \<oplus> \<midarrow>y) = \<midarrow>(\<midarrow>x) \<otimes> \<midarrow>(\<midarrow>y)" 
      using `\<midarrow>x \<oplus> \<midarrow>y \<noteq> u` 
      by (rule sum_complement_is_complements_product)
    with `x = \<midarrow>(\<midarrow>x)` have  "\<midarrow>(\<midarrow>x \<oplus> \<midarrow>y) = x \<otimes> \<midarrow>(\<midarrow>y)" 
      by (rule ssubst)
    with `y = \<midarrow>(\<midarrow>y)` have  "\<midarrow>(\<midarrow>x \<oplus> \<midarrow>y) = x \<otimes> y" 
      by (rule ssubst)
    hence "P (\<midarrow>(x \<otimes> y))(\<midarrow>(\<midarrow>(\<midarrow>x \<oplus> \<midarrow>y)))"
      using part_reflexivity by (rule subst)
    ultimately show "P (\<midarrow>(x \<otimes> y))(\<midarrow>x \<oplus> \<midarrow>y)" 
      by (rule ssubst)
  qed
qed

theorem complement_of_product_is_sum_of_complements:
  "O x y \<Longrightarrow> x \<oplus> y \<noteq> u \<Longrightarrow> \<midarrow>(x \<otimes> y) = (\<midarrow>x) \<oplus> (\<midarrow>y)"
proof -
  assume "O x y"
  assume "x \<oplus> y \<noteq> u"
  show "\<midarrow>(x \<otimes> y) = (\<midarrow>x) \<oplus> (\<midarrow>y)"
  proof (rule part_antisymmetry)
    have "x \<noteq> u" using \<open>x \<oplus> y \<noteq> u\<close> 
      by (rule first_summand_not_universe)
    have "y \<noteq> u" using \<open>x \<oplus> y \<noteq> u\<close> 
      by (rule second_summand_not_universe) 
    show "P (\<midarrow> (x \<otimes> y)) (\<midarrow> x \<oplus> \<midarrow> y)"
      using `x \<noteq> u` `y \<noteq> u` by (rule product_complement_in_complements_sum)
    show " P (\<midarrow> x \<oplus> \<midarrow> y) (\<midarrow> (x \<otimes> y))"
      using `O x y` `x \<noteq> u` `y \<noteq> u` by (rule complement_sum_in_product_complement)
  qed
qed

end

(*<*) end (*>*)