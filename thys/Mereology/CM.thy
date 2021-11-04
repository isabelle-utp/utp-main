section \<open> Closed Mereology \<close>

(*<*)
theory CM
  imports M
begin
(*>*)

text \<open> The theory of \emph{closed mereology} adds to ground mereology conditions guaranteeing the
existence of sums and products.\footnote{See @{cite "masolo_atomicity_1999"} p. 238. @{cite "varzi_parts_1996"} p. 263 
and @{cite "casati_parts_1999"} p. 43 give a slightly weaker version of the sum closure axiom, which is
equivalent given axioms considered later.} \<close>

locale CM = M +
  assumes sum_eq: "x \<oplus> y = (THE z. \<forall>v. O v z \<longleftrightarrow> O v x \<or> O v y)"
  assumes sum_closure: "\<exists>z. \<forall>v. O v z \<longleftrightarrow> O v x \<or> O v y"
  assumes product_eq: 
    "x \<otimes> y = (THE z. \<forall>v. P v z \<longleftrightarrow> P v x \<and> P v y)"
  assumes product_closure: 
    "O x y \<Longrightarrow> \<exists>z. \<forall>v. P v z \<longleftrightarrow> P v x \<and> P v y"
begin

subsection \<open> Products \<close>

lemma product_intro: 
  "(\<forall>w. P w z \<longleftrightarrow> (P w x \<and> P w y)) \<Longrightarrow> x \<otimes> y = z"
proof -
  assume z: "\<forall>w. P w z \<longleftrightarrow> (P w x \<and> P w y)"
  hence "(THE v. \<forall>w. P w v \<longleftrightarrow> P w x \<and> P w y) = z"
  proof (rule the_equality)
    fix v
    assume v: "\<forall>w. P w v \<longleftrightarrow> (P w x \<and> P w y)"
    have "\<forall>w. P w v \<longleftrightarrow> P w z"
    proof
      fix w
      from z have "P w z \<longleftrightarrow> (P w x \<and> P w y)"..
      moreover from v have "P w v \<longleftrightarrow> (P w x \<and> P w y)"..
      ultimately show "P w v \<longleftrightarrow> P w z" by (rule ssubst)
    qed
    with part_extensionality show "v = z"..
  qed
  thus "x \<otimes> y = z"
    using product_eq by (rule subst)
qed

lemma product_idempotence: "x \<otimes> x = x"
proof -
  have "\<forall>w. P w x \<longleftrightarrow> P w x \<and> P w x"
  proof
    fix w
    show "P w x \<longleftrightarrow> P w x \<and> P w x"
    proof
      assume "P w x"
      thus "P w x \<and> P w x" using `P w x`..
    next
      assume "P w x \<and> P w x"
      thus "P w x"..
    qed
  qed
  thus "x \<otimes> x = x" by (rule product_intro)
qed

lemma product_character: 
  "O x y \<Longrightarrow> (\<forall>w. P w (x \<otimes> y) \<longleftrightarrow> (P w x \<and> P w y))"
proof -
  assume "O x y"
  hence "\<exists>z. \<forall>w. P w z \<longleftrightarrow> (P w x \<and> P w y)" by (rule product_closure)
  then obtain z where z: "\<forall>w. P w z \<longleftrightarrow> (P w x \<and> P w y)"..
  hence "x \<otimes> y = z" by (rule product_intro)
  thus "\<forall>w. P w (x \<otimes> y) \<longleftrightarrow> P w x \<and> P w y"
    using z by (rule ssubst)
qed

lemma product_commutativity: "O x y \<Longrightarrow> x \<otimes> y = y \<otimes> x"
proof -
  assume "O x y"
  hence "O y x" by (rule overlap_symmetry)
  hence "\<forall>w. P w (y \<otimes> x) \<longleftrightarrow> (P w y \<and> P w x)" by (rule product_character)
  hence "\<forall>w. P w (y \<otimes> x) \<longleftrightarrow> (P w x \<and> P w y)" by auto
  thus "x \<otimes> y = y \<otimes> x" by (rule product_intro)
qed

lemma product_in_factors: "O x y \<Longrightarrow> P (x \<otimes> y) x \<and> P (x \<otimes> y) y"
proof -
  assume "O x y"
  hence "\<forall>w. P w (x \<otimes> y) \<longleftrightarrow> P w x \<and> P w y" by (rule product_character)
  hence "P (x \<otimes> y) (x \<otimes> y) \<longleftrightarrow> P (x \<otimes> y) x \<and> P (x \<otimes> y) y"..
  moreover have "P (x \<otimes> y) (x \<otimes> y)" by (rule part_reflexivity)
  ultimately show "P (x \<otimes> y) x \<and> P (x \<otimes> y) y"..
qed

lemma product_in_first_factor: "O x y \<Longrightarrow> P (x \<otimes> y) x"
proof -
  assume "O x y"
  hence "P (x \<otimes> y) x \<and> P (x \<otimes> y) y" by (rule product_in_factors)
  thus "P (x \<otimes> y) x"..
qed

lemma product_in_second_factor: "O x y \<Longrightarrow> P (x \<otimes> y) y"
proof -
  assume "O x y"
  hence "P (x \<otimes> y) x \<and> P (x \<otimes> y) y" by (rule product_in_factors)
  thus "P (x \<otimes> y) y"..
qed

lemma nonpart_implies_proper_product: 
  "\<not> P x y \<and> O x y \<Longrightarrow> PP (x \<otimes> y) x"
proof -
  assume antecedent: "\<not> P x y \<and> O x y"
  hence "\<not> P x y"..
  from antecedent have "O x y"..
  hence "P (x \<otimes> y) x" by (rule product_in_first_factor)
  moreover have "(x \<otimes> y) \<noteq> x"
  proof
    assume "(x \<otimes> y) = x"
    hence "\<not> P (x \<otimes> y) y"
      using `\<not> P x y` by (rule ssubst)
    moreover have "P (x \<otimes> y) y"
      using `O x y` by (rule product_in_second_factor)
    ultimately show "False"..
  qed
  ultimately have "P (x \<otimes> y) x \<and> x \<otimes> y \<noteq> x"..
  with nip_eq show "PP (x \<otimes> y) x"..
qed

lemma common_part_in_product: "P z x \<and> P z y \<Longrightarrow> P z (x \<otimes> y)"
proof -
  assume antecedent: "P z x \<and> P z y"
  hence "\<exists>z. P z x \<and> P z y"..
  with overlap_eq have "O x y"..
  hence "\<forall>w. P w (x \<otimes> y) \<longleftrightarrow> (P w x \<and> P w y)"
    by (rule product_character)
  hence "P z (x \<otimes> y) \<longleftrightarrow> (P z x \<and> P z y)"..
  thus "P z (x \<otimes> y)" 
    using `P z x \<and> P z y`..
qed

lemma product_part_in_factors: 
  "O x y \<Longrightarrow> P z (x \<otimes> y) \<Longrightarrow> P z x \<and> P z y"
proof -
  assume "O x y"
  hence "\<forall>w. P w (x \<otimes> y) \<longleftrightarrow> (P w x \<and> P w y)"
    by (rule product_character)
  hence "P z (x \<otimes> y) \<longleftrightarrow> (P z x \<and> P z y)"..
  moreover assume "P z (x \<otimes> y)"
  ultimately show "P z x \<and> P z y"..
qed

corollary product_part_in_first_factor: 
  "O x y \<Longrightarrow> P z (x \<otimes> y) \<Longrightarrow> P z x"
proof -
  assume "O x y"
  moreover assume "P z (x \<otimes> y)"
  ultimately have "P z x \<and> P z y"
    by (rule product_part_in_factors)
  thus "P z x"..
qed

corollary product_part_in_second_factor: 
  "O x y \<Longrightarrow> P z (x \<otimes> y) \<Longrightarrow> P z y"
proof -
  assume "O x y"
  moreover assume "P z (x \<otimes> y)"
  ultimately have "P z x \<and> P z y"
    by (rule product_part_in_factors)
  thus "P z y"..
qed

lemma part_product_identity: "P x y \<Longrightarrow> x \<otimes> y = x"
proof -
  assume "P x y"
  with part_reflexivity have "P x x \<and> P x y"..
  hence "P x (x \<otimes> y)" by (rule common_part_in_product)
  have "O x y" using `P x y` by (rule part_implies_overlap)
  hence  "P (x \<otimes> y) x" by (rule product_in_first_factor)
  thus "x \<otimes> y = x" using `P x (x \<otimes> y)` by (rule part_antisymmetry)
qed

lemma product_overlap: "P z x \<Longrightarrow> O z y \<Longrightarrow> O z (x \<otimes> y)"
proof -
  assume "P z x"
  assume "O z y"
  with overlap_eq have "\<exists>v. P v z \<and> P v y"..
  then obtain v where v: "P v z \<and> P v y"..
  hence "P v y"..
  from v have "P v z"..
  hence "P v x" using `P z x` by (rule part_transitivity)
  hence "P v x \<and> P v y" using `P v y`..
  hence "P v (x \<otimes> y)" by (rule common_part_in_product)
  with `P v z` have "P v z \<and> P v (x \<otimes> y)"..
  hence "\<exists>v. P v z \<and> P v (x \<otimes> y)"..
  with overlap_eq show "O z (x \<otimes> y)"..
qed

lemma disjoint_from_second_factor: 
  "P x y \<and> \<not> O x (y \<otimes> z) \<Longrightarrow> \<not> O x z" 
proof -
  assume antecedent: "P x y \<and> \<not> O x (y \<otimes> z)"
  hence "\<not> O x (y \<otimes> z)"..
  show "\<not> O x z"
  proof
    from antecedent have "P x y"..
    moreover assume "O x z"
    ultimately have "O x (y \<otimes> z)"
      by (rule product_overlap)
    with `\<not> O x (y \<otimes> z)` show "False"..
  qed
qed

lemma converse_product_overlap: 
  "O x y \<Longrightarrow> O z (x \<otimes> y) \<Longrightarrow> O z y"
proof -
  assume "O x y"
  hence "P (x \<otimes> y) y" by (rule product_in_second_factor)
  moreover assume "O z (x \<otimes> y)"
  ultimately show "O z y"
    by (rule overlap_monotonicity)
qed

lemma part_product_in_whole_product:
  "O x y \<Longrightarrow> P x v \<and> P y z \<Longrightarrow> P (x \<otimes> y) (v \<otimes> z)"
proof -
  assume "O x y"
  assume "P x v \<and> P y z"
  have "\<forall>w. P w (x \<otimes> y) \<longrightarrow> P w (v \<otimes> z)"
  proof
    fix w
    show "P w (x \<otimes> y) \<longrightarrow> P w (v \<otimes> z)"
    proof
      assume "P w (x \<otimes> y)"
      with `O x y` have "P w x \<and> P w y"
        by (rule product_part_in_factors)
      have "P w v \<and> P w z"
      proof
        from `P w x \<and> P w y` have "P w x"..
        moreover from `P x v \<and> P y z` have "P x v"..
        ultimately show "P w v" by (rule part_transitivity)
      next
        from `P w x \<and> P w y` have "P w y"..
        moreover from `P x v \<and> P y z` have "P y z"..
        ultimately show "P w z" by (rule part_transitivity)
      qed     
      thus "P w (v \<otimes> z)" by (rule common_part_in_product)
    qed
  qed
  hence "P (x \<otimes> y) (x \<otimes> y) \<longrightarrow> P (x \<otimes> y) (v \<otimes> z)"..
  moreover have "P (x \<otimes> y) (x \<otimes> y)" by (rule part_reflexivity)
  ultimately show "P (x \<otimes> y) (v \<otimes> z)"..
qed

lemma right_associated_product: "(\<exists>w. P w x \<and> P w y \<and> P w z) \<Longrightarrow>
  (\<forall>w. P w (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> P w x \<and> (P w y \<and> P w z))"
proof -
  assume antecedent: "(\<exists>w. P w x \<and> P w y \<and> P w z)"
  then obtain w where w: "P w x \<and> P w y \<and> P w z"..
  hence "P w x"..
  from w have "P w y \<and> P w z"..
  hence "\<exists>w. P w y \<and> P w z"..
  with overlap_eq have "O y z"..
  hence yz: "\<forall>w. P w (y \<otimes> z) \<longleftrightarrow> (P w y \<and> P w z)"
    by (rule product_character)
  hence "P w (y \<otimes> z) \<longleftrightarrow> (P w y \<and> P w z)"..
  hence "P w (y \<otimes> z)"
    using `P w y \<and> P w z`..
  with `P w x` have "P w x \<and> P w (y \<otimes> z)"..
  hence "\<exists>w. P w x \<and> P w (y \<otimes> z)"..
  with overlap_eq have "O x (y \<otimes> z)"..
  hence xyz: "\<forall>w. P w (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> P w x \<and> P w (y \<otimes> z)"
    by (rule product_character)
  show "\<forall>w. P w (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> P w x \<and> (P w y \<and> P w z)"
  proof
    fix w
    from yz have wyz: "P w (y \<otimes> z) \<longleftrightarrow> (P w y \<and> P w z)"..
    moreover from xyz have 
      "P w (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> P w x \<and> P w (y \<otimes> z)"..
    ultimately show 
      "P w (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> P w x \<and> (P w y \<and> P w z)"
      by (rule subst)
  qed
qed

lemma left_associated_product: "(\<exists>w. P w x \<and> P w y \<and> P w z) \<Longrightarrow>
  (\<forall>w. P w ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> (P w x \<and> P w y) \<and> P w z)"
proof -
  assume antecedent: "(\<exists>w. P w x \<and> P w y \<and> P w z)"
  then obtain w where w: "P w x \<and> P w y \<and> P w z"..
  hence "P w y \<and> P w z"..
  hence "P w y"..
  have "P w z"
    using `P w y \<and> P w z`..
  from w have "P w x"..
  hence "P w x \<and> P w y"
    using `P w y`..
  hence "\<exists>z. P z x \<and> P z y"..
  with overlap_eq have "O x y"..
  hence xy: "\<forall>w. P w (x \<otimes> y) \<longleftrightarrow> (P w x \<and> P w y)"
    by (rule product_character)
  hence "P w (x \<otimes> y) \<longleftrightarrow> (P w x \<and> P w y)"..
  hence "P w (x \<otimes> y)"
    using `P w x \<and> P w y`..
  hence "P w (x \<otimes> y) \<and> P w z"
    using `P w z`..
  hence "\<exists>w. P w (x \<otimes> y) \<and> P w z"..
  with overlap_eq have "O (x \<otimes> y) z"..
  hence xyz: "\<forall>w. P w ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> P w (x \<otimes> y) \<and> P w z"
    by (rule product_character)
  show "\<forall>w. P w ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> (P w x \<and> P w y) \<and> P w z"
  proof
    fix v
    from xy have vxy: "P v (x \<otimes> y) \<longleftrightarrow> (P v x \<and> P v y)"..
    moreover from xyz have 
      "P v ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> P v (x \<otimes> y) \<and> P v z"..
    ultimately show "P v ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> (P v x \<and> P v y) \<and> P v z"
      by (rule subst)
  qed
qed

theorem product_associativity:
  "(\<exists>w. P w x \<and> P w y \<and> P w z) \<Longrightarrow> x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z"
proof -
  assume ante:"(\<exists>w. P w x \<and> P w y \<and> P w z)"
  hence "(\<forall>w. P w (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> P w x \<and> (P w y \<and> P w z))"
    by (rule right_associated_product)
  moreover from ante have 
    "(\<forall>w. P w ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> (P w x \<and> P w y) \<and> P w z)"
    by (rule left_associated_product)
  ultimately have "\<forall>w. P w (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> P w ((x \<otimes> y) \<otimes> z)" 
    by simp
  with part_extensionality show "x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z"..
qed

end

subsection \<open> Differences  \<close>

text \<open> Some writers also add to closed mereology the axiom of difference closure.\footnote{See, for example,
@{cite "varzi_parts_1996"} p. 263 and @{cite "masolo_atomicity_1999"} p. 238.} \<close>

locale CMD = CM +
  assumes difference_eq: 
    "x \<ominus> y = (THE z. \<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y)"
  assumes difference_closure:
    "(\<exists>w. P w x \<and> \<not> O w y) \<Longrightarrow> (\<exists>z. \<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y)"
begin

lemma difference_intro: 
  "(\<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y) \<Longrightarrow> x \<ominus> y = z"
proof -
  assume antecedent: "(\<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y)"
  hence "(THE z. \<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y) = z"
  proof (rule the_equality)
    fix v
    assume v: "(\<forall>w. P w v \<longleftrightarrow> P w x \<and> \<not> O w y)"
    have "\<forall>w. P w v \<longleftrightarrow> P w z"
    proof
      fix w
      from antecedent have "P w z \<longleftrightarrow> P w x \<and> \<not> O w y"..
      moreover from v have "P w v \<longleftrightarrow> P w x \<and> \<not> O w y"..
      ultimately show "P w v \<longleftrightarrow> P w z" by (rule ssubst)
    qed
    with part_extensionality show "v = z"..
  qed
  with difference_eq show "x \<ominus> y = z" by (rule ssubst)
qed

lemma difference_idempotence: "\<not> O x y \<Longrightarrow> (x \<ominus> y) = x"
proof -
  assume "\<not> O x y"
  hence "\<not> O y x" by (rule disjoint_symmetry)
  have "\<forall>w. P w x \<longleftrightarrow> P w x \<and> \<not> O w y"
  proof
    fix w
    show "P w x \<longleftrightarrow> P w x \<and> \<not> O w y"
    proof
      assume "P w x"
      hence "\<not> O y w" using `\<not> O y x`
        by (rule disjoint_demonotonicity)
      hence "\<not> O w y" by (rule disjoint_symmetry)
      with `P w x` show "P w x \<and> \<not> O w y"..
    next
      assume "P w x \<and> \<not> O w y"
      thus "P w x"..
    qed
  qed
  thus "(x \<ominus> y) = x" by (rule difference_intro)
qed

lemma difference_character: "(\<exists>w. P w x \<and> \<not> O w y) \<Longrightarrow> 
  (\<forall>w. P w (x \<ominus> y) \<longleftrightarrow> P w x \<and> \<not> O w y)"
proof -
  assume "\<exists>w. P w x \<and> \<not> O w y"
  hence "\<exists>z. \<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y" by (rule difference_closure)
  then obtain z where z: "\<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y"..
  hence "(x \<ominus> y) = z" by (rule difference_intro)
  thus "\<forall>w. P w (x \<ominus> y) \<longleftrightarrow> P w x \<and> \<not> O w y" using z by (rule ssubst)
qed

lemma difference_disjointness: 
  "(\<exists>z. P z x \<and> \<not> O z y) \<Longrightarrow> \<not> O y (x \<ominus> y)"
proof -
  assume "\<exists>z. P z x \<and> \<not> O z y"
  hence xmy: "\<forall>w. P w (x \<ominus> y) \<longleftrightarrow> (P w x \<and> \<not> O w y)"
    by (rule difference_character)
  show "\<not> O y (x \<ominus> y)"
  proof
    assume "O y (x \<ominus> y)"
    with overlap_eq have "\<exists>v. P v y \<and> P v (x \<ominus> y)"..
    then obtain v where v: "P v y \<and> P v (x \<ominus> y)"..
    from xmy have "P v (x \<ominus> y) \<longleftrightarrow> (P v x \<and> \<not> O v y)"..
    moreover from v have "P v (x \<ominus> y)"..
    ultimately have "P v x \<and> \<not> O v y"..
    hence "\<not> O v y"..
    moreover from v have "P v y"..
    hence "O v y" by (rule part_implies_overlap)
    ultimately show "False"..
  qed
qed

end

subsection \<open> The Universe \<close>

text \<open> Another closure condition sometimes considered is the existence of the universe.\footnote{
See, for example, @{cite "varzi_parts_1996"} p. 264 and @{cite "casati_parts_1999"} p. 45.}  \<close>

locale CMU = CM +
  assumes universe_eq: "u = (THE z. \<forall>w. P w z)" 
  assumes universe_closure: "\<exists>y. \<forall>x. P x y"
begin

lemma universe_intro: "(\<forall>w. P w z) \<Longrightarrow> u = z"
proof -
  assume z: "\<forall>w. P w z"
  hence "(THE z. \<forall>w. P w z) = z"
  proof (rule the_equality)
    fix v
    assume v: "\<forall>w. P w v"
    have "\<forall>w. P w v \<longleftrightarrow> P w z"
    proof
      fix w
      show "P w v \<longleftrightarrow> P w z"
      proof
        assume "P w v"
        from z show "P w z"..
      next
        assume "P w z"
        from v show "P w v"..
      qed
    qed
    with part_extensionality show "v = z"..
  qed
  thus "u = z" using universe_eq by (rule subst)
qed

lemma universe_character: "P x u"
proof -
  from universe_closure obtain y where y: "\<forall>x. P x y"..
  hence "u = y" by (rule universe_intro)
  hence "\<forall>x. P x u" using y by (rule ssubst)
  thus "P x u"..
qed

lemma "\<not> PP u x"
proof
  assume "PP u x"
  hence "\<not> P x u" by (rule proper_implies_not_part)
  thus "False" using universe_character..
qed

lemma product_universe_implies_factor_universe: 
  "O x y \<Longrightarrow> x \<otimes> y = u \<Longrightarrow> x = u"
proof -
  assume "x \<otimes> y = u"
  moreover assume "O x y"
  hence "P (x \<otimes> y) x"
    by (rule product_in_first_factor)  
  ultimately have "P u x"
    by (rule subst)
  with universe_character show "x = u"
    by (rule part_antisymmetry)
qed

end

subsection \<open> Complements \<close>

text \<open> As is a condition ensuring the existence of complements.\footnote{See, for example, 
 @{cite "varzi_parts_1996"} p. 264 and @{cite "casati_parts_1999"} p. 45.} \<close>

locale CMC = CM +
  assumes complement_eq: "\<midarrow>x = (THE z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)"
  assumes complement_closure: 
    "(\<exists>w. \<not> O w x) \<Longrightarrow> (\<exists>z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)"
  assumes difference_eq: 
    "x \<ominus> y = (THE z. \<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y)"
begin

lemma complement_intro:
  "(\<forall>w. P w z \<longleftrightarrow> \<not> O w x) \<Longrightarrow> \<midarrow>x = z"
proof -
  assume antecedent: "\<forall>w. P w z \<longleftrightarrow> \<not> O w x"
  hence "(THE z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x) = z"
  proof (rule the_equality)
    fix v
    assume v: "\<forall>w. P w v \<longleftrightarrow> \<not> O w x"
    have "\<forall>w. P w v \<longleftrightarrow> P w z"
    proof
      fix w
      from antecedent have "P w z \<longleftrightarrow> \<not> O w x"..
      moreover from v have "P w v \<longleftrightarrow> \<not> O w x"..
      ultimately show "P w v \<longleftrightarrow> P w z" by (rule ssubst)
    qed
    with part_extensionality show "v = z"..
  qed
  with complement_eq show "\<midarrow>x = z" by (rule ssubst)
qed

lemma complement_character:
  "(\<exists>w. \<not> O w x) \<Longrightarrow> (\<forall>w. P w (\<midarrow>x) \<longleftrightarrow> \<not> O w x)"
proof -
  assume "\<exists>w. \<not> O w x"
  hence "(\<exists>z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)" by (rule complement_closure)
  then obtain z where z: "\<forall>w. P w z \<longleftrightarrow> \<not> O w x"..
  hence "\<midarrow>x = z" by (rule complement_intro)
  thus "\<forall>w. P w (\<midarrow>x) \<longleftrightarrow> \<not> O w x"
    using z by (rule ssubst)
qed

lemma not_complement_part: "\<exists>w. \<not> O w x \<Longrightarrow> \<not> P x (\<midarrow>x)"
proof -
  assume "\<exists>w. \<not> O w x"
  hence "\<forall>w. P w (\<midarrow>x) \<longleftrightarrow> \<not> O w x"
    by (rule complement_character)
  hence "P x (\<midarrow>x) \<longleftrightarrow> \<not> O x x"..
  show "\<not> P x (\<midarrow>x)"
  proof
    assume "P x (\<midarrow>x)"
    with `P x (\<midarrow>x) \<longleftrightarrow> \<not> O x x` have "\<not> O x x"..
    thus "False" using overlap_reflexivity..
  qed
qed

lemma complement_part: "\<not> O x y \<Longrightarrow> P x (\<midarrow>y)"
proof -
  assume "\<not> O x y"
  hence "\<exists>z. \<not> O z y"..
  hence "\<forall>w. P w (\<midarrow>y) \<longleftrightarrow> \<not> O w y"
    by (rule complement_character)
  hence "P x (\<midarrow>y) \<longleftrightarrow> \<not> O x y"..
  thus "P x (\<midarrow>y)" using `\<not> O x y`..
qed

lemma complement_overlap: "\<not> O x y \<Longrightarrow> O x (\<midarrow>y)"
proof -
  assume "\<not> O x y"
  hence "P x (\<midarrow>y)"
    by (rule complement_part)
  thus "O x (\<midarrow>y)"
    by (rule part_implies_overlap)
qed

lemma or_complement_overlap: "\<forall>y. O y x \<or> O y (\<midarrow>x)"
proof
  fix y
  show "O y x \<or> O y (\<midarrow>x)"
  proof cases
    assume "O y x"
    thus "O y x \<or> O y (\<midarrow>x)"..
  next
    assume "\<not> O y x"
    hence "O y (\<midarrow>x)"
      by (rule complement_overlap)
    thus "O y x \<or> O y (\<midarrow>x)"..
  qed
qed

lemma complement_disjointness: "\<exists>v. \<not> O v x \<Longrightarrow> \<not> O x (\<midarrow>x)"
proof -
  assume "\<exists>v. \<not> O v x"
  hence w: "\<forall>w. P w (\<midarrow>x) \<longleftrightarrow> \<not> O w x"
    by (rule complement_character)
  show "\<not> O x (\<midarrow>x)"
  proof
    assume "O x (\<midarrow>x)"
    with overlap_eq have "\<exists>v. P v x \<and> P v (\<midarrow>x)"..
    then obtain v where v: "P v x \<and> P v (\<midarrow>x)"..
    from w have "P v (\<midarrow>x) \<longleftrightarrow> \<not> O v x"..
    moreover from v have  "P v (\<midarrow>x)"..
    ultimately have "\<not> O v x"..
    moreover from v have "P v x"..
    hence "O v x" by (rule part_implies_overlap)
    ultimately show "False"..
  qed
qed

lemma part_disjoint_from_complement:
  "\<exists>v. \<not> O v x \<Longrightarrow> P y x \<Longrightarrow> \<not> O y (\<midarrow>x)"
proof
  assume "\<exists>v. \<not> O v x"
  hence "\<not> O x (\<midarrow>x)" by (rule complement_disjointness)
  assume "P y x"
  assume "O y (\<midarrow>x)"
  with overlap_eq have "\<exists>v. P v y \<and> P v (\<midarrow>x)"..
  then obtain v where v: "P v y \<and> P v (\<midarrow>x)"..
  hence "P v y"..
  hence "P v x" using `P y x` by (rule part_transitivity)
  moreover from v have "P v (\<midarrow>x)"..
  ultimately have "P v x \<and> P v (\<midarrow>x)"..
  hence "\<exists>v. P v x \<and> P v (\<midarrow>x)"..
  with overlap_eq have "O x (\<midarrow>x)"..
  with `\<not> O x (\<midarrow>x)` show "False"..
qed

lemma product_complement_character: "(\<exists>w. P w x \<and> \<not> O w y) \<Longrightarrow> 
  (\<forall>w. P w (x \<otimes> (\<midarrow>y)) \<longleftrightarrow> (P w x \<and> (\<not> O w y)))"
proof -
  assume antecedent: "\<exists>w. P w x \<and> \<not> O w y"
  then obtain w where w: "P w x \<and> \<not> O w y"..
  hence "P w x"..
  moreover from w have "\<not> O w y"..
  hence "P w (\<midarrow>y)" by (rule complement_part)  
  ultimately have  "P w x \<and> P w (\<midarrow>y)"..
  hence "\<exists>w. P w x \<and> P w (\<midarrow>y)"..
  with overlap_eq have "O x (\<midarrow>y)"..
  hence prod: "(\<forall>w. P w (x \<otimes> (\<midarrow>y)) \<longleftrightarrow> (P w x \<and> P w (\<midarrow>y)))"
    by (rule product_character)
  show "\<forall>w. P w (x \<otimes> (\<midarrow>y)) \<longleftrightarrow> (P w x \<and> (\<not> O w y))"
  proof
    fix v
    from w have "\<not> O w y"..
    hence "\<exists>w. \<not> O w y"..
    hence "\<forall>w. P w (\<midarrow>y) \<longleftrightarrow> \<not> O w y"
      by (rule complement_character)
    hence "P v (\<midarrow>y) \<longleftrightarrow> \<not> O v y"..
    moreover have "P v (x \<otimes> (\<midarrow>y)) \<longleftrightarrow> (P v x \<and> P v (\<midarrow>y))"
      using prod..
    ultimately show "P v (x \<otimes> (\<midarrow>y)) \<longleftrightarrow> (P v x \<and> (\<not> O v y))"
      by (rule subst)
  qed
qed

theorem difference_closure: "(\<exists>w. P w x \<and> \<not> O w y) \<Longrightarrow> 
  (\<exists>z. \<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y)"
proof -
  assume "\<exists>w. P w x \<and> \<not> O w y"
  hence "\<forall>w. P w (x \<otimes> (\<midarrow>y)) \<longleftrightarrow> P w x \<and> \<not> O w y"
    by (rule product_complement_character)
  thus "(\<exists>z. \<forall>w. P w z \<longleftrightarrow> P w x \<and> \<not> O w y)" by (rule exI)
qed

end

sublocale CMC \<subseteq> CMD
proof
  fix x y
  show "x \<ominus> y = (THE z. \<forall>w. P w z = (P w x \<and> \<not> O w y))"
    using difference_eq.
  show "(\<exists>w. P w x \<and> \<not> O w y) \<Longrightarrow> 
    (\<exists>z. \<forall>w. P w z = (P w x \<and> \<not> O w y))"
    using difference_closure.
qed

corollary (in CMC) difference_is_product_of_complement:
  "(\<exists>w. P w x \<and> \<not> O w y) \<Longrightarrow> (x \<ominus> y) = x \<otimes> (\<midarrow>y)" 
proof -
  assume antecedent: "\<exists>w. P w x \<and> \<not> O w y"
  hence "\<forall>w. P w (x \<otimes> (\<midarrow>y)) \<longleftrightarrow> P w x \<and> \<not> O w y"
    by (rule product_complement_character)
  thus "(x \<ominus> y) = x \<otimes> (\<midarrow>y)" by (rule difference_intro)
qed

text \<open> Universe and difference closure entail complement closure, since the difference of an individual
and the universe is the individual's complement. \<close>

locale CMUD = CMU + CMD +
  assumes complement_eq: "\<midarrow>x = (THE z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)"
begin

lemma universe_difference:
  "(\<exists>w. \<not> O w x) \<Longrightarrow> (\<forall>w. P w (u \<ominus> x) \<longleftrightarrow> \<not> O w x)"
proof -
  assume "\<exists>w. \<not> O w x"
  then obtain w where w: "\<not> O w x"..
  from universe_character have "P w u".
  hence "P w u \<and> \<not> O w x" using `\<not> O w x`..
  hence "\<exists>z. P z u \<and> \<not> O z x"..
  hence ux: "\<forall>w. P w (u \<ominus> x) \<longleftrightarrow> (P w u \<and> \<not> O w x)"
    by (rule difference_character)
  show "\<forall>w. P w (u \<ominus> x) \<longleftrightarrow> \<not> O w x"
  proof
    fix w
    from ux have wux: "P w (u \<ominus> x) \<longleftrightarrow> (P w u \<and> \<not> O w x)"..
    show "P w (u \<ominus> x) \<longleftrightarrow> \<not> O w x"
    proof
      assume "P w (u \<ominus> x)"
      with wux have "P w u \<and> \<not> O w x"..
      thus "\<not> O w x"..
    next
      assume "\<not> O w x"
      from universe_character have "P w u".
      hence "P w u \<and> \<not> O w x" using `\<not> O w x`..
      with wux show "P w (u \<ominus> x)"..
    qed
  qed
qed

theorem complement_closure: 
  "(\<exists>w. \<not> O w x) \<Longrightarrow> (\<exists>z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)"
proof -
  assume "\<exists>w. \<not> O w x"
  hence "\<forall>w. P w (u \<ominus> x) \<longleftrightarrow> \<not> O w x"
    by (rule universe_difference)
  thus "\<exists>z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x"..
qed

end

sublocale CMUD \<subseteq> CMC
proof
  fix x y
  show "\<midarrow>x = (THE z. \<forall>w. P w z \<longleftrightarrow> (\<not> O w x))" 
    using complement_eq.
  show "\<exists>w. \<not> O w x \<Longrightarrow> \<exists>z. \<forall>w. P w z \<longleftrightarrow> (\<not> O w x)" 
    using complement_closure.
  show "x \<ominus> y = (THE z. \<forall>w. P w z = (P w x \<and> \<not> O w y))" 
    using difference_eq.
qed

corollary (in CMUD) complement_universe_difference: 
  "(\<exists>y. \<not> O y x) \<Longrightarrow> \<midarrow>x = (u \<ominus> x)"
proof -
  assume "\<exists>w. \<not> O w x"
  hence "\<forall>w. P w (u \<ominus> x) \<longleftrightarrow> \<not> O w x"
    by (rule universe_difference)
  thus " \<midarrow>x = (u \<ominus> x)"
    by (rule complement_intro)
qed

(*<*) end (*>*)