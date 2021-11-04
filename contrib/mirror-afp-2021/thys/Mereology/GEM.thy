section \<open> General Extensional Mereology \<close>

(*<*)
theory GEM
  imports GMM CEM
begin (*>*)

text \<open> The theory of \emph{general extensional mereology}, also known as \emph{classical extensional
mereology} adds general mereology to extensional mereology.\footnote{For this axiomatization see
@{cite "varzi_parts_1996"} p. 265  and @{cite "casati_parts_1999"} p. 46.} \<close>

locale GEM = GM + EM +
  assumes sum_eq: "x \<oplus> y = (THE z. \<forall>v. O v z \<longleftrightarrow> O v x \<or> O v y)" 
  assumes product_eq: 
    "x \<otimes> y = (THE z. \<forall>v. P v z \<longleftrightarrow> P v x \<and> P v y)"
  assumes difference_eq: 
    "x \<ominus> y = (THE z. \<forall>w. P w z = (P w x \<and> \<not> O w y))"
  assumes complement_eq: "\<midarrow> x = (THE z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)"
  assumes universe_eq: "u = (THE x. \<forall>y. P y x)"
  assumes fusion_eq: "\<exists>x. F x \<Longrightarrow> 
    (\<sigma> x. F x) = (THE x. \<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z))"
  assumes general_product_eq: "(\<pi> x. F x) = (\<sigma> x. \<forall>y. F y \<longrightarrow> P x y)"

sublocale GEM \<subseteq> GMM
proof
qed

subsection \<open> General Sums  \<close>

context GEM
begin

lemma fusion_intro: 
"(\<forall>y. O y z \<longleftrightarrow> (\<exists>x. F x \<and> O y x)) \<Longrightarrow> (\<sigma> x. F x) = z"
proof -
  assume antecedent: "(\<forall>y. O y z \<longleftrightarrow> (\<exists>x. F x \<and> O y x))"
  hence "(THE x. \<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z)) = z"
  proof (rule the_equality)
    fix a
    assume a: "(\<forall>y. O y a \<longleftrightarrow> (\<exists>x. F x \<and> O y x))"
    have "\<forall>x. O x a \<longleftrightarrow> O x z"
    proof
      fix b     
      from antecedent have "O b z \<longleftrightarrow> (\<exists>x. F x \<and> O b x)"..
      moreover from a have "O b a \<longleftrightarrow> (\<exists>x. F x \<and> O b x)"..
      ultimately show "O b a \<longleftrightarrow> O b z" by (rule ssubst)
    qed
    with overlap_extensionality show "a = z"..
  qed
  moreover from antecedent have "O z z \<longleftrightarrow> (\<exists>x. F x \<and> O z x)"..
  hence "\<exists>x. F x \<and> O z x" using overlap_reflexivity..
  hence "\<exists>x. F x" by auto
  hence "(\<sigma> x. F x) = (THE x. \<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z))"
    by (rule fusion_eq)
  ultimately show "(\<sigma> v. F v) = z" by (rule subst)
qed

lemma fusion_idempotence: "(\<sigma> x. z = x) = z"
proof -
  have "\<forall>y. O y z \<longleftrightarrow> (\<exists>x. z = x \<and> O y x)"
  proof
    fix y
    show "O y z \<longleftrightarrow> (\<exists>x. z = x \<and> O y x)"
    proof
      assume "O y z"
      with refl have "z = z \<and> O y z"..
      thus "\<exists>x. z = x \<and> O y x"..
    next
      assume "\<exists>x. z = x \<and> O y x"
      then obtain x where x: "z = x \<and> O y x"..
      hence "z = x"..
      moreover from x have "O y x"..
      ultimately show "O y z" by (rule ssubst)
    qed
  qed
  thus "(\<sigma> x. z = x) = z"
    by (rule fusion_intro)
qed

text \<open> The whole is the sum of its parts. \<close>

lemma fusion_absorption: "(\<sigma> x. P x z) = z"
proof -
  have "(\<forall>y. O y z \<longleftrightarrow> (\<exists>x. P x z \<and> O y x))"
  proof
    fix y
    show "O y z \<longleftrightarrow> (\<exists>x. P x z \<and> O y x)"
    proof
      assume "O y z"
      with part_reflexivity have "P z z \<and> O y z"..
      thus "\<exists>x. P x z \<and> O y x"..
    next
      assume "\<exists>x. P x z \<and> O y x"
      then obtain x where x: "P x z \<and> O y x"..
      hence "P x z"..
      moreover from x have "O y x"..
      ultimately show "O y z" by (rule overlap_monotonicity)
    qed
  qed
  thus "(\<sigma> x. P x z) = z"
    by (rule fusion_intro)
qed

lemma part_fusion: "P w (\<sigma> v. P v x) \<Longrightarrow> P w x"
proof -
  assume "P w (\<sigma> v. P v x)"
  with fusion_absorption show "P w x" by (rule subst)
qed

lemma fusion_character: 
  "\<exists>x. F x \<Longrightarrow> (\<forall>y. O y (\<sigma> v. F v) \<longleftrightarrow> (\<exists>x. F x \<and> O y x))"
proof -
  assume "\<exists>x. F x"
  hence "\<exists>z. \<forall>y. O y z \<longleftrightarrow> (\<exists>x. F x \<and> O y x)"
    by (rule fusion)
  then obtain z where z: "\<forall>y. O y z \<longleftrightarrow> (\<exists>x. F x \<and> O y x)"..
  hence "(\<sigma> v. F v) = z " by (rule fusion_intro)
  thus "\<forall>y. O y (\<sigma> v. F v) \<longleftrightarrow> (\<exists>x. F x \<and> O y x)" using z by (rule ssubst)
qed

text \<open> The next lemma characterises fusions in terms of parthood.\footnote{See @{cite "pontow_note_2004"} pp. 202-9.} \<close>

lemma fusion_part_character: "\<exists>x. F x \<Longrightarrow> 
  (\<forall>y. P y (\<sigma> v. F v) \<longleftrightarrow> (\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v)))"
proof -
  assume "(\<exists>x. F x)"
  hence F: "\<forall>y. O y (\<sigma> v. F v) \<longleftrightarrow> (\<exists>x. F x \<and> O y x)"
    by (rule fusion_character)
  show "\<forall>y. P y (\<sigma> v. F v) \<longleftrightarrow> (\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v))"
  proof
    fix y
    show "P y (\<sigma> v. F v) \<longleftrightarrow> (\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v))"
    proof
      assume "P y (\<sigma> v. F v)"
      show "\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v)"
      proof
        fix w
        from F have w: "O w (\<sigma> v. F v) \<longleftrightarrow> (\<exists>x. F x \<and> O w x)"..
        show "P w y \<longrightarrow> (\<exists>v. F v \<and> O w v)"
        proof
          assume "P w y"
          hence "P w (\<sigma> v. F v)" using `P y (\<sigma> v. F v)`
            by (rule part_transitivity)
          hence "O w (\<sigma> v. F v)" by (rule part_implies_overlap)
          with w show "\<exists>x. F x \<and> O w x"..
        qed
      qed
    next
      assume right: "\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v)"
      show "P y (\<sigma> v. F v)"
      proof (rule ccontr)
        assume "\<not> P y (\<sigma> v. F v)"
        hence "\<exists>v. P v y \<and> \<not> O v (\<sigma> v. F v)"
          by (rule strong_supplementation)
        then obtain v where v: "P v y \<and> \<not> O v (\<sigma> v. F v)"..
        hence "\<not> O v (\<sigma> v. F v)"..
        from right have "P v y \<longrightarrow> (\<exists>w. F w \<and> O v w)"..
        moreover from v have "P v y"..
        ultimately have "\<exists>w. F w \<and> O v w"..
        from F have "O v (\<sigma> v. F v) \<longleftrightarrow> (\<exists>x. F x \<and> O v x)"..
        hence "O v (\<sigma> v. F v)" using `\<exists>w. F w \<and> O v w`..
        with `\<not> O v (\<sigma> v. F v)` show "False"..
      qed
    qed
  qed
qed

lemma fusion_part: "F x \<Longrightarrow> P x (\<sigma> x. F x)"
proof -
  assume "F x"
  hence "\<exists>x. F x"..
  hence "\<forall>y. P y (\<sigma> v. F v) \<longleftrightarrow> (\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v))"
    by (rule fusion_part_character)
  hence "P x (\<sigma> v. F v) \<longleftrightarrow> (\<forall>w. P w x \<longrightarrow> (\<exists>v. F v \<and> O w v))"..
  moreover have "\<forall>w. P w x \<longrightarrow> (\<exists>v. F v \<and> O w v)"
  proof
    fix w
    show "P w x \<longrightarrow> (\<exists>v. F v \<and> O w v)"
    proof
      assume "P w x"
      hence "O w x" by (rule part_implies_overlap)
      with `F x` have "F x \<and> O w x"..
      thus "\<exists>v. F v \<and> O w v"..
    qed
  qed
  ultimately show "P x (\<sigma> v. F v)"..
qed

lemma common_part_fusion: 
  "O x y \<Longrightarrow> (\<forall>w. P w (\<sigma> v. (P v x \<and> P v y)) \<longleftrightarrow> (P w x \<and> P w y))"
proof -
  assume "O x y"
  with overlap_eq have "\<exists>z. (P z x \<and> P z y)"..
  hence sum: "(\<forall>w. P w (\<sigma> v. (P v x \<and> P v y)) \<longleftrightarrow> 
    (\<forall>z. P z w \<longrightarrow> (\<exists>v. (P v x \<and> P v y) \<and> O z v)))"
    by (rule fusion_part_character)
  show "\<forall>w. P w (\<sigma> v. (P v x \<and> P v y)) \<longleftrightarrow> (P w x \<and> P w y)"
  proof
    fix w
    from sum have w: "P w (\<sigma> v. (P v x \<and> P v y)) 
      \<longleftrightarrow> (\<forall>z. P z w \<longrightarrow> (\<exists>v. (P v x \<and> P v y) \<and> O z v))"..
    show "P w (\<sigma> v. (P v x \<and> P v y)) \<longleftrightarrow> (P w x \<and> P w y)"
    proof
      assume "P w (\<sigma> v. (P v x \<and> P v y))"
      with w have bla: 
        "(\<forall>z. P z w \<longrightarrow> (\<exists>v. (P v x \<and> P v y) \<and> O z v))"..
      show "P w x \<and> P w y" 
      proof
        show "P w x"
        proof (rule ccontr)
          assume "\<not> P w x"
          hence "\<exists>z. P z w \<and> \<not> O z x"
            by (rule strong_supplementation)
          then obtain z where z: "P z w \<and> \<not> O z x"..
          hence "\<not> O z x"..
          from bla have "P z w \<longrightarrow> (\<exists>v. (P v x \<and> P v y) \<and> O z v)"..
          moreover from z have "P z w"..
          ultimately have "\<exists>v. (P v x \<and> P v y) \<and> O z v"..
          then obtain v where v: "(P v x \<and> P v y) \<and> O z v"..
          hence "P v x \<and> P v y"..
          hence "P v x"..
          moreover from v have "O z v"..
          ultimately have "O z x"
            by (rule overlap_monotonicity)
          with `\<not> O z x` show "False"..
        qed
        show "P w y"
        proof (rule ccontr)
          assume "\<not> P w y"
          hence "\<exists>z. P z w \<and> \<not> O z y"
            by (rule strong_supplementation)
          then obtain z where z: "P z w \<and> \<not> O z y"..
          hence "\<not> O z y"..
          from bla have "P z w \<longrightarrow> (\<exists>v. (P v x \<and> P v y) \<and> O z v)"..
          moreover from z have "P z w"..
          ultimately have "\<exists>v. (P v x \<and> P v y) \<and> O z v"..
          then obtain v where v: "(P v x \<and> P v y) \<and> O z v"..
          hence "P v x \<and> P v y"..
          hence "P v y"..
          moreover from v have "O z v"..
          ultimately have "O z y"
            by (rule overlap_monotonicity)
          with `\<not> O z y` show "False"..
        qed
      qed
    next
      assume "P w x \<and> P w y"
      thus "P w (\<sigma> v. (P v x \<and> P v y))"
        by (rule fusion_part)
    qed
  qed
qed

theorem product_closure: 
  "O x y \<Longrightarrow> (\<exists>z. \<forall>w. P w z \<longleftrightarrow> (P w x \<and> P w y))"
proof -
  assume "O x y"
  hence "(\<forall>w. P w (\<sigma> v. (P v x \<and> P v y)) \<longleftrightarrow> (P w x \<and> P w y))"
    by (rule common_part_fusion)
  thus "\<exists>z. \<forall>w. P w z \<longleftrightarrow> (P w x \<and> P w y)"..
qed

end

sublocale GEM \<subseteq> CEM
proof
  fix x y
  show "\<exists>z. \<forall>w. O w z = (O w x \<or> O w y)" 
    using sum_closure.
  show "x \<oplus> y = (THE z. \<forall>v. O v z \<longleftrightarrow> O v x \<or> O v y)" 
    using sum_eq.
  show "x \<otimes> y = (THE z. \<forall>v. P v z \<longleftrightarrow> P v x \<and> P v y)" 
    using product_eq.
  show "O x y \<Longrightarrow> (\<exists>z. \<forall>w. P w z = (P w x \<and> P w y))" 
    using product_closure.
qed

context GEM
begin

corollary "O x y \<Longrightarrow> x \<otimes> y = (\<sigma> v. P v x \<and> P v y)"
proof -
  assume "O x y"
  hence "(\<forall>w. P w (\<sigma> v. (P v x \<and> P v y)) \<longleftrightarrow> (P w x \<and> P w y))"
    by (rule common_part_fusion)
  thus "x \<otimes> y = (\<sigma> v. P v x \<and> P v y)" by (rule product_intro)
qed

lemma disjoint_fusion:
  "\<exists>w. \<not> O w x \<Longrightarrow> (\<forall>w. P w (\<sigma> z. \<not> O z x) \<longleftrightarrow> \<not> O w x)"
proof -
  assume antecedent: "\<exists>w. \<not> O w x"
  hence "\<forall>y. O y (\<sigma> v. \<not> O v x) \<longleftrightarrow> (\<exists>v. \<not> O v x \<and> O y v)"
    by (rule fusion_character)
  hence x: "O x (\<sigma> v. \<not> O v x) \<longleftrightarrow> (\<exists>v. \<not> O v x \<and> O x v)"..
  show "\<forall>w. P w (\<sigma> z. \<not> O z x) \<longleftrightarrow> \<not> O w x"
  proof
    fix y
    show "P y (\<sigma> z. \<not> O z x) \<longleftrightarrow> \<not> O y x"
    proof
      assume "P y (\<sigma> z. \<not> O z x)"
      moreover have "\<not> O x (\<sigma> z. \<not> O z x)"
      proof
        assume "O x (\<sigma> z. \<not> O z x)"
        with x have "(\<exists>v. \<not> O v x \<and> O x v)"..
        then obtain v where v: "\<not> O v x \<and> O x v"..
        hence "\<not> O v x"..
        from v have "O x v"..
        hence "O v x" by (rule overlap_symmetry)
        with `\<not> O v x` show "False"..
      qed
      ultimately have "\<not> O x y"
        by (rule disjoint_demonotonicity)
      thus "\<not> O y x" by (rule disjoint_symmetry)
    next
      assume "\<not> O y x"
      thus "P y (\<sigma> v. \<not> O v x)"
        by (rule fusion_part)
    qed
  qed
qed

theorem complement_closure: 
  "\<exists>w. \<not> O w x \<Longrightarrow> (\<exists>z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)"
proof -
  assume "(\<exists>w. \<not> O w x)"
  hence "\<forall>w. P w (\<sigma> z. \<not> O z x) \<longleftrightarrow> \<not> O w x"
    by (rule disjoint_fusion)
  thus "\<exists>z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x"..
qed

end

sublocale GEM \<subseteq> CEMC
proof
  fix x y
  show "\<midarrow> x = (THE z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)" 
    using complement_eq.
  show "(\<exists>w. \<not> O w x) \<Longrightarrow> (\<exists>z. \<forall>w. P w z = (\<not> O w x))" 
    using complement_closure.
  show "x \<ominus> y = (THE z. \<forall>w. P w z = (P w x \<and> \<not> O w y))" 
    using difference_eq.
  show "u = (THE x. \<forall>y. P y x)"
    using universe_eq.
qed

context GEM
begin

corollary complement_is_disjoint_fusion: 
  "\<exists>w. \<not> O w x \<Longrightarrow> \<midarrow> x = (\<sigma> z. \<not> O z x)"
proof -
  assume "\<exists>w. \<not> O w x"
  hence "\<forall>w. P w (\<sigma> z. \<not> O z x) \<longleftrightarrow> \<not> O w x"
    by (rule disjoint_fusion)
  thus "\<midarrow> x = (\<sigma> z. \<not> O z x)"
    by (rule complement_intro)
qed

theorem strong_fusion: "\<exists>x. F x \<Longrightarrow>
  \<exists>x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))"
proof -
  assume "\<exists>x. F x"
  have "(\<forall>y. F y \<longrightarrow> P y (\<sigma> v. F v)) \<and>
     (\<forall>y. P y (\<sigma> v. F v) \<longrightarrow> (\<exists>z. F z \<and> O y z))"
  proof
    show "\<forall>y. F y \<longrightarrow> P y (\<sigma> v. F v)"
    proof
      fix y
      show "F y \<longrightarrow> P y (\<sigma> v. F v)"
      proof
        assume "F y"
        thus "P y (\<sigma> v. F v)"
          by (rule fusion_part)
      qed
    qed
  next
    have "(\<forall>y. P y (\<sigma> v. F v) \<longleftrightarrow> 
      (\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v)))"
      using `\<exists>x. F x` by (rule fusion_part_character)
    hence "P (\<sigma> v. F v) (\<sigma> v. F v) \<longleftrightarrow> (\<forall>w. P w (\<sigma> v. F v) \<longrightarrow> 
      (\<exists>v. F v \<and> O w v))"..
    thus "\<forall>w. P w (\<sigma> v. F v) \<longrightarrow> (\<exists>v. F v \<and> O w v)" using part_reflexivity..
  qed
  thus ?thesis..
qed

theorem strong_fusion_eq: "\<exists>x. F x \<Longrightarrow> (\<sigma> x. F x) = 
  (THE x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)))"
proof -
  assume "\<exists>x. F x"
  have "(THE x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))) = (\<sigma> x. F x)" 
  proof (rule the_equality)
    show "(\<forall>y. F y \<longrightarrow> P y (\<sigma> x. F x)) \<and> (\<forall>y. P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z))"
    proof
      show "\<forall>y. F y \<longrightarrow> P y (\<sigma> x. F x)"
      proof
        fix y
        show "F y \<longrightarrow> P y (\<sigma> x. F x)"
        proof
          assume "F y"
          thus "P y (\<sigma> x. F x)"
            by (rule fusion_part)
        qed
      qed
    next
      show "(\<forall>y. P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z))"
      proof
        fix y
        show "P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z)"
        proof
          have  "\<forall>y. P y (\<sigma> v. F v) \<longleftrightarrow> (\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v))"
            using `\<exists>x. F x` by (rule fusion_part_character)
          hence "P y (\<sigma> v. F v) \<longleftrightarrow> (\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v))"..
          moreover assume "P y (\<sigma> x. F x)"
          ultimately have "\<forall>w. P w y \<longrightarrow> (\<exists>v. F v \<and> O w v)"..
          hence "P y y \<longrightarrow> (\<exists>v. F v \<and> O y v)"..
          thus "\<exists>v. F v \<and> O y v" using part_reflexivity..
        qed
      qed
    qed
  next
    fix x
    assume x: "(\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))"
    have "\<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z)"
    proof
      fix y
      show "O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z)"
      proof
        assume "O y x"
        with overlap_eq have "\<exists>v. P v y \<and> P v x"..
        then obtain v where v: "P v y \<and> P v x"..
        from x have "\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)"..
        hence "P v x \<longrightarrow> (\<exists>z. F z \<and> O v z)"..
        moreover from v have "P v x"..
        ultimately have "\<exists>z. F z \<and> O v z"..
        then obtain z where z: "F z \<and> O v z"..
        hence "F z"..
        from v have "P v y"..
        moreover from z have "O v z"..
        hence "O z v" by (rule overlap_symmetry)
        ultimately have "O z y" by (rule overlap_monotonicity)
        hence "O y z" by (rule overlap_symmetry)
        with `F z` have "F z \<and> O y z"..
        thus "\<exists>z. F z \<and> O y z"..
      next
        assume "\<exists>z. F z \<and> O y z"
        then obtain z where z: "F z \<and> O y z"..
        from x have "\<forall>y. F y \<longrightarrow> P y x"..
        hence "F z \<longrightarrow> P z x"..
        moreover from z have "F z"..
        ultimately have "P z x"..
        moreover from z have "O y z"..
        ultimately show "O y x"
          by (rule overlap_monotonicity)
      qed
    qed
    hence "(\<sigma> x. F x) = x"
      by (rule fusion_intro)
    thus "x = (\<sigma> x. F x)"..
  qed
  thus ?thesis..
qed

lemma strong_sum_eq: "x \<oplus> y = (THE z. (P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y))"
proof -
  have "(THE z. (P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)) = x \<oplus> y"
  proof (rule the_equality)
    show "(P x (x \<oplus> y) \<and> P y (x \<oplus> y)) \<and> (\<forall>w. P w (x \<oplus> y) \<longrightarrow> O w x \<or> O w y)"
    proof
      show "P x (x \<oplus> y) \<and> P y (x \<oplus> y)"
        proof
          show "P x (x \<oplus> y)" using first_summand_in_sum.
          show "P y (x \<oplus> y)" using second_summand_in_sum.
        qed
      show "\<forall>w. P w (x \<oplus> y) \<longrightarrow> O w x \<or> O w y"
      proof
        fix w
        show "P w (x \<oplus> y) \<longrightarrow> O w x \<or> O w y"
        proof
          assume "P w (x \<oplus> y)"
          hence "O w (x \<oplus> y)" by (rule part_implies_overlap)
          with sum_overlap show "O w x \<or> O w y"..
        qed
      qed
    qed
    fix z
    assume z: "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)"
    hence "P x z \<and> P y z"..
    have "\<forall>w. O w z \<longleftrightarrow> (O w x \<or> O w y)"
    proof
      fix w
      show "O w z \<longleftrightarrow> (O w x \<or> O w y)"
      proof
        assume "O w z"
        with overlap_eq have "\<exists>v. P v w \<and> P v z"..
        then obtain v where v: "P v w \<and> P v z"..
        hence "P v w"..
        from z have "\<forall>w. P w z \<longrightarrow> O w x \<or> O w y"..
        hence "P v z \<longrightarrow> O v x \<or> O v y"..
        moreover from v have "P v z"..
        ultimately have "O v x \<or> O v y"..
        thus "O w x \<or> O w y"
        proof
          assume "O v x"
          hence "O x v" by (rule overlap_symmetry)
          with `P v w` have "O x w" by (rule overlap_monotonicity)
          hence "O w x" by (rule overlap_symmetry)
          thus "O w x \<or> O w y"..
        next
          assume "O v y"
          hence "O y v" by (rule overlap_symmetry)
          with `P v w` have "O y w" by (rule overlap_monotonicity)
          hence "O w y" by (rule overlap_symmetry)
          thus "O w x \<or> O w y"..
        qed
      next
        assume "O w x \<or> O w y"
        thus "O w z"
        proof
          from `P x z \<and> P y z` have "P x z"..
          moreover assume "O w x"
          ultimately show "O w z"
            by (rule overlap_monotonicity)
        next
          from `P x z \<and> P y z` have "P y z"..
          moreover assume "O w y"
          ultimately show "O w z"
            by (rule overlap_monotonicity)
        qed
      qed
    qed
    hence "x \<oplus> y = z" by (rule sum_intro)
    thus "z = x \<oplus> y"..
  qed
  thus ?thesis..
qed

subsection \<open> General Products \<close>

lemma general_product_intro: "(\<forall>y. O y x \<longleftrightarrow> (\<exists>z. (\<forall>y. F y \<longrightarrow> P z y) \<and> O y z)) \<Longrightarrow> (\<pi> x. F x) = x"
proof -
  assume "\<forall>y. O y x \<longleftrightarrow> (\<exists>z. (\<forall>y. F y \<longrightarrow> P z y) \<and> O y z)"
  hence "(\<sigma> x. \<forall>y. F y \<longrightarrow> P x y) = x" by (rule fusion_intro)
  with general_product_eq show "(\<pi> x. F x) = x" by (rule ssubst)
qed

lemma general_product_idempotence: "(\<pi> z. z = x) = x"
proof -
  have "\<forall>y. O y x \<longleftrightarrow> (\<exists>z. (\<forall>y. y = x \<longrightarrow> P z y) \<and> O y z)"
    by (meson overlap_eq part_reflexivity part_transitivity)
  thus "(\<pi> z. z = x) = x" by (rule general_product_intro)
qed

lemma general_product_absorption: "(\<pi> z. P x z) = x"
proof -
  have "\<forall>y. O y x \<longleftrightarrow> (\<exists>z. (\<forall>y. P x y \<longrightarrow> P z y) \<and> O y z)"
    by (meson overlap_eq part_reflexivity part_transitivity)
  thus "(\<pi> z. P x z) = x" by (rule general_product_intro)
qed

lemma general_product_character: "\<exists>z. \<forall>y. F y \<longrightarrow> P z y \<Longrightarrow> 
  \<forall>y. O y (\<pi> x. F x) \<longleftrightarrow> (\<exists>z. (\<forall>y. F y \<longrightarrow> P z y) \<and> O y z)"
proof -
  assume "(\<exists>z. \<forall>y. F y \<longrightarrow> P z y)"
  hence "(\<exists>x. \<forall>y. O y x \<longleftrightarrow> (\<exists>z. (\<forall>y. F y \<longrightarrow> P z y) \<and> O y z))"
    by (rule fusion)
  then obtain x where x: 
    "\<forall>y. O y x \<longleftrightarrow> (\<exists>z. (\<forall>y. F y \<longrightarrow> P z y) \<and> O y z)"..
  hence "(\<pi> x. F x) = x" by (rule general_product_intro)
  thus "(\<forall>y. O y (\<pi> x. F x) \<longleftrightarrow> (\<exists>z. (\<forall>y. F y \<longrightarrow> P z y) \<and> O y z))"
    using x by (rule ssubst)
qed

corollary "\<not> (\<exists>x. F x) \<Longrightarrow> u = (\<pi> x. F x)"
proof -
  assume antecedent: "\<not> (\<exists>x. F x)"
  have "\<forall>y. P y (\<pi> x. F x)"
  proof
    fix y
    show "P y (\<pi> x. F x)"
    proof (rule ccontr)
      assume "\<not> P y (\<pi> x. F x)"
     hence "\<exists>z. P z y \<and> \<not> O z (\<pi> x. F x)" by (rule strong_supplementation)
      then obtain z where z: "P z y \<and> \<not> O z (\<pi> x. F x)"..
      hence "\<not> O z (\<pi> x. F x)"..
      from antecedent have bla: "\<forall> y. F y \<longrightarrow> P z y" by simp 
      hence "\<exists> v. \<forall> y. F y \<longrightarrow> P v y"..
      hence "(\<forall>y. O y (\<pi> x. F x) \<longleftrightarrow> (\<exists>z. (\<forall>y. F y \<longrightarrow> P z y) \<and> O y z))" by (rule general_product_character)
      hence "O z (\<pi> x. F x) \<longleftrightarrow> (\<exists>v. (\<forall>y. F y \<longrightarrow> P v y) \<and> O z v)"..
      moreover from bla have  "(\<forall> y. F y \<longrightarrow> P z y) \<and> O z z" 
        using overlap_reflexivity..
      hence "\<exists> v. (\<forall> y. F y \<longrightarrow> P v y) \<and> O z v"..
      ultimately have "O z (\<pi> x. F x)"..
      with `\<not> O z (\<pi> x. F x)` show "False"..
    qed
  qed
  thus "u = (\<pi> x. F x)"
    by (rule universe_intro)
qed

end

subsection \<open> Strong Fusion \<close>

text \<open> An alternative axiomatization of general extensional mereology adds a stronger version of the
fusion axiom to minimal mereology, with correspondingly stronger definitions of sums and general
sums.\footnote{See @{cite "tarski_foundations_1983"} p. 25. The proofs in this section are adapted
from @{cite "hovda_what_2009"}.} \<close>

locale GEM1 = MM + 
  assumes strong_fusion: "\<exists>x. F x \<Longrightarrow> \<exists>x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))"
  assumes strong_sum_eq: "x \<oplus> y = (THE z. (P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y))"
  assumes product_eq: 
    "x \<otimes> y = (THE z. \<forall>v. P v z \<longleftrightarrow> P v x \<and> P v y)"
  assumes difference_eq: 
    "x \<ominus> y = (THE z. \<forall>w. P w z = (P w x \<and> \<not> O w y))"
  assumes complement_eq: "\<midarrow> x = (THE z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)"
  assumes universe_eq: "u = (THE x. \<forall>y. P y x)"
  assumes strong_fusion_eq:  "\<exists>x. F x \<Longrightarrow> (\<sigma> x. F x) = (THE x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)))"
  assumes general_product_eq: "(\<pi> x. F x) = (\<sigma> x. \<forall>y. F y \<longrightarrow> P x y)"
begin

theorem fusion: 
  "\<exists>x. \<phi> x \<Longrightarrow> (\<exists>z. \<forall>y. O y z \<longleftrightarrow> (\<exists>x. \<phi> x \<and> O y x))"
proof -
  assume "\<exists>x. \<phi> x"
  hence "\<exists>x. (\<forall>y. \<phi> y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. \<phi> z \<and> O y z))" by (rule strong_fusion)
  then obtain x where x: 
    "(\<forall>y. \<phi> y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. \<phi> z \<and> O y z))"..
  have "\<forall>y. O y x \<longleftrightarrow> (\<exists>v. \<phi> v \<and> O y v)"
  proof
    fix y
    show "O y x \<longleftrightarrow> (\<exists>v. \<phi> v \<and> O y v)"
    proof
      assume "O y x"
      with overlap_eq have "\<exists>z. P z y \<and> P z x"..
      then obtain z where z: "P z y \<and> P z x"..
      hence "P z x"..
      from x have "\<forall>y. P y x \<longrightarrow> (\<exists>v. \<phi> v \<and> O y v)"..
      hence "P z x \<longrightarrow> (\<exists>v. \<phi> v \<and> O z v)"..
      hence "\<exists>v. \<phi> v \<and> O z v" using `P z x`..
      then obtain v where v: "\<phi> v \<and> O z v"..
      hence "O z v"..
      with overlap_eq have "\<exists>w. P w z \<and> P w v"..
      then obtain w where w: "P w z \<and> P w v"..
      hence "P w z"..
      moreover from z have "P z y"..
      ultimately have "P w y"
        by (rule part_transitivity)
      moreover from w have "P w v"..
      ultimately have "P w y \<and> P w v"..
      hence "\<exists>w. P w y \<and> P w v"..
      with overlap_eq have "O y v"..
      from v have "\<phi> v"..
      hence "\<phi> v \<and> O y v" using `O y v`..
      thus "\<exists>v. \<phi> v \<and> O y v"..
    next
      assume "\<exists>v. \<phi> v \<and> O y v"
      then obtain v where v: "\<phi> v \<and> O y v"..
      hence "O y v"..
      with overlap_eq have "\<exists>z. P z y \<and> P z v"..
      then obtain z where z: "P z y \<and> P z v"..
      hence "P z v"..
      from x have "\<forall>y. \<phi> y \<longrightarrow> P y x"..
      hence "\<phi> v \<longrightarrow> P v x"..
      moreover from v have "\<phi> v"..
      ultimately have "P v x"..
      with `P z v` have "P z x"
        by (rule part_transitivity)
      from z have "P z y"..
      thus "O y x" using `P z x`
        by (rule overlap_intro)
    qed
  qed
  thus "(\<exists>z. \<forall>y. O y z \<longleftrightarrow> (\<exists>x. \<phi> x \<and> O y x))"..
qed

lemma pair: "\<exists>v. (\<forall>w. (w = x \<or> w = y) \<longrightarrow> P w v) \<and> (\<forall>w. P w v \<longrightarrow> (\<exists>z. (z = x \<or> z = y) \<and> O w z))"
proof -
  have "x = x"..
  hence "x = x \<or> x = y"..
  hence "\<exists>v. v = x \<or> v = y"..
  thus ?thesis
    by (rule strong_fusion)
qed

lemma or_id: "(v = x \<or> v = y) \<and> O w v \<Longrightarrow> O w x \<or> O w y"
proof -
  assume v: "(v = x \<or> v = y) \<and> O w v"
  hence "O w v"..
  from v have "v = x \<or> v = y"..
  thus "O w x \<or> O w y"
  proof
    assume "v = x"
    hence "O w x" using `O w v` by (rule subst)
    thus "O w x \<or> O w y"..
  next
    assume "v = y"
    hence "O w y" using `O w v` by (rule subst)
    thus "O w x \<or> O w y"..
  qed
qed

lemma strong_sum_closure: 
  "\<exists>z. (P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)"
proof -
  from pair obtain z where z: "(\<forall>w. (w = x \<or> w = y) \<longrightarrow> P w z) \<and> (\<forall>w. P w z \<longrightarrow> (\<exists>v. (v = x \<or> v = y) \<and> O w v))"..
  have "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)"
  proof
    from z have allw: "\<forall>w. (w = x \<or> w = y) \<longrightarrow> P w z"..
    hence "x = x \<or> x = y \<longrightarrow> P x z"..
    moreover have "x = x \<or> x = y" using refl..
    ultimately have "P x z"..
    from allw have "y = x \<or> y = y \<longrightarrow> P y z"..
    moreover have "y = x \<or> y = y" using refl..
    ultimately have "P y z"..
    with `P x z` show "P x z \<and> P y z"..
  next
    show "\<forall>w. P w z \<longrightarrow> O w x \<or> O w y"
    proof
      fix w
      show "P w z \<longrightarrow> O w x \<or> O w y"
      proof
        assume "P w z"
        from z have "\<forall>w. P w z \<longrightarrow> (\<exists>v. (v = x \<or> v = y) \<and> O w v)"..
        hence "P w z \<longrightarrow> (\<exists>v. (v = x \<or> v = y) \<and> O w v)"..
        hence "\<exists>v. (v = x \<or> v = y) \<and> O w v" using `P w z`..
        then obtain v where v: "(v = x \<or> v = y) \<and> O w v"..
        thus "O w x \<or> O w y" by (rule or_id)
      qed
    qed
  qed
  thus ?thesis..
qed

end 

sublocale GEM1 \<subseteq> GMM
proof
  fix x y \<phi>
  show "(\<exists>x. \<phi> x) \<Longrightarrow> (\<exists>z. \<forall>y. O y z \<longleftrightarrow> (\<exists>x. \<phi> x \<and> O y x))" using fusion.
qed

context GEM1
begin

lemma least_upper_bound:
  assumes sf: 
    "((\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)))"
  shows lub: 
      "(\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>z. (\<forall>y. F y \<longrightarrow> P y z) \<longrightarrow> P x z)"
proof
 from sf show "\<forall>y. F y \<longrightarrow> P y x"..
next
 show "(\<forall>z. (\<forall>y. F y \<longrightarrow> P y z) \<longrightarrow> P x z)"
 proof
  fix z
  show "(\<forall>y. F y \<longrightarrow> P y z) \<longrightarrow> P x z"
  proof
   assume z: "\<forall>y. F y \<longrightarrow> P y z"
   from pair obtain v where v: "(\<forall>w. (w = x \<or> w = z) \<longrightarrow> P w v) \<and> (\<forall>w. P w v \<longrightarrow> (\<exists>y. (y = x \<or> y = z) \<and> O w y))"..
   hence left: "(\<forall>w. (w = x \<or> w = z) \<longrightarrow> P w v)"..
   hence "(x = x \<or> x = z) \<longrightarrow> P x v"..
   moreover have "x = x \<or> x = z" using refl..
   ultimately have "P x v"..
   have "z = v"
   proof (rule ccontr)
    assume "z \<noteq> v"
    from left have "z = x \<or> z = z \<longrightarrow> P z v"..
    moreover have "z = x \<or> z = z" using refl..
    ultimately have "P z v"..
    hence "P z v \<and> z \<noteq> v" using `z \<noteq> v`..
    with nip_eq have "PP z v"..
    hence "\<exists>w. P w v \<and> \<not> O w z" by (rule weak_supplementation)
    then obtain w where w: "P w v \<and> \<not> O w z"..
    hence "P w v"..
    from v have right: 
      "\<forall>w. P w v \<longrightarrow> (\<exists>y. (y = x \<or> y = z) \<and> O w y)"..
    hence "P w v \<longrightarrow> (\<exists>y. (y = x \<or> y = z) \<and> O w y)"..
    hence "\<exists>y. (y = x \<or> y = z) \<and> O w y" using `P w v`..
    then obtain s where s: "(s = x \<or> s = z) \<and> O w s"..
    hence "s = x \<or> s = z"..
    thus "False"
    proof
     assume "s = x"
     moreover from s have "O w s"..
     ultimately have "O w x" by (rule subst)
     with overlap_eq have "\<exists>t. P t w \<and> P t x"..
     then obtain t where t: "P t w \<and> P t x"..
     hence "P t x"..
     from sf have "(\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))"..
     hence "P t x \<longrightarrow> (\<exists>z. F z \<and> O t z)"..
     hence "\<exists>z. F z \<and> O t z" using `P t x`..
     then obtain a where a: "F a \<and> O t a"..
     hence "F a"..
     from sf have ub: "\<forall>y. F y \<longrightarrow> P y x"..
     hence "F a \<longrightarrow> P a x"..
     hence "P a x" using `F a`..
     moreover from a have "O t a"..
     ultimately have "O t x"
      by (rule overlap_monotonicity)
     from t have "P t w"..
     moreover have "O z t"
     proof -
      from z have "F a \<longrightarrow> P a z"..
      moreover from a have "F a"..
      ultimately have "P a z"..
      moreover from a have "O t a"..
      ultimately have "O t z"
       by (rule overlap_monotonicity)
      thus "O z t" by (rule overlap_symmetry)
     qed
     ultimately have "O z w"
      by (rule overlap_monotonicity)
     hence "O w z" by (rule overlap_symmetry)
     from w have "\<not> O w z"..
     thus "False" using `O w z`..
    next
     assume "s = z"
     moreover from s have "O w s"..
     ultimately have "O w z" by (rule subst)
     from w have "\<not> O w z"..
     thus "False" using `O w z`..
    qed
   qed
   thus "P x z" using `P x v` by (rule ssubst)
  qed
 qed
qed

corollary strong_fusion_intro:  "(\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)) \<Longrightarrow> (\<sigma> x. F x) = x"
proof -
  assume antecedent: "(\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))"
  with least_upper_bound have lubx: 
    "(\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>z. (\<forall>y. F y \<longrightarrow> P y z) \<longrightarrow> P x z)".
  from antecedent have "\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)"..
  hence "P x x \<longrightarrow> (\<exists>z. F z \<and> O x z)"..
  hence "\<exists>z. F z \<and> O x z" using part_reflexivity..
  then obtain z where z: "F z \<and> O x z"..
  hence "F z"..
  hence "\<exists>z. F z"..
  hence "(\<sigma> x. F x) = (THE x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)))" by (rule strong_fusion_eq)
  moreover have "(THE x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))) = x"
  proof (rule the_equality)
    show "(\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))"
      using antecedent.
  next
    fix w
    assume w: 
      "(\<forall>y. F y \<longrightarrow> P y w) \<and> (\<forall>y. P y w \<longrightarrow> (\<exists>z. F z \<and> O y z))"
    with least_upper_bound have lubw:
      "(\<forall>y. F y \<longrightarrow> P y w) \<and> (\<forall>z. (\<forall>y. F y \<longrightarrow> P y z) \<longrightarrow> P w z)".
    hence "(\<forall>z. (\<forall>y. F y \<longrightarrow> P y z) \<longrightarrow> P w z)"..
    hence "(\<forall>y. F y \<longrightarrow> P y x) \<longrightarrow> P w x"..
    moreover from antecedent have "\<forall>y. F y \<longrightarrow> P y x"..
    ultimately have "P w x"..
    from lubx have "(\<forall>z. (\<forall>y. F y \<longrightarrow> P y z) \<longrightarrow> P x z)"..
    hence "(\<forall>y. F y \<longrightarrow> P y w) \<longrightarrow> P x w"..
    moreover from lubw have "(\<forall>y. F y \<longrightarrow> P y w)"..
    ultimately have "P x w"..
    with `P w x` show "w = x"
      by (rule part_antisymmetry)
  qed
  ultimately show "(\<sigma> x. F x) = x" by (rule ssubst)
qed

lemma strong_fusion_character: "\<exists>x. F x \<Longrightarrow> ((\<forall>y. F y \<longrightarrow> P y (\<sigma> x. F x)) \<and> (\<forall>y. P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z)))"
proof -
  assume "\<exists>x. F x"
  hence "(\<exists>x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)))" by (rule strong_fusion)
  then obtain x where x: 
    "(\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))"..
  hence "(\<sigma> x. F x) = x" by (rule strong_fusion_intro)
  thus ?thesis using x by (rule ssubst)
qed

lemma F_in: "\<exists>x. F x \<Longrightarrow> (\<forall>y. F y \<longrightarrow> P y (\<sigma> x. F x))"
proof -
  assume "\<exists>x. F x"
  hence "((\<forall>y. F y \<longrightarrow> P y (\<sigma> x. F x)) \<and> (\<forall>y. P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z)))" by (rule strong_fusion_character)
 thus "\<forall>y. F y \<longrightarrow> P y (\<sigma> x. F x)"..
qed

lemma parts_overlap_Fs:
  "\<exists>x. F x \<Longrightarrow> (\<forall>y. P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z))"
proof -
  assume "\<exists>x. F x"
  hence "((\<forall>y. F y \<longrightarrow> P y (\<sigma> x. F x)) \<and> (\<forall>y. P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z)))" by (rule strong_fusion_character)
  thus "(\<forall>y. P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z))"..
qed

lemma in_strong_fusion: "P z (\<sigma> x. z = x)"
proof -
  have "\<exists>y. z = y" using refl..
  hence "\<forall>y. z = y \<longrightarrow> P y (\<sigma> x. z = x)"
    by (rule F_in)
  hence "z = z \<longrightarrow> P z (\<sigma> x. z = x)"..
  thus "P z (\<sigma> x. z = x)" using refl..
qed

lemma strong_fusion_in: "P (\<sigma> x. z = x) z"
proof -
  have "\<exists>y. z = y" using refl..
  hence sf:
    "(\<forall>y. z = y \<longrightarrow> P y (\<sigma> x. z = x)) \<and> (\<forall>y. P y (\<sigma> x. z = x) \<longrightarrow> (\<exists>v. z = v \<and> O y v))"
    by (rule strong_fusion_character)
  with least_upper_bound have lub: "(\<forall>y. z = y \<longrightarrow> P y (\<sigma> x. z = x)) \<and> (\<forall>v. (\<forall>y. z = y \<longrightarrow> P y v) \<longrightarrow> P (\<sigma> x. z = x) v)".
  hence "(\<forall>v. (\<forall>y. z = y \<longrightarrow> P y v) \<longrightarrow> P (\<sigma> x. z = x) v)"..
  hence "(\<forall>y. z = y \<longrightarrow> P y z) \<longrightarrow> P (\<sigma> x. z = x) z"..
  moreover have "(\<forall>y. z = y \<longrightarrow> P y z)"
  proof
    fix y
    show "z = y \<longrightarrow> P y z"
    proof
      assume "z = y"
      thus "P y z" using part_reflexivity by (rule subst)
    qed
  qed
  ultimately show "P (\<sigma> x. z = x) z"..
qed

lemma strong_fusion_idempotence: "(\<sigma> x. z = x) = z"
 using strong_fusion_in in_strong_fusion by (rule part_antisymmetry)

subsection \<open> Strong Sums \<close>

lemma pair_fusion: "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y) \<longrightarrow> (\<sigma> z. z = x \<or> z = y) = z"
proof
 assume z: "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)"
  have "(\<forall>v. v = x \<or> v = y \<longrightarrow> P v z) \<and> (\<forall>v. P v z \<longrightarrow> (\<exists>z. (z = x \<or> z = y) \<and> O v z))"
 proof
  show "\<forall>v. v = x \<or> v = y \<longrightarrow> P v z"
  proof
   fix w
   from z have "P x z \<and> P y z"..
   show "w = x \<or> w = y \<longrightarrow> P w z"
   proof
    assume "w = x \<or> w = y"
    thus "P w z"
    proof
     assume "w = x"
     moreover from `P x z \<and> P y z` have "P x z"..
     ultimately show "P w z" by (rule ssubst)
    next
     assume "w = y"
     moreover from `P x z \<and> P y z` have "P y z"..
     ultimately show "P w z" by (rule ssubst)
    qed
   qed
  qed
  show "\<forall>v. P v z \<longrightarrow> (\<exists>z. (z = x \<or> z = y) \<and> O v z)"
  proof
   fix v
   show "P v z \<longrightarrow> (\<exists>z. (z = x \<or> z = y) \<and> O v z)"
   proof
    assume "P v z"
    from z have "\<forall>w. P w z \<longrightarrow> O w x \<or> O w y"..
    hence "P v z \<longrightarrow> O v x \<or> O v y"..
    hence "O v x \<or> O v y" using `P v z`..
    thus "\<exists>z. (z = x \<or> z = y) \<and> O v z"
    proof
     assume "O v x"
     have "x = x \<or> x = y" using refl.. 
     hence "(x = x \<or> x = y) \<and> O v x" using `O v x`..
     thus "\<exists>z. (z = x \<or> z = y) \<and> O v z"..
    next
     assume "O v y"
     have "y = x \<or> y = y" using refl..
     hence "(y = x \<or> y = y) \<and> O v y" using `O v y`..
     thus "\<exists>z. (z = x \<or> z = y) \<and> O v z"..
    qed
   qed
  qed
 qed
  thus "(\<sigma> z. z = x \<or> z = y) = z"
    by (rule strong_fusion_intro)
qed

corollary strong_sum_fusion: "x \<oplus> y = (\<sigma> z. z = x \<or> z = y)"
proof -
  have "(THE z. (P x z \<and> P y z) \<and> 
    (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)) = (\<sigma> z. z = x \<or> z = y)"
  proof (rule the_equality)
    have "x = x \<or> x = y" using refl..
    hence exz: "\<exists>z. z = x \<or> z = y"..
    hence allw: "(\<forall>w. w = x \<or> w = y \<longrightarrow> P w (\<sigma> z. z = x \<or> z = y))"
      by (rule F_in)
    show "(P x (\<sigma> z. z = x \<or> z = y) \<and> P y (\<sigma> z. z = x \<or> z = y)) \<and> 
      (\<forall>w. P w (\<sigma> z. z = x \<or> z = y) \<longrightarrow> O w x \<or> O w y)"
    proof
      show "(P x (\<sigma> z. z = x \<or> z = y) \<and> P y (\<sigma> z. z = x \<or> z = y))"
      proof
        from allw have "x = x \<or> x = y \<longrightarrow> P x (\<sigma> z. z = x \<or> z = y)"..
        thus "P x (\<sigma> z. z = x \<or> z = y)" 
          using `x = x \<or> x = y`..
      next
        from allw have "y = x \<or> y = y \<longrightarrow> P y (\<sigma> z. z = x \<or> z = y)"..
        moreover have "y = x \<or> y = y" 
          using refl..
        ultimately show "P y (\<sigma> z. z = x \<or> z = y)"..
      qed
    next
      show "\<forall>w. P w (\<sigma> z. z = x \<or> z = y) \<longrightarrow> O w x \<or> O w y"
      proof
        fix w
        show "P w (\<sigma> z. z = x \<or> z = y) \<longrightarrow> O w x \<or> O w y"
        proof
          have "\<forall>v. P v (\<sigma> z. z = x \<or> z = y) \<longrightarrow> (\<exists>z. (z = x \<or> z = y) \<and> O v z)" using exz by (rule parts_overlap_Fs)
          hence "P w (\<sigma> z. z = x \<or> z = y) \<longrightarrow> (\<exists>z. (z = x \<or> z = y) \<and> O w z)"..
          moreover assume "P w (\<sigma> z. z = x \<or> z = y)"
          ultimately have "(\<exists>z. (z = x \<or> z = y) \<and> O w z)"..
          then obtain z where z: "(z = x \<or> z = y) \<and> O w z"..
          thus "O w x \<or> O w y" by (rule or_id)
        qed
      qed
    qed
  next
    fix z
    assume z: "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)"
    with pair_fusion have "(\<sigma> z. z = x \<or> z = y) = z"..
    thus "z = (\<sigma> z. z = x \<or> z = y)"..
  qed
  with strong_sum_eq show "x \<oplus> y = (\<sigma> z. z = x \<or> z = y)" 
    by (rule ssubst)
qed

corollary strong_sum_intro: 
  "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y) \<longrightarrow> x \<oplus> y = z"
proof
  assume z: "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)"
  with pair_fusion have "(\<sigma> z. z = x \<or> z = y) = z"..
  with strong_sum_fusion show "(x \<oplus> y) = z" 
    by (rule ssubst)
qed

corollary strong_sum_character: "(P x (x \<oplus> y) \<and> P y (x \<oplus> y)) \<and> (\<forall>w. P w (x \<oplus> y) \<longrightarrow> O w x \<or> O w y)"
proof -
  from strong_sum_closure obtain z where z: 
    "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)"..
 with strong_sum_intro have "x \<oplus> y = z"..
 thus ?thesis using z by (rule ssubst)
qed

corollary summands_in: "(P x (x \<oplus> y) \<and> P y (x \<oplus> y))"
  using strong_sum_character..

corollary first_summand_in: "P x (x \<oplus> y)" using summands_in..

corollary second_summand_in: "P y (x \<oplus> y)" using summands_in..

corollary sum_part_overlap: "(\<forall>w. P w (x \<oplus> y) \<longrightarrow> O w x \<or> O w y)" using strong_sum_character..

lemma strong_sum_absorption: "y = (x \<oplus> y) \<Longrightarrow> P x y"
proof -
 assume "y = (x \<oplus> y)"
 thus "P x y" using first_summand_in by (rule ssubst)
qed

theorem strong_supplementation: "\<not> P x y \<Longrightarrow> (\<exists>z. P z x \<and> \<not> O z y)"
proof -
 assume "\<not> P x y"
 have "\<not> (\<forall>z. P z x \<longrightarrow> O z y)"
 proof
  assume z: "\<forall>z. P z x \<longrightarrow> O z y"
  have "(\<forall>v. y = v \<longrightarrow> P v (x \<oplus> y)) \<and> 
    (\<forall>v. P v (x \<oplus> y) \<longrightarrow> (\<exists>z. y = z \<and> O v z))"
  proof
   show "\<forall>v. y = v \<longrightarrow> P v (x \<oplus> y)"
   proof
    fix v
    show "y = v \<longrightarrow> P v (x \<oplus> y)"
    proof
     assume "y = v"
     thus "P v (x \<oplus> y)" 
       using second_summand_in by (rule subst)
    qed
   qed
   show "\<forall>v. P v (x \<oplus> y) \<longrightarrow> (\<exists>z. y = z \<and> O v z)"
   proof
    fix v
    show "P v (x \<oplus> y) \<longrightarrow> (\<exists>z. y = z \<and> O v z)"
    proof
     assume "P v (x \<oplus> y)"
     moreover from sum_part_overlap have
       "P v (x \<oplus> y) \<longrightarrow> O v x \<or> O v y"..
     ultimately have "O v x \<or> O v y" by (rule rev_mp)
     hence "O v y"
     proof
      assume "O v x"
      with overlap_eq have "\<exists>w. P w v \<and> P w x"..
      then obtain w where w: "P w v \<and> P w x"..
      from z have "P w x \<longrightarrow> O w y"..
      moreover from w have "P w x"..
      ultimately have "O w y"..
      with overlap_eq have "\<exists>t. P t w \<and> P t y"..
      then obtain t where t: "P t w \<and> P t y"..
      hence "P t w"..
      moreover from w have "P w v"..
      ultimately have "P t v"
        by (rule part_transitivity)
      moreover from t have "P t y"..
      ultimately show "O v y"
        by (rule overlap_intro)
     next
      assume "O v y"
      thus "O v y".
     qed
     with refl have "y = y \<and> O v y"..
     thus "\<exists>z. y = z \<and> O v z"..
    qed
   qed
  qed
  hence  "(\<sigma> z. y = z) = (x \<oplus> y)" by (rule strong_fusion_intro)
  with strong_fusion_idempotence have "y = x \<oplus> y" by (rule subst)
  hence "P x y" by (rule strong_sum_absorption)
  with `\<not> P x y` show "False"..
 qed
 thus "\<exists>z. P z x \<and> \<not> O z y" by simp
qed

lemma sum_character: "\<forall>v. O v (x \<oplus> y) \<longleftrightarrow> (O v x \<or> O v y)"
proof
  fix v
  show "O v (x \<oplus> y) \<longleftrightarrow> (O v x \<or> O v y)"
  proof
    assume "O v (x \<oplus> y)"
    with overlap_eq have "\<exists>w. P w v \<and> P w (x \<oplus> y)"..
    then obtain w where w: "P w v \<and> P w (x \<oplus> y)"..
    hence "P w v"..
    have "P w (x \<oplus> y) \<longrightarrow> O w x \<or> O w y" using sum_part_overlap..
    moreover from w have "P w (x \<oplus> y)"..
    ultimately have "O w x \<or> O w y"..
    thus "O v x \<or> O v y"
    proof
      assume "O w x"
      hence "O x w"
        by (rule overlap_symmetry)
      with `P w v` have "O x v"
        by (rule overlap_monotonicity)
      hence "O v x"
        by (rule overlap_symmetry)
      thus "O v x \<or> O v y"..
    next
      assume "O w y"
      hence "O y w"
        by (rule overlap_symmetry)
      with `P w v` have "O y v"
        by (rule overlap_monotonicity)
      hence "O v y" by (rule overlap_symmetry)
      thus "O v x \<or> O v y"..
    qed
  next
    assume "O v x \<or> O v y"
    thus "O v (x \<oplus> y)"
    proof
      assume "O v x"
      with overlap_eq have "\<exists>w. P w v \<and> P w x"..
      then obtain w where w: "P w v \<and> P w x"..
      hence "P w v"..
      moreover from w have "P w x"..
      hence "P w (x \<oplus> y)" using first_summand_in
        by (rule part_transitivity)
      ultimately show "O v (x \<oplus> y)"
        by (rule overlap_intro)
    next
      assume "O v y"
      with overlap_eq have "\<exists>w. P w v \<and> P w y"..
      then obtain w where w: "P w v \<and> P w y"..
      hence "P w v"..
      moreover from w have "P w y"..
      hence "P w (x \<oplus> y)" using second_summand_in
        by (rule part_transitivity)
      ultimately show "O v (x \<oplus> y)"
        by (rule overlap_intro)
    qed
  qed
qed

lemma sum_eq: "x \<oplus> y = (THE z. \<forall>v. O v z = (O v x \<or> O v y))"
proof -
  have "(THE z. \<forall>v. O v z \<longleftrightarrow> (O v x \<or> O v y)) = x \<oplus> y"
  proof (rule the_equality)
    show "\<forall>v. O v (x \<oplus> y) \<longleftrightarrow> (O v x \<or> O v y)" using sum_character.
  next
    fix z
    assume z: "\<forall>v. O v z \<longleftrightarrow> (O v x \<or> O v y)"
    have "(P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y)"
    proof
      show "P x z \<and> P y z"
      proof
        show "P x z"
        proof (rule ccontr)
          assume "\<not> P x z"
          hence "\<exists>v. P v x \<and> \<not> O v z"
            by (rule strong_supplementation)
          then obtain v where v: "P v x \<and> \<not> O v z"..
          hence "\<not> O v z"..
          from z have "O v z \<longleftrightarrow> (O v x \<or> O v y)"..
          moreover from v have "P v x"..
          hence "O v x" by (rule part_implies_overlap)
          hence "O v x \<or> O v y"..
          ultimately have "O v z"..
          with `\<not> O v z` show "False"..
        qed
      next
        show "P y z"
        proof (rule ccontr)
          assume "\<not> P y z"
          hence "\<exists>v. P v y \<and> \<not> O v z"
            by (rule strong_supplementation)
          then obtain v where v: "P v y \<and> \<not> O v z"..
          hence "\<not> O v z"..
          from z have "O v z \<longleftrightarrow> (O v x \<or> O v y)"..
          moreover from v have "P v y"..
          hence "O v y" by (rule part_implies_overlap)
          hence "O v x \<or> O v y"..
          ultimately have "O v z"..
          with `\<not> O v z` show "False"..
        qed
      qed
      show "\<forall>w. P w z \<longrightarrow> (O w x \<or> O w y)"
      proof
        fix w
        show "P w z \<longrightarrow> (O w x \<or> O w y)"
        proof
          from z have "O w z \<longleftrightarrow> O w x \<or> O w y"..
          moreover assume "P w z"
          hence "O w z" by (rule part_implies_overlap)
          ultimately show "O w x \<or> O w y"..
        qed
      qed
    qed
    with strong_sum_intro have "x \<oplus> y = z"..
    thus "z = x \<oplus> y"..
  qed
  thus ?thesis..
qed

theorem fusion_eq: "\<exists>x. F x \<Longrightarrow>
  (\<sigma> x. F x) = (THE x. \<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z))"
proof -
  assume "\<exists>x. F x"
  hence bla: "\<forall>y. P y (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z)"
    by (rule parts_overlap_Fs)
  have "(THE x. \<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z)) = (\<sigma> x. F x)"
  proof (rule the_equality)
    show "\<forall>y. O y (\<sigma> x. F x) \<longleftrightarrow> (\<exists>z. F z \<and> O y z)"
    proof
      fix y
      show "O y (\<sigma> x. F x) \<longleftrightarrow> (\<exists>z. F z \<and> O y z)"
      proof
        assume "O y (\<sigma> x. F x)"
        with overlap_eq have "\<exists>v. P v y \<and> P v (\<sigma> x. F x)"..
        then obtain v where v: "P v y \<and> P v (\<sigma> x. F x)"..
        hence "P v y"..
        from bla have "P v (\<sigma> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O v z)"..
        moreover from v have "P v (\<sigma> x. F x)"..
        ultimately have "(\<exists>z. F z \<and> O v z)"..
        then obtain z where z: "F z \<and> O v z"..
        hence "F z"..
        moreover from z have "O v z"..
        hence "O z v" by (rule overlap_symmetry)
        with `P v y` have "O z y" by (rule overlap_monotonicity)
        hence "O y z" by (rule overlap_symmetry)
        ultimately have "F z \<and> O y z"..
        thus "(\<exists>z. F z \<and> O y z)"..
      next
        assume "\<exists>z. F z \<and> O y z"
        then obtain z where z: "F z \<and> O y z"..
        from`\<exists>x. F x` have "(\<forall>y. F y \<longrightarrow> P y (\<sigma> x. F x))"
          by (rule F_in)
        hence "F z \<longrightarrow>  P z (\<sigma> x. F x)"..
        moreover from z have "F z"..
        ultimately have "P z (\<sigma> x. F x)"..
        moreover from z have "O y z"..
        ultimately show "O y (\<sigma> x. F x)"
          by (rule overlap_monotonicity)
      qed
    qed
  next
    fix x
    assume x: "\<forall>y. O y x \<longleftrightarrow> (\<exists>v. F v \<and> O y v)"
    have "(\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z))"
    proof
      show "\<forall>y. F y \<longrightarrow> P y x"
      proof
        fix y
        show "F y \<longrightarrow> P y x"
        proof
          assume "F y"
          show "P y x"
          proof (rule ccontr)
            assume "\<not> P y x"
            hence "\<exists>z. P z y \<and> \<not> O z x"
              by (rule strong_supplementation)
            then obtain z where z: "P z y \<and> \<not> O z x"..
            hence "\<not> O z x"..
            from x have "O z x \<longleftrightarrow> (\<exists>v. F v \<and> O z v)"..
            moreover from z have "P z y"..
            hence "O z y" by (rule part_implies_overlap)
            with `F y` have "F y \<and> O z y"..
            hence "\<exists>y. F y \<and> O z y"..
            ultimately have "O z x"..
            with `\<not> O z x` show "False"..
          qed
        qed
      qed
      show "\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)"
      proof
        fix y
        show "P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)"
        proof
          from x have "O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z)"..
          moreover assume "P y x"
          hence "O y x" by (rule part_implies_overlap)
          ultimately show "\<exists>z. F z \<and> O y z"..
        qed
      qed
    qed
    hence "(\<sigma> x. F x) = x"
      by (rule strong_fusion_intro)
    thus "x = (\<sigma> x. F x)"..
  qed
  thus "(\<sigma> x. F x) = (THE x. \<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z))"..
qed

end

sublocale GEM1 \<subseteq> GEM
proof
  fix x y F
  show "\<not> P x y \<Longrightarrow> \<exists>z. P z x \<and> \<not> O z y" 
    using strong_supplementation.
  show "x \<oplus> y = (THE z. \<forall>v. O v z \<longleftrightarrow> (O v x \<or> O v y))" 
    using sum_eq.
  show "x \<otimes> y = (THE z. \<forall>v. P v z \<longleftrightarrow> P v x \<and> P v y)" 
    using product_eq.
  show "x \<ominus> y = (THE z. \<forall>w. P w z = (P w x \<and> \<not> O w y))" 
    using difference_eq.
  show "\<midarrow> x = (THE z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)" 
    using complement_eq.
  show "u = (THE x. \<forall>y. P y x)" 
    using universe_eq.
  show "\<exists>x. F x \<Longrightarrow> (\<sigma> x. F x) = (THE x. \<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O y z))" using fusion_eq.
  show "(\<pi> x. F x) = (\<sigma> x. \<forall>y. F y \<longrightarrow> P x y)" 
    using general_product_eq.
qed

sublocale GEM \<subseteq> GEM1
proof
  fix x y F
  show "\<exists>x. F x \<Longrightarrow> (\<exists>x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)))" using strong_fusion.
  show "\<exists>x. F x \<Longrightarrow> (\<sigma> x. F x) = (THE x. (\<forall>y. F y \<longrightarrow> P y x) \<and> (\<forall>y. P y x \<longrightarrow> (\<exists>z. F z \<and> O y z)))" using strong_fusion_eq.
  show "(\<pi> x. F x) = (\<sigma> x. \<forall>y. F y \<longrightarrow> P x y)" using general_product_eq.
  show "x \<oplus> y = (THE z. (P x z \<and> P y z) \<and> (\<forall>w. P w z \<longrightarrow> O w x \<or> O w y))" using strong_sum_eq.
  show "x \<otimes> y = (THE z. \<forall>v. P v z \<longleftrightarrow> P v x \<and> P v y)" 
    using product_eq.
  show "x \<ominus> y = (THE z. \<forall>w. P w z = (P w x \<and> \<not> O w y))" 
    using difference_eq.
  show "\<midarrow> x = (THE z. \<forall>w. P w z \<longleftrightarrow> \<not> O w x)" using complement_eq.
  show "u = (THE x. \<forall>y. P y x)" using universe_eq.
qed

(*<*) end (*>*)