section \<open> Extensional Mereology \<close>

(*<*)
theory EM
  imports MM
begin
(*>*)

text \<open> Extensional mereology adds to ground mereology the axiom of strong supplementation.\footnote{
See @{cite "simons_parts:_1987"} p. 29, @{cite "varzi_parts_1996"} p. 262 and @{cite "casati_parts_1999"} 
p. 39-40.} \<close>

locale EM = M +
  assumes strong_supplementation: 
    "\<not> P x y \<Longrightarrow> (\<exists>z. P z x \<and> \<not> O z y)"
begin

text \<open> Strong supplementation entails weak supplementation.\footnote{See @{cite "simons_parts:_1987"}
p. 29 and @{cite "casati_parts_1999"} p. 40.} \<close>

lemma weak_supplementation: "PP x y \<Longrightarrow> (\<exists>z. P z y \<and> \<not> O z x)"
proof -
  assume "PP x y"
  hence "\<not> P y x" by (rule proper_implies_not_part)
  thus "\<exists>z. P z y \<and> \<not> O z x" by (rule strong_supplementation)
qed

end

text \<open> So minimal mereology is a subtheory of extensional mereology.\footnote{@{cite "casati_parts_1999"} p. 40.} \<close>

sublocale EM \<subseteq> MM
proof
  fix y x
  show "PP y x \<Longrightarrow> \<exists>z. P z x \<and> \<not> O z y" using weak_supplementation.
qed

text \<open> Strong supplementation also entails the proper parts principle.\footnote{See @{cite "simons_parts:_1987"}
pp. 28-9 and @{cite "varzi_parts_1996"} p. 263.} \<close>

context EM
begin

lemma proper_parts_principle:
"(\<exists>z. PP z x) \<Longrightarrow> (\<forall>z. PP z x \<longrightarrow> P z y) \<Longrightarrow> P x y"
proof -
  assume "\<exists>z. PP z x"
  then obtain v where v: "PP v x"..
  hence "P v x" by (rule proper_implies_part)
  assume antecedent: "\<forall>z. PP z x \<longrightarrow> P z y"
  hence "PP v x \<longrightarrow> P v y"..
  hence "P v y" using `PP v x`..
  with `P v x` have "P v x \<and> P v y"..
  hence "\<exists>v. P v x \<and> P v y"..
  with overlap_eq have "O x y"..
  show "P x y"
  proof (rule ccontr)
    assume "\<not> P x y"
    hence "\<exists>z. P z x \<and> \<not> O z y"
      by (rule strong_supplementation)
    then obtain z where z: "P z x \<and> \<not> O z y"..
    hence "P z x"..
    moreover have "z \<noteq> x"
    proof
      assume "z = x"
      moreover from z have "\<not> O z y"..
      ultimately have "\<not> O x y" by (rule subst)
      thus "False"  using `O x y`..
    qed
    ultimately have "P z x \<and> z \<noteq> x"..
    with nip_eq have "PP z x"..
    from antecedent have "PP z x \<longrightarrow> P z y"..
    hence "P z y" using `PP z x`..
    hence "O z y" by (rule part_implies_overlap)
    from z have "\<not> O z y"..
    thus "False" using `O z y`..
  qed
qed

text \<open> Which with antisymmetry entails the extensionality of proper parthood.\footnote{See
@{cite "simons_parts:_1987"} p. 28, @{cite "varzi_parts_1996"} p. 263 and @{cite "casati_parts_1999"}
p. 40.} \<close>

theorem proper_part_extensionality:
"(\<exists>z. PP z x \<or> PP z y) \<Longrightarrow> x = y \<longleftrightarrow> (\<forall>z. PP z x \<longleftrightarrow> PP z y)"
proof -
  assume antecedent: "\<exists>z. PP z x \<or> PP z y"
  show "x = y \<longleftrightarrow> (\<forall>z. PP z x \<longleftrightarrow> PP z y)"
  proof
    assume "x = y"
    moreover have "\<forall>z. PP z x \<longleftrightarrow> PP z x" by simp
    ultimately show "\<forall>z. PP z x \<longleftrightarrow> PP z y" by (rule subst)
  next
    assume right: "\<forall>z. PP z x \<longleftrightarrow> PP z y"
    have "\<forall>z. PP z x \<longrightarrow> P z y"
    proof
      fix z
      show "PP z x \<longrightarrow> P z y"
      proof
        assume "PP z x"
        from right have "PP z x \<longleftrightarrow> PP z y"..
        hence "PP z y" using `PP z x`..
        thus "P z y" by (rule proper_implies_part)
      qed
    qed
    have "\<forall>z. PP z y \<longrightarrow> P z x"
    proof
      fix z
      show "PP z y \<longrightarrow> P z x"
      proof
        assume "PP z y"
        from right have "PP z x \<longleftrightarrow> PP z y"..
        hence "PP z x" using `PP z y`..
        thus "P z x" by (rule proper_implies_part)
      qed
    qed
    from antecedent obtain z where z: "PP z x \<or> PP z y"..
    thus "x = y"
    proof (rule disjE)
      assume "PP z x"
      hence "\<exists>z. PP z x"..
      hence "P x y" using `\<forall>z. PP z x \<longrightarrow> P z y`
        by (rule proper_parts_principle)
      from right have "PP z x \<longleftrightarrow> PP z y"..
      hence "PP z y" using `PP z x`..
      hence "\<exists>z. PP z y"..
      hence "P y x" using `\<forall>z. PP z y \<longrightarrow> P z x`
        by (rule proper_parts_principle)
      with `P x y` show "x = y"
        by (rule part_antisymmetry)
    next
      assume "PP z y"
      hence "\<exists>z. PP z y"..
      hence "P y x" using `\<forall>z. PP z y \<longrightarrow> P z x`
        by (rule proper_parts_principle)
      from right have "PP z x \<longleftrightarrow> PP z y"..
      hence "PP z x" using `PP z y`..
      hence "\<exists>z. PP z x"..
      hence "P x y" using `\<forall>z. PP z x \<longrightarrow> P z y`
          by (rule proper_parts_principle)
      thus "x = y"
        using `P y x` by (rule part_antisymmetry)
    qed
  qed
qed

text \<open> It also follows from strong supplementation that parthood is definable in terms of overlap.\footnote{
See @{cite "parsons_many_2014"} p. 4.}  \<close>

lemma part_overlap_eq: "P x y \<longleftrightarrow> (\<forall>z. O z x \<longrightarrow> O z y)"
proof
  assume "P x y"
  show "(\<forall>z. O z x \<longrightarrow> O z y)"
  proof
    fix z
    show "O z x \<longrightarrow> O z y"
    proof
      assume "O z x"
      with `P x y` show "O z y"
        by (rule overlap_monotonicity)
    qed
  qed
next
  assume right: "\<forall>z. O z x \<longrightarrow> O z y"
  show "P x y"
  proof (rule ccontr)
    assume "\<not> P x y"
    hence "\<exists>z. P z x \<and> \<not> O z y"
      by (rule strong_supplementation)
    then obtain z where z: "P z x \<and> \<not> O z y"..
    hence "\<not> O z y"..
    from right have "O z x \<longrightarrow> O z y"..
    moreover from z have "P z x"..
    hence "O z x" by (rule part_implies_overlap)
    ultimately have "O z y"..
    with `\<not> O z y` show "False"..
  qed
qed

text \<open> Which entails the extensionality of overlap. \<close>

theorem overlap_extensionality: "x = y \<longleftrightarrow> (\<forall>z. O z x \<longleftrightarrow> O z y)"
proof
  assume "x = y"
  moreover have "\<forall>z. O z x \<longleftrightarrow> O z x"
  proof
    fix z
    show "O z x \<longleftrightarrow> O z x"..
  qed
  ultimately show "\<forall>z. O z x \<longleftrightarrow> O z y"
    by (rule subst)
next
  assume right: "\<forall>z. O z x \<longleftrightarrow> O z y"
  have "\<forall>z. O z y \<longrightarrow> O z x"
  proof
    fix z
    from right have "O z x \<longleftrightarrow> O z y"..
    thus "O z y \<longrightarrow> O z x"..
  qed
  with part_overlap_eq have "P y x"..
  have "\<forall>z. O z x \<longrightarrow> O z y"
  proof
    fix z
    from right have "O z x \<longleftrightarrow> O z y"..
    thus "O z x \<longrightarrow> O z y"..
  qed
  with part_overlap_eq have "P x y"..
  thus "x = y" 
    using `P y x` by (rule part_antisymmetry)
qed

end

(*<*) end (*>*)