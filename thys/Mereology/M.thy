section \<open> Ground Mereology \<close>

(*<*)
theory M
  imports PM
begin
(*>*)

text \<open> The theory of \emph{ground mereology} adds to premereology the antisymmetry of parthood, and
defines proper parthood as nonidentical parthood.\footnote{For this axiomatization of ground mereology see,
for example, @{cite "varzi_parts_1996"} p. 261 and @{cite "casati_parts_1999"} p. 36. For discussion of the 
antisymmetry of parthood see, for example, @{cite "cotnoir_antisymmetry_2010"}. For the definition of 
proper parthood as nonidentical parthood, see for example, @{cite "leonard_calculus_1940"} p. 47.} 
In other words, ground mereology assumes that parthood is a partial order.\<close>

locale M = PM +
  assumes part_antisymmetry: "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y"
  assumes nip_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
begin

subsection \<open> Proper Parthood \<close>

lemma proper_implies_part: "PP x y \<Longrightarrow> P x y"
proof -
  assume "PP x y"
  with nip_eq have "P x y \<and> x \<noteq> y"..
  thus "P x y"..
qed

lemma proper_implies_distinct: "PP x y \<Longrightarrow> x \<noteq> y"
proof -
  assume "PP x y"
  with nip_eq have "P x y \<and> x \<noteq> y"..
  thus "x \<noteq> y"..
qed

lemma proper_implies_not_part: "PP x y \<Longrightarrow> \<not> P y x"
proof -
  assume "PP x y"
  hence "P x y" by (rule proper_implies_part)
  show "\<not> P y x"
  proof
    from `PP x y` have "x \<noteq> y" by (rule proper_implies_distinct)
    moreover assume "P y x"
    with `P x y` have "x = y" by (rule part_antisymmetry)
    ultimately show "False"..
  qed
qed

lemma proper_part_asymmetry: "PP x y \<Longrightarrow> \<not> PP y x"
proof -
  assume "PP x y"
  hence "P x y" by (rule proper_implies_part)
  from `PP x y` have "x \<noteq> y" by (rule proper_implies_distinct)
  show "\<not> PP y x"
  proof
    assume "PP y x"
    hence "P y x" by (rule proper_implies_part)
    with `P x y` have "x = y" by (rule part_antisymmetry)
    with `x \<noteq> y` show "False"..
  qed
qed

lemma proper_implies_overlap: "PP x y \<Longrightarrow> O x y"
proof -
  assume "PP x y"
  hence "P x y" by (rule proper_implies_part)
  thus "O x y" by (rule part_implies_overlap)
qed

end

text \<open> The rest of this section compares four alternative axiomatizations of ground mereology, and
verifies their equivalence. \<close>

text \<open> The first alternative axiomatization defines proper parthood as nonmutual instead of nonidentical parthood.\footnote{
See, for example, @{cite "varzi_parts_1996"} p. 261 and @{cite "casati_parts_1999"} p. 36. For the distinction
between nonmutual and nonidentical parthood, see @{cite "parsons_many_2014"} pp. 6-8.}
In the presence of antisymmetry, the two definitions of proper parthood are equivalent.\footnote{
See @{cite "cotnoir_antisymmetry_2010"} p. 398, @{cite "donnelly_using_2011"} p. 233, 
@{cite "cotnoir_non-wellfounded_2012"} p. 191, @{cite "obojska_remarks_2013"} p. 344,
@{cite "cotnoir_does_2016"} p. 128 and @{cite "cotnoir_is_2018"}.} \<close>

locale M1 = PM +
  assumes nmp_eq: "PP x y \<longleftrightarrow> P x y \<and> \<not> P y x"
  assumes part_antisymmetry: "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y"

sublocale M \<subseteq> M1
proof
  fix x y
  show nmp_eq: "PP x y \<longleftrightarrow> P x y \<and> \<not> P y x"
  proof
    assume "PP x y"
    with nip_eq have nip: "P x y \<and> x \<noteq> y"..
    hence "x \<noteq> y"..
    from nip have "P x y"..
    moreover have "\<not> P y x"
    proof
      assume "P y x"
      with `P x y` have "x = y" by (rule part_antisymmetry)
      with `x \<noteq> y` show "False"..
    qed
    ultimately show "P x y \<and> \<not> P y x"..
  next
    assume nmp: "P x y \<and> \<not> P y x"
    hence "\<not> P y x"..
    from nmp have "P x y"..
    moreover have "x \<noteq> y"
    proof
      assume "x = y"
      hence "\<not> P y y" using `\<not> P y x` by (rule subst)
      thus "False" using part_reflexivity..
    qed
    ultimately have "P x y \<and> x \<noteq> y"..
    with nip_eq show "PP x y"..
  qed
  show  "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y" using part_antisymmetry.
qed

sublocale M1 \<subseteq> M
proof
  fix x y
  show nip_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
  proof
    assume "PP x y"
    with nmp_eq have nmp: "P x y \<and> \<not> P y x"..
    hence "\<not> P y x"..
    from nmp have "P x y"..
    moreover have "x \<noteq> y"
    proof
      assume "x = y"
      hence "\<not> P y y" using `\<not> P y x` by (rule subst)
      thus "False" using part_reflexivity..
    qed
    ultimately show "P x y \<and> x \<noteq> y"..
  next
    assume nip: "P x y \<and> x \<noteq> y"
    hence "x \<noteq> y"..
    from nip have "P x y"..
    moreover have "\<not> P y x"
    proof
      assume "P y x"
      with `P x y` have "x = y" by (rule part_antisymmetry)
      with `x \<noteq> y` show "False"..
    qed
    ultimately have "P x y \<and> \<not> P y x"..
    with nmp_eq show "PP x y"..
  qed
  show  "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y" using part_antisymmetry.
qed

text \<open> Conversely, assuming the two definitions of proper parthood are equivalent entails the antisymmetry
of parthood, leading to the second alternative axiomatization, which assumes both equivalencies.\footnote{
For this point see especially @{cite "parsons_many_2014"} pp. 9-10.} \<close>

locale M2 = PM +
  assumes nip_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
  assumes nmp_eq: "PP x y \<longleftrightarrow> P x y \<and> \<not> P y x"

sublocale M \<subseteq> M2
proof
  fix x y
  show "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y" using nip_eq.
  show "PP x y \<longleftrightarrow> P x y \<and> \<not> P y x" using nmp_eq.
qed

sublocale M2 \<subseteq> M
proof
  fix x y
  show "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y" using nip_eq.
  show "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y" 
  proof -
    assume "P x y"
    assume "P y x"
    show "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      with `P x y` have "P x y \<and> x \<noteq> y"..
      with nip_eq have "PP x y"..
      with nmp_eq have "P x y \<and> \<not> P y x"..
      hence "\<not> P y x"..
      thus "False" using `P y x`..
    qed
  qed
qed

text \<open> In the context of the other axioms, antisymmetry is equivalent to the extensionality of parthood, 
which gives the third alternative axiomatization.\footnote{For this point see @{cite "cotnoir_antisymmetry_2010"} p. 401 
and @{cite "cotnoir_non-wellfounded_2012"} p. 191-2.} \<close>

locale M3 = PM +
  assumes nip_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
  assumes part_extensionality: "x = y \<longleftrightarrow> (\<forall> z. P z x \<longleftrightarrow> P z y)"

sublocale M \<subseteq> M3
proof
  fix x y
  show "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y" using nip_eq.
  show part_extensionality: "x = y \<longleftrightarrow> (\<forall> z. P z x \<longleftrightarrow> P z y)"
  proof
    assume "x = y"
    moreover have "\<forall> z. P z x \<longleftrightarrow> P z x" by simp
    ultimately show "\<forall> z. P z x \<longleftrightarrow> P z y" by (rule subst)
  next
    assume z: "\<forall> z. P z x \<longleftrightarrow> P z y"
    show "x = y"
    proof (rule part_antisymmetry)
      from z have "P y x \<longleftrightarrow> P y y"..
      moreover have "P y y" by (rule part_reflexivity)
      ultimately show "P y x"..
    next
      from z have "P x x \<longleftrightarrow> P x y"..
      moreover have "P x x" by (rule part_reflexivity)
      ultimately show "P x y"..
    qed
  qed
qed

sublocale M3 \<subseteq> M
proof
  fix x y
  show "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y" using nip_eq.
  show part_antisymmetry: "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y"
  proof -
    assume "P x y"
    assume "P y x"
    have "\<forall> z. P z x \<longleftrightarrow> P z y"
    proof
      fix z
      show "P z x \<longleftrightarrow> P z y"
      proof
        assume "P z x"
        thus "P z y" using `P x y` by (rule part_transitivity)
      next
        assume "P z y"
        thus "P z x" using `P y x` by (rule part_transitivity)
      qed
    qed
    with part_extensionality show "x = y"..
  qed
qed

text \<open>The fourth axiomatization adopts proper parthood as primitive.\footnote{See, for example, 
@{cite "simons_parts:_1987"}, p. 26 and @{cite "casati_parts_1999"} p. 37.} Improper parthood is
defined as proper parthood or identity.\<close>

locale M4 =
  assumes part_eq: "P x y \<longleftrightarrow> PP x y \<or> x = y"
  assumes  overlap_eq: "O x y \<longleftrightarrow> (\<exists> z. P z x \<and> P z y)"
  assumes proper_part_asymmetry: "PP x y \<Longrightarrow> \<not> PP y x"
  assumes proper_part_transitivity: "PP x y \<Longrightarrow> PP y z \<Longrightarrow> PP x z"
begin

lemma proper_part_irreflexivity: "\<not> PP x x"
proof
  assume "PP x x"
  hence "\<not> PP x x" by (rule proper_part_asymmetry)
  thus "False" using `PP x x`..
qed

end

sublocale M \<subseteq> M4
proof
  fix x y z
  show part_eq: "P x y \<longleftrightarrow> (PP x y \<or> x = y)"
  proof
    assume "P x y"
    show "PP x y \<or> x = y"
    proof cases
      assume "x = y"
      thus "PP x y \<or> x = y"..
    next
      assume "x \<noteq> y"
      with `P x y` have "P x y \<and> x \<noteq> y"..
      with nip_eq have "PP x y"..
      thus "PP x y \<or> x = y"..
    qed
  next
    assume "PP x y \<or> x = y"
    thus "P x y"
    proof
      assume "PP x y"
      thus "P x y" by (rule proper_implies_part)
    next
      assume "x = y" 
      thus "P x y" by (rule identity_implies_part)
    qed
  qed
  show "O x y \<longleftrightarrow> (\<exists> z. P z x \<and> P z y)" using overlap_eq.
  show "PP x y \<Longrightarrow> \<not> PP y x" using proper_part_asymmetry.
  show proper_part_transitivity: "PP x y \<Longrightarrow> PP y z \<Longrightarrow> PP x z"
  proof -
    assume "PP x y"
    assume "PP y z"
    have "P x z \<and> x \<noteq> z"
    proof
      from `PP x y` have "P x y" by (rule proper_implies_part)
      moreover from `PP y z` have "P y z" by (rule proper_implies_part)
      ultimately show "P x z" by (rule part_transitivity)
    next
      show "x \<noteq> z"
      proof
        assume "x = z"
        hence "PP y x" using `PP y z` by (rule ssubst)
        hence "\<not> PP x y" by (rule proper_part_asymmetry)
        thus "False" using `PP x y`..
      qed
    qed
    with nip_eq show "PP x z"..
  qed
qed

sublocale M4 \<subseteq> M
proof
  fix x y z
  show proper_part_eq: "PP x y \<longleftrightarrow> P x y \<and> x \<noteq> y"
  proof
    assume "PP x y"
    hence "PP x y \<or> x = y"..
    with part_eq have "P x y"..
    moreover have "x \<noteq> y"
    proof
      assume "x = y"
      hence "PP y y" using `PP x y` by (rule subst)
      with proper_part_irreflexivity show "False"..
    qed
    ultimately show "P x y \<and> x \<noteq> y"..
  next
    assume rhs: "P x y \<and> x \<noteq> y"
    hence "x \<noteq> y"..
    from rhs have "P x y"..
    with part_eq have "PP x y \<or> x = y"..
    thus "PP x y" 
    proof
      assume "PP x y"
      thus "PP x y".
    next
      assume "x = y"
      with `x \<noteq> y` show "PP x y"..
    qed
  qed
  show "P x x"
  proof -
    have "x = x" by (rule refl)
    hence "PP x x \<or> x = x"..
    with part_eq show "P x x"..
  qed
  show "O x y \<longleftrightarrow> (\<exists> z. P z x \<and> P z y)" using overlap_eq.
  show "P x y \<Longrightarrow> P y x \<Longrightarrow> x = y"
  proof -
    assume "P x y"
    assume "P y x"
    from part_eq have "PP x y \<or> x = y" using `P x y`..
    thus "x = y"
    proof
      assume "PP x y"
      hence "\<not> PP y x" by (rule proper_part_asymmetry)
      from part_eq have "PP y x \<or> y = x" using `P y x`..
      thus "x = y"
      proof
        assume "PP y x"
        with `\<not> PP y x` show "x = y"..
      next
        assume "y = x"
        thus "x = y"..
      qed
    qed
  qed
  show "P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
  proof -
    assume "P x y"
    assume "P y z"
    with part_eq have "PP y z \<or> y = z"..
    hence "PP x z \<or> x = z"
    proof
      assume "PP y z"
      from part_eq have "PP x y \<or> x = y" using `P x y`..
      hence "PP x z"
      proof
        assume "PP x y"
        thus "PP x z" using `PP y z` by (rule proper_part_transitivity)
      next
        assume "x = y"
        thus "PP x z" using `PP y z` by (rule ssubst)
      qed
      thus "PP x z \<or> x = z"..
    next
      assume "y = z"
      moreover from part_eq have "PP x y \<or> x = y" using `P x y`..
      ultimately show "PP x z \<or> x = z" by (rule subst)
    qed
    with part_eq show "P x z"..
  qed
qed

(*<*) end (*>*)