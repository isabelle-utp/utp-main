section \<open> Introduction \<close>

(*<*)
theory PM
  imports Main
begin
(*>*)

text \<open> In this paper, we use Isabelle/HOL to verify some elementary theorems and alternative axiomatizations
of classical extensional mereology, as well as some of its weaker subtheories.\footnote{For similar 
developments see @{cite "sen_computational_2017"} and @{cite "bittner_formal_2018"}.} We mostly follow the 
presentations from @{cite "simons_parts:_1987"}, @{cite "varzi_parts_1996"} and @{cite "casati_parts_1999"}, 
with some important corrections from @{cite "pontow_note_2004"} and @{cite "hovda_what_2009"} as well as
some detailed proofs adapted from @{cite "pietruszczak_metamereology_2018"}.\footnote{For help with 
this project I am grateful to Zach Barnett, Sam Baron, Bob Beddor, Olivier Danvy, Mark Goh,
Jeremiah Joven Joaquin, Wang-Yen Lee, Kee Wei Loo, Bruno Woltzenlogel Paleo, Michael Pelczar, Hsueh Qu, 
Abelard Podgorski, Divyanshu Sharma, Manikaran Singh, Neil Sinhababu, Weng-Hong Tang and Zhang Jiang.} \<close> 

text \<open> We will use the following notation throughout.\footnote{See @{cite "simons_parts:_1987"} pp. 99-100 
for a helpful comparison of alternative notations.} \<close>

typedecl i
consts part :: "i \<Rightarrow> i \<Rightarrow> bool" ("P")
consts overlap :: "i \<Rightarrow> i \<Rightarrow> bool" ("O")
consts proper_part :: "i \<Rightarrow> i \<Rightarrow> bool" ("PP")
consts sum :: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<oplus>" 52)
consts product :: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<otimes>" 53)
consts difference :: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<ominus>" 51)
consts complement:: "i \<Rightarrow> i" ("\<midarrow>")
consts universe :: "i" ("u")
consts general_sum :: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<sigma>" 9)
consts general_product :: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<pi>" [8] 9)

section \<open> Premereology \<close>

text \<open> The theory of \emph{premereology} assumes parthood is reflexive and transitive.\footnote{ 
For discussion of reflexivity see @{cite "kearns_can_2011"}. For transitivity see @{cite "varzi_note_2006"}.}
In other words, parthood is assumed to be a partial ordering relation.\footnote{Hence the name \emph{premereology},
from @{cite "parsons_many_2014"} p. 6.} Overlap is defined as common parthood.\footnote{See
@{cite "simons_parts:_1987"} p. 28, @{cite "varzi_parts_1996"} p. 261 and @{cite "casati_parts_1999"} p. 36. } \<close>

locale PM =
  assumes part_reflexivity: "P x x"
  assumes part_transitivity : "P x y \<Longrightarrow> P y z \<Longrightarrow> P x z"
  assumes overlap_eq: "O x y \<longleftrightarrow> (\<exists> z. P z x \<and> P z y)"
begin

subsection \<open> Parthood \<close>

lemma identity_implies_part : "x = y \<Longrightarrow> P x y"
proof -
  assume "x = y"
  moreover have "P x x" by (rule part_reflexivity)
  ultimately show "P x y" by (rule subst)
qed

subsection \<open> Overlap \<close>

lemma overlap_intro: "P z x \<Longrightarrow> P z y \<Longrightarrow> O x y"
proof-
  assume "P z x"
  moreover assume "P z y"
  ultimately have "P z x \<and> P z y"..
  hence "\<exists> z. P z x \<and> P z y"..
  with overlap_eq show "O x y"..
qed

lemma part_implies_overlap: "P x y \<Longrightarrow> O x y"
proof -
  assume "P x y"
  with part_reflexivity have "P x x \<and> P x y"..
  hence "\<exists> z. P z x \<and> P z y"..
  with overlap_eq show "O x y"..
qed

lemma overlap_reflexivity: "O x x"
proof -
  have "P x x \<and> P x x" using part_reflexivity part_reflexivity..
  hence "\<exists> z. P z x \<and> P z x"..
  with overlap_eq show "O x x"..
qed

lemma overlap_symmetry: "O x y \<Longrightarrow> O y x"
proof-
  assume "O x y"
  with overlap_eq have "\<exists> z. P z x \<and> P z y"..
  hence "\<exists> z. P z y \<and> P z x" by auto
  with overlap_eq show "O y x"..
qed

lemma overlap_monotonicity: "P x y \<Longrightarrow> O z x \<Longrightarrow> O z y"
proof -
  assume "P x y"
  assume "O z x"
  with overlap_eq have "\<exists> v. P v z \<and> P v x"..
  then obtain v where v: "P v z \<and> P v x"..
  hence "P v z"..
  moreover from v have "P v x"..
  hence "P v y" using `P x y` by (rule part_transitivity)
  ultimately have "P v z \<and> P v y"..
  hence "\<exists> v. P v z \<and> P v y"..
  with overlap_eq show "O z y"..
qed

text \<open> The next lemma is from @{cite "hovda_what_2009"} p. 66. \<close>

lemma overlap_lemma: "\<exists>x. (P x y \<and> O z x) \<longrightarrow> O y z"
proof -
  fix x
  have "P x y \<and> O z x \<longrightarrow> O y z"
  proof
    assume antecedent: "P x y \<and> O z x"
    hence "O z x"..
    with overlap_eq have "\<exists>v. P v z \<and> P v x"..
    then obtain v where v: "P v z \<and> P v x"..
    hence "P v x"..
    moreover from antecedent have "P x y"..
    ultimately have "P v y" by (rule part_transitivity)
    moreover from v have "P v z"..
    ultimately have "P v y \<and> P v z"..
    hence "\<exists>v. P v y \<and> P v z"..
    with overlap_eq show "O y z"..
  qed
  thus "\<exists>x. (P x y \<and> O z x) \<longrightarrow> O y z"..
qed

subsection \<open> Disjointness \<close>

lemma disjoint_implies_distinct: "\<not> O x y \<Longrightarrow> x \<noteq> y"
proof -
  assume "\<not> O x y"
  show "x \<noteq> y"
  proof
    assume "x = y"
    hence "\<not> O y y" using `\<not> O x y` by (rule subst)
    thus "False" using overlap_reflexivity..
  qed
qed

lemma disjoint_implies_not_part: "\<not> O x y \<Longrightarrow> \<not> P x y"
proof -
  assume "\<not> O x y"
  show "\<not> P x y"
  proof
    assume "P x y"
    hence "O x y" by (rule part_implies_overlap)
    with `\<not> O x y` show "False"..
  qed
qed

lemma disjoint_symmetry: "\<not> O x y \<Longrightarrow> \<not> O y x"
proof -
  assume "\<not> O x y"
  show "\<not> O y x"
  proof
    assume "O y x"
    hence "O x y" by (rule overlap_symmetry)
    with `\<not> O x y` show "False"..
  qed
qed

lemma disjoint_demonotonicity: "P x y \<Longrightarrow> \<not> O z y \<Longrightarrow> \<not> O z x"
proof -
  assume "P x y"
  assume "\<not> O z y"
  show "\<not> O z x"
  proof
    assume "O z x"
    with `P x y` have "O z y"
      by (rule overlap_monotonicity)
    with `\<not> O z y` show "False"..
  qed
qed

end

(*<*)end(*>*)