section \<open>\<open>Extra_Lattice\<close> -- Additional results about lattices\<close>

theory Extra_Lattice
  imports Main
begin


subsection\<open>\<open>Lattice_Missing\<close> -- Miscellaneous missing facts about lattices\<close>

text \<open>Two bundles to activate and deactivate lattice specific notation (e.g., \<open>\<sqinter>\<close> etc.).
  Activate the notation locally via "@{theory_text \<open>includes lattice_notation\<close>}" in a lemma statement.
  (Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle lattice_notation ... unbundle no_lattice_notation\<close>}.)\<close>

bundle lattice_notation begin
notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)
notation Inf ("\<Sqinter>")
notation Sup ("\<Squnion>")
notation bot ("\<bottom>")
notation top ("\<top>")
end

bundle no_lattice_notation begin
notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)
notation Inf ("\<Sqinter>")
notation Sup ("\<Squnion>")
notation bot ("\<bottom>")
notation top ("\<top>")
end

unbundle lattice_notation

text \<open>The following class \<open>complemented_lattice\<close> describes complemented lattices (with
  \<^const>\<open>uminus\<close> for the complement). The definition follows 
  \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Definition_and_basic_properties\<close>.
  Additionally, it adopts the convention from \<^class>\<open>boolean_algebra\<close> of defining 
  \<^const>\<open>minus\<close> in terms of the complement.\<close>

class complemented_lattice = bounded_lattice + uminus + minus + 
  assumes inf_compl_bot[simp]: "inf x (-x) = bot"
    and sup_compl_top[simp]: "sup x (-x) = top"
    and diff_eq:  "x - y = inf x (- y)" begin

lemma dual_complemented_lattice:
  "class.complemented_lattice (\<lambda>x y. x \<squnion> (- y)) uminus sup greater_eq greater inf \<top> \<bottom>"
proof (rule class.complemented_lattice.intro)
  show "class.bounded_lattice (\<squnion>) (\<lambda>x y. (y::'a) \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_bounded_lattice)
  show "class.complemented_lattice_axioms (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<sqinter>) \<top> \<bottom>"
    by (unfold_locales, auto simp add: diff_eq)
qed


lemma compl_inf_bot [simp]: "inf (- x) x = bot"
  by (simp add: inf_commute)

lemma compl_sup_top [simp]: "sup (- x) x = top"
  by (simp add: sup_commute)

end

class complete_complemented_lattice = complemented_lattice + complete_lattice 

text \<open>The following class \<open>complemented_lattice\<close> describes orthocomplemented lattices,
  following   \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Orthocomplementation\<close>.\<close>
class orthocomplemented_lattice = complemented_lattice +
  assumes ortho_involution[simp]: "- (- x) = x"
    and ortho_antimono: "x \<le> y \<Longrightarrow> -x \<ge> -y" begin

lemma dual_orthocomplemented_lattice:
  "class.orthocomplemented_lattice (\<lambda>x y. x \<squnion> - y) uminus sup greater_eq greater inf \<top> \<bottom>"
proof (rule class.orthocomplemented_lattice.intro)
  show "class.complemented_lattice (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_complemented_lattice)
  show "class.orthocomplemented_lattice_axioms uminus (\<lambda>x y. (y::'a) \<le> x)"
    by (unfold_locales, auto simp add: diff_eq intro: ortho_antimono)
qed



lemma compl_eq_compl_iff [simp]: "- x = - y \<longleftrightarrow> x = y"
  by (metis ortho_involution)

lemma compl_bot_eq [simp]: "- bot = top"
  by (metis inf_compl_bot inf_top_left ortho_involution)

lemma compl_top_eq [simp]: "- top = bot"
  using compl_bot_eq ortho_involution by blast

text \<open>De Morgan's law\<close>
  (* Proof from: https://planetmath.org/orthocomplementedlattice *)
lemma compl_sup [simp]: "- (x \<squnion> y) = - x \<sqinter> - y"
proof -
  have "- (x \<squnion> y) \<le> - x"
    by (simp add: ortho_antimono)
  moreover have "- (x \<squnion> y) \<le> - y"
    by (simp add: ortho_antimono)
  ultimately have 1: "- (x \<squnion> y) \<le> - x \<sqinter> - y"
    by (simp add: sup.coboundedI1)
  have \<open>x \<le> - (-x \<sqinter> -y)\<close>
    by (metis inf.cobounded1 ortho_antimono ortho_involution)
  moreover have \<open>y \<le> - (-x \<sqinter> -y)\<close>
    by (metis inf.cobounded2 ortho_antimono ortho_involution)
  ultimately have \<open>x \<squnion> y \<le> - (-x \<sqinter> -y)\<close>
    by auto
  hence 2: \<open>-x \<sqinter> -y \<le> - (x \<squnion> y)\<close>
    using ortho_antimono by fastforce
  from 1 2 show ?thesis
    by (simp add: eq_iff)
qed

text \<open>De Morgan's law\<close>
lemma compl_inf [simp]: "- (x \<sqinter> y) = - x \<squnion> - y"
  using compl_sup
  by (metis ortho_involution)

lemma compl_mono:
  assumes "x \<le> y"
  shows "- y \<le> - x"
  by (simp add: assms local.ortho_antimono)

lemma compl_le_compl_iff [simp]: "- x \<le> - y \<longleftrightarrow> y \<le> x"
  by (auto dest: compl_mono)

lemma compl_le_swap1:
  assumes "y \<le> - x"
  shows "x \<le> -y"
  using assms ortho_antimono by fastforce

lemma compl_le_swap2:
  assumes "- y \<le> x"
  shows "- x \<le> y"
  using assms local.ortho_antimono by fastforce

lemma compl_less_compl_iff[simp]: "- x < - y \<longleftrightarrow> y < x"
  by (auto simp add: less_le)

lemma compl_less_swap1:
  assumes "y < - x"
  shows "x < - y"
  using assms compl_less_compl_iff by fastforce

lemma compl_less_swap2:
  assumes "- y < x"
  shows "- x < y"
  using assms compl_le_swap1 compl_le_swap2 less_le_not_le by auto

lemma sup_cancel_left1: "sup (sup x a) (sup (- x) b) = top"
  by (simp add: sup_commute sup_left_commute)

lemma sup_cancel_left2: "sup (sup (- x) a) (sup x b) = top"
  by (simp add: sup.commute sup_left_commute)

lemma inf_cancel_left1: "inf (inf x a) (inf (- x) b) = bot"
  by (simp add: inf.left_commute inf_commute)

lemma inf_cancel_left2: "inf (inf (- x) a) (inf x b) = bot"
  using inf.left_commute inf_commute by auto

lemma sup_compl_top_left1 [simp]: "sup (- x) (sup x y) = top"
  by (simp add: sup_assoc[symmetric])

lemma sup_compl_top_left2 [simp]: "sup x (sup (- x) y) = top"
  using sup_compl_top_left1[of "- x" y] by simp

lemma inf_compl_bot_left1 [simp]: "inf (- x) (inf x y) = bot"
  by (simp add: inf_assoc[symmetric])

lemma inf_compl_bot_left2 [simp]: "inf x (inf (- x) y) = bot"
  using inf_compl_bot_left1[of "- x" y] by simp

lemma inf_compl_bot_right [simp]: "inf x (inf y (- x)) = bot"
  by (subst inf_left_commute) simp

end

class complete_orthocomplemented_lattice = orthocomplemented_lattice + complete_lattice

instance complete_orthocomplemented_lattice \<subseteq> complete_complemented_lattice
  by intro_classes

text \<open>The following class \<open>orthomodular_lattice\<close> describes orthomodular lattices,
following   \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Orthomodular_lattices\<close>.\<close>
class orthomodular_lattice = orthocomplemented_lattice +
  assumes orthomodular: "x \<le> y \<Longrightarrow> sup x (inf (-x) y) = y" begin

lemma dual_orthomodular_lattice:
  "class.orthomodular_lattice (\<lambda>x y. x \<squnion> - y) uminus sup greater_eq greater inf \<top> \<bottom>"
proof (rule class.orthomodular_lattice.intro)
  show "class.orthocomplemented_lattice (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_orthocomplemented_lattice)
  show "class.orthomodular_lattice_axioms uminus (\<squnion>) (\<lambda>x y. (y::'a) \<le> x) (\<sqinter>)"
  proof (unfold_locales)
    show "(x::'a) \<sqinter> (- x \<squnion> y) = y"
      if "(y::'a) \<le> x"
      for x :: 'a
        and y :: 'a
      using that local.compl_eq_compl_iff local.ortho_antimono local.orthomodular by fastforce
  qed

qed


end

class complete_orthomodular_lattice = orthomodular_lattice + complete_lattice begin

end

instance complete_orthomodular_lattice \<subseteq> complete_orthocomplemented_lattice
  by intro_classes


instance boolean_algebra \<subseteq> orthomodular_lattice
proof
  fix x y :: 'a  
  show "sup (x::'a) (inf (- x) y) = y"
    if "(x::'a) \<le> y"
    using that
    by (simp add: sup.absorb_iff2 sup_inf_distrib1) 
  show "x - y = inf x (- y)"
    by (simp add: boolean_algebra_class.diff_eq)
qed auto

instance complete_boolean_algebra \<subseteq> complete_orthomodular_lattice
  by intro_classes

lemma image_of_maximum:
  fixes f::"'a::order \<Rightarrow> 'b::conditionally_complete_lattice"
  assumes "mono f"
    and "\<And>x. x:M \<Longrightarrow> x\<le>m"
    and "m:M"
  shows "(SUP x\<in>M. f x) = f m"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(3) cSup_eq_maximum imageE imageI monoD)

lemma cSup_eq_cSup:
  fixes A B :: \<open>'a::conditionally_complete_lattice set\<close>
  assumes bdd: \<open>bdd_above A\<close>
  assumes B: \<open>\<And>a. a\<in>A \<Longrightarrow> \<exists>b\<in>B. b \<ge> a\<close>
  assumes A: \<open>\<And>b. b\<in>B \<Longrightarrow> \<exists>a\<in>A. a \<ge> b\<close>
  shows \<open>Sup A = Sup B\<close>
proof (cases \<open>B = {}\<close>)
  case True
  with A B have \<open>A = {}\<close>
    by auto
  with True show ?thesis by simp
next
  case False
  have \<open>bdd_above B\<close>
    by (meson A bdd bdd_above_def order_trans)
  have \<open>A \<noteq> {}\<close>
    using A False by blast
  moreover have \<open>a \<le> Sup B\<close> if \<open>a \<in> A\<close> for a
  proof -
    obtain b where \<open>b \<in> B\<close> and \<open>b \<ge> a\<close>
      using B \<open>a \<in> A\<close> by auto
    then show ?thesis
      apply (rule cSup_upper2)
      using \<open>bdd_above B\<close> by simp
  qed
  moreover have \<open>Sup B \<le> c\<close> if \<open>\<And>a. a \<in> A \<Longrightarrow> a \<le> c\<close> for c
    using False apply (rule cSup_least)
    using A that by fastforce
  ultimately show ?thesis
    by (rule cSup_eq_non_empty)
qed

unbundle no_lattice_notation

end
