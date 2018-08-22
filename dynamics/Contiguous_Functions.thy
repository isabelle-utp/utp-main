section {* Contiguous Functions *}

(*<*)
theory Contiguous_Functions
  imports
  HOL.Real_Vector_Spaces
  "Optics.Lenses"
  "UTP-Toolkit.Map_Extra"
  "UTP-Toolkit.List_Extra"
  "UTP-Toolkit.Trace_Algebra"
  Derivative_extra
  "HOL-Analysis.Topology_Euclidean_Space"
begin
(*>*)

text {* In this section we will define a type to represent contiguous functions with
  a real domain, which will be used to represent trajectories, together with suitable algebraic
  operators. We then specialise this to piecewise continuous and convergent functions, and show
  closure of the algebraic operators. The properties we use here will be crucial in our hybrid
  relational calculus. Our model and the associated algebra is based partly on the work of
  Hayes~\cite{Hayes2006,Hayes2010} who introduces a theory of timed traces to give semantics
  to real-time programs, and also H\"{o}fner~\cite{Hofner2009} who gives and algebraic foundation for verifying
  hybrid systems, including operators on continuous trajectories that underlie hybrid automata.
  A timed trace is essentially a function from real numbers to a continuous state space; in the
  following we will further elaborate this.
*}

subsection {* Preliminaries *}

text {* We first define two functions that a shift a partial function to the left and the right by
  a value $n$, respectively, by a suitable minus or addition on the input. These functions will
  allow us to define concatenation of two timed traces. *}

abbreviation rshift :: "('a::ring \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixr "\<ggreater>" 66) where
"rshift f n \<equiv> (\<lambda> x. f (x - n))"

abbreviation lshift :: "'a \<Rightarrow> ('a::ring \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" (infixl "\<lless>" 65) where
"lshift n f \<equiv> (\<lambda> x. f (x + n))"

text {* We can then show the following two results that give the domain of left and right shifted
  functions. *}

lemma dom_shift_plus: "dom (n \<lless> f) = {x - n | x. x \<in> dom f}"
  by (auto simp add: dom_def, force)

lemma dom_shift_minus: "dom (f \<ggreater> n) = (+) n ` dom f"
  by (simp add: dom_def image_Collect, force)

lemma shift_minus_cong: "f \<ggreater> n = g \<ggreater> n \<Longrightarrow> f = g"
  apply (auto simp add: fun_eq_iff)
  apply (drule_tac x="x + n" in spec)
  apply (simp)
done

lemma dom_shift_map_add: "(f ++ g) \<ggreater> n = (f \<ggreater> n) ++ (g \<ggreater> n)"
  by (simp add: map_add_def)

lemma atLeastLessThan_union_disj [simp]: "\<lbrakk> 0 \<le> i; i \<le> j \<rbrakk> \<Longrightarrow> {0..<i::real} \<union> {i..<j} = {0..<j}"
  by (auto)

definition Sup' :: "real set \<Rightarrow> real" where
"Sup' A = (if (A = {}) then 0 else Sup A)"

text {* We also define the @{term Sup} operator that gives the supremum of a set of positive real numbers.
  Specifically, if the set is empty then it is 0, otherwise it is the built-in supremum for
  real numbers. We can then prove some properties about such suprema. *}

lemma Sup'_empty [simp]: "Sup' {} = 0"
  by (simp add: Sup'_def)

lemma Sup'_interval [simp]: "Sup' {0..<m} = (if (m > 0) then m else 0)"
  by (simp add: Sup'_def)

lemma Sup'_interval': "Sup' {t. 0 \<le> t \<and> t < l} = (if (l > 0) then l else 0)"
  by (metis (no_types, lifting) Sup'_interval atLeastLessThan_iff equalityI mem_Collect_eq subsetI)
    
text {* The first property tells us that the supremum of an empty set is zero, and the second
  tells us that the supremum of a right open interval is the limit of the interval. *}

subsection {* Contiguous Functions *}

typedef 'a cgf =
  "{f :: real \<rightharpoonup> 'a. (\<exists> i. i \<ge> 0 \<and> dom(f) = {0..<i})}"
proof
  have "\<exists>i::real\<ge>0. {} = {0..<i}"
    by (rule_tac x="0" in exI, auto)
  thus "Map.empty \<in> {f. \<exists>i\<ge>0::real. dom f = {0..<i}}"
    by (auto)
qed

(*<*)
setup_lifting type_definition_cgf
(*>*)

text {* We begin our definition of contiguous functions by defining the core type, @{typ "'a cgf"}
  using the Isabelle \textbf{typedef} command. Such a definition creates a new type from a subset
  of an existing type, assuming the subset is non-empty. A contiguous function is a partial function
  from real numbers to some range type @{typ "'a"}, such that there is a non-negative @{term i} that gives
  the "end point" of the contiguous function. Specifically, the domain is the right-open interval
  @{term "{0..<i}"}, which in pure mathematics is usually written as [0,i). *}

lift_definition cgf_apply :: "'a cgf \<Rightarrow> real \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>C") is "\<lambda> f x. the (f x)" .
lift_definition cgf_dom :: "'a cgf \<Rightarrow> real set" ("dom\<^sub>C") is dom .
lift_definition cgf_end :: "'a cgf \<Rightarrow> real" ("end\<^sub>C") is "\<lambda> f. Sup'(dom(f))" .
lift_definition cgf_map :: "(real \<times> 'a \<Rightarrow> 'b) \<Rightarrow> 'a cgf \<Rightarrow> 'b cgf" ("map\<^sub>C")
  is "\<lambda> f g x. if (x \<in> dom(g)) then Some (f (x, the(g(x)))) else None"
  by (auto simp add: dom_if)

abbreviation "map'\<^sub>C f \<equiv> cgf_map (\<lambda> (i, x). f x)"

lift_definition cgf_restrict :: "'a cgf \<Rightarrow> real \<Rightarrow> 'a cgf" (infix "\<restriction>\<^sub>C" 85)
is "\<lambda> f i. f |` {0..<i}"
  by (auto simp add: min_def, blast, metis atLeastLessThan_empty_iff2 less_eq_real_def less_irrefl)

lift_definition cgf_force :: "'a cgf \<Rightarrow> real \<Rightarrow> 'a cgf" (infix "!\<^sub>C" 85)
is "\<lambda> f i x. if (0 \<le> x \<and> x < i) then Some(the(f(x))) else None"
  apply (rename_tac f n)
  apply (case_tac "n \<ge> 0")
  apply (auto simp add: dom_if)
done

lemma cgf_end_alt_def:
  "end\<^sub>C(f) = Inf ({0..} - dom\<^sub>C(f))"
  by (transfer, auto, metis Diff_iff atLeastLessThan_iff atLeast_iff cInf_eq_minimum le_less_linear not_less_iff_gr_or_eq)

text {* We also create functions that allow various manipulations on contiguous functions by
  lifting functions on the underlying partial function type. Function @{term cgf_apply}, also
  written as @{term "\<langle>f\<rangle>\<^sub>C"}, allows the application of a contiguous function to an input real number.
  When the input is outside of the domain, and arbitrary value is returned. @{term cgf_dom}
  (@{term "dom\<^sub>C(f)"}) gives the domain of function, and @{term [source] cgf_end} (@{term "end\<^sub>C(f)"}) returns
  the end point. Term (@{term "map\<^sub>C f g"}) applies a function to every element
  in the range, like a typical map function. Finally, @{term [source] cgf_restrict} (@{term "f \<restriction>\<^sub>C i"}) restricts
  the domain of a contiguous function to the interval [0,i), and @{term cgf_force} (@{term "f !\<^sub>C i"}) has
  a similar effect but forces the function to be extended if necessary. If the function is required
  to extend then the range will be filled with arbitrary values. *}

instantiation cgf :: (type) zero
begin
  lift_definition zero_cgf :: "'a cgf" is Map.empty by (auto)
instance ..
end

abbreviation (input) cgf_empty :: "'a cgf" ("[]\<^sub>C") where "[]\<^sub>C \<equiv> 0"

text {* We will now define the algebraic operators of timed traces, with which we will be able to
  instantiate our theory of generalised reactive designs with, and thence produce timed reactive designs. We do
  this by instantiating various type classes towards showing that contiguous functions form a
  cancellative monoid, which is the underlying trace algebra. The zero element is the empty
  contiguous function, obtained by lifting the empty partial function
  and demonstrating (as before) that this satisfies the invariant of a contiguous function. We
  also give the zero element the syntax @{term [source] "[]\<^sub>C"}. *}

instantiation cgf :: (type) plus
begin

lift_definition plus_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf"
is "\<lambda> f g. (g \<ggreater> Sup'(dom(f))) ++ f"
proof -
  fix f g :: "real \<rightharpoonup> 'a"
  assume "\<exists>i\<ge>0. dom f = {0..<i}" "\<exists>j\<ge>0. dom g = {0..<j}"
  then obtain i j where ij: "i \<ge> 0" "j \<ge> 0" "dom f = {0..<i}" "dom g = {0..<j}"
    by auto
  let ?k = "i + j"
  from ij have "?k \<ge> 0"
    by auto
  moreover from ij have "dom ((g \<ggreater> Sup' (dom f)) ++ f) = {0..<?k}"
    by (auto simp add: dom_shift_minus)
  ultimately show "\<exists>i\<ge>0. dom ((g \<ggreater> Sup' (dom f)) ++ f) = {0..<i}"
    by force
qed
instance ..

end

abbreviation (input) cgf_cat :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf" (infixl "@\<^sub>C" 85)
where "xs @\<^sub>C ys \<equiv> xs + ys"

text {* We next define the concatenation operator, which in our algebra is a plus operator. The
  concatentation of functions, @{term [source] "f @\<^sub>C g"}, takes @{term g}, shifts it to the right by
  the length of @{term f}, and finally unions this with @{term f} using the partial function
  operator @{term "(++)"}. It is necessary to show that this definition is closed under contiguous functions,
  i.e. we must demonstrate an $k$ such that the domain of @{term [source] "f @\<^sub>C g"} is $[0..k)$, which we do
  using an Isar proof. Since we're concatentating two functions of length $i$ and $j$, respectively,
  then their combined length will be $i + j$, which our proof confirms. *}

lemma cgf_cat_left_unit [simp]: "[]\<^sub>C @\<^sub>C t = t"
  by (transfer, simp)

lemma cgf_cat_right_unit [simp]: "t @\<^sub>C []\<^sub>C = t"
  by (transfer, auto)

text {* We can then show that the concatenation operator has @{term "[]\<^sub>C"} as its left and right
  zeros. *}

lemma cgf_eqI: "\<lbrakk> end\<^sub>C f = end\<^sub>C g; \<And> t. \<lbrakk> 0 \<le> t; t <end\<^sub>C g \<rbrakk> \<Longrightarrow> \<langle>f\<rangle>\<^sub>C t = \<langle>g\<rangle>\<^sub>C t \<rbrakk> \<Longrightarrow> f = g"
  apply (transfer)
  apply (auto)
  apply (rename_tac f g i j)
  apply (case_tac "i = 0")
  apply (simp_all)
  using less_eq_real_def apply auto[1]
  apply (case_tac "j = 0")
  apply (auto)
  apply (rule map_eqI)
  apply (auto)
done

text {* Lemma @{thm [source] cgf_eqI} is an extensionality principle for contiguous functions. If two
  $f$ and $g$ have the same end points, and they agree on every value before these end points
  then the two functions are the same. *}

lemma cgf_end_ge_0 [simp]: "end\<^sub>C(f) \<ge> 0"
  by (transfer, auto simp add: less_eq_real_def)

lemma cgf_end_empty [simp]: "end\<^sub>C([]\<^sub>C) = 0"
  by (transfer, simp)

lemma cgf_end_0_iff: "end\<^sub>C(f) = 0 \<longleftrightarrow> f = []\<^sub>C"
  by (transfer, force simp add: antisym_conv2)

lemma cgf_end_cat: "end\<^sub>C(f @\<^sub>C g) = end\<^sub>C(f)+end\<^sub>C(g)"
  by (transfer, auto simp add: dom_shift_minus)

text {* Next we demonstrate some properties about the @{term end\<^sub>C} function. It always returns
  a positive value (@{thm [source] cgf_end_ge_0}), the end of the empty function is 0 (@{thm [source] cgf_end_empty}),
  if a function has 0 as its end then it is equal to @{term "[]\<^sub>C"} (@{thm [source] cgf_end_0_iff}), and the
  end of a concatenation is the sum of the two ends (@{thm [source] cgf_end_cat}). *}

lemma cgf_cat_ext_first:
  assumes "x < end\<^sub>C f"
  shows "\<langle>f @\<^sub>C g\<rangle>\<^sub>C x = \<langle>f\<rangle>\<^sub>C x"
proof (cases "f = []\<^sub>C")
  case True with assms show ?thesis
    by (transfer, auto, metis atLeastLessThan_iff domIff less_le_not_le)
next
  case False with assms show ?thesis
    by (transfer, auto simp add: map_add_def option.case_eq_if)
       (metis atLeastLessThan_iff domIff less_iff_diff_less_0 not_less)
qed

lemma cgf_cat_ext_last: "x \<ge> end\<^sub>C f \<Longrightarrow> \<langle>f @\<^sub>C g\<rangle>\<^sub>C x = \<langle>g\<rangle>\<^sub>C (x - end\<^sub>C f)"
  by (transfer, auto simp add: map_add_dom_app_simps(3))

text {* Lemmas @{thm [source] cgf_cat_ext_first} and @{thm [source] cgf_cat_ext_last} show the effect of applying
  an input $x$ to an appended trace. If $x$ is less than the end of the first trace, then this
  is equivalent to applying it to the first trace. Otherwise, if $x$ is greater than or equal
  to the end of the first, then the result is to apply to the second, but with the input shifted. *}

lemma cgf_zero_sum_left:
  "f @\<^sub>C g = []\<^sub>C \<Longrightarrow> f = []\<^sub>C"
  by (metis cgf_cat_right_unit cgf_end_0_iff cgf_end_cat cgf_end_ge_0
            dual_order.antisym le_add_same_cancel2)

text {* The next lemma tells us that if two functions concatenate to become the empty function then the
  first must be empty. Now by the fact that @{term "[]\<^sub>C"} is a left unit we can also show that
  the second must also be empty. *}

lemma cgf_cat_left_imp_eq:
  assumes "f @\<^sub>C g = f @\<^sub>C h"
  shows "g = h"
using assms proof (transfer)
  fix f g h :: "real \<rightharpoonup> 'a"
  assume a:
    "\<exists>i\<ge>0. dom f = {0..<i}" "\<exists>i\<ge>0. dom g = {0..<i}" "\<exists>i\<ge>0. dom h = {0..<i}"
    "(g \<ggreater> Sup' (dom f)) ++ f = (h \<ggreater> Sup' (dom f)) ++ f"
  then obtain i j k where ijk:
    "i \<ge> 0" "j \<ge> 0" "k \<ge> 0" "dom f = {0..<i}" "dom g = {0..<j}" "dom h = {0..<k}"
    by auto
  show "g = h"
  proof (cases "i > 0")
    case False with ijk a(4) show ?thesis
      by (auto)
  next
    case True
    with ijk have "dom(g \<ggreater> i) \<inter> {0..<i} = {}"
      by (auto simp add: dom_shift_minus)
    moreover from True ijk have "dom(h \<ggreater> i) \<inter> {0..<i} = {}"
      by (auto simp add: dom_shift_minus)
    ultimately show ?thesis using True ijk a(4)
      by (auto dest!: map_plus_eq_left shift_minus_cong simp add: restrict_map_neg_disj dom_shift_minus)
  qed
qed

text {* Lemma @{thm [source] cgf_cat_left_imp_eq} shows that concatenation is cancellative in its first argument.
  Intuitively this means that a trace can be uniquely decomposed into its constituent parts and
  is one of the key properties of the trace algebra of generalised reactive processes. *}

lemma cgf_cat_right_imp_eq:
  assumes "f @\<^sub>C h = g @\<^sub>C h"
  shows "f = g"
proof -
  have ends: "end\<^sub>C(f) = end\<^sub>C(g)"
    by (metis add.commute add_left_cancel assms cgf_end_cat)
  show ?thesis
  proof (cases "f = []\<^sub>C")
    case True
    hence "g = []\<^sub>C"
      using cgf_end_0_iff ends by auto
    with True show ?thesis ..
  next
    case False
    with assms ends show ?thesis
    proof (transfer)
      fix f g h :: "real \<rightharpoonup> 'a"
      assume a: "\<exists>i\<ge>0. dom f = {0..<i}" "\<exists>i\<ge>0. dom g = {0..<i}" "\<exists>i\<ge>0. dom h = {0..<i}"
             "(h \<ggreater> Sup' (dom f)) ++ f = (h \<ggreater> Sup' (dom g)) ++ g"
             "(Sup' (dom f)) = (Sup' (dom g))"
             "f \<noteq> Map.empty"
      hence "dom f = dom g"
        by (metis Sup'_interval atLeastLessThan_empty not_le)
      with a obtain i j where "dom f = {0..<i}" "dom g = {0..<i}" "dom h = {0..<j}"
        by (auto)
      moreover with a have "i > 0"
        by (auto)
      ultimately show "f = g" using a(4)
        by (simp, metis (mono_tags, lifting) map_eqI map_le_def map_le_map_add)
    qed
  qed
qed

text {* Similarly, we show that concatenation is cancellative in its second argument. *}

lemma cgf_cat_assoc: "(f @\<^sub>C g) @\<^sub>C h = f @\<^sub>C (g @\<^sub>C h)"
proof (rule cgf_eqI, simp_all add: cgf_end_cat add.assoc)
  fix x
  assume x: "x < end\<^sub>C f + (end\<^sub>C g + end\<^sub>C h)"
  show "\<langle>f @\<^sub>C g @\<^sub>C h\<rangle>\<^sub>C x = \<langle>f @\<^sub>C (g @\<^sub>C h)\<rangle>\<^sub>C x"
  proof (cases "x < end\<^sub>C f")
    case True thus ?thesis
      by (metis (mono_tags, hide_lams) add.right_neutral add_less_cancel_left
                cgf_cat_ext_first cgf_end_cat cgf_end_ge_0 le_less_trans not_le)
  next
    case False
    hence x_gef: "x \<ge> end\<^sub>C f"
      by auto
    thus ?thesis
    proof (cases "x < end\<^sub>C f+end\<^sub>C g")
      case True thus ?thesis
        by (simp add: add_less_imp_less_left cgf_cat_ext_first cgf_cat_ext_last cgf_end_cat x_gef)
    next
      case False
      hence x_gefg: "x \<ge> end\<^sub>C f+end\<^sub>C g"
        by auto
      thus ?thesis
        by (simp add: cgf_cat_ext_last cgf_end_cat cancel_ab_semigroup_add_class.diff_diff_add
                      add_le_imp_le_diff x_gef)
    qed
  qed
qed

text {* Another key property is associativity of concatenation, which is demonstrated above. We prove
  this by extensionality, and split the proof into values of the index $x$ that fall within the
  three concatenated sections of the contiguous function. This allows us to show, below, that
  contiguous functions form a monoid. *}

instance cgf :: (type) monoid_add
  by (intro_classes, simp_all add: cgf_cat_assoc)

instantiation cgf :: (type) ord
begin
  lift_definition less_eq_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> bool" is
  "(\<subseteq>\<^sub>m)" .
  definition less_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> bool" where
  "less_cgf x y = (x \<le> y \<and> \<not> y \<le> x)"
instance ..
end

text {* We can also construct a suitably order relation on contiguous functions by lifting of the
  corresponding order on partial functions, @{term "(\<subseteq>\<^sub>m)"}, which corresponds to the subset
  operator when considering the function as a relation. *}

abbreviation (input) cgf_prefix :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> bool" (infix "\<subseteq>\<^sub>C" 50)
where "f \<subseteq>\<^sub>C g \<equiv> f \<le> g"

text {* We give the alternative notation of @{term "f \<subseteq>\<^sub>C g"} to the function order to highlight
  its role as a subset-like operator. *}
  
lemma monoid_le_ttrace:
  "(f :: 'a cgf) \<le>\<^sub>m g \<longleftrightarrow> f \<le> g"
  apply (simp add: monoid_le_def, transfer, auto)
  apply (rename_tac g f i j)
  apply (rule_tac x="j \<lless> (g |` {j..<i})" in exI)
  apply (auto simp add: dom_shift_plus)
  apply (rule_tac x="i-j" in exI)
  apply (auto)
  using map_le_implies_dom_le apply fastforce
  apply (metis add.commute add_increasing cancel_ab_semigroup_add_class.add_diff_cancel_left'
               less_diff_eq less_eq_real_def)
  apply (subgoal_tac "f = g |` {0..<j}")
  apply (simp)
  apply (subst map_add_split, auto)
  apply (simp add: map_le_via_restrict)
done

lemma cgf_prefix_iff: "f \<le> g \<longleftrightarrow> (\<exists> h. g = f @\<^sub>C h)"
  apply (transfer, auto)
   apply (rename_tac f g i j)
   apply (rule_tac x="i \<lless> (g |` {i..<j})" in exI)
   apply (auto simp add: dom_shift_plus)
   apply (rule_tac x="j-i" in exI)
   apply (auto)
  using map_le_implies_dom_le apply fastforce
   apply (metis (no_types, hide_lams) Groups.add_ac(2) add.right_neutral add_diff_cancel_right' add_mono_thms_linordered_field(1) diff_add_cancel diff_left_mono dual_order.trans le_less_linear order.asym)
  apply (case_tac "i < j")
   apply (auto)
   apply (metis atLeastLessThan_union_disj less_eq_real_def map_add_split map_le_iff_map_add_commute map_le_via_restrict)
  apply (metis (full_types) dual_order.trans ivl_subset less_eq_real_def map_le_implies_dom_le map_le_refl map_le_via_restrict)  
done  
  
lemma cgf_sub_cat_cases: "f \<subseteq>\<^sub>C g @\<^sub>C h \<Longrightarrow> f \<subseteq>\<^sub>C g \<or> g \<subseteq>\<^sub>C f"
  apply (transfer, auto)
  apply (rename_tac f g h i j k)
  apply (case_tac "0 < j")
  apply (auto)
  apply (case_tac "i \<le> j")
  apply (auto simp add: map_le_def)
done
  
lemma cgf_sum_eq_sum_conv:
  "a @\<^sub>C b = c @\<^sub>C d \<Longrightarrow> \<exists>e. a = c @\<^sub>C e \<and> e @\<^sub>C b = d \<or> a @\<^sub>C e = c \<and> b = e @\<^sub>C d"
  by (metis cgf_cat_assoc cgf_cat_left_imp_eq cgf_prefix_iff cgf_sub_cat_cases)
  
instantiation cgf :: (type) trace
begin
  definition minus_cgf :: "'a cgf \<Rightarrow> 'a cgf \<Rightarrow> 'a cgf" where
  "minus_cgf x y = x -\<^sub>m y"
instance
  apply (intro_classes)
  using cgf_cat_left_imp_eq apply blast
  using cgf_zero_sum_left apply blast
  apply (simp add: cgf_sum_eq_sum_conv)
  apply (simp add: monoid_le_ttrace)
  apply (simp add: less_cgf_def)
  apply (simp add: minus_cgf_def)
done
end

text {* Thus we can show that our operators form a trace algebra. In order to show this we 
  also have to construct the subtraction operator which we obtain from the derived monoidal subtraction, $x -_m y$. *}
  
lemma cgf_sub_end:
  assumes "f \<le> g"
  shows "end\<^sub>C f \<le> end\<^sub>C g"
proof -
  obtain f' where "g = f + f'"
    by (meson assms monoid_le_def monoid_le_ttrace)
  thus ?thesis
    by (simp add: cgf_end_cat)
qed

lemma cgf_dom_empty [simp]: "dom\<^sub>C([]\<^sub>C) = {}"
  by (transfer, simp)

lemma cgf_dom: "dom\<^sub>C(f) = {0..<end\<^sub>C f}"
  apply (cases "f = []\<^sub>C")
  apply (auto)
  apply (transfer, auto)
  apply (transfer, auto)
  using less_eq_real_def apply auto[1]
  apply (transfer, auto)
  using less_eq_real_def apply auto
done

text {* We now show a few more properties about the domain of a contiguous function, namely that
  the @{term "map\<^sub>C"} function is domain preserving, that the domain of an empty function is empty,
  and that the domain of a function is the set [0..end(f)). *}

lemma cgf_prefix_dom:
  "f \<subseteq>\<^sub>C g \<Longrightarrow> dom\<^sub>C(f) \<subseteq> dom\<^sub>C(g)"
  by (simp add: cgf_dom cgf_sub_end)

text {* If function $f$ is a subfunction of $g$ then $f$ can be no longer than $g$. Similarly,
  the domeain of the $f$ would be a subset of the domain of $g$. *}

lemma cgf_restrict_le: "t \<restriction>\<^sub>C n \<le> t"
  by (transfer, auto simp add: map_le_def)

lemma cgf_end_restrict [simp]: "\<lbrakk> 0 \<le> n; n \<le> end\<^sub>C f \<rbrakk> \<Longrightarrow> end\<^sub>C (f \<restriction>\<^sub>C n) = n"
  by (transfer, auto)

lemma cgf_restrict_less: "\<lbrakk> 0 \<le> n ; n < end\<^sub>C(t) \<rbrakk> \<Longrightarrow> t \<restriction>\<^sub>C n < t"
  by (metis cgf_end_restrict cgf_restrict_le dual_order.strict_iff_order)

text {* Restriction yields a function which is guaranteed to be no longer than the original,
  and is strictly less than the original provided that $n$ is positive and is less than the original
  length. *}

lemma cgf_left_mono_iff: "f @\<^sub>C g \<le> f @\<^sub>C h \<longleftrightarrow> g \<le> h"
  using add_le_imp_le_left add_left_mono by blast

text {* The next two facts are simply derived from the trace algebra: the alternative definition
  of prefix, and that concatenation is monotone in its second argument. *}

lemma cgf_end_map [simp]: "end\<^sub>C (map\<^sub>C f g) = end\<^sub>C g"
  by (transfer, auto simp add: dom_if)

lemma cgf_restrict_empty [simp]: "[]\<^sub>C \<restriction>\<^sub>C n = []\<^sub>C"
  by (transfer, simp)

text {* We also show some properties about the restriction operator: restricting an empty
  function has no effect, and the end of a restricted function yields the request end value,
  provided that the function is no shorter than this value. *}

lemma cgf_end_force [simp]: "n \<ge> 0 \<Longrightarrow> end\<^sub>C (f !\<^sub>C n) = n"
  apply (transfer, auto simp add: dom_if)
  apply (rename_tac n f i)
  apply (subgoal_tac "{x. 0 \<le> x \<and> x < n} = {0..<n}")
  apply (auto)
done

text {* Conversley, forcing a function to be a particular length will always yield a function of
  that length. *}

lemma cgf_map_indep:
  "end\<^sub>C f = end\<^sub>C g \<Longrightarrow> map\<^sub>C (\<lambda>(i, x). \<langle>g\<rangle>\<^sub>C i) f = g"
  apply (transfer, auto, rule ext, auto)
  apply (metis (mono_tags) atLeastLessThan_iff domD not_le option.sel)
  apply fastforce
  apply (metis atLeastLessThan_iff domIff less_eq_real_def)
done

text {* The above property shows that mapping a function to take the values of another function
  of the same length will yield exactly the latter contiguous function. *}

lemma cgf_restrict_map [simp]: "(map\<^sub>C f g) \<restriction>\<^sub>C n = map\<^sub>C f (g \<restriction>\<^sub>C n)"
  apply (transfer, auto simp add: restrict_map_def, rule ext, auto simp add: domD)
  apply (metis atLeastLessThan_iff domI option.distinct(1))
done

text {* Restriction also distributes through contiguous function maps. *}

lemma cgf_restrict_restrict [simp]: "(g \<restriction>\<^sub>C m) \<restriction>\<^sub>C n = g \<restriction>\<^sub>C (min m n)"
  apply (auto simp add: min_def)
  apply (transfer, simp add: min.absorb_iff2 min.commute)
  apply (transfer, auto simp add: min_def)
done

text {* Restricting a function twice yields a restriction with the minimum value of the two restrictions. *}

lemma cgf_map_empty [simp]:
  "map\<^sub>C f []\<^sub>C = []\<^sub>C"
  by (transfer, simp)

text {* Mapping over an empty function yields an empty function. *}

lemma cgf_map_apply [simp]:
  assumes "0 \<le> x" "x < end\<^sub>C(g)"
  shows "\<langle>map\<^sub>C f g\<rangle>\<^sub>C x = f (x, \<langle>g\<rangle>\<^sub>C x)"
proof -
  have "x \<in> dom\<^sub>C(g)"
    using assms cgf_dom by fastforce
  thus ?thesis
    by (transfer, auto simp add: dom_if)
qed

text {* Application of a value $x$ to a contiguous function mapped through $g$ is equivalent to
  applying the function to the given value and function value at that point. *}

lemma cgf_map_map: "map\<^sub>C f (map\<^sub>C g h) = map\<^sub>C (\<lambda> (i, x). f (i, g (i, x))) h"
  by (transfer, auto simp add: dom_if)

definition cgf_lens :: "('a cgf \<Longrightarrow> '\<alpha>) \<Rightarrow> ('b \<Longrightarrow> 'a) \<Rightarrow> ('b cgf \<Longrightarrow> '\<alpha>)" where
[lens_defs]: "cgf_lens X Y =
  \<lparr> lens_get = \<lambda> s. map'\<^sub>C get\<^bsub>Y\<^esub> (get\<^bsub>X\<^esub> s)
  , lens_put = \<lambda> s v. put\<^bsub>X\<^esub> s (map\<^sub>C (\<lambda> (i, x). put\<^bsub>Y\<^esub> x (\<langle>v\<rangle>\<^sub>C i)) (get\<^bsub>X\<^esub> s !\<^sub>C (end\<^sub>C v))) \<rparr>"

lemma cgf_weak_lens: "\<lbrakk> weak_lens X; weak_lens Y \<rbrakk> \<Longrightarrow> weak_lens (cgf_lens X Y)"
  by (unfold_locales, auto simp add: cgf_lens_def cgf_map_map cgf_map_indep)

text {* Finally we show a few properties about subtraction that are also derived from the trace
  algebra. *}

lemma cgf_cat_minus_prefix:
  "f \<le> g \<Longrightarrow> g = f @\<^sub>C (g - f)"
  by (simp add: diff_add_cancel_left')

lemma cgf_apply_minus [simp]: "\<lbrakk> 0 \<le> x; f \<le> g \<rbrakk> \<Longrightarrow> \<langle>g - f\<rangle>\<^sub>C x = \<langle>g\<rangle>\<^sub>C (x + end\<^sub>C(f))"
  by (metis add_diff_cancel cgf_cat_ext_last cgf_cat_minus_prefix le_add_same_cancel2)

lemma cgf_end_minus: "g \<le> f \<Longrightarrow> end\<^sub>C(f-g) = end\<^sub>C(f)-end\<^sub>C(g)"
  by (auto simp add: cgf_prefix_iff cgf_end_cat)

lemma list_concat_minus_list_concat: "(f @\<^sub>C g) - (f @\<^sub>C h) = g - h"
  using trace_class.add_diff_cancel_left' by blast

text {* The following function constructs a contiguous function from a given end point and total
  function. *}
    
lift_definition cgf_mk :: "real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> 'a cgf" ("mk\<^sub>C") is
"\<lambda> l f. [t \<mapsto> f t | t. 0 \<le> t \<and> t < l]"
  apply (auto simp add: graph_map_dom)
  apply (rename_tac l f)
  apply (case_tac "l < 0")
  apply (rule_tac x="0" in exI)
  apply (simp) 
  apply (rule_tac x="l" in exI)  
  apply (auto simp add: image_iff)
done
    
lemma cgf_mk_apply [simp]: "\<lbrakk> 0 \<le> x; x < l \<rbrakk> \<Longrightarrow> \<langle>mk\<^sub>C l f\<rangle>\<^sub>C x = f x"
  by (transfer, simp)
    
lemma cgf_mk_end [simp]: 
  "0 \<le> l \<Longrightarrow> end\<^sub>C(mk\<^sub>C l f) = l"
  by (transfer, simp add: Sup'_interval')

lemma cgf_mk_le_0 [simp]: "l \<le> 0 \<Longrightarrow> mk\<^sub>C l f = []\<^sub>C"
  by (transfer, auto)
    
(*<*)
end
(*>*)