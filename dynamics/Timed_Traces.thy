section {* Timed Traces *}

theory Timed_Traces
imports Contiguous_Functions
begin

subsection {* Piecewise continuity *}
  
text {* With the foundation of contiguous functions established, we can now proceed to define
  piecewise continuous and convergent functions. We begin with a locale that gives the necessary
  invariants on a piecewise continuous function. *}

locale pc_interval =
  fixes I :: "real list" and f :: "'a::topological_space cgf"
  assumes I_range: "set(I) \<subseteq> {0 .. end\<^sub>C f}"
  and I_bounds: "{0, end\<^sub>C f} \<subseteq> set(I)"
  and I_sorted [simp]: "sorted I"
  and I_distinct [simp]: "distinct I"
  and continuous_segments [intro]: "\<And> i. i < length(I) - 1 \<Longrightarrow> continuous_on {I!i ..< I!(Suc i)} \<langle>f\<rangle>\<^sub>C"
begin

text {* Piecewise continuity means that there exists an ordered list $I$ of points (equivalently 
    a finite set) within in the contiguous function $f$, such that each inter-point segment is 
    continuous. This list can therefore be thought of as as a finite set of segments.
    In order to allow the specification of continuity we require that the range type of $f$ is a suitable topological
    space, via a type class restriction. We characterise piecewise continuity with five axioms which 
    are given above. These require, respectively, that:

    \begin{itemize}
      \item the points within $I$ are all within the function domain;
      \item the beginning and end point are both within the domain;
      \item $I$ is sorted list;
      \item no point in $I$ appears twice -- it is a distinct list;
      \item $f$ is continuous between each point $i$ and its successor.
    \end{itemize}

    The function predicate @{term "continuous_on g A"} describes that a function $g$ is continuous
    on the sub-domain $A$. From these axioms we can derive some theorems, which are listed below.
 *}

  lemma I_length [simp]: "length(I) > 0"
    using I_bounds by auto

  lemma ne_f_I_length [simp]: "f \<noteq> []\<^sub>C \<Longrightarrow> length(I) > Suc 0"
    by (metis I_bounds I_length Suc_lessI cgf_end_0_iff in_set_conv_nth insert_subset less_Suc0)

  text {* The length of the point list cannot be empty, and assuming the contiguous function is non-empty
    then there must be more than one point. *}

  lemma I_hd [simp]: "hd(I) = 0"
    by (metis I_bounds I_range I_sorted atLeastAtMost_iff atLeastLessThan_empty 
              atLeastLessThan_empty_iff contra_subsetD empty_iff hd_in_set insert_subset 
              less_eq_real_def list.exhaust_sel list.set(1) sorted_Cons tl_element)

  lemma I_last: "last(I) = end\<^sub>C(f)"
    by (metis I_bounds I_range I_sorted atLeastAtMost_iff dual_order.antisym empty_iff 
              insert_subset last_in_set list.set(1) sorted_last subsetCE)
    
  text {* The first point is always 0, and the final point is the end point of the function. *}

  lemma tl_I_ge_0 [simp]: "x \<in> set (tl I) \<Longrightarrow> x > 0"
    by (metis I_distinct I_hd I_length I_sorted distinct.simps(2) hd_Cons_tl length_greater_0_conv 
              less_eq_real_def sorted_Cons)

  text {* Any point after the initial point must be strictly positive. *}

  lemma I_z [simp]: "0 \<in> set(I)"
    using I_bounds by blast

  lemma I_nz [simp]: "x \<in> set(I) \<Longrightarrow> 0 \<le> x"
    using I_range atLeastAtMost_iff by blast

  text {* One of the points is 0, and every element is no less than 0. *}

  lemma nth_I_nz: "i < length I \<Longrightarrow> 0 \<le> I!i"
    by simp

  lemma I_le_end [simp]: "x \<in> set(I) \<Longrightarrow> x \<le> end\<^sub>C(f)"
    using I_last I_sorted sorted_last by fastforce

end

text {* In addition to piecewise continuous function we also define the following locale that
  characterises piecewise convergent functions. Specifically, it characterises functions where
  each continuous segment also converges to a given limit. We will make this requirement of
  our timed traces to ensure that the "final" value of a trace can always be obtained. *}

locale pc_cvg_interval = pc_interval +
  -- {* The following assumption requires that each continuous segment also converges to a limit *}
  assumes cvg_segments [intro]: 
    "\<And> i. i < length(I) - 1 \<Longrightarrow> \<exists> L. (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I!(Suc i)) within {I!i ..< I!(Suc i)})"

text {* We characterise piecewise convergent functions $f$ by requiring that for each segment $(i, i+1)$ 
  there exists a limit $L$ which the function tends to at point $i+1$. *}

definition piecewise_continuous :: "'a::topological_space cgf \<Rightarrow> bool" where
"piecewise_continuous f = (\<exists> I. pc_interval I f)"

definition piecewise_convergent :: "'a::topological_space cgf \<Rightarrow> bool" where
"piecewise_convergent f = (\<exists> I. pc_cvg_interval I f)"

text {* Functions are respectively piecewise continuous or convergent, if there exists an $I$
  that characterises the piecewise segments.  *}

lemma piecewise_continuous_empty [simp]: "piecewise_continuous []\<^sub>C"
  by (auto simp add: piecewise_continuous_def, rule_tac x="[0]" in exI, 
      simp add: pc_interval_def cgf_end_empty)

lemma piecewise_convergent_empty [simp]: "piecewise_convergent []\<^sub>C"
   by (auto simp add: piecewise_convergent_def, rule_tac x="[0]" in exI, 
       simp add: pc_interval_def pc_cvg_interval_def pc_cvg_interval_axioms_def cgf_end_empty)

text {* Empty contiguous functions are both piecewise continuous and piecewise convergent. *}
  
subsection {* Concatenation of piecewise continuous functions *}

text {* A major result of this theory is to show that the a piecewise continuous function can always
  be decomposed into two piecewise continuous functions with the help of concatenation operator.
  This requires a lot of lemmas and theorems which we will develop in this section. We first prove 
  some continuity properties about transformed functions. *}

lemma continuous_on_linear: 
  fixes A :: "real set"
  shows "continuous_on A (\<lambda> x. m*x + a)"
proof (clarsimp simp add: continuous_on_def)
  fix x
  show "((\<lambda>x. m * x + a) \<longlongrightarrow> m * x + a) (at x within A)"
    by (force intro: tendsto_add[of "(\<lambda>x. m * x)" "m * x" "at x within A" "\<lambda>_. a" a, simplified] tendsto_mult)
qed

text {* This property states that any linear function on real number is everywhere continuous. *}

lemma continuous_on_shift:
  fixes f :: "real \<Rightarrow> 'b::topological_space"
  assumes "continuous_on A f"
  shows "continuous_on {x + y | x. x \<in> A} (\<lambda> x. f (x - y))" 
proof -
  have "((\<lambda>x. x - y) ` {x + y |x. x \<in> A}) = A"
    by (force simp add: image_Collect)
  moreover have "continuous_on {x + y |x. x \<in> A} (\<lambda>x. x - y)"
    using continuous_on_linear[of "{x + y |x. x \<in> A}" 1 "- y"] by (simp)
  ultimately show ?thesis 
  using continuous_on_compose[of "{x + y | x. x \<in> A}" "\<lambda> x. x - y" f]
    by (simp add: assms)
qed

text {* This property shows that, given a continuous function $f$ on $A$, then if we shift the 
  the function to right by $y$, the resulting function is continuous on a shifted domain. *}

lemma continuous_on_cgf_cat_left:
  assumes "j \<le> end\<^sub>C f" "continuous_on {i..<j} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
  shows "continuous_on {i..<j} \<langle>f\<rangle>\<^sub>C"
proof -
  have "continuous_on {i..<j} \<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longleftrightarrow> continuous_on {i..<j} \<langle>f\<rangle>\<^sub>C"
    by (rule continuous_on_cong, auto, meson assms(1) cgf_cat_ext_first le_less_trans not_le)
  thus ?thesis
    using assms by blast
qed

lemma continuous_on_cgf_cat_right:
  assumes "0 \<le> i" "continuous_on {i+end\<^sub>C(f)..<j+end\<^sub>C(f)} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
  shows "continuous_on {i..<j} \<langle>g\<rangle>\<^sub>C"
proof -
  have "{x - end\<^sub>C f |x. i + end\<^sub>C f \<le> x \<and> x < j + end\<^sub>C f} = {i..<j}"
    by (auto, metis add_diff_cancel add_le_cancel_right add_less_cancel_right)
  hence "continuous_on {i..<j} (\<lambda>x. \<langle>f @\<^sub>C g\<rangle>\<^sub>C (x + end\<^sub>C f))"
    using continuous_on_shift[of _ _ "- end\<^sub>C f",OF assms(2), simplified] by (simp)
  moreover from assms(1) have "continuous_on {i..<j} (\<lambda>x. \<langle>f @\<^sub>C g\<rangle>\<^sub>C (x + end\<^sub>C f)) = ?thesis"
    by (rule_tac continuous_on_cong, auto simp add: cgf_cat_ext_last)
  ultimately show ?thesis
    by simp
qed

lemma continuous_on_cgf_cat_last:
  assumes "end\<^sub>C(f) \<le> i" "continuous_on {i-end\<^sub>C(f)..<j-end\<^sub>C(f)} \<langle>g\<rangle>\<^sub>C"
  shows "continuous_on {i..<j} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
proof -
  have "{x + end\<^sub>C f |x. i - end\<^sub>C f \<le> x \<and> x < j - end\<^sub>C f} = {i..<j}"
    by (auto, metis add_diff_cancel diff_add_eq diff_right_mono diff_strict_right_mono)
  hence "continuous_on {i..<j} (\<lambda> x. \<langle>g\<rangle>\<^sub>C (x-end\<^sub>C(f)))"
    using continuous_on_shift[of _ _ "end\<^sub>C f",OF assms(2)] by simp
  moreover from assms(1) have "continuous_on {i..<j} (\<lambda>x. \<langle>g\<rangle>\<^sub>C (x - end\<^sub>C f)) = ?thesis"
    by (rule_tac continuous_on_cong, auto intro: continuous_on_cong simp add: cgf_cat_ext_last)
  ultimately show ?thesis by blast
qed

text {* These previous three theorems show that if the concatenation of two contiguous functions is continuous,
  then the functions themselves must also be continuous. *}

definition "left_pc_interval n I = (takeWhile (\<lambda> x. x < n) I) @ [n]"

definition "right_pc_interval n I = 0 # map (\<lambda> x. x - n) (dropWhile (\<lambda> x. x \<le> n) I)"

text {* An important part of manipulating timed traces is that we can decompose them. In order to do
  this, and ensure closure of the operators, we need to show that decomposition of a piecewise
  continuous function results in two piecewise continuous segments, each of which will be characterised
  by its own piecewise continuous segment set. These two functions extract the 
  set of left and right segments, respectively, of the corresponding segment set $I$ about a point $n$. 
  The tricky part is when $n$ falls within one of the segments in $I$. This being the case the
  segment must be split, with one half placed in the left and half in the right segment set. 

  Function @{term left_pc_interval} is written in terms of the @{term "takeWhile P xs"} function which
  builds a list corresponding to the maximal prefix of $xs$ with elements which satisfy the predicate $P$.
  In this instance we extract the elements that are strictly less than the given point, and then add
  the point on the end to complete the final interval. The second function, @{term right_pc_interval}, 
  conversely takes the remainder of the list, and shifts each element to the left by $n$ (so as to
  construct a segment set for the right trace only). Finally, it prepends the list with $0$ to denote
  the beginning of the first segment. *}

lemma set_left_pc_interval:
  "sorted I \<Longrightarrow> set (left_pc_interval n I) = insert n {x |x. x \<in> ran\<^sub>l I \<and> n > x}"
  by (auto dest: set_takeWhileD simp add: left_pc_interval_def set_dropWhile_le 
                 image_Collect set_takeWhile_less_sorted)

lemma set_right_pc_interval:
  "sorted I \<Longrightarrow> set (right_pc_interval n I) = insert 0 {x - n |x. x \<in> ran\<^sub>l I \<and> n < x}"
  by (simp add: right_pc_interval_def set_dropWhile_le image_Collect)

text {* These two properties show the set of points that will be present in the left and right
  segment sets, respectively. We will next prove that both the left and right segment sets characterise
  piecewise continuity for the elements of a decomposed piecewise continuous functions. *}

lemma pc_interval_left:
  assumes "pc_interval I (f @\<^sub>C g)"
  shows "pc_interval (left_pc_interval (end\<^sub>C f) I) f"
proof
  interpret I: pc_interval I "(f @\<^sub>C g)" by (simp add: assms)

  -- {* We first need to show the basic properties of the decomposed interval; that its points
        lie within the range of function $f$ and that is is sorted and distinct. These properties
        follow relatively easily. *}

  show "set (left_pc_interval (end\<^sub>C f) I) \<subseteq> {0..end\<^sub>C f}"
    by (auto simp add: set_left_pc_interval)
  show "{0, end\<^sub>C f} \<subseteq> ran\<^sub>l (left_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: set_left_pc_interval dual_order.strict_iff_order)
  show "sorted (left_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: left_pc_interval_def sorted_takeWhile sorted_append, 
        meson less_eq_real_def set_takeWhileD)
  show "distinct (left_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: left_pc_interval_def, meson less_irrefl set_takeWhileD)

  -- {* The complicated part of the proof is to show that each of the segments, characterised
        by $i$ and $i+1$, is continuous. *}

  show "\<And>i. i < length (left_pc_interval (end\<^sub>C f) I) - 1 \<Longrightarrow>
         continuous_on {left_pc_interval (end\<^sub>C f) I ! i..<left_pc_interval (end\<^sub>C f) I ! Suc i} \<langle>f\<rangle>\<^sub>C"
  proof (rule continuous_on_cgf_cat_left[of _ _ _ g])
    fix i
    assume i:"i < length (left_pc_interval (end\<^sub>C f) I) - 1"
    hence ef_nz: "end\<^sub>C f > 0"
      by (auto simp add: left_pc_interval_def nth_append takeWhile_nth, 
          metis I.nth_I_nz le_less_trans length_takeWhile_le not_less nth_mem 
                set_takeWhileD takeWhile_nth)
    from i show "left_pc_interval (end\<^sub>C f) I ! Suc i \<le> end\<^sub>C f"
      by (auto simp add: left_pc_interval_def nth_append, meson less_eq_real_def nth_mem set_takeWhileD)
    from i show "continuous_on {left_pc_interval (end\<^sub>C f) I ! i..<
                                left_pc_interval (end\<^sub>C f) I ! Suc i} \<langle>f + g\<rangle>\<^sub>C"
    proof (cases "Suc i < length (takeWhile (\<lambda>x. x < end\<^sub>C f) I)")
      case True
      with i show ?thesis
        by (auto simp add: left_pc_interval_def nth_append, metis I.I_length I.continuous_segments 
                 One_nat_def Suc_lessD Suc_less_eq Suc_pred length_takeWhile_le 
                 less_le_trans takeWhile_nth)
    next
      case False
      let ?l = "length (takeWhile (\<lambda>x. x < end\<^sub>C f) I)"
      from False i have i_def: "i = ?l - 1"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth)
      have lI: "last I \<ge> end\<^sub>C f"
        by (simp add: I.I_last cgf_sub_end)
      have ltI: "?l > 0"
          by (metis One_nat_def add.left_neutral cancel_comm_monoid_add_class.diff_zero 
                    diff_Suc_Suc i left_pc_interval_def length_append length_greater_0_conv 
                    less_nat_zero_code list.size(3) list.size(4))
      hence I_ge_end:"I ! Suc (?l - 1) \<ge> end\<^sub>C f"
      proof -
        from lI have "I ! length (takeWhile (\<lambda>x. x < end\<^sub>C f) I) \<ge> end\<^sub>C f"
          by (rule_tac nth_length_takeWhile_less, auto, metis I.I_z empty_iff last_in_set list.set(1))
        with ltI show ?thesis
          by simp
      qed
      have c: "continuous_on {I ! (?l - 1)..<I ! Suc(?l - 1)} \<langle>f + g\<rangle>\<^sub>C"
      proof -
        have "length (takeWhile (\<lambda>x. x < end\<^sub>C f) I) < length I"
          using I.I_length lI last_in_set length_takeWhile_less by fastforce
        thus ?thesis
          using ltI by (rule_tac I.continuous_segments, auto, linarith)
      qed
      have "continuous_on {I ! (?l - 1)..<end\<^sub>C f} \<langle>f + g\<rangle>\<^sub>C"
        by (rule continuous_on_subset[OF c], auto, metis I_ge_end One_nat_def)
      with False i i_def show ?thesis
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth)
    qed
  qed
qed
    
text {* The next proof dualises the above proof. *}

lemma pc_interval_right:
  assumes "pc_interval I (f @\<^sub>C g)"
  shows "pc_interval (right_pc_interval (end\<^sub>C f) I) g"
proof
  interpret I: pc_interval I "(f @\<^sub>C g)" by (simp add: assms)
  obtain I' where I': "I = 0 # I'" "sorted I'" "distinct I'"
    by (metis I.I_distinct I.I_hd I.I_length I.I_sorted distinct.simps(2) hd_Cons_tl 
              length_greater_0_conv sorted_Cons)
  show "set (right_pc_interval (end\<^sub>C f) I) \<subseteq> {0..end\<^sub>C g}"
    by (auto simp add: set_right_pc_interval, metis I.I_le_end 
             cancel_ab_semigroup_add_class.add_diff_cancel_left' 
             cgf_end_cat diff_strict_right_mono less_eq_real_def)
  show "{0, end\<^sub>C g} \<subseteq> set (right_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: set_right_pc_interval, 
        metis I.I_last I.I_z cancel_ab_semigroup_add_class.add_diff_cancel_left' cgf_end_cat 
        cgf_end_ge_0 diff_gt_0_iff_gt last_in_set length_greater_0_conv length_pos_if_in_set 
        less_eq_real_def)
  show "sorted (right_pc_interval (end\<^sub>C f) I)"
    apply (auto intro!:sorted_map sorted_dropWhile simp add: right_pc_interval_def sorted_Cons mono_def)
    using I.I_sorted dropWhile_sorted_le_above less_eq_real_def apply blast
  done
  show "distinct (right_pc_interval (end\<^sub>C f) I)"
    by (auto simp add: right_pc_interval_def set_dropWhile_le distinct_map inj_onI)
  show "\<And>i. i < length (right_pc_interval (end\<^sub>C f) I) - 1 \<Longrightarrow>
         continuous_on {right_pc_interval (end\<^sub>C f) I ! i..<right_pc_interval (end\<^sub>C f) I ! Suc i} \<langle>g\<rangle>\<^sub>C"
  proof -
    fix i
    assume i: "i < length (right_pc_interval (end\<^sub>C f) I) - 1"
    hence egnz: "end\<^sub>C g > 0"
      by (simp add: right_pc_interval_def, metis I.I_le_end I.I_sorted add.right_neutral cgf_end_0_iff cgf_end_ge_0 dropWhile_sorted_le_above less_eq_real_def not_less nth_mem set_dropWhileD)      
    let ?i' = "length (takeWhile (\<lambda>x. x \<le> end\<^sub>C f) I)"
    show "continuous_on {right_pc_interval (end\<^sub>C f) I ! i..<right_pc_interval (end\<^sub>C f) I ! Suc i} \<langle>g\<rangle>\<^sub>C"
    proof (cases "i = 0")
      case True 
      have "?i' < length I"
        by (metis I.I_last I.I_length add.right_neutral add_left_cancel append_Nil2 egnz  
                  cgf_end_cat le_add cgf_sub_end last_in_set le_less_trans length_0_conv 
                  length_append length_takeWhile_le not_less_iff_gr_or_eq set_takeWhileD 
                  takeWhile_dropWhile_id)
      moreover have "?i' > 0"
        by (metis I.I_sorted I.I_z Un_iff cgf_end_ge_0 dropWhile_sorted_le_above empty_iff 
                  length_greater_0_conv list.set(1) not_less set_append takeWhile_dropWhile_id)
      moreover have "continuous_on {I ! (?i'-1)..<I ! Suc(?i'-1)} \<langle>f + g\<rangle>\<^sub>C"
        by (metis I.I_length I.pc_interval_axioms One_nat_def Suc_less_eq Suc_pred
                  pc_interval.continuous_segments calculation)
      moreover have "{end\<^sub>C f..<I ! Suc(?i'-1)} \<subseteq> {I ! (?i'-1)..<I ! Suc(?i'-1)}"
        by (auto, metis (no_types, lifting) One_nat_def Suc_pred calculation(2) lessI 
                  nth_append nth_mem set_takeWhileD takeWhile_dropWhile_id)
      ultimately have "continuous_on {end\<^sub>C f..<I ! ?i'} \<langle>f + g\<rangle>\<^sub>C"
        by (metis (no_types, lifting) One_nat_def Suc_pred continuous_on_subset)
      with True i show ?thesis
        by (auto simp add: right_pc_interval_def dropWhile_nth) 
           (rule continuous_on_cgf_cat_right[of _ f], auto)
    next
      case False
      with i have i'l: "i + ?i' - Suc 0 < length I - 1"
      proof -
        from False i 
        have "i + ?i' - 1 < length (takeWhile (\<lambda>x. x \<le> end\<^sub>C f) I 
                                    @ dropWhile (\<lambda>x. x \<le> end\<^sub>C f) I) - 1"
          by (unfold length_append, auto simp add: right_pc_interval_def)
        thus ?thesis
          by (auto)
      qed
      with False i have "end\<^sub>C f \<le> I ! (i + ?i' - 1)"
        by (rule_tac nth_le_takeWhile_ord, auto)
      moreover have "continuous_on {I ! (i + ?i' - 1)..<I ! Suc (i + ?i' - 1)} \<langle>f + g\<rangle>\<^sub>C"
        by (auto intro: i'l)
      ultimately show ?thesis using i False
        by (auto intro: continuous_on_cgf_cat_right[of _ f] 
                 simp add: right_pc_interval_def dropWhile_nth)        
    qed
  qed    
qed

text {* Having proved that a piecewise continuous function can be decomposed into two piecewise
  continuous functions, we now prove the same property but for convergent functions. The first
  step is to show some properties about limits. *}

lemma Lim_cgf_plus_shift: 
  assumes "0 \<le> m" "m < n"
  shows "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (n+end\<^sub>C(f)) within {m+end\<^sub>C(f)..<n+end\<^sub>C(f)})
         \<longleftrightarrow> 
         (\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) (at n within {m..<n})" 
  (is "?L1 \<longleftrightarrow> ?L2")
proof -
  have "?L1 \<longleftrightarrow> ((\<langle>g\<rangle>\<^sub>C \<circ> (\<lambda> x. x - end\<^sub>C(f))) \<longlongrightarrow> L) (at (n+end\<^sub>C(f)) within {m+end\<^sub>C(f)..<n+end\<^sub>C(f)})"
    apply (rule Lim_cong_within, auto)
    using assms(1) cgf_cat_ext_last le_add_same_cancel2 order_trans by (blast intro: Lim_cong_within)
  also have "... = ?L2"
    by (simp add: filtermap_within_range_minus tendsto_compose_filtermap)
  finally show ?thesis .
qed

text {* Theorem @{thm [source] Lim_cgf_plus_shift} shows that a composed function converges to a point beyond
  the end of the first (left) function if and only if the second function also conveges to this
  point, but with shifted indices. We then use this properties to show that the a piecewise
  convergent function can be decomposed into two. *}

lemma pc_cvg_interval_left:
  assumes "pc_cvg_interval I (f @\<^sub>C g)"
  shows "pc_cvg_interval (left_pc_interval (end\<^sub>C f) I) f" (is "pc_cvg_interval ?RI f")
proof -
  interpret I: pc_cvg_interval I "(f @\<^sub>C g)" by (simp add: assms) 
  interpret lI: pc_interval "(left_pc_interval (end\<^sub>C f) I)" f
    using I.pc_interval_axioms pc_interval_left by auto
  have "\<And>i. i < length (left_pc_interval (end\<^sub>C f) I) - 1 \<Longrightarrow>
         \<exists>L. (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L)
             (at (left_pc_interval (end\<^sub>C f) I ! Suc i) 
              within {left_pc_interval (end\<^sub>C f) I ! i..<left_pc_interval (end\<^sub>C f) I ! Suc i})"
  proof -
    let ?i' = "length (takeWhile (\<lambda>x. x < end\<^sub>C f) I)"
    fix i
    assume i: "i < length (left_pc_interval (end\<^sub>C f) I) - 1"
    hence ef_nz: "end\<^sub>C f > 0"
      by (auto simp add: left_pc_interval_def nth_append takeWhile_nth, 
          metis I.nth_I_nz le_less_trans length_takeWhile_le not_less nth_mem 
                set_takeWhileD takeWhile_nth)

    show "\<exists>L. (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L)
               (at (left_pc_interval (end\<^sub>C f) I ! Suc i) 
                within {left_pc_interval (end\<^sub>C f) I ! i..<left_pc_interval (end\<^sub>C f) I ! Suc i})"
    proof (cases "Suc i < ?i'")
      case True
      hence "left_pc_interval (end\<^sub>C f) I ! i = I ! i"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth)
      moreover have "left_pc_interval (end\<^sub>C f) I ! Suc i = I ! Suc i"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth True)
      moreover obtain L where "((\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc i) within {I ! i..<I ! Suc i}))"
        by (metis I.I_length One_nat_def Suc_less_eq Suc_pred True assms length_takeWhile_le 
                  less_le_trans pc_cvg_interval.cvg_segments)
      moreover have "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc i) within {I ! i..<I ! Suc i}) 
                      \<longleftrightarrow> (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc i) within {I ! i..<I ! Suc i})"
        by (rule Lim_cong_within, auto, 
            metis True cgf_cat_ext_first le_less_trans not_le 
            nth_mem order.asym set_takeWhileD takeWhile_nth)
      ultimately show ?thesis
        by auto
    next
      case False
      have lI: "last I \<ge> end\<^sub>C f"
        by (simp add: I.I_last cgf_sub_end)
      have ltI: "?i' > 0"
          by (metis One_nat_def add.left_neutral cancel_comm_monoid_add_class.diff_zero 
                    diff_Suc_Suc i left_pc_interval_def length_append length_greater_0_conv 
                    less_nat_zero_code list.size(3) list.size(4))       
      from False i have i_def: "i = ?i' - 1"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth)
      have "left_pc_interval (end\<^sub>C f) I ! i = I ! i"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth, 
            metis Suc_eq_plus1_left add.commute add.right_neutral 
                  cancel_ab_semigroup_add_class.add_diff_cancel_left' i left_pc_interval_def 
                  length_append list.size(3) list.size(4))
      moreover from False have "left_pc_interval (end\<^sub>C f) I ! Suc i = end\<^sub>C f"
        by (auto simp add: left_pc_interval_def nth_append takeWhile_nth, 
            metis (no_types) Suc_eq_plus1_left Suc_leI add.commute add.left_neutral 
            cancel_comm_monoid_add_class.diff_zero diff_Suc_Suc diff_is_0_eq i 
            left_pc_interval_def length_append list.size(3) list.size(4) nth_Cons')
      moreover have Ii: "I ! i < end\<^sub>C f"
        by (metis Suc_eq_plus1_left add.commute calculation(1) calculation(2) i lI.I_distinct 
                  lI.I_sorted sorted_distinct)
      moreover have I_ge_end:"I ! Suc i \<ge> end\<^sub>C f"
      proof -
        from lI have "I ! length (takeWhile (\<lambda>x. x < end\<^sub>C f) I) \<ge> end\<^sub>C f"
          by (rule_tac nth_length_takeWhile_less, auto, metis I.I_z empty_iff last_in_set list.set(1))
        with ltI show ?thesis
          by (simp add: i_def)
      qed
      obtain L where "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f})"
      proof -
        have "I ! Suc i > end\<^sub>C f \<Longrightarrow> \<exists>L. (\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f})"
        proof (rule_tac x="\<langle>g\<rangle>\<^sub>C 0" in exI)
          assume a:"I ! Suc i > end\<^sub>C f"
          have "continuous_on {I ! i..<I ! Suc i} \<langle>f + g\<rangle>\<^sub>C"
            by (rule I.continuous_segments, metis I.I_length Suc_diff_1 Suc_eq_plus1_left 
                     add.commute i_def lI last_in_set length_takeWhile_less less_diff_conv 
                     list.size(3) ltI nat.simps(3) not_less)
          thus "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> \<langle>g\<rangle>\<^sub>C 0) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f})"
            apply (simp add: continuous_on_def)
            apply (drule_tac x="end\<^sub>C f" in bspec)
            apply (metis Suc_diff_1 a atLeastLessThan_iff calculation(1) i_def left_pc_interval_def 
                         lessI ltI not_less nth_append nth_mem order.asym set_takeWhileD)
            apply (simp add: I_ge_end cgf_cat_ext_last tendsto_within_subset)
          done
        qed
        moreover have "\<exists>L. (\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc i) within {I ! i..<I ! Suc i})"
          by (metis (full_types) I.cvg_segments Ii Suc_le_eq Suc_pred' i_def lI last_conv_nth 
                    length_takeWhile_le less_SucE list.size(3) ltI not_le not_less0)

        ultimately show ?thesis using that I_ge_end
          by (fastforce)
      qed
      moreover have "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f}) 
                     \<longleftrightarrow> (\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C f) within {I ! i..<end\<^sub>C f})"
        by (rule Lim_cong_within, auto, simp add: cgf_cat_ext_first)
      ultimately show ?thesis
        by (auto)      
    qed
  qed
  thus ?thesis
    by (unfold_locales, simp)
qed

lemma pc_cvg_interval_right:
  assumes "pc_cvg_interval I (f @\<^sub>C g)"
  shows "pc_cvg_interval (right_pc_interval (end\<^sub>C f) I) g" (is "pc_cvg_interval ?RI g")
proof -
  interpret I: pc_cvg_interval I "(f @\<^sub>C g)" by (simp add: assms) 
  interpret rI: pc_interval "(right_pc_interval (end\<^sub>C f) I)" g
    by (simp add: I.pc_interval_axioms pc_interval_right)
  show ?thesis
  proof
    show "\<And>i. i < length ?RI - 1 \<Longrightarrow>
          \<exists>L. (\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?RI ! Suc i) within {?RI ! i..<?RI ! Suc i})"
    proof -
      fix i
      assume i:"i < length ?RI - 1"
      hence egnz: "end\<^sub>C g > 0"
        by (simp add: right_pc_interval_def, 
            metis I.I_le_end I.I_sorted add.right_neutral cgf_end_0_iff cgf_end_ge_0 
                  dropWhile_sorted_le_above less_eq_real_def not_less nth_mem set_dropWhileD)      
      let ?i' = "length (takeWhile (\<lambda>x. x \<le> end\<^sub>C f) I)"
      show "\<exists>L. (\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?RI ! Suc i) within {?RI ! i..<?RI ! Suc i})"
      proof (cases "i = 0")
        case True 
        have "?i' < length I"
          by (metis I.I_last I.I_length add.right_neutral add_left_cancel append_Nil2 egnz 
              cgf_end_cat le_add cgf_sub_end last_in_set le_less_trans length_0_conv length_append 
              length_takeWhile_le not_less_iff_gr_or_eq set_takeWhileD takeWhile_dropWhile_id)
        moreover have "?i' > 0"
          by (metis I.I_sorted I.I_z Un_iff cgf_end_ge_0 dropWhile_sorted_le_above empty_iff 
                    length_greater_0_conv list.set(1) not_less set_append takeWhile_dropWhile_id)
        moreover have "length (dropWhile (\<lambda>x. x \<le> end\<^sub>C f) I) > 0"
          by (metis add.right_neutral calculation(1) length_append length_greater_0_conv 
                    less_not_refl2 list.size(3) takeWhile_dropWhile_id)
        moreover have "I ! (?i'-1) \<le> end\<^sub>C f"
          by (auto, metis One_nat_def Suc_pred calculation(2) last_conv_nth last_in_set 
                    length_greater_0_conv lessI nth_append set_takeWhileD takeWhile_dropWhile_id)
        moreover have "(?i'-1) < length I - 1"
          using calculation(1) calculation(2) by linarith
        moreover 
        then obtain L 
        where "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc (?i'-1)) within {I ! (?i'-1)..<I ! Suc (?i'-1)})"
          using I.cvg_segments[of "?i'-1"] by (auto)
        moreover have "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc (?i'-1)) within {end\<^sub>C f..<I ! Suc (?i'-1)})"
          using calculation(1) calculation(2) calculation(4) calculation(6) 
                filter_upto_contract nth_length_takeWhile by fastforce
          
        ultimately show ?thesis using True
          apply (auto simp add: right_pc_interval_def dropWhile_nth)
          apply (subst Lim_cgf_plus_shift[of _ _ f g, THEN sym])
          apply (auto)
          apply (meson not_less nth_length_takeWhile)
        done
      next
        case False
        with i have i'l: "i + ?i' - Suc 0 < length I - 1"
        proof -
        from False i 
        have "i + ?i' - 1 < length (takeWhile (\<lambda>x. x \<le> end\<^sub>C f) I @ dropWhile (\<lambda>x. x \<le> end\<^sub>C f) I) - 1"
          by (unfold length_append, auto simp add: right_pc_interval_def)
        thus ?thesis
          by (auto)
        qed
        with False i have "end\<^sub>C f \<le> I ! (i + ?i' - 1)"
          by (rule_tac nth_le_takeWhile_ord, auto)
        moreover 
        then obtain L 
        where "(\<langle>f + g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (I ! Suc (i + ?i' - 1)) 
                                 within {I ! (i + ?i' - 1)..<I ! Suc (i + ?i' - 1)})"
          by (metis One_nat_def assms i'l pc_cvg_interval_axioms_def pc_cvg_interval_def)
        ultimately show ?thesis using i False
          apply (auto  simp add: right_pc_interval_def dropWhile_nth)        
          apply (subst Lim_cgf_plus_shift[of _ _ f g, THEN sym])
          apply (auto)
          apply (metis (no_types, lifting) False I.pc_interval_axioms Nat.add_diff_assoc2 
                       Suc_eq_plus1 Suc_leI add_eq_if i'l pc_interval_def sorted_distinct)
        done
      qed
    qed    
  qed
qed

text {* Having proved all these properties about the intervals of piecewise continuous functions,
  we can now lift this to the functions themselves. *}

lemma piecewise_continuous_cat_left:
  assumes "piecewise_continuous (f @\<^sub>C g)"
  shows "piecewise_continuous f"
  using assms pc_interval_left by (auto simp add: piecewise_continuous_def)

lemma piecewise_convergent_cat_left:
  assumes "piecewise_convergent (f @\<^sub>C g)"
  shows "piecewise_convergent f"
  using assms pc_cvg_interval_left by (auto simp add: piecewise_convergent_def)

lemma piecewise_continuous_cat_right:
  assumes "piecewise_continuous (f @\<^sub>C g)"
  shows "piecewise_continuous g"
  using assms pc_interval_right by (auto simp add: piecewise_continuous_def)

lemma piecewise_convergent_cat_right:
  assumes "piecewise_convergent (f @\<^sub>C g)"
  shows "piecewise_convergent g"
  using assms pc_cvg_interval_right by (auto simp add: piecewise_convergent_def)

text {* Next we need to show that the composition of two piecewise continuous functions yields
  a piecewise continuous function; the inverse direction of the above proofs. Again, we do
  this by constructing a suitable interval set, though this time we compose $I_1$ and $I_2$
  of the underlying functions by shifting $I_2$ to the right. *}

lemma pc_interval_cat:
  assumes "pc_interval I\<^sub>1 f" "pc_interval I\<^sub>2 g"
  shows "pc_interval (I\<^sub>1 @ map (op + (end\<^sub>C f)) (tl I\<^sub>2)) (f @\<^sub>C g)"
proof (cases "g = []\<^sub>C")
  case True thus ?thesis 
    by (simp, metis append_Nil2 assms(1) assms(2) cgf_end_empty last_in_set length_greater_0_conv 
                    length_map list.set_sel(2) not_less pc_interval.I_last pc_interval.I_length 
                    pc_interval.tl_I_ge_0 pc_interval_def sorted_last)
next
  case False note gne = this
  hence gegz: "end\<^sub>C(g) > 0"
    using cgf_end_0_iff cgf_end_ge_0 less_eq_real_def by auto 

  interpret I\<^sub>1: pc_interval I\<^sub>1 f by (simp add: assms)
  interpret I\<^sub>2: pc_interval I\<^sub>2 g by (simp add: assms)

  let ?I = "I\<^sub>1 @ map (op + (end\<^sub>C f)) (tl I\<^sub>2)"

  have "ran\<^sub>l ?I \<subseteq> {0..end\<^sub>C f+end\<^sub>C g}"
    using I\<^sub>2.I_length list.set_sel(2) by (force simp add: add_increasing2 less_imp_le)

  moreover have "end\<^sub>C f+end\<^sub>C g \<in> set(?I)"
    using I\<^sub>2.I_bounds cgf_end_0_iff gne tl_element by fastforce 

  moreover have "sorted ?I"
    by (auto intro!:sorted_map monoI simp add: sorted_append sorted_tl)
       (metis I\<^sub>1.I_le_end I\<^sub>2.tl_I_ge_0 add.commute le_add_same_cancel2 less_eq_real_def order_trans)

  moreover have "distinct ?I"
    apply (auto simp add: distinct_map distinct_tl inj_onI)
    using I\<^sub>1.I_le_end I\<^sub>2.tl_I_ge_0 by fastforce

  moreover have "\<And> i. i < length(?I) - 1 \<Longrightarrow> continuous_on {?I!i ..< ?I!(Suc i)} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
  proof (simp)
    fix i
    assume i:"i < length I\<^sub>1 + (length I\<^sub>2 - Suc 0) - Suc 0" 
    thus "continuous_on {?I!i ..< ?I!(Suc i)} \<langle>f @\<^sub>C g\<rangle>\<^sub>C"
    proof (cases "i < length I\<^sub>1 - 1")
      case True 
      hence Si: "Suc i < length I\<^sub>1"
        by (simp add: gne)

      hence "\<And> x. x \<in> {I\<^sub>1 ! i..<I\<^sub>1 ! Suc i} \<Longrightarrow> \<langle>f @\<^sub>C g\<rangle>\<^sub>C x = \<langle>f\<rangle>\<^sub>C x"
        using I\<^sub>1.I_le_end less_le_trans nth_mem by (force simp add: cgf_cat_ext_first)

      with Si show ?thesis
        by (metis I\<^sub>1.continuous_segments Suc_lessD True continuous_on_cong nth_append)
    next
      case False 
      moreover hence il: "i \<ge> length I\<^sub>1 - 1"
        by auto
      moreover hence "?I ! i = (I\<^sub>2 ! (i - (length I\<^sub>1 - Suc 0))) + end\<^sub>C(f)"
      proof (cases "i < length I\<^sub>1")
        case True
        moreover with il have "i = length I\<^sub>1 - Suc 0"
          by auto
        moreover have "I\<^sub>1 ! (length I\<^sub>1 - Suc 0) = last(I\<^sub>1)"
          using I\<^sub>1.I_length last_conv_nth by force
        moreover have "I\<^sub>2 ! 0 = hd(I\<^sub>2)"
          using I\<^sub>2.I_length hd_conv_nth by force
        ultimately show ?thesis
          by (auto simp add: nth_append I\<^sub>1.I_last)
      next
        case False
        moreover hence "i \<ge> length I\<^sub>1"
          by auto
        moreover hence "(i - length I\<^sub>1) < length (tl I\<^sub>2)"
          using i by auto
        ultimately show ?thesis
          by (auto simp add: nth_append nth_tl, 
              metis I\<^sub>1.I_length One_nat_def Suc_diff_eq_diff_pred Suc_diff_le)
      qed

      moreover have "(i - (length I\<^sub>1 - Suc 0)) < length I\<^sub>2"
        using False i by linarith
        
      moreover have "(Suc i - length I\<^sub>1) < length (tl I\<^sub>2)"
        by (metis False I\<^sub>1.I_length I\<^sub>2.I_length Nat.add_diff_assoc2 One_nat_def 
                  Suc_diff_eq_diff_pred Suc_leI Suc_pred add_diff_inverse_nat calculation(4) 
                  i length_tl less_antisym nat_neq_iff)

      moreover have "tl I\<^sub>2 ! (Suc i - length I\<^sub>1) = I\<^sub>2 ! Suc (i - (length I\<^sub>1 - Suc 0))"
        by (metis I\<^sub>1.I_length One_nat_def Suc_diff_eq_diff_pred calculation(5) nth_tl)
        
      ultimately show ?thesis
        apply (auto simp add: nth_append)
        apply (rule continuous_on_cgf_cat_last)
        apply (auto)
        apply (rule I\<^sub>2.continuous_segments)
        apply (auto)
        apply (metis I\<^sub>1.I_length One_nat_def Suc_diff_eq_diff_pred)
      done
    qed
  qed

  ultimately show "pc_interval ?I (f @\<^sub>C g)"
    by (unfold_locales, simp_all add: cgf_end_cat)
qed

text {* Thus we can show that the composition of piecewise continuous functions yields a piecewise
  continuous function. *}
  
lemma piecewise_continuous_cat:
  assumes "piecewise_continuous f" "piecewise_continuous g"
  shows "piecewise_continuous (f @\<^sub>C g)"
  using assms
  by (auto intro: pc_interval_cat simp add: piecewise_continuous_def)
     
text {* Since we've proved this property in both directions we can prove the following if and only if
  -- the composition of two functions is piecewise continuous if and only if the underlying
  functions are piecewise continuous. *}

lemma piecewise_continuous_cat_iff:
  "piecewise_continuous (f @\<^sub>C g) \<longleftrightarrow> piecewise_continuous f \<and> piecewise_continuous g"
  using piecewise_continuous_cat piecewise_continuous_cat_left piecewise_continuous_cat_right 
  by blast

text {* We then also need to show that the composition of two piecewise convergent functions yields
  a piecewise convergent function, in a similar way to the above. *}

lemma pc_cvg_interval_cat:
  assumes "pc_cvg_interval I\<^sub>1 f" "pc_cvg_interval I\<^sub>2 g"
  shows "pc_cvg_interval (I\<^sub>1 @ map (op + (end\<^sub>C f)) (tl I\<^sub>2)) (f @\<^sub>C g)"
proof -
  interpret I\<^sub>1: pc_cvg_interval I\<^sub>1 f by (simp add: assms)
  interpret I\<^sub>2: pc_cvg_interval I\<^sub>2 g by (simp add: assms)
  let ?I = "I\<^sub>1 @ map (op + (end\<^sub>C f)) (tl I\<^sub>2)"
  interpret I: pc_interval ?I "(f @\<^sub>C g)"
    using pc_interval_cat[of I\<^sub>1 f I\<^sub>2 g] I\<^sub>1.pc_interval_axioms I\<^sub>2.pc_interval_axioms by blast
  have "\<And> i. i < length(?I) - 1 \<Longrightarrow> 
              \<exists> L. (\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i)) within {?I!i ..< ?I!(Suc i)})"
  proof (simp)
    fix i
    assume i:"i < length I\<^sub>1 + (length I\<^sub>2 - Suc 0) - Suc 0" 

    thus "\<exists> L. (\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i)) within {?I!i ..< ?I!(Suc i)})"
    proof (cases "i < length I\<^sub>1 - 1")
      case True
      then 
      obtain L 
      where "(\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i)) within {?I!i ..< ?I!(Suc i)})" (is "(_ \<longlongrightarrow> _) (?F)")
        by (metis I\<^sub>1.I_length I\<^sub>1.pc_cvg_interval_axioms One_nat_def Suc_diff_Suc Suc_mono 
                  cancel_comm_monoid_add_class.diff_zero less_SucI nth_append 
                  pc_cvg_interval.cvg_segments)
      moreover have "(\<langle>f\<rangle>\<^sub>C \<longlongrightarrow> L) ?F \<longleftrightarrow> (\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longlongrightarrow> L) ?F"
        by (rule Lim_cong_within, simp_all, 
            metis I\<^sub>1.I_last I\<^sub>1.I_sorted Suc_eq_plus1 True cgf_cat_ext_first in_set_conv_nth 
                  less_diff_conv less_le_trans nth_append sorted_last)
      ultimately show ?thesis
        by blast
    next
      case False
      have Ii: "?I ! i = (I\<^sub>2 ! (i - (length I\<^sub>1 - Suc 0))) + end\<^sub>C(f)"
      proof (cases "i < length I\<^sub>1")
        case True
        moreover have "i = length I\<^sub>1 - Suc 0"
          using False calculation by linarith
        moreover have "I\<^sub>1 ! (length I\<^sub>1 - Suc 0) = last(I\<^sub>1)"
          using I\<^sub>1.I_length last_conv_nth by force
        moreover have "I\<^sub>2 ! 0 = hd(I\<^sub>2)"
          using I\<^sub>2.I_length hd_conv_nth by force
        ultimately show ?thesis
          by (auto simp add: nth_append I\<^sub>1.I_last)
      next
        case False
        moreover hence "i \<ge> length I\<^sub>1"
          by auto
        moreover hence "(i - length I\<^sub>1) < length (tl I\<^sub>2)"
          using i by auto
        ultimately show ?thesis
          by (auto simp add: nth_append nth_tl, 
              metis I\<^sub>1.I_length One_nat_def Suc_diff_eq_diff_pred Suc_diff_le)
      qed
      from i False have ISi: "?I!(Suc i) = (I\<^sub>2 ! Suc (i - (length I\<^sub>1 - Suc 0))) + end\<^sub>C(f)"
        by (auto simp add: nth_append, 
            metis I\<^sub>1.I_length I\<^sub>2.I_length Nitpick.size_list_simp(2) One_nat_def 
                  Suc_diff_eq_diff_pred gr_implies_not0 list.exhaust_sel nth_Cons_Suc)

      from ISi Ii 
      obtain L 
      where L:"(\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i) - end\<^sub>C(f)) 
                             within {?I!i - end\<^sub>C(f) ..< ?I!(Suc i) - end\<^sub>C(f)})" 
              (is "(_ \<longlongrightarrow> _) (?F1)")
        by (simp, metis False I\<^sub>1.I_length I\<^sub>2.cvg_segments Nat.add_diff_assoc2 One_nat_def Suc_leI 
                        add_diff_inverse_nat add_less_cancel_left i)
      
      have "(\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<longlongrightarrow> L) (at (?I!(Suc i)) within {?I!i ..< ?I!(Suc i)}) \<longleftrightarrow>
            ((\<langle>f @\<^sub>C g\<rangle>\<^sub>C \<circ> (\<lambda> x. x + end\<^sub>C(f))) \<longlongrightarrow> L) ?F1"
        by (simp add: tendsto_compose_filtermap filtermap_within_range_plus)
      also have "... \<longleftrightarrow> (\<langle>g\<rangle>\<^sub>C \<longlongrightarrow> L) ?F1"
      proof -
        have "i - (length I\<^sub>1 - Suc 0) < length I\<^sub>2"
            using I\<^sub>2.I_length i by linarith

        thus ?thesis
          apply (rule_tac Lim_cong_within)
          apply (auto simp add: Ii ISi)
          apply (subst cgf_cat_ext_last)
          apply (auto)
          apply (meson I\<^sub>2.nth_I_nz le_less_linear le_less_trans less_numeral_extra(3))
        done
      qed
      finally show ?thesis
        using L by blast
    qed
  qed
  thus ?thesis
    by (unfold_locales, auto)
qed   

text {* Then, we can show that the composition of two piecewise convergent functions is piecewise
  convergent, and prove a similar "if and only if". *}

lemma piecewise_convergent_cat:
  assumes "piecewise_convergent f" "piecewise_convergent g"
  shows "piecewise_convergent (f @\<^sub>C g)"
  using assms
  by (auto intro: pc_cvg_interval_cat simp add: piecewise_convergent_def)

lemma piecewise_convergent_cat_iff:
  "piecewise_convergent (f @\<^sub>C g) \<longleftrightarrow> piecewise_convergent f \<and> piecewise_convergent g"
  using piecewise_convergent_cat piecewise_convergent_cat_left piecewise_convergent_cat_right 
  by blast

subsection {* Timed trace type *}

text {* Finally, having proved the important closure properties for piecewise continuous and convergent
  functions we can now create our type of timed traces, which are piecewise convergent functions. *}

typedef (overloaded) 'a::topological_space ttrace = 
  "{f :: 'a cgf. piecewise_convergent f}"
  by (rule_tac x="[]\<^sub>C" in exI, simp)

text {* The parameter of a timed trace must be within the @{class topological_space} class so that
  we can talk about limits and continuity. As before, we need to exhibit a piecewise convergent 
  function to ensure non-emptiness of the characteristic type set, and in this case we chose the 
  empty trace. *}

setup_lifting type_definition_ttrace

text {* As for contiguous functions, we instantiate various type classes that equip our type
  with suitable algebraic operators. Note that all of these instantiations require that
  the parameter be a topological space. *}

instantiation ttrace :: (topological_space) zero
begin
  lift_definition zero_ttrace :: "'a ttrace" is 0 by auto
instance ..
end

abbreviation (input) tt_empty :: "'a::topological_space ttrace" ("[]\<^sub>t") where "[]\<^sub>t \<equiv> 0"

text {* The zero trace is the empty trace, and we give this the syntax @{term "[]\<^sub>t"}. *}

instantiation ttrace :: (topological_space) plus
begin

lift_definition plus_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> 'a ttrace"
is "op +" by (simp add: piecewise_convergent_cat)

instance ..

end

abbreviation (input) 
  tt_cat :: "'a::topological_space ttrace \<Rightarrow> 'a ttrace \<Rightarrow> 'a ttrace" (infixl "@\<^sub>t" 85) 
where "xs @\<^sub>t ys \<equiv> xs + ys"

text {* Plus is trace concatenation, which we also give the syntax of @{term "s @\<^sub>t t"}. It is here 
  where we rely on our closure property for piecewise convergent functions since lifted functions 
  must be closed under the timed trace characteristic set. *}

instance ttrace :: (topological_space) monoid_add
  by (intro_classes, (transfer, simp add: add.assoc)+)

text {* Now, since we know that timed traces are closure under plus we can prove that timed traces
  form a monoid, simply by transfer of the equivalent property on contiguous functions. *}

instantiation ttrace :: (topological_space) ord
begin

definition less_eq_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> bool" 
where "less_eq_ttrace = op \<le>\<^sub>m"
definition less_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> bool" 
where "less_ttrace a b = (a \<le> b \<and> \<not> b \<le> a)"

instance ..

end

text {* We can also define the ordering relation on traces, by lifting the order induced by 
  our summation operator (as for contiguous functions). *}

instantiation ttrace :: (topological_space) minus
begin

  definition minus_ttrace :: "'a ttrace \<Rightarrow> 'a ttrace \<Rightarrow> 'a ttrace"
  where "minus_ttrace f g = f -\<^sub>m g"

  instance ..

end

text {* Similarly, we can define the minus operator for timed traces by definition from the
  summation operator. *}

instance ttrace :: (topological_space) ordered_cancel_monoid_diff
  apply (intro_classes)
  apply (transfer, metis add_monoid_diff_cancel_left)
  apply (transfer, metis cgf_zero_sum_left)
  apply (transfer, metis cgf_cat_right_imp_eq)
  apply (simp_all add: less_eq_ttrace_def less_ttrace_def minus_ttrace_def)
done

text {* We can then show that time traces also form a cancellative monoid, and thus fulfil the
  obligations to our trace algebra. We next lift some of the other operators for contiguous functions. *}

lift_definition tt_end :: "'a::topological_space ttrace \<Rightarrow> real" ("end\<^sub>t") is "cgf_end" .

text {* @{term tt_end} retrieves the end point of a timed trace by doing so on the underlying
  contiguous function. We can then lift multiple properties about this function. *}

lemma tt_end_ge_0 [simp]: "end\<^sub>t(f) \<ge> 0" by (transfer, simp)

lemma tt_end_empty [simp]: "end\<^sub>t([]\<^sub>t) = 0" by (transfer, simp)

lemma tt_end_0_iff: "end\<^sub>t(f) = 0 \<longleftrightarrow> f = []\<^sub>t"
  by (transfer, simp add: cgf_end_0_iff)

lemma tt_end_cat: "end\<^sub>t(f @\<^sub>t g) = end\<^sub>t(f)+end\<^sub>t(g)"
  by (transfer, simp add: cgf_end_cat)

lemma tt_end_minus: "g \<le> f \<Longrightarrow> end\<^sub>t(f-g) = end\<^sub>t(f)-end\<^sub>t(g)"
  by (metis add.commute diff_add_cancel_left' diff_eq_eq tt_end_cat)

lift_definition tt_apply :: "'a::topological_space ttrace \<Rightarrow> real \<Rightarrow> 'a" ("\<langle>_\<rangle>\<^sub>t") is cgf_apply .

text {* @{term tt_apply} is function application for timed traces, likewise defined by lifting
  and transfer of properties below. *}

lemma tt_cat_ext_first [simp]: "x < end\<^sub>t f \<Longrightarrow> \<langle>f @\<^sub>t g\<rangle>\<^sub>t x = \<langle>f\<rangle>\<^sub>t x"
  by (transfer, simp add: cgf_cat_ext_first)

lemma tt_cat_ext_last [simp]: "x \<ge> end\<^sub>t f \<Longrightarrow> \<langle>f @\<^sub>t g\<rangle>\<^sub>t x = \<langle>g\<rangle>\<^sub>t (x - end\<^sub>t f)"
  by (transfer, simp add: cgf_cat_ext_last)

lemma tt_apply_minus [simp]: 
  assumes "0 \<le> x" "f \<le> g"
  shows "\<langle>g - f\<rangle>\<^sub>t x = \<langle>g\<rangle>\<^sub>t (x + end\<^sub>t(f))"
proof -
  obtain f' where f': "g = f + f'"
    using assms(2) le_iff_add by blast
  thus ?thesis
    by (simp add: assms(1))
qed 

lift_definition tt_restrict :: "'a::topological_space ttrace \<Rightarrow> real \<Rightarrow> 'a ttrace" (infix "\<restriction>\<^sub>t" 85)
is "\<lambda> f n. f \<restriction>\<^sub>C n"
proof -
  fix f :: "'a cgf" and n
  assume a: "piecewise_convergent f"
  have "f = (f \<restriction>\<^sub>C n) @\<^sub>C (f - (f \<restriction>\<^sub>C n))"
    by (simp add: cgf_cat_minus_prefix cgf_restrict_le)
  with a show "piecewise_convergent (f \<restriction>\<^sub>C n)"
    by (metis piecewise_convergent_cat_left)
qed

text {* Lifting the @{term tt_restrict} operator is a little more complicated since we need to
  show that the restricted contiguous function remains piecewise convergent. However, since
  we can rewrite our restricted function as a concatenation, and we know that concatenations
  can be decomposed to piecewise convergent parts, we can easily prove closure of the operator. 
  Then we can easily lift properties from convergent functions. *}

lemma tt_restrict_le: "t \<restriction>\<^sub>t n \<le> t"
  by (simp add: less_eq_ttrace_def monoid_le_def, transfer)
     (metis cgf_restrict_le mem_Collect_eq ordered_cancel_monoid_diff_class.le_iff_add 
            piecewise_convergent_cat_iff)

lemma tt_restrict_empty [simp]: "[]\<^sub>t \<restriction>\<^sub>t n = []\<^sub>t"
  by (transfer, simp)

lemma tt_end_restrict [simp]: "\<lbrakk> 0 \<le> n; n \<le> end\<^sub>t f \<rbrakk> \<Longrightarrow> end\<^sub>t (f \<restriction>\<^sub>t n) = n"
  by (transfer, simp)

text {* We prove the following useful property: a non-empty timed trace can always be divided into 
  two non-empty sections, which just uses our restriction operator. It is useful because
  It means we can always chop up a trace into two traces, which is important for piecewise
  reasoning about systems. *}

lemma ttrace_divisible: 
  assumes "end\<^sub>t(t) > 0"
  obtains t\<^sub>1 t\<^sub>2 where "t = t\<^sub>1 + t\<^sub>2" "end\<^sub>t(t\<^sub>1) > 0" "end\<^sub>t(t\<^sub>2) > 0"
proof -
  have "t = t \<restriction>\<^sub>t (end\<^sub>t t / 2) @\<^sub>t (t - t \<restriction>\<^sub>t (end\<^sub>t t / 2))"
    by (simp add: diff_add_cancel_left' tt_restrict_le)
  moreover have "end\<^sub>t(t \<restriction>\<^sub>t (end\<^sub>t t / 2)) > 0"
    by (simp add: assms)
  moreover have "end\<^sub>t(t - t \<restriction>\<^sub>t (end\<^sub>t t / 2)) > 0"
    by (simp add: tt_end_minus tt_restrict_le assms)
  ultimately show ?thesis
    using that by blast
qed

text {* We also show that any non-empty piecewise convergent function must exhibit a definite 
  end point $l$ that it converges to. *}

lemma piecewise_convergent_end:
  assumes "piecewise_convergent t" "0 < end\<^sub>C t"
  obtains l where "(\<langle>t\<rangle>\<^sub>C \<longlongrightarrow> l) (at_left (end\<^sub>C t))"
proof -
  obtain I where pcI: "pc_cvg_interval I t"
    using assms(1) pc_cvg_interval_def piecewise_convergent_def by blast
  have I_end: "I!(length I - 1) = end\<^sub>C(t)"
    by (metis last_conv_nth less_numeral_extra(3) list.size(3) pcI pc_cvg_interval_def 
              pc_interval.I_last pc_interval.I_length)
  let ?k = "I!(length I - 2)"
  have k_Suc: "Suc (length I - 2) = length I - 1"
    using assms(2) pcI pc_cvg_interval.axioms(1) pc_interval.ne_f_I_length by fastforce
  have k_end: "?k < end\<^sub>C t"
    by (metis I_end Suc_eq_plus1 k_Suc lessI pcI pc_cvg_interval_def pc_interval_def sorted_distinct)
  obtain L where L:"(\<langle>t\<rangle>\<^sub>C \<longlongrightarrow> L) (at (end\<^sub>C t) within {?k..<end\<^sub>C(t)})"
    by (metis I_end k_Suc lessI pcI pc_cvg_interval.axioms(2) pc_cvg_interval_axioms_def)
  from k_end have at_left_end: "(at_left (end\<^sub>C t)) = at (end\<^sub>C t) within {?k..<end\<^sub>C(t)}"
    by (rule_tac at_within_nhd[of _ "{?k<..<end\<^sub>C(t)+1}"], auto)
  from that show ?thesis
    using L at_left_end by auto
qed

text {* We then also lift this property to timed traces. *}

lemma ttrace_convergent_end:
  assumes "0 < end\<^sub>t t"
  obtains l where "(\<langle>t\<rangle>\<^sub>t \<longlongrightarrow> l) (at_left (end\<^sub>t t))"
  using assms
  by (transfer, blast intro: piecewise_convergent_end)

text {* Finally, we hide the implementation details for contiguous functions and timed traces. *}
  
lifting_update cgf.lifting
lifting_forget cgf.lifting

lifting_update ttrace.lifting
lifting_forget ttrace.lifting

end