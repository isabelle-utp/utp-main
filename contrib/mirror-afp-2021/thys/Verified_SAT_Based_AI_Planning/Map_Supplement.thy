(*
  Author: Fred Kurz
*)
theory Map_Supplement
imports Main
begin

lemma map_of_defined_if_constructed_from_list_of_constant_assignments:
  "l = map (\<lambda>x. (x, a)) xs \<Longrightarrow> \<forall>x \<in> set xs. (map_of l) x = Some a" 
proof (induction xs arbitrary: l)
  case (Cons x xs)
  let ?l' = "map (\<lambda>v. (v, a)) xs"
  from Cons.prems(1) have "l = (x, a) # map (\<lambda>v. (v, a)) xs" 
    by force
  moreover have "\<forall>v \<in> set xs. (map_of ?l') v = Some a" 
    using Cons.IH[where l="?l'"]
    by blast
  ultimately show ?case
    by auto
qed auto

\<comment> \<open> NOTE Function graph is the set of pairs (x, f x) for a (total) function f. \<close>
\<comment> \<open> TODO Remove the first premise (follows from the second). \<close>
lemma map_of_from_function_graph_is_some_if:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "set xs \<noteq> {}"
   and "x \<in> set xs"
  shows "(map_of (map (\<lambda>x. (x, f x)) xs)) x = Some (f x)" 
  using assms 
proof (induction xs arbitrary: f x)
  \<comment> \<open> NOTE Base case follows trivially from violation of assumption \<open>set xs \<noteq> {}\<close>. \<close>
  case (Cons a xs)
    thm Cons
    let ?m = "map_of (map (\<lambda>x. (x, f x)) xs)" 
    have a: "map_of (map (\<lambda>x. (x, f x)) (Cons a xs)) = ?m(a \<mapsto> f a)" 
      unfolding map_of_def
      by simp
    thus ?case 
      proof(cases "x = a")
        case False
        thus ?thesis 
        proof (cases "set xs = {}")
            \<comment> \<open> NOTE Follows from contradiction (\<open>x \<in> set (Cons a xs) \<and> set xs = {} \<and> x \<noteq> a \<equiv> \<bottom>\<close>)\<close>
            case True
            thus ?thesis 
              using Cons.prems(2)
              by fastforce
          next
            case False
            then have "x \<in> set xs" 
              using \<open>x \<noteq> a\<close> Cons.prems(2)
              by fastforce
            moreover have "map_of (map (\<lambda>x. (x, f x)) (Cons a xs)) x = ?m x"
              using \<open>x \<noteq> a\<close>
              by fastforce
            ultimately show ?thesis 
              using Cons.IH[OF False]
              by presburger
          qed 
      qed force
    qed blast

lemma foldl_map_append_is_some_if:
  assumes "b x = Some y \<or> (\<exists>m \<in> set ms. m x = Some y)" 
    and "\<forall>m' \<in> set ms. m' x = Some y \<or> m' x = None"
  shows "foldl (++) b ms x = Some y" 
using assms
proof (induction ms arbitrary: b)
  \<comment> \<open> NOTE Induction base case violates first assumption (we have at least one element in ms 
    and hence \<open>ms \<noteq> []\<close>). \<close>
  case (Cons a ms)
  consider (b_is_some_y) "b x = Some y" 
    | (m_is_some_y) "\<exists>m \<in> set (a # ms). m x = Some y" 
    using Cons.prems(1)
    by blast
  hence "(b ++ a) x = Some y \<or> (\<exists>m\<in>set ms. m x = Some y)"
    proof (cases)
      case b_is_some_y
      moreover have "a x = Some y \<or> a x = None" 
        using Cons.prems(2)
        by simp
      ultimately show ?thesis 
        using map_add_Some_iff[of b a x y]
        by blast
    next
      case m_is_some_y
      then show ?thesis 
        proof (cases "a x = Some y")
          case False 
          then obtain m where "m \<in> set ms" and "m x = Some y" 
            using m_is_some_y try0
            by auto
          thus ?thesis
            by blast
        qed simp
    qed
  moreover have "\<forall>m' \<in> set ms. m' x = Some y \<or> m' x = None"  
    using Cons.prems(2)
    by fastforce
  ultimately show ?case using Cons.IH[where b="b ++ a"]
    by simp
qed auto

(* TODO "\<forall>(v, a) \<in> set l. \<forall>(v', a') \<in> set l. v \<noteq> v' \<or> a = a'" \<leadsto>
  "\<forall>(v', a') \<in> set l. v \<noteq> v' \<or> a = a'" (this is too strong; we only consider (v, a), i.e. fixed v)
*)
(* TODO isn't this the same as map_of_is_SomeI? *)
lemma map_of_constant_assignments_defined_if:
  assumes "\<forall>(v, a) \<in> set l. \<forall>(v', a') \<in> set l. v \<noteq> v' \<or> a = a'"
    and "(v, a) \<in> set l" 
  shows "map_of l v = Some a" 
  using assms
proof (induction l)
  case (Cons x l)
  thm Cons
  then show ?case 
    proof (cases "x = (v, a)")
      case False
      have v_a_in_l: "(v, a) \<in> set l" 
        using Cons.prems(2) False
        by fastforce
      {
        have "\<forall>(v, a) \<in> set l. \<forall>(v', a') \<in> set l. v \<noteq> v' \<or> a = a'"
          using Cons.prems(1)
          by auto 
        hence "map_of l v = Some a"
          using Cons.IH v_a_in_l
          by linarith
      } note ih = this
      {
        have "x \<in> set (x # l)" 
          by auto
        hence "fst x \<noteq> v \<or> snd x = a" 
          using Cons.prems(1) v_a_in_l
          by fastforce
      } note nb = this
      \<comment> \<open> NOTE If @{text "fst x = v"} then @{text "snd x = a"} by fact @{text "nb"}; moreover if 
        on the other hand @{text "fst x \<noteq> v"}, then the proposition follows from the induction 
        hypothesis since @{text "map_of (x # l) v = map_of l v"} in that case. \<close>
      thus ?thesis
        using ih nb
        by (cases "fst x = v") fastforce+
    qed simp
qed fastforce

end