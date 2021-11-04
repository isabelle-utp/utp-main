(*
  Author: Fred Kurz
*)
theory List_Supplement
imports Main
begin

lemma list_foot: 
  assumes "l \<noteq> []" 
  obtains y ys where "l = ys @ [y]"
proof -
  {
    assume a: "l \<noteq> []"
    have "\<exists>y ys. l = ys @ [y]" 
      using a 
      proof (induction l)
        case (Cons a l)
        then show ?case 
          proof (cases "l = []")
            case True
            have "[] @ [a] = a # l" 
              using True
              by simp
            thus ?thesis 
              using Cons.prems(1)
              by simp
          next
            case False
            thm Cons
            then obtain y ys where "l = ys @ [y]" 
              using Cons.IH
              by blast
            then have "a # l = a # ys @ [y]" 
              by blast
            thus ?thesis
              by fastforce
          qed
      qed simp
  }
  thus ?thesis 
    using assms that 
    by blast
qed

lemma list_ex_intersection: "list_ex (\<lambda>v. list_ex ((=) v) ys) xs \<longleftrightarrow> set xs \<inter> set ys \<noteq> {}"
proof -
  {
    assume "list_ex (\<lambda>v. list_ex ((=) v) ys) xs"
    then have "\<exists>v \<in> set xs. list_ex ((=) v) ys" 
      using list_ex_iff
      by fast
    moreover have "\<forall>v. list_ex ((=) v) ys = (\<exists>v' \<in> set ys. v = v')" 
      using list_ex_iff
      by blast
    ultimately have "\<exists>v \<in> set xs. (\<exists>v' \<in> set ys. v = v')"
      by blast
    then obtain v v' where "v \<in> set xs" and "v' \<in> set ys" and "v = v'"
      by blast
    then have "set xs \<inter> set ys \<noteq> {}"
      by blast
  } moreover {
    assume  "set xs \<inter> set ys \<noteq> {}"
    then obtain v v' where "v \<in> set xs" and "v' \<in> set ys" and "v = v'"
      by blast
    then have "list_ex (\<lambda>v. \<exists>v' \<in> set ys. v = v') xs" 
      using list_ex_iff 
      by fast
    moreover have "\<forall>v. (\<exists>v' \<in> set ys. v = v') = list_ex ((=) v) ys" 
      using list_ex_iff
      by blast
    ultimately have "list_ex (\<lambda>v. list_ex ((=) v) ys) xs" 
      by force
  } ultimately show ?thesis
    by blast
qed

lemma length_map_upt: "length (map f [a..<b]) = b - a" 
proof -
  have "length [a..<b] = b - a" 
    using length_upt
    by blast
  moreover have "length (map f [a..<b]) = length [a..<b]"
    by simp
  ultimately show ?thesis
    by argo
qed

lemma not_list_ex_equals_list_all_not: "(\<not>list_ex P xs) = list_all (\<lambda>x. \<not>P x) xs" 
proof -
  have "(\<not>list_ex P xs) = (\<not>Bex (set xs) P)"
    using list_ex_iff 
    by blast
  also have "\<dots> = Ball (set xs) (\<lambda>x. \<not>P x)"
    by blast 
  finally show ?thesis
    by (simp add: Ball_set_list_all)
qed

lemma element_of_subseqs_then_subset:
  assumes "l \<in> set (subseqs l')" 
  shows"set l \<subseteq> set l'" 
  using assms
proof (induction l' arbitrary: l)
  case (Cons x l')
  have "set (subseqs (x # l')) = (Cons x) ` set (subseqs l') \<union> set (subseqs l')"
    unfolding subseqs.simps(2) Let_def set_map set_append..
  then consider (A) "l \<in> (Cons x) ` set (subseqs l')"
    | (B) "l \<in> set (subseqs l')" 
    using Cons.prems
    by blast
  thus ?case 
    proof (cases)
      case A
      then obtain l'' where "l'' \<in> set (subseqs l')" and "l = x # l''" 
        by blast
      moreover have "set l'' \<subseteq> set l'" 
        using Cons.IH[of l'', OF calculation(1)].
      ultimately show ?thesis 
        by auto
    next
      case B
      then show ?thesis 
        using Cons.IH
        by auto
    qed
qed simp

(* TODO rewrite using list comprehension \<open>embed xs = [[x]. x \<leftarrow> xs]\<close> *)
text \<open> Embed a list into a list of singleton lists. \<close>
primrec embed :: "'a list \<Rightarrow> 'a list list" 
  where "embed [] = []" 
  | "embed (x # xs) = [x] # embed xs"

lemma set_of_embed_is: "set (embed xs) = { [x] | x. x \<in> set xs }" 
  by (induction xs; force+)

lemma concat_is_inverse_of_embed:
  "concat (embed xs) = xs"
  by (induction xs; simp)

lemma embed_append[simp]: "embed (xs @ ys) = embed xs @ embed ys"
proof (induction xs)
  case (Cons x xs)
  have "embed (x # xs @ ys) = [x] # embed (xs @ ys)" 
    try0
    by simp
  also have "\<dots> = [x] # (embed xs @ embed ys)" 
    using Cons.IH 
    by simp
  finally show ?case 
    by fastforce
qed simp

end
