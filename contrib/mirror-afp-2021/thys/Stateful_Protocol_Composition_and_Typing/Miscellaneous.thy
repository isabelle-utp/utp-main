(*
(C) Copyright Andreas Viktor Hess, DTU, 2015-2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      Miscellaneous.thy
    Author:     Andreas Viktor Hess, DTU
*)

section \<open>Miscellaneous Lemmata\<close>
theory Miscellaneous
imports Main "HOL-Library.Sublist" "HOL-Library.While_Combinator"
begin

subsection \<open>List: zip, filter, map\<close>
lemma zip_arg_subterm_split:
  assumes "(x,y) \<in> set (zip xs ys)"
  obtains xs' xs'' ys' ys'' where "xs = xs'@x#xs''" "ys = ys'@y#ys''" "length xs' = length ys'"
proof -
  from assms have "\<exists>zs zs' vs vs'. xs = zs@x#zs' \<and> ys = vs@y#vs' \<and> length zs = length vs"
  proof (induction ys arbitrary: xs)
    case (Cons y' ys' xs)
    then obtain x' xs' where x': "xs = x'#xs'"
      by (metis empty_iff list.exhaust list.set(1) set_zip_leftD)
    show ?case
      by (cases "(x, y) \<in> set (zip xs' ys')",
          metis \<open>xs = x'#xs'\<close> Cons.IH[of xs'] Cons_eq_appendI list.size(4),
          use Cons.prems x' in fastforce)
  qed simp
  thus ?thesis using that by blast
qed

lemma zip_arg_index:
  assumes "(x,y) \<in> set (zip xs ys)"
  obtains i where "xs ! i = x" "ys ! i = y" "i < length xs" "i < length ys"
proof -
  obtain xs1 xs2 ys1 ys2 where "xs = xs1@x#xs2" "ys = ys1@y#ys2" "length xs1 = length ys1"
    using zip_arg_subterm_split[OF assms] by moura
  thus ?thesis using nth_append_length[of xs1 x xs2] nth_append_length[of ys1 y ys2] that by simp
qed

lemma filter_nth: "i < length (filter P xs) \<Longrightarrow> P (filter P xs ! i)"
using nth_mem by force

lemma list_all_filter_eq: "list_all P xs \<Longrightarrow> filter P xs = xs"
by (metis list_all_iff filter_True)

lemma list_all_filter_nil:
  assumes "list_all P xs"
    and "\<And>x. P x \<Longrightarrow> \<not>Q x"
  shows "filter Q xs = []"
using assms by (induct xs) simp_all

lemma list_all_concat: "list_all (list_all f) P \<longleftrightarrow> list_all f (concat P)"
by (induct P) auto

lemma map_upt_index_eq:
  assumes "j < length xs"
  shows "(map (\<lambda>i. xs ! is i) [0..<length xs]) ! j = xs ! is j"
using assms by (simp add: map_nth)

lemma map_snd_list_insert_distrib:
  assumes "\<forall>(i,p) \<in> insert x (set xs). \<forall>(i',p') \<in> insert x (set xs). p = p' \<longrightarrow> i = i'"
  shows "map snd (List.insert x xs) = List.insert (snd x) (map snd xs)"
using assms
proof (induction xs rule: List.rev_induct)
  case (snoc y xs)
  hence IH: "map snd (List.insert x xs) = List.insert (snd x) (map snd xs)" by fastforce

  obtain iy py where y: "y = (iy,py)" by (metis surj_pair)
  obtain ix px where x: "x = (ix,px)" by (metis surj_pair)

  have "(ix,px) \<in> insert x (set (y#xs))" "(iy,py) \<in> insert x (set (y#xs))" using y x by auto
  hence *: "iy = ix" when "py = px" using that snoc.prems by auto

  show ?case
  proof (cases "px = py")
    case True
    hence "y = x" using * y x by auto
    thus ?thesis using IH by simp
  next
    case False
    hence "y \<noteq> x" using y x by simp
    have "List.insert x (xs@[y]) = (List.insert x xs)@[y]"
    proof -
      have 1: "insert y (set xs) = set (xs@[y])" by simp
      have 2: "x \<notin> insert y (set xs) \<or> x \<in> set xs" using \<open>y \<noteq> x\<close> by blast
      show ?thesis using 1 2 by (metis (no_types) List.insert_def append_Cons insertCI)
    qed
    thus ?thesis using IH y x False by (auto simp add: List.insert_def)
  qed
qed simp

lemma map_append_inv: "map f xs = ys@zs \<Longrightarrow> \<exists>vs ws. xs = vs@ws \<and> map f vs = ys \<and> map f ws = zs"
proof (induction xs arbitrary: ys zs)
  case (Cons x xs')
  note prems = Cons.prems
  note IH = Cons.IH

  show ?case
  proof (cases ys)
    case (Cons y ys') 
    then obtain vs' ws where *: "xs' = vs'@ws" "map f vs' = ys'" "map f ws = zs"
      using prems IH[of ys' zs] by auto
    hence "x#xs' = (x#vs')@ws" "map f (x#vs') = y#ys'" using Cons prems by force+
    thus ?thesis by (metis Cons *(3))
  qed (use prems in simp)
qed simp


subsection \<open>List: subsequences\<close>
lemma subseqs_set_subset:
  assumes "ys \<in> set (subseqs xs)"
  shows "set ys \<subseteq> set xs"
using assms subseqs_powset[of xs] by auto

lemma subset_sublist_exists:
  "ys \<subseteq> set xs \<Longrightarrow> \<exists>zs. set zs = ys \<and> zs \<in> set (subseqs xs)"
proof (induction xs arbitrary: ys)
  case Cons thus ?case by (metis (no_types, lifting) Pow_iff imageE subseqs_powset) 
qed simp

lemma map_subseqs: "map (map f) (subseqs xs) = subseqs (map f xs)"
proof (induct xs)
  case (Cons x xs)
  have "map (Cons (f x)) (map (map f) (subseqs xs)) = map (map f) (map (Cons x) (subseqs xs))"
    by (induct "subseqs xs") auto
  thus ?case by (simp add: Let_def Cons)
qed simp

lemma subseqs_Cons:
  assumes "ys \<in> set (subseqs xs)"
  shows "ys \<in> set (subseqs (x#xs))"
by (metis assms Un_iff set_append subseqs.simps(2))

lemma subseqs_subset:
  assumes "ys \<in> set (subseqs xs)"
  shows "set ys \<subseteq> set xs"
using assms by (metis Pow_iff image_eqI subseqs_powset)


subsection \<open>List: prefixes, suffixes\<close>
lemma suffix_Cons': "suffix [x] (y#ys) \<Longrightarrow> suffix [x] ys \<or> (y = x \<and> ys = [])"
using suffix_Cons[of "[x]"] by auto

lemma prefix_Cons': "prefix (x#xs) (x#ys) \<Longrightarrow> prefix xs ys"
by simp

lemma prefix_map: "prefix xs (map f ys) \<Longrightarrow> \<exists>zs. prefix zs ys \<and> map f zs = xs"
using map_append_inv unfolding prefix_def by fast

lemma length_prefix_ex:
  assumes "n \<le> length xs"
  shows "\<exists>ys zs. xs = ys@zs \<and> length ys = n"
  using assms
proof (induction n)
  case (Suc n)
  then obtain ys zs where IH: "xs = ys@zs" "length ys = n" by moura
  hence "length zs > 0" using Suc.prems(1) by auto
  then obtain v vs where v: "zs = v#vs" by (metis Suc_length_conv gr0_conv_Suc)
  hence "length (ys@[v]) = Suc n" using IH(2) by simp
  thus ?case using IH(1) v by (metis append.assoc append_Cons append_Nil)
qed simp

lemma length_prefix_ex':
  assumes "n < length xs"
  shows "\<exists>ys zs. xs = ys@xs ! n#zs \<and> length ys = n"
proof -
  obtain ys zs where xs: "xs = ys@zs" "length ys = n" using assms length_prefix_ex[of n xs] by moura
  hence "length zs > 0" using assms by auto
  then obtain v vs where v: "zs = v#vs" by (metis Suc_length_conv gr0_conv_Suc)
  hence "(ys@zs) ! n = v" using xs by auto
  thus ?thesis using v xs by auto
qed

lemma length_prefix_ex2:
  assumes "i < length xs" "j < length xs" "i < j"
  shows "\<exists>ys zs vs. xs = ys@xs ! i#zs@xs ! j#vs \<and> length ys = i \<and> length zs = j - i - 1"
by (smt assms length_prefix_ex' nth_append append.assoc append.simps(2) add_diff_cancel_left'
        diff_Suc_1 length_Cons length_append)


subsection \<open>List: products\<close>
lemma product_lists_Cons:
  "x#xs \<in> set (product_lists (y#ys)) \<longleftrightarrow> (xs \<in> set (product_lists ys) \<and> x \<in> set y)"
by auto

lemma product_lists_in_set_nth:
  assumes "xs \<in> set (product_lists ys)"
  shows "\<forall>i<length ys. xs ! i \<in> set (ys ! i)"
proof -
  have 0: "length ys = length xs" using assms(1) by (simp add: in_set_product_lists_length)
  thus ?thesis using assms
  proof (induction ys arbitrary: xs)
    case (Cons y ys)
    obtain x xs' where xs: "xs = x#xs'" using Cons.prems(1) by (metis length_Suc_conv)
    hence "xs' \<in> set (product_lists ys) \<Longrightarrow> \<forall>i<length ys. xs' ! i \<in> set (ys ! i)"
          "length ys = length xs'" "x#xs' \<in> set (product_lists (y#ys))"
      using Cons by simp_all
    thus ?case using xs product_lists_Cons[of x xs' y ys] by (simp add: nth_Cons')
  qed simp
qed

lemma product_lists_in_set_nth':
  assumes "\<forall>i<length xs. ys ! i \<in> set (xs ! i)"
    and "length xs = length ys"
  shows "ys \<in> set (product_lists xs)"
using assms
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  obtain y ys' where ys: "ys = y#ys'" using Cons.prems(2) by (metis length_Suc_conv)
  hence "ys' \<in> set (product_lists xs)" "y \<in> set x" "length xs = length ys'"
    using Cons by fastforce+
  thus ?case using ys product_lists_Cons[of y ys' x xs] by (simp add: nth_Cons')
qed simp


subsection \<open>Other Lemmata\<close>
lemma inv_set_fset: "finite M \<Longrightarrow> set (inv set M) = M"
unfolding inv_def by (metis (mono_tags) finite_list someI_ex)

lemma lfp_eqI':
  assumes "mono f"
    and "f C = C"
    and "\<forall>X \<in> Pow C. f X = X \<longrightarrow> X = C"
  shows "lfp f = C"
by (metis PowI assms lfp_lowerbound lfp_unfold subset_refl)

lemma lfp_while':
  fixes f::"'a set \<Rightarrow> 'a set" and M::"'a set"
  defines "N \<equiv> while (\<lambda>A. f A \<noteq> A) f {}"
  assumes f_mono: "mono f"
    and N_finite: "finite N"
    and N_supset: "f N \<subseteq> N"
  shows "lfp f = N"
proof -
  have *: "f X \<subseteq> N" when "X \<subseteq> N" for X using N_supset monoD[OF f_mono that] by blast
  show ?thesis
    using lfp_while[OF f_mono * N_finite]
    by (simp add: N_def)
qed

lemma lfp_while'':
  fixes f::"'a set \<Rightarrow> 'a set" and M::"'a set"
  defines "N \<equiv> while (\<lambda>A. f A \<noteq> A) f {}"
  assumes f_mono: "mono f"
    and lfp_finite: "finite (lfp f)"
  shows "lfp f = N"
proof -
  have *: "f X \<subseteq> lfp f" when "X \<subseteq> lfp f" for X
    using lfp_fixpoint[OF f_mono] monoD[OF f_mono that]
    by blast
  show ?thesis
    using lfp_while[OF f_mono * lfp_finite]
    by (simp add: N_def)
qed

lemma preordered_finite_set_has_maxima:
  assumes "finite A" "A \<noteq> {}"
  shows "\<exists>a::'a::{preorder} \<in> A. \<forall>b \<in> A. \<not>(a < b)"
using assms 
proof (induction A rule: finite_induct)
  case (insert a A) thus ?case
    by (cases "A = {}", simp, metis insert_iff order_trans less_le_not_le)
qed simp

lemma partition_index_bij:
  fixes n::nat
  obtains I k where
    "bij_betw I {0..<n} {0..<n}" "k \<le> n"
    "\<forall>i. i < k \<longrightarrow> P (I i)"
    "\<forall>i. k \<le> i \<and> i < n \<longrightarrow> \<not>(P (I i))"
proof -
  define A where "A = filter P [0..<n]"
  define B where "B = filter (\<lambda>i. \<not>P i) [0..<n]"
  define k where "k = length A"
  define I where "I = (\<lambda>n. (A@B) ! n)"

  note defs = A_def B_def k_def I_def
  
  have k1: "k \<le> n" by (metis defs(1,3) diff_le_self dual_order.trans length_filter_le length_upt)

  have "i < k \<Longrightarrow> P (A ! i)" for i by (metis defs(1,3) filter_nth)
  hence k2: "i < k \<Longrightarrow> P ((A@B) ! i)" for i by (simp add: defs nth_append) 

  have "i < length B \<Longrightarrow> \<not>(P (B ! i))" for i by (metis defs(2) filter_nth)
  hence "i < length B \<Longrightarrow> \<not>(P ((A@B) ! (k + i)))" for i using k_def by simp 
  hence "k \<le> i \<and> i < k + length B \<Longrightarrow> \<not>(P ((A@B) ! i))" for i
    by (metis add.commute add_less_imp_less_right le_add_diff_inverse2)
  hence k3: "k \<le> i \<and> i < n \<Longrightarrow> \<not>(P ((A@B) ! i))" for i by (simp add: defs sum_length_filter_compl)

  have *: "length (A@B) = n" "set (A@B) = {0..<n}" "distinct (A@B)"
    by (metis defs(1,2) diff_zero length_append length_upt sum_length_filter_compl)
       (auto simp add: defs)

  have I: "bij_betw I {0..<n} {0..<n}"
  proof (intro bij_betwI')
    fix x y show "x \<in> {0..<n} \<Longrightarrow> y \<in> {0..<n} \<Longrightarrow> (I x = I y) = (x = y)"
      by (metis *(1,3) defs(4) nth_eq_iff_index_eq atLeastLessThan_iff)
  next
    fix x show "x \<in> {0..<n} \<Longrightarrow> I x \<in> {0..<n}"
      by (metis *(1,2) defs(4) atLeastLessThan_iff nth_mem)
  next
    fix y show "y \<in> {0..<n} \<Longrightarrow> \<exists>x \<in> {0..<n}. y = I x"
      by (metis * defs(4) atLeast0LessThan distinct_Ex1 lessThan_iff)
  qed

  show ?thesis using k1 k2 k3 I that by (simp add: defs)
qed

lemma finite_lists_length_eq':
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> finite {y. P x y}"
  shows "finite {ys. length xs = length ys \<and> (\<forall>y \<in> set ys. \<exists>x \<in> set xs. P x y)}"
proof -
  define Q where "Q \<equiv> \<lambda>ys. \<forall>y \<in> set ys. \<exists>x \<in> set xs. P x y"
  define M where "M \<equiv> {y. \<exists>x \<in> set xs. P x y}"

  have 0: "finite M" using assms unfolding M_def by fastforce

  have "Q ys \<longleftrightarrow> set ys \<subseteq> M"
       "(Q ys \<and> length ys = length xs) \<longleftrightarrow> (length xs = length ys \<and> Q ys)"
    for ys
    unfolding Q_def M_def by auto
  thus ?thesis
    using finite_lists_length_eq[OF 0, of "length xs"]
    unfolding Q_def by presburger
qed

lemma trancl_eqI:
  assumes "\<forall>(a,b) \<in> A. \<forall>(c,d) \<in> A. b = c \<longrightarrow> (a,d) \<in> A"
  shows "A = A\<^sup>+"
proof
  show "A\<^sup>+ \<subseteq> A"
  proof
    fix x assume x: "x \<in> A\<^sup>+"
    then obtain a b where ab: "x = (a,b)" by (metis surj_pair)
    hence "(a,b) \<in> A\<^sup>+" using x by metis
    hence "(a,b) \<in> A" using assms by (induct rule: trancl_induct) auto
    thus "x \<in> A" using ab by metis
  qed
qed auto

lemma trancl_eqI':
  assumes "\<forall>(a,b) \<in> A. \<forall>(c,d) \<in> A. b = c \<and> a \<noteq> d \<longrightarrow> (a,d) \<in> A"
    and "\<forall>(a,b) \<in> A. a \<noteq> b"
  shows "A = {(a,b) \<in> A\<^sup>+. a \<noteq> b}"
proof
  show "{(a,b) \<in> A\<^sup>+. a \<noteq> b} \<subseteq> A"
  proof
    fix x assume x: "x \<in> {(a,b) \<in> A\<^sup>+. a \<noteq> b}"
    then obtain a b where ab: "x = (a,b)" by (metis surj_pair)
    hence "(a,b) \<in> A\<^sup>+" "a \<noteq> b" using x by blast+
    hence "(a,b) \<in> A"
    proof (induction rule: trancl_induct)
      case base thus ?case by blast
    next
      case step thus ?case using assms(1) by force
    qed
    thus "x \<in> A" using ab by metis
  qed
qed (use assms(2) in auto)

lemma distinct_concat_idx_disjoint:
  assumes xs: "distinct (concat xs)"
    and ij: "i < length xs" "j < length xs" "i < j"
  shows "set (xs ! i) \<inter> set (xs ! j) = {}"
proof -
  obtain ys zs vs where ys: "xs = ys@xs ! i#zs@xs ! j#vs" "length ys = i" "length zs = j - i - 1"
    using length_prefix_ex2[OF ij] by moura
  thus ?thesis
    using xs concat_append[of "ys@xs ! i#zs" "xs ! j#vs"]
          distinct_append[of "concat (ys@xs ! i#zs)" "concat (xs ! j#vs)"]
    by auto
qed

lemma remdups_ex2:
  "length (remdups xs) > 1 \<Longrightarrow> \<exists>a \<in> set xs. \<exists>b \<in> set xs. a \<noteq> b"
by (metis distinct_Ex1 distinct_remdups less_trans nth_mem set_remdups zero_less_one zero_neq_one)

lemma trancl_minus_refl_idem:
  defines "cl \<equiv> \<lambda>ts. {(a,b) \<in> ts\<^sup>+. a \<noteq> b}"
  shows "cl (cl ts) = cl ts"
proof -
  have 0: "(ts\<^sup>+)\<^sup>+ = ts\<^sup>+" "cl ts \<subseteq> ts\<^sup>+" "(cl ts)\<^sup>+ \<subseteq> (ts\<^sup>+)\<^sup>+"
  proof -
    show "(ts\<^sup>+)\<^sup>+ = ts\<^sup>+" "cl ts \<subseteq> ts\<^sup>+" unfolding cl_def by auto
    thus "(cl ts)\<^sup>+ \<subseteq> (ts\<^sup>+)\<^sup>+" using trancl_mono[of _ "cl ts" "ts\<^sup>+"] by blast
  qed

  have 1: "t \<in> cl (cl ts)" when t: "t \<in> cl ts" for t
    using t 0 unfolding cl_def by fast

  have 2: "t \<in> cl ts" when t: "t \<in> cl (cl ts)" for t
  proof -
    obtain a b where ab: "t = (a,b)" by (metis surj_pair)
    have "t \<in> (cl ts)\<^sup>+" and a_neq_b: "a \<noteq> b" using t unfolding cl_def ab by force+
    hence "t \<in> ts\<^sup>+" using 0 by blast
    thus ?thesis using a_neq_b unfolding cl_def ab by blast
  qed

  show ?thesis using 1 2 by blast
qed


subsection \<open>Infinite Paths in Relations as Mappings from Naturals to States\<close>
context
begin

private fun rel_chain_fun::"nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a" where
  "rel_chain_fun 0 x _ _ = x"
| "rel_chain_fun (Suc i) x y r = (if i = 0 then y else SOME z. (rel_chain_fun i x y r, z) \<in> r)"

lemma infinite_chain_intro:
  fixes r::"('a \<times> 'a) set"
  assumes "\<forall>(a,b) \<in> r. \<exists>c. (b,c) \<in> r" "r \<noteq> {}"
  shows "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> r"
proof -
  from assms(2) obtain a b where "(a,b) \<in> r" by auto

  let ?P = "\<lambda>i. (rel_chain_fun i a b r, rel_chain_fun (Suc i) a b r) \<in> r"
  let ?Q = "\<lambda>i. \<exists>z. (rel_chain_fun i a b r, z) \<in> r"

  have base: "?P 0" using \<open>(a,b) \<in> r\<close> by auto

  have step: "?P (Suc i)" when i: "?P i" for i
  proof -
    have "?Q (Suc i)" using assms(1) i by auto
    thus ?thesis using someI_ex[OF \<open>?Q (Suc i)\<close>] by auto
  qed

  have "\<forall>i::nat. (rel_chain_fun i a b r, rel_chain_fun (Suc i) a b r) \<in> r"
    using base step nat_induct[of ?P] by simp
  thus ?thesis by fastforce
qed

end

lemma infinite_chain_intro':
  fixes r::"('a \<times> 'a) set"
  assumes base: "\<exists>b. (x,b) \<in> r" and step: "\<forall>b. (x,b) \<in> r\<^sup>+ \<longrightarrow> (\<exists>c. (b,c) \<in> r)" 
  shows "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> r"
proof -
  let ?s = "{(a,b) \<in> r. a = x \<or> (x,a) \<in> r\<^sup>+}"

  have "?s \<noteq> {}" using base by auto

  have "\<exists>c. (b,c) \<in> ?s" when ab: "(a,b) \<in> ?s" for a b
  proof (cases "a = x")
    case False
    hence "(x,a) \<in> r\<^sup>+" using ab by auto
    hence "(x,b) \<in> r\<^sup>+" using \<open>(a,b) \<in> ?s\<close> by auto
    thus ?thesis using step by auto
  qed (use ab step in auto)
  hence "\<exists>f. \<forall>i. (f i, f (Suc i)) \<in> ?s" using infinite_chain_intro[of ?s] \<open>?s \<noteq> {}\<close> by blast
  thus ?thesis by auto
qed

lemma infinite_chain_mono:
  assumes "S \<subseteq> T" "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> S"
  shows "\<exists>f. \<forall>i::nat. (f i, f (Suc i)) \<in> T"
using assms by auto

end
