(*  Title:      CoW_Lyndon.Lyndon_Addition
    Author:     Štěpán Holub, Charles University
    Author:     Štěpán Starosta, CTU in Prague
*)

theory Lyndon_Addition
  imports Lyndon Szpilrajn.Szpilrajn

begin

subsection "The minimal relation"

text \<open>We define the minimal relation which guarantees the lexicographic minimality of w compared to its 
nontrivial conjugates.\<close>

inductive_set rotate_rel :: "'a list \<Rightarrow> 'a rel" for w
  where  "0 < n \<Longrightarrow> n < \<^bold>|w\<^bold>| \<Longrightarrow> (mismatch_pair w (rotate n w)) \<in> rotate_rel w"

text\<open>A word is Lyndon iff the corresponding order of letters is compatible with  @{term "rotate_rel w"}.\<close>

lemma (in linorder) rotate_rel_iff: assumes "w \<noteq> \<epsilon>"
  shows  "Lyndon w \<longleftrightarrow> rotate_rel w \<subseteq> {(x,y). x < y}" (is "?L \<longleftrightarrow> ?R")
proof
  assume "Lyndon w" show "rotate_rel w \<subseteq> {(x,y). x < y}"
  proof
    fix  x assume "x \<in> rotate_rel w"
    then obtain n where "x = mismatch_pair w (rotate n w)" and "0 < n" and "n < \<^bold>|w\<^bold>|"
      using rotate_rel.cases by blast
    have "w <lex rotate n w" 
      using LyndonD[OF \<open>Lyndon w\<close> \<open>0 < n\<close> \<open>n < \<^bold>|w\<^bold>|\<close>]. 
    from this[unfolded lexordp_conv_lexord] 
      prim_no_rotate[OF Lyndon_prim[OF \<open>Lyndon w\<close>] \<open>0 < n\<close>  \<open>n < \<^bold>|w\<^bold>|\<close>]
    show "x \<in> {(a, b). a < b}" 
      using lexord_mismatch[of w "rotate n w" "{(a,b). a < b}", folded \<open>x = mismatch_pair w (rotate n w)\<close>]
        \<open>rotate n w \<noteq> w\<close> rotate_comp_eq[of w n] 
      unfolding irrefl_def by blast
  qed
next
  assume "?R" 
  show "?L"
    unfolding Lyndon.simps
  proof(simp add: assms)
    have "w <lex rotate n w" if "0 < n"  "n < \<^bold>|w\<^bold>|" for n 
    proof-
      have "\<not> w \<bowtie> rotate n w" 
        using rotate_comp_eq[of w n] subsetD[OF \<open>?R\<close>, OF rotate_rel.intros[OF \<open>0 < n\<close> \<open>n < \<^bold>|w\<^bold>|\<close>]]
          mismatch_pair_lcp[of w "rotate n w"] by fastforce
      from mismatch_lexord_linorder[OF this subsetD[OF \<open>?R\<close>, OF rotate_rel.intros[OF \<open>0 < n\<close> \<open>n < \<^bold>|w\<^bold>|\<close>]]]
      show "w <lex rotate n w".
    qed 
    thus "\<forall>n. 0 < n \<and> n < \<^bold>|w\<^bold>| \<longrightarrow> w <lex rotate n w"  by blast 
  qed
qed

text\<open>It is well known that an acyclic order can be extended to a total strict linear order. This means that
a word is Lyndon with respect to some order iff its @{term "rotate_rel w"} is acyclic.
\<close>
lemma Lyndon_rotate_rel_iff:
  "acyclic (rotate_rel w) \<longleftrightarrow> (\<exists> r. strict_linear_order r \<and> rotate_rel w \<subseteq> r)" (is "?L \<longleftrightarrow> ?R")
proof
  assume "?R" thus "?L"
    unfolding strict_linear_order_on_def acyclic_def irrefl_def
    using trancl_id trancl_mono by metis
next
  assume "?L" thus "?R"
    using can_extend_acyclic_order_to_strict_linear by auto
qed


lemma slo_linorder: "strict_linear_order r \<Longrightarrow> class.linorder (\<lambda> a b. (a,b) \<in> r\<^sup>=) (\<lambda> a b. (a,b) \<in> r)"
    unfolding strict_linear_order_def strict_partial_order_def irrefl_def trans_def total_on_def
    by unfold_locales blast+

text\<open>Application examples\<close>

lemma assumes "w \<noteq> \<epsilon>" and "acyclic (rotate_rel w)" shows "primitive w"
proof-
  obtain r where "strict_linear_order r" and "rotate_rel w \<subseteq> r"
    using Lyndon_rotate_rel_iff assms by auto

  interpret r: linorder "\<lambda> a b. (a,b) \<in> r\<^sup>=" "\<lambda> a b. (a,b) \<in> r" 
    using slo_linorder[OF \<open>strict_linear_order r\<close>]. 

  have "r.Lyndon w"
    using r.rotate_rel_iff[OF \<open>w \<noteq> \<epsilon>\<close>] \<open>rotate_rel w \<subseteq> r\<close> by blast

  from r.Lyndon_prim[OF this]
  show "primitive w".

qed

lemma assumes "w \<noteq> \<epsilon>" and "acyclic (rotate_rel w)" shows "\<not> bordered w"
proof-
  obtain r where "strict_linear_order r" and "rotate_rel w \<subseteq> r"
    using Lyndon_rotate_rel_iff assms by auto

  interpret r: linorder "\<lambda> a b. (a,b) \<in> r\<^sup>=" "\<lambda> a b. (a,b) \<in> r" 
    using slo_linorder[OF \<open>strict_linear_order r\<close>]. 

  have "r.Lyndon w"
    using r.rotate_rel_iff[OF \<open>w \<noteq> \<epsilon>\<close>] \<open>rotate_rel w \<subseteq> r\<close> by blast

  from r.Lyndon_unbordered[OF this]
  show "\<not> bordered w".
qed

end