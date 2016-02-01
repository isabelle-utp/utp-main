subsection {* Weakest precondition calculus *}

theory utp_wp
imports utp_rel
begin

text {* A very quick implementation of wp -- more laws still needed! *}

named_theorems wp

method wp_tac = (simp add: wp)

consts
  uwp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "wp" 60)

definition wp_upred :: "('\<alpha>, '\<beta>) relation \<Rightarrow> '\<beta> condition \<Rightarrow> '\<alpha> condition" where
"wp_upred Q r = \<lfloor>\<not> (Q ;; \<not> \<lceil>r\<rceil>\<^sub><)\<rfloor>\<^sub><"

adhoc_overloading
  uwp wp_upred

declare wp_upred_def [urel_defs]

theorem wp_assigns_r [wp]: 
  "(assigns_r \<sigma>) wp r = \<sigma> \<dagger> r"
  by rel_tac

theorem wp_skip_r [wp]:
  "II wp r = r"
  by rel_tac

theorem wp_true [wp]:
  "r \<noteq> true \<Longrightarrow> true wp r = false"
  by rel_tac

theorem wp_conj [wp]:
  "P wp (q \<and> r) = (P wp q \<and> P wp r)"
  by rel_tac

theorem wp_seq_r [wp]: "(P ;; Q) wp r = P wp (Q wp r)"
  by rel_tac

theorem wp_cond [wp]: "(P \<triangleleft> b \<triangleright> Q) wp r = ((b \<Rightarrow> P wp r) \<and> ((\<not> b) \<Rightarrow> Q wp r))"
  by rel_tac

end