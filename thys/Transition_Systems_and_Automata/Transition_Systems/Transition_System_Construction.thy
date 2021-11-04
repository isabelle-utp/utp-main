section \<open>Constructing Paths and Runs in Transition Systems\<close>

theory Transition_System_Construction
imports
  "../Basic/Sequence_LTL"
  "Transition_System"
begin

  context transition_system
  begin

    lemma invariant_run:
      assumes "P p" "\<And> p. P p \<Longrightarrow> \<exists> a. enabled a p \<and> P (execute a p) \<and> Q p a"
      obtains r
      where "run r p" "pred_stream P (p ## trace r p)" "stream_all2 Q (p ## trace r p) r"
    proof -
      obtain f where 1: "enabled (f p) p" "P (execute (f p) p)" "Q p (f p)" if "P p" for p using assms(2) by metis
      let ?g = "\<lambda> p. execute (f p) p"
      let ?r = "\<lambda> p. smap f (siterate ?g p)"
      show ?thesis
      proof
        show "run (?r p) p" using assms(1) 1 by (coinduction arbitrary: p) (auto)
        show "pred_stream P (p ## trace (?r p) p)" using assms(1) 1 by (coinduction arbitrary: p) (auto)
        show "stream_all2 Q (p ## trace (?r p) p) (?r p)" using assms(1) 1 by (coinduction arbitrary: p) (auto)
      qed
    qed
    lemma recurring_condition:
      assumes "P p" "\<And> p. P p \<Longrightarrow> \<exists> r. r \<noteq> [] \<and> path r p \<and> P (target r p)"
      obtains r
      where "run r p" "infs P (p ## trace r p)"
    proof -
      obtain f where 1: "f p \<noteq> []" "path (f p) p" "P (target (f p) p)" if "P p" for p using assms(2) by metis
      let ?g = "\<lambda> p. target (f p) p"
      let ?r = "\<lambda> p. flat (smap f (siterate ?g p))"
      have 2: "?r p = f p @- ?r (?g p)" if "P p" for p using that 1(1) by (simp add: flat_unfold)
      show ?thesis
      proof
        show "run (?r p) p" using assms(1) 1 2 by (coinduction arbitrary: p rule: run_coinduct_shift) (blast)
        show "infs P (p ## trace (?r p) p)" using assms(1) 1 2 by (coinduction arbitrary: p rule: infs_sscan_coinduct) (blast)
      qed
    qed

    lemma invariant_run_index:
      assumes "P n p" "\<And> n p. P n p \<Longrightarrow> \<exists> a. enabled a p \<and> P (Suc n) (execute a p) \<and> Q n p a"
      obtains r
      where
        "run r p"
        "\<And> i. P (n + i) (target (stake i r) p)"
        "\<And> i. Q (n + i) (target (stake i r) p) (r !! i)"
    proof -
      define s where "s \<equiv> (n, p)"
      have 1: "case_prod P s" using assms(1) unfolding s_def by auto
      obtain f where 2:
        "\<And> n p. P n p \<Longrightarrow> enabled (f n p) p"
        "\<And> n p. P n p \<Longrightarrow> P (Suc n) (execute (f n p) p)"
        "\<And> n p. P n p \<Longrightarrow> Q n p (f n p)"
        using assms(2) by metis
      define g where "g \<equiv> \<lambda> (n, p). (Suc n, execute (f n p) p)"

      let ?r = "smap (case_prod f) (siterate g s)"

      have 3: "run ?r (snd s)" using 1 2(1, 2) unfolding g_def by (coinduction arbitrary: s) (auto)
      have 4: "case_prod P (compow k g s)" for k using 1 2(2) unfolding g_def by (induct k) (auto)
      have 5: "case_prod Q (compow k g s) (?r !! k)" for k using 2(3) 4 by (simp add: case_prod_beta)

      have 6: "compow k g (n, p) = (n + k, target (stake k ?r) p)" for k
        unfolding s_def g_def by (induct k) (auto simp add: stake_Suc simp del: stake.simps(2))

      show ?thesis using that 3 4 5 unfolding s_def 6 by simp
    qed

    lemma koenig:
      assumes "infinite (reachable p)"
      assumes "\<And> q. q \<in> reachable p \<Longrightarrow> finite (successors q)"
      obtains r
      where "run r p"
    proof (rule invariant_run[where ?P = "\<lambda> q. q \<in> reachable p \<and> infinite (reachable q)"])
      show "p \<in> reachable p \<and> infinite (reachable p)" using assms(1) by auto
    next
      fix q
      assume 1: "q \<in> reachable p \<and> infinite (reachable q)"
      have 2: "finite (successors q)" using assms(2) 1 by auto
      have 3: "infinite (insert q (\<Union>(reachable ` (successors q))))" using reachable_step 1 by metis
      obtain s where 4: "s \<in> successors q" "infinite (reachable s)" using 2 3 by auto
      show "\<exists> a. enabled a q \<and> (execute a q \<in> reachable p \<and> infinite (reachable (execute a q))) \<and> True"
        using 1 4 by auto
    qed

  end

end
