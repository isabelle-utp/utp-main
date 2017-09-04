theory isabelle_tutorial
  imports Main Real
begin

(* Please turn off "Auto Quickcheck" and "Auto Solve Direct" in Plugins/Plugin Options/Isabelle/General/Automatically tried tools" *)

  declare [[show_sorts]]

  lemma True
    oops

  lemma False
    oops

  lemma "P \<Longrightarrow> P"
    oops

  lemma "P \<Longrightarrow> Q"
    oops

  lemma "P \<longrightarrow> P"
    oops

  lemma "P \<and> Q \<longrightarrow> P"
    oops

  lemma "P \<or> Q \<longrightarrow> P"
    oops

  lemma "P \<longrightarrow> \<not> \<not> P"
    oops

  lemma "P \<or> \<not> P"
    oops

  lemma "(P \<and> Q) \<longleftrightarrow> (Q \<and> P)"
    oops

  lemma "\<forall> x. x = x"
    oops

  lemma "\<exists> x. x = y"
    oops

  lemma "\<forall> x. x \<ge> 0" (* Correct this goal so it can be discharged *)
    oops

  (* Specify and prove the following 4 proof goals *)

  lemma "insert_here" (* "There is a boolean that is true" *)
    oops

  lemma "insert_here" (* "There exists an integer greater than 0" *)
    oops

  lemma "insert_here" (* "The does not exist a natural number less than zero *)
    oops

  lemma "insert_here" (* "Between any two real numbers there is another, distinct real number" *)
    oops

  lemma "1 + 1 = 2" (* Correct this goal so it can be discharged *)
    oops

  lemma "[1] @ [2] @ [3] = [1,2,3]"
    oops

  lemma "(xs @ ys) @ zs = xs @ (ys @ zs)"
    oops

  lemma "[1] @ [2] @ [3] = [1,2,3]" (* Prove manually using subst and append.simps *)
    oops

  lemma "\<forall> x. P x"
    oops

  lemma "x \<in> {x, y}"
    oops

  lemma "x \<in> {}" (* Correct this goal *)
    oops

  lemma "x \<notin> {y, z}" (* Can this be discharged? Why / why not? Correct if necessary. *)
    oops

  lemma "x \<in> UNIV"
    oops

  lemma "\<exists> x. x \<in> {m ..< n}" (* Can this be discharged? Why / why not? Correct if necessary. *)
    oops

  (* What's the difference between the following two goals? *)

  lemma "\<forall> y :: int. \<exists> x :: int. x > y"
    oops

  lemma "\<exists> x :: int. \<forall> y :: int. x > y"
    oops

  (* Complete this proof *)
  lemma isar1: "\<forall> x::int \<in> {m ..< n}. m \<le> x \<and> x < n"
  proof
    fix x :: int
    assume assm: "x \<in> {m ..< n}"
    from assm have f1: "m \<le> x"
      sorry
    from assm have f2: "insert_here"
      by auto
    from f1 f2 show "m \<le> x \<and> x < n"
      by auto
  qed

  (* Complete this proof *)
  lemma isar2:
    fixes x y :: real
    assumes "y > x"
    shows "\<exists> m. x < m \<and> m < y"
  proof -
    let ?m = "0"

    have f1: "x < ?m"
      sorry
    have f2: "?m < y"
      sorry

    from f1 f2 show ?thesis
      by auto
  qed

  theorem cantor: "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  proof
    let ?S = "{x. x \<notin> f x}"
    show "?S \<notin> range f"
    proof
      assume "?S \<in> range f"
      then obtain y where "?S = f y" ..
      then show False
      proof (rule equalityCE)
        assume "y \<in> f y"
        assume "y \<in> ?S"
        then have "y \<notin> f y" ..
        with \<open>y \<in> f y\<close> show ?thesis by contradiction
      next
        assume "y \<notin> ?S"
        assume "y \<notin> f y"
        then have "y \<in> ?S" ..
        with \<open>y \<notin> ?S\<close> show ?thesis by contradiction
      qed
    qed
  qed
end