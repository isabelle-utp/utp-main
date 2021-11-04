section \<open> General Mereology \<close>

(*<*)
theory GM
  imports CM
begin (*>*)

text \<open> The theory of \emph{general mereology} adds the axiom of fusion to ground mereology.\footnote{
See @{cite "simons_parts:_1987"} p. 36, @{cite "varzi_parts_1996"} p. 265 and @{cite "casati_parts_1999"} p. 46.} \<close>

locale GM = M +
  assumes fusion: 
    "\<exists> x. \<phi> x \<Longrightarrow> \<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. \<phi> x \<and> O y x)"
begin

text \<open> Fusion entails sum closure. \<close>

theorem sum_closure: "\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w a \<or> O w b)"
proof -
  have "a = a"..
  hence "a = a \<or> a = b"..
  hence "\<exists> x. x = a \<or> x = b"..
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O y x))"
    by (rule fusion)
  then obtain z where z: 
    "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O y x)"..
  have "\<forall> w. O w z \<longleftrightarrow> (O w a \<or> O w b)"
  proof
    fix w
    from z have w: "O w z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O w x)"..
    show "O w z \<longleftrightarrow> (O w a \<or> O w b)"
    proof
      assume "O w z"
      with w have "\<exists> x. (x = a \<or> x = b) \<and> O w x"..
      then obtain x where x: "(x = a \<or> x = b) \<and> O w x"..
      hence "O w x"..
      from x have "x = a \<or> x = b"..
      thus "O w a \<or> O w b"
      proof (rule disjE)
        assume "x = a"
        hence "O w a" using `O w x` by (rule subst)
        thus "O w a \<or> O w b"..
      next
        assume "x = b"
        hence "O w b" using `O w x` by (rule subst)
        thus "O w a \<or> O w b"..
      qed
    next
      assume "O w a \<or> O w b"
      hence "\<exists> x. (x = a \<or> x = b) \<and> O w x"
      proof (rule disjE)
        assume "O w a"
        with `a = a \<or> a = b` have "(a = a \<or> a = b) \<and> O w a"..
        thus "\<exists> x. (x = a \<or> x = b) \<and> O w x"..
      next
        have "b = b"..
        hence "b = a \<or> b = b"..
        moreover assume "O w b"
        ultimately have "(b = a \<or> b = b) \<and> O w b"..
        thus "\<exists> x. (x = a \<or> x = b) \<and> O w x"..
      qed
      with w show "O w z"..
    qed
  qed
  thus "\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w a \<or> O w b)"..
qed

end

(*<*) end (*>*)
