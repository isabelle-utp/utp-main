theory utp_tutorial
  imports "../utp/utp_designs"
begin

(* Set up the lenses for our two state variables, x and y *)

record my_state =
  st_x :: int
  st_y :: int

definition "x = VAR st_x"
definition "y = VAR st_y"

lemma uvar_x [simp]: "vwb_lens x"
  by (unfold_locales, auto simp add: x_def)

lemma uvar_y [simp]: "vwb_lens y"
  by (unfold_locales, auto simp add: y_def)

lemma my_state_indeps [simp]: "x \<bowtie> y" "y \<bowtie> x"
  by (simp_all add: lens_indep_def x_def y_def)

(* Beginning of exercises *)

lemma "(true \<and> false) = false"
  oops

lemma "true = false"
  oops

lemma "x \<sharp> true"
  oops

lemma "x \<sharp> &y"
  oops

lemma "(&x =\<^sub>u 1 \<and> &y =\<^sub>u &x) = (&x =\<^sub>u 1 \<and> &y =\<^sub>u 1)"
  oops

lemma "(&x =\<^sub>u 1 \<and> &y =\<^sub>u &x)\<lbrakk>2/x\<rbrakk> = false"
  oops

lemma "(\<forall> x \<bullet> &x =\<^sub>u &x) = true"
  oops

lemma "(\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> =\<^sub>u \<guillemotleft>x\<guillemotright>) = true"
  oops

lemma "(1 :\<^sub>u nat) + 1 = 2"
  oops

lemma "(x := 1 ;; x := &x + 1) = (x := 2)"
  oops

lemma "(x := 1 ;; x := &x + 1) = (x := 2)"
  oops (* Redo above as Isar proof *)

lemma "true \<sqsubseteq> x, y := &x + 1, &y"
  oops

lemma "($x\<acute> >\<^sub>u $x \<and> $y\<acute> =\<^sub>u $y) \<sqsubseteq> x, y := &x + 1, &y"
  oops (* Jim's refinement example *)

lemma "($x\<acute> >\<^sub>u $x \<and> $y\<acute> <\<^sub>u $y) \<sqsubseteq> x, y := &x + 1, &y"
  oops

lemma "false \<sqsubseteq> x, y := &x + 1, &y"
  oops

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y := 1,7)"
  oops

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y := 1,7)"
  oops (* Redo above as Isar proof *)

lemma "(x :=\<^sub>D 1 ;; x :=\<^sub>D &x + 1) = (x :=\<^sub>D 2)"
  oops (* Rule required: assigns_d_comp *)

lemma violate_precond:
  "(true \<turnstile>\<^sub>n x := 1 ;; (&x >\<^sub>u 1) \<turnstile>\<^sub>n y := 2) = \<bottom>\<^sub>D"
  oops (* Prove using Isar *)

end

