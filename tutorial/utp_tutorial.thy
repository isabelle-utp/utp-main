theory utp_tutorial
  imports "../utp/utp_designs"
begin

(* Set up the lenses for our two state variables, x and y *)

record my_state =
  st_x :: int
  st_y :: int
  st_z :: int

definition "x = VAR st_x"
definition "y = VAR st_y"
definition "z = VAR st_z"

lemma uvar_x [simp]: "vwb_lens x"
  by (unfold_locales, auto simp add: x_def)

lemma uvar_y [simp]: "vwb_lens y"
  by (unfold_locales, auto simp add: y_def)

lemma uvar_z [simp]: "vwb_lens z"
  by (unfold_locales, auto simp add: z_def)

lemma my_state_indeps [simp]: "x \<bowtie> y" "y \<bowtie> x" "x \<bowtie> z" "z \<bowtie> x" "y \<bowtie> z" "z \<bowtie> y"
  by (simp_all add: lens_indep_def x_def y_def z_def)

(* Beginning of exercises *)

lemma "(true \<and> false) = false"
  by simp

lemma "true = false"
  oops

lemma "x \<sharp> true"
  oops (* Use unrest_tac *)

lemma "x \<sharp> &y"
  oops

lemma "(&x =\<^sub>u 1 \<and> &y =\<^sub>u &x) = (&x =\<^sub>u 1 \<and> &y =\<^sub>u 1)"
  oops

lemma "(&x =\<^sub>u 1 \<and> &y =\<^sub>u &x)\<lbrakk>2/x\<rbrakk> = false"
  oops (* Use subst_tac *)

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

lemma "(true ;; x := \<guillemotleft>c\<guillemotright>) = ($x\<acute> =\<^sub>u \<guillemotleft>c\<guillemotright>)"
  oops (* Modified Jim's property *)

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y := 1,7)"
  oops

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y := 1,7)"
  oops (* Redo above as Isar proof *)

lemma wp_ex_1: "(x := &x - 5) wp (&x >\<^sub>u 10) = (&x >\<^sub>u 15)"
  oops (* Use wp_tac, subst_tac, and pred_tac *)

lemma wp_ex_2: "(x := &x - 5 ;; x := &x div 2) wp (&x >\<^sub>u 20) = (&x >\<^sub>u 46)"
  oops

lemma wp_ex_3:
      "(x := \<guillemotleft>X\<guillemotright> ;; 
        y := \<guillemotleft>Y\<guillemotright> ;; 
        x := &x + &y ;; 
        y := &x - &y ;; 
        x := &x - y) wp (&x =\<^sub>u \<guillemotleft>Y\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>X\<guillemotright>) = true" 
  oops

lemma wp_ex_4: 
      "(x := \<guillemotleft>X\<guillemotright> ;; 
        y := \<guillemotleft>Y\<guillemotright> ;; 
        x := &x * &y ;; 
        y := &x div &y ;; 
        x := &x div &y) wp (&x =\<^sub>u \<guillemotleft>Y\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>X\<guillemotright>) = true" 
  oops (* Additional assumptions are needed *)

lemma hoare_ex_1:
  "\<lbrace>true\<rbrace>(z := &x) \<triangleleft> (&x \<ge>\<^sub>u &y) \<triangleright>\<^sub>r (z := &y)\<lbrace>&z =\<^sub>u max\<^sub>u(&x, &y)\<rbrace>\<^sub>u"
  oops

lemma hoare_ex_2:
  assumes "X > 0" "Y > 0"
  shows
  "\<lbrace>&x =\<^sub>u \<guillemotleft>X\<guillemotright> \<and> &y =\<^sub>u \<guillemotleft>Y\<guillemotright>\<rbrace>
    while \<not>(&x =\<^sub>u &y)
    invr &x >\<^sub>u 0 \<and> &y >\<^sub>u 0 \<and> (gcd\<^sub>u(&x,&y) =\<^sub>u gcd\<^sub>u(\<guillemotleft>X\<guillemotright>,\<guillemotleft>Y\<guillemotright>))
    do 
       (x := &x - &y) \<triangleleft> (&x >\<^sub>u &y) \<triangleright>\<^sub>r (y := &y - &x)
    od
    \<lbrace>&x =\<^sub>u gcd\<^sub>u(\<guillemotleft>X\<guillemotright>, \<guillemotleft>Y\<guillemotright>)\<rbrace>\<^sub>u"
  oops

lemma "(x :=\<^sub>D 1 ;; x :=\<^sub>D &x + 1) = (x :=\<^sub>D 2)"
  oops (* Rule required: assigns_d_comp *)

lemma violate_precond:
  "(true \<turnstile>\<^sub>n x := 1 ;; (&x >\<^sub>u 1) \<turnstile>\<^sub>n y := 2) = \<bottom>\<^sub>D"
  oops (* Prove using Isar *)



end

