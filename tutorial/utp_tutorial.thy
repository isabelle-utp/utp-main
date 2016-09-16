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

lemma "(x := 1 ;; x := &x + 1) = (x := 2)"
  by (rel_tac)

lemma "(x := 1 ;; x := &x + 1) = (x := 2)"
proof -
  have "(x := 1 ;; x := &x + 1) = (x := &x + 1)\<lbrakk>1/$x\<rbrakk>"
    by (simp add: assigns_r_comp alpha)
  also have "... = x := 1 + 1" 
    by (rel_tac)
  also have "... = x := 2"
    by (simp)
  finally show ?thesis .
qed

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y := 1,7)"
  by (rel_tac)

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y := 1,7)"
proof -
  have 1:"(1 :\<^sub>u int) >\<^sub>u 0 = true"
    by pred_tac
  have "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)\<lbrakk>1/$x\<rbrakk>"
    by (simp add: assigns_r_comp alpha)
  also have "... =  ((y := 7)\<lbrakk>1/$x\<rbrakk> \<triangleleft> (1 :\<^sub>u int) >\<^sub>u 0 \<triangleright> (y := 8)\<lbrakk>1/$x\<rbrakk>)"
    by (simp add: usubst)
  also have "... = (y := 7)\<lbrakk>1/$x\<rbrakk>"
    by (simp add: 1)
  also have "... = (x,y := 1,7)"
    by (rel_tac)
  finally show ?thesis .
qed

lemma "(x :=\<^sub>D 1 ;; x :=\<^sub>D &x + 1) = (x :=\<^sub>D 2)"
  by (simp add: assigns_d_comp usubst)

lemma violate_precond:
  "(true \<turnstile>\<^sub>n x := 1 ;; (&x >\<^sub>u 1) \<turnstile>\<^sub>n y := 2) = \<bottom>\<^sub>D"
proof -
  have ge1: "((1 :\<^sub>u int) >\<^sub>u 1) = false"
    by pred_tac
  have "(true \<turnstile>\<^sub>n x := 1 ;; (&x >\<^sub>u 1) \<turnstile>\<^sub>n y := 2) = (x := 1 wp (x >\<^sub>u 1) \<turnstile>\<^sub>n (x := 1 ;; y := 2))"
    by (simp add: ndesign_composition_wp unrest usubst)
  also have "... = ((1 :\<^sub>u int) >\<^sub>u 1) \<turnstile>\<^sub>n (x := 1 ;; y := 2)"
    by (simp add: wp usubst)
  also have "... = (false \<turnstile>\<^sub>n (x := 1 ;; y := 2))"
    by (simp add: ge1)
  also have "... = true"
    by (simp add: ndesign_false_pre)
  finally show ?thesis .
qed  

end

