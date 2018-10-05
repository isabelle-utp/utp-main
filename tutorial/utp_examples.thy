section {* Isabelle/UTP Examples *}

theory utp_examples
  imports 
    "UTP-Designs.utp_designs"
    "UTP.utp_easy_parser"
begin recall_syntax

alphabet my_state =
  x :: "int"
  y :: "int"
  z :: "int"

(* Beginning of exercises *)

lemma "(true \<and> false) = false"
  by simp

lemma "true = false"
  oops (* Not provable: show pred_auto produces False *)

lemma "x \<sharp> true"
  by unrest_tac

lemma "x \<sharp> &y"
  by unrest_tac

lemma "(&x =\<^sub>u 1 \<and> &y =\<^sub>u &x) = (&x =\<^sub>u 1 \<and> &y =\<^sub>u 1)"
  by pred_auto

lemma "(&x =\<^sub>u 1 \<and> &y =\<^sub>u &x)\<lbrakk>2/x\<rbrakk> = false"
  apply (subst_tac)
  apply (pred_auto)
done

(* The next two examples illustrate UTP and shallow lifted quantification *)

lemma "(\<forall> x \<bullet> &x =\<^sub>u &x) = true"
  by (pred_auto)

lemma "(\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> =\<^sub>u \<guillemotleft>x\<guillemotright>) = true"
  by (pred_auto)

lemma "(1 :\<^sub>u nat) + 1 = 2"
  by (pred_auto)

lemma "(x := 1 ;; x := x + 1) = (x := 2)"
  by (rel_auto)

lemma "(x := 1 ;; x := x + 1) = (x := 2)"
proof -
  have "x := 1 ;; x := x + 1 = (x := (x + 1))\<lbrakk>1/$x\<rbrakk>"
    by (simp add: assigns_r_comp alpha usubst)
  also have "... = x := (1 + 1)"
    by (rel_auto)
  also have "... = x := 2"
    by (simp)
  finally show ?thesis .
qed

lemma "true \<sqsubseteq> x, y := x + 1, y"
  by (rel_auto)

(* Need to change y' < y to y' = y or similar to discharge with rel_auto *)
lemma "($x\<acute> >\<^sub>u $x \<and> $y\<acute> <\<^sub>u $y) \<sqsubseteq> x, y := x + 1, y"
  oops

lemma "false \<sqsubseteq> x, y := x + 1, y"
  apply (rel_simp)
  oops

lemma "(true ;; x := \<guillemotleft>c\<guillemotright>) = ($x\<acute> =\<^sub>u \<guillemotleft>c\<guillemotright>)"
  oops (* Modified Jim's property *)

lemma "x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8) = (x,y) := (1,7)"
  oops

lemma "x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8) = (x,y) := (1,7)"
  oops (* Redo above as Isar proof *)

lemma wp_ex_1: "x := x - 5 wp (x > 10) = (&x >\<^sub>u 15)"
  oops (* Use wp_tac, subst_tac, and pred_auto *)

lemma wp_ex_2: "x := x - 5 ;; x := (x div 2) wp (x > 20) = (&x >\<^sub>u 46)"
  oops

lemma wp_ex_3:
      "(x := \<guillemotleft>X\<guillemotright> ;;
        y := \<guillemotleft>Y\<guillemotright> ;;
        x := x + y ;;
        y := x - y ;;
        x := x - y) wp (x = \<guillemotleft>Y\<guillemotright> \<and> y = \<guillemotleft>X\<guillemotright>) = true"
  oops

lemma wp_ex_4:
      "((x := \<guillemotleft>X\<guillemotright> ;;
         y := \<guillemotleft>Y\<guillemotright> ;;
         x := x * y ;;
         y := x div y ;;
         x := x div y) wp (x = \<guillemotleft>Y\<guillemotright> \<and> y = \<guillemotleft>X\<guillemotright>)) = true"
  oops (* Additional assumptions are needed *)

lemma hoare_ex_1:
  "{{true}} if x > y then z := x else z := y fi {{z = max(x, y)}}"
  apply (hoare_auto)
  oops

lemma hoare_ex_2:
  assumes "X > 0" "Y > 0"
  shows
  "{{x = \<guillemotleft>X\<guillemotright> \<and> y = \<guillemotleft>Y\<guillemotright>}}
    while \<not>(x = y)
    invr x > 0 \<and> y > 0 \<and> (gcd(x,y) = gcd(\<guillemotleft>X\<guillemotright>,\<guillemotleft>Y\<guillemotright>))
    do
       if x > y then x := x - y else y := y - x fi
    od
    {{x = gcd(\<guillemotleft>X\<guillemotright>, \<guillemotleft>Y\<guillemotright>)}}"
  using assms
  apply (hoare_auto)
  apply (simp add: gcd_diff1)
  oops
  
lemma hoare_ex_3:
  assumes "X > 0" "Y > 0"
  shows
  "{{x = \<guillemotleft>X\<guillemotright> \<and> y = \<guillemotleft>Y\<guillemotright>}}
    while \<not>(x = y)
    invr x > 0 \<and> y > 0 \<and> (gcd(x,y) = gcd(\<guillemotleft>X\<guillemotright>,\<guillemotleft>Y\<guillemotright>))
    vrt nat(x + y)
    do
       if x > y then x := x - y else y := y - x fi
    od
    {{x = gcd(\<guillemotleft>X\<guillemotright>, \<guillemotleft>Y\<guillemotright>)}}"
  using assms 
  apply (hoare_auto)
  oops
    
lemma "x :=\<^sub>D 1 ;; x :=\<^sub>D (x + 1) = x :=\<^sub>D 2"
  oops (* Rule required: assigns_d_comp *)

lemma violate_precond:
  "(true \<turnstile>\<^sub>n x := 1) ;; ((&x >\<^sub>u 1) \<turnstile>\<^sub>n y := 2) = \<bottom>\<^sub>D"
  oops (* Prove using Isar *)
end