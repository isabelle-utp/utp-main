theory utp_lens_demo
  imports "../theories/utp_designs"
begin

alphabet person =
  surname :: string
  forename :: string
  dateOfBirth :: "nat * nat * nat"

alphabet myst =
  x :: nat
  y :: person
  z :: "int list"

lemma "(\<exists> x \<bullet> &x >\<^sub>u 1) = true"
  by (rel_auto)

lemma "(\<forall> x \<bullet> &x >\<^sub>u 1) = true"
  apply (rel_simp)
  nitpick
oops

lemma "(x := 1 ;; x := &x + 1) = (x := 2)"
  by (rel_auto)

lemma "(x := 1 ;; x := &x + 2) = (x := 2)"
  apply (rel_auto)
  oops

lemma "(x := &x - 5) wp (&x >\<^sub>u 10) = (&x >\<^sub>u 15)"
  apply (simp add: wp)
  apply (subst_tac)
  apply (pred_auto)
done

lemma "(true \<turnstile>\<^sub>n x := 1 ;; (&x >\<^sub>u 1) \<turnstile>\<^sub>n y := &y) = \<bottom>\<^sub>D"
  apply (simp add: ndesign_composition_wp)
  apply (simp add: wp)
  apply (subst_tac)
  apply (pred_auto)
done

term "x +\<^sub>L y"

lemma "x \<bowtie> y"
  by (simp)

lemma "x +\<^sub>L y \<bowtie> z"
  by (simp add: plus_pres_lens_indep)

term "surname ;\<^sub>L y"

term "y:surname := \<guillemotleft>''Foster''\<guillemotright> ;; y:dateOfBirth := (02, 02, &x)\<^sub>u"

lemma "(surname ;\<^sub>L y) \<subseteq>\<^sub>L y"
  by (simp add: lens_comp_lb)

lemma "x +\<^sub>L y +\<^sub>L z \<approx>\<^sub>L 1\<^sub>L"
  oops
end