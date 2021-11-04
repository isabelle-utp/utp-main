(*
    File:     Group_Hom.thy
    Author:   Joseph Thommes, TU München
*)
section \<open>Group Homomorphisms\<close>

theory Group_Hom
  imports Set_Multiplication
begin

text \<open>This section extends the already existing library about group homomorphisms in HOL-Algebra by
some useful lemmas. These were mainly inspired by the needs that arised throughout the other proofs.\<close>

lemma (in group_hom) generate_hom:
  assumes "A \<subseteq> carrier G"
  shows "h ` (generate G A) = generate H (h ` A)"
  using assms group_hom.generate_img group_hom_axioms by blast

text \<open>For two elements with the same image we can find an element in the kernel that maps one of the
two elements on the other by multiplication.\<close>

lemma (in group_hom) kernel_assoc_elem:
  assumes "x \<in> carrier G" "y \<in> carrier G" "h x = h y"
  obtains z where "x = y \<otimes>\<^bsub>G\<^esub> z" "z \<in> kernel G H h"
proof -
  have c: "inv y \<otimes>\<^bsub>G\<^esub> x \<in> carrier G" using assms by simp
  then have e: "x = y \<otimes>\<^bsub>G\<^esub> (inv y \<otimes>\<^bsub>G\<^esub> x)" using assms G.m_assoc
    using G.inv_solve_left by blast
  then have "h x = h (y \<otimes>\<^bsub>G\<^esub> (inv y \<otimes>\<^bsub>G\<^esub> x))" by simp
  then have "h x = h y \<otimes>\<^bsub>H\<^esub> h (inv y \<otimes>\<^bsub>G\<^esub> x)" using c assms by simp
  then have "\<one>\<^bsub>H\<^esub> = h (inv y \<otimes>\<^bsub>G\<^esub> x)" using assms by simp
  then have "(inv y \<otimes>\<^bsub>G\<^esub> x) \<in> kernel G H h" unfolding kernel_def using c by simp
  thus ?thesis using e that by blast
qed

text \<open>This can then be used to characterize the pre-image of a set $A$ under homomorphism as a
product of $A$ itself with the kernel of the homomorphism.\<close>

lemma (in group_hom) vimage_eq_set_mult_kern_right:
  assumes "A \<subseteq> carrier G"
  shows "{x \<in> carrier G. h x \<in> h ` A} = A <#> kernel G H h"
proof(intro equalityI subsetI)
  fix x
  assume assm: "x \<in> A <#> kernel G H h"
  then have xc: "x \<in> carrier G" unfolding kernel_def set_mult_def using assms by blast
  from assm obtain a b where ab: "a \<in> A" "b \<in> kernel G H h" "x = a \<otimes>\<^bsub>G\<^esub> b"
    unfolding set_mult_def by blast
  then have abc: "a \<in> carrier G" "b \<in> carrier G" unfolding kernel_def using assms by auto
  from ab have "h x = h (a \<otimes>\<^bsub>G\<^esub> b)" by blast
  also have "\<dots> = h a \<otimes>\<^bsub>H\<^esub> h b" using abc by simp
  also have "\<dots> = h a \<otimes>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub>" using ab(2) unfolding kernel_def by simp
  also have "\<dots> = h a" using abc by simp
  also have "\<dots> \<in> h ` A" using ab by blast 
  finally have "h x \<in> h ` A" .
  thus "x \<in> {x \<in> carrier G. h x \<in> h ` A}" using xc by blast
next
  fix x
  assume "x \<in> {x \<in> carrier G. h x \<in> h ` A}"
  then have x: "x \<in> carrier G" "h x \<in> h ` A" by simp+
  then obtain y where y: "y \<in> A" "h x = h y" "y \<in> carrier G" using assms by auto
  with kernel_assoc_elem obtain z where "x = y \<otimes>\<^bsub>G\<^esub> z" "z \<in> kernel G H h" using x by metis
  thus "x \<in> A <#> kernel G H h" unfolding set_mult_def using y by blast
qed

lemma (in group_hom) vimage_subset_generate_kern:
  assumes "A \<subseteq> carrier G"
  shows "{x \<in> carrier G. h x \<in> h ` A} \<subseteq> generate G (A \<union> kernel G H h)"
  using vimage_eq_set_mult_kern_right[of A] G.set_mult_subset_generate[of "A" "kernel G H h"] assms
  unfolding kernel_def by blast

text \<open>The preimage of a subgroup under a homomorphism is also a subgroup.\<close>

lemma (in group_hom) subgroup_vimage_is_subgroup:
  assumes "subgroup I H"
  shows "subgroup {x \<in> carrier G. h x \<in> I} G" (is "subgroup ?J G")
proof
  show "?J \<subseteq> carrier G" by blast
  show "\<one> \<in> ?J" using subgroup.one_closed[of I H] assms by simp
  fix x
  assume x: "x \<in> ?J"
  then have hx: "h x \<in> I" by blast
  show "inv x \<in> ?J"
  proof -
    from hx have "inv\<^bsub>H\<^esub> (h x) \<in> I" using subgroup.m_inv_closed assms by fast
    moreover have "inv x \<in> carrier G" using x by simp
    moreover have "inv\<^bsub>H\<^esub> (h x) = h (inv x)" using x by auto
    ultimately show "inv x \<in> ?J" by simp
  qed
  fix y
  assume y: "y \<in> ?J"
  then have hy: "h y \<in> I" by blast
  show "x \<otimes> y \<in> {x \<in> carrier G. h x \<in> I}"
  proof -
    have "h (x \<otimes> y) = h x \<otimes>\<^bsub>H\<^esub> h y" using x y by simp
    also have "\<dots> \<in> I" using hx hy assms subgroup.m_closed by fast
    finally have "h (x \<otimes> y) \<in> I" .
    moreover have "x \<otimes> y \<in> carrier G" using x y by simp
    ultimately show ?thesis by blast
  qed
qed

lemma (in group_hom) iso_kernel:
  assumes "h \<in> iso G H"
  shows "kernel G H h = {\<one>\<^bsub>G\<^esub>}"
  unfolding kernel_def using assms
  using hom_one iso_iff by blast

\<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close> (* adapted by Joseph Thommes *)
lemma (in group_hom) induced_group_hom_same_group: 
  assumes "subgroup I G"
  shows "group_hom (G \<lparr> carrier := I \<rparr>) H h"
proof -
  have "h \<in> hom (G \<lparr> carrier := I \<rparr>) H"
    using homh subgroup.mem_carrier[OF assms] unfolding hom_def by auto
  thus ?thesis
    unfolding group_hom_def group_hom_axioms_def
    using subgroup.subgroup_is_group[OF assms G.is_group] by simp
qed

text \<open>The order of an element under a homomorphism divides the order of the element.\<close>

lemma (in group_hom) hom_ord_dvd_ord:
  assumes "a \<in> carrier G"
  shows "H.ord (h a) dvd G.ord a"
proof -
  have "h a [^]\<^bsub>H\<^esub> (G.ord a) = h (a [^]\<^bsub>G\<^esub> G.ord a)"
    using assms local.hom_nat_pow by presburger
  also have "\<dots> = h (\<one>\<^bsub>G\<^esub>)" using G.pow_ord_eq_1 assms by simp
  also have "\<dots> = \<one>\<^bsub>H\<^esub>" by simp
  finally have "h a [^]\<^bsub>H\<^esub> G.ord a = \<one>\<^bsub>H\<^esub>" .
  then show ?thesis using pow_eq_id assms by simp
qed

text \<open>In particular, this implies that the image of an element with a finite order also will have a
finite order.\<close>

lemma (in group_hom) finite_ord_stays_finite:
  assumes "a \<in> carrier G" "G.ord a \<noteq> 0"
  shows "H.ord (h a) \<noteq> 0"
  using hom_ord_dvd_ord assms by fastforce

text \<open>For injective homomorphisms, the order stays the same.\<close>

lemma (in group_hom) inj_imp_ord_eq:
  assumes "a \<in> carrier G" "inj_on h (carrier G)" "G.ord a \<noteq> 0"
  shows "H.ord (h a) = G.ord a"
proof (rule antisym)
  show "H.ord (h a) \<le> G.ord a" using hom_ord_dvd_ord assms by force
  show "G.ord a \<le> H.ord (h a)"
  proof -
    have "\<one>\<^bsub>H\<^esub> = h (a [^]\<^bsub>G\<^esub> H.ord(h a))" using H.pow_ord_eq_1 assms
      by (simp add: local.hom_nat_pow)
    then have "a [^]\<^bsub>G\<^esub> H.ord (h a) = \<one>\<^bsub>G\<^esub>" using assms inj_on_one_iff by simp
    then have "G.ord a dvd H.ord (h a)" using G.pow_eq_id assms(1) by blast
    thus ?thesis using assms finite_ord_stays_finite by fastforce
  qed
qed

lemma (in group_hom) one_in_kernel:
  "\<one> \<in> kernel G H h"
  using subgroup.one_closed subgroup_kernel by blast

lemma hom_in_carr:
  assumes "f \<in> hom G H"
  shows "\<And>x. x \<in> carrier G \<Longrightarrow> f x \<in> carrier H"
  using assms unfolding hom_def bij_betw_def by blast

lemma iso_in_carr:
  assumes "f \<in> iso G H"
  shows "\<And>x. x \<in> carrier G \<Longrightarrow> f x \<in> carrier H"
  using assms unfolding iso_def bij_betw_def by blast

lemma triv_iso:
  assumes "group G" "group H" "carrier G = {\<one>\<^bsub>G\<^esub>}" "carrier H = {\<one>\<^bsub>H\<^esub>}"
  shows "G \<cong> H"
proof(unfold is_iso_def iso_def)
  interpret G: group G by fact
  interpret H: group H by fact
  let ?f = "\<lambda>_. \<one>\<^bsub>H\<^esub>"
  have "?f \<in> hom G H" by (intro homI, auto)
  moreover have "bij_betw ?f (carrier G) (carrier H)" unfolding bij_betw_def
    using assms(3, 4) by auto
  ultimately show "{h \<in> hom G H. bij_betw h (carrier G) (carrier H)} \<noteq> {}" by blast
qed

text \<open>The cardinality of the image of a group homomorphism times the cardinality of its kernel is
equal to the group order. This is basically another form of Lagrange's theorem.\<close>

lemma (in group_hom) image_kernel_product: "card (h ` (carrier G)) * card (kernel G H h) = order G" 
proof -
  interpret G: group G by simp
  interpret H: group H by simp
  interpret ih: subgroup "h ` (carrier G)" H using img_is_subgroup by blast
  interpret ih: group "H\<lparr>carrier := h ` (carrier G)\<rparr>" using subgroup.subgroup_is_group by blast
  interpret h: group_hom G "H\<lparr>carrier := h ` (carrier G)\<rparr>"
    by (unfold_locales, unfold hom_def, auto)
  interpret k: subgroup "kernel G (H\<lparr>carrier := h ` carrier G\<rparr>) h" G using h.subgroup_kernel by blast
  from h.FactGroup_iso
  have "G Mod kernel G (H\<lparr>carrier := h ` carrier G\<rparr>) h \<cong> H\<lparr>carrier := h ` carrier G\<rparr>" by auto
  hence "card (h ` (carrier G)) = order (G Mod kernel G (H\<lparr>carrier := h ` carrier G\<rparr>) h)"
    using iso_same_card unfolding order_def by fastforce
  moreover have "order (G Mod kernel G (H\<lparr>carrier := h ` carrier G\<rparr>) h)
                 * card (kernel G (H\<lparr>carrier := h ` carrier G\<rparr>) h) = order G"
    using G.lagrange[OF k.subgroup_axioms] unfolding order_def FactGroup_def by force
  moreover have "kernel G (H\<lparr>carrier := h ` carrier G\<rparr>) h = kernel G H h"
    unfolding kernel_def by auto
  ultimately show ?thesis by argo
qed

end