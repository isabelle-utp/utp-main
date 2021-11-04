(*  Title:       CartesianClosedCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Cartesian Closed Category"

theory CartesianClosedCategory
imports CartesianCategory
begin

  text\<open>
    A \emph{cartesian closed category} is a cartesian category such that,
    for every object \<open>b\<close>, the functor \<open>prod \<hyphen> b\<close> is a left adjoint functor.
    A right adjoint to this functor takes each object \<open>c\<close> to the \emph{exponential}
    \<open>exp b c\<close>.  The adjunction yields a natural bijection between \<open>hom (prod a b) c\<close>
    and \<open>hom a (exp b c)\<close>.
  \<close>

  locale cartesian_closed_category =
    cartesian_category C
  for C :: "'a comp" +
  assumes left_adjoint_prod: "\<And>b. ide b \<Longrightarrow> left_adjoint_functor C C (\<lambda>x. prod x b)"

  locale elementary_cartesian_closed_category =
    elementary_cartesian_category C pr0 pr1 one trm
  for C :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixr \<open>\<cdot>\<close> 55)
  and pr0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>\<pp>\<^sub>0[_, _]\<close>)
  and pr1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (\<open>\<pp>\<^sub>1[_, _]\<close>)
  and one :: "'a"              (\<open>\<one>\<close>)
  and trm :: "'a \<Rightarrow> 'a"        (\<open>\<t>[_]\<close>)
  and exp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and eval :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  and \<Lambda> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" +
  assumes eval_in_hom: "\<lbrakk> ide b; ide c \<rbrakk> \<Longrightarrow> \<guillemotleft>eval b c : prod (exp b c) b \<rightarrow> c\<guillemotright>"
  and ide_exp: "\<lbrakk> ide b; ide c \<rbrakk> \<Longrightarrow> ide (exp b c)"
  and lam_in_hom: "\<lbrakk> ide a; ide b; ide c; \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright> \<rbrakk> \<Longrightarrow> \<guillemotleft>\<Lambda> a b c g : a \<rightarrow> exp b c\<guillemotright>"
  and eval_prod_lam: "\<lbrakk> ide a; ide b; ide c; \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright> \<rbrakk>
                          \<Longrightarrow> C (eval b c) (prod (\<Lambda> a b c g) b) = g"
  and lam_eval_prod: "\<lbrakk> ide a; ide b; ide c; \<guillemotleft>h : a \<rightarrow> exp b c\<guillemotright> \<rbrakk>
                          \<Longrightarrow> \<Lambda> a b c (C (eval b c) (prod h b)) = h"

  context cartesian_closed_category
  begin

    lemma has_exponentials:
    assumes "ide b" and "ide c"
    shows "\<exists>x e. ide x \<and> \<guillemotleft>e : prod x b \<rightarrow> c\<guillemotright> \<and>
                 (\<forall>a g. ide a \<and> \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright> \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> x\<guillemotright> \<and> g = C e (prod f b)))"
    proof -
      interpret F: left_adjoint_functor C C \<open>\<lambda>x. prod x b\<close>
        using assms(1) left_adjoint_prod by simp
      obtain x e where e: "terminal_arrow_from_functor C C (\<lambda>x. prod x b) x c e"
        using assms F.ex_terminal_arrow [of c] by auto
      interpret e: terminal_arrow_from_functor C C \<open>\<lambda>x. prod x b\<close> x c e
        using e by simp
      have "\<And>a g. \<lbrakk> ide a; \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright> \<rbrakk> \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> x\<guillemotright> \<and> g = C e (prod f b)"
        using e.is_terminal category_axioms F.functor_axioms
        unfolding e.is_coext_def arrow_from_functor_def arrow_from_functor_axioms_def
        by simp
      thus ?thesis
        using e.arrow by metis
    qed

    definition exp
    where "exp b c \<equiv> SOME x. ide x \<and>
                              (\<exists>e. \<guillemotleft>e : prod x b \<rightarrow> c\<guillemotright> \<and>
                                   (\<forall>a g. ide a \<and> \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright>
                                           \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> x\<guillemotright> \<and> g = C e (prod f b))))"

    definition eval
    where "eval b c \<equiv> SOME e. \<guillemotleft>e : prod (exp b c) b \<rightarrow> c\<guillemotright> \<and>
                              (\<forall>a g. ide a \<and> \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright>
                                       \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright> \<and> g = C e (prod f b)))"

    definition \<Lambda>
    where "\<Lambda> a b c g \<equiv> THE f. \<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright> \<and> g = C (eval b c) (prod f b)"

    lemma ex_un_lam:
    assumes "ide b" and "ide c"
    shows "ide (exp b c)" and "\<guillemotleft>eval b c : prod (exp b c) b \<rightarrow> c\<guillemotright>"
    and "\<lbrakk> ide a; \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright> \<rbrakk> \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright> \<and> g = C (eval b c) (prod f b)"
      using assms exp_def eval_def has_exponentials
            someI_ex [of "\<lambda>x. ide x \<and> (\<exists>e. \<guillemotleft>e : prod x b \<rightarrow> c\<guillemotright> \<and>
                                           (\<forall>a g. ide a \<and> \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright>
                                              \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> x\<guillemotright> \<and> g = C e (prod f b))))"]
            someI_ex [of "\<lambda>e. \<guillemotleft>e : prod (exp b c) b \<rightarrow> c\<guillemotright> \<and>
                              (\<forall>a g. ide a \<and> \<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright>
                                           \<longrightarrow> (\<exists>!f. \<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright> \<and> g = C e (prod f b)))"]
      by auto

    lemma eval_in_hom [intro]:
    assumes "ide b" and "ide c"
    shows "\<guillemotleft>eval b c : prod (exp b c) b \<rightarrow> c\<guillemotright>"
      using assms ex_un_lam by simp

    lemma eval_prod_lam:
    assumes "ide a" and "ide b" and "ide c" and "\<guillemotleft>g : prod a b \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>\<Lambda> a b c g : a \<rightarrow> exp b c\<guillemotright> \<and> g = C (eval b c) (prod (\<Lambda> a b c g) b)"
      using assms \<Lambda>_def ex_un_lam
            theI' [of "\<lambda>f. \<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright> \<and> g = C (eval b c) (prod f b)"]
      by simp

    lemma lam_eval_prod:
    assumes "ide a" and "ide b" and "ide c" and "\<guillemotleft>h : a \<rightarrow> exp b c\<guillemotright>"
    shows "\<Lambda> a b c (C (eval b c) (prod h b)) = h"
    proof -
      have "\<exists>!f. \<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright> \<and> C (eval b c) (prod h b) = C (eval b c) (prod f b)"
      proof -
        have "ide a \<and> \<guillemotleft>C (eval b c) (prod h b) : prod a b \<rightarrow> c\<guillemotright>"
        proof (intro conjI)
          show "ide a" by fact
          show "\<guillemotleft>C (eval b c) (prod h b) : prod a b \<rightarrow> c\<guillemotright>"
            using assms by (intro comp_in_homI) auto
        qed
        thus ?thesis
          using assms ex_un_lam by simp
      qed
      moreover have "\<guillemotleft>h : a \<rightarrow> exp b c\<guillemotright> \<and> C (eval b c) (prod h b) = C (eval b c) (prod h b)"
        using assms by simp
      ultimately show ?thesis
        using assms \<Lambda>_def ex_un_lam eval_prod_lam
              the1_equality [of "\<lambda>f. \<guillemotleft>f : a \<rightarrow> exp b c\<guillemotright> \<and>
                                     C (eval b c) (prod h b) = C (eval b c) (prod f b)"]
        by simp
    qed

    interpretation elementary_cartesian_closed_category C pr0 pr1 \<one> trm exp eval \<Lambda>
      using eval_in_hom ex_un_lam eval_prod_lam lam_eval_prod
      apply unfold_locales by auto

    lemma induces_elementary_cartesian_closed_category:
    shows "elementary_cartesian_closed_category C pr0 pr1 \<one> trm exp eval \<Lambda>"
      ..

  end

  context elementary_cartesian_closed_category
  begin

    lemma left_adjoint_prod:
    assumes "ide b"
    shows "left_adjoint_functor C C (\<lambda>x. x \<otimes> b)"
    proof -
      interpret "functor" C C \<open>\<lambda>x. x \<otimes> b\<close>
      proof
        show "\<And>f. \<not> arr f \<Longrightarrow> f \<otimes> b = null"
          using tuple_ext prod_def by auto
        fix f
        show "arr f \<Longrightarrow> dom (f \<otimes> b) = dom f \<otimes> b"
          using assms by simp
        show "arr f \<Longrightarrow> arr (f \<otimes> b)"
          using assms by simp
        show "arr f \<Longrightarrow> cod (f \<otimes> b) = cod f \<otimes> b"
          using assms by simp
        fix g
        show "seq g f \<Longrightarrow> g \<cdot> f \<otimes> b = (g \<otimes> b) \<cdot> (f \<otimes> b)"
          using assms interchange by simp
      qed
      interpret left_adjoint_functor C C \<open>\<lambda>x. x \<otimes> b\<close>
      proof
        show "\<And>c. ide c \<Longrightarrow> \<exists>x e. terminal_arrow_from_functor C C (\<lambda>x. x \<otimes> b) x c e"
        proof -
          fix c
          assume c: "ide c"
          show "\<exists>x e. terminal_arrow_from_functor C C (\<lambda>x. x \<otimes> b) x c e"
          proof (intro exI)
            interpret arrow_from_functor C C \<open>\<lambda>x. x \<otimes> b\<close> \<open>exp b c\<close> c \<open>eval b c\<close>
            proof
              show "ide (exp b c) \<and> \<guillemotleft>eval b c : exp b c \<otimes> b \<rightarrow> c\<guillemotright>"
              proof (intro conjI)
                show "\<guillemotleft>eval b c : exp b c \<otimes> b \<rightarrow> c\<guillemotright>"
                  using assms c eval_in_hom by simp
                show "ide (exp b c)"
                  using assms c ide_exp by simp
              qed
            qed
            interpret terminal_arrow_from_functor C C \<open>\<lambda>x. x \<otimes> b\<close> \<open>exp b c\<close> c \<open>eval b c\<close>
            proof
              show "\<And>a f. arrow_from_functor C C (\<lambda>x. x \<otimes> b) a c f \<Longrightarrow>
                            \<exists>!g. arrow_from_functor.is_coext C C
                                   (\<lambda>x. x \<otimes> b) (exp b c) (eval b c) a f g"
              proof -
                fix a f
                assume f: "arrow_from_functor C C (\<lambda>x. x \<otimes> b) a c f"
                interpret f: arrow_from_functor C C \<open>\<lambda>x. x \<otimes> b\<close> a c f
                  using f by simp
                show "\<exists>!g. is_coext a f g"
                proof
                  have a: "ide a"
                    using f.arrow by simp
                  show "is_coext a f (\<Lambda> a b c f)"
                    unfolding is_coext_def
                    using assms a c lam_in_hom [of a b c f] eval_prod_lam [of a b c f]
                          f.arrow
                    by simp
                  show "\<And>g. is_coext a f g \<Longrightarrow> g = \<Lambda> a b c f"
                    unfolding is_coext_def
                    using assms a c lam_eval_prod [of a b c] f.arrow by simp
                qed
              qed
            qed
            show "terminal_arrow_from_functor C C (\<lambda>x. x \<otimes> b) (exp b c) c (eval b c)" ..
          qed
        qed
      qed
      show ?thesis ..
    qed

    interpretation CCC: cartesian_category C
      using is_cartesian_category by simp

    interpretation CCC: cartesian_closed_category C
    proof
      fix b
      assume b: "ide b"
      interpret left_adjoint_functor C C \<open>\<lambda>x. CCC.prod x b\<close>
      proof -
        (*
         * We know that (\<lambda>x. x \<otimes> b) is a left adjoint functor, where \<otimes> is the
         * product ultimately defined in terms of the projections that are parameters
         * to the elementary_category_with_binary_products locale that is the present context.
         * This is not necessarily the same as (\<lambda>x. CCC.prod x b), which is defined in terms
         * of projections chosen arbitrarily in category_with_binary_products.
         * However, since they are both categorical products, they are naturally isomorphic,
         * so one is a left adjoint functor if and only if the other is.
         *)
        have "naturally_isomorphic C C (\<lambda>x. x \<otimes> b) (\<lambda>x. CCC.prod x b)"
        proof -
          interpret CC: product_category C C ..
          interpret X: binary_functor C C C \<open>\<lambda>fg. fst fg \<otimes> snd fg\<close>
            using binary_functor_Prod(1) by auto
          interpret Xb: "functor" C C \<open>\<lambda>x. x \<otimes> b\<close>
            using b X.fixing_ide_gives_functor_2 by simp
          interpret prod: binary_functor C C C \<open>\<lambda>fg. CCC.prod (fst fg) (snd fg)\<close>
            using CCC.binary_functor_Prod(1) by simp
          interpret prod_b: "functor" C C \<open>\<lambda>x. CCC.prod x b\<close>
             using b prod.fixing_ide_gives_functor_2 by simp
          interpret \<phi>: transformation_by_components C C \<open>\<lambda>x. x \<otimes> b\<close> \<open>\<lambda>x. CCC.prod x b\<close>
                         \<open>\<lambda>a. CCC.tuple (pr1 a b) (pr0 a b)\<close>
            using b CCC.prod_tuple by unfold_locales auto
          interpret \<phi>: natural_isomorphism C C \<open>\<lambda>x. x \<otimes> b\<close> \<open>\<lambda>x. CCC.prod x b\<close> \<phi>.map
          proof
            fix a
            assume a: "ide a"
            show "iso (\<phi>.map a)"
            proof
              show "inverse_arrows (\<phi>.map a) \<langle>CCC.pr1 a b, CCC.pr0 a b\<rangle>"
                using a b by auto
            qed
          qed
          show ?thesis
            using naturally_isomorphic_def \<phi>.natural_isomorphism_axioms by blast
        qed
        moreover have "left_adjoint_functor C C (\<lambda>x. x \<otimes> b)"
          using b left_adjoint_prod [of b] by simp
        ultimately show "left_adjoint_functor C C (\<lambda>x. CCC.prod x b)"
          using left_adjoint_functor_respects_naturally_isomorphic by auto
      qed
      show "\<And>f. \<not> arr f \<Longrightarrow> CCC.prod f b = null"
        using is_extensional by blast
      show "\<And>f. arr f \<Longrightarrow> dom (CCC.prod f b) = CCC.prod (dom f) b"
        by simp
      show "\<And>f. arr f \<Longrightarrow> cod (CCC.prod f b) = CCC.prod (cod f) b"
        by simp
      show "\<And>f. arr f \<Longrightarrow> arr (CCC.prod f b)"
        by simp
      show "\<And>g f. seq g f \<Longrightarrow> CCC.prod (g \<cdot> f) b = CCC.prod g b \<cdot> CCC.prod f b"
        by simp
      show "\<And>y. ide y \<Longrightarrow> \<exists>x e. terminal_arrow_from_functor (\<cdot>) (\<cdot>) (\<lambda>x. CCC.prod x b) x y e"
        using ex_terminal_arrow by simp
    qed

    lemma is_cartesian_closed_category:
    shows "cartesian_closed_category C"
      ..

  end

end
