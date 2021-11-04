theory Padic_Construction
imports "HOL-Number_Theory.Residues" "HOL-Algebra.RingHom" "HOL-Algebra.IntRing"
begin

type_synonym padic_int = "nat \<Rightarrow> int"

section  \<open>Inverse Limit Construction of the $p$-adic Integers\<close>

text\<open>
  This section formalizes the standard construction of the $p$-adic integers as the inverse
  limit of the finite rings $\mathbb{Z} / p^n \mathbb{Z}$ along the residue maps
  $\mathbb{Z} / p^n \mathbb{Z} \mapsto \mathbb{Z} / p^n \mathbb{Z} $ defined by
  $x \mapsto x \mod p^m$ when $n \geq m$. This is exposited, for example, in section 7.6 of 
  \cite{dummit2004abstract}. The other main route for formalization is to first define the
  $p$-adic absolute value $|\cdot|_p$ on the rational numbers, and then define the field
  $\mathbb{Q}_p$ of $p$-adic numbers as the completion of the rationals under this absolute
  value. One can then define the ring of $p$-adic integers $\mathbb{Z}_p$ as the unit ball in 
  $\mathbb{Q}_p$ using the unique extension of $|\cdot|_p$. There exist advantages and 
  disadvantages to both approaches. The primary advantage to the absolute value approach is 
  that the construction can be done generically using existing libraries for completions of 
  normed fields. There are difficulties associated with performing such a construction in 
  Isabelle using existing HOL formalizations. The chief issue is that the tools in HOL-Analysis 
  require that a metric space be a type. If one then wanted to construct the fields 
  $\mathbb{Q}_p$ as metric spaces, one would have to circumvent the apparent dependence on 
  the parameter $p$, as Isabelle does not support dependent types. A workaround to this proposed 
  by José Manuel Rodríguez Caballero on the Isabelle mailing list is to define a typeclass for 
  fields $\mathbb{Q}_p$ as the completions of the rational numbers with a non-Archimedean absolute 
  value. By Ostrowski's Theorem, any such absolute value must be a $p$-adic absolute value. We can 
  recover the parameter $p$ from a completion under one of these absolute values as the cardinality 
  of the residue field.

  Our approach uses HOL-Algebra, where algebraic structures are constructed as records which carry 
  the data of the underlying carrier set plus other algebraic operations, and assumptions about 
  these structures can be organized into locales. This approach is practical for abstract 
  algebraic reasoning where definitions of structures which are dependent on object-level 
  parameters are ubiquitous. Using this approach, we define $\mathbb{Z}_p$ directly as an 
  inverse limit of rings, from which $\mathbb{Q}_p$ can later be defined as the field of fractions.
\<close>

subsection\<open>Canonical Projection Maps Between Residue Rings\<close>

definition residue :: "int \<Rightarrow> int \<Rightarrow> int" where 
"residue n m = m mod n"

lemma residue_is_hom_0:
  assumes "n > 1"
  shows "residue n \<in> ring_hom \<Z> (residue_ring n)" 
proof(rule ring_hom_memI)
  have R: "residues n" 
    by (simp add: assms residues_def) 
  show "\<And>x. x \<in> carrier \<Z> \<Longrightarrow> residue n x \<in> carrier (residue_ring n)"
    using assms residue_def residues.mod_in_carrier residues_def by auto 
  show " \<And>x y. x \<in> carrier \<Z> \<Longrightarrow> y \<in> carrier \<Z> \<Longrightarrow>
   residue n (x \<otimes>\<^bsub>\<Z>\<^esub> y) = residue n x \<otimes>\<^bsub>residue_ring n\<^esub> residue n y"
    by (simp add: R residue_def residues.mult_cong) 
  show "\<And>x y. x \<in> carrier \<Z> \<Longrightarrow>
               y \<in> carrier \<Z> \<Longrightarrow>
         residue n (x \<oplus>\<^bsub>\<Z>\<^esub> y) = residue n x \<oplus>\<^bsub>residue_ring n\<^esub> residue n y"
    by (simp add: R residue_def residues.res_to_cong_simps(1)) 
  show "residue n \<one>\<^bsub>\<Z>\<^esub> = \<one>\<^bsub>residue_ring n\<^esub>" 
    by (simp add: R residue_def residues.res_to_cong_simps(4)) 
qed

text\<open>The residue map is a ring homomorphism from $\mathbb{Z}/m\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$ when n divides m\<close>

lemma residue_is_hom_1:
  assumes "n > 1"
  assumes "m > 1"
  assumes "n dvd m"
  shows "residue n \<in> ring_hom (residue_ring m) (residue_ring n)"
proof(rule ring_hom_memI)
  have 0: "residues n" 
    by (simp add: assms(1) residues_def) 
  have 1: "residues m" 
    by (simp add: assms(2) residues_def) 
  show "\<And>x. x \<in> carrier (residue_ring m) \<Longrightarrow> residue n x \<in> carrier (residue_ring n)" 
    using assms(1) residue_def residue_ring_def by auto 
  show "\<And>x y. x \<in> carrier (residue_ring m) \<Longrightarrow>
               y \<in> carrier (residue_ring m) \<Longrightarrow> 
          residue n (x \<otimes>\<^bsub>residue_ring m\<^esub> y) = residue n x \<otimes>\<^bsub>residue_ring n\<^esub> residue n y"
    using 0 1 assms by (metis mod_mod_cancel residue_def residues.mult_cong residues.res_mult_eq) 
  show "\<And>x y. x \<in> carrier (residue_ring m) 
        \<Longrightarrow> y \<in> carrier (residue_ring m) 
        \<Longrightarrow> residue n (x \<oplus>\<^bsub>residue_ring m\<^esub> y) = residue n x \<oplus>\<^bsub>residue_ring n\<^esub> residue n y"
    using 0 1 assms by (metis mod_mod_cancel residue_def residues.add_cong residues.res_add_eq) 
  show "residue n \<one>\<^bsub>residue_ring m\<^esub> = \<one>\<^bsub>residue_ring n\<^esub>" 
    by (simp add: assms(1) residue_def residue_ring_def) 
qed

lemma residue_id:
  assumes "x \<in> carrier (residue_ring n)"
  assumes "n \<ge>0"
  shows "residue n x = x"
proof(cases "n=0")
  case True
  then show ?thesis 
    by (simp add: residue_def) 
next
  case False 
  have 0: "x \<ge>0"  
    using assms(1)  by (simp add: residue_ring_def)
  have 1: "x < n" 
    using assms(1) residue_ring_def by auto 
  have "x mod n = x" 
    using 0 1 by simp 
  then show ?thesis 
    using residue_def by auto
qed

text\<open>
  The residue map is a ring homomorphism from
  $\mathbb{Z}/p^n\mathbb{Z} \to \mathbb{Z}/p^m\mathbb{Z}$ when $n \geq m$:
\<close>

lemma residue_hom_p:
  assumes "(n::nat) \<ge> m"
  assumes "m >0"
  assumes "prime (p::int)"
  shows "residue (p^m) \<in> ring_hom (residue_ring (p^n)) (residue_ring (p^m))"
proof(rule residue_is_hom_1)
  show " 1 < p^n" using assms  
    using prime_gt_1_int by auto
  show "1 < p^m" 
    by (simp add: assms(2) assms(3) prime_gt_1_int)
  show "p ^ m dvd p ^ n" using assms(1) 
    by (simp add: dvd_power_le) 
qed

subsection\<open>Defining the Set of $p$-adic Integers\<close>

text\<open>
  The set of $p$-adic integers is the set of all maps $f: \mathbb{N} \to \mathbb{Z}$ which maps
  $n \to \{0,...,p^n -1\}$ such that $f m \mod p^{n} = f n$ when $m \geq n$. A p-adic integer $x$
  consists of the data of a residue map $x \mapsto x\mod p^n$ which commutes with further reduction
  $\mod p^m$. This formalization is specialized to just the $p$-adics, but this definition would
  work essentially as-is for any family of rings and residue maps indexed by a partially
  ordered type.
\<close>

definition padic_set :: "int \<Rightarrow> padic_int set" where
"padic_set p = {f::nat \<Rightarrow> int .(\<forall> m::nat. (f m) \<in> carrier (residue_ring (p^m)))
                  
                   \<and>(\<forall>(n::nat) (m::nat). n > m \<longrightarrow> residue (p^m) (f n) = (f m)) }"


lemma padic_set_res_closed:
  assumes "f \<in> padic_set p"
  shows "(f m) \<in> (carrier (residue_ring (p^m)))" 
  using assms padic_set_def by auto  

lemma padic_set_res_coherent:
  assumes "f \<in> padic_set p"
  assumes "n \<ge> m"
  assumes "prime p"
  shows "residue (p^m) (f n) = (f m)"
proof(cases "n=m")
  case True
  have "(f m) \<in> carrier (residue_ring (p^m))" 
    using assms padic_set_res_closed by blast 
  then have "residue (p^m) (f m) = (f m)" 
    by (simp add: residue_def residue_ring_def) 
  then show ?thesis 
    using True by blast 
next
  case False
  then show ?thesis
    using assms(1) assms(2) padic_set_def by auto 
qed

text\<open>
  A consequence of this formalization is that each $p$-adic number is trivially
  defined to take a value of $0$ at $0$:
\<close>

lemma padic_set_zero_res:
  assumes "prime p"
  assumes "f \<in> (padic_set p)"
  shows "f 0 = 0"
proof-
  have "f 0 \<in> carrier (residue_ring 1)" 
    using assms(1) padic_set_res_closed 
    by (metis assms(2)  power_0) 
  then show ?thesis 
    using residue_ring_def  by simp 
qed

lemma padic_set_memI:
  fixes f :: "padic_int"
  assumes "\<And>m. (f m) \<in> (carrier (residue_ring (p^m)))"
  assumes "(\<And>(m::nat) n. (n > m \<Longrightarrow> (residue (p^m) (f n) = (f m))))"
  shows "f \<in> padic_set (p::int)"
  by (simp add: assms(1) assms(2) padic_set_def) 

lemma padic_set_memI':
  fixes f :: "padic_int"
  assumes "\<And>m. (f m) \<in> {0..<p^m}"
  assumes "\<And>(m::nat) n. n > m \<Longrightarrow> (f n) mod p^m = (f m)"
  shows "f \<in> padic_set (p::int)"
  apply(rule padic_set_memI)
  using assms(1) residue_ring_def apply auto[1]
  by (simp add: assms(2) residue_def)


section\<open>The standard operations on the $p$-adic integers\<close>

    (**********************************************************************************************)
    subsection\<open>Addition\<close>
    (**********************************************************************************************)

text\<open>Addition and multiplication are defined componentwise on residue rings:\<close>

definition padic_add :: "int \<Rightarrow> padic_int \<Rightarrow> padic_int \<Rightarrow> padic_int " 
  where "padic_add p f g \<equiv> (\<lambda> n. (f n) \<oplus>\<^bsub>(residue_ring (p^n))\<^esub> (g n))"

lemma padic_add_res:
"(padic_add p f g) n = (f n) \<oplus>\<^bsub>(residue_ring (p^n))\<^esub> (g n)"
  by (simp add: padic_add_def) 

text\<open>Definition of the $p$-adic additive unit:\<close>

definition padic_zero :: "int \<Rightarrow> padic_int" where
"padic_zero p \<equiv> (\<lambda>n. 0)"

lemma padic_zero_simp:
"padic_zero p n = \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
"padic_zero p n = 0"
  apply (simp add: padic_zero_def residue_ring_def) 
  using  padic_zero_def by auto

lemma padic_zero_in_padic_set:
  assumes "p > 0"
  shows "padic_zero p \<in> padic_set p" 
  apply(rule padic_set_memI)
  by(auto simp: assms padic_zero_def residue_def residue_ring_def)

text\<open>$p$-adic additive inverses:\<close>

definition padic_a_inv :: "int \<Rightarrow>  padic_int \<Rightarrow>  padic_int" where
"padic_a_inv p f \<equiv> \<lambda> n. \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (f n)"

lemma padic_a_inv_simp:
"padic_a_inv p f n\<equiv> \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (f n)"
   by (simp add: padic_a_inv_def) 

lemma padic_a_inv_simp':
  assumes "prime p"
  assumes "f \<in> padic_set p"
  assumes "n >0"
  shows "padic_a_inv p f n = (if n=0 then 0 else (- (f n)) mod (p^n))"
proof-
  have "residues (p^n)"
  by (simp add: assms(1) assms(3) prime_gt_1_int residues.intro)  
  then show ?thesis 
    using residue_ring_def padic_a_inv_def residues.res_neg_eq
    by auto 
qed

text\<open>
  We show that \<^const>\<open>padic_set\<close> is closed under additive inverses. Note that we have to treat the
  case of residues at $0$ separately.
\<close>

lemma residue_1_prop:
"\<ominus>\<^bsub>residue_ring 1\<^esub> \<zero>\<^bsub>residue_ring 1\<^esub> =  \<zero>\<^bsub>residue_ring 1\<^esub>"
proof-
  let ?x = "\<zero>\<^bsub>residue_ring 1\<^esub>"
  let ?y = "\<ominus>\<^bsub>residue_ring 1\<^esub> \<zero>\<^bsub>residue_ring 1\<^esub>"
  let ?G = "add_monoid (residue_ring 1)"
  have P0:" ?x \<oplus>\<^bsub>residue_ring 1\<^esub> ?x =  ?x" 
    by (simp add: residue_ring_def) 
  have P1: "?x \<in> carrier (residue_ring 1)" 
    by (simp add: residue_ring_def) 
  have "?x \<in> carrier ?G \<and> ?x \<otimes>\<^bsub>?G\<^esub> ?x = \<one>\<^bsub>?G\<^esub> \<and> ?x \<otimes>\<^bsub>?G\<^esub> ?x = \<one>\<^bsub>?G\<^esub>"
    using P0 P1  by auto 
  then show ?thesis 
    by (simp add: m_inv_def a_inv_def residue_ring_def) 
qed

lemma residue_1_zero:
  "residue 1 n = 0" 
  by (simp add: residue_def) 

lemma padic_a_inv_in_padic_set:
  assumes "f \<in> padic_set p"
  assumes "prime (p::int)"
  shows "(padic_a_inv p f) \<in> padic_set p"
proof(rule padic_set_memI)
  show "\<And>m. padic_a_inv p f m \<in> carrier (residue_ring (p ^ m))"
  proof-
    fix m
    show "padic_a_inv p f m \<in> carrier (residue_ring (p ^ m))"
    proof-
      have P0: "padic_a_inv p f m = \<ominus>\<^bsub>residue_ring (p^m)\<^esub> (f m)" 
        using padic_a_inv_def by simp 
      then show ?thesis 
        by (metis (no_types, lifting) assms(1) assms(2) cring.cring_simprules(3) neq0_conv 
            one_less_power padic_set_res_closed padic_set_zero_res power_0 prime_gt_1_int residue_1_prop
            residue_ring_def residues.cring residues.intro ring.simps(1))
    qed
  qed
  show "\<And>m n. m < n \<Longrightarrow> residue (p ^ m) (padic_a_inv p f n) = padic_a_inv p f m" 
  proof-
    fix m n::nat
    assume "m < n"
    show "residue (p ^ m) (padic_a_inv p f n) = padic_a_inv p f m" 
    proof(cases "m=0")
      case True
      then have 0: "residue (p ^ m) (padic_a_inv p f n) = 0" using residue_1_zero 
        by simp
      have "f m = 0" 
        using assms True padic_set_def residue_ring_def padic_set_zero_res 
        by auto       
      then have 1: "padic_a_inv p f m = 0" using residue_1_prop assms
        by (simp add: True padic_a_inv_def residue_ring_def) 
      then show ?thesis using 0 1
        by simp 
      next
        case False
        have 0: "f n \<in> carrier (residue_ring (p^n)) "
          using assms(1) padic_set_res_closed by auto
        have 1: "padic_a_inv p f n = \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (f n)" using padic_a_inv_def
          by simp 
        have 2: "padic_a_inv p f m = \<ominus>\<^bsub>residue_ring (p^m)\<^esub> (f m)" using  False padic_a_inv_def
          by simp 
        have 3: "residue (p ^ m) \<in> ring_hom (residue_ring (p ^ n)) (residue_ring (p ^ m))" 
          using residue_hom_p False \<open>m < n\<close> assms(2) by auto 
        have 4: " cring (residue_ring (p ^ n))" 
          using \<open>m < n\<close> assms(2) prime_gt_1_int residues.cring residues.intro by auto 
        have 5: " cring (residue_ring (p ^ m))" 
          using False assms(2) prime_gt_1_int residues.cring residues.intro by auto
        have  "ring_hom_cring (residue_ring (p ^ n))  (residue_ring (p ^ m)) (residue (p ^ m))"
          using 3 4 5 UnivPoly.ring_hom_cringI by blast  
        then show ?thesis using 0  1 2 ring_hom_cring.hom_a_inv 
          by (metis \<open>m < n\<close> assms(1) assms(2) less_imp_le_nat padic_set_res_coherent)          
      qed
    qed
  qed

    (**********************************************************************************************)
    subsection\<open>Multiplication\<close>
    (**********************************************************************************************)

definition padic_mult :: "int \<Rightarrow> padic_int \<Rightarrow> padic_int \<Rightarrow> padic_int" 
  where "padic_mult p f g \<equiv> (\<lambda> n. (f n) \<otimes>\<^bsub>(residue_ring (p^n))\<^esub> (g n))"

lemma padic_mult_res: 
"(padic_mult p f g) n = (f n) \<otimes>\<^bsub>(residue_ring (p^n))\<^esub> (g n)"
  by (simp add: padic_mult_def) 

text\<open>Definition of the $p$-adic multiplicative unit:\<close>

definition padic_one :: "int \<Rightarrow> padic_int" where
"padic_one p \<equiv> (\<lambda>n.(if n=0 then 0 else 1))"

lemma padic_one_simp:
  assumes "n >0"
  shows "padic_one p n =  \<one>\<^bsub>residue_ring (p^n)\<^esub>" 
        "padic_one p n = 1"
  apply (simp add: assms padic_one_def residue_ring_def) 
  using assms padic_one_def by auto

lemma padic_one_in_padic_set:
  assumes "prime p"
  shows "padic_one p \<in> padic_set p"
  apply(rule padic_set_memI)
  by(auto simp : assms padic_one_def prime_gt_1_int residue_def residue_ring_def)

lemma padic_simps:
"padic_zero p n = \<zero>\<^bsub>residue_ring (p^n)\<^esub>" 
"padic_a_inv p f n \<equiv> \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (f n)"
"(padic_mult p f g) n = (f n) \<otimes>\<^bsub>(residue_ring (p^n))\<^esub> (g n)"
"(padic_add p f g) n = (f n) \<oplus>\<^bsub>(residue_ring (p^n))\<^esub> (g n)"
"n>0 \<Longrightarrow>padic_one p n =  \<one>\<^bsub>residue_ring (p^n)\<^esub>"
  apply (simp add: padic_zero_simp) 
  apply (simp add: padic_a_inv_simp)
  apply (simp add: padic_mult_def)
  apply (simp add: padic_add_res)  
  using padic_one_simp by auto

lemma residue_1_mult:
  assumes "x \<in> carrier (residue_ring 1)"
  assumes "y \<in> carrier (residue_ring 1)"
  shows "x \<otimes>\<^bsub>residue_ring 1\<^esub> y = 0"
  by (simp add: residue_ring_def)

lemma padic_mult_in_padic_set:
  assumes "f \<in> (padic_set p)"
  assumes "g \<in> (padic_set p)"
  assumes "prime p"
  shows "(padic_mult p f g)\<in> (padic_set p)"
proof(rule padic_set_memI')
  show "\<And>m. padic_mult p f g m \<in> {0..<p ^ m}"
    unfolding padic_mult_def 
    using assms residue_ring_def  
    by (simp add: prime_gt_0_int)
  show "\<And>m n. m < n \<Longrightarrow> padic_mult p f g n mod p ^ m = padic_mult p f g m"
  proof-
      fix m n::nat
      assume A: "m < n"
      then show "padic_mult p f g n mod p ^ m = padic_mult p f g m"
      proof(cases "m=0")
        case True
        then show ?thesis 
          by (metis assms(1) assms(2) mod_by_1 padic_mult_def padic_set_res_closed power_0 residue_1_mult)
      next
        case False       
        have 0:"residue (p ^ m)  \<in> ring_hom (residue_ring (p^n)) (residue_ring (p^m))"
          using A residue_hom_p assms  False by auto  
        have 1:"f n \<in> carrier (residue_ring (p^n))" 
          using assms(1) padic_set_res_closed by auto 
        have 2:"g n \<in> carrier (residue_ring (p^n))" 
          using assms(2) padic_set_res_closed by auto 
        have 3: "residue (p^m) (f n \<otimes>\<^bsub>residue_ring (p^n)\<^esub> g n) 
                    = f m \<otimes>\<^bsub>residue_ring (p^m)\<^esub> g m" 
          using  "0" "1" "2" A assms(1) assms(2) assms(3) less_imp_le of_nat_power padic_set_res_coherent 
            by (simp add: assms(2) ring_hom_mult)
        then show ?thesis
          using ring_hom_mult padic_simps[simp] residue_def
          by auto          
        qed
  qed
qed

section\<open>The $p$-adic Valuation\<close>

text\<open>This section defines the integer-valued $p$-adic valuation. Maps $0$ to $-1$ for now, otherwise is correct. We want the valuation to be integer-valued, but in practice we know it will always be positive. When we extend the valuation from the $p$-adic integers to the $p$-adic field we will have elements of negative valuation. \<close>

definition padic_val :: "int \<Rightarrow>  padic_int \<Rightarrow> int"  where
"padic_val p f \<equiv> if (f = padic_zero p) then -1 else int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"

text\<open>Characterization of $padic\_val$ on nonzero elements\<close>

lemma val_of_nonzero:
  assumes "f \<in> padic_set p"
  assumes "f \<noteq> padic_zero p"
  assumes "prime p"
  shows "f (nat (padic_val p f) + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^((nat (padic_val p f) + 1)))\<^esub>"
        "f (nat (padic_val p f)) =  \<zero>\<^bsub>residue_ring (p^((nat (padic_val p f))))\<^esub>"
        "f (nat (padic_val p f) + 1) \<noteq> 0"
        "f (nat (padic_val p f)) =  0"
proof-
  let ?vf = "padic_val p f"
  have 0: "?vf =int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"
    using assms(2) padic_val_def by auto    
  have 1: "(\<exists> k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"
    proof-
      obtain k where 1: "(f k) \<noteq> (padic_zero p k)"
        using assms(2) by (meson ext) 
      have 2: "k \<noteq> 0" 
      proof
        assume "k=0"
        then have "f k = 0"
          using assms padic_set_zero_res by blast 
        then show False 
          using padic_zero_def 1 by simp 
      qed
        then obtain m where "k = Suc m"
      by (meson lessI less_Suc_eq_0_disj)
    then have "(f (Suc m)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc m))\<^esub>" 
      using "1" padic_zero_simp by simp    
    then show ?thesis 
      by auto
  qed
  then have "(f (Suc (nat ?vf))) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc (nat ?vf)))\<^esub>" 
    using 0 by (metis (mono_tags, lifting) LeastI_ex nat_int) 
  then show C0: "f (nat (padic_val p f) + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^((nat (padic_val p f) + 1)))\<^esub>" 
    using 0 1 by simp
  show C1: "f (nat (padic_val p f)) =  \<zero>\<^bsub>residue_ring (p^((nat (padic_val p f))))\<^esub>"
  proof(cases "(padic_val p f) = 0")
    case True
    then show ?thesis 
      using assms(1) assms(3) padic_set_zero_res residue_ring_def by auto 
  next
    case False 
    have "\<not> f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>residue_ring (p ^ nat (padic_val p f))\<^esub>"
    proof
      assume "f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>residue_ring (p ^ nat (padic_val p f))\<^esub>"
      obtain k where " (Suc k) = (nat (padic_val p f))" using False 
        using "0" gr0_conv_Suc by auto
      then have "?vf  \<noteq> int (LEAST k::nat. (f (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"
        using False by (metis (mono_tags, lifting) Least_le 
          \<open>f (nat (padic_val p f)) \<noteq> \<zero>\<^bsub>residue_ring (p ^ nat (padic_val p f))\<^esub>\<close>
            add_le_same_cancel2 nat_int not_one_le_zero plus_1_eq_Suc)
      then show False  using "0" by blast
    qed    
    then show "f (nat (padic_val p f)) = \<zero>\<^bsub>residue_ring (p ^ nat (padic_val p f))\<^esub>" by auto
  qed
  show  "f (nat (padic_val p f) + 1) \<noteq> 0"
    using C0  residue_ring_def 
    by auto 
  show  "f (nat (padic_val p f)) =  0"
    by (simp add: C1 residue_ring_def) 
qed

text\<open>If $x \mod p^{n+1} \neq 0$, then $n \geq val x$.\<close>

lemma below_val_zero:
  assumes "prime p"
  assumes "x \<in> (padic_set p)"
  assumes "x (Suc n) \<noteq>  \<zero>\<^bsub>residue_ring (p^(Suc n))\<^esub>"
  shows  "int n \<ge> (padic_val p x )"
proof(cases "x = padic_zero p")
  case True
  then show  ?thesis  
    using assms(3) padic_zero_simp by blast 
next
  case False
  then have "padic_val p x = int (LEAST k::nat. x (Suc k) \<noteq> \<zero>\<^bsub>residue_ring (p ^ Suc k)\<^esub>)"
    using padic_val_def by auto  
  then show "of_nat n \<ge> (padic_val p x )"
    by (metis (mono_tags, lifting) Least_le assms(3) nat_int nat_le_iff)
qed

text\<open>If $n < val x$ then $x \mod p^n = 0$:\<close>

lemma  zero_below_val:
  assumes "prime p"
  assumes "x \<in> padic_set p"
  assumes "n \<le> padic_val p x"
  shows  "x n =  \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
         "x n = 0"
proof-
 show "x n = \<zero>\<^bsub>residue_ring (p ^ n)\<^esub>"
 proof(cases "n=0")
  case True
  then have  "x 0 \<in>carrier (residue_ring (p^0))" 
    using assms(2) padic_set_res_closed  by blast
  then show ?thesis 
    by (simp add: True residue_ring_def) 
  next
    case False 
    show ?thesis 
    proof(cases "x = padic_zero p")
      case True 
      then show ?thesis 
        by (simp add: padic_zero_simp)
    next
      case F: False
      then have A: "padic_val p x = int (LEAST k::nat. (x (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)" 
        using padic_val_def by auto
      have "\<not> (x n) \<noteq> \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
      proof
        assume "(x n) \<noteq> \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
        obtain k where "n = Suc k" 
          using False old.nat.exhaust by auto
        then have "k \<ge> padic_val p x" using A 
          using \<open>x n \<noteq> \<zero>\<^bsub>residue_ring (p ^ n)\<^esub>\<close> assms(1) assms(2) below_val_zero by blast          
        then have "n > padic_val p x" 
          using \<open>n = Suc k\<close> by linarith
        then show False using assms(3) 
          by linarith
      qed
      then show ?thesis 
        by simp
    qed
  qed
  show "x n = 0"
    by (simp add: \<open>x n = \<zero>\<^bsub>residue_ring (p ^ n)\<^esub>\<close> residue_ring_def) 
qed

text\<open>Zero is the only element with valuation equal to $-1$:\<close>

lemma val_zero:
 assumes P: "f \<in> (padic_set p)"   
 shows "padic_val p f = -1 \<longleftrightarrow>  (f = (padic_zero p))"
proof
  show "padic_val p f = -1 \<Longrightarrow>  (f = (padic_zero p))"
  proof
    assume A:"padic_val p f = -1" 
    fix k
    show "f k = padic_zero p k" 
    proof-
      have  "f k \<noteq> padic_zero p k \<Longrightarrow> False"
      proof-
        assume A0: " f k \<noteq> padic_zero p k"
        have False
        proof-
          have "f 0 \<in> carrier (residue_ring 1)" using P padic_set_def 
            by (metis (no_types, lifting) mem_Collect_eq power_0) 
          then have "f 0 = \<zero>\<^bsub>residue_ring (p^0)\<^esub>"  
            by (simp add: residue_ring_def) 
          then have "k>0" 
            using A0 gr0I padic_zero_def 
            by (metis padic_zero_simp)    
          then have "(LEAST k. 0 < k \<and> f (Suc k) \<noteq> padic_zero p (Suc k)) \<ge>0 " 
            by simp
          then have "padic_val p f \<ge>0" 
            using A0 padic_val_def by auto 
          then show ?thesis  using A0 by (simp add: A)  
        qed
        then show ?thesis by blast
      qed
      then show ?thesis 
        by blast
    qed
  qed
  assume B: "f = padic_zero p"
  then show "padic_val p f = -1" 
  using padic_val_def by simp 
qed

text\<open>
  The valuation turns multiplication into integer addition on nonzero elements. Note that this i
  the first instance where we need to explicity use the fact that $p$ is a prime.
\<close>

lemma val_prod:
  assumes "prime p"
  assumes "f \<in> (padic_set p)" 
  assumes "g \<in> (padic_set p)"
  assumes "f \<noteq> padic_zero p"
  assumes "g \<noteq> padic_zero p"
  shows "padic_val p (padic_mult p f g) = padic_val p f + padic_val p g"
proof-
  let ?vp = "padic_val p (padic_mult p f g)"
  let ?vf = "padic_val p f"
  let ?vg = "padic_val p g"
  have 0: "f (nat ?vf + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^(nat ?vf + 1))\<^esub>" 
    using assms(2) assms(4) val_of_nonzero  assms(1) by blast 
  have 1: "g (nat ?vg + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^(nat ?vg + 1))\<^esub>" 
    using assms(3) assms(5) val_of_nonzero assms(1) by blast 
  have 2: "f (nat ?vf) =  \<zero>\<^bsub>residue_ring (p^(nat ?vf))\<^esub>" 
    using assms(1) assms(2) assms(4) val_of_nonzero(2) by blast 
  have 3: "g (nat ?vg) =  \<zero>\<^bsub>residue_ring (p^(nat ?vg))\<^esub>" 
    using assms(1) assms(3) assms(5) val_of_nonzero(2) by blast
  let ?nm = "((padic_mult p f g) (Suc (nat (?vf + ?vg))))"    
  let ?n = "(f (Suc (nat (?vf + ?vg))))"    
  let ?m = "(g (Suc (nat (?vf + ?vg))))"  
  have A: "?nm = ?n \<otimes>\<^bsub>residue_ring (p^((Suc (nat (?vf + ?vg))))) \<^esub> ?m" 
    using padic_mult_def  by simp 
  have 5: "f (nat ?vf + 1) = residue (p^(nat ?vf + 1)) ?n" 
  proof-
    have "(Suc (nat (?vf + ?vg))) \<ge> (nat ?vf + 1)" 
      by (simp add: assms(5) padic_val_def)
    then have "f (nat ?vf + 1) =  residue (p^(nat ?vf + 1)) (f (Suc (nat (?vf + ?vg))))" 
      using assms(1) assms(2) padic_set_res_coherent by presburger
    then show ?thesis by auto 
  qed
  have 6: "f (nat ?vf) = residue (p^(nat ?vf)) ?n" 
   using add.commute assms(1) assms(2) assms(5) int_nat_eq nat_int 
        nat_le_iff not_less_eq_eq padic_set_res_coherent padic_val_def plus_1_eq_Suc  by auto 
  have 7: "g (nat ?vg + 1) = residue (p^(nat ?vg + 1)) ?m"  
  proof-
    have "(Suc (nat (?vf + ?vg))) \<ge> (nat ?vg + 1)" 
      by (simp add: assms(4) padic_val_def)
    then have "g (nat ?vg + 1) =  residue (p^(nat ?vg + 1)) (g (Suc (nat (?vf + ?vg))))" 
      using assms(1) assms(3) padic_set_res_coherent by presburger
    then show ?thesis by auto 
  qed
  have 8: "g (nat ?vg) = residue (p^(nat ?vg)) ?m"
  proof-
    have "(Suc (nat (?vf + ?vg))) \<ge> (nat ?vg)" 
      by (simp add: assms(4) padic_val_def)
    then have "g (nat ?vg) =  residue (p^(nat ?vg)) (g (Suc (nat (?vf + ?vg))))" 
      using assms(1) assms(3) padic_set_res_coherent by presburger
    then show ?thesis by auto 
  qed 
  have 9: "f (nat ?vf) = 0" 
    by (simp add: "2" residue_ring_def) 
  have 10: "g (nat ?vg) = 0" 
    by (simp add: "3" residue_ring_def) 
  have 11: "f (nat ?vf + 1) \<noteq> 0" 
    using "0" residue_ring_def by auto 
  have 12: "g (nat ?vg + 1) \<noteq>0" 
    using "1" residue_ring_def by auto 
  have 13:"\<exists>i. ?n = i*p^(nat ?vf) \<and> \<not> p dvd (nat i)" 
  proof-
    have  "residue (p^(nat ?vf)) (?n) = f (nat ?vf)" 
      by (simp add: "6") 
    then have P0: "residue (p^(nat ?vf)) (?n) = 0" 
      using "9" by linarith 
    have "residue (p^(nat ?vf + 1)) (?n) = f (nat ?vf + 1)" 
      using "5" by linarith 
    then have P1: "residue (p^(nat ?vf + 1)) (?n) \<noteq> 0"
      using "11" by linarith 
    have P2: "?n mod (p^(nat ?vf)) = 0" 
      using P0 residue_def by auto 
    have P3: "?n mod (p^(nat ?vf + 1)) \<noteq>  0" 
      using P1 residue_def by auto 
    have "p^(nat ?vf) dvd ?n" 
      using P2 by auto 
    then obtain i where A0:"?n = i*(p^(nat ?vf))" 
      by fastforce 
    have "?n \<in> carrier (residue_ring (p^(Suc (nat (?vf + ?vg)))))" 
      using assms(2) padic_set_res_closed by blast 
    then have "?n \<ge>0" 
      by (simp add: residue_ring_def) 
    then have NN:"i \<ge> 0" 
    proof-
      have S0:"?n \<ge>0" 
        using \<open>0 \<le> f (Suc (nat (padic_val p f + padic_val p g)))\<close> by blast
      have S1:"(p^(nat ?vf)) > 0" 
        using assms(1) prime_gt_0_int zero_less_power by blast        
      have "\<not> i<0"
      proof
        assume "i < 0"
        then have "?n < 0" 
          using S1 A0 by (metis mult.commute times_int_code(1) zmult_zless_mono2)
        then show False 
          using S0  by linarith
      qed
      then show ?thesis by auto 
    qed
    have A1: "\<not> p dvd (nat i)"
    proof
      assume "p dvd nat i"
      then obtain j where "nat i = j*p" 
        by fastforce 
      then have "?n = j*p*(p^(nat ?vf))" using A0 NN 
        by simp        
      then show False 
        using P3 by auto 
    qed
    then show ?thesis 
      using A0 by blast      
  qed
  have 14:"\<exists> i. ?m = i*p^(nat ?vg) \<and> \<not> p dvd (nat i)"
  proof-
    have  "residue (p^(nat ?vg)) (?m) = g (nat ?vg)" 
      by (simp add: "8") 
    then have P0: "residue (p^(nat ?vg)) (?m) = 0" 
      using "10" by linarith 
    have "residue (p^(nat ?vg + 1)) (?m) = g (nat ?vg + 1)" 
      using "7" by auto 
    then have P1: "residue (p^(nat ?vg + 1)) (?m) \<noteq> 0"
      using "12" by linarith 
    have P2: "?m mod (p^(nat ?vg)) = 0"
      using P0 residue_def by auto 
    have P3: "?m mod (p^(nat ?vg + 1)) \<noteq>  0" 
      using P1 residue_def by auto 
    have "p^(nat ?vg) dvd ?m" 
      using P2 by auto 
    then obtain i where A0:"?m = i*(p^(nat ?vg))" 
      by fastforce 
    have "?m \<in> carrier (residue_ring (p^(Suc (nat (?vf + ?vg)))))" 
      using assms(3) padic_set_res_closed by blast 
    then have S0: "?m \<ge>0" 
      by (simp add: residue_ring_def) 
    then have NN:"i \<ge> 0" 
      using 0 assms(1) prime_gt_0_int[of p] zero_le_mult_iff zero_less_power[of p]
      by (metis A0 linorder_not_less) 
    have A1: "\<not> p dvd (nat i)"
    proof
      assume "p dvd nat i"
      then obtain j where "nat i = j*p" 
        by fastforce 
      then have "?m = j*p*(p^(nat ?vg))" using A0 NN 
        by (metis int_nat_eq ) 
      then show False 
        using P3 by auto 
    qed
    then show ?thesis 
      by (metis (no_types, lifting) A0) 
  qed
  obtain i where I:"?n = i*p^(nat ?vf) \<and> \<not> p dvd (nat i)" 
    using "13" by blast 
  obtain j where J:"?m = j*p^(nat ?vg) \<and> \<not> p dvd (nat j)"
    using "14" by blast 
  let ?i = "(p^(Suc (nat (?vf + ?vg))))"
  have P:"?nm mod ?i = ?n*?m mod ?i"
  proof-
    have P1:"?nm = (?n \<otimes>\<^bsub>residue_ring ?i \<^esub> ?m)"
      using A by simp
    have P2:"(?n \<otimes>\<^bsub>residue_ring ?i \<^esub> ?m) = (residue ?i (?n)) \<otimes>\<^bsub>residue_ring ?i\<^esub>   (residue ?i (?m))" 
      using assms(1) assms(2) assms(3) padic_set_res_closed prime_ge_0_int residue_id by presburger      
    then have P3:"(?n \<otimes>\<^bsub>residue_ring ?i \<^esub> ?m) = (residue ?i (?n*?m))" 
      by (metis monoid.simps(1) residue_def residue_ring_def) 
    then show ?thesis 
      by (simp add: P1 residue_def) 
  qed
  then have 15: "?nm mod ?i =  i*j*p^((nat ?vf) +(nat ?vg)) mod ?i"
    by (simp add: I J mult.assoc mult.left_commute power_add)   
  have 16: "\<not> p dvd (i*j)" using 13 14
    using I J assms(1) prime_dvd_mult_iff 
    by (metis dvd_0_right int_nat_eq)     
  have 17: "((nat ?vf) +(nat ?vg)) < (Suc (nat (?vf + ?vg)))" 
    by (simp add: assms(4) assms(5) nat_add_distrib padic_val_def) 
  have 18:"?nm mod ?i \<noteq>0"
  proof-
    have A0:"\<not>  p^((Suc (nat (?vf + ?vg)))) dvd p^((nat ?vf) +(nat ?vg)) " 
      using 17 
      by (metis "16" assms(1) dvd_power_iff dvd_trans less_int_code(1) linorder_not_less one_dvd prime_gt_0_int)
    then have A1: "p^((nat ?vf) +(nat ?vg)) mod ?i \<noteq> 0" 
      using dvd_eq_mod_eq_0 
      by auto      
    have "\<not>  p^((Suc (nat (?vf + ?vg)))) dvd i*j*p^((nat ?vf) +(nat ?vg)) "
      using 16 A0 assms(1) assms(4) assms(5) nat_int_add padic_val_def by auto      
    then show ?thesis 
      using "15" by force
  qed
  have 19: "(?nm mod ?i ) mod (p^(nat ?vf + nat ?vg)) = i*j*p^((nat ?vf) +(nat ?vg)) mod (p^(nat ?vf + nat ?vg))"
    using 15 by (simp add: assms(4) assms(5) nat_add_distrib padic_val_def)  
  have 20: "?nm mod (p^(nat ?vf + nat ?vg)) = 0"
  proof-
    have "(?nm mod ?i ) mod (p^(nat ?vf + nat ?vg)) = 0"
      using 19 
      by simp
    then show ?thesis 
      using "17" assms(1) int_nat_eq mod_mod_cancel[of "p^(nat ?vf + nat ?vg)" ?i] 
           mod_pos_pos_trivial
      by (metis le_imp_power_dvd less_imp_le_nat)
  qed
  have 21: "(padic_mult p f g) \<noteq> padic_zero p"
  proof
    assume "(padic_mult p f g) =  padic_zero p"
    then have "(padic_mult p f g) (Suc (nat (padic_val p f + padic_val p g))) =  padic_zero p (Suc (nat (padic_val p f + padic_val p g)))"
      by simp
    then have "?nm  = (padic_zero p (Suc (nat (padic_val p f + padic_val p g))))"
      by blast 
    then have "?nm = 0"  
      by (simp add: padic_zero_def)  
    then show False
      using "18" by auto
  qed
  have 22: "(padic_mult p f g)\<in> (padic_set p)" 
    using assms(1) assms(2) assms(3) padic_mult_in_padic_set by blast 
  have 23: "\<And> j. j < Suc (nat (padic_val p f + padic_val p g)) \<Longrightarrow> (padic_mult p f g) j = \<zero>\<^bsub>residue_ring (p^j)\<^esub>"
  proof-
    fix k
    let ?j = "Suc (nat (padic_val p f + padic_val p g))"
    assume P: "k < ?j"
    show "(padic_mult p f g) k = \<zero>\<^bsub>residue_ring (p^k)\<^esub>" 
      proof-
      have P0: "(padic_mult p f g) (nat ?vf + nat ?vg) = \<zero>\<^bsub>residue_ring (p^(nat ?vf + nat ?vg))\<^esub>"
        proof-
          let ?k = "(nat ?vf + nat ?vg)"
          have "((padic_mult p f g) ?k) = residue (p^?k) ((padic_mult p f g) ?k) " 
            using P 22 padic_set_res_coherent by (simp add: assms(1) prime_gt_0_nat)
          then have "((padic_mult p f g) ?k) = residue (p^?k) ?nm" 
            using "17" "22" assms(1) padic_set_res_coherent by fastforce 
          then have "((padic_mult p f g) ?k) = residue (p^?k) ?nm" 
            by (simp add: residue_def)
          then have "((padic_mult p f g) ?k) = residue (p^?k) 0"  
            using "20" residue_def by auto 
          then show ?thesis 
            by (simp add: residue_def residue_ring_def) 
        qed
      then show ?thesis 
      proof(cases "k = (nat ?vf + nat ?vg)")
      case True then show ?thesis  
        using P0 by blast
    next
      case B: False
      then show ?thesis 
      proof(cases "k=0")
        case True
        then show ?thesis 
          using "22" assms(1) padic_set_zero_res residue_ring_def by auto 
      next
        case C: False 
        then have "((padic_mult p f g) k) = residue (p^k) ((padic_mult p f g) (nat ?vf + nat ?vg)) " 
          using B P 22 padic_set_res_coherent by (simp add: assms(1) assms(4) assms(5) padic_val_def prime_gt_0_nat) 
        then have S: "((padic_mult p f g) k) = residue (p^k) \<zero>\<^bsub>residue_ring (p^((nat ?vf + nat ?vg)))\<^esub>" 
          by (simp add: P0)
        have "residue (p^k) \<in> ring_hom (residue_ring (p^((nat ?vf + nat ?vg)))) (residue_ring (p^k))"
          using B P C residue_hom_p 
          using assms(1) assms(4) assms(5) less_Suc0 nat_int not_less_eq of_nat_power padic_val_def prime_nat_int_transfer by auto 
        then show ?thesis using S 
          using P0 padic_zero_def padic_zero_simp residue_def by auto 
      qed
    qed
  qed
qed
  have 24: "(padic_mult p f g) (Suc (nat ?vf + nat ?vg)) \<noteq> \<zero>\<^bsub>residue_ring ((p ^ Suc (nat (padic_val p f + padic_val p g))))\<^esub>" 
    by (metis (no_types, lifting) "18" A P assms(4) assms(5) monoid.simps(1) nat_int nat_int_add padic_val_def residue_ring_def ring.simps(1)) 
  have 25: "padic_val p (padic_mult p f g) = int (LEAST k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)"
    using padic_val_def 21 by auto 
  have 26:"(nat (padic_val p f + padic_val p g)) \<in> {k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>}" using 24 
    using "18" assms(1) prime_gt_0_nat 
    by (metis (mono_tags, lifting) mem_Collect_eq mod_0 residue_ring_def ring.simps(1))
  have 27: "\<And> j. j < (nat (padic_val p f + padic_val p g)) \<Longrightarrow>
     j \<notin> {k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>}" 
    by (simp add: "23") 
  have "(nat (padic_val p f + padic_val p g)) = (LEAST k::nat. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>) "
  proof-
    obtain P where C0: "P= (\<lambda> k. ((padic_mult p f g) (Suc k)) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc k))\<^esub>)" 
      by simp
    obtain x where C1: "x = (nat (padic_val p f + padic_val p g))" 
      by blast
    have C2: "P x" 
      using "26" C0 C1  by blast
    have C3:"\<And> j. j< x \<Longrightarrow> \<not> P j" 
      using C0 C1 by (simp add: "23")
    have C4: "\<And> j. P j \<Longrightarrow> x \<le>j" 
      using C3 le_less_linear by blast
    have "x = (LEAST k. P k)" 
      using C2 C4 Least_equality by auto 
    then show ?thesis using C0 C1 by auto
  qed
  then have "padic_val p (padic_mult p f g) = (nat (padic_val p f + padic_val p g))" 
    using "25" by linarith
  then show ?thesis 
    by (simp add: assms(4) assms(5) padic_val_def)

qed

section\<open>Defining the Ring of $p$-adic Integers:\<close>

definition padic_int :: "int \<Rightarrow> padic_int ring"
  where "padic_int p \<equiv> \<lparr>carrier = (padic_set p),
         Group.monoid.mult = (padic_mult p), one = (padic_one p), 
          zero = (padic_zero p), add = (padic_add p)\<rparr>"

lemma padic_int_simps:
 "\<one>\<^bsub>padic_int p\<^esub> = padic_one p"
 "\<zero>\<^bsub>padic_int p\<^esub> = padic_zero p"
 "(\<oplus>\<^bsub>padic_int p\<^esub>) = padic_add p"
 "(\<otimes>\<^bsub>padic_int p\<^esub>) = padic_mult p"
 "carrier (padic_int p) = padic_set p"
  unfolding padic_int_def by auto 

lemma residues_n:
  assumes "n \<noteq> 0"
  assumes "prime p"
  shows "residues (p^n)" 
proof
  have "p > 1" using assms(2) 
    using prime_gt_1_int by auto
  then show " 1 < p ^ n "  
    using assms(1) by auto
qed

text\<open>$p$-adic multiplication is associative\<close>

lemma padic_mult_assoc:
assumes "prime p"
shows  "\<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow> 
       z \<in> carrier (padic_int p) \<Longrightarrow>
       x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
proof-
  fix x y z
  assume Ax: " x \<in> carrier (padic_int p)"
  assume Ay: " y \<in> carrier (padic_int p)"
  assume Az: " z \<in> carrier (padic_int p)"
  show "x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
  proof
    fix n
    show "((x \<otimes>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z) n = (x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)) n"
    proof(cases "n=0") 
      case True
      then show ?thesis using padic_int_simps
        by (metis Ax Ay Az assms padic_mult_in_padic_set padic_set_zero_res)        
    next
      case False
      then have "residues (p^n)" 
        by (simp add: assms residues_n)
      then show ?thesis 
        using residues.cring padic_set_res_closed padic_mult_in_padic_set Ax Ay Az padic_mult_res
        by (simp add: cring.cring_simprules(11) padic_int_def)        
    qed
  qed
qed

text\<open>The $p$-adic integers are closed under addition:\<close>

lemma padic_add_closed:
  assumes "prime p"
  shows  "\<And>x y.
         x \<in> carrier (padic_int p) \<Longrightarrow>
         y \<in> carrier (padic_int p) \<Longrightarrow>
         x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
proof
  fix x::"padic_int"
  fix y::"padic_int"
  assume Px: "x \<in>carrier (padic_int p) "
  assume Py: "y \<in>carrier (padic_int p)"
  show "x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
  proof-
    let ?f = "x \<oplus>\<^bsub>(padic_int p)\<^esub> y"       
    have 0: "(\<forall>(m::nat). (?f m) \<in> (carrier (residue_ring (p^m))))"
    proof fix m
      have A1 : "?f m = (x m) \<oplus>\<^bsub>(residue_ring (p^m))\<^esub> (y m)"
        by (simp add: padic_int_def padic_add_def)  
      have A2: "(x m) \<in>(carrier (residue_ring (p^m)))" 
        using Px by (simp add: padic_int_def padic_set_def) 
      have A3: "(y m) \<in>(carrier (residue_ring (p^m)))" 
        using Py by (simp add: padic_int_def padic_set_def) 
      then show "(?f m) \<in> (carrier (residue_ring (p^m)))" 
        using A1 assms of_nat_0_less_iff prime_gt_0_nat residue_ring_def by force  
    qed
    have 1: "(\<forall>(n::nat) (m::nat). (n > m \<longrightarrow> (residue (p^m) (?f n) = (?f m))))" 
    proof 
      fix n::nat
      show "(\<forall>(m::nat). (n > m \<longrightarrow> (residue (p^m) (?f n) = (?f m))))" 
      proof
        fix m::nat
        show "(n > m \<longrightarrow> (residue (p^m) (?f n) = (?f m)))"
        proof
          assume A: "m < n"
          show "(residue (p^m) (?f n) = (?f m))"
          proof(cases "m = 0")
            case True 
            then have A0: "(residue (p^m) (?f n)) = 0" 
              by (simp add: residue_1_zero) 
            have A1: "?f m = 0" using True 
              by (simp add: padic_add_res padic_int_simps(3) residue_ring_def)              
            then show ?thesis 
              using A0 by linarith 
          next
            case False
            then have  "m \<noteq>0" using A by linarith
            have D: "p^n mod p^m = 0" using A 
              by (simp add: le_imp_power_dvd)
            let ?LHS = "residue (p ^ m) ((x \<oplus>\<^bsub>padic_int p\<^esub> y) n)"
            have A0: "?LHS = residue (p ^ m) ((x n)\<oplus>\<^bsub>residue_ring (p^n)\<^esub>( y n))" 
              by (simp add: padic_int_def padic_add_def)  
            have "residue (p^m) \<in> ring_hom (residue_ring ((p^n))) (residue_ring ((p^m)))"
              using A False assms residue_hom_p by auto 
            then have "residue (p ^ m) ((x n)\<oplus>\<^bsub>residue_ring (p^n)\<^esub>( y n)) = (residue (p ^ m) (x n))\<oplus>\<^bsub>residue_ring (p^m)\<^esub>((residue (p ^ m) (y n)))"  
              by (metis (no_types, lifting) padic_int_simps(5) Px Py mem_Collect_eq padic_set_def ring_hom_add) 
            then have "?LHS =(residue (p ^ m) (x n))\<oplus>\<^bsub>residue_ring (p^m)\<^esub>((residue (p ^ m) (y n)))" 
              using A0 by force 
            then show ?thesis
              using A Px Py padic_set_def by (simp add: padic_int_def padic_add_def) 
          qed
        qed
      qed
    qed
    then show ?thesis
      using "0" padic_set_memI padic_int_simps by auto 
  qed
  then have "  x \<oplus>\<^bsub>padic_int p\<^esub> y \<in> (padic_set p)" 
    by(simp add:  padic_int_def)
  then show "carrier (padic_int p) \<subseteq> carrier (padic_int p)" 
    by blast  
qed

text\<open>$p$-adic addition is associative:\<close>

lemma padic_add_assoc:
assumes "prime p"
shows  " \<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow> z \<in> carrier (padic_int p)
       \<Longrightarrow> x \<oplus>\<^bsub>padic_int p\<^esub> y \<oplus>\<^bsub>padic_int p\<^esub> z = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
proof-
  fix x y z
  assume Ax: "x \<in> carrier (padic_int p)"
  assume Ay: "y \<in> carrier (padic_int p)"
  assume Az: "z \<in> carrier (padic_int p)"
  show " (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
  proof
    fix n
    show "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = (x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)) n "
    proof-
      have Ex: "(x n) \<in> carrier (residue_ring (p^n))" 
        using Ax padic_set_def padic_int_simps by auto 
      have Ey: "(y n) \<in> carrier (residue_ring (p^n))" 
        using Ay padic_set_def padic_int_simps by auto 
      have Ez: "(z n) \<in> carrier (residue_ring (p^n))" 
        using Az padic_set_def  padic_int_simps by auto 
      let ?x = "(x n)"
      let ?y = "(y n)"
      let ?z = "(z n)"
      have P1: "(?x \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ?y) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ?z = (x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
      proof(cases "n = 0")
        case True
        then show ?thesis 
          by (simp add: residue_ring_def)
      next
        case False
        then have "residues (p^n)" 
          by (simp add: assms residues_n)
        then show ?thesis 
          using Ex Ey Ez cring.cring_simprules(7) padic_add_res residues.cring  padic_int_simps 
          by fastforce
      qed
      have " ((y n)) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n =((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
        using padic_add_def padic_int_simps by simp 
      then have P0: "(x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n) = ((x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n))"
        using padic_add_def  padic_int_simps by simp 
      have "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = ((x  \<oplus>\<^bsub>padic_int p\<^esub> y) n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n"
        using padic_add_def padic_int_simps by simp
      then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n =((x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> (y n)) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n"
        using padic_add_def padic_int_simps by simp 
      then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n =((x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> z n))"
        using Ex Ey Ez P1 P0  by linarith 
      then have  "((x \<oplus>\<^bsub>padic_int p\<^esub> y) \<oplus>\<^bsub>padic_int p\<^esub> z) n = (x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> ((y \<oplus>\<^bsub>padic_int p\<^esub> z) n)"
        using P0 by linarith 
      then show ?thesis by (simp add:  padic_int_def padic_add_def) 
    qed
  qed
qed

text\<open>$p$-adic addition is commutative:\<close>

lemma padic_add_comm:
  assumes "prime p"
  shows " \<And>x y. 
          x \<in> carrier (padic_int p) \<Longrightarrow> 
          y \<in> carrier (padic_int p) \<Longrightarrow> 
          x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
proof-
  fix x y
  assume Ax: "x \<in> carrier (padic_int p)" assume Ay:"y \<in> carrier (padic_int p)"
  show "x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
  proof fix n
    show "(x \<oplus>\<^bsub>padic_int p\<^esub> y) n = (y \<oplus>\<^bsub>padic_int p\<^esub> x) n " 
    proof(cases "n=0")
      case True
      then show ?thesis 
        by (metis Ax Ay assms padic_add_def padic_set_zero_res padic_int_simps(3,5)) 
    next
      case False
      have LHS0: "(x \<oplus>\<^bsub>padic_int p\<^esub> y) n = (x n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> (y n)" 
        by (simp add:  padic_int_simps padic_add_res) 
      have RHS0: "(y \<oplus>\<^bsub>padic_int p\<^esub> x) n = (y n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> (x n)" 
        by (simp add:  padic_int_simps padic_add_res) 
      have Ex: "(x n) \<in> carrier (residue_ring (p^n))" 
        using Ax padic_set_res_closed  padic_int_simps by auto 
      have Ey: "(y n) \<in> carrier (residue_ring (p^n))" 
        using Ay padic_set_res_closed  padic_int_simps by auto 
      have LHS1: "(x \<oplus>\<^bsub>padic_int p\<^esub> y) n = ((x n) +(y n)) mod (p^n)"
        using LHS0 residue_ring_def by simp
      have RHS1: "(y \<oplus>\<^bsub>padic_int p\<^esub> x) n = ((y n) +(x n)) mod (p^n)"
        using RHS0 residue_ring_def by simp
      then show ?thesis using LHS1 RHS1 by presburger 
    qed
  qed
qed

text\<open>$padic\_zero$ is an additive identity:\<close>

lemma padic_add_zero:
assumes "prime p"
shows "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x"
proof-
  fix x
  assume Ax: "x \<in> carrier (padic_int p)"
  show " \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x " 
  proof fix n
    have A: "(padic_zero p) n = 0" 
      by (simp add: padic_zero_def) 
    have "((padic_zero p) \<oplus>\<^bsub>padic_int p\<^esub> x) n = x n" 
      using Ax padic_int_simps(5) padic_set_res_closed residue_ring_def 
      by(auto simp add: padic_zero_def padic_int_simps padic_add_res residue_ring_def)
    then show "(\<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x) n = x n" 
      by (simp add: padic_int_def)      
  qed
qed

text\<open>Closure under additive inverses:\<close>

lemma padic_add_inv:
assumes "prime p"
shows "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow>
           \<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
proof-
  fix x
  assume Ax: " x \<in> carrier (padic_int p)"
  show "\<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
    proof
      let ?y = "(padic_a_inv p) x"
      show "?y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
      proof 
        fix n
        show  "(?y \<oplus>\<^bsub>padic_int p\<^esub> x) n = \<zero>\<^bsub>padic_int p\<^esub> n" 
        proof(cases "n=0")
          case True
          then show ?thesis 
            using Ax assms padic_add_closed padic_set_zero_res 
              padic_a_inv_in_padic_set padic_zero_def padic_int_simps by auto 
        next
          case False 
          have C: "(x n) \<in> carrier (residue_ring (p^n))" 
            using Ax padic_set_res_closed padic_int_simps by auto
          have R: "residues (p^n)" 
            using False  by (simp add: assms residues_n)
          have "(?y \<oplus>\<^bsub>padic_int p\<^esub> x) n = (?y n) \<oplus>\<^bsub>residue_ring (p^n)\<^esub> x n" 
            by (simp add: padic_int_def padic_add_res)
          then have "(?y \<oplus>\<^bsub>padic_int p\<^esub> x) n = 0"
            using C R residue_ring_def[simp] residues.cring 
            by (metis (no_types, lifting) cring.cring_simprules(9) padic_a_inv_def residues.zero_cong)            
          then show ?thesis 
            by (simp add: padic_int_def padic_zero_def)
        qed
      qed
    then show "padic_a_inv p x \<in> carrier (padic_int p)" 
      using padic_a_inv_in_padic_set padic_int_simps
            Ax assms prime_gt_0_nat by auto 
  qed
qed

text\<open>The ring of padic integers forms an abelian group under addition:\<close>

lemma padic_is_abelian_group:
assumes "prime p"
shows "abelian_group (padic_int p)"
  proof (rule abelian_groupI)
    show 0: "\<And>x y. x \<in> carrier (padic_int p) \<Longrightarrow>
                y \<in> carrier (padic_int p) \<Longrightarrow> 
                x \<oplus>\<^bsub>(padic_int p)\<^esub> y \<in> carrier (padic_int p)"
      using padic_add_closed  by (simp add: assms)
    show zero: "\<zero>\<^bsub>padic_int p\<^esub> \<in> carrier (padic_int p)" 
      by (metis "0" assms padic_add_inv padic_int_simps(5) padic_one_in_padic_set)      
    show add_assoc: " \<And>x y z.
                      x \<in> carrier (padic_int p) \<Longrightarrow>
                      y \<in> carrier (padic_int p) \<Longrightarrow> 
                      z \<in> carrier (padic_int p) \<Longrightarrow> 
                             x \<oplus>\<^bsub>padic_int p\<^esub> y \<oplus>\<^bsub>padic_int p\<^esub> z 
                           = x \<oplus>\<^bsub>padic_int p\<^esub> (y \<oplus>\<^bsub>padic_int p\<^esub> z)"
      using assms padic_add_assoc by auto
    show comm: " \<And>x y. 
                      x \<in> carrier (padic_int p) \<Longrightarrow>
                      y \<in> carrier (padic_int p) \<Longrightarrow> 
                      x \<oplus>\<^bsub>padic_int p\<^esub> y = y \<oplus>\<^bsub>padic_int p\<^esub> x"
      using assms padic_add_comm by blast
    show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<zero>\<^bsub>padic_int p\<^esub> \<oplus>\<^bsub>padic_int p\<^esub> x = x"
      using assms padic_add_zero by blast
    show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> 
          \<exists>y\<in>carrier (padic_int p). y \<oplus>\<^bsub>padic_int p\<^esub> x = \<zero>\<^bsub>padic_int p\<^esub>"
      using assms padic_add_inv by blast
  qed

text\<open>One is a multiplicative identity:\<close>

lemma padic_one_id:
assumes "prime p"
assumes "x \<in> carrier (padic_int p)"
shows  "\<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x = x"
proof
  fix n
  show "(\<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x) n = x n "
  proof(cases "n=0")
    case True
    then show ?thesis 
      by (metis padic_int_simps(1,4,5) assms(1) assms(2) padic_mult_in_padic_set padic_one_in_padic_set padic_set_zero_res) 
  next
    case False
    then have "residues (p^n)" 
      by (simp add: assms(1) residues_n)
    then show ?thesis 
      using False assms(2) cring.cring_simprules(12) padic_int_simps
        padic_mult_res padic_one_simp padic_set_res_closed residues.cring by fastforce
  qed
qed

text\<open>$p$-adic multiplication is commutative:\<close>

lemma padic_mult_comm:
assumes "prime p"
assumes "x \<in> carrier (padic_int p)"
assumes "y \<in> carrier (padic_int p)"
shows "x \<otimes>\<^bsub>padic_int p\<^esub> y = y \<otimes>\<^bsub>padic_int p\<^esub> x"
proof
  fix n
  have Ax: "(x n) \<in> carrier (residue_ring (p^n))" 
    using padic_set_def assms(2) padic_int_simps by auto
  have Ay: "(y n) \<in>carrier (residue_ring (p^n))"
    using padic_set_def assms(3) padic_set_res_closed padic_int_simps 
    by blast    
  show "(x \<otimes>\<^bsub>padic_int p\<^esub> y) n = (y \<otimes>\<^bsub>padic_int p\<^esub> x) n"
  proof(cases "n=0")
    case True
    then show ?thesis 
      by (metis padic_int_simps(4,5) assms(1) assms(2) assms(3) padic_set_zero_res padic_simps(3)) 
  next
    case False
    have LHS0: "(x \<otimes>\<^bsub>padic_int p\<^esub> y) n = (x n) \<otimes>\<^bsub>residue_ring (p^n)\<^esub> (y n)" 
      by (simp add: padic_int_def padic_mult_res)       
    have RHS0: "(y \<otimes>\<^bsub>padic_int p\<^esub> x) n = (y n) \<otimes>\<^bsub>residue_ring (p^n)\<^esub> (x n)" 
      by (simp add: padic_int_def padic_mult_res) 
    have Ex: "(x n) \<in> carrier (residue_ring (p^n))" 
      using Ax padic_set_res_closed by auto 
    have Ey: "(y n) \<in> carrier (residue_ring (p^n))" 
      using Ay padic_set_res_closed by auto 
    have LHS1: "(x \<otimes>\<^bsub>padic_int p\<^esub> y) n = ((x n) *(y n)) mod (p^n)"
      using LHS0 
      by (simp add: residue_ring_def) 
    have RHS1: "(y \<otimes>\<^bsub>padic_int p\<^esub> x) n = ((y n) *(x n)) mod (p^n)"
      using RHS0 
      by (simp add: residue_ring_def) 
    then show ?thesis using LHS1 RHS1 
      by (simp add: mult.commute) 
  qed
qed

lemma padic_is_comm_monoid:
assumes "prime p"
shows "Group.comm_monoid (padic_int p)"
proof(rule comm_monoidI)
  show  "\<And>x y. 
            x \<in> carrier (padic_int p) \<Longrightarrow> 
            y \<in> carrier (padic_int p) \<Longrightarrow> 
            x \<otimes>\<^bsub>padic_int p\<^esub> y \<in> carrier (padic_int p)"
    by (simp add: padic_int_def assms padic_mult_in_padic_set) 
  show "\<one>\<^bsub>padic_int p\<^esub> \<in> carrier (padic_int p)" 
    by (metis padic_int_simps(1,5) assms  padic_one_in_padic_set)
  show "\<And>x y z. 
            x \<in> carrier (padic_int p) \<Longrightarrow>
            y \<in> carrier (padic_int p) \<Longrightarrow> 
            z \<in> carrier (padic_int p) \<Longrightarrow>
            x \<otimes>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z = x \<otimes>\<^bsub>padic_int p\<^esub> (y \<otimes>\<^bsub>padic_int p\<^esub> z)"
    using assms padic_mult_assoc by auto
  show "\<And>x. x \<in> carrier (padic_int p) \<Longrightarrow> \<one>\<^bsub>padic_int p\<^esub> \<otimes>\<^bsub>padic_int p\<^esub> x = x"
    using assms  padic_one_id by blast 
  show "\<And>x y. 
          x \<in> carrier (padic_int p) \<Longrightarrow>
          y \<in> carrier (padic_int p) \<Longrightarrow>
          x \<otimes>\<^bsub>padic_int p\<^esub> y = y \<otimes>\<^bsub>padic_int p\<^esub> x"
    using padic_mult_comm  by (simp add: assms)
qed

lemma padic_int_is_cring:
  assumes "prime p"
  shows "cring (padic_int p)"
proof (rule cringI)
  show "abelian_group (padic_int p)"
    by (simp add: assms padic_is_abelian_group)
  show "Group.comm_monoid (padic_int p)"
    by (simp add: assms padic_is_comm_monoid)
  show "\<And>x y z.
       x \<in> carrier (padic_int p) \<Longrightarrow>
       y \<in> carrier (padic_int p) \<Longrightarrow>
       z \<in> carrier (padic_int p) \<Longrightarrow>
       (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z =
         x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z "
  proof-
    fix x y z
    assume Ax: " x \<in> carrier (padic_int p)"
    assume Ay: " y \<in> carrier (padic_int p)"
    assume Az: " z \<in> carrier (padic_int p)"
    show "(x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z 
          = x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z"
    proof
      fix n
      have Ex: " (x n) \<in> carrier (residue_ring (p^n))" 
        using Ax padic_set_def padic_int_simps by auto
      have Ey: " (y n) \<in> carrier (residue_ring (p^n))" 
        using Ay padic_set_def padic_int_simps by auto
      have Ez: " (z n) \<in> carrier (residue_ring (p^n))" 
        using Az padic_set_def padic_int_simps by auto
      show "( (x \<oplus>\<^bsub>padic_int p\<^esub> y) \<otimes>\<^bsub>padic_int p\<^esub> z) n 
            = (x \<otimes>\<^bsub>padic_int p\<^esub> z \<oplus>\<^bsub>padic_int p\<^esub> y \<otimes>\<^bsub>padic_int p\<^esub> z) n "
      proof(cases "n=0")
        case True
        then show ?thesis 
          by (metis Ax Ay Az assms padic_add_closed padic_int_simps(4) padic_int_simps(5) padic_mult_in_padic_set padic_set_zero_res)                            
      next
        case False 
        then have "residues (p^n)" 
          by (simp add: assms residues_n)
        then show ?thesis 
          using Ex Ey Ez cring.cring_simprules(13) padic_add_res padic_int_simps
            padic_mult_res residues.cring by fastforce 
      qed
    qed
  qed
qed

text\<open>The $p$-adic ring has no nontrivial zero divisors. Note that this argument is short because we have proved that the valuation is multiplicative on nonzero elements, which is where the primality assumption is used.\<close>

lemma padic_no_zero_divisors:
assumes "prime p"
assumes "a \<in> carrier (padic_int p)"
assumes "b \<in>carrier (padic_int p)"
assumes "a \<noteq>\<zero>\<^bsub>padic_int p\<^esub> "
assumes "b \<noteq>\<zero>\<^bsub>padic_int p\<^esub> "
shows "a \<otimes>\<^bsub>padic_int p\<^esub> b \<noteq> \<zero>\<^bsub>padic_int p\<^esub> "
proof
  assume C: "a \<otimes>\<^bsub>padic_int p\<^esub> b = \<zero>\<^bsub>padic_int p\<^esub>"
  show False
  proof-
    have 0: "a = \<zero>\<^bsub>padic_int p\<^esub> \<or> b = \<zero>\<^bsub>padic_int p\<^esub>"
    proof(cases "a = \<zero>\<^bsub>padic_int p\<^esub>")
      case True
      then show ?thesis by auto
    next
      case False
      have "\<not> b  \<noteq>\<zero>\<^bsub>padic_int p\<^esub>"
      proof
        assume "b \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
        have "padic_val p (a \<otimes>\<^bsub>padic_int p\<^esub> b) = (padic_val p a) + (padic_val p b)" 
          using False assms(1) assms(2) assms(3) assms(5) val_prod padic_int_simps by auto
          then have "padic_val p (a \<otimes>\<^bsub>padic_int p\<^esub> b) \<noteq> -1" 
          using False \<open>b \<noteq> \<zero>\<^bsub>padic_int p\<^esub>\<close> padic_val_def padic_int_simps by auto
        then show False 
          using C padic_val_def padic_int_simps by auto      
        qed
      then show ?thesis 
        by blast
    qed
    show ?thesis 
      using "0" assms(4) assms(5) by blast
  qed
qed

lemma padic_int_is_domain:
  assumes "prime p"
  shows "domain (padic_int p)"
proof(rule domainI)
  show "cring (padic_int p)" 
    using padic_int_is_cring assms(1) by auto
  show "\<one>\<^bsub>padic_int p\<^esub> \<noteq> \<zero>\<^bsub>padic_int p\<^esub>"
  proof
    assume "\<one>\<^bsub>padic_int p\<^esub> = \<zero>\<^bsub>padic_int p\<^esub> "
    then have "(\<one>\<^bsub>padic_int p\<^esub>) 1 = \<zero>\<^bsub>padic_int p\<^esub> 1" by auto
    then show False 
      using padic_int_simps(1,2) 
      unfolding padic_one_def padic_zero_def by auto  
  qed
  show "\<And>a b. a \<otimes>\<^bsub>padic_int p\<^esub> b = \<zero>\<^bsub>padic_int p\<^esub>   \<Longrightarrow>
              a \<in> carrier (padic_int p) \<Longrightarrow> 
              b \<in> carrier (padic_int p) \<Longrightarrow> 
              a = \<zero>\<^bsub>padic_int p\<^esub> \<or> b = \<zero>\<^bsub>padic_int p\<^esub>"
    using assms padic_no_zero_divisors 
    by (meson prime_nat_int_transfer)    
qed     

section\<open>The Ultrametric Inequality:\<close>

lemma padic_val_ultrametric:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p) "
  assumes "b \<in> carrier (padic_int p) "
  assumes "a \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  assumes "b \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  assumes  "a \<oplus>\<^bsub>(padic_int p)\<^esub> b \<noteq> \<zero>\<^bsub>(padic_int p)\<^esub>"
  shows "padic_val p (a \<oplus>\<^bsub>(padic_int p)\<^esub> b) \<ge> min (padic_val p a) (padic_val p b)"
proof-
  let ?va = " nat (padic_val p a)"
  let ?vb = "nat (padic_val p b)"
  let ?vab = "nat (padic_val p (a \<oplus>\<^bsub>(padic_int p)\<^esub> b))"
  have P:" \<not> ?vab < min ?va ?vb"
  proof
    assume P0: "?vab < min ?va ?vb"
    then have "Suc ?vab \<le> min ?va ?vb"
      using Suc_leI by blast
    have "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) \<in> carrier (padic_int p) " 
      using assms(1) assms(2) assms(3)  padic_add_closed by simp
    then have C: "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) \<noteq>  \<zero>\<^bsub>residue_ring (p^(?vab + 1))\<^esub>" 
      using val_of_nonzero(1) assms(6)
      by (simp add: padic_int_def val_of_nonzero(1) assms(1)) 
    have S: "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) = (a (?vab + 1)) \<oplus>\<^bsub>residue_ring (p^((?vab + 1)))\<^esub> (b ((?vab + 1)))"  
      by (simp add: padic_int_def padic_add_def)
    have "int (?vab + 1) \<le> padic_val p a" 
      using P0  using Suc_le_eq by auto
    then have A: "(a (?vab + 1)) = \<zero>\<^bsub>residue_ring (p^((?vab + 1)))\<^esub> " 
      using assms(1) assms(2) zero_below_val padic_int_simps residue_ring_def 
      by auto     
    have "int (?vab + 1) \<le> padic_val p b" 
      using P0  using Suc_le_eq by auto
    then have B: "(b (?vab + 1)) = \<zero>\<^bsub>residue_ring (p^((?vab + 1)))\<^esub> " 
      using assms(1) assms(3) zero_below_val 
      by (metis A \<open>int (nat (padic_val p (a \<oplus>\<^bsub>padic_int p\<^esub> b)) + 1) \<le> padic_val p a\<close> 
          assms(2) padic_int_simps(3,5))      
    have "p^(?vab + 1) > 1" 
      using assms(1) by (metis add.commute plus_1_eq_Suc power_gt1 prime_gt_1_int)
    then have "residues (p^(?vab + 1))" 
      using less_imp_of_nat_less residues.intro by fastforce 
    then have "(a \<oplus>\<^bsub>(padic_int p)\<^esub> b) (?vab + 1) = \<zero>\<^bsub>residue_ring (p^((?vab + 1)))\<^esub> "
      using A B by (metis (no_types, lifting) S cring.cring_simprules(2)
          cring.cring_simprules(8) residues.cring) 
    then show False using C by auto
  qed
  have A0: "(padic_val p a) \<ge> 0" 
    using assms(4) padic_val_def by(auto simp: padic_int_def) 
  have A1: "(padic_val p b) \<ge> 0" 
    using assms(5) padic_val_def by(auto simp: padic_int_def) 
  have A2: "padic_val p (a \<oplus>\<^bsub>(padic_int p)\<^esub> b) \<ge> 0" 
    using assms(6) padic_val_def by(auto simp: padic_int_def) 
  show ?thesis using P A0 A1 A2 
    by linarith 
qed

lemma padic_a_inv:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p)"
  shows "\<ominus>\<^bsub>padic_int p\<^esub> a = (\<lambda> n. \<ominus>\<^bsub>residue_ring (p^n)\<^esub> (a n))"
proof
  fix n
  show "(\<ominus>\<^bsub>padic_int p\<^esub> a) n = \<ominus>\<^bsub>residue_ring (p^n)\<^esub> a n" 
  proof(cases "n=0")
    case True
    then show ?thesis 
      by (metis (no_types, lifting) abelian_group.a_inv_closed assms(1) assms(2) padic_int_simps(5) 
          padic_is_abelian_group padic_set_zero_res power_0 residue_1_prop residue_ring_def ring.simps(1))             
  next
    case False
    then have R: "residues (p^n)" 
      by (simp add: assms(1) residues_n)
    have "(\<ominus>\<^bsub>padic_int p\<^esub> a) \<oplus>\<^bsub>padic_int p\<^esub> a = \<zero>\<^bsub>padic_int p\<^esub>" 
      by (simp add: abelian_group.l_neg assms(1) assms(2) padic_is_abelian_group)      
    then have P: "(\<ominus>\<^bsub>padic_int p\<^esub> a) n \<oplus>\<^bsub>residue_ring (p^n)\<^esub> a n = 0"
      by (metis padic_add_res padic_int_simps(2) padic_int_simps(3) padic_zero_def)      
    have Q: "(a n) \<in> carrier (residue_ring (p^n))" 
      using assms(2) padic_set_res_closed by(auto simp: padic_int_def)
    show ?thesis using R Q residues.cring  
      by (metis P abelian_group.a_inv_closed abelian_group.minus_equality assms(1) assms(2) 
          padic_int_simps(5) padic_is_abelian_group padic_set_res_closed residues.abelian_group
          residues.res_zero_eq)                
  qed
qed

lemma padic_val_a_inv:
  assumes "prime p"
  assumes "a \<in> carrier (padic_int p)"
  shows "padic_val p a = padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a)"
proof(cases "a = \<zero>\<^bsub>padic_int p\<^esub>")
  case True
  then show ?thesis 
    by (metis abelian_group.a_inv_closed abelian_group.r_neg abelian_groupE(5) assms(1) assms(2) padic_is_abelian_group)    
next
  case False
  have 0: "\<And> n. (a n) = \<zero>\<^bsub>residue_ring (p^n)\<^esub> \<Longrightarrow> (\<ominus>\<^bsub>padic_int p\<^esub> a) n = \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
    using padic_a_inv 
    by (metis (no_types, lifting) assms(1) assms(2) cring.cring_simprules(22) power_0 residue_1_prop residues.cring residues_n)    
  have 1: "\<And> n. (a n) \<noteq> \<zero>\<^bsub>residue_ring (p^n)\<^esub> \<Longrightarrow> (\<ominus>\<^bsub>padic_int p\<^esub> a) n \<noteq> \<zero>\<^bsub>residue_ring (p^n)\<^esub>"
    using padic_a_inv 
    by (metis (no_types, lifting) abelian_group.a_inv_closed abelian_group.minus_minus assms(1)
        assms(2) cring.cring_simprules(22) padic_int_simps(5) padic_is_abelian_group padic_set_zero_res
        residues.cring residues_n)        
  have A:"padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<ge> (padic_val p a)" 
  proof-
    have "\<not> padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) < (padic_val p a)" 
    proof 
      assume "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) < padic_val p a"
      let ?n = "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a)"
      let ?m = " padic_val p a"
      have "(\<ominus>\<^bsub>padic_int p\<^esub> a)  \<noteq> (padic_zero p)" 
        by (metis False abelian_group.l_neg assms(1) assms(2) padic_add_zero padic_int_simps(2) padic_is_abelian_group)                      
      then have P0: "?n \<ge>0" 
        by (simp add: padic_val_def)
      have P1: "?m \<ge>0" using False 
        using \<open>0 \<le> padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a)\<close> 
          \<open>padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) < padic_val p a\<close> by linarith
      have "(Suc (nat ?n)) < Suc (nat (padic_val p a))"
        using P0 P1  \<open>padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) < padic_val p a\<close> by linarith
      then have "int (Suc (nat ?n)) \<le> (padic_val p a)" 
        using of_nat_less_iff by linarith
      then have "a (Suc (nat ?n)) =  \<zero>\<^bsub>residue_ring (p ^ ((Suc (nat ?n))))\<^esub>" 
        using assms(1) assms(2) zero_below_val residue_ring_def by(auto simp: padic_int_def)
      then have "(\<ominus>\<^bsub>padic_int p\<^esub> a) (Suc (nat ?n)) =  \<zero>\<^bsub>residue_ring (p ^ ((Suc (nat ?n))))\<^esub>" 
        using 0 by simp
      then show False using below_val_zero assms 
        by (metis Suc_eq_plus1 \<open>\<ominus>\<^bsub>padic_int p\<^esub> a \<noteq> padic_zero p\<close> abelian_group.a_inv_closed 
            padic_int_simps(5) padic_is_abelian_group val_of_nonzero(1))                    
    qed
    then show ?thesis 
      by linarith
  qed
  have B: "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<le> (padic_val p a)" 
  proof-
   let ?n = "nat (padic_val p a)"
    have "a (Suc ?n) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc ?n))\<^esub> " 
      using False assms(2) val_of_nonzero(1) 
      by (metis padic_int_simps(2,5) Suc_eq_plus1 assms(1)) 
    then have "(\<ominus>\<^bsub>padic_int p\<^esub> a) (Suc ?n) \<noteq> \<zero>\<^bsub>residue_ring (p^(Suc ?n))\<^esub> "
      using 1  by blast 
    then have  "padic_val p (\<ominus>\<^bsub>padic_int p\<^esub> a) \<le> int ?n"  using assms(1) assms(2) below_val_zero  
      by (metis padic_int_simps(5) abelian_group.a_inv_closed padic_is_abelian_group) 
    then show ?thesis 
      using False padic_val_def padic_int_simps by auto 
  qed
  then show ?thesis using A B by auto
qed

end
