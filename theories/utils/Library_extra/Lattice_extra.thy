theory Lattice_extra
imports "~~/src/HOL/Algebra/Lattice"
begin

definition dual_gorder :: "('a, 'b) gorder_scheme \<Rightarrow> 'a gorder" where
  "dual_gorder L = \<lparr> carrier = carrier L
                   , eq = op .=\<^bsub>L\<^esub>
                   , le = (\<lambda> x y. y \<sqsubseteq>\<^bsub>L \<^esub>x) \<rparr>"

definition
  LFP :: "('a, 'b) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<mu>\<index>") where
  "LFP L f = \<Sqinter>\<^bsub>L\<^esub> {u \<in> carrier L. f u \<sqsubseteq>\<^bsub>L\<^esub> u}"    --{*least fixed point*}

definition
  GFP:: "('a, 'b) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<nu>\<index>") where
  "GFP L f = \<Squnion>\<^bsub>L\<^esub> {u \<in> carrier L. u \<sqsubseteq>\<^bsub>L\<^esub> f u}"    --{*greatest fixed point*}

lemma eq_dual [simp]:
  "(x .=\<^bsub>dual_gorder L\<^esub> y) = (x .=\<^bsub>L\<^esub> y)"
  by (simp add:dual_gorder_def)

lemma le_dual [simp]:
  "x \<sqsubseteq>\<^bsub>dual_gorder L\<^esub> y = (y \<sqsubseteq>\<^bsub>L\<^esub> x)"
  by (simp add:dual_gorder_def)

lemma carrier_dual [simp]:
  "carrier (dual_gorder L) = carrier L"
  by (simp add:dual_gorder_def)

lemma Lower_dual [simp]:
  "Lower (dual_gorder L) A = Upper L A"
  by (simp add:Upper_def Lower_def dual_gorder_def)

lemma Upper_dual [simp]:
  "Upper (dual_gorder L) A = Lower L A"
  by (simp add:Upper_def Lower_def dual_gorder_def)

lemma least_dual [simp]:
  "least (dual_gorder L) x A = greatest L x A"
  by (simp add:least_def greatest_def dual_gorder_def)

lemma greatest_dual [simp]:
  "greatest (dual_gorder L) x A = least L x A"
  by (simp add:least_def greatest_def dual_gorder_def)

lemma sup_dual [simp]: 
  "\<Squnion>\<^bsub>dual_gorder L\<^esub>A = \<Sqinter>\<^bsub>L\<^esub>A"
  by (simp add:sup_def inf_def)

lemma inf_dual [simp]: 
  "\<Sqinter>\<^bsub>dual_gorder L\<^esub>A = \<Squnion>\<^bsub>L\<^esub>A"
  by (simp add:sup_def inf_def)

lemma join_dual [simp]:
  "p \<squnion>\<^bsub>dual_gorder L\<^esub> q = p \<sqinter>\<^bsub>L\<^esub> q"
  by (simp add:join_def meet_def)

lemma meet_dual [simp]:
  "p \<sqinter>\<^bsub>dual_gorder L\<^esub> q = p \<squnion>\<^bsub>L\<^esub> q"
  by (simp add:join_def meet_def)

lemma top_dual [simp]:
  "\<top>\<^bsub>dual_gorder L\<^esub> = \<bottom>\<^bsub>L\<^esub>"
  by (simp add:top_def bottom_def)

lemma bottom_dual [simp]:
  "\<bottom>\<^bsub>dual_gorder L\<^esub> = \<top>\<^bsub>L\<^esub>"
  by (simp add:top_def bottom_def)

lemma LFP_dual [simp]:
  "LFP (dual_gorder L) f = GFP L f"
  by (simp add:LFP_def GFP_def)

lemma GFP_dual [simp]:
  "GFP (dual_gorder L) f = LFP L f"
  by (simp add:LFP_def GFP_def)

context weak_partial_order
begin

lemma dual_weak_order:
  "weak_partial_order (dual_gorder L)"
  apply (unfold_locales)
  apply (simp_all add:dual_gorder_def)
  apply (metis sym)
  apply (metis trans)
  apply (metis weak_le_antisym)
  apply (metis le_trans)
  apply (metis le_cong_l le_cong_r sym)
done

definition Mono :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"Mono f \<longleftrightarrow> (\<forall>x\<in>carrier L. \<forall>y\<in>carrier L. x \<sqsubseteq> y \<longrightarrow> f x \<sqsubseteq> f y)"

lemma MonoI [intro?]:
  fixes f :: "'a \<Rightarrow> 'a"
  assumes "(\<And>x y. \<lbrakk> x \<in> carrier L; y \<in> carrier L; x \<sqsubseteq> y \<rbrakk> \<Longrightarrow> f x \<sqsubseteq> f y)"
  shows "Mono f"
  by (metis assms Mono_def)

end

context weak_lattice
begin

lemma dual_weak_lattice:
  "weak_lattice (dual_gorder L)"
proof -
  interpret dual: weak_partial_order "dual_gorder L"
    by (metis dual_weak_order)

  show ?thesis
    apply (unfold_locales)
    apply (simp_all add: inf_of_two_exists sup_of_two_exists)
  done
qed

end

sublocale lattice \<subseteq> weak_lattice ..

context lattice
begin

lemma dual_lattice:
  "lattice (dual_gorder L)"
proof -
  interpret dual: weak_lattice "dual_gorder L"
    by (metis dual_weak_lattice)

  show ?thesis
    apply (unfold_locales)
    apply (simp_all add: inf_of_two_exists sup_of_two_exists)
    apply (simp add:dual_gorder_def eq_is_equal)
  done
qed

end

locale weak_partial_order_bottom = weak_partial_order L for L (structure) +
  assumes bottom_exists: "\<exists> x. least L x (carrier L)"
begin

lemma bottom_least: "least L \<bottom> (carrier L)"
proof -
  obtain x where "least L x (carrier L)"
    by (metis bottom_exists)

  thus ?thesis
    apply (simp add:bottom_def inf_def)
    apply (rule_tac someI2[of _ "x"])
    apply (rule greatest_LowerI)
    apply (auto simp add:least_def assms)
    apply (metis assms greatest_Lower_below order_refl)
  done
qed

lemma bottom_closed':
  "\<bottom> \<in> carrier L"
  by (metis bottom_least least_mem)

lemma bottom_lower:
  "x \<in> carrier L \<Longrightarrow> \<bottom> \<sqsubseteq> x"
  by (metis bottom_least least_le)

end

locale weak_partial_order_top = weak_partial_order L for L (structure) +
  assumes top_exists: "\<exists> x. greatest L x (carrier L)"
begin

lemma top_greatest: "greatest L \<top> (carrier L)"
proof -
  obtain x where "greatest L x (carrier L)"
    by (metis top_exists)

  thus ?thesis
    apply (simp add:top_def sup_def)
    apply (rule_tac someI2[of _ "x"])
    apply (rule least_UpperI)
    apply (auto simp add:greatest_def assms)
    apply (metis least_Upper_above order_refl)
  done
qed

lemma top_closed':
  "\<top> \<in> carrier L"
  by (metis greatest_mem top_greatest)

lemma top_higher:
  "x \<in> carrier L \<Longrightarrow> x \<sqsubseteq> \<top>"
  by (metis greatest_le top_greatest)

end

locale weak_bounded_lattice = weak_lattice + weak_partial_order_bottom + weak_partial_order_top
begin

lemma bottom_meet: "x \<in> carrier L \<Longrightarrow> \<bottom> \<sqinter> x .= \<bottom>"
  by (metis bottom_least least_def meet_closed meet_left weak_le_antisym)

lemma bottom_join: "x \<in> carrier L \<Longrightarrow> \<bottom> \<squnion> x .= x"
  by (metis bottom_least join_closed join_le join_right le_refl least_def weak_le_antisym)

lemma bottom_weak_eq:  "\<lbrakk> b \<in> carrier L; \<And> x. x \<in> carrier L \<Longrightarrow> b \<sqsubseteq> x \<rbrakk> \<Longrightarrow> b .= \<bottom>"
  by (metis bottom_closed' bottom_lower weak_le_antisym)

lemma top_join: "x \<in> carrier L \<Longrightarrow> \<top> \<squnion> x .= \<top>"
  by (metis join_closed join_left top_closed' top_higher weak_le_antisym)

lemma top_meet: "x \<in> carrier L \<Longrightarrow> \<top> \<sqinter> x .= x"
  by (metis le_refl meet_closed meet_le meet_right top_closed' top_higher weak_le_antisym)

lemma top_weak_eq:  "\<lbrakk> t \<in> carrier L; \<And> x. x \<in> carrier L \<Longrightarrow> x \<sqsubseteq> t \<rbrakk> \<Longrightarrow> t .= \<top>"
  by (metis top_closed' top_higher weak_le_antisym)

end

sublocale weak_complete_lattice \<subseteq> weak_bounded_lattice
  apply (unfold_locales)
  apply (metis Upper_empty empty_subsetI sup_exists)
  apply (metis Lower_empty empty_subsetI inf_exists)
done

locale bounded_lattice = lattice + weak_partial_order_bottom + weak_partial_order_top
begin

lemma bottom_eq:  "\<lbrakk> b \<in> carrier L; \<And> x. x \<in> carrier L \<Longrightarrow> b \<sqsubseteq> x \<rbrakk> \<Longrightarrow> b = \<bottom>"
  by (metis bottom_closed' bottom_lower le_antisym)

lemma top_eq:  "\<lbrakk> t \<in> carrier L; \<And> x. x \<in> carrier L \<Longrightarrow> x \<sqsubseteq> t \<rbrakk> \<Longrightarrow> t = \<top>"
  by (metis le_antisym top_closed' top_higher)

end

context weak_complete_lattice
begin

lemma dual_weak_complete_lattice:
  "weak_complete_lattice (dual_gorder L)"
proof -
  interpret dual: weak_lattice "dual_gorder L"
    by (metis dual_weak_lattice)

  show ?thesis
    apply (unfold_locales)
    apply (simp_all add:inf_exists sup_exists)
  done
qed

lemma inf_glb: 
  assumes "A \<subseteq> carrier L"
  shows "greatest L (\<Sqinter>A) (Lower L A)"
proof -
  obtain i where "greatest L i (Lower L A)"
    by (metis assms inf_exists)

  thus ?thesis
    apply (simp add:inf_def)
    apply (rule someI2[of _ "i"])
    apply (auto)
  done
qed

lemma inf_lower:
  assumes "A \<subseteq> carrier L" "x \<in> A"
  shows "\<Sqinter>A \<sqsubseteq> x"
  by (metis assms greatest_Lower_below inf_glb)

lemma inf_greatest: 
  assumes "A \<subseteq> carrier L" "z \<in> carrier L" 
          "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x)"
  shows "z \<sqsubseteq> \<Sqinter>A"
  by (metis Lower_memI assms greatest_le inf_glb)

lemma sup_lub: 
  assumes "A \<subseteq> carrier L"
  shows "least L (\<Squnion>A) (Upper L A)"
proof -
  interpret dual: weak_complete_lattice "dual_gorder L"
    by (metis dual_weak_complete_lattice)

  show ?thesis
    by (metis Lower_dual assms carrier_dual dual.inf_glb greatest_dual inf_dual)
qed

lemma sup_upper: 
  assumes "A \<subseteq> carrier L" "x \<in> A"
  shows "x \<sqsubseteq> \<Squnion>A"
  by (metis assms least_Upper_above supI)

lemma sup_least:
  assumes "A \<subseteq> carrier L" "z \<in> carrier L" 
          "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z)" 
  shows "\<Squnion>A \<sqsubseteq> z"
  by (metis Upper_memI assms least_le sup_lub)

lemma LFP_closed:
  "\<mu> f \<in> carrier L"
  by (metis (lifting) LFP_def inf_closed mem_Collect_eq subsetI)

lemma GFP_closed:
  "\<nu> f \<in> carrier L"
  by (metis LFP_dual carrier_dual dual_weak_complete_lattice weak_complete_lattice.LFP_closed)

lemma LFP_lowerbound: 
  assumes "x \<in> carrier L" "f x \<sqsubseteq> x" 
  shows "\<mu> f \<sqsubseteq> x"
  by (auto intro:inf_lower assms simp add:LFP_def)

lemma GFP_upperbound:
  assumes "x \<in> carrier L" "x \<sqsubseteq> f x"
  shows "x \<sqsubseteq> \<nu> f"
  by (metis LFP_dual assms carrier_dual dual_weak_complete_lattice le_dual weak_complete_lattice.LFP_lowerbound)

lemma LFP_greatest: 
  assumes "x \<in> carrier L" 
          "(\<And>u. \<lbrakk> u \<in> carrier L; f u \<sqsubseteq> u \<rbrakk> \<Longrightarrow> x \<sqsubseteq> u)"
  shows "x \<sqsubseteq> \<mu> f"
  by (auto simp add:LFP_def intro:inf_greatest assms)

lemma GFP_least: 
  assumes "x \<in> carrier L" 
          "(\<And>u. \<lbrakk> u \<in> carrier L; u \<sqsubseteq> f u \<rbrakk> \<Longrightarrow> u \<sqsubseteq> x)"
  shows "\<nu> f \<sqsubseteq> x"
  by (auto simp add:GFP_def intro:sup_least assms)

lemma LFP_lemma2: 
  assumes "Mono f" "\<And> x. x \<in> carrier L \<Longrightarrow> f x \<in> carrier L"
  shows "f (\<mu> f) \<sqsubseteq> \<mu> f"
  apply (rule LFP_greatest)
  apply (metis LFP_closed assms)
  apply (metis LFP_closed LFP_lowerbound Mono_def assms le_trans)
done

lemma LFP_lemma3: 
  assumes "Mono f" "\<And> x. x \<in> carrier L \<Longrightarrow> f x \<in> carrier L"
  shows "\<mu> f \<sqsubseteq> f (\<mu> f)"
  by (metis LFP_closed LFP_lemma2 LFP_lowerbound Mono_def assms)

lemma LFP_weak_unfold: 
  "\<lbrakk> Mono f; \<And> x. x \<in> carrier L \<Longrightarrow> f x \<in> carrier L \<rbrakk> \<Longrightarrow> \<mu> f .= f (\<mu> f)"
  by (metis LFP_closed LFP_lemma2 LFP_lemma3 weak_le_antisym)

lemma GFP_lemma2:
  assumes "Mono f" "\<And> x. x \<in> carrier L \<Longrightarrow> f x \<in> carrier L"
  shows "\<nu> f \<sqsubseteq> f (\<nu> f)"
  apply (rule GFP_least)
  apply (metis GFP_closed assms(2))
  apply (metis GFP_closed GFP_upperbound Mono_def assms le_trans)
done

lemma GFP_lemma3:
  assumes "Mono f" "\<And> x. x \<in> carrier L \<Longrightarrow> f x \<in> carrier L"
  shows "f (\<nu> f) \<sqsubseteq> \<nu> f"
  by (metis GFP_closed GFP_lemma2 GFP_upperbound Mono_def assms)

lemma GFP_weak_unfold: 
  "\<lbrakk> Mono f; \<And> x. x \<in> carrier L \<Longrightarrow> f x \<in> carrier L \<rbrakk> \<Longrightarrow> \<nu> f .= f (\<nu> f)"
  by (metis GFP_closed GFP_lemma2 GFP_lemma3 weak_le_antisym)

end

context complete_lattice
begin

lemma LFP_unfold: 
  "\<lbrakk> Mono f; \<And> x. x \<in> carrier L \<Longrightarrow> f x \<in> carrier L \<rbrakk> \<Longrightarrow> \<mu> f = f (\<mu> f)"
  by (metis LFP_closed LFP_lemma2 LFP_lemma3 le_antisym)

lemma GFP_unfold:
  "\<lbrakk> Mono f; \<And> x. x \<in> carrier L \<Longrightarrow> f x \<in> carrier L \<rbrakk> \<Longrightarrow> \<nu> f = f (\<nu> f)"
  by (metis GFP_closed GFP_lemma2 GFP_lemma3 le_antisym)

end

sublocale weak_bounded_lattice \<subseteq> weak_partial_order ..

sublocale bounded_lattice \<subseteq> partial_order ..

sublocale bounded_lattice \<subseteq> weak_bounded_lattice ..

text {* Unfortunately we have to hide the algebra lattice syntax so it doesn't conflict
        with the builtin HOL version. *}

no_notation
  le (infixl "\<sqsubseteq>\<index>" 50) and
  lless (infixl "\<sqsubset>\<index>" 50) and
  sup ("\<Squnion>\<index>_" [90] 90) and
  inf ("\<Sqinter>\<index>_" [90] 90) and
  join (infixl "\<squnion>\<index>" 65) and
  meet (infixl "\<sqinter>\<index>" 70) and
  top ("\<top>\<index>") and
  bottom ("\<bottom>\<index>") and
  LFP ("\<mu>\<index>") and
  GFP ("\<nu>\<index>")

end