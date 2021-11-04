(* Title: Examples/Vector_Spaces/VS_Prerequisites.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
chapter\<open>TTS Vector Spaces\<close>
theory VS_Prerequisites
  imports Types_To_Sets_Extension.ETTS_Auxiliary
begin




section\<open>Introduction\<close>



subsection\<open>Background\<close>


text\<open>
The content of this chapter is an adoption of the applied relativization
study presented in \cite{immler_smooth_2019} to the ETTS. 
The content of this chapter incorporates 
many elements of the content of the aforementioned relativization study without 
an explicit reference. Nonetheless, no attempt was made to ensure that
the theorems obtained as a result of this work are identical to the theorems 
obtained in \cite{immler_smooth_2019}. 
\<close>



subsection\<open>Prerequisites\<close>

ctr parametricity
  in bij_betw_ow: bij_betw_def

lemma bij_betw_parametric'[transfer_rule]:
  includes lifting_syntax
  assumes "bi_unique A"
  shows "((A ===> A) ===> rel_set A ===> rel_set A ===> (=)) 
    bij_betw bij_betw"
  by (rule bij_betw_ow.transfer[OF assms assms])

lemma vimage_transfer[transfer_rule]: 
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique B" "right_total A" 
  shows 
    "((A ===> B) ===> (rel_set B) ===> rel_set A) 
      (\<lambda>f s. (vimage f s) \<inter> (Collect (Domainp A))) (-`)"
  by transfer_prover

lemma Eps_unique_transfer_lemma:
  includes lifting_syntax
  assumes [transfer_rule]: 
    "right_total A" "(A ===> (=)) f g" "(A ===> (=)) f' g'"
    and holds: "\<exists>x. Domainp A x \<and> f x"
    and unique_g: "\<And>x y. \<lbrakk> g x; g y \<rbrakk> \<Longrightarrow> g' x = g' y"
  shows "f' (Eps (\<lambda>x. Domainp A x \<and> f x)) = g' (Eps g)"
proof -
  define Epsg where "Epsg = Eps g"
  have "\<exists>x. g x" by transfer (simp add: holds)
  then have "g Epsg" unfolding Epsg_def by (rule someI_ex)
  obtain x where x[transfer_rule]: "A x Epsg" 
    by (meson \<open>right_total A\<close> right_totalE)
  then have "Domainp A x" by auto
  from \<open>g Epsg\<close>[untransferred] have "f x" .
  from unique_g have unique:
    "\<And>x y. \<lbrakk> Domainp A x; Domainp A y; f x; f y \<rbrakk> \<Longrightarrow> f' x = f' y"
    by transfer
  have "f' (Eps (\<lambda>x. Domainp A x \<and> f x)) = f' x"
    by (rule unique[OF _ \<open>Domainp A x\<close> _ \<open>f x\<close>]) 
      (metis (mono_tags, lifting) local.holds someI_ex)+
  show "f' (SOME x. Domainp A x \<and> f x) = g' (Eps g)"
    using x \<open>f' (Eps _) = f' x\<close> Epsg_def rel_funE assms(3) by fastforce
qed

text\<open>\newpage\<close>

end