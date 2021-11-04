(* Title: Examples/SML_Relativization/Lattices/SML_Lattices.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about lattices\<close>
theory SML_Lattices
  imports SML_Semilattices
begin



subsection\<open>Simple lattices\<close>


subsubsection\<open>Definitions and common properties\<close>

locale lattice_ow = 
  semilattice_inf_ow U inf le ls + semilattice_sup_ow U sup le ls 
  for U :: "'al set" and inf le ls sup

locale lattice_pair_ow = 
  lattice\<^sub>1: lattice_ow U\<^sub>1 inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 +
  lattice\<^sub>2: lattice_ow U\<^sub>2 inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2
  for U\<^sub>1 :: "'al set" and inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1
    and U\<^sub>2 :: "'bl set" and inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2
begin

sublocale semilattice_inf_pair_ow ..
sublocale semilattice_sup_pair_ow ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma lattice_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===>
      (A ===> A ===> (=)) ===>
      (A ===> A ===> A) ===> 
      (=)
    )
    (lattice_ow (Collect (Domainp A))) class.lattice"
  unfolding class.lattice_def lattice_ow_def by transfer_prover
  
end


subsubsection\<open>Relativization\<close>

context lattice_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting lattice_ow_axioms
  eliminating through simp
begin

tts_lemma inf_sup_aci:
  assumes "x \<in> U" and "y \<in> U"
  shows 
    "x \<sqinter>\<^sub>o\<^sub>w y = y \<sqinter>\<^sub>o\<^sub>w x"
    "z \<in> U \<Longrightarrow> x \<sqinter>\<^sub>o\<^sub>w y \<sqinter>\<^sub>o\<^sub>w z = x \<sqinter>\<^sub>o\<^sub>w (y \<sqinter>\<^sub>o\<^sub>w z)"
    "z \<in> U \<Longrightarrow> x \<sqinter>\<^sub>o\<^sub>w (y \<sqinter>\<^sub>o\<^sub>w z) = y \<sqinter>\<^sub>o\<^sub>w (x \<sqinter>\<^sub>o\<^sub>w z)"
    "x \<sqinter>\<^sub>o\<^sub>w (x \<sqinter>\<^sub>o\<^sub>w y) = x \<sqinter>\<^sub>o\<^sub>w y"
    "x \<squnion>\<^sub>o\<^sub>w y = y \<squnion>\<^sub>o\<^sub>w x"
    "z \<in> U \<Longrightarrow> x \<squnion>\<^sub>o\<^sub>w y \<squnion>\<^sub>o\<^sub>w z = x \<squnion>\<^sub>o\<^sub>w (y \<squnion>\<^sub>o\<^sub>w z)"
    "z \<in> U \<Longrightarrow> x \<squnion>\<^sub>o\<^sub>w (y \<squnion>\<^sub>o\<^sub>w z) = y \<squnion>\<^sub>o\<^sub>w (x \<squnion>\<^sub>o\<^sub>w z)"
    "x \<squnion>\<^sub>o\<^sub>w (x \<squnion>\<^sub>o\<^sub>w y) = x \<squnion>\<^sub>o\<^sub>w y"
    is lattice_class.inf_sup_aci.
    
tts_lemma inf_sup_absorb:
  assumes "x \<in> U" and "y \<in> U"
  shows "x \<sqinter>\<^sub>o\<^sub>w (x \<squnion>\<^sub>o\<^sub>w y) = x"
    is lattice_class.inf_sup_absorb.

tts_lemma sup_inf_absorb:
  assumes "x \<in> U" and "y \<in> U"
  shows "x \<squnion>\<^sub>o\<^sub>w (x \<sqinter>\<^sub>o\<^sub>w y) = x"
    is lattice_class.sup_inf_absorb.
    
tts_lemma bdd_above_insert:
  assumes "a \<in> U" and "A \<subseteq> U"
  shows "local.bdd_above (insert a A) = local.bdd_above A"
    is lattice_class.bdd_above_insert.

tts_lemma bdd_below_insert:
  assumes "a \<in> U" and "A \<subseteq> U"
  shows "local.bdd_below (insert a A) = local.bdd_below A"
  is lattice_class.bdd_below_insert.
    
tts_lemma distrib_sup_le:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U"
  shows "x \<squnion>\<^sub>o\<^sub>w (y \<sqinter>\<^sub>o\<^sub>w z) \<le>\<^sub>o\<^sub>w x \<squnion>\<^sub>o\<^sub>w y \<sqinter>\<^sub>o\<^sub>w (x \<squnion>\<^sub>o\<^sub>w z)"
    is lattice_class.distrib_sup_le.

tts_lemma distrib_inf_le:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U"
  shows "x \<sqinter>\<^sub>o\<^sub>w y \<squnion>\<^sub>o\<^sub>w (x \<sqinter>\<^sub>o\<^sub>w z) \<le>\<^sub>o\<^sub>w x \<sqinter>\<^sub>o\<^sub>w (y \<squnion>\<^sub>o\<^sub>w z)"
    is lattice_class.distrib_inf_le.

tts_lemma distrib_imp1:
  assumes "x \<in> U"
    and "y \<in> U"
    and "z \<in> U"
    and 
      "\<And>x y z. \<lbrakk>x \<in> U; y \<in> U; z \<in> U\<rbrakk> \<Longrightarrow> 
        x \<sqinter>\<^sub>o\<^sub>w (y \<squnion>\<^sub>o\<^sub>w z) = x \<sqinter>\<^sub>o\<^sub>w y \<squnion>\<^sub>o\<^sub>w (x \<sqinter>\<^sub>o\<^sub>w z)"
  shows "x \<squnion>\<^sub>o\<^sub>w (y \<sqinter>\<^sub>o\<^sub>w z) = x \<squnion>\<^sub>o\<^sub>w y \<sqinter>\<^sub>o\<^sub>w (x \<squnion>\<^sub>o\<^sub>w z)"
    is lattice_class.distrib_imp1.

tts_lemma distrib_imp2:
  assumes "x \<in> U"
    and "y \<in> U"
    and "z \<in> U"
    and 
      "\<And>x y z. \<lbrakk>x \<in> U; y \<in> U; z \<in> U\<rbrakk> \<Longrightarrow> 
        x \<squnion>\<^sub>o\<^sub>w (y \<sqinter>\<^sub>o\<^sub>w z) = x \<squnion>\<^sub>o\<^sub>w y \<sqinter>\<^sub>o\<^sub>w (x \<squnion>\<^sub>o\<^sub>w z)"
  shows "x \<sqinter>\<^sub>o\<^sub>w (y \<squnion>\<^sub>o\<^sub>w z) = x \<sqinter>\<^sub>o\<^sub>w y \<squnion>\<^sub>o\<^sub>w (x \<sqinter>\<^sub>o\<^sub>w z)"
    is lattice_class.distrib_imp2.

tts_lemma bdd_above_Un:
  assumes "A \<subseteq> U" and "B \<subseteq> U"
  shows "local.bdd_above (A \<union> B) = (local.bdd_above A \<and> local.bdd_above B)"
    is lattice_class.bdd_above_Un.

tts_lemma bdd_below_Un:
  assumes "A \<subseteq> U" and "B \<subseteq> U"
  shows "local.bdd_below (A \<union> B) = (local.bdd_below A \<and> local.bdd_below B)"
    is lattice_class.bdd_below_Un.

tts_lemma bdd_above_image_sup:
  assumes "range f \<subseteq> U" and "range g \<subseteq> U"
  shows "local.bdd_above ((\<lambda>x. f x \<squnion>\<^sub>o\<^sub>w g x) ` A) = 
    (local.bdd_above (f ` A) \<and> local.bdd_above (g ` A))"
    is lattice_class.bdd_above_image_sup.

tts_lemma bdd_below_image_inf:
  assumes "range f \<subseteq> U" and "range g \<subseteq> U"
  shows "local.bdd_below ((\<lambda>x. f x \<sqinter>\<^sub>o\<^sub>w g x) ` A) = 
    (local.bdd_below (f ` A) \<and> local.bdd_below (g ` A))"
    is lattice_class.bdd_below_image_inf.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting lattice_ow_axioms
  eliminating through simp
begin

tts_lemma bdd_above_UN:
  assumes "U \<noteq> {}" and "range A \<subseteq> Pow U" and "finite I"
  shows "bdd_above (\<Union> (A ` I)) = (\<forall>x\<in>I. bdd_above (A x))"
    is lattice_class.bdd_above_UN .

tts_lemma bdd_below_UN:
  assumes "U \<noteq> {}" and "range A \<subseteq> Pow U" and "finite I"
  shows "local.bdd_below (\<Union> (A ` I)) = (\<forall>x\<in>I. local.bdd_below (A x))"
    is lattice_class.bdd_below_UN.
    
tts_lemma bdd_above_finite:
  assumes "U \<noteq> {}" and "A \<subseteq> U" and "finite A"
  shows "local.bdd_above A"
    is lattice_class.bdd_above_finite.

tts_lemma bdd_below_finite:
  assumes "U \<noteq> {}" and "A \<subseteq> U" and "finite A"
  shows "local.bdd_below A"
    is lattice_class.bdd_below_finite.

end

end



subsection\<open>Bounded lattices\<close>


subsubsection\<open>Definitions and common properties\<close>

locale bounded_lattice_bot_ow = 
  lattice_ow U inf le ls sup + order_bot_ow U bot le ls
  for U :: "'al set" and inf le ls sup bot
begin

sublocale bounded_semilattice_sup_bot_ow U \<open>(\<squnion>\<^sub>o\<^sub>w)\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> \<open>\<bottom>\<^sub>o\<^sub>w\<close> ..

end

locale bounded_lattice_bot_pair_ow = 
  blb\<^sub>1: bounded_lattice_bot_ow U\<^sub>1 inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 bot\<^sub>1 +
  blb\<^sub>2: bounded_lattice_bot_ow U\<^sub>2 inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2 bot\<^sub>2
  for U\<^sub>1 :: "'al set" and inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 bot\<^sub>1
    and U\<^sub>2 :: "'bl set" and inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2 bot\<^sub>2
begin

sublocale lattice_pair_ow ..
sublocale order_bot_pair_ow U\<^sub>1 bot\<^sub>1 le\<^sub>1 ls\<^sub>1 U\<^sub>2 bot\<^sub>2 le\<^sub>2 ls\<^sub>2 ..

end

locale bounded_lattice_top_ow = 
  lattice_ow U inf le ls sup + order_top_ow U le ls top
  for U :: "'al set" and inf le ls sup top 
begin

sublocale bounded_semilattice_inf_top_ow U \<open>(\<sqinter>\<^sub>o\<^sub>w)\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> \<open>\<top>\<^sub>o\<^sub>w\<close> ..

end

locale bounded_lattice_top_pair_ow = 
  blb\<^sub>1: bounded_lattice_top_ow U\<^sub>1 inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 top\<^sub>1 +
  blb\<^sub>2: bounded_lattice_top_ow U\<^sub>2 inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2 top\<^sub>2
  for U\<^sub>1 :: "'al set" and inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 top\<^sub>1
    and U\<^sub>2 :: "'bl set" and inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2 top\<^sub>2
begin

sublocale lattice_pair_ow ..
sublocale order_top_pair_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 top\<^sub>1 U\<^sub>2 le\<^sub>2 ls\<^sub>2 top\<^sub>2 ..

end

locale bounded_lattice_ow = 
  lattice_ow U inf le ls sup + 
  order_bot_ow U bot le ls + 
  order_top_ow U le ls top
  for U :: "'al set" and inf le ls sup bot top
begin

sublocale bounded_lattice_bot_ow U \<open>(\<sqinter>\<^sub>o\<^sub>w)\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> \<open>(\<squnion>\<^sub>o\<^sub>w)\<close> \<open>\<bottom>\<^sub>o\<^sub>w\<close> ..
sublocale bounded_lattice_top_ow U \<open>(\<sqinter>\<^sub>o\<^sub>w)\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> \<open>(\<squnion>\<^sub>o\<^sub>w)\<close> \<open>\<top>\<^sub>o\<^sub>w\<close> ..

end

locale bounded_lattice_pair_ow = 
  bl\<^sub>1: bounded_lattice_ow U\<^sub>1 inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 bot\<^sub>1 top\<^sub>1 +
  bl\<^sub>2: bounded_lattice_ow U\<^sub>2 inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2 bot\<^sub>2 top\<^sub>2
  for U\<^sub>1 :: "'al set" and inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 bot\<^sub>1 top\<^sub>1 
    and U\<^sub>2 :: "'bl set" and inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2 bot\<^sub>2 top\<^sub>2
begin

sublocale bounded_lattice_bot_pair_ow ..
sublocale bounded_lattice_top_pair_ow ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma bounded_lattice_bot_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> A) ===> 
      A ===> 
      (=)
    ) 
    (bounded_lattice_bot_ow (Collect (Domainp A))) 
    class.bounded_lattice_bot"
  unfolding bounded_lattice_bot_ow_def class.bounded_lattice_bot_def
  by transfer_prover

lemma bounded_lattice_top_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "
    (
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> A) ===> 
      A ===> 
      (=)
    ) 
      (bounded_lattice_top_ow (Collect (Domainp A))) 
      class.bounded_lattice_top"
  unfolding bounded_lattice_top_ow_def class.bounded_lattice_top_def
  by transfer_prover

lemma bounded_lattice_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> A) ===> 
      A ===> 
      A ===> 
      (=)
    ) 
    (bounded_lattice_ow (Collect (Domainp A))) class.bounded_lattice"
  unfolding bounded_lattice_ow_def class.bounded_lattice_def by transfer_prover

end


subsubsection\<open>Relativization\<close>

context bounded_lattice_bot_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting bounded_lattice_bot_ow_axioms and sup_bot.sl_neut.not_empty
  applying [OF inf_closed' sup_closed' bot_closed]
begin

tts_lemma inf_bot_left:
  assumes "x \<in> U"
  shows "\<bottom>\<^sub>o\<^sub>w \<sqinter>\<^sub>o\<^sub>w x = \<bottom>\<^sub>o\<^sub>w"
    is bounded_lattice_bot_class.inf_bot_left.

tts_lemma inf_bot_right:
  assumes "x \<in> U"
  shows "x \<sqinter>\<^sub>o\<^sub>w \<bottom>\<^sub>o\<^sub>w = \<bottom>\<^sub>o\<^sub>w"
    is bounded_lattice_bot_class.inf_bot_right.

end

end

context bounded_lattice_top_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting bounded_lattice_top_ow_axioms and inf_top.sl_neut.not_empty
  applying [OF inf_closed' sup_closed' top_closed]
begin
    
tts_lemma sup_top_left:
  assumes "x \<in> U"
  shows "\<top>\<^sub>o\<^sub>w \<squnion>\<^sub>o\<^sub>w x = \<top>\<^sub>o\<^sub>w"
    is bounded_lattice_top_class.sup_top_left.
    
tts_lemma sup_top_right:
  assumes "x \<in> U"
  shows "x \<squnion>\<^sub>o\<^sub>w \<top>\<^sub>o\<^sub>w = \<top>\<^sub>o\<^sub>w"
    is bounded_lattice_top_class.sup_top_right.
    
end

end

context bounded_lattice_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting bounded_lattice_ow_axioms 
  applying [OF sup_bot.sl_neut.not_empty, simplified]
begin

tts_lemma atLeastAtMost_eq_UNIV_iff:
  assumes "x \<in> U" and "y \<in> U"
  shows "({x..\<^sub>o\<^sub>wy} = U) = (x = \<bottom>\<^sub>o\<^sub>w \<and> y = \<top>\<^sub>o\<^sub>w)"
    is bounded_lattice_class.atLeastAtMost_eq_UNIV_iff.

end

end



subsection\<open>Distributive lattices\<close>


subsubsection\<open>Definitions and common properties\<close>

locale distrib_lattice_ow =
  lattice_ow U inf le ls sup for U :: "'al set" and inf le ls sup  +
  assumes sup_inf_distrib1: 
    "\<lbrakk> x \<in> U; y \<in> U; z \<in> U \<rbrakk> \<Longrightarrow> x \<squnion>\<^sub>o\<^sub>w (y \<sqinter>\<^sub>o\<^sub>w z) = (x \<squnion>\<^sub>o\<^sub>w y) \<sqinter>\<^sub>o\<^sub>w (x \<squnion>\<^sub>o\<^sub>w z)"


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma distrib_lattice_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===>
      (A ===> A ===> (=)) ===>
      (A ===> A ===> A) ===> 
      (=)
    )
    (distrib_lattice_ow (Collect (Domainp A))) class.distrib_lattice"
  unfolding 
    distrib_lattice_ow_def class.distrib_lattice_def  
    class.distrib_lattice_axioms_def distrib_lattice_ow_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp
  
end


subsubsection\<open>Relativization\<close>

context distrib_lattice_ow 
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting distrib_lattice_ow_axioms
  eliminating through simp
begin

tts_lemma inf_sup_distrib1:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U"
  shows "x \<sqinter>\<^sub>o\<^sub>w (y \<squnion>\<^sub>o\<^sub>w z) = x \<sqinter>\<^sub>o\<^sub>w y \<squnion>\<^sub>o\<^sub>w (x \<sqinter>\<^sub>o\<^sub>w z)"
  is distrib_lattice_class.inf_sup_distrib1.

tts_lemma inf_sup_distrib2:
  assumes "y \<in> U" and "z \<in> U" and "x \<in> U"
  shows "y \<squnion>\<^sub>o\<^sub>w z \<sqinter>\<^sub>o\<^sub>w x = y \<sqinter>\<^sub>o\<^sub>w x \<squnion>\<^sub>o\<^sub>w (z \<sqinter>\<^sub>o\<^sub>w x)"
    is distrib_lattice_class.inf_sup_distrib2.

tts_lemma sup_inf_distrib2:
  assumes "y \<in> U" and "z \<in> U" and "x \<in> U"
  shows "y \<sqinter>\<^sub>o\<^sub>w z \<squnion>\<^sub>o\<^sub>w x = y \<squnion>\<^sub>o\<^sub>w x \<sqinter>\<^sub>o\<^sub>w (z \<squnion>\<^sub>o\<^sub>w x)"
    is distrib_lattice_class.sup_inf_distrib2.

end

end

text\<open>\newpage\<close>

end