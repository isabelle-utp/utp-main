(* Title: Examples/SML_Relativization/Lattices/SML_Complete_Lattices.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about complete lattices\<close>
theory SML_Complete_Lattices
  imports SML_Lattices
begin



subsection\<open>Simple complete lattices\<close>


subsubsection\<open>Definitions and common properties\<close>

locale Inf_ow = 
  fixes U :: "'al set" and Inf (\<open>\<Sqinter>\<^sub>o\<^sub>w\<close>)
  assumes Inf_closed[simp]: "\<Sqinter>\<^sub>o\<^sub>w ` Pow U \<subseteq> U"
begin

notation Inf (\<open>\<Sqinter>\<^sub>o\<^sub>w\<close>)

lemma Inf_closed'[simp]: "\<forall>x\<subseteq>U. \<Sqinter>\<^sub>o\<^sub>w x \<in> U" using Inf_closed by blast

end

locale Inf_pair_ow = Inf\<^sub>1: Inf_ow U\<^sub>1 Inf\<^sub>1 + Inf\<^sub>2: Inf_ow U\<^sub>2 Inf\<^sub>2 
  for U\<^sub>1 :: "'al set" and Inf\<^sub>1 and U\<^sub>2 :: "'bl set" and Inf\<^sub>2
begin

notation Inf\<^sub>1 (\<open>\<Sqinter>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close>)
notation Inf\<^sub>2 (\<open>\<Sqinter>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close>)

end

locale Sup_ow = 
  fixes U :: "'al set" and Sup (\<open>\<Squnion>\<^sub>o\<^sub>w\<close>)
  assumes Sup_closed[simp]: "\<Squnion>\<^sub>o\<^sub>w ` Pow U \<subseteq> U"
begin

notation Sup (\<open>\<Squnion>\<^sub>o\<^sub>w\<close>)

lemma Sup_closed'[simp]: "\<forall>x\<subseteq>U. \<Squnion>\<^sub>o\<^sub>w x \<in> U" using Sup_closed by blast

end

locale Sup_pair_ow = Sup\<^sub>1: Sup_ow U\<^sub>1 Sup\<^sub>1 + Sup\<^sub>2: Sup_ow U\<^sub>2 Sup\<^sub>2 
  for U\<^sub>1 :: "'al set" and Sup\<^sub>1 and U\<^sub>2 :: "'bl set" and Sup\<^sub>2
begin

notation Sup\<^sub>1 (\<open>\<Squnion>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close>)
notation Sup\<^sub>2 (\<open>\<Squnion>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close>)

end

locale complete_lattice_ow =
  lattice_ow U inf le ls sup +
  Inf_ow U Inf + 
  Sup_ow U Sup + 
  bot_ow U bot + 
  top_ow U top
  for U :: "'al set" and Inf  Sup inf le ls sup bot top +
  assumes Inf_lower: "\<lbrakk> A \<subseteq> U; x \<in> A \<rbrakk> \<Longrightarrow> \<Sqinter>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w x"
    and Inf_greatest: 
      "\<lbrakk> A \<subseteq> U; z \<in> U; (\<And>x. x \<in> A \<Longrightarrow> z \<le>\<^sub>o\<^sub>w x) \<rbrakk> \<Longrightarrow> z \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w A"
    and Sup_upper: "\<lbrakk> x \<in> A; A \<subseteq> U \<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w A"
    and Sup_least: 
      "\<lbrakk> A \<subseteq> U; z \<in> U; (\<And>x. x \<in> A \<Longrightarrow> x \<le>\<^sub>o\<^sub>w z) \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w z"
    and Inf_empty[simp]: "\<Sqinter>\<^sub>o\<^sub>w {} = \<top>\<^sub>o\<^sub>w"
    and Sup_empty[simp]: "\<Squnion>\<^sub>o\<^sub>w {} = \<bottom>\<^sub>o\<^sub>w"
begin

sublocale bounded_lattice_ow U \<open>(\<sqinter>\<^sub>o\<^sub>w)\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> \<open>(\<squnion>\<^sub>o\<^sub>w)\<close> \<open>\<bottom>\<^sub>o\<^sub>w\<close> \<open>\<top>\<^sub>o\<^sub>w\<close>
  apply standard
  subgoal using Sup_least by force
  subgoal using Inf_greatest by fastforce
  done

tts_register_sbts \<open>\<bottom>\<^sub>o\<^sub>w\<close> | U
proof-
  assume ALA: "Domainp ALA = (\<lambda>x. x \<in> U)" 
  have "Domainp ALA \<bottom>\<^sub>o\<^sub>w" unfolding ALA by simp
  then obtain bot' where "ALA \<bottom>\<^sub>o\<^sub>w bot'" by blast
  then show "\<exists>bot'. ALA \<bottom>\<^sub>o\<^sub>w bot'" by auto
qed

tts_register_sbts \<open>\<top>\<^sub>o\<^sub>w\<close> | U
proof-
  assume ALA: "Domainp ALA = (\<lambda>x. x \<in> U)" 
  have "Domainp ALA \<top>\<^sub>o\<^sub>w" unfolding ALA by simp
  then obtain top' where "ALA \<top>\<^sub>o\<^sub>w top'" by blast
  then show "\<exists>top'. ALA \<top>\<^sub>o\<^sub>w top'" by auto
qed

end

locale complete_lattice_pair_ow = 
  cl\<^sub>1: complete_lattice_ow U\<^sub>1 Inf\<^sub>1 Sup\<^sub>1 inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 bot\<^sub>1 top\<^sub>1 + 
  cl\<^sub>2: complete_lattice_ow U\<^sub>2 Inf\<^sub>2 Sup\<^sub>2 inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2 bot\<^sub>2 top\<^sub>2 
  for U\<^sub>1 :: "'al set" and Inf\<^sub>1 Sup\<^sub>1 inf\<^sub>1 le\<^sub>1 ls\<^sub>1 sup\<^sub>1 bot\<^sub>1 top\<^sub>1
    and U\<^sub>2 :: "'bl set" and Inf\<^sub>2 Sup\<^sub>2 inf\<^sub>2 le\<^sub>2 ls\<^sub>2 sup\<^sub>2 bot\<^sub>2 top\<^sub>2
begin

sublocale bounded_lattice_pair_ow ..
sublocale Inf_pair_ow ..
sublocale Sup_pair_ow ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma complete_lattice_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (rel_set A ===> A) ===> 
      (rel_set A ===> A) ===>
      (A ===> A ===> A) ===>
      (A ===> A ===> (=)) ===>
      (A ===> A ===> (=)) ===>
      (A ===> A ===> A) ===> 
      A ===> A ===>
      (=)
    )
    (complete_lattice_ow (Collect (Domainp A))) class.complete_lattice"
proof-
  let ?P = 
    "(
      (rel_set A ===> A) ===> 
      (rel_set A ===> A) ===>
      (A ===> A ===> A) ===>
      (A ===> A ===> (=)) ===>
      (A ===> A ===> (=)) ===>
      (A ===> A ===> A) ===> 
      A ===> A ===>
      (=)
    )"
  let ?complete_lattice_ow = "(complete_lattice_ow (Collect (Domainp A)))"
  let ?Inf_Sup_UNIV = 
    "(\<lambda>F'::'b set \<Rightarrow> 'b. (F' ` Pow UNIV \<subseteq> UNIV))"
  have rrng:
    "((A2 \<and> A3 \<and> A4 \<and> A5 \<and> A1 \<and> A6 \<and> A7 \<and> A8 \<and> A9 \<and> A10 \<and> A11) = F') \<Longrightarrow>
    ((A1 \<and> A2 \<and> A3 \<and> A4 \<and> A5 \<and> A6 \<and> A7 \<and> A8 \<and> A9 \<and> A10 \<and> A11) = F')"
    for A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 F'
    by auto
  have 
    "?P 
      ?complete_lattice_ow
      (
        \<lambda>Inf Sup inf le ls sup bot top. 
          ?Inf_Sup_UNIV Inf \<and> ?Inf_Sup_UNIV Sup \<and> bot \<in> UNIV \<and> top \<in> UNIV \<and>
          class.complete_lattice Inf Sup inf le ls sup bot top
      )"
    unfolding 
      complete_lattice_ow_def class.complete_lattice_def
      complete_lattice_ow_axioms_def class.complete_lattice_axioms_def
      Inf_ow_def Sup_ow_def bot_ow_def top_ow_def
    apply transfer_prover_start
    apply transfer_step+
    apply(simp, intro ext, rule rrng, intro arg_cong2[where f="(\<and>)"])
    subgoal unfolding Ball_Collect by simp
    subgoal unfolding Ball_Collect by simp
    subgoal by simp
    subgoal by simp
    subgoal by simp
    subgoal unfolding Ball_Collect[symmetric] by auto
    subgoal unfolding Ball_Collect[symmetric] by metis
    subgoal unfolding Ball_Collect[symmetric] by auto
    subgoal unfolding Ball_Collect[symmetric] by metis
    subgoal by simp
    subgoal by simp
    done
  then show ?thesis by simp
qed
  
end


subsubsection\<open>Relativization\<close>

context complete_lattice_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating \<open>?a \<in> ?A\<close> and \<open>?A \<subseteq> ?B\<close> through auto
  applying [OF Inf_closed' Sup_closed' inf_closed' sup_closed']
begin

tts_lemma Inf_atLeast:
  assumes "x \<in> U"
  shows "\<Sqinter>\<^sub>o\<^sub>w {x..\<^sub>o\<^sub>w} = x"
  is complete_lattice_class.Inf_atLeast.
    
tts_lemma Inf_atMost:
  assumes "x \<in> U"
  shows "\<Sqinter>\<^sub>o\<^sub>w {..\<^sub>o\<^sub>wx} = \<bottom>\<^sub>o\<^sub>w"
    is complete_lattice_class.Inf_atMost.
    
tts_lemma Sup_atLeast:
  assumes "x \<in> U"
  shows "\<Squnion>\<^sub>o\<^sub>w {x..\<^sub>o\<^sub>w} = \<top>\<^sub>o\<^sub>w"
  is complete_lattice_class.Sup_atLeast.
    
tts_lemma Sup_atMost:
  assumes "y \<in> U"
  shows "\<Squnion>\<^sub>o\<^sub>w {..\<^sub>o\<^sub>wy} = y"
    is complete_lattice_class.Sup_atMost.
    
tts_lemma Inf_insert:
  assumes "a \<in> U" and "A \<subseteq> U"
  shows "\<Sqinter>\<^sub>o\<^sub>w (insert a A) = a \<sqinter>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w A"
    is complete_lattice_class.Inf_insert.
    
tts_lemma Sup_insert:
  assumes "a \<in> U" and "A \<subseteq> U"
  shows "\<Squnion>\<^sub>o\<^sub>w (insert a A) = a \<squnion>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w A"
    is complete_lattice_class.Sup_insert.
    
tts_lemma Inf_atMostLessThan:
  assumes "x \<in> U" and "\<top>\<^sub>o\<^sub>w <\<^sub>o\<^sub>w x"
  shows "\<Sqinter>\<^sub>o\<^sub>w {..<\<^sub>o\<^sub>wx} = \<bottom>\<^sub>o\<^sub>w"
    is complete_lattice_class.Inf_atMostLessThan.
    
tts_lemma Sup_greaterThanAtLeast:
  assumes "x \<in> U" and "x <\<^sub>o\<^sub>w \<top>\<^sub>o\<^sub>w"
  shows "\<Squnion>\<^sub>o\<^sub>w {x<\<^sub>o\<^sub>w..} = \<top>\<^sub>o\<^sub>w"
    is complete_lattice_class.Sup_greaterThanAtLeast.
    
tts_lemma le_Inf_iff:
  assumes "b \<in> U" and "A \<subseteq> U"
  shows "(b \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w A) = Ball A ((\<le>\<^sub>o\<^sub>w) b)"
    is complete_lattice_class.le_Inf_iff.
    
tts_lemma Sup_le_iff:
  assumes "A \<subseteq> U" and "b \<in> U"
  shows "(\<Squnion>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w b) = (\<forall>x\<in>A. x \<le>\<^sub>o\<^sub>w b)"
    is complete_lattice_class.Sup_le_iff.
    
tts_lemma Inf_atLeastLessThan:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "\<Sqinter>\<^sub>o\<^sub>w (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {x..<y}) = x"
    is complete_lattice_class.Inf_atLeastLessThan.
    
tts_lemma Sup_greaterThanAtMost:
  assumes "x \<in> U" and "y \<in> U" and "x <\<^sub>o\<^sub>w y"
  shows "\<Squnion>\<^sub>o\<^sub>w {x<\<^sub>o\<^sub>w..y} = y"
    is complete_lattice_class.Sup_greaterThanAtMost.
    
tts_lemma Inf_atLeastAtMost:
  assumes "x \<in> U" and "y \<in> U" and "x \<le>\<^sub>o\<^sub>w y"
  shows "\<Sqinter>\<^sub>o\<^sub>w {x..\<^sub>o\<^sub>wy} = x"
is complete_lattice_class.Inf_atLeastAtMost.
    
tts_lemma Sup_atLeastAtMost:
  assumes "x \<in> U" and "y \<in> U" and "x \<le>\<^sub>o\<^sub>w y"
  shows "\<Squnion>\<^sub>o\<^sub>w {x..\<^sub>o\<^sub>wy} = y"
    is complete_lattice_class.Sup_atLeastAtMost.
    
tts_lemma Inf_lower2:
  assumes "A \<subseteq> U" and "v \<in> U" and "u \<in> A" and "u \<le>\<^sub>o\<^sub>w v"
  shows "\<Sqinter>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w v"
  is complete_lattice_class.Inf_lower2.
    
tts_lemma Sup_upper2:
  assumes "A \<subseteq> U" and "v \<in> U" and "u \<in> A" and "v \<le>\<^sub>o\<^sub>w u"
  shows "v \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w A"
    is complete_lattice_class.Sup_upper2.
    
tts_lemma Inf_less_eq:
  assumes "A \<subseteq> U" and "u \<in> U" and "\<And>v. v \<in> A \<Longrightarrow> v \<le>\<^sub>o\<^sub>w u" and "A \<noteq> {}"
  shows "\<Sqinter>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w u"
  given complete_lattice_class.Inf_less_eq by auto

tts_lemma less_eq_Sup:
  assumes "A \<subseteq> U" and "u \<in> U" and "\<And>v. v \<in> A \<Longrightarrow> u \<le>\<^sub>o\<^sub>w v" and "A \<noteq> {}"
  shows "u \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w A"
  given complete_lattice_class.less_eq_Sup by auto

tts_lemma Sup_eqI:
  assumes "A \<subseteq> U"
    and "x \<in> U"
    and "\<And>y. y \<in> A \<Longrightarrow> y \<le>\<^sub>o\<^sub>w x"
    and "\<And>y. \<lbrakk>y \<in> U; \<And>z. z \<in> A \<Longrightarrow> z \<le>\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w y"
  shows "\<Squnion>\<^sub>o\<^sub>w A = x"
    given complete_lattice_class.Sup_eqI
    by (simp add: Sup_least Sup_upper order.antisym)
    
tts_lemma Inf_eqI:
  assumes "A \<subseteq> U"
    and "x \<in> U"
    and "\<And>i. i \<in> A \<Longrightarrow> x \<le>\<^sub>o\<^sub>w i"
    and "\<And>y. \<lbrakk>y \<in> U; \<And>i. i \<in> A \<Longrightarrow> y \<le>\<^sub>o\<^sub>w i\<rbrakk> \<Longrightarrow> y \<le>\<^sub>o\<^sub>w x"
  shows "\<Sqinter>\<^sub>o\<^sub>w A = x"
    given complete_lattice_class.Inf_eqI 
  by (simp add: subset_eq)

tts_lemma Inf_union_distrib:
  assumes "A \<subseteq> U" and "B \<subseteq> U"
  shows "\<Sqinter>\<^sub>o\<^sub>w (A \<union> B) = \<Sqinter>\<^sub>o\<^sub>w A \<sqinter>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w B"
    is complete_lattice_class.Inf_union_distrib.

tts_lemma Sup_union_distrib:
  assumes "A \<subseteq> U" and "B \<subseteq> U"
  shows "\<Squnion>\<^sub>o\<^sub>w (A \<union> B) = \<Squnion>\<^sub>o\<^sub>w A \<squnion>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w B"
    is complete_lattice_class.Sup_union_distrib.

tts_lemma Sup_inter_less_eq:
  assumes "A \<subseteq> U" and "B \<subseteq> U"
  shows "\<Squnion>\<^sub>o\<^sub>w (A \<inter> B) \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w A \<sqinter>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w B"
    is complete_lattice_class.Sup_inter_less_eq.

tts_lemma less_eq_Inf_inter:
  assumes "A \<subseteq> U" and "B \<subseteq> U"
  shows "\<Sqinter>\<^sub>o\<^sub>w A \<squnion>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w B \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (A \<inter> B)"
    is complete_lattice_class.less_eq_Inf_inter.

tts_lemma Sup_subset_mono:
  assumes "B \<subseteq> U" and "A \<subseteq> B"
  shows "\<Squnion>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w B"
    is complete_lattice_class.Sup_subset_mono.

tts_lemma Inf_superset_mono:
  assumes "A \<subseteq> U" and "B \<subseteq> A"
  shows "\<Sqinter>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w B"
    is complete_lattice_class.Inf_superset_mono.

tts_lemma Sup_bot_conv:
  assumes "A \<subseteq> U" 
  shows 
    "(\<Squnion>\<^sub>o\<^sub>w A = \<bottom>\<^sub>o\<^sub>w) = (\<forall>x\<in>A. x = \<bottom>\<^sub>o\<^sub>w)"
    "(\<bottom>\<^sub>o\<^sub>w = \<Squnion>\<^sub>o\<^sub>w A) = (\<forall>x\<in>A. x = \<bottom>\<^sub>o\<^sub>w)"
    is complete_lattice_class.Sup_bot_conv.

tts_lemma Inf_top_conv:
  assumes "A \<subseteq> U"
  shows 
    "(\<Sqinter>\<^sub>o\<^sub>w A = \<top>\<^sub>o\<^sub>w) = (\<forall>x\<in>A. x = \<top>\<^sub>o\<^sub>w)" 
    "(\<top>\<^sub>o\<^sub>w = \<Sqinter>\<^sub>o\<^sub>w A) = (\<forall>x\<in>A. x = \<top>\<^sub>o\<^sub>w)"
    is complete_lattice_class.Inf_top_conv.

tts_lemma Inf_le_Sup:
  assumes "A \<subseteq> U" and "A \<noteq> {}"
  shows "\<Sqinter>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w A"
    is complete_lattice_class.Inf_le_Sup.

tts_lemma INF_UNIV_bool_expand:
  assumes "range A \<subseteq> U"
  shows "\<Sqinter>\<^sub>o\<^sub>w (range A) = A True \<sqinter>\<^sub>o\<^sub>w A False"
    is complete_lattice_class.INF_UNIV_bool_expand.

tts_lemma SUP_UNIV_bool_expand:
  assumes "range A \<subseteq> U"
  shows "\<Squnion>\<^sub>o\<^sub>w (range A) = A True \<squnion>\<^sub>o\<^sub>w A False"
    is complete_lattice_class.SUP_UNIV_bool_expand.

tts_lemma Sup_mono:
  assumes "A \<subseteq> U" and "B \<subseteq> U" and "\<And>a. a \<in> A \<Longrightarrow> Bex B ((\<le>\<^sub>o\<^sub>w) a)"
  shows "\<Squnion>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w B"
    given complete_lattice_class.Sup_mono by simp

tts_lemma Inf_mono:
  assumes "B \<subseteq> U"
    and "A \<subseteq> U"
    and "\<And>b. b \<in> B \<Longrightarrow> \<exists>x\<in>A. x \<le>\<^sub>o\<^sub>w b"
  shows "\<Sqinter>\<^sub>o\<^sub>w A \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w B"
    given complete_lattice_class.Inf_mono by simp

tts_lemma Sup_Inf_le:
  assumes "A \<subseteq> Pow U"
  shows "\<Squnion>\<^sub>o\<^sub>w 
    (
      \<Sqinter>\<^sub>o\<^sub>w ` {x. x \<subseteq> U \<and> (\<exists>f\<in>{f. f ` Pow U \<subseteq> U}. x = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y))}
    ) \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (\<Squnion>\<^sub>o\<^sub>w ` A)"
    is complete_lattice_class.Sup_Inf_le.

end

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty 
  applying [
    OF Inf_closed' Sup_closed' inf_closed' sup_closed' bot_closed top_closed
    ]
begin

tts_lemma Inf_UNIV: "\<Sqinter>\<^sub>o\<^sub>w U = \<bottom>\<^sub>o\<^sub>w"
    is complete_lattice_class.Inf_UNIV.

tts_lemma Sup_UNIV: "\<Squnion>\<^sub>o\<^sub>w U = \<top>\<^sub>o\<^sub>w"
    is complete_lattice_class.Sup_UNIV.

end

context 
  fixes U\<^sub>2 :: "'b set"
begin

lemmas [transfer_rule] =
  image_transfer[where ?'a='b]

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through (insert Sup_least, auto)
begin

tts_lemma SUP_upper2:
  assumes "A \<subseteq> U\<^sub>2"
    and "u \<in> U"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "i \<in> A"
    and "u \<le>\<^sub>o\<^sub>w f i"
  shows "u \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (f ` A)"
  is complete_lattice_class.SUP_upper2.

tts_lemma INF_lower2:
  assumes "A \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "u \<in> U"
    and "i \<in> A"
    and "f i \<le>\<^sub>o\<^sub>w u"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w u"
  is complete_lattice_class.INF_lower2.
    
tts_lemma less_INF_D:
  assumes "y \<in> U"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "A \<subseteq> U\<^sub>2"
    and "y <\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (f ` A)"
    and "i \<in> A"
  shows "y <\<^sub>o\<^sub>w f i"
  is complete_lattice_class.less_INF_D.
    
tts_lemma SUP_lessD:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "A \<subseteq> U\<^sub>2"
    and "y \<in> U"
    and "\<Squnion>\<^sub>o\<^sub>w (f ` A) <\<^sub>o\<^sub>w y"
    and "i \<in> A"
  shows "f i <\<^sub>o\<^sub>w y"
  is complete_lattice_class.SUP_lessD.

tts_lemma SUP_le_iff:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "A \<subseteq> U\<^sub>2" and "u \<in> U"
  shows "(\<Squnion>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w u) = (\<forall>x\<in>A. f x \<le>\<^sub>o\<^sub>w u)"
    is complete_lattice_class.SUP_le_iff.

end

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through (auto dest: top_le)
begin

tts_lemma INF_eqI:
  assumes "A \<subseteq> U\<^sub>2"
    and "x \<in> U"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "\<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> A\<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w f i"
    and "\<And>y. \<lbrakk>y \<in> U; \<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> A\<rbrakk> \<Longrightarrow> y \<le>\<^sub>o\<^sub>w f i\<rbrakk> \<Longrightarrow> y \<le>\<^sub>o\<^sub>w x"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) = x"
  is complete_lattice_class.INF_eqI.

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through (auto simp: sup_bot.eq_iff)
begin

tts_lemma SUP_eqI:
  assumes "A \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "x \<in> U"
    and "\<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> A\<rbrakk> \<Longrightarrow> f i \<le>\<^sub>o\<^sub>w x"
    and "\<And>y. \<lbrakk>y \<in> U; \<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> A\<rbrakk> \<Longrightarrow> f i \<le>\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w y"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` A) = x"
    is complete_lattice_class.SUP_eqI.
    
end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through simp
begin

tts_lemma INF_le_SUP:
  assumes "A \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "A \<noteq> {}"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (f ` A)"
  is complete_lattice_class.INF_le_SUP.
    
tts_lemma INF_inf_const1:
  assumes "I \<subseteq> U\<^sub>2" and "x \<in> U" and "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "I \<noteq> {}"
  shows "\<Sqinter>\<^sub>o\<^sub>w ((\<lambda>i. x \<sqinter>\<^sub>o\<^sub>w f i) ` I) = x \<sqinter>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (f ` I)"
    is complete_lattice_class.INF_inf_const1.
    
tts_lemma INF_inf_const2:
  assumes "I \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "x \<in> U" and "I \<noteq> {}"
  shows "\<Sqinter>\<^sub>o\<^sub>w ((\<lambda>i. f i \<sqinter>\<^sub>o\<^sub>w x) ` I) = \<Sqinter>\<^sub>o\<^sub>w (f ` I) \<sqinter>\<^sub>o\<^sub>w x"
    is complete_lattice_class.INF_inf_const2.    

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through auto
begin

tts_lemma INF_eq_const:
  assumes "I \<subseteq> U\<^sub>2" 
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U" 
    and "I \<noteq> {}"
    and "\<And>i. i \<in> I \<Longrightarrow> f i = x"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` I) = x"
    given complete_lattice_class.INF_eq_const
proof-
  assume 
    "\<lbrakk>I \<subseteq> U\<^sub>2; \<forall>x\<in>U\<^sub>2. f x \<in> U; I \<noteq> {}; \<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> I\<rbrakk> \<Longrightarrow> f i = x\<rbrakk> \<Longrightarrow> 
      \<Sqinter>\<^sub>o\<^sub>w (f ` I) = x"
    for I :: "'a set" and U\<^sub>2 f x
  then have 
    "\<lbrakk>I \<subseteq> U\<^sub>2; \<forall>x\<in>U\<^sub>2. f x \<in> U; I \<noteq> {}; \<And>i. i \<in> I \<Longrightarrow> f i = x\<rbrakk> \<Longrightarrow> 
      \<Sqinter>\<^sub>o\<^sub>w (f ` I) = x"
    by presburger
  then show "\<Sqinter>\<^sub>o\<^sub>w (f ` I) = x" using assms by simp
qed
    
tts_lemma SUP_eq_const:
  assumes "I \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "I \<noteq> {}"
    and "\<And>i. i \<in> I \<Longrightarrow> f i = x"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` I) = x"
    given complete_lattice_class.SUP_eq_const
proof-
  assume 
    "\<lbrakk>I \<subseteq> U\<^sub>2; \<forall>x\<in>U\<^sub>2. f x \<in> U; I \<noteq> {}; \<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> I\<rbrakk> \<Longrightarrow> f i = x\<rbrakk> \<Longrightarrow> 
      \<Squnion>\<^sub>o\<^sub>w (f ` I) = x"
    for I :: "'a set" and U\<^sub>2 f x
  then have 
    "\<lbrakk>I \<subseteq> U\<^sub>2; \<forall>x\<in>U\<^sub>2. f x \<in> U; I \<noteq> {}; \<And>i. i \<in> I \<Longrightarrow> f i = x\<rbrakk> \<Longrightarrow> 
      \<Squnion>\<^sub>o\<^sub>w (f ` I) = x"
    by presburger
  then show "\<Squnion>\<^sub>o\<^sub>w (f ` I) = x" using assms by simp
qed
    
tts_lemma SUP_eq_iff:
  assumes "I \<subseteq> U\<^sub>2"
    and "c \<in> U"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "I \<noteq> {}"
    and "\<And>i. i \<in> I \<Longrightarrow> c \<le>\<^sub>o\<^sub>w f i"
  shows "(\<Squnion>\<^sub>o\<^sub>w (f ` I) = c) = (\<forall>x\<in>I. f x = c)"
    given complete_lattice_class.SUP_eq_iff
proof-
  assume 
    "\<lbrakk>
      I \<subseteq> U\<^sub>2; 
      c \<in> U; \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      I \<noteq> {}; 
      \<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> I\<rbrakk> \<Longrightarrow> c \<le>\<^sub>o\<^sub>w f i
    \<rbrakk> \<Longrightarrow>  (\<Squnion>\<^sub>o\<^sub>w (f ` I) = c) = (\<forall>x\<in>I. f x = c)"
    for I :: "'a set" and U\<^sub>2 c f
  then have 
    "\<lbrakk>
      I \<subseteq> U\<^sub>2; 
      c \<in> U; \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      I \<noteq> {}; 
      \<And>i. i \<in> I \<Longrightarrow> c \<le>\<^sub>o\<^sub>w f i
    \<rbrakk> \<Longrightarrow> (\<Squnion>\<^sub>o\<^sub>w (f ` I) = c) = (\<forall>x\<in>I. f x = c)"
    by presburger
  then show "(\<Squnion>\<^sub>o\<^sub>w (f ` I) = c) = (\<forall>x\<in>I. f x = c)" using assms by auto
qed
    
tts_lemma INF_eq_iff:
  assumes "I \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "c \<in> U"
    and "I \<noteq> {}"
    and "\<And>i. i \<in> I \<Longrightarrow> f i \<le>\<^sub>o\<^sub>w c"
  shows "(\<Sqinter>\<^sub>o\<^sub>w (f ` I) = c) = (\<forall>x\<in>I. f x = c)"
    given complete_lattice_class.INF_eq_iff
proof-
  assume 
    "\<lbrakk>
      I \<subseteq> U\<^sub>2; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; c \<in> U; 
      I \<noteq> {}; 
      \<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> I\<rbrakk> \<Longrightarrow> f i \<le>\<^sub>o\<^sub>w c
    \<rbrakk> \<Longrightarrow> (\<Sqinter>\<^sub>o\<^sub>w (f ` I) = c) = (\<forall>x\<in>I. f x = c)"
    for I :: "'a set" and U\<^sub>2 f c
  then have 
    "\<lbrakk>
      I \<subseteq> U\<^sub>2; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; c \<in> U; 
      I \<noteq> {}; 
      \<And>i. i \<in> I \<Longrightarrow> f i \<le>\<^sub>o\<^sub>w c
    \<rbrakk> \<Longrightarrow> (\<Sqinter>\<^sub>o\<^sub>w (f ` I) = c) = (\<forall>x\<in>I. f x = c)"
    by presburger
  then show "(\<Sqinter>\<^sub>o\<^sub>w (f ` I) = c) = (\<forall>x\<in>I. f x = c)" using assms by auto
qed

end


context 
  fixes U\<^sub>2 :: "'b set"
begin

lemmas [transfer_rule] =
  image_transfer[where ?'a='b]

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through (auto simp: sup_bot.top_unique top_le intro: Sup_least)
begin

tts_lemma INF_insert:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "a \<in> U\<^sub>2" and "A \<subseteq> U\<^sub>2"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` insert a A) = f a \<sqinter>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (f ` A)"
  is complete_lattice_class.INF_insert.
    
tts_lemma SUP_insert:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "a \<in> U\<^sub>2" and "A \<subseteq> U\<^sub>2"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` insert a A) = f a \<squnion>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (f ` A)"
    is complete_lattice_class.SUP_insert.
    
tts_lemma le_INF_iff:
  assumes "u \<in> U" and "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "A \<subseteq> U\<^sub>2"
  shows "(u \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (f ` A)) = (\<forall>x\<in>A. u \<le>\<^sub>o\<^sub>w f x)"
  is complete_lattice_class.le_INF_iff.
    
tts_lemma INF_union:
  assumes "\<forall>x\<in>U\<^sub>2. M x \<in> U" and "A \<subseteq> U\<^sub>2" and "B \<subseteq> U\<^sub>2"
  shows "\<Sqinter>\<^sub>o\<^sub>w (M ` (A \<union> B)) = \<Sqinter>\<^sub>o\<^sub>w (M ` A) \<sqinter>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (M ` B)"
    is complete_lattice_class.INF_union.
    
tts_lemma SUP_union:
  assumes "\<forall>x\<in>U\<^sub>2. M x \<in> U" and "A \<subseteq> U\<^sub>2" and "B \<subseteq> U\<^sub>2"
  shows "\<Squnion>\<^sub>o\<^sub>w (M ` (A \<union> B)) = \<Squnion>\<^sub>o\<^sub>w (M ` A) \<squnion>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (M ` B)"
  is complete_lattice_class.SUP_union.
    
tts_lemma SUP_bot_conv:
  assumes "\<forall>x\<in>U\<^sub>2. B x \<in> U" and "A \<subseteq> U\<^sub>2"
  shows 
    "(\<Squnion>\<^sub>o\<^sub>w (B ` A) = \<bottom>\<^sub>o\<^sub>w) = (\<forall>x\<in>A. B x = \<bottom>\<^sub>o\<^sub>w)"
    "(\<bottom>\<^sub>o\<^sub>w = \<Squnion>\<^sub>o\<^sub>w (B ` A)) = (\<forall>x\<in>A. B x = \<bottom>\<^sub>o\<^sub>w)"
  is complete_lattice_class.SUP_bot_conv.
    
tts_lemma INF_top_conv:
  assumes "\<forall>x\<in>U\<^sub>2. B x \<in> U" and "A \<subseteq> U\<^sub>2"
  shows 
    "(\<Sqinter>\<^sub>o\<^sub>w (B ` A) = \<top>\<^sub>o\<^sub>w) = (\<forall>x\<in>A. B x = \<top>\<^sub>o\<^sub>w)"
    "(\<top>\<^sub>o\<^sub>w = \<Sqinter>\<^sub>o\<^sub>w (B ` A)) = (\<forall>x\<in>A. B x = \<top>\<^sub>o\<^sub>w)"
  is complete_lattice_class.INF_top_conv.
    
tts_lemma SUP_upper:
  assumes "A \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "i \<in> A"
  shows "f i \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (f ` A)"
  is complete_lattice_class.SUP_upper.
    
tts_lemma INF_lower:
  assumes "A \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "i \<in> A"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w f i"
  is complete_lattice_class.INF_lower.

tts_lemma INF_inf_distrib:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "A \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. g x \<in> U"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) \<sqinter>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (g ` A) = \<Sqinter>\<^sub>o\<^sub>w ((\<lambda>a. f a \<sqinter>\<^sub>o\<^sub>w g a) ` A)"
    is complete_lattice_class.INF_inf_distrib.

tts_lemma SUP_sup_distrib:
  assumes "\<forall>x\<in>U\<^sub>2. f x \<in> U" and "A \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. g x \<in> U"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` A) \<squnion>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (g ` A) = \<Squnion>\<^sub>o\<^sub>w ((\<lambda>a. f a \<squnion>\<^sub>o\<^sub>w g a) ` A)"
    is complete_lattice_class.SUP_sup_distrib.

tts_lemma SUP_subset_mono:
  assumes "B \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "\<forall>x\<in>U\<^sub>2. g x \<in> U"
    and "A \<subseteq> B"
    and "\<And>x. x \<in> A \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w g x"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (g ` B)"
    given complete_lattice_class.SUP_subset_mono
proof-
  assume 
    "\<lbrakk>
      B \<subseteq> U\<^sub>2; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      \<forall>x\<in>U\<^sub>2. g x \<in> U; 
      A \<subseteq> B; 
      \<And>x. \<lbrakk>x \<in> U\<^sub>2; x \<in> A\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w g x
    \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (g ` B)"
    for B :: "'b set" and f g A
  then have
    "\<lbrakk>
      B \<subseteq> U\<^sub>2; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      \<forall>x\<in>U\<^sub>2. g x \<in> U; 
      A \<subseteq> B; 
      \<And>x. x \<in> A \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w g x
    \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (g ` B)"
    by auto
  then show "\<Squnion>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (g ` B)" using assms by blast
qed

tts_lemma INF_superset_mono:
  assumes "A \<subseteq> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U"
    and "\<forall>x\<in>U\<^sub>2. g x \<in> U"
    and "B \<subseteq> A"
    and "\<And>x. \<lbrakk>x \<in> U\<^sub>2; x \<in> B\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w g x"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (g ` B)"
    given complete_lattice_class.INF_superset_mono
proof-
  assume 
    "\<lbrakk>
      A \<subseteq> U\<^sub>2; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      \<forall>x\<in>U\<^sub>2. g x \<in> U; 
      B \<subseteq> A; 
      \<And>x. \<lbrakk>x \<in> U\<^sub>2; x \<in> B\<rbrakk> \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w g x
    \<rbrakk> \<Longrightarrow> \<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (g ` B)"
    for A :: "'b set" and f g B
  then have
    "\<lbrakk>
      A \<subseteq> U\<^sub>2; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      \<forall>x\<in>U\<^sub>2. g x \<in> U; 
      B \<subseteq> A; 
      \<And>x. x \<in> B \<Longrightarrow> f x \<le>\<^sub>o\<^sub>w g x
    \<rbrakk> \<Longrightarrow> \<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (g ` B)"
    by auto
  then show "\<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (g ` B)" using assms by blast
qed

tts_lemma INF_absorb:
  assumes "I \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. A x \<in> U" and "k \<in> I"
  shows "A k \<sqinter>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (A ` I) = \<Sqinter>\<^sub>o\<^sub>w (A ` I)"
    is complete_lattice_class.INF_absorb.

tts_lemma SUP_absorb:
  assumes "I \<subseteq> U\<^sub>2" and "\<forall>x\<in>U\<^sub>2. A x \<in> U" and "k \<in> I"
  shows "A k \<squnion>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (A ` I) = \<Squnion>\<^sub>o\<^sub>w (A ` I)"
    is complete_lattice_class.SUP_absorb.

end

end

context 
  fixes f :: "'b \<Rightarrow> 'al" and U\<^sub>2 :: "'b set"
  assumes f[transfer_rule]: "\<forall>x \<in> U\<^sub>2. f x = \<bottom>\<^sub>o\<^sub>w"
begin

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  sbterms: (\<open>Orderings.bot::?'a::complete_lattice\<close> to \<open>\<bottom>\<^sub>o\<^sub>w\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through simp
begin

tts_lemma SUP_bot:
  assumes "A \<subseteq> U\<^sub>2"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` A) = \<bottom>\<^sub>o\<^sub>w"
    is complete_lattice_class.SUP_bot[folded const_fun_def].

end

end

context 
  fixes f :: "'b \<Rightarrow> 'al" and U\<^sub>2 :: "'b set"
  assumes f[transfer_rule]: "\<forall>x \<in> U\<^sub>2. f x = \<top>\<^sub>o\<^sub>w"
begin

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  sbterms: (\<open>Orderings.top::?'a::complete_lattice\<close> to \<open>\<top>\<^sub>o\<^sub>w\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through simp
begin

tts_lemma INF_top:
  assumes "A \<subseteq> U\<^sub>2"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) = \<top>\<^sub>o\<^sub>w"
  is complete_lattice_class.INF_top[folded const_fun_def].

end

end

context 
  fixes f :: "'b \<Rightarrow> 'al" and c and F and U\<^sub>2 :: "'b set"
  assumes c_closed[transfer_rule]: "c \<in> U"
  assumes f[transfer_rule]: "\<forall>x \<in> U\<^sub>2. f x = c"
begin

tts_register_sbts \<open>c\<close> | U
proof-
  assume ALC: "Domainp ALC = (\<lambda>x. x \<in> U)" 
  have "Domainp ALC c" unfolding ALC by (simp add: c_closed)
  then obtain c' where "ALC c c'" by blast
  then show "\<exists>c'. ALC c c'" by auto
qed

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  sbterms: (\<open>?c::?'a::complete_lattice\<close> to \<open>c\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through simp
begin

tts_lemma INF_constant:
  assumes "A \<subseteq> U\<^sub>2"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) = (if A = {} then \<top>\<^sub>o\<^sub>w else c)"
    is complete_lattice_class.INF_constant[folded const_fun_def].

tts_lemma SUP_constant:
  assumes "A \<subseteq> U\<^sub>2"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` A) = (if A = {} then \<bottom>\<^sub>o\<^sub>w else c)"
    is complete_lattice_class.SUP_constant[folded const_fun_def].

end

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>)
  sbterms: (\<open>?f::?'a::complete_lattice\<close> to \<open>c\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  eliminating through simp
begin

tts_lemma INF_const:
  assumes "A \<subseteq> U\<^sub>2" and "A \<noteq> {}"
  shows "\<Sqinter>\<^sub>o\<^sub>w ((\<lambda>i. c) ` A) = c"
    is complete_lattice_class.INF_const.
    
tts_lemma SUP_const:
  assumes "A \<subseteq> U\<^sub>2" and "A \<noteq> {}"
  shows "\<Squnion>\<^sub>o\<^sub>w ((\<lambda>i. c) ` A) = c"
    is complete_lattice_class.SUP_const.

end

end

end

context complete_lattice_ow
begin

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>) and (?'c to \<open>U\<^sub>3::'c set\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty  
  eliminating \<open>?U \<noteq> {}\<close> through (force simp: subset_iff INF_top equals0D)
  applying [
    OF Inf_closed' Sup_closed' inf_closed' sup_closed' bot_closed top_closed
    ]
begin

tts_lemma SUP_eq:
  assumes "A \<subseteq> U\<^sub>2"
    and "B \<subseteq> U\<^sub>3"
    and "\<forall>x\<in>U\<^sub>2. f (x::'a) \<in> U"
    and "\<forall>x\<in>U\<^sub>3. g x \<in> U"
    and "\<And>i. i \<in> A \<Longrightarrow> \<exists>x\<in>B. f i \<le>\<^sub>o\<^sub>w g x"
    and "\<And>j. j \<in> B \<Longrightarrow> \<exists>x\<in>A. g j \<le>\<^sub>o\<^sub>w f x"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` A) = \<Squnion>\<^sub>o\<^sub>w (g ` B)"
    given complete_lattice_class.SUP_eq
proof-
  assume 
    "\<lbrakk>
      A \<subseteq> U\<^sub>2; 
      B \<subseteq> U\<^sub>3; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      \<forall>x\<in>U\<^sub>3. g x \<in> U; 
      \<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> A\<rbrakk> \<Longrightarrow> \<exists>x\<in>B. f i \<le>\<^sub>o\<^sub>w g x; 
      \<And>j. \<lbrakk>j \<in> U\<^sub>3; j \<in> B\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. g j \<le>\<^sub>o\<^sub>w f x
    \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>o\<^sub>w (f ` A) = \<Squnion>\<^sub>o\<^sub>w (g ` B)"
    for A :: "'a set" and U\<^sub>2 and B :: "'b set" and U\<^sub>3 f g
  then have
    "\<lbrakk>
      A \<subseteq> U\<^sub>2; 
      B \<subseteq> U\<^sub>3; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      \<forall>x\<in>U\<^sub>3. g x \<in> U; 
      \<And>i. i \<in> A \<Longrightarrow> \<exists>x\<in>B. f i \<le>\<^sub>o\<^sub>w g x; 
      \<And>j. j \<in> B \<Longrightarrow> \<exists>x\<in>A. g j \<le>\<^sub>o\<^sub>w f x
    \<rbrakk> \<Longrightarrow> \<Squnion>\<^sub>o\<^sub>w (f ` A) = \<Squnion>\<^sub>o\<^sub>w (g ` B)"
    by simp
  then show "\<Squnion>\<^sub>o\<^sub>w (f ` A) = \<Squnion>\<^sub>o\<^sub>w (g ` B)" using assms by simp
qed

tts_lemma INF_eq:
  assumes "A \<subseteq> U\<^sub>2"
    and "B \<subseteq> U\<^sub>3"
    and "\<forall>x\<in>U\<^sub>3. g x \<in> U"
    and "\<forall>x\<in>U\<^sub>2. f (x::'a) \<in> U"
    and "\<And>i. i \<in> A \<Longrightarrow> \<exists>x\<in>B. g x \<le>\<^sub>o\<^sub>w f i"
    and "\<And>j. j \<in> B \<Longrightarrow> \<exists>x\<in>A. f x \<le>\<^sub>o\<^sub>w g j"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) = \<Sqinter>\<^sub>o\<^sub>w (g ` B)"
    given complete_lattice_class.INF_eq
proof-
  assume 
    "\<lbrakk>
      A \<subseteq> U\<^sub>2; 
      B \<subseteq> U\<^sub>3; 
      \<forall>x\<in>U\<^sub>3. g x \<in> U; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      \<And>i. \<lbrakk>i \<in> U\<^sub>2; i \<in> A\<rbrakk> \<Longrightarrow> \<exists>x\<in>B. g x \<le>\<^sub>o\<^sub>w f i; 
      \<And>j. \<lbrakk>j \<in> U\<^sub>3; j \<in> B\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. f x \<le>\<^sub>o\<^sub>w g j
    \<rbrakk> \<Longrightarrow> \<Sqinter>\<^sub>o\<^sub>w (f ` A) = \<Sqinter>\<^sub>o\<^sub>w (g ` B)"
    for A :: "'a set" and U\<^sub>2 and B :: "'b set" and U\<^sub>3 g f
  then have
    "\<lbrakk>
      A \<subseteq> U\<^sub>2; 
      B \<subseteq> U\<^sub>3; 
      \<forall>x\<in>U\<^sub>3. g x \<in> U; 
      \<forall>x\<in>U\<^sub>2. f x \<in> U; 
      \<And>i. i \<in> A \<Longrightarrow> \<exists>x\<in>B. g x \<le>\<^sub>o\<^sub>w f i; 
      \<And>j. j \<in> B \<Longrightarrow> \<exists>x\<in>A. f x \<le>\<^sub>o\<^sub>w g j
    \<rbrakk> \<Longrightarrow> \<Sqinter>\<^sub>o\<^sub>w (f ` A) = \<Sqinter>\<^sub>o\<^sub>w (g ` B)"
    by simp
  then show "\<Sqinter>\<^sub>o\<^sub>w (f ` A) = \<Sqinter>\<^sub>o\<^sub>w (g ` B)" using assms by simp
qed

end

end

context complete_lattice_ow
begin

context 
  fixes U\<^sub>2 :: "'b set" and U\<^sub>3 :: "'c set"
begin

lemmas [transfer_rule] =
  image_transfer[where ?'a='b]
  image_transfer[where ?'a='c]

tts_context
  tts: (?'a to U) and (?'b to \<open>U\<^sub>2::'b set\<close>) and (?'c to \<open>U\<^sub>3::'c set\<close>)
  rewriting ctr_simps
  substituting complete_lattice_ow_axioms and sup_bot.sl_neut.not_empty
  applying [
    OF _ _ Inf_closed' Sup_closed' inf_closed' sup_closed' bot_closed top_closed
    ]
begin

tts_lemma ne_INF_commute:
  assumes "U\<^sub>2 \<noteq> {}"
    and "U\<^sub>3 \<noteq> {}"
    and "\<forall>x\<in>U\<^sub>2. \<forall>y\<in>U\<^sub>3. f (x::'b) y \<in> U"
    and "B \<subseteq> U\<^sub>3"
    and "A \<subseteq> U\<^sub>2"
  shows "\<Sqinter>\<^sub>o\<^sub>w ((\<lambda>i. \<Sqinter>\<^sub>o\<^sub>w (f i ` B)) ` A) = \<Sqinter>\<^sub>o\<^sub>w ((\<lambda>j. \<Sqinter>\<^sub>o\<^sub>w ((\<lambda>i. f i j) ` A)) ` B)"
    is complete_lattice_class.INF_commute.
    
tts_lemma ne_SUP_commute:
  assumes "U\<^sub>2 \<noteq> {}"
    and "U\<^sub>3 \<noteq> {}"
    and "\<forall>x\<in>U\<^sub>2. \<forall>y\<in>U\<^sub>3. f (x::'b) y \<in> U"
    and "B \<subseteq> U\<^sub>3"
    and "A \<subseteq> U\<^sub>2"
  shows "\<Squnion>\<^sub>o\<^sub>w ((\<lambda>i. \<Squnion>\<^sub>o\<^sub>w (f i ` B)) ` A) = \<Squnion>\<^sub>o\<^sub>w ((\<lambda>j. \<Squnion>\<^sub>o\<^sub>w ((\<lambda>i. f i j) ` A)) ` B)"
    is complete_lattice_class.SUP_commute.
    
tts_lemma ne_SUP_mono:
  assumes "U\<^sub>2 \<noteq> {}"
    and "U\<^sub>3 \<noteq> {}"
    and "A \<subseteq> U\<^sub>2"
    and "B \<subseteq> U\<^sub>3"
    and "\<forall>x\<in>U\<^sub>2. f (x::'b) \<in> U"
    and "\<forall>x\<in>U\<^sub>3. g x \<in> U"
    and "\<And>n. \<lbrakk>n \<in> U\<^sub>2; n \<in> A\<rbrakk> \<Longrightarrow> \<exists>x\<in>B. f n \<le>\<^sub>o\<^sub>w g x"
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (g ` B)"
    is complete_lattice_class.SUP_mono.
    
tts_lemma ne_INF_mono:
  assumes "U\<^sub>2 \<noteq> {}"
    and "U\<^sub>3 \<noteq> {}"
    and "B \<subseteq> U\<^sub>2"
    and "A \<subseteq> U\<^sub>3"
    and "\<forall>x\<in>U\<^sub>3. f x \<in> U"
    and "\<forall>x\<in>U\<^sub>2. g (x::'b) \<in> U"
    and "\<And>m. \<lbrakk>m \<in> U\<^sub>2; m \<in> B\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. f x \<le>\<^sub>o\<^sub>w g m"
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (g ` B)"
    is complete_lattice_class.INF_mono.

end

end

lemma INF_commute:
  assumes "\<forall>x\<in>U\<^sub>2. \<forall>y\<in>U\<^sub>3. f x y \<in> U" and "B \<subseteq> U\<^sub>3" and "A \<subseteq> U\<^sub>2" 
  shows 
    "\<Sqinter>\<^sub>o\<^sub>w ((\<lambda>x. \<Sqinter>\<^sub>o\<^sub>w (f x ` B)) ` A) = \<Sqinter>\<^sub>o\<^sub>w ((\<lambda>j. \<Sqinter>\<^sub>o\<^sub>w ((\<lambda>i. f i j) ` A)) ` B)"
proof(cases \<open>U\<^sub>2 = {}\<close>)
  case True then show ?thesis 
    using assms by (simp add: inf_top.sl_neut.neutral_map Inf_top_conv(2)) 
next
  case ne_U\<^sub>2: False show ?thesis
  proof(cases \<open>U\<^sub>3 = {}\<close>)
    case True show ?thesis
    proof-
      from assms(2) have "B = {}" unfolding True by simp
      from assms(1) show ?thesis 
        unfolding \<open>B = {}\<close> by (force intro: INF_top)
    qed
  next
    case False 
    from ne_U\<^sub>2 False assms show ?thesis by (rule ne_INF_commute)
  qed
qed

lemma SUP_commute:
  assumes "\<forall>x\<in>U\<^sub>2. \<forall>y\<in>U\<^sub>3. f x y \<in> U" and "B \<subseteq> U\<^sub>3" and "A \<subseteq> U\<^sub>2"
  shows 
    "\<Squnion>\<^sub>o\<^sub>w ((\<lambda>x. \<Squnion>\<^sub>o\<^sub>w (f x ` B)) ` A) = \<Squnion>\<^sub>o\<^sub>w ((\<lambda>j. \<Squnion>\<^sub>o\<^sub>w ((\<lambda>i. f i j) ` A)) ` B)"
proof(cases \<open>U\<^sub>2 = {}\<close>)
  case True show ?thesis
  proof-
    from assms(3) have "A = {}" unfolding True by simp
    from assms(2) show ?thesis 
      unfolding \<open>A = {}\<close> 
      by (simp add: sup_bot.sl_neut.neutral_map inf_absorb1 SUP_bot)
  qed
next
  case ne_U\<^sub>2: False show ?thesis
  proof(cases \<open>U\<^sub>3 = {}\<close>)
    case True show ?thesis
    proof-
      from assms(2) have "B = {}" unfolding True by simp
      from assms(1) show ?thesis 
        unfolding \<open>B = {}\<close> 
        by (simp add: sup_bot.sl_neut.neutral_map Sup_bot_conv(1))
    qed
  next
    case False 
    from ne_U\<^sub>2 False assms show ?thesis by (rule ne_SUP_commute)
  qed
qed

lemma SUP_mono:
  assumes "A \<subseteq> U\<^sub>2" 
    and "B \<subseteq> U\<^sub>3" 
    and "\<forall>x\<in>U\<^sub>2. f x \<in> U" 
    and "\<forall>x\<in>U\<^sub>3. g x \<in> U"
    and "\<And>n. n \<in> A \<Longrightarrow> \<exists>m\<in>B. f n \<le>\<^sub>o\<^sub>w g m" 
  shows "\<Squnion>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Squnion>\<^sub>o\<^sub>w (g ` B)"
proof(cases \<open>U\<^sub>2 = {}\<close>)
  case True show ?thesis
  proof-
    from assms(1) have "A = {}" unfolding True by simp
    have "f ` A = {}" unfolding \<open>A = {}\<close> by simp
    from assms(2,4) show ?thesis 
      unfolding \<open>f ` A = {}\<close> by (simp add: image_subset_iff in_mono)
  qed
next
  case ne_U\<^sub>2: False show ?thesis
  proof(cases \<open>U\<^sub>3 = {}\<close>)
    case True show ?thesis
    proof-
      from assms(2) have "B = {}" unfolding True by simp
      have "g ` B = {}" unfolding \<open>B = {}\<close> by simp
      from assms(1,3,5) show ?thesis
        unfolding \<open>g ` B = {}\<close> \<open>B = {}\<close> by (force simp: subset_iff)
    qed
  next
    case False 
    from ne_U\<^sub>2 False assms show ?thesis by (rule ne_SUP_mono)
  qed
qed

lemma INF_mono:
  assumes "B \<subseteq> U\<^sub>2" 
    and "A \<subseteq> U\<^sub>3" 
    and "\<forall>x\<in>U\<^sub>3. f x \<in> U" 
    and "\<forall>x\<in>U\<^sub>2. g x \<in> U"
    and "\<And>m. m \<in> B \<Longrightarrow> \<exists>n\<in>A. f n \<le>\<^sub>o\<^sub>w g m" 
  shows "\<Sqinter>\<^sub>o\<^sub>w (f ` A) \<le>\<^sub>o\<^sub>w \<Sqinter>\<^sub>o\<^sub>w (g ` B)"
proof(cases \<open>U\<^sub>2 = {}\<close>)
  case True show ?thesis
  proof-
    from assms(1) have "B = {}" unfolding True by simp
    have "g ` B = {}" unfolding \<open>B = {}\<close> by simp
    from assms(2,3) show ?thesis 
      unfolding \<open>g ` B = {}\<close> by (simp add: image_subset_iff in_mono)
  qed
next
  case ne_U\<^sub>2: False show ?thesis
  proof(cases \<open>U\<^sub>3 = {}\<close>)
    case True show ?thesis
    proof-
      from assms(2) have "A = {}" unfolding True by simp
      have "f ` A = {}" unfolding \<open>A = {}\<close> by simp
      from assms show ?thesis
        unfolding \<open>f ` A = {}\<close> \<open>A = {}\<close> by (auto simp: subset_iff) fastforce
    qed
  next
    case False from ne_U\<^sub>2 False assms show ?thesis by (rule ne_INF_mono)
  qed                                                              
qed

end

context complete_lattice_pair_ow
begin

tts_context
  tts: (?'a to U\<^sub>1) and (?'b to U\<^sub>2) 
  rewriting ctr_simps
  substituting cl\<^sub>1.complete_lattice_ow_axioms
    and cl\<^sub>2.complete_lattice_ow_axioms
    and cl\<^sub>1.inf_top.sl_neut.not_empty
    and cl\<^sub>2.inf_top.sl_neut.not_empty
  applying 
    [
      OF 
        cl\<^sub>1.Inf_closed' 
        cl\<^sub>1.Sup_closed' 
        cl\<^sub>1.inf_closed'   
        cl\<^sub>1.sup_closed'
        cl\<^sub>1.bot_closed
        cl\<^sub>1.top_closed
        cl\<^sub>2.Inf_closed' 
        cl\<^sub>2.Sup_closed' 
        cl\<^sub>2.inf_closed'   
        cl\<^sub>2.sup_closed'
        cl\<^sub>2.bot_closed
        cl\<^sub>2.top_closed
    ]
begin

tts_lemma mono_Inf:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "A \<subseteq> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
  shows "f (\<Sqinter>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 A) \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 \<Sqinter>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 (f ` A)"
    is complete_lattice_class.mono_Inf.
    
tts_lemma mono_Sup:
  assumes "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "A \<subseteq> U\<^sub>1"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
  shows "\<Squnion>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 (f ` A) \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f (\<Squnion>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 A)"
    is complete_lattice_class.mono_Sup.

end

context 
  fixes U\<^sub>3 :: "'c set"
begin

lemmas [transfer_rule] =
  image_transfer[where ?'a='c]

tts_context
  tts: (?'a to U\<^sub>1) and (?'b to U\<^sub>2) and (?'c to \<open>U\<^sub>3::'c set\<close>) 
  rewriting ctr_simps
  substituting cl\<^sub>1.complete_lattice_ow_axioms
    and cl\<^sub>2.complete_lattice_ow_axioms
    and cl\<^sub>1.inf_top.sl_neut.not_empty
    and cl\<^sub>2.inf_top.sl_neut.not_empty
  eliminating through (simp add: image_subset_iff image_subset_iff')
  applying 
    [
      OF 
        _
        cl\<^sub>1.Inf_closed' 
        cl\<^sub>1.Sup_closed' 
        cl\<^sub>1.inf_closed'   
        cl\<^sub>1.sup_closed'
        cl\<^sub>1.bot_closed
        cl\<^sub>1.top_closed
        cl\<^sub>2.Inf_closed' 
        cl\<^sub>2.Sup_closed' 
        cl\<^sub>2.inf_closed'   
        cl\<^sub>2.sup_closed'
        cl\<^sub>2.bot_closed
        cl\<^sub>2.top_closed
    ]
begin

tts_lemma mono_SUP:
  assumes "U\<^sub>3 \<noteq> {}"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>3. A x \<in> U\<^sub>1"
    and "I \<subseteq> U\<^sub>3"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
  shows "\<Squnion>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 ((\<lambda>x. f (A x)) ` I) \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 f (\<Squnion>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 (A ` I))"
    is complete_lattice_class.mono_SUP.
    
tts_lemma mono_INF:
  assumes "U\<^sub>3 \<noteq> {}"
    and "\<forall>x\<in>U\<^sub>1. f x \<in> U\<^sub>2"
    and "\<forall>x\<in>U\<^sub>3. A x \<in> U\<^sub>1"
    and "I \<subseteq> U\<^sub>3"
    and "on U\<^sub>1 with (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2) (\<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>1) : \<guillemotleft>mono\<guillemotright> f"
  shows "f (\<Sqinter>\<^sub>o\<^sub>w\<^sub>.\<^sub>1 (A ` I)) \<le>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 \<Sqinter>\<^sub>o\<^sub>w\<^sub>.\<^sub>2 ((\<lambda>x. f (A x)) ` I)"
    is complete_lattice_class.mono_INF.
    
end

end

end

text\<open>\newpage\<close>

end