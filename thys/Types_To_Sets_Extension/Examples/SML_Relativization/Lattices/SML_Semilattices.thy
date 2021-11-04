(* Title: Examples/SML_Relativization/Lattices/SML_Semilattices.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about semilattices\<close>
theory SML_Semilattices
  imports 
    "../Simple_Orders/SML_Simple_Orders"
    "../Algebra/SML_Monoids"
begin



subsection\<open>Commutative bands\<close>


subsubsection\<open>Definitions and common properties\<close>

locale semilattice_ow = abel_semigroup_ow U f 
  for U :: "'al set" and f +
  assumes idem[simp]: "x \<in> U \<Longrightarrow> x \<^bold>*\<^sub>o\<^sub>w x = x"

locale semilattice_set_ow = 
  semilattice_ow U f for U :: "'al set" and f (infixl \<open>\<^bold>*\<^sub>o\<^sub>w\<close> 70)


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semilattice_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (\<lambda>f. semilattice_ow (Collect (Domainp A)) f) semilattice"
  unfolding
    semilattice_ow_def semilattice_def 
    semilattice_ow_axioms_def semilattice_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

lemma semilattice_set_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> (=)) 
      (\<lambda>f. semilattice_set_ow (Collect (Domainp A)) f) semilattice_set"
  unfolding semilattice_set_ow_def semilattice_set_def by transfer_prover

end


subsubsection\<open>Relativization\<close>

context semilattice_ow 
begin

tts_context
  tts: (?'a to U)
  substituting semilattice_ow_axioms
  eliminating through simp
begin

tts_lemma left_idem:
  assumes "a \<in> U" and "b \<in> U"
  shows "a \<^bold>*\<^sub>o\<^sub>w (a \<^bold>*\<^sub>o\<^sub>w b) = a \<^bold>*\<^sub>o\<^sub>w b"
    is semilattice.left_idem.

tts_lemma right_idem:
  assumes "a \<in> U" and "b \<in> U"
  shows "a \<^bold>*\<^sub>o\<^sub>w b \<^bold>*\<^sub>o\<^sub>w b = a \<^bold>*\<^sub>o\<^sub>w b"
    is semilattice.right_idem.

end

end



subsection\<open>Simple upper and lower semilattices\<close>


subsubsection\<open>Definitions and common properties\<close>

locale semilattice_order_ow = semilattice_ow U f 
  for U :: "'al set" and f  +
  fixes le :: "['al, 'al] \<Rightarrow> bool" (infix \<open>\<le>\<^sub>o\<^sub>w\<close> 50)
    and ls :: "['al, 'al] \<Rightarrow> bool" (infix \<open><\<^sub>o\<^sub>w\<close> 50)
  assumes order_iff: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<le>\<^sub>o\<^sub>w b \<longleftrightarrow> a = a \<^bold>*\<^sub>o\<^sub>w b"
    and strict_order_iff: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a <\<^sub>o\<^sub>w b \<longleftrightarrow> a = a \<^bold>*\<^sub>o\<^sub>w b \<and> a \<noteq> b"
begin

sublocale ordering_ow U \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close>
proof
  show "\<lbrakk>a \<in> U; b \<in> U\<rbrakk> \<Longrightarrow> (a <\<^sub>o\<^sub>w b) = (a \<le>\<^sub>o\<^sub>w b \<and> a \<noteq> b)" for a b
    apply standard
    subgoal by (auto simp: commute order_iff strict_order_iff)
    subgoal by (auto simp: order_iff strict_order_iff)
    done
  show "x \<in> U \<Longrightarrow> x \<le>\<^sub>o\<^sub>w x" for x by (simp add: order_iff)
  show "\<lbrakk> x \<in> U; y \<in> U; z \<in> U; x \<le>\<^sub>o\<^sub>w y; y \<le>\<^sub>o\<^sub>w z \<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w z" for x y z
  proof-
    assume "x \<in> U" and "y \<in> U" and "z \<in> U" and "x \<le>\<^sub>o\<^sub>w y" and "y \<le>\<^sub>o\<^sub>w z"
    note xy = order_iff[THEN iffD1, OF \<open>x \<in> U\<close> \<open>y \<in> U\<close> \<open>x \<le>\<^sub>o\<^sub>w y\<close>]
    note yz = order_iff[THEN iffD1, OF \<open>y \<in> U\<close> \<open>z \<in> U\<close> \<open>y \<le>\<^sub>o\<^sub>w z\<close>]
    note xz = assoc[OF \<open>x \<in> U\<close> \<open>y \<in> U\<close> \<open>z \<in> U\<close>, folded xy yz, symmetric]
    show ?thesis by (rule order_iff[THEN iffD2, OF \<open>x \<in> U\<close> \<open>z \<in> U\<close> xz])
  qed
  show "\<lbrakk> x \<in> U; y \<in> U; x \<le>\<^sub>o\<^sub>w y; y \<le>\<^sub>o\<^sub>w x \<rbrakk> \<Longrightarrow> x = y" for x y
    by (fastforce simp: commute order_iff)
qed

notation le (infix "\<le>\<^sub>o\<^sub>w" 50)
  and ls (infix "<\<^sub>o\<^sub>w" 50)

end

locale semilattice_order_set_ow = 
  semilattice_order_ow U f le ls + semilattice_set_ow U f
  for U :: "'al set" and f le ls  

locale inf_ow =
  fixes U :: "'al set" and inf (infixl \<open>\<sqinter>\<^sub>o\<^sub>w\<close> 70)
  assumes inf_closed[simp]: "\<lbrakk> x \<in> U; y \<in> U \<rbrakk> \<Longrightarrow> x \<sqinter>\<^sub>o\<^sub>w y \<in> U"
begin

notation inf (infixl \<open>\<sqinter>\<^sub>o\<^sub>w\<close> 70)

lemma inf_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x \<sqinter>\<^sub>o\<^sub>w y \<in> U" by simp

end

locale inf_pair_ow = inf\<^sub>1: inf_ow U\<^sub>1 inf\<^sub>1 + inf\<^sub>2: inf_ow U\<^sub>2 inf\<^sub>2
  for U\<^sub>1 :: "'al set" and inf\<^sub>1
    and U\<^sub>2 :: "'bl set" and inf\<^sub>2
begin

notation inf\<^sub>1 (infixl \<open>\<sqinter>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close> 70)
notation inf\<^sub>2 (infixl \<open>\<sqinter>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close> 70)

end

locale semilattice_inf_ow = inf_ow U inf + order_ow U le ls 
  for U :: "'al set" and inf le ls  +
  assumes inf_le1[simp]: "\<lbrakk> x \<in> U; y \<in> U \<rbrakk> \<Longrightarrow> x \<sqinter>\<^sub>o\<^sub>w y \<le>\<^sub>o\<^sub>w x"
    and inf_le2[simp]: "\<lbrakk> x \<in> U; y \<in> U \<rbrakk> \<Longrightarrow> x \<sqinter>\<^sub>o\<^sub>w y \<le>\<^sub>o\<^sub>w y"
    and inf_greatest: 
      "\<lbrakk> x \<in> U; y \<in> U; z \<in> U; x \<le>\<^sub>o\<^sub>w y; x \<le>\<^sub>o\<^sub>w z \<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w y \<sqinter>\<^sub>o\<^sub>w z"
begin

sublocale inf: semilattice_order_ow U \<open>(\<sqinter>\<^sub>o\<^sub>w)\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close>
proof

  show *: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<sqinter>\<^sub>o\<^sub>w b \<in> U" for a b by simp

  show **: "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a \<sqinter>\<^sub>o\<^sub>w b \<sqinter>\<^sub>o\<^sub>w c = a \<sqinter>\<^sub>o\<^sub>w (b \<sqinter>\<^sub>o\<^sub>w c)" 
    for a b c
  proof -
    
    assume "a \<in> U" and "b \<in> U" and "c \<in> U"
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have ab_c: "a \<sqinter>\<^sub>o\<^sub>w b \<sqinter>\<^sub>o\<^sub>w c \<in> U" by simp
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have a_bc: "a \<sqinter>\<^sub>o\<^sub>w (b \<sqinter>\<^sub>o\<^sub>w c) \<in> U" by simp

    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "a \<sqinter>\<^sub>o\<^sub>w b \<sqinter>\<^sub>o\<^sub>w c \<le>\<^sub>o\<^sub>w b" 
      by (meson * inf_le1 inf_le2 order_trans)
    moreover from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "a \<sqinter>\<^sub>o\<^sub>w b \<sqinter>\<^sub>o\<^sub>w c \<le>\<^sub>o\<^sub>w c" by simp
    ultimately have abc_le_bc: "a \<sqinter>\<^sub>o\<^sub>w b \<sqinter>\<^sub>o\<^sub>w c \<le>\<^sub>o\<^sub>w b \<sqinter>\<^sub>o\<^sub>w c"
      by (rule inf_greatest[OF ab_c \<open>b \<in> U\<close> \<open>c \<in> U\<close>])
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have abc_le_a: "a \<sqinter>\<^sub>o\<^sub>w b \<sqinter>\<^sub>o\<^sub>w c \<le>\<^sub>o\<^sub>w a" 
      by (meson inf_le1 order_trans inf_closed)
    note lhs = 
      inf_greatest[OF ab_c \<open>a \<in> U\<close> *[OF \<open>b \<in> U\<close> \<open>c \<in> U\<close>] abc_le_a abc_le_bc]

    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "a \<sqinter>\<^sub>o\<^sub>w (b \<sqinter>\<^sub>o\<^sub>w c) \<le>\<^sub>o\<^sub>w a" 
      by (meson * inf_le1 order_trans)
    moreover from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "a \<sqinter>\<^sub>o\<^sub>w (b \<sqinter>\<^sub>o\<^sub>w c) \<le>\<^sub>o\<^sub>w b" 
      by (meson * inf_le1 inf_le2 order_trans)
    ultimately have abc_le_bc: "a \<sqinter>\<^sub>o\<^sub>w (b \<sqinter>\<^sub>o\<^sub>w c) \<le>\<^sub>o\<^sub>w a \<sqinter>\<^sub>o\<^sub>w b"
      by (rule inf_greatest[OF a_bc \<open>a \<in> U\<close> \<open>b \<in> U\<close>])
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have abc_le_a: "a \<sqinter>\<^sub>o\<^sub>w (b \<sqinter>\<^sub>o\<^sub>w c) \<le>\<^sub>o\<^sub>w c" 
      by (meson inf_le2 order_trans inf_closed)
    note rhs =
      inf_greatest[OF a_bc *[OF \<open>a \<in> U\<close> \<open>b \<in> U\<close>] \<open>c \<in> U\<close> abc_le_bc abc_le_a] 
    show "a \<sqinter>\<^sub>o\<^sub>w b \<sqinter>\<^sub>o\<^sub>w c = a \<sqinter>\<^sub>o\<^sub>w (b \<sqinter>\<^sub>o\<^sub>w c)" 
      by (rule antisym[OF ab_c a_bc lhs rhs])
 
  qed

  show ***: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<sqinter>\<^sub>o\<^sub>w b = b \<sqinter>\<^sub>o\<^sub>w a" for a b
    by (simp add: eq_iff inf_greatest)

  show ****: "x \<in> U \<Longrightarrow> x \<sqinter>\<^sub>o\<^sub>w x = x" for x
  proof-
    assume "x \<in> U"
    have "x \<sqinter>\<^sub>o\<^sub>w x \<le>\<^sub>o\<^sub>w x" by (simp add: \<open>x \<in> U\<close>)
    moreover have "x \<le>\<^sub>o\<^sub>w x \<sqinter>\<^sub>o\<^sub>w x" by (simp add: \<open>x \<in> U\<close> inf_greatest)
    ultimately show "x \<sqinter>\<^sub>o\<^sub>w x = x" by (simp add: \<open>x \<in> U\<close> antisym)
  qed

  show *****: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> (a \<le>\<^sub>o\<^sub>w b) = (a = a \<sqinter>\<^sub>o\<^sub>w b)" for a b
    by (metis * *** eq_iff inf_greatest inf_le1 inf_le2)

  show "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> (a <\<^sub>o\<^sub>w b) = (a = a \<sqinter>\<^sub>o\<^sub>w b \<and> a \<noteq> b)" for a b
    by (simp add: ***** less_le)

qed

sublocale Inf_fin: semilattice_order_set_ow U \<open>(\<sqinter>\<^sub>o\<^sub>w)\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> ..

end

locale semilattice_inf_pair_ow = 
  sl_inf\<^sub>1: semilattice_inf_ow U\<^sub>1 inf\<^sub>1 le\<^sub>1 ls\<^sub>1 +
  sl_inf\<^sub>2: semilattice_inf_ow U\<^sub>2 inf\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'al set" and inf\<^sub>1 le\<^sub>1 ls\<^sub>1
    and U\<^sub>2 :: "'bl set" and inf\<^sub>2 le\<^sub>2 ls\<^sub>2
begin

sublocale inf_pair_ow ..
sublocale order_pair_ow ..

end

locale sup_ow =
  fixes U :: "'ao set" and sup :: "['ao, 'ao] \<Rightarrow> 'ao" (infixl \<open>\<squnion>\<^sub>o\<^sub>w\<close> 70)
  assumes sup_closed[simp]: "\<lbrakk> x \<in> U; y \<in> U \<rbrakk> \<Longrightarrow> sup x y \<in> U"
begin

notation sup (infixl \<open>\<squnion>\<^sub>o\<^sub>w\<close> 70)

lemma sup_closed'[simp]: "\<forall>x\<in>U. \<forall>y\<in>U. x \<squnion>\<^sub>o\<^sub>w y \<in> U" by simp

end

locale sup_pair_ow = sup\<^sub>1: sup_ow U\<^sub>1 sup\<^sub>1 + sup\<^sub>2: sup_ow U\<^sub>2 sup\<^sub>2
  for U\<^sub>1 :: "'al set" and sup\<^sub>1
    and U\<^sub>2 :: "'bl set" and sup\<^sub>2
begin

notation sup\<^sub>1 (infixl \<open>\<squnion>\<^sub>o\<^sub>w\<^sub>.\<^sub>1\<close> 70)
notation sup\<^sub>2 (infixl \<open>\<squnion>\<^sub>o\<^sub>w\<^sub>.\<^sub>2\<close> 70)

end

locale semilattice_sup_ow = sup_ow U sup + order_ow U le ls 
  for U :: "'al set" and sup le ls + 
  assumes sup_ge1[simp]: "\<lbrakk> x \<in> U; y \<in> U \<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w x \<squnion>\<^sub>o\<^sub>w y"
    and sup_ge2[simp]: "\<lbrakk> y \<in> U; x \<in> U \<rbrakk> \<Longrightarrow> y \<le>\<^sub>o\<^sub>w x \<squnion>\<^sub>o\<^sub>w y"
    and sup_least: 
      "\<lbrakk> y \<in> U; x \<in> U; z \<in> U; y \<le>\<^sub>o\<^sub>w x; z \<le>\<^sub>o\<^sub>w x \<rbrakk> \<Longrightarrow> y \<squnion>\<^sub>o\<^sub>w z \<le>\<^sub>o\<^sub>w x"
begin

sublocale sup: semilattice_order_ow U \<open>(\<squnion>\<^sub>o\<^sub>w)\<close> \<open>(\<ge>\<^sub>o\<^sub>w)\<close> \<open>(>\<^sub>o\<^sub>w)\<close>
proof

  show *: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<squnion>\<^sub>o\<^sub>w b \<in> U" for a b by simp

  show **: 
    "\<lbrakk> a \<in> U; b \<in> U; c \<in> U \<rbrakk> \<Longrightarrow> a \<squnion>\<^sub>o\<^sub>w b \<squnion>\<^sub>o\<^sub>w c = a \<squnion>\<^sub>o\<^sub>w (b \<squnion>\<^sub>o\<^sub>w c)" for a b c
  proof -
    
    assume "a \<in> U" and "b \<in> U" and "c \<in> U"
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have ab_c: "a \<squnion>\<^sub>o\<^sub>w b \<squnion>\<^sub>o\<^sub>w c \<in> U" by simp
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have a_bc: "a \<squnion>\<^sub>o\<^sub>w (b \<squnion>\<^sub>o\<^sub>w c) \<in> U" by simp

    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "b \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w b \<squnion>\<^sub>o\<^sub>w c"
      by (meson order_trans sup_ge1 sup_ge2 sup_closed')
    moreover from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "c \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w b \<squnion>\<^sub>o\<^sub>w c" by simp
    ultimately have ab_le_abc: "b \<squnion>\<^sub>o\<^sub>w c \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w b \<squnion>\<^sub>o\<^sub>w c"
      by (rule sup_least[OF \<open>b \<in> U\<close> ab_c \<open>c \<in> U\<close>])
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have a_le_abc: "a \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w b \<squnion>\<^sub>o\<^sub>w c" 
      by (meson "*" order_trans sup_ge1)
    note rhs = 
      sup_least[OF \<open>a \<in> U\<close> ab_c *[OF \<open>b \<in> U\<close> \<open>c \<in> U\<close>] a_le_abc ab_le_abc]

    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "a \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w (b \<squnion>\<^sub>o\<^sub>w c)" by simp
    moreover from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have "b \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w (b \<squnion>\<^sub>o\<^sub>w c)" 
      by (meson order_trans sup_ge1 sup_ge2 sup_closed')
    ultimately have ab_le_abc: "a \<squnion>\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w (b \<squnion>\<^sub>o\<^sub>w c)"
      by (rule sup_least[OF \<open>a \<in> U\<close> a_bc \<open>b \<in> U\<close>])
    from \<open>a \<in> U\<close> \<open>b \<in> U\<close> \<open>c \<in> U\<close> have c_le_abc: "c \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w (b \<squnion>\<^sub>o\<^sub>w c)" 
      by (meson "*" order_trans sup_ge2)
    note lhs =
      sup_least[OF *[OF \<open>a \<in> U\<close> \<open>b \<in> U\<close>] a_bc \<open>c \<in> U\<close> ab_le_abc c_le_abc]  
    show "a \<squnion>\<^sub>o\<^sub>w b \<squnion>\<^sub>o\<^sub>w c = a \<squnion>\<^sub>o\<^sub>w (b \<squnion>\<^sub>o\<^sub>w c)"
      by (rule antisym[OF ab_c a_bc lhs rhs])
 
  qed

  show ***: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> a \<squnion>\<^sub>o\<^sub>w b = b \<squnion>\<^sub>o\<^sub>w a" for a b
    by (simp add: eq_iff sup_least)

  show ****: "x \<in> U \<Longrightarrow> x \<squnion>\<^sub>o\<^sub>w x = x" for x
  proof-
    assume "x \<in> U"
    have "x \<le>\<^sub>o\<^sub>w x \<squnion>\<^sub>o\<^sub>w x" by (simp add: \<open>x \<in> U\<close>)
    moreover have "x \<squnion>\<^sub>o\<^sub>w x \<le>\<^sub>o\<^sub>w x" by (simp add: \<open>x \<in> U\<close> sup_least)
    ultimately show "x \<squnion>\<^sub>o\<^sub>w x = x" by (simp add: \<open>x \<in> U\<close> antisym)
  qed

  show *****: "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> (a \<ge>\<^sub>o\<^sub>w b) = (a = a \<squnion>\<^sub>o\<^sub>w b)" for a b 
    by (metis *** sup_ge2 sup_least eq_iff eq_refl sup_closed')

  show "\<lbrakk> a \<in> U; b \<in> U \<rbrakk> \<Longrightarrow> (a >\<^sub>o\<^sub>w b) = (a = a \<squnion>\<^sub>o\<^sub>w b \<and> a \<noteq> b)" for a b
    by (auto simp: ***** less_le)

qed

sublocale Sup_fin: semilattice_order_set_ow U sup "(\<ge>\<^sub>o\<^sub>w)" "(>\<^sub>o\<^sub>w)" ..

end


locale semilattice_sup_pair_ow = 
  sl_sup\<^sub>1: semilattice_sup_ow U\<^sub>1 sup\<^sub>1 le\<^sub>1 ls\<^sub>1 +
  sl_sup\<^sub>2: semilattice_sup_ow U\<^sub>2 sup\<^sub>2 le\<^sub>2 ls\<^sub>2
  for U\<^sub>1 :: "'al set" and sup\<^sub>1 le\<^sub>1 ls\<^sub>1
    and U\<^sub>2 :: "'bl set" and sup\<^sub>2 le\<^sub>2 ls\<^sub>2
begin

sublocale sup_pair_ow ..
sublocale order_pair_ow ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semilattice_order_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (=)
    ) (semilattice_order_ow (Collect (Domainp A))) semilattice_order"
  unfolding
    semilattice_order_ow_def semilattice_order_def 
    semilattice_order_ow_axioms_def semilattice_order_axioms_def
  apply transfer_prover_start
  apply transfer_step+
  by simp

lemma semilattice_order_set_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (=)
    ) (semilattice_order_set_ow (Collect (Domainp A))) semilattice_order_set"
  unfolding semilattice_order_set_ow_def semilattice_order_set_def 
  apply transfer_prover_start
  apply transfer_step+
  by simp

lemma semilattice_inf_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (=)
    ) (semilattice_inf_ow (Collect (Domainp A))) class.semilattice_inf"
proof -
  let ?P = 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===>
      (A ===> A ===> (=)) ===>
      (=)
    )"
  let ?semilattice_ow = "semilattice_inf_ow (Collect (Domainp A))"
  let ?rf_UNIV = 
    "(\<lambda>inf::['b, 'b] \<Rightarrow> 'b. (\<forall>x y. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> inf x y \<in> UNIV))"
  have 
    "?P 
    ?semilattice_ow 
    (\<lambda>inf le ls. ?rf_UNIV inf \<and> class.semilattice_inf inf le ls)"
    unfolding 
      class.semilattice_inf_def semilattice_inf_ow_def 
      class.semilattice_inf_axioms_def semilattice_inf_ow_axioms_def
      inf_ow_def
    apply transfer_prover_start
    apply transfer_step+
    unfolding Ball_def by fastforce
  then show ?thesis by simp
qed

lemma semilattice_sup_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (=)
    ) (semilattice_sup_ow (Collect (Domainp A))) class.semilattice_sup"
proof -
  let ?P = 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===>
      (A ===> A ===> (=)) ===>
      (=)
    )"
  let ?semilattice_ow = "semilattice_sup_ow (Collect (Domainp A))"
  let ?rf_UNIV = 
    "(\<lambda>sup::['b, 'b] \<Rightarrow> 'b. (\<forall>x y. x \<in> UNIV \<longrightarrow> y \<in> UNIV \<longrightarrow> sup x y \<in> UNIV))"
  have 
    "?P 
    ?semilattice_ow 
    (\<lambda>sup le ls. ?rf_UNIV sup \<and> class.semilattice_sup sup le ls)"
  unfolding 
    class.semilattice_sup_def semilattice_sup_ow_def 
    class.semilattice_sup_axioms_def semilattice_sup_ow_axioms_def
    sup_ow_def
  apply transfer_prover_start
  apply transfer_step+
  unfolding Ball_def by fastforce
  then show ?thesis by simp
qed

end


subsubsection\<open>Relativization\<close>

context semilattice_order_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting semilattice_order_ow_axioms
  eliminating through simp
begin

tts_lemma cobounded1:
  assumes "a \<in> U" and "b \<in> U"
  shows "a \<^bold>*\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w a"
    is semilattice_order.cobounded1.
    
tts_lemma cobounded2:
  assumes "a \<in> U" and "b \<in> U"
  shows "a \<^bold>*\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w b"
    is semilattice_order.cobounded2.

tts_lemma absorb_iff1:
  assumes "a \<in> U" and "b \<in> U"
  shows "(a \<le>\<^sub>o\<^sub>w b) = (a \<^bold>*\<^sub>o\<^sub>w b = a)"
    is semilattice_order.absorb_iff1.

tts_lemma absorb_iff2:
  assumes "b \<in> U" and "a \<in> U"
  shows "(b \<le>\<^sub>o\<^sub>w a) = (a \<^bold>*\<^sub>o\<^sub>w b = b)"
    is semilattice_order.absorb_iff2.

tts_lemma strict_coboundedI1:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U" and "a <\<^sub>o\<^sub>w c"
  shows "a \<^bold>*\<^sub>o\<^sub>w b <\<^sub>o\<^sub>w c"
    is semilattice_order.strict_coboundedI1.

tts_lemma strict_coboundedI2:
  assumes "b \<in> U" and "c \<in> U" and "a \<in> U" and "b <\<^sub>o\<^sub>w c"
  shows "a \<^bold>*\<^sub>o\<^sub>w b <\<^sub>o\<^sub>w c"
    is semilattice_order.strict_coboundedI2.

tts_lemma absorb1:
  assumes "a \<in> U" and "b \<in> U" and "a \<le>\<^sub>o\<^sub>w b"
  shows "a \<^bold>*\<^sub>o\<^sub>w b = a"
    is semilattice_order.absorb1.

tts_lemma coboundedI1:
  assumes "a \<in> U" and "c \<in> U" and "b \<in> U" and "a \<le>\<^sub>o\<^sub>w c"
  shows "a \<^bold>*\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w c"
    is semilattice_order.coboundedI1.

tts_lemma absorb2:
  assumes "b \<in> U" and "a \<in> U" and "b \<le>\<^sub>o\<^sub>w a"
  shows "a \<^bold>*\<^sub>o\<^sub>w b = b"
    is semilattice_order.absorb2.

tts_lemma coboundedI2:
  assumes "b \<in> U" and "c \<in> U" and "a \<in> U" and "b \<le>\<^sub>o\<^sub>w c"
  shows "a \<^bold>*\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w c"
    is semilattice_order.coboundedI2.

tts_lemma orderI:
  assumes "a \<in> U" and "b \<in> U" and "a = a \<^bold>*\<^sub>o\<^sub>w b"
  shows "a \<le>\<^sub>o\<^sub>w b"
    is semilattice_order.orderI.

tts_lemma bounded_iff:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U"
  shows "(a \<le>\<^sub>o\<^sub>w b \<^bold>*\<^sub>o\<^sub>w c) = (a \<le>\<^sub>o\<^sub>w b \<and> a \<le>\<^sub>o\<^sub>w c)"
    is semilattice_order.bounded_iff.

tts_lemma boundedI:
  assumes "a \<in> U" and "b \<in> U" and "c \<in> U" and "a \<le>\<^sub>o\<^sub>w b" and "a \<le>\<^sub>o\<^sub>w c"
  shows "a \<le>\<^sub>o\<^sub>w b \<^bold>*\<^sub>o\<^sub>w c"
    is semilattice_order.boundedI.

tts_lemma orderE:
  assumes "a \<in> U" and "b \<in> U"  and "a \<le>\<^sub>o\<^sub>w b" and "a = a \<^bold>*\<^sub>o\<^sub>w b \<Longrightarrow> thesis"
  shows thesis
    is semilattice_order.orderE.

tts_lemma mono:
  assumes "a \<in> U"
    and "c \<in> U"
    and "b \<in> U"
    and "d \<in> U"
    and "a \<le>\<^sub>o\<^sub>w c"
    and "b \<le>\<^sub>o\<^sub>w d"
  shows "a \<^bold>*\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w c \<^bold>*\<^sub>o\<^sub>w d"
    is semilattice_order.mono.

tts_lemma strict_boundedE:
  assumes "a \<in> U"
    and "b \<in> U"
    and "c \<in> U"
    and "a <\<^sub>o\<^sub>w b \<^bold>*\<^sub>o\<^sub>w c"
  obtains "a <\<^sub>o\<^sub>w b" and "a <\<^sub>o\<^sub>w c"
    given semilattice_order.strict_boundedE by auto

tts_lemma boundedE:
  assumes "a \<in> U"
    and "b \<in> U"
    and "c \<in> U"
    and "a \<le>\<^sub>o\<^sub>w b \<^bold>*\<^sub>o\<^sub>w c"
  obtains "a \<le>\<^sub>o\<^sub>w b" and "a \<le>\<^sub>o\<^sub>w c"
    given semilattice_order.boundedE by auto

end

end

context semilattice_inf_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting semilattice_inf_ow_axioms
  eliminating through simp
begin

tts_lemma le_iff_inf:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x \<le>\<^sub>o\<^sub>w y) = (x \<sqinter>\<^sub>o\<^sub>w y = x)"
    is semilattice_inf_class.le_iff_inf.
    
tts_lemma less_infI1:
  assumes "a \<in> U" and "x \<in> U" and "b \<in> U" and "a <\<^sub>o\<^sub>w x"
  shows "a \<sqinter>\<^sub>o\<^sub>w b <\<^sub>o\<^sub>w x"
    is semilattice_inf_class.less_infI1.

tts_lemma less_infI2:
  assumes "b \<in> U" and "x \<in> U" and "a \<in> U" and "b <\<^sub>o\<^sub>w x"
  shows "a \<sqinter>\<^sub>o\<^sub>w b <\<^sub>o\<^sub>w x"
    is semilattice_inf_class.less_infI2.

tts_lemma le_infI1:
  assumes "a \<in> U" and "x \<in> U" and "b \<in> U" and "a \<le>\<^sub>o\<^sub>w x"
  shows "a \<sqinter>\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w x"
    is semilattice_inf_class.le_infI1.

tts_lemma le_infI2:
  assumes "b \<in> U" and "x \<in> U" and "a \<in> U" and "b \<le>\<^sub>o\<^sub>w x"
  shows "a \<sqinter>\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w x"
    is semilattice_inf_class.le_infI2.

tts_lemma le_inf_iff:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U"
  shows "(x \<le>\<^sub>o\<^sub>w y \<sqinter>\<^sub>o\<^sub>w z) = (x \<le>\<^sub>o\<^sub>w y \<and> x \<le>\<^sub>o\<^sub>w z)"
    is semilattice_inf_class.le_inf_iff.

tts_lemma le_infI:
  assumes "x \<in> U" and "a \<in> U" and "b \<in> U" and "x \<le>\<^sub>o\<^sub>w a" and "x \<le>\<^sub>o\<^sub>w b"
  shows "x \<le>\<^sub>o\<^sub>w a \<sqinter>\<^sub>o\<^sub>w b"
    is semilattice_inf_class.le_infI.

tts_lemma le_infE:
  assumes "x \<in> U"
    and "a \<in> U"
    and "b \<in> U"
    and "x \<le>\<^sub>o\<^sub>w a \<sqinter>\<^sub>o\<^sub>w b"
    and "\<lbrakk>x \<le>\<^sub>o\<^sub>w a; x \<le>\<^sub>o\<^sub>w b\<rbrakk> \<Longrightarrow> P"
  shows P
    is semilattice_inf_class.le_infE.

tts_lemma inf_mono:
  assumes "a \<in> U"
    and "c \<in> U"
    and "b \<in> U"
    and "d \<in> U"
    and "a \<le>\<^sub>o\<^sub>w c"
    and "b \<le>\<^sub>o\<^sub>w d"
  shows "a \<sqinter>\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w c \<sqinter>\<^sub>o\<^sub>w d"
    is semilattice_inf_class.inf_mono.

end

end

context semilattice_sup_ow
begin

tts_context
  tts: (?'a to U)
  rewriting ctr_simps
  substituting semilattice_sup_ow_axioms
  eliminating through simp
begin

tts_lemma le_iff_sup:
  assumes "x \<in> U" and "y \<in> U"
  shows "(x \<le>\<^sub>o\<^sub>w y) = (x \<squnion>\<^sub>o\<^sub>w y = y)"
    is semilattice_sup_class.le_iff_sup.

tts_lemma less_supI1:
  assumes "x \<in> U" and "a \<in> U" and "b \<in> U" and "x <\<^sub>o\<^sub>w a"
  shows "x <\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w b"
    is semilattice_sup_class.less_supI1.

tts_lemma less_supI2:
  assumes "x \<in> U" and "b \<in> U" and "a \<in> U" and "x <\<^sub>o\<^sub>w b"
  shows "x <\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w b"
    is semilattice_sup_class.less_supI2.

tts_lemma le_supI1:
  assumes "x \<in> U" and "a \<in> U" and "b \<in> U" and "x \<le>\<^sub>o\<^sub>w a"
  shows "x \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w b"
    is semilattice_sup_class.le_supI1.

tts_lemma le_supI2:
  assumes "x \<in> U" and "b \<in> U" and "a \<in> U" and "x \<le>\<^sub>o\<^sub>w b"
  shows "x \<le>\<^sub>o\<^sub>w a \<squnion>\<^sub>o\<^sub>w b"
    is semilattice_sup_class.le_supI2.

tts_lemma le_sup_iff:
  assumes "x \<in> U" and "y \<in> U" and "z \<in> U"
  shows "(x \<squnion>\<^sub>o\<^sub>w y \<le>\<^sub>o\<^sub>w z) = (x \<le>\<^sub>o\<^sub>w z \<and> y \<le>\<^sub>o\<^sub>w z)"
    is semilattice_sup_class.le_sup_iff.

tts_lemma le_supI:
  assumes "a \<in> U" and "x \<in> U" and "b \<in> U" and "a \<le>\<^sub>o\<^sub>w x" and "b \<le>\<^sub>o\<^sub>w x"
  shows "a \<squnion>\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w x"
    is semilattice_sup_class.le_supI.

tts_lemma le_supE:
  assumes "a \<in> U"
    and "b \<in> U"
    and "x \<in> U"
    and "a \<squnion>\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w x"
    and "\<lbrakk>a \<le>\<^sub>o\<^sub>w x; b \<le>\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> P"
  shows P
    is semilattice_sup_class.le_supE.

tts_lemma sup_unique:
  assumes "\<forall>x\<in>U. \<forall>y\<in>U. f x y \<in> U"
    and "x \<in> U"
    and "y \<in> U"
    and "\<And>x y. \<lbrakk>x \<in> U; y \<in> U\<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w f x y"
    and "\<And>x y. \<lbrakk>x \<in> U; y \<in> U\<rbrakk> \<Longrightarrow> y \<le>\<^sub>o\<^sub>w f x y"
    and "\<And>x y z. \<lbrakk>x \<in> U; y \<in> U; z \<in> U; y \<le>\<^sub>o\<^sub>w x; z \<le>\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> f y z \<le>\<^sub>o\<^sub>w x"
  shows "x \<squnion>\<^sub>o\<^sub>w y = f x y"
    is semilattice_sup_class.sup_unique.

tts_lemma sup_mono:
  assumes "a \<in> U"
    and "c \<in> U"
    and "b \<in> U"
    and "d \<in> U"
    and "a \<le>\<^sub>o\<^sub>w c"
    and "b \<le>\<^sub>o\<^sub>w d"
  shows "a \<squnion>\<^sub>o\<^sub>w b \<le>\<^sub>o\<^sub>w c \<squnion>\<^sub>o\<^sub>w d"
    is semilattice_sup_class.sup_mono.

end

end



subsection\<open>Bounded semilattices\<close>


subsubsection\<open>Definitions and common properties\<close>

locale semilattice_neutral_ow = semilattice_ow U f + comm_monoid_ow U f z
  for U :: "'al set" and f z

locale semilattice_neutral_order_ow = 
  sl_neut: semilattice_neutral_ow U f z + 
  sl_ord: semilattice_order_ow U f le ls
  for U :: "'al set" and f z le ls 
begin

sublocale order_top_ow U \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close> \<open>\<^bold>1\<^sub>o\<^sub>w\<close>
  apply unfold_locales
  subgoal by (auto simp: antisym sl_ord.strict_iff_order sl_ord.antisym)
  subgoal by (auto simp: sl_ord.order_iff)
  subgoal by (auto intro: sl_ord.trans)
  subgoal by (auto simp: sl_ord.antisym)
  subgoal by auto
  subgoal by (simp add: sl_ord.absorb_iff1)
  done

end

locale bounded_semilattice_inf_top_ow =
  semilattice_inf_ow U inf le ls + order_top_ow U le ls top
  for U :: "'al set" and inf le ls top 
begin

sublocale inf_top: semilattice_neutral_order_ow U \<open>(\<sqinter>\<^sub>o\<^sub>w)\<close> \<open>\<top>\<^sub>o\<^sub>w\<close> \<open>(\<le>\<^sub>o\<^sub>w)\<close> \<open>(<\<^sub>o\<^sub>w)\<close>
  apply unfold_locales
  subgoal by simp
  subgoal using top_greatest by (simp add: inf.order_iff)
  done

end

locale bounded_semilattice_sup_bot_ow = 
  semilattice_sup_ow U sup le ls + order_bot_ow U bot le ls
  for U :: "'al set" and sup le ls bot
begin

sublocale sup_bot: semilattice_neutral_order_ow U \<open>(\<squnion>\<^sub>o\<^sub>w)\<close> \<open>\<bottom>\<^sub>o\<^sub>w\<close> \<open>(\<ge>\<^sub>o\<^sub>w)\<close> \<open>(>\<^sub>o\<^sub>w)\<close>
  by unfold_locales (simp_all add: sup.absorb1)

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma semilattice_neutral_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "((A ===> A ===> A) ===> A ===> (=))
      (semilattice_neutral_ow (Collect (Domainp A))) semilattice_neutr"
  unfolding semilattice_neutral_ow_def semilattice_neutr_def by transfer_prover
  
lemma semilattice_neutr_order_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      A ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (=)
    )
    (semilattice_neutral_order_ow (Collect (Domainp A))) 
    semilattice_neutr_order"
  unfolding semilattice_neutral_order_ow_def semilattice_neutr_order_def 
  by transfer_prover

lemma bounded_semilattice_inf_top_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      A ===> 
      (=)
    ) 
    (bounded_semilattice_inf_top_ow (Collect (Domainp A))) 
    class.bounded_semilattice_inf_top"
  unfolding
    bounded_semilattice_inf_top_ow_def class.bounded_semilattice_inf_top_def
  by transfer_prover

lemma bounded_semilattice_sup_bot_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> A) ===> 
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      A ===> 
      (=)
    ) 
    (bounded_semilattice_sup_bot_ow (Collect (Domainp A))) 
    class.bounded_semilattice_sup_bot"
  unfolding
    bounded_semilattice_sup_bot_ow_def class.bounded_semilattice_sup_bot_def
  by transfer_prover

end

text\<open>\newpage\<close>

end