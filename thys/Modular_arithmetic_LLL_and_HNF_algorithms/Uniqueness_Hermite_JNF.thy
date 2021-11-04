section \<open>Uniqueness of Hermite normal form in JNF\<close>

text \<open>This theory contains the proof of the uniqueness theorem of the Hermite normal form in JNF,
moved from HOL Analysis.\<close>

theory Uniqueness_Hermite_JNF
  imports 
  Hermite.Hermite
  Uniqueness_Hermite
  Smith_Normal_Form.SNF_Missing_Lemmas
  Smith_Normal_Form.Mod_Type_Connect
  Smith_Normal_Form.Finite_Field_Mod_Type_Connection
begin  

hide_const (open) residues

text \<open>We first define some properties that currently exist in HOL Analysis, but not in
JNF, namely a predicate for being in echelon form, another one for being in Hermite normal form,
definition of a row of zeros up to a concrete position, and so on.\<close>

definition is_zero_row_upt_k_JNF :: "nat  => nat =>'a::{zero} mat => bool"
  where "is_zero_row_upt_k_JNF i k A = (\<forall>j. j < k \<longrightarrow> A $$ (i,j) = 0)"

definition is_zero_row_JNF :: "nat =>'a::{zero} mat  => bool"
  where "is_zero_row_JNF i A =  (\<forall>j<dim_col A. A $$ (i, j) = 0)"

lemma echelon_form_def': 
"echelon_form A = (
    (\<forall>i. is_zero_row i A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row j A)) 
    \<and>  
    (\<forall>i j. i<j \<and> \<not> (is_zero_row i A) \<and> \<not> (is_zero_row j A) 
          \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0))))"
  unfolding echelon_form_def echelon_form_upt_k_def unfolding is_zero_row_def by auto

definition 
  echelon_form_JNF :: "'a::{bezout_ring} mat \<Rightarrow> bool" 
  where 
  "echelon_form_JNF A = (
    (\<forall>i<dim_row A. is_zero_row_JNF i A \<longrightarrow> \<not> (\<exists>j. j < dim_row A \<and> j>i \<and> \<not> is_zero_row_JNF j A)) 
    \<and>  
    (\<forall>i j. i<j \<and> j<dim_row A \<and> \<not> (is_zero_row_JNF i A) \<and> \<not> (is_zero_row_JNF j A) 
          \<longrightarrow> ((LEAST n. A $$ (i, n) \<noteq> 0) < (LEAST n. A $$ (j, n) \<noteq> 0))))"


text \<open>Now, we connect the existing definitions in HOL Analysis to the ones just defined in JNF by
means of transfer rules.\<close>

context includes lifting_syntax
begin


lemma HMA_is_zero_row_mod_type[transfer_rule]: 
  "((Mod_Type_Connect.HMA_I) ===> (Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) 
    ===> (=)) is_zero_row_JNF is_zero_row"
proof (intro rel_funI, goal_cases)
  case (1 i i' A A')
  note ii' = "1"(1)[transfer_rule]
  note AA' = "1"(2)[transfer_rule]
  have "(\<forall>j<dim_col A. A $$ (i, j) = 0) = (\<forall>j. A' $h i' $h j = 0)"
  proof (rule;rule+)
    fix j'::'n assume Aij_0: "\<forall>j<dim_col A. A $$ (i, j) = 0" 
    define j where "j = mod_type_class.to_nat j'"
    have [transfer_rule]: "Mod_Type_Connect.HMA_I j j'" unfolding Mod_Type_Connect.HMA_I_def j_def by auto
    have A_ij0': "A $$ (i,j) = 0" using Aij_0 unfolding j_def
      by (metis AA' Mod_Type_Connect.HMA_M_def Mod_Type_Connect.from_hma\<^sub>m_def 
          dim_col_mat(1) mod_type_class.to_nat_less_card)
    hence "index_hma A' i' j' = 0" by transfer
    thus "A' $h i' $h j' = 0" unfolding index_hma_def by simp
  next
    fix j assume 1: "\<forall>j'. A' $h i' $h j' = 0" and 2: "j < dim_col A" 
    define j'::'n where "j' = mod_type_class.from_nat j"
    have [transfer_rule]: "Mod_Type_Connect.HMA_I j j'" unfolding Mod_Type_Connect.HMA_I_def j'_def 
      using Mod_Type.to_nat_from_nat_id[of j, where ?'a = 'n] 2
      using AA' Mod_Type_Connect.dim_col_transfer_rule by force
    have "A' $h i' $h j' = 0" using 1 by auto
    hence "index_hma A' i' j' = 0" unfolding index_hma_def by simp  
    thus "A $$ (i, j) = 0" by transfer
  qed
  thus ?case unfolding is_zero_row_def' is_zero_row_JNF_def by auto
qed

lemma HMA_echelon_form_mod_type[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a ::bezout_ring ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) ===> (=))
  echelon_form_JNF echelon_form"
proof (intro rel_funI, goal_cases)
  case (1 A A')
  note AA' = "1"(1)[transfer_rule]
  have 1: "(\<forall>i<dim_row A. is_zero_row_JNF i A \<longrightarrow> \<not> (\<exists>j < dim_row A. j>i \<and> \<not> is_zero_row_JNF j A))
    = (\<forall>i. is_zero_row i A' \<longrightarrow> \<not> (\<exists>j>i. \<not> is_zero_row j A'))"
  proof (auto)
    fix i' j' assume 1: "\<forall>i<dim_row A. is_zero_row_JNF i A \<longrightarrow> (\<forall>j>i. j < dim_row A \<longrightarrow> is_zero_row_JNF j A)"
      and 2: "is_zero_row i' A'" and 3: "i' < j'"
    let ?i = "Mod_Type.to_nat i'"
    let ?j = "Mod_Type.to_nat j'"
    have ii'[transfer_rule]: "Mod_Type_Connect.HMA_I ?i i'" and jj'[transfer_rule]: "Mod_Type_Connect.HMA_I ?j j'" 
      unfolding Mod_Type_Connect.HMA_I_def by auto
    have "is_zero_row_JNF ?i A" using 2 by transfer' 
    hence "is_zero_row_JNF ?j A" using 1 3 to_nat_mono
      by (metis AA' Mod_Type_Connect.HMA_M_def Mod_Type_Connect.from_hma\<^sub>m_def
          dim_row_mat(1) mod_type_class.to_nat_less_card)
    thus "is_zero_row j' A'" by transfer'
  next
    fix i j assume 1: "\<forall>i'. is_zero_row i' A' \<longrightarrow> (\<forall>j'>i'. is_zero_row j' A')"
      and 2: "is_zero_row_JNF i A" and 3: "i < j" and 4: "j<dim_row A"
    let ?i' = "Mod_Type.from_nat i::'m"
    let ?j' = "Mod_Type.from_nat j::'m"
    have ii'[transfer_rule]: "Mod_Type_Connect.HMA_I i ?i'"
      unfolding Mod_Type_Connect.HMA_I_def using Mod_Type.to_nat_from_nat_id[of i]
      using 3 4 AA' Mod_Type_Connect.dim_row_transfer_rule less_trans by fastforce
    have jj'[transfer_rule]: "Mod_Type_Connect.HMA_I j ?j'" 
      unfolding Mod_Type_Connect.HMA_I_def  using Mod_Type.to_nat_from_nat_id[of j]
      using 3 4 AA' Mod_Type_Connect.dim_row_transfer_rule less_trans by fastforce
    have "is_zero_row ?i' A'" using 2 by transfer
    moreover have "?i' < ?j'" using 3 4 AA' Mod_Type_Connect.dim_row_transfer_rule from_nat_mono by fastforce
    ultimately have "is_zero_row ?j' A'" using 1 3 by auto
    thus "is_zero_row_JNF j A" by transfer
  qed
  have 2: "((\<forall>i j. i<j \<and> \<not> (is_zero_row i A') \<and> \<not> (is_zero_row j A') 
    \<longrightarrow> ((LEAST n. A' $h i $h n \<noteq> 0) < (LEAST n. A' $h j $h n \<noteq> 0)))) 
    = (\<forall>i j. i<j \<and> j<dim_row A \<and> \<not> (is_zero_row_JNF i A) \<and> \<not> (is_zero_row_JNF j A) 
    \<longrightarrow> ((LEAST n. A $$ (i, n) \<noteq> 0) < (LEAST n. A $$ (j, n) \<noteq> 0)))"
  proof (auto)
    fix i j assume 1: "\<forall>i' j'. i' < j' \<and> \<not> is_zero_row i' A' \<and> \<not> is_zero_row j' A' 
      \<longrightarrow> (LEAST n'. A' $h i' $h n' \<noteq> 0) < (LEAST n'. A' $h j' $h n' \<noteq> 0)"
      and ij: "i < j" and j: "j < dim_row A" and i0: "\<not> is_zero_row_JNF i A"
      and j0: "\<not> is_zero_row_JNF j A"
    let ?i' = "Mod_Type.from_nat i::'m"
    let ?j' = "Mod_Type.from_nat j::'m"
    have ii'[transfer_rule]: "Mod_Type_Connect.HMA_I i ?i'"
      unfolding Mod_Type_Connect.HMA_I_def using Mod_Type.to_nat_from_nat_id[of i]
      using ij j AA' Mod_Type_Connect.dim_row_transfer_rule less_trans by fastforce
    have jj'[transfer_rule]: "Mod_Type_Connect.HMA_I j ?j'" 
      unfolding Mod_Type_Connect.HMA_I_def  using Mod_Type.to_nat_from_nat_id[of j]
      using ij j AA' Mod_Type_Connect.dim_row_transfer_rule less_trans by fastforce
    have i'0: "\<not> is_zero_row ?i' A'" using i0 by transfer
    have j'0: "\<not> is_zero_row ?j' A'" using j0 by transfer
    have i'j': "?i' < ?j'"
      using AA' Mod_Type_Connect.dim_row_transfer_rule from_nat_mono ij j by fastforce
    have l1l2: "(LEAST n'. A' $h ?i' $h n' \<noteq> 0) < (LEAST n'. A' $h ?j' $h n' \<noteq> 0)"
      using 1 i'0 j'0 i'j' by auto
    define l1 where "l1 = (LEAST n'. A' $h ?i' $h n' \<noteq> 0)"
    define l2 where "l2 = (LEAST n'. A' $h ?j' $h n' \<noteq> 0)"
    let ?least_n1 = "Mod_Type.to_nat l1"
    let ?least_n2 = "Mod_Type.to_nat l2"
    have l1[transfer_rule]: "Mod_Type_Connect.HMA_I ?least_n1 l1" and [transfer_rule]: "Mod_Type_Connect.HMA_I ?least_n2 l2"
      unfolding Mod_Type_Connect.HMA_I_def by auto
    have "(LEAST n. A $$ (i, n) \<noteq> 0) = ?least_n1" 
    proof (rule Least_equality)
      obtain n' where n'1: "A $$ (i,n') \<noteq> 0" and n'2: "n'<dim_col A"
        using i0 unfolding is_zero_row_JNF_def by auto
      let ?n' = "Mod_Type.from_nat n'::'n"
      have n'n'[transfer_rule]: "Mod_Type_Connect.HMA_I n' ?n'"
        unfolding Mod_Type_Connect.HMA_I_def using Mod_Type.to_nat_from_nat_id n'2
        using AA' Mod_Type_Connect.dim_col_transfer_rule by fastforce
      have "index_hma A' ?i' ?n' \<noteq> 0" using n'1 by transfer
      hence A'i'n': "A' $h ?i' $h ?n' \<noteq> 0" unfolding index_hma_def by simp
      have least_le_n': "(LEAST n. A $$ (i, n) \<noteq> 0)  \<le> n'" by (simp add: Least_le n'1)
      have l1_le_n': "l1 \<le> ?n'" by (simp add: A'i'n' Least_le l1_def)
      have "A $$ (i, ?least_n1) = index_hma A' ?i' l1" by (transfer, simp)
      also have "... = A' $h mod_type_class.from_nat i $h l1" unfolding index_hma_def by simp
      also have "... \<noteq> 0" unfolding l1_def by (metis (mono_tags, lifting) LeastI i'0 is_zero_row_def')
      finally show "A $$ (i, mod_type_class.to_nat l1) \<noteq> 0" .
      fix y assume Aiy: "A $$ (i, y) \<noteq> 0"
      let ?y' = "Mod_Type.from_nat y::'n"
      show "Mod_Type.to_nat l1 \<le> y"
      proof (cases "y\<le>n'")
        case True
        hence y: "y < dim_col A" using n'2 by auto
        have yy'[transfer_rule]: "Mod_Type_Connect.HMA_I y ?y'" unfolding Mod_Type_Connect.HMA_I_def
          apply (rule Mod_Type.to_nat_from_nat_id[symmetric])
          using y Mod_Type_Connect.dim_col_transfer_rule[OF AA'] by auto
        have "Mod_Type.to_nat l1 \<le> Mod_Type.to_nat ?y'"
        proof (rule to_nat_mono')
          have "index_hma A' ?i' ?y' \<noteq> 0" using Aiy by transfer
          hence "A' $h ?i' $h ?y' \<noteq> 0" unfolding index_hma_def by simp
          thus "l1 \<le> ?y'" unfolding l1_def by (simp add: Least_le)
        qed
          then show ?thesis by (metis Mod_Type_Connect.HMA_I_def yy')
        next
          case False
          hence "n' < y" by auto
          then show ?thesis
            by (metis False Mod_Type_Connect.HMA_I_def dual_order.trans l1_le_n' linear n'n' to_nat_mono')
        qed
      qed
      moreover have "(LEAST n. A $$ (j, n) \<noteq> 0) = ?least_n2"
      proof (rule Least_equality)
        obtain n' where n'1: "A $$ (j,n') \<noteq> 0" and n'2: "n'<dim_col A"
        using j0 unfolding is_zero_row_JNF_def by auto
      let ?n' = "Mod_Type.from_nat n'::'n"
      have n'n'[transfer_rule]: "Mod_Type_Connect.HMA_I n' ?n'" 
        unfolding Mod_Type_Connect.HMA_I_def using Mod_Type.to_nat_from_nat_id n'2
        using AA' Mod_Type_Connect.dim_col_transfer_rule by fastforce
      have "index_hma A' ?j' ?n' \<noteq> 0" using n'1 by transfer
      hence A'i'n': "A' $h ?j' $h ?n' \<noteq> 0" unfolding index_hma_def by simp
      have least_le_n': "(LEAST n. A $$ (j, n) \<noteq> 0)  \<le> n'" by (simp add: Least_le n'1)
      have l1_le_n': "l2 \<le> ?n'" by (simp add: A'i'n' Least_le l2_def)
      have "A $$ (j, ?least_n2) = index_hma A' ?j' l2" by (transfer, simp)
      also have "... = A' $h ?j' $h l2" unfolding index_hma_def by simp
      also have "... \<noteq> 0" unfolding l2_def by (metis (mono_tags, lifting) LeastI j'0 is_zero_row_def')
      finally show "A $$ (j, mod_type_class.to_nat l2) \<noteq> 0" .
      fix y assume Aiy: "A $$ (j, y) \<noteq> 0"
      let ?y' = "Mod_Type.from_nat y::'n"
      show "Mod_Type.to_nat l2 \<le> y"
      proof (cases "y\<le>n'")
        case True
        hence y: "y < dim_col A" using n'2 by auto
        have yy'[transfer_rule]: "Mod_Type_Connect.HMA_I y ?y'" unfolding Mod_Type_Connect.HMA_I_def
          apply (rule Mod_Type.to_nat_from_nat_id[symmetric])
          using y Mod_Type_Connect.dim_col_transfer_rule[OF AA'] by auto
        have "Mod_Type.to_nat l2 \<le> Mod_Type.to_nat ?y'"
        proof (rule to_nat_mono')
          have "index_hma A' ?j' ?y' \<noteq> 0" using Aiy by transfer
          hence "A' $h ?j' $h ?y' \<noteq> 0" unfolding index_hma_def by simp
          thus "l2 \<le> ?y'" unfolding l2_def by (simp add: Least_le)
        qed
          then show ?thesis by (metis Mod_Type_Connect.HMA_I_def yy')
        next
          case False
          hence "n' < y" by auto
          then show ?thesis
            by (metis False Mod_Type_Connect.HMA_I_def dual_order.trans l1_le_n' linear n'n' to_nat_mono')
        qed
      qed
      ultimately show "(LEAST n. A $$ (i, n) \<noteq> 0) < (LEAST n. A $$ (j, n) \<noteq> 0)"
        using l1l2 unfolding l1_def l2_def by (simp add: to_nat_mono)
    next
      fix i' j' assume 1: "\<forall>i j. i < j \<and> j < dim_row A \<and> \<not> is_zero_row_JNF i A \<and> \<not> is_zero_row_JNF j A 
      \<longrightarrow> (LEAST n. A $$ (i, n) \<noteq> 0) < (LEAST n. A $$ (j, n) \<noteq> 0)"
       and i'j': "i' < j'" and i': "\<not> is_zero_row i' A'" and j': "\<not> is_zero_row j' A'"
      let ?i = "Mod_Type.to_nat i'"
      let ?j = "Mod_Type.to_nat j'"
      have [transfer_rule]: "Mod_Type_Connect.HMA_I ?i i'" 
        and [transfer_rule]: "Mod_Type_Connect.HMA_I ?j j'"
        unfolding Mod_Type_Connect.HMA_I_def by auto
      have i: "\<not> is_zero_row_JNF ?i A" using i' by transfer'
      have j: "\<not> is_zero_row_JNF ?j A" using j' by transfer'
      have ij: "?i < ?j" using i'j' to_nat_mono by blast
      have j_dim_row: "?j < dim_row A" 
        using AA' Mod_Type_Connect.dim_row_transfer_rule mod_type_class.to_nat_less_card by fastforce
      have least_ij: "(LEAST n. A $$ (?i, n) \<noteq> 0) < (LEAST n. A $$ (?j, n) \<noteq> 0)"
        using i j ij j_dim_row 1 by auto
      define l1 where "l1 = (LEAST n'. A $$ (?i, n') \<noteq> 0)"
      define l2 where "l2 = (LEAST n'. A $$ (?j, n') \<noteq> 0)"
      let ?least_n1 = "Mod_Type.from_nat l1::'n"
      let ?least_n2 = "Mod_Type.from_nat l2::'n"
      have l1_dim_col: "l1 < dim_col A"
        by (smt is_zero_row_JNF_def j l1_def leI le_less_trans least_ij less_trans not_less_Least)
      have l2_dim_col: "l2 < dim_col A"
        by (metis (mono_tags, lifting) Least_le is_zero_row_JNF_def j l2_def le_less_trans)
      have [transfer_rule]: "Mod_Type_Connect.HMA_I l1 ?least_n1" unfolding Mod_Type_Connect.HMA_I_def
        using AA' Mod_Type_Connect.dim_col_transfer_rule l1_dim_col Mod_Type.to_nat_from_nat_id
        by fastforce
      have [transfer_rule]: "Mod_Type_Connect.HMA_I l2 ?least_n2" unfolding Mod_Type_Connect.HMA_I_def
        using AA' Mod_Type_Connect.dim_col_transfer_rule l2_dim_col Mod_Type.to_nat_from_nat_id
        by fastforce
      have "(LEAST n. A' $h i' $h n \<noteq> 0) = ?least_n1"
      proof (rule Least_equality)
        obtain n' where n'1: "A' $h i' $h n' \<noteq> 0" using i' unfolding is_zero_row_def' by auto
        have "A' $h i' $h ?least_n1 = index_hma A' i' ?least_n1" unfolding index_hma_def by simp
        also have "... = A$$ (?i, l1)"  by (transfer, simp)
        also have "... \<noteq> 0" by (metis (mono_tags, lifting) LeastI i is_zero_row_JNF_def l1_def)
        finally show "A' $h i' $h ?least_n1 \<noteq> 0" .
      next
        fix y assume y: "A' $h i' $h y \<noteq> 0"
        let ?y' = "Mod_Type.to_nat y"
        have [transfer_rule]: "Mod_Type_Connect.HMA_I ?y' y" unfolding Mod_Type_Connect.HMA_I_def by simp
        have "?least_n1 \<le> Mod_Type.from_nat ?y'"
        proof (unfold l1_def, rule from_nat_mono')                      
          show "Mod_Type.to_nat y < CARD('n)" by (simp add: mod_type_class.to_nat_less_card)
          have *: "A $$ (mod_type_class.to_nat i', mod_type_class.to_nat y) \<noteq> 0" 
            using y[unfolded index_hma_def[symmetric]] by transfer'
          show "(LEAST n'. A $$ (mod_type_class.to_nat i', n') \<noteq> 0) \<le> mod_type_class.to_nat y" 
            by (rule Least_le, simp add: *)
        qed
        also have "... = y" by simp
        finally show "?least_n1 \<le> y" .
      qed
      moreover have "(LEAST n. A' $h j' $h n \<noteq> 0) = ?least_n2"
      proof (rule Least_equality)
        obtain n' where n'1: "A' $h j' $h n' \<noteq> 0" using j' unfolding is_zero_row_def' by auto
        have "A' $h j' $h ?least_n2 = index_hma A' j' ?least_n2" unfolding index_hma_def by simp
        also have "... = A$$ (?j, l2)"  by (transfer, simp)
        also have "... \<noteq> 0" by (metis (mono_tags, lifting) LeastI j is_zero_row_JNF_def l2_def)
        finally show "A' $h j' $h ?least_n2 \<noteq> 0" .
      next
        fix y assume y: "A' $h j' $h y \<noteq> 0"
        let ?y' = "Mod_Type.to_nat y"
        have [transfer_rule]: "Mod_Type_Connect.HMA_I ?y' y" unfolding Mod_Type_Connect.HMA_I_def by simp
        have "?least_n2 \<le> Mod_Type.from_nat ?y'"
        proof (unfold l2_def, rule from_nat_mono')                      
          show "Mod_Type.to_nat y < CARD('n)" by (simp add: mod_type_class.to_nat_less_card)
          have *: "A $$ (mod_type_class.to_nat j', mod_type_class.to_nat y) \<noteq> 0" 
            using y[unfolded index_hma_def[symmetric]] by transfer'
          show "(LEAST n'. A $$ (mod_type_class.to_nat j', n') \<noteq> 0) \<le> mod_type_class.to_nat y" 
            by (rule Least_le, simp add: *)
        qed
        also have "... = y" by simp
        finally show "?least_n2 \<le> y" .
      qed
      ultimately show "(LEAST n. A' $h i' $h n \<noteq> 0) < (LEAST n. A' $h j' $h n \<noteq> 0)" using least_ij
        unfolding l1_def l2_def
        using AA' Mod_Type_Connect.dim_col_transfer_rule from_nat_mono l2_def l2_dim_col
        by fastforce
    qed
   show ?case unfolding echelon_form_JNF_def echelon_form_def' using 1 2 by auto
qed


definition Hermite_JNF :: "'a::{bezout_ring_div,normalization_semidom} set \<Rightarrow> ('a \<Rightarrow> 'a set) \<Rightarrow> 'a mat \<Rightarrow> bool"
  where "Hermite_JNF associates residues A = (
  Complete_set_non_associates associates \<and> (Complete_set_residues residues) \<and> echelon_form_JNF A 
  \<and> (\<forall>i<dim_row A. \<not> is_zero_row_JNF i A \<longrightarrow> A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0) \<in> associates)
  \<and> (\<forall>i<dim_row A. \<not> is_zero_row_JNF i A \<longrightarrow> (\<forall>j. j<i \<longrightarrow> A $$ (j, (LEAST n. A $$ (i, n) \<noteq> 0)) 
     \<in> residues (A $$ (i,(LEAST n. A $$ (i,n) \<noteq> 0)))
  )))"


lemma HMA_LEAST[transfer_rule]:
  assumes AA': "(Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) A A'"
  and ii': "Mod_Type_Connect.HMA_I i i'" and zero_i: "\<not> is_zero_row_JNF i A"
shows "Mod_Type_Connect.HMA_I (LEAST n. A $$ (i, n) \<noteq> 0) (LEAST n. index_hma A' i' n \<noteq> 0)"
proof -
  define l where "l = (LEAST n'. A' $h i' $h n' \<noteq> 0)"
  let ?least_n2 = "Mod_Type.to_nat l"
  note AA'[transfer_rule] ii'[transfer_rule]
  have [transfer_rule]: "Mod_Type_Connect.HMA_I ?least_n2 l"
    by (simp add: Mod_Type_Connect.HMA_I_def)
  have zero_i': "\<not> is_zero_row i' A'" using zero_i by transfer
  have "(LEAST n. A $$ (i, n) \<noteq> 0) = ?least_n2"
      proof (rule Least_equality)
        obtain n' where n'1: "A $$ (i,n') \<noteq> 0" and n'2: "n'<dim_col A"
        using zero_i unfolding is_zero_row_JNF_def by auto
      let ?n' = "Mod_Type.from_nat n'::'n"
      have n'n'[transfer_rule]: "Mod_Type_Connect.HMA_I n' ?n'" 
        unfolding Mod_Type_Connect.HMA_I_def using Mod_Type.to_nat_from_nat_id n'2
        using AA' Mod_Type_Connect.dim_col_transfer_rule by fastforce
      have "index_hma A' i' ?n' \<noteq> 0" using n'1 by transfer
      hence A'i'n': "A' $h i' $h ?n' \<noteq> 0" unfolding index_hma_def by simp
      have least_le_n': "(LEAST n. A $$ (i, n) \<noteq> 0)  \<le> n'" by (simp add: Least_le n'1)
      have l1_le_n': "l \<le> ?n'" by (simp add: A'i'n' Least_le l_def)
      have "A $$ (i, ?least_n2) = index_hma A' i' l" by (transfer, simp)
      also have "... = A' $h i' $h l" unfolding index_hma_def by simp
      also have "... \<noteq> 0" unfolding l_def by (metis (mono_tags) A'i'n' LeastI)
      finally show "A $$ (i, mod_type_class.to_nat l) \<noteq> 0" .
      fix y assume Aiy: "A $$ (i, y) \<noteq> 0"
      let ?y' = "Mod_Type.from_nat y::'n"
      show "Mod_Type.to_nat l \<le> y"
      proof (cases "y\<le>n'")
        case True
        hence y: "y < dim_col A" using n'2 by auto
        have yy'[transfer_rule]: "Mod_Type_Connect.HMA_I y ?y'" unfolding Mod_Type_Connect.HMA_I_def
          apply (rule Mod_Type.to_nat_from_nat_id[symmetric])
          using y Mod_Type_Connect.dim_col_transfer_rule[OF AA'] by auto
        have "Mod_Type.to_nat l \<le> Mod_Type.to_nat ?y'"
        proof (rule to_nat_mono')
          have "index_hma A' i' ?y' \<noteq> 0" using Aiy by transfer
          hence "A' $h i' $h ?y' \<noteq> 0" unfolding index_hma_def by simp
          thus "l \<le> ?y'" unfolding l_def by (simp add: Least_le)
        qed
          then show ?thesis by (metis Mod_Type_Connect.HMA_I_def yy')
        next
          case False
          hence "n' < y" by auto
          then show ?thesis
            by (metis False Mod_Type_Connect.HMA_I_def dual_order.trans l1_le_n' linear n'n' to_nat_mono')
        qed
      qed
      thus ?thesis unfolding Mod_Type_Connect.HMA_I_def l_def index_hma_def by auto
qed


lemma element_least_not_zero_eq_HMA_JNF:
  fixes A':: "'a :: comm_ring_1 ^ 'n :: mod_type ^ 'm :: mod_type"
  assumes AA': "Mod_Type_Connect.HMA_M A A'" and jj': "Mod_Type_Connect.HMA_I j j'"
    and ii': "Mod_Type_Connect.HMA_I i i'" and zero_i': "\<not> is_zero_row i' A'"
  shows "A $$ (j, LEAST n. A $$ (i, n) \<noteq> 0) = A' $h j' $h (LEAST n. A' $h i' $h n \<noteq> 0)" 
proof -
  note AA'[transfer_rule] jj'[transfer_rule] ii'[transfer_rule]
  have [transfer_rule]: "Mod_Type_Connect.HMA_I (LEAST n. A $$ (i, n) \<noteq> 0) (LEAST n. index_hma A' i' n \<noteq> 0)"
    by (rule HMA_LEAST[OF AA' ii'], insert zero_i', transfer, simp)
  have "A' $h j' $h (LEAST n. A' $h i' $h n \<noteq> 0) = index_hma A' j' (LEAST n. index_hma A' i' n \<noteq> 0)" 
    unfolding index_hma_def by simp
  also have "... = A $$ (j, LEAST n. A $$ (i, n) \<noteq> 0)" by (transfer', simp)
  finally show ?thesis by simp
qed


lemma HMA_Hermite[transfer_rule]:
  shows "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: {bezout_ring_div,normalization_semidom} ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) ===> (=)) 
  (Hermite_JNF associates residues) (Hermite associates residues)"
proof (intro rel_funI, goal_cases)
  case (1 A A')
  note AA' = "1"(1)[transfer_rule]
  have 1: "echelon_form A' = echelon_form_JNF A" by (transfer, simp)
  have 2: "(\<forall>i<dim_row A. \<not> is_zero_row_JNF i A \<longrightarrow> A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0) \<in> associates) =
  (\<forall>i. \<not> is_zero_row i A' \<longrightarrow> A' $h i $h (LEAST n. A' $h i $h n \<noteq> 0) \<in> associates)" (is "?lhs = ?rhs")
  proof 
    assume lhs: "?lhs"
    show "?rhs"
    proof (rule allI, rule impI)
      fix i' assume zero_i': "\<not> is_zero_row i' A'" 
      let ?i = "Mod_Type.to_nat i'"
      have ii'[transfer_rule]: "Mod_Type_Connect.HMA_I ?i i'" unfolding Mod_Type_Connect.HMA_I_def by simp
      have [simp]: "?i < dim_row A" using Mod_Type.to_nat_less_card[of i']
        using AA' Mod_Type_Connect.dim_row_transfer_rule by fastforce
      have zero_i: "\<not> is_zero_row_JNF ?i A" using zero_i' by transfer
      have [transfer_rule]: "Mod_Type_Connect.HMA_I (LEAST n. A $$ (?i, n) \<noteq> 0) (LEAST n. index_hma A' i' n \<noteq> 0)"
        by (rule HMA_LEAST[OF AA' ii'], insert zero_i', transfer, simp)
      have "A' $h i' $h (LEAST n. A' $h i' $h n \<noteq> 0) = A $$ (?i, LEAST n. A $$ (?i, n) \<noteq> 0)"
        by (rule element_least_not_zero_eq_HMA_JNF[OF AA' ii' ii' zero_i', symmetric])
      also have "... \<in> associates" using lhs zero_i by simp  
      finally show "A' $h i' $h (LEAST n. A' $h i' $h n \<noteq> 0) \<in> associates" .
    qed
  next
    assume rhs: "?rhs"
    show "?lhs"
    proof (rule allI, rule impI, rule impI)
      fix i assume zero_i: "\<not> is_zero_row_JNF i A" and i: "i < dim_row A"
      let ?i' = "Mod_Type.from_nat i :: 'm"
      have ii'[transfer_rule]: "Mod_Type_Connect.HMA_I i ?i'" unfolding Mod_Type_Connect.HMA_I_def
        using Mod_Type.to_nat_from_nat_id AA' Mod_Type_Connect.dim_row_transfer_rule i by fastforce
      have zero_i': "\<not> is_zero_row ?i' A'" using zero_i by transfer
      have "A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0) = A' $h ?i' $h (LEAST n. A' $h ?i' $h n \<noteq> 0)"   
        by (rule element_least_not_zero_eq_HMA_JNF[OF AA' ii' ii' zero_i'])
      also have "... \<in> associates" using rhs zero_i' i by simp  
      finally show "A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0) \<in> associates" .
    qed
  qed
  have 3: "(\<forall>i<dim_row A. \<not> is_zero_row_JNF i A \<longrightarrow> (\<forall>j<i. A $$ (j, LEAST n. A $$ (i, n) \<noteq> 0) 
            \<in> residues (A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0)))) =
            (\<forall>i. \<not> is_zero_row i A' \<longrightarrow> (\<forall>j<i. A' $h j $h (LEAST n. A' $h i $h n \<noteq> 0)
            \<in> residues (A' $h i $h (LEAST n. A' $h i $h n \<noteq> 0))))" (is "?lhs = ?rhs")
  proof 
    assume lhs: "?lhs"
    show "?rhs"
    proof (rule allI, rule impI, rule allI, rule impI)
      fix i' j' :: 'm
      assume zero_i': "\<not> is_zero_row i' A'" and j'i': "j' < i'" 
      let ?i = "Mod_Type.to_nat i'"
      have ii'[transfer_rule]: "Mod_Type_Connect.HMA_I ?i i'" unfolding Mod_Type_Connect.HMA_I_def by simp
      have i: "?i < dim_row A"
        using AA' Mod_Type_Connect.dim_row_transfer_rule mod_type_class.to_nat_less_card
        by fastforce
      have zero_i: "\<not> is_zero_row_JNF ?i A" using zero_i' by transfer'
      let ?j = "Mod_Type.to_nat j'"
      have jj'[transfer_rule]: "Mod_Type_Connect.HMA_I ?j j'" unfolding Mod_Type_Connect.HMA_I_def by simp
      have ji: "?j<?i" using j'i' to_nat_mono by blast
      have eq1: "A $$ (?j, LEAST n. A $$ (?i, n) \<noteq> 0) = A' $h j' $h (LEAST n. A' $h i' $h n \<noteq> 0)"
        by (rule element_least_not_zero_eq_HMA_JNF[OF AA' jj' ii' zero_i'])
      have eq2: "A $$ (?i, LEAST n. A $$ (?i, n) \<noteq> 0) = A' $h i' $h (LEAST n. A' $h i' $h n \<noteq> 0)"
        by (rule element_least_not_zero_eq_HMA_JNF[OF AA' ii' ii' zero_i'])
      show "A' $h j' $h (LEAST n. A' $h i' $h n \<noteq> 0) \<in> residues (A' $h i' $h (LEAST n. A' $h i' $h n \<noteq> 0))"
        using lhs eq1 eq2 ji i zero_i by fastforce
    qed
  next
    assume rhs: "?rhs"
    show "?lhs"
    proof (safe)
      fix i j assume i: "i < dim_row A" and zero_i: "\<not> is_zero_row_JNF i A" and ji: "j < i"
      let ?i' = "Mod_Type.from_nat i :: 'm"
      have ii'[transfer_rule]: "Mod_Type_Connect.HMA_I i ?i'" unfolding Mod_Type_Connect.HMA_I_def
        using Mod_Type.to_nat_from_nat_id AA' Mod_Type_Connect.dim_row_transfer_rule i by fastforce
      have zero_i': "\<not> is_zero_row ?i' A'" using zero_i by transfer
      let ?j' = "Mod_Type.from_nat j :: 'm"
      have j'i': "?j' < ?i'" using AA' Mod_Type_Connect.dim_row_transfer_rule from_nat_mono i ji
        by fastforce
      have jj'[transfer_rule]: "Mod_Type_Connect.HMA_I j ?j'" unfolding Mod_Type_Connect.HMA_I_def
        using Mod_Type.to_nat_from_nat_id[of j, where ?'a='m] AA' 
          Mod_Type_Connect.dim_row_transfer_rule[OF AA'] j'i' i ji by auto
      have zero_i': "\<not> is_zero_row ?i' A'" using zero_i by transfer
      have eq1: "A $$ (j, LEAST n. A $$ (i, n) \<noteq> 0) = A' $h ?j' $h (LEAST n. A' $h ?i' $h n \<noteq> 0)"
        by (rule element_least_not_zero_eq_HMA_JNF[OF AA' jj' ii' zero_i'])
      have eq2: "A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0) = A' $h ?i' $h (LEAST n. A' $h ?i' $h n \<noteq> 0)"
        by (rule element_least_not_zero_eq_HMA_JNF[OF AA' ii' ii' zero_i'])
      show "A $$ (j, LEAST n. A $$ (i, n) \<noteq> 0) \<in> residues (A $$ (i, LEAST n. A $$ (i, n) \<noteq> 0))"
        using rhs eq1 eq2 j'i' i zero_i' by fastforce
    qed
  qed
  show "Hermite_JNF associates residues A = Hermite associates residues A'"
    unfolding Hermite_def Hermite_JNF_def 
    using 1 2 3 by auto
qed


corollary HMA_Hermite2[transfer_rule]:
  shows "((=) ===> (=) ===> (Mod_Type_Connect.HMA_M :: _ 
  \<Rightarrow> 'a :: {bezout_ring_div,normalization_semidom} ^ 'n :: mod_type ^ 'm :: mod_type \<Rightarrow> _) ===> (=)) 
  (Hermite_JNF) (Hermite)"
  by (simp add: HMA_Hermite rel_funI)


text \<open>Once the definitions of both libraries are connected, we start to move the theorem about
the uniqueness of the Hermite normal form (stated in HOL Analysis, named @{text "Hermite_unique"})
to JNF.\<close>


text \<open>Using the previous transfer rules, we get an statement in JNF. However, the matrices
have @{text "CARD('n::mod_type)"} rows and columns. We want to get rid of that type variable and
just state that they are of dimension $n \times n$ (expressed via the predicate @{text "carrier_mat"}\<close>

lemma Hermite_unique_JNF':
  fixes A::"'a::{bezout_ring_div,normalization_euclidean_semiring,unique_euclidean_ring} mat"
  assumes "A \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
    "P \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
    "H \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
    "Q \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
    "K \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
  assumes "A = P * H"
    and "A = Q * K" and "invertible_mat A" and "invertible_mat P" 
    and "invertible_mat Q" and "Hermite_JNF associates res H" and "Hermite_JNF associates res K"
shows "H = K" 
proof -
  define A' where "A' = (Mod_Type_Connect.to_hma\<^sub>m A :: 'a ^'n :: mod_type ^'n :: mod_type)"
  define P' where "P' = (Mod_Type_Connect.to_hma\<^sub>m P :: 'a ^'n :: mod_type ^'n :: mod_type)"
  define H' where "H' = (Mod_Type_Connect.to_hma\<^sub>m H :: 'a ^'n :: mod_type ^'n :: mod_type)"
  define Q' where "Q' = (Mod_Type_Connect.to_hma\<^sub>m Q :: 'a ^'n :: mod_type ^'n :: mod_type)"
  define K' where "K' = (Mod_Type_Connect.to_hma\<^sub>m K :: 'a ^'n :: mod_type ^'n :: mod_type)"
  have AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'" unfolding Mod_Type_Connect.HMA_M_def using assms A'_def by auto  
  have PP'[transfer_rule]: "Mod_Type_Connect.HMA_M P P'" unfolding Mod_Type_Connect.HMA_M_def using assms P'_def by auto
  have HH'[transfer_rule]: "Mod_Type_Connect.HMA_M H H'" unfolding Mod_Type_Connect.HMA_M_def using assms H'_def by auto
  have QQ'[transfer_rule]: "Mod_Type_Connect.HMA_M Q Q'" unfolding Mod_Type_Connect.HMA_M_def using assms Q'_def by auto
  have KK'[transfer_rule]: "Mod_Type_Connect.HMA_M K K'" unfolding Mod_Type_Connect.HMA_M_def using assms K'_def by auto
  have A_PH: "A' = P' ** H'" using assms by transfer
  moreover have A_QK: "A' = Q' ** K'" using assms by transfer
  moreover have inv_A: "invertible A'" using assms by transfer
  moreover have inv_P: "invertible P'" using assms by transfer
  moreover have inv_Q: "invertible Q'" using assms by transfer
  moreover have H: "Hermite associates res H'" using assms by transfer
  moreover have K: "Hermite associates res K'" using assms by transfer
  ultimately have "H' = K'" using Hermite_unique by blast
  thus "H=K" by transfer
qed




text \<open>Since the @{text "mod_type"} restriction relies on many things, the shortcut is to use 
the @{text "mod_ring"} typedef developed in the Berlekamp-Zassenhaus development. 
This type definition allows us to apply local type definitions easily.
Since @{text "mod_ring"} is just an instance of @{text "mod_type"}, it is straightforward to
obtain the following lemma, where @{text "CARD('n::mod_type)"} has now been substituted by
@{text "CARD('n::nontriv mod_ring)"}\<close>

corollary Hermite_unique_JNF_with_nontriv_mod_ring:
  fixes A::"'a::{bezout_ring_div,normalization_euclidean_semiring,unique_euclidean_ring} mat"
  assumes "A \<in> carrier_mat CARD('n) CARD('n::nontriv mod_ring)"
    "P \<in> carrier_mat CARD('n) CARD('n)"
    "H \<in> carrier_mat CARD('n) CARD('n)"
    "Q \<in> carrier_mat CARD('n) CARD('n)"
    "K \<in> carrier_mat CARD('n) CARD('n)"
  assumes "A = P * H"
    and "A = Q * K" and "invertible_mat A" and "invertible_mat P" 
    and "invertible_mat Q" and "Hermite_JNF associates res H" and "Hermite_JNF associates res K"
shows "H = K" using Hermite_unique_JNF' assms by (smt CARD_mod_ring)

text \<open>Now, we assume in a context that there exists a type text @{text "'b"} of cardinality $n$
and we prove inside this context the lemma.\<close>

context
  fixes n::nat
  assumes local_typedef: "\<exists>(Rep :: ('b \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<n :: int}"
  and p: "n>1"
begin

private lemma type_to_set:
  shows "class.nontriv TYPE('b)" (is ?a) and "n=CARD('b)" (is ?b)
proof -
  from local_typedef obtain Rep::"('b \<Rightarrow> int)" and Abs 
    where t: "type_definition Rep Abs {0..<n :: int}" by auto
  have "card (UNIV :: 'b set) = card {0..<n}" using t type_definition.card by fastforce
  also have "... = n" by auto
  finally show ?b ..
  then show ?a unfolding class.nontriv_def using p by auto
qed


lemma Hermite_unique_JNF_aux:
  fixes A::"'a::{bezout_ring_div,normalization_euclidean_semiring,unique_euclidean_ring} mat"
  assumes "A \<in> carrier_mat n n"
    "P \<in> carrier_mat n n"
    "H \<in> carrier_mat n n"
    "Q \<in> carrier_mat n n "
    "K \<in> carrier_mat n n"
  assumes "A = P * H"
    and "A = Q * K" and "invertible_mat A" and "invertible_mat P" 
    and "invertible_mat Q" and "Hermite_JNF associates res H" and "Hermite_JNF associates res K"
shows "H = K"
  using Hermite_unique_JNF_with_nontriv_mod_ring[unfolded CARD_mod_ring,
      internalize_sort "'n::nontriv", where ?'a='b]
  unfolding type_to_set(2)[symmetric] using type_to_set(1) assms by blast
end                     

text \<open>Now, we cancel the local type definition of the previous context. 
Since the @{text "mod_type"} restriction imposes the type to have cardinality greater than 1, 
the cases $n=0$ and $n=1$ must be proved separately (they are trivial)\<close>

lemma Hermite_unique_JNF:
  fixes A::"'a::{bezout_ring_div,normalization_euclidean_semiring,unique_euclidean_ring} mat"
  assumes A: "A \<in> carrier_mat n n" and P: "P \<in> carrier_mat n n" and H: "H \<in> carrier_mat n n"
   and Q: "Q \<in> carrier_mat n n" and K: "K \<in> carrier_mat n n"
 assumes A_PH: "A = P * H" and A_QK: "A = Q * K"
   and inv_A: "invertible_mat A" and inv_P: "invertible_mat P" and inv_Q: "invertible_mat Q"
   and HNF_H: "Hermite_JNF associates res H" and HNF_K: "Hermite_JNF associates res K"
  shows "H = K"
proof (cases "n=0 \<or> n=1")
  case True note zero_or_one = True
  show ?thesis
  proof (cases "n=0")
    case True
    then show ?thesis using assms by auto
  next
    case False
    have CS_A: "Complete_set_non_associates associates" using HNF_H unfolding Hermite_JNF_def by simp
    have H: "H \<in> carrier_mat 1 1" and K: "K\<in> carrier_mat 1 1" using False zero_or_one assms by auto
    have det_P_dvd_1: "Determinant.det P dvd 1" using invertible_iff_is_unit_JNF inv_P P by blast
    have det_Q_dvd_1: "Determinant.det Q dvd 1" using invertible_iff_is_unit_JNF inv_Q Q by blast
    have PH_QK: "Determinant.det P * Determinant.det H = Determinant.det Q * Determinant.det K"
      using Determinant.det_mult assms by metis
    hence "Determinant.det P * H $$ (0,0) = Determinant.det Q * K $$ (0,0)"
      by (metis H K determinant_one_element)
    obtain u where uH_K: "u * H $$(0,0) = K $$ (0,0)" and unit_u: "is_unit u"
      by (metis (no_types, hide_lams) H K PH_QK algebraic_semidom_class.dvd_mult_unit_iff det_P_dvd_1 
          det_Q_dvd_1 det_singleton dvdE dvd_mult_cancel_left mult.commute mult.right_neutral one_dvd)
    have H00_not_0: "H $$ (0,0) \<noteq> 0"
      by (metis A A_PH Determinant.det_mult False H P determinant_one_element inv_A
          invertible_iff_is_unit_JNF mult_not_zero not_is_unit_0 zero_or_one)
    hence LEAST_H: "(LEAST n. H $$ (0,n) \<noteq> 0) = 0" by simp
    have H00: "H $$ (0,0) \<in> associates" using HNF_H LEAST_H H H00_not_0 
      unfolding Hermite_JNF_def is_zero_row_JNF_def by auto
    have K00_not_0: "K $$ (0,0) \<noteq> 0"
      by (metis A A_QK Determinant.det_mult False K Q determinant_one_element inv_A
          invertible_iff_is_unit_JNF mult_not_zero not_is_unit_0 zero_or_one)
    hence LEAST_K: "(LEAST n. K $$ (0,n) \<noteq> 0) = 0" by simp
    have K00: "K $$ (0,0) \<in> associates" using HNF_K LEAST_K K K00_not_0 
      unfolding Hermite_JNF_def is_zero_row_JNF_def by auto
    have ass_H00_K00: "normalize (H $$ (0,0)) = normalize (K $$ (0,0))"
      by (metis normalize_mult_unit_left uH_K unit_u)
    have H00_eq_K00: "H $$ (0,0) = K $$ (0,0)" 
      using in_Ass_not_associated[OF CS_A H00 K00] ass_H00_K00 by auto
    show ?thesis by (rule eq_matI, insert H K H00_eq_K00, auto)
  qed
next
  case False
  hence "{0..<int n} \<noteq> {}" by auto
  moreover have "n>1" using False by simp
  ultimately show ?thesis using Hermite_unique_JNF_aux[cancel_type_definition] assms by metis (*Cancel local type definition*)
qed

end

text \<open>From here on, we apply the same approach to move the new generalized statement about
the uniqueness Hermite normal form, i.e., the version restricted to integer matrices, but imposing
invertibility over the rationals.\<close>

(*TODO: move to Mod_Type_Connect in SNF development. 
  There are two definitions of map_matrix, one in HMA_Connect and one in Finite_Cartesian_Product, 
  but they are the same.*)
lemma HMA_map_matrix [transfer_rule]: 
  "((=) ===> Mod_Type_Connect.HMA_M ===> Mod_Type_Connect.HMA_M) map_mat map_matrix"
  unfolding map_vector_def map_matrix_def[abs_def] map_mat_def[abs_def] 
    Mod_Type_Connect.HMA_M_def Mod_Type_Connect.from_hma\<^sub>m_def
  by auto



lemma Hermite_unique_generalized_JNF':
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
    "P \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
    "H \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
    "Q \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
    "K \<in> carrier_mat CARD('n::mod_type) CARD('n::mod_type)"
  assumes "A = P * H"
    and "A = Q * K" and "invertible_mat (map_mat rat_of_int A)" and "invertible_mat P" 
    and "invertible_mat Q" and "Hermite_JNF associates res H" and "Hermite_JNF associates res K"
shows "H = K" 
proof -
  define A' where "A' = (Mod_Type_Connect.to_hma\<^sub>m A :: int ^'n :: mod_type ^'n :: mod_type)"
  define P' where "P' = (Mod_Type_Connect.to_hma\<^sub>m P :: int ^'n :: mod_type ^'n :: mod_type)"
  define H' where "H' = (Mod_Type_Connect.to_hma\<^sub>m H :: int ^'n :: mod_type ^'n :: mod_type)"
  define Q' where "Q' = (Mod_Type_Connect.to_hma\<^sub>m Q :: int ^'n :: mod_type ^'n :: mod_type)"
  define K' where "K' = (Mod_Type_Connect.to_hma\<^sub>m K :: int ^'n :: mod_type ^'n :: mod_type)"
  have AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'" unfolding Mod_Type_Connect.HMA_M_def using assms A'_def by auto  
  have PP'[transfer_rule]: "Mod_Type_Connect.HMA_M P P'" unfolding Mod_Type_Connect.HMA_M_def using assms P'_def by auto
  have HH'[transfer_rule]: "Mod_Type_Connect.HMA_M H H'" unfolding Mod_Type_Connect.HMA_M_def using assms H'_def by auto
  have QQ'[transfer_rule]: "Mod_Type_Connect.HMA_M Q Q'" unfolding Mod_Type_Connect.HMA_M_def using assms Q'_def by auto
  have KK'[transfer_rule]: "Mod_Type_Connect.HMA_M K K'" unfolding Mod_Type_Connect.HMA_M_def using assms K'_def by auto
  have A_PH: "A' = P' ** H'" using assms by transfer
  moreover have A_QK: "A' = Q' ** K'" using assms by transfer
  moreover have inv_A: "invertible (map_matrix rat_of_int A')" using assms by transfer
  moreover have "invertible (Finite_Cartesian_Product.map_matrix rat_of_int A')"
    using inv_A unfolding Finite_Cartesian_Product.map_matrix_def map_matrix_def map_vector_def
    by simp
  moreover have inv_P: "invertible P'" using assms by transfer
  moreover have inv_Q: "invertible Q'" using assms by transfer
  moreover have H: "Hermite associates res H'" using assms by transfer
  moreover have K: "Hermite associates res K'" using assms by transfer
  ultimately have "H' = K'" using Hermite_unique_generalized by blast
  thus "H=K" by transfer
qed


corollary Hermite_unique_generalized_JNF_with_nontriv_mod_ring:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat CARD('n) CARD('n::nontriv mod_ring)"
    "P \<in> carrier_mat CARD('n) CARD('n)"
    "H \<in> carrier_mat CARD('n) CARD('n)"
    "Q \<in> carrier_mat CARD('n) CARD('n)"
    "K \<in> carrier_mat CARD('n) CARD('n)"
  assumes "A = P * H"
    and "A = Q * K" and "invertible_mat (map_mat rat_of_int A)" and "invertible_mat P" 
    and "invertible_mat Q" and "Hermite_JNF associates res H" and "Hermite_JNF associates res K"
shows "H = K" using Hermite_unique_generalized_JNF' assms by (smt CARD_mod_ring)




context
  fixes p::nat
  assumes local_typedef: "\<exists>(Rep :: ('b \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<p :: int}"
  and p: "p>1"
begin

private lemma type_to_set2:
  shows "class.nontriv TYPE('b)" (is ?a) and "p=CARD('b)" (is ?b)
proof -
  from local_typedef obtain Rep::"('b \<Rightarrow> int)" and Abs 
    where t: "type_definition Rep Abs {0..<p :: int}" by auto
  have "card (UNIV :: 'b set) = card {0..<p}" using t type_definition.card by fastforce
  also have "... = p" by auto
  finally show ?b ..
  then show ?a unfolding class.nontriv_def using p by auto
qed


lemma Hermite_unique_generalized_JNF_aux:
  fixes A::"int mat"
  assumes "A \<in> carrier_mat p p"
    "P \<in> carrier_mat p p"
    "H \<in> carrier_mat p p"
    "Q \<in> carrier_mat p p"
    "K \<in> carrier_mat p p"
  assumes "A = P * H"
    and "A = Q * K" and "invertible_mat (map_mat rat_of_int A)" and "invertible_mat P" 
    and "invertible_mat Q" and "Hermite_JNF associates res H" and "Hermite_JNF associates res K"
shows "H = K"
  using Hermite_unique_generalized_JNF_with_nontriv_mod_ring[unfolded CARD_mod_ring,
      internalize_sort "'n::nontriv", where ?'a='b]
  unfolding type_to_set2(2)[symmetric] using type_to_set2(1) assms by blast
end                     


lemma HNF_unique_generalized_JNF:
  fixes A::"int mat"
  assumes A: "A \<in> carrier_mat n n" and P: "P \<in> carrier_mat n n" and H: "H \<in> carrier_mat n n"
   and Q: "Q \<in> carrier_mat n n" and K: "K \<in> carrier_mat n n"
 assumes A_PH: "A = P * H" and A_QK: "A = Q * K"
   and inv_A: "invertible_mat (map_mat rat_of_int A)" and inv_P: "invertible_mat P" and inv_Q: "invertible_mat Q"
   and HNF_H: "Hermite_JNF associates res H" and HNF_K: "Hermite_JNF associates res K"
  shows "H = K"
proof (cases "n=0 \<or> n=1")
  case True note zero_or_one = True
  show ?thesis
  proof (cases "n=0")
    case True
    then show ?thesis using assms by auto
  next
    let ?RAT = "map_mat rat_of_int"
    case False
    hence n: "n=1" using zero_or_one by auto
    have CS_A: "Complete_set_non_associates associates" using HNF_H unfolding Hermite_JNF_def by simp
    have H: "H \<in> carrier_mat 1 1" and K: "K\<in> carrier_mat 1 1" using False zero_or_one assms by auto
    have det_P_dvd_1: "Determinant.det P dvd 1" using invertible_iff_is_unit_JNF inv_P P by blast
    have det_Q_dvd_1: "Determinant.det Q dvd 1" using invertible_iff_is_unit_JNF inv_Q Q by blast
    have PH_QK: "Determinant.det P * Determinant.det H = Determinant.det Q * Determinant.det K"
      using Determinant.det_mult assms by metis
    hence "Determinant.det P * H $$ (0,0) = Determinant.det Q * K $$ (0,0)"
      by (metis H K determinant_one_element)
    obtain u where uH_K: "u * H $$(0,0) = K $$ (0,0)" and unit_u: "is_unit u"
      by (metis (no_types, hide_lams) H K PH_QK algebraic_semidom_class.dvd_mult_unit_iff det_P_dvd_1 
          det_Q_dvd_1 det_singleton dvdE dvd_mult_cancel_left mult.commute mult.right_neutral one_dvd)
    have H00_not_0: "H $$ (0,0) \<noteq> 0"
    proof -      
      have "?RAT A = ?RAT P * ?RAT H" using A_PH
        using P H n of_int_hom.mat_hom_mult by blast
      hence "det (?RAT H) \<noteq> 0" 
        by (metis A Determinant.det_mult False H P inv_A invertible_iff_is_unit_JNF 
            map_carrier_mat mult_eq_0_iff not_is_unit_0 zero_or_one)
      thus ?thesis
        using H determinant_one_element by force      
    qed
    hence LEAST_H: "(LEAST n. H $$ (0,n) \<noteq> 0) = 0" by simp
    have H00: "H $$ (0,0) \<in> associates" using HNF_H LEAST_H H H00_not_0 
      unfolding Hermite_JNF_def is_zero_row_JNF_def by auto
    have K00_not_0: "K $$ (0,0) \<noteq> 0"
    proof -
      have "?RAT A = ?RAT Q * ?RAT K" using A_QK
        using Q K n of_int_hom.mat_hom_mult by blast
      hence "det (?RAT K) \<noteq> 0" 
        by (metis A Determinant.det_mult False Q K inv_A invertible_iff_is_unit_JNF 
            map_carrier_mat mult_eq_0_iff not_is_unit_0 zero_or_one)
      thus ?thesis
        using K determinant_one_element by force
    qed
    hence LEAST_K: "(LEAST n. K $$ (0,n) \<noteq> 0) = 0" by simp
    have K00: "K $$ (0,0) \<in> associates" using HNF_K LEAST_K K K00_not_0 
      unfolding Hermite_JNF_def is_zero_row_JNF_def by auto
    have ass_H00_K00: "normalize (H $$ (0,0)) = normalize (K $$ (0,0))"
      by (metis normalize_mult_unit_left uH_K unit_u)
    have H00_eq_K00: "H $$ (0,0) = K $$ (0,0)" 
      using in_Ass_not_associated[OF CS_A H00 K00] ass_H00_K00 by auto
    show ?thesis by (rule eq_matI, insert H K H00_eq_K00, auto)
  qed
next
  case False
  hence "{0..<int n} \<noteq> {}" by auto
  moreover have "n>1" using False by simp
  ultimately show ?thesis 
    using Hermite_unique_generalized_JNF_aux[cancel_type_definition] assms by metis (*Cancel local type definition*)
qed 

end
