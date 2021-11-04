(* Title: Examples/SML_Relativization/Topology/SML_Product_Topology.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about product topologies\<close>
theory SML_Product_Topology
  imports 
    SML_Topological_Space
    "../Foundations/Product_Type_Ext"
begin



subsection\<open>Definitions and common properties\<close>

ud\<open>
  open_prod_inst.open_prod::
    ('a::topological_space \<times> 'b::topological_space) set \<Rightarrow> _
  \<close>
ud\<open>open::('a::topological_space \<times> 'b::topological_space) set \<Rightarrow> bool\<close>

ctr relativization
  synthesis ctr_simps
  assumes [transfer_domain_rule, transfer_rule]: 
    "Domainp B = (\<lambda>x. x \<in> U\<^sub>1)" "Domainp A = (\<lambda>x. x \<in> U\<^sub>2)"
    and [transfer_rule]: "bi_unique A" "right_total A"
      "bi_unique B" "right_total B"
  trp (?'a A) and (?'b B) 
  in open_ow: open_prod.with_def
    (\<open>'(/on _ _ with _ _ : \<guillemotleft>open\<guillemotright> _/')\<close> [1000, 999, 1000, 999, 1000] 10) 

locale product_topology_ow =
  ts\<^sub>1: topological_space_ow U\<^sub>1 \<tau>\<^sub>1 + ts\<^sub>2: topological_space_ow U\<^sub>2 \<tau>\<^sub>2 
  for U\<^sub>1 :: "'at set" and \<tau>\<^sub>1 :: "'at set \<Rightarrow> bool" 
    and U\<^sub>2 :: "'bt set"and \<tau>\<^sub>2 :: "'bt set \<Rightarrow> bool" +
  fixes \<tau> :: "('at \<times> 'bt) set \<Rightarrow> bool"
  assumes open_prod[tts_implicit]: "\<tau> = open_ow U\<^sub>1 U\<^sub>2 \<tau>\<^sub>2 \<tau>\<^sub>1"
begin 

sublocale topological_space_ow \<open>U\<^sub>1 \<times> U\<^sub>2\<close> \<tau>
proof
  let ?U = "U\<^sub>1 \<times> U\<^sub>2"  
  have open_prod': "\<tau> S = open_ow U\<^sub>1 U\<^sub>2 \<tau>\<^sub>2 \<tau>\<^sub>1 S" for S
    by (simp only: open_prod)
  note op = open_prod'[unfolded open_ow_def, THEN iffD2, rule_format]
  show "\<tau> (U\<^sub>1 \<times> U\<^sub>2)" by (rule op) auto   
  show "\<lbrakk> S \<subseteq> ?U; T \<subseteq> ?U; \<tau> S; \<tau> T \<rbrakk> \<Longrightarrow> \<tau> (S \<inter> T)" for S T
  proof-
    assume "S \<subseteq> ?U" and "T \<subseteq> ?U" and "\<tau> S" and "\<tau> T"
    from \<open>S \<subseteq> ?U\<close> \<open>T \<subseteq> ?U\<close> have "S \<inter> T \<subseteq> ?U" by auto
    show "\<tau> (S \<inter> T)"
    proof(rule op)
      fix x assume "x \<in> S \<inter> T"
      then have "x \<in> S" and "x \<in> T" by auto
      from open_prod'[
          unfolded open_ow_def, THEN iffD1, rule_format, OF \<open>\<tau> S\<close> \<open>x \<in> S\<close>
          ]
      obtain A\<^sub>S B\<^sub>S where 
        "A\<^sub>S \<subseteq> U\<^sub>1" "B\<^sub>S \<subseteq> U\<^sub>2" "\<tau>\<^sub>1 A\<^sub>S" "\<tau>\<^sub>2 B\<^sub>S" "x \<in> A\<^sub>S \<times> B\<^sub>S" "A\<^sub>S \<times> B\<^sub>S \<subseteq> S" 
        by auto 
      from open_prod'[
          unfolded open_ow_def, THEN iffD1, rule_format, 
          OF \<open>\<tau> T\<close> \<open>x \<in> T\<close>
          ]
      obtain A\<^sub>T B\<^sub>T where 
        "A\<^sub>T \<subseteq> U\<^sub>1" "B\<^sub>T \<subseteq> U\<^sub>2" "\<tau>\<^sub>1 A\<^sub>T" "\<tau>\<^sub>2 B\<^sub>T" "x \<in> A\<^sub>T \<times> B\<^sub>T" "A\<^sub>T \<times> B\<^sub>T \<subseteq> T" 
        by auto
      from \<open>A\<^sub>S \<subseteq> U\<^sub>1\<close> \<open>A\<^sub>T \<subseteq> U\<^sub>1\<close> have "A\<^sub>S \<inter> A\<^sub>T \<subseteq> U\<^sub>1" by auto
      moreover from \<open>B\<^sub>S \<subseteq> U\<^sub>2\<close> \<open>B\<^sub>T \<subseteq> U\<^sub>2\<close> have "B\<^sub>S \<inter> B\<^sub>T \<subseteq> U\<^sub>2" by auto
      moreover from \<open>A\<^sub>S \<subseteq> U\<^sub>1\<close> \<open>A\<^sub>T \<subseteq> U\<^sub>1\<close> \<open>\<tau>\<^sub>1 A\<^sub>S\<close> \<open>\<tau>\<^sub>1 A\<^sub>T\<close> have "\<tau>\<^sub>1 (A\<^sub>S \<inter> A\<^sub>T)" 
        by auto
      moreover from \<open>B\<^sub>S \<subseteq> U\<^sub>2\<close> \<open>B\<^sub>T \<subseteq> U\<^sub>2\<close> \<open>\<tau>\<^sub>2 B\<^sub>S\<close> \<open>\<tau>\<^sub>2 B\<^sub>T\<close> have "\<tau>\<^sub>2 (B\<^sub>S \<inter> B\<^sub>T)" 
        by auto
      moreover from \<open>x \<in> A\<^sub>S \<times> B\<^sub>S\<close> \<open>x \<in> A\<^sub>T \<times> B\<^sub>T\<close> have 
        "x \<in> (A\<^sub>S \<inter> A\<^sub>T) \<times> (B\<^sub>S \<inter> B\<^sub>T)"
        by clarsimp
      moreover from \<open>A\<^sub>S \<times> B\<^sub>S \<subseteq> S\<close> \<open>A\<^sub>T \<times> B\<^sub>T \<subseteq> T\<close> have 
        "(A\<^sub>S \<inter> A\<^sub>T) \<times> (B\<^sub>S \<inter> B\<^sub>T) \<subseteq> S \<inter> T"
        by auto
      ultimately show 
        "\<exists>A\<in>Pow U\<^sub>1. \<exists>B\<in>Pow U\<^sub>2. \<tau>\<^sub>1 A \<and> \<tau>\<^sub>2 B \<and> A \<times> B \<subseteq> S \<inter> T \<and> x \<in> A \<times> B" 
        by auto
    qed
  qed
  show "\<lbrakk> K \<subseteq> Pow ?U; \<forall>S\<in>K. \<tau> S \<rbrakk> \<Longrightarrow> \<tau> (\<Union>K)" for K
  proof -
    assume "K \<subseteq> Pow ?U" and "\<forall>S\<in>K. \<tau> S" 
    from \<open>K \<subseteq> Pow ?U\<close> have "\<Union>K \<subseteq> ?U" by auto
    show "\<tau> (\<Union>K)"
    proof(rule op)
      fix x assume "x \<in> \<Union>K"
      then obtain k where k: "x \<in> k" and "k \<in> K" by clarsimp
      from \<open>k \<in> K\<close> have "k \<subseteq> \<Union>K" by auto
      from \<open>k \<in> K\<close> have "\<tau> k" by (rule \<open>\<forall>S\<in>K. \<tau> S\<close>[rule_format])
      from open_prod'[
          unfolded open_ow_def, THEN iffD1, rule_format,
          OF this \<open>x \<in> k\<close>
          ]
      obtain A B where 
        "A \<subseteq> U\<^sub>1" "B \<subseteq> U\<^sub>2" "\<tau>\<^sub>1 A" "\<tau>\<^sub>2 B" "x \<in> A \<times> B" "A \<times> B \<subseteq> k"
        by auto
      from \<open>A \<times> B \<subseteq> k\<close> \<open>k \<subseteq> \<Union>K\<close> have "A \<times> B \<subseteq> \<Union>K" by simp
      from \<open>A \<subseteq> U\<^sub>1\<close> \<open>B \<subseteq> U\<^sub>2\<close> \<open>\<tau>\<^sub>1 A\<close> \<open>\<tau>\<^sub>2 B\<close> \<open>x \<in> A \<times> B\<close> this show 
        " \<exists>A\<in>Pow U\<^sub>1. \<exists>B\<in>Pow U\<^sub>2. \<tau>\<^sub>1 A \<and> \<tau>\<^sub>2 B \<and> A \<times> B \<subseteq> \<Union> K \<and> x \<in> A \<times> B"
        by auto
    qed
  qed
qed

end



subsection\<open>Transfer rules\<close>

lemma (in product_topology_ow) open_with_oo_transfer[transfer_rule]:
  includes lifting_syntax
  fixes A :: "['at, 'a] \<Rightarrow> bool"
    and B :: "['bt, 'b] \<Rightarrow> bool"
  assumes tdr_U\<^sub>1[transfer_domain_rule]: "Domainp A = (\<lambda>x. x \<in> U\<^sub>1)"
    and [transfer_rule]: "bi_unique A" "right_total A"  
    and tdr_U\<^sub>2[transfer_domain_rule]: "Domainp B = (\<lambda>x. x \<in> U\<^sub>2)"
    and [transfer_rule]: "bi_unique B" "right_total B" 
    and \<tau>\<^sub>1\<tau>\<^sub>1'[transfer_rule]: "(rel_set A ===> (=)) \<tau>\<^sub>1 \<tau>\<^sub>1'"
    and \<tau>\<^sub>2\<tau>\<^sub>2'[transfer_rule]: "(rel_set B ===> (=)) \<tau>\<^sub>2 \<tau>\<^sub>2'"
  shows "(rel_set (rel_prod A B) ===> (=)) \<tau> (open_prod.with \<tau>\<^sub>2' \<tau>\<^sub>1')"
  unfolding open_prod.with_def
  apply transfer_prover_start
  apply transfer_step+
  apply simp
  apply(fold subset_eq)
  unfolding open_prod open_ow_def tdr_U\<^sub>1 tdr_U\<^sub>2 
  by (meson Pow_iff)



subsection\<open>Relativization\<close>

context product_topology_ow
begin

tts_context
  tts: (?'a to U\<^sub>1) and (?'b to U\<^sub>2)
  rewriting ctr_simps
  substituting ts\<^sub>1.topological_space_ow_axioms 
    and ts\<^sub>2.topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (fold tts_implicit, insert closed_empty, simp)
  applying [folded tts_implicit]
begin

tts_lemma open_prod_intro:
  assumes "S \<subseteq> U\<^sub>1 \<times> U\<^sub>2"
    and "\<And>x. \<lbrakk>x \<in> U\<^sub>1 \<times> U\<^sub>2; x \<in> S\<rbrakk> \<Longrightarrow> 
      \<exists>A\<in>Pow U\<^sub>1. \<exists>B\<in>Pow U\<^sub>2. \<tau>\<^sub>1 A \<and> \<tau>\<^sub>2 B \<and> A \<times> B \<subseteq> S \<and> x \<in> A \<times> B"
  shows "\<tau> S"
    is open_prod_intro.

tts_lemma open_Times:
  assumes "S \<subseteq> U\<^sub>1" and "T \<subseteq> U\<^sub>2" and "\<tau>\<^sub>1 S" and "\<tau>\<^sub>2 T"
  shows "\<tau> (S \<times> T)"
    is open_Times.
    
tts_lemma open_vimage_fst:
  assumes "S \<subseteq> U\<^sub>1" and "\<tau>\<^sub>1 S"
  shows "\<tau> (fst -` S \<inter> U\<^sub>1 \<times> U\<^sub>2)"
    is open_vimage_fst.

tts_lemma closed_vimage_fst:
  assumes "S \<subseteq> U\<^sub>1" and "ts\<^sub>1.closed S"
  shows "closed (fst -` S \<inter> U\<^sub>1 \<times> U\<^sub>2)"
    is closed_vimage_fst.

tts_lemma closed_Times:
  assumes "S \<subseteq> U\<^sub>1" and "T \<subseteq> U\<^sub>2" and "ts\<^sub>1.closed S" and "ts\<^sub>2.closed T"
  shows "closed (S \<times> T)"
    is closed_Times.

tts_lemma open_image_fst:
  assumes "S \<subseteq> U\<^sub>1 \<times> U\<^sub>2" and "\<tau> S"
  shows "\<tau>\<^sub>1 (fst ` S)"
    is open_image_fst.

tts_lemma open_image_snd:
  assumes "S \<subseteq> U\<^sub>1 \<times> U\<^sub>2" and "\<tau> S"
  shows "\<tau>\<^sub>2 (snd ` S)"
    is open_image_snd.

end

tts_context
  tts: (?'a to U\<^sub>1) and (?'b to U\<^sub>2)
  rewriting ctr_simps
  substituting ts\<^sub>1.topological_space_ow_axioms 
    and ts\<^sub>2.topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> 
    through (fold tts_implicit, unfold connected_ow_def, simp)
  applying [folded tts_implicit]
begin

tts_lemma connected_Times:
  assumes "S \<subseteq> U\<^sub>1" and "T \<subseteq> U\<^sub>2" and "ts\<^sub>1.connected S" and "ts\<^sub>2.connected T"
  shows "connected (S \<times> T)"
    is connected_Times.
    
tts_lemma connected_Times_eq:
  assumes "S \<subseteq> U\<^sub>1" and "T \<subseteq> U\<^sub>2"
  shows 
    "connected (S \<times> T) = (S = {} \<or> T = {} \<or> ts\<^sub>1.connected S \<and> ts\<^sub>2.connected T)"
  is connected_Times_eq.

end

tts_context
  tts: (?'b to U\<^sub>1) and (?'a to U\<^sub>2)
  rewriting ctr_simps
  substituting ts\<^sub>1.topological_space_ow_axioms 
    and ts\<^sub>2.topological_space_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through (fold tts_implicit, insert closed_empty, simp)
  applying [folded tts_implicit]
begin

tts_lemma open_vimage_snd:
  assumes "S \<subseteq> U\<^sub>2" and "\<tau>\<^sub>2 S"
  shows "\<tau> (snd -` S \<inter> U\<^sub>1 \<times> U\<^sub>2)"
    is open_vimage_snd.

tts_lemma closed_vimage_snd:
  assumes "S \<subseteq> U\<^sub>2" and "ts\<^sub>2.closed S"
  shows "closed (snd -` S \<inter> U\<^sub>1 \<times> U\<^sub>2)"
    is closed_vimage_snd.

end

end

text\<open>\newpage\<close>

end