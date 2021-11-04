(* Title: Examples/SML_Relativization/Topology/SML_Ordered_Topological_Spaces.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)
section\<open>Relativization of the results about ordered topological spaces\<close>
theory SML_Ordered_Topological_Spaces
  imports 
    SML_Topological_Space
    "../Lattices/SML_Linorders"
begin



subsection\<open>Ordered topological space\<close>


subsubsection\<open>Definitions and common properties\<close>

locale order_topology_ow = 
  order_ow U le ls for U :: "'at set" and le ls +
  fixes \<tau> :: "'at set \<Rightarrow> bool"
  assumes open_generated_order: "s \<subseteq> U \<Longrightarrow> 
    \<tau> s = 
      (
        (
          in_topology_generated_by 
            (
              (\<lambda>a. (on U with (<\<^sub>o\<^sub>w) : {..< a})) ` U \<union> 
              (\<lambda>a. (on U with (<\<^sub>o\<^sub>w) : {a <..})) ` U
            ) 
          on U : \<guillemotleft>open\<guillemotright> s 
        )
      )"
begin

sublocale topological_space_ow
proof -
  define \<tau>' where \<tau>': 
    "\<tau>' = generate_topology_on 
      (
        (\<lambda>a. (on U with (<\<^sub>o\<^sub>w) : {..< a})) ` U \<union> 
        (\<lambda>a. (on U with (<\<^sub>o\<^sub>w) : {a <..})) ` U
      ) 
      U"
  have 
    "(
      (\<lambda>a. (on U with (<\<^sub>o\<^sub>w) : {..< a})) ` U \<union> 
      (\<lambda>a. (on U with (<\<^sub>o\<^sub>w) : {a <..})) ` U
    ) \<subseteq> Pow U"
    unfolding lessThan_def greaterThan_def lessThan_ow_def greaterThan_ow_def
    by auto
  then have "topological_space_ow U \<tau>'"
    unfolding \<tau>' by (simp add: topological_space_generate_topology)
  moreover then have "s \<subseteq> U \<Longrightarrow> \<tau>' s = \<tau> s" for s
    unfolding \<tau>' using open_generated_order by blast
  ultimately show "topological_space_ow U \<tau>"  
    unfolding \<tau>' by (rule ts_open_eq_ts_open)
qed

end

locale ts_ot_ow = 
  ts: topological_space_ow U\<^sub>1 \<tau>\<^sub>1 + ot: order_topology_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
  for U\<^sub>1 :: "'at set" and \<tau>\<^sub>1 and U\<^sub>2 :: "'bt set" and le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
begin

sublocale topological_space_pair_ow U\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 \<tau>\<^sub>2 ..

end

locale order_topology_pair_ow = 
  ot\<^sub>1: order_topology_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 \<tau>\<^sub>1 + ot\<^sub>2: order_topology_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
  for U\<^sub>1 :: "'at set" and le\<^sub>1 ls\<^sub>1 \<tau>\<^sub>1 and U\<^sub>2 :: "'bt set" and le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
begin

sublocale ts_ot_ow U\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2 ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma order_topology_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (rel_set A ===> (=)) ===> 
      (=)
    ) (order_topology_ow (Collect (Domainp A))) class.order_topology"
  unfolding order_topology_ow_def class.order_topology_def
  unfolding order_topology_ow_axioms_def class.order_topology_axioms_def
proof(intro rel_funI, standard; elim conjE)
  let ?U = "Collect (Domainp A)"
  fix le :: "['a, 'a] \<Rightarrow> bool" 
    and le' :: "['b, 'b] \<Rightarrow> bool"
    and ls :: "['a, 'a] \<Rightarrow> bool" 
    and ls' :: "['b, 'b] \<Rightarrow> bool"
    and \<tau> :: "'a set \<Rightarrow> bool"
    and \<tau>' :: "'b set \<Rightarrow> bool"
  assume [transfer_rule]: "(A ===> A ===> (=)) le le'" 
    and [transfer_rule]: "(A ===> A ===> (=)) ls ls'"
    and [transfer_rule]: "(rel_set A ===> (=)) \<tau> \<tau>'"
    and oow: "order_ow (Collect (Domainp A)) le ls"
    and \<tau>: 
      "\<forall>s\<subseteq>Collect (Domainp A). \<tau> s =
        generate_topology_on
          (lessThan_ow ?U ls ` ?U \<union> greaterThan_ow ?U ls ` ?U) ?U s" 
  have [transfer_rule]: "Domainp A = (\<lambda>x. x \<in> Collect (Domainp A))" by auto
  interpret oow: order_ow ?U le ls by (rule oow)
  interpret co: order le' ls' by transfer (rule oow)
  have ineq_fold:
    "lessThan.with ls y \<equiv> {x. ls x y}" 
    "greaterThan.with ls y \<equiv> {x. ls y x}"
    for ls :: "'c \<Rightarrow> 'c \<Rightarrow> bool" and y 
    unfolding lessThan.with_def greaterThan.with_def by auto
  have 
    "\<tau>' = generate_topology (
      range (ord.lessThan ls') \<union> range (ord.greaterThan ls')
      )"
    unfolding co.lessThan_def co.greaterThan_def
    unfolding ineq_fold[symmetric]
    by (transfer, intro allI impI) (auto simp: \<tau>)    
  from co.order_axioms this show
    "class.order le' ls' \<and> 
      \<tau>' = generate_topology (
        range (ord.lessThan ls') \<union> range (ord.greaterThan ls')
      )"
    by simp
next
  let ?U = "Collect (Domainp A)"
  fix le :: "['a, 'a] \<Rightarrow> bool" 
    and le' :: "['b, 'b] \<Rightarrow> bool"
    and ls :: "['a, 'a] \<Rightarrow> bool" 
    and ls' :: "['b, 'b] \<Rightarrow> bool"
    and \<tau> :: "'a set \<Rightarrow> bool"
    and \<tau>' :: "'b set \<Rightarrow> bool"
  assume [transfer_rule]: "(A ===> A ===> (=)) le le'" 
    and [transfer_rule]: "(A ===> A ===> (=)) ls ls'"
    and [transfer_rule]: "(rel_set A ===> (=)) \<tau> \<tau>'"
    and co: "class.order le' ls'"
    and \<tau>': "\<tau>' = generate_topology
      (range (ord.lessThan ls') \<union> range (ord.greaterThan ls'))"
  have [transfer_rule]: "Domainp A = (\<lambda>x. x \<in> Collect (Domainp A))" by auto
  interpret co: order le' ls' by (rule co)
  have ineq_fold:
    "lessThan.with ls y \<equiv> {x. ls x y}" 
    "greaterThan.with ls y \<equiv> {x. ls y x}"
    for ls :: "'c \<Rightarrow> 'c \<Rightarrow> bool" and y 
    unfolding lessThan.with_def greaterThan.with_def by auto
  from co have "order_ow ?U le ls" by transfer
  moreover have 
    "\<forall>s\<subseteq>Collect (Domainp A). \<tau> s =
      SML_Topological_Space.generate_topology_on
        (lessThan_ow ?U ls ` ?U \<union> greaterThan_ow ?U ls ` ?U) ?U s"
    by 
      (
        rule \<tau>'[
          unfolded co.lessThan_def co.greaterThan_def,
          folded ineq_fold,
          untransferred
          ]
       )
  ultimately show 
    "order_ow ?U le ls \<and>
      (
        \<forall>s\<subseteq>Collect (Domainp A). \<tau> s = 
          SML_Topological_Space.generate_topology_on
            (lessThan_ow ?U ls ` ?U \<union> greaterThan_ow ?U ls ` ?U) ?U s
      )"
    by simp
qed
  
end


subsubsection\<open>Relativization\<close>

context order_topology_ow 
begin

tts_context
  tts: (?'a to U)
  substituting order_topology_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through simp
begin

tts_lemma open_greaterThan:
  assumes "a \<in> U"
  shows "\<tau> {a<\<^sub>o\<^sub>w..}"
    is order_topology_class.open_greaterThan.
    
tts_lemma open_lessThan:
  assumes "a \<in> U"
  shows "\<tau> {..<\<^sub>o\<^sub>wa}"
  is order_topology_class.open_lessThan.

tts_lemma open_greaterThanLessThan:
  assumes "a \<in> U" and "b \<in> U"
  shows "\<tau> {a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb}"
    is order_topology_class.open_greaterThanLessThan.

end

end



subsection\<open>Linearly ordered topological space\<close>


subsubsection\<open>Definitions and common properties\<close>

locale linorder_topology_ow = 
  linorder_ow U le ls + order_topology_ow U le ls \<tau> 
  for U :: "'at set" and le ls \<tau>

locale ts_lt_ow = 
  ts: topological_space_ow U\<^sub>1 \<tau>\<^sub>1 + lt: linorder_topology_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
  for U\<^sub>1 :: "'at set" and \<tau>\<^sub>1 and U\<^sub>2 :: "'bt set" and le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
begin

sublocale ts_ot_ow U\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2 ..

end

locale ot_lt_ow = 
  ot: order_topology_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 \<tau>\<^sub>1 + lt: linorder_topology_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
  for U\<^sub>1 :: "'at set" and le\<^sub>1 ls\<^sub>1 \<tau>\<^sub>1 and U\<^sub>2 :: "'bt set" and le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
begin

sublocale ts_lt_ow U\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2 ..
sublocale order_topology_pair_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2 ..

end

locale linorder_topology_pair_ow = 
  lt\<^sub>1: linorder_topology_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 \<tau>\<^sub>1 + lt\<^sub>2: linorder_topology_ow U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
  for U\<^sub>1 :: "'at set" and le\<^sub>1 ls\<^sub>1 \<tau>\<^sub>1 and U\<^sub>2 :: "'bt set" and le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2
begin

sublocale ot_lt_ow U\<^sub>1 le\<^sub>1 ls\<^sub>1 \<tau>\<^sub>1 U\<^sub>2 le\<^sub>2 ls\<^sub>2 \<tau>\<^sub>2 ..

end


subsubsection\<open>Transfer rules\<close>

context
  includes lifting_syntax
begin

lemma linorder_topology_transfer[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A" "right_total A" 
  shows 
    "(
      (A ===> A ===> (=)) ===> 
      (A ===> A ===> (=)) ===> 
      (rel_set A ===> (=)) ===> 
      (=)
    ) 
    (linorder_topology_ow (Collect (Domainp A))) class.linorder_topology"
  unfolding linorder_topology_ow_def class.linorder_topology_def
  by transfer_prover

end


subsubsection\<open>Relativization\<close>

context linorder_topology_ow 
begin

tts_context
  tts: (?'a to U) 
  rewriting ctr_simps
  substituting linorder_topology_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through clarsimp
begin

tts_lemma open_right:
  assumes "S \<subseteq> U"
    and "x \<in> U"
    and "y \<in> U"
    and "\<tau> S"
    and "x \<in> S"
    and "x <\<^sub>o\<^sub>w y"
  shows "\<exists>z\<in>U. x <\<^sub>o\<^sub>w z \<and> (on U with (\<le>\<^sub>o\<^sub>w) (<\<^sub>o\<^sub>w) : {x..<z}) \<subseteq> S"
    is linorder_topology_class.open_right.
    
tts_lemma open_left:
  assumes "S \<subseteq> U"
    and "x \<in> U"
    and "y \<in> U"
    and "\<tau> S"
    and "x \<in> S"
    and "y <\<^sub>o\<^sub>w x"
  shows "\<exists>z\<in>U. z <\<^sub>o\<^sub>w x \<and> {z<\<^sub>o\<^sub>w..x} \<subseteq> S"
    is linorder_topology_class.open_left.

tts_lemma connectedD_interval:
  assumes "U \<subseteq> U"
    and "x \<in> U"
    and "y \<in> U"
    and "z \<in> U"
    and "connected U"
    and "x \<in> U"
    and "y \<in> U"
    and "x \<le>\<^sub>o\<^sub>w z"
    and "z \<le>\<^sub>o\<^sub>w y"
  shows "z \<in> U"
    is linorder_topology_class.connectedD_interval.

tts_lemma connected_contains_Icc:
  assumes "A \<subseteq> U"
    and "a \<in> U"
    and "b \<in> U"
    and "connected A"
    and "a \<in> A"
    and "b \<in> A"
  shows "{a..\<^sub>o\<^sub>wb} \<subseteq> A"
    is Topological_Spaces.connected_contains_Icc.

tts_lemma connected_contains_Ioo:
  assumes "A \<subseteq> U"
    and "a \<in> U"
    and "b \<in> U"
    and "connected A"
    and "a \<in> A"
    and "b \<in> A"
  shows "{a<\<^sub>o\<^sub>w..<\<^sub>o\<^sub>wb} \<subseteq> A"
    is Topological_Spaces.connected_contains_Ioo.

end

tts_context
  tts: (?'a to U) 
  rewriting ctr_simps
  substituting linorder_topology_ow_axioms
  eliminating \<open>?U \<noteq> {}\<close> through clarsimp
begin

tts_lemma not_in_connected_cases:
  assumes "S \<subseteq> U"
    and "x \<in> U"
    and "connected S"
    and "x \<notin> S"
    and "S \<noteq> {}"
    and "\<lbrakk>bdd_above S; \<And>y. \<lbrakk>y \<in> U; y \<in> S\<rbrakk> \<Longrightarrow> y \<le>\<^sub>o\<^sub>w x\<rbrakk> \<Longrightarrow> thesis"
    and "\<lbrakk>bdd_below S; \<And>y. \<lbrakk>y \<in> U; y \<in> S\<rbrakk> \<Longrightarrow> x \<le>\<^sub>o\<^sub>w y\<rbrakk> \<Longrightarrow> thesis"
  shows thesis
    is linorder_topology_class.not_in_connected_cases.

tts_lemma compact_attains_sup:
  assumes "S \<subseteq> U"
    and "compact S"
    and "S \<noteq> {}"
  shows "\<exists>x\<in>S. \<forall>y\<in>S. y \<le>\<^sub>o\<^sub>w x"
    is linorder_topology_class.compact_attains_sup.

tts_lemma compact_attains_inf:
  assumes "S \<subseteq> U"
    and "compact S"
    and "S \<noteq> {}"
  shows "\<exists>x\<in>S. Ball S ((\<le>\<^sub>o\<^sub>w) x)"
    is linorder_topology_class.compact_attains_inf.

end

end

text\<open>\newpage\<close>

end