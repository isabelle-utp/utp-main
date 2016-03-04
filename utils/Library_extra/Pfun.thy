section {* Partial functions *}

theory Pfun
imports Map_Extra
begin

text {* I'm not completely satisfied with partial functions as provided by Map.thy, since they don't
        have a unique type and so we can't instantiate classes, make use of adhoc-overloading
        etc. Consequently I've created a new type and derived the laws. *}

typedef ('a, 'b) pfun = "UNIV :: ('a \<rightharpoonup> 'b) set" ..

setup_lifting type_definition_pfun

lift_definition pfun_app :: "('a, 'b) pfun \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>p" [999,0] 999) is "\<lambda> f x. the (f x)" .

lift_definition pfun_upd :: "('a, 'b) pfun \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pfun"
is "\<lambda> f k v. f(k := Some v)" .

lift_definition pdom :: "('a, 'b) pfun \<Rightarrow> 'a set" is dom .

lift_definition pran :: "('a, 'b) pfun \<Rightarrow> 'b set" is ran .

lift_definition pfun_comp :: "('b, 'c) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'c) pfun" (infixl "\<circ>\<^sub>p" 55) is map_comp .

lift_definition pfun_member :: "'a \<times> 'b \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<in>\<^sub>p" 50) is "op \<in>\<^sub>m" .

lift_definition pId_on :: "'a set \<Rightarrow> ('a, 'a) pfun" is "\<lambda> A x. if (x \<in> A) then Some x else None" .

abbreviation pId :: "('a, 'a) pfun" where
"pId \<equiv> pId_on UNIV"

lift_definition pdom_res :: "'a set \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" (infixl "\<lhd>\<^sub>p" 85) 
is "\<lambda> A f. restrict_map f A" .

lift_definition pran_res :: "('a, 'b) pfun \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) pfun" (infixl "\<rhd>\<^sub>p" 85) 
is ran_restrict_map .

lift_definition pfun_graph :: "('a, 'b) pfun \<Rightarrow> ('a \<times> 'b) set" is map_graph .

lift_definition graph_pfun :: "('a \<times> 'b) set \<Rightarrow> ('a, 'b) pfun" is graph_map .

instantiation pfun :: (type, type) zero
begin
lift_definition zero_pfun :: "('a, 'b) pfun" is "Map.empty" .
instance ..
end

instantiation pfun :: (type, type) plus
begin
lift_definition plus_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is "op ++" .
instance ..
end

instantiation pfun :: (type, type) minus
begin
lift_definition minus_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is "op --" .
instance ..
end

instance pfun :: (type, type) monoid_add
  by (intro_classes, (transfer, auto)+)

instantiation pfun :: (type, type) inf
begin
lift_definition inf_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is
"\<lambda> f g x. if (x \<in> dom(f) \<inter> dom(g) \<and> f(x) = g(x)) then f(x) else None" .
instance ..
end

abbreviation pfun_inter :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" (infixl "\<inter>\<^sub>p" 80)
where "pfun_inter \<equiv> inf"

instantiation pfun :: (type, type) order
begin
  lift_definition less_eq_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" is
  "\<lambda> f g. f \<subseteq>\<^sub>m g" .
  lift_definition less_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" is
  "\<lambda> f g. f \<subseteq>\<^sub>m g \<and> f \<noteq> g" .
instance
  by (intro_classes, (transfer, auto intro: map_le_trans simp add: map_le_antisym)+)
end

abbreviation pfun_subset :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<subset>\<^sub>p" 50)
where "pfun_subset \<equiv> less"

abbreviation pfun_subset_eq :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<subseteq>\<^sub>p" 50)
where "pfun_subset_eq \<equiv> less_eq"

instance pfun :: (type, type) semilattice_inf
  by (intro_classes, (transfer, auto simp add: map_le_def dom_def)+)

lemma pfun_ext: "\<lbrakk> \<And> x y. (x, y) \<in>\<^sub>p f \<longleftrightarrow> (x, y) \<in>\<^sub>p g \<rbrakk> \<Longrightarrow> f = g"
  by (transfer, simp add: map_ext)

lemma pfun_member_alt_def:
  "(x, y) \<in>\<^sub>p f \<longleftrightarrow> (x \<in> pdom f \<and> f(x)\<^sub>p = y)"
  by (transfer, auto simp add: map_member_alt_def map_apply_def)

lemma pdom_zero [simp]: "pdom 0 = {}"
  by (transfer, simp)

lemma pran_zero [simp]: "pran 0 = {}"
  by (transfer, simp)

lemma pdom_plus [simp]: "pdom (f + g) = pdom f \<union> pdom g"
  by (transfer, auto)

lemma pfun_comp_assoc: "f \<circ>\<^sub>p (g \<circ>\<^sub>p h) = (f \<circ>\<^sub>p g) \<circ>\<^sub>p h"
  by (transfer, simp add: map_comp_assoc)

lemma pfun_comp_left_id [simp]: "pId \<circ>\<^sub>p f = f"
  by (transfer, auto)

lemma pfun_comp_right_id [simp]: "f \<circ>\<^sub>p pId = f"
  by (transfer, auto)

lemma pfun_override_dist_comp:
  "(f + g) \<circ>\<^sub>p h = (f \<circ>\<^sub>p h) + (g \<circ>\<^sub>p h)"
  apply (transfer)
  apply (rule ext)
  apply (auto simp add: map_add_def)
  apply (rename_tac f g h x)
  apply (case_tac "h x")
  apply (auto)
  apply (rename_tac f g h x y)
  apply (case_tac "g y")
  apply (auto)
done

lemma pdom_res_alt_def: "A \<lhd>\<^sub>p f =  f \<circ>\<^sub>p pId_on A"
  by (transfer, rule ext, auto simp add: restrict_map_def)

lemma pran_res_alt_def: "f \<rhd>\<^sub>p A = pId_on A \<circ>\<^sub>p f"
  by (transfer, rule ext, auto simp add: ran_restrict_map_def)

lemma pdom_res_override: "A \<lhd>\<^sub>p (f + g) = (A \<lhd>\<^sub>p f) + (A \<lhd>\<^sub>p g)"
  by (transfer, rule ext, auto simp add: map_add_def restrict_map_def)

lemma pran_res_override: "(f + g) \<rhd>\<^sub>p A \<subseteq>\<^sub>p (f \<rhd>\<^sub>p A) + (g \<rhd>\<^sub>p A)"
  apply (transfer, auto simp add: map_add_def ran_restrict_map_def map_le_def)
  apply (rename_tac f g A a y x)
  apply (case_tac "g a")
  apply (auto)
done

lemma pdom_pdom_res [simp]: "pdom (A \<lhd>\<^sub>p f) = A \<inter> pdom(f)"
  by (transfer, auto)

lemma pran_pran_res [simp]: "pran (f \<rhd>\<^sub>p A) = pran(f) \<inter> A"
  by (transfer, auto)

lemma pdom_res_dist: "(A \<lhd>\<^sub>p f) \<rhd>\<^sub>p B = A \<lhd>\<^sub>p (f \<rhd>\<^sub>p B)"
  by (transfer, auto simp add: restrict_map_def ran_restrict_map_def)

lemma pdom_res_twice [simp]: "A \<lhd>\<^sub>p (B \<lhd>\<^sub>p f) = (A \<inter> B) \<lhd>\<^sub>p f"
  by (transfer, auto simp add: Int_commute)

lemma pfun_member_plus:
  "(x, y) \<in>\<^sub>p f + g \<longleftrightarrow> ((x \<notin> pdom(g) \<and> (x, y) \<in>\<^sub>p f) \<or> (x, y) \<in>\<^sub>p g)"
  by (transfer, simp add: map_member_plus)

lemma pfun_member_minus:
  "(x, y) \<in>\<^sub>p f - g \<longleftrightarrow> (x, y) \<in>\<^sub>p f \<and> (\<not> (x, y) \<in>\<^sub>p g)"
  by (transfer, simp add: map_member_minus)

lemma pfun_minus_unit [simp]:
  fixes f :: "('a, 'b) pfun"
  shows "f - 0 = f"
  by (transfer, simp add: map_minus_def)

lemma pfun_minus_zero [simp]:
  fixes f :: "('a, 'b) pfun"
  shows "0 - f = 0"
  by (transfer, simp add: map_minus_def)

lemma pfun_minus_plus_commute:
  "pdom(g) \<inter> pdom(h) = {} \<Longrightarrow> (f - g) + h = (f + h) - g"
  by (transfer, simp add: map_minus_plus_commute)

lemma pfun_minus_common_subset:
  "\<lbrakk> h \<subseteq>\<^sub>p f; h \<subseteq>\<^sub>p g \<rbrakk> \<Longrightarrow> (f - h = g - h) = (f = g)"
  by (transfer, simp add: map_minus_common_subset)

lemma pfun_graph_inv: "graph_pfun (pfun_graph f) = f"
  by (transfer, simp)

lemma pfun_graph_zero: "pfun_graph 0 = {}"
  by (transfer, simp add: map_graph_def)

lemma pfun_graph_pId_on: "pfun_graph (pId_on A) = Id_on A"
  by (transfer, auto simp add: map_graph_def)

lemma pfun_graph_minus: "pfun_graph (f - g) = pfun_graph f - pfun_graph g"
  by (transfer, simp add: map_graph_minus)

lemma pfun_graph_inter: "pfun_graph (f \<inter>\<^sub>p g) = pfun_graph f \<inter> pfun_graph g"
  apply (transfer, auto simp add: map_graph_def)
  apply (metis option.discI)+
done
  
end