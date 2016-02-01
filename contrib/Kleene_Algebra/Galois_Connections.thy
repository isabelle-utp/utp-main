theory Galois_Connections
  imports Main
begin

notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)

notation Inf ("\<Sqinter>_" [900] 900)
notation Sup ("\<Squnion>_" [900] 900)

notation bot ("\<bottom>")
notation top ("\<top>")

definition idem :: "('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"idem f \<longleftrightarrow> (\<forall> x. f(f(x)) = f(x))"

lemma idem [simp]: "idem f \<Longrightarrow> f(f(x)) = f(x)"
  by (simp add: idem_def)

lemma idem_comp [simp]: "idem f \<Longrightarrow> f \<circ> f = f"
  by auto

default_sort order

definition galois_connection :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "galois_connection f g \<longleftrightarrow> (\<forall>x y. (f x \<le> y) \<longleftrightarrow> (x \<le> g y))"

definition dual_galois_connection :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "dual_galois_connection f g \<equiv> \<forall>x y. (f x \<ge> y) \<longleftrightarrow> (x \<ge> g y)"

definition lower_adjoint :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "lower_adjoint f \<equiv> \<exists>g. galois_connection f g"

definition upper_adjoint :: "('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "upper_adjoint g \<equiv> \<exists>f. galois_connection f g"

lemma galois_deflation: "galois_connection f g \<Longrightarrow> f (g y) \<le> y" 
  by (metis galois_connection_def le_less)

lemma galois_inflation: "galois_connection f g \<Longrightarrow> x \<le> g (f x)" 
  using galois_connection_def by blast

lemma lower_iso: "galois_connection f g \<Longrightarrow> mono f"
  by (metis (full_types) galois_connection_def galois_inflation mono_def order.trans)

lemma upper_iso: "galois_connection f g \<Longrightarrow> mono g"
  by (metis (no_types, lifting) dual_order.trans galois_connection_def galois_deflation monoI)

lemma galois_lower_comp: 
  assumes "galois_connection f g"
  shows "f \<circ> g \<circ> f = f"
proof
  fix x
  show "(f \<circ> g \<circ> f) x = f x"
    by (metis (mono_tags, hide_lams) antisym assms comp_apply galois_deflation galois_inflation lower_iso mono_def)
qed

lemma galois_upper_comp: 
  assumes "galois_connection f g"
  shows "g \<circ> f \<circ> g = g"
proof
  fix x
  have "\<forall>a. a \<le> g (f a)"
    by (simp add: assms galois_inflation)
  thus "(g \<circ> f \<circ> g) x = g x"
    by (metis (no_types, lifting) antisym assms comp_apply galois_deflation mono_def upper_iso)
qed

lemma galois_upper_idem1: "galois_connection f g \<Longrightarrow> idem (f \<circ> g)"
  by (metis (no_types, lifting) comp_apply galois_upper_comp idem_def)

lemma galois_upper_idem2: "galois_connection f g \<Longrightarrow> idem (g \<circ> f)"
  by (metis (no_types, lifting) comp_apply galois_upper_comp idem_def)

lemma galois_dual: "galois_connection f g \<Longrightarrow> dual_galois_connection g f"
  by (metis dual_galois_connection_def galois_connection_def)

lemma dual_galois_dual: "dual_galois_connection f g \<Longrightarrow> galois_connection g f"
  by (metis dual_galois_connection_def galois_connection_def)

end