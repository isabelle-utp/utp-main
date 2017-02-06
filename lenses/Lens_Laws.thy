section \<open>Core Lens Laws\<close>

theory Lens_Laws
imports 
  Two Interp
begin

subsection \<open>Lens signature\<close>
  
record ('a, 'b) lens =
  lens_get :: "'b \<Rightarrow> 'a" ("get\<index>")
  lens_put :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("put\<index>")

type_notation
  lens (infixr "\<Longrightarrow>" 0)

named_theorems lens_defs

definition lens_create :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("create\<index>") where
[lens_defs]: "lens_create X v = lens_put X undefined v"

subsection {* Weak lenses *}

locale weak_lens =
  fixes x :: "'a \<Longrightarrow> 'b" (structure)
  assumes put_get: "get (put \<sigma> v) = v"
begin

  lemma create_get: "get (create v) = v"
    by (simp add: lens_create_def put_get)

  lemma create_inj: "inj create"
    by (metis create_get injI)

  definition update :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b)" where
  [lens_defs]: "update f \<sigma> = put \<sigma> (f (get \<sigma>))"

  lemma get_update: "get (update f \<sigma>) = f (get \<sigma>)"
    by (simp add: put_get update_def)

  lemma view_determination: "put \<sigma> u = put \<rho> v \<Longrightarrow> u = v"
    by (metis put_get)

  lemma put_inj: "inj (put \<sigma>)"
    by (simp add: injI view_determination)
end

declare weak_lens.put_get [simp]
declare weak_lens.create_get [simp]

subsection {* Well-behaved lenses *}

locale wb_lens = weak_lens +
  assumes get_put: "put \<sigma> (get \<sigma>) = \<sigma>"
begin

  lemma put_twice: "put (put \<sigma> v) v = put \<sigma> v"
    by (metis get_put put_get)

  lemma put_surjectivity: "\<exists> \<rho> v. put \<rho> v = \<sigma>"
    using get_put by blast

  lemma source_stability: "\<exists> v. put \<sigma> v = \<sigma>"
    using get_put by auto

end

declare wb_lens.get_put [simp]

lemma wb_lens_weak [simp]: "wb_lens x \<Longrightarrow> weak_lens x"
  by (simp_all add: wb_lens_def)


subsection {* Mainly well-behaved lenses *}

locale mwb_lens = weak_lens +
  assumes put_put: "put (put \<sigma> v) u = put \<sigma> u"
begin

  lemma update_comp: "update f (update g \<sigma>) = update (f \<circ> g) \<sigma>"
    by (simp add: put_get put_put update_def)

end

declare mwb_lens.put_put [simp]

lemma mwb_lens_weak [simp]:
  "mwb_lens x \<Longrightarrow> weak_lens x"
  by (simp add: mwb_lens_def)

subsection {* Very well-behaved lenses *}

locale vwb_lens = wb_lens + mwb_lens
begin

  lemma source_determination:"get \<sigma> = get \<rho> \<Longrightarrow> put \<sigma> v = put \<rho> v \<Longrightarrow> \<sigma> = \<rho>"
    by (metis get_put put_put)

 lemma put_eq:
   "\<lbrakk> get \<sigma> = k; put \<sigma> u = put \<rho> v \<rbrakk> \<Longrightarrow> put \<rho> k = \<sigma>"
   by (metis get_put put_put)

end

lemma vwb_lens_wb [simp]: "vwb_lens x \<Longrightarrow> wb_lens x"
  by (simp_all add: vwb_lens_def)

lemma vwb_lens_mwb [simp]: "vwb_lens x \<Longrightarrow> mwb_lens x"
  by (simp_all add: vwb_lens_def)

subsection {* Ineffectual lenses *}

locale ief_lens = weak_lens +
  assumes put_inef: "put \<sigma> v = \<sigma>"
begin

sublocale vwb_lens
proof
  fix \<sigma> v u
  show "put \<sigma> (get \<sigma>) = \<sigma>"
    by (simp add: put_inef)
  show "put (put \<sigma> v) u = put \<sigma> u"
    by (simp add: put_inef)
qed

lemma ineffectual_const_get:
  "\<exists> v.  \<forall> \<sigma>. get \<sigma> = v"
  by (metis create_get lens_create_def put_inef)

end

abbreviation "eff_lens X \<equiv> (weak_lens X \<and> (\<not> ief_lens X))"

subsection {* Bijective lenses *}

text {* Bijective lenses express that two views of a particular source are equivalent. *}

locale bij_lens = weak_lens +
  assumes strong_get_put: "put \<sigma> (get \<rho>) = \<rho>"
begin

sublocale vwb_lens
proof
  fix \<sigma> v u
  show "put \<sigma> (get \<sigma>) = \<sigma>"
    by (simp add: strong_get_put)
  show "put (put \<sigma> v) u = put \<sigma> u"
    by (metis put_get strong_get_put)
qed

  lemma put_surj: "surj (put \<sigma>)"
    by (metis strong_get_put surj_def)

  lemma put_bij: "bij (put \<sigma>)"
    by (simp add: bijI put_inj put_surj)

  lemma put_is_create: "put \<sigma> v = create v"
    by (metis create_get strong_get_put)

  lemma get_create: "create (get \<sigma>) = \<sigma>"
    by (metis put_get put_is_create source_stability)

end

declare bij_lens.strong_get_put [simp]
declare bij_lens.get_create [simp]

lemma bij_lens_weak [simp]:
  "bij_lens x \<Longrightarrow> weak_lens x"
  by (simp_all add: bij_lens_def)

lemma bij_lens_vwb [simp]: "bij_lens x \<Longrightarrow> vwb_lens x"
  by (unfold_locales, simp_all add: bij_lens.put_is_create)
  
subsection {* Lens independence *}

locale lens_indep =
  fixes X :: "'a \<Longrightarrow> 'c" and Y :: "'b \<Longrightarrow> 'c"
  assumes lens_put_comm: "lens_put X (lens_put Y \<sigma> v) u = lens_put Y (lens_put X \<sigma> u) v"
  and lens_put_irr1: "lens_get X (lens_put Y \<sigma> v) = lens_get X \<sigma>"
  and lens_put_irr2: "lens_get Y (lens_put X \<sigma> u) = lens_get Y \<sigma>"

notation lens_indep (infix "\<bowtie>" 50)

lemma lens_indepI:
  "\<lbrakk> \<And> u v \<sigma>. lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v;
     \<And> v \<sigma>. lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>;
     \<And> u \<sigma>. lens_get y (lens_put x \<sigma> u) = lens_get y \<sigma> \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lens_indep_def)

text {* Independence is irreflexive for effectual lenses *}

lemma lens_indep_sym:  "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
  by (simp add: lens_indep_def)

lemma lens_indep_comm:
  "x \<bowtie> y \<Longrightarrow> lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v"
  by (simp add: lens_indep_def)

lemma lens_indep_get [simp]:
  assumes "x \<bowtie> y"
  shows "lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>"
  using assms lens_indep_def by fastforce

end