section {* Alphabetised relations *}

theory utp_rel
imports  
  utp_pred
  utp_lift
begin

default_sort type

named_theorems urel_defs

consts
  useq   :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 15)
  uskip  :: "'a" ("II")

definition in\<alpha> :: "('\<alpha>, '\<alpha> \<times> '\<beta>) uvar" where
"in\<alpha> = \<lparr> lens_get = fst, lens_put = \<lambda> (A, A') v. (v, A') \<rparr>"

definition out\<alpha> :: "('\<beta>, '\<alpha> \<times> '\<beta>) uvar" where
"out\<alpha> = \<lparr> lens_get = snd, lens_put = \<lambda> (A, A') v. (A, v) \<rparr>"

declare in\<alpha>_def [urel_defs]
declare out\<alpha>_def [urel_defs]

lemma var_in_alpha [simp]: "x ;\<^sub>L in\<alpha> = ivar x"
  by (simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma var_out_alpha [simp]: "x ;\<^sub>L out\<alpha> = ovar x"
  by (simp add: out\<alpha>_def out_var_def snd_lens_def)

text {* The alphabet of a relation consists of the input and output portions *}

lemma alpha_in_out:
  "\<Sigma> \<approx>\<^sub>L in\<alpha> +\<^sub>L out\<alpha>"
  by (metis fst_lens_def fst_snd_id_lens in\<alpha>_def lens_equiv_refl out\<alpha>_def snd_lens_def)

type_synonym '\<alpha> condition       = "'\<alpha> upred"
type_synonym ('\<alpha>, '\<beta>) relation  = "('\<alpha> \<times> '\<beta>) upred"
type_synonym '\<alpha> hrelation       = "('\<alpha> \<times> '\<alpha>) upred"

definition cond::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" 
                                                          ("(3_ \<triangleleft> _ \<triangleright>/ _)" [14,0,15] 14)
where "(P \<triangleleft> b \<triangleright> Q) \<equiv> (b \<and> P) \<or> ((\<not> b) \<and> Q)"

abbreviation rcond::"('\<alpha>,  '\<beta>) relation \<Rightarrow> '\<alpha> condition \<Rightarrow> ('\<alpha>,  '\<beta>) relation \<Rightarrow> ('\<alpha>,  '\<beta>) relation" 
                                                          ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r / _)" [14,0,15] 14)
where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>< \<triangleright> Q)"

lift_definition seqr::"(('\<alpha> \<times> '\<beta>) upred) \<Rightarrow> (('\<beta> \<times> '\<gamma>) upred) \<Rightarrow> ('\<alpha> \<times> '\<gamma>) upred"
is "\<lambda> P Q r. r \<in> ({p. P p} O {q. Q q})" .

lift_definition conv_r :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta> \<times> '\<alpha>) uexpr" ("_\<^sup>-" [999] 999)
is "\<lambda> e (b1, b2). e (b2, b1)" .

definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>'\<alpha> hrelation" where
[urel_defs]: "skip_ra v = ($v\<acute> =\<^sub>u $v)"

syntax
  "_skip_ra" :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")

translations
  "_skip_ra v" == "CONST skip_ra v"

abbreviation usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> \<sigma> \<oplus>\<^sub>s in\<alpha>"

abbreviation usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) usubst \<Rightarrow> '\<alpha> usubst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s \<equiv> \<sigma> \<restriction>\<^sub>s in\<alpha>"


definition assigns_ra :: "'\<alpha> usubst \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> '\<alpha> hrelation" ("\<langle>_\<rangle>\<^bsub>_\<^esub>") where
"\<langle>\<sigma>\<rangle>\<^bsub>a\<^esub> = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II\<^bsub>a\<^esub>)"

lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrelation" ("\<langle>_\<rangle>\<^sub>a")
  is "\<lambda> \<sigma> (A, A'). A' = \<sigma>(A)" .

definition skip_r :: "'\<alpha> hrelation" where
"skip_r = assigns_r id"

abbreviation assign_r :: "('t, '\<alpha>) uvar \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrelation"
where "assign_r x v \<equiv> assigns_r [x \<mapsto>\<^sub>s v]"

abbreviation assign_2_r :: 
  "('t1, '\<alpha>) uvar \<Rightarrow> ('t2, '\<alpha>) uvar \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrelation"
where "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

nonterminal 
  svid_list and uexpr_list

syntax
  "_svid_unit"  :: "svid \<Rightarrow> svid_list" ("_")
  "_svid_list"  :: "svid \<Rightarrow> svid_list \<Rightarrow> svid_list" ("_,/ _")
  "_uexpr_unit" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list" ("_" [40] 40)
  "_uexpr_list" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list \<Rightarrow> uexpr_list" ("_,/ _" [40,40] 40)
  "_assignment" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrelation"  (infixr ":=" 62)
  "_mk_usubst"  :: "svid_list \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"

translations
  "_mk_usubst \<sigma> (_svid_unit x) v" == "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" == "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST assigns_r (_mk_usubst (CONST id) xs vs)"
  "x := v" <= "CONST assigns_r (CONST subst_upd (CONST id) (CONST svar x) v)"
  "x := v" <= "CONST assigns_r (CONST subst_upd (CONST id) x v)"
  "x,y := u,v" <= "CONST assigns_r (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"

adhoc_overloading
  useq seqr and
  uskip skip_r

method rel_simp = ((simp add: upred_defs urel_defs)?, (transfer, (rule_tac ext)?, simp_all add: lens_defs urel_defs relcomp_unfold fun_eq_iff prod.case_eq_if)?)
method rel_tac = ((simp add: upred_defs urel_defs)?, (transfer, (rule_tac ext)?, auto simp add: lens_defs urel_defs relcomp_unfold fun_eq_iff prod.case_eq_if)?)

text {* We describe some properties of relations *}

definition ufunctional :: "('a, 'b) relation \<Rightarrow> bool"
where "ufunctional R \<longleftrightarrow> (II \<sqsubseteq> (R\<^sup>- ;; R))"

declare ufunctional_def [urel_defs]

definition uinj :: "('a, 'b) relation \<Rightarrow> bool"
where "uinj R \<longleftrightarrow> II \<sqsubseteq> (R ;; R\<^sup>-)"

declare uinj_def [urel_defs]

text {* A test is like a precondition, except that it identifies to the postcondition. It
        forms the basis for Kleene Algebra with Tests (KAT). *}

definition lift_test :: "'\<alpha> condition \<Rightarrow> '\<alpha> hrelation" ("\<lceil>_\<rceil>\<^sub>t")
where "\<lceil>b\<rceil>\<^sub>t = (\<lceil>b\<rceil>\<^sub>< \<and> II)"
 
declare cond_def [urel_defs]
declare skip_r_def [urel_defs]

text {* We implement a poor man's version of alphabet restriction that hides a variable within a relation *}

definition rel_var_res :: "'\<alpha> hrelation \<Rightarrow> ('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrelation" (infix "\<restriction>\<^sub>\<alpha>" 80) where
"P \<restriction>\<^sub>\<alpha> x = (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P)"

declare rel_var_res_def [urel_defs]

subsection {* Unrestriction Laws *}

lemma unrest_iuvar [unrest]: "semi_uvar x \<Longrightarrow> out\<alpha> \<sharp> $x"
  by (simp add: out\<alpha>_def, transfer, auto)

lemma unrest_ouvar [unrest]: "semi_uvar x \<Longrightarrow> in\<alpha> \<sharp> $x\<acute>"
  by (simp add: in\<alpha>_def, transfer, auto)

lemma unrest_semir_undash [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "$x \<sharp> P"
  shows "$x \<sharp> (P ;; Q)"
  using assms by (rel_tac)

lemma unrest_semir_dash [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "$x\<acute> \<sharp> Q"
  shows "$x\<acute> \<sharp> (P ;; Q)"
  using assms by (rel_tac)

lemma unrest_cond [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> b; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<triangleleft> b \<triangleright> Q)"
  by (rel_tac)

lemma unrest_in\<alpha>_var [unrest]:
  "\<lbrakk> semi_uvar x; in\<alpha> \<sharp> (P :: ('\<alpha>, '\<beta>) relation) \<rbrakk> \<Longrightarrow> $x \<sharp> P"
  by (pred_tac, simp add: in\<alpha>_def, blast, metis in\<alpha>_def lens.select_convs(2) old.prod.case)

lemma unrest_out\<alpha>_var [unrest]:
  "\<lbrakk> semi_uvar x; out\<alpha> \<sharp> (P :: ('\<alpha>, '\<beta>) relation) \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P"
  by (pred_tac, simp add: out\<alpha>_def, blast, metis lens.select_convs(2) old.prod.case out\<alpha>_def)

lemma in\<alpha>_uvar [simp]: "uvar in\<alpha>"
  by (unfold_locales, auto simp add: in\<alpha>_def)

lemma out\<alpha>_uvar [simp]: "uvar out\<alpha>"
  by (unfold_locales, auto simp add: out\<alpha>_def)

lemma unrest_pre_out\<alpha> [unrest]: "out\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub><"
  by (transfer, auto simp add: out\<alpha>_def)

lemma unrest_post_in\<alpha> [unrest]: "in\<alpha> \<sharp> \<lceil>b\<rceil>\<^sub>>"
  by (transfer, auto simp add: in\<alpha>_def)

lemma unrest_pre_in_var [unrest]: 
  "x \<sharp> p1 \<Longrightarrow> $x \<sharp> \<lceil>p1\<rceil>\<^sub><"
  by (transfer, simp)

lemma unrest_post_out_var [unrest]: 
  "x \<sharp> p1 \<Longrightarrow> $x\<acute> \<sharp> \<lceil>p1\<rceil>\<^sub>>"
  by (transfer, simp)

lemma unrest_convr_out\<alpha> [unrest]: 
  "in\<alpha> \<sharp> p \<Longrightarrow> out\<alpha> \<sharp> p\<^sup>-"
  by (transfer, auto simp add: in\<alpha>_def out\<alpha>_def)

lemma unrest_convr_in\<alpha> [unrest]: 
  "out\<alpha> \<sharp> p \<Longrightarrow> in\<alpha> \<sharp> p\<^sup>-"
  by (transfer, auto simp add: in\<alpha>_def out\<alpha>_def)

lemma unrest_in_rel_var_res [unrest]: 
  "uvar x \<Longrightarrow> $x \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

lemma unrest_out_rel_var_res [unrest]: 
  "uvar x \<Longrightarrow> $x\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

subsection {* Substitution laws *}

text {* It should be possible to substantially generalise the following two laws *}

lemma usubst_seq_left [usubst]: 
  "\<lbrakk> semi_uvar x; out\<alpha> \<sharp> v \<rbrakk> \<Longrightarrow> (P ;; Q)\<lbrakk>v/$x\<rbrakk> = ((P\<lbrakk>v/$x\<rbrakk>) ;; Q)"
  apply (rel_tac)
  apply (rename_tac x v P Q a y ya)
  apply (rule_tac x="ya" in exI)
  apply (simp)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="y" in spec)
  apply (drule_tac x="ya" in spec)
  apply (simp)
  apply (rename_tac x v P Q a ba y)
  apply (rule_tac x="y" in exI)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="y" in spec)
  apply (drule_tac x="ba" in spec)
  apply (simp)
done

lemma usubst_seq_right [usubst]: 
  "\<lbrakk> semi_uvar x; in\<alpha> \<sharp> v \<rbrakk> \<Longrightarrow> (P ;; Q)\<lbrakk>v/$x\<acute>\<rbrakk> = (P ;; Q\<lbrakk>v/$x\<acute>\<rbrakk>)"
  by (rel_tac, metis+)

lemma usubst_condr [usubst]:
  "\<sigma> \<dagger> (P \<triangleleft> b \<triangleright> Q) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> b \<triangleright> \<sigma> \<dagger> Q)"
  by rel_tac

lemma subst_skip_r [usubst]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "II\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk> = (x := v)"
  by (rel_tac)

lemma usubst_upd_in_comp [usubst]:
  "\<sigma>(&in\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x \<mapsto>\<^sub>s v)"
  by (simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma usubst_upd_out_comp [usubst]:
  "\<sigma>(&out\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x\<acute> \<mapsto>\<^sub>s v)"
  by (simp add: out\<alpha>_def out_var_def snd_lens_def)

lemma subst_lift_upd [usubst]: 
  fixes x :: "('a, '\<alpha>) uvar"
  shows "\<lceil>\<sigma>(x \<mapsto>\<^sub>s v)\<rceil>\<^sub>s = \<lceil>\<sigma>\<rceil>\<^sub>s($x \<mapsto>\<^sub>s \<lceil>v\<rceil>\<^sub><)"
  by (simp add: alpha usubst, simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma subst_lift_pre [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>b\<rceil>\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub><"
  by (metis apply_subst_ext fst_lens_def fst_vwb_lens in\<alpha>_def)

lemma unrest_usubst_lift_in [unrest]:
  "x \<sharp> P \<Longrightarrow> $x \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by (pred_tac, auto simp add: unrest_usubst_def in\<alpha>_def)

lemma unrest_usubst_lift_out [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "$x\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by (pred_tac, auto simp add: unrest_usubst_def in\<alpha>_def)

subsection {* Relation laws *}

text {* Homogeneous relations form a quantale *}

abbreviation truer :: "'\<alpha> hrelation" ("true\<^sub>h") where
"truer \<equiv> true"

abbreviation falser :: "'\<alpha> hrelation" ("false\<^sub>h") where
"falser \<equiv> false"

interpretation upred_quantale: unital_quantale_plus
  where times = seqr and one = skip_r and Sup = Sup and Inf = Inf and inf = inf and less_eq = less_eq and less = less
  and sup = sup and bot = bot and top = top
apply (unfold_locales)
apply (rel_tac)
apply (unfold SUP_def, transfer, auto)
apply (unfold SUP_def, transfer, auto)
apply (unfold INF_def, transfer, auto)
apply (unfold INF_def, transfer, auto)
apply (rel_tac)
apply (rel_tac)
done

lemma drop_pre_inv [simp]: "\<lbrakk> out\<alpha> \<sharp> p \<rbrakk> \<Longrightarrow> \<lceil>\<lfloor>p\<rfloor>\<^sub><\<rceil>\<^sub>< = p"
  by (pred_tac, auto simp add: out\<alpha>_def lens_create_def fst_lens_def prod.case_eq_if)

abbreviation ustar :: "'\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("_\<^sup>\<star>\<^sub>u" [999] 999) where
"P\<^sup>\<star>\<^sub>u \<equiv> unital_quantale.qstar II op ;; Sup P"

definition while :: "'\<alpha> condition \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("while _ do _ od") where
"while b do P od = ((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u \<and> (\<not> \<lceil>b\<rceil>\<^sub>>))"

declare while_def [urel_defs] 

text {* While loops with invariant decoration *}

definition while_inv :: "'\<alpha> condition \<Rightarrow> '\<alpha> condition \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("while _ invr _ do _ od") where
"while b invr p do S od = while b do S od"

lemma cond_idem:"(P \<triangleleft> b \<triangleright> P) = P" by rel_tac 

lemma cond_symm:"(P \<triangleleft> b \<triangleright> Q) = (Q \<triangleleft> \<not> b \<triangleright> P)" by rel_tac

lemma cond_assoc: "((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> R) = (P \<triangleleft> b \<and> c \<triangleright> (Q \<triangleleft> c \<triangleright> R))" by rel_tac

lemma cond_distr: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> c \<triangleright> R)) = ((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> (P \<triangleleft> b \<triangleright> R))" by rel_tac

lemma cond_unit_T [simp]:"(P \<triangleleft> true \<triangleright> Q) = P" by rel_tac

lemma cond_unit_F [simp]:"(P \<triangleleft> false \<triangleright> Q) = Q" by rel_tac

lemma cond_and_T_integrate:
  "((P \<and> b) \<or> (Q \<triangleleft> b \<triangleright> R)) = ((P \<or> Q) \<triangleleft> b \<triangleright> R)"
  by (rel_tac)

lemma cond_L6: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)" by rel_tac

lemma cond_L7: "(P \<triangleleft> b \<triangleright> (P \<triangleleft> c \<triangleright> Q)) = (P \<triangleleft> b \<or> c \<triangleright> Q)" by rel_tac

lemma cond_and_distr: "((P \<and> Q) \<triangleleft> b \<triangleright> (R \<and> S)) = ((P \<triangleleft> b \<triangleright> R) \<and> (Q \<triangleleft> b \<triangleright> S))" by rel_tac

lemma cond_or_distr: "((P \<or> Q) \<triangleleft> b \<triangleright> (R \<or> S)) = ((P \<triangleleft> b \<triangleright> R) \<or> (Q \<triangleleft> b \<triangleright> S))" by rel_tac

lemma cond_imp_distr: 
"((P \<Rightarrow> Q) \<triangleleft> b \<triangleright> (R \<Rightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Rightarrow> (Q \<triangleleft> b \<triangleright> S))" by rel_tac

lemma cond_eq_distr: 
"((P \<Leftrightarrow> Q) \<triangleleft> b \<triangleright> (R \<Leftrightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Leftrightarrow> (Q \<triangleleft> b \<triangleright> S))" by rel_tac

lemma cond_conj_distr:"(P \<and> (Q \<triangleleft> b \<triangleright> S)) = ((P \<and> Q) \<triangleleft> b \<triangleright> (P \<and> S))" by rel_tac

lemma cond_disj_distr:"(P \<or> (Q \<triangleleft> b \<triangleright> S)) = ((P \<or> Q) \<triangleleft> b \<triangleright> (P \<or> S))" by rel_tac

lemma cond_neg: "\<not> (P \<triangleleft> b \<triangleright> Q) = (\<not> P \<triangleleft> b \<triangleright> \<not> Q)" by rel_tac

lemma comp_cond_left_distr:
  "((P \<triangleleft> b \<triangleright>\<^sub>r Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright>\<^sub>r (Q ;; R))"
  by rel_tac

lemma cond_var_subst_left:
  assumes "uvar x"
  shows "(P \<triangleleft> $x \<triangleright> Q) = (P\<lbrakk>true/$x\<rbrakk> \<triangleleft> $x \<triangleright> Q)"
  using assms by (metis cond_def conj_pos_var_subst) 

lemma cond_var_subst_right:
  assumes "uvar x"
  shows "(P \<triangleleft> $x \<triangleright> Q) = (P \<triangleleft> $x \<triangleright> Q\<lbrakk>false/$x\<rbrakk>)"
  using assms by (metis cond_def conj_neg_var_subst) 

lemma cond_var_split:
  "uvar x \<Longrightarrow> (P\<lbrakk>true/x\<rbrakk> \<triangleleft> var x \<triangleright> P\<lbrakk>false/x\<rbrakk>) = P"
  by (rel_tac, (metis (full_types) vwb_lens.put_eq)+)

lemma cond_seq_left_distr:
  "out\<alpha> \<sharp> b \<Longrightarrow> ((P \<triangleleft> b \<triangleright> Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright> (Q ;; R))"
  by (rel_tac, blast+)

lemma cond_seq_right_distr:
  "in\<alpha> \<sharp> b \<Longrightarrow> (P ;; (Q \<triangleleft> b \<triangleright> R)) = ((P ;; Q) \<triangleleft> b \<triangleright> (P ;; R))"
  by (rel_tac, blast+)

text {* These laws may seem to duplicate quantale laws, but they don't -- they are
        applicable to non-homogeneous relations as well, which will become important
        later. *}

lemma seqr_assoc: "(P ;; (Q ;; R)) = ((P ;; Q) ;; R)" 
  by rel_tac

lemma seqr_left_unit [simp]:
  "(II ;; P) = P"
  by rel_tac

lemma seqr_right_unit [simp]:
  "(P ;; II) = P"
  by rel_tac

lemma seqr_left_zero [simp]:
  "(false ;; P) = false"
  by pred_tac
  
lemma seqr_right_zero [simp]:
  "(P ;; false) = false"
  by pred_tac

lemma seqr_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ;; Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 ;; Q\<^sub>2)"
  by (rel_tac, blast)

lemma spec_refine:
  "Q \<sqsubseteq> (P \<and> R) \<Longrightarrow> (P \<Rightarrow> Q) \<sqsubseteq> R"
  by (rel_tac)

lemma cond_skip: "out\<alpha> \<sharp> b \<Longrightarrow> (b \<and> II) = (II \<and> b\<^sup>-)"
  by (rel_tac)

lemma pre_skip_post: "(\<lceil>b\<rceil>\<^sub>< \<and> II) = (II \<and> \<lceil>b\<rceil>\<^sub>>)"
  by (rel_tac)

lemma skip_var:
  fixes x :: "(bool, '\<alpha>) uvar"
  shows "($x \<and> II) = (II \<and> $x\<acute>)"
  by (rel_tac)

lemma seqr_exists_left:
  "semi_uvar x \<Longrightarrow> ((\<exists> $x \<bullet> P) ;; Q) = (\<exists> $x \<bullet> (P ;; Q))"
  by (rel_tac)

lemma seqr_exists_right:
  "semi_uvar x \<Longrightarrow> (P ;; (\<exists> $x\<acute> \<bullet> Q)) = (\<exists> $x\<acute> \<bullet> (P ;; Q))"
  by (rel_tac)

lemma assigns_subst [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a"
  by (rel_tac)

lemma assigns_r_comp: "(\<langle>\<sigma>\<rangle>\<^sub>a ;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P)"
  by rel_tac

lemma assigns_r_feasible:
  "(\<langle>\<sigma>\<rangle>\<^sub>a ;; true) = true"
  by (rel_tac)

lemma assign_subst [usubst]:
  "\<lbrakk> semi_uvar x; semi_uvar y \<rbrakk> \<Longrightarrow> [$x \<mapsto>\<^sub>s \<lceil>u\<rceil>\<^sub><] \<dagger> (y := v) = (x, y := u, [x \<mapsto>\<^sub>s u] \<dagger> v)"
  by rel_tac
 
lemma assigns_idem: "semi_uvar x \<Longrightarrow> (x,x := u,v) = (x := v)"
  by (simp add: usubst)

lemma assigns_comp: "(\<langle>f\<rangle>\<^sub>a ;; \<langle>g\<rangle>\<^sub>a) = \<langle>g \<circ> f\<rangle>\<^sub>a"
  by (simp add: assigns_r_comp usubst) 

lemma assigns_r_conv:
  "bij f \<Longrightarrow> \<langle>f\<rangle>\<^sub>a\<^sup>- = \<langle>inv f\<rangle>\<^sub>a"
  by (rel_tac, simp_all add: bij_is_inj bij_is_surj surj_f_inv_f)

lemma assign_r_comp: "semi_uvar x \<Longrightarrow> (x := u ;; P) = P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>"
  by (simp add: assigns_r_comp usubst)

lemma assign_test: "semi_uvar x \<Longrightarrow> (x := \<guillemotleft>u\<guillemotright> ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright>)"
  by (simp add: assigns_comp subst_upd_comp subst_lit usubst_upd_idem)

lemma assign_twice: "\<lbrakk> uvar x; x \<sharp> f \<rbrakk> \<Longrightarrow> (x := e ;; x := f) = (x := f)"
  by (simp add: assigns_comp usubst)

lemma assign_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x := e ;; y := f) = (y := f ;; x := e)"
  using assms
  by (rel_tac, simp_all add: lens_indep_comm)

lemma assign_cond:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "out\<alpha> \<sharp> b"
  shows "(x := e ;; (P \<triangleleft> b \<triangleright> Q)) = ((x := e ;; P) \<triangleleft> (b\<lbrakk>\<lceil>e\<rceil>\<^sub></$x\<rbrakk>) \<triangleright> (x := e ;; Q))"
  by rel_tac

lemma assign_rcond:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x := e ;; (P \<triangleleft> b \<triangleright>\<^sub>r Q)) = ((x := e ;; P) \<triangleleft> (b\<lbrakk>e/x\<rbrakk>) \<triangleright>\<^sub>r (x := e ;; Q))"
  by rel_tac

lemma assign_r_alt_def:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "x := v = II\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk>"
  by rel_tac

lemma assigns_r_ufunc: "ufunctional \<langle>f\<rangle>\<^sub>a"
  by (rel_tac)

lemma assigns_r_uinj: "inj f \<Longrightarrow> uinj \<langle>f\<rangle>\<^sub>a"
  by (rel_tac, simp add: inj_eq)

lemma assigns_r_swap_uinj:
  "\<lbrakk> uvar x; uvar y; x \<bowtie> y \<rbrakk> \<Longrightarrow> uinj (x,y := &y,&x)"
  using assigns_r_uinj swap_usubst_inj by auto

lemma skip_r_unfold:
  "uvar x \<Longrightarrow> II = ($x\<acute> =\<^sub>u $x \<and> II\<restriction>\<^sub>\<alpha>x)"
  by (rel_tac, blast, metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)

lemma skip_r_alpha_eq:
  "II = ($\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"
  by (rel_tac)

lemma skip_ra_unfold:
  "II\<^bsub>x,y\<^esub> = ($x\<acute> =\<^sub>u $x \<and> II\<^bsub>y\<^esub>)"
  by (rel_tac)

lemma skip_res_as_ra:
  "\<lbrakk> vwb_lens y; x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L; x \<bowtie> y \<rbrakk> \<Longrightarrow> II\<restriction>\<^sub>\<alpha>x = II\<^bsub>y\<^esub>"
  apply (rel_tac)
  apply (metis (no_types, lifting) lens_indep_def)
  apply (metis vwb_lens.put_eq)
done

lemma assign_unfold:
  "uvar x \<Longrightarrow> (x := v) = ($x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub>< \<and> II\<restriction>\<^sub>\<alpha>x)"
  apply (rel_tac, auto simp add: comp_def)
  using vwb_lens.put_eq by fastforce

lemma seqr_or_distl:
  "((P \<or> Q) ;; R) = ((P ;; R) \<or> (Q ;; R))"
  by rel_tac

lemma seqr_or_distr:
  "(P ;; (Q \<or> R)) = ((P ;; Q) \<or> (P ;; R))"
  by rel_tac

lemma seqr_and_distr_ufunc:
  "ufunctional P \<Longrightarrow> (P ;; (Q \<and> R)) = ((P ;; Q) \<and> (P ;; R))"
  by rel_tac

lemma seqr_and_distl_uinj:
  "uinj R \<Longrightarrow> ((P \<and> Q) ;; R) = ((P ;; R) \<and> (Q ;; R))"
  by (rel_tac, metis)

lemma seqr_unfold:
  "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<Sigma>\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<Sigma>\<rbrakk>)"
  by rel_tac

lemma seqr_middle: 
  assumes "uvar x"
  shows "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  apply (rel_tac)
  apply (rename_tac xa P Q a b y)
  apply (rule_tac x="get\<^bsub>xa\<^esub> y" in exI)
  apply (rule_tac x="y" in exI)
  apply (simp)
done

lemma seqr_left_one_point:
  assumes "uvar x"
  shows "(P \<and> ($x\<acute> =\<^sub>u \<guillemotleft>v\<guillemotright>) ;; Q) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_tac, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point:
  assumes "uvar x"
  shows "(P ;; ($x =\<^sub>u \<guillemotleft>v\<guillemotright>) \<and> Q) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_tac, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_insert_ident_left:
  assumes "uvar x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(($x\<acute> =\<^sub>u $x \<and> P) ;; Q) = (P ;; Q)"
  using assms
  by (rel_tac, meson vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_insert_ident_right:
  assumes "uvar x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(P ;; ($x\<acute> =\<^sub>u $x \<and> Q)) = (P ;; Q)"
  using assms
  by (rel_tac, metis (no_types, hide_lams) vwb_lens_def wb_lens_def weak_lens.put_get)

lemma seq_var_ident_lift:
  assumes "uvar x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(($x\<acute> =\<^sub>u $x \<and> P) ;; ($x\<acute> =\<^sub>u $x) \<and> Q) = ($x\<acute> =\<^sub>u $x \<and> (P ;; Q))"
  using assms apply (rel_tac)
  by (metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)

theorem precond_equiv:
  "P = (P ;; true) \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  by (rel_tac)

theorem postcond_equiv:
  "P = (true ;; P) \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  by (rel_tac)

lemma precond_right_unit: "out\<alpha> \<sharp> p \<Longrightarrow> (p ;; true) = p"
  by (metis precond_equiv)
  
lemma postcond_left_unit: "in\<alpha> \<sharp> p \<Longrightarrow> (true ;; p) = p"
  by (metis postcond_equiv)

theorem precond_left_zero:
  assumes "out\<alpha> \<sharp> p" "p \<noteq> false"
  shows "(true ;; p) = true"
  using assms
  apply (simp add: out\<alpha>_def upred_defs)
  apply (transfer, auto simp add: relcomp_unfold, rule ext, auto)
  apply (rename_tac p b)
  apply (subgoal_tac "\<exists> b1 b2. p (b1, b2)")
  apply (auto)
done

subsection {* Converse laws *}

lemma convr_invol [simp]: "p\<^sup>-\<^sup>- = p"
  by pred_tac

lemma lit_convr [simp]: "\<guillemotleft>v\<guillemotright>\<^sup>- = \<guillemotleft>v\<guillemotright>"
  by pred_tac

lemma uivar_convr [simp]: 
  fixes x :: "('a, '\<alpha>) uvar"
  shows "($x)\<^sup>- = $x\<acute>"
  by pred_tac

lemma uovar_convr [simp]: 
  fixes x :: "('a, '\<alpha>) uvar"
  shows "($x\<acute>)\<^sup>- = $x"
  by pred_tac

lemma uop_convr [simp]: "(uop f u)\<^sup>- = uop f (u\<^sup>-)"
  by (pred_tac)

lemma bop_convr [simp]: "(bop f u v)\<^sup>- = bop f (u\<^sup>-) (v\<^sup>-)"
  by (pred_tac)

lemma eq_convr [simp]: "(p =\<^sub>u q)\<^sup>- = (p\<^sup>- =\<^sub>u q\<^sup>-)"
  by (pred_tac)

lemma not_convr [simp]: "(\<not> p)\<^sup>- = (\<not> p\<^sup>-)"
  by (pred_tac)

lemma disj_convr [simp]: "(p \<or> q)\<^sup>- = (q\<^sup>- \<or> p\<^sup>-)"
  by (pred_tac)

lemma conj_convr [simp]: "(p \<and> q)\<^sup>- = (q\<^sup>- \<and> p\<^sup>-)"
  by (pred_tac)

lemma seqr_convr [simp]: "(p ;; q)\<^sup>- = (q\<^sup>- ;; p\<^sup>-)"
  by rel_tac

lemma pre_convr [simp]: "\<lceil>p\<rceil>\<^sub><\<^sup>- = \<lceil>p\<rceil>\<^sub>>"
  by (rel_tac)

lemma post_convr [simp]: "\<lceil>p\<rceil>\<^sub>>\<^sup>- = \<lceil>p\<rceil>\<^sub><"
  by (rel_tac)

theorem seqr_pre_transfer: "in\<alpha> \<sharp> q \<Longrightarrow> ((P \<and> q) ;; R) = (P ;; (q\<^sup>- \<and> R))"
  by (rel_tac)

theorem seqr_post_out: "in\<alpha> \<sharp> r \<Longrightarrow> (P ;; (Q \<and> r)) = ((P ;; Q) \<and> r)"
  by (rel_tac, blast+)

lemma seqr_post_var_out: 
  fixes x :: "(bool, '\<alpha>) uvar"
  shows "(P ;; (Q \<and> $x\<acute>)) = ((P ;; Q) \<and> $x\<acute>)"
  by (rel_tac)

theorem seqr_post_transfer: "out\<alpha> \<sharp> q \<Longrightarrow> (P ;; (q \<and> R)) = (P \<and> q\<^sup>- ;; R)"
  by (simp add: seqr_pre_transfer unrest_convr_in\<alpha>)

lemma seqr_pre_out: "out\<alpha> \<sharp> p \<Longrightarrow> ((p \<and> Q) ;; R) = (p \<and> (Q ;; R))"
  by (rel_tac, blast+)

lemma seqr_pre_var_out: 
  fixes x :: "(bool, '\<alpha>) uvar"
  shows "(($x \<and> P) ;; Q) = ($x \<and> (P ;; Q))"
  by (rel_tac)

lemma seqr_true_lemma: 
  "(P = (\<not> (\<not> P ;; true))) = (P = (P ;; true))"
  by rel_tac

lemma shEx_lift_seq_1 [uquant_lift]: 
  "((\<^bold>\<exists> x \<bullet> P x) ;; Q) = (\<^bold>\<exists> x \<bullet> (P x ;; Q))"
  by pred_tac

lemma shEx_lift_seq_2 [uquant_lift]: 
  "(P ;; (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P ;; Q x))"
  by pred_tac

text {* Frame and antiframe *}

definition frame :: "('a, '\<alpha>) lens \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" where
[urel_defs]: "frame x P = (II\<^bsub>x\<^esub> \<and> P)"

definition antiframe :: "('a, '\<alpha>) lens \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" where
[urel_defs]: "antiframe x P = (II\<restriction>\<^sub>\<alpha>x \<and> P)"

syntax
  "_frame"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:\<lbrakk>_\<rbrakk>" [64,0] 80)
  "_antiframe" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [64,0] 80)

translations
  "_frame x P" == "CONST frame x P"
  "_antiframe x P" == "CONST antiframe x P"

lemma frame_disj: "(x:\<lbrakk>P\<rbrakk> \<or> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<or> Q\<rbrakk>"
  by (rel_tac)

lemma frame_conj: "(x:\<lbrakk>P\<rbrakk> \<and> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<and> Q\<rbrakk>"
  by (rel_tac)

lemma frame_seq:
  "\<lbrakk> uvar x; $x\<acute> \<sharp> P; $x \<sharp> Q \<rbrakk>  \<Longrightarrow> (x:\<lbrakk>P\<rbrakk> ;; x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P ;; Q\<rbrakk>"
  by (rel_tac, metis vwb_lens_def wb_lens_weak weak_lens.put_get)

lemma antiframe_to_frame:
  "\<lbrakk> x \<bowtie> y; x +\<^sub>L y = 1\<^sub>L \<rbrakk> \<Longrightarrow> x:[P] = y:\<lbrakk>P\<rbrakk>"
  by (rel_tac, metis lens_indep_def, metis lens_indep_def surj_pair)

text {* While loop laws *}

lemma while_cond_true:
  "((while b do P od) \<and> \<lceil>b\<rceil>\<^sub><) = ((P \<and> \<lceil>b\<rceil>\<^sub><) ;; while b do P od)"
proof -
  have "(while b do P od \<and> \<lceil>b\<rceil>\<^sub><) = (((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u \<and> (\<not> \<lceil>b\<rceil>\<^sub>>)) \<and> \<lceil>b\<rceil>\<^sub><)"
    by (simp add: while_def)
  also have "... = (((II \<or> ((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; (\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u)) \<and> \<not> \<lceil>b\<rceil>\<^sub>>) \<and> \<lceil>b\<rceil>\<^sub><)"
    by (simp add: disj_upred_def)
  also have "... = ((\<lceil>b\<rceil>\<^sub>< \<and> (II \<or> ((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; (\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u))) \<and> (\<not> \<lceil>b\<rceil>\<^sub>>))"
    by (simp add: conj_comm utp_pred.inf.left_commute)
  also have "... = (((\<lceil>b\<rceil>\<^sub>< \<and> II) \<or> (\<lceil>b\<rceil>\<^sub>< \<and> ((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; (\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u))) \<and> (\<not> \<lceil>b\<rceil>\<^sub>>))"
    by (simp add: conj_disj_distr)
  also have "... = ((((\<lceil>b\<rceil>\<^sub>< \<and> II) \<or> ((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; (\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u))) \<and> (\<not> \<lceil>b\<rceil>\<^sub>>))"
    by (subst seqr_pre_out[THEN sym], simp add: unrest, rel_tac)
  also have "... = ((((II \<and> \<lceil>b\<rceil>\<^sub>>) \<or> ((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; (\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u))) \<and> (\<not> \<lceil>b\<rceil>\<^sub>>))"
    by (simp add: pre_skip_post)
  also have "... = ((II \<and> \<lceil>b\<rceil>\<^sub>> \<and> \<not> \<lceil>b\<rceil>\<^sub>>) \<or> (((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; ((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u)) \<and> (\<not> \<lceil>b\<rceil>\<^sub>>)))"
    by (simp add: utp_pred.inf.assoc utp_pred.inf_sup_distrib2)
  also have "... = (((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; ((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u)) \<and> (\<not> \<lceil>b\<rceil>\<^sub>>))"
    by simp
  also have "... = ((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; (((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u) \<and> (\<not> \<lceil>b\<rceil>\<^sub>>)))"
    by (simp add: seqr_post_out unrest)
  also have "... = ((P \<and> \<lceil>b\<rceil>\<^sub><) ;; while b do P od)"
    by (simp add: utp_pred.inf_commute while_def)
  finally show ?thesis .
qed

lemma while_cond_false:
  "((while b do P od) \<and> (\<not> \<lceil>b\<rceil>\<^sub><)) = (II \<and> \<not> \<lceil>b\<rceil>\<^sub><)"
proof -
  have "(while b do P od \<and> (\<not> \<lceil>b\<rceil>\<^sub><)) = (((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u \<and> (\<not> \<lceil>b\<rceil>\<^sub>>)) \<and> (\<not> \<lceil>b\<rceil>\<^sub><))"
    by (simp add: while_def)
  also have "... = (((II \<or> ((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; (\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u)) \<and> \<not> \<lceil>b\<rceil>\<^sub>>) \<and> (\<not> \<lceil>b\<rceil>\<^sub><))"
    by (simp add: disj_upred_def)
  also have "... = (((II \<and> \<not> \<lceil>b\<rceil>\<^sub>>) \<and> \<not> \<lceil>b\<rceil>\<^sub><) \<or> ((\<not> \<lceil>b\<rceil>\<^sub><) \<and> (((\<lceil>b\<rceil>\<^sub>< \<and> P) ;; ((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u)) \<and> \<not> \<lceil>b\<rceil>\<^sub>>)))"
    by (simp add: conj_disj_distr utp_pred.inf.commute)
  also have "... = (((II \<and> \<not> \<lceil>b\<rceil>\<^sub>>) \<and> \<not> \<lceil>b\<rceil>\<^sub><) \<or> ((((\<not> \<lceil>b\<rceil>\<^sub><) \<and> (\<lceil>b\<rceil>\<^sub>< \<and> P) ;; ((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u)) \<and> \<not> \<lceil>b\<rceil>\<^sub>>)))"
    by (simp add: seqr_pre_out unrest_not unrest_pre_out\<alpha> utp_pred.inf.assoc)
  also have "... = (((II \<and> \<not> \<lceil>b\<rceil>\<^sub>>) \<and> \<not> \<lceil>b\<rceil>\<^sub><) \<or> (((false ;; ((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u)) \<and> \<not> \<lceil>b\<rceil>\<^sub>>)))"
    by (simp add: conj_comm utp_pred.inf.left_commute)
  also have "... = ((II \<and> \<not> \<lceil>b\<rceil>\<^sub>>) \<and> \<not> \<lceil>b\<rceil>\<^sub><)"
    by simp
  also have "... = (II \<and> \<not> \<lceil>b\<rceil>\<^sub><)"
    by rel_tac
  finally show ?thesis .
qed
    
theorem while_unfold:
  "while b do P od = ((P ;; while b do P od) \<triangleleft> b \<triangleright>\<^sub>r II)"
  by (metis (no_types, hide_lams) bounded_semilattice_sup_bot_class.sup_bot.left_neutral comp_cond_left_distr cond_def cond_idem disj_comm disj_upred_def seqr_right_zero upred_quantale.bot_zerol utp_pred.inf_bot_right utp_pred.inf_commute while_cond_false while_cond_true)

subsection {* Relational unrestriction *}

text {* Relational unrestriction states that a variable is unchanged by a relation. Eventually
  I'd also like to have it state that the relation also does not depend on the variable's
  initial value, but I'm not sure how to state that yet. For now we represent this by
  the parametric healthiness condition RID. *}

definition RID :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" 
where "RID x P = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x)"

declare RID_def [urel_defs]

lemma RID_idem:
  "semi_uvar x \<Longrightarrow> RID(x)(RID(x)(P)) = RID(x)(P)"
  by rel_tac

lemma RID_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RID(x)(P) \<sqsubseteq> RID(x)(Q)"
  by rel_tac

lemma RID_skip_r:
  "uvar x \<Longrightarrow> RID(x)(II) = II"
  apply rel_tac
using vwb_lens.put_eq apply fastforce
by auto

lemma RID_disj:
  "RID(x)(P \<or> Q) = (RID(x)(P) \<or> RID(x)(Q))"
  by rel_tac

lemma RID_conj:
  "uvar x \<Longrightarrow> RID(x)(RID(x)(P) \<and> RID(x)(Q)) = (RID(x)(P) \<and> RID(x)(Q))"
  by rel_tac

lemma RID_assigns_r_diff:
  "\<lbrakk> uvar x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> RID(x)(\<langle>\<sigma>\<rangle>\<^sub>a) = \<langle>\<sigma>\<rangle>\<^sub>a"
  apply (rel_tac)
  apply (auto simp add: unrest_usubst_def)
  apply (metis vwb_lens.put_eq)
  apply (metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)
done

lemma RID_assign_r_same:
  "uvar x \<Longrightarrow> RID(x)(x := v) = II"
  apply (rel_tac)
  using vwb_lens.put_eq apply fastforce
  apply blast
done

lemma RID_seq_left:
  assumes "uvar x"
  shows "RID(x)(RID(x)(P) ;; Q) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(RID(x)(P) ;; Q) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x ;; Q) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> (\<exists> $x \<bullet> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_tac)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_tac)
    apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_tac, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_tac, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by rel_tac
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by rel_tac
  finally show ?thesis .
qed

lemma RID_seq_right:
  assumes "uvar x"
  shows "RID(x)(P ;; RID(x)(Q)) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(P ;; RID(x)(Q)) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = (((\<exists> $x \<bullet>  P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> (\<exists> $x\<acute> \<bullet> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_tac)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_tac)
    apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_tac, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_tac, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by rel_tac
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by rel_tac
  finally show ?thesis .
qed

definition unrest_relation :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrelation \<Rightarrow> bool" (infix "\<sharp>\<sharp>" 20)
where "(x \<sharp>\<sharp> P) \<longleftrightarrow> (P = RID(x)(P))"

declare unrest_relation_def [urel_defs]

lemma skip_r_runrest [unrest]:
  "uvar x \<Longrightarrow> x \<sharp>\<sharp> II"
  by (simp add: RID_skip_r unrest_relation_def)

lemma assigns_r_runrest:
  "\<lbrakk> uvar x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: RID_assigns_r_diff unrest_relation_def)
 
lemma seq_r_runrest [unrest]:
  assumes "uvar x" "x \<sharp>\<sharp> P" "x \<sharp>\<sharp> Q"
  shows "x \<sharp>\<sharp> (P ;; Q)"
  by (metis RID_seq_left assms unrest_relation_def)

lemma false_runrest [unrest]: "x \<sharp>\<sharp> false"
  by (rel_tac)

lemma and_runrest [unrest]: "\<lbrakk> uvar x; x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<and> Q)"
  by (metis RID_conj unrest_relation_def)

lemma or_runrest [unrest]: "\<lbrakk> x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<or> Q)"
  by (simp add: RID_disj unrest_relation_def)

subsection {* Alphabet laws *}

lemma aext_cond [alpha]: 
  "(P \<triangleleft> b \<triangleright> Q) \<oplus>\<^sub>p a = ((P \<oplus>\<^sub>p a) \<triangleleft> (b \<oplus>\<^sub>p a) \<triangleright> (Q \<oplus>\<^sub>p a))"
  by rel_tac

lemma aext_seq [alpha]:
  "wb_lens a \<Longrightarrow> ((P ;; Q) \<oplus>\<^sub>p (a \<times>\<^sub>L a)) = ((P \<oplus>\<^sub>p (a \<times>\<^sub>L a)) ;; (Q \<oplus>\<^sub>p (a \<times>\<^sub>L a)))"
  by (rel_tac, metis wb_lens_weak weak_lens.put_get)

subsection {* Relation algebra laws *}

theorem RA1: "(P ;; (Q ;; R)) = ((P ;; Q) ;; R)"
  using seqr_assoc by auto

theorem RA2: "(P ;; II) = P" "(II ;; P) = P"
  by simp_all

theorem RA3: "P\<^sup>-\<^sup>- = P"
  by simp

theorem RA4: "(P ;; Q)\<^sup>- = (Q\<^sup>- ;; P\<^sup>-)"
  by simp

theorem RA5: "(P \<or> Q)\<^sup>- = (P\<^sup>- \<or> Q\<^sup>-)"
  by rel_tac

theorem RA6: "((P \<or> Q) ;; R) = ((P;;R) \<or> (Q;;R))"
  using seqr_or_distl by blast

theorem RA7: "((P\<^sup>- ;; (\<not>(P ;; Q))) \<or> (\<not>Q)) = (\<not>Q)"
  by (rel_tac)

subsection {* Relational alphabet extension *}

lift_definition rel_alpha_ext :: "'\<beta> hrelation \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrelation" (infix "\<oplus>\<^sub>R" 65)
is "\<lambda> P x (b1, b2). P (get\<^bsub>x\<^esub> b1, get\<^bsub>x\<^esub> b2) \<and> (\<forall> b. b1 \<oplus>\<^sub>L b on x = b2 \<oplus>\<^sub>L b on x)" .

lemma rel_alpha_ext_alt_def:
  assumes "uvar y" "x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L" "x \<bowtie> y"
  shows "P \<oplus>\<^sub>R x = (P \<oplus>\<^sub>p (x \<times>\<^sub>L x) \<and> $y\<acute> =\<^sub>u $y)"
  using assms
  apply (rel_tac, simp_all add: lens_override_def)
  apply (metis lens_indep_get lens_indep_sym)
  apply (metis vwb_lens_def wb_lens.get_put wb_lens_def weak_lens.put_get)
done

subsection {* Program values *}
  
abbreviation prog_val :: "'\<alpha> hrelation \<Rightarrow> ('\<alpha> hrelation, '\<alpha>) uexpr" ("\<lbrace>_\<rbrace>\<^sub>u")
where "\<lbrace>P\<rbrace>\<^sub>u \<equiv> \<guillemotleft>P\<guillemotright>"

lift_definition call :: "('\<alpha> hrelation, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrelation"
is "\<lambda> P b. P (fst b) b" .

lemma call_prog_val: "call \<lbrace>P\<rbrace>\<^sub>u = P"
  by (simp add: call_def urel_defs lit.rep_eq Rep_uexpr_inverse)

end