section {* Alphabetised relations *}

theory utp_rel
imports
  utp_pred
  utp_lift
  utp_tactics
begin

default_sort type

consts
  useq   :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 51)
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

lemma out_alpha_in_indep [simp]:
  "out\<alpha> \<bowtie> in_var x" "in_var x \<bowtie> out\<alpha>"
  by (simp_all add: in_var_def out\<alpha>_def lens_indep_def fst_lens_def lens_comp_def)

lemma in_alpha_out_indep [simp]:
  "in\<alpha> \<bowtie> out_var x" "out_var x \<bowtie> in\<alpha>"
  by (simp_all add: in_var_def in\<alpha>_def lens_indep_def fst_lens_def lens_comp_def)

text {* The alphabet of a relation consists of the input and output portions *}

lemma alpha_in_out:
  "\<Sigma> \<approx>\<^sub>L in\<alpha> +\<^sub>L out\<alpha>"
  by (metis fst_lens_def fst_snd_id_lens in\<alpha>_def lens_equiv_refl out\<alpha>_def snd_lens_def)

type_synonym '\<alpha> cond      = "'\<alpha> upred"
type_synonym ('\<alpha>, '\<beta>) rel = "('\<alpha> \<times> '\<beta>) upred"
type_synonym '\<alpha> hrel      = "('\<alpha> \<times> '\<alpha>) upred"

translations
  (type) "('\<alpha>, '\<beta>) rel" <= (type) "('\<alpha> \<times> '\<beta>) upred"

definition cond::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred"
                                                          ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)
where "(P \<triangleleft> b \<triangleright> Q) \<equiv> (b \<and> P) \<or> ((\<not> b) \<and> Q)"

abbreviation rcond::"('\<alpha>,  '\<beta>) rel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>,  '\<beta>) rel \<Rightarrow> ('\<alpha>,  '\<beta>) rel"
                                                          ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r/ _)" [52,0,53] 52)
where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>< \<triangleright> Q)"

lift_definition seqr::"(('\<alpha> \<times> '\<beta>) upred) \<Rightarrow> (('\<beta> \<times> '\<gamma>) upred) \<Rightarrow> ('\<alpha> \<times> '\<gamma>) upred"
is "\<lambda> P Q r. r \<in> ({p. P p} O {q. Q q})" .

lift_definition conv_r :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta> \<times> '\<alpha>) uexpr" ("_\<^sup>-" [999] 999)
is "\<lambda> e (b1, b2). e (b2, b1)" .

definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>'\<alpha> hrel" where
[urel_defs]: "skip_ra v = ($v\<acute> =\<^sub>u $v)"

syntax
  "_skip_ra" :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")

translations
  "_skip_ra v" == "CONST skip_ra v"

abbreviation usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> \<sigma> \<oplus>\<^sub>s in\<alpha>"

abbreviation usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) usubst \<Rightarrow> '\<alpha> usubst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s \<equiv> \<sigma> \<restriction>\<^sub>s in\<alpha>"

definition assigns_ra :: "'\<alpha> usubst \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^bsub>_\<^esub>") where
"\<langle>\<sigma>\<rangle>\<^bsub>a\<^esub> = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II\<^bsub>a\<^esub>)"

lift_definition assigns_r :: "'\<alpha> usubst \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^sub>a")
  is "\<lambda> \<sigma> (A, A'). A' = \<sigma>(A)" .

definition skip_r :: "'\<alpha> hrel" where
"skip_r = assigns_r id"

abbreviation assign_r :: "('t, '\<alpha>) uvar \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
where "assign_r x v \<equiv> assigns_r [x \<mapsto>\<^sub>s v]"

abbreviation assign_2_r ::
  "('t1, '\<alpha>) uvar \<Rightarrow> ('t2, '\<alpha>) uvar \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
where "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

nonterminal
  svid_list and uexpr_list

syntax
  "_svid_unit"  :: "svid \<Rightarrow> svid_list" ("_")
  "_svid_list"  :: "svid \<Rightarrow> svid_list \<Rightarrow> svid_list" ("_,/ _")
  "_uexpr_unit" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list" ("_" [40] 40)
  "_uexpr_list" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list \<Rightarrow> uexpr_list" ("_,/ _" [40,40] 40)
  "_assignment" :: "svid_list \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  (infixr ":=" 62)
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

definition rassume :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sup>\<top>" [999] 999) where
[urel_defs]: "rassume c = II \<triangleleft> c \<triangleright>\<^sub>r false"

definition rassert :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("_\<^sub>\<bottom>" [999] 999) where
[urel_defs]: "rassert c = II \<triangleleft> c \<triangleright>\<^sub>r true"

text {* We describe some properties of relations *}

definition ufunctional :: "('a, 'b) rel \<Rightarrow> bool"
where "ufunctional R \<longleftrightarrow> II \<sqsubseteq> R\<^sup>- ;; R"

declare ufunctional_def [urel_defs]

definition uinj :: "('a, 'b) rel \<Rightarrow> bool"
where "uinj R \<longleftrightarrow> II \<sqsubseteq> R ;; R\<^sup>-"

declare uinj_def [urel_defs]

text {* A test is like a precondition, except that it identifies to the postcondition. It
        forms the basis for Kleene Algebra with Tests (KAT). *}

definition lift_test :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel" ("\<lceil>_\<rceil>\<^sub>t")
where "\<lceil>b\<rceil>\<^sub>t = (\<lceil>b\<rceil>\<^sub>< \<and> II)"

declare cond_def [urel_defs]
declare skip_r_def [urel_defs]

text {* We implement a poor man's version of alphabet restriction that hides a variable within a relation *}

definition rel_var_res :: "'\<alpha> hrel \<Rightarrow> ('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrel" (infix "\<restriction>\<^sub>\<alpha>" 80) where
"P \<restriction>\<^sub>\<alpha> x = (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P)"

declare rel_var_res_def [urel_defs]

-- {* Configuration for UTP tactics (see @{theory utp_tactics}). *}

update_uexpr_rep_eq_thms -- {* Reread @{text rep_eq} theorems. *}

subsection {* Unrestriction Laws *}

lemma unrest_iuvar [unrest]: "mwb_lens x \<Longrightarrow> out\<alpha> \<sharp> $x"
  by (simp add: out\<alpha>_def, transfer, auto)

lemma unrest_ouvar [unrest]: "mwb_lens x \<Longrightarrow> in\<alpha> \<sharp> $x\<acute>"
  by (simp add: in\<alpha>_def, transfer, auto)

lemma unrest_semir_undash [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "$x \<sharp> P"
  shows "$x \<sharp> P ;; Q"
  using assms by (rel_auto)

lemma unrest_semir_dash [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "$x\<acute> \<sharp> Q"
  shows "$x\<acute> \<sharp> P ;; Q"
  using assms by (rel_auto)

lemma unrest_cond [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> b; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<triangleleft> b \<triangleright> Q"
  by (rel_auto)

lemma unrest_in\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; in\<alpha> \<sharp> (P :: ('\<alpha>, '\<beta>) rel) \<rbrakk> \<Longrightarrow> $x \<sharp> P"
  by (pred_auto, simp add: in\<alpha>_def, blast, metis in\<alpha>_def lens.select_convs(2) old.prod.case)

lemma unrest_out\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; out\<alpha> \<sharp> (P :: ('\<alpha>, '\<beta>) rel) \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P"
  by (pred_auto, simp add: out\<alpha>_def, blast, metis lens.select_convs(2) old.prod.case out\<alpha>_def)

lemma in\<alpha>_uvar [simp]: "vwb_lens in\<alpha>"
  by (unfold_locales, auto simp add: in\<alpha>_def)

lemma out\<alpha>_uvar [simp]: "vwb_lens out\<alpha>"
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
  "vwb_lens x \<Longrightarrow> $x \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

lemma unrest_out_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

subsection {* Substitution laws *}

lemma subst_seq_left [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = (\<sigma> \<dagger> P) ;; Q"
  by (rel_simp, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

lemma subst_seq_right [usubst]:
  "in\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = P ;; (\<sigma> \<dagger> Q)"
  by (rel_simp, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

text {* The following laws support substitution in heterogeneous relations for polymorphically
  types literal expressions. These cannot be supported more generically due to limitations
  in HOL's type system. The laws are presented in a slightly strange way so as to be as
  general as possible. *}

lemma bool_seqr_laws [usubst]:
  fixes x :: "(bool \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>true/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>false/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s true) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>true/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s false) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>false/$x\<acute>\<rbrakk>)"
    by (rel_auto)+

lemma zero_one_seqr_laws [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 0) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>0/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s 1) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>1/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 0) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>0/$x\<acute>\<rbrakk>)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s 1) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>1/$x\<acute>\<rbrakk>)"
    by (rel_auto)+

lemma numeral_seqr_laws [usubst]:
  fixes x :: "(_ \<Longrightarrow> '\<alpha>)"
  shows
    "\<And> P Q \<sigma>. \<sigma>($x \<mapsto>\<^sub>s numeral n) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P\<lbrakk>numeral n/$x\<rbrakk> ;; Q)"
    "\<And> P Q \<sigma>. \<sigma>($x\<acute> \<mapsto>\<^sub>s numeral n) \<dagger> (P ;; Q) = \<sigma> \<dagger> (P ;; Q\<lbrakk>numeral n/$x\<acute>\<rbrakk>)"
  by (rel_auto)+

lemma usubst_condr [usubst]:
  "\<sigma> \<dagger> (P \<triangleleft> b \<triangleright> Q) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> b \<triangleright> \<sigma> \<dagger> Q)"
  by (rel_auto)

lemma subst_skip_r [usubst]:
  "out\<alpha> \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> II = \<langle>\<lfloor>\<sigma>\<rfloor>\<^sub>s\<rangle>\<^sub>a"
  by (rel_simp, (metis (mono_tags, lifting) prod.sel(1) sndI surjective_pairing)+)

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

lemma subst_drop_upd [usubst]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "\<lfloor>\<sigma>($x \<mapsto>\<^sub>s v)\<rfloor>\<^sub>s = \<lfloor>\<sigma>\<rfloor>\<^sub>s(x \<mapsto>\<^sub>s \<lfloor>v\<rfloor>\<^sub><)"
  by (pred_simp, simp add: in\<alpha>_def prod.case_eq_if)

lemma subst_lift_pre [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>b\<rceil>\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub><"
  by (metis apply_subst_ext fst_lens_def fst_vwb_lens in\<alpha>_def)

lemma unrest_usubst_lift_in [unrest]:
  "x \<sharp> P \<Longrightarrow> $x \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by (pred_simp, auto simp add: unrest_usubst_def in\<alpha>_def)

lemma unrest_usubst_lift_out [unrest]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "$x\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by (pred_simp, auto simp add: unrest_usubst_def in\<alpha>_def)

subsection {* Relation laws *}

text {* Homogeneous relations form a quantale. This allows us to import a large number of laws
        from Struth and Armstrong's Kleene Algebra theory~\cite{Armstrong2015}. *}

abbreviation truer :: "'\<alpha> hrel" ("true\<^sub>h") where
"truer \<equiv> true"

abbreviation falser :: "'\<alpha> hrel" ("false\<^sub>h") where
"falser \<equiv> false"

lemma drop_pre_inv [simp]: "\<lbrakk> out\<alpha> \<sharp> p \<rbrakk> \<Longrightarrow> \<lceil>\<lfloor>p\<rfloor>\<^sub><\<rceil>\<^sub>< = p"
  by (pred_simp, auto simp add: out\<alpha>_def lens_create_def fst_lens_def prod.case_eq_if)

definition while :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ do _ od") where
"while b do P od = (\<nu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

declare while_def [urel_defs]

text {* While loops with invariant decoration *}

definition while_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ invr _ do _ od") where
"while b invr p do S od = while b do S od"

lemma cond_idem:"(P \<triangleleft> b \<triangleright> P) = P" by (rel_auto)

lemma cond_symm:"(P \<triangleleft> b \<triangleright> Q) = (Q \<triangleleft> \<not> b \<triangleright> P)" by (rel_auto)

lemma cond_assoc: "((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> R) = (P \<triangleleft> b \<and> c \<triangleright> (Q \<triangleleft> c \<triangleright> R))" by (rel_auto)

lemma cond_distr: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> c \<triangleright> R)) = ((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> (P \<triangleleft> b \<triangleright> R))" by (rel_auto)

lemma cond_unit_T [simp]:"(P \<triangleleft> true \<triangleright> Q) = P" by (rel_auto)

lemma cond_unit_F [simp]:"(P \<triangleleft> false \<triangleright> Q) = Q" by (rel_auto)

lemma cond_and_T_integrate:
  "((P \<and> b) \<or> (Q \<triangleleft> b \<triangleright> R)) = ((P \<or> Q) \<triangleleft> b \<triangleright> R)"
  by (rel_auto)

lemma cond_L6: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)" by (rel_auto)

lemma cond_L7: "(P \<triangleleft> b \<triangleright> (P \<triangleleft> c \<triangleright> Q)) = (P \<triangleleft> b \<or> c \<triangleright> Q)" by (rel_auto)

lemma cond_and_distr: "((P \<and> Q) \<triangleleft> b \<triangleright> (R \<and> S)) = ((P \<triangleleft> b \<triangleright> R) \<and> (Q \<triangleleft> b \<triangleright> S))" by (rel_auto)

lemma cond_or_distr: "((P \<or> Q) \<triangleleft> b \<triangleright> (R \<or> S)) = ((P \<triangleleft> b \<triangleright> R) \<or> (Q \<triangleleft> b \<triangleright> S))" by (rel_auto)

lemma cond_imp_distr:
"((P \<Rightarrow> Q) \<triangleleft> b \<triangleright> (R \<Rightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Rightarrow> (Q \<triangleleft> b \<triangleright> S))" by (rel_auto)

lemma cond_eq_distr:
"((P \<Leftrightarrow> Q) \<triangleleft> b \<triangleright> (R \<Leftrightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Leftrightarrow> (Q \<triangleleft> b \<triangleright> S))" by (rel_auto)

lemma cond_conj_distr:"(P \<and> (Q \<triangleleft> b \<triangleright> S)) = ((P \<and> Q) \<triangleleft> b \<triangleright> (P \<and> S))" by (rel_auto)

lemma cond_disj_distr:"(P \<or> (Q \<triangleleft> b \<triangleright> S)) = ((P \<or> Q) \<triangleleft> b \<triangleright> (P \<or> S))" by (rel_auto)

lemma cond_neg: "\<not> (P \<triangleleft> b \<triangleright> Q) = ((\<not> P) \<triangleleft> b \<triangleright> (\<not> Q))" by (rel_auto)

lemma cond_USUP_dist: "(\<Squnion> P\<in>S \<bullet> F(P)) \<triangleleft> b \<triangleright> (\<Squnion> P\<in>S \<bullet> G(P)) = (\<Squnion> P\<in>S \<bullet> F(P) \<triangleleft> b \<triangleright> G(P))"
  by (subst uexpr_eq_iff, auto simp add: disj_upred_def conj_upred_def not_upred_def cond_def UINF.rep_eq uminus_uexpr_def inf_uexpr.rep_eq sup_uexpr.rep_eq uop.rep_eq bop.rep_eq lit.rep_eq)

lemma cond_UINF_dist: "(\<Sqinter> P\<in>S \<bullet> F(P)) \<triangleleft> b \<triangleright> (\<Sqinter> P\<in>S \<bullet> G(P)) = (\<Sqinter> P\<in>S \<bullet> F(P) \<triangleleft> b \<triangleright> G(P))"
  by (subst uexpr_eq_iff, auto simp add: disj_upred_def conj_upred_def not_upred_def cond_def USUP.rep_eq uminus_uexpr_def inf_uexpr.rep_eq sup_uexpr.rep_eq uop.rep_eq bop.rep_eq lit.rep_eq)

lemma cond_conj: "P \<triangleleft> b \<and> c \<triangleright> Q = (P \<triangleleft> c \<triangleright> Q) \<triangleleft> b \<triangleright> Q"
  by (rel_auto)

lemma comp_cond_left_distr:
  "((P \<triangleleft> b \<triangleright>\<^sub>r Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright>\<^sub>r (Q ;; R))"
  by (rel_auto)

lemma cond_var_subst_left:
  assumes "vwb_lens x"
  shows "(P\<lbrakk>true/x\<rbrakk> \<triangleleft> var x \<triangleright> Q) = (P \<triangleleft> var x \<triangleright> Q)"
  using assms by (metis cond_def conj_comm conj_var_subst upred_eq_true)

lemma cond_var_subst_right:
  assumes "vwb_lens x"
  shows "(P \<triangleleft> var x \<triangleright> Q\<lbrakk>false/x\<rbrakk>) = (P \<triangleleft> var x \<triangleright> Q)"
  using assms by (metis cond_def conj_var_subst upred_eq_false utp_pred.inf_commute)

lemma cond_var_split:
  "vwb_lens x \<Longrightarrow> (P\<lbrakk>true/x\<rbrakk> \<triangleleft> var x \<triangleright> P\<lbrakk>false/x\<rbrakk>) = P"
  by (rel_simp, (metis (full_types) vwb_lens.put_eq)+)

lemma cond_seq_left_distr:
  "out\<alpha> \<sharp> b \<Longrightarrow> ((P \<triangleleft> b \<triangleright> Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright> (Q ;; R))"
  by (rel_auto)

lemma cond_seq_right_distr:
  "in\<alpha> \<sharp> b \<Longrightarrow> (P ;; (Q \<triangleleft> b \<triangleright> R)) = ((P ;; Q) \<triangleleft> b \<triangleright> (P ;; R))"
  by (rel_auto)

lemma seqr_assoc: "P ;; (Q ;; R) = (P ;; Q) ;; R"
  by (rel_auto)

lemma seqr_left_unit [simp]:
  "II ;; P = P"
  by (rel_auto)

lemma seqr_right_unit [simp]:
  "P ;; II = P"
  by (rel_auto)

lemma seqr_left_zero [simp]:
  "false ;; P = false"
  by pred_auto

lemma seqr_right_zero [simp]:
  "P ;; false = false"
  by pred_auto

text {* Quantale laws for relations *}

lemma seq_Sup_distl: "P ;; (\<Sqinter> A) = (\<Sqinter> Q\<in>A. P ;; Q)"
  by (transfer, auto)

lemma seq_Sup_distr: "(\<Sqinter> A) ;; Q = (\<Sqinter> P\<in>A. P ;; Q)"
  by (transfer, auto)

lemma seq_UINF_distl: "P ;; (\<Sqinter> Q\<in>A \<bullet> F(Q)) = (\<Sqinter> Q\<in>A \<bullet> P ;; F(Q))"
  by (simp add: USUP_as_Sup_collect seq_Sup_distl)

lemma seq_UINF_distr: "(\<Sqinter> P\<in>A \<bullet> F(P)) ;; Q = (\<Sqinter> P\<in>A \<bullet> F(P) ;; Q)"
  by (simp add: USUP_as_Sup_collect seq_Sup_distr)

lemma impl_seqr_mono: "\<lbrakk> `P \<Rightarrow> Q`; `R \<Rightarrow> S` \<rbrakk> \<Longrightarrow> `(P ;; R) \<Rightarrow> (Q ;; S)`"
  by (pred_blast)

lemma seqr_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 ;; Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 ;; Q\<^sub>2)"
  by (rel_blast)

lemma seqr_monotonic:
  "\<lbrakk> mono P; mono Q \<rbrakk> \<Longrightarrow> mono (\<lambda> X. P X ;; Q X)"
  by (simp add: mono_def, rel_blast)

lemma cond_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<triangleleft> b \<triangleright> Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 \<triangleleft> b \<triangleright> Q\<^sub>2)"
  by (rel_auto)

lemma cond_monotonic:
  "\<lbrakk> mono P; mono Q \<rbrakk> \<Longrightarrow> mono (\<lambda> X. P X \<triangleleft> b \<triangleright> Q X)"
  by (simp add: mono_def, rel_blast)

lemma spec_refine:
  "Q \<sqsubseteq> (P \<and> R) \<Longrightarrow> (P \<Rightarrow> Q) \<sqsubseteq> R"
  by (rel_auto)

lemma cond_skip: "out\<alpha> \<sharp> b \<Longrightarrow> (b \<and> II) = (II \<and> b\<^sup>-)"
  by (rel_auto)

lemma pre_skip_post: "(\<lceil>b\<rceil>\<^sub>< \<and> II) = (II \<and> \<lceil>b\<rceil>\<^sub>>)"
  by (rel_auto)

lemma skip_var:
  fixes x :: "(bool, '\<alpha>) uvar"
  shows "($x \<and> II) = (II \<and> $x\<acute>)"
  by (rel_auto)

lemma seqr_exists_left:
  "mwb_lens x \<Longrightarrow> ((\<exists> $x \<bullet> P) ;; Q) = (\<exists> $x \<bullet> (P ;; Q))"
  by (rel_auto)

lemma seqr_exists_right:
  "mwb_lens x \<Longrightarrow> (P ;; (\<exists> $x\<acute> \<bullet> Q)) = (\<exists> $x\<acute> \<bullet> (P ;; Q))"
  by (rel_auto)

lemma assigns_subst [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<langle>\<rho>\<rangle>\<^sub>a = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a"
  by (rel_auto)

lemma assigns_r_comp: "(\<langle>\<sigma>\<rangle>\<^sub>a ;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P)"
  by (rel_auto)

lemma assigns_r_feasible:
  "(\<langle>\<sigma>\<rangle>\<^sub>a ;; true) = true"
  by (rel_auto)

lemma assign_subst [usubst]:
  "\<lbrakk> mwb_lens x; mwb_lens y \<rbrakk> \<Longrightarrow> [$x \<mapsto>\<^sub>s \<lceil>u\<rceil>\<^sub><] \<dagger> (y := v) = (x, y := u, [x \<mapsto>\<^sub>s u] \<dagger> v)"
  by (rel_auto)

lemma assigns_idem: "mwb_lens x \<Longrightarrow> (x,x := u,v) = (x := v)"
  by (simp add: usubst)

lemma assigns_comp: "(\<langle>f\<rangle>\<^sub>a ;; \<langle>g\<rangle>\<^sub>a) = \<langle>g \<circ> f\<rangle>\<^sub>a"
  by (simp add: assigns_r_comp usubst)

lemma assigns_r_conv:
  "bij f \<Longrightarrow> \<langle>f\<rangle>\<^sub>a\<^sup>- = \<langle>inv f\<rangle>\<^sub>a"
  by (rel_auto, simp_all add: bij_is_inj bij_is_surj surj_f_inv_f)

lemma assign_pred_transfer:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "$x \<sharp> b" "out\<alpha> \<sharp> b"
  shows "(b \<and> x := v) = (x := v \<and> b\<^sup>-)"
  using assms by (rel_blast)

lemma assign_r_comp: "mwb_lens x \<Longrightarrow> (x := u ;; P) = P\<lbrakk>\<lceil>u\<rceil>\<^sub></$x\<rbrakk>"
  by (simp add: assigns_r_comp usubst)

lemma assign_test: "mwb_lens x \<Longrightarrow> (x := \<guillemotleft>u\<guillemotright> ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright>)"
  by (simp add: assigns_comp subst_upd_comp subst_lit usubst_upd_idem)

lemma assign_twice: "\<lbrakk> vwb_lens x; x \<sharp> f \<rbrakk> \<Longrightarrow> (x := e ;; x := f) = (x := f)"
  by (simp add: assigns_comp usubst)

lemma assign_commute:
  assumes "x \<bowtie> y" "x \<sharp> f" "y \<sharp> e"
  shows "(x := e ;; y := f) = (y := f ;; x := e)"
  using assms
  by (rel_simp, simp_all add: lens_indep_comm)

lemma assign_cond:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "out\<alpha> \<sharp> b"
  shows "(x := e ;; (P \<triangleleft> b \<triangleright> Q)) = ((x := e ;; P) \<triangleleft> (b\<lbrakk>\<lceil>e\<rceil>\<^sub></$x\<rbrakk>) \<triangleright> (x := e ;; Q))"
  by (rel_auto)

lemma assign_rcond:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x := e ;; (P \<triangleleft> b \<triangleright>\<^sub>r Q)) = ((x := e ;; P) \<triangleleft> (b\<lbrakk>e/x\<rbrakk>) \<triangleright>\<^sub>r (x := e ;; Q))"
  by (rel_auto)

lemma assign_r_alt_def:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "x := v = II\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk>"
  by (rel_auto)

lemma assigns_r_ufunc: "ufunctional \<langle>f\<rangle>\<^sub>a"
  by (rel_auto)

lemma assigns_r_uinj: "inj f \<Longrightarrow> uinj \<langle>f\<rangle>\<^sub>a"
  by (rel_simp, simp add: inj_eq)

lemma assigns_r_swap_uinj:
  "\<lbrakk> vwb_lens x; vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> uinj (x,y := &y,&x)"
  using assigns_r_uinj swap_usubst_inj by auto

lemma skip_r_unfold:
  "vwb_lens x \<Longrightarrow> II = ($x\<acute> =\<^sub>u $x \<and> II\<restriction>\<^sub>\<alpha>x)"
  by (rel_simp, metis mwb_lens.put_put vwb_lens_mwb vwb_lens_wb wb_lens.get_put)

lemma skip_r_alpha_eq:
  "II = ($\<Sigma>\<acute> =\<^sub>u $\<Sigma>)"
  by (rel_auto)

lemma skip_ra_unfold:
  "II\<^bsub>x;y\<^esub> = ($x\<acute> =\<^sub>u $x \<and> II\<^bsub>y\<^esub>)"
  by (rel_auto)

lemma skip_res_as_ra:
  "\<lbrakk> vwb_lens y; x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L; x \<bowtie> y \<rbrakk> \<Longrightarrow> II\<restriction>\<^sub>\<alpha>x = II\<^bsub>y\<^esub>"
  apply (rel_auto)
  apply (metis (no_types, lifting) lens_indep_def)
  apply (metis vwb_lens.put_eq)
done

lemma assign_unfold:
  "vwb_lens x \<Longrightarrow> (x := v) = ($x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub>< \<and> II\<restriction>\<^sub>\<alpha>x)"
  apply (rel_auto, auto simp add: comp_def)
  using vwb_lens.put_eq by fastforce

lemma seqr_or_distl:
  "((P \<or> Q) ;; R) = ((P ;; R) \<or> (Q ;; R))"
  by (rel_auto)

lemma seqr_or_distr:
  "(P ;; (Q \<or> R)) = ((P ;; Q) \<or> (P ;; R))"
  by (rel_auto)

lemma seqr_and_distr_ufunc:
  "ufunctional P \<Longrightarrow> (P ;; (Q \<and> R)) = ((P ;; Q) \<and> (P ;; R))"
  by (rel_auto)

lemma seqr_and_distl_uinj:
  "uinj R \<Longrightarrow> ((P \<and> Q) ;; R) = ((P ;; R) \<and> (Q ;; R))"
  by (rel_auto)

lemma seqr_unfold:
  "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<Sigma>\<acute>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$\<Sigma>\<rbrakk>)"
  by (rel_auto)

lemma seqr_middle:
  assumes "vwb_lens x"
  shows "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  apply (rel_auto robust)
  apply (rename_tac xa P Q a b y)
  apply (rule_tac x="get\<^bsub>xa\<^esub> y" in exI)
  apply (rule_tac x="y" in exI)
  apply (simp)
done

lemma seqr_left_one_point:
  assumes "vwb_lens x"
  shows "((P \<and> $x\<acute> =\<^sub>u \<guillemotleft>v\<guillemotright>) ;; Q) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_right_one_point:
  assumes "vwb_lens x"
  shows "(P ;; ($x =\<^sub>u \<guillemotleft>v\<guillemotright> \<and> Q)) = (P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  by (rel_auto, metis vwb_lens_wb wb_lens.get_put)

lemma seqr_insert_ident_left:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(($x\<acute> =\<^sub>u $x \<and> P) ;; Q) = (P ;; Q)"
  using assms
  by (rel_simp, meson vwb_lens_wb wb_lens_weak weak_lens.put_get)

lemma seqr_insert_ident_right:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(P ;; ($x\<acute> =\<^sub>u $x \<and> Q)) = (P ;; Q)"
  using assms
  by (rel_simp, metis (no_types, hide_lams) vwb_lens_def wb_lens_def weak_lens.put_get)

lemma seq_var_ident_lift:
  assumes "vwb_lens x" "$x\<acute> \<sharp> P" "$x \<sharp> Q"
  shows "(($x\<acute> =\<^sub>u $x \<and> P) ;; ($x\<acute> =\<^sub>u $x \<and> Q)) = ($x\<acute> =\<^sub>u $x \<and> (P ;; Q))"
  using assms apply (rel_auto)
  by (metis (no_types, lifting) vwb_lens_wb wb_lens_weak weak_lens.put_get)

theorem precond_equiv:
  "P = (P ;; true) \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  by (rel_auto)

theorem postcond_equiv:
  "P = (true ;; P) \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  by (rel_auto)

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
  by pred_auto

lemma lit_convr [simp]: "\<guillemotleft>v\<guillemotright>\<^sup>- = \<guillemotleft>v\<guillemotright>"
  by pred_auto

lemma uivar_convr [simp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "($x)\<^sup>- = $x\<acute>"
  by pred_auto

lemma uovar_convr [simp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "($x\<acute>)\<^sup>- = $x"
  by pred_auto

lemma uop_convr [simp]: "(uop f u)\<^sup>- = uop f (u\<^sup>-)"
  by (pred_auto)

lemma bop_convr [simp]: "(bop f u v)\<^sup>- = bop f (u\<^sup>-) (v\<^sup>-)"
  by (pred_auto)

lemma eq_convr [simp]: "(p =\<^sub>u q)\<^sup>- = (p\<^sup>- =\<^sub>u q\<^sup>-)"
  by (pred_auto)

lemma not_convr [simp]: "(\<not> p)\<^sup>- = (\<not> p\<^sup>-)"
  by (pred_auto)

lemma disj_convr [simp]: "(p \<or> q)\<^sup>- = (q\<^sup>- \<or> p\<^sup>-)"
  by (pred_auto)

lemma conj_convr [simp]: "(p \<and> q)\<^sup>- = (q\<^sup>- \<and> p\<^sup>-)"
  by (pred_auto)

lemma seqr_convr [simp]: "(p ;; q)\<^sup>- = (q\<^sup>- ;; p\<^sup>-)"
  by (rel_auto)

lemma pre_convr [simp]: "\<lceil>p\<rceil>\<^sub><\<^sup>- = \<lceil>p\<rceil>\<^sub>>"
  by (rel_auto)

lemma post_convr [simp]: "\<lceil>p\<rceil>\<^sub>>\<^sup>- = \<lceil>p\<rceil>\<^sub><"
  by (rel_auto)

theorem seqr_pre_transfer: "in\<alpha> \<sharp> q \<Longrightarrow> ((P \<and> q) ;; R) = (P ;; (q\<^sup>- \<and> R))"
  by (rel_auto)

theorem seqr_pre_transfer':
  "((P \<and> \<lceil>q\<rceil>\<^sub>>) ;; R) = (P ;; (\<lceil>q\<rceil>\<^sub>< \<and> R))"
  by (rel_auto)

theorem seqr_post_out: "in\<alpha> \<sharp> r \<Longrightarrow> (P ;; (Q \<and> r)) = ((P ;; Q) \<and> r)"
  by (rel_blast)

lemma seqr_post_var_out:
  fixes x :: "(bool, '\<alpha>) uvar"
  shows "(P ;; (Q \<and> $x\<acute>)) = ((P ;; Q) \<and> $x\<acute>)"
  by (rel_auto)

theorem seqr_post_transfer: "out\<alpha> \<sharp> q \<Longrightarrow> (P ;; (q \<and> R)) = ((P \<and> q\<^sup>-) ;; R)"
  by (simp add: seqr_pre_transfer unrest_convr_in\<alpha>)

lemma seqr_pre_out: "out\<alpha> \<sharp> p \<Longrightarrow> ((p \<and> Q) ;; R) = (p \<and> (Q ;; R))"
  by (rel_blast)

lemma seqr_pre_var_out:
  fixes x :: "(bool, '\<alpha>) uvar"
  shows "(($x \<and> P) ;; Q) = ($x \<and> (P ;; Q))"
  by (rel_auto)

lemma seqr_true_lemma:
  "(P = (\<not> ((\<not> P) ;; true))) = (P = (P ;; true))"
  by (rel_auto)

lemma seqr_to_conj: "\<lbrakk> out\<alpha> \<sharp> P; in\<alpha> \<sharp> Q \<rbrakk> \<Longrightarrow> (P ;; Q) = (P \<and> Q)"
  by (metis postcond_left_unit seqr_pre_out utp_pred.inf_top.right_neutral)

lemma shEx_lift_seq_1 [uquant_lift]:
  "((\<^bold>\<exists> x \<bullet> P x) ;; Q) = (\<^bold>\<exists> x \<bullet> (P x ;; Q))"
  by pred_auto

lemma shEx_lift_seq_2 [uquant_lift]:
  "(P ;; (\<^bold>\<exists> x \<bullet> Q x)) = (\<^bold>\<exists> x \<bullet> (P ;; Q x))"
  by pred_auto

subsection {* Assertions and assumptions *}

lemma assume_twice: "(b\<^sup>\<top> ;; c\<^sup>\<top>) = (b \<and> c)\<^sup>\<top>"
  by (rel_auto)

lemma assert_twice: "(b\<^sub>\<bottom> ;; c\<^sub>\<bottom>) = (b \<and> c)\<^sub>\<bottom>"
  by (rel_auto)

subsection {* Frame and antiframe *}

definition frame :: "('a, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "frame x P = (II\<^bsub>x\<^esub> \<and> P)"

definition antiframe :: "('a, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "antiframe x P = (II\<restriction>\<^sub>\<alpha>x \<and> P)"

syntax
  "_frame"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:\<lbrakk>_\<rbrakk>" [64,0] 80)
  "_antiframe" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]" [64,0] 80)

translations
  "_frame x P" == "CONST frame x P"
  "_antiframe x P" == "CONST antiframe x P"

lemma frame_disj: "(x:\<lbrakk>P\<rbrakk> \<or> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<or> Q\<rbrakk>"
  by (rel_auto)

lemma frame_conj: "(x:\<lbrakk>P\<rbrakk> \<and> x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P \<and> Q\<rbrakk>"
  by (rel_auto)

lemma frame_seq:
  "\<lbrakk> vwb_lens x; $x\<acute> \<sharp> P; $x \<sharp> Q \<rbrakk>  \<Longrightarrow> (x:\<lbrakk>P\<rbrakk> ;; x:\<lbrakk>Q\<rbrakk>) = x:\<lbrakk>P ;; Q\<rbrakk>"
  by (rel_simp, metis vwb_lens_def wb_lens_weak weak_lens.put_get)

lemma antiframe_to_frame:
  "\<lbrakk> x \<bowtie> y; x +\<^sub>L y = 1\<^sub>L \<rbrakk> \<Longrightarrow> x:[P] = y:\<lbrakk>P\<rbrakk>"
  by (rel_auto, metis lens_indep_def, metis lens_indep_def surj_pair)

text {* While loop laws *}

theorem while_unfold:
  "while b do P od = ((P ;; while b do P od) \<triangleleft> b \<triangleright>\<^sub>r II)"
proof -
  have m:"mono (\<lambda>X. (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"
    by (auto intro: monoI seqr_mono cond_mono)
  have "(while b do P od) = (\<nu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"
    by (simp add: while_def)
  also have "... = ((P ;; (\<nu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)) \<triangleleft> b \<triangleright>\<^sub>r II)"
    by (subst lfp_unfold, simp_all add: m)
  also have "... = ((P ;; while b do P od) \<triangleleft> b \<triangleright>\<^sub>r II)"
    by (simp add: while_def)
  finally show ?thesis .
qed

subsection {* Relational unrestriction *}

text {* Relational unrestriction states that a variable is unchanged by a relation. Eventually
  I'd also like to have it state that the relation also does not depend on the variable's
  initial value, but I'm not sure how to state that yet. For now we represent this by
  the parametric healthiness condition RID. *}

definition RID :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel"
where "RID x P = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x)"

declare RID_def [urel_defs]

lemma RID_idem:
  "mwb_lens x \<Longrightarrow> RID(x)(RID(x)(P)) = RID(x)(P)"
  by (rel_auto)

lemma RID_mono:
  "P \<sqsubseteq> Q \<Longrightarrow> RID(x)(P) \<sqsubseteq> RID(x)(Q)"
  by (rel_auto)

lemma RID_skip_r:
  "vwb_lens x \<Longrightarrow> RID(x)(II) = II"
  apply (rel_auto) using vwb_lens.put_eq by fastforce

lemma RID_disj:
  "RID(x)(P \<or> Q) = (RID(x)(P) \<or> RID(x)(Q))"
  by (rel_auto)

lemma RID_conj:
  "vwb_lens x \<Longrightarrow> RID(x)(RID(x)(P) \<and> RID(x)(Q)) = (RID(x)(P) \<and> RID(x)(Q))"
  by (rel_auto)

lemma RID_assigns_r_diff:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> RID(x)(\<langle>\<sigma>\<rangle>\<^sub>a) = \<langle>\<sigma>\<rangle>\<^sub>a"
  apply (rel_auto)
  apply (metis vwb_lens.put_eq)
  apply (metis vwb_lens_wb wb_lens.get_put wb_lens_weak weak_lens.put_get)
done

lemma RID_assign_r_same:
  "vwb_lens x \<Longrightarrow> RID(x)(x := v) = II"
  apply (rel_auto)
  using vwb_lens.put_eq apply fastforce
done

lemma RID_seq_left:
  assumes "vwb_lens x"
  shows "RID(x)(RID(x)(P) ;; Q) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(RID(x)(P) ;; Q) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; Q) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> (\<exists> $x \<bullet> $x\<acute> =\<^sub>u $x)) ;; (\<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_auto)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_auto)
    apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by (rel_auto)
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma RID_seq_right:
  assumes "vwb_lens x"
  shows "RID(x)(P ;; RID(x)(Q)) = (RID(x)(P) ;; RID(x)(Q))"
proof -
  have "RID(x)(P ;; RID(x)(Q)) = ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (simp add: RID_def usubst)
  also from assms have "... = (((\<exists> $x \<bullet>  P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> (\<exists> $x\<acute> \<bullet> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_auto)
  also from assms have "... = (((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    apply (rel_auto)
    apply (metis vwb_lens.put_eq)
    apply (metis mwb_lens.put_put vwb_lens_mwb)
  done
  also from assms have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp robust, metis (full_types) mwb_lens.put_put vwb_lens_def wb_lens_weak weak_lens.put_get)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)) \<and> $x\<acute> =\<^sub>u $x)"
    by (rel_simp, fastforce)
  also have "... = ((((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P) \<and> $x\<acute> =\<^sub>u $x) ;; ((\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> Q) \<and> $x\<acute> =\<^sub>u $x)))"
    by (rel_auto)
  also have "... = (RID(x)(P) ;; RID(x)(Q))"
    by (rel_auto)
  finally show ?thesis .
qed

definition unrest_relation :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> hrel \<Rightarrow> bool" (infix "\<sharp>\<sharp>" 20)
where "(x \<sharp>\<sharp> P) \<longleftrightarrow> (P = RID(x)(P))"

declare unrest_relation_def [urel_defs]

lemma skip_r_runrest [unrest]:
  "vwb_lens x \<Longrightarrow> x \<sharp>\<sharp> II"
  by (simp add: RID_skip_r unrest_relation_def)

lemma assigns_r_runrest:
  "\<lbrakk> vwb_lens x; x \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: RID_assigns_r_diff unrest_relation_def)

lemma seq_r_runrest [unrest]:
  assumes "vwb_lens x" "x \<sharp>\<sharp> P" "x \<sharp>\<sharp> Q"
  shows "x \<sharp>\<sharp> (P ;; Q)"
  by (metis RID_seq_left assms unrest_relation_def)

lemma false_runrest [unrest]: "x \<sharp>\<sharp> false"
  by (rel_auto)

lemma and_runrest [unrest]: "\<lbrakk> vwb_lens x; x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<and> Q)"
  by (metis RID_conj unrest_relation_def)

lemma or_runrest [unrest]: "\<lbrakk> x \<sharp>\<sharp> P; x \<sharp>\<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp>\<sharp> (P \<or> Q)"
  by (simp add: RID_disj unrest_relation_def)

subsection {* Alphabet laws *}

lemma aext_cond [alpha]:
  "(P \<triangleleft> b \<triangleright> Q) \<oplus>\<^sub>p a = ((P \<oplus>\<^sub>p a) \<triangleleft> (b \<oplus>\<^sub>p a) \<triangleright> (Q \<oplus>\<^sub>p a))"
  by (rel_auto)

lemma aext_seq [alpha]:
  "wb_lens a \<Longrightarrow> ((P ;; Q) \<oplus>\<^sub>p (a \<times>\<^sub>L a)) = ((P \<oplus>\<^sub>p (a \<times>\<^sub>L a)) ;; (Q \<oplus>\<^sub>p (a \<times>\<^sub>L a)))"
  by (rel_simp, metis wb_lens_weak weak_lens.put_get)

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
  by (rel_auto)

theorem RA6: "((P \<or> Q) ;; R) = ((P;;R) \<or> (Q;;R))"
  using seqr_or_distl by blast

theorem RA7: "((P\<^sup>- ;; (\<not>(P ;; Q))) \<or> (\<not>Q)) = (\<not>Q)"
  by (rel_auto)

subsection {* Relational alphabet extension *}

lift_definition rel_alpha_ext :: "'\<beta> hrel \<Rightarrow> ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" (infix "\<oplus>\<^sub>R" 65)
is "\<lambda> P x (b1, b2). P (get\<^bsub>x\<^esub> b1, get\<^bsub>x\<^esub> b2) \<and> (\<forall> b. b1 \<oplus>\<^sub>L b on x = b2 \<oplus>\<^sub>L b on x)" .

lemma rel_alpha_ext_alt_def:
  assumes "vwb_lens y" "x +\<^sub>L y \<approx>\<^sub>L 1\<^sub>L" "x \<bowtie> y"
  shows "P \<oplus>\<^sub>R x = (P \<oplus>\<^sub>p (x \<times>\<^sub>L x) \<and> $y\<acute> =\<^sub>u $y)"
  using assms
  apply (rel_auto robust, simp_all add: lens_override_def)
  apply (metis lens_indep_get lens_indep_sym)
  apply (metis vwb_lens_def wb_lens.get_put wb_lens_def weak_lens.put_get)
done

subsection {* Program values *}

abbreviation prog_val :: "'\<alpha> hrel \<Rightarrow> ('\<alpha> hrel, '\<alpha>) uexpr" ("\<lbrace>_\<rbrace>\<^sub>u")
where "\<lbrace>P\<rbrace>\<^sub>u \<equiv> \<guillemotleft>P\<guillemotright>"

lift_definition call :: "('\<alpha> hrel, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
is "\<lambda> P b. P (fst b) b" .

lemma call_prog_val: "call \<lbrace>P\<rbrace>\<^sub>u = P"
  by (simp add: call_def urel_defs lit.rep_eq Rep_uexpr_inverse)
end