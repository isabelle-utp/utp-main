section {* Alphabetised relations *}

theory utp_rel
imports  
  utp_pred
begin

default_sort type

named_theorems urel_defs

consts
  useq   :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 15)
  uskip  :: "'a" ("II")

definition in\<alpha> :: "('\<alpha>, '\<alpha> \<times> '\<beta>) uvar" where
"in\<alpha> = \<lparr> var_lookup = fst, var_update = \<lambda> f (A, A'). (f A, A') \<rparr>"

definition out\<alpha> :: "('\<beta>, '\<alpha> \<times> '\<beta>) uvar" where
"out\<alpha> = \<lparr> var_lookup = snd, var_update = \<lambda> f (A, A'). (A, f A') \<rparr>"

declare in\<alpha>_def [urel_defs]
declare out\<alpha>_def [urel_defs]

type_synonym '\<alpha> condition       = "'\<alpha> upred"
type_synonym ('\<alpha>, '\<beta>) relation  = "('\<alpha> \<times> '\<beta>) upred"
type_synonym '\<alpha> hrelation       = "('\<alpha> \<times> '\<alpha>) upred"

definition cond::"('\<alpha>,  '\<beta>) relation \<Rightarrow> ('\<alpha>,  '\<beta>) relation \<Rightarrow> ('\<alpha>,  '\<beta>) relation \<Rightarrow> ('\<alpha>,  '\<beta>) relation" 
                                                          ("(3_ \<triangleleft> _ \<triangleright> / _)" [14,0,15] 14)
where "(P \<triangleleft> b \<triangleright> Q) \<equiv> (b \<and> P) \<or> ((\<not> b) \<and> Q)"

abbreviation rcond::"('\<alpha>,  '\<beta>) relation \<Rightarrow> '\<alpha> condition \<Rightarrow> ('\<alpha>,  '\<beta>) relation \<Rightarrow> ('\<alpha>,  '\<beta>) relation" 
                                                          ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r / _)" [14,0,15] 14)
where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>< \<triangleright> Q)"

lift_definition seqr::"(('\<alpha> \<times> '\<beta>) upred) \<Rightarrow> (('\<beta> \<times> '\<gamma>) upred) \<Rightarrow> ('\<alpha> \<times> '\<gamma>) upred"
is "\<lambda> P Q r. r : ({p. P p} O {q. Q q})" .

lift_definition conv_r :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta> \<times> '\<alpha>) uexpr" ("_\<^sup>-" [999] 999)
is "\<lambda> e (b1, b2). e (b2, b1)" .

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
  id_list and uexpr_list

syntax
  "_id_unit"    :: "id \<Rightarrow> id_list" ("_")
  "_id_list"    :: "id \<Rightarrow> id_list \<Rightarrow> id_list" ("_,/ _")
  "_uexpr_unit" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list" ("_" [40] 40)
  "_uexpr_list" :: "('a, '\<alpha>) uexpr \<Rightarrow> uexpr_list \<Rightarrow> uexpr_list" ("_,/ _" [40,40] 40)
  "_assignment" :: "svars \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrelation"  (infixr ":=" 35)
  "_mk_usubst"  :: "svars \<Rightarrow> uexpr_list \<Rightarrow> '\<alpha> usubst"

translations
  "_mk_usubst (_svar x) (_uexpr_unit v)" == "[x \<mapsto>\<^sub>s v]"
  "_mk_usubst (_id_list x xs) (_uexpr_list v vs)" == "(_mk_usubst xs vs)(x \<mapsto>\<^sub>s v)"
  "_assignment xs vs" => "CONST assigns_r (_psubst (CONST id) xs vs)"
  "x := v" <= "CONST assign_r x v"
  "x,y := u,v" <= "CONST assign_2_r x y u v"

adhoc_overloading
  useq seqr and
  uskip skip_r

method rel_tac = ((simp add: upred_defs urel_defs)?, (transfer, (rule_tac ext)?, auto simp add: urel_defs relcomp_unfold fun_eq_iff)?)

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

lemma unrest_iuvar [unrest]: "uvar x \<Longrightarrow> out\<alpha> \<sharp> $x"
  by (simp add: out\<alpha>_def iuvar_def, transfer, auto)

lemma unrest_ouvar [unrest]: "uvar x \<Longrightarrow> in\<alpha> \<sharp> $x\<acute>"
  by (simp add: in\<alpha>_def ouvar_def, transfer, auto)

lemma unrest_in\<alpha>_var [unrest]:
  "\<lbrakk> uvar x; in\<alpha> \<sharp> P \<rbrakk> \<Longrightarrow> $x \<sharp> P"
  by (pred_tac, simp add: in\<alpha>_def)

lemma unrest_out\<alpha>_var [unrest]:
  "\<lbrakk> uvar x; out\<alpha> \<sharp> P \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P"
  by (pred_tac, simp add: out\<alpha>_def)

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
  "\<lbrakk> uvar x; out\<alpha> \<sharp> v \<rbrakk> \<Longrightarrow> (P ;; Q)\<lbrakk>v/$x\<rbrakk> = ((P\<lbrakk>v/$x\<rbrakk>) ;; Q)"
  apply (rel_tac)
  apply (rename_tac x v P Q a y ya)
  apply (rule_tac x="ya" in exI)
  apply (simp)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="y" in spec)
  apply (drule_tac x="\<lambda>_.ya" in spec)
  apply (simp)
  apply (rename_tac x v P Q a ba y)
  apply (rule_tac x="y" in exI)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="y" in spec)
  apply (drule_tac x="\<lambda>_.ba" in spec)
  apply (simp)
done

lemma usubst_seq_right [usubst]: 
  "\<lbrakk> uvar x; in\<alpha> \<sharp> v \<rbrakk> \<Longrightarrow> (P ;; Q)\<lbrakk>v/$x\<acute>\<rbrakk> = (P ;; Q\<lbrakk>v/$x\<acute>\<rbrakk>)"
  apply (rel_tac)
  apply (rename_tac x v P Q b xa ya)
  apply (rule_tac x="ya" in exI)
  apply (simp)
  apply (drule_tac x="ya" in spec)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="\<lambda>_.xa" in spec)
  apply (simp)
  apply (rename_tac x v P Q b aa y)
  apply (rule_tac x="y" in exI)
  apply (simp)
  apply (drule_tac x="aa" in spec)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="\<lambda>_.y" in spec)
  apply (simp)
done

lemma usubst_condr [usubst]:
  "\<sigma> \<dagger> (P \<triangleleft> b \<triangleright> Q) = (\<sigma> \<dagger> P \<triangleleft> \<sigma> \<dagger> b \<triangleright> \<sigma> \<dagger> Q)"
  by rel_tac

lemma subst_skip_r [usubst]:
  "II\<lbrakk>\<lceil>v\<rceil>\<^sub></$x\<rbrakk> = (x := v)"
  by (rel_tac)

subsection {* Lifting laws *}

lemma lift_pre_conj [ulift]: "\<lceil>p \<and> q\<rceil>\<^sub>< = (\<lceil>p\<rceil>\<^sub>< \<and> \<lceil>q\<rceil>\<^sub><)"
  by (pred_tac)

lemma lift_post_conj [ulift]: "\<lceil>p \<and> q\<rceil>\<^sub>> = (\<lceil>p\<rceil>\<^sub>> \<and> \<lceil>q\<rceil>\<^sub>>)"
  by (pred_tac)

lemma lift_pre_disj [ulift]: "\<lceil>p \<or> q\<rceil>\<^sub>< = (\<lceil>p\<rceil>\<^sub>< \<or> \<lceil>q\<rceil>\<^sub><)"
  by (pred_tac)

lemma lift_post_disj [ulift]: "\<lceil>p \<or> q\<rceil>\<^sub>> = (\<lceil>p\<rceil>\<^sub>> \<or> \<lceil>q\<rceil>\<^sub>>)"
  by (pred_tac)

lemma lift_pre_not [ulift]: "\<lceil>\<not> p\<rceil>\<^sub>< = (\<not> \<lceil>p\<rceil>\<^sub><)"
  by (pred_tac)

lemma lift_post_not [ulift]: "\<lceil>\<not> p\<rceil>\<^sub>> = (\<not> \<lceil>p\<rceil>\<^sub>>)"
  by (pred_tac)

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
  apply (pred_tac, auto simp add: out\<alpha>_def)
  apply (rename_tac p a b)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="\<lambda> _. a" in spec)
  apply (simp)
done

abbreviation ustar :: "'\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("_\<^sup>\<star>\<^sub>u" [999] 999) where
"P\<^sup>\<star>\<^sub>u \<equiv> unital_quantale.qstar II op ;; Sup P"

definition while :: "'\<alpha> condition \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" ("while _ do _ od") where
"while b do P od = ((\<lceil>b\<rceil>\<^sub>< \<and> P)\<^sup>\<star>\<^sub>u \<and> (\<not> \<lceil>b\<rceil>\<^sub>>))"

declare while_def [urel_defs] 

lemma cond_idem:"(P \<triangleleft> b \<triangleright> P) = P" by rel_tac 

lemma cond_symm:"(P \<triangleleft> b \<triangleright> Q) = (Q \<triangleleft> \<not> b \<triangleright> P)" by rel_tac

lemma cond_assoc: "((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> R) = (P \<triangleleft> b \<and> c \<triangleright> (Q \<triangleleft> c \<triangleright> R))" by rel_tac

lemma cond_distr: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> c \<triangleright> R)) = ((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> (P \<triangleleft> b \<triangleright> R))" by rel_tac

lemma cond_unit_T:"(P \<triangleleft> true \<triangleright> Q) = P" by rel_tac

lemma cond_unit_F:"(P \<triangleleft> false \<triangleright> Q) = Q" by rel_tac

lemma cond_L6: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)" by rel_tac

lemma cond_L7: "(P \<triangleleft> b \<triangleright> (P \<triangleleft> c \<triangleright> Q)) = (P \<triangleleft> b \<or> c \<triangleright> Q)" by rel_tac

lemma cond_and_distr: "((P \<and> Q) \<triangleleft> b \<triangleright> (R \<and> S)) = ((P \<triangleleft> b \<triangleright> R) \<and> (Q \<triangleleft> b \<triangleright> S))" by rel_tac

lemma cond_or_distr: "((P \<or> Q) \<triangleleft> b \<triangleright> (R \<or> S)) = ((P \<triangleleft> b \<triangleright> R) \<or> (Q \<triangleleft> b \<triangleright> S))" by rel_tac

lemma cond_imp_distr: 
"((P \<Rightarrow> Q) \<triangleleft> b \<triangleright> (R \<Rightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Rightarrow> (Q \<triangleleft> b \<triangleright> S))" by rel_tac

lemma cond_eq_distr: 
"((P \<Leftrightarrow> Q) \<triangleleft> b \<triangleright> (R \<Leftrightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Leftrightarrow> (Q \<triangleleft> b \<triangleright> S))" by rel_tac

lemma comp_cond_left_distr:
  "((P \<triangleleft> b \<triangleright>\<^sub>r Q) ;; R) = ((P ;; R) \<triangleleft> b \<triangleright>\<^sub>r (Q ;; R))"
  by rel_tac

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

lemma pre_skip_post: "(\<lceil>b\<rceil>\<^sub>< \<and> II) = (II \<and> \<lceil>b\<rceil>\<^sub>>)"
  by (rel_tac)

lemma seqr_exists_left:
  "uvar x \<Longrightarrow> ((\<exists> $x \<bullet> P) ;; Q) = (\<exists> $x \<bullet> (P ;; Q))"
  by (rel_tac, auto simp add: comp_def)

lemma seqr_exists_right:
  "uvar x \<Longrightarrow> (P ;; (\<exists> $x\<acute> \<bullet> Q)) = (\<exists> $x\<acute> \<bullet> (P ;; Q))"
  by (rel_tac, auto simp add: comp_def)

text {* We should be able to generalise this law to arbitrary assignments at some point,
        but that requires additional conversion operators for substitutions that act
        only on @{const "in\<alpha>"}. *}

lemma assign_subst [usubst]:
  "\<lbrakk> uvar x; uvar y \<rbrakk> \<Longrightarrow> [$x \<mapsto>\<^sub>s \<lceil>u\<rceil>\<^sub><] \<dagger> (y := v) = (x, y := u, [x \<mapsto>\<^sub>s u] \<dagger> v)"
  by rel_tac
 
lemma assigns_idem: "uvar x \<Longrightarrow> (x,x := u,v) = (x := v)"
  by (simp add: usubst)

lemma assigns_comp: "(assigns_r f ;; assigns_r g) = assigns_r (g \<circ> f)" 
  by (transfer, auto simp add:relcomp_unfold)

lemma assigns_r_comp: "uvar x \<Longrightarrow> (\<langle>\<sigma>\<rangle>\<^sub>a ;; P) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P)"
  by rel_tac

lemma assign_r_comp: "uvar x \<Longrightarrow> (x := u ;; P) = ([$x \<mapsto>\<^sub>s \<lceil>u\<rceil>\<^sub><] \<dagger> P)"
  by (simp add: assigns_r_comp usubst)

lemma assign_test: "uvar x \<Longrightarrow> (x := \<guillemotleft>u\<guillemotright> ;; x := \<guillemotleft>v\<guillemotright>) = (x := \<guillemotleft>v\<guillemotright>)"
  by (simp add: assigns_comp subst_upd_comp subst_lit usubst_upd_idem)

lemma skip_r_unfold:
  "uvar x \<Longrightarrow> II = ($x\<acute> =\<^sub>u $x \<and> II\<restriction>\<^sub>\<alpha>x)"
  by (rel_tac, blast, metis uvar.var_state_eq_iff uvar.var_update_lookup)

lemma assign_unfold:
  "uvar x \<Longrightarrow> (x := v) = ($x\<acute> =\<^sub>u \<lceil>v\<rceil>\<^sub>< \<and> II\<restriction>\<^sub>\<alpha>x)"
  apply (rel_tac, auto simp add: comp_def )
  using var_assign_eq apply fastforce
done

lemma seqr_or_distl:
  "((P \<or> Q) ;; R) = ((P ;; R) \<or> (Q ;; R))"
  by rel_tac

lemma seqr_or_distr:
  "(P ;; (Q \<or> R)) = ((P ;; Q) \<or> (P ;; R))"
  by rel_tac

lemma seqr_middle: 
  assumes "uvar x"
  shows "(P ;; Q) = (\<^bold>\<exists> v \<bullet> P\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<acute>\<rbrakk> ;; Q\<lbrakk>\<guillemotleft>v\<guillemotright>/$x\<rbrakk>)"
  using assms
  apply (rel_tac)
  apply (rename_tac xa P Q a b y)
  apply (rule_tac x="var_lookup xa y" in exI)
  apply (rule_tac x="y" in exI)
  apply (simp)
done

theorem precond_equiv:
  "P = (P ;; true) \<longleftrightarrow> (out\<alpha> \<sharp> P)"
  apply (rel_tac)
  apply (rename_tac P a b y)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="\<lambda> _.y" in spec)
  apply (simp)
done

theorem postcond_equiv:
  "P = (true ;; P) \<longleftrightarrow> (in\<alpha> \<sharp> P)"
  apply (rel_tac)
  apply (rename_tac P a b y)
  apply (drule_tac x="a" in spec)
  apply (drule_tac x="b" in spec)
  apply (drule_tac x="\<lambda> _.y" in spec)
  apply (simp)
done

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
  apply (rule_tac x="b1" in exI)
  apply (drule_tac x="b1" in spec)
  apply (drule_tac x="b2" in spec)
  apply (drule_tac x="\<lambda> _. b" in spec)
  apply (simp)
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

lemma disj_convr [simp]: "(p \<or> q)\<^sup>- = (q\<^sup>- \<or> p\<^sup>-)"
  by (pred_tac)

lemma conj_convr [simp]: "(p \<and> q)\<^sup>- = (q\<^sup>- \<and> p\<^sup>-)"
  by (pred_tac)

lemma seqr_convr [simp]: "(p ;; q)\<^sup>- = (q\<^sup>- ;; p\<^sup>-)"
  by rel_tac

theorem seqr_pre_transfer: "in\<alpha> \<sharp> q \<Longrightarrow> ((P \<and> q) ;; R) = (P ;; (q\<^sup>- \<and> R))"
  apply (rel_tac)
  apply (rename_tac q P R a b y)
  apply (rule_tac x="y" in exI, simp)
  apply (drule_tac x="b" in spec, drule_tac x="y" in spec, drule_tac x="\<lambda>_.a" in spec, simp)
  apply (rename_tac q P R a b y)
  apply (rule_tac x="y" in exI, simp)
  apply (drule_tac x="a" in spec, drule_tac x="y" in spec, drule_tac x="\<lambda>_.b" in spec, simp)
done

theorem seqr_post_out: "in\<alpha> \<sharp> r \<Longrightarrow> (P ;; (Q \<and> r)) = ((P ;; Q) \<and> r)"
  apply (rel_tac)
  apply (rename_tac r P Q a b y)
  apply (drule_tac x="a" in spec, drule_tac x="b" in spec, drule_tac x="\<lambda>_.y" in spec, simp)
  apply (rename_tac r P Q a b y)
  apply (rule_tac x="y" in exI)
  apply (simp, drule_tac x="a" in spec, drule_tac x="b" in spec, drule_tac x="\<lambda>_.y" in spec, simp)
done

theorem seqr_post_transfer: "out\<alpha> \<sharp> q \<Longrightarrow> (P ;; (q \<and> R)) = (P \<and> q\<^sup>- ;; R)"
  by (simp add: seqr_pre_transfer unrest_convr_in\<alpha>)

lemma seqr_pre_out: "out\<alpha> \<sharp> p \<Longrightarrow> ((p \<and> Q) ;; R) = (p \<and> (Q ;; R))"
  apply (rel_tac)
  apply (rename_tac p Q R a b y)
  apply (drule_tac x="a" in spec, drule_tac x="b" in spec, drule_tac x="\<lambda>_.y" in spec, simp)
  apply (rename_tac p Q R a b y)
  apply (rule_tac x="y" in exI)
  apply (simp, drule_tac x="a" in spec, drule_tac x="b" in spec, drule_tac x="\<lambda>_.y" in spec, simp)
done

lemma seqr_true_lemma: 
  "(P = (\<not> (\<not> P ;; true))) = (P = (P ;; true))"
  by rel_tac

lemma shEx_lift_seq [uquant_lift]: 
  "((\<^bold>\<exists> x \<bullet> P(x)) ;; (\<^bold>\<exists> y \<bullet> Q(y))) = (\<^bold>\<exists> x \<bullet> \<^bold>\<exists> y \<bullet> P(x) ;; Q(y))"
  by pred_tac

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

end