section {* Alphabetised Predicates *}

theory utp_pred
imports  
  utp_expr
  utp_subst
begin

text {* An alphabetised predicate is a simply a boolean valued expression *}

type_synonym '\<alpha> upred = "(bool, '\<alpha>) uexpr"

translations
  (type) "'\<alpha> upred" <= (type) "(bool, '\<alpha>) uexpr"

named_theorems upred_defs

subsection {* Predicate syntax *}

text {* We want to remain as close as possible to the mathematical UTP syntax, but also
        want to be conservative with HOL. For this reason we chose not to steal syntax
        from HOL, but where possible use polymorphism to allow selection of the appropriate
        operator (UTP vs. HOL). Thus we will first remove the standard syntax for conjunction,
        disjunction, and negation, and replace these with adhoc overloaded definitions. *}

no_notation
  conj (infixr "\<and>" 35) and
  disj (infixr "\<or>" 30) and
  Not ("\<not> _" [40] 40)

consts
  utrue  :: "'a" ("true")
  ufalse :: "'a" ("false")
  uconj  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<and>" 35)
  udisj  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<or>" 30)
  uimpl  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<Rightarrow>" 25)
  uiff   :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<Leftrightarrow>" 25) 
  unot   :: "'a \<Rightarrow> 'a" ("\<not> _" [40] 40)
  uex    :: "('a, '\<alpha>) uvar \<Rightarrow> 'p \<Rightarrow> 'p"
  uall   :: "('a, '\<alpha>) uvar \<Rightarrow> 'p \<Rightarrow> 'p"
  ushEx  :: "['a \<Rightarrow> 'p] \<Rightarrow> 'p"
  ushAll :: "['a \<Rightarrow> 'p] \<Rightarrow> 'p"

adhoc_overloading
  uconj conj and 
  udisj disj and
  unot Not

text {* We set up two versions of each of the quantifiers: @{const uex} / @{const uall} and
        @{const ushEx} / @{const ushAll}. The former pair allows quantification of UTP variables,
        whilst the latter allows quantification of HOL variables. Both varieties will be
        needed at various points. Syntactically they are distinguish by a boldface quantifier
        for the HOL versions (achieved by the "bold" escape in Isabelle). *}

syntax
  "_uex"     :: "svar \<Rightarrow> logic \<Rightarrow> logic" ("\<exists> _ \<bullet> _" [0, 10] 10)
  "_uall"    :: "svar \<Rightarrow> logic \<Rightarrow> logic" ("\<forall> _ \<bullet> _" [0, 10] 10)
  "_ushEx"   :: "idt \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<exists> _ \<bullet> _" [0, 10] 10)
  "_ushAll"  :: "idt \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ \<bullet> _" [0, 10] 10)
  "_ushBEx"  :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<exists> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ushBAll" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ \<in> _ \<bullet> _" [0, 0, 10] 10)

translations
  "\<exists> &x \<bullet> P"  => "CONST uex x P"
  "\<exists> $x \<bullet> P"  == "CONST uex (CONST in_var x) P"
  "\<exists> $x\<acute> \<bullet> P" == "CONST uex (CONST out_var x) P"
  "\<exists> x \<bullet> P"   == "CONST uex x P"
  "\<forall> &x \<bullet> P"  => "CONST uall x P"
  "\<forall> $x \<bullet> P"  == "CONST uall (CONST in_var x) P"
  "\<forall> $x\<acute> \<bullet> P" == "CONST uall (CONST out_var x) P"
  "\<forall> x \<bullet> P"   == "CONST uall x P"
  "\<^bold>\<exists> x \<bullet> P"   == "CONST ushEx (\<lambda> x. P)"
  "\<^bold>\<exists> x \<in> A \<bullet> P" => "\<^bold>\<exists> x \<bullet> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u A \<and> P"
  "\<^bold>\<forall> x \<bullet> P"   == "CONST ushAll (\<lambda> x. P)"
  "\<^bold>\<forall> x \<in> A \<bullet> P" => "\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u A \<Rightarrow> P"

subsection {* Predicate operators *}

text {* We chose to maximally reuse definitions and laws built into HOL. For this reason,
        when introducing the core operators we proceed by lifting operators from the
        polymorphic algebraic hiearchy of HOL. Thus the initial definitions take
        place in the context of type class instantiations. We first introduce our own
        class called \emph{refine} that will add the refinement operator syntax to
        the HOL partial order class. *}

class refine = order

abbreviation refineBy :: "'a::refine \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<sqsubseteq>" 50) where
"P \<sqsubseteq> Q \<equiv> less_eq Q P"

text {* Since, on the whole, lattices in UTP are the opposite way up to the standard definitions
        in HOL, we syntactically invert the lattice operators. This is the one exception where
        we do steal HOL syntax, but I think it makes sense for UTP. *}

notation inf (infixl "\<squnion>" 70)
notation sup (infixl "\<sqinter>" 65)

notation Inf ("\<Squnion>_" [900] 900)
notation Sup ("\<Sqinter>_" [900] 900)

notation bot ("\<top>")
notation top ("\<bottom>")

text {* We now introduce a partial order on expressions. Note this is more general than refinement
        since it lifts an order on any expression type (not just Boolean). However, the Boolean
        version does equate to refinement. *}

instantiation uexpr :: (order, type) order
begin
  lift_definition less_eq_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  is "\<lambda> P Q. (\<forall> A. P A \<le> Q A)" .
  definition less_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> bool"
  where "less_uexpr P Q = (P \<le> Q \<and> \<not> Q \<le> P)"
instance proof
  fix x y z :: "('a, 'b) uexpr"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (simp add: less_uexpr_def)
  show "x \<le> x" by (transfer, auto)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" 
    by (transfer, blast intro:order.trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (transfer, rule ext, simp add: eq_iff)
qed
end

text {* We also trivially instantiate our refinement class *}

instance uexpr :: (order, type) refine ..

text {* Next we introduce the lattice operators, which is again done by lifting. *}

instantiation uexpr :: (lattice, type) lattice
begin
  lift_definition sup_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  is "\<lambda>P Q A. sup (P A) (Q A)" .
  lift_definition inf_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  is "\<lambda>P Q A. inf (P A) (Q A)" .
instance
  by (intro_classes) (transfer, auto)+
end

instantiation uexpr :: (bounded_lattice, type) bounded_lattice
begin
  lift_definition bot_uexpr :: "('a, 'b) uexpr" is "\<lambda> A. bot" .
  lift_definition top_uexpr :: "('a, 'b) uexpr" is "\<lambda> A. top" .
instance
  by (intro_classes) (transfer, auto)+
end

text {* Finally we show that predicates form a Boolean algebra (under the lattice operators). *}

instance uexpr :: (boolean_algebra, type) boolean_algebra
  by (intro_classes, simp_all add: uexpr_defs) 
     (transfer, simp add: sup_inf_distrib1 inf_compl_bot sup_compl_top diff_eq)+

instantiation uexpr :: (complete_lattice, type) complete_lattice
begin
  lift_definition Inf_uexpr :: "('a, 'b) uexpr set \<Rightarrow> ('a, 'b) uexpr" 
  is "\<lambda> PS A. INF P:PS. P(A)" .
  lift_definition Sup_uexpr :: "('a, 'b) uexpr set \<Rightarrow> ('a, 'b) uexpr" 
  is "\<lambda> PS A. SUP P:PS. P(A)" .
instance
  by (intro_classes)
     (transfer, auto intro: INF_lower SUP_upper simp add: INF_greatest SUP_least)+
end

text {* With the lattice operators defined, we can proceed to give definitions for the
        standard predicate operators in terms of them. *}

definition "true_upred  = (top :: '\<alpha> upred)"
definition "false_upred = (bot :: '\<alpha> upred)"
definition "conj_upred  = (inf :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)" 
definition "disj_upred  = (sup :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)"
definition "not_upred   = (uminus :: '\<alpha> upred \<Rightarrow> '\<alpha> upred)"
definition "diff_upred  = (minus :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)"

text {* We also define the other predicate operators *}

lift_definition impl::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> P Q A. P A \<longrightarrow> Q A" .

lift_definition iff_upred ::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> P Q A. P A \<longleftrightarrow> Q A" .

lift_definition ex :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> x P b. (\<exists> v. P(var_assign x v b))" .

lift_definition shEx ::"['\<beta> \<Rightarrow>'\<alpha> upred] \<Rightarrow> '\<alpha> upred" is
"\<lambda> P A. \<exists> x. (P x) A" .

lift_definition all :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> x P b. (\<forall> v. P(var_assign x v b))" .

lift_definition shAll ::"['\<beta> \<Rightarrow>'\<alpha> upred] \<Rightarrow> '\<alpha> upred" is
"\<lambda> P A. \<forall> x. (P x) A" .

text {* We have to add a u subscript to the closure operator as I don't want to override the syntax
        for HOL lists (we'll be using them later). *}

lift_definition closure::"'\<alpha> upred \<Rightarrow> '\<alpha> upred" ("[_]\<^sub>u") is
"\<lambda> P A. \<forall>A'. P A'" .

lift_definition taut :: "'\<alpha> upred \<Rightarrow> bool" ("`_`")
is "\<lambda> P. \<forall> A. P A" .

adhoc_overloading
  utrue "true_upred" and
  ufalse "false_upred" and
  unot "not_upred" and
  uconj "conj_upred" and
  udisj "disj_upred" and
  uimpl impl and
  uiff iff_upred and
  uex ex and
  uall all and
  ushEx shEx and
  ushAll shAll

subsection {* Proof support *}

text {* We set up a simple tactic with the help of \emph{Eisbach} that applies predicate
        definitions, applies the transfer method to drop down to the core definitions,
        applies extensionality (to remove the resulting lambda term) and the applies auto.
        This simple tactic will suffice to prove most of the standard laws. *}

method pred_tac = ((simp only: upred_defs)? ; (transfer, (rule_tac ext)?, auto simp add: fun_eq_iff)?)

declare true_upred_def [upred_defs]
declare false_upred_def [upred_defs]
declare conj_upred_def [upred_defs]
declare disj_upred_def [upred_defs]
declare not_upred_def [upred_defs]
declare diff_upred_def [upred_defs]
declare subst_upd_uvar_def [upred_defs]
declare subst_upd_dvar_def [upred_defs]
declare uexpr_defs [upred_defs]
declare usubst_rel_lift_def [upred_defs]
declare usubst_rel_drop_def [upred_defs]

lemma true_alt_def: "true = \<guillemotleft>True\<guillemotright>"
  by (pred_tac)

lemma false_alt_def: "false = \<guillemotleft>False\<guillemotright>"
  by (pred_tac)

subsection {* Unrestriction Laws *}

lemma unrest_true [unrest]: "x \<sharp> true"
  by (pred_tac)

lemma unrest_false [unrest]: "x \<sharp> false"
  by (pred_tac)

lemma unrest_conj [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<and> Q"
  by (pred_tac)

lemma unrest_disj [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<or> Q"
  by (pred_tac)

lemma unrest_impl [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<Rightarrow> Q"
  by (pred_tac)

lemma unrest_iff [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<Leftrightarrow> Q"
  by (pred_tac)

lemma unrest_not [unrest]: "x \<sharp> P \<Longrightarrow> x \<sharp> (\<not> P)"
  by (pred_tac)

lemma unrest_ex_same [unrest]:
  "semi_uvar x \<Longrightarrow> x \<sharp> (\<exists> x \<bullet> P)"
  by pred_tac

lemma unrest_ex_diff [unrest]:
  assumes "x \<bowtie> y" "y \<sharp> P"
  shows "y \<sharp> (\<exists> x \<bullet> P)"
  using assms 
  apply (pred_tac)
  using lens_indep_comm apply fastforce+
done

lemma unrest_all_same [unrest]:
  "semi_uvar x \<Longrightarrow> x \<sharp> (\<forall> x \<bullet> P)"
  by pred_tac

lemma unrest_all_diff [unrest]:
  assumes "x \<bowtie> y" "y \<sharp> P"
  shows "y \<sharp> (\<forall> x \<bullet> P)"
  using assms 
  by (pred_tac, simp_all add: lens_indep_comm)

lemma unrest_shEx [unrest]: 
  assumes "\<And> y. x \<sharp> P(y)"
  shows "x \<sharp> (\<^bold>\<exists> y \<bullet> P(y))"
  using assms by pred_tac

lemma unrest_shAll [unrest]: 
  assumes "\<And> y. x \<sharp> P(y)"
  shows "x \<sharp> (\<^bold>\<forall> y \<bullet> P(y))"
  using assms by pred_tac

lemma unrest_closure [unrest]:
  "x \<sharp> [P]\<^sub>u"
  by pred_tac

subsection {* Substitution Laws *}

lemma subst_true [usubst]: "\<sigma> \<dagger> true = true"                                                                      
  by (pred_tac)

lemma subst_false [usubst]: "\<sigma> \<dagger> false = false"
  by (pred_tac)

lemma subst_not [usubst]: "\<sigma> \<dagger> (\<not> P) = (\<not> \<sigma> \<dagger> P)"
  by (pred_tac)

lemma subst_impl [usubst]: "\<sigma> \<dagger> (P \<Rightarrow> Q) = (\<sigma> \<dagger> P \<Rightarrow> \<sigma> \<dagger> Q)"
  by (pred_tac)

lemma subst_iff [usubst]: "\<sigma> \<dagger> (P \<Leftrightarrow> Q) = (\<sigma> \<dagger> P \<Leftrightarrow> \<sigma> \<dagger> Q)"
  by (pred_tac)

lemma subst_disj [usubst]: "\<sigma> \<dagger> (P \<or> Q) = (\<sigma> \<dagger> P \<or> \<sigma> \<dagger> Q)"
  by (pred_tac)

lemma subst_conj [usubst]: "\<sigma> \<dagger> (P \<and> Q) = (\<sigma> \<dagger> P \<and> \<sigma> \<dagger> Q)"
  by (pred_tac)

lemma subst_closure [usubst]: "\<sigma> \<dagger> [P]\<^sub>u = [P]\<^sub>u"
  by (pred_tac)

lemma subst_shEx [usubst]: "\<sigma> \<dagger> (\<^bold>\<exists> x \<bullet> P(x)) = (\<^bold>\<exists> x \<bullet> \<sigma> \<dagger> P(x))"
  by pred_tac

lemma subst_shAll [usubst]: "\<sigma> \<dagger> (\<^bold>\<forall> x \<bullet> P(x)) = (\<^bold>\<forall> x \<bullet> \<sigma> \<dagger> P(x))"
  by pred_tac

text {* TODO: Generalise the quantifier substitution laws to n-ary substitutions *}

lemma subst_ex_same [usubst]:
  assumes "semi_uvar x"
  shows "(\<exists> x \<bullet> P)\<lbrakk>v/x\<rbrakk> = (\<exists> x \<bullet> P)"
  by (simp add: assms id_subst subst_unrest unrest_ex_same)

lemma subst_ex_indep [usubst]: 
  assumes "x \<bowtie> y" "y \<sharp> v"
  shows "(\<exists> y \<bullet> P)\<lbrakk>v/x\<rbrakk> = (\<exists> y \<bullet> P\<lbrakk>v/x\<rbrakk>)" 
  using assms
  apply (pred_tac)
  using lens_indep_comm apply fastforce+
done
 
lemma subst_all_same [usubst]:
  assumes "semi_uvar x"
  shows "(\<forall> x \<bullet> P)\<lbrakk>v/x\<rbrakk> = (\<forall> x \<bullet> P)"
  by (simp add: assms id_subst subst_unrest unrest_all_same)

lemma subst_all_indep [usubst]: 
  assumes "x \<bowtie> y" "y \<sharp> v"
  shows "(\<forall> y \<bullet> P)\<lbrakk>v/x\<rbrakk> = (\<forall> y \<bullet> P\<lbrakk>v/x\<rbrakk>)" 
  using assms
  by (pred_tac, simp_all add: lens_indep_comm)

subsection {* Predicate Laws *}

text {* Showing that predicates form a Boolean Algebra (under the predicate operators) gives us
        many useful laws. *}

interpretation boolean_algebra diff_upred not_upred conj_upred "op \<le>" "op <" disj_upred false_upred true_upred
  by (unfold_locales, pred_tac+)

lemma refBy_order: "P \<sqsubseteq> Q = `Q \<Rightarrow> P`"
  by (transfer, auto)

lemma conj_idem [simp]: "((P::'\<alpha> upred) \<and> P) = P"
  by pred_tac

lemma disj_idem [simp]: "((P::'\<alpha> upred) \<or> P) = P"
  by pred_tac

lemma conj_comm: "((P::'\<alpha> upred) \<and> Q) = (Q \<and> P)"
  by pred_tac

lemma disj_comm: "((P::'\<alpha> upred) \<or> Q) = (Q \<or> P)"
  by pred_tac

lemma conj_subst: "P = R \<Longrightarrow> ((P::'\<alpha> upred) \<and> Q) = (R \<and> Q)"
  by pred_tac

lemma disj_subst: "P = R \<Longrightarrow> ((P::'\<alpha> upred) \<or> Q) = (R \<or> Q)"
  by pred_tac

lemma conj_assoc:"(((P::'\<alpha> upred) \<and> Q) \<and> S) = (P \<and> (Q \<and> S))"
  by pred_tac

lemma disj_assoc:"(((P::'\<alpha> upred) \<or> Q) \<or> S) = (P \<or> (Q \<or> S))"
  by pred_tac

lemma conj_disj_abs:"((P::'\<alpha> upred) \<and> (P \<or> Q)) = P"
  by pred_tac

lemma disj_conj_abs:"((P::'\<alpha> upred) \<or> (P \<and> Q)) = P"
  by pred_tac

lemma conj_disj_distr:"((P::'\<alpha> upred) \<and> (Q \<or> R)) = ((P \<and> Q) \<or> (P \<and> R))"
  by pred_tac

lemma disj_conj_distr:"((P::'\<alpha> upred) \<or> (Q \<and> R)) = ((P \<or> Q) \<and> (P \<or> R))"
  by pred_tac

lemma true_disj_zero [simp]: 
  "(P \<or> true) = true" "(true \<or> P) = true"
  by (pred_tac) (pred_tac)

lemma true_conj_zero [simp]:
  "(P \<and> false) = false" "(false \<and> P) = false"
  by (pred_tac) (pred_tac)

lemma imp_vacuous [simp]: "(false \<Rightarrow> u) = true"
  by pred_tac

lemma imp_true [simp]: "(p \<Rightarrow> true) = true"
  by pred_tac

lemma true_imp [simp]: "(true \<Rightarrow> p) = p"
  by pred_tac

lemma p_and_not_p [simp]: "(P \<and> \<not> P) = false"
  by pred_tac

lemma p_or_not_p [simp]: "(P \<or> \<not> P) = true"
  by pred_tac

lemma p_imp_p [simp]: "(P \<Rightarrow> P) = true"
  by pred_tac

lemma p_iff_p [simp]: "(P \<Leftrightarrow> P) = true"
  by pred_tac

lemma p_imp_false [simp]: "(P \<Rightarrow> false) = (\<not> P)"
  by pred_tac

lemma not_conj_deMorgans [simp]: "(\<not> ((P::'\<alpha> upred) \<and> Q)) = ((\<not> P) \<or> (\<not> Q))"
  by pred_tac

lemma not_disj_deMorgans [simp]: "(\<not> ((P::'\<alpha> upred) \<or> Q)) = ((\<not> P) \<and> (\<not> Q))"
  by pred_tac

lemma conj_disj_not_abs [simp]: "((P::'\<alpha> upred) \<and> ((\<not>P) \<or> Q)) = (P \<and> Q)"
  by (pred_tac)

lemma double_negation [simp]: "(\<not> \<not> (P::'\<alpha> upred)) = P"
  by (pred_tac)

lemma true_not_false [simp]: "true \<noteq> false" "false \<noteq> true"
  by pred_tac+

lemma closure_conj_distr: "([P]\<^sub>u \<and> [Q]\<^sub>u) = [P \<and> Q]\<^sub>u"
  by pred_tac

lemma closure_imp_distr: "`[P \<Rightarrow> Q]\<^sub>u \<Rightarrow> [P]\<^sub>u \<Rightarrow> [Q]\<^sub>u`"
  by pred_tac

lemma true_iff [simp]: "(P \<Leftrightarrow> true) = P"
  by pred_tac

lemma impl_alt_def: "(P \<Rightarrow> Q) = (\<not> P \<or> Q)"
  by pred_tac

lemma eq_upred_refl [simp]: "(x =\<^sub>u x) = true"
  by pred_tac

lemma eq_upred_sym: "(x =\<^sub>u y) = (y =\<^sub>u x)"
  by pred_tac

lemma conj_eq_in_var_subst:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "uvar x"
  shows "(P \<and> $x =\<^sub>u v) = (P\<lbrakk>v/$x\<rbrakk> \<and> $x =\<^sub>u v)"
  using assms
  by (pred_tac, (metis vwb_lens_wb wb_lens.get_put)+)

lemma conj_eq_out_var_subst:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "uvar x"
  shows "(P \<and> $x\<acute> =\<^sub>u v) = (P\<lbrakk>v/$x\<acute>\<rbrakk> \<and> $x\<acute> =\<^sub>u v)"
  using assms
  by (pred_tac, (metis vwb_lens_wb wb_lens.get_put)+)

lemma shEx_bool [simp]: "shEx P = (P True \<or> P False)"
  by (pred_tac, metis (full_types))

lemma shAll_bool [simp]: "shAll P = (P True \<and> P False)"
  by (pred_tac, metis (full_types))

lemma upred_eq_true [simp]: "(p =\<^sub>u true) = p"
  by pred_tac

lemma upred_eq_false [simp]: "(p =\<^sub>u false) = (\<not> p)"
  by pred_tac

lemma one_point:
  assumes "semi_uvar x" "x \<sharp> v"
  shows "(\<exists> x \<bullet> (P \<and> (var x =\<^sub>u v))) = P\<lbrakk>v/x\<rbrakk>"
  using assms
  by (simp add: upred_defs, transfer, auto)

lemma uvar_assign_exists:
  "uvar x \<Longrightarrow> \<exists> v. b = var_assign x v b"
  by (rule_tac x="var_lookup x b" in exI, simp)

lemma uvar_obtain_assign:
  assumes "uvar x"
  obtains v where "b = var_assign x v b"
  using assms
  by (drule_tac uvar_assign_exists[of _ b], auto)

lemma taut_split_subst:
  assumes "uvar x"
  shows "`P` \<longleftrightarrow> (\<forall> v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`)"
  using assms
  by (pred_tac, metis uvar_assign_exists)

lemma eq_split:
  assumes "`P \<Rightarrow> Q`" "`Q \<Rightarrow> P`"
  shows "P = Q"
  using assms
  by (pred_tac)

lemma subst_bool_split:
  assumes "uvar x"
  shows "`P` = `(P\<lbrakk>false/x\<rbrakk> \<and> P\<lbrakk>true/x\<rbrakk>)`"
proof -
  from assms have "`P` = (\<forall> v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`)"
    by (subst taut_split_subst[of x], auto)
  also have "... = (`P\<lbrakk>\<guillemotleft>True\<guillemotright>/x\<rbrakk>` \<and> `P\<lbrakk>\<guillemotleft>False\<guillemotright>/x\<rbrakk>`)"
    by (metis (mono_tags, lifting))
  also have "... = `(P\<lbrakk>false/x\<rbrakk> \<and> P\<lbrakk>true/x\<rbrakk>)`"
    by (pred_tac)
  finally show ?thesis .
qed
 
lemma taut_iff_eq: 
  "`P \<Leftrightarrow> Q` \<longleftrightarrow> (P = Q)"
  by pred_tac

lemma subst_eq_replace: 
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(p\<lbrakk>u/x\<rbrakk> \<and> u =\<^sub>u v) = (p\<lbrakk>v/x\<rbrakk> \<and> u =\<^sub>u v)"
  by pred_tac

lemma exists_twice: "semi_uvar x \<Longrightarrow> (\<exists> x \<bullet> \<exists> x \<bullet> P) = (\<exists> x \<bullet> P)"
  by (pred_tac)

lemma all_twice: "semi_uvar x \<Longrightarrow> (\<forall> x \<bullet> \<forall> x \<bullet> P) = (\<forall> x \<bullet> P)"
  by (pred_tac)

lemma ex_commute:
  assumes "x \<bowtie> y"
  shows "(\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  using assms
  apply (pred_tac)
  using lens_indep_comm apply fastforce+
done

lemma all_commute:
  assumes "x \<bowtie> y"
  shows "(\<forall> x \<bullet> \<forall> y \<bullet> P) = (\<forall> y \<bullet> \<forall> x \<bullet> P)"
  using assms
  apply (pred_tac)
  using lens_indep_comm apply fastforce+
done

subsection {* Quantifier lifting *}

named_theorems uquant_lift

lemma shEx_lift_conj_1 [uquant_lift]:
  "((\<^bold>\<exists> x \<bullet> P(x)) \<and> Q) = (\<^bold>\<exists> x \<bullet> P(x) \<and> Q)"
  by pred_tac

lemma shEx_lift_conj_2 [uquant_lift]:
  "(P \<and> (\<^bold>\<exists> x \<bullet> Q(x))) = (\<^bold>\<exists> x \<bullet> P \<and> Q(x))"
  by pred_tac

end