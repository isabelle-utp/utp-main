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
  "_uex"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<exists> _ \<bullet> _" [0, 10] 10)
  "_uall"    :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<forall> _ \<bullet> _" [0, 10] 10)
  "_ushEx"   :: "idt \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<exists> _ \<bullet> _" [0, 10] 10)
  "_ushAll"  :: "idt \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ \<bullet> _" [0, 10] 10)
  "_ushBEx"  :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<exists> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ushBAll" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ushGAll" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ | _ \<bullet> _" [0, 0, 10] 10)

translations
  "_uex x P"   == "CONST uex x P"
  "_uall x P"   == "CONST uall x P"
  "\<^bold>\<exists> x \<bullet> P"   == "CONST ushEx (\<lambda> x. P)"
  "\<^bold>\<exists> x \<in> A \<bullet> P" => "\<^bold>\<exists> x \<bullet> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u A \<and> P"
  "\<^bold>\<forall> x \<bullet> P"   == "CONST ushAll (\<lambda> x. P)"
  "\<^bold>\<forall> x \<in> A \<bullet> P" => "\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u A \<Rightarrow> P"
  "\<^bold>\<forall> x | P \<bullet> Q" => "\<^bold>\<forall> x \<bullet> P \<Rightarrow> Q"

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

no_notation inf (infixl "\<sqinter>" 70)
notation inf (infixl "\<squnion>" 70)
no_notation sup (infixl "\<squnion>" 65)
notation sup (infixl "\<sqinter>" 65)

no_notation Inf ("\<Sqinter>_" [900] 900)
notation Inf ("\<Squnion>_" [900] 900)
no_notation Sup ("\<Squnion>_" [900] 900)
notation Sup ("\<Sqinter>_" [900] 900)

no_notation bot ("\<bottom>")
notation bot ("\<top>")
no_notation top ("\<top>")
notation top ("\<bottom>")

no_syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)

text {* We trivially instantiate our refinement class *}

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

lift_definition USUP :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> ('b::complete_lattice, '\<alpha>) uexpr) \<Rightarrow> ('b, '\<alpha>) uexpr"
is "\<lambda> P F b. Sup {\<lbrakk>F x\<rbrakk>\<^sub>eb | x. \<lbrakk>P x\<rbrakk>\<^sub>eb}" .

lift_definition UINF :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> ('b::complete_lattice, '\<alpha>) uexpr) \<Rightarrow> ('b, '\<alpha>) uexpr"
is "\<lambda> P F b. Inf {\<lbrakk>F x\<rbrakk>\<^sub>eb | x. \<lbrakk>P x\<rbrakk>\<^sub>eb}" .

declare USUP_def [upred_defs]
declare UINF_def [upred_defs]

syntax
  "_USup"     :: "idt \<Rightarrow> logic \<Rightarrow> logic"            ("\<Sqinter> _ \<bullet> _" [0, 10] 10)
  "_USup_mem" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Sqinter> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_USUP"     :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Sqinter> _ | _ \<bullet> _" [0, 0, 10] 10)
  "_UInf"     :: "idt \<Rightarrow> logic \<Rightarrow> logic"            ("\<Squnion> _ \<bullet> _" [0, 10] 10)
  "_UInf_mem" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Squnion> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_UINF"     :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Squnion> _ | _ \<bullet> _" [0, 10] 10)

translations
  "\<Sqinter> x | P \<bullet> F" => "CONST USUP (\<lambda> x. P) (\<lambda> x. F)"
  "\<Sqinter> x \<bullet> F"     == "\<Sqinter> x | true \<bullet> F"
  "\<Sqinter> x \<bullet> F"     == "\<Sqinter> x | true \<bullet> F"
  "\<Sqinter> x \<in> A \<bullet> F" => "\<Sqinter> x | \<guillemotleft>x\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Sqinter> x | P \<bullet> F" <= "CONST USUP (\<lambda> x. P) (\<lambda> y. F)" 
  "\<Squnion> x | P \<bullet> F" => "CONST UINF (\<lambda> x. P) (\<lambda> x. F)"
  "\<Squnion> x \<bullet> F"     == "\<Squnion> x | true \<bullet> F"
  "\<Squnion> x \<in> A \<bullet> F" => "\<Squnion> x | \<guillemotleft>x\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Squnion> x | P \<bullet> F" <= "CONST UINF (\<lambda> x. P) (\<lambda> y. F)" 

text {* We also define the other predicate operators *}

lift_definition impl::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> P Q A. P A \<longrightarrow> Q A" .

lift_definition iff_upred ::"'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> P Q A. P A \<longleftrightarrow> Q A" .

lift_definition ex :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> x P b. (\<exists> v. P(put\<^bsub>x\<^esub> b v))" .

lift_definition shEx ::"['\<beta> \<Rightarrow>'\<alpha> upred] \<Rightarrow> '\<alpha> upred" is
"\<lambda> P A. \<exists> x. (P x) A" .

lift_definition all :: "('a, '\<alpha>) uvar \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred" is
"\<lambda> x P b. (\<forall> v. P(put\<^bsub>x\<^esub> b v))" .

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

syntax
  "_uneq"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<noteq>\<^sub>u" 50)
  "_unmem"      :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix "\<notin>\<^sub>u" 50)

translations
  "x \<noteq>\<^sub>u y" == "CONST unot (x =\<^sub>u y)"
  "x \<notin>\<^sub>u A" == "CONST unot (CONST bop (op \<in>) x A)"

subsection {* Proof support *}

text {* We set up a simple tactic with the help of \emph{Eisbach} that applies predicate
        definitions, applies the transfer method to drop down to the core definitions,
        applies extensionality (to remove the resulting lambda term) and the applies auto.
        This simple tactic will suffice to prove most of the standard laws. *}

method pred_tac = ((simp only: upred_defs)? ; (transfer, (rule_tac ext)?, auto simp add: lens_defs fun_eq_iff prod.case_eq_if)?)

declare true_upred_def [upred_defs]
declare false_upred_def [upred_defs]
declare conj_upred_def [upred_defs]
declare disj_upred_def [upred_defs]
declare not_upred_def [upred_defs]
declare diff_upred_def [upred_defs]
declare subst_upd_uvar_def [upred_defs]
declare subst_upd_dvar_def [upred_defs]
declare uexpr_defs [upred_defs]

lemma true_alt_def: "true = \<guillemotleft>True\<guillemotright>"
  by (pred_tac)

lemma false_alt_def: "false = \<guillemotleft>False\<guillemotright>"
  by (pred_tac)

subsection {* Unrestriction Laws *}

lemma unrest_true [unrest]: "x \<sharp> true"
  by (pred_tac)

lemma unrest_false [unrest]: "x \<sharp> false"
  by (pred_tac)

lemma unrest_conj [unrest]: "\<lbrakk> x \<sharp> (P :: '\<alpha> upred); x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<and> Q"
  by (pred_tac)

lemma unrest_disj [unrest]: "\<lbrakk> x \<sharp> (P :: '\<alpha> upred); x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<or> Q"
  by (pred_tac)

lemma unrest_USUP [unrest]: 
  "\<lbrakk> (\<And> i. x \<sharp> P(i)); (\<And> i. x \<sharp> Q(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Sqinter> i | P(i) \<bullet> Q(i))"
  by (simp add: USUP_def, pred_tac)

lemma unrest_UINF [unrest]: 
  "\<lbrakk> (\<And> i. x \<sharp> P(i)); (\<And> i. x \<sharp> Q(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Squnion> i | P(i) \<bullet> Q(i))"
  by (simp add: UINF_def, pred_tac)

lemma unrest_impl [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<Rightarrow> Q"
  by (pred_tac)

lemma unrest_iff [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<Leftrightarrow> Q"
  by (pred_tac)

lemma unrest_not [unrest]: "x \<sharp> (P :: '\<alpha> upred) \<Longrightarrow> x \<sharp> (\<not> P)"
  by (pred_tac)

text {* The sublens proviso can be thought of as membership below. *}

lemma unrest_ex_in [unrest]:
  "\<lbrakk> semi_uvar y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> x \<sharp> (\<exists> y \<bullet> P)"
  by (pred_tac)

declare sublens_refl [simp]
declare lens_plus_ub [simp]
declare lens_plus_right_sublens [simp]
declare comp_wb_lens [simp]
declare comp_mwb_lens [simp]
declare plus_mwb_lens [simp]
  
lemma unrest_ex_diff [unrest]:
  assumes "x \<bowtie> y" "y \<sharp> P"
  shows "y \<sharp> (\<exists> x \<bullet> P)"
  using assms 
  apply (pred_tac)
  using lens_indep_comm apply fastforce+
done

lemma unrest_all_in [unrest]:
  "\<lbrakk> semi_uvar y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> x \<sharp> (\<forall> y \<bullet> P)"
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

lemma subst_sup [usubst]: "\<sigma> \<dagger> (P \<sqinter> Q) = (\<sigma> \<dagger> P \<sqinter> \<sigma> \<dagger> Q)"
  by (pred_tac)

lemma subst_inf [usubst]: "\<sigma> \<dagger> (P \<squnion> Q) = (\<sigma> \<dagger> P \<squnion> \<sigma> \<dagger> Q)"
  by (pred_tac)

lemma subst_USUP [usubst]: "\<sigma> \<dagger> (\<Sqinter> i | P(i) \<bullet> Q(i)) = (\<Sqinter> i | (\<sigma> \<dagger> P(i)) \<bullet> (\<sigma> \<dagger> Q(i)))"
  by (simp add: USUP_def, pred_tac)

lemma subst_UINF [usubst]: "\<sigma> \<dagger> (\<Squnion> i | P(i) \<bullet> Q(i)) = (\<Squnion> i | (\<sigma> \<dagger> P(i)) \<bullet> (\<sigma> \<dagger> Q(i)))"
  by (simp add: UINF_def, pred_tac)

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
  by (simp add: assms id_subst subst_unrest unrest_ex_in)

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
  by (simp add: assms id_subst subst_unrest unrest_all_in)

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

lemma USUP_cong_eq:
  "\<lbrakk> \<And> x. P\<^sub>1(x) = P\<^sub>2(x); \<And> x. `P\<^sub>1(x) \<Rightarrow> Q\<^sub>1(x) =\<^sub>u Q\<^sub>2(x)` \<rbrakk> \<Longrightarrow>
        (\<Sqinter> x | P\<^sub>1(x) \<bullet> Q\<^sub>1(x)) = (\<Sqinter> x | P\<^sub>2(x) \<bullet> Q\<^sub>2(x))"
  by (simp add: USUP_def, pred_tac, metis)

lemma USUP_as_Sup: "(\<Sqinter> P \<in> \<P> \<bullet> P) = \<Sqinter> \<P>"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_tac)
  apply (unfold SUP_def)
  apply (rule cong[of "Sup"])
  apply (auto)
done

lemma USUP_as_Sup_collect: "(\<Sqinter>P\<in>A \<bullet> f(P)) = (\<Sqinter>P\<in>A. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (unfold SUP_def)
  apply (pred_tac)
  apply (simp add: Setcompr_eq_image)
done

lemma USUP_as_Sup_image: "(\<Sqinter> P | \<guillemotleft>P\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> f(P)) = \<Sqinter> (f ` A)"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_tac)
  apply (unfold SUP_def)
  apply (rule cong[of "Sup"])
  apply (auto)
done

lemma UINF_as_Inf: "(\<Squnion> P \<in> \<P> \<bullet> P) = \<Squnion> \<P>"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Inf_uexpr_def)
  apply (pred_tac)
  apply (unfold INF_def)
  apply (rule cong[of "Inf"])
  apply (auto)
done

lemma UINF_as_Inf_collect: "(\<Squnion>P\<in>A \<bullet> f(P)) = (\<Squnion>P\<in>A. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (unfold INF_def)
  apply (pred_tac)
  apply (simp add: Setcompr_eq_image)
done

lemma UINF_as_Inf_image: "(\<Squnion> P \<in> \<P> \<bullet> f(P)) = \<Squnion> (f ` \<P>)"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Inf_uexpr_def)
  apply (pred_tac)
  apply (unfold INF_def)
  apply (rule cong[of "Inf"])
  apply (auto)
done

lemma true_iff [simp]: "(P \<Leftrightarrow> true) = P"
  by pred_tac

lemma impl_alt_def: "(P \<Rightarrow> Q) = (\<not> P \<or> Q)"
  by pred_tac

lemma eq_upred_refl [simp]: "(x =\<^sub>u x) = true"
  by pred_tac

lemma eq_upred_sym: "(x =\<^sub>u y) = (y =\<^sub>u x)"
  by pred_tac

lemma eq_cong_left:
  assumes "uvar x" "$x \<sharp> Q" "$x\<acute> \<sharp> Q" "$x \<sharp> R" "$x\<acute> \<sharp> R"
  shows "(($x\<acute> =\<^sub>u $x \<and> Q) = ($x\<acute> =\<^sub>u $x \<and> R)) \<longleftrightarrow> (Q = R)"
  using assms
  by (pred_tac, (meson mwb_lens_def vwb_lens_mwb weak_lens_def)+)

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

lemma conj_pos_var_subst:
  assumes "uvar x"
  shows "($x \<and> Q) = ($x \<and> Q\<lbrakk>true/$x\<rbrakk>)"
  using assms
  by (pred_tac, metis (full_types) vwb_lens_wb wb_lens.get_put, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma conj_neg_var_subst:
  assumes "uvar x"
  shows "(\<not> $x \<and> Q) = (\<not> $x \<and> Q\<lbrakk>false/$x\<rbrakk>)"
  using assms
  by (pred_tac, metis (full_types) vwb_lens_wb wb_lens.get_put, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma le_pred_refl [simp]:
  fixes x :: "('a::preorder, '\<alpha>) uexpr"
  shows "(x \<le>\<^sub>u x) = true"
  by (pred_tac)

lemma shEx_unbound [simp]: "(\<^bold>\<exists> x \<bullet> P) = P"
  by pred_tac

lemma shEx_bool [simp]: "shEx P = (P True \<or> P False)"
  by (pred_tac, metis (full_types))

lemma shAll_bool [simp]: "shAll P = (P True \<and> P False)"
  by (pred_tac, metis (full_types))

lemma upred_eq_true [simp]: "(p =\<^sub>u true) = p"
  by pred_tac

lemma upred_eq_false [simp]: "(p =\<^sub>u false) = (\<not> p)"
  by pred_tac

lemma conj_var_subst: 
  assumes "uvar x"
  shows "(P \<and> &x =\<^sub>u v) = (P\<lbrakk>v/x\<rbrakk> \<and> &x =\<^sub>u v)"
  using assms
  by (pred_tac, (metis (no_types, lifting) vwb_lens.put_eq)+)

lemma one_point:
  assumes "semi_uvar x" "x \<sharp> v"
  shows "(\<exists> x \<bullet> P \<and> &x =\<^sub>u v) = P\<lbrakk>v/x\<rbrakk>"
  using assms
  by (pred_tac)

lemma uvar_assign_exists:
  "uvar x \<Longrightarrow> \<exists> v. b = put\<^bsub>x\<^esub> b v"
  by (rule_tac x="get\<^bsub>x\<^esub> b" in exI, simp)

lemma uvar_obtain_assign:
  assumes "uvar x"
  obtains v where "b = put\<^bsub>x\<^esub> b v"
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

lemma exists_sub: "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> P)"
  by pred_tac

lemma all_sub: "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> (\<forall> x \<bullet> \<forall> y \<bullet> P) = (\<forall> y \<bullet> P)"
  by pred_tac

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

lemma ex_equiv:
  assumes "x \<approx>\<^sub>L y"
  shows "(\<exists> x \<bullet> P) = (\<exists> y \<bullet> P)"
  using assms
  by (pred_tac, metis (no_types, lifting) lens.select_convs(2))

lemma all_equiv:
  assumes "x \<approx>\<^sub>L y"
  shows "(\<forall> x \<bullet> P) = (\<forall> y \<bullet> P)"
  using assms
  by (pred_tac, metis (no_types, lifting) lens.select_convs(2))

lemma ex_zero:
  "(\<exists> &\<emptyset> \<bullet> P) = P"
  by pred_tac

lemma all_zero:
  "(\<forall> &\<emptyset> \<bullet> P) = P"
  by pred_tac

lemma ex_plus:
  "(\<exists> y,x \<bullet> P) = (\<exists> x \<bullet> \<exists> y \<bullet> P)"
  by pred_tac

lemma all_plus:
  "(\<forall> y,x \<bullet> P) = (\<forall> x \<bullet> \<forall> y \<bullet> P)"
  by pred_tac

lemma closure_all:
  "[P]\<^sub>u = (\<forall> &\<Sigma> \<bullet> P)"
  by pred_tac

lemma unrest_as_exists:
  "vwb_lens x \<Longrightarrow> (x \<sharp> P) \<longleftrightarrow> ((\<exists> x \<bullet> P) = P)"
  by (pred_tac, metis vwb_lens.put_eq)

subsection {* Cylindric algebra *}

lemma C1: "(\<exists> x \<bullet> false) = false"
  by (pred_tac)

lemma C2: "wb_lens x \<Longrightarrow> `P \<Rightarrow> (\<exists> x \<bullet> P)`"
  by (pred_tac, metis wb_lens.get_put)

lemma C3: "mwb_lens x \<Longrightarrow> (\<exists> x \<bullet> (P \<and> (\<exists> x \<bullet> Q))) = ((\<exists> x \<bullet> P) \<and> (\<exists> x \<bullet> Q))"
  by (pred_tac)

lemma C4a: "x \<approx>\<^sub>L y \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  by (pred_tac, metis (no_types, lifting) lens.select_convs(2))+

lemma C4b: "x \<bowtie> y \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  using ex_commute by blast

lemma C5: 
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(&x =\<^sub>u &x) = true"
  by pred_tac

lemma C6:
  assumes "wb_lens x" "x \<bowtie> y" "x \<bowtie> z"
  shows "(&y =\<^sub>u &z) = (\<exists> x \<bullet> &y =\<^sub>u &x \<and> &x =\<^sub>u &z)"
  using assms
  by (pred_tac, (metis lens_indep_def)+)

lemma C7:
  assumes "weak_lens x" "x \<bowtie> y"
  shows "((\<exists> x \<bullet> &x =\<^sub>u &y \<and> P) \<and> (\<exists> x \<bullet> &x =\<^sub>u &y \<and> \<not> P)) = false"
  using assms
  by (pred_tac, simp add: lens_indep_sym)

subsection {* Quantifier lifting *}

named_theorems uquant_lift

lemma shEx_lift_conj_1 [uquant_lift]:
  "((\<^bold>\<exists> x \<bullet> P(x)) \<and> Q) = (\<^bold>\<exists> x \<bullet> P(x) \<and> Q)"
  by pred_tac

lemma shEx_lift_conj_2 [uquant_lift]:
  "(P \<and> (\<^bold>\<exists> x \<bullet> Q(x))) = (\<^bold>\<exists> x \<bullet> P \<and> Q(x))"
  by pred_tac

end