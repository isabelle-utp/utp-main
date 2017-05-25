section {* Alphabetised Predicates *}

theory utp_pred
imports
  utp_expr
  utp_subst
  utp_tactics
begin
  
text {* An alphabetised predicate is a simply a boolean valued expression *}

type_synonym '\<alpha> upred = "(bool, '\<alpha>) uexpr"

translations
  (type) "'\<alpha> upred" <= (type) "(bool, '\<alpha>) uexpr"

subsection {* Predicate syntax *}

text {* We want to remain as close as possible to the mathematical UTP syntax, but also
        want to be conservative with HOL. For this reason we chose not to steal syntax
        from HOL, but where possible use polymorphism to allow selection of the appropriate
        operator (UTP vs. HOL). Thus we will first remove the standard syntax for conjunction,
        disjunction, and negation, and replace these with adhoc overloaded definitions. *}

purge_notation
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

nonterminal idt_list

syntax
  "_idt_el"  :: "idt \<Rightarrow> idt_list" ("_")
  "_idt_list" :: "idt \<Rightarrow> idt_list \<Rightarrow> idt_list" ("(_,/ _)" [0, 1])
  "_uex"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<exists> _ \<bullet> _" [0, 10] 10)
  "_uall"    :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<forall> _ \<bullet> _" [0, 10] 10)
  "_ushEx"   :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<exists> _ \<bullet> _" [0, 10] 10)
  "_ushAll"  :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ \<bullet> _" [0, 10] 10)
  "_ushBEx"  :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<exists> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ushBAll" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ushGAll" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<^bold>\<forall> _ | _ \<bullet> _" [0, 0, 10] 10)
  "_ushGtAll" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>\<forall> _ > _ \<bullet> _" [0, 0, 10] 10)
  "_ushLtAll" :: "idt \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<^bold>\<forall> _ < _ \<bullet> _" [0, 0, 10] 10)

translations
  "_uex x P"                   == "CONST uex x P"
  "_uex (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_uex (x +\<^sub>L y) P"
  "_uall x P"                  == "CONST uall x P"
  "_uall (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_uall (x +\<^sub>L y) P"
  "_ushEx x P"                 == "CONST ushEx (\<lambda> x. P)"
  "\<^bold>\<exists> x \<in> A \<bullet> P"                => "\<^bold>\<exists> x \<bullet> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u A \<and> P"
  "_ushAll x P"                == "CONST ushAll (\<lambda> x. P)"
  "\<^bold>\<forall> x \<in> A \<bullet> P"                => "\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> \<in>\<^sub>u A \<Rightarrow> P"
  "\<^bold>\<forall> x | P \<bullet> Q"                => "\<^bold>\<forall> x \<bullet> P \<Rightarrow> Q"
  "\<^bold>\<forall> x > y \<bullet> P"                => "\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> >\<^sub>u y \<Rightarrow> P"
  "\<^bold>\<forall> x < y \<bullet> P"                => "\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> <\<^sub>u y \<Rightarrow> P"

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

purge_notation Lattices.inf (infixl "\<sqinter>" 70)
notation Lattices.inf (infixl "\<squnion>" 70)
purge_notation Lattices.sup (infixl "\<squnion>" 65)
notation Lattices.sup (infixl "\<sqinter>" 65)
  
purge_notation Inf ("\<Sqinter>_" [900] 900)
notation Inf ("\<Squnion>_" [900] 900)
purge_notation Sup ("\<Squnion>_" [900] 900)
notation Sup ("\<Sqinter>_" [900] 900)
  
purge_notation bot ("\<bottom>")
notation bot ("\<top>")
purge_notation top ("\<top>")
notation top ("\<bottom>")

purge_syntax
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

-- {* Configure transfer law for refinement for the fast relational tactics. *}

theorem upred_ref_iff [uexpr_transfer_laws]:
"(P \<sqsubseteq> Q) = (\<forall>b. \<lbrakk>Q\<rbrakk>\<^sub>e b \<longrightarrow> \<lbrakk>P\<rbrakk>\<^sub>e b)"
apply (transfer)
apply (clarsimp)
done

text {* Next we introduce the lattice operators, which is again done by lifting. *}

instantiation uexpr :: (lattice, type) lattice
begin
  lift_definition sup_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  is "\<lambda>P Q A. Lattices.sup (P A) (Q A)" .
  lift_definition inf_uexpr :: "('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr \<Rightarrow> ('a, 'b) uexpr"
  is "\<lambda>P Q A. Lattices.inf (P A) (Q A)" .
instance
  by (intro_classes) (transfer, auto)+
end

instantiation uexpr :: (bounded_lattice, type) bounded_lattice
begin
  lift_definition bot_uexpr :: "('a, 'b) uexpr" is "\<lambda> A. Orderings.bot" .
  lift_definition top_uexpr :: "('a, 'b) uexpr" is "\<lambda> A. Orderings.top" .
instance
  by (intro_classes) (transfer, auto)+
end

instance uexpr :: (distrib_lattice, type) distrib_lattice
  by (intro_classes) (transfer, rule ext, auto simp add: sup_inf_distrib1)

text {* Finally we show that predicates form a Boolean algebra (under the lattice operators). *}

instance uexpr :: (boolean_algebra, type) boolean_algebra
apply (intro_classes, unfold uexpr_defs; transfer, rule ext)
apply (simp_all add: sup_inf_distrib1 diff_eq)
done

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

syntax
  "_mu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<mu> _ \<bullet> _" [0, 10] 10)
  "_nu" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic" ("\<nu> _ \<bullet> _" [0, 10] 10)

notation gfp ("\<mu>")
notation lfp ("\<nu>")

translations
  "\<nu> X \<bullet> P" == "CONST lfp (\<lambda> X. P)"
  "\<mu> X \<bullet> P" == "CONST gfp (\<lambda> X. P)"

instance uexpr :: (complete_distrib_lattice, type) complete_distrib_lattice
  apply (intro_classes)
  apply (transfer, rule ext, auto)
  using sup_INF apply fastforce
  apply (transfer, rule ext, auto)
  using inf_SUP apply fastforce
done

instance uexpr :: (complete_boolean_algebra, type) complete_boolean_algebra ..

text {* With the lattice operators defined, we can proceed to give definitions for the
        standard predicate operators in terms of them. *}

definition "true_upred  = (Orderings.top :: '\<alpha> upred)"
definition "false_upred = (Orderings.bot :: '\<alpha> upred)"
definition "conj_upred  = (Lattices.inf :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)"
definition "disj_upred  = (Lattices.sup :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)"
definition "not_upred   = (uminus :: '\<alpha> upred \<Rightarrow> '\<alpha> upred)"
definition "diff_upred  = (minus :: '\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> '\<alpha> upred)"

abbreviation Conj_upred :: "'\<alpha> upred set \<Rightarrow> '\<alpha> upred" ("\<And>_" [900] 900) where
"\<And> A \<equiv> \<Squnion> A"

abbreviation Disj_upred :: "'\<alpha> upred set \<Rightarrow> '\<alpha> upred" ("\<Or>_" [900] 900) where
"\<Or> A \<equiv> \<Sqinter> A"

notation
  conj_upred (infixr "\<and>\<^sub>p" 35) and
  disj_upred (infixr "\<or>\<^sub>p" 30)

lift_definition USUP :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> ('b::complete_lattice, '\<alpha>) uexpr) \<Rightarrow> ('b, '\<alpha>) uexpr"
is "\<lambda> P F b. Sup {\<lbrakk>F x\<rbrakk>\<^sub>eb | x. \<lbrakk>P x\<rbrakk>\<^sub>eb}" .

lift_definition UINF :: "('a \<Rightarrow> '\<alpha> upred) \<Rightarrow> ('a \<Rightarrow> ('b::complete_lattice, '\<alpha>) uexpr) \<Rightarrow> ('b, '\<alpha>) uexpr"
is "\<lambda> P F b. Inf {\<lbrakk>F x\<rbrakk>\<^sub>eb | x. \<lbrakk>P x\<rbrakk>\<^sub>eb}" .

declare USUP_def [upred_defs]
declare UINF_def [upred_defs]

syntax
  "_USup"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"            ("\<Or> _ \<bullet> _" [0, 10] 10)
  "_USup"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"            ("\<Sqinter> _ \<bullet> _" [0, 10] 10)
  "_USup_mem" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Or> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_USup_mem" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Sqinter> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_USUP"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Or> _ | _ \<bullet> _" [0, 0, 10] 10)
  "_USUP"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Sqinter> _ | _ \<bullet> _" [0, 0, 10] 10)
  "_UInf"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"            ("\<And> _ \<bullet> _" [0, 10] 10)
  "_UInf"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic"            ("\<Squnion> _ \<bullet> _" [0, 10] 10)
  "_UInf_mem" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<And> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_UInf_mem" :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Squnion> _ \<in> _ \<bullet> _" [0, 10] 10)
  "_UINF"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<And> _ | _ \<bullet> _" [0, 10] 10)
  "_UINF"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("\<Squnion> _ | _ \<bullet> _" [0, 10] 10)

translations
  "\<Sqinter> x | P \<bullet> F" => "CONST USUP (\<lambda> x. P) (\<lambda> x. F)"
  "\<Sqinter> x \<bullet> F"     == "\<Sqinter> x | true \<bullet> F"
  "\<Sqinter> x \<bullet> F"     == "\<Sqinter> x | true \<bullet> F"
  "\<Sqinter> x \<in> A \<bullet> F" => "\<Sqinter> x | \<guillemotleft>x\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Sqinter> x \<in> A \<bullet> F" <= "\<Sqinter> x | \<guillemotleft>y\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Sqinter> x | P \<bullet> F" <= "CONST USUP (\<lambda> y. P) (\<lambda> x. F)"
  "\<Sqinter> x | P \<bullet> F(x)" <= "CONST USUP (\<lambda> x. P) F"
  "\<Squnion> x | P \<bullet> F" => "CONST UINF (\<lambda> x. P) (\<lambda> x. F)"
  "\<Squnion> x \<bullet> F"     == "\<Squnion> x | true \<bullet> F"
  "\<Squnion> x \<in> A \<bullet> F" => "\<Squnion> x | \<guillemotleft>x\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Squnion> x \<in> A \<bullet> F" <= "\<Squnion> x | \<guillemotleft>y\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> F"
  "\<Squnion> x | P \<bullet> F" <= "CONST UINF (\<lambda> y. P) (\<lambda> x. F)"
  "\<Squnion> x | P \<bullet> F(x)" <= "CONST UINF (\<lambda> x. P) F"

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

-- {* Configuration for UTP tactics (see @{theory utp_tactics}). *}

update_uexpr_rep_eq_thms -- {* Reread @{text rep_eq} theorems. *}

declare utp_pred.taut.rep_eq [upred_defs]

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

declare true_upred_def [upred_defs]
declare false_upred_def [upred_defs]
declare conj_upred_def [upred_defs]
declare disj_upred_def [upred_defs]
declare not_upred_def [upred_defs]
declare diff_upred_def [upred_defs]
declare subst_upd_uvar_def [upred_defs]
declare unrest_usubst_def [upred_defs]
declare uexpr_defs [upred_defs]

lemma true_alt_def: "true = \<guillemotleft>True\<guillemotright>"
  by (pred_auto)

lemma false_alt_def: "false = \<guillemotleft>False\<guillemotright>"
  by (pred_auto)

declare true_alt_def[THEN sym,lit_simps]
declare false_alt_def[THEN sym,lit_simps]

abbreviation cond ::
  "('a,'\<alpha>) uexpr \<Rightarrow> '\<alpha> upred \<Rightarrow> ('a,'\<alpha>) uexpr \<Rightarrow> ('a,'\<alpha>) uexpr"
  ("(3_ \<triangleleft> _ \<triangleright>/ _)" [52,0,53] 52)
where "P \<triangleleft> b \<triangleright> Q \<equiv> trop If b P Q"

subsection {* Unrestriction Laws *}

lemma unrest_allE:
  "\<lbrakk> &\<Sigma> \<sharp> P; P = true \<Longrightarrow> Q; P = false \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (pred_auto)
  
lemma unrest_true [unrest]: "x \<sharp> true"
  by (pred_auto)

lemma unrest_false [unrest]: "x \<sharp> false"
  by (pred_auto)

lemma unrest_conj [unrest]: "\<lbrakk> x \<sharp> (P :: '\<alpha> upred); x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<and> Q"
  by (pred_auto)

lemma unrest_disj [unrest]: "\<lbrakk> x \<sharp> (P :: '\<alpha> upred); x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<or> Q"
  by (pred_auto)

lemma unrest_USUP [unrest]:
  "\<lbrakk> (\<And> i. x \<sharp> P(i)); (\<And> i. x \<sharp> Q(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Sqinter> i | P(i) \<bullet> Q(i))"
  by (pred_auto)

lemma unrest_UINF [unrest]:
  "\<lbrakk> (\<And> i. x \<sharp> P(i)); (\<And> i. x \<sharp> Q(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Squnion> i | P(i) \<bullet> Q(i))"
  by (pred_auto)

lemma unrest_USUP_mem [unrest]:
  "\<lbrakk>(\<And> i. i \<in> A \<Longrightarrow> x \<sharp> P(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Sqinter> i\<in>A \<bullet> P(i))"
  by (pred_simp, metis)

lemma unrest_UINF_mem [unrest]:
  "\<lbrakk>(\<And> i. i \<in> A \<Longrightarrow> x \<sharp> P(i)) \<rbrakk> \<Longrightarrow> x \<sharp> (\<Squnion> i\<in>A \<bullet> P(i))"
  by (pred_simp, metis)

lemma unrest_impl [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<Rightarrow> Q"
  by (pred_auto)

lemma unrest_iff [unrest]: "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<Leftrightarrow> Q"
  by (pred_auto)

lemma unrest_not [unrest]: "x \<sharp> (P :: '\<alpha> upred) \<Longrightarrow> x \<sharp> (\<not> P)"
  by (pred_auto)

text {* The sublens proviso can be thought of as membership below. *}

lemma unrest_ex_in [unrest]:
  "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> x \<sharp> (\<exists> y \<bullet> P)"
  by (pred_auto)

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
  apply (pred_auto)
  using lens_indep_comm apply fastforce+
done

lemma unrest_all_in [unrest]:
  "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> x \<sharp> (\<forall> y \<bullet> P)"
  by (pred_auto)

lemma unrest_all_diff [unrest]:
  assumes "x \<bowtie> y" "y \<sharp> P"
  shows "y \<sharp> (\<forall> x \<bullet> P)"
  using assms
  by (pred_simp, simp_all add: lens_indep_comm)

lemma unrest_shEx [unrest]:
  assumes "\<And> y. x \<sharp> P(y)"
  shows "x \<sharp> (\<^bold>\<exists> y \<bullet> P(y))"
  using assms by (pred_auto)

lemma unrest_shAll [unrest]:
  assumes "\<And> y. x \<sharp> P(y)"
  shows "x \<sharp> (\<^bold>\<forall> y \<bullet> P(y))"
  using assms by (pred_auto)

lemma unrest_closure [unrest]:
  "x \<sharp> [P]\<^sub>u"
  by (pred_auto)

subsection {* Substitution Laws *}

text {* Substitution is monotone *}

lemma subst_mono: "P \<sqsubseteq> Q \<Longrightarrow> (\<sigma> \<dagger> P) \<sqsubseteq> (\<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_true [usubst]: "\<sigma> \<dagger> true = true"
  by (pred_auto)

lemma subst_false [usubst]: "\<sigma> \<dagger> false = false"
  by (pred_auto)

lemma subst_not [usubst]: "\<sigma> \<dagger> (\<not> P) = (\<not> \<sigma> \<dagger> P)"
  by (pred_auto)

lemma subst_impl [usubst]: "\<sigma> \<dagger> (P \<Rightarrow> Q) = (\<sigma> \<dagger> P \<Rightarrow> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_iff [usubst]: "\<sigma> \<dagger> (P \<Leftrightarrow> Q) = (\<sigma> \<dagger> P \<Leftrightarrow> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_disj [usubst]: "\<sigma> \<dagger> (P \<or> Q) = (\<sigma> \<dagger> P \<or> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_conj [usubst]: "\<sigma> \<dagger> (P \<and> Q) = (\<sigma> \<dagger> P \<and> \<sigma> \<dagger> Q)"
  by (pred_auto)

declare [[show_sorts]]
    
term "P \<sqinter> Q"
    
lemma subst_sup [usubst]: "\<sigma> \<dagger> (P \<sqinter> Q) = (\<sigma> \<dagger> P \<sqinter> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_inf [usubst]: "\<sigma> \<dagger> (P \<squnion> Q) = (\<sigma> \<dagger> P \<squnion> \<sigma> \<dagger> Q)"
  by (pred_auto)

lemma subst_USUP [usubst]: "\<sigma> \<dagger> (\<Sqinter> i | P(i) \<bullet> Q(i)) = (\<Sqinter> i | (\<sigma> \<dagger> P(i)) \<bullet> (\<sigma> \<dagger> Q(i)))"
  by (pred_auto)

lemma subst_UINF [usubst]: "\<sigma> \<dagger> (\<Squnion> i | P(i) \<bullet> Q(i)) = (\<Squnion> i | (\<sigma> \<dagger> P(i)) \<bullet> (\<sigma> \<dagger> Q(i)))"
  by (pred_auto)

lemma subst_closure [usubst]: "\<sigma> \<dagger> [P]\<^sub>u = [P]\<^sub>u"
  by (pred_auto)

lemma subst_shEx [usubst]: "\<sigma> \<dagger> (\<^bold>\<exists> x \<bullet> P(x)) = (\<^bold>\<exists> x \<bullet> \<sigma> \<dagger> P(x))"
  by (pred_auto)

lemma subst_shAll [usubst]: "\<sigma> \<dagger> (\<^bold>\<forall> x \<bullet> P(x)) = (\<^bold>\<forall> x \<bullet> \<sigma> \<dagger> P(x))"
  by (pred_auto)

text {* TODO: Generalise the quantifier substitution laws to n-ary substitutions *}

lemma subst_ex_same [usubst]:
  "mwb_lens x \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> (\<exists> x \<bullet> P) = \<sigma> \<dagger> (\<exists> x \<bullet> P)"
  by (pred_auto)

lemma subst_ex_indep [usubst]:
  assumes "x \<bowtie> y" "y \<sharp> v"
  shows "(\<exists> y \<bullet> P)\<lbrakk>v/x\<rbrakk> = (\<exists> y \<bullet> P\<lbrakk>v/x\<rbrakk>)"
  using assms
  apply (pred_auto)
  using lens_indep_comm apply fastforce+
done

lemma subst_ex_unrest [usubst]:
  "x \<sharp> \<sigma> \<Longrightarrow> \<sigma> \<dagger> (\<exists> x \<bullet> P) = (\<exists> x \<bullet> \<sigma> \<dagger> P)"
  by (pred_auto)

lemma subst_all_same [usubst]:
  "mwb_lens x \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s v) \<dagger> (\<forall> x \<bullet> P) = \<sigma> \<dagger> (\<forall> x \<bullet> P)"
  by (simp add: id_subst subst_unrest unrest_all_in)

lemma subst_all_indep [usubst]:
  assumes "x \<bowtie> y" "y \<sharp> v"
  shows "(\<forall> y \<bullet> P)\<lbrakk>v/x\<rbrakk> = (\<forall> y \<bullet> P\<lbrakk>v/x\<rbrakk>)"
  using assms
  by (pred_simp, simp_all add: lens_indep_comm)

subsection {* Predicate Laws *}

text {* Showing that predicates form a Boolean Algebra (under the predicate operators) gives us
        many useful laws. *}

interpretation boolean_algebra diff_upred not_upred conj_upred "op \<le>" "op <"
  disj_upred false_upred true_upred
  by (unfold_locales; pred_auto)

lemma taut_true [simp]: "`true`"
  by (pred_auto)

lemma taut_false [simp]: "`false` = False"
  by (pred_auto)

lemma upred_eval_taut:
  "`P\<lbrakk>\<guillemotleft>b\<guillemotright>/&\<Sigma>\<rbrakk>` = \<lbrakk>P\<rbrakk>\<^sub>eb"
  by (pred_auto)
    
lemma refBy_order: "P \<sqsubseteq> Q = `Q \<Rightarrow> P`"
  by (pred_auto)

lemma conj_idem [simp]: "((P::'\<alpha> upred) \<and> P) = P"
  by (pred_auto)

lemma disj_idem [simp]: "((P::'\<alpha> upred) \<or> P) = P"
  by (pred_auto)

lemma conj_comm: "((P::'\<alpha> upred) \<and> Q) = (Q \<and> P)"
  by (pred_auto)

lemma disj_comm: "((P::'\<alpha> upred) \<or> Q) = (Q \<or> P)"
  by (pred_auto)

lemma conj_subst: "P = R \<Longrightarrow> ((P::'\<alpha> upred) \<and> Q) = (R \<and> Q)"
  by (pred_auto)

lemma disj_subst: "P = R \<Longrightarrow> ((P::'\<alpha> upred) \<or> Q) = (R \<or> Q)"
  by (pred_auto)

lemma conj_assoc:"(((P::'\<alpha> upred) \<and> Q) \<and> S) = (P \<and> (Q \<and> S))"
  by (pred_auto)

lemma disj_assoc:"(((P::'\<alpha> upred) \<or> Q) \<or> S) = (P \<or> (Q \<or> S))"
  by (pred_auto)

lemma conj_disj_abs:"((P::'\<alpha> upred) \<and> (P \<or> Q)) = P"
  by (pred_auto)

lemma disj_conj_abs:"((P::'\<alpha> upred) \<or> (P \<and> Q)) = P"
  by (pred_auto)

lemma conj_disj_distr:"((P::'\<alpha> upred) \<and> (Q \<or> R)) = ((P \<and> Q) \<or> (P \<and> R))"
  by (pred_auto)

lemma disj_conj_distr:"((P::'\<alpha> upred) \<or> (Q \<and> R)) = ((P \<or> Q) \<and> (P \<or> R))"
  by (pred_auto)

lemma true_disj_zero [simp]:
  "(P \<or> true) = true" "(true \<or> P) = true"
  by (pred_auto)+

lemma true_conj_zero [simp]:
  "(P \<and> false) = false" "(false \<and> P) = false"
  by (pred_auto)+

lemma imp_vacuous [simp]: "(false \<Rightarrow> u) = true"
  by (pred_auto)

lemma imp_true [simp]: "(p \<Rightarrow> true) = true"
  by (pred_auto)

lemma true_imp [simp]: "(true \<Rightarrow> p) = p"
  by (pred_auto)

lemma impl_mp1 [simp]: "(P \<and> (P \<Rightarrow> Q)) = (P \<and> Q)"
  by (pred_auto)

lemma impl_mp2 [simp]: "((P \<Rightarrow> Q) \<and> P) = (Q \<and> P)"
  by (pred_auto)

lemma impl_adjoin: "((P \<Rightarrow> Q) \<and> R) = ((P \<and> R \<Rightarrow> Q \<and> R) \<and> R)"
  by (pred_auto)

lemma impl_refine_intro:
  "\<lbrakk> Q\<^sub>1 \<sqsubseteq> P\<^sub>1; P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2) \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<Rightarrow> P\<^sub>2) \<sqsubseteq> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)"
  by (pred_auto)

lemma impl_disjI: "\<lbrakk> `P \<Rightarrow> R`; `Q \<Rightarrow> R` \<rbrakk> \<Longrightarrow> `(P \<or> Q) \<Rightarrow> R`"
  by (rel_auto)

lemma conditional_iff:
  "(P \<Rightarrow> Q) = (P \<Rightarrow> R) \<longleftrightarrow> `P \<Rightarrow> (Q \<Leftrightarrow> R)`"
  by (pred_auto)

lemma p_and_not_p [simp]: "(P \<and> \<not> P) = false"
  by (pred_auto)

lemma p_or_not_p [simp]: "(P \<or> \<not> P) = true"
  by (pred_auto)

lemma p_imp_p [simp]: "(P \<Rightarrow> P) = true"
  by (pred_auto)

lemma p_iff_p [simp]: "(P \<Leftrightarrow> P) = true"
  by (pred_auto)

lemma p_imp_false [simp]: "(P \<Rightarrow> false) = (\<not> P)"
  by (pred_auto)

lemma not_conj_deMorgans [simp]: "(\<not> ((P::'\<alpha> upred) \<and> Q)) = ((\<not> P) \<or> (\<not> Q))"
  by (pred_auto)

lemma not_disj_deMorgans [simp]: "(\<not> ((P::'\<alpha> upred) \<or> Q)) = ((\<not> P) \<and> (\<not> Q))"
  by (pred_auto)

lemma conj_disj_not_abs [simp]: "((P::'\<alpha> upred) \<and> ((\<not>P) \<or> Q)) = (P \<and> Q)"
  by (pred_auto)

lemma subsumption1:
  "`P \<Rightarrow> Q` \<Longrightarrow> (P \<or> Q) = Q"
  by (pred_auto)

lemma subsumption2:
  "`Q \<Rightarrow> P` \<Longrightarrow> (P \<or> Q) = P"
  by (pred_auto)

lemma neg_conj_cancel1: "(\<not> P \<and> (P \<or> Q)) = (\<not> P \<and> Q :: '\<alpha> upred)"
  by (pred_auto)

lemma neg_conj_cancel2: "(\<not> Q \<and> (P \<or> Q)) = (\<not> Q \<and> P :: '\<alpha> upred)"
  by (pred_auto)

lemma double_negation [simp]: "(\<not> \<not> (P::'\<alpha> upred)) = P"
  by (pred_auto)

lemma true_not_false [simp]: "true \<noteq> false" "false \<noteq> true"
  by (pred_auto)+

lemma closure_conj_distr: "([P]\<^sub>u \<and> [Q]\<^sub>u) = [P \<and> Q]\<^sub>u"
  by (pred_auto)

lemma closure_imp_distr: "`[P \<Rightarrow> Q]\<^sub>u \<Rightarrow> [P]\<^sub>u \<Rightarrow> [Q]\<^sub>u`"
  by (pred_auto)

lemma uinf_or:
  fixes P Q :: "'\<alpha> upred"
  shows "(P \<sqinter> Q) = (P \<or> Q)"
  by (pred_auto)

lemma usup_and:
  fixes P Q :: "'\<alpha> upred"
  shows "(P \<squnion> Q) = (P \<and> Q)"
  by (pred_auto)

lemma UINF_alt_def:
  "(\<Sqinter> i | A(i) \<bullet> P(i)) = (\<Sqinter> i \<bullet> A(i) \<and> P(i))"
  by (rel_auto)
    
lemma USUP_true [simp]: "(\<Squnion> P | F(P) \<bullet> true) = true"
  by (pred_auto)

lemma UINF_mem_UNIV [simp]: "(\<Sqinter> x\<in>UNIV \<bullet> P(x)) = (\<Sqinter> x \<bullet> P(x))"
  by (pred_auto)

lemma USUP_mem_UNIV [simp]: "(\<Squnion> x\<in>UNIV \<bullet> P(x)) = (\<Squnion> x \<bullet> P(x))"
  by (pred_auto)

lemma USUP_false [simp]: "(\<Squnion> i \<bullet> false) = false"
  by (pred_simp)

lemma UINF_true [simp]: "(\<Sqinter> i \<bullet> true) = true"
  by (pred_simp)

lemma UINF_mem_true [simp]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter> i\<in>A \<bullet> true) = true"
  by (pred_auto)

lemma UINF_false [simp]: "(\<Sqinter> i | P(i) \<bullet> false) = false"
  by (pred_auto)

lemma USUP_cong_eq:
  "\<lbrakk> \<And> x. P\<^sub>1(x) = P\<^sub>2(x); \<And> x. `P\<^sub>1(x) \<Rightarrow> Q\<^sub>1(x) =\<^sub>u Q\<^sub>2(x)` \<rbrakk> \<Longrightarrow>
        (\<Sqinter> x | P\<^sub>1(x) \<bullet> Q\<^sub>1(x)) = (\<Sqinter> x | P\<^sub>2(x) \<bullet> Q\<^sub>2(x))"
 by (unfold USUP_def, pred_simp, metis)

lemma USUP_as_Sup: "(\<Sqinter> P \<in> \<P> \<bullet> P) = \<Sqinter> \<P>"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (rule cong[of "Sup"])
  apply (auto)
done

lemma USUP_as_Sup_collect: "(\<Sqinter>P\<in>A \<bullet> f(P)) = (\<Sqinter>P\<in>A. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (simp add: Setcompr_eq_image)
done

lemma USUP_as_Sup_collect': "(\<Sqinter>P \<bullet> f(P)) = (\<Sqinter>P. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (simp add: full_SetCompr_eq)
done

lemma USUP_as_Sup_image: "(\<Sqinter> P | \<guillemotleft>P\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> f(P)) = \<Sqinter> (f ` A)"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (rule cong[of "Sup"])
  apply (auto)
done

lemma UINF_as_Inf: "(\<Squnion> P \<in> \<P> \<bullet> P) = \<Squnion> \<P>"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Inf_uexpr_def)
  apply (pred_simp)
  apply (rule cong[of "Inf"])
  apply (auto)
done

lemma UINF_as_Inf_collect: "(\<Squnion>P\<in>A \<bullet> f(P)) = (\<Squnion>P\<in>A. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (simp add: Setcompr_eq_image)
done

lemma UINF_as_Inf_collect': "(\<Squnion>P \<bullet> f(P)) = (\<Squnion>P. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (simp add: full_SetCompr_eq)
done

lemma UINF_as_Inf_image: "(\<Squnion> P \<in> \<P> \<bullet> f(P)) = \<Squnion> (f ` \<P>)"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Inf_uexpr_def)
  apply (pred_simp)
  apply (rule cong[of "Inf"])
  apply (auto)
done

lemma USUP_image_eq [simp]: "USUP (\<lambda>i. \<guillemotleft>i\<guillemotright> \<in>\<^sub>u \<guillemotleft>f ` A\<guillemotright>) g = (\<Sqinter> i\<in>A \<bullet> g(f(i)))"
  by (pred_simp, rule_tac cong[of Sup Sup], auto)

lemma UINF_image_eq [simp]: "UINF (\<lambda>i. \<guillemotleft>i\<guillemotright> \<in>\<^sub>u \<guillemotleft>f ` A\<guillemotright>) g = (\<Squnion> i\<in>A \<bullet> g(f(i)))"
  by (pred_simp, rule_tac cong[of Inf Inf], auto)

lemma subst_continuous [usubst]: "\<sigma> \<dagger> (\<Sqinter> A) = (\<Sqinter> {\<sigma> \<dagger> P | P. P \<in> A})"
  by (simp add: USUP_as_Sup[THEN sym] usubst setcompr_eq_image)

lemma not_USUP: "(\<not> (\<Sqinter> i\<in>A\<bullet> P(i))) = (\<Squnion> i\<in>A\<bullet> \<not> P(i))"
  by (pred_auto)

lemma not_UINF: "(\<not> (\<Squnion> i\<in>A\<bullet> P(i))) = (\<Sqinter> i\<in>A\<bullet> \<not> P(i))"
  by (pred_auto)

lemma USUP_empty [simp]: "(\<Sqinter> i \<in> {} \<bullet> P(i)) = false"
  by (pred_auto)

lemma USUP_insert [simp]: "(\<Sqinter> i\<in>insert x xs \<bullet> P(i)) = (P(x) \<sqinter> (\<Sqinter> i\<in>xs \<bullet> P(i)))"
  apply (pred_simp)
  apply (subst Sup_insert[THEN sym])
  apply (rule_tac cong[of Sup Sup])
  apply (auto)
done

lemma UINF_empty [simp]: "(\<Squnion> i \<in> {} \<bullet> P(i)) = true"
  by (pred_auto)

lemma UINF_insert [simp]: "(\<Squnion> i\<in>insert x xs \<bullet> P(i)) = (P(x) \<squnion> (\<Squnion> i\<in>xs \<bullet> P(i)))"
  apply (pred_simp)
  apply (subst Inf_insert[THEN sym])
  apply (rule_tac cong[of Inf Inf])
  apply (auto)
done

lemma conj_USUP_dist:
  "(P \<and> (\<Sqinter> Q\<in>S \<bullet> F(Q))) = (\<Sqinter> Q\<in>S \<bullet> P \<and> F(Q))"
  by (simp add: upred_defs bop.rep_eq lit.rep_eq, pred_auto)

lemma disj_USUP_dist:
  "S \<noteq> {} \<Longrightarrow> (P \<or> (\<Sqinter> Q\<in>S \<bullet> F(Q))) = (\<Sqinter> Q\<in>S \<bullet> P \<or> F(Q))"
  by (simp add: upred_defs bop.rep_eq lit.rep_eq, pred_auto)

lemma conj_UINF_dist:
  "S \<noteq> {} \<Longrightarrow> (P \<and> (\<Squnion> Q\<in>S \<bullet> F(Q))) = (\<Squnion> Q\<in>S \<bullet> P \<and> F(Q))"
  by (subst uexpr_eq_iff, auto simp add: conj_upred_def UINF.rep_eq inf_uexpr.rep_eq bop.rep_eq lit.rep_eq)

lemma UINF_conj_UINF: "((\<Squnion> P \<in> A \<bullet> F(P)) \<and> (\<Squnion> P \<in> A \<bullet> G(P))) = (\<Squnion> P \<in> A \<bullet> F(P) \<and> G(P))"
  by (simp add: upred_defs bop.rep_eq lit.rep_eq, pred_auto)

lemma UINF_all_cong:
  assumes "\<And> P. F(P) = G(P)"
  shows "(\<Sqinter> P \<bullet> F(P)) = (\<Sqinter> P \<bullet> G(P))"
  by (simp add: USUP_as_Sup_collect assms)

lemma UINF_cong:
  assumes "\<And> P. P \<in> A \<Longrightarrow> F(P) = G(P)"
  shows "(\<Sqinter> P\<in>A \<bullet> F(P)) = (\<Sqinter> P\<in>A \<bullet> G(P))"
  by (simp add: USUP_as_Sup_collect assms)

lemma USUP_cong:
  assumes "\<And> P. P \<in> A \<Longrightarrow> F(P) = G(P)"
  shows "(\<Squnion> P\<in>A \<bullet> F(P)) = (\<Squnion> P\<in>A \<bullet> G(P))"
  by (simp add: UINF_as_Inf_collect assms)

lemma UINF_subset_mono: "A \<subseteq> B \<Longrightarrow> (\<Sqinter> P\<in>B \<bullet> F(P)) \<sqsubseteq> (\<Sqinter> P\<in>A \<bullet> F(P))"
  by (simp add: SUP_subset_mono USUP_as_Sup_collect)

lemma USUP_subset_mono: "A \<subseteq> B \<Longrightarrow> (\<Squnion> P\<in>A \<bullet> F(P)) \<sqsubseteq> (\<Squnion> P\<in>B \<bullet> F(P))"
  by (simp add: INF_superset_mono UINF_as_Inf_collect)

lemma UINF_impl: "(\<Sqinter> P\<in>A \<bullet> F(P) \<Rightarrow> G(P)) = ((\<Squnion> P\<in>A \<bullet> F(P)) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> G(P)))"
  by (pred_auto)

lemma UINF_all_nats [simp]:
  fixes P :: "nat \<Rightarrow> '\<alpha> upred"
  shows "(\<Sqinter> n \<bullet> \<Sqinter> i\<in>{0..n} \<bullet> P(i)) = (\<Sqinter> i\<in>{0..} \<bullet> P(i))"
  by (pred_auto)

lemma mu_id: "(\<mu> X \<bullet> X) = true"
  by (simp add: antisym gfp_upperbound)

lemma mu_const: "(\<mu> X \<bullet> P) = P"
  by (simp add: gfp_const)

lemma nu_id: "(\<nu> X \<bullet> X) = false"
  by (simp add: lfp_lowerbound utp_pred.bot.extremum_uniqueI)

lemma nu_const: "(\<nu> X \<bullet> P) = P"
  by (simp add: lfp_const)

text {* Obtaining termination proofs via approximation chains. Theorems and proofs adapted
  from chapter 2, page 63 of the UTP book.  *}

lemma mu_refine_intro:
  assumes "(C \<Rightarrow> S) \<sqsubseteq> F(C \<Rightarrow> S)" "`C \<Rightarrow> (\<mu> F \<Leftrightarrow> \<nu> F)`"
  shows "(C \<Rightarrow> S) \<sqsubseteq> \<mu> F"
proof -
  from assms have "(C \<Rightarrow> S) \<sqsubseteq> \<nu> F"
    by (simp add: lfp_lowerbound)
  with assms show ?thesis
    by (pred_auto)
qed

type_synonym 'a chain = "nat \<Rightarrow> 'a upred"

definition chain :: "'a chain \<Rightarrow> bool" where
  "chain Y = ((Y 0 = false) \<and> (\<forall> i. Y (Suc i) \<sqsubseteq> Y i))"

lemma chain0 [simp]: "chain Y \<Longrightarrow> Y 0 = false"
  by (simp add:chain_def)

lemma chainI:
  assumes "Y 0 = false" "\<And> i. Y (Suc i) \<sqsubseteq> Y i"
  shows "chain Y"
  using assms by (auto simp add: chain_def)

lemma chainE:
  assumes "chain Y" "\<And> i. \<lbrakk> Y 0 = false; Y (Suc i) \<sqsubseteq> Y i \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms by (simp add: chain_def)

lemma L274:
  assumes "\<forall> n. ((E n \<and>\<^sub>p X) = (E n \<and> Y))"
  shows "(\<Sqinter> (range E) \<and> X) = (\<Sqinter> (range E) \<and> Y)"
  using assms by (pred_auto)

text {* Constructive chains *}

definition constr ::
  "('a upred \<Rightarrow> 'a upred) \<Rightarrow> 'a chain \<Rightarrow> bool" where
"constr F E \<longleftrightarrow> chain E \<and> (\<forall> X n. ((F(X) \<and> E(n + 1)) = (F(X \<and> E(n)) \<and> E (n + 1))))"

text {* This lemma gives a way of showing that there is a unique fixed-point when
        the predicate function can be built using a constructive function F
        over an approximation chain E *}

lemma chain_pred_terminates:
  assumes "constr F E" "mono F"
  shows "(\<Sqinter> (range E) \<and> \<mu> F) = (\<Sqinter> (range E) \<and> \<nu> F)"
proof -
  from assms have "\<forall> n. (E n \<and> \<mu> F) = (E n \<and> \<nu> F)"
  proof (rule_tac allI)
    fix n
    from assms show "(E n \<and> \<mu> F) = (E n \<and> \<nu> F)"
    proof (induct n)
      case 0 thus ?case by (simp add: constr_def)
    next
      case (Suc n)
      note hyp = this
      thus ?case
      proof -
        have "(E (n + 1) \<and> \<mu> F) = (E (n + 1) \<and> F (\<mu> F))"
          using gfp_unfold[OF hyp(3), THEN sym] by (simp add: constr_def)
        also from hyp have "... = (E (n + 1) \<and> F (E n \<and> \<mu> F))"
          by (metis conj_comm constr_def)
        also from hyp have "... = (E (n + 1) \<and> F (E n \<and> \<nu> F))"
          by simp
        also from hyp have "... = (E (n + 1) \<and> \<nu> F)"
          by (metis (no_types, lifting) conj_comm constr_def lfp_unfold)
        ultimately show ?thesis
          by simp
      qed
    qed
  qed
  thus ?thesis
    by (auto intro: L274)
qed

theorem constr_fp_uniq:
  assumes "constr F E" "mono F" "\<Sqinter> (range E) = C"
  shows "(C \<and> \<mu> F) = (C \<and> \<nu> F)"
  using assms(1) assms(2) assms(3) chain_pred_terminates by blast

lemma true_iff [simp]: "(P \<Leftrightarrow> true) = P"
  by (pred_auto)

lemma impl_alt_def: "(P \<Rightarrow> Q) = (\<not> P \<or> Q)"
  by (pred_auto)

lemma eq_upred_refl [simp]: "(x =\<^sub>u x) = true"
  by (pred_auto)

lemma eq_upred_sym: "(x =\<^sub>u y) = (y =\<^sub>u x)"
  by (pred_auto)

lemma eq_cong_left:
  assumes "vwb_lens x" "$x \<sharp> Q" "$x\<acute> \<sharp> Q" "$x \<sharp> R" "$x\<acute> \<sharp> R"
  shows "(($x\<acute> =\<^sub>u $x \<and> Q) = ($x\<acute> =\<^sub>u $x \<and> R)) \<longleftrightarrow> (Q = R)"
  using assms
  by (pred_simp, (meson mwb_lens_def vwb_lens_mwb weak_lens_def)+)

lemma conj_eq_in_var_subst:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "vwb_lens x"
  shows "(P \<and> $x =\<^sub>u v) = (P\<lbrakk>v/$x\<rbrakk> \<and> $x =\<^sub>u v)"
  using assms
  by (pred_simp, (metis vwb_lens_wb wb_lens.get_put)+)

lemma conj_eq_out_var_subst:
  fixes x :: "('a, '\<alpha>) uvar"
  assumes "vwb_lens x"
  shows "(P \<and> $x\<acute> =\<^sub>u v) = (P\<lbrakk>v/$x\<acute>\<rbrakk> \<and> $x\<acute> =\<^sub>u v)"
  using assms
  by (pred_simp, (metis vwb_lens_wb wb_lens.get_put)+)

lemma conj_pos_var_subst:
  assumes "vwb_lens x"
  shows "($x \<and> Q) = ($x \<and> Q\<lbrakk>true/$x\<rbrakk>)"
  using assms
  by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma conj_neg_var_subst:
  assumes "vwb_lens x"
  shows "(\<not> $x \<and> Q) = (\<not> $x \<and> Q\<lbrakk>false/$x\<rbrakk>)"
  using assms
  by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma le_pred_refl [simp]:
  fixes x :: "('a::preorder, '\<alpha>) uexpr"
  shows "(x \<le>\<^sub>u x) = true"
  by (pred_auto)

lemma shEx_unbound [simp]: "(\<^bold>\<exists> x \<bullet> P) = P"
  by (pred_auto)

lemma shEx_bool [simp]: "shEx P = (P True \<or> P False)"
  by (pred_simp, metis (full_types))

lemma shEx_commute: "(\<^bold>\<exists> x \<bullet> \<^bold>\<exists> y \<bullet> P x y) = (\<^bold>\<exists> y \<bullet> \<^bold>\<exists> x \<bullet> P x y)"
  by (pred_auto)

lemma shEx_cong: "\<lbrakk> \<And> x. P x = Q x \<rbrakk> \<Longrightarrow> shEx P = shEx Q"
  by (pred_auto)

lemma shAll_unbound [simp]: "(\<^bold>\<forall> x \<bullet> P) = P"
  by (pred_auto)

lemma shAll_bool [simp]: "shAll P = (P True \<and> P False)"
  by (pred_simp, metis (full_types))

lemma shAll_cong: "\<lbrakk> \<And> x. P x = Q x \<rbrakk> \<Longrightarrow> shAll P = shAll Q"
  by (pred_auto)

lemma upred_eq_true [simp]: "(p =\<^sub>u true) = p"
  by (pred_auto)

lemma upred_eq_false [simp]: "(p =\<^sub>u false) = (\<not> p)"
  by (pred_auto)

lemma upred_true_eq [simp]: "(true =\<^sub>u p) = p"
  by (pred_auto)

lemma upred_false_eq [simp]: "(false =\<^sub>u p) = (\<not> p)"
  by (pred_auto)

lemma conj_var_subst:
  assumes "vwb_lens x"
  shows "(P \<and> var x =\<^sub>u v) = (P\<lbrakk>v/x\<rbrakk> \<and> var x =\<^sub>u v)"
  using assms
  by (pred_simp, (metis (full_types) vwb_lens_def wb_lens.get_put)+)

lemma one_point:
  assumes "mwb_lens x" "x \<sharp> v"
  shows "(\<exists> x \<bullet> P \<and> var x =\<^sub>u v) = P\<lbrakk>v/x\<rbrakk>"
  using assms
  by (pred_auto)

lemma uvar_assign_exists:
  "vwb_lens x \<Longrightarrow> \<exists> v. b = put\<^bsub>x\<^esub> b v"
  by (rule_tac x="get\<^bsub>x\<^esub> b" in exI, simp)

lemma uvar_obtain_assign:
  assumes "vwb_lens x"
  obtains v where "b = put\<^bsub>x\<^esub> b v"
  using assms
  by (drule_tac uvar_assign_exists[of _ b], auto)

lemma eq_split_subst:
  assumes "vwb_lens x"
  shows "(P = Q) \<longleftrightarrow> (\<forall> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> = Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)"
  using assms
  by (pred_simp, metis uvar_assign_exists)

lemma eq_split_substI:
  assumes "vwb_lens x" "\<And> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> = Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>"
  shows "P = Q"
  using assms(1) assms(2) eq_split_subst by blast

lemma taut_split_subst:
  assumes "vwb_lens x"
  shows "`P` \<longleftrightarrow> (\<forall> v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`)"
  using assms
  by (pred_simp, metis uvar_assign_exists)

lemma eq_split:
  assumes "`P \<Rightarrow> Q`" "`Q \<Rightarrow> P`"
  shows "P = Q"
  using assms
  by (pred_auto)

lemma bool_eq_splitI:
  assumes "vwb_lens x" "P\<lbrakk>true/x\<rbrakk> = Q\<lbrakk>true/x\<rbrakk>" "P\<lbrakk>false/x\<rbrakk> = Q\<lbrakk>false/x\<rbrakk>"
  shows "P = Q"
  by (metis (full_types) assms eq_split_subst false_alt_def true_alt_def)

lemma subst_bool_split:
  assumes "vwb_lens x"
  shows "`P` = `(P\<lbrakk>false/x\<rbrakk> \<and> P\<lbrakk>true/x\<rbrakk>)`"
proof -
  from assms have "`P` = (\<forall> v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`)"
    by (subst taut_split_subst[of x], auto)
  also have "... = (`P\<lbrakk>\<guillemotleft>True\<guillemotright>/x\<rbrakk>` \<and> `P\<lbrakk>\<guillemotleft>False\<guillemotright>/x\<rbrakk>`)"
    by (metis (mono_tags, lifting))
  also have "... = `(P\<lbrakk>false/x\<rbrakk> \<and> P\<lbrakk>true/x\<rbrakk>)`"
    by (pred_auto)
  finally show ?thesis .
qed

lemma taut_iff_eq:
  "`P \<Leftrightarrow> Q` \<longleftrightarrow> (P = Q)"
  by (pred_auto)

lemma subst_eq_replace:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(p\<lbrakk>u/x\<rbrakk> \<and> u =\<^sub>u v) = (p\<lbrakk>v/x\<rbrakk> \<and> u =\<^sub>u v)"
  by (pred_auto)

lemma exists_twice: "mwb_lens x \<Longrightarrow> (\<exists> x \<bullet> \<exists> x \<bullet> P) = (\<exists> x \<bullet> P)"
  by (pred_auto)

lemma all_twice: "mwb_lens x \<Longrightarrow> (\<forall> x \<bullet> \<forall> x \<bullet> P) = (\<forall> x \<bullet> P)"
  by (pred_auto)

lemma exists_sub: "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> P)"
  by (pred_auto)

lemma all_sub: "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> (\<forall> x \<bullet> \<forall> y \<bullet> P) = (\<forall> y \<bullet> P)"
  by (pred_auto)

lemma ex_commute:
  assumes "x \<bowtie> y"
  shows "(\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  using assms
  apply (pred_auto)
  using lens_indep_comm apply fastforce+
done

lemma all_commute:
  assumes "x \<bowtie> y"
  shows "(\<forall> x \<bullet> \<forall> y \<bullet> P) = (\<forall> y \<bullet> \<forall> x \<bullet> P)"
  using assms
  apply (pred_auto)
  using lens_indep_comm apply fastforce+
done

lemma ex_equiv:
  assumes "x \<approx>\<^sub>L y"
  shows "(\<exists> x \<bullet> P) = (\<exists> y \<bullet> P)"
  using assms
  by (pred_simp, metis (no_types, lifting) lens.select_convs(2))

lemma all_equiv:
  assumes "x \<approx>\<^sub>L y"
  shows "(\<forall> x \<bullet> P) = (\<forall> y \<bullet> P)"
  using assms
  by (pred_simp, metis (no_types, lifting) lens.select_convs(2))

lemma ex_zero:
  "(\<exists> &\<emptyset> \<bullet> P) = P"
  by (pred_auto)

lemma all_zero:
  "(\<forall> &\<emptyset> \<bullet> P) = P"
  by (pred_auto)

lemma ex_plus:
  "(\<exists> y;x \<bullet> P) = (\<exists> x \<bullet> \<exists> y \<bullet> P)"
  by (pred_auto)

lemma all_plus:
  "(\<forall> y;x \<bullet> P) = (\<forall> x \<bullet> \<forall> y \<bullet> P)"
  by (pred_auto)

lemma closure_all:
  "[P]\<^sub>u = (\<forall> &\<Sigma> \<bullet> P)"
  by (pred_auto)

lemma unrest_as_exists:
  "vwb_lens x \<Longrightarrow> (x \<sharp> P) \<longleftrightarrow> ((\<exists> x \<bullet> P) = P)"
  by (pred_simp, metis vwb_lens.put_eq)

lemma ex_mono: "P \<sqsubseteq> Q \<Longrightarrow> (\<exists> x \<bullet> P) \<sqsubseteq> (\<exists> x \<bullet> Q)"
  by (pred_auto)

lemma ex_weakens: "wb_lens x \<Longrightarrow> (\<exists> x \<bullet> P) \<sqsubseteq> P"
  by (pred_simp, metis wb_lens.get_put)

lemma all_mono: "P \<sqsubseteq> Q \<Longrightarrow> (\<forall> x \<bullet> P) \<sqsubseteq> (\<forall> x \<bullet> Q)"
  by (pred_auto)

lemma all_strengthens: "wb_lens x \<Longrightarrow> P \<sqsubseteq> (\<forall> x \<bullet> P)"
  by (pred_simp, metis wb_lens.get_put)

lemma ex_unrest: "x \<sharp> P \<Longrightarrow> (\<exists> x \<bullet> P) = P"
  by (pred_auto)

lemma all_unrest: "x \<sharp> P \<Longrightarrow> (\<forall> x \<bullet> P) = P"
  by (pred_auto)

lemma not_ex_not: "\<not> (\<exists> x \<bullet> \<not> P) = (\<forall> x \<bullet> P)"
  by (pred_auto)

lemma not_all_not: "\<not> (\<forall> x \<bullet> \<not> P) = (\<exists> x \<bullet> P)"
  by (pred_auto)

subsection {* Conditional laws *}

lemma cond_def:
  "(P \<triangleleft> b \<triangleright> Q) = ((b \<and> P) \<or> ((\<not> b) \<and> Q))"
  by (pred_auto)

lemma cond_idem:"(P \<triangleleft> b \<triangleright> P) = P" by (pred_auto)

lemma cond_symm:"(P \<triangleleft> b \<triangleright> Q) = (Q \<triangleleft> \<not> b \<triangleright> P)" by (pred_auto)

lemma cond_assoc: "((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> R) = (P \<triangleleft> b \<and> c \<triangleright> (Q \<triangleleft> c \<triangleright> R))" by (pred_auto)

lemma cond_distr: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> c \<triangleright> R)) = ((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> (P \<triangleleft> b \<triangleright> R))" by (pred_auto)

lemma cond_unit_T [simp]:"(P \<triangleleft> true \<triangleright> Q) = P" by (pred_auto)

lemma cond_unit_F [simp]:"(P \<triangleleft> false \<triangleright> Q) = Q" by (pred_auto)

lemma cond_and_T_integrate:
  "((P \<and> b) \<or> (Q \<triangleleft> b \<triangleright> R)) = ((P \<or> Q) \<triangleleft> b \<triangleright> R)"
  by (pred_auto)

lemma cond_L6: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)" by (pred_auto)

lemma cond_L7: "(P \<triangleleft> b \<triangleright> (P \<triangleleft> c \<triangleright> Q)) = (P \<triangleleft> b \<or> c \<triangleright> Q)" by (pred_auto)

lemma cond_and_distr: "((P \<and> Q) \<triangleleft> b \<triangleright> (R \<and> S)) = ((P \<triangleleft> b \<triangleright> R) \<and> (Q \<triangleleft> b \<triangleright> S))" by (pred_auto)

lemma cond_or_distr: "((P \<or> Q) \<triangleleft> b \<triangleright> (R \<or> S)) = ((P \<triangleleft> b \<triangleright> R) \<or> (Q \<triangleleft> b \<triangleright> S))" by (pred_auto)

lemma cond_imp_distr:
"((P \<Rightarrow> Q) \<triangleleft> b \<triangleright> (R \<Rightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Rightarrow> (Q \<triangleleft> b \<triangleright> S))" by (pred_auto)

lemma cond_eq_distr:
"((P \<Leftrightarrow> Q) \<triangleleft> b \<triangleright> (R \<Leftrightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Leftrightarrow> (Q \<triangleleft> b \<triangleright> S))" by (pred_auto)

lemma cond_conj_distr:"(P \<and> (Q \<triangleleft> b \<triangleright> S)) = ((P \<and> Q) \<triangleleft> b \<triangleright> (P \<and> S))" by (pred_auto)

lemma cond_disj_distr:"(P \<or> (Q \<triangleleft> b \<triangleright> S)) = ((P \<or> Q) \<triangleleft> b \<triangleright> (P \<or> S))" by (pred_auto)

lemma cond_neg: "\<not> (P \<triangleleft> b \<triangleright> Q) = ((\<not> P) \<triangleleft> b \<triangleright> (\<not> Q))" by (pred_auto)

lemma cond_conj: "P \<triangleleft> b \<and> c \<triangleright> Q = (P \<triangleleft> c \<triangleright> Q) \<triangleleft> b \<triangleright> Q"
  by (pred_auto)

lemma spec_cond_dist: "(P \<Rightarrow> (Q \<triangleleft> b \<triangleright> R)) = ((P \<Rightarrow> Q) \<triangleleft> b \<triangleright> (P \<Rightarrow> R))"
  by (pred_auto)

lemma cond_USUP_dist: "(\<Squnion> P\<in>S \<bullet> F(P)) \<triangleleft> b \<triangleright> (\<Squnion> P\<in>S \<bullet> G(P)) = (\<Squnion> P\<in>S \<bullet> F(P) \<triangleleft> b \<triangleright> G(P))"
  by (pred_auto)

lemma cond_UINF_dist: "(\<Sqinter> P\<in>S \<bullet> F(P)) \<triangleleft> b \<triangleright> (\<Sqinter> P\<in>S \<bullet> G(P)) = (\<Sqinter> P\<in>S \<bullet> F(P) \<triangleleft> b \<triangleright> G(P))"
  by (pred_auto)

lemma cond_var_subst_left:
  assumes "vwb_lens x"
  shows "(P\<lbrakk>true/x\<rbrakk> \<triangleleft> var x \<triangleright> Q) = (P \<triangleleft> var x \<triangleright> Q)"
  using assms by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma cond_var_subst_right:
  assumes "vwb_lens x"
  shows "(P \<triangleleft> var x \<triangleright> Q\<lbrakk>false/x\<rbrakk>) = (P \<triangleleft> var x \<triangleright> Q)"
  using assms by (pred_auto, metis (full_types) vwb_lens.put_eq)

lemma cond_var_split:
  "vwb_lens x \<Longrightarrow> (P\<lbrakk>true/x\<rbrakk> \<triangleleft> var x \<triangleright> P\<lbrakk>false/x\<rbrakk>) = P"
  by (rel_simp, (metis (full_types) vwb_lens.put_eq)+)

lemma cond_assign_subst:
  "vwb_lens x \<Longrightarrow> (P \<triangleleft> utp_expr.var x =\<^sub>u v \<triangleright> Q) = (P\<lbrakk>v/x\<rbrakk> \<triangleleft> utp_expr.var x =\<^sub>u v \<triangleright> Q)"
  apply (rel_simp) using vwb_lens.put_eq by force

text {* Function to obtain the set of observations of a predicate *}
    
definition obs_upred :: "'\<alpha> upred \<Rightarrow> '\<alpha> set" ("\<lbrakk>_\<rbrakk>\<^sub>o")
where [upred_defs]: "\<lbrakk>P\<rbrakk>\<^sub>o = {b. \<lbrakk>P\<rbrakk>\<^sub>eb}"
    
lemma obs_upred_refine_iff: 
  "P \<sqsubseteq> Q \<longleftrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>o \<subseteq> \<lbrakk>P\<rbrakk>\<^sub>o"
  by (pred_auto)
    
text {* A refinement can be demonstrated by considering only the observations of the predicates
  which are relevant, i.e. not unrestricted, for them. In other words, if the alphabet can
  be split into two disjoint segments, $x$ and $y$, and neither predicate refers to $y$ then
  only $x$ need be considered when checking for observations. *}
    
lemma refine_by_obs:
  assumes "x \<bowtie> y" "bij_lens (x +\<^sub>L y)" "y \<sharp> P" "y \<sharp> Q" "{v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`} \<subseteq> {v. `Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`}"
  shows "Q \<sqsubseteq> P"
  using assms(3-5)
  apply (simp add: obs_upred_refine_iff subset_eq)
  apply (pred_simp)
  apply (rename_tac b)
  apply (drule_tac x="get\<^bsub>x\<^esub>b" in spec)
  apply (auto simp add: assms)
  apply (metis assms(1) assms(2) bij_lens.axioms(2) bij_lens_axioms_def lens_override_def lens_override_plus)+
done
    
subsection {* Cylindric algebra *}

lemma C1: "(\<exists> x \<bullet> false) = false"
  by (pred_auto)

lemma C2: "wb_lens x \<Longrightarrow> `P \<Rightarrow> (\<exists> x \<bullet> P)`"
  by (pred_simp, metis wb_lens.get_put)

lemma C3: "mwb_lens x \<Longrightarrow> (\<exists> x \<bullet> (P \<and> (\<exists> x \<bullet> Q))) = ((\<exists> x \<bullet> P) \<and> (\<exists> x \<bullet> Q))"
  by (pred_auto)

lemma C4a: "x \<approx>\<^sub>L y \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  by (pred_simp, metis (no_types, lifting) lens.select_convs(2))+

lemma C4b: "x \<bowtie> y \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  using ex_commute by blast

lemma C5:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(&x =\<^sub>u &x) = true"
  by (pred_auto)

lemma C6:
  assumes "wb_lens x" "x \<bowtie> y" "x \<bowtie> z"
  shows "(&y =\<^sub>u &z) = (\<exists> x \<bullet> &y =\<^sub>u &x \<and> &x =\<^sub>u &z)"
  using assms
  by (pred_simp, (metis lens_indep_def)+)

lemma C7:
  assumes "weak_lens x" "x \<bowtie> y"
  shows "((\<exists> x \<bullet> &x =\<^sub>u &y \<and> P) \<and> (\<exists> x \<bullet> &x =\<^sub>u &y \<and> \<not> P)) = false"
  using assms
  by (pred_simp, simp add: lens_indep_sym)

subsection {* Quantifier lifting *}

named_theorems uquant_lift

lemma shEx_lift_conj_1 [uquant_lift]:
  "((\<^bold>\<exists> x \<bullet> P(x)) \<and> Q) = (\<^bold>\<exists> x \<bullet> P(x) \<and> Q)"
  by (pred_auto)

lemma shEx_lift_conj_2 [uquant_lift]:
  "(P \<and> (\<^bold>\<exists> x \<bullet> Q(x))) = (\<^bold>\<exists> x \<bullet> P \<and> Q(x))"
  by (pred_auto)

end