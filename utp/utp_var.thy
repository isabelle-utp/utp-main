section {* UTP variables *}

theory utp_var
imports 
  "../contrib/Kleene_Algebras/Quantales"
  "../utils/cardinals"
  "../utils/Continuum"
  "../utils/finite_bijection"
  "~~/src/HOL/Library/Prefix_Order"
  "~~/src/HOL/Library/Adhoc_Overloading"
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Countable"
  "~~/src/HOL/Eisbach/Eisbach"
  utp_parser_utils
begin

text {* This theory describes the foundational structure of UTP variables, upon which the rest
        of our model rests. We start by defining alphabets, which is this shallow model are
        simple represented as types, though by convention usually a record type where each
        field corresponds to a variable. *}

type_synonym '\<alpha> "alphabet"  = "'\<alpha>"

text {* UTP variables carry two type parameters, $'a$ that corresponds to the variable's type
        and $'\alpha$ that corresponds to alphabet of which the variable is a type. There
        is a thus a strong link between alphabets and variables in this model. Variable are characterized 
        by two functions, \emph{var-lookup} and \emph{var-update}, that respectively lookup and update 
        the variable's value in some alphabetised state space. These functions can readily be extracted
        from an Isabelle record type.
*}

record ('a, '\<alpha>) uvar =
  var_lookup :: "'\<alpha> \<Rightarrow> 'a"
  var_update :: "('a \<Rightarrow> 'a) \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>"

text {* The \emph{var-assign} function uses the @{const var_update} function of a variable to update its value.*}

abbreviation var_assign :: "('a, '\<alpha>) uvar \<Rightarrow> 'a \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha>"
  where "var_assign f v \<equiv> var_update f (\<lambda> _ . v)"

text {* The $VAR$ function is a syntactic translations that allows to retrieve a variable given its 
        name, assuming the variable is a field in a record. *}

syntax "_VAR" :: "id \<Rightarrow> ('a, 'r) uvar"  ("VAR _")
translations "VAR x" => "\<lparr> var_lookup = x, var_update = _update_name x \<rparr>"

text {* In order to allow reasoning about variables generically, we introduce a locale called
        \emph{uvar}, that axiomatises properties of a valid variable, that should be satisfied
        for any record field. When a UTP alphabet record is created it will be necessary to
        prove these properties for each variable field, though this will always be automatic. 
        The locale effectively describes the relationship between the functions @{const var_update}
        and @{const var_lookup}, and thus prevents one from having arbitrary functions as
        variables. Moreover, these properties allow us to prove several important UTP laws,
        such as the assignment laws in the theory of alphabetised relations. *}

locale semi_uvar =
  fixes x :: "('a, 'r) uvar"
  -- {* Application of two updates should correspond to the composition of update functions *}
  assumes var_update_comp: "var_update x f (var_update x g \<sigma>) = var_update x (f \<circ> g) \<sigma>"
  -- {* Updating a variable's value to the one it already has is ineffectual *}
  and var_update_eta: "var_update x (\<lambda>_. var_lookup x \<sigma>) \<sigma> = \<sigma>"

locale uvar = semi_uvar +
  assumes var_update_lookup: "var_lookup x (var_update x f \<sigma>) = f (var_lookup x \<sigma>)"

declare semi_uvar.var_update_comp [simp]
declare uvar.var_update_lookup [simp]
declare semi_uvar.var_update_eta [simp]

lemma uvar_semi_var [simp]: "uvar x \<Longrightarrow> semi_uvar x"
  by (simp add: uvar_def)
  

text {* In addition to defining the validity of variable, we also need to show how two variables
        are related. Since variables are pairs of functions and have no identifying name that
        we can reason about, and moreover will often have different types, we cannot use the 
        usual HOL inequalities to reason about them. Thus we define a weaker notion of inequality
        called \emph{independence} -- two variables are independent if their update functions
        commute. That is to say, updates to the variables do not have any effect on each other.
        This assumes they are also valid variables. *}

definition uvar_indep :: "('a, 'r) uvar \<Rightarrow> ('b, 'r) uvar \<Rightarrow> bool" (infix "\<bowtie>" 50) where
"x \<bowtie> y \<longleftrightarrow> (\<forall> f g \<sigma>. var_update x f (var_update y g \<sigma>) = var_update y g (var_update x f \<sigma>))"

text {* We can now demonstrate some useful properties about the variable independence relation. *}

lemma uvar_indep_sym: "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
  by (simp add: uvar_indep_def)

lemma uvar_indep_comm:
  assumes "x \<bowtie> y"
  shows "var_update x f (var_update y g \<sigma>) = var_update y g (var_update x f \<sigma>)"
  using assms by (simp add: uvar_indep_def)

text {* The following property states that looking up the value of a variable is unaffected
        by an update to an independent variable. *}

lemma uvar_indep_lookup_upd [simp]:
  assumes "uvar x" "x \<bowtie> y"
  shows "var_lookup x (var_update y f \<sigma>) = var_lookup x \<sigma>"
proof -
  have "var_lookup x (var_update y f \<sigma>) = var_lookup x (var_update y f (var_update x (\<lambda>_. var_lookup x \<sigma>) \<sigma>))"
    by (simp add: assms(1))
  also have "... = var_lookup x (var_update x (\<lambda>_. var_lookup x \<sigma>) (var_update y f \<sigma>))"
    using assms(2) by (auto simp add:uvar_indep_def)
  also have "... = var_lookup x \<sigma>"
    by (simp add: assms(1))
  finally show ?thesis .
qed
 
text {* We also define some lifting functions for variables to create input and output variables.
        These simply lift the alphabet to a tuple type since relations will ultimately be defined
        to a tuple alphabet. *}

definition in_var :: "('a, '\<alpha>) uvar \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uvar" where
"in_var x = \<lparr> var_lookup = var_lookup x \<circ> fst, var_update = (\<lambda> f (A, A'). (var_update x f A, A')) \<rparr>"

definition out_var :: "('a, '\<beta>) uvar \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) uvar" where
"out_var x = \<lparr> var_lookup = var_lookup x \<circ> snd, var_update = (\<lambda> f (A, A'). (A, var_update x f A')) \<rparr>"

text {* We show that lifted input and output variables are both valid variables, and that input
        and output variables are always independent. *}

lemma in_var_semi_uvar [simp]:
  assumes "semi_uvar x"
  shows "semi_uvar (in_var x)"
  using assms 
  by (unfold_locales, auto simp add: in_var_def)

lemma out_var_semi_uvar [simp]:
  assumes "semi_uvar x"
  shows "semi_uvar (out_var x)"
  using assms 
  by (unfold_locales, auto simp add: out_var_def)

lemma in_var_uvar [simp]:
  assumes "uvar x"
  shows "uvar (in_var x)"
  using assms 
  by (unfold_locales, auto simp add: in_var_def)

lemma out_var_uvar [simp]:
  assumes "uvar x"
  shows "uvar (out_var x)"
  using assms 
  by (unfold_locales, auto simp add: out_var_def)

lemma in_out_indep [simp]:
  "in_var x \<bowtie> out_var y"
  by (simp add: uvar_indep_def in_var_def out_var_def)

lemma out_in_indep [simp]:
  "out_var x \<bowtie> in_var y"
  by (simp add: uvar_indep_def in_var_def out_var_def)

lemma in_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> in_var x \<bowtie> in_var y"
  by (simp add: uvar_indep_def in_var_def)

lemma out_var_indep [simp]:
  "x \<bowtie> y \<Longrightarrow> out_var x \<bowtie> out_var y"
  by (simp add: uvar_indep_def out_var_def)

text {* We also define some lookup abstraction simplifications. *}

lemma var_lookup_in [simp]: "var_lookup (in_var x) (A, A') = var_lookup x A"
  by (simp add: in_var_def)

lemma var_lookup_out [simp]: "var_lookup (out_var x) (A, A') = var_lookup x A'"
  by (simp add: out_var_def)

lemma var_update_in [simp]: "var_update (in_var x) f (A, A') = (var_update x f A, A')"
  by (simp add: in_var_def)

lemma var_update_out [simp]: "var_update (out_var x) f (A, A') = (A, var_update x f A')"
  by (simp add: out_var_def)

text {* Variables can also be used to effectively define sets of variables. Here we define the
        the universal alphabet ($\Sigma$) to be a variable with identity for both the lookup
        and update functions. Effectively this is just a function directly on the alphabet type. *}

definition univ_alpha :: "('\<alpha>, '\<alpha>) uvar" ("\<Sigma>") where
"univ_alpha = \<lparr> var_lookup = id, var_update = id \<rparr>"


text {* The following operator attempts to combine two variables to produce a unified projection
        update pair. I hoped this could be used to define alphabet subsets by allowing
        a finite composition of variables. However, I don't think it works as the update
        function can't really be split into it's constituent parts if, e.g. the update of
        the first component depends on the second etc. You really want to update the two
        fields in parallel, but I don't think this is possible. *}

definition uvar_comp :: "('a, '\<alpha>) uvar \<Rightarrow> ('b, '\<alpha>) uvar \<Rightarrow> ('a \<times> 'b, '\<alpha>) uvar" (infix "\<circ>\<^sub>v" 35) where
"uvar_comp x y = \<lparr> var_lookup = \<lambda> A. (var_lookup x A, var_lookup y A)
                 , var_update = \<lambda> f. var_update x (\<lambda> a. fst (f (a, undefined))) \<circ>
                                     var_update y (\<lambda> b. snd (f (undefined, b))) \<rparr>"

nonterminal svar

syntax
  "_svar"     :: "id \<Rightarrow> svar" ("_" [999] 999)
  "_spvar"    :: "id \<Rightarrow> svar" ("&_" [999] 999)
  "_sinvar"   :: "id \<Rightarrow> svar" ("$_" [999] 999)
  "_soutvar"  :: "id \<Rightarrow> svar" ("$_\<acute>" [999] 999)

translations
  "_svar x" => "x"
  "_spvar x" => "x"
  "_sinvar x" == "CONST in_var x"
  "_soutvar x" == "CONST out_var x"

end