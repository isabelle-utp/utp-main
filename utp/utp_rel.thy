section \<open> Alphabetised Relations \<close>

theory utp_rel
imports
  utp_pred_laws
  utp_healthy
  utp_lift
  utp_tactics
  utp_lift_pretty
begin

text \<open> An alphabetised relation is simply a predicate whose state-space is a product type. In this
  theory we construct the core operators of the relational calculus, and prove a libary of 
  associated theorems, based on Chapters 2 and 5 of the UTP book~\cite{Hoare&98}. \<close>
  
subsection \<open> Relational Alphabets \<close>
  
text \<open> We set up convenient syntax to refer to the input and output parts of the alphabet, as is
  common in UTP. Since we are in a product space, these are simply the lenses @{term "fst\<^sub>L"} and
  @{term "snd\<^sub>L"}. \<close>
  
definition in\<alpha> :: "('\<alpha> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "in\<alpha> = fst\<^sub>L"

definition out\<alpha> :: "('\<beta> \<Longrightarrow> '\<alpha> \<times> '\<beta>)" where
[lens_defs]: "out\<alpha> = snd\<^sub>L"

lemma in\<alpha>_uvar [simp]: "vwb_lens in\<alpha>"
  by (unfold_locales, auto simp add: in\<alpha>_def)

lemma out\<alpha>_uvar [simp]: "vwb_lens out\<alpha>"
  by (unfold_locales, auto simp add: out\<alpha>_def)

lemma var_in_alpha [simp]: "x ;\<^sub>L in\<alpha> = in_var x"
  by (simp add: fst_lens_def in\<alpha>_def in_var_def)

lemma var_out_alpha [simp]: "x ;\<^sub>L out\<alpha> = out_var x"
  by (simp add: out\<alpha>_def out_var_def snd_lens_def)

lemma drop_pre_inv [simp]: "\<lbrakk> out\<alpha> \<sharp> p \<rbrakk> \<Longrightarrow> \<lceil>\<lfloor>p\<rfloor>\<^sub><\<rceil>\<^sub>< = p"
  by (pred_simp)

lemma usubst_lookup_in_var_unrest [usubst]:
  "in\<alpha> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s (in_var x) = $x"
  by (rel_simp, metis fstI)

lemma usubst_lookup_out_var_unrest [usubst]:
  "out\<alpha> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<langle>\<sigma>\<rangle>\<^sub>s (out_var x) = $x\<acute>"
  by (rel_simp, metis sndI)
    
lemma out_alpha_in_indep [simp]:
  "out\<alpha> \<bowtie> in_var x" "in_var x \<bowtie> out\<alpha>"
  by (simp_all add: in_var_def out\<alpha>_def lens_indep_def fst_lens_def snd_lens_def lens_comp_def)

lemma in_alpha_out_indep [simp]:
  "in\<alpha> \<bowtie> out_var x" "out_var x \<bowtie> in\<alpha>"
  by (simp_all add: in_var_def in\<alpha>_def lens_indep_def fst_lens_def lens_comp_def)

text \<open> The following two functions lift a predicate substitution to a relational one. \<close>
    
abbreviation usubst_rel_lift :: "'\<alpha> usubst \<Rightarrow> ('\<alpha> \<times> '\<beta>) usubst" ("\<lceil>_\<rceil>\<^sub>s") where
"\<lceil>\<sigma>\<rceil>\<^sub>s \<equiv> \<sigma> \<oplus>\<^sub>s in\<alpha>"

abbreviation usubst_rel_drop :: "('\<alpha> \<times> '\<alpha>) usubst \<Rightarrow> '\<alpha> usubst" ("\<lfloor>_\<rfloor>\<^sub>s") where
"\<lfloor>\<sigma>\<rfloor>\<^sub>s \<equiv> \<sigma> \<restriction>\<^sub>s in\<alpha>"

utp_const usubst_rel_lift usubst_rel_drop

text \<open> The alphabet of a relation then consists wholly of the input and output portions. \<close>

lemma alpha_in_out:
  "\<Sigma> \<approx>\<^sub>L in\<alpha> +\<^sub>L out\<alpha>"
  by (simp add: fst_snd_id_lens in\<alpha>_def lens_equiv_refl out\<alpha>_def)

subsection \<open> Relational Types and Operators \<close>

text \<open> We create type synonyms for conditions (which are simply predicates) -- i.e. relations
  without dashed variables --, alphabetised relations where the input and output alphabet can
  be different, and finally homogeneous relations. \<close>
  
type_synonym '\<alpha> cond        = "'\<alpha> upred"
type_synonym ('\<alpha>, '\<beta>) urel  = "('\<alpha> \<times> '\<beta>) upred"
type_synonym '\<alpha> hrel        = "('\<alpha> \<times> '\<alpha>) upred"
type_synonym ('a, '\<alpha>) hexpr = "('a, '\<alpha> \<times> '\<alpha>) uexpr"
  
translations
  (type) "('\<alpha>, '\<beta>) urel" <= (type) "('\<alpha> \<times> '\<beta>) upred"

text \<open> We set up some overloaded constants for sequential composition and the identity in case
  we want to overload their definitions later. \<close>
  
consts
  useq     :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr ";;" 61)
  uassigns :: "('a, 'b) psubst \<Rightarrow> 'c" ("\<langle>_\<rangle>\<^sub>a")
  uskip    :: "'a" ("II")
  
text \<open> We define a specialised version of the conditional where the condition can refer only to
  undashed variables, as is usually the case in programs, but not universally in UTP models. 
  We implement this by lifting the condition predicate into the relational state-space with
  construction @{term "\<lceil>b\<rceil>\<^sub><"}. \<close>
  
definition lift_rcond ("\<lceil>_\<rceil>\<^sub>\<leftarrow>") where
[upred_defs]: "\<lceil>b\<rceil>\<^sub>\<leftarrow> = \<lceil>b\<rceil>\<^sub><"
    
abbreviation 
  rcond :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<alpha> cond \<Rightarrow> ('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<alpha>, '\<beta>) urel"
  ("(3_ \<triangleleft> _ \<triangleright>\<^sub>r/ _)" [52,0,53] 52)
  where "(P \<triangleleft> b \<triangleright>\<^sub>r Q) \<equiv> (P \<triangleleft> \<lceil>b\<rceil>\<^sub>\<leftarrow> \<triangleright> Q)"

text \<open> Sequential composition is heterogeneous, and simply requires that the output alphabet
  of the first matches then input alphabet of the second. We define it by lifting HOL's 
  built-in relational composition operator (@{term "(O)"}). Since this returns a set, the
  definition states that the state binding $b$ is an element of this set. \<close>
  
lift_definition seqr::"('\<alpha>, '\<beta>) urel \<Rightarrow> ('\<beta>, '\<gamma>) urel \<Rightarrow> ('\<alpha> \<times> '\<gamma>) upred"
is "\<lambda> P Q b. b \<in> ({p. P p} O {q. Q q})" .

adhoc_overloading
  useq seqr
   
text \<open> We also set up a homogeneous sequential composition operator, and versions of @{term true}
  and @{term false} that are explicitly typed by a homogeneous alphabet. \<close>

abbreviation seqh :: "'\<alpha> hrel \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" (infixr ";;\<^sub>h" 61) where
"seqh P Q \<equiv> (P ;; Q)"

abbreviation truer :: "'\<alpha> hrel" ("true\<^sub>h") where
"truer \<equiv> true"

abbreviation falser :: "'\<alpha> hrel" ("false\<^sub>h") where
"falser \<equiv> false"
  
text \<open> We define the relational converse operator as an alphabet extrusion on the bijective
  lens @{term swap\<^sub>L} that swaps the elements of the product state-space. \<close>
    
abbreviation conv_r :: "('a, '\<alpha> \<times> '\<beta>) uexpr \<Rightarrow> ('a, '\<beta> \<times> '\<alpha>) uexpr" ("_\<^sup>-" [999] 999)
where "conv_r e \<equiv> e \<oplus>\<^sub>p swap\<^sub>L"

text \<open> Assignment is defined using substitutions, where latter defines what each variable should
  map to. This approach, which is originally due to Back~\cite{Back1998}, permits more general 
  assignment expressions. The definition of the operator identifies the after state binding, $b'$, 
  with the substitution function applied to the before state binding $b$. \<close>
  
lift_definition assigns_r :: "('\<alpha>,'\<beta>) psubst \<Rightarrow> ('\<alpha>, '\<beta>) urel"
  is "\<lambda> \<sigma> (b, b'). b' = \<sigma>(b)" .

adhoc_overloading
  uassigns assigns_r
    
text \<open> Relational identity, or skip, is then simply an assignment with the identity substitution:
  it simply identifies all variables. \<close>
    
definition skip_r :: "'\<alpha> hrel" where
[urel_defs]: "skip_r = assigns_r id\<^sub>s"

adhoc_overloading
  uskip skip_r

text \<open> Non-deterministic assignment, also known as ``choose'', assigns an arbitrarily chosen value 
  to the given variable \<close>

definition nd_assign :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" where
[urel_defs]: "nd_assign x = (\<Sqinter> v \<bullet> assigns_r [x \<mapsto>\<^sub>s \<guillemotleft>v\<guillemotright>])"

text \<open> We set up iterated sequential composition which iterates an indexed predicate over the
  elements of a list. \<close>
  
definition seqr_iter :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b hrel) \<Rightarrow> 'b hrel" where
[urel_defs]: "seqr_iter xs P = foldr (\<lambda> i Q. P(i) ;; Q) xs II"
  
text \<open> A singleton assignment simply applies a singleton substitution function, and similarly
  for a double assignment. \<close>

abbreviation assign_r :: "('t \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
where "assign_r x v \<equiv> \<langle>[x \<mapsto>\<^sub>s v]\<rangle>\<^sub>a"

abbreviation assign_2_r ::
  "('t1 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t2 \<Longrightarrow> '\<alpha>) \<Rightarrow> ('t1, '\<alpha>) uexpr \<Rightarrow> ('t2, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel"
where "assign_2_r x y u v \<equiv> assigns_r [x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v]"

text \<open> We also define the alphabetised skip operator that identifies all input and output variables
  in the given alphabet lens. All other variables are unrestricted. We also set up syntax for it. \<close>
  
definition skip_ra :: "('\<beta>, '\<alpha>) lens \<Rightarrow>'\<alpha> hrel" where
[urel_defs]: "skip_ra v = ($v\<acute> =\<^sub>u $v)"

text \<open> Similarly, we define the alphabetised assignment operator. \<close>

definition assigns_ra :: "'\<alpha> usubst \<Rightarrow> ('\<beta>, '\<alpha>) lens \<Rightarrow> '\<alpha> hrel" ("\<langle>_\<rangle>\<^bsub>_\<^esub>") where
"\<langle>\<sigma>\<rangle>\<^bsub>a\<^esub> = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> skip_ra a)"

text \<open> Assumptions ($c^{\top}$) and assertions ($c_{\bot}$) are encoded as conditionals. An assumption
  behaves like skip if the condition is true, and otherwise behaves like @{term false} (miracle).
  An assertion is the same, but yields @{term true}, which is an abort. They are the same as
  tests, as in Kleene Algebra with Tests~\cite{kozen1997kleene,Armstrong2015} 
  (KAT), which embeds a Boolean algebra into a Kleene algebra to represent conditions. \<close>

definition rassume :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("[_]\<^sup>\<top>") where
[urel_defs]: "rassume c = II \<triangleleft> c \<triangleright>\<^sub>r false"

notation rassume ("?[_]")

utp_lift_notation rassume

definition rassert :: "'\<alpha> upred \<Rightarrow> '\<alpha> hrel" ("{_}\<^sub>\<bottom>") where
[urel_defs]: "rassert c = II \<triangleleft> c \<triangleright>\<^sub>r true"

utp_lift_notation rassert

text \<open> We also encode ``naked'' guarded commands~\cite{Dijkstra75,Morgan90} by composing an 
  assumption with a relation. \<close>

definition rgcmd :: "'a upred \<Rightarrow> 'a hrel \<Rightarrow> 'a hrel" ("_ \<longrightarrow>\<^sub>r _" [55, 56] 55) where
[urel_defs]: "rgcmd b P = (rassume b ;; P)"

utp_lift_notation rgcmd (1)

text \<open> We define two variants of while loops based on strongest and weakest fixed points. The former
  is @{term false} for an infinite loop, and the latter is @{term true}. \<close>

definition while_top :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sup>\<top> _ do _ od") where
[urel_defs]: "while_top b P = (\<nu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

notation while_top ("while _ do _ od")

utp_lift_notation while_top (1)

definition while_bot :: "'\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ do _ od") where
[urel_defs]: "while_bot b P = (\<mu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"

utp_lift_notation while_bot (1)

text \<open> While loops with invariant decoration (cf. \cite{Armstrong2015}) -- partial correctness. \<close>

definition while_inv :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while _ invr _ do _ od") where
[urel_defs]: "while_inv b p S = while_top b S"

utp_lift_notation while_inv (2)

text \<open> While loops with invariant decoration -- total correctness. \<close>

definition while_inv_bot :: "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel" ("while\<^sub>\<bottom> _ invr _ do _ od" 71) where
[urel_defs]: "while_inv_bot b p S = while_bot b S"  

utp_lift_notation while_inv_bot (2)

text \<open> While loops with invariant and variant decorations -- total correctness. \<close>

definition while_vrt :: 
  "'\<alpha> cond \<Rightarrow> '\<alpha> cond \<Rightarrow> (nat, '\<alpha>) uexpr \<Rightarrow> '\<alpha> hrel \<Rightarrow> '\<alpha> hrel"  ("while _ invr _ vrt _ do _ od") where
[urel_defs]: "while_vrt b p v S = while_bot b S"

utp_lift_notation while_vrt (3)

translations
  "?[b]" <= "?[U(b)]"
  "{b}\<^sub>\<bottom>" <= "{U(b)}\<^sub>\<bottom>"
  "while b do P od" <= "while U(b) do P od"
  "while b invr c do P od" <= "while U(b) invr U(c) do P od"

text \<open> We implement a poor man's version of alphabet restriction that hides a variable within 
  a relation. \<close>

definition rel_var_res :: "'\<alpha> hrel \<Rightarrow> ('a \<Longrightarrow> '\<alpha>) \<Rightarrow> '\<alpha> hrel" (infix "\<restriction>\<^sub>\<alpha>" 80) where
[urel_defs]: "P \<restriction>\<^sub>\<alpha> x = (\<exists> $x \<bullet> \<exists> $x\<acute> \<bullet> P)"

subsection \<open> Syntax Translations \<close>

\<comment> \<open> Alternative traditional conditional syntax \<close>

abbreviation (input) rifthenelse ("(if (_)/ then (_)/ else (_)/ fi)") 
  where "rifthenelse b P Q \<equiv> P \<triangleleft> b \<triangleright>\<^sub>r Q"

abbreviation (input) rifthen ("(if (_)/ then (_)/ fi)")
  where "rifthen b P \<equiv> rifthenelse b P II"

utp_lift_notation rifthenelse (1 2)
utp_lift_notation rifthen (1)

syntax
  \<comment> \<open> Iterated sequential composition \<close>
  "_seqr_iter" :: "pttrn \<Rightarrow> 'a list \<Rightarrow> '\<sigma> hrel \<Rightarrow> '\<sigma> hrel" ("(3;; _ : _ \<bullet>/ _)" [0, 0, 10] 10)
  \<comment> \<open> Single and multiple assignement \<close>
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  ("'(_') := '(_')")  
  "_assignment"     :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> hrel"  (infixr ":=" 62)
  \<comment> \<open> Non-deterministic assignment \<close>
  "_nd_assign" :: "svids \<Rightarrow> logic" ("_ := *" [62] 62)
  \<comment> \<open> Substitution constructor \<close>
  "_mk_usubst"      :: "svids \<Rightarrow> uexprs \<Rightarrow> '\<alpha> usubst"
  \<comment> \<open> Alphabetised skip \<close>
  "_skip_ra"        :: "salpha \<Rightarrow> logic" ("II\<^bsub>_\<^esub>")

translations
  ";; x : l \<bullet> P" \<rightleftharpoons> "(CONST seqr_iter) l (\<lambda>x. P)"
  "_mk_usubst \<sigma> (_svid_unit x) v" \<rightleftharpoons> "\<sigma>(&x \<mapsto>\<^sub>s v)"
  "_mk_usubst \<sigma> (_svid_list x xs) (_uexprs v vs)" \<rightleftharpoons> "(_mk_usubst (\<sigma>(&x \<mapsto>\<^sub>s v)) xs vs)"
  "_assignment xs vs" => "CONST uassigns (_mk_usubst id\<^sub>s xs vs)"
  "_assignment x v" <= "CONST uassigns (CONST subst_upd id\<^sub>s x v)"
  "_assignment x v" <= "_assignment (_spvar x) v"
  "_assignment x v" <= "_assignment x (_UTP v)"
  "_nd_assign x" => "CONST nd_assign (_mk_svid_list x)"
  "_nd_assign x" <= "CONST nd_assign x"
  "x,y := u,v" <= "CONST uassigns (CONST subst_upd (CONST subst_upd id\<^sub>s (CONST pr_var x) u) (CONST pr_var y) v)"
  "_skip_ra v" \<rightleftharpoons> "CONST skip_ra v"

text \<open> The following code sets up pretty-printing for homogeneous relational expressions. We cannot 
  do this via the ``translations'' command as we only want the rule to apply when the input and output
  alphabet types are the same. The code has to deconstruct a @{typ "('a, '\<alpha>) uexpr"} type, determine 
  that it is relational (product alphabet), and then checks if the types \emph{alpha} and \emph{beta} 
  are the same. If they are, the type is printed as a \emph{hexpr}. Otherwise, we have no match. 
  We then set up a regular translation for the \emph{hrel} type that uses this. \<close>
  
print_translation \<open>
let
fun tr' ctx [ a
            , Const (@{type_syntax "prod"},_) $ alpha $ beta ] = 
  if (alpha = beta) 
    then Syntax.const @{type_syntax "hexpr"} $ a $ alpha
    else raise Match;
in [(@{type_syntax "uexpr"},tr')]
end
\<close>

translations
  (type) "'\<alpha> hrel" <= (type) "(bool, '\<alpha>) hexpr"
  
subsection \<open> Relation Properties \<close>
  
text \<open> We describe some properties of relations, including functional and injective relations. We
  also provide operators for extracting the domain and range of a UTP relation. \<close>

definition ufunctional :: "('a, 'b) urel \<Rightarrow> bool"
where [urel_defs]: "ufunctional R \<longleftrightarrow> II \<sqsubseteq> R\<^sup>- ;; R"

definition uinj :: "('a, 'b) urel \<Rightarrow> bool"
where [urel_defs]: "uinj R \<longleftrightarrow> II \<sqsubseteq> R ;; R\<^sup>-"
  
definition Pre :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<alpha> upred" 
where [upred_defs]: "Pre P = \<lfloor>\<exists> $\<^bold>v\<acute> \<bullet> P\<rfloor>\<^sub><"

definition Post :: "('\<alpha>, '\<beta>) urel \<Rightarrow> '\<beta> upred" 
where [upred_defs]: "Post P = \<lfloor>\<exists> $\<^bold>v \<bullet> P\<rfloor>\<^sub>>"

utp_const Pre Post

\<comment> \<open> Configuration for UTP tactics. \<close>

update_uexpr_rep_eq_thms \<comment> \<open> Reread @{text rep_eq} theorems. \<close>

subsection \<open> Introduction laws \<close>

lemma urel_refine_ext:
  "\<lbrakk> \<And> s s'. P\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>/$\<^bold>v,$\<^bold>v\<acute>\<rbrakk> \<sqsubseteq> Q\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>/$\<^bold>v,$\<^bold>v\<acute>\<rbrakk> \<rbrakk> \<Longrightarrow> P \<sqsubseteq> Q"
  by (rel_auto)

lemma urel_eq_ext:
  "\<lbrakk> \<And> s s'. P\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>/$\<^bold>v,$\<^bold>v\<acute>\<rbrakk> = Q\<lbrakk>\<guillemotleft>s\<guillemotright>,\<guillemotleft>s'\<guillemotright>/$\<^bold>v,$\<^bold>v\<acute>\<rbrakk> \<rbrakk> \<Longrightarrow> P = Q"
  by (rel_auto)

subsection \<open> Unrestriction Laws \<close>

lemma unrest_iuvar [unrest]: "out\<alpha> \<sharp> $x"
  by (metis fst_snd_lens_indep lift_pre_var out\<alpha>_def unrest_aext_indep)

lemma unrest_ouvar [unrest]: "in\<alpha> \<sharp> $x\<acute>"
  by (metis in\<alpha>_def lift_post_var snd_fst_lens_indep unrest_aext_indep)

lemma unrest_semir_undash [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "$x \<sharp> P"
  shows "$x \<sharp> P ;; Q"
  using assms by (rel_auto)

lemma unrest_semir_dash [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "$x\<acute> \<sharp> Q"
  shows "$x\<acute> \<sharp> P ;; Q"
  using assms by (rel_auto)

lemma unrest_cond [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> b; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> P \<triangleleft> b \<triangleright> Q"
  by (rel_auto)

lemma unrest_lift_rcond [unrest]:
  "x \<sharp> \<lceil>b\<rceil>\<^sub>< \<Longrightarrow> x \<sharp> \<lceil>b\<rceil>\<^sub>\<leftarrow>"
  by (simp add: lift_rcond_def)
    
lemma unrest_in\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; in\<alpha> \<sharp> (P :: ('a, ('\<alpha> \<times> '\<beta>)) uexpr) \<rbrakk> \<Longrightarrow> $x \<sharp> P"
  by (rel_auto)

lemma unrest_out\<alpha>_var [unrest]:
  "\<lbrakk> mwb_lens x; out\<alpha> \<sharp> (P :: ('a, ('\<alpha> \<times> '\<beta>)) uexpr) \<rbrakk> \<Longrightarrow> $x\<acute> \<sharp> P"
  by (rel_auto)

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
  by (transfer, auto simp add: lens_defs)

lemma unrest_convr_in\<alpha> [unrest]:
  "out\<alpha> \<sharp> p \<Longrightarrow> in\<alpha> \<sharp> p\<^sup>-"
  by (transfer, auto simp add: lens_defs)

lemma unrest_out_alpha_usubst_rel_lift [unrest]: 
  "out\<alpha> \<sharp>\<^sub>s \<lceil>\<sigma>\<rceil>\<^sub>s"
  by (rel_auto)

lemma unrest_in_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

lemma unrest_out_rel_var_res [unrest]:
  "vwb_lens x \<Longrightarrow> $x\<acute> \<sharp> (P \<restriction>\<^sub>\<alpha> x)"
  by (simp add: rel_var_res_def unrest)

subsection \<open> Substitution laws \<close>

lemma subst_seq_left [usubst]:
  "out\<alpha> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = (\<sigma> \<dagger> P) ;; Q"
  by (rel_simp, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

lemma subst_seq_right [usubst]:
  "in\<alpha> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<sigma> \<dagger> (P ;; Q) = P ;; (\<sigma> \<dagger> Q)"
  by (rel_simp, (metis (no_types, lifting) Pair_inject surjective_pairing)+)

text \<open> The following laws support substitution in heterogeneous relations for polymorphically
  typed literal expressions. These cannot be supported more generically due to limitations
  in HOL's type system. The laws are presented in a slightly strange way so as to be as
  general as possible. \<close>

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
  "out\<alpha> \<sharp>\<^sub>s \<sigma> \<Longrightarrow> \<sigma> \<dagger> II = \<langle>\<lfloor>\<sigma>\<rfloor>\<^sub>s\<rangle>\<^sub>a"
  by (rel_simp, (metis (mono_tags, lifting) prod.sel(1) sndI surjective_pairing)+)

lemma subst_pre_skip [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> II = \<langle>\<sigma>\<rangle>\<^sub>a"
  by (rel_auto)
    
lemma subst_rel_lift_seq [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> (P ;; Q) = (\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P) ;; Q"
  by (rel_auto)
  
lemma subst_rel_lift_comp [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>s \<circ>\<^sub>s \<lceil>\<rho>\<rceil>\<^sub>s = \<lceil>\<sigma> \<circ>\<^sub>s \<rho>\<rceil>\<^sub>s"
  by (rel_auto)
    
lemma usubst_upd_in_comp [usubst]:
  "\<sigma>(&in\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x \<mapsto>\<^sub>s v)"
  by (simp add: pr_var_def fst_lens_def in\<alpha>_def in_var_def)

lemma usubst_upd_out_comp [usubst]:
  "\<sigma>(&out\<alpha>:x \<mapsto>\<^sub>s v) = \<sigma>($x\<acute> \<mapsto>\<^sub>s v)"
  by (simp add: pr_var_def out\<alpha>_def out_var_def snd_lens_def)

lemma subst_lift_upd [alpha]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<lceil>\<sigma>(x \<mapsto>\<^sub>s v)\<rceil>\<^sub>s = \<lceil>\<sigma>\<rceil>\<^sub>s($x \<mapsto>\<^sub>s \<lceil>v\<rceil>\<^sub><)"
  by (simp add: alpha usubst, simp add: pr_var_def fst_lens_def in\<alpha>_def in_var_def)

lemma subst_drop_upd [alpha]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "\<lfloor>\<sigma>($x \<mapsto>\<^sub>s v)\<rfloor>\<^sub>s = \<lfloor>\<sigma>\<rfloor>\<^sub>s(x \<mapsto>\<^sub>s \<lfloor>v\<rfloor>\<^sub><)"
  by pred_simp

lemma subst_lift_pre [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>b\<rceil>\<^sub>< = \<lceil>\<sigma> \<dagger> b\<rceil>\<^sub><"
  by (metis apply_subst_ext fst_vwb_lens in\<alpha>_def) 
    
lemma unrest_usubst_lift_in [unrest]:
  "x \<sharp> P \<Longrightarrow> $x \<sharp> \<lceil>P\<rceil>\<^sub>s"
  by pred_simp

lemma unrest_usubst_lift_out [unrest]:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "$x\<acute> \<sharp>\<^sub>s \<lceil>P\<rceil>\<^sub>s"
  by pred_simp

lemma subst_lift_cond [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> \<lceil>s\<rceil>\<^sub>\<leftarrow> = \<lceil>\<sigma> \<dagger> s\<rceil>\<^sub>\<leftarrow>"
  by (rel_auto)

lemma msubst_seq [usubst]: "(P(x) ;; Q(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk> = ((P(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk> ;; (Q(x))\<lbrakk>x\<rightarrow>\<guillemotleft>v\<guillemotright>\<rbrakk>)"
  by (rel_auto)  

subsection \<open> Alphabet laws \<close>

lemma aext_cond [alpha]:
  "(P \<triangleleft> b \<triangleright> Q) \<oplus>\<^sub>p a = ((P \<oplus>\<^sub>p a) \<triangleleft> (b \<oplus>\<^sub>p a) \<triangleright> (Q \<oplus>\<^sub>p a))"
  by (rel_auto)

lemma aext_seq [alpha]:
  "wb_lens a \<Longrightarrow> ((P ;; Q) \<oplus>\<^sub>p (a \<times>\<^sub>L a)) = ((P \<oplus>\<^sub>p (a \<times>\<^sub>L a)) ;; (Q \<oplus>\<^sub>p (a \<times>\<^sub>L a)))"
  by (rel_simp, metis wb_lens_weak weak_lens.put_get)

lemma rcond_lift_true [simp]:
  "\<lceil>true\<rceil>\<^sub>\<leftarrow> = true"
  by rel_auto

lemma rcond_lift_false [simp]:
  "\<lceil>false\<rceil>\<^sub>\<leftarrow> = false"
  by rel_auto

no_utp_lift rcond uassigns id seqr useq uskip rcond rassume rassert 
  conv_r rgcmd while_top while_bot while_inv while_inv_bot while_vrt

end