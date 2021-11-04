section \<open>PDDL and STRIPS Semantics\<close>
theory PDDL_STRIPS_Semantics
imports
  "Propositional_Proof_Systems.Formulas"
  "Propositional_Proof_Systems.Sema"
  "Propositional_Proof_Systems.Consistency"
  "Automatic_Refinement.Misc"
  "Automatic_Refinement.Refine_Util"
begin
no_notation insert ("_ \<triangleright> _" [56,55] 55)

subsection \<open>Utility Functions\<close>
definition "index_by f l \<equiv> map_of (map (\<lambda>x. (f x,x)) l)"

lemma index_by_eq_Some_eq[simp]:
  assumes "distinct (map f l)"
  shows "index_by f l n = Some x \<longleftrightarrow> (x\<in>set l \<and> f x = n)"
  unfolding index_by_def
  using assms
  by (auto simp: o_def)

lemma index_by_eq_SomeD:
  shows "index_by f l n = Some x \<Longrightarrow> (x\<in>set l \<and> f x = n)"
  unfolding index_by_def
  by (auto dest: map_of_SomeD)


lemma lookup_zip_idx_eq:
  assumes "length params = length args"
  assumes "i<length args"
  assumes "distinct params"
  assumes "k = params ! i"
  shows "map_of (zip params args) k = Some (args ! i)"
  using assms
  by (auto simp: in_set_conv_nth)

lemma rtrancl_image_idem[simp]: "R\<^sup>* `` R\<^sup>* `` s = R\<^sup>* `` s"
  by (metis relcomp_Image rtrancl_idemp_self_comp)


subsection \<open>Abstract Syntax\<close>

subsubsection \<open>Generic Entities\<close>
type_synonym name = string

datatype predicate = Pred (name: name)

text \<open>Some of the AST entities are defined over a polymorphic \<open>'val\<close> type,
  which gets either instantiated by variables (for domains)
  or objects (for problems).
\<close>

text \<open>An atom is either a predicate with arguments, or an equality statement.\<close>
datatype 'ent atom = predAtm (predicate: predicate) (arguments: "'ent list")
                     | Eq (lhs: 'ent) (rhs: 'ent)

text \<open>A type is a list of primitive type names.
  To model a primitive type, we use a singleton list.\<close>
datatype type = Either (primitives: "name list")

text \<open>An effect contains a list of values to be added, and a list of values
  to be removed.\<close>
datatype 'ent ast_effect = Effect (adds: "('ent atom formula) list") (dels: "('ent atom formula) list")

text \<open>Variables are identified by their names.\<close>
datatype variable = varname: Var name
text \<open>Objects and constants are identified by their names\<close>
datatype object = name: Obj name

datatype "term" = VAR variable | CONST object
hide_const (open) VAR CONST \<comment> \<open>Refer to constructors by qualified names only\<close>




subsubsection \<open>Domains\<close>

text \<open>An action schema has a name, a typed parameter list, a precondition,
  and an effect.\<close>
datatype ast_action_schema = Action_Schema
  (name: name)
  (parameters: "(variable \<times> type) list")
  (precondition: "term atom formula")
  (effect: "term ast_effect")

text \<open>A predicate declaration contains the predicate's name and its
  argument types.\<close>
datatype predicate_decl = PredDecl
  (pred: predicate)
  (argTs: "type list")

text \<open>A domain contains the declarations of primitive types, predicates,
  and action schemas.\<close>
datatype ast_domain = Domain
  (types: "(name \<times> name) list") \<comment> \<open> \<open>(type, supertype)\<close> declarations. \<close>
  (predicates: "predicate_decl list")
  ("consts": "(object \<times> type) list")
  (actions: "ast_action_schema list")

subsubsection \<open>Problems\<close>


text \<open>A fact is a predicate applied to objects.\<close>
type_synonym fact = "predicate \<times> object list"

text \<open>A problem consists of a domain, a list of objects,
  a description of the initial state, and a description of the goal state. \<close>
datatype ast_problem = Problem
  (domain: ast_domain)
  (objects: "(object \<times> type) list")
  (init: "object atom formula list")
  (goal: "object atom formula")


subsubsection \<open>Plans\<close>
datatype plan_action = PAction
  (name: name)
  (arguments: "object list")

type_synonym plan = "plan_action list"

subsubsection \<open>Ground Actions\<close>
text \<open>The following datatype represents an action scheme that has been
  instantiated by replacing the arguments with concrete objects,
  also called ground action.
\<close>
datatype ground_action = Ground_Action
  (precondition: "(object atom) formula")
  (effect: "object ast_effect")



subsection \<open>Closed-World Assumption, Equality, and Negation\<close>
  text \<open>Discriminator for atomic predicate formulas.\<close>
  fun is_predAtom where
    "is_predAtom (Atom (predAtm _ _)) = True" | "is_predAtom _ = False"


  text \<open>The world model is a set of (atomic) formulas\<close>
  type_synonym world_model = "object atom formula set"

  text \<open>It is basic, if it only contains atoms\<close>
  definition "wm_basic M \<equiv> \<forall>a\<in>M. is_predAtom a"

  text \<open>A valuation extracted from the atoms of the world model\<close>
  definition valuation :: "world_model \<Rightarrow> object atom valuation"
    where "valuation M \<equiv> \<lambda>predAtm p xs \<Rightarrow> Atom (predAtm p xs) \<in> M | Eq a b \<Rightarrow> a=b"

  text \<open>Augment a world model by adding negated versions of all atoms
    not contained in it, as well as interpretations of equality.\<close>
  definition close_world :: "world_model \<Rightarrow> world_model" where "close_world M =
    M \<union> {\<^bold>\<not>(Atom (predAtm p as)) | p as. Atom (predAtm p as) \<notin> M}
    \<union> {Atom (Eq a a) | a. True} \<union> {\<^bold>\<not>(Atom (Eq a b)) | a b. a\<noteq>b}"

  definition "close_neg M \<equiv> M \<union> {\<^bold>\<not>(Atom a) | a. Atom a \<notin> M}"
  lemma "wm_basic M \<Longrightarrow> close_world M = close_neg (M \<union> {Atom (Eq a a) | a. True})"
    unfolding close_world_def close_neg_def wm_basic_def
    apply clarsimp
    apply (auto 0 3)
    by (metis atom.exhaust)


  abbreviation cw_entailment (infix "\<^sup>c\<TTurnstile>\<^sub>=" 53) where
    "M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<equiv> close_world M \<TTurnstile> \<phi>"


  lemma
    close_world_extensive: "M \<subseteq> close_world M" and
    close_world_idem[simp]: "close_world (close_world M) = close_world M"
    by (auto simp: close_world_def)

  lemma in_close_world_conv:
    "\<phi> \<in> close_world M \<longleftrightarrow> (
        \<phi>\<in>M
      \<or> (\<exists>p as. \<phi>=\<^bold>\<not>(Atom (predAtm p as)) \<and> Atom (predAtm p as)\<notin>M)
      \<or> (\<exists>a. \<phi>=Atom (Eq a a))
      \<or> (\<exists>a b. \<phi>=\<^bold>\<not>(Atom (Eq a b)) \<and> a\<noteq>b)
    )"
    by (auto simp: close_world_def)

  lemma valuation_aux_1:
    fixes M :: world_model and \<phi> :: "object atom formula"
    defines "C \<equiv> close_world M"
    assumes A: "\<forall>\<phi>\<in>C. \<A> \<Turnstile> \<phi>"
    shows "\<A> = valuation M"
    using A unfolding C_def
    apply -
    apply (auto simp: in_close_world_conv valuation_def Ball_def intro!: ext split: atom.split)
    apply (metis formula_semantics.simps(1) formula_semantics.simps(3))
    apply (metis formula_semantics.simps(1) formula_semantics.simps(3))
    by (metis atom.collapse(2) formula_semantics.simps(1) is_predAtm_def)



  lemma valuation_aux_2:
    assumes "wm_basic M"
    shows "(\<forall>G\<in>close_world M. valuation M \<Turnstile> G)"
    using assms unfolding wm_basic_def
    by (force simp: in_close_world_conv valuation_def elim: is_predAtom.elims)

  lemma val_imp_close_world: "valuation M \<Turnstile> \<phi> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi>"
    unfolding entailment_def
    using valuation_aux_1
    by blast

  lemma close_world_imp_val:
    "wm_basic M \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
    unfolding entailment_def using valuation_aux_2 by blast

  text \<open>Main theorem of this section:
    If a world model \<open>M\<close> contains only atoms, its induced valuation
    satisfies a formula \<open>\<phi>\<close> if and only if the closure of \<open>M\<close> entails \<open>\<phi>\<close>.

    Note that there are no syntactic restrictions on \<open>\<phi>\<close>,
    in particular, \<open>\<phi>\<close> may contain negation.
  \<close>
  theorem valuation_iff_close_world:
    assumes "wm_basic M"
    shows "valuation M \<Turnstile> \<phi> \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi>"
    using assms val_imp_close_world close_world_imp_val by blast


subsubsection \<open>Proper Generalization\<close>
text \<open>Adding negation and equality is a proper generalization of the
  case without negation and equality\<close>

fun is_STRIPS_fmla :: "'ent atom formula \<Rightarrow> bool" where
  "is_STRIPS_fmla (Atom (predAtm _ _)) \<longleftrightarrow> True"
| "is_STRIPS_fmla (\<bottom>) \<longleftrightarrow> True"
| "is_STRIPS_fmla (\<phi>\<^sub>1 \<^bold>\<and> \<phi>\<^sub>2) \<longleftrightarrow> is_STRIPS_fmla \<phi>\<^sub>1 \<and> is_STRIPS_fmla \<phi>\<^sub>2"
| "is_STRIPS_fmla (\<phi>\<^sub>1 \<^bold>\<or> \<phi>\<^sub>2) \<longleftrightarrow> is_STRIPS_fmla \<phi>\<^sub>1 \<and> is_STRIPS_fmla \<phi>\<^sub>2"
| "is_STRIPS_fmla (\<^bold>\<not>\<bottom>) \<longleftrightarrow> True"
| "is_STRIPS_fmla _ \<longleftrightarrow> False"

lemma aux1: "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>; valuation M \<Turnstile> \<phi>; \<forall>G\<in>M. \<A> \<Turnstile> G\<rbrakk> \<Longrightarrow> \<A> \<Turnstile> \<phi>"
  apply(induction \<phi> rule: is_STRIPS_fmla.induct)
  by (auto simp: valuation_def)

lemma aux2: "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>; \<forall>\<A>. (\<forall>G\<in>M. \<A> \<Turnstile> G) \<longrightarrow> \<A> \<Turnstile> \<phi>\<rbrakk> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
  apply(induction \<phi> rule: is_STRIPS_fmla.induct)
  apply simp_all
  apply (metis in_close_world_conv valuation_aux_2)
  using in_close_world_conv valuation_aux_2 apply blast
  using in_close_world_conv valuation_aux_2 by auto


lemma valuation_iff_STRIPS:
  assumes "wm_basic M"
  assumes "is_STRIPS_fmla \<phi>"
  shows "valuation M \<Turnstile> \<phi> \<longleftrightarrow> M \<TTurnstile> \<phi>"
proof -
  have aux1: "\<And>\<A>. \<lbrakk>valuation M \<Turnstile> \<phi>; \<forall>G\<in>M. \<A> \<Turnstile> G\<rbrakk> \<Longrightarrow> \<A> \<Turnstile> \<phi>"
    using assms apply(induction \<phi> rule: is_STRIPS_fmla.induct)
    by (auto simp: valuation_def)
  have aux2: "\<lbrakk>\<forall>\<A>. (\<forall>G\<in>M. \<A> \<Turnstile> G) \<longrightarrow> \<A> \<Turnstile> \<phi>\<rbrakk> \<Longrightarrow> valuation M \<Turnstile> \<phi>"
    using assms
    apply(induction \<phi> rule: is_STRIPS_fmla.induct)
    apply simp_all
    apply (metis in_close_world_conv valuation_aux_2)
    using in_close_world_conv valuation_aux_2 apply blast
    using in_close_world_conv valuation_aux_2 by auto
  show ?thesis
    by (auto simp: entailment_def intro: aux1 aux2)
qed

text \<open>Our extension to negation and equality is a proper generalization of the
  standard STRIPS semantics for formula without negation and equality\<close>
theorem proper_STRIPS_generalization:
  "\<lbrakk>wm_basic M; is_STRIPS_fmla \<phi>\<rbrakk> \<Longrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= \<phi> \<longleftrightarrow> M \<TTurnstile> \<phi>"
  by (simp add: valuation_iff_close_world[symmetric] valuation_iff_STRIPS)

subsection \<open>STRIPS Semantics\<close>

text \<open>For this section, we fix a domain \<open>D\<close>, using Isabelle's
  locale mechanism.\<close>
locale ast_domain =
  fixes D :: ast_domain
begin
  text \<open>It seems to be agreed upon that, in case of a contradictory effect,
    addition overrides deletion. We model this behaviour by first executing
    the deletions, and then the additions.\<close>
  fun apply_effect :: "object ast_effect \<Rightarrow> world_model \<Rightarrow> world_model"
  where
     "apply_effect (Effect a d) s = (s - set d) \<union> (set a)"

  text \<open>Execute a ground action\<close>
  definition execute_ground_action :: "ground_action \<Rightarrow> world_model \<Rightarrow> world_model"
  where
    "execute_ground_action a M = apply_effect (effect a) M"

  text \<open>Predicate to model that the given list of action instances is
    executable, and transforms an initial world model \<open>M\<close> into a final
    model \<open>M'\<close>.

    Note that this definition over the list structure is more convenient in HOL
    than to explicitly define an indexed sequence \<open>M\<^sub>0\<dots>M\<^sub>N\<close> of intermediate world
     models, as done in [Lif87].
  \<close>
  fun ground_action_path
    :: "world_model \<Rightarrow> ground_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
  | "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition \<alpha>
    \<and> ground_action_path (execute_ground_action \<alpha> M) \<alpha>s M'"

  text \<open>Function equations as presented in paper,
    with inlined @{const execute_ground_action}.\<close>
  lemma ground_action_path_in_paper:
    "ground_action_path M [] M' \<longleftrightarrow> (M = M')"
    "ground_action_path M (\<alpha>#\<alpha>s) M' \<longleftrightarrow> M \<^sup>c\<TTurnstile>\<^sub>= precondition \<alpha>
    \<and> (ground_action_path (apply_effect (effect \<alpha>) M) \<alpha>s M')"
    by (auto simp: execute_ground_action_def)

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>



subsection \<open>Well-Formedness of PDDL\<close>

(* Well-formedness *)

(*
  Compute signature: predicate/arity
  Check that all atoms (schemas and facts) satisfy signature

  for action:
    Check that used parameters \<subseteq> declared parameters

  for init/goal: Check that facts only use declared objects
*)


fun ty_term where
  "ty_term varT objT (term.VAR v) = varT v"
| "ty_term varT objT (term.CONST c) = objT c"


lemma ty_term_mono: "varT \<subseteq>\<^sub>m varT' \<Longrightarrow> objT \<subseteq>\<^sub>m objT' \<Longrightarrow>
  ty_term varT objT \<subseteq>\<^sub>m ty_term varT' objT'"
  apply (rule map_leI)
  subgoal for x v
    apply (cases x)
    apply (auto dest: map_leD)
    done
  done


context ast_domain begin

  text \<open>The signature is a partial function that maps the predicates
    of the domain to lists of argument types.\<close>
  definition sig :: "predicate \<rightharpoonup> type list" where
    "sig \<equiv> map_of (map (\<lambda>PredDecl p n \<Rightarrow> (p,n)) (predicates D))"

  text \<open>We use a flat subtype hierarchy, where every type is a subtype
    of object, and there are no other subtype relations.

    Note that we do not need to restrict this relation to declared types,
    as we will explicitly ensure that all types used in the problem are
    declared.
    \<close>

  fun subtype_edge where
    "subtype_edge (ty,superty) = (superty,ty)"

  definition "subtype_rel \<equiv> set (map subtype_edge (types D))"

  (*
  definition "subtype_rel \<equiv> {''object''}\<times>UNIV"
  *)

  definition of_type :: "type \<Rightarrow> type \<Rightarrow> bool" where
    "of_type oT T \<equiv> set (primitives oT) \<subseteq> subtype_rel\<^sup>* `` set (primitives T)"
  text \<open>This checks that every primitive on the LHS is contained in or a
    subtype of a primitive on the RHS\<close>


  text \<open>For the next few definitions, we fix a partial function that maps
    a polymorphic entity type @{typ "'e"} to types. An entity can be
    instantiated by variables or objects later.\<close>
  context
    fixes ty_ent :: "'ent \<rightharpoonup> type"  \<comment> \<open>Entity's type, None if invalid\<close>
  begin

    text \<open>Checks whether an entity has a given type\<close>
    definition is_of_type :: "'ent \<Rightarrow> type \<Rightarrow> bool" where
      "is_of_type v T \<longleftrightarrow> (
        case ty_ent v of
          Some vT \<Rightarrow> of_type vT T
        | None \<Rightarrow> False)"

    fun wf_pred_atom :: "predicate \<times> 'ent list \<Rightarrow> bool" where
      "wf_pred_atom (p,vs) \<longleftrightarrow> (
        case sig p of
          None \<Rightarrow> False
        | Some Ts \<Rightarrow> list_all2 is_of_type vs Ts)"

    text \<open>Predicate-atoms are well-formed if their arguments match the
      signature, equalities are well-formed if the arguments are valid
      objects (have a type).

      TODO: We could check that types may actually overlap
    \<close>
    fun wf_atom :: "'ent atom \<Rightarrow> bool" where
      "wf_atom (predAtm p vs) \<longleftrightarrow> wf_pred_atom (p,vs)"
    | "wf_atom (Eq a b) \<longleftrightarrow> ty_ent a \<noteq> None \<and> ty_ent b \<noteq> None"

    text \<open>A formula is well-formed if it consists of valid atoms,
      and does not contain negations, except for the encoding \<open>\<^bold>\<not>\<bottom>\<close> of true.
    \<close>
    fun wf_fmla :: "('ent atom) formula \<Rightarrow> bool" where
      "wf_fmla (Atom a) \<longleftrightarrow> wf_atom a"
    | "wf_fmla (\<bottom>) \<longleftrightarrow> True"
    | "wf_fmla (\<phi>1 \<^bold>\<and> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"
    | "wf_fmla (\<phi>1 \<^bold>\<or> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"
    | "wf_fmla (\<^bold>\<not>\<phi>) \<longleftrightarrow> wf_fmla \<phi>"
    | "wf_fmla (\<phi>1 \<^bold>\<rightarrow> \<phi>2) \<longleftrightarrow> (wf_fmla \<phi>1 \<and> wf_fmla \<phi>2)"

    lemma "wf_fmla \<phi> = (\<forall>a\<in>atoms \<phi>. wf_atom a)"
      by (induction \<phi>) auto

    (*lemma wf_fmla_add_simps[simp]: "wf_fmla (\<^bold>\<not>\<phi>) \<longleftrightarrow> \<phi>=\<bottom>"
      by (cases \<phi>) auto*)

    text \<open>Special case for a well-formed atomic predicate formula\<close>
    fun wf_fmla_atom where
      "wf_fmla_atom (Atom (predAtm a vs)) \<longleftrightarrow> wf_pred_atom (a,vs)"
    | "wf_fmla_atom _ \<longleftrightarrow> False"

    lemma wf_fmla_atom_alt: "wf_fmla_atom \<phi> \<longleftrightarrow> is_predAtom \<phi> \<and> wf_fmla \<phi>"
      by (cases \<phi> rule: wf_fmla_atom.cases) auto

    text \<open>An effect is well-formed if the added and removed formulas
      are atomic\<close>
    fun wf_effect where
      "wf_effect (Effect a d) \<longleftrightarrow>
          (\<forall>ae\<in>set a. wf_fmla_atom ae)
        \<and> (\<forall>de\<in>set d.  wf_fmla_atom de)"

  end \<comment> \<open>Context fixing \<open>ty_ent\<close>\<close>


  definition constT :: "object \<rightharpoonup> type" where
    "constT \<equiv> map_of (consts D)"

  text \<open>An action schema is well-formed if the parameter names are distinct,
    and the precondition and effect is well-formed wrt.\ the parameters.
  \<close>
  fun wf_action_schema :: "ast_action_schema \<Rightarrow> bool" where
    "wf_action_schema (Action_Schema n params pre eff) \<longleftrightarrow> (
      let
        tyt = ty_term (map_of params) constT
      in
        distinct (map fst params)
      \<and> wf_fmla tyt pre
      \<and> wf_effect tyt eff)"

  text \<open>A type is well-formed if it consists only of declared primitive types,
     and the type object.\<close>
  fun wf_type where
    "wf_type (Either Ts) \<longleftrightarrow> set Ts \<subseteq> insert ''object'' (fst`set (types D))"

  text \<open>A predicate is well-formed if its argument types are well-formed.\<close>
  fun wf_predicate_decl where
    "wf_predicate_decl (PredDecl p Ts) \<longleftrightarrow> (\<forall>T\<in>set Ts. wf_type T)"

  text \<open>The types declaration is well-formed, if all supertypes are declared types (or object)\<close>
  definition "wf_types \<equiv> snd`set (types D) \<subseteq> insert ''object'' (fst`set (types D))"

  text \<open>A domain is well-formed if
    \<^item> there are no duplicate declared predicate names,
    \<^item> all declared predicates are well-formed,
    \<^item> there are no duplicate action names,
    \<^item> and all declared actions are well-formed
    \<close>
  definition wf_domain :: "bool" where
    "wf_domain \<equiv>
      wf_types
    \<and> distinct (map (predicate_decl.pred) (predicates D))
    \<and> (\<forall>p\<in>set (predicates D). wf_predicate_decl p)
    \<and> distinct (map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (consts D). wf_type T)
    \<and> distinct (map ast_action_schema.name (actions D))
    \<and> (\<forall>a\<in>set (actions D). wf_action_schema a)
    "

end \<comment> \<open>locale \<open>ast_domain\<close>\<close>

text \<open>We fix a problem, and also include the definitions for the domain
  of this problem.\<close>
locale ast_problem = ast_domain "domain P"
  for P :: ast_problem
begin
  text \<open>We refer to the problem domain as \<open>D\<close>\<close>
  abbreviation "D \<equiv> ast_problem.domain P"

  definition objT :: "object \<rightharpoonup> type" where
    "objT \<equiv> map_of (objects P) ++ constT"

  lemma objT_alt: "objT = map_of (consts D @ objects P)"
    unfolding objT_def constT_def
    apply (clarsimp)
    done

  definition wf_fact :: "fact \<Rightarrow> bool" where
    "wf_fact = wf_pred_atom objT"

  text \<open>This definition is needed for well-formedness of the initial model,
    and forward-references to the concept of world model.
  \<close>
  definition wf_world_model where
    "wf_world_model M = (\<forall>f\<in>M. wf_fmla_atom objT f)"

  (*Note: current semantics assigns each object a unique type *)
  definition wf_problem where
    "wf_problem \<equiv>
      wf_domain
    \<and> distinct (map fst (objects P) @ map fst (consts D))
    \<and> (\<forall>(n,T)\<in>set (objects P). wf_type T)
    \<and> distinct (init P)
    \<and> wf_world_model (set (init P))
    \<and> wf_fmla objT (goal P)
    "

  fun wf_effect_inst :: "object ast_effect \<Rightarrow> bool" where
    "wf_effect_inst (Effect (a) (d))
      \<longleftrightarrow> (\<forall>a\<in>set a \<union> set d. wf_fmla_atom objT a)"

  lemma wf_effect_inst_alt: "wf_effect_inst eff = wf_effect objT eff"
    by (cases eff) auto

end \<comment> \<open>locale \<open>ast_problem\<close>\<close>

text \<open>Locale to express a well-formed domain\<close>
locale wf_ast_domain = ast_domain +
  assumes wf_domain: wf_domain

text \<open>Locale to express a well-formed problem\<close>
locale wf_ast_problem = ast_problem P for P +
  assumes wf_problem: wf_problem
begin
  sublocale wf_ast_domain "domain P"
    apply unfold_locales
    using wf_problem
    unfolding wf_problem_def by simp

end \<comment> \<open>locale \<open>wf_ast_problem\<close>\<close>

subsection \<open>PDDL Semantics\<close>

(* Semantics *)

(*  To apply plan_action:
    find action schema, instantiate, check precond, apply effect
*)



context ast_domain begin

  definition resolve_action_schema :: "name \<rightharpoonup> ast_action_schema" where
    "resolve_action_schema n = index_by ast_action_schema.name (actions D) n"

  fun subst_term where
    "subst_term psubst (term.VAR x) = psubst x"
  | "subst_term psubst (term.CONST c) = c"

  text \<open>To instantiate an action schema, we first compute a substitution from
    parameters to objects, and then apply this substitution to the
    precondition and effect. The substitution is applied via the \<open>map_xxx\<close>
    functions generated by the datatype package.
    \<close>
  fun instantiate_action_schema
    :: "ast_action_schema \<Rightarrow> object list \<Rightarrow> ground_action"
  where
    "instantiate_action_schema (Action_Schema n params pre eff) args = (let
        tsubst = subst_term (the o (map_of (zip (map fst params) args)));
        pre_inst = (map_formula o map_atom) tsubst pre;
        eff_inst = (map_ast_effect) tsubst eff
      in
        Ground_Action pre_inst eff_inst
      )"

end \<comment> \<open>Context of \<open>ast_domain\<close>\<close>


context ast_problem begin

  text \<open>Initial model\<close>
  definition I :: "world_model" where
    "I \<equiv> set (init P)"


  text \<open>Resolve a plan action and instantiate the referenced action schema.\<close>
  fun resolve_instantiate :: "plan_action \<Rightarrow> ground_action" where
    "resolve_instantiate (PAction n args) =
      instantiate_action_schema
        (the (resolve_action_schema n))
        args"

  text \<open>Check whether object has specified type\<close>
  definition "is_obj_of_type n T \<equiv> case objT n of
    None \<Rightarrow> False
  | Some oT \<Rightarrow> of_type oT T"

  text \<open>We can also use the generic \<open>is_of_type\<close> function.\<close>
  lemma is_obj_of_type_alt: "is_obj_of_type = is_of_type objT"
    apply (intro ext)
    unfolding is_obj_of_type_def is_of_type_def by auto


  text \<open>HOL encoding of matching an action's formal parameters against an
    argument list.
    The parameters of the action are encoded as a list of \<open>name\<times>type\<close> pairs,
    such that we map it to a list of types first. Then, the list
    relator @{const list_all2} checks that arguments and types have the same
    length, and each matching pair of argument and type
    satisfies the predicate @{const is_obj_of_type}.
  \<close>
  definition "action_params_match a args
    \<equiv> list_all2 is_obj_of_type args (map snd (parameters a))"

  text \<open>At this point, we can define well-formedness of a plan action:
    The action must refer to a declared action schema, the arguments must
    be compatible with the formal parameters' types.
  \<close>
 (* Objects are valid and match parameter types *)
  fun wf_plan_action :: "plan_action \<Rightarrow> bool" where
    "wf_plan_action (PAction n args) = (
      case resolve_action_schema n of
        None \<Rightarrow> False
      | Some a \<Rightarrow>
          action_params_match a args
        \<and> wf_effect_inst (effect (instantiate_action_schema a args))
        )"
  text \<open>
    TODO: The second conjunct is redundant, as instantiating a well formed
      action with valid objects yield a valid effect.
  \<close>



  text \<open>A sequence of plan actions form a path, if they are well-formed and
    their instantiations form a path.\<close>
  definition plan_action_path
    :: "world_model \<Rightarrow> plan_action list \<Rightarrow> world_model \<Rightarrow> bool"
  where
    "plan_action_path M \<pi>s M' =
        ((\<forall>\<pi> \<in> set \<pi>s. wf_plan_action \<pi>)
      \<and> ground_action_path M (map resolve_instantiate \<pi>s) M')"

  text \<open>A plan is valid wrt.\ a given initial model, if it forms a path to a
    goal model \<close>
  definition valid_plan_from :: "world_model \<Rightarrow> plan \<Rightarrow> bool" where
    "valid_plan_from M \<pi>s = (\<exists>M'. plan_action_path M \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P))"

  (* Implementation note: resolve and instantiate already done inside
      enabledness check, redundancy! *)

  text \<open>Finally, a plan is valid if it is valid wrt.\ the initial world
    model @{const I}\<close>
  definition valid_plan :: "plan \<Rightarrow> bool"
    where "valid_plan \<equiv> valid_plan_from I"

  text \<open>Concise definition used in paper:\<close>
  lemma "valid_plan \<pi>s \<equiv> \<exists>M'. plan_action_path I \<pi>s M' \<and> M' \<^sup>c\<TTurnstile>\<^sub>= (goal P)"
    unfolding valid_plan_def valid_plan_from_def by auto


end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>



subsection \<open>Preservation of Well-Formedness\<close>

subsubsection \<open>Well-Formed Action Instances\<close>
text \<open>The goal of this section is to establish that well-formedness of
  world models is preserved by execution of well-formed plan actions.
\<close>

context ast_problem begin

  text \<open>As plan actions are executed by first instantiating them, and then
    executing the action instance, it is natural to define a well-formedness
    concept for action instances.\<close>

  fun wf_ground_action :: "ground_action \<Rightarrow> bool" where
    "wf_ground_action (Ground_Action pre eff) \<longleftrightarrow> (
        wf_fmla objT pre
      \<and> wf_effect objT eff
      )
    "

  text \<open>We first prove that instantiating a well-formed action schema will yield
    a well-formed action instance.

    We begin with some auxiliary lemmas before the actual theorem.
  \<close>

  lemma (in ast_domain) of_type_refl[simp, intro!]: "of_type T T"
    unfolding of_type_def by auto

  lemma (in ast_domain) of_type_trans[trans]:
    "of_type T1 T2 \<Longrightarrow> of_type T2 T3 \<Longrightarrow> of_type T1 T3"
    unfolding of_type_def
    by clarsimp (metis (no_types, hide_lams)
      Image_mono contra_subsetD order_refl rtrancl_image_idem)

  lemma is_of_type_map_ofE:
    assumes "is_of_type (map_of params) x T"
    obtains i xT where "i<length params" "params!i = (x,xT)" "of_type xT T"
    using assms
    unfolding is_of_type_def
    by (auto split: option.splits dest!: map_of_SomeD simp: in_set_conv_nth)

  lemma wf_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_atom tys a"
    shows "wf_atom tys' a"
  proof -
    have "list_all2 (is_of_type tys') xs Ts" if "list_all2 (is_of_type tys) xs Ts" for xs Ts
      using that
      apply induction
      by (auto simp: is_of_type_def split: option.splits dest: map_leD[OF SS])
    with WF show ?thesis
      by (cases a) (auto split: option.splits dest: map_leD[OF SS])
  qed

  lemma wf_fmla_atom_mono:
    assumes SS: "tys \<subseteq>\<^sub>m tys'"
    assumes WF: "wf_fmla_atom tys a"
    shows "wf_fmla_atom tys' a"
  proof -
    have "list_all2 (is_of_type tys') xs Ts" if "list_all2 (is_of_type tys) xs Ts" for xs Ts
      using that
      apply induction
      by (auto simp: is_of_type_def split: option.splits dest: map_leD[OF SS])
    with WF show ?thesis
      by (cases a rule: wf_fmla_atom.cases) (auto split: option.splits dest: map_leD[OF SS])
  qed


  lemma constT_ss_objT: "constT \<subseteq>\<^sub>m objT"
    unfolding constT_def objT_def
    apply rule
    by (auto simp: map_add_def split: option.split)

  lemma wf_atom_constT_imp_objT: "wf_atom (ty_term Q constT) a \<Longrightarrow> wf_atom (ty_term Q objT) a"
    apply (erule wf_atom_mono[rotated])
    apply (rule ty_term_mono)
    by (simp_all add: constT_ss_objT)

  lemma wf_fmla_atom_constT_imp_objT: "wf_fmla_atom (ty_term Q constT) a \<Longrightarrow> wf_fmla_atom (ty_term Q objT) a"
    apply (erule wf_fmla_atom_mono[rotated])
    apply (rule ty_term_mono)
    by (simp_all add: constT_ss_objT)

  context
    fixes Q and f :: "variable \<Rightarrow> object"
    assumes INST: "is_of_type Q x T \<Longrightarrow> is_of_type objT (f x) T"
  begin

    lemma is_of_type_var_conv: "is_of_type (ty_term Q objT) (term.VAR x) T  \<longleftrightarrow> is_of_type Q x T"
      unfolding is_of_type_def by (auto)

    lemma is_of_type_const_conv: "is_of_type (ty_term Q objT) (term.CONST x) T  \<longleftrightarrow> is_of_type objT x T"
      unfolding is_of_type_def
      by (auto split: option.split)

    lemma INST': "is_of_type (ty_term Q objT) x T \<Longrightarrow> is_of_type objT (subst_term f x) T"
      apply (cases x) using INST apply (auto simp: is_of_type_var_conv is_of_type_const_conv)
      done


    lemma wf_inst_eq_aux: "Q x = Some T \<Longrightarrow> objT (f x) \<noteq> None"
      using INST[of x T] unfolding is_of_type_def
      by (auto split: option.splits)

    lemma wf_inst_eq_aux': "ty_term Q objT x = Some T \<Longrightarrow> objT (subst_term f x) \<noteq> None"
      by (cases x) (auto simp: wf_inst_eq_aux)


    lemma wf_inst_atom:
      assumes "wf_atom (ty_term Q constT) a"
      shows "wf_atom objT (map_atom (subst_term f) a)"
    proof -
      have X1: "list_all2 (is_of_type objT) (map (subst_term f) xs) Ts" if
        "list_all2 (is_of_type (ty_term Q objT)) xs Ts" for xs Ts
        using that
        apply induction
        using INST'
        by auto
      then show ?thesis
        using assms[THEN wf_atom_constT_imp_objT] wf_inst_eq_aux'
        by (cases a; auto split: option.splits)

    qed

    lemma wf_inst_formula_atom:
      assumes "wf_fmla_atom (ty_term Q constT) a"
      shows "wf_fmla_atom objT ((map_formula o map_atom o subst_term) f a)"
      using assms[THEN wf_fmla_atom_constT_imp_objT] wf_inst_atom
      apply (cases a rule: wf_fmla_atom.cases; auto split: option.splits)
      by (simp add: INST' list.rel_map(1) list_all2_mono)

    lemma wf_inst_effect:
      assumes "wf_effect (ty_term Q constT) \<phi>"
      shows "wf_effect objT ((map_ast_effect o subst_term) f \<phi>)"
      using assms
      proof (induction \<phi>)
        case (Effect x1a x2a)
        then show ?case using wf_inst_formula_atom by auto
      qed

    lemma wf_inst_formula:
      assumes "wf_fmla (ty_term Q constT) \<phi>"
      shows "wf_fmla objT ((map_formula o map_atom o subst_term) f \<phi>)"
      using assms
      by (induction \<phi>) (auto simp: wf_inst_atom dest: wf_inst_eq_aux)

  end



  text \<open>Instantiating a well-formed action schema with compatible arguments
    will yield a well-formed action instance.
  \<close>
  theorem wf_instantiate_action_schema:
    assumes "action_params_match a args"
    assumes "wf_action_schema a"
    shows "wf_ground_action (instantiate_action_schema a args)"
  proof (cases a)
    case [simp]: (Action_Schema name params pre eff)
    have INST:
      "is_of_type objT ((the \<circ> map_of (zip (map fst params) args)) x) T"
      if "is_of_type (map_of params) x T" for x T
      using that
      apply (rule is_of_type_map_ofE)
      using assms
      apply (clarsimp simp: Let_def)
      subgoal for i xT
        unfolding action_params_match_def
        apply (subst lookup_zip_idx_eq[where i=i];
          (clarsimp simp: list_all2_lengthD)?)
        apply (frule list_all2_nthD2[where p=i]; simp?)
        apply (auto
                simp: is_obj_of_type_alt is_of_type_def
                intro: of_type_trans
                split: option.splits)
        done
      done
    then show ?thesis
      using assms(2) wf_inst_formula wf_inst_effect
      by (fastforce split: term.splits simp: Let_def comp_apply[abs_def])
  qed
end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>



subsubsection \<open>Preservation\<close>

context ast_problem begin

  text \<open>We start by defining two shorthands for enabledness and execution of
    a plan action.\<close>

  text \<open>Shorthand for enabled plan action: It is well-formed, and the
    precondition holds for its instance.\<close>
  definition plan_action_enabled :: "plan_action \<Rightarrow> world_model \<Rightarrow> bool" where
    "plan_action_enabled \<pi> M
      \<longleftrightarrow> wf_plan_action \<pi> \<and> M \<^sup>c\<TTurnstile>\<^sub>= precondition (resolve_instantiate \<pi>)"

  text \<open>Shorthand for executing a plan action: Resolve, instantiate, and
    apply effect\<close>
  definition execute_plan_action :: "plan_action \<Rightarrow> world_model \<Rightarrow> world_model"
    where "execute_plan_action \<pi> M
      = (apply_effect (effect (resolve_instantiate \<pi>)) M)"

  text \<open>The @{const plan_action_path} predicate can be decomposed naturally
    using these shorthands: \<close>
  lemma plan_action_path_Nil[simp]: "plan_action_path M [] M' \<longleftrightarrow> M'=M"
    by (auto simp: plan_action_path_def)

  lemma plan_action_path_Cons[simp]:
    "plan_action_path M (\<pi>#\<pi>s) M' \<longleftrightarrow>
      plan_action_enabled \<pi> M
    \<and> plan_action_path (execute_plan_action \<pi> M) \<pi>s M'"
    by (auto
      simp: plan_action_path_def execute_plan_action_def
            execute_ground_action_def plan_action_enabled_def)



end \<comment> \<open>Context of \<open>ast_problem\<close>\<close>

context wf_ast_problem begin
  text \<open>The initial world model is well-formed\<close>
  lemma wf_I: "wf_world_model I"
    using wf_problem
    unfolding I_def wf_world_model_def wf_problem_def
    apply(safe) subgoal for f by (induction f) auto
    done

  text \<open>Application of a well-formed effect preserves well-formedness
    of the model\<close>
  lemma wf_apply_effect:
    assumes "wf_effect objT e"
    assumes "wf_world_model s"
    shows "wf_world_model (apply_effect e s)"
    using assms wf_problem
    unfolding wf_world_model_def wf_problem_def wf_domain_def
    by (cases e) (auto split: formula.splits prod.splits)

  text \<open>Execution of plan actions preserves well-formedness\<close>
  theorem wf_execute:
    assumes "plan_action_enabled \<pi> s"
    assumes "wf_world_model s"
    shows "wf_world_model (execute_plan_action \<pi> s)"
    using assms
  proof (cases \<pi>)
    case [simp]: (PAction name args)

    from \<open>plan_action_enabled \<pi> s\<close> have "wf_plan_action \<pi>"
      unfolding plan_action_enabled_def by auto
    then obtain a where
      "resolve_action_schema name = Some a" and
      T: "action_params_match a args"
      by (auto split: option.splits)

    from wf_domain have
      [simp]: "distinct (map ast_action_schema.name (actions D))"
      unfolding wf_domain_def by auto

    from \<open>resolve_action_schema name = Some a\<close> have
      "a \<in> set (actions D)"
      unfolding resolve_action_schema_def by auto
    with wf_domain have "wf_action_schema a"
      unfolding wf_domain_def by auto
    hence "wf_ground_action (resolve_instantiate \<pi>)"
      using \<open>resolve_action_schema name = Some a\<close> T
        wf_instantiate_action_schema
      by auto
    thus ?thesis
      apply (simp add: execute_plan_action_def execute_ground_action_def)
      apply (rule wf_apply_effect)
      apply (cases "resolve_instantiate \<pi>"; simp)
      by (rule \<open>wf_world_model s\<close>)
  qed

  theorem wf_execute_compact_notation:
    "plan_action_enabled \<pi> s \<Longrightarrow> wf_world_model s
    \<Longrightarrow> wf_world_model (execute_plan_action \<pi> s)"
    by (rule wf_execute)


  text \<open>Execution of a plan preserves well-formedness\<close>
  corollary wf_plan_action_path:
    assumes "wf_world_model M" and " plan_action_path M \<pi>s M'"
    shows "wf_world_model M'"
    using assms
    by (induction \<pi>s arbitrary: M) (auto intro: wf_execute)


end \<comment> \<open>Context of \<open>wf_ast_problem\<close>\<close>




end \<comment> \<open>Theory\<close>
