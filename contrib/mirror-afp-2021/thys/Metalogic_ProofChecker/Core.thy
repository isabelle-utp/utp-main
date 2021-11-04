
section \<open>Core Inference system\<close>

text \<open>Contains just the stuff necessary for the definition of the Inference system\<close>

theory Core
  imports Main
begin

text \<open>Basic types \<close>
type_synonym name = String.literal
type_synonym indexname = "name \<times> int"

type_synonym "class" = String.literal

type_synonym "sort" = "class set"
abbreviation "full_sort \<equiv> ({}::sort)"

(* Name duplication with Fv in term, change later*)
datatype variable = Free name | Var indexname

datatype "typ" =
  is_Ty: Ty name "typ list" |
  is_Tv: Tv variable sort

datatype "term" =
  is_Ct: Ct name "typ" |
  is_Fv: Fv variable "typ" |
  is_Bv: Bv nat |
  is_Abs: Abs "typ" "term" |
  is_App: App "term" "term" (infixl "$" 100)

abbreviation "mk_fun_typ S T \<equiv> Ty STR ''fun'' [S,T]" 
notation mk_fun_typ (infixr "\<rightarrow>" 100)

text \<open>Collect variables in a term\<close>

fun fv :: "term \<Rightarrow> (variable \<times> typ) set" where
  "fv (Ct _ _) = {}"
| "fv (Fv v T) = {(v, T)}"
| "fv (Bv _) = {}"
| "fv (Abs _ body) = fv body"
| "fv (t $ u) = fv t \<union> fv u"
definition [simp]: "FV S = (\<Union>s\<in>S . fv s)"

text \<open>Typ/term instantiations\<close>

fun tsubstT :: "typ \<Rightarrow> (variable \<Rightarrow> sort \<Rightarrow> typ) \<Rightarrow> typ" where 
  "tsubstT (Tv a s) \<rho> = \<rho> a s"
| "tsubstT (Ty \<kappa> \<sigma>s) \<rho> = Ty \<kappa> (map (\<lambda>\<sigma>. tsubstT \<sigma> \<rho>) \<sigma>s)"
definition "tinstT T1 T2 \<equiv> \<exists>\<rho>. tsubstT T2 \<rho> = T1"

fun tsubst :: "term \<Rightarrow> (variable \<Rightarrow> sort \<Rightarrow> typ) \<Rightarrow> term" where
  "tsubst (Ct s T) \<rho> = Ct s (tsubstT T \<rho>)"
| "tsubst (Fv v T) \<rho> = Fv v (tsubstT T \<rho>)"
| "tsubst (Bv i) _ = Bv i"
| "tsubst (Abs T t) \<rho> = Abs (tsubstT T \<rho>) (tsubst t \<rho>)"
| "tsubst (t $ u) \<rho> = tsubst t \<rho> $ tsubst u \<rho>"

text \<open>Typ of a term\<close>

inductive has_typ1 :: "typ list \<Rightarrow> term \<Rightarrow> typ \<Rightarrow> bool" ("_ \<turnstile>\<^sub>\<tau> _ : _" [51, 51, 51] 51) where
  "has_typ1 _ (Ct _ T) T"
| "i < length Ts \<Longrightarrow> has_typ1 Ts (Bv i) (nth Ts i)"
| "has_typ1 _ (Fv _ T) T"
| "has_typ1 (T#Ts) t T' \<Longrightarrow> has_typ1 Ts (Abs T t) (T \<rightarrow> T')"
| "has_typ1 Ts u U \<Longrightarrow> has_typ1 Ts t (U \<rightarrow> T) \<Longrightarrow>
      has_typ1 Ts (t $ u) T"
definition has_typ :: "term \<Rightarrow> typ \<Rightarrow> bool" ("\<turnstile>\<^sub>\<tau> _ : _" [51, 51] 51) where "has_typ t T = has_typ1 [] t T"

definition "typ_of t = (if \<exists>T . has_typ t T then Some (THE T . has_typ t T) else None)"

text\<open>More operations on terms\<close>

fun lift :: "term \<Rightarrow> nat \<Rightarrow> term" where
  "lift (Bv i) n = (if i \<ge> n then Bv (i+1) else Bv i)"
| "lift (Abs T body) n = Abs T (lift body (n+1))"
| "lift (App f t) n = App (lift f n) (lift t n)"
| "lift u n = u"

fun subst_bv2 :: "term \<Rightarrow> nat \<Rightarrow> term \<Rightarrow> term" where
  "subst_bv2 (Bv i) n u = (if i < n then Bv i
    else if i = n then u
    else (Bv (i - 1)))" 
| "subst_bv2 (Abs T body) n u = Abs T (subst_bv2 body (n + 1) (lift u 0))"
| "subst_bv2 (f $ t) n u = subst_bv2 f n u $ subst_bv2 t n u"
| "subst_bv2 t _ _ = t"

definition "subst_bv u t = subst_bv2 t 0 u"

fun bind_fv2 :: "(variable \<times> typ) \<Rightarrow> nat \<Rightarrow> term \<Rightarrow> term" where
  "bind_fv2 vT n (Fv v T) = (if vT = (v,T) then Bv n else Fv v T)"
| "bind_fv2 vT n (Abs T t) = Abs T (bind_fv2 vT (n+1) t)"
| "bind_fv2 vT n (f $ u) = bind_fv2 vT n f $ bind_fv2 vT n u"
| "bind_fv2 _ _ t = t"

definition "bind_fv vT t = bind_fv2 vT 0 t"

abbreviation "Abs_fv v T t \<equiv> Abs T (bind_fv (v,T) t)"

text \<open>Some typ/term constants\<close>

abbreviation "itselfT ty \<equiv> Ty STR ''itself'' [ty]"
abbreviation "constT name \<equiv> Ty name []"
abbreviation "propT \<equiv> constT STR ''prop''"

abbreviation "mk_eq t1 t2 \<equiv> Ct STR ''Pure.eq'' 
  (the (typ_of t1) \<rightarrow> (the (typ_of t2) \<rightarrow> propT)) $ t1 $ t2"
(* Because mk_eq works only with closed terms *)
abbreviation "mk_eq' ty t1 t2 \<equiv> Ct STR ''Pure.eq'' 
  (ty \<rightarrow> (ty \<rightarrow> propT)) $ t1 $ t2"
abbreviation mk_imp :: "term \<Rightarrow> term \<Rightarrow> term"  (infixr "\<longmapsto>" 51) where 
  "A \<longmapsto> B \<equiv> Ct STR ''Pure.imp'' (propT \<rightarrow> (propT \<rightarrow> propT)) $ A $ B"
abbreviation "mk_all x ty t \<equiv>
  Ct STR ''Pure.all'' ((ty \<rightarrow> propT) \<rightarrow> propT) $ Abs_fv x ty t"

text \<open>Order sorted signature\<close>

type_synonym osig = "(class rel \<times> (name \<rightharpoonup> (class \<rightharpoonup> sort list)))"

fun "subclass" :: "osig \<Rightarrow> class rel" where "subclass (cl, _) = cl"
fun tcsigs :: "osig \<Rightarrow> (name \<rightharpoonup> (class \<rightharpoonup> sort list))" where "tcsigs (_, ars) = ars"

text \<open>Relation in sorts\<close>

definition "class_leq sub c1 c2 = ((c1,c2) \<in> sub)"
definition "class_les sub c1 c2 = (class_leq sub c1 c2 \<and> \<not> class_leq sub c2 c1)"
definition "sort_leq sub s1 s2 = (\<forall>c\<^sub>2 \<in> s2 . \<exists>c\<^sub>1 \<in> s1. class_leq sub c\<^sub>1 c\<^sub>2)"

text \<open>Is a class/sort defined\<close>

definition "class_ex rel c = (c \<in> Field rel)"
definition "sort_ex rel S = (S \<subseteq> Field rel)"

text \<open>Normalizing sorts\<close>

definition "normalize_sort sub (S::sort)
  = {c \<in> S. \<not> (\<exists>c' \<in> S. class_les sub c' c)}"
abbreviation "normalized_sort sub S \<equiv> normalize_sort sub S = S"

definition "wf_sort sub S = (normalized_sort sub S \<and> sort_ex sub S)"

text \<open>Wellformedness of osig\<close>

definition [simp]: "wf_subclass rel = (trans rel \<and> antisym rel \<and> Refl rel)"

definition "complete_tcsigs sub tcs \<equiv> (\<forall>ars \<in> ran tcs . 
  \<forall>(c\<^sub>1, c\<^sub>2) \<in> sub . c\<^sub>1\<in>dom ars \<longrightarrow> c\<^sub>2\<in>dom ars)"

definition "coregular_tcsigs sub tcs \<equiv> (\<forall>ars \<in> ran tcs .
  \<forall>c\<^sub>1 \<in> dom ars. \<forall>c\<^sub>2 \<in> dom ars.
    (class_leq sub c\<^sub>1 c\<^sub>2 \<longrightarrow> list_all2 (sort_leq sub) (the (ars c\<^sub>1)) (the (ars c\<^sub>2))))" 

definition "consistent_length_tcsigs tcs \<equiv> (\<forall>ars \<in> ran tcs . 
  \<forall>ss\<^sub>1 \<in> ran ars. \<forall>ss\<^sub>2 \<in> ran ars. length ss\<^sub>1 = length ss\<^sub>2)"

definition "all_normalized_and_ex_tcsigs sub tcs \<equiv>
  (\<forall>ars \<in> ran tcs . \<forall>ss \<in> ran ars . \<forall>s \<in> set ss. wf_sort sub s)"

definition [simp]: "wf_tcsigs sub tcs \<longleftrightarrow>
    coregular_tcsigs sub tcs
  \<and> complete_tcsigs sub tcs
  \<and> consistent_length_tcsigs tcs
  \<and> all_normalized_and_ex_tcsigs sub tcs"

fun wf_osig where "wf_osig (sub, tcs) \<longleftrightarrow> wf_subclass sub \<and> wf_tcsigs sub tcs"

text \<open>Embedding typs into terms/Encoding of type classes\<close>

definition "mk_type ty = Ct STR ''Pure.type'' (Core.itselfT ty)"

abbreviation "mk_suffix (str::name) suff \<equiv> String.implode (String.explode str @ String.explode suff)"

abbreviation "classN \<equiv> STR ''_class''"
abbreviation "const_of_class name \<equiv> mk_suffix name classN"

definition "mk_of_class ty c =
  Ct (const_of_class c) (Core.itselfT ty \<rightarrow> propT) $ mk_type ty"

text \<open>Checking if a typ belongs to a sort\<close>

inductive has_sort :: "osig \<Rightarrow> typ \<Rightarrow> sort \<Rightarrow> bool" where
  has_sort_Tv[intro]: "sort_leq sub S S' \<Longrightarrow> has_sort (sub, tcs) (Tv a S) S'"
| has_sort_Ty: 
  "tcs \<kappa> = Some dm \<Longrightarrow> \<forall>c \<in> S. \<exists>Ss . dm c = Some Ss \<and> list_all2 (has_sort (sub, tcs)) Ts Ss
    \<Longrightarrow> has_sort (sub, tcs) (Ty \<kappa> Ts) S"

text \<open>Signatures \<close>

type_synonym signature = "(name \<rightharpoonup> typ) \<times> (name \<rightharpoonup> nat) \<times> osig"

fun const_type :: "signature \<Rightarrow> (name \<rightharpoonup> typ)" where "const_type (ctf, _, _) = ctf"
fun type_arity :: "signature \<Rightarrow> (name \<rightharpoonup> nat)" where "type_arity (_, arf, _) = arf"
fun osig :: "signature \<Rightarrow> osig" where "osig (_, _, oss) = oss"

(* Which typs and consts must be defined in a signature*)
fun is_std_sig where "is_std_sig (ctf, arf, _) \<longleftrightarrow>
    arf STR ''fun'' = Some 2 \<and> arf STR ''prop'' = Some 0 
  \<and> arf STR ''itself'' = Some 1
  \<and> ctf STR ''Pure.eq'' 
    = Some ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> ((Tv (Var (STR '''a'', 0)) full_sort) \<rightarrow> propT))
  \<and> ctf STR ''Pure.all'' = Some ((Tv (Var  (STR '''a'', 0)) full_sort \<rightarrow> propT) \<rightarrow> propT)
  \<and> ctf STR ''Pure.imp'' = Some (propT \<rightarrow> (propT \<rightarrow> propT))
  \<and> ctf STR ''Pure.type'' = Some (itselfT (Tv (Var (STR '''a'', 0)) full_sort))"

text \<open>Wellformedness checks\<close>

definition [simp]: "class_ok_sig \<Sigma> c \<equiv> class_ex (subclass (osig \<Sigma>)) c"

inductive wf_type :: "signature \<Rightarrow> typ \<Rightarrow> bool" where
  typ_ok_Ty: "type_arity \<Sigma> \<kappa> = Some (length Ts) \<Longrightarrow> \<forall>T\<in>set Ts . wf_type \<Sigma> T
    \<Longrightarrow> wf_type \<Sigma> (Ty \<kappa> Ts)"
| typ_ok_Tv[intro]: "wf_sort (subclass (osig \<Sigma>)) S \<Longrightarrow> wf_type \<Sigma> (Tv a S)"

inductive wf_term :: "signature \<Rightarrow> term \<Rightarrow> bool" where
  "wf_type \<Sigma> T \<Longrightarrow> wf_term \<Sigma> (Fv v T)"
| "wf_term \<Sigma> (Bv n)"
| "const_type \<Sigma> s = Some ty \<Longrightarrow> wf_type \<Sigma> T \<Longrightarrow> tinstT T ty \<Longrightarrow> wf_term \<Sigma> (Ct s T)"
| "wf_term \<Sigma> t \<Longrightarrow> wf_term \<Sigma> u \<Longrightarrow> wf_term \<Sigma> (t $ u)"
| "wf_type \<Sigma> T \<Longrightarrow> wf_term \<Sigma> t \<Longrightarrow> wf_term \<Sigma> (Abs T t)"

definition "wt_term \<Sigma> t \<equiv> wf_term \<Sigma> t \<and> (\<exists>T. has_typ t T)"

fun wf_sig :: "signature \<Rightarrow> bool" where                
  "wf_sig (ctf, arf, oss) = (wf_osig oss
  \<and> dom (tcsigs oss) = dom arf
  \<and> (\<forall>type \<in> dom (tcsigs oss). (\<forall>ars \<in> ran (the (tcsigs oss type)) . the (arf type) = length ars))
  \<and> (\<forall>ty \<in> Map.ran ctf . wf_type (ctf, arf, oss) ty))"

text \<open>Theories\<close>

type_synonym "theory" = "signature \<times> term set"

fun sig :: "theory \<Rightarrow> signature" where "sig (\<Sigma>, _) = \<Sigma>"
fun axioms :: "theory \<Rightarrow> term set" where "axioms (_, axs) = axs"

text \<open>Equality axioms, stated directly\<close>

abbreviation "tvariable a \<equiv> (Tv (Var (a, 0)) full_sort)"
abbreviation "variable x T \<equiv> Fv (Var (x, 0)) T"

abbreviation "aT \<equiv> tvariable STR '''a''"
abbreviation "bT \<equiv> tvariable STR '''b''"
abbreviation "x \<equiv> variable STR ''x'' aT"
abbreviation "y \<equiv> variable STR ''y'' aT"
abbreviation "z \<equiv> variable STR ''z'' aT"
abbreviation "f \<equiv> variable STR ''f'' (aT \<rightarrow> bT)"
abbreviation "g \<equiv> variable STR ''g'' (aT \<rightarrow> bT)"
abbreviation "P \<equiv> variable STR ''P'' (aT \<rightarrow> propT)"
abbreviation "Q \<equiv> variable STR ''Q'' (aT \<rightarrow> propT)"
abbreviation "A \<equiv> variable STR ''A'' propT"
abbreviation "B \<equiv> variable STR ''B'' propT"

definition "eq_reflexive_ax \<equiv> mk_eq x x"
definition "eq_symmetric_ax \<equiv> mk_eq x y \<longmapsto> mk_eq y x"
definition "eq_transitive_ax \<equiv> mk_eq x y \<longmapsto> mk_eq y z \<longmapsto> mk_eq x z"
definition "eq_intr_ax \<equiv> (A \<longmapsto> B) \<longmapsto> (B \<longmapsto> A) \<longmapsto> mk_eq A B"
definition "eq_elim_ax \<equiv> mk_eq A B \<longmapsto> A \<longmapsto> B"
definition "eq_combination_ax \<equiv> mk_eq f g \<longmapsto> mk_eq x y \<longmapsto> mk_eq (f $ x) (g $ y)"
definition "eq_abstract_rule_ax \<equiv> 
      (Ct STR ''Pure.all'' ((aT \<rightarrow> propT) \<rightarrow> propT) $ Abs aT (mk_eq' bT (f $ Bv 0) (g $ Bv 0)))
  \<longmapsto> mk_eq (Abs aT (f $ Bv 0)) (Abs aT (g $ Bv 0))"

hide_const (open) x y z f g P Q A B

abbreviation "eq_axs \<equiv> {eq_reflexive_ax, eq_symmetric_ax, eq_transitive_ax, eq_intr_ax, eq_elim_ax,
  eq_combination_ax, eq_abstract_rule_ax}"

text\<open>Wellformedness of theories\<close>

fun wf_theory where "wf_theory (\<Sigma>, axs) \<longleftrightarrow>
    (\<forall>p \<in> axs . wt_term \<Sigma> p \<and> has_typ p propT)
  \<and> is_std_sig \<Sigma> 
  \<and> wf_sig \<Sigma>
  \<and> eq_axs \<subseteq> axs"

text\<open>Wellformedness of typ antiations\<close>

definition [simp]: "wf_inst \<Theta> \<rho> \<equiv> 
  (\<forall>v S . \<rho> v S \<noteq> Tv v S \<longrightarrow>
    (has_sort (osig (sig \<Theta>)) (\<rho> v S) S) \<and> wf_type (sig \<Theta>) (\<rho> v S))"

text\<open>Inference system\<close>

inductive proves :: "theory \<Rightarrow> term set \<Rightarrow> term \<Rightarrow> bool" ("(_,_) \<turnstile> (_)" 50) for \<Theta> where
  axiom: "wf_theory \<Theta> \<Longrightarrow> A\<in>axioms \<Theta> \<Longrightarrow> wf_inst \<Theta> \<rho>
  \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> tsubst A \<rho>"
| "assume": "wf_term (sig \<Theta>) A \<Longrightarrow> has_typ A propT \<Longrightarrow> A \<in> \<Gamma> \<Longrightarrow> \<Theta>,\<Gamma> \<turnstile> A"
| forall_intro: "wf_theory \<Theta> \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> B \<Longrightarrow> (x,\<tau>) \<notin> FV \<Gamma> \<Longrightarrow> wf_type (sig \<Theta>)  \<tau>
  \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> mk_all x \<tau> B"
| forall_elim: "\<Theta>, \<Gamma> \<turnstile> Ct STR ''Pure.all'' ((\<tau> \<rightarrow> propT) \<rightarrow> propT) $ Abs \<tau> B
  \<Longrightarrow> has_typ a \<tau> \<Longrightarrow> wf_term (sig \<Theta>) a
  \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> subst_bv a B"
| implies_intro: "wf_theory \<Theta> \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> B \<Longrightarrow> wf_term (sig \<Theta>) A \<Longrightarrow> has_typ A propT 
  \<Longrightarrow> \<Theta>, \<Gamma> - {A} \<turnstile> A \<longmapsto> B"
| implies_elim: "\<Theta>, \<Gamma>\<^sub>1 \<turnstile> A \<longmapsto> B \<Longrightarrow> \<Theta>, \<Gamma>\<^sub>2 \<turnstile> A \<Longrightarrow> \<Theta>, \<Gamma>\<^sub>1\<union>\<Gamma>\<^sub>2 \<turnstile> B"
| of_class: "wf_theory \<Theta>
  \<Longrightarrow> const_type (sig \<Theta>) (const_of_class c) = Some (Core.itselfT aT \<rightarrow> propT)
  \<Longrightarrow> wf_type (sig \<Theta>) T
  \<Longrightarrow> has_sort (osig (sig \<Theta>)) T {c}
  \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> mk_of_class T c"
(* Stuff about equality that cannot be expressed as an axiom*)
| \<beta>_conversion: "wf_theory \<Theta> \<Longrightarrow> wt_term (sig \<Theta>) (Abs T t) \<Longrightarrow> wf_term (sig \<Theta>) u \<Longrightarrow> has_typ u T 
  \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> mk_eq (Abs T t $ u) (subst_bv u t)"
| eta: "wf_theory \<Theta> \<Longrightarrow> wf_term (sig \<Theta>) t \<Longrightarrow> has_typ t (\<tau> \<rightarrow> \<tau>')
  \<Longrightarrow> \<Theta>, \<Gamma> \<turnstile> mk_eq (Abs \<tau> (t $ Bv 0)) t"

text\<open>Ensure no garbage in \<open>\<Theta>,\<Gamma>\<close>\<close>

definition proves' :: "theory \<Rightarrow> term set \<Rightarrow> term \<Rightarrow> bool" ("(_,_) \<tturnstile> (_)" 51) where
  "proves' \<Theta> \<Gamma> t \<equiv> wf_theory \<Theta> \<and> (\<forall>h \<in> \<Gamma> . wf_term (sig \<Theta>) h \<and> has_typ h propT) \<and> \<Theta>, \<Gamma> \<turnstile> t"

hide_const (open) aT bT

end