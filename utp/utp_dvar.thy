subsection {* Deep UTP variables *}

theory utp_dvar
  imports utp_var
begin

text {* UTP variables represented by record fields are shallow, nameless entities. They are fundamentally
        static in nature, since a new record field can only be introduced definitionally and cannot be
        otherwise arbitrarily created. They are nevertheless very useful as proof automation is excellent,
        and they can fully make use of the Isabelle type system. However, for constructs like alphabet
        extension that can introduce new variables they are inadequate. As a result we also introduce
        a notion of deep variables to complement them. A deep variable is not a record field, but
        rather a key within a store map that records the values of all deep variables. As such the
        Isabelle type system is agnostic of them, and the creation of a new deep variable does not
        change the portion of the alphabet specified by the type system.

        In order to create a type of stores (or bindings) for variables, we must fix a universe
        for the variable valuations. This is the major downside of deep variables -- they cannot
        have any type, but only a type whose cardinality is up to $\mathfrak{c}$, the cardinality
        of the continuum. This is why we need both deep and shallow variables, as the latter are
        unrestricted in this respect. Each deep variable will therefore specify the cardinality
        of the type it possesses. *}

subsection {* Cardinalities *}

text {* We first fix a datatype representing all possible cardinalities for a deep variable. These
        include finite cardinalities, $\aleph_0$ (countable), and $\mathfrak{c}$ (uncountable up
        to the continuum). *}

datatype ucard = fin nat | aleph0 ("\<aleph>\<^sub>0") | cont ("\<c>")

text {* Our universe is simply the set of natural numbers; this is sufficient for all types up
        to cardinality $\mathfrak{c}$. *}

type_synonym uuniv = "nat set"

text {* We introduce a function that gives the set of values within our universe of the given
        cardinality. Since a cardinality of 0 is no proper type, we use finite cardinality 0 to 
        mean cardinality 1, 1 to mean 2 etc. *}

fun uuniv :: "ucard \<Rightarrow> uuniv set" ("\<U>'(_')") where
"\<U>(fin n) = {{x} | x. x \<le> n}" |
"\<U>(\<aleph>\<^sub>0) = {{x} | x. True}" |
"\<U>(\<c>) = UNIV" 

text {* We also define the following function that gives the cardinality of a type within
        the @{class continuum} type class. *}

definition ucard_of :: "'a::continuum itself \<Rightarrow> ucard" where
"ucard_of x = (if (finite (UNIV :: 'a set))
                  then fin(card(UNIV :: 'a set) - 1)
               else if (countable (UNIV :: 'a set))
                  then \<aleph>\<^sub>0
               else \<c>)"

syntax
  "_ucard" :: "type \<Rightarrow> ucard" ("UCARD'(_')")

translations
  "UCARD('a)" == "CONST ucard_of (TYPE('a))"

lemma ucard_of_finite [simp]:
  "finite (UNIV :: 'a::continuum set) \<Longrightarrow> UCARD('a) = fin(card(UNIV :: 'a set) - 1)"
  by (simp add: ucard_of_def)

lemma ucard_of_countably_infinite [simp]:
  "\<lbrakk> countable(UNIV :: 'a::continuum set); infinite(UNIV :: 'a set) \<rbrakk> \<Longrightarrow> UCARD('a) = \<aleph>\<^sub>0"
  by (simp add: ucard_of_def)

lemma ucard_of_uncountably_infinite [simp]:
  "uncountable (UNIV :: 'a set) \<Longrightarrow> UCARD('a :: continuum) = \<c>"
  apply (simp add: ucard_of_def)
  using countable_finite apply blast
done

subsection {* Injection functions *}

definition uinject_finite :: "'a::finite \<Rightarrow> uuniv" where
"uinject_finite x = {to_nat_fin x}"

definition uinject_aleph0 :: "'a::{countable, infinite} \<Rightarrow> uuniv" where
"uinject_aleph0 x = {to_nat_bij x}"

definition uinject_continuum :: "'a::{continuum, infinite} \<Rightarrow> uuniv" where
"uinject_continuum x = to_nat_set_bij x"

definition uinject :: "'a::continuum \<Rightarrow> uuniv" where
"uinject x = (if (finite (UNIV :: 'a set))
                 then {to_nat_fin x}
               else if (countable (UNIV :: 'a set))
                  then {to_nat_on (UNIV :: 'a set) x}
               else to_nat_set x)"

definition uproject :: "uuniv \<Rightarrow> 'a::continuum" where
"uproject = inv uinject"

lemma uinject_finite:
  "finite (UNIV :: 'a::continuum set) \<Longrightarrow> uinject = (\<lambda> x :: 'a. {to_nat_fin x})"
  by (rule ext, auto simp add: uinject_def)

lemma uinject_uncountable:
  "uncountable (UNIV :: 'a::continuum set) \<Longrightarrow> (uinject :: 'a \<Rightarrow> uuniv) = to_nat_set"
  by (rule ext, auto simp add: uinject_def countable_finite)

lemma card_finite_lemma: 
  assumes "finite (UNIV :: 'a set)"
  shows "x < card (UNIV :: 'a set) \<longleftrightarrow> x \<le> card (UNIV :: 'a set) - Suc 0"
proof -
  have "card (UNIV :: 'a set) > 0"
    by (simp add: assms finite_UNIV_card_ge_0)
  thus ?thesis
    by linarith
qed

text {* This is a key theorem that shows that the injection function provides a bijection between 
        any continuum type and the subuniverse of types with a matching cardinality. *}

lemma uinject_bij:
  "bij_betw (uinject :: 'a::continuum \<Rightarrow> uuniv) UNIV \<U>(UCARD('a))"
proof (cases "finite (UNIV :: 'a set)")
  case True thus ?thesis
    apply (auto simp add: uinject_def bij_betw_def inj_on_def image_def card_finite_lemma[THEN sym])
    apply (auto simp add: inj_eq to_nat_fin_inj to_nat_fin_bounded)
    using to_nat_fin_ex apply blast
  done
  next
  case False note infinite = this thus ?thesis
  proof (cases "countable (UNIV :: 'a set)")
    case True thus ?thesis
      apply (auto simp add: uinject_def bij_betw_def inj_on_def infinite image_def card_finite_lemma[THEN sym])
      apply (meson image_to_nat_on infinite surj_def)
    done
    next
    case False note uncount = this thus ?thesis
      apply (simp add: uinject_uncountable)
      using to_nat_set_bij apply blast
    done
  qed
qed

lemma uinject_card [simp]: "uinject (x :: 'a::continuum) \<in> \<U>(UCARD('a))"
  by (metis bij_betw_def rangeI uinject_bij)

lemma uinject_inv [simp]:
  "uproject (uinject x) = x"
  by (metis UNIV_I bij_betw_def inv_into_f_f uinject_bij uproject_def)

lemma uproject_inv [simp]:
  "x \<in> \<U>(UCARD('a::continuum)) \<Longrightarrow> uinject ((uproject :: nat set \<Rightarrow> 'a)  x) = x"
  by (metis bij_betw_inv_into_right uinject_bij uproject_def)

subsection {* Deep variables *}

text {* A deep variable name stores both a name and the cardinality of the type it points to *}

record dname =
  dname_name :: "string"
  dname_card :: "ucard"

text {* A vstore is a function mapping deep variable names to corresponding values in the universe, such
        that the deep variables specified cardinality is matched by the value it points to. *}

typedef vstore = "{f :: dname \<Rightarrow> uuniv. \<forall> x. f(x) \<in> \<U>(dname_card x)}" 
  apply (rule_tac x="\<lambda> x. {0}" in exI)
  apply (auto)
  apply (rename_tac x)
  apply (case_tac "dname_card x")
  apply (simp_all)
done

setup_lifting type_definition_vstore

typedef ('a::continuum) dvar = "{x :: dname. dname_card x = UCARD('a)}"
  by (auto, meson dname.select_convs(2))

setup_lifting type_definition_dvar

lift_definition mk_dvar :: "string \<Rightarrow> ('a::continuum) dvar" ("\<lceil>_\<rceil>\<^sub>d")
is "\<lambda> n. \<lparr> dname_name = n, dname_card = UCARD('a) \<rparr>"
  by auto

lift_definition dvar_name :: "'a::continuum dvar \<Rightarrow> string" is "dname_name" .
lift_definition dvar_card :: "'a::continuum dvar \<Rightarrow> ucard" is "dname_card" .

lemma dvar_name [simp]: "dvar_name \<lceil>x\<rceil>\<^sub>d = x"
  by (transfer, simp)

lift_definition vstore_lookup :: "('a::continuum) dvar \<Rightarrow> vstore \<Rightarrow> 'a"
is "\<lambda> x s. (uproject :: uuniv \<Rightarrow> 'a) (s(x))" .

lift_definition vstore_put :: "('a::continuum) dvar \<Rightarrow> 'a \<Rightarrow> vstore \<Rightarrow> vstore"
is "\<lambda> (x :: dname) (v :: 'a) f . f(x := uinject v)"
  by (auto)

definition vstore_upd :: "('a::continuum) dvar \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> vstore \<Rightarrow> vstore"
where "vstore_upd x f s = vstore_put x (f (vstore_lookup x s)) s"

lemma vstore_upd_comp [simp]:
  "vstore_upd x f (vstore_upd x g s) = vstore_upd x (f \<circ> g) s"
  by (simp add: vstore_upd_def, transfer, simp)

lemma vstore_lookup_upd [simp]: "vstore_lookup x (vstore_upd x f s) = f (vstore_lookup x s)"
  by (simp add: vstore_upd_def, transfer, simp)

lemma vstore_upd_eta [simp]: "vstore_upd x (\<lambda> _. vstore_lookup x s) s = s"
  apply (simp add: vstore_upd_def, transfer, auto)
  apply (metis Domainp_iff dvar.domain fun_upd_idem_iff uproject_inv)
done

lemma vstore_lookup_put_diff_var [simp]:
  assumes "dvar_name x \<noteq> dvar_name y"
  shows "vstore_lookup x (vstore_put y v s) = vstore_lookup x s"
  using assms by (transfer, auto)

lemma vstore_put_commute:
  assumes "dvar_name x \<noteq> dvar_name y"
  shows "vstore_put x u (vstore_put y v s) = vstore_put y v (vstore_put x u s)"
  using assms
  by (transfer, fastforce)

text {* The vst class provides an interface for extracting a variable store from a state space.
        For now, the state-space is limited to countably infinite types, though we will in
        the future build a more expressive universe. *}

class vst =
  fixes get_vstore :: "'a \<Rightarrow> vstore"
  and   upd_vstore :: "(vstore \<Rightarrow> vstore) \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes get_upd_vstore [simp]: "get_vstore (upd_vstore f s) = f (get_vstore s)"
  and upd_vstore_comp [simp]: "upd_vstore f (upd_vstore g s) = upd_vstore (f \<circ> g) s"  
  and upd_vstore_eta [simp]: "upd_vstore (\<lambda> _. get_vstore s) s = s"
  and upd_store_parm: "upd_vstore f s = upd_vstore (\<lambda> _. f (get_vstore s)) s"

definition dvar_lift :: "'a::continuum dvar \<Rightarrow> ('a, '\<alpha>::vst) uvar" ("_\<up>" [999] 999)
where "dvar_lift x = \<lparr> var_lookup = \<lambda> v. vstore_lookup x (get_vstore v)
                     , var_update = \<lambda> f s. upd_vstore (vstore_upd x f) s
                     \<rparr>"

definition [simp]: "in_dvar x = in_var (x\<up>)"
definition [simp]: "out_dvar x = out_var (x\<up>)"

adhoc_overloading
  ivar in_dvar and ovar out_dvar

lemma vstore_upd_compose [simp]: "vstore_upd x f \<circ> vstore_upd x g = vstore_upd x (f \<circ> g)"
  by (rule ext, simp add: vstore_upd_def, transfer, auto)

lemma update_vstore_appl: "upd_vstore (\<lambda> x. f (g x)) s = upd_vstore f (upd_vstore g s)"
  by (metis comp_apply upd_store_parm upd_vstore_comp)

lemma vstore_upd_appl: "vstore_upd x (\<lambda> x. f (g x)) s = vstore_upd x f (vstore_upd x g s)"
  by (metis (no_types, lifting) vstore_lookup_upd vstore_upd_comp vstore_upd_def)

lemma uvar_dvar: "uvar (x\<up>)"
proof
  fix f g :: "'a \<Rightarrow> 'a" and \<sigma> :: "'b"
  show "var_update (x\<up>) f (var_update (x\<up>) g \<sigma>) = var_update (x\<up>) (f \<circ> g) \<sigma>"
    by (simp add: dvar_lift_def)
  show "var_assign (x\<up>) (var_lookup (x\<up>) \<sigma>) \<sigma> = \<sigma>"
    by (simp add: dvar_lift_def, subst upd_store_parm, simp)
  show "var_lookup (x\<up>) (var_update (x\<up>) f \<sigma>) = f (var_lookup (x\<up>) \<sigma>)"
    by (simp add: dvar_lift_def)
  fix \<rho> :: 'b and v :: 'a
  show "var_lookup (x\<up>) \<sigma> = var_lookup (x\<up>) \<rho> \<Longrightarrow> var_assign (x\<up>) v \<sigma> = var_assign (x\<up>) v \<rho> \<Longrightarrow> \<sigma> = \<rho>"
  proof -
    assume vl: "var_lookup (x\<up>) \<sigma> = var_lookup (x\<up>) \<rho>" and va: "var_assign (x\<up>) v \<sigma> = var_assign (x\<up>) v \<rho>"

    have "get_vstore \<sigma> = get_vstore \<rho>"
      by (metis (no_types, lifting) dvar_lift_def get_upd_vstore uvar.select_convs(1) uvar.select_convs(2) va vl vstore_lookup_upd vstore_upd_comp vstore_upd_def vstore_upd_eta)

    moreover from va have "upd_vstore (\<lambda>_. get_vstore \<rho>) \<sigma> = \<rho>"
      by (simp add: dvar_lift_def, metis upd_store_parm upd_vstore_eta update_vstore_appl)

    ultimately show ?thesis
      by (metis upd_vstore_eta)
  qed
qed

text {* Deep variables with different names are independent *}

lemma dvar_indep_diff_name:
  assumes "dvar_name x \<noteq> dvar_name y"
  shows "x\<up> \<bowtie> y\<up>"
proof -
  from assms have "\<And> f g. vstore_upd x f \<circ> vstore_upd y g = vstore_upd y g \<circ> vstore_upd x f"
    apply (auto simp add: comp_def vstore_upd_def)
    apply (rule ext, subst vstore_put_commute, auto)
  done
 
 thus ?thesis
    by (auto simp add: uvar_indep_def dvar_name_def dvar_card_def dvar_lift_def vstore_upd_def)
qed

lemma dvar_indep_diff_name' [simp]:
  "x \<noteq> y \<Longrightarrow> \<lceil>x\<rceil>\<^sub>d\<up> \<bowtie> \<lceil>y\<rceil>\<^sub>d\<up>"
  by (auto intro: dvar_indep_diff_name)

text {* A basic record structure for vstores *}

record vstore_d =
  vstore :: vstore

instantiation vstore_d_ext :: (type) vst
begin
  definition [simp]: "get_vstore_vstore_d_ext = vstore"
  definition [simp]: "upd_vstore_vstore_d_ext = vstore_update"
instance
  by (intro_classes, simp_all)
end

end