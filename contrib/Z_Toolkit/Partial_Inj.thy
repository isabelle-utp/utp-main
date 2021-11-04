section \<open> Partial Injections \<close>

theory Partial_Inj
  imports Partial_Fun
begin

typedef ('a, 'b) pinj = "{f :: ('a, 'b) pfun. pfun_inj f}" 
  morphisms pfun_of_pinj pinj_of_pfun 
  by (auto intro: pfun_inj_empty)

lemma pinj_eq_pfun: "f = g \<longleftrightarrow> pfun_of_pinj f = pfun_of_pinj g"
  by (simp add: pfun_of_pinj_inject)

lemma pfun_inj_pinj [simp]: "pfun_inj (pfun_of_pinj f)"
  using pfun_of_pinj by auto

type_notation pinj (infixr "\<Zpinj>" 1)

setup_lifting type_definition_pinj

lift_definition pinv :: "'a \<Zpinj> 'b \<Rightarrow> 'b \<Zpinj> 'a" is pfun_inv
  by (simp add: pfun_inj_inv)

instantiation pinj :: (type, type) zero
begin
  lift_definition zero_pinj :: "('a, 'b) pinj" is "0"
    by simp
instance ..
end

abbreviation pinj_empty :: "('a, 'b) pinj" ("{}\<^sub>\<rho>") where "{}\<^sub>\<rho> \<equiv> 0"

lift_definition pinj_app :: "('a, 'b) pinj \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>\<rho>" [999,0] 999) 
is "pfun_app" .

text \<open> Adding a maplet to a partial injection requires that we remove any other maplet that points
  to the value @{term v}, to preserve injectivity. \<close>

lift_definition pinj_upd :: "('a, 'b) pinj \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pinj"
is "\<lambda> f k v. pfun_upd (f \<rhd>\<^sub>p (- {v})) k v"
  by (simp add: pfun_inj_rres pfun_inj_upd)

lift_definition pidom :: "'a \<Zpinj> 'b \<Rightarrow> 'a set" is pdom .

lift_definition piran :: "'a \<Zpinj> 'b \<Rightarrow> 'b set" is pran .

lift_definition pinj_dres :: "'a set \<Rightarrow> ('a, 'b) pinj \<Rightarrow> ('a, 'b) pinj" (infixr "\<lhd>\<^sub>\<rho>" 85) is pdom_res
  by (simp add: pfun_inj_dres)

lift_definition pinj_rres :: "('a, 'b) pinj \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) pinj" (infixl "\<rhd>\<^sub>\<rho>" 86) is pran_res
  by (simp add: pfun_inj_rres)

lift_definition pinj_comp :: "'b \<Zpinj> 'c \<Rightarrow> 'a \<Zpinj> 'b \<Rightarrow> 'a \<Zpinj> 'c" (infixl "\<circ>\<^sub>\<rho>" 55) is "(\<circ>\<^sub>p)"
  by (simp add: pfun_inj_comp)

syntax
  "_PinjUpd"  :: "[('a, 'b) pinj, maplets] => ('a, 'b) pinj" ("_'(_')\<^sub>\<rho>" [900,0]900)
  "_Pinj"     :: "maplets => ('a, 'b) pinj"            ("(1{_}\<^sub>\<rho>)")

translations
  "_PinjUpd m (_Maplets xy ms)"  == "_PinjUpd (_PinjUpd m xy) ms"
  "_PinjUpd m (_maplet  x y)"    == "CONST pinj_upd m x y"
  "_Pinj ms"                     => "_PinjUpd (CONST pempty) ms"
  "_Pinj (_Maplets ms1 ms2)"     <= "_PinjUpd (_Pinj ms1) ms2"
  "_Pinj ms"                     <= "_PinjUpd (CONST pempty) ms"

lemma pinj_app_upd [simp]: "(f(k \<mapsto> v)\<^sub>\<rho>)(x)\<^sub>\<rho> = (if (k = x) then v else (f \<rhd>\<^sub>\<rho> (-{v})) (x)\<^sub>\<rho>)"
  by (transfer, simp)

lemma pinj_eq_iff: "f = g \<longleftrightarrow> (pidom(f) = pidom(g) \<and> (\<forall> x\<in>pidom(f). f(x)\<^sub>\<rho> = g(x)\<^sub>\<rho>))"
  by (transfer, simp add: pfun_eq_iff)

lemma pinv_pempty [simp]: "pinv {}\<^sub>\<rho> = {}\<^sub>\<rho>"
  by (transfer, simp)

lemma pinv_pinj_upd [simp]: "pinv (f(x \<mapsto> y)\<^sub>\<rho>) = (pinv ((-{x}) \<lhd>\<^sub>\<rho> f))(y \<mapsto> x)\<^sub>\<rho>"
  by (transfer, subst pfun_inv_upd, simp_all add: pfun_inj_dres pfun_inj_rres  pfun_inv_rres pdres_rres_commute, simp add: pfun_inv_dres)

lemma pinv_pinv: "pinv (pinv f) = f"
  by (transfer, simp add: pfun_inj_inv_inv)

lemma pinv_pcomp: "pinv (f \<circ>\<^sub>\<rho> g) = pinv g \<circ>\<^sub>\<rho> pinv f"
  by (transfer, simp add: pfun_eq_graph pfun_graph_pfun_inv pfun_graph_comp pfun_inj_comp converse_relcomp)

lemmas pidom_empty [simp] = pdom_zero[Transfer.transferred]
lemma piran_zero [simp]: "piran {}\<^sub>\<rho> = {}" by (transfer, simp)

lemmas pinj_dres_empty [simp] = pdom_res_zero[Transfer.transferred]
lemmas pinj_rres_empty [simp] = pran_res_zero[Transfer.transferred]

lemmas pidom_res_empty [simp] = pdom_res_empty[Transfer.transferred]
lemmas piran_res_empty [simp] = pran_res_empty[Transfer.transferred]

lemma pidom_res_upd: "A \<lhd>\<^sub>\<rho> f(k \<mapsto> v)\<^sub>\<rho> = (if k \<in> A then (A \<lhd>\<^sub>\<rho> f)(k \<mapsto> v)\<^sub>\<rho> else A \<lhd>\<^sub>\<rho> (f \<rhd>\<^sub>\<rho> (- {v})))"
  by (transfer, simp, metis pdom_res_swap)

thm pdom_res_upd_out[Transfer.transferred]

lemma piran_res_upd: "f(x \<mapsto> v)\<^sub>\<rho> \<rhd>\<^sub>\<rho> A = (if v \<in> A then (f \<rhd>\<^sub>\<rho> A)(x \<mapsto> v)\<^sub>\<rho> else ((- {x}) \<lhd>\<^sub>\<rho> f) \<rhd>\<^sub>\<rho> A)"
  by (transfer, simp add: inf.commute)
     (metis (no_types, hide_lams) ComplI Compl_Un double_compl insert_absorb insert_is_Un pdom_res_swap pran_res_twice)

lemma pinj_upd_with_dres_rres: "((-{x}) \<lhd>\<^sub>\<rho> f \<rhd>\<^sub>\<rho> (-{y}))(x \<mapsto> y)\<^sub>\<rho> = f(x \<mapsto> y)\<^sub>\<rho>"
  by (transfer, simp add: pdom_res_swap)

lemma pidres_twice: "A \<lhd>\<^sub>\<rho> B \<lhd>\<^sub>\<rho> f = (A \<inter> B) \<lhd>\<^sub>\<rho> f"
  by (transfer, metis pdom_res_twice)

lemma pidres_commute: "A \<lhd>\<^sub>\<rho> B \<lhd>\<^sub>\<rho> f = B \<lhd>\<^sub>\<rho> A \<lhd>\<^sub>\<rho> f"
  by (metis (no_types, hide_lams) inf_commute pidres_twice)

lemma pidres_rres_commute: "A \<lhd>\<^sub>\<rho> (P \<rhd>\<^sub>\<rho> B) = (A \<lhd>\<^sub>\<rho> P) \<rhd>\<^sub>\<rho> B"
  by (transfer, simp, metis (mono_tags, hide_lams) pdres_rres_commute)

lemma pirres_twice: "f \<rhd>\<^sub>\<rho> A \<rhd>\<^sub>\<rho> B = f \<rhd>\<^sub>\<rho> (A \<inter> B)"
  by (transfer, metis (no_types, hide_lams) pran_res_twice)

lemma pirres_commute: "f \<rhd>\<^sub>\<rho> A \<rhd>\<^sub>\<rho> B = f \<rhd>\<^sub>\<rho> B \<rhd>\<^sub>\<rho> A"
  by (metis inf_commute pirres_twice)

lemma pidom_upd: "pidom (f(k \<mapsto> v)\<^sub>\<rho>) = insert k (pidom (f \<rhd>\<^sub>\<rho> (- {v})))"
  by (transfer, simp)

(* FIXME: Properly integrate using a proof strategy for coercion to partial injections *)

lemma f_pinv_f_apply: "x \<in> pran (pfun_of_pinj f) \<Longrightarrow> (pfun_of_pinj f)(pfun_of_pinj (pinv f) (x)\<^sub>p)\<^sub>p = x"
  by (transfer, simp add: f_pfun_inv_f_apply)

fun pinj_of_alist :: "('a \<times> 'b) list \<Rightarrow> 'a \<Zpinj> 'b" where
"pinj_of_alist [] = {}\<^sub>\<rho>" |
"pinj_of_alist (p # ps) = (pinj_of_alist ps)(fst p \<mapsto> snd p)\<^sub>\<rho>" 

lemma pinj_empty_alist [code]: "{}\<^sub>\<rho> = pinj_of_alist []"
  by simp

lemma pinj_upd_alist [code]: "(pinj_of_alist xs)(k \<mapsto> v)\<^sub>\<rho> = pinj_of_alist ((k, v) # xs)"
  by simp

context begin

text \<open> Injective associative lists \<close>

definition ialist :: "('a \<times> 'b) list \<Rightarrow> bool" where
"ialist xs = (distinct (map fst xs) \<and> distinct (map snd xs))"

text \<open> Remove pairs where either the key or value appeared in a previous pair \<close>

qualified fun clearjunk :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
"clearjunk [] = []" |
"clearjunk (p#ps) = p # filter (\<lambda> (k', v'). k' \<noteq> fst p \<and> v' \<noteq> snd p) (clearjunk ps)"

lemma ialist_clearjunk: "ialist (clearjunk xs)"
  by (induct xs rule:clearjunk.induct, auto simp add: ialist_def, (meson distinct_map_filter)+)

lemma ialist_clearjunk_fp: "ialist xs \<Longrightarrow> clearjunk xs = xs"
  by (induct xs, auto simp add: ialist_def filter_id_conv rev_image_eqI)

lemma clearjunk_idem [simp]: "clearjunk (clearjunk xs) = clearjunk xs"
  using ialist_clearjunk ialist_clearjunk_fp by blast

lemma pinj_of_alist_ndres: "k \<notin> fst ` set xs \<Longrightarrow> (-{k}) \<lhd>\<^sub>\<rho> (pinj_of_alist xs) = pinj_of_alist xs"
  by (induct xs, auto simp add: pidom_res_upd)

lemma pinj_of_alist_nrres: "v \<notin> snd ` set xs \<Longrightarrow> (pinj_of_alist xs) \<rhd>\<^sub>\<rho> (- {v}) = pinj_of_alist xs"
  by (induct xs, auto simp add: piran_res_upd)

lemma pidom_ialist: "ialist xs \<Longrightarrow> pidom (pinj_of_alist xs) = set (map fst xs)"
  by (induct xs, auto simp add: ialist_def pidom_upd)
     (metis (no_types, lifting) fst_conv image_eqI pinj_of_alist_nrres)+

lemma pinj_of_alist_filter_as_dres_rres:
  "ialist xs \<Longrightarrow> pinj_of_alist (filter (\<lambda>(k', v'). k' \<noteq> fst p \<and> v' \<noteq> snd p) xs) = (-{fst p}) \<lhd>\<^sub>\<rho> pinj_of_alist xs \<rhd>\<^sub>\<rho> (-{snd p})"
  by (induct xs rule: pinj_of_alist.induct)
     (auto simp add: ialist_def piran_res_upd pinj_of_alist_ndres pidom_res_upd
     ,metis (no_types, lifting) pinj_of_alist_nrres pirres_commute)
  
lemma pinj_of_alist_clearjunk: "pinj_of_alist (clearjunk xs) = pinj_of_alist xs"
  by (induct xs rule:clearjunk.induct, simp add: pinj_eq_iff)
     (simp add: ialist_clearjunk pinj_of_alist_filter_as_dres_rres pinj_upd_with_dres_rres)

lemma pinv_pinj_of_ialist:
  "ialist xs \<Longrightarrow> pinv (pinj_of_alist xs) = pinj_of_alist (map (\<lambda> (x, y). (y, x)) xs)"
  by (induct xs rule: pinj_of_alist.induct, auto simp add: ialist_def simp add: pinj_of_alist_ndres)


lemma pfun_of_ialist: "ialist xs \<Longrightarrow> pfun_of_pinj (pinj_of_alist xs) = pfun_of_alist xs"
  by (induct xs rule: pinj_of_alist.induct, auto simp add: zero_pinj.rep_eq ialist_def pinj_upd.rep_eq )
     (metis pinj_of_alist_nrres pinj_rres.rep_eq)


declare clearjunk.simps [simp del]

end

lemma pinv_pinj_of_alist [code]: "pinv (pinj_of_alist xs) = pinj_of_alist (map (\<lambda> (x, y). (y, x)) (Partial_Inj.clearjunk xs))"
  by (metis ialist_clearjunk pinj_of_alist_clearjunk pinv_pinj_of_ialist)

lemma pfun_of_pinj_of_alist [code]: 
  "pfun_of_pinj (pinj_of_alist xs) = pfun_of_alist (Partial_Inj.clearjunk xs)"
  by (metis ialist_clearjunk pfun_of_ialist pinj_of_alist_clearjunk)

declare pinj_of_alist.simps [simp del]

end