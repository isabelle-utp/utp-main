section "Terms"

text\<open>
  Originally based on @{file "~~/src/Pure/term.ML"}.
  Diverged substantially, but some influences are still visible.
  Further influences from @{dir "~~/src/HOL/Proofs/Lambda/"}.\<close>

theory Term
  imports Main Core Preliminaries 
begin

text\<open>Collecting parts of typs/terms and more substitutions\<close>

fun tvsT :: "typ \<Rightarrow> (variable \<times> sort) set" where 
  "tvsT (Tv v S) = {(v,S)}"
| "tvsT (Ty _ Ts) = \<Union>(set (map tvsT Ts))"

fun tvs :: "term \<Rightarrow> (variable \<times> sort) set" where
  "tvs (Ct _ T) = tvsT T"
| "tvs (Fv _ T) = tvsT T"
| "tvs (Bv _) = {}"
| "tvs (Abs T t) = tvsT T \<union> tvs t"
| "tvs (t $ u) = tvs t \<union> tvs u"

abbreviation "tvs_set S \<equiv> \<Union>t\<in>S . tvs t"

lemma tvsT_tsubstT: "tvsT (tsubstT \<sigma> \<rho>) = \<Union> {tvsT (\<rho> a s) | a s. (a, s) \<in> tvsT \<sigma>}"
  by (induction \<sigma>) fastforce+ 

lemma tsubstT_cong: 
  "(\<forall>(v,S) \<in> tvsT \<sigma>. \<rho>1 v = \<rho>2 v) \<Longrightarrow> tsubstT \<sigma> \<rho>1 = tsubstT \<sigma> \<rho>2"
  by (induction \<sigma>) fastforce+ 

lemma tsubstT_ith: "i < length Ts \<Longrightarrow>  map (\<lambda>T . tsubstT T \<rho>) Ts ! i = tsubstT (Ts ! i) \<rho>" 
  by simp

lemma tsubstT_fun_typ_dist: "tsubstT (T \<rightarrow> T1) \<rho> = tsubstT T \<rho> \<rightarrow> tsubstT T1 \<rho>" 
    by simp

fun subst :: "term \<Rightarrow> (variable \<Rightarrow> typ \<Rightarrow> term) \<Rightarrow> term" where
  "subst (Ct s T) \<rho> = Ct s T"
| "subst (Fv v T) \<rho> = \<rho> v T"
| "subst (Bv i) _ = Bv i"
| "subst (Abs T t) \<rho> = Abs T (subst t \<rho>)"
| "subst (t $ u) \<rho> = subst t \<rho> $ subst u \<rho>"

definition "tinst t1 t2 \<equiv> \<exists>\<rho>. tsubst t2 \<rho> = t1"
definition "inst t1 t2 \<equiv> \<exists>\<rho>. subst t2 \<rho> = t1" 

fun SortsT :: "typ \<Rightarrow> sort set" where
  "SortsT (Tv _ S) = {S}"
| "SortsT (Ty _ Ts) = (\<Union>T\<in>set Ts . SortsT T)"

fun Sorts :: "term \<Rightarrow> sort set" where
  "Sorts (Ct _ T) = SortsT T"
| "Sorts (Fv _ T) = SortsT T"
| "Sorts (Bv _) = {}"
| "Sorts (Abs T t) = SortsT T \<union> Sorts t"
| "Sorts (t $ u) = Sorts t \<union> Sorts u"

fun Types :: "term \<Rightarrow> typ set" where
  "Types (Ct _ T) = {T}"
| "Types (Fv _ T) = {T}"
| "Types (Bv _) = {}"
| "Types (Abs T t) =  insert T (Types t)"
| "Types (t $ u) = Types t \<union> Types u"

abbreviation "tvs_Set S \<equiv> \<Union>s\<in>S . tvs s"
abbreviation "tvsT_Set S \<equiv> \<Union>s\<in>S . tvsT s"

(* All those sets are finite *)
lemma finite_SortsT[simp]: "finite (SortsT T)"
  by (induction T) auto
lemma finite_Sorts[simp]: "finite (Sorts t)"
  by (induction t) auto
lemma finite_Types[simp]: "finite (Types t)"
  by (induction t) auto
lemma finite_tvsT[simp]: "finite (tvsT T)"
  by (induction T) auto
lemma no_tvsT_imp_tsubsT_unchanged: "tvsT T = {} \<Longrightarrow> tsubstT T \<rho> = T"
  by (induction T) (auto simp add: map_idI)
lemma finite_fv[simp]: "finite (fv t)"
  by (induction t) auto
lemma finite_tvs[simp]: "finite (tvs t)"
  by (induction t) auto

lemma finite_FV: "finite S \<Longrightarrow> finite (FV S)"
  by (induction S rule: finite_induct) auto
lemma finite_tvs_Set: "finite S \<Longrightarrow> finite (tvs_Set S)"
  by (induction S rule: finite_induct) auto
lemma finite_tvsT_Set: "finite S \<Longrightarrow> finite (tvsT_Set S)"
  by (induction S rule: finite_induct) auto

lemma no_tvs_imp_tsubst_unchanged: "tvs t = {} \<Longrightarrow> tsubst t \<rho> = t"
  by (induction t) (auto simp add: map_idI no_tvsT_imp_tsubsT_unchanged) 
lemma no_fv_imp_subst_unchanged: "fv t = {} \<Longrightarrow> subst t \<rho> = t"
  by (induction t) (auto simp add: map_idI)

text\<open>Functional(also executable) version of @{term has_typ}\<close>

fun typ_of1 :: "typ list \<Rightarrow> term \<Rightarrow> typ option" where
  "typ_of1 _ ( Ct _ T) = Some T"
| "typ_of1 Ts (Bv i) = (if i < length Ts then Some (nth Ts i) else None)"
| "typ_of1 _ (Fv _ T) = Some T"
| "typ_of1 Ts (Abs T body) = Option.bind (typ_of1 (T#Ts) body) (\<lambda>x. Some (T \<rightarrow> x))"
| "typ_of1 Ts (t $ u) = Option.bind (typ_of1 Ts u) (\<lambda>U. Option.bind (typ_of1 Ts t) (\<lambda>T. 
    case T of
          Ty fun [T1,T2] \<Rightarrow> if fun = STR ''fun'' then
            if T1=U then Some T2 else None
            else None
        | _ \<Rightarrow> None
    ))"


text\<open>For historic reasons a lot of proofs/definitions are still in terms of @{term typ_of1} instead of
@{term has_typ1}\<close>

lemma has_typ1_weaken_Ts: "has_typ1 Ts t rT \<Longrightarrow> has_typ1 (Ts@[T]) t rT"
proof (induction arbitrary: rule: has_typ1.induct)
  case (2 i Ts)
  hence "has_typ1 (Ts @ [T]) (Bv i) ((Ts@[T]) ! i)"
    by (auto intro: has_typ1.intros(2))
  then show ?case
    by (simp add: "2.hyps" nth_append)
qed (auto intro: has_typ1.intros) thm less_Suc_eq nth_butlast

lemma has_typ1_imp_typ_of1: "has_typ1 Ts t ty \<Longrightarrow> typ_of1 Ts t = Some ty"
  by (induction rule: has_typ1.induct) auto

lemma typ_of1_imp_has_typ1: "typ_of1 Ts t = Some ty \<Longrightarrow> has_typ1 Ts t ty"
proof (induction t arbitrary: Ts ty)
  case (App t u)  
  from this obtain U where U: "typ_of1 Ts u = Some U" by fastforce
  from this App obtain T where T: "typ_of1 Ts t = Some T" by fastforce
  from U T App obtain T2 where "T = Ty STR ''fun'' [U, T2]"
    by (auto simp add: bind_eq_Some_conv intro!: has_typ1.intros 
        split: if_splits typ.splits list.splits)
  from this U T show ?case using App by (auto intro!: has_typ1.intros(5))
qed (auto simp add: bind_eq_Some_conv intro!: has_typ1.intros split: if_splits)

corollary has_typ1_iff_typ_of1[iff]: "has_typ1 Ts t ty \<longleftrightarrow> typ_of1 Ts t = Some ty" 
  using has_typ1_imp_typ_of1 typ_of1_imp_has_typ1 by blast
corollary has_typ_iff_typ_of[iff]: "has_typ t ty \<longleftrightarrow> typ_of t = Some ty"
  by (force simp add: has_typ_def typ_of_def)

corollary typ_of_imp_has_typ: "typ_of t = Some ty \<Longrightarrow> has_typ t ty"
  by simp

lemma typ_of1_weaken_Ts: "typ_of1 Ts t = Some ty \<Longrightarrow> typ_of1 (Ts@[T]) t = Some ty"
  using has_typ1_weaken_Ts by simp

lemma typ_of1_weaken:
  assumes "typ_of1 Ts t = Some T"
  shows "typ_of1 (Ts@Ts') t = Some T"
  using assms by (induction Ts t arbitrary: Ts' T rule: typ_of1.induct)
    (auto split: if_splits simp add: nth_append bind_eq_Some_conv)

(* Instantiation of type variables produces instantiated types *)
lemma has_typ1_tsubst: 
  "has_typ1 Ts t T \<Longrightarrow> has_typ1 (map (\<lambda>T. tsubstT T \<rho>) Ts) (tsubst t \<rho>) (tsubstT T \<rho>)"
proof (induction rule: has_typ1.induct)
  case (2 i Ts)
  (* tsubst_ith must be applied reversed, in this direction it can cause simplifier to loop *)
  then show ?case using tsubstT_ith by (metis has_typ1.intros(2) length_map tsubst.simps(3))
qed (auto simp add: tsubstT_fun_typ_dist intro: has_typ1.intros)

corollary has_typ1_unique: 
  assumes "has_typ1 \<tau>s t \<tau>1" and "has_typ1 \<tau>s t \<tau>2" shows "\<tau>1 = \<tau>2"
  using assms
  by (metis has_typ1_imp_typ_of1 option.inject)

hide_fact typ_of_def

lemma typ_of_def: "typ_of t \<equiv> typ_of1 [] t"
  by (smt has_typ1_iff_typ_of1 has_typ_def has_typ_iff_typ_of not_None_eq)

text\<open>Loose bound variables\<close>

fun loose_bvar :: "term \<Rightarrow> nat \<Rightarrow> bool" where
  "loose_bvar (Bv i) k \<longleftrightarrow> i \<ge> k"
| "loose_bvar (t $ u) k \<longleftrightarrow> loose_bvar t k \<or> loose_bvar u k"
| "loose_bvar (Abs _ t) k = loose_bvar t (k+1)"
| "loose_bvar _ _ = False"

fun loose_bvar1 :: "term \<Rightarrow> nat \<Rightarrow> bool" where
  "loose_bvar1 (Bv i) k \<longleftrightarrow> i = k"
| "loose_bvar1 (t $ u) k \<longleftrightarrow> loose_bvar1 t k \<or> loose_bvar1 u k"
| "loose_bvar1 (Abs _ t) k = loose_bvar1 t (k+1)"
| "loose_bvar1 _ _ = False"


lemma loose_bvar1_imp_loose_bvar: "loose_bvar1 t n \<Longrightarrow> loose_bvar t n" 
  by (induction t arbitrary: n) auto
lemma not_loose_bvar_imp_not_loose_bvar1: "\<not> loose_bvar t n \<Longrightarrow> \<not> loose_bvar1 t n"
  by (induction t arbitrary: n) auto

lemma loose_bvar_iff_exist_loose_bvar1: "loose_bvar t lev \<longleftrightarrow> (\<exists>lev'\<ge>lev. loose_bvar1 t lev')"
  by (induction t arbitrary: lev) (auto dest: Suc_le_D)

definition "is_open t \<equiv> loose_bvar t 0"
abbreviation "is_closed t \<equiv> \<not> is_open t"
definition "is_dependent t \<equiv> loose_bvar1 t 0"

lemma loose_bvar_Suc: "loose_bvar t (Suc k) \<Longrightarrow> loose_bvar t k"
  by (induction t arbitrary: k) auto
lemma loose_bvar_leq: "k\<ge>p \<Longrightarrow> loose_bvar t k \<Longrightarrow> loose_bvar t p"
  by (induction rule: inc_induct) (use loose_bvar_Suc in auto)

lemma has_typ1_imp_no_loose_bvar: "has_typ1 Ts t ty \<Longrightarrow> \<not> loose_bvar t (length Ts)"
  by (induction rule: has_typ1.induct) auto

corollary has_typ_imp_closed: "has_typ t ty \<Longrightarrow> \<not> is_open t"
  unfolding is_open_def has_typ_def using has_typ1_imp_no_loose_bvar by fastforce

corollary typ_of_imp_closed: "typ_of t = Some ty \<Longrightarrow> \<not> is_open t"
  by (simp add: has_typ_imp_closed)

text\<open>Subterms\<close>

(* probably ugly for proofs... *)
fun exists_subterm :: "(term \<Rightarrow> bool) \<Rightarrow> term \<Rightarrow> bool" where
  "exists_subterm P t \<longleftrightarrow> P t \<or> (case t of
      (t $ u) \<Rightarrow> exists_subterm P t \<or> exists_subterm P u
    | Abs ty body \<Rightarrow> exists_subterm P body
    | _ \<Rightarrow> False)"
(* Is this better? *)
fun exists_subterm' :: "(term \<Rightarrow> bool) \<Rightarrow> term \<Rightarrow> bool" where
  "exists_subterm' P (t $ u) \<longleftrightarrow> P (t $ u) \<or> exists_subterm' P t \<or> exists_subterm' P u"
| "exists_subterm' P (Abs ty body) \<longleftrightarrow> P (Abs ty body) \<or> exists_subterm' P body"
| "exists_subterm' P t \<longleftrightarrow>  P t"

lemma exists_subterm_iff_exists_subterm': "exists_subterm P t \<longleftrightarrow> exists_subterm' P t"
  by (induction t) auto
lemma "exists_subterm (\<lambda>t. t=Fv idx T) t \<longleftrightarrow> (idx, T) \<in> fv t"
  by (induction t) auto

(* Fairly old, however still needed for some proofs about "subterms" *)
(* Must have no loose bounds in t, from Logic.ML*)
abbreviation "occs t u \<equiv> exists_subterm (\<lambda>s. t = s) u"

lemma occs_Fv_eq_elem_fv: "occs (Fv v S) t \<longleftrightarrow> (v, S) \<in> fv t"
  by (induction t) auto

lemma bind_fv2_unchanged: 
  "\<not>loose_bvar tm lev \<Longrightarrow> bind_fv2 v lev tm = tm \<Longrightarrow> v \<notin> fv tm"
  by (induction v lev tm rule: bind_fv2.induct) auto
lemma bind_fv2_unchanged': 
  "\<not>loose_bvar tm lev \<Longrightarrow> bind_fv2 v lev tm = tm \<Longrightarrow> \<not> occs (case_prod Fv v) tm"
  by (induction v lev tm rule: bind_fv2.induct) auto

lemma bind_fv2_changed: 
  "bind_fv2 v lev tm \<noteq> tm \<Longrightarrow> v \<in> fv tm"
  by (induction v lev tm rule: bind_fv2.induct) (auto split: if_splits)
lemma bind_fv2_changed': 
  "bind_fv2 v lev tm \<noteq> tm \<Longrightarrow> occs (case_prod Fv v) tm"
  by (induction v lev tm rule: bind_fv2.induct) (auto split: if_splits)

corollary bind_fv_changed: "bind_fv v tm \<noteq> tm \<Longrightarrow> v \<in> fv tm"
  unfolding is_open_def bind_fv_def using bind_fv2_changed by simp
corollary bind_fv_changed': "bind_fv v tm \<noteq> tm \<Longrightarrow> occs (case_prod Fv v) tm"
  unfolding is_open_def bind_fv_def using bind_fv2_changed' by simp

corollary bind_fv_unchanged: "(x,\<tau>) \<notin> fv t \<Longrightarrow> bind_fv (x,\<tau>) t = t"
  using bind_fv_changed by auto

inductive_cases has_typ1_app_elim: "has_typ1 Ts (t $ u) R"
lemma has_typ1_arg_typ: "has_typ1 Ts (t $ u) R \<Longrightarrow> has_typ1 Ts u U \<Longrightarrow> has_typ1 Ts t (U \<rightarrow> R)"
  using has_typ1_app_elim
  by (metis has_typ1_imp_typ_of1 option.inject typ_of1_imp_has_typ1)
 
lemma has_typ1_fun_typ: "has_typ1 Ts (t $ u) R \<Longrightarrow> has_typ1 Ts t (U \<rightarrow> R) \<Longrightarrow> has_typ1 Ts u U"
  by (cases rule: has_typ1_app_elim[of Ts t u R "has_typ1 Ts u U"]) (use has_typ1_unique in auto)

lemma typ_of1_arg_typ: 
  "typ_of1 Ts (t $ u) = Some R \<Longrightarrow> typ_of1 Ts u = Some U \<Longrightarrow> typ_of1 Ts t = Some (U \<rightarrow> R)"
  using has_typ1_iff_typ_of1 has_typ1_arg_typ by simp

corollary typ_of_arg: "typ_of (t$u) = Some R \<Longrightarrow> typ_of u = Some T \<Longrightarrow> typ_of t = Some (T \<rightarrow> R)"
  by (metis typ_of1_arg_typ typ_of_def)

lemma typ_of1_fun_typ: 
  "typ_of1 Ts (t $ u) = Some R \<Longrightarrow> typ_of1 Ts t = Some (U \<rightarrow> R) \<Longrightarrow> typ_of1 Ts u = Some U"
  using has_typ1_iff_typ_of1 has_typ1_fun_typ by blast

corollary typ_of_fun: "typ_of (t$u) = Some R \<Longrightarrow> typ_of t = Some (U \<rightarrow> R) \<Longrightarrow> typ_of u = Some U"
  by (metis typ_of1_fun_typ typ_of_def)

lemma typ_of_eta_expand: "typ_of f = Some (\<tau> \<rightarrow> \<tau>') \<Longrightarrow> typ_of (Abs \<tau> (f $ Bv 0)) = Some (\<tau> \<rightarrow> \<tau>')"
  using typ_of1_weaken by (fastforce simp add: bind_eq_Some_conv typ_of_def)

lemma bind_fv2_preserves_type:
  assumes "typ_of1 Ts t = Some ty" 
  shows "typ_of1 (Ts@[T]) (bind_fv2 (v, T) (length Ts) t) = Some ty"
  using assms by (induction "(v, T)" "length Ts" t arbitrary: T Ts ty rule: bind_fv2.induct)
    (force simp add: bind_eq_Some_conv nth_append split: if_splits)+

lemma typ_of_Abs_bind_fv:
  assumes "typ_of A = Some ty"
  shows "typ_of (Abs bT (bind_fv (v, bT) A)) = Some (bT \<rightarrow> ty)"
  using bind_fv2_preserves_type bind_fv_def assms typ_of_def by fastforce

corollary typ_of_Abs_fv:
  assumes "typ_of A = Some ty"
  shows "typ_of (Abs_fv v bT A) = Some (bT \<rightarrow> ty)"
  using assms typ_of_Abs_bind_fv typ_of_def by simp

lemma typ_of_mk_all:
  assumes "typ_of A = Some propT" 
  shows "typ_of (mk_all x ty A) = Some propT"
  using typ_of_Abs_bind_fv[OF assms, of ty] by (auto simp add: typ_of_def)

fun incr_bv :: "nat \<Rightarrow> nat \<Rightarrow> term \<Rightarrow> term" where
  "incr_bv inc n (Bv i) = (if i \<ge> n then Bv (i+inc) else Bv i)"
| "incr_bv inc n (Abs T body) = Abs T (incr_bv inc (n+1) body)"
| "incr_bv inc n (App f t) = App (incr_bv inc n f) (incr_bv inc n t)"
| "incr_bv _   _ u = u"

(* Bridging *)
lemma lift_def: "lift t n = incr_bv 1 n t"
  by (induction t n rule: lift.induct) auto

declare lift.simps[simp del]
declare lift_def[simp]

definition "incr_boundvars inc t = incr_bv inc 0 t"

fun decr :: "nat \<Rightarrow> term \<Rightarrow> term" where
  "decr lev (Bv i) = (if i \<ge> lev then Bv (i - 1) else Bv i)"
| "decr lev (Abs T t) = Abs T (decr (lev + 1) t)"
| "decr lev (t $ u) = (decr lev t $ decr lev u)"
| "decr _ t = t"

lemma incr_bv_0[simp]: "incr_bv 0 lev t = t"
  by (induction t arbitrary: lev) auto

lemma loose_bvar_incr_bvar: "loose_bvar t lev \<longleftrightarrow> loose_bvar (incr_bv inc lev t) (lev+inc)"
  by (induction t arbitrary: inc lev) force+

lemma no_loose_bvar_no_incr[simp]: "\<not> loose_bvar t lev \<Longrightarrow> incr_bv inc lev t = t"
  by (induction t arbitrary: inc lev) auto

lemma is_close_no_incr_boundvars[simp]: "is_closed t \<Longrightarrow> incr_boundvars inc t = t"
  using no_loose_bvar_no_incr by (simp add: incr_boundvars_def is_open_def)

lemma fv_incr_bv [simp]: "fv (incr_bv inc lev t) = fv t"
  by (induction inc lev t rule: incr_bv.induct) auto
lemma fv_incr_boundvars [simp]: "fv (incr_boundvars inc t) = fv t"
  by (simp add: incr_boundvars_def)

lemma loose_bvar_decr: "\<not> loose_bvar t k \<Longrightarrow> \<not> loose_bvar (decr k t) k"
  by (induction t k rule: loose_bvar.induct) auto
lemma loose_bvar_decr_unchanged[simp]: "\<not> loose_bvar t k \<Longrightarrow> decr k t = t"
  by (induction t k rule: loose_bvar.induct) auto
lemma is_closed_decr_unchanged[simp]: "is_closed t \<Longrightarrow> decr 0 t = t"
  by (simp add: is_open_def)

fun subst_bv1 :: "term \<Rightarrow> nat \<Rightarrow> term \<Rightarrow> term" where
  "subst_bv1 (Bv i) lev u = (if i < lev then Bv i
    else if i = lev then (incr_boundvars lev u)
    else (Bv (i - 1)))"
| "subst_bv1 (Abs T body) lev u = Abs T (subst_bv1 body (lev + 1) u)"
| "subst_bv1 (f $ t) lev u = subst_bv1 f lev u $ subst_bv1 t lev u"
| "subst_bv1 t _ _ = t"

lemma incr_bv_combine: "incr_bv m k (incr_bv n k s) = incr_bv (m+n) k s"
  by (induction s arbitrary: k) auto

lemma substn_subst_n : "subst_bv1 t n s = subst_bv2 t n (incr_bv n 0 s)"
  by (induct t arbitrary: n) (auto simp add: incr_boundvars_def incr_bv_combine)

theorem substn_subst_0: "subst_bv1 t 0 s = subst_bv2 t 0 s"
  by (simp add: substn_subst_n)

corollary substn_subst_0': "subst_bv s t = subst_bv2 t 0 s"
  using subst_bv_def substn_subst_0 by simp

lemma subst_bv2_eq [simp]: "subst_bv2 (Bv k) k u = u"
  by (simp add:)

lemma subst_bv2_gt [simp]: "i < j \<Longrightarrow> subst_bv2 (Bv j) i u = Bv (j - 1)"
  by (simp add:)

lemma subst_bv2_subst_lt [simp]: "j < i \<Longrightarrow> subst_bv2 (Bv j) i u = Bv j"
  by (simp add:)

lemma lift_lift:
    "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i"
  by (induct t arbitrary: i k) auto

lemma lift_subst [simp]:
    "j < i + 1 \<Longrightarrow> lift (subst_bv2 t j s) i = subst_bv2 (lift t (i + 1)) j (lift s i)"
proof (induction t arbitrary: i j s)
  case (Abs T t)
  then show ?case 
    by (simp_all add: diff_Suc lift_lift split: nat.split) 
      (metis One_nat_def Suc_eq_plus1 lift_def lift_lift zero_less_Suc)
qed (simp_all add: diff_Suc lift_lift split: nat.split) 

lemma lift_subst_bv2_subst_lt:
    "i < j + 1 \<Longrightarrow> lift (subst_bv2 t j s) i = subst_bv2 (lift t i) (j + 1) (lift s i)"
proof (induction t arbitrary: i j s)
  case (Abs x1 t)
  then show ?case
    using lift_lift by force
qed (auto simp add: lift_lift)

lemma subst_bv2_lift [simp]:
    "subst_bv2 (lift t k) k s = t"
  by (induct t arbitrary: k s) simp_all

lemma subst_bv2_subst_bv2:
    "i < j + 1 \<Longrightarrow> subst_bv2 (subst_bv2 t (Suc j) (lift v i)) i (subst_bv2 u j v) 
    = subst_bv2 (subst_bv2 t i u) j v"
proof(induction t arbitrary: i j u v)
  case (Abs s T t)
  then show ?case
    by (smt Suc_mono add.commute lift_lift lift_subst_bv2_subst_lt plus_1_eq_Suc subst_bv2.simps(2) zero_less_Suc)
qed (use subst_bv2_lift in \<open>auto simp add: diff_Suc lift_lift [symmetric] lift_subst_bv2_subst_lt split: nat.split\<close>)

(* Bridging *)
hide_fact (open) subst_bv_def
lemma subst_bv_def: "subst_bv u t \<equiv> subst_bv1 t 0 u"
  by (simp add: substn_subst_0' substn_subst_n)

(* Probably not necessary *)
fun subst_bvs1 :: "term \<Rightarrow> nat \<Rightarrow> term list \<Rightarrow> term" where
  "subst_bvs1 (Bv n) lev args = (if n < lev 
    then Bv n 
    else if n - lev < length args 
      then incr_boundvars lev (nth args (n-lev)) 
      else Bv (n - length args))"
| "subst_bvs1 (Abs T body) lev args = Abs T (subst_bvs1 body (lev+1) args)"
| "subst_bvs1 (f $ t) lev args = subst_bvs1 f lev args $ subst_bvs1 t lev args"
| "subst_bvs1 t _ _ = t"

definition "subst_bvs args t \<equiv> subst_bvs1 t 0 args"

lemma subst_bvs_App[simp]: "subst_bvs args (s$t) = subst_bvs args s $ subst_bvs args t"
  by (auto simp add: subst_bvs_def)

lemma subst_bv1_special_case_subst_bvs1: "subst_bvs1 t lev [x] = subst_bv1 t lev x"
  by (induction t lev "[x]" arbitrary: x rule: subst_bvs1.induct) auto

lemma no_loose_bvar_imp_no_subst_bv1: "\<not>loose_bvar t lev \<Longrightarrow> subst_bv1 t lev u = t"
  by (induction t arbitrary: lev) auto
lemma no_loose_bvar_imp_no_subst_bvs1: "\<not>loose_bvar t lev \<Longrightarrow> subst_bvs1 t lev us = t"
  by (induction t arbitrary: lev) auto

(* The precondition in the following lemmas makes them fairly useless *)
lemma subst_bvs1_step:             
  assumes "\<not> loose_bvar t lev"
  shows "subst_bvs1 t lev (args@[u]) = subst_bv1 (subst_bvs1 t lev args) lev u"
  using assms by (induction t arbitrary: lev args u) auto

corollary closed_subst_bv_no_change: "is_closed t \<Longrightarrow> subst_bv u t = t"
  unfolding is_open_def subst_bv_def no_loose_bvar_imp_no_subst_bv1 by simp

lemma is_variable_imp_incr_bv_unchanged: "incr_bv inc lev (Fv v T) = (Fv v T)" 
  by simp
lemma is_variable_imp_incr_boundvars_unchganged: "incr_boundvars inc (Fv v T) = (Fv v T)" 
  using is_variable_imp_incr_bv_unchanged incr_boundvars_def by simp

lemma loose_bvar_subst_bv1: 
  "\<not> loose_bvar (subst_bv1 t lev u) lev \<Longrightarrow> \<not> loose_bvar t (Suc lev)"
  by (induction t lev u rule: subst_bv1.induct) auto
lemma is_closed_subst_bv: "is_closed (subst_bv u t) \<Longrightarrow> \<not> loose_bvar t 1"
  by (simp add: is_open_def loose_bvar_subst_bv1 subst_bv_def)

lemma subst_bv1_bind_fv2: 
  assumes "\<not> loose_bvar t lev" 
  shows "subst_bv1 (bind_fv2 (v, T) lev t) lev (Fv v T) = t"
  using assms by (induction t arbitrary: lev) (use is_variable_imp_incr_boundvars_unchganged in auto)

corollary subst_bv_bind_fv: 
  assumes "is_closed t"
  shows "subst_bv (Fv v T) (bind_fv (v, T) t) = t"
  unfolding bind_fv_def subst_bv_def using assms subst_bv1_bind_fv2 is_open_def
  by blast

fun betapply :: "term \<Rightarrow> term \<Rightarrow> term" (infixl "\<bullet>" 52) where
  "betapply (Abs _ t) u = subst_bv u t"
| "betapply t u = t $ u"

lemma betapply_Abs_fv:
  assumes "is_closed t"
  shows "betapply (Abs_fv v T t) (Fv v T) = t"
using assms subst_bv_bind_fv by simp

lemma typ_of1_imp_no_loose_bvar: "typ_of1 Ts t = Some ty \<Longrightarrow> \<not> loose_bvar t (length Ts)"
  by (simp add: has_typ1_imp_no_loose_bvar)

lemma typ_of1_subst_bv:
  assumes "typ_of1 (Ts@[uty]) f = Some fty"
    and "typ_of u = Some uty"
  shows "typ_of1 Ts (subst_bv1 f (length Ts) u) = Some fty"
  using assms 
proof (induction f "length Ts" u arbitrary: uty fty Ts rule: subst_bv1.induct)
  case (1 i arg)
  then show ?case
    using no_loose_bvar_no_incr typ_of1_imp_no_loose_bvar typ_of1_weaken
    by (force simp add: bind_eq_Some_conv incr_boundvars_def nth_append typ_of_def
        split: if_splits)
next
  case (2 a T body arg)
  then show ?case 
    by (simp add: bind_eq_Some_conv typ_of_def) (smt append_Cons bind_eq_Some_conv length_Cons)
qed (auto simp add: bind_eq_Some_conv)

lemma typ_of1_split_App:
  "typ_of1 Ts (t $ u) = Some ty \<Longrightarrow> (\<exists>uty . typ_of1 Ts t = Some (uty \<rightarrow> ty) \<and> typ_of1 Ts u = Some uty)"
  by (metis (no_types, lifting) bind.bind_lzero the_default.elims typ_of1.simps(5) typ_of1_arg_typ)

corollary typ_of1_split_App_obtains:
  assumes "typ_of1 Ts (t $ u) = Some ty" 
  obtains uty where "typ_of1 Ts t = Some (uty \<rightarrow> ty)" "typ_of1 Ts u = Some uty"
  using typ_of1_split_App assms by blast

lemma typ_of1_incr_bv:
  assumes "typ_of1 Ts t = Some ty" 
    and "lev \<le> length Ts"
  shows "typ_of1 (take lev Ts @ Ts' @ drop lev Ts) (incr_bv (length Ts') lev t) = Some ty"
  using assms by (induction t arbitrary: ty Ts Ts' lev) 
    (fastforce simp add: nth_append bind_eq_Some_conv min_def split: if_splits)+

corollary typ_of1_incr_bv_lev0:
  assumes "typ_of1 Ts t = Some ty" 
  shows "typ_of1 (Ts' @ Ts) (incr_bv (length Ts') 0 t) = Some ty"
  using assms typ_of1_incr_bv[where lev=0] by simp

lemma typ_of1_subst_bv_gen:
  assumes "typ_of1 (Ts'@[uty]@Ts) t = Some tty" and "typ_of1 Ts u = Some uty"
  shows "typ_of1 (Ts' @ Ts) (subst_bv1 t (length Ts') u) = Some tty"
  using assms 
proof (induction t "length Ts'" u arbitrary: tty uty Ts Ts' rule: subst_bv1.induct)
next
  case (2 a T body arg)
  then show ?case
    by (simp add: bind_eq_Some_conv) (metis append_Cons length_Cons)
qed (auto simp add: bind_eq_Some_conv nth_append incr_boundvars_def 
    typ_of1_incr_bv_lev0 split: if_splits)

(* This is the correct version, the other one inserts "at the wrong side of the bounds" *)
lemma typ_of1_subst_bv_gen_depre:
  assumes "typ_of1 (Ts'@Ts) f = Some (fty)"
    and "typ_of1 (Ts) u = Some uty"
    and "last Ts' = uty" and "Ts' \<noteq> []"
  shows "typ_of1 (butlast Ts' @ Ts) (subst_bv1 f (length Ts'-1) u) = Some fty"
  using assms 
proof (induction f "length Ts'" u arbitrary: fty uty Ts Ts' rule: subst_bv1.induct)
  case (1 i arg)
  from 1 consider (LT) "(length Ts' - 1) < i" | (EQ) "(length Ts' - 1) = i" | (GT) "(length Ts' - 1) > i" 
    using linorder_neqE_nat by blast
  then show ?case
    by cases (metis "1.prems" append_assoc append_butlast_last_id length_butlast typ_of1_subst_bv_gen)+
next
  case (2 a T body arg)
  then show ?case 
    by (metis append.assoc append_butlast_last_id length_butlast typ_of1_subst_bv_gen)
next
  case (3 f t arg)
  then show ?case 
    by (auto simp add: bind_eq_Some_conv nth_append incr_boundvars_def subst_bv_def 
        split: if_splits)
qed auto

corollary typ_of1_subst_bv_gen':
  assumes "typ_of1 (uty#Ts) t = Some tty"
    and "typ_of1 Ts u = Some uty"
  shows "typ_of1 Ts (subst_bv1 t 0 u) = Some tty"
  using assms typ_of1_subst_bv_gen
  by (metis append.left_neutral append_Cons list.size(3))

lemma typ_of_betapply: 
  assumes "typ_of1 Ts (Abs uty t) = Some (uty \<rightarrow> tty)"
  assumes "typ_of1 Ts u = Some uty"
  shows "typ_of1 Ts ((Abs uty t) \<bullet> u) = Some tty"
  using assms typ_of1_subst_bv_gen'
  by (auto simp add: bind_eq_Some_conv subst_bv_def)

lemma no_Bv_Type_param_irrelevant_typ_of:
  "\<not>exists_subterm (\<lambda>x . case x of Bv _ \<Rightarrow> True | _ \<Rightarrow> False) t 
  \<Longrightarrow> typ_of1 Ts t = typ_of1 Ts' t"
  by (induction t arbitrary: Ts Ts') (simp_all, metis+)

lemma typ_of1_drop_extra_bounds:
  "\<not>loose_bvar t (length Ts) 
  \<Longrightarrow> typ_of1 (Ts@rest) t = typ_of1 Ts t"
  by (induction Ts t arbitrary: rest rule: typ_of1.induct) (fastforce simp add: nth_append)+

lemma typ_of_betaply:
  assumes "typ_of t = Some (uty \<rightarrow> tty)" "typ_of u = Some uty"
  shows "typ_of (t \<bullet> u) = Some tty" 
proof (cases t)
  case (Abs T t)
  then show ?thesis
  proof (cases "is_open t")
    case True
    then show ?thesis
      unfolding is_open_def using assms Abs typ_of1_subst_bv
      apply (simp add: bind_eq_Some_conv subst_bv_def typ_of_def) 
      by (metis append_Nil list.size(3) typ_of_def)
  next
    case False
    hence "typ_of1 [uty] t = Some tty" using assms(1)   
      by (auto simp add: bind_eq_Some_conv typ_of_def is_open_def Abs)
      
    then show ?thesis 
      using assms False no_loose_bvar_imp_no_subst_bv1 
      apply (simp add: bind_eq_Some_conv typ_of_def is_open_def subst_bv_def Abs)
      using no_Bv_Type_param_irrelevant_typ_of
      using typ_of1_drop_extra_bounds 
      by (metis list.size(3) self_append_conv2)
  qed
qed (use assms in \<open>simp_all add: typ_of_def\<close>)

fun beta_reducible :: "term \<Rightarrow> bool" where
  "beta_reducible (App (Abs _ _) _) = True"
| "beta_reducible (Abs _ t) = beta_reducible t"
| "beta_reducible (App t u) = (beta_reducible t \<or> beta_reducible u)"
| "beta_reducible _ = False"

fun eta_reducible :: "term \<Rightarrow> bool" where
  "eta_reducible (Abs _ (t $ Bv 0)) = (\<not> is_dependent t \<or> eta_reducible t)"
| "eta_reducible (Abs _ t) = eta_reducible t"
| "eta_reducible (App t u) = (eta_reducible t \<or> eta_reducible u)"
| "eta_reducible _ = False"

lemma "\<not> loose_bvar t lev \<Longrightarrow> decr lev t = t" 
  by (induction t arbitrary: lev) auto

lemma decr_incr_bv1: "decr lev (incr_bv 1 lev t) = t"
  by (induction t arbitrary: lev) auto

(* For termination proofs *)
fun depth :: "term \<Rightarrow> nat" where
  "depth (Abs _ t) = depth t + 1"
| "depth (t $ u) = max (depth t) (depth u) +1"
| "depth t = 0"

lemma depth_decr: "depth (decr lev t) = depth t"
  by (induction lev t rule: decr.induct) auto

lemma loose_bvar1_decr: "lev > 0 \<Longrightarrow> \<not> loose_bvar1 t (Suc lev) \<Longrightarrow> \<not> loose_bvar1 (decr lev t) lev"
  by (induction lev t arbitrary: rule: decr.induct) auto

lemma loose_bvar1_decr':
  "\<not> loose_bvar1 t (Suc lev) \<Longrightarrow> \<not> loose_bvar1 t lev \<Longrightarrow> \<not> loose_bvar1 (decr lev t) lev"
  by (induction lev t arbitrary: rule: decr.induct) auto

lemma eta_reducible_Abs1: "\<not> eta_reducible (Abs T (t $ Bv 0)) \<Longrightarrow> \<not> eta_reducible t" by simp

lemma eta_reducible_Abs2: 
  assumes "\<not> (\<exists>f. t=f $ Bv 0)" "\<not> eta_reducible (Abs T t)" 
  shows "\<not> eta_reducible t" 
proof (cases t)
  case (Abs T body)
  then show ?thesis using assms(2) by (cases body) auto
next
  case (App f u)
  then show ?thesis using assms less_imp_Suc_add by (cases f; cases u) fastforce+ 
qed auto

lemma eta_reducible_Abs: "\<not> eta_reducible (Abs T t) \<Longrightarrow> \<not> eta_reducible t" 
  using eta_reducible_Abs1 eta_reducible_Abs2
  by (metis eta_reducible.simps(11) eta_reducible.simps(14))

lemma loose_bvar1_decr'': "loose_bvar1 t lev \<Longrightarrow> lev < lev'\<Longrightarrow> loose_bvar1 (decr lev' t) lev"
  by (induction t arbitrary: lev lev') auto
lemma loose_bvar1_decr''': "loose_bvar1 t (Suc lev) \<Longrightarrow> lev' \<le> lev \<Longrightarrow> loose_bvar1 (decr lev' t) lev"
  by (induction t arbitrary: lev lev') auto

lemma loose_bvar1_decr'''': "\<not> loose_bvar1 t lev' \<Longrightarrow> lev' \<le> lev  \<Longrightarrow> \<not> loose_bvar1 t (Suc lev) 
  \<Longrightarrow> \<not> loose_bvar1 (decr lev' t) lev"
  by (induction lev t arbitrary: lev' rule: decr.induct) auto

lemma not_eta_reducible_decr: 
  "\<not> eta_reducible t \<Longrightarrow> \<not> loose_bvar1 t lev \<Longrightarrow> \<not> eta_reducible (decr lev t) " 
proof (induction lev t arbitrary: rule: decr.induct)
  case (2 lev T body)
  hence "\<not> eta_reducible body" using eta_reducible_Abs by blast
  hence I: "\<not> eta_reducible (decr (lev + 1) body)" using "2.IH"
    using "2.prems"(2) by simp

  then show ?case 
  proof(cases body)
    case (App f u)
    note app = this
    then show ?thesis
    proof (cases u)
      case (Bv n)
      then show ?thesis
      proof (cases "n")
        case 0
        have "is_dependent f" "\<not> eta_reducible f" 
          using "0" "2.prems"(1) App Bv eta_reducible.simps(1) by blast+
        hence "loose_bvar1 f 0" by (simp add: is_dependent_def)
        hence "loose_bvar1 (decr (Suc lev) f) 0" using loose_bvar1_decr'' by simp
        then show ?thesis using I by (auto simp add: 0 Bv App is_dependent_def)
      next
        case (Suc nat)
        then show ?thesis 
          using 2 App Bv 
          by (auto elim: eta_reducible.elims(2) simp add: Suc Bv App is_dependent_def)
      qed
    next
      case (Abs T t)
      then show ?thesis 
        using I by (auto split: if_splits simp add: App is_dependent_def) 
    qed (use I in \<open>auto split: if_splits simp add: App is_dependent_def\<close>)
  qed (auto split: if_splits simp add: is_dependent_def) 
qed auto


function (sequential, domintros) eta_norm :: "term \<Rightarrow> term" where
  "eta_norm (Abs T t) = (case eta_norm t of 
    f $ Bv 0 \<Rightarrow> (if is_dependent f then Abs T (f $ Bv 0) else decr 0 (eta_norm f))
  | body \<Rightarrow> Abs T body)"
| "eta_norm (t $ u) = eta_norm t $ eta_norm u"
| "eta_norm t = t"
  by pat_completeness auto

lemma eta_norm_reduces_depth: "eta_norm_dom t \<Longrightarrow> depth (eta_norm t) <= depth t"
  by (induction t rule: eta_norm.pinduct)
    (use depth_decr in \<open>fastforce simp add: eta_norm.psimps eta_norm.domintros is_dependent_def 
      split: term.splits nat.splits\<close>)+

termination eta_norm
proof (relation "measure depth")
  fix T body t u n
  assume asms: "eta_norm body = t $ u" "u = Bv n" "n = 0" "\<not> is_dependent t" "eta_norm_dom body"
  have "depth t < depth (t $ Bv 0)" by auto
  moreover have "depth (eta_norm body) \<le> depth body" using asms eta_norm_reduces_depth by blast
  ultimately show "(t, Abs T body) \<in> measure depth" using asms by (auto simp add: eta_norm.psimps)
qed simp_all

lemma loose_bvar1_eta_norm: "loose_bvar1 t lev \<Longrightarrow> loose_bvar1 (eta_norm t) lev"
  by (induction t arbitrary: lev rule: eta_norm.induct)
    (use loose_bvar1_decr''' in \<open>(fastforce split: term.splits nat.splits)+\<close>)

lemma loose_bvar1_eta_norm': "\<not> loose_bvar1 t lev \<Longrightarrow> \<not> loose_bvar1 (eta_norm t) lev"
proof (induction t arbitrary: lev rule: eta_norm.induct)
  case (1 T body)
  hence "\<not> loose_bvar1 body (Suc lev)" by simp
  hence I: "\<not> loose_bvar1 (eta_norm body) (Suc lev)" using 1 by simp
  then show ?case
  proof (cases body)
    case (Abs ty b)
    show ?thesis 
      using I loose_bvar1_decr''''
      by (auto split: term.splits nat.splits if_splits simp add: "1.IH"(2) is_dependent_def)
  next
    case (App T t)
    then show ?thesis using 1 I loose_bvar1_decr''''
      by (fastforce split: term.splits nat.splits if_splits simp add: is_dependent_def)
  qed (auto split: term.splits nat.splits simp add: is_dependent_def)
qed (auto split: term.splits nat.splits simp add: is_dependent_def)

lemma not_eta_reducible_eta_norm: "\<not> eta_reducible (eta_norm t)" 
proof (induction t rule: eta_norm.induct)
  case (1 T body) 
  then show ?case
  proof (cases "eta_norm (body)")
    case (Abs T t)
    then show ?thesis using 1 by auto 
  next
    case (App f u)
    then show ?thesis
    proof (cases "u = Bv 0")
      case True
      note u = this
      then show ?thesis
      proof (cases "is_dependent f")
        case True
        then show ?thesis 
          using 1 App u by (auto simp add: is_dependent_def split: term.splits nat.splits if_splits)
      next
        case False
        have "\<not> eta_reducible f" using 1 App u by simp
        hence "\<not> eta_reducible (eta_norm f)" 
          by (simp add: "1.IH"(2) App False u)
        have "\<not> loose_bvar1 f 0"
          using False is_dependent_def by blast
        hence  "\<not> loose_bvar1 (eta_norm f) 0" 
          using  loose_bvar1_eta_norm' by blast
        show ?thesis
          using 1 App u False not_eta_reducible_decr loose_bvar1_eta_norm \<open>\<not> loose_bvar1 (eta_norm f) 0\<close> 
          by (auto simp add: is_dependent_def split: term.splits nat.splits if_splits) 
      qed
    next
      case False
      then show ?thesis using 1 App by (auto simp add: is_dependent_def
            split: term.splits nat.splits if_splits)
    qed
  qed auto
qed auto

lemma not_eta_reducible_imp_eta_norm_no_change: "\<not> eta_reducible t \<Longrightarrow> eta_norm t = t"
  by (induction t rule: eta_norm.induct) (auto simp add: eta_reducible_Abs is_dependent_def 
      split: term.splits nat.splits)

lemma eta_norm_collapse: "eta_norm (eta_norm t) = eta_norm t"
  using not_eta_reducible_imp_eta_norm_no_change not_eta_reducible_eta_norm by blast

lemma typ_of1_decr: "typ_of1 (Ts@[T]@Ts') t = Some ty \<Longrightarrow> \<not> loose_bvar1 t (length Ts) 
  \<Longrightarrow> typ_of1 (Ts@Ts') (decr (length Ts) t) = Some ty"
proof (induction t arbitrary: Ts T Ts' ty)
  case (Abs bT t)
  then show ?case 
    by (simp add: bind_eq_Some_conv) (metis append_Cons length_Cons)
qed (auto split: if_splits simp add: bind_eq_Some_conv nth_append)

lemma typ_of1_decr_gen: "typ_of1 (Ts@[T]@Ts') t = tyo \<Longrightarrow> \<not> loose_bvar1 t (length Ts)
  \<Longrightarrow> typ_of1 (Ts@Ts') (decr (length Ts) t) = tyo"
proof (induction t arbitrary: Ts T Ts' tyo)
  case (Abs T t)
  then show ?case 
    by (simp add: bind_eq_Some_conv) (metis append_Cons length_Cons)
next
  case (App t1 t2)
  then show ?case by simp
qed (auto split: if_splits simp add: bind_eq_Some_conv nth_append
        split: option.splits)

lemma typ_of1_decr_gen': "typ_of1 (Ts@Ts') (decr (length Ts) t) = tyo\<Longrightarrow> \<not> loose_bvar1 t (length Ts)
  \<Longrightarrow> typ_of1 (Ts@[T]@Ts') t = tyo"
proof (induction t arbitrary: Ts T Ts' tyo)
  case (Abs T t)
  then show ?case 
    by (simp add: bind_eq_Some_conv) (metis append_Cons length_Cons)
qed (auto split: if_splits simp add: bind_eq_Some_conv nth_append
        split: option.splits)

(* Other direction does not necessarily hold, eta_norm could remove incorrect abstractions *)
lemma typ_of1_eta_norm: "typ_of1 Ts t = Some ty \<Longrightarrow> typ_of1 Ts (eta_norm t) = Some ty"
proof (induction Ts t arbitrary: ty rule: typ_of1.induct)
  case (4 Ts T body)
  then show ?case 
  proof(cases "eta_norm body")
    case (App f u)
    then show ?thesis
    (* In dire need of cleanup *)
    proof (cases u)
      case (Bv n)
      then show ?thesis
      proof (cases n)
        case 0
        then show ?thesis
        proof (cases "is_dependent f")
          case True
          hence "eta_norm (Abs T body) = Abs T (f $ Bv 0)" 
            by (auto simp add: App 0 "4.IH" Bv bind_eq_Some_conv is_dependent_def split: nat.splits)
          then show ?thesis 
            using 4 by (force simp add: "0" Bv App is_dependent_def bind_eq_Some_conv split: if_splits)
        next
          case False
          
          hence simp: "eta_norm (Abs T body) = decr 0 (eta_norm f)" 
            by (auto simp add: App 0 "4.IH" Bv bind_eq_Some_conv bind_eq_None_conv
                is_dependent_def split: nat.splits)

          obtain bT where bT: "typ_of1 (T # Ts) body = Some bT"
            using "4.prems" by fastforce
          hence "typ_of1 (T # Ts) (eta_norm body) = Some bT"
            using "4.IH" by blast
          moreover have "T \<rightarrow> bT = ty"
            using "4.prems" bT by auto
          ultimately have "typ_of1 (T#Ts) f = Some ty"
            by (metis "0" App Bv length_Cons nth_Cons_0 typ_of1.simps(2) typ_of1_arg_typ zero_less_Suc)
          hence "typ_of1 Ts (decr 0 f) = Some ty"
            by (metis False append_Cons append_Nil is_dependent_def list.size(3) typ_of1_decr)
          hence "typ_of1 Ts (decr 0 (eta_norm f)) = Some ty"
            by (metis App eta_reducible.simps(11) not_eta_reducible_eta_norm not_eta_reducible_imp_eta_norm_no_change)
                    
          then show ?thesis 
            by(auto simp add: App 0 Bv False)
        qed
      next
        case (Suc nat)
        then show ?thesis
          using 4 apply (simp add: App "4.IH" Bv bind_eq_Some_conv split: option.splits)
          using option.sel by fastforce
      qed
    qed (use 4 in \<open>fastforce simp add: bind_eq_Some_conv nth_append split: if_splits\<close>)+
  qed (use 4 in \<open>fastforce simp add: bind_eq_Some_conv nth_append split: if_splits\<close>)+
next
  case (5 Ts f u)
  then show ?case 
    apply (clarsimp split: term.splits typ.splits if_splits nat.splits option.splits
        simp add: bind_eq_Some_conv)
    by blast
qed (auto split: term.splits typ.splits if_splits nat.splits option.splits 
    simp add: bind_eq_Some_conv)

corollary typ_of_eta_norm: "typ_of t = Some ty \<Longrightarrow> typ_of (eta_norm t) = Some ty"
  using typ_of1_eta_norm typ_of_def by simp

lemma typ_of_Abs_body_typ: "typ_of1 Ts (Abs T t) = Some ty \<Longrightarrow> \<exists>rty. ty = (T \<rightarrow> rty)" 
  by (metis (no_types, lifting) bind_eq_Some_conv option.sel typ_of1.simps(4))
lemma typ_of_Abs_body_typ': "typ_of1 Ts (Abs T t) = Some ty 
  \<Longrightarrow> \<exists>rty. ty = (T \<rightarrow> rty) \<and> typ_of1 (T#Ts) t = Some rty" 
  by (metis (no_types, lifting) bind_eq_Some_conv option.sel typ_of1.simps(4))

lemma typ_of_beta_redex_arg: "typ_of (Abs T s $ t) \<noteq> None \<Longrightarrow> typ_of t = Some T"
  by (metis list.inject not_Some_eq typ.inject(1) typ_of1_split_App typ_of_Abs_body_typ' typ_of_def)

lemma [partial_function_mono]: "option.mono_body
          (\<lambda>beta_norm. map_option (Abs T) (beta_norm t))"
  by (smt flat_ord_def fun_ord_def map_option_is_None monotone_def)
lemma [partial_function_mono]: "option.mono_body
          (\<lambda>beta_norm.
              case beta_norm x of None \<Rightarrow> None
              | Some (Ct list typ) \<Rightarrow>
                  map_option (($) (Ct list typ)) (beta_norm u)
              | Some (Fv p typ) \<Rightarrow>
                  map_option (($) (Fv p typ)) (beta_norm u)
              | Some (Bv n) \<Rightarrow>
                  map_option (($) (Bv n)) (beta_norm u)
              | Some (Abs T body) \<Rightarrow>
                  beta_norm (subst_bv u body)
              | Some (term1 $ term2) \<Rightarrow>
                  map_option (($) (term1 $ term2)) (beta_norm u))"
proof(standard, goal_cases)
  case (1 a b)
  then show ?case
  proof(cases "a x"; cases "b x", simp_all add: flat_ord_def fun_ord_def, goal_cases)
    case (1 a)
    then show ?case
      by (metis option.discI)
  next
    case (2 r s)
    then show ?case
      apply (cases r; cases s)
      apply (simp_all add: flat_ord_def fun_ord_def) 
      apply (metis option.distinct option.inject option.sel term.distinct term.inject)+
      done
  qed 
qed

(* Does not terminate in general :( *)
partial_function (option) beta_norm :: "term \<Rightarrow> term option" where
  "beta_norm t = (case t of
    (Abs T body) \<Rightarrow> map_option (Abs T) (beta_norm body)
  | (Abs T body $ u) \<Rightarrow> beta_norm (subst_bv u body)
  | (f $ u) \<Rightarrow> (case beta_norm f of 
      Some (Abs T body) \<Rightarrow> beta_norm (subst_bv u body)
    | Some f' \<Rightarrow> map_option (App f') (beta_norm u)
    | None \<Rightarrow> None)
  | t \<Rightarrow> Some t)"

simps_of_case beta_norm_simps[simp]: beta_norm.simps
declare beta_norm_simps[code]

lemma not_beta_reducible_imp_beta_norm_unchanged: "\<not> beta_reducible t \<Longrightarrow> beta_norm t = Some t"
proof (induction t)
  case (App t u)
  then show ?case by (cases t) auto
qed auto

lemma not_beta_reducible_decr: "\<not> beta_reducible t \<Longrightarrow> \<not> beta_reducible (decr n t)"
  by (induction t arbitrary: n rule: beta_reducible.induct) auto

lemma "\<not> beta_reducible t \<Longrightarrow> eta_norm t = t' \<Longrightarrow> \<not> beta_reducible t'"
proof (induction t arbitrary: t' rule: eta_norm.induct)
  case (1 T body)
  show ?case 
  proof(cases "eta_norm body")
    case (Abs T' t)
    then show ?thesis using 1 by fastforce
  next
    case (App f u)
    note oApp = this
    show ?thesis
    proof(cases u)
      case (Bv n)
      show ?thesis
      proof(cases n)
        case 0
        then show ?thesis
        proof(cases "is_dependent f")
          case True
          then show ?thesis 
            using 1 oApp Bv 0 apply simp
            using beta_reducible.simps(2) by blast
        next
          case False
          obtain body' where body': "eta_norm body = body'" by simp
          obtain f' where f': "eta_norm f = f'" by simp 
          moreover have t': "t' = decr 0 f'" using "1.prems"(2)[symmetric] oApp Bv 0 False f' by simp

          moreover have "\<not> beta_reducible t'"
          proof-
            have "\<not> beta_reducible (f $ Bv 0)"
              using "1.IH"(1) 1 oApp Bv 0 by simp
            hence "\<not> beta_reducible (decr 0 (f' $ Bv 0))"
              by (metis eta_reducible.simps(11) f' not_beta_reducible_decr 
                  not_eta_reducible_eta_norm not_eta_reducible_imp_eta_norm_no_change oApp) 
            hence "\<not> beta_reducible (decr 0 f' $ Bv 0)" by simp
            hence "\<not> beta_reducible (decr 0 f')" by (auto elim: beta_reducible.elims)
            thus ?thesis using t' by simp
          qed
          ultimately show ?thesis by blast
        qed
      next
        case (Suc nat)
        then show ?thesis using 1 oApp Bv by auto
      qed
    qed (use 1 oApp in auto)
  qed (use 1 in auto)
next
  case (2 f u)
  hence "\<not> beta_reducible f" "\<not> beta_reducible u" by (blast elim!: beta_reducible.elims(3))+
  moreover obtain f' u' where "eta_norm f = f'" "eta_norm u = u'" by simp_all
  ultimately have "\<not> beta_reducible f'" "\<not> beta_reducible u'" using "2.IH" by simp_all
  show ?case
  proof(cases t')
    case (App l r)
    then show ?thesis 
      using "2.IH"(2) "2.prems"(2) \<open>\<not> beta_reducible u\<close> \<open>\<not> beta_reducible f'\<close> \<open>eta_norm f = f'\<close> "2"(3)
      by (auto elim: beta_reducible.elims(3)) 
  qed (use "2.prems"(2) in auto)
qed auto

fun is_variable :: "term \<Rightarrow> bool" where
  "is_variable (Fv _ _) = True"
| "is_variable _ = False"

lemma fv_occs: "(x,\<tau>) \<in> fv t \<Longrightarrow> occs (Fv x \<tau>) t" 
  by (induction t) auto

lemma fv_iff_occs: "(x,\<tau>) \<in> fv t \<longleftrightarrow> occs (Fv x \<tau>) t" 
  by (induction t) auto

(* Next few definitions directly from ML code *)
fun strip_abs :: "term \<Rightarrow> typ list * term" where
  "strip_abs (Abs T t) = (let (a', t') = strip_abs t in (T # a', t'))"
| "strip_abs t = ([], t)"

(*maps  (x1,...,xn)t   to   t*)
fun strip_abs_body :: "term \<Rightarrow> term" where
  "strip_abs_body (Abs _ t) = strip_abs_body t"
| "strip_abs_body u = u"

(*maps  (x1,...,xn)t   to   [x1, ..., xn]*)
fun strip_abs_vars :: "term \<Rightarrow> typ list" where
  "strip_abs_vars (Abs T t) = T # strip_abs_vars t"
| "strip_abs_vars u = []"

(*Dropped inner helper function, instead passing qnt along.  *)
fun strip_qnt_body :: "name \<Rightarrow> term \<Rightarrow> term" where
  "strip_qnt_body qnt ((Ct c ty) $ (Abs _ t)) = 
    (if c=qnt then strip_qnt_body qnt t else (Ct c ty))"
| "strip_qnt_body _ t = t"

(*Dropped inner helper function, instead passing qnt along.  *)
fun strip_qnt_vars :: "name \<Rightarrow> term \<Rightarrow> typ list" where 
  "strip_qnt_vars qnt (Ct c _ $ Abs T t)= (if c=qnt then T # strip_qnt_vars qnt t else [])"
| "strip_qnt_vars qnt t  =  []"

(*maps   (f, [t1,...,tn])  to  f(t1,...,tn)*)
definition list_comb :: "term * term list \<Rightarrow> term" where "list_comb = case_prod (foldl ($))"
(*seems more natural curried...*)
definition list_comb' :: "term \<Rightarrow> term list \<Rightarrow> term" where "list_comb' = foldl ($)"

lemma "list_comb (h,t) = list_comb' h t" by (simp add: list_comb_def list_comb'_def)

(*curry this... ?*)
fun strip_comb_imp where
  "strip_comb_imp (f$t, ts) = strip_comb_imp (f, t # ts)"
| "strip_comb_imp x = x"

(*maps   f(t1,...,tn)  to  (f, [t1,...,tn]) ; naturally tail-recursive*)
definition strip_comb :: "term \<Rightarrow> term * term list" where
  "strip_comb u = strip_comb_imp (u,[])"

(*maps   f(t1,...,tn)  to  f , which is never a combination*)
fun head_of :: "term \<Rightarrow> term" where
  "head_of (f$t) = head_of f"
| "head_of u = u"

(*some sanity check lemmas*)

lemma fst_strip_comb_imp_eq_head_of: "fst (strip_comb_imp (t,ts)) = head_of t" 
  by (induction "(t,ts)" arbitrary: t ts rule: strip_comb_imp.induct) simp_all
corollary "fst (strip_comb t) = head_of t"
  using fst_strip_comb_imp_eq_head_of by (simp add: strip_comb_def)

(*not in ML*)
fun is_app :: "term \<Rightarrow> bool" where
  "is_app (_ $ _) = True"
| "is_app _ = False"

lemma not_is_app_imp_strip_com_imp_unchanged: "\<not> is_app t \<Longrightarrow> strip_comb_imp (t,ts) = (t,ts)" 
  by (cases t) simp_all
corollary not_is_app_imp_strip_com_unchanged: "\<not> is_app t \<Longrightarrow> strip_comb t = (t,[])" 
  unfolding strip_comb_def using not_is_app_imp_strip_com_imp_unchanged .

lemma list_comb_fuse: "list_comb (list_comb (t,ts), ss) = list_comb (t,ts@ss)"
  unfolding list_comb_def by simp        
       
fun add_size_term :: "term \<Rightarrow> int \<Rightarrow> int" where
  "add_size_term (t $ u) n = add_size_term t (add_size_term u n)"
| "add_size_term (Abs _ t) n = add_size_term t (n + 1)"
| "add_size_term _ n = n + 1"

definition "size_of_term t = add_size_term t 0"

fun add_size_type :: "typ \<Rightarrow> int \<Rightarrow> int" where
  "add_size_type (Ty _ tys) n = fold add_size_type tys (n + 1)"
| "add_size_type _ n = n + 1"

definition "size_of_type ty = add_size_type ty 0"

fun map_types :: "(typ \<Rightarrow> typ) \<Rightarrow> term \<Rightarrow> term" where
  "map_types f (Ct a T) = Ct a (f T)"
| "map_types f (Fv v T) = Fv v (f T)"
| "map_types f (Bv i) = Bv i"
| "map_types f (Abs T t) = Abs (f T) (map_types f t)"
| "map_types f (t $ u) = map_types f t $ map_types f u"

fun map_atyps :: "(typ \<Rightarrow> typ) \<Rightarrow> typ \<Rightarrow> typ" where
  "map_atyps f (Ty a Ts) = Ty a (map (map_atyps f) Ts)"
| "map_atyps f T = f T"

lemma "map_atyps id ty = ty"
  by (induction rule: typ.induct) (simp_all add: map_idI)

fun map_aterms :: "(term \<Rightarrow> term) \<Rightarrow> term \<Rightarrow> term" where
  "map_aterms f (t $ u) = map_aterms f t $ map_aterms f u"
| "map_aterms f (Abs T t) = Abs T (map_aterms f t)"
| "map_aterms f t = f t"

lemma "map_aterms id t = t"
  by (induction rule: term.induct) simp_all

definition "map_type_tvar f = map_atyps (\<lambda>x . case x of Tv iname s \<Rightarrow>  f iname s | T \<Rightarrow> T)"

lemma map_types_id[simp]: "map_types id t = t"
  by (induction t) simp_all
lemma map_types_id'[simp]: "map_types (\<lambda>a . a) t = t"
  using map_types_id by (simp add: id_def)

(* fold types and terms *)                
fun fold_atyps :: "(typ \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> typ \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fold_atyps f (Ty _ Ts) s = fold (fold_atyps f) Ts s"
| "fold_atyps f T s = f T s"

definition "fold_atyps_sorts f =
  fold_atyps (\<lambda>x . case x of Tv vn S \<Rightarrow> f (Tv vn S) S)"

fun fold_aterms :: "(term \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> term \<Rightarrow> 'a \<Rightarrow> 'a" where
  "fold_aterms f (t $ u) s = fold_aterms f u (fold_aterms f t s)"
| "fold_aterms f (Abs _ t) s = fold_aterms f t s"
| "fold_aterms f a s = f a s"

fun fold_term_types :: "(term \<Rightarrow> typ \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> term \<Rightarrow> 'a \<Rightarrow> 'a" where 
  "fold_term_types f (Ct n T) s = f (Ct n T) T s"
| "fold_term_types f (Fv idn T) s = f (Fv idn T) T s"
| "fold_term_types f (Bv _) s = s"
| "fold_term_types f (Abs T b) s = fold_term_types f b (f (Abs T b) T s)"
| "fold_term_types f (t $ u) s = fold_term_types f u (fold_term_types f t s)"

definition "fold_types f = fold_term_types (\<lambda>x . f)"

(* Patterns for empty list except with Bv missing. Probably need a precond when using *)
fun replace_types :: "term \<Rightarrow> typ list \<Rightarrow> term \<times> typ list" where
  "replace_types (Ct c _) (T # Ts) = (Ct c T, Ts)"
| "replace_types (Fv xi _) (T # Ts) = (Fv xi T, Ts)"
| "replace_types (Bv i) Ts = (Bv i, Ts)"
| "replace_types (Abs _ b) (T # Ts) =
    (let (b', Ts') = replace_types b Ts
    in (Abs T b', Ts'))"
| "replace_types (t $ u) Ts =
    (let
      (t', Ts') = replace_types t Ts in
      (let (u', Ts'') = replace_types u Ts
    in (t' $ u', Ts'')))"

(* 
  collect variables, is the order important? Or should I just return sets? 
  The set case is basically just (T)fv(T)...
  List.insert should keep order, just no duplicates...
*)
definition "add_tvar_namesT' = fold_atyps (\<lambda>x l . case x of Tv xi _ => List.insert xi l | _ => l)"
definition "add_tvar_names' = fold_types add_tvar_namesT'"
definition "add_tvarsT' = fold_atyps (\<lambda>x l . case x of Tv idn s => List.insert (idn,s) l | _ => l)"
definition "add_tvars' = fold_types add_tvarsT'"
definition "add_vars' = fold_aterms (\<lambda>x l . case x of Fv idn s => List.insert (idn,s) l | _ => l)"
definition "add_var_names' = fold_aterms (\<lambda>x l . case x of Fv xi _ => List.insert xi l | _ => l)"

definition "add_const_names' = fold_aterms (\<lambda>x l . case x of Ct c _ => List.insert c l | _ => l)"
definition "add_consts' = fold_aterms (\<lambda>x l . case x of Ct n s => List.insert (n,s) l | _ => l)"

definition "add_tvar_namesT = fold_atyps (\<lambda>x . case x of Tv xi _  => insert xi | _ => id)"
definition "add_tvar_names = fold_types add_tvar_namesT"
definition "add_tvarsT = fold_atyps (\<lambda>x . case x of Tv idn s => insert (idn,s) | _ => id)"
definition "add_tvars = fold_types add_tvarsT"
definition "add_var_names = fold_aterms (\<lambda>x . case x of Fv xi _ => insert xi | _ => id)"
definition "add_vars = fold_aterms (\<lambda>x . case x of Fv idn s => insert (idn,s) | _ => id)"

definition "add_const_names = fold_aterms (\<lambda>x . case x of Ct c _ => insert c | _ => id)"
definition "add_consts = fold_aterms (\<lambda>x . case x of Ct n s => insert (n,s) | _ => id)"
(*which of those do I need ^ *)

(* Show that these behave like (T)fv(T)? *)

lemma add_tvarsT'_tvsT_pre[simp]: "set (add_tvarsT' T acc) = set acc \<union> tvsT T"
  unfolding add_tvarsT'_def
proof (induction T arbitrary: acc)
  case (Ty n Ts)
  then show ?case by (induction Ts arbitrary: acc) auto
qed auto

lemma add_tvars'_tvs_pre[simp]: "set (add_tvars' t acc) = set acc \<union> tvs t"
  by (induction t arbitrary: acc) (auto simp add: add_tvars'_def fold_types_def)

lemma "add_tvarsT T acc = acc \<union> tvsT T"
  unfolding add_tvarsT_def
proof (induction T arbitrary: acc)
  case (Ty n Ts)
  then show ?case by (induction Ts arbitrary: acc) auto
qed auto

lemma add_vars'_fv_pre: "set (add_vars' t acc) = set acc \<union> fv t"
  unfolding add_vars'_def by (induction t arbitrary: acc) auto
corollary add_vars'_fv: "set (add_vars' t []) = fv t"
  using add_vars'_fv_pre by simp
(*extra type variables in a term, not covered by its type*)

(* For some experiments for handling \<And>*)

(* I differ from the ML code here, requiring the correct typ for the \<And>*)
fun strip_all_body :: "term \<Rightarrow> term" where
  "strip_all_body (Ct all S $ Abs T t) = (if all= STR ''Pure.all'' \<and> S=(T\<rightarrow>propT)\<rightarrow>propT
    then strip_all_body t else (Ct all S $ Abs T t))"
| "strip_all_body t = t"

fun strip_all_vars :: "term \<Rightarrow> typ list" where
  "strip_all_vars (Ct all S $ Abs T t) = (if all= STR ''Pure.all'' \<and> S=(T\<rightarrow>propT)\<rightarrow>propT 
    then T # strip_all_vars t else [])"
| "strip_all_vars t = []"

fun strip_all_single_body :: "term \<Rightarrow> term" where
  "strip_all_single_body (Ct all S $ Abs T t) = (if all= STR ''Pure.all'' \<and> S=(T\<rightarrow>propT)\<rightarrow>propT 
    then t else (Ct all S $ Abs T t))"
| "strip_all_single_body t = t"

fun strip_all_single_var :: "term \<Rightarrow> typ option" where
  "strip_all_single_var (Ct all S $ Abs T t) = (if all= STR ''Pure.all'' \<and> S=(T\<rightarrow>propT)\<rightarrow>propT
    then Some T else None)"
| "strip_all_single_var t = None"

fun strip_all_multiple_body :: "nat \<Rightarrow> term \<Rightarrow> term" where
  "strip_all_multiple_body 0 t = t"
| "strip_all_multiple_body (Suc n) (Ct all S $ Abs T t) = (if all= STR ''Pure.all'' \<and> S=(T\<rightarrow>propT)\<rightarrow>propT
    then strip_all_multiple_body n t else (Ct all S $ Abs T t))"
| "strip_all_multiple_body _ t = t"

fun strip_all_multiple_vars :: "nat \<Rightarrow> term \<Rightarrow> typ list" where
  "strip_all_multiple_vars 0 _ = []"
| "strip_all_multiple_vars (Suc n) (Ct all S $ Abs T t) = (if all= STR ''Pure.all'' \<and> S=(T\<rightarrow>propT)\<rightarrow>propT 
    then T # strip_all_multiple_vars n t else [])"
| "strip_all_multiple_vars _ t = []"

lemma strip_all_vars_strip_all_multiple_vars: 
  "n\<ge>length (strip_all_vars t) \<Longrightarrow> strip_all_multiple_vars n t = strip_all_vars t"
  by (induction n t rule: strip_all_multiple_vars.induct) auto
lemma "n\<ge>length (strip_all_vars t) \<Longrightarrow> strip_all_multiple_body n t = strip_all_body t"
  by (induction n t rule: strip_all_multiple_vars.induct) (auto elim!: strip_all_vars.elims)

lemma length_strip_all_multiple_vars: "length (strip_all_multiple_vars n t) \<le> n"
  by (induction n t rule: strip_all_multiple_vars.induct) auto 

lemma prefix_strip_all_multiple_vars: "prefix (strip_all_multiple_vars n t) (strip_all_vars t)"
  unfolding prefix_def by (induction n t rule: strip_all_multiple_vars.induct) auto

definition "mk_all_list l t = fold (\<lambda>(n,T) acc . mk_all n T acc) l t"

lemma mk_all_list_empty[simp]: "mk_all_list [] t = t" by (simp add: mk_all_list_def)
                                         
(* Again, need correct typ here *)
fun is_all :: "term \<Rightarrow> bool" where
  "is_all (Ct all S $ Abs T t) = (all= STR ''Pure.all'' \<and> S=(T\<rightarrow>propT)\<rightarrow>propT)"
| "is_all _ = False"

lemma strip_all_single_var_is_all: "strip_all_single_var t \<noteq> None \<longleftrightarrow> is_all t"
  apply (cases t) apply simp_all 
  subgoal for f u apply (cases f; cases u) by (auto elim: is_all.elims split: if_splits) 
  done

lemma "is_all t \<Longrightarrow> hd (strip_all_vars t) = the (strip_all_single_var t)"
  by (auto elim: is_all.elims)

lemma strip_all_body_single_simp[simp]: "strip_all_body (strip_all_single_body t) = strip_all_body t"
  by (induction t rule: strip_all_body.induct) auto 
lemma strip_all_body_single_simp'[simp]: "strip_all_single_body (strip_all_body t) = strip_all_body t"
  by (induction t rule: strip_all_body.induct) auto

lemma strip_all_vars_step: 
  "strip_all_single_var t = Some T \<Longrightarrow> T # strip_all_vars (strip_all_single_body t) = strip_all_vars t"
  by (induction t arbitrary: T rule: strip_all_vars.induct) (auto split: if_splits) 

lemma is_all_iff_strip_all_vars_not_empty: "is_all t \<longleftrightarrow> strip_all_vars t \<noteq> []"
  apply (cases t) apply simp_all
  subgoal for f u apply (cases f; cases u) by (auto elim: strip_all_vars.elims is_all.elims split: if_splits)
  done

lemma strip_all_vars_bind_fv: 
  "strip_all_vars (bind_fv2 v lev t) = (strip_all_vars t)"
  by (induction t arbitrary: lev rule: strip_all_vars.induct) auto

lemma strip_all_vars_mk_all[simp]: "strip_all_vars (mk_all s ty t) = ty # strip_all_vars t"
  using bind_fv_def strip_all_vars_bind_fv typ_of_def by auto

lemma strip_all_vars_mk_all_list:
  "\<not>is_all t \<Longrightarrow> strip_all_vars (mk_all_list l t) = rev (map snd l)"
proof (induction l rule: rev_induct)
  case Nil
  then show ?case using is_all_iff_strip_all_vars_not_empty by simp
next
  case (snoc v vs)
  hence I: "strip_all_vars (mk_all_list vs t) = rev (map snd vs)" by simp
  obtain s ty where v: "v = (s,ty)" by fastforce

  have "strip_all_vars (mk_all_list (vs @ [v]) t) 
    = strip_all_vars (mk_all s ty (mk_all_list vs t))"
    by (auto simp add: mk_all_list_def v)
  also have "\<dots> = ty # strip_all_vars (mk_all_list vs t)"
    using strip_all_vars_mk_all[of ty s "mk_all_list vs t"] by blast
  also have "\<dots> = ty # rev (map snd vs)"
    by (simp add: I)
  also have "\<dots> = rev (map snd (vs @ [v]))"
    using v by simp
  finally show ?case .
qed

(* Move up *)
lemma subst_bv_no_loose_unchanged:
  assumes "\<And>x . x \<ge> lev \<Longrightarrow> \<not> loose_bvar1 t x"
  assumes "is_variable v"
  shows "(subst_bv1 t lev v) = t"
using assms proof (induction t arbitrary: lev)
  case (Bv x)
  then show ?case
    using loose_bvar_iff_exist_loose_bvar1 no_loose_bvar_imp_no_subst_bv1 by presburger
next
  case (Abs T t)
  then show ?case
    using loose_bvar_iff_exist_loose_bvar1 no_loose_bvar_imp_no_subst_bv1 by presburger
qed auto

(* Should state those in terms "of \<in> fv", occs is a relict *)
lemma bind_fv2_no_occs_unchanged:
  assumes "\<not> occs (case_prod Fv v) t"
  shows "(bind_fv2 v lev t) = t"
  using assms by (induction t arbitrary: lev) auto

lemma bind_fv2_subst_bv1_cancel:
  assumes "\<And>x . x > lev \<Longrightarrow> \<not> loose_bvar1 t x"
  assumes "\<not> occs (case_prod Fv v)  t"
  shows "bind_fv2 v lev (subst_bv1 t lev (case_prod Fv v)) = t"
  using assms proof (induction t arbitrary: lev)
  case (Bv x)
  then show ?case
    using linorder_neqE_nat 
    by (auto split: prod.splits simp add: is_variable_imp_incr_boundvars_unchganged)
next
  case (Abs T t)
  hence "bind_fv2 v (lev+1) (subst_bv1 t (lev+1) (case_prod Fv v)) = t" 
    by (auto elim: Suc_lessE)
  then show ?case by simp
next
  (* This proof contains so much duplication it makes me vomit... 
    Got even uglier after translation
  *)
  case (App t1 t2)
  then show ?case
  proof(cases "loose_bvar1 t1 lev")
    case True
    hence I1: "bind_fv2 v lev (subst_bv1 t1 lev (case_prod Fv v)) = t1" using App by auto 
    then show ?thesis
    proof(cases "loose_bvar1 t2 lev")
      case True
      hence "bind_fv2 v lev (subst_bv1 t2 lev (case_prod Fv v)) = t2" using App by auto
      then show ?thesis using I1 App.prems is_variable.elims(2) by auto
    next
      case False
      hence "bind_fv2 v lev (subst_bv1 t2 lev  (case_prod Fv v)) = t2"
      proof-
        have "subst_bv1 t2 lev  (case_prod Fv v) = t2" using subst_bv_no_loose_unchanged
          using App.prems(1-2) False assms le_neq_implies_less loose_bvar1.simps(2)
          by (metis loose_bvar_iff_exist_loose_bvar1 no_loose_bvar_imp_no_subst_bv1)
        moreover have "bind_fv2 v lev t2 = t2"
          using App.prems(2) bind_fv2_no_occs_unchanged
          using App.prems(2) bind_fv2_changed' exists_subterm'.simps(1) 
            exists_subterm_iff_exists_subterm' by blast
        ultimately show ?thesis by simp
      qed
      then show ?thesis using I1 App.prems is_variable.elims(2) by auto
    qed
  next
    case False
    hence I1: "bind_fv2 v lev (subst_bv1 t1 lev (case_prod Fv v)) = t1"
    proof-
      have "subst_bv1 t1 lev (case_prod Fv v) = t1" using subst_bv_no_loose_unchanged
        using App.prems(1-2) False le_neq_implies_less loose_bvar1.simps(2) 
          by (metis loose_bvar_iff_exist_loose_bvar1 no_loose_bvar_imp_no_subst_bv1)
      moreover have "bind_fv2 v lev t1 = t1"
        using App.prems(2) bind_fv2_no_occs_unchanged by auto
      ultimately show ?thesis by simp
    qed
    then show ?thesis
    proof(cases "loose_bvar1 t2 lev")
      case True
      hence "bind_fv2 v lev (subst_bv1 t2 lev (case_prod Fv v)) = t2" using App by auto
      then show ?thesis using I1 App.prems is_variable.elims(2) by auto
    next
      case False
      hence "bind_fv2 v lev (subst_bv1 t2 lev (case_prod Fv v)) = t2"
      proof-
        have "subst_bv1 t2 lev (case_prod Fv v) = t2" using subst_bv_no_loose_unchanged
          using App.prems(1-2) False assms le_neq_implies_less loose_bvar1.simps(2) 
          by (metis loose_bvar_iff_exist_loose_bvar1 no_loose_bvar_imp_no_subst_bv1)
        moreover have "bind_fv2 v lev t2 = t2"
          using App.prems(2) bind_fv2_no_occs_unchanged by auto
        ultimately show ?thesis by simp
      qed
      then show ?thesis using I1 App.prems is_variable.elims(2) by auto
    qed
  qed
qed auto

lemma bind_fv_subst_bv_cancel:
  assumes "\<And>x . x > 0 \<Longrightarrow> \<not> loose_bvar1 t x"
  assumes "\<not> occs (case_prod Fv v) t"
  shows "bind_fv v (subst_bv (case_prod Fv v) t) = t"
  using bind_fv2_subst_bv1_cancel bind_fv_def assms subst_bv_def by auto
  
lemma not_loose_bvar_imp_not_loose_bvar1_all_greater: "\<not> loose_bvar t lev \<Longrightarrow> x>lev \<Longrightarrow> \<not> loose_bvar1 t x"
  by (simp add: loose_bvar_iff_exist_loose_bvar1)

lemma mk_all'_subst_bv_strip_all_single_body_cancel:
  assumes "strip_all_single_var t = Some T"
  assumes "is_closed t"
  assumes "(name, T) \<notin> fv t"
  shows "mk_all name T (subst_bv (Fv name T) (strip_all_single_body t) ) = t"
proof-
  from assms(1) obtain t' where t': "(Ct STR ''Pure.all'' ((T \<rightarrow> propT) \<rightarrow> propT) $ Abs T t') = t" 
    by (auto elim!: strip_all_single_var.elims 
        simp add: bind_eq_Some_conv typ_of_def split: if_splits option.splits if_splits)
 
  hence s: "strip_all_single_body t = t'" by auto

  have "\<And>x. x > 0 \<Longrightarrow> \<not> loose_bvar1 t x"
    using assms(2) is_open_def loose_bvar_iff_exist_loose_bvar1 by blast 

  have "0 < x \<Longrightarrow> \<not> loose_bvar1 t' x" for x
      using assms(2) by (auto simp add: is_open_def t'[symmetric] loose_bvar_iff_exist_loose_bvar1 gr0_conv_Suc)

  have "occs t' t" by (simp add: t'[symmetric])

  have "bind_fv (name, T) (subst_bv (Fv name T) (strip_all_single_body t)) =
    (strip_all_single_body t)" 
    using assms(2-3) bind_fv_subst_bv_cancel gr0_conv_Suc
    by (force simp add: s is_open_def t'[symmetric] 
        loose_bvar_iff_exist_loose_bvar1 fv_iff_occs intro!: bind_fv_subst_bv_cancel)
  then show ?thesis using assms by (auto simp add: s typ_of_def t') 
qed

lemma not_is_all_imp_strip_all_body_unchanged: "\<not> is_all t \<Longrightarrow> strip_all_body t = t"
  by (auto elim!: is_all.elims split: if_splits) 

lemma no_loose_bvar_imp_no_subst_bvs: "is_closed t \<Longrightarrow> subst_bvs [] t = t"
  using no_loose_bvar_imp_no_subst_bvs1 subst_bvs_def is_open_def by simp

lemma "is_closed (Abs T t) \<Longrightarrow> \<not> loose_bvar t 1" unfolding is_open_def by simp

lemma bind_fv2_Fv_fv[simp]: "fv (bind_fv2 (x, \<tau>) lev t) = fv t - {(x,\<tau>)}"
  by (induction "(x, \<tau>)" lev t rule: bind_fv2.induct) (auto split: if_splits term.splits)

corollary mk_all_fv_unchanged: "fv (mk_all x \<tau> B) = fv B - {(x,\<tau>)}"
  using bind_fv2_Fv_fv bind_fv_def by auto

lemma mk_all_list_fv_unchanged: "fv (mk_all_list l B) = fv B - set l"
proof (induction l arbitrary: B rule: rev_induct)
  case Nil
  then show ?case by simp
next
  (* After translation, look at proof again*)
  case (snoc x xs)
  have s: "mk_all_list (xs@[x]) B = case_prod mk_all x (mk_all_list xs B)" 
    by (simp add: mk_all_list_def)
  show ?case 
    by (simp only: s "snoc.IH" mk_all_fv_unchanged split: prod.splits) auto
qed

(* Hs parameter to check if var is fixed by hypotheses *)
abbreviation "forall_intro_vars t Hs \<equiv> mk_all_list 
  (diff_list (add_vars' t []) (fold (add_vars') Hs [])) t"

end