section "Executable Instance Relations"

theory Instances
  imports Term
begin

(*
  Executable versions for the following definitions

  Do by computing such a \<rho> 

  First using partial functions, then with alists

  definition "tinstT T1 T2 \<equiv> \<exists>\<rho>. tsubstT T2 \<rho> = T1"
  definition "tinst t1 t2 \<equiv> \<exists>\<rho>. tsubst t2 \<rho> = t1"
  definition "inst t1 t2 \<equiv> \<exists>\<rho>. subst t2 \<rho> = t1" 
*)
         
(* Straight forward code translation from ML code in distribution *)
fun raw_match :: "typ \<Rightarrow> typ \<Rightarrow> ((variable \<times> sort) \<rightharpoonup> typ) \<Rightarrow> ((variable \<times> sort) \<rightharpoonup> typ) option" 
  and raw_matches :: "typ list \<Rightarrow> typ list \<Rightarrow> ((variable \<times> sort) \<rightharpoonup> typ) \<Rightarrow> ((variable \<times> sort) \<rightharpoonup> typ) option" 
  where
  "raw_match (Tv v S) T subs =
    (case subs (v,S) of
      None \<Rightarrow> Some (subs((v,S) := Some T))
    | Some U \<Rightarrow> (if U = T then Some subs else None))"
| "raw_match (Ty a Ts) (Ty b Us) subs =
    (if a=b then raw_matches Ts Us subs else None)"
| "raw_match _ _ _ = None"
| "raw_matches (T#Ts) (U#Us) subs = Option.bind (raw_match T U subs) (raw_matches Ts Us)"
| "raw_matches [] [] subs = Some subs"
| "raw_matches _ _ subs = None"

(* Probably easier to use *)
function (sequential) raw_match' 
  :: "typ \<Rightarrow> typ \<Rightarrow> ((variable \<times> sort) \<rightharpoonup> typ) \<Rightarrow> ((variable \<times> sort) \<rightharpoonup> typ) option" where
  "raw_match' (Tv v S) T subs =
    (case subs (v,S) of
      None \<Rightarrow> Some (subs((v,S) := Some T))
    | Some U \<Rightarrow> (if U = T then Some subs else None))"
| "raw_match' (Ty a Ts) (Ty b Us) subs =
    (if a=b \<and> length Ts = length Us 
      then fold (\<lambda>(T, U) subs . Option.bind subs (raw_match' T U)) (zip Ts Us) (Some subs)
      else None)"
| "raw_match' T U subs = (if T = U then Some subs else None)"
  by pat_completeness auto
termination proof (relation "measure (\<lambda>(T, U, subs) . size T + size U)", goal_cases)
  case 1
  then show ?case 
    by auto
next
  case (2 a Ts b Us subs x xa y xb aa)
  hence "length Ts = length Us" "a=b"
    by auto
  from this 2(2-) show ?case 
    by (induction Ts Us rule: list_induct2) auto
qed

lemma length_neq_imp_not_raw_matches: "length Ts \<noteq> length Us \<Longrightarrow> raw_matches Ts Us subs = None" 
  by (induction Ts Us subs rule: raw_match_raw_matches.induct(2) [where P = "\<lambda>T U subs . True"])
    (auto cong: Option.bind_cong)

(* Making sure I did not mess up my version of the definition *)
lemma "raw_match T U subs = raw_match' T U subs"
proof (induction T U subs rule: raw_match_raw_matches.induct(1)
      [where Q = "\<lambda>Ts Us subs . raw_matches Ts Us subs 
        = (if length Ts = length Us 
      then fold (\<lambda>(T, U) subs . Option.bind subs (raw_match' T U)) (zip Ts Us) (Some subs)
      else None)"])
  case (4 T Ts U Us subs)
  then show ?case
  proof (cases "raw_match T U subs")
    case None
    then show ?thesis
    proof (cases "length Ts = length Us")
      case True
      then show ?thesis using 4 None by (induction Ts Us rule: list_induct2) auto
    next
      case False
      then show ?thesis using 4 None length_neq_imp_not_raw_matches by auto
    qed 
  next
    case (Some a)
    then show ?thesis using 4 by auto
  qed
qed simp_all

lemma raw_match'_map_le: "raw_match' T U subs = Some subs' \<Longrightarrow> map_le subs subs'"
proof (induction T U subs arbitrary: subs' rule: raw_match'.induct)
  case (2 a Ts b Us subs)
  have "length Ts = length Us"
    using "2.prems" by (auto split: if_splits) 
  moreover have I: "(a,b) \<in> set (zip Ts Us) \<Longrightarrow> raw_match' a b subs = Some subs' \<Longrightarrow> subs \<subseteq>\<^sub>m subs'" 
      for a b subs subs' 
    using "2.prems" by (auto split: if_splits intro: "2.IH")
  ultimately show ?case using "2.prems" 
  proof (induction Ts Us arbitrary: subs subs' rule: rev_induct2)
    case Nil
    then show ?case
      by (auto split: if_splits) 
  next
    case (snoc x xs y ys)
    then show ?case 
      using map_le_trans by (fastforce split: if_splits prod.splits simp add: bind_eq_Some_conv)
  qed
qed (auto simp add: map_le_def split: if_splits option.splits)

(* Specializing for raw_match' *)
lemma fold_matches_first_step_not_None:
  assumes
    "fold (\<lambda>(T, U) subs . Option.bind subs (raw_match' T U)) (zip (x#xs) (y#ys)) (Some subs) = Some subs'" 
  obtains point where
    "raw_match' x y subs = Some point"
    "fold (\<lambda>(T, U) subs . Option.bind subs (raw_match' T U)) (zip (xs) (ys)) (Some point) = Some subs'"
  using fold_matches_first_step_not_None assms .
lemma fold_matches_last_step_not_None:
  assumes
    "length xs = length ys"
    "fold (\<lambda>(T, U) subs . Option.bind subs (raw_match' T U)) (zip (xs@[x]) (ys@[y])) (Some subs) = Some subs'" 
  obtains point where
    "fold (\<lambda>(T, U) subs . Option.bind subs (raw_match' T U)) (zip (xs) (ys)) (Some subs) = Some point"
    "raw_match' x y point = Some subs'"
  using fold_matches_last_step_not_None assms .

corollary raw_match'_Type_conds:
  assumes "raw_match' (Ty a Ts) (Ty b Us) subs = Some subs'"
  shows "a=b" "length Ts = length Us"
  using assms by (auto split: if_splits)

corollary fold_matches_first_step_not_None':
  assumes "length xs = length ys"
    "fold (\<lambda>(T, U) subs . Option.bind subs (raw_match' T U)) (zip (x#xs) (y#ys)) (Some subs) = Some subs'"  
  shows "raw_match' x y subs ~= None"
  using assms fold_matches_first_step_not_None 
  by (metis option.discI) 

corollary raw_match'_hd_raw_match':
  assumes "raw_match' (Ty a (T#Ts)) (Ty b (U#Us)) subs = Some subs'"
  shows "raw_match' T U subs ~= None"
  using assms fold_matches_first_step_not_None' raw_match'_Type_conds
  by (metis (no_types, lifting) length_Cons nat.simps(1) raw_match'.simps(2))

corollary raw_match'_eq_Some_at_point_not_None':
  assumes "length Ts = length Us"
  assumes "raw_match' (Ty a (Ts@Ts')) (Ty b (Us@Us')) subs = Some subs'"
  shows "raw_match' (Ty a (Ts)) (Ty b (Us)) subs ~= None"
  using assms fold_Option_bind_eq_Some_at_point_not_None' by (fastforce split: if_splits)

(* I should have defined a custom induction rule here, instead I copied the structure of the proof 
  each time... Clean up when time
*)

lemma raw_match'_tvsT_subset_dom_res: "raw_match' T U subs = Some subs' \<Longrightarrow> tvsT T \<subseteq> dom subs'"
proof (induction T U subs arbitrary: subs' rule: raw_match'.induct)
  case (2 a Ts b Us subs)
  have l: "length Ts = length Us" "a = b" using 2 
    by (metis option.discI raw_match'.simps(2))+
  
  from this 2 have better_IH: 
    "(x, y) \<in> set (zip Ts Us) \<Longrightarrow> raw_match' x y subs = Some subs' \<Longrightarrow> tvsT x \<subseteq> dom subs'"
    for x y subs subs' by simp
  from l "2.prems" better_IH show ?case
  proof (induction Ts Us arbitrary: a b subs subs' rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)
    obtain point where point: "raw_match' x y subs = Some point"
      and rest: "raw_match' (Ty a xs) (Ty b ys) point = Some subs'"
      by (metis (no_types, lifting) Cons.hyps Cons.prems(1) Cons.prems(2) fold_matches_first_step_not_None 
          raw_match'.simps(2) raw_match'_Type_conds(2))  

    have "tvsT (Ty a xs) \<subseteq> dom subs'"
      apply (rule Cons.IH[of _ b point])
      using Cons.prems rest apply blast+
      by (metis Cons.prems(3) list.set_intros(2) zip_Cons_Cons)
    moreover have "tvsT x \<subseteq> dom point"
      by (metis Cons.prems(3) list.set_intros(1) point zip_Cons_Cons)
    moreover have "dom point \<subseteq> dom subs'"
      using map_le_implies_dom_le raw_match'_map_le rest by blast
    ultimately show ?case
      by auto
  qed
qed (auto split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv) 

lemma raw_match'_dom_res_subset_tvsT: 
  "raw_match' T U subs = Some subs' \<Longrightarrow> dom subs' \<subseteq> tvsT T \<union> dom subs"
proof (induction T U subs arbitrary: subs' rule: raw_match'.induct)
  case (2 a Ts b Us subs)
  have l: "length Ts = length Us" "a = b" using 2 
    by (metis option.discI raw_match'.simps(2))+
  
  from this 2 have better_IH: 
    "(x, y) \<in> set (zip Ts Us) \<Longrightarrow> raw_match' x y subs = Some subs' 
      \<Longrightarrow> dom subs' \<subseteq> tvsT x \<union> dom subs"
    for x y subs subs' by blast
  from l "2.prems" better_IH show ?case
  proof (induction Ts Us arbitrary: a b subs subs' rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)
    obtain point where first: "raw_match' x y subs = Some point"
      and rest: "raw_match' (Ty a xs) (Ty b ys) point = Some subs'"
      by (metis (no_types, lifting) Cons.hyps Cons.prems(1) Cons.prems(2) fold_matches_first_step_not_None raw_match'.simps(2) raw_match'_Type_conds(2))

    from first have "dom point \<subseteq> tvsT x \<union> dom subs"
      using Cons.prems(3) by fastforce
    moreover have "dom subs' \<subseteq> tvsT (Ty a xs) \<union> dom point"
      apply (rule Cons.IH)
      using Cons.prems(1) apply simp
      using Cons.prems(2) rest apply simp
      by (metis Cons.prems(3) list.set_intros(2) zip_Cons_Cons)
    
    ultimately show ?case using Cons.prems in_mono
      apply (clarsimp split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv domIff)
      by (smt UN_iff Un_iff domIff in_mono option.distinct(1))
      (*by fastforce, but too slow, check later *)
  qed
qed (auto split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv) 

corollary raw_match'_dom_res_eq_tvsT: 
  "raw_match' T U subs = Some subs' \<Longrightarrow> dom subs' = tvsT T \<union> dom subs"
  by (simp add: map_le_implies_dom_le raw_match'_tvsT_subset_dom_res 
      raw_match'_dom_res_subset_tvsT raw_match'_map_le subset_antisym)

corollary raw_match'_dom_res_eq_tvsT_empty: 
  "raw_match' T U (\<lambda>x. None) = Some subs' \<Longrightarrow> dom subs' = tvsT T"
  using raw_match'_dom_res_eq_tvsT by simp

lemma raw_match'_map_defined: "raw_match' T U subs = Some subs' \<Longrightarrow> p\<in>tvsT T \<Longrightarrow> subs' p ~= None" 
  using raw_match'_dom_res_eq_tvsT by blast

lemma raw_match'_extend_map_preserve:
  "raw_match' T U subs = Some subs' \<Longrightarrow> map_le subs' subs'' \<Longrightarrow> p\<in>tvsT T \<Longrightarrow> subs'' p = subs' p" 
  using raw_match'_dom_res_eq_tvsT domIff map_le_implies_dom_le 
  by (simp add: map_le_def)

abbreviation "convert_subs subs \<equiv> (\<lambda>v S . the_default (Tv v S) (subs (v, S)))"

lemma map_eq_on_tvsT_imp_map_eq_on_typ:
  "(\<And>p . p\<in>tvsT T \<Longrightarrow> subs p = subs' p) 
  \<Longrightarrow> tsubstT T (convert_subs subs)
    = tsubstT T (convert_subs subs')"
  by (induction T) auto

lemma raw_match'_extend_map_preserve':
  assumes "raw_match' T U subs = Some subs'" "map_le subs' subs''"
  shows "tsubstT T (convert_subs subs')
    = tsubstT T (convert_subs subs'')"
  apply (rule map_eq_on_tvsT_imp_map_eq_on_typ)
  using raw_match'_extend_map_preserve assms by metis

lemma raw_match'_produces_matcher:
  "raw_match' T U subs = Some subs' 
    \<Longrightarrow> tsubstT T (convert_subs subs') = U"
proof (induction T U subs arbitrary: subs' rule: raw_match'.induct)
  case (2 a Ts b Us subs)
  hence l: "length Ts = length Us" "a=b" by (simp_all split: if_splits)
  from this 2 have better_IH: 
    "(x, y) \<in> set (zip Ts Us) \<Longrightarrow> raw_match' x y subs = Some subs' 
    \<Longrightarrow> tsubstT x (convert_subs subs') = y"
    for x y subs subs' by simp
  from l better_IH show ?case using 2
  proof(induction Ts Us arbitrary: subs subs' rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)
    obtain point where first: "raw_match' x y subs = Some point"
      and rest: "raw_match' (Ty a xs) (Ty b ys) point = Some subs'"
      by (metis (no_types, lifting) Cons.hyps Cons.prems(4) fold_matches_first_step_not_None l(2) length_Cons raw_match'.simps(2))

    have "tsubstT x (convert_subs point) = y"
      using Cons.prems(2) first by auto
    moreover have "map_le point subs'"
      using raw_match'_map_le rest by blast
    ultimately have subs'_hd: "tsubstT x (convert_subs subs') = y" 
      using raw_match'_extend_map_preserve' first by simp

    show ?case using Cons by (auto simp add: bind_eq_Some_conv subs'_hd first)
  qed
qed (auto split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv) 

lemma tsubstT_matcher_imp_raw_match'_unchanged:
  "tsubstT T \<rho> = U \<Longrightarrow> raw_match' T U (\<lambda>(idx, S). Some (\<rho> idx S)) = Some (\<lambda>(idx, S). Some (\<rho> idx S))"
proof (induction T arbitrary: U \<rho>)
  case (Ty a Ts)
  then show ?case
  proof (induction Ts arbitrary: U)
    case Nil
    then show ?case by auto
  next
    case (Cons T Ts)
    then show ?case 
      by auto
  qed
qed auto

lemma raw_match'_imp_raw_match'_on_map_le:
  assumes "raw_match' T U subs = Some subs'"
  assumes "map_le lesubs subs"
  shows "\<exists>lesubs'. raw_match' T U lesubs = Some lesubs' \<and> map_le lesubs' subs'"
  using assms proof (induction T U subs arbitrary: lesubs subs' rule: raw_match'.induct)
  case (1 v S T subs lesubs subs')
  then show ?case 
    by (force split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv map_le_def
        intro!: domI)
next
  case (2 a Ts b Us subs)
  hence l: "length Ts = length Us" "a=b" by (simp_all split: if_splits)
  from this 2 have better_IH: 
    "(x, y) \<in> set (zip Ts Us) \<Longrightarrow> raw_match' x y subs = Some subs' 
    \<Longrightarrow> lesubs \<subseteq>\<^sub>m subs \<Longrightarrow> \<exists>lesubs'. raw_match' x y lesubs = Some lesubs' \<and> lesubs' \<subseteq>\<^sub>m subs'"
    for x y subs lesubs subs' by simp
  from l better_IH show ?case using 2
  proof(induction Ts Us arbitrary: subs lesubs subs' rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)
    obtain point where first: "raw_match' x y subs = Some point"
      and rest: "raw_match' (Ty a xs) (Ty b ys) point = Some subs'"
      by (metis (no_types, lifting) Cons.hyps Cons.prems(4) fold_matches_first_step_not_None l(2) length_Cons raw_match'.simps(2))

    have "\<exists>lepoint. raw_match' x y lesubs = Some lepoint \<and> lepoint \<subseteq>\<^sub>m point"
      using Cons first by auto
    from this obtain lepoint where 
        comp_lepoint: "raw_match' x y lesubs = Some lepoint" and le_lepoint: "lepoint \<subseteq>\<^sub>m point"
      by auto

    have "\<exists>lesubs'. raw_match' (Ty a xs) (Ty b ys) lepoint = Some lesubs' \<and> lesubs' \<subseteq>\<^sub>m subs'"
      using Cons rest le_lepoint by auto
    from this obtain lesubs' where 
        comp_lesubs': "raw_match' (Ty a xs) (Ty b ys) lepoint = Some lesubs'" 
        and le_lesubs': "lesubs' \<subseteq>\<^sub>m subs'"
      by auto

    show ?case using Cons.prems Cons.hyps comp_lepoint comp_lesubs' le_lesubs' by auto
  qed
qed (auto split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv) 

lemma map_le_same_dom_imp_same_map: "dom f = dom g \<Longrightarrow> map_le f g \<Longrightarrow> f = g"
  by (simp add: map_le_antisym map_le_def)

corollary map_le_produces_same_raw_match':
  assumes "raw_match' T U subs = Some subs'"
  assumes "dom subs \<subseteq> tvsT T"
  assumes "map_le lesubs subs"
  shows "raw_match' T U lesubs = Some subs'"
proof-
  have "dom subs' = tvsT T"
    using assms(1) assms(2) raw_match'_dom_res_eq_tvsT by auto
  moreover obtain lesubs' where "raw_match' T U lesubs = Some lesubs'" "map_le lesubs' subs'"
    using raw_match'_imp_raw_match'_on_map_le assms(1) assms(3) by blast
  moreover hence "dom lesubs' = tvsT T"
    using \<open>dom subs' = tvsT T\<close> map_le_implies_dom_le raw_match'_tvsT_subset_dom_res by fastforce

  ultimately show ?thesis using map_le_same_dom_imp_same_map by metis
qed

corollary "raw_match' T U subs = Some subs' \<Longrightarrow> dom subs \<subseteq> tvsT T \<Longrightarrow>
  raw_match' T U (\<lambda>p . None) = Some subs'"
  using map_le_empty map_le_produces_same_raw_match' by blast

lemma raw_match'_restriction:
  assumes "raw_match' T U subs = Some subs'"
  assumes " tvsT T \<subseteq> restriction "
  shows "raw_match' T U (subs|`restriction) = Some (subs'|`restriction)"
using assms proof (induction T U subs arbitrary: restriction subs' rule: raw_match'.induct)
  case (1 v S T subs)
  then show ?case
    apply simp
    by (smt fun_upd_restrict_conv option.case_eq_if option.discI option.sel restrict_fun_upd)
next
  case (2 a Ts b Us subs)
  hence l: "length Ts = length Us" "a=b" by (simp_all split: if_splits)
  from this 2 have better_IH: 
    "(x, y) \<in> set (zip Ts Us) \<Longrightarrow> raw_match' x y subs = Some subs' \<Longrightarrow> tvsT x \<subseteq> restriction
    \<Longrightarrow> raw_match' x y (subs |` restriction) = Some (subs' |` restriction)"
    for x y subs restriction subs' by simp
  from l better_IH show ?case using 2
  proof(induction Ts Us arbitrary: subs subs' rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)
    obtain point where first: "raw_match' x y subs = Some point"
      and rest: "raw_match' (Ty a xs) (Ty b ys) point = Some subs'"
      by (metis (no_types, lifting) Cons.hyps Cons.prems(4) fold_matches_first_step_not_None l(2) 
          length_Cons raw_match'.simps(2))

    have "raw_match' x y (subs |` restriction) 
      = Some (point |` restriction)"
      using Cons first by simp

    moreover have "raw_match' (Ty a xs) (Ty b ys) (point |` restriction) 
      = Some (subs' |` restriction)"
      using Cons rest by simp

     ultimately show ?case by (simp split: if_splits)        
  qed
qed (auto split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv)


corollary raw_match'_restriction_on_tvsT:
  assumes "raw_match' T U subs = Some subs'"
  shows "raw_match' T U (subs|`tvsT T) = Some (subs'|`tvsT T)"
  using raw_match'_restriction assms by simp

lemma tinstT_imp_ex_raw_match':
  assumes "tinstT T1 T2" 
  shows "\<exists>subs. raw_match' T2 T1 (\<lambda>p . None) = Some subs"
proof-
  obtain \<rho> where "tsubstT T2 \<rho> = T1" using assms tinstT_def by auto
  hence "raw_match' T2 T1 (\<lambda>(idx, S). Some (\<rho> idx S)) = Some (\<lambda>(idx, S). Some (\<rho> idx S))" 
    using tsubstT_matcher_imp_raw_match'_unchanged by auto
  
  hence "raw_match' T2 T1 ((\<lambda>(idx, S). Some (\<rho> idx S))|`tvsT T2) 
    = Some ((\<lambda>(idx, S). Some (\<rho> idx S))|`tvsT T2)" 
    using raw_match'_restriction_on_tvsT by simp
  moreover have "dom ((\<lambda>(idx, S). Some (\<rho> idx S))|`tvsT T2) = tvsT T2" by auto
  ultimately show ?thesis using map_le_produces_same_raw_match'
    using map_le_empty by blast
qed

lemma ex_raw_match'_imp_tinstT:
  assumes "\<exists>subs. raw_match' T2 T1 (\<lambda>p . None) = Some subs"
  shows "tinstT T1 T2"
proof-
  obtain subs where "raw_match' T2 T1 (\<lambda>p . None) = Some subs" 
    using assms by auto
  hence "tsubstT T2 (convert_subs subs) = T1"
    using raw_match'_produces_matcher by blast
  thus ?thesis unfolding tinstT_def by fast
qed

corollary tinstT_iff_ex_raw_match': 
  "tinstT T1 T2 \<longleftrightarrow> (\<exists>subs. raw_match' T2 T1 (\<lambda>p . None) = Some subs)"
  using ex_raw_match'_imp_tinstT tinstT_imp_ex_raw_match' by blast

function (sequential) raw_match_term 
  :: "term \<Rightarrow> term \<Rightarrow> ((variable \<times> sort) \<rightharpoonup> typ) \<Rightarrow> ((variable \<times> sort) \<rightharpoonup> typ) option"
  where
  "raw_match_term (Ct a T) (Ct b U) subs = (if a = b then raw_match' T U subs else None)"
| "raw_match_term (Fv a T) (Fv b U) subs = (if a = b then raw_match' T U subs else None)"
| "raw_match_term (Bv i) (Bv j) subs = (if i = j then Some subs else None)"
| "raw_match_term (Abs T t) (Abs U u) subs = 
    Option.bind (raw_match' T U subs) (raw_match_term t u)"
| "raw_match_term (f $ u) (f' $ u') subs = Option.bind (raw_match_term f f' subs) (raw_match_term u u')"
| "raw_match_term _ _ _ = None"
  by pat_completeness auto
termination by size_change

lemma raw_match_term_map_le: "raw_match_term t u subs = Some subs' \<Longrightarrow> map_le subs subs'"
  by (induction t u subs arbitrary: subs' rule: raw_match_term.induct)
    (auto split: if_splits prod.splits intro: map_le_trans raw_match'_map_le simp add: bind_eq_Some_conv)

lemma raw_match_term_tvs_subset_dom_res:
  "raw_match_term t u subs = Some subs' \<Longrightarrow> tvs t \<subseteq> dom subs'"
proof (induction t u subs arbitrary: subs' rule: raw_match_term.induct)
  case (4 T t U u subs)
  from this obtain bsubs where bsubs: "raw_match' T U subs = Some bsubs"
    by (auto simp add: bind_eq_Some_conv raw_match'_produces_matcher)
  moreover hence body: "raw_match_term t u bsubs = Some subs'"
    using "4.prems" by (auto simp add: bind_eq_Some_conv raw_match'_produces_matcher)
  
  ultimately have 1: "tvs t \<subseteq> dom subs'"
    using 4 by fastforce

  from bsubs have "tvsT T \<subseteq> dom bsubs" 
    using raw_match'_tvsT_subset_dom_res by auto

  moreover have "bsubs \<subseteq>\<^sub>m subs'" using raw_match_term_map_le body by blast

  ultimately have 2: "tvsT T \<subseteq> dom subs'"
    using map_le_implies_dom_le by blast
  then show ?case
    using "4.prems" 1 2 by (simp split: if_splits)
next
  case (5 f u f' u' subs)
  from this obtain fsubs where f: "raw_match_term f f' subs = Some fsubs"
    by (auto simp add: bind_eq_Some_conv)
  hence u: "raw_match_term u u' fsubs = Some subs'"
    using "5.prems" by auto

  have 1: "tvs u \<subseteq> dom subs'"
    using f u "5.IH" by auto

  have "tvs f \<subseteq> dom fsubs"
    using 5 f by simp
  moreover have "fsubs \<subseteq>\<^sub>m subs'" using raw_match_term_map_le u by blast
  ultimately have 2: "tvs f \<subseteq> dom subs'"
    using map_le_implies_dom_le by blast

  then show ?case using 1 by simp
qed (use raw_match'_tvsT_subset_dom_res in \<open>auto split: option.splits if_splits prod.splits\<close>) 


lemma raw_match_term_dom_res_subset_tvs: 
  "raw_match_term t u subs = Some subs' \<Longrightarrow> dom subs' \<subseteq> tvs t \<union> dom subs"
proof (induction t u subs arbitrary: subs' rule: raw_match_term.induct)
  case (4 T t U u subs)
  from this obtain bsubs where bsubs: "raw_match' T U subs = Some bsubs"
    by (auto simp add: bind_eq_Some_conv raw_match'_produces_matcher)
  moreover hence body: "raw_match_term t u bsubs = Some subs'"
    using "4.prems" by (auto simp add: bind_eq_Some_conv raw_match'_produces_matcher)
  
  ultimately have 1: "dom subs' \<subseteq> tvs t \<union> dom bsubs"
    using 4 by fastforce

  from bsubs have "dom bsubs \<subseteq> tvsT T \<union> dom bsubs" 
    using raw_match'_dom_res_subset_tvsT by auto

  moreover have "subs \<subseteq>\<^sub>m bsubs" using bsubs raw_match'_map_le by blast

  ultimately have 2: "dom bsubs \<subseteq> tvsT T \<union> dom subs" 
    using bsubs raw_match'_dom_res_subset_tvsT by auto
  then show ?case
    using "4.prems" 1 2 by (auto split: if_splits) 
next
  case (5 f u f' u' subs)
  from this obtain fsubs where f: "raw_match_term f f' subs = Some fsubs"
    by (auto simp add: bind_eq_Some_conv)
  hence u: "raw_match_term u u' fsubs = Some subs'"
    using "5.prems" by auto

  have 1: "dom fsubs \<subseteq> tvs f \<union> dom subs"
    using 5 f u by simp

  have "dom subs' \<subseteq> tvs u \<union> dom fsubs"
    using 5 f by simp
  moreover have "fsubs \<subseteq>\<^sub>m subs'" using raw_match_term_map_le u by blast
  ultimately have 2: "dom subs' \<subseteq> tvs f \<union> tvs u \<union> dom subs"
    by (smt "1" Un_commute inf_sup_aci(6) subset_Un_eq)
  then show ?case using 1 by simp
qed (use raw_match'_dom_res_subset_tvsT in \<open>auto split: option.splits if_splits prod.splits\<close>) 

corollary raw_match_term_dom_res_eq_tvs: 
  "raw_match_term t u subs = Some subs' \<Longrightarrow> dom subs' = tvs t \<union> dom subs"
  by (simp add: map_le_implies_dom_le raw_match_term_tvs_subset_dom_res 
      raw_match_term_dom_res_subset_tvs raw_match_term_map_le subset_antisym)

lemma raw_match_term_extend_map_preserve:
  "raw_match_term t u subs = Some subs' \<Longrightarrow> map_le subs' subs'' \<Longrightarrow> p\<in>tvs t \<Longrightarrow> subs'' p = subs' p" 
  using raw_match_term_dom_res_eq_tvs domIff map_le_implies_dom_le 
  by (simp add: map_le_def)

lemma map_eq_on_tvs_imp_map_eq_on_term:
  "(\<And>p . p\<in>tvs t \<Longrightarrow> subs p = subs' p) 
  \<Longrightarrow> tsubst t (convert_subs subs)
    = tsubst t (convert_subs subs')"
  by (induction t) (use map_eq_on_tvsT_imp_map_eq_on_typ in \<open>fastforce+\<close>)

lemma raw_match_extend_map_preserve':
  assumes "raw_match_term t u subs = Some subs'" "map_le subs' subs''"
  shows "tsubst t (convert_subs subs') 
    = tsubst t (convert_subs subs'')"
  apply (rule map_eq_on_tvs_imp_map_eq_on_term)
  using raw_match_term_extend_map_preserve assms by fastforce

lemma raw_match_term_produces_matcher:
  "raw_match_term t u subs = Some subs' 
    \<Longrightarrow> tsubst t (convert_subs subs') = u"
proof (induction t u subs arbitrary: subs' rule: raw_match_term.induct)
  case (4 T t U u subs)
  from this obtain bsubs where bsubs: "raw_match' T U subs = Some bsubs"
    by (auto simp add: bind_eq_Some_conv raw_match'_produces_matcher)
  moreover hence body: "raw_match_term t u bsubs = Some subs'"
    using "4.prems" by (auto simp add: bind_eq_Some_conv raw_match'_produces_matcher)
  
  ultimately have 1: "tsubst t (convert_subs subs') = u"
    using 4 by fastforce

  from bsubs have "tsubstT T (convert_subs bsubs) = U"
    using raw_match'_produces_matcher by blast

  moreover have "bsubs \<subseteq>\<^sub>m subs'" using raw_match_term_map_le body by blast

  ultimately have 2: "tsubstT T (convert_subs subs') = U"
    using raw_match'_extend_map_preserve'[OF bsubs, of subs'] by simp

  then show ?case
    using "4.prems" 1 2 by (simp split: if_splits)
next
  case (5 f u f' u' subs)
  from this obtain fsubs where f: "raw_match_term f f' subs = Some fsubs"
    by (auto simp add: bind_eq_Some_conv)
  hence u: "raw_match_term u u' fsubs = Some subs'"
    using "5.prems" by auto

  have 1: "tsubst u (convert_subs subs') = u'"
    using f u "5.IH" by auto

  have "tsubst f (convert_subs fsubs) = f'"
    using 5 f by simp
  moreover have "fsubs \<subseteq>\<^sub>m subs'" using raw_match_term_map_le u by blast
  ultimately have 2: "tsubst f (convert_subs subs') = f'"
    using raw_match_extend_map_preserve'[OF f, of subs'] by simp

  then show ?case using raw_match'_extend_map_preserve' 1 by auto
qed (auto split: if_splits simp add: bind_eq_Some_conv raw_match'_produces_matcher)

lemma ex_raw_match_term_imp_tinst:
  assumes "\<exists>subs. raw_match_term t2 t1 (\<lambda>p . None) = Some subs"
  shows "tinst t1 t2"
proof-
  obtain subs where "raw_match_term t2 t1 (\<lambda>p . None) = Some subs" 
    using assms by auto
  hence "tsubst t2 (convert_subs subs) = t1"
    using raw_match_term_produces_matcher by blast
  thus ?thesis unfolding tinst_def by fast
qed

lemma tsubst_matcher_imp_raw_match_term_unchanged:
  "tsubst t \<rho> = u \<Longrightarrow> raw_match_term t u (\<lambda>(idx, S). Some (\<rho> idx S)) = Some (\<lambda>(idx, S). Some (\<rho> idx S))"
  by (induction t arbitrary: u \<rho>) (auto simp add: tsubstT_matcher_imp_raw_match'_unchanged)

lemma raw_match_term_restriction:
  assumes "raw_match_term t u subs = Some subs'"
  assumes "tvs t \<subseteq> restriction "
  shows "raw_match_term t u (subs|`restriction) = Some (subs'|`restriction)"
  using assms by (induction t u subs arbitrary: restriction subs' rule: raw_match_term.induct)
    (use raw_match'_restriction in 
    \<open>auto split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv\<close>)

corollary raw_match_term_restriction_on_tvs:
  assumes "raw_match_term t u subs = Some subs'"
  shows "raw_match_term t u (subs|`tvs t) = Some (subs'|`tvs t)"
  using raw_match_term_restriction assms by simp

lemma raw_match_term_imp_raw_match_term_on_map_le:
  assumes "raw_match_term t u subs = Some subs'"
  assumes "map_le lesubs subs"
  shows "\<exists>lesubs'. raw_match_term t u lesubs = Some lesubs' \<and> map_le lesubs' subs'"
using assms proof (induction t u subs arbitrary: lesubs subs' rule: raw_match_term.induct)
  case (4 T t U u subs)
  from this obtain bsubs where bsubs: "raw_match' T U subs = Some bsubs"
    by (auto simp add: bind_eq_Some_conv raw_match'_produces_matcher)
  hence body: "raw_match_term t u bsubs = Some subs'"
    using "4.prems" by (auto simp add: bind_eq_Some_conv raw_match'_produces_matcher)

  from bsubs 4 obtain lebsubs where 
    lebsubs: "raw_match' T U subs = Some lebsubs" "map_le lebsubs bsubs"
    using raw_match'_map_le map_le_trans
    by (fastforce split: if_splits simp add: bind_eq_Some_conv raw_match'_produces_matcher)
  from this obtain lesubs' where 
    lesubs':"raw_match_term t u lebsubs = Some lesubs'" "map_le lesubs' subs'"
    using "4.prems" 
    by (auto split: if_splits simp add: bind_eq_Some_conv raw_match'_produces_matcher)

  show ?case
    using lebsubs lesubs' 4 apply ( auto split: if_splits simp add: bind_eq_Some_conv)
    by (meson raw_match'_imp_raw_match'_on_map_le)
next
  case (5 f u f' u' subs)
    from this obtain fsubs where f: "raw_match_term f f' subs = Some fsubs"
      by (auto simp add: bind_eq_Some_conv)
    hence u: "raw_match_term u u' fsubs = Some subs'"
      using "5.prems" by auto
  
   from 5 obtain lefsubs where 
    lefsubs: "raw_match_term f f' subs = Some lefsubs" "map_le lefsubs fsubs"
    using raw_match_term_map_le map_le_trans f by auto
  from this obtain lesubs' where 
    lesubs':"raw_match_term u u' lefsubs = Some lesubs'" "map_le lesubs' subs'"
    using "5.prems" 
    by (auto split: if_splits simp add: bind_eq_Some_conv raw_match'_produces_matcher)

  from lefsubs lesubs' show ?case using 5 by (fastforce split: if_splits simp add: bind_eq_Some_conv)
qed (use raw_match'_imp_raw_match'_on_map_le in 
    \<open>auto split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv\<close>)

corollary map_le_produces_same_raw_match_term:
  assumes "raw_match_term t u subs = Some subs'"
  assumes "dom subs \<subseteq> tvs t"
  assumes "map_le lesubs subs"
  shows "raw_match_term t u lesubs = Some subs'"
proof-
  have "dom subs' = tvs t"
    using assms(1) assms(2) raw_match_term_dom_res_eq_tvs by auto
  moreover obtain lesubs' where "raw_match_term t u lesubs = Some lesubs'" "map_le lesubs' subs'"
    using raw_match_term_imp_raw_match_term_on_map_le assms(1) assms(3) by blast
  moreover hence "dom lesubs' = tvs t"
    using \<open>dom subs' = tvs t\<close> map_le_implies_dom_le raw_match_term_tvs_subset_dom_res by fastforce

  ultimately show ?thesis using map_le_same_dom_imp_same_map by metis
qed

lemma tinst_imp_ex_raw_match_term:
  assumes "tinst t1 t2" 
  shows "\<exists>subs. raw_match_term t2 t1 (\<lambda>p . None) = Some subs"
proof-
  obtain \<rho> where "tsubst t2 \<rho> = t1" using assms tinst_def by auto
  hence "raw_match_term t2 t1 (\<lambda>(idx, S). Some (\<rho> idx S)) = Some (\<lambda>(idx, S). Some (\<rho> idx S))" 
    using tsubst_matcher_imp_raw_match_term_unchanged by auto
  
  hence "raw_match_term t2 t1 ((\<lambda>(idx, S). Some (\<rho> idx S))|`tvs t2) 
    = Some ((\<lambda>(idx, S). Some (\<rho> idx S))|`tvs t2)" 
    using raw_match_term_restriction_on_tvs by simp
  moreover have "dom ((\<lambda>(idx, S). Some (\<rho> idx S))|`tvs t2) = tvs t2" by auto
  ultimately show ?thesis using map_le_produces_same_raw_match_term
    using map_le_empty by blast
qed

corollary tinst_iff_ex_raw_match_term: 
  "tinst t1 t2 \<longleftrightarrow> (\<exists>subs. raw_match_term t2 t1 (\<lambda>p . None) = Some subs)"
  using ex_raw_match_term_imp_tinst tinst_imp_ex_raw_match_term by blast

(* Now transfer to assoc lists for executability *)

function (sequential) assoc_match
  :: "typ \<Rightarrow> typ \<Rightarrow> ((variable \<times> sort) \<times> typ) list \<Rightarrow> ((variable \<times> sort) \<times> typ) list option" where
  "assoc_match (Tv v S) T subs =
    (case lookup (\<lambda>x. x=(v,S)) subs of
      None \<Rightarrow> Some (((v,S), T) # subs)
    | Some U \<Rightarrow> (if U = T then Some subs else None))"
| "assoc_match (Ty a Ts) (Ty b Us) subs =
    (if a=b \<and> length Ts = length Us 
      then fold (\<lambda>(T, U) subs . Option.bind subs (assoc_match T U)) (zip Ts Us) (Some subs)
      else None)"
| "assoc_match T U subs = (if T = U then Some subs else None)"
  by (pat_completeness) auto
termination proof (relation "measure (\<lambda>(T, U, subs) . size T + size U)", goal_cases)
  case 1
  then show ?case 
    by auto
next
  case (2 a Ts b Us subs x xa y xb aa)
  hence "length Ts = length Us" "a=b"
    by auto
  from this 2(2-) show ?case 
    by (induction Ts Us rule: list_induct2) auto
qed

corollary assoc_match_Type_conds:
  assumes "assoc_match (Ty a Ts) (Ty b Us) subs = Some subs'"
  shows "a=b" "length Ts = length Us"
  using assms by (auto split: if_splits)

lemma fold_assoc_matches_first_step_not_None:
  assumes
    "fold (\<lambda>(T, U) subs . Option.bind subs (assoc_match T U)) (zip (x#xs) (y#ys)) (Some subs) = Some subs'" 
  obtains point where
    "assoc_match x y subs = Some point"
    "fold (\<lambda>(T, U) subs . Option.bind subs (assoc_match T U)) (zip (xs) (ys)) (Some point) = Some subs'"
  using assms apply (simp split: option.splits)
  by (metis fold_Option_bind_eq_Some_start_not_None' not_None_eq)

lemma assoc_match_subset: "assoc_match T U subs = Some subs' \<Longrightarrow> set subs \<subseteq> set subs'"
proof (induction T U subs arbitrary: subs' rule: assoc_match.induct)
  case (2 a Ts b Us subs)
  hence l: "length Ts = length Us" "a = b" by (simp_all split: if_splits)
  have better_IH: "(x, y) \<in> set (zip Ts Us) \<Longrightarrow> 
    assoc_match x y subs = Some subs' \<Longrightarrow> set subs \<subseteq> set subs'"
    for x y subs subs' using 2 by (simp split: if_splits)
  from l better_IH "2.prems" show ?case 
  proof (induction Ts Us arbitrary: subs rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)

    obtain point where first: "assoc_match x y subs = Some point"
      and rest: "assoc_match (Ty a xs) (Ty b ys) point = Some subs'"
      using fold_assoc_matches_first_step_not_None
      by (metis (no_types, lifting) Cons.hyps Cons.prems assoc_match.simps(2) assoc_match_Type_conds(2))

    then show ?case 
      using Cons.IH Cons.prems(2) by (fastforce split: option.splits prod.splits if_splits 
          simp add: lookup_present_eq_key bind_eq_Some_conv)
  qed
qed (auto split: option.splits prod.splits if_splits simp add: lookup_present_eq_key)

lemma assoc_match_distinct: "assoc_match T U subs = Some subs' \<Longrightarrow> distinct (map fst subs) 
  \<Longrightarrow> distinct (map fst subs')"
proof (induction T U subs arbitrary: subs' rule: assoc_match.induct)
  case (2 a Ts b Us subs)
  hence l: "length Ts = length Us" "a = b" by (simp_all split: if_splits)
  have better_IH: "(x, y) \<in> set (zip Ts Us) \<Longrightarrow> 
    assoc_match x y subs = Some subs' \<Longrightarrow> distinct (map fst subs) \<Longrightarrow> distinct (map fst subs')"
    for x y subs subs' using 2 by (simp split: if_splits)
  from l better_IH "2.prems" show ?case 
  proof (induction Ts Us arbitrary: subs subs' rule: list_induct2)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs y ys)

    obtain point where first: "assoc_match x y subs = Some point"
      and rest: "assoc_match (Ty a xs) (Ty b ys) point = Some subs'"
      using fold_assoc_matches_first_step_not_None
      by (metis (no_types, lifting) Cons.hyps Cons.prems assoc_match.simps(2) assoc_match_Type_conds(2))

    have dst_point: "distinct (map fst point)"
      apply (rule Cons.prems)
      using first Cons.prems by simp_all
      
    have "distinct (map fst subs')"
      apply (rule Cons.IH)
      using Cons.prems rest apply simp
      using Cons.prems apply auto[1]
      using rest apply simp
      using dst_point apply simp
      done

    then show ?case 
      using Cons.IH Cons.prems(2) by simp
  qed
qed (auto split: option.splits prod.splits if_splits simp add: lookup_present_eq_key)


(* Seems that distinct is not even necessary, as both take the first one in case of duplicates*)
lemma lookup_eq_map_of_ap:                           
  shows "lookup (\<lambda>x. x=k) subs = map_of subs k"
  by (induction subs arbitrary: k) auto

(* Ugly proof, but should mean that I can replace raw_match' with the executable assoc_match *)
lemma raw_match'_assoc_match:
  shows "raw_match' T U (map_of subs) = map_option map_of (assoc_match T U subs)"
  proof (induction T U "map_of subs" arbitrary: subs rule: raw_match'.induct)
case (1 v S T)
  then show ?case 
    by (auto split: option.splits prod.splits simp add: lookup_present_eq_key lookup_eq_map_of_ap)
next
  case (2 a Ts b Us subs)
  then show ?case
  proof(cases "(raw_match' (Ty a Ts) (Ty b Us) (map_of subs))")
    case None
    then show ?thesis
    proof (cases "a = b \<and> length Ts = length Us")
      case True
      hence "length Ts = length Us" "a = b" by auto
      then show ?thesis using 2 None 
      proof (induction Ts Us arbitrary: subs rule: list_induct2)
        case Nil
        then show ?case by simp
      next
        case (Cons x xs y ys)

        hence eq_hd: "raw_match' x y (map_of subs) = map_option map_of (assoc_match x y subs)"
          by auto

        then show ?case
        proof(cases "assoc_match x y subs")
          case None
          hence "raw_match' x y (map_of subs) = None" using eq_hd by simp
          then show ?thesis 
            using fold_Option_bind_at_some_point_None_eq_None fold_assoc_matches_first_step_not_None
              Cons.prems 
            by (auto split: option.splits prod.splits if_splits 
                simp add: fold_Option_bind_eq_None_start_None)
        next
          case (Some res)
          hence "raw_match' x y (map_of subs) = Some (map_of res)" using eq_hd by simp
          then show ?thesis 
            using fold_assoc_matches_first_step_not_None fold_Option_bind_eq_Some_at_each_point_Some
              Cons.prems Cons.IH
            by (auto split: option.splits prod.splits if_splits 
                simp add: fold_Option_bind_eq_None_start_None)
        qed
      qed
    next
      case False
      then show ?thesis using None 2 by auto
    qed
  next
    case (Some res)
    hence l: "length Ts = length Us" "a = b" by (simp_all split: if_splits)
    have better_IH: "(x, y) \<in> set (zip Ts Us) \<Longrightarrow>
    raw_match' x y (map_of subs) = map_option map_of (assoc_match x y subs)"
      for x y subs using 2 Some by (simp split: if_splits)
    from l better_IH Some "2.prems" show ?thesis 
    proof (induction Ts Us arbitrary: subs res rule: list_induct2)
      case Nil
      then show ?case by simp
    next
      case (Cons x xs y ys)

      obtain point where first: "raw_match' x y (map_of subs) = Some (map_of point)"
        and rest: "raw_match' (Ty a xs) (Ty b ys) (map_of point) = Some res"
        using fold_matches_first_step_not_None Cons.prems
        by (simp split: option.splits prod.splits if_splits) (smt map_option_eq_Some)

      have 1: "raw_match' x y (map_of subs) = map_option map_of (assoc_match x y subs)"
        using Cons.prems by simp

      have 2: "raw_match' (Ty a xs) (Ty b ys) (map_of point)
        = map_option map_of (assoc_match (Ty a xs) (Ty b ys) point)"
        using Cons rest by auto

      show ?case 
        using 1 2 first rest
        apply (simp split: if_splits option.splits prod.splits)
        by (smt Cons.IH Cons.prems(2) assoc_match.simps(2) list.set_intros(2) map_option_eq_Some 
            rest zip_Cons_Cons)
    qed
  qed
qed (auto split: option.splits prod.splits simp add: lookup_present_eq_key)

lemma dom_eq_and_eq_on_dom_imp_eq: "dom m = dom m' \<Longrightarrow> \<forall>x\<in>dom m . m x = m' x \<Longrightarrow> m = m'"
  by (simp add: map_le_def map_le_same_dom_imp_same_map)

lemma list_of_map:
  assumes "finite (dom subs)" 
  shows "\<exists>l. map_of l = subs"
proof-
  have "finite {(k, the (subs k)) | k . k\<in>dom subs}" using assms by simp
  from this obtain l where l: "set l = {(k, the (subs k)) | k . k\<in>dom subs}" 
    using finite_list by fastforce

  hence "dom (map_of l) = fst ` {(k, the (subs k)) | k . k\<in>dom subs}"
    by (simp add: dom_map_of_conv_image_fst)
  also have "\<dots> = dom subs"
    by (simp add: Setcompr_eq_image domI image_image)
  finally have "dom (map_of l) = dom subs" .
  moreover have "map_of l x = subs x" if "x\<in>dom subs" for x 
    using that
    by (smt l domIff fst_conv map_of_SomeD mem_Collect_eq option.collapse prod.sel(2) weak_map_of_SomeI)
  ultimately have "map_of l = subs" 
    by (simp add: dom_eq_and_eq_on_dom_imp_eq)
  thus ?thesis ..
qed

corollary tinstT_iff_assoc_match[code]: "tinstT T1 T2 \<longleftrightarrow> assoc_match T2 T1 [] ~= None" 
  using tinstT_iff_ex_raw_match' list_of_map raw_match'_assoc_match
  by (smt map_of_eq_empty_iff map_option_is_None option.collapse option.distinct(1))

function (sequential) assoc_match_term 
  :: "term \<Rightarrow> term \<Rightarrow> ((variable \<times> sort) \<times> typ) list \<Rightarrow> ((variable \<times> sort) \<times> typ) list option"
  where
  "assoc_match_term (Ct a T) (Ct b U) subs = (if a = b then assoc_match T U subs else None)"
| "assoc_match_term (Fv a T) (Fv b U) subs = (if a = b then assoc_match T U subs else None)"
| "assoc_match_term (Bv i) (Bv j) subs = (if i = j then Some subs else None)"
| "assoc_match_term (Abs T t) (Abs U u) subs = 
    Option.bind (assoc_match T U subs) (assoc_match_term t u)"
| "assoc_match_term (f $ u) (f' $ u') subs = Option.bind (assoc_match_term f f' subs) (assoc_match_term u u')"
| "assoc_match_term _ _ _ = None"
  by pat_completeness auto
termination by size_change

lemma raw_match_term_assoc_match_term:
  "raw_match_term t u (map_of subs) = map_option map_of (assoc_match_term t u subs)"
proof (induction t u "map_of subs" arbitrary: subs rule: raw_match_term.induct)
  case (4 T t U u)

  then show ?case
  proof (cases "assoc_match T U subs")
    case None
    then show ?thesis using raw_match'_assoc_match by simp
  next
    case (Some bsubs)
    hence 1: "raw_match' T U (map_of subs) = Some (map_of bsubs)"
      using raw_match'_assoc_match by simp
    hence "raw_match_term t u (map_of bsubs) = map_option map_of (assoc_match_term t u bsubs)"
      using 4 by blast
    then show ?thesis by (simp add: Some 1)
  qed
next
  case (5 f u f' u')
  (* Do a real proof here when time *)
  from "5.hyps"(1) "5.hyps"(2) have "Option.bind (map_option map_of (assoc_match_term f f' subs))
     (raw_match_term u u') =
    map_option map_of (Option.bind (assoc_match_term f f' subs) (assoc_match_term u u'))"
    by (smt None_eq_map_option_iff bind.bind_lunit bind_eq_None_conv option.collapse option.map_sel)
  with 5 show ?case 
    using raw_match'_assoc_match 5 
    by (auto split: option.splits prod.splits simp add: lookup_present_eq_key bind_eq_Some_conv bind_eq_None_conv)
qed (use raw_match'_assoc_match in \<open>auto split: option.splits prod.splits\<close>)

(* Automation surprisingly broke on translation :( *)
corollary tinst_iff_assoc_match_term[code]: "tinst t1 t2 \<longleftrightarrow> assoc_match_term t2 t1 [] \<noteq> None" 
proof
  assume "tinst t1 t2"
  from this obtain asubs where "raw_match_term t2 t1 Map.empty = Some asubs"
    using tinst_imp_ex_raw_match_term by blast
  from this obtain csubs where "assoc_match_term t2 t1 [] = Some csubs"
    by (metis empty_eq_map_of_iff map_option_eq_Some raw_match_term_assoc_match_term)
  thus "assoc_match_term t2 t1 [] \<noteq> None" by simp
next
  assume "assoc_match_term t2 t1 [] \<noteq> None" 
  from this obtain csubs where "assoc_match_term t2 t1 [] = Some csubs"
    by blast
  from this obtain asubs where "raw_match_term t2 t1 Map.empty = Some asubs"
    by (metis empty_eq_map_of_iff option.simps(9) raw_match_term_assoc_match_term)
  thus "tinst t1 t2" 
    using tinst_iff_ex_raw_match_term by blast
qed

hide_fact fold_matches_first_step_not_None fold_matches_last_step_not_None

end