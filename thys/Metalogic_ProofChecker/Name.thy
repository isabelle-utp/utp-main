(*
  Generation of fresh names
*)

section "Names"

theory Name
  imports Preliminaries Term
    "HOL-Library.Char_ord"
begin

(* Horrible generator for now(make a string of "a"s that is longer than all strings in the set),
   make something better later 
   Needs list nature of strings, so not directly on literals
*)
fun fresh_name :: "string set \<Rightarrow> string" where
  "fresh_name S = (if S=empty then ''a'' else replicate (Max (length ` S) + 1) (CHR ''a''))"

lemma fresh_name_fresh:
  assumes "finite S"
  shows "fresh_name S \<notin> S"
proof(cases "S=empty")
  case True
  then show ?thesis by simp
next
  case False
  hence "length (fresh_name S) > (Max (image length S))" by auto
  hence "\<forall>s\<in>S. length (fresh_name S) > length s" using assms by (simp add: le_imp_less_Suc)
  thus "fresh_name S \<notin> S" by blast
qed

(* Lift this generator to literals *)
context
  includes "String.literal.lifting"
begin
lift_definition fresh_name' :: "String.literal set \<Rightarrow> String.literal" is "fresh_name"
  by (auto split: if_splits)


lemma [code]: "fresh_name' S = String.implode (fresh_name (String.explode ` S))"
  by (metis String.implode_explode_eq fresh_name'.rep_eq)

lemma fresh_name'_fresh:
  assumes "finite S"
  shows "fresh_name' S \<notin> S"
  by (metis assms finite_imageI fresh_name'.rep_eq fresh_name_fresh rev_image_eqI)
end

fun variant_name :: "name \<Rightarrow> name set \<Rightarrow> (name \<times> name set)" where
  "variant_name s S = (let s' = (fresh_name' S) in (s', insert s' S))"

lemma variant_name_fresh:
  assumes "finite S"
  shows "fst (variant_name s S) \<notin> S"
  using assms fresh_name'_fresh
  by (metis fst_conv variant_name.simps)

lemma variant_name_adds:
  shows "snd (variant_name s S) = insert (fst (variant_name s S)) S"
  by (metis fst_conv snd_conv variant_name.simps)

(* This is a hack to transfer result to variables, better to write generator directly *)
fun name :: "variable \<Rightarrow> name" where
  "name (variable.Free n) = n"
| "name (Var (n,_)) = n"

(* And for variables *)
fun variant_variable :: "variable \<Rightarrow> variable set \<Rightarrow> (variable \<times> variable set)" where 
  "variant_variable (variable.Free n) S = (let s' = fresh_name' (name ` S) in 
    (Free s', insert (variable.Free s') S))"
| "variant_variable (Var (n,_)) S = (let s' = fresh_name' (name ` S) in 
    (Var (s',0), insert (Var (s',0)) S))"


lemma variant_variable_fresh:
  assumes "finite S"
  shows "fst (variant_variable s S) \<notin> S"
  apply (cases s)
  using assms fresh_name'_fresh
  apply (metis finite_imageI fstI name.simps(1) rev_image_eqI variant_variable.simps(1))
  using assms fresh_name'_fresh 
  by (metis (no_types, hide_lams) finite_imageI fst_conv image_iff name.simps(2) surj_pair variant_variable.simps(2))

lemma variant_variable_adds:
  shows "snd (variant_variable s S) = insert (fst (variant_variable s S)) S"
  by (metis (no_types, lifting) fst_conv snd_conv variant_variable.elims)

(* Even worse generator for fresh variable names to allow transforming parallel to sequential substitutions 
  Applied hack for variables here too
*)

fun variant_variables :: "nat \<Rightarrow> variable \<Rightarrow> variable set \<Rightarrow> (variable list \<times> variable set)" where
  "variant_variables 0 _ S = ([], S)"
| "variant_variables (Suc n) s S = 
    (let (s', S') = variant_variable s S in 
      (let (ss, S'') = variant_variables n s' S' in
        (s'#ss, S'')))"

lemma variant_names_fresh:
  assumes "finite S"
  shows "\<forall>s \<in> set (fst (variant_variables n s S)) . s \<notin> S"
  using assms proof (induction n arbitrary: s S)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain s' S' where s'S': "variant_variable s S = (s', S')"
    by fastforce
  hence "s' \<notin> S"
    by (metis Suc.prems fst_conv variant_variable_fresh)
  moreover have I: "\<forall>s\<in>set (fst (variant_variables n s' S')). s \<notin> S'"
    by (metis Suc.IH Suc.prems s'S' finite.insertI snd_conv variant_variable_adds)
  moreover have "S \<subseteq> S'"
    by (metis insert_iff s'S' snd_conv subsetI variant_variable_adds)
  ultimately show ?case 
    by (auto simp add: Let_def s'S' split: prod.splits)
qed

lemma variant_names_distinct:
  assumes "finite S"
  shows "distinct (fst (variant_variables n s S))"
  using assms proof (induction n arbitrary: s S)
  case 0
  then show ?case by simp
next
  case (Suc n)
  obtain s' S' where s'S': "variant_variable s S = (s', S')"
    by fastforce
  hence "s' \<notin> S"
    by (metis Suc.prems fst_conv variant_variable_fresh)
  moreover have I: "distinct (fst (variant_variables n s' S'))"
    by (metis Suc.IH Suc.prems s'S' finite.insertI snd_conv variant_variable_adds)
  moreover have "S \<subseteq> S'"
    by (metis insert_iff s'S' snd_conv subsetI variant_variable_adds)
  ultimately show ?case 
    apply (simp add: Let_def s'S' split: prod.splits) 
    by (metis Suc.prems finite.insertI fst_conv insertI1 s'S' snd_conv variant_names_fresh variant_variable_adds)
qed

corollary variant_names_amount:
  assumes "finite S"
  shows "length (fst (variant_variables n s S)) = n" 
  using assms by (induction n arbitrary: s S) (simp_all add: case_prod_beta variant_variable_adds)

(* 
  After translation I also need to make sure fresh vars are not in the context
*)
abbreviation "fresh_rename_ns n B insts G \<equiv> fst (variant_variables n (Free STR ''lol'')
  (fst ` (fv B \<union> (\<Union>t\<in>snd ` set insts . fv t) \<union> (fst ` set insts)) \<union> G))"
abbreviation "fresh_rename_idns n B insts \<equiv> fresh_rename_ns n B insts"

lemma map_Pair_zip_replicate_conv: "map (\<lambda>x. Pair x c) l = zip l (replicate (length l) c)" 
  by (induction l) auto

lemma distinct_fresh_rename_ns: "finite G \<Longrightarrow> distinct (fresh_rename_ns n B insts G)"
  by (metis (no_types, lifting) List.finite_set add_vars'_fv finite_UN finite_Un finite_imageI variant_names_distinct)

lemma fresh_fresh_rename_ns: "finite G \<Longrightarrow> \<forall>nm \<in> set (fresh_rename_ns n B insts G) . 
  nm \<notin> (fst ` (fv B \<union> (\<Union>t \<in> snd ` set insts . (fv t)) \<union> (fst ` set insts)) \<union> G)"
  by (metis (no_types, lifting) List.finite_set add_vars'_fv finite_UN finite_Un finite_imageI variant_names_fresh)
  
lemma length_fresh_rename_ns: "finite G \<Longrightarrow> length (fresh_rename_ns n B insts G) = n"
  by (metis (no_types, lifting) List.finite_set add_vars'_fv finite_UN finite_Un finite_imageI variant_names_amount)

lemma distinct_fresh_rename_idns: "finite G \<Longrightarrow> distinct (fresh_rename_idns n B insts G)"
  using distinct_fresh_rename_ns by (metis)

lemma fresh_fresh_rename_idns: "finite G \<Longrightarrow> \<forall>nm \<in> set (fresh_rename_idns n B insts G) . 
  nm \<notin> (fst ` (fv B \<union> (\<Union>t \<in> snd ` set insts . (fv t)) \<union> (fst ` set insts)) \<union> G)"
  using distinct_fresh_rename_ns map_Pair_zip_replicate_conv map_Pair_zip_replicate_conv
  by (smt fresh_fresh_rename_ns fst_conv imageE image_eqI list.set_map)

lemma length_fresh_rename_idns: "finite G \<Longrightarrow>  length (fresh_rename_idns n B insts G) = n"
  by (metis length_fresh_rename_ns)

end