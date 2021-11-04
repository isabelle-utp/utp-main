theory Result
  imports
    Main
    "HOL-Library.Monad_Syntax"
begin

datatype ('err, 'a) result =
  is_err: Error 'err |
  is_ok: Ok 'a

section \<open>Monadic bind\<close>

context begin

qualified fun bind :: "('a, 'b) result \<Rightarrow> ('b \<Rightarrow> ('a, 'c) result) \<Rightarrow> ('a, 'c) result" where
  "bind (Error x) _ = Error x" |
  "bind (Ok x) f = f x"

end

adhoc_overloading
  bind Result.bind

context begin

qualified lemma bind_Ok[simp]: "x \<bind> Ok = x"
  by (cases x) simp_all

qualified lemma bind_eq_Ok_conv: "(x \<bind> f = Ok z) = (\<exists>y. x = Ok y \<and> f y = Ok z)"
  by (cases x) simp_all

qualified lemmas bind_eq_OkD[dest!] = bind_eq_Ok_conv[THEN iffD1]
qualified lemmas bind_eq_OkE = bind_eq_OkD[THEN exE]
qualified lemmas bind_eq_OkI[intro] = conjI[THEN exI[THEN bind_eq_Ok_conv[THEN iffD2]]]

qualified lemma bind_eq_Error_conv:
  "x \<bind> f = Error z \<longleftrightarrow> x = Error z \<or> (\<exists>y. x = Ok y \<and> f y = Error z)"
  by (cases x) simp_all

qualified lemmas bind_eq_ErrorD[dest!] = bind_eq_Error_conv[THEN iffD1]
qualified lemmas bind_eq_ErrorE = bind_eq_ErrorD[THEN disjE]
qualified lemmas bind_eq_ErrorI =
  disjI1[THEN bind_eq_Error_conv[THEN iffD2]]
  conjI[THEN exI[THEN disjI2[THEN bind_eq_Error_conv[THEN iffD2]]]]

lemma if_then_else_Ok[simp]:
  "(if a then b else Error c) = Ok d \<longleftrightarrow> a \<and> b = Ok d"
  "(if a then Error c else b) = Ok d \<longleftrightarrow> \<not> a \<and> b = Ok d"
  by (cases a) simp_all

qualified lemma if_then_else_Error[simp]:
  "(if a then Ok b else c) = Error d \<longleftrightarrow> \<not> a \<and> c = Error d"
  "(if a then c else Ok b) = Error d \<longleftrightarrow> a \<and> c = Error d"
  by (cases a) simp_all

qualified lemma map_eq_Ok_conv: "map_result f g x = Ok y \<longleftrightarrow> (\<exists>x'. x = Ok x' \<and> y = g x')"
  by (cases x; auto)

qualified lemma map_eq_Error_conv: "map_result f g x = Error y \<longleftrightarrow> (\<exists>x'. x = Error x' \<and> y = f x')"
  by (cases x; auto)

qualified lemmas map_eq_OkD[dest!] = iffD1[OF map_eq_Ok_conv]
qualified lemmas map_eq_ErrorD[dest!] = iffD1[OF map_eq_Error_conv]

end


section \<open>Conversion functions\<close>

context begin

qualified fun of_option where
  "of_option e None = Error e" |
  "of_option e (Some x) = Ok x"

qualified lemma of_option_injective[simp]: "(of_option e x = of_option e y) = (x = y)"
  by (cases x; cases y; simp)

qualified lemma of_option_eq_Ok[simp]: "(of_option x y = Ok z) = (y = Some z)"
  by (cases y) simp_all

qualified fun to_option where
  "to_option (Error _) = None" |
  "to_option (Ok x) = Some x"

qualified lemma to_option_Some[simp]: "(to_option r = Some x) = (r = Ok x)"
  by (cases r) simp_all

qualified fun those :: "('err, 'ok) result list \<Rightarrow> ('err, 'ok list) result" where
  "those [] = Ok []" |
  "those (x # xs) = do {
    y \<leftarrow> x;
    ys \<leftarrow> those xs;
    Ok (y # ys)
  }"

qualified lemma those_Cons_OkD: "those (x # xs) = Ok ys \<Longrightarrow> \<exists>y ys'. ys = y # ys' \<and> x = Ok y \<and> those xs = Ok ys'"
  by auto

end

end