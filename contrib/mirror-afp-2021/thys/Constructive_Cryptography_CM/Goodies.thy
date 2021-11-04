theory Goodies
  imports
    Main
begin

primrec 
  inits :: "'a list \<Rightarrow> 'a list list"
  where
    "inits [] = []"
  | "inits (x # xs) = [x] # map ((#) x) (inits xs)"

definition 
  inits_self :: "'a list \<Rightarrow> ('a list \<times> 'a) list" 
  where
    "inits_self xs = zip ([] # inits xs) xs"

lemma inits_map: "inits (map f xs) = map (map f) (inits xs)"
  by(induction xs) simp_all

lemma inits_append [simp]: "inits (xs @ ys) = inits xs @ map ((@) xs) (inits ys)"
  by(induction xs) (simp_all)

lemma inits_self_simps [simp]:
    "inits_self [] = []"
    "inits_self (x # xs) = ([], x) # map (apfst ((#) x)) (inits_self xs)"
  by(simp_all add: inits_self_def apfst_def map_prod_def zip_map1[symmetric])

lemma inits_self_map: "inits_self (map f xs) = map (map_prod (map f) f) (inits_self xs)"
  by(induction xs) (simp_all add: apfst_def prod.map_comp o_def)

lemma in_set_inits_self: "(ys, z) \<in> set (inits_self xs) \<longleftrightarrow> (\<exists>zs. xs = ys @ z # zs)"
  by(induction xs arbitrary: ys z)(auto simp add: Cons_eq_append_conv apfst_def map_prod_def)

lemma foldl_append: "foldl (\<lambda>s e. s @ [e]) s l = s @ l"
  by (induction l arbitrary: s) auto

lemma foldl_insert: "foldl (\<lambda>A x. insert (f x) A) A xs = A \<union> (f ` set xs)"
  by(induction xs arbitrary: A) simp_all

lemma foldl_concat_prodl: "foldl (\<lambda>(l, r) x. (l @ g r x, f r x)) (l, r) xs =
    (l @ concat (map (\<lambda>(ys, x). g (foldl f r ys) x) (inits_self xs)), foldl f r xs)"
  by(induction xs arbitrary: l r) (simp_all add: split_def o_def)

end