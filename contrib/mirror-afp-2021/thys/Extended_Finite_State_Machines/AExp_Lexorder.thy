subsection\<open>AExp Lexorder\<close>

text\<open>This theory defines a lexicographical ordering on arithmetic expressions such that we can build
orderings for guards and, subsequently, transitions. We make use of the previously established
orderings on variable names and values.\<close>

theory AExp_Lexorder
imports AExp Value_Lexorder
begin

text_raw\<open>\snip{height}{1}{2}{%\<close>
fun height :: "'a aexp \<Rightarrow> nat"  where
  "height (L l2) = 1" |
  "height (V v2) = 1" |
  "height (Plus e1 e2) = 1 + max (height e1) (height e2)" |
  "height (Minus e1 e2) = 1 + max (height e1) (height e2)" |
  "height (Times e1 e2) = 1 + max (height e1) (height e2)"
text_raw\<open>}%endsnip\<close>

instantiation aexp :: (linorder) linorder begin
fun less_aexp_aux :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> bool"  where
  "less_aexp_aux (L l1) (L l2) = (l1 < l2)" |
  "less_aexp_aux (L l1) _ = True" |

  "less_aexp_aux (V v1) (L l1) = False" |
  "less_aexp_aux (V v1) (V v2) = (v1 < v2)" |
  "less_aexp_aux (V v1) _ = True" |

  "less_aexp_aux (Plus e1 e2) (L l2) = False" |
  "less_aexp_aux (Plus e1 e2) (V v2) = False" |
  "less_aexp_aux (Plus e1 e2) (Plus e1' e2') = ((less_aexp_aux e1 e1') \<or> ((e1 = e1') \<and> (less_aexp_aux e2 e2')))"|
  "less_aexp_aux (Plus e1 e2) _ = True" |

  "less_aexp_aux (Minus e1 e2) (Minus e1' e2') =  ((less_aexp_aux e1 e1') \<or> ((e1 = e1') \<and> (less_aexp_aux e2 e2')))" |
  "less_aexp_aux (Minus e1 e2) (Times e1' e2') = True" |
  "less_aexp_aux (Minus e1 e2) _ = False" |

  "less_aexp_aux (Times e1 e2) (Times e1' e2') =  ((less_aexp_aux e1 e1') \<or> ((e1 = e1') \<and> (less_aexp_aux e2 e2')))" |
  "less_aexp_aux (Times e1 e2) _ = False"

definition less_aexp :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> bool" where
  "less_aexp a1 a2 = (
    let
      h1 = height a1;
      h2 = height a2
    in
    if h1 = h2 then
      less_aexp_aux a1 a2
    else
      h1 < h2
  )"

definition less_eq_aexp :: "'a aexp \<Rightarrow> 'a aexp \<Rightarrow> bool"
  where "less_eq_aexp e1 e2 \<equiv> (e1 < e2) \<or> (e1 = e2)"

declare less_aexp_def [simp]

lemma less_aexp_aux_antisym: "less_aexp_aux x  y = (\<not>(less_aexp_aux y x) \<and> (x \<noteq> y))"
  by (induct x y rule: less_aexp_aux.induct, auto)

lemma less_aexp_antisym: "(x::'a aexp) < y = (\<not>(y < x) \<and> (x \<noteq> y))"
  apply (simp add: Let_def)
  apply standard
  using less_aexp_aux_antisym apply blast
  apply (simp add: not_less)
  apply clarify
  by (induct x, auto)

lemma less_aexp_aux_trans: "less_aexp_aux x y \<Longrightarrow> less_aexp_aux y z \<Longrightarrow> less_aexp_aux x z"
proof (induct x y arbitrary: z rule: less_aexp_aux.induct)
  case (1 l1 l2)
  then show ?case by (cases z, auto)
next
  case ("2_1" l1 v)
  then show ?case by (cases z, auto)
next
  case ("2_2" l1 v va)
  then show ?case by (cases z, auto)
next
  case ("2_3" l1 v va)
  then show ?case by (cases z, auto)
next
  case ("2_4" l1 v va)
  then show ?case by (cases z, auto)
next
  case (3 v1 l1)
  then show ?case by (cases z, auto)
next
  case (4 v1 v2)
  then show ?case by (cases z, auto)
next
  case ("5_1" v1 v va)
  then show ?case by (cases z, auto)
next
  case ("5_2" v1 v va)
  then show ?case by (cases z, auto)
next
  case ("5_3" v1 v va)
  then show ?case by (cases z, auto)
next
  case (6 e1 e2 l2)
  then show ?case by (cases z, auto)
next
  case (7 e1 e2 v2)
  then show ?case by (cases z, auto)
next
  case (8 e1 e2 e1' e2')
  then show ?case by (cases z, auto)
next
  case ("9_1" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case ("9_2" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case (10 e1 e2 e1' e2')
  then show ?case by (cases z, auto)
next
  case (11 e1 e2 e1' e2')
  then show ?case by (cases z, auto)
next
  case ("12_1" e1 e2 v)
  then show ?case by (cases z, auto)
next
  case ("12_2" e1 e2 v)
  then show ?case by (cases z, auto)
next
  case ("12_3" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case (13 e1 e2 e1' e2')
  then show ?case by (cases z, auto)
next
  case ("14_1" e1 e2 v)
  then show ?case by (cases z, auto)
next
  case ("14_2" e1 e2 v)
  then show ?case by (cases z, auto)
next
  case ("14_3" e1 e2 v va)
  then show ?case by (cases z, auto)
next
  case ("14_4" e1 e2 v va)
  then show ?case by (cases z, auto)
qed

lemma less_aexp_trans: "(x::'a aexp) < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  apply (simp add: Let_def)
  apply standard
   apply (metis AExp_Lexorder.less_aexp_aux_trans dual_order.asym)
  by presburger

instance proof
    fix x y z :: "'a aexp"
    show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
      by (metis less_aexp_antisym less_eq_aexp_def)
    show "(x \<le> x)"
      by (simp add: less_eq_aexp_def)
    show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      by (metis less_aexp_trans less_eq_aexp_def)
    show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
      unfolding less_eq_aexp_def using less_aexp_antisym by blast
    show "x \<le> y \<or> y \<le> x"
      unfolding less_eq_aexp_def using less_aexp_antisym by blast
  qed
end

lemma smaller_height: "height a1 < height a2 \<Longrightarrow> a1 < a2"
  by simp

end
