theory Prod_lexorder_alt
imports Main
begin

definition prod_lexord :: "'a rel \<Rightarrow> 'b rel \<Rightarrow> ('a \<times> 'b) rel" where
"prod_lexord R S = {((x\<^sub>1,y\<^sub>1),(x\<^sub>2,y\<^sub>2)). (x\<^sub>1,x\<^sub>2) \<in> R \<or> (x\<^sub>1 = x\<^sub>2 \<and> (y\<^sub>1,y\<^sub>2) \<in> S)}"

instantiation prod :: (ord, ord) ord
begin

  definition less_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool"
  where "less_prod x y \<longleftrightarrow> (x,y) \<in> prod_lexord {(a,b). a < b} {(a,b). a < b}"

  definition less_eq_prod :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq_prod x y \<longleftrightarrow> (x = y) \<or> (x < y)"

instance ..

end

instance prod :: (preorder, preorder) preorder
  apply (intro_classes)
  apply (auto simp add: less_prod_def less_eq_prod_def prod_lexord_def)
  using less_asym apply blast
  using less_asym apply blast
  using less_trans apply blast+
done

instance prod :: (order, order) order
  by (intro_classes, auto simp add: less_prod_def less_eq_prod_def prod_lexord_def)

instance prod :: (linorder, linorder) linorder
  by (intro_classes, auto simp add: less_prod_def less_eq_prod_def prod_lexord_def)

lemma less_eq_prod_simp [simp, code]:
  fixes x1 x2 :: "'a :: order" and y1 y2 :: "'b :: order"
  shows "(x1, y1) \<le> (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 \<le> x2 \<and> y1 \<le> y2"
  apply (auto simp add: less_eq_prod_def less_prod_def prod_lexord_def less_imp_le)
  apply (simp_all add: less_le_not_le)
done

lemma less_prod_simp [simp, code]:
  fixes x1 x2 :: "'a :: order" and y1 y2 :: "'b :: order"
  shows "(x1, y1) < (x2, y2) \<longleftrightarrow> x1 < x2 \<or> x1 \<le> x2 \<and> y1 < y2"
  apply (simp add: less_prod_def prod_lexord_def)
  using dual_order.strict_iff_order apply blast
done

lemma less_prod_def':
  fixes x y :: "'a::ord \<times> 'b::ord"
  shows "x < y \<longleftrightarrow> fst x < fst y \<or> fst x = fst y \<and> snd x < snd y"
  by (auto simp add: less_prod_def le_less prod_lexord_def)

instantiation prod :: (linorder, linorder) distrib_lattice
begin

definition
  "(inf :: 'a \<times> 'b \<Rightarrow> _ \<Rightarrow> _) = min"

definition
  "(sup :: 'a \<times> 'b \<Rightarrow> _ \<Rightarrow> _) = max"

instance
  by default (auto simp add: inf_prod_def sup_prod_def max_min_distrib2)

end

instantiation prod :: (bot, bot) bot
begin

definition
  "bot = (bot, bot)"

instance ..

end

instance prod :: (order_bot, order_bot) order_bot
  by default (auto simp add: bot_prod_def)

instantiation prod :: (top, top) top
begin

definition
  "top = (top, top)"

instance ..

end

instance prod :: (order_top, order_top) order_top
  by default (auto simp add: top_prod_def)

instance prod :: (wellorder, wellorder) wellorder
proof
  fix P :: "'a \<times> 'b \<Rightarrow> bool" and z :: "'a \<times> 'b"
  assume P: "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x"
  show "P z"
  proof (induct z)
    case (Pair a b)
    show "P (a, b)"
    proof (induct a arbitrary: b rule: less_induct)
      case (less a\<^sub>1) note a\<^sub>1 = this
      show "P (a\<^sub>1, b)"
      proof (induct b rule: less_induct)
        case (less b\<^sub>1) note b\<^sub>1 = this
        show "P (a\<^sub>1, b\<^sub>1)"
        proof (rule P)
          fix p assume p: "p < (a\<^sub>1, b\<^sub>1)"
          show "P p"
          proof (cases "fst p < a\<^sub>1")
            case True
            then have "P (fst p, snd p)" by (rule a\<^sub>1)
            then show ?thesis by simp
          next
            case False
            with p have 1: "a\<^sub>1 = fst p" and 2: "snd p < b\<^sub>1"
              by (simp_all add: less_prod_def')
            from 2 have "P (a\<^sub>1, snd p)" by (rule b\<^sub>1)
            with 1 show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed

text {* Legacy lemma bindings *}

lemmas prod_le_def = less_eq_prod_def
lemmas prod_less_def = less_prod_def
lemmas prod_less_eq = less_prod_def'

lemma prod_lexord_mono [mono]:
  "(\<And> x y. f x y \<longrightarrow> g x y) \<Longrightarrow> (\<And> x y. f' x y \<longrightarrow> g' x y) \<Longrightarrow>
  (x, y) \<in> prod_lexord {(x, y). f x y} {(x, y). f' x y} \<longrightarrow> (x, y) \<in> prod_lexord {(x, y). g x y} {(x, y). g' x y}"
  by (auto simp add: prod_lexord_def)
end