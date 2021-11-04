(*  Title:      CoW/CoWBasic.thy
    Author:     Štěpán Holub, Charles University
    Author:     Martin Raška, Charles University
    Author:     Štěpán Starosta, CTU in Prague
*)

theory CoWBasic
  imports "HOL-Library.Sublist" Arithmetical_Hints Reverse_Symmetry
begin                                                            

chapter "Basics of Combinatorics on Words"

text\<open>Combinatorics on Words, as the name suggests, studies words, finite or infinite sequences of elements from a, usually finite, alphabet.
The essential operation on finite words is the concatenation of two words, which is associative and noncommutative. 
This operation yields many simply formulated problems, often in terms of \emph{equations on words}, that are mathematically challenging.

See for instance @{cite ChoKa97} for an introduction to Combinatorics on Words, and \cite{Lo,Lo2,Lo3} as another reference for Combinatorics on Words.
This theory deals exclusively with finite words and  provides basic facts of the field which can be considered as folklore.

The most natural way to represent finite words is by the type @{typ "'a list"}.
 From an algebraic viewpoint, lists are free monoids. On the other hand, any free monoid is isomoporphic to a monoid of lists of its generators.
The algebraic point of view and the combinatorial point of view therefore overlap significantly in Combinatorics on Words.
\<close>

section "Definitions and notations"

text\<open>First, we introduce elementary definitions and notations.\<close>

text\<open>The concatenation @{term append} of two finite lists/words is the very basic operation in Combinatorics on Words, its notation is usually omitted.
In this field, a common notation for this operation is $\cdot$, which we use and add here.\<close>


notation append (infixr "\<cdot>" 65)

lemmas rassoc = append_assoc
lemmas lassoc = append_assoc[symmetric]

text\<open>We add a common notation for the length of a given word $|w|$.\<close>


notation
  length  ("\<^bold>|_\<^bold>|") \<comment> \<open>note that it's bold |\<close>
notation (latex output)
  length  ("\<^latex>\<open>\\ensuremath{\\left| \<close>_\<^latex>\<open>\\right|}\<close>")

subsection \<open>Empty and nonempty word\<close>

text\<open>As the word of length zero @{term Nil} or @{term "[]"} will be used often, we adopt its frequent notation $\varepsilon $ in this formalization.\<close>

notation Nil ("\<epsilon>")

abbreviation drop_emp :: "'a list set \<Rightarrow> 'a list set" ( "_\<^sub>+" [1000] ) where
  "drop_emp S \<equiv> S - {\<epsilon>}"

subsection \<open>Prefix\<close>

text\<open>The property of being a prefix shall be frequently used, and we give it yet another frequent shorthand notation.
Analogously, we introduce shorthand notations for non-empty prefix and strict prefix, and continue with suffixes and factors.
\<close>


notation prefix (infixl "\<le>p" 50)
notation (latex output) prefix  ("\<le>\<^sub>p")
lemmas [simp] = prefix_def

lemmas prefI'[intro] = prefixI

lemma prefI[intro]: "p \<cdot> s = w \<Longrightarrow> p \<le>p w"
  by auto

lemma prefD: "u \<le>p v \<Longrightarrow> \<exists> z. v = u \<cdot> z"
  unfolding prefix_def.

definition prefix_comparable :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "\<bowtie>" 50) 
  where prefix_comparable_def[simp]: "(prefix_comparable u v) \<equiv> u \<le>p v \<or> v \<le>p u"

lemma pref_compIff[iff]: "u \<bowtie> v \<longleftrightarrow> u \<le>p v \<or> v \<le>p u"
  by simp

definition nonempty_prefix (infixl "\<le>np" 50) where nonempty_prefix_def[simp]:  "u \<le>np v \<equiv> u \<noteq> \<epsilon> \<and> u \<le>p v"
notation (latex output) nonempty_prefix  ("\<le>\<^bsub>np\<^esub>" 50)

lemma npI[intro]: "u \<noteq> \<epsilon> \<Longrightarrow> u \<le>p v \<Longrightarrow> u \<le>np v"
  by auto

lemma npI'[intro]: "u \<noteq> \<epsilon> \<Longrightarrow> (\<exists> z. u \<cdot> z = v) \<Longrightarrow> u \<le>np v"
  by auto

lemma npD: "u \<le>np v \<Longrightarrow> u \<le>p v"
  by simp

lemma npD': "u \<le>np v \<Longrightarrow> u \<noteq> \<epsilon>"
  by simp

notation strict_prefix (infixl "<p" 50)
notation (latex output) strict_prefix  ("<\<^sub>p")
lemmas [simp] = strict_prefix_def

lemma sprefI1[intro]: "v = u \<cdot> z \<Longrightarrow> z \<noteq> \<epsilon> \<Longrightarrow> u <p v"
  by simp

lemma sprefI1'[intro]: "u \<cdot> z = v \<Longrightarrow> z \<noteq> \<epsilon> \<Longrightarrow> u <p v"
   by blast

lemma sprefI2[intro]: "u \<le>p v \<Longrightarrow> length u < length v \<Longrightarrow> u <p v"
  unfolding strict_prefix_def
  by blast

lemma sprefD[elim]: "u <p v \<Longrightarrow> u \<le>p v \<and> u \<noteq> v"
  by auto

lemmas sprefD1[elim] = prefix_order.order.strict_implies_order and
  sprefD2[elim] = prefix_order.less_imp_neq

lemma sprefE [elim]: assumes "u <p v" obtains z where "u \<cdot> z = v" and "z \<noteq> \<epsilon>"
  using assms  by auto

subsection \<open>Suffix\<close>

notation suffix (infixl "\<le>s" 60)
notation (latex output) suffix ("\<le>\<^sub>s")
lemmas [simp] = suffix_def

lemma sufI[intro]: "p \<cdot> s = w \<Longrightarrow> s \<le>s w"
  by auto

lemma sufD[elim]: "u \<le>s v \<Longrightarrow> \<exists> z. z \<cdot> u = v"
  by auto

notation strict_suffix (infixl "<s" 50)
notation (latex output) strict_suffix  ("<\<^sub>s")
lemmas [simp] = strict_suffix_def

lemmas [intro] = suffix_order.le_neq_trans

lemma ssufI1[intro]: "u \<cdot> v = w \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> v <s w"
  by blast

lemma ssufI2[intro]: "u \<le>s v \<Longrightarrow> length u < length v \<Longrightarrow> u <s v"
  by blast

lemma ssufD[elim]: "u <s v \<Longrightarrow> u \<le>s v \<and> u \<noteq> v"
  by auto

lemmas ssufD1[elim] = suffix_order.order.strict_implies_order and
  ssufD2[elim] = suffix_order.less_imp_neq

definition suffix_comparable :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infixl "\<bowtie>\<^sub>s" 50) 
  where suffix_comparable_def[simp]: "(suffix_comparable u v) \<equiv> (rev u) \<bowtie> (rev v)"

definition nonempty_suffix (infixl "\<le>ns" 60) where nonempty_suffix_def[simp]:  "u \<le>ns v \<equiv> u \<noteq> \<epsilon> \<and> u \<le>s v"
notation (latex output) nonempty_suffix  ("\<le>\<^bsub>ns\<^esub>" 50)

lemma nsI[intro]: "u \<noteq> \<epsilon> \<Longrightarrow> u \<le>s v \<Longrightarrow> u \<le>ns v"
  by auto

lemma nsI'[intro]: "u \<noteq> \<epsilon> \<Longrightarrow> (\<exists> z. z \<cdot> u = v) \<Longrightarrow> u \<le>ns v"
  by blast

lemma nsD: "u \<le>ns v \<Longrightarrow> u \<le>s v"
  by simp

lemma nsD': "u \<le>ns v \<Longrightarrow> u \<noteq> \<epsilon>"
  by simp

subsection \<open>Factor\<close>

text\<open>A @{term sublist} of some word is in Combinatorics of Words called a factor.
We adopt a common shorthand notation for the property of being a factor, strict factor and nonempty factor (the latter we also define).\<close>


notation sublist (infixl "\<le>f" 60)
notation (latex output) sublist ("\<le>\<^sub>f")
lemmas factor_def[simp] = sublist_def


notation strict_sublist (infixl "<f" 60)
notation (latex output) strict_sublist ("<\<^bsub>f\<^esub>")
lemmas strict_factor_def[simp] = strict_sublist_def

definition nonempty_factor (infixl "\<le>nf" 60) where nonempty_factor_def[simp]:  "u \<le>nf v \<equiv> u \<noteq> \<epsilon> \<and> (\<exists> p s. p\<cdot>u\<cdot>s = v)"
notation (latex output) nonempty_factor ("\<le>\<^bsub>nf\<^esub>")

lemma facI: "u \<le>f p\<cdot>u\<cdot>s"
  using sublist_appendI.

lemma facI': "a \<cdot> u \<cdot> b = w \<Longrightarrow> u \<le>f w"
  by auto

lemma facE[elim]: assumes "u \<le>f v" 
  obtains p s where "v = p \<cdot> u \<cdot> s"
  using assms unfolding factor_def
  by blast

lemma facE'[elim]: assumes "u \<le>f v" 
  obtains p s where "p \<cdot> u \<cdot> s = v"
  using assms unfolding factor_def
  by blast

section "Various elementary lemmas"

lemmas concat_morph = sym[OF concat_append]

lemmas cancel = same_append_eq and
    cancel_right = append_same_eq

lemma bij_lists: "bij_betw f X Y \<Longrightarrow> bij_betw (map f) (lists X) (lists Y)"
proof-
  assume "bij_betw f X Y"
  hence "inj_on f X"
    by (simp add: bij_betw_def)
  have "\<And> x y. x \<in> lists X \<Longrightarrow> y \<in> lists X \<Longrightarrow> (set x \<union> set y) \<subseteq> X"
    by blast 
  hence "\<And> x y. x \<in> lists X \<Longrightarrow> y \<in> lists X \<Longrightarrow> inj_on f (set x \<union> set y)"
    using subset_inj_on[OF \<open>inj_on f X\<close>] by meson
  hence "\<And> x y. x \<in> lists X \<Longrightarrow> y \<in> lists X \<Longrightarrow> map f x = map f y \<longleftrightarrow> x  = y" 
    by (simp add: inj_on_map_eq_map)
  hence "inj_on (map f) (lists X)"
    by (simp add: inj_on_def) 
  thus ?thesis using  \<open>bij_betw f X Y\<close> bij_betw_def lists_image
    by metis
qed

lemma concat_sing': "concat [r] = r"
  by simp

lemma concat_sing:  "s = [hd s] \<Longrightarrow> concat s = hd s"
  using concat_sing'[of "hd s"] by auto

lemma rev_sing: "rev [x] = [x]"
  by simp

lemma hd_word: "a#ws = [a] \<cdot> ws"
  by simp

lemma hd_word': "w \<noteq> \<epsilon> \<Longrightarrow> [hd w] \<cdot> tl w = w"
  by simp

lemma hd_pref: "w \<noteq> \<epsilon> \<Longrightarrow> [hd w] \<le>p w"
  using hd_word'
  by blast

lemma add_nth: assumes "n < \<^bold>|w\<^bold>|" shows "(take n w) \<cdot> [w!n] \<le>p w"
  using take_is_prefix[of "Suc n" w, unfolded take_Suc_conv_app_nth[OF assms]].

lemma hd_pref': "w \<noteq> \<epsilon> \<Longrightarrow> [w!0] \<le>p w"
  using add_nth by fastforce

lemma sub_lists_mono: "A \<subseteq> B \<Longrightarrow> x \<in> lists A \<Longrightarrow> x \<in> lists B"
  by auto

lemma lists_hd: "us \<noteq> \<epsilon> \<Longrightarrow> us \<in> lists Q \<Longrightarrow> hd us \<in> Q"
  by fastforce

lemma replicate_in_lists: "replicate k z \<in> lists {z}"
  by (induction k) auto

lemma tl_lists: assumes "us \<in> lists A" shows "tl us \<in> lists A"
  using suffix_lists[OF suffix_tl assms].

lemma long_list_tl: assumes "1 < \<^bold>|us\<^bold>|" shows "tl us \<noteq> \<epsilon>"
proof
  assume "tl us = \<epsilon>"
  from assms
  have "us \<noteq> \<epsilon>" and "\<^bold>|us\<^bold>| = Suc \<^bold>|tl us\<^bold>|" and "\<^bold>|us\<^bold>| \<noteq> Suc 0"
    by auto
  thus False
    using \<open>tl us = \<epsilon>\<close> by simp
qed

lemma tl_set: "x \<in> set (tl a) \<Longrightarrow> x \<in> set a"
  using list.sel(2) list.set_sel(2) by metis

lemma drop_take_inv: "n \<le> \<^bold>|u\<^bold>| \<Longrightarrow> drop n (take n u \<cdot> w) = w"
  by simp

lemma split_list_long: assumes "1 < \<^bold>|us\<^bold>|" and "u \<in> set us" 
  obtains xs ys where "us = xs \<cdot> [u] \<cdot> ys" and "xs\<cdot>ys\<noteq>\<epsilon>"
proof-
  obtain xs ys where "us = xs \<cdot> [u] \<cdot> ys"
    using split_list_first[OF \<open>u \<in> set us\<close>] by auto
  hence "xs\<cdot>ys\<noteq>\<epsilon>" 
    using \<open>1 < \<^bold>|us\<^bold>|\<close> by auto
  from that[OF \<open>us = xs \<cdot> [u] \<cdot> ys\<close> this]
  show thesis.
qed

lemma flatten_lists: "G \<subseteq> lists B \<Longrightarrow> xs \<in> lists G \<Longrightarrow> concat xs \<in> lists B"
proof (induct xs, simp)
  case (Cons a xs)
  hence "concat xs \<in> lists B" and "a \<in> lists B"
    by auto 
  thus ?case
    by simp
qed

lemma concat_map_sing_ident: "concat (map (\<lambda> x. [x]) xs) = xs"
  by auto                                           

lemma hd_concat_tl: assumes "ws \<noteq> \<epsilon>" shows "hd ws \<cdot> concat (tl ws) = concat ws"
  using concat.simps(2)[of "hd ws" "tl ws", unfolded list.collapse[OF \<open>ws \<noteq> \<epsilon>\<close>], symmetric].

lemma concat_butlast_last: assumes "ws \<noteq> \<epsilon>" shows "concat (butlast ws) \<cdot> last ws = concat ws"
  using  concat_morph[of "butlast ws" "[last ws]", unfolded concat_sing' append_butlast_last_id[OF \<open>ws \<noteq> \<epsilon>\<close>]].

lemma concat_last_suf: "ws \<noteq> \<epsilon> \<Longrightarrow> last ws \<le>s concat ws"
  using concat_butlast_last by blast

lemma concat_hd_pref: "ws \<noteq> \<epsilon> \<Longrightarrow> hd ws \<le>p concat ws"
  using hd_concat_tl by blast

lemma set_nemp_concat_nemp: assumes "ws \<noteq> \<epsilon>" and "\<epsilon> \<notin> set ws" shows "concat ws \<noteq> \<epsilon>"
  using \<open>\<epsilon> \<notin> set ws\<close> last_in_set[OF \<open>ws \<noteq> \<epsilon>\<close>] concat_butlast_last[OF \<open>ws \<noteq> \<epsilon>\<close>] by fastforce

lemmas takedrop = append_take_drop_id

lemma comm_rev_iff: "rev u \<cdot> rev v = rev v \<cdot> rev u \<longleftrightarrow> u \<cdot> v = v \<cdot> u" 
  unfolding rev_append[symmetric] rev_is_rev_conv eq_ac(1)[of "u \<cdot> v"] by blast

lemma rev_induct2:
  "\<lbrakk> P [] [];
  \<And>x xs. P (xs\<cdot>[x]) [];
  \<And>y ys. P [] (ys\<cdot>[y]);
  \<And>x xs y ys. P xs ys  \<Longrightarrow> P (xs\<cdot>[x]) (ys\<cdot>[y]) \<rbrakk>
 \<Longrightarrow> P xs ys"
proof (induct xs arbitrary: ys rule: rev_induct)
  case Nil
  then show ?case
    using rev_induct[of "P \<epsilon>"]
    by presburger
next
  case (snoc x xs)
  hence "P xs ys'" for ys'
    by simp
  then show ?case
    by (simp add: rev_induct snoc.prems(2) snoc.prems(4))
qed

subsection \<open>Orderings on lists: prefix, suffix, factor\<close>

lemmas self_pref = prefix_order.order.refl
lemmas pref_antisym = prefix_order.order.antisym
lemmas pref_trans = prefix_order.order.trans
lemmas suf_trans = suffix_order.order.trans


subsection "On the empty word"

lemma nemp_elem_setI[intro]: "u \<in> S \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> u \<in> S\<^sub>+"
  by simp

lemma nel_drop_emp: "u \<noteq> \<epsilon> \<Longrightarrow> u \<in> S \<Longrightarrow> u \<in> S\<^sub>+"
  by simp

lemma drop_emp_nel: assumes "u \<in> S\<^sub>+" shows "u \<noteq> \<epsilon>" and "u \<in> S"
  using assms by simp+

lemma emp_concat_emp: "us \<in> lists S\<^sub>+ \<Longrightarrow> concat us = \<epsilon> \<Longrightarrow> us = \<epsilon>"
  using DiffD2 by auto

lemma take_nemp: "w \<noteq> \<epsilon> \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> take n w \<noteq> \<epsilon>"
  by simp

lemma pref_nemp [intro]: "u \<noteq> \<epsilon> \<Longrightarrow> u \<cdot> v \<noteq> \<epsilon>"
  unfolding append_is_Nil_conv by simp

lemma suf_nemp [intro]: "v \<noteq> \<epsilon> \<Longrightarrow> u \<cdot> v \<noteq> \<epsilon>"
  unfolding append_is_Nil_conv by simp

section "Length and its properties"

lemma lenarg: "u = v \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
  by simp

lemma npos_len: "\<^bold>|u\<^bold>| \<le> 0 \<Longrightarrow> u = \<epsilon>"
  by simp

lemma nemp_pos_len: "r \<noteq> \<epsilon> \<Longrightarrow> 1 \<le> \<^bold>|r\<^bold>|"
  by (simp add: leI)

lemma swap_len: "\<^bold>|u \<cdot> v\<^bold>| = \<^bold>|v \<cdot> u\<^bold>|"
  by simp

lemma len_after_drop: "p + q \<le> \<^bold>|w\<^bold>| \<Longrightarrow>  q \<le> \<^bold>|drop p w\<^bold>|"
  by simp 

lemma short_take_append: "n \<le> \<^bold>|u\<^bold>|\<Longrightarrow> take n (u \<cdot> v) = take n u"
  by simp

lemma sing_word: "\<^bold>|us\<^bold>| = 1 \<Longrightarrow> [hd us] = us"
  by (cases us) simp+

lemma sing_word_concat: assumes "\<^bold>|us\<^bold>| = 1" shows "[concat us] = us"
  by (simp add: assms concat_sing sing_word)

lemma nonsing_concat_len: "\<^bold>|us\<^bold>| \<noteq> 1 \<Longrightarrow> concat us \<noteq> \<epsilon> \<Longrightarrow> 1 < \<^bold>|us\<^bold>|"
  using nat_neq_iff by fastforce

lemma sing_len: "\<^bold>|[a]\<^bold>| = 1"
  by simp
 
lemma pref_len': "\<^bold>|u\<^bold>| \<le> \<^bold>|u \<cdot> z\<^bold>|"
  by auto

lemma suf_len': "\<^bold>|u\<^bold>| \<le> \<^bold>|z \<cdot> u\<^bold>|"
  by auto

lemma fac_len: "u \<le>f v \<Longrightarrow> \<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>|"
  by auto

lemma fac_len': "\<^bold>|w\<^bold>| \<le> \<^bold>|u \<cdot> w \<cdot> v\<^bold>|"
  by simp

lemma fac_len_eq: "u \<le>f v \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  unfolding factor_def using length_append npos_len by fastforce

lemma drop_len: "\<^bold>|u \<cdot> w\<^bold>| \<le> \<^bold>|u \<cdot> v \<cdot> w\<^bold>|"
  by simp

lemma drop_pref: "drop \<^bold>|u\<^bold>| (u \<cdot> w) = w"
  by simp

lemma take_len: "p \<le> \<^bold>|w\<^bold>| \<Longrightarrow> \<^bold>|take p w\<^bold>| = p"
  using trans[OF length_take min_absorb2].

lemma conj_len: "p \<cdot> x = x \<cdot> s \<Longrightarrow> \<^bold>|p\<^bold>| = \<^bold>|s\<^bold>|"
  using length_append[of p x] length_append[of x s] add.commute add_left_imp_eq
  by auto

lemma take_nemp_len: "u \<noteq> \<epsilon> \<Longrightarrow> r \<noteq> \<epsilon> \<Longrightarrow> take \<^bold>|r\<^bold>| u \<noteq> \<epsilon>"
  by simp

lemma nemp_len: "u \<noteq> \<epsilon> \<Longrightarrow> \<^bold>|u\<^bold>| \<noteq> 0" 
  by simp

lemma take_self: "take \<^bold>|w\<^bold>| w = w"
  using take_all[of w "\<^bold>|w\<^bold>|", OF order.refl].

lemma len_le_concat: "\<epsilon> \<notin>  set ws \<Longrightarrow> \<^bold>|ws\<^bold>| \<le> \<^bold>|concat ws\<^bold>|"
proof (induct ws, simp)
  case (Cons a ws)
  hence "1 \<le> \<^bold>|a\<^bold>|"
    using list.set_intros(1)[of a ws] nemp_pos_len[of a] by blast 
  then show ?case 
    unfolding   concat.simps(2)  unfolding  length_append hd_word[of a ws] sing_len 
    using Cons.hyps Cons.prems by simp
qed

lemma eq_len_iff: assumes eq: "x \<cdot> y = u \<cdot> v" shows "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<longleftrightarrow> \<^bold>|v\<^bold>| \<le> \<^bold>|y\<^bold>|"
  using lenarg[OF eq] unfolding length_append by auto

lemma eq_len_iff_less: assumes eq: "x \<cdot> y = u \<cdot> v" shows "\<^bold>|x\<^bold>| < \<^bold>|u\<^bold>| \<longleftrightarrow> \<^bold>|v\<^bold>| < \<^bold>|y\<^bold>|"
  using lenarg[OF eq] unfolding length_append by auto

section "Prefix and prefix comparability properties"

lemmas pref_emp = prefix_bot.bot.extremum_uniqueI

lemma triv_pref: "r \<le>p r \<cdot> s"
  using prefI[OF refl].

lemma triv_spref: "s \<noteq> \<epsilon> \<Longrightarrow> r <p r \<cdot> s"
  by simp

lemma pref_cancel: "z \<cdot> u \<le>p z \<cdot> v \<Longrightarrow> u \<le>p v"
  by simp

lemma pref_cancel': "u \<le>p v \<Longrightarrow> z \<cdot> u \<le>p z \<cdot> v"
  by simp

lemmas pref_cancel_conv = same_prefix_prefix

lemmas pref_ext = prefix_prefix \<comment> \<open>provided by Sublist.thy\<close>

lemma spref_ext: "r <p u \<Longrightarrow> r <p u \<cdot> v"
  by force

lemma pref_ext_nemp: "r \<le>p u \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> r <p u \<cdot> v"
  by auto

lemma pref_take: "p \<le>p w \<Longrightarrow> take \<^bold>|p\<^bold>| w = p"
  by auto

lemma pref_take_conv: "take (\<^bold>|r\<^bold>|) w = r \<longleftrightarrow> r \<le>p w"
  using pref_take[of r w] take_is_prefix[of "\<^bold>|r\<^bold>|" w] by argo

lemma le_suf_drop: assumes "i \<le> j" shows "drop j w \<le>s drop i w"
  using suffix_drop[of "j - i" "drop i w", unfolded drop_drop le_add_diff_inverse2[OF \<open>i \<le> j\<close>]].

lemma spref_take: "p <p w \<Longrightarrow> take \<^bold>|p\<^bold>| w = p"
  by auto

lemma pref_same_len: "u \<le>p v \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  by auto    

lemma add_nth_pref: assumes "u <p w" shows "u \<cdot> [w!\<^bold>|u\<^bold>|] \<le>p w"
  using add_nth[OF prefix_length_less[OF \<open>u <p w\<close>], unfolded spref_take[OF \<open>u <p w\<close>]].

lemma index_pref: "\<^bold>|u\<^bold>| \<le> \<^bold>|w\<^bold>| \<Longrightarrow> (\<forall> i < \<^bold>|u\<^bold>|.  u!i = w!i) \<Longrightarrow> u \<le>p w"
  using trans[OF sym[OF take_all[OF order_refl]] nth_take_lemma[OF order_refl], of u w] 
    take_is_prefix[of "\<^bold>|u\<^bold>|" w] by auto

lemma pref_index: assumes "u \<le>p w" "i < \<^bold>|u\<^bold>|" shows "u!i = w!i"
  using nth_take[OF \<open>i < \<^bold>|u\<^bold>|\<close>, of w, unfolded pref_take[OF \<open>u \<le>p w\<close>]].

lemma pref_drop: "u \<le>p v \<Longrightarrow> drop p u \<le>p drop p v"
  using prefI[OF sym[OF drop_append]] by auto

subsection "Prefix comparability"

lemma pref_comp_sym[sym]: "u \<bowtie> v \<Longrightarrow> v \<bowtie> u"
  by blast

lemmas ruler_le = prefix_length_prefix and
       ruler = prefix_same_cases and
       ruler' = prefix_same_cases[folded prefix_comparable_def] 

lemma ruler_equal: "u \<le>p w \<Longrightarrow> v \<le>p w \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  by auto

lemma ruler_comp: "u \<le>p v \<Longrightarrow> u' \<le>p v' \<Longrightarrow> v \<bowtie> v' \<Longrightarrow> u \<bowtie> u'"
  unfolding prefix_comparable_def
  using disjE[OF _ ruler[OF pref_trans] ruler[OF _ pref_trans]].

lemma ruler_pref: "w \<le>p v\<cdot>z \<Longrightarrow> w \<bowtie> v"
  unfolding prefix_comparable_def
  using ruler by blast

lemma pref_prod_pref_short: "u \<le>p z \<cdot> w \<Longrightarrow> v \<le>p w \<Longrightarrow> \<^bold>|u\<^bold>| \<le> \<^bold>|z \<cdot> v\<^bold>| \<Longrightarrow> u \<le>p z \<cdot> v"
  using ruler_le[OF _ pref_cancel'].

lemma pref_prod_pref: "u \<le>p z \<cdot> w \<Longrightarrow> u \<le>p w \<Longrightarrow>  u \<le>p z \<cdot> u"
  using pref_prod_pref_short[OF _ _ suf_len'].

lemma pref_prod_pref': assumes "u \<le>p z\<cdot>u\<cdot>w" shows "u \<le>p z\<cdot>u"
  using pref_prod_pref[of  u z "u \<cdot> w", OF \<open>u \<le>p z\<cdot>u\<cdot>w\<close> triv_pref].

lemma pref_prod_long: "u \<le>p v \<cdot> w \<Longrightarrow> \<^bold>|v\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> v \<le>p u"
  using ruler_le[OF triv_pref].

lemma pref_keeps_root: "u \<le>p r \<cdot> u \<Longrightarrow> v \<le>p u \<Longrightarrow> v \<le>p r \<cdot> v"
  using pref_prod_pref[of v r u] pref_trans[of v u "r\<cdot>u"] by blast

lemma pref_prolong:  "w \<le>p z \<cdot> r \<Longrightarrow> r \<le>p s \<Longrightarrow> w \<le>p z \<cdot> s"
  using pref_trans[OF _ pref_cancel'].

lemma pref_prolong': assumes "u \<le>p w \<cdot> z" "v \<cdot> u \<le>p z" shows "u \<le>p w \<cdot> v \<cdot> u"
  using prefix_length_prefix[OF \<open>u \<le>p w \<cdot> z\<close> pref_cancel'[OF \<open>v \<cdot> u \<le>p z\<close>, of w] suf_len'[of u "w\<cdot>v", unfolded rassoc]].

lemma pref_prolong_comp: "u \<le>p w \<cdot> z \<Longrightarrow> v \<cdot> u \<bowtie> z \<Longrightarrow> u \<le>p w \<cdot> v \<cdot> u"
  using pref_prolong[of u w z "v \<cdot> u"] pref_prolong'[of u w z v] by blast

lemma pref_prod_short: "u \<le>p v \<cdot> w \<Longrightarrow> \<^bold>|u\<^bold>| \<le> \<^bold>|v\<^bold>| \<Longrightarrow> u \<le>p v"
  using  prefI prefix_length_prefix[of u "v\<cdot>w" v]
  by blast

lemma pref_prod_short': assumes "u \<le>p v \<cdot> w" and "\<^bold>|u\<^bold>| < \<^bold>|v\<^bold>|" shows "u <p v"
  using pref_prod_short[OF \<open>u \<le>p v \<cdot> w\<close> less_imp_le[OF \<open>\<^bold>|u\<^bold>| < \<^bold>|v\<^bold>|\<close>]]  \<open>\<^bold>|u\<^bold>| < \<^bold>|v\<^bold>|\<close> by blast

lemma pref_prod_cancel: assumes "u \<le>p p\<cdot>w\<cdot>q" and "\<^bold>|p\<^bold>| \<le> \<^bold>|u\<^bold>|" and "\<^bold>|u\<^bold>| \<le> \<^bold>|p\<cdot>w\<^bold>|"
  obtains r where "u = p \<cdot> r" and "r \<le>p w"
proof-
  have "p \<le>p u"
    using pref_prod_long[OF \<open>u \<le>p p\<cdot>w\<cdot>q\<close>  \<open>\<^bold>|p\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>].
  then obtain r where "u = p \<cdot> r" using prefD by blast 
  hence "r \<le>p w"  using \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|p\<cdot>w\<^bold>|\<close> \<open>u \<le>p p\<cdot>w\<cdot>q\<close> 
    unfolding \<open>u = p \<cdot> r\<close> pref_cancel_conv length_append using pref_prod_short[of r w q] by simp
  from that[OF \<open>u = p \<cdot> r\<close> this]
  show thesis.
qed

lemma pref_prod_cancel': assumes "u \<le>p p\<cdot>w\<cdot>q" and "\<^bold>|p\<^bold>| < \<^bold>|u\<^bold>|" and "\<^bold>|u\<^bold>| \<le> \<^bold>|p\<cdot>w\<^bold>|"
  obtains r where "u = p \<cdot> r" and "r \<le>p w" and "r \<noteq> \<epsilon>" 
proof-
  obtain r where "u = p \<cdot> r" and "r \<le>p w" 
    using pref_prod_cancel[OF \<open>u \<le>p p\<cdot>w\<cdot>q\<close> less_imp_le[OF \<open>\<^bold>|p\<^bold>| < \<^bold>|u\<^bold>|\<close>] \<open>\<^bold>|u\<^bold>| \<le> \<^bold>|p\<cdot>w\<^bold>|\<close>].
  moreover have "r \<noteq> \<epsilon>" using  \<open>u = p \<cdot> r\<close> less_not_refl3[OF \<open>\<^bold>|p\<^bold>| < \<^bold>|u\<^bold>|\<close>, folded self_append_conv] by simp
  ultimately show thesis using that by simp
qed


lemma pref_comp_eq: "u \<bowtie> v \<Longrightarrow>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  by auto

lemma non_comp_parallel: "\<not> u \<bowtie> v \<longleftrightarrow> u \<parallel> v"
  unfolding prefix_comparable_def parallel_def de_Morgan_disj..

lemma comp_refl: "u \<bowtie> u"
  by simp

lemma incomp_cancel: "\<not> p\<cdot>u \<bowtie> p\<cdot>v \<Longrightarrow> \<not> u \<bowtie> v"
  by simp

lemma comp_cancel: "z \<cdot> u \<bowtie> z \<cdot> v \<Longrightarrow> u \<bowtie> v"
  by simp

lemma comm_ruler: "r \<cdot> s \<le>p w1 \<Longrightarrow> s \<cdot> r \<le>p w2 \<Longrightarrow> w1 \<bowtie> w2 \<Longrightarrow> r \<cdot> s = s \<cdot> r"
  using pref_comp_eq[OF ruler_comp swap_len].

lemma pref_share_take: "u \<le>p v \<Longrightarrow> q \<le> \<^bold>|u\<^bold>| \<Longrightarrow> take q u = take q v"
  by auto

lemma pref_prod_longer: "u \<le>p z \<cdot> w \<Longrightarrow> v \<le>p w \<Longrightarrow> \<^bold>|z \<cdot> v\<^bold>| \<le> \<^bold>|u\<^bold>|  \<Longrightarrow> z \<cdot> v \<le>p u" 
  using ruler_le[OF pref_cancel'].

lemma pref_comp_not_pref: "u \<bowtie> v \<Longrightarrow> \<not> v \<le>p u \<Longrightarrow> u <p v"
  by auto

lemma pref_comp_not_spref: "u \<bowtie> v \<Longrightarrow> \<not> u <p v \<Longrightarrow> v \<le>p u"
  using contrapos_np[OF _ pref_comp_not_pref].

lemma hd_prod: "u \<noteq> \<epsilon> \<Longrightarrow> (u \<cdot> v)!0 = u!0"
  by (cases u) (blast, simp)

lemma distinct_first: assumes "w \<noteq> \<epsilon>" "z \<noteq> \<epsilon>" "w!0 \<noteq> z!0" shows "w \<cdot> w' \<noteq> z \<cdot> z'"
  using hd_prod[of w w', OF \<open>w \<noteq> \<epsilon>\<close>] hd_prod[of z z', OF \<open>z \<noteq> \<epsilon>\<close>] \<open>w!0 \<noteq> z!0\<close> by auto 

lemmas last_no_split = prefix_snoc

lemma last_no_split': assumes "u <p w" "w \<le>p u \<cdot> [a]" shows "w = u \<cdot> [a]"
  using assms(1)[unfolded prefix_order.less_le_not_le] assms(2)[unfolded last_no_split] by presburger

lemma pcomp_shorter: "v \<bowtie> w \<Longrightarrow> \<^bold>|v\<^bold>| \<le> \<^bold>|w\<^bold>| \<Longrightarrow> v \<le>p w"
  by auto

lemma pref_comp_len_trans: "w \<le>p v \<Longrightarrow> u \<bowtie> v \<Longrightarrow> \<^bold>|w\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> w \<le>p u"
  unfolding prefix_comparable_def
  using prefix_length_prefix[of w v u] prefix_order.order.trans[of w v u]
  by argo

lemma comp_ext: "z \<cdot> w1 \<bowtie> z \<cdot> w2 \<longleftrightarrow> w1 \<bowtie> w2"
  using pref_cancel by auto

lemma emp_pref: "\<epsilon> \<le>p u"
  by simp

lemma emp_spref:  "u \<noteq> \<epsilon> \<Longrightarrow> \<epsilon> <p u"
  by simp

lemma long_pref: "u \<le>p v \<Longrightarrow> \<^bold>|v\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> u = v"
  by auto

lemma incomp_ext: "\<not> w1 \<bowtie>  w2 \<Longrightarrow> \<not> w1 \<cdot> z \<bowtie> w2 \<cdot> z'"
  using contrapos_nn[OF _ ruler_comp[OF triv_pref triv_pref]].

lemma mismatch_incopm: "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> u \<cdot> [x] \<bowtie> v \<cdot> [y]"
  by simp

lemma comp_prefs_comp: "u \<cdot> z \<bowtie> v \<cdot> w \<Longrightarrow> u \<bowtie> v"
  using ruler_comp[OF prefI[of _ z] prefI[of _ w], OF refl refl].

lemma comp_hd_eq: "u \<bowtie> v \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> hd u = hd v"
  by auto 

lemma pref_hd_eq': "p \<le>p u \<Longrightarrow> p \<le>p v \<Longrightarrow> p \<noteq> \<epsilon> \<Longrightarrow>  hd u = hd v"
  by auto

lemma pref_hd_eq: "u \<le>p v \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow>  hd u = hd v" 
  by auto

lemma suf_last_eq: "p \<le>s u \<Longrightarrow> p \<le>s v \<Longrightarrow> p \<noteq> \<epsilon> \<Longrightarrow>  last u = last v"
  by auto

lemma comp_hd_eq': assumes  "u \<cdot> r \<bowtie> v \<cdot> s" "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>" shows "hd u = hd v"
  using comp_prefs_comp[OF \<open>u \<cdot> r \<bowtie> v \<cdot> s\<close>] \<open>u \<noteq> \<epsilon>\<close> \<open>v \<noteq> \<epsilon>\<close> by auto 

section "Suffix and suffix comparability  properties"

lemmas suf_emp = suffix_bot.bot.extremum_uniqueI

lemma triv_suf: "u \<le>s v \<cdot> u"
  by simp

lemma emp_ssuf: "u \<noteq> \<epsilon> \<Longrightarrow> \<epsilon> <s u"
  by simp

lemma suf_cancel: "u\<cdot>v \<le>s w\<cdot>v \<Longrightarrow> u \<le>s w"
  by simp 

lemma suf_cancel': "u \<le>s w \<Longrightarrow> u\<cdot>v \<le>s w\<cdot>v"
  by simp 

lemmas suf_cancel_eq = same_suffix_suffix \<comment> \<open>provided by Sublist.thy\<close>

text\<open>Straightforward relations of suffix and prefix follow.\<close>

lemmas suf_rev_pref_iff = suffix_to_prefix \<comment> \<open>provided by Sublist.thy\<close>

lemmas ssuf_rev_pref_iff = strict_suffix_to_prefix \<comment> \<open>provided by Sublist.thy\<close>

lemma pref_rev_suf_iff: "u \<le>p v \<longleftrightarrow> rev u \<le>s rev v"
  using suffix_to_prefix[of "rev u" "rev v"] unfolding rev_rev_ident
  by blast

lemma spref_rev_suf_iff: "s <p w \<longleftrightarrow> rev s <s rev w"
  using strict_suffix_to_prefix[of "rev s" "rev w", unfolded rev_rev_ident, symmetric].

lemma nsuf_rev_pref_iff: "s \<le>ns w \<longleftrightarrow> rev s \<le>np rev w"
  unfolding nonempty_prefix_def nonempty_suffix_def suffix_to_prefix
  by fast

lemma npref_rev_suf_iff: "s \<le>np w \<longleftrightarrow> rev s \<le>ns rev w"
  unfolding nonempty_prefix_def nonempty_suffix_def pref_rev_suf_iff
  by fast

lemmas [reversal_rule] = 
  suf_rev_pref_iff[symmetric]
  pref_rev_suf_iff[symmetric]
  nsuf_rev_pref_iff[symmetric]
  npref_rev_suf_iff[symmetric]
  ssuf_rev_pref_iff[symmetric]
  spref_rev_suf_iff[symmetric]

lemmas suf_ext = suffix_appendI \<comment> \<open>provided by Sublist.thy\<close>

lemmas ssuf_ext = spref_ext[reversed] and
  suf_ext_nem = pref_ext_nemp[reversed] and
  suf_same_len = pref_same_len[reversed] and
  suf_take = pref_drop[reversed] and
  suf_share_take = pref_share_take[reversed] and
  long_suf = long_pref[reversed]

subsection "Suffix comparability"

lemma pref_comp_rev_suf_comp[reversal_rule]: "(rev w) \<bowtie>\<^sub>s (rev v) \<longleftrightarrow> w \<bowtie> v"
  by simp

lemma suf_comp_rev_pref_comp[reversal_rule]: "(rev w) \<bowtie> (rev v) \<longleftrightarrow> w \<bowtie>\<^sub>s v"
  by simp

lemmas suf_ruler_le = suffix_length_suffix \<comment> \<open>provided by Sublist.thy, same as ruler\_le[reversed]\<close>

lemmas suf_ruler = suffix_same_cases \<comment> \<open>provided by Sublist.thy, same as ruler[reversed]\<close>

lemmas suf_ruler_equal = ruler_equal[reversed] and
    suf_ruler_comp = ruler_comp[reversed] and
    ruler_suf = ruler_pref[reversed] and
    suf_prod_short = pref_prod_short[reversed] and
    suf_prod_short' = pref_prod_short'[reversed] and
    suf_prod_cancel = pref_prod_cancel[reversed] and
    suf_prod_cancel' = pref_prod_cancel'[reversed] and
    suf_prod_suf_short = pref_prod_pref_short[reversed] and
    suf_prod_suf = pref_prod_pref[reversed] and
    suf_prod_suf' = pref_prod_pref'[reversed, unfolded rassoc] and
    suf_prolong = pref_prolong[reversed] and
    suf_prolong' = pref_prolong'[reversed, unfolded rassoc] and
    suf_prolong_comp = pref_prolong_comp[reversed, unfolded rassoc] and
    suf_prod_long = pref_prod_long[reversed] and
    suf_prod_longer = pref_prod_longer[reversed] and
    suf_keeps_root = pref_keeps_root[reversed] and
    comm_suf_ruler = comm_ruler[reversed]

lemmas comp_sufs_comp = comp_prefs_comp[reversed] and
  suf_comp_not_suf = pref_comp_not_pref[reversed] and
  suf_comp_not_ssuf = pref_comp_not_spref[reversed] and
  (* hd_no_split = last_no_split[reversed] *) (* this is suffix_Cons *)
  suf_comp_ext = comp_ext[reversed] and
  suf_incomp_ext = incomp_ext[reversed] and
  mismatch_suf_incopm = mismatch_incopm[reversed] and
  suf_comp_sym[sym] = pref_comp_sym[reversed]

lemma suf_comp_last_eq: assumes "u \<bowtie>\<^sub>s v" "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>"
    shows "last u = last v"
  using comp_hd_eq[reversed, OF assms] unfolding hd_rev[OF \<open>u \<noteq> \<epsilon>\<close>] hd_rev[OF \<open>v \<noteq> \<epsilon>\<close>].

lemma suf_comp_last_eq': "r \<cdot> u \<bowtie>\<^sub>s s \<cdot> v \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> v \<noteq> \<epsilon> \<Longrightarrow> last u = last v"
  using comp_sufs_comp suf_comp_last_eq  by blast

section "Left and Right Quotient"

text\<open>A useful function of left quotient is given. Note that the function is sometimes undefined.\<close>

definition left_quotient:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"   ("(_\<inverse>\<^sup>>)(_)" [75,74] 74)
  where left_quotient_def[simp]: "left_quotient u v  = (if u \<le>p v then (THE z. u \<cdot> z = v) else undefined)" 
notation (latex output) left_quotient  ("\<^latex>\<open>\\ensuremath{ {\<close>_ \<^latex>\<open>}^{-1} \\cdot {\<close> _ \<^latex>\<open>}}\<close>")

text\<open>Analogously, we define the right quotient.\<close>

definition right_quotient :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  ("(_)(\<^sup><\<inverse>_) " [76,77] 76)
  where right_quotient_def[simp]: "right_quotient u v  = rev ((rev v)\<inverse>\<^sup>>(rev u))"
notation (latex output) right_quotient ("\<^latex>\<open>\\ensuremath{ {\<close>_ \<^latex>\<open>} \\cdot {\<close> _ \<^latex>\<open>}^{-1}}\<close>")

text\<open>Priorities of these operations are as follows:\<close>

lemma "u\<^sup><\<inverse>v\<^sup><\<inverse>w = (u\<^sup><\<inverse>v)\<^sup><\<inverse>w"
  by simp

lemma "u\<inverse>\<^sup>>v\<inverse>\<^sup>>w = u\<inverse>\<^sup>>(v\<inverse>\<^sup>>w)"
  by simp

lemma "u\<inverse>\<^sup>>v\<^sup><\<inverse>w = u\<inverse>\<^sup>>(v\<^sup><\<inverse>w)"
  by simp

lemma "r \<cdot> u\<inverse>\<^sup>>w\<^sup><\<inverse>v \<cdot> s = r \<cdot> (u\<inverse>\<^sup>>w\<^sup><\<inverse>v) \<cdot> s"
  by simp


lemma rq_rev_lq[reversal_rule]: "(rev v)\<^sup><\<inverse>(rev u) = rev (u\<inverse>\<^sup>>v)"
  by simp

lemma lq_rev_rq[reversal_rule]: "(rev v)\<inverse>\<^sup>>rev u = rev (u\<^sup><\<inverse>v)"
  by simp

subsection \<open>Left Quotient\<close>

lemma lqI:  "u \<cdot> z = v \<Longrightarrow> u\<inverse>\<^sup>>v = z"
  by auto

lemma lq_triv[simp]:  "u\<inverse>\<^sup>>(u \<cdot> z) = z"
  using lqI[OF refl].

lemma lq_triv'[simp]:  "u \<cdot> u\<inverse>\<^sup>>(u \<cdot> z) = u \<cdot>z"
  by simp

lemma lq_self[simp]: "u\<inverse>\<^sup>>u = \<epsilon>"     
  by auto

lemma lq_emp[simp]: "\<epsilon>\<inverse>\<^sup>>u = u"  
  by auto       

lemma lq_pref[simp]: "u \<le>p v \<Longrightarrow> u \<cdot> (u\<inverse>\<^sup>>v) = v"
  by auto

lemma lq_the[simp]: "u \<le>p v \<Longrightarrow> (u\<inverse>\<^sup>>v) = (THE z. u \<cdot> z = v)"
  by simp

lemma lq_reassoc: "u \<le>p v \<Longrightarrow> (u\<inverse>\<^sup>>v)\<cdot>w = u\<inverse>\<^sup>>(v\<cdot>w)"
  by auto

lemma lq_trans: "u \<le>p v \<Longrightarrow> v \<le>p w \<Longrightarrow> (u\<inverse>\<^sup>>v) \<cdot> (v\<inverse>\<^sup>>w) = u\<inverse>\<^sup>>w"
  by auto

lemma lq_rq_reassoc_suf: "u \<le>p z \<Longrightarrow> u \<le>s w \<Longrightarrow> w\<cdot>u\<inverse>\<^sup>>z = w\<^sup><\<inverse>u \<cdot> z"
  using lq_pref[reversed]
  by fastforce

lemma lq_ne: "p \<le>p u\<cdot>p \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> p\<inverse>\<^sup>>(u\<cdot>p) \<noteq> \<epsilon>"
  using lq_pref[of p "u \<cdot> p"] by fastforce 

lemma lq_spref: "u <p v \<Longrightarrow> u\<inverse>\<^sup>>v \<noteq> \<epsilon>"
  using lq_pref by auto

lemma lq_suf_suf: "r \<le>p s \<Longrightarrow> (r\<inverse>\<^sup>>s) \<le>s s"
  by auto

lemma lq_len: "r \<le>p s \<Longrightarrow> \<^bold>|r\<^bold>| +  \<^bold>|r\<inverse>\<^sup>>s\<^bold>| = \<^bold>|s\<^bold>|"
  by auto

lemma pref_lq: "u \<le>p v \<Longrightarrow> v \<le>p w \<Longrightarrow> u\<inverse>\<^sup>>v \<le>p u\<inverse>\<^sup>>w"
  by auto

lemma spref_lq: "u \<le>p v \<Longrightarrow> v <p w \<Longrightarrow> u\<inverse>\<^sup>>v <p u\<inverse>\<^sup>>w"
  by force

lemma conjug_lq: "x \<cdot> z = z \<cdot> y \<Longrightarrow> y = z\<inverse>\<^sup>>(x \<cdot> z)"
  by simp

lemma conjug_emp_emp: "p \<le>p u \<cdot> p \<Longrightarrow> p\<inverse>\<^sup>>(u \<cdot> p) = \<epsilon> \<Longrightarrow> u = \<epsilon>"
  using lq_ne by blast 

lemma lq_drop:  "u \<le>p v \<Longrightarrow> u\<inverse>\<^sup>>v = drop \<^bold>|u\<^bold>| v"
  by fastforce

lemma lq_code [code]:
  "left_quotient \<epsilon> v = v" 
  "left_quotient (a#u) \<epsilon> = undefined"
  "left_quotient (a#u) (b#v) = (if a=b then left_quotient u v else undefined)"
  by simp_all

subsection "Right quotient"

lemmas rqI = lqI[reversed] and
  rq_triv = lq_triv[reversed] and
  rq_triv' = lq_triv'[reversed] and
  rq_sefl = lq_self[reversed] and
  rq_emp = lq_emp[reversed] and
  rq_suf = lq_pref[reversed] and
  rq_ssuf = lq_spref[reversed] and
  rq_reassoc = lq_reassoc[reversed] and
  rq_len = lq_len[reversed] and
  rq_trans = lq_trans[reversed] and
  rq_lq_reassoc_suf = lq_rq_reassoc_suf[reversed] and
  rq_ne = lq_ne[reversed] and
  rq_suf_suf = lq_suf_suf[reversed] and
  suf_rq = pref_lq[reversed] and
  ssuf_rq = spref_lq[reversed] and
  conjug_rq = conjug_lq[reversed] and
  conjug_emp_emp' = conjug_emp_emp[reversed] and
  rq_take = lq_drop[reversed]

subsection \<open>Left and right quotients combined\<close>

lemma rev_lq': "r \<le>p s \<Longrightarrow> rev (r\<inverse>\<^sup>>s) = (rev s)\<^sup><\<inverse>(rev r)"
  by auto

lemma pref_rq_suf_lq: "s \<le>s u \<Longrightarrow> r \<le>p (u\<^sup><\<inverse>s) \<Longrightarrow> s \<le>s (r\<inverse>\<^sup>>u)"
  using lq_reassoc[of r "u\<^sup><\<inverse>s" s] rq_suf[of s u] triv_suf[of s "r\<inverse>\<^sup>>u\<^sup><\<inverse>s"]
  by presburger

lemmas suf_lq_pref_rq = pref_rq_suf_lq[reversed]

lemma "w\<cdot>s = v \<Longrightarrow> v\<^sup><\<inverse>s = w" using rqI.

lemma lq_rq_assoc: "s \<le>s u \<Longrightarrow> r \<le>p (u\<^sup><\<inverse>s) \<Longrightarrow> (r\<inverse>\<^sup>>u)\<^sup><\<inverse>s = r\<inverse>\<^sup>>(u\<^sup><\<inverse>s)"
  using lq_reassoc[of r "u\<^sup><\<inverse>s" s] rq_suf[of s u] rqI[of "r\<inverse>\<^sup>>u\<^sup><\<inverse>s" s "r\<inverse>\<^sup>>u"]
  by argo

lemmas rq_lq_assoc = lq_rq_assoc[reversed]

lemma lq_prod: "u \<le>p v\<cdot>u \<Longrightarrow> u \<le>p w \<Longrightarrow>  u\<inverse>\<^sup>>(v\<cdot>u)\<cdot>u\<inverse>\<^sup>>w = u\<inverse>\<^sup>>(v\<cdot>w)"
  using lq_reassoc[of u "v \<cdot> u" "u\<inverse>\<^sup>>w"] lq_rq_reassoc_suf[of u w "v \<cdot> u", unfolded rq_triv[of v u]]
  by auto

lemmas rq_prod = lq_prod[reversed]

section \<open>Equidivisibility\<close>

text\<open>Equidivisibility is the following property: if
\[
xy = uv,
\]
then there exists a word $t$ such that $xt = u$ and $ty = v$, or $ut = x$ and $y = tv$.
For monoids over words, this property is equivalent to the freeness of the monoid.
As the monoid of all words is free, we can prove that it is equidivisible.
Related lemmas based on this property follow.
\<close>


lemma eqd: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> \<exists> t. x \<cdot> t = u \<and> t \<cdot> v = y"
  by (simp add: append_eq_conv_conj)

lemma eqdE: assumes "x \<cdot> y = u \<cdot> v" and "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|" 
  obtains t where "x \<cdot> t = u" and "t \<cdot> v = y"
  using eqd[OF assms] by blast

lemma eqdE': assumes "x \<cdot> y = u \<cdot> v" and "\<^bold>|v\<^bold>| \<le> \<^bold>|y\<^bold>|" 
  obtains t where "x \<cdot> t = u" and "t \<cdot> v = y"
  using eqdE[OF assms(1)] lenarg[OF assms(1), unfolded length_append] assms(2)
  by auto 

lemma eqd_pref: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> x \<cdot> (x\<inverse>\<^sup>>u) = u \<and> (x\<inverse>\<^sup>>u) \<cdot> v = y"
  using eqd lq_triv by blast

lemma eqd_prefE: assumes "x \<cdot> y = u \<cdot> v" and  "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|" 
  obtains t where "x \<cdot> t = u" and  "t \<cdot> v = y"
  using eqd_pref assms by blast

lemma eqd_pref1: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> x \<cdot> (x\<inverse>\<^sup>>u) = u"
  using eqd_pref by blast

lemma eqd_pref2: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> (x\<inverse>\<^sup>>u) \<cdot> v = y"
  using eqd_pref by blast

lemma eqd_equal: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| = \<^bold>|u\<^bold>| \<Longrightarrow> x = u \<and> y = v"
  by simp 

lemma pref_equal: "u \<le>p v \<cdot> w \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u = v"
  by simp

lemma eqd_equal_suf: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|y\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> x = u \<and> y = v"
  by simp 

lemma eqd_comp: assumes "x \<cdot> y = u \<cdot> v" shows "x \<bowtie> u"
  using le_cases[of "\<^bold>|x\<^bold>|" "\<^bold>|u\<^bold>|" "x \<bowtie> u"] 
    eqd_pref1[of x y u v, THEN prefI[of x "x\<inverse>\<^sup>>u" u], OF assms] 
    eqd_pref1[of u v x y, THEN prefI[of u "u\<inverse>\<^sup>>x" x], OF assms[symmetric]] by auto

\<comment> \<open>not equal to eqd\_pref1[reversed]\<close>
lemma eqd_suf1: "x \<cdot> y = u \<cdot> v \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>| \<Longrightarrow> (y\<^sup><\<inverse>v)\<cdot>v = y"
  using eqd_pref2 rq_triv by blast

\<comment> \<open>not equal to eqd\_pref2[reversed]\<close> 
lemma eqd_suf2: assumes "x \<cdot> y = u \<cdot> v" "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|" shows "x \<cdot> (y\<^sup><\<inverse>v) = u"
  using rq_reassoc[OF sufI[OF eqd_suf1[OF \<open>x \<cdot> y = u \<cdot> v\<close> \<open>\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>]], of x, unfolded \<open>x \<cdot> y = u \<cdot> v\<close> rq_triv[of u v]]. 

\<comment> \<open> not equal to eqd\_pref[reversed] \<close>
lemma eqd_suf: assumes "x \<cdot> y = u \<cdot> v" and "\<^bold>|x\<^bold>| \<le> \<^bold>|u\<^bold>|" 
  shows "(y\<^sup><\<inverse>v)\<cdot>v = y \<and> x \<cdot> (y\<^sup><\<inverse>v) = u"
  using eqd_suf1[OF assms] eqd_suf2[OF assms] by blast 

section \<open>Longest common prefix\<close>

notation longest_common_prefix  ("_ \<and>\<^sub>p _" [61,62] 64) \<comment> \<open>provided by Sublist.thy\<close>

lemmas lcp_simps = longest_common_prefix.simps \<comment> \<open>provided by Sublist.thy\<close>

lemma lcp_sym: "u \<and>\<^sub>p v = v \<and>\<^sub>p u" 
  by (induct u v rule: list_induct2') auto

 \<comment> \<open>provided by Sublist.thy\<close>
lemmas lcp_pref = longest_common_prefix_prefix1
lemmas lcp_pref' = longest_common_prefix_prefix2
lemmas pref_pref_lcp = longest_common_prefix_max_prefix

lemma lcp_take_eq: "take (\<^bold>|u \<and>\<^sub>p v\<^bold>|) u = take (\<^bold>|u \<and>\<^sub>p v\<^bold>|) v"
  using pref_take[OF lcp_pref[of u v]] pref_take[OF lcp_pref'[of u v]] by simp

lemma lcp_pref_conv: "u \<and>\<^sub>p v = u \<longleftrightarrow> u \<le>p v"
  unfolding prefix_order.eq_iff[of "u \<and>\<^sub>p v" u]
  using lcp_pref'[of u v] 
    lcp_pref[of u v] longest_common_prefix_max_prefix[OF self_pref[of u], of v]
  by auto

lemma pref_lcp_pref: "w \<le>p u \<and>\<^sub>p v \<Longrightarrow> w \<le>p u"
  using lcp_pref pref_trans by blast 

lemma pref_lcp_pref': "w \<le>p u \<and>\<^sub>p v \<Longrightarrow> w \<le>p v"
  using pref_lcp_pref[of w v u, unfolded lcp_sym[of v u]].

lemma lcp_self[simp]: "w \<and>\<^sub>p w = w"
  using lcp_pref_conv by blast

lemma lcp_eq: "\<^bold>|u\<^bold>| = \<^bold>|u \<and>\<^sub>p v\<^bold>| \<Longrightarrow> u = u \<and>\<^sub>p v"
  using  long_pref[OF lcp_pref, of u v] by auto                                       

lemma lcp_len: "\<^bold>|u\<^bold>| \<le> \<^bold>|u \<and>\<^sub>p v\<^bold>| \<Longrightarrow> u \<le>p v"
  using long_pref[OF lcp_pref, of u v] unfolding lcp_pref_conv[symmetric]. 

lemma lcp_len': "\<not> u \<le>p v \<Longrightarrow> \<^bold>|u \<and>\<^sub>p v\<^bold>| < \<^bold>|u\<^bold>|"
  using not_le_imp_less[OF contrapos_nn[OF _ lcp_len]].

lemma incomp_lcp_len: assumes "\<not> u \<bowtie> v" shows "\<^bold>|u \<and>\<^sub>p v\<^bold>| < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|"
  unfolding min_less_iff_conj[of "\<^bold>|u \<and>\<^sub>p v\<^bold>|" "\<^bold>|u\<^bold>|" "\<^bold>|v\<^bold>|"]
  using assms lcp_len'[of u v] lcp_len'[of v u, folded lcp_sym[of u v]]  
    min_less_iff_conj[of "\<^bold>|u \<and>\<^sub>p v\<^bold>|" "\<^bold>|u\<^bold>|" "\<^bold>|v\<^bold>|"] by blast

lemma lcp_ext_right [case_names comp non_comp]: obtains  "r \<bowtie> r'" | "(r \<cdot> u) \<and>\<^sub>p (r' \<cdot> v) = r \<and>\<^sub>p r'"
proof-
  have "\<not> r \<bowtie> r' \<Longrightarrow> r \<cdot> u \<and>\<^sub>p r' \<cdot> v = r \<and>\<^sub>p r'"
    by (induct r r' rule: list_induct2', simp+)
  thus ?thesis
    using that(1) that(2) by linarith
qed

lemma lcp_same_len: "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>| \<Longrightarrow> u \<noteq> v \<Longrightarrow> u \<and>\<^sub>p v = u \<cdot> w \<and>\<^sub>p v \<cdot> w'"
  using lcp_ext_right[of u v _ w w'] pref_comp_eq[of u v] by argo

lemma lcp_mismatch: "\<^bold>|u \<and>\<^sub>p v\<^bold>| < \<^bold>|u\<^bold>| \<Longrightarrow> \<^bold>|u \<and>\<^sub>p v\<^bold>| < \<^bold>|v\<^bold>| \<Longrightarrow> u! \<^bold>|u \<and>\<^sub>p v\<^bold>| \<noteq> v! \<^bold>|u \<and>\<^sub>p v\<^bold>|"
  by (induct u v rule: list_induct2') auto

lemma lcp_mismatch': assumes "\<not> u \<bowtie> v" shows "u! \<^bold>|u \<and>\<^sub>p v\<^bold>| \<noteq> v! \<^bold>|u \<and>\<^sub>p v\<^bold>|"
  using incomp_lcp_len[OF assms, unfolded min_less_iff_conj] lcp_mismatch
  by blast

lemma lcp_ext_left: "(z \<cdot> u) \<and>\<^sub>p (z \<cdot> v) = z \<cdot> (u \<and>\<^sub>p v)"
  by (induct z) auto

lemma lcp_first_letters: "u!0 \<noteq> v!0 \<Longrightarrow> u \<and>\<^sub>p v = \<epsilon>"
  by (induct u v rule: list_induct2') auto

lemma lcp_first_mismatch: "a \<noteq> b \<Longrightarrow> w \<cdot> [a] \<cdot> u \<and>\<^sub>p w \<cdot> [b] \<cdot> v  = w"
  by (simp add: lcp_ext_left)

lemma lcp_first_mismatch': "a \<noteq> b \<Longrightarrow> u \<cdot> [a] \<and>\<^sub>p u \<cdot> [b] = u"
  using lcp_first_mismatch[of a b u \<epsilon> \<epsilon>] by simp

lemma lcp_mismatch_shorter: assumes "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|" "x \<noteq> y" shows "u \<cdot> [x] \<and>\<^sub>p v \<cdot> [y] = u \<and>\<^sub>p v"
  by (cases "u = v") 
    (simp add: lcp_self[of v]  lcp_first_mismatch'[OF \<open>x \<noteq> y\<close>, of v],
    use lcp_same_len[OF \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close>, of "[x]" "[y]"] in auto)

lemma lcp_rulers: "r \<le>p s \<Longrightarrow> r' \<le>p s' \<Longrightarrow> (r \<bowtie> r' \<or> r \<and>\<^sub>p r' = s \<and>\<^sub>p s')"
  using lcp_ext_right prefD[of r s] prefD[of r' s'] by metis

lemma pref_pref_lcp': "w \<le>p r \<Longrightarrow> w' \<le>p s \<Longrightarrow> w \<and>\<^sub>p w' \<le>p (r \<and>\<^sub>p s)"
  using pref_pref_lcp lcp_pref lcp_sym pref_trans by metis

lemma lcp_distinct_hd: "hd u \<noteq> hd v \<Longrightarrow> u \<and>\<^sub>p v = \<epsilon>"
proof-
  assume "hd u \<noteq> hd v"
  hence "(u \<noteq> \<epsilon> \<and> v \<noteq> \<epsilon>) \<Longrightarrow> hd u \<noteq> hd v \<Longrightarrow>  u \<and>\<^sub>p v = \<epsilon>"
    by (simp add: lcp_first_letters hd_conv_nth)
  moreover have "u = \<epsilon> \<or> v = \<epsilon> \<Longrightarrow>  u \<and>\<^sub>p v = \<epsilon>"
    using lcp_pref' by auto 
  ultimately show ?thesis using \<open>hd u \<noteq> hd v\<close> by blast
qed   

lemma lcp_lenI: assumes "i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|" and "take i u = take i v" and "u!i \<noteq> v!i" 
  shows "i = \<^bold>|u \<and>\<^sub>p v\<^bold>|" 
proof-
  have u: "take i u \<cdot> [u ! i] \<cdot> (drop (Suc i) u) = u" 
    using \<open>i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|\<close> id_take_nth_drop[of i u] by simp  
  have v: "take i u \<cdot> [v ! i] \<cdot> drop (Suc i) v = v" using \<open>i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|\<close>
    unfolding \<open>take i u = take i v\<close> using id_take_nth_drop by fastforce  
  from lcp_first_mismatch[OF \<open>u!i \<noteq> v!i\<close>, of "take i u" "drop (Suc i) u" "drop (Suc i) v", unfolded u v]
  have "u \<and>\<^sub>p v = take i u".
  thus ?thesis
    using \<open>i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|\<close> by auto 
qed

lemma lcp_prefs: "\<^bold>|u \<cdot> w \<and>\<^sub>p v \<cdot> w'\<^bold>| < \<^bold>|u\<^bold>| \<Longrightarrow> \<^bold>|u \<cdot> w \<and>\<^sub>p v \<cdot> w'\<^bold>| < \<^bold>|v\<^bold>| \<Longrightarrow> u \<and>\<^sub>p v = u \<cdot> w \<and>\<^sub>p v \<cdot> w'"
  by (induct u v rule: list_induct2') auto

subsection "Longest common prefix and prefix comparability"

lemma lexord_cancel_right: "(u \<cdot> z, v \<cdot> w) \<in> lexord r \<Longrightarrow> \<not> u \<bowtie> v \<Longrightarrow> (u,v) \<in> lexord r"
  by (induction rule: list_induct2', simp+, auto)

lemma lcp_ruler: "r \<bowtie> w1 \<Longrightarrow> r \<bowtie> w2 \<Longrightarrow> \<not> w1 \<bowtie> w2 \<Longrightarrow> r \<le>p w1 \<and>\<^sub>p w2"
  unfolding prefix_comparable_def
  by (meson pref_pref_lcp pref_trans ruler)

lemma comp_monotone: "w \<bowtie> r  \<Longrightarrow> u \<le>p w \<Longrightarrow> u \<bowtie> r"
  using pref_trans[of u w r] ruler[of u w r] by blast

lemma comp_monotone': "w \<bowtie> r  \<Longrightarrow> w \<and>\<^sub>p w' \<bowtie> r"
  using comp_monotone[of w r "w \<and>\<^sub>p w'", OF _ longest_common_prefix_prefix1].

lemma double_ruler: assumes "w \<bowtie> r" and "w' \<bowtie> r'" and "\<not> r \<bowtie> r'" 
  shows "w \<and>\<^sub>p w' \<le>p r \<and>\<^sub>p r'"
  using comp_monotone'[OF \<open>w' \<bowtie> r'\<close>, of w]  unfolding lcp_sym[of w' w]
  using lcp_ruler[OF comp_monotone'[OF \<open>w \<bowtie> r\<close>, of w'] _ \<open>\<not> r \<bowtie> r'\<close>] by blast

lemma pref_comp_ruler: assumes "w \<bowtie> u \<cdot> [x]" and "w \<bowtie> v \<cdot> [y]" and "x \<noteq> y" and "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|" 
  shows "w \<le>p u \<and> w \<le>p v"
  using double_ruler[OF \<open>w \<bowtie> u \<cdot> [x]\<close> \<open>w \<bowtie> v \<cdot> [y]\<close> mismatch_incopm[OF \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close> \<open>x \<noteq> y\<close>]] unfolding lcp_self[of w] lcp_mismatch_shorter[OF \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close> \<open>x \<noteq> y\<close>]
  using pref_lcp_pref pref_lcp_pref' by blast

lemmas suf_comp_ruler = pref_comp_ruler[reversed]

section "Mismatch"

text \<open>The first pair of letters on which two words/lists disagree\<close>

fun mismatch_pair :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a \<times> 'a)" where
  "mismatch_pair \<epsilon> v = (\<epsilon>!0, v!0)" |
  "mismatch_pair v \<epsilon> = (v!0, \<epsilon>!0)" |
  "mismatch_pair (a#u) (b#v) = (if a=b then mismatch_pair u v else (a,b))"

text \<open>Alternatively, mismatch pair may be defined using the longest common prefix as follows.\<close>

lemma mismatch_pair_lcp: "mismatch_pair u v = (u!\<^bold>|u\<and>\<^sub>pv\<^bold>|,v!\<^bold>|u\<and>\<^sub>pv\<^bold>|)"
proof(induction u v rule: mismatch_pair.induct, simp+)
qed

text \<open>For incomparable words the pair is out of diagonal.\<close>

lemma incomp_neq: "\<not> u \<bowtie> v \<Longrightarrow> (mismatch_pair u v) \<notin> Id"
  unfolding mismatch_pair_lcp by (simp add: lcp_mismatch')

lemma mismatch_ext_left: "\<not> u \<bowtie> v \<Longrightarrow> mismatch_pair u v = mismatch_pair (p\<cdot>u) (p\<cdot>v)" 
  unfolding mismatch_pair_lcp by (simp add: lcp_ext_left)

lemma mismatch_ext_right: assumes  "\<not> u \<bowtie> v" 
  shows "mismatch_pair u v = mismatch_pair (u\<cdot>z) (v\<cdot>w)"
proof- 
  have less1: "\<^bold>|u \<and>\<^sub>p v\<^bold>| < \<^bold>|u\<^bold>|" and less2: "\<^bold>|v \<and>\<^sub>p u\<^bold>| < \<^bold>|v\<^bold>|"
    using lcp_len'[of u v] lcp_len'[of v u] assms  by auto 
  show ?thesis 
    unfolding mismatch_pair_lcp unfolding pref_index[OF triv_pref less1, of z]  pref_index[OF triv_pref less2, of w, unfolded lcp_sym[of v]]
    using assms lcp_ext_right[of u v _ z w] by metis
qed    

lemma mismatchI: "\<not> u \<bowtie> v \<Longrightarrow> i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>| \<Longrightarrow> take i u = take i v \<Longrightarrow> u!i \<noteq> v!i
   \<Longrightarrow> mismatch_pair u v = (u!i,v!i)"
  unfolding mismatch_pair_lcp using lcp_lenI by blast    

text \<open>For incomparable words, the mismatch letters work in a similar way as the lexicographic order\<close>

lemma mismatch_lexord: assumes "\<not> u \<bowtie> v" and "mismatch_pair u v \<in> r"    
  shows "(u,v) \<in> lexord r"
  unfolding lexord_take_index_conv mismatch_pair_lcp
  using  \<open>mismatch_pair u v \<in> r\<close>[unfolded mismatch_pair_lcp]
    incomp_lcp_len[OF assms(1)] lcp_take_eq by blast

text \<open>However, the equivalence requires r to be irreflexive. 
(Due to the definition of lexord which is designed for irreflexive relations.)\<close>

lemma lexord_mismatch: assumes "\<not> u \<bowtie> v" and "irrefl r" 
  shows "mismatch_pair u v \<in> r \<longleftrightarrow> (u,v) \<in> lexord r"
proof
  assume "(u,v) \<in> lexord r"
  obtain i where  "i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|" and  "take i u = take i v" and "(u ! i, v ! i) \<in> r"
    using \<open>(u,v) \<in> lexord r\<close>[unfolded lexord_take_index_conv] \<open>\<not> u \<bowtie> v\<close> pref_take_conv by blast
  have "u!i \<noteq> v!i"
    using  \<open>irrefl r\<close>[unfolded irrefl_def] \<open>(u ! i, v ! i) \<in> r\<close> by fastforce
  from \<open>(u ! i, v ! i) \<in> r\<close>[folded mismatchI[OF \<open>\<not> u \<bowtie> v\<close> \<open>i < min \<^bold>|u\<^bold>| \<^bold>|v\<^bold>|\<close> \<open>take i u = take i v\<close> \<open>u!i \<noteq> v!i\<close>]]
  show  "mismatch_pair u v \<in> r".
next
  from mismatch_lexord[OF \<open>\<not> u \<bowtie> v\<close>]
  show "mismatch_pair u v \<in> r \<Longrightarrow> (u, v) \<in> lexord r".
qed

section "Factor properties"

lemma rev_fac[reversal_rule]: "rev u \<le>f rev v \<longleftrightarrow> u \<le>f v"
  using Sublist.sublist_rev.

lemma fac_pref: "u \<le>f v \<equiv> \<exists> p. p \<cdot> u \<le>p v"
  by simp

lemma fac_pref_suf: "u \<le>f v \<Longrightarrow> \<exists> p. p \<le>p v \<and> u \<le>s p"
  using sublist_altdef by blast

lemma pref_suf_fac: "r \<le>p v \<Longrightarrow> u \<le>s r \<Longrightarrow> u \<le>f v"
  using sublist_altdef by blast

lemmas 
  fac_suf = fac_pref[reversed] and
  fac_suf_pref = fac_pref_suf[reversed] and
  suf_pref_fac = pref_suf_fac[reversed]

lemma suf_pref_eq: "s \<le>s p \<Longrightarrow> p \<le>p s \<Longrightarrow> p = s"
  using sublist_order.eq_iff by blast

lemma fac_triv': assumes  "p\<cdot>x\<cdot>q = x" shows "q = \<epsilon>"
  using prefI[of "p\<cdot>x" q "p\<cdot>x\<cdot>q"] sufI[of \<epsilon> "p\<cdot>x\<cdot>q" "x", THEN suf_ext[of "p\<cdot>x\<cdot>q" x p]] 
    suf_pref_eq[of x "p\<cdot>x"] self_append_conv[of "p\<cdot>x" q] 
  unfolding assms append_Nil rassoc 
  by blast

lemma fac_triv: "p\<cdot>x\<cdot>q = x \<Longrightarrow> p = \<epsilon>"
  using fac_triv' by force 

lemmas 
  suf_fac = suffix_imp_sublist and
  pref_fac = prefix_imp_sublist

lemma fac_Cons_E: assumes "u \<le>f (a#v)"
  obtains "u \<le>p (a#v)" | "u \<le>f v"
  using assms[unfolded sublist_Cons_right]
  by fast

lemmas
  fac_snoc_E = fac_Cons_E[reversed]

section "Power and its properties"

text\<open>Word powers are often investigated in Combinatorics on Words.
We thus interpret words as @{term monoid_mult} and adopt a notation for the word power.
\<close>


declare power.power.simps [code] 

interpretation  monoid_mult "\<epsilon>" "append"
   by standard simp+

notation power (infixr "\<^sup>@" 80)

\<comment> \<open>inherited power properties\<close>

lemma pow_zero [simp]:  "u\<^sup>@0 = \<epsilon>"
  using power.power_0.

lemma emp_pow: "\<epsilon>\<^sup>@n = \<epsilon>"
  using power_one.

lemma pow_Suc_list: "u\<^sup>@(Suc n) = u \<cdot> u\<^sup>@n"
  using power.power_Suc.

lemma pow_commutes_list: "u\<^sup>@n \<cdot> u = u \<cdot> u\<^sup>@n" 
  using power_commutes.

lemma pow_add_list: "x\<^sup>@(a+b) = x\<^sup>@a\<cdot>x\<^sup>@b"
  using power_add.

lemma pow_Suc2_list: "u\<^sup>@Suc n = u\<^sup>@n \<cdot> u"
  using power_Suc2.

lemma pow_eq_if_list: "p\<^sup>@m = (if m = 0 then \<epsilon> else p \<cdot> p\<^sup>@(m-1))"
  using power_eq_if.

lemma pow_one_id: "u\<^sup>@1 = u" 
  using power_one_right.

lemma pow2_list: "u\<^sup>@2 = u \<cdot> u"
  using power2_eq_square.

lemma comm_add_exp: "u \<cdot> v = v \<cdot> u \<Longrightarrow> u \<^sup>@ n \<cdot> v = v \<cdot> u \<^sup>@ n"
  using power_commuting_commutes.

lemma pow_mult_list: "u\<^sup>@(m*n) = (u\<^sup>@m)\<^sup>@n"
  using power_mult.

lemma pow_rev_emp_conv[reversal_rule]: "power.power (rev \<epsilon>) (\<cdot>) = (\<^sup>@)"
  by simp

\<comment> \<open>more power properties\<close>

lemma zero_exp: "n = 0 \<Longrightarrow> r\<^sup>@n = \<epsilon>"
  by simp

lemma nemp_pow[elim]: "t\<^sup>@m \<noteq> \<epsilon> \<Longrightarrow> m \<noteq> 0"
  using zero_exp by blast

lemma nemp_pow'[elim]: "t\<^sup>@m \<noteq> \<epsilon> \<Longrightarrow> t \<noteq> \<epsilon>"
  using emp_pow by auto

lemma sing_pow:"i < m \<Longrightarrow> ([a]\<^sup>@m) ! i = a"
  by (induct i m rule: diff_induct) auto

lemma pow_is_concat_replicate: "u\<^sup>@n = concat (replicate n u)"
  by (induct n) auto

lemma pow_slide: "u \<cdot> (v \<cdot> u)\<^sup>@n  \<cdot> v = (u \<cdot> v)\<^sup>@(Suc n)"
  by (induct n) simp+

lemma pop_pow_one:  "m \<noteq> 0 \<Longrightarrow> r\<^sup>@m = r \<cdot> r\<^sup>@(m-1)"
  by (simp add: pow_eq_if_list)

lemma hd_pow: assumes "n \<noteq> 0" shows "hd(u\<^sup>@n) = hd u"
  unfolding pop_pow_one[OF \<open>n \<noteq> 0\<close>] using  hd_append2 by (cases "u = \<epsilon>", simp)   


lemma pop_pow: "m \<le> k \<Longrightarrow>u\<^sup>@m \<cdot> u\<^sup>@(k-m) =  u\<^sup>@k"
  using le_add_diff_inverse pow_add_list  by metis 

lemma pop_pow_cancel: "u\<^sup>@k \<cdot> v = u\<^sup>@m \<cdot> w \<Longrightarrow> m \<le> k \<Longrightarrow> u\<^sup>@(k-m) \<cdot> v = w"
  using  lassoc pop_pow[of m k u] same_append_eq[of "u\<^sup>@m" "u\<^sup>@(k-m)\<cdot>v" w, unfolded lassoc] by argo 

lemma pow_comm: "t\<^sup>@k \<cdot> t\<^sup>@m = t\<^sup>@m \<cdot> t\<^sup>@k"
  unfolding pow_add_list[symmetric] add.commute[of k]..

lemma comm_add_exps: assumes "r \<cdot> u = u \<cdot> r" shows "r\<^sup>@m \<cdot> u\<^sup>@k = u\<^sup>@k \<cdot> r\<^sup>@m"
  using comm_add_exp[OF comm_add_exp[OF assms, symmetric], symmetric].

lemma rev_pow: "rev (x\<^sup>@m) = (rev x)\<^sup>@m"
  by (induct m, simp, simp add: pow_commutes_list)

lemmas [reversal_rule] = rev_pow[symmetric]

lemmas pow_eq_if_list' = pow_eq_if_list[reversed] and
  pop_pow_one' = pop_pow_one[reversed] and
  pop_pow' = pop_pow[reversed] and
  pop_pow_cancel' = pop_pow_cancel[reversed]

lemma pow_len:  "\<^bold>|u\<^sup>@k\<^bold>| = k * \<^bold>|u\<^bold>|" 
  by (induct k) simp+

lemma eq_pow_exp: assumes "u \<noteq> \<epsilon>" shows "u\<^sup>@k = u\<^sup>@m \<longleftrightarrow> k = m"
proof
  assume "k = m" thus "u\<^sup>@k = u\<^sup>@m" by simp
next
  assume "u\<^sup>@k = u\<^sup>@m" 
  from lenarg[OF this, unfolded pow_len mult_cancel2]
  show "k = m"
  using \<open>u \<noteq> \<epsilon>\<close>[folded length_0_conv] by blast
qed


lemma nemp_emp_power: assumes "u \<noteq> \<epsilon>" shows "u\<^sup>@m = \<epsilon> \<longleftrightarrow> m = 0"
   using  eq_pow_exp[OF assms]  by fastforce

lemma nonzero_pow_emp: assumes "m \<noteq> 0" shows "u\<^sup>@m = \<epsilon> \<longleftrightarrow>  u = \<epsilon>"
  by (meson assms nemp_emp_power nemp_pow')

lemma pow_eq_eq:
  assumes "u\<^sup>@k = v\<^sup>@k" and "k \<noteq> 0"
  shows "u = v"
proof-
  have "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
    using lenarg[OF \<open>u\<^sup>@k = v\<^sup>@k\<close>, unfolded pow_len] \<open>k \<noteq> 0\<close> by simp
  from eqd_equal[of u "u\<^sup>@(k-1)" v "v\<^sup>@(k-1)", OF _ this] 
  show ?thesis
      using \<open>u\<^sup>@k = v\<^sup>@k\<close> unfolding pop_pow_one[OF \<open>k \<noteq> 0\<close>] by blast
qed

lemma sing_pow_empty: "[a]\<^sup>@n = \<epsilon> \<longleftrightarrow> n = 0"
  by (simp add: nemp_emp_power)

lemma sing_pow_lists: "a \<in> A \<Longrightarrow> [a]\<^sup>@n \<in> lists A"
  by (induct n, auto)

lemma long_power: "r \<noteq> \<epsilon> \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|r\<^sup>@\<^bold>|x\<^bold>|\<^bold>|"
  unfolding pow_len[of r "\<^bold>|x\<^bold>|"] using nemp_pos_len by auto

lemma long_power': "r \<noteq> \<epsilon> \<Longrightarrow> \<^bold>|x\<^bold>| < \<^bold>|r\<^sup>@(Suc \<^bold>|x\<^bold>|)\<^bold>|"
  unfolding pow_Suc_list length_append 
  by (simp add: long_power add_strict_increasing)  

lemma long_pow_exp: "r \<noteq> \<epsilon> \<Longrightarrow> m \<le> \<^bold>|r\<^sup>@m\<^bold>|"
  unfolding pow_len[of r m] using nemp_pos_len[of r] by simp  

lemma long_pow_ex: assumes "r \<noteq> \<epsilon>" obtains n where  "m \<le> \<^bold>|r\<^sup>@n\<^bold>|" and "n \<noteq> 0"
proof-
  obtain x :: "'a list" where "\<^bold>|x\<^bold>| = m"
    using Ex_list_of_length by auto 
  show thesis
    using that[of m, OF long_power[OF \<open>r \<noteq> \<epsilon>\<close>, of x, unfolded \<open>\<^bold>|x\<^bold>| = m\<close>]] that[of "Suc 1"] by auto
qed

lemma pref_pow_ext: "x \<le>p r\<^sup>@k \<Longrightarrow> x \<le>p r\<^sup>@Suc k"
  using pref_trans[OF _ prefI[OF pow_Suc2_list[symmetric]]].

lemma pref_pow_ext': "u \<le>p r\<^sup>@k \<Longrightarrow> u \<le>p r \<cdot> r\<^sup>@k"
  using pref_pow_ext[unfolded pow_Suc_list].

lemma pref_pow_root_ext: "x \<le>p r\<^sup>@k \<Longrightarrow> r \<cdot> x \<le>p r\<^sup>@Suc k"
  by simp

lemma pref_prod_root: "u \<le>p r\<^sup>@k \<Longrightarrow> u \<le>p r \<cdot> u"
  using pref_pow_ext'[THEN pref_prod_pref].

lemma pref_exps_pow:  "k \<le> l \<Longrightarrow> r\<^sup>@k \<le>p r\<^sup>@l"
  using leI pop_pow[of k l r] by blast

lemma pref_exp_le: assumes "u \<noteq> \<epsilon>" "u\<^sup>@m \<le>p u\<^sup>@n" shows "m \<le> n"
  using mult_cancel_le[OF nemp_len[OF \<open>u \<noteq> \<epsilon>\<close>], of m n] 
    prefix_length_le[OF \<open>u\<^sup>@m \<le>p u\<^sup>@n\<close>, unfolded pow_len[of u m] pow_len[of u n]]
  by blast       

lemmas
    suf_pow_ext = pref_pow_ext[reversed] and
    suf_pow_ext'= pref_pow_ext'[reversed] and
    suf_pow_root_ext = pref_pow_root_ext[reversed] and
    suf_prod_root = pref_prod_root[reversed] and
    suf_exps_pow = pref_exps_pow[reversed] and
    suf_exp_le = pref_exp_le[reversed]

lemma comm_common_power: assumes "r \<cdot> u = u \<cdot> r" shows "r\<^sup>@\<^bold>|u\<^bold>| = u\<^sup>@\<^bold>|r\<^bold>|"
  using eqd_equal[OF comm_add_exps[OF \<open>r \<cdot> u = u \<cdot> r\<close>], of "\<^bold>|u\<^bold>|" "\<^bold>|r\<^bold>|"]
  unfolding pow_len by fastforce   

lemma one_generated_list_power: "u \<in> lists {x} \<Longrightarrow> \<exists>k. concat u = x\<^sup>@k"
proof(induction u)
  case Nil
  then show ?case
    by (simp add: pow_is_concat_replicate)
next
  case (Cons a u)
  then show ?case
    unfolding Cons_in_lists_iff concat.simps(2) 
    using singletonD[of a x] pow_Suc_list[of a] by metis
qed

lemma pow_lists: "0 < k \<Longrightarrow> u\<^sup>@k \<in> lists B \<Longrightarrow> u \<in> lists B"
  by (simp add: pow_eq_if_list)

lemma concat_morph_power: "xs \<in> lists B \<Longrightarrow> xs = ts\<^sup>@k \<Longrightarrow> concat ts\<^sup>@k = concat xs"
  by (induct k arbitrary: xs ts) simp+

lemma pref_not_idem:  "z \<noteq> \<epsilon> \<Longrightarrow> z \<noteq> x \<Longrightarrow> z \<cdot> x\<^sup>@k \<noteq> x"
  using fac_triv by (cases k, simp, auto)

lemma per_exp_pref: "u \<le>p r \<cdot> u \<Longrightarrow> u \<le>p r\<^sup>@k \<cdot> u"
proof(induct k, simp)
  case (Suc k) show ?case
    unfolding pow_Suc_list rassoc
    using Suc.hyps Suc.prems pref_prolong by blast
qed

lemmas
  suf_not_idem =  pref_not_idem[reversed] and
  per_exp_suf = per_exp_pref[reversed]

lemma hd_sing_power: "k \<noteq> 0 \<Longrightarrow> hd ([a]\<^sup>@k) = a"
  by (induction k) simp+

lemma root_pref_cancel: assumes "t\<^sup>@m \<cdot> y = t\<^sup>@k" shows "y = t\<^sup>@(k - m)"
  using lqI[of "t\<^sup>@m" "t\<^sup>@(k-m)" "t\<^sup>@k"]  unfolding lqI[OF \<open>t\<^sup>@m \<cdot> y = t\<^sup>@k\<close>]
  using  nat_le_linear[of m k] pop_pow[of m k t] diff_is_0_eq[of k m]   append.right_neutral[of "t\<^sup>@k"] pow_zero[of t] 
    pref_antisym[of "t\<^sup>@m" "t\<^sup>@k", OF prefI[OF  \<open>t\<^sup>@m \<cdot> y = t\<^sup>@k\<close>] pref_exps_pow[of k m t]] 
  by presburger

lemmas root_suf_cancel = root_pref_cancel[reversed]

lemma index_pow_mod: "i < \<^bold>|r\<^sup>@k\<^bold>| \<Longrightarrow> (r\<^sup>@k)!i = r!(i mod \<^bold>|r\<^bold>|)"
proof(induction k)
  have aux:  "\<^bold>|r\<^sup>@(Suc l)\<^bold>| = \<^bold>|r\<^sup>@l\<^bold>| + \<^bold>|r\<^bold>|" for l
    by simp
  have aux1: "\<^bold>|(r\<^sup>@l)\<^bold>| \<le> i \<Longrightarrow> i < \<^bold>|r\<^sup>@l\<^bold>| + \<^bold>|r\<^bold>| \<Longrightarrow>  i mod \<^bold>|r\<^bold>| = i -  \<^bold>|r\<^sup>@l\<^bold>|" for l
    unfolding pow_len[of r l] using less_diff_conv2[of "l * \<^bold>|r\<^bold>|" i "\<^bold>|r\<^bold>|", unfolded add.commute[of "\<^bold>|r\<^bold>|"  "l * \<^bold>|r\<^bold>|"]]
      get_mod[of "i - l * \<^bold>|r\<^bold>|" "\<^bold>|r\<^bold>|" l] le_add_diff_inverse[of "l*\<^bold>|r\<^bold>|" i] by argo 
  case (Suc k)
  show ?case
    unfolding aux sym[OF pow_Suc2_list[symmetric]] nth_append le_mod_geq 
    using aux1[ OF _ Suc.prems[unfolded aux]]
      Suc.IH pow_Suc2_list[symmetric] Suc.prems[unfolded aux] leI[of i "\<^bold>|r \<^sup>@ k\<^bold>|"] by presburger
qed auto

lemma sing_pow_len: "\<^bold>|[r]\<^sup>@l\<^bold>| = l"
  by (induct l) auto

lemma concat_take_sing: "k \<le> l \<Longrightarrow> concat (take k ([r]\<^sup>@l)) = r\<^sup>@k"
proof(induct k, simp)
  case (Suc k)
  then show ?case 
    using concat_morph[of "take k ((r # \<epsilon>) \<^sup>@ l)""(r # \<epsilon>)", unfolded
        sym[OF take_Suc_conv_app_nth[of k "[r]\<^sup>@l", unfolded sing_pow_len[of r l] less_eq_Suc_le  
            sing_pow[OF iffD2[OF less_eq_Suc_le Suc.prems], of r], OF \<open>Suc k \<le> l\<close>]] 
        concat_sing'[of r] 
        Suc.hyps[OF Suc_leD[OF Suc.prems]]
        pow_Suc2_list[symmetric]]
    by argo
qed

lemma concat_sing_pow: "concat ([a]\<^sup>@k) = a\<^sup>@k"
proof(induct k)
  show "concat ((a # \<epsilon>) \<^sup>@ 0) = a \<^sup>@ 0"
    by simp
next
  fix k assume "concat ((a # \<epsilon>) \<^sup>@ k) = a \<^sup>@ k"
  thus "concat ((a # \<epsilon>) \<^sup>@ Suc k) = a \<^sup>@ Suc k"
    by simp
qed

lemma unique_letter_word: "(\<forall> c. c \<in> set w \<longrightarrow> c = a) \<Longrightarrow> \<exists> k. w = [a]\<^sup>@k"
proof (induct w)
  case Nil
  then show ?case
    by (metis pow_zero) 
next
  case (Cons b w) 
  then show ?case  
  proof-
    obtain k where "w = [a]\<^sup>@k" using Cons.hyps Cons.prems by auto 
    hence "b#w = [a]\<^sup>@Suc k"
      by (simp add: \<open>w = (a # \<epsilon>)\<^sup>@k\<close> Cons.prems) 
    thus ?thesis by blast 
  qed
qed

lemma unique_letter_wordE[elim]: assumes "(\<forall> c. c \<in> set w \<longrightarrow> c = a)" obtains k where "w = [a]\<^sup>@k"
  using unique_letter_word assms by metis
  
lemma unique_letter_wordE'[elim]: assumes "set w \<subseteq> {a}" obtains k where "w = [a] \<^sup>@ k"
  using assms unique_letter_word[of w a] by blast

lemma conjug_pow: "x \<cdot> z = z \<cdot> y \<Longrightarrow> x\<^sup>@k \<cdot> z = z \<cdot> y\<^sup>@k"
  by (induct k) fastforce+

lemma shift_pow: "(u\<cdot>v)\<^sup>@k\<cdot>u = u\<cdot>(v\<cdot>u)\<^sup>@k"
  by (simp add: conjug_pow)

lemma lq_conjug_pow: assumes "p \<le>p x \<cdot> p" shows "p\<inverse>\<^sup>>(x\<^sup>@k \<cdot> p) = (p\<inverse>\<^sup>>(x \<cdot> p))\<^sup>@k"
  using lqI[OF sym[OF conjug_pow[of x p  "p\<inverse>\<^sup>>(x \<cdot> p)", OF sym[OF lq_pref[OF \<open>p \<le>p x \<cdot> p\<close>]], of k]]]. 

lemmas rq_conjug_pow = lq_conjug_pow[reversed]

section "Total morphisms"

locale  morphism =
  fixes f :: "'a list \<Rightarrow> 'b list"
  assumes morph: "f (u \<cdot> v) = f u \<cdot> f v"
begin

lemma emp_to_emp[simp]: "f \<epsilon> = \<epsilon>"
  using morph[of \<epsilon> \<epsilon>] self_append_conv2[of "f \<epsilon>" "f \<epsilon>"] by simp

lemma pow_morph: "f (x\<^sup>@k) = (f x)\<^sup>@k"
  by (induction k) (simp add: morph)+

lemma pop_hd: "f (a#u) = f [a] \<cdot> f u"
  unfolding hd_word[of a u] using morph. 

lemma pop_hd_nemp: "u \<noteq> \<epsilon> \<Longrightarrow> f (u) = f [hd u] \<cdot> f (tl u)"
  using list.exhaust_sel pop_hd[of "hd u" "tl u"] by force

lemma pop_last_nemp: "u \<noteq> \<epsilon> \<Longrightarrow> f (u) = f (butlast u) \<cdot> f [last u]"
  unfolding morph[symmetric] append_butlast_last_id ..

lemma pref_mono: "u \<le>p v \<Longrightarrow> f u \<le>p f v"
  using morph by auto

lemma morph_concat_map: "f x = concat (map (\<lambda> x. f [x]) x)"
proof (induction x, simp)
  case (Cons a x)
  then show ?case 
    unfolding pop_hd[of a x] by auto 
qed 

end 

locale two_morphisms = morphg: morphism g + morphh: morphism h for g h :: "'a list \<Rightarrow> 'b list"
begin
lemma def_on_sings:
  assumes "\<And>a. g [a] = h [a]"
  shows "g u = h u"
proof (induct u, simp)
next
  case (Cons a u)
  then show ?case
    unfolding morphg.pop_hd[of a u] morphh.pop_hd[of a u] using \<open>\<And>a. g [a] = h [a]\<close>  by presburger
qed
end

section \<open>Reversed morphism and composition\<close>

definition rev_morph :: "('a list \<Rightarrow> 'b list) \<Rightarrow> ('a list \<Rightarrow> 'b list)" where 
  "rev_morph f = rev \<circ> f \<circ> rev" 

lemma rev_morph_idemp[simp]: "rev_morph (rev_morph f) = f"
  unfolding rev_morph_def by auto

lemma morph_compose: "morphism f \<Longrightarrow> morphism g \<Longrightarrow> morphism (f \<circ> g)"
  by (simp add: morphism_def)

lemma rev_morph_arg: "rev_morph f u = rev (f (rev u))"
  by (simp add: rev_morph_def)

lemmas rev_morph_arg_rev[reversal_rule] = rev_morph_arg[reversed add: rev_rev_ident]

lemma rev_morph_sing: "rev_morph f [a] =  rev (f [a])"
  unfolding rev_morph_def by simp

context morphism
begin

lemma  rev_morph_morph: "morphism (rev_morph f)"
  by (standard, auto simp add: rev_morph_def morph)

lemma morph_rev_len:  "\<^bold>|f (rev u)\<^bold>| = \<^bold>|f u\<^bold>|"
proof (induction u, simp)
  case (Cons a u)
  then show ?case 
    unfolding rev.simps(2) pop_hd[of a u] morph length_append by force
qed

lemma  rev_morph_len: "\<^bold>|rev_morph f u\<^bold>| = \<^bold>|f u\<^bold>|"
  unfolding rev_morph_def
  by (simp add: morph_rev_len) 

end

section \<open>Rotation\<close>

lemma rotate_comp_eq:"w \<bowtie> rotate n w \<Longrightarrow> rotate n w = w"
  using  pref_same_len[OF _ length_rotate[of n w]] pref_same_len[OF _ length_rotate[of n w, symmetric], symmetric]
  by blast

corollary mismatch_iff_lexord: assumes "rotate n w \<noteq> w" and "irrefl r"
  shows "mismatch_pair w (rotate  n w) \<in> r \<longleftrightarrow> (w,rotate n w) \<in> lexord r"
proof-
  have "\<not> w \<bowtie> rotate n w"
    using rotate_comp_eq \<open>rotate n w \<noteq> w\<close> 
    unfolding prefix_comparable_def by blast
  from lexord_mismatch[OF this \<open>irrefl r\<close>]
  show ?thesis.
qed

lemma rotate_back: obtains m where "rotate m (rotate n u) = u"
proof(cases "u = \<epsilon>", simp)
  assume "u \<noteq> \<epsilon>"
  show ?thesis
    using that[of "\<^bold>|u\<^bold>| - n mod \<^bold>|u\<^bold>|"]   
    unfolding rotate_rotate[of "\<^bold>|u\<^bold>| - n mod \<^bold>|u\<^bold>|" "n mod \<^bold>|u\<^bold>|" u]
      le_add_diff_inverse2[OF  
        less_imp_le_nat[OF mod_less_divisor[OF nemp_len[OF \<open>u \<noteq> \<epsilon>\<close>, unfolded neq0_conv], of n]]]
      arg_cong[OF rotate_conv_mod[of n u], of "rotate (\<^bold>|u\<^bold>| - n mod \<^bold>|u\<^bold>|)"]
    by simp
qed

lemma rotate_class_rotate': "(\<exists>n. rotate n w = u) \<longleftrightarrow> (\<exists>n. rotate n (rotate l w) = u)"
proof  
  obtain m where rot_m: "rotate m (rotate l w) = w" using rotate_back.
  assume "\<exists>n. rotate n w = u"
  then obtain n where rot_n: "rotate n w = u" by blast 
  show "\<exists>n. rotate n (rotate l w) = u"
    using  exI[of "\<lambda> x. rotate x (rotate l w) = u" "n+m", OF 
        rotate_rotate[symmetric, of n m "rotate l w", unfolded rot_m rot_n]].
next
  show "\<exists>n. rotate n (rotate l w) = u \<Longrightarrow> \<exists>n. rotate n w = u"
    using rotate_rotate[symmetric] by blast 
qed

lemma rotate_class_rotate: "{u . \<exists>n. rotate n w = u} = {u . \<exists>n. rotate n (rotate l w) = u}"
  using rotate_class_rotate' by blast

lemma rotate_pow_self: "rotate (l*\<^bold>|u\<^bold>|) (u\<^sup>@k) = u\<^sup>@k"
proof(induct l, simp)
  case (Suc l)
  then show ?case
  proof(cases "k = 0", simp)
    assume "k \<noteq> 0" 
    show ?thesis
      unfolding rotate_rotate[of "\<^bold>|u\<^bold>|" "l * \<^bold>|u\<^bold>|" "u\<^sup>@k", unfolded mult_Suc[symmetric] Suc.hyps, symmetric]
      using rotate_append[of u "u\<^sup>@(k-1)", folded pop_pow_one[OF \<open>k \<noteq> 0\<close>, of u] pop_pow_one'[OF \<open>k \<noteq> 0\<close>, of u]].
  qed
qed

lemma rotate_root_self: "rotate \<^bold>|r\<^bold>| (r\<^sup>@k) = r\<^sup>@k"
  using rotate_pow_self[of 1 r k] by auto

lemma rotate_pow_mod:  "rotate n (u\<^sup>@k) = rotate (n mod \<^bold>|u\<^bold>|) (u\<^sup>@k)"
  using rotate_rotate[of "n mod \<^bold>|u\<^bold>|" "n div \<^bold>|u\<^bold>| * \<^bold>|u\<^bold>|" "u\<^sup>@k", symmetric]
  unfolding rotate_pow_self[of "n div \<^bold>|u\<^bold>|" u k] div_mult_mod_eq[of n "\<^bold>|u\<^bold>|", unfolded add.commute[of "n div \<^bold>|u\<^bold>| * \<^bold>|u\<^bold>|" "n mod \<^bold>|u\<^bold>|"]].

lemma rotate_conj_pow: "rotate \<^bold>|u\<^bold>| ((u\<cdot>v)\<^sup>@k) = (v\<cdot>u)\<^sup>@k"
  by (induct k, simp, simp add: rotate_append shift_pow)

lemma rotate_pow_comm: "rotate n (u\<^sup>@k) = (rotate n u)\<^sup>@k"
proof (cases "u = \<epsilon>", simp)
  assume "u \<noteq> \<epsilon>"
  show ?thesis
    unfolding rotate_drop_take[of n u] rotate_pow_mod[of n u k]
    using rotate_conj_pow[of "take (n mod \<^bold>|u\<^bold>|) u" "drop (n mod \<^bold>|u\<^bold>|) u" k, unfolded append_take_drop_id[of "n mod \<^bold>|u\<^bold>|" u]]
    unfolding  mod_le_divisor[of "\<^bold>|u\<^bold>|" n, THEN take_len, OF \<open>u\<noteq>\<epsilon>\<close>[unfolded length_greater_0_conv[symmetric]]].
qed


subsection \<open>Lists of words and their concatenation\<close>

text\<open>The helpful lemmas of this section deal with concatenation of a list of words @{term concat}.
The main objective is to cover elementary facts needed to study factorizations of words.
\<close>


lemma append_in_lists: "u \<in> lists A \<Longrightarrow> v \<in> lists A \<Longrightarrow> u \<cdot> v \<in> lists A"
  by simp

lemma concat_take_is_prefix: "concat(take n ws) \<le>p concat ws"
  using concat_morph[of "take n ws" "drop n ws", unfolded append_take_drop_id[of n ws], THEN prefI]. 

lemma concat_take_suc: assumes "j < \<^bold>|ws\<^bold>|" shows "concat(take j ws) \<cdot> ws!j = concat(take (Suc j) ws)"
  unfolding take_Suc_conv_app_nth[OF \<open>j < \<^bold>|ws\<^bold>|\<close>] 
  using sym[OF concat_append[of "(take j ws)" "[ws ! j]",
        unfolded concat.simps(2)[of "ws!j" \<epsilon>, unfolded concat.simps(1) append_Nil2]]].

lemma pref_mod_list': assumes "u \<le>np concat ws" 
  obtains j r where "j < \<^bold>|ws\<^bold>|" and "r \<le>np ws!j" and "concat (take j ws) \<cdot> r = u"  
proof-
  have "\<^bold>|ws\<^bold>| \<noteq> 0"
    using assms by fastforce
  then obtain l where "Suc l = \<^bold>|ws\<^bold>|"
    using Suc_pred by blast
  let ?P = "\<lambda> j. u \<le>p concat(take (Suc j) ws)"
  have "?P l"
    using assms  \<open>Suc l = \<^bold>|ws\<^bold>|\<close> by auto

  define j where "j = (LEAST j. ?P j)" \<comment> \<open>largest j such that concat (take j ws) <p u\<close>
  have "u \<le>p concat(take (Suc j) ws)" and "j < \<^bold>|ws\<^bold>|"
    using Least_le[of ?P, OF \<open>?P l\<close>]
      LeastI[of ?P, OF \<open>?P l\<close>] \<open>Suc l = \<^bold>|ws\<^bold>|\<close>
    unfolding sym[OF j_def] by auto

  have "concat(take j ws) <p u"
  proof (cases "j = 0")
    assume "j = 0" thus "concat(take j ws) <p u"
      using  assms by fastforce 
  next
    assume "j \<noteq> 0" hence "j - 1 < j" and "Suc (j-1) = j" by auto
    hence "\<not> ?P (j-1)"
      using j_def not_less_Least by blast   
    from this[unfolded \<open>Suc (j-1) = j\<close>]
    show "concat(take j ws) <p u"
      using pref_comp_not_pref ruler[OF concat_take_is_prefix npD[OF assms], of j] 
      unfolding prefix_comparable_def by blast
  qed

  let ?r = "concat(take j ws)\<inverse>\<^sup>>u"
  have "concat(take j ws) \<cdot> ?r = u" and "?r \<noteq> \<epsilon>"
    using \<open>concat (take j ws) <p u\<close> by auto                  
  have "?r \<le>p ws!j"
    using  pref_cancel[of "concat (take j ws)" "concat (take j ws)\<inverse>\<^sup>>u" "ws ! j"]
      \<open>u \<le>p concat (take (Suc j) ws)\<close>[unfolded sym[OF concat_take_suc[OF \<open>j < \<^bold>|ws\<^bold>|\<close>]]]
      \<open>concat (take j ws) \<cdot> concat (take j ws)\<inverse>\<^sup>>u = u\<close> by argo 
  show thesis
    using that[OF \<open>j < \<^bold>|ws\<^bold>|\<close>  npI[OF \<open>?r \<noteq> \<epsilon>\<close> \<open>?r \<le>p ws!j\<close>] \<open>concat(take j ws) \<cdot> ?r = u\<close>]. 
qed


lemma pref_mod_list_suf: assumes "u \<le>np concat ws" 
  obtains j s where "j < \<^bold>|ws\<^bold>|" and "s <s ws!j" and "concat (take (Suc j) ws) = u \<cdot> s"  
proof-
  obtain j r where "j < \<^bold>|ws\<^bold>|" and "r \<le>np ws!j" and "concat (take j ws) \<cdot> r = u"
    using pref_mod_list'[OF assms] by blast
  have "r\<inverse>\<^sup>>(ws!j) <s (ws!j)"
    using ssufI1[OF _ npD'[OF \<open>r \<le>np ws ! j\<close>]]  lq_pref[OF npD[OF \<open>r \<le>np ws ! j\<close>]]. 
  have "concat (take (Suc j) ws) = u \<cdot> r\<inverse>\<^sup>>(ws!j)"
    using lq_pref[OF npD[OF \<open>r \<le>np ws ! j\<close>], symmetric, unfolded
        same_append_eq[of "concat (take j ws)" "ws ! j" "r \<cdot> r\<inverse>\<^sup>>ws ! j", symmetric] lassoc
        \<open>concat (take j ws) \<cdot> r = u\<close> concat_take_suc[OF \<open>j < \<^bold>|ws\<^bold>|\<close>] \<open>r \<le>np ws!j\<close>].
  from that[OF \<open>j < \<^bold>|ws\<^bold>|\<close> \<open>r\<inverse>\<^sup>>(ws!j) <s (ws!j)\<close> this]
  show thesis.
qed


lemma suf_mod_list': "s \<le>ns concat ws \<Longrightarrow> ws \<noteq> \<epsilon> \<Longrightarrow> \<exists>j r. j < \<^bold>|ws\<^bold>| \<and> r \<cdot> (concat (drop (Suc j) ws)) = s \<and> r \<le>ns ws!j"
proof-
  assume "s \<le>ns concat ws" "ws \<noteq> \<epsilon>"

  have "rev s \<le>np concat (rev (map (\<lambda>u. rev u) ws))"
    using \<open>s \<le>ns concat ws\<close>[unfolded nsuf_rev_pref_iff]
    by (simp add: rev_concat rev_map) 
  have  "rev ws \<noteq> \<epsilon>" 
    by (simp add: \<open>ws \<noteq> \<epsilon>\<close>)
  then obtain j r where "j < \<^bold>|rev (map rev ws)\<^bold>|" "concat (take j (rev (map rev ws))) \<cdot> r = rev s" "r \<le>np rev (map rev ws) ! j"
    using pref_mod_list'[of "rev s" "rev (map (\<lambda>u. rev u) ws)" thesis]
      \<open>rev s \<le>np concat (rev (map rev ws))\<close> by blast

  have "rev ws ! j = rev (rev (map rev ws) ! j)"
    using \<open>j < \<^bold>|rev (map rev ws)\<^bold>|\<close> length_map nth_map[of j "rev ws" rev, unfolded rev_map[of rev ws, symmetric]]  rev_rev_ident
    by simp
  from \<open>j < \<^bold>|rev (map rev ws)\<^bold>|\<close> rev_nth[of j ws, unfolded this]
  have "rev (rev (map rev ws) ! j) = ws!(\<^bold>|ws\<^bold>|- Suc j)"
    by fastforce
  from \<open>r \<le>np rev (map rev ws) ! j\<close>[unfolded npref_rev_suf_iff, unfolded this]
  have p2: "rev r \<le>ns ws!(\<^bold>|ws\<^bold>|-Suc j)".
  have "concat (take j (rev (map rev ws))) = rev (concat (drop (\<^bold>|ws\<^bold>|-j) ws))"
    by (simp add: rev_concat rev_map take_map take_rev)
  from arg_cong[OF this, of "\<lambda>x. x\<cdot>r", unfolded \<open>concat (take j (rev (map rev ws))) \<cdot> r = rev s\<close>]
  have p1: "s = rev r \<cdot> (concat (drop (\<^bold>|ws\<^bold>|-j) ws))"
    using  rev_append[of "rev (concat (drop (\<^bold>|ws\<^bold>| - j) ws))" r] rev_rev_ident[of s] rev_rev_ident[of "(concat (drop (\<^bold>|ws\<^bold>| - j) ws))"]
    by argo

  have p0: "\<^bold>|ws\<^bold>| - Suc j < \<^bold>|ws\<^bold>|"
    by (simp add: \<open>ws \<noteq> \<epsilon>\<close>)

  have "\<^bold>|ws\<^bold>| - j = Suc (\<^bold>|ws\<^bold>| - Suc j)"
    using  Suc_diff_Suc[OF \<open>j < \<^bold>|rev (map rev ws)\<^bold>|\<close>] by auto
  from p0 p1[unfolded this] p2 show ?thesis
    by blast
qed

lemma pref_mod_list: assumes "u <p concat ws" 
  obtains j r where "j < \<^bold>|ws\<^bold>|" and "r <p ws!j" and "concat (take j ws) \<cdot> r = u"  
proof-
  have "\<^bold>|ws\<^bold>| \<noteq> 0"
    using assms by auto
  then obtain l where "Suc l = \<^bold>|ws\<^bold>|"
    using Suc_pred by blast
  let ?P = "\<lambda> j. u <p concat(take (Suc j) ws)"
  have "?P l"
    using assms  \<open>Suc l = \<^bold>|ws\<^bold>|\<close> by auto
  define j where "j = (LEAST j. ?P j)" \<comment> \<open>smallest j such that concat (take (Suc j) ws) <p u\<close>
  have "u <p concat(take (Suc j) ws)"
    using  LeastI[of ?P, OF \<open>?P l\<close>] unfolding sym[OF j_def]. 
  have  "j < \<^bold>|ws\<^bold>|"
    using Least_le[of ?P, OF \<open>?P l\<close>] \<open>Suc l = \<^bold>|ws\<^bold>|\<close> unfolding sym[OF j_def]
    by auto
  have "0 < j \<Longrightarrow> concat(take j ws) \<le>p u"
    using Least_le[of ?P "(j- Suc 0)", unfolded sym[OF j_def]] 
      ruler[OF concat_take_is_prefix sprefD1[OF assms], of j]
    by force  
  hence "concat(take j ws) \<le>p u"
    by fastforce
  let ?r = "concat(take j ws)\<inverse>\<^sup>>u"
  have "concat(take j ws) \<cdot> ?r = u"
    using \<open>concat (take j ws) \<le>p u\<close> by auto                  
  have "?r <p ws!j"
    using spref_lq[OF \<open>concat (take j ws) \<le>p u\<close> \<open>u <p concat (take (Suc j) ws)\<close>, unfolded 
        lq_triv[of "concat (take j ws)" "ws!j", unfolded concat_take_suc[OF \<open>j < \<^bold>|ws\<^bold>|\<close>]]].
  show thesis
    using that[OF \<open>j < \<^bold>|ws\<^bold>|\<close> \<open>?r <p ws!j\<close> \<open>concat(take j ws) \<cdot> ?r = u\<close>]. 
qed

lemma pref_mod_power: assumes "u <p w\<^sup>@l"
  obtains k z where "k < l" and "z <p w" and "w\<^sup>@k\<cdot>z = u"
  using pref_mod_list[of u "[w]\<^sup>@l", unfolded sing_pow_len concat_sing_pow, OF \<open>u <p w\<^sup>@l\<close>, of thesis] 
    sing_pow[of _ l w] concat_take_sing
    less_imp_le_nat by metis

lemma get_pow_exp: assumes "z <p t" shows "m = \<^bold>|t\<^sup>@m\<cdot>z\<^bold>| div \<^bold>|t\<^bold>|"
  unfolding length_append[of "t\<^sup>@m" z, unfolded pow_len] using  get_div[OF prefix_length_less[OF assms]].

lemma get_pow_remainder: assumes "z <p t" shows "z = drop ((\<^bold>|t\<^sup>@m\<cdot>z\<^bold>| div \<^bold>|t\<^bold>|)*\<^bold>|t\<^bold>|) (t\<^sup>@m\<cdot>z)"
  using  drop_pref[of "t\<^sup>@m" z]  pow_len[of t m] get_pow_exp[OF assms, of m] by simp

lemma pref_mod_power': assumes "u \<le>np w\<^sup>@l"
  obtains k z where "k < l" and "z \<le>np w" and "w\<^sup>@k\<cdot>z = u"
  using pref_mod_list'[of u "[w]\<^sup>@l", unfolded sing_pow_len concat_sing_pow, OF \<open>u \<le>np w\<^sup>@l\<close>] 
    sing_pow[of _ l w] concat_take_sing[of _ l w]
    less_imp_le_nat[of _ l] by metis

lemma pref_power: assumes "t \<noteq> \<epsilon>" and  "u \<le>p t\<^sup>@k" 
  shows "\<exists> m. t\<^sup>@m \<le>p u \<and> u <p t\<^sup>@m \<cdot> t"
proof (cases "u = t\<^sup>@k")
  show "u = t \<^sup>@ k \<Longrightarrow> \<exists>m. t \<^sup>@ m \<le>p u \<and> u <p t \<^sup>@ m \<cdot> t"
    using \<open>t \<noteq> \<epsilon>\<close> by blast
next
  assume "u \<noteq> t \<^sup>@ k" 
  obtain m z where "m < k" "z <p t" "t \<^sup>@ m \<cdot> z = u"
    using pref_mod_power[of u t k] \<open>u \<le>p t\<^sup>@k\<close>[unfolded prefix_order.dual_order.order_iff_strict] \<open>u \<noteq> t\<^sup>@k\<close>
    by blast
  hence "t \<^sup>@ m \<le>p u" and "u <p t \<^sup>@ m \<cdot> t" by auto 
  thus ?thesis by blast 
qed   

lemma pref_powerE: assumes "t \<noteq> \<epsilon>" and  "u \<le>p t\<^sup>@k" 
  obtains m where "t\<^sup>@m \<le>p u" "u <p t\<^sup>@m \<cdot> t"
  using assms pref_power by blast 

lemma pref_power': assumes "u \<noteq> \<epsilon>" and  "u \<le>p t\<^sup>@k" 
  shows "\<exists> m. t\<^sup>@m <p u \<and> u \<le>p t\<^sup>@m \<cdot> t"
proof-
  obtain m z where "m < k" "z \<le>np t" "t \<^sup>@ m \<cdot> z = u"  
    using pref_mod_power'[OF npI[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<le>p t\<^sup>@k\<close>]].
  thus ?thesis  
    by auto 
qed   

lemma suf_power: assumes "t \<noteq> \<epsilon>" and "u \<le>s t\<^sup>@k" shows "\<exists>m. t\<^sup>@m \<le>s u \<and> u <s t \<cdot> t\<^sup>@m"
proof-
  have "rev u \<le>p (rev t)\<^sup>@k" 
    using \<open>u \<le>s t\<^sup>@k\<close>[unfolded suffix_to_prefix rev_pow].   
  from pref_power[OF _ this]
  obtain m where "(rev t)\<^sup>@m \<le>p rev u" and "rev u <p (rev t)\<^sup>@m \<cdot> rev t"
    using \<open>t \<noteq> \<epsilon>\<close> by blast 
  have "t\<^sup>@m \<le>s u"
    using \<open>(rev t)\<^sup>@m \<le>p rev u\<close>[folded suffix_to_prefix rev_pow]. 
  moreover have "u <s t \<cdot> t\<^sup>@m" 
    using sprefD1[OF \<open>rev u <p (rev t)\<^sup>@m \<cdot> rev t\<close>, folded rev_pow  rev_append suffix_to_prefix]
      sprefD2[OF \<open>rev u <p (rev t)\<^sup>@m \<cdot> rev t\<close>, folded rev_pow  rev_append]
     by blast
  ultimately show ?thesis by blast
qed

lemma suf_powerE: assumes "t \<noteq> \<epsilon>" and  "u \<le>s t\<^sup>@k" 
  obtains m where "t\<^sup>@m \<le>s u" "u <s t \<cdot> t\<^sup>@m"
  using assms suf_power by blast 

lemma del_emp_concat: "concat us = concat (filter (\<lambda>x. x \<noteq> \<epsilon>) us)"
  by (induct us) simp+

lemma lists_drop_emp: "us \<in> lists C\<^sub>+ \<Longrightarrow> us \<in> lists C"
  by blast

lemma lists_drop_emp': "us \<in> lists C \<Longrightarrow> (filter (\<lambda>x. x \<noteq> \<epsilon>) us) \<in> lists C\<^sub>+"
  by (simp add: in_lists_conv_set)

lemma pref_concat_pref: "us \<le>p ws \<Longrightarrow> concat us \<le>p concat ws" 
  by auto

lemma le_take_is_prefix: assumes "k \<le> n" shows "take k ws \<le>p take n ws"
  using take_add[of k "(n-k)" ws, unfolded le_add_diff_inverse[OF \<open>k \<le> n\<close>]] 
  by force

lemma take_pp_less: assumes "take k ws <p take n ws" shows "k < n"
  using  conjunct2[OF sprefD[OF assms]] 
    leI[of k n, THEN[2] le_take_is_prefix[of n k ws, THEN[2] pref_antisym[of "take k ws" "take n ws"]], OF conjunct1[OF sprefD[OF assms]]]  
  by blast

lemma concat_pp_less: assumes "concat (take k ws) <p concat (take n ws)" shows "k < n" 
  using le_take_is_prefix[of n k ws, THEN pref_concat_pref] conjunct1[OF sprefD[OF assms]] 
    conjunct2[OF sprefD[OF assms]] pref_antisym[of "concat(take k ws)" "concat(take n ws)"]
  by fastforce

section \<open>Root\<close>

definition root :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<in> _*" [51,51] 60 )
  where  "u \<in> r* =  (\<exists> k. r\<^sup>@k = u)"
notation (latex output) root ("_ \<in> _\<^sup>*")

text\<open>Empty word has all roots, including the empty root.\<close>

lemma "\<epsilon> \<in> r*"
  unfolding root_def using power_0 by blast

lemma rootI: "r\<^sup>@k \<in> r*"
  using root_def by auto

lemma self_root: "u \<in> u*"
  using rootI[of u "Suc 0"] by simp

lemma rootE: assumes "u \<in> r*" obtains k where "r\<^sup>@k = u"
  using assms root_def by auto

lemma empty_all_roots[simp]: "\<epsilon> \<in> r*"
  using  rootI[of r 0, unfolded pow_zero].

lemma take_root: "k \<noteq> 0 \<Longrightarrow> r = take (length r) (r\<^sup>@k)"
  by (simp add: pow_eq_if_list)

lemma root_nemp: "u \<noteq> \<epsilon> \<Longrightarrow> u \<in> r* \<Longrightarrow> r \<noteq> \<epsilon>"
  unfolding root_def using emp_pow by auto 

lemma root_shorter: "u \<noteq> \<epsilon> \<Longrightarrow> u \<in> r* \<Longrightarrow> u \<noteq> r \<Longrightarrow> \<^bold>|r\<^bold>| < \<^bold>|u\<^bold>|"
  by (metis root_def leI take_all take_root pow_zero)

lemma root_shorter_eq: "u \<noteq> \<epsilon> \<Longrightarrow> u \<in> r* \<Longrightarrow> \<^bold>|r\<^bold>| \<le> \<^bold>|u\<^bold>|"
  using root_shorter by fastforce

lemma root_trans[trans]: "\<lbrakk>v \<in> u*; u \<in> t*\<rbrakk> \<Longrightarrow> v \<in> t*"                                   
  by (metis root_def pow_mult_list)

lemma root_pow_root[trans]: "v \<in> u* \<Longrightarrow> v\<^sup>@n \<in> u*"
  using rootI root_trans by blast

lemma root_len: "u \<in> q* \<Longrightarrow> \<exists>k. \<^bold>|u\<^bold>| = k*\<^bold>|q\<^bold>|"
  unfolding root_def using pow_len by auto

lemma root_len_dvd: "u \<in> t* \<Longrightarrow> \<^bold>|t\<^bold>| dvd \<^bold>|u\<^bold>|"
  using root_len root_def by fastforce 

lemma common_root_len_gcd: "u \<in> t* \<Longrightarrow> v \<in> t* \<Longrightarrow> \<^bold>|t\<^bold>| dvd ( gcd \<^bold>|u\<^bold>| \<^bold>|v\<^bold>| )"
  by (simp add: root_len_dvd)

lemma add_root[simp]: "z \<cdot> w \<in> z* \<longleftrightarrow> w \<in> z*"
proof
  assume "w \<in> z*" thus "z \<cdot> w \<in> z*" 
    unfolding root_def using pow_Suc_list by blast 
next
  assume "z \<cdot> w \<in> z*" thus "w \<in> z*"
    unfolding root_def
    using root_pref_cancel[of z 1 w, unfolded power_one_right] by metis
qed 

lemma add_roots: "w \<in> z* \<Longrightarrow> w' \<in> z* \<Longrightarrow> w \<cdot> w' \<in> z*"
  unfolding root_def using pow_add_list by blast 

lemma concat_sing_list_pow: "ws \<in> lists {u} \<Longrightarrow> \<^bold>|ws\<^bold>| = k \<Longrightarrow> concat ws = u\<^sup>@k"
proof(induct k arbitrary: ws)
  case (Suc k)
  have "ws \<noteq> \<epsilon>"
    using  list.size(3) nat.distinct(2)[of k, folded \<open>\<^bold>|ws\<^bold>| = Suc k\<close>] by blast   
  from hd_Cons_tl[OF this] 
  have "ws = hd ws # tl ws"  and "\<^bold>|tl ws\<^bold>| = k"
    using \<open> \<^bold>|ws\<^bold>| = Suc k\<close> by simp+
  then show ?case
    unfolding  pow_Suc_list hd_concat_tl[OF \<open>ws \<noteq> \<epsilon>\<close>, symmetric] 
    using Suc.hyps[OF tl_lists[OF \<open> ws \<in> lists {u}\<close>] \<open>\<^bold>|tl ws\<^bold>| = k\<close>]
          Nitpick.size_list_simp(2) lists_hd[of "ws" "{u}"] \<open>ws \<in> lists{u}\<close> by blast
qed simp

lemma concat_sing_list_pow': "ws \<in> lists{u} \<Longrightarrow> concat ws = u\<^sup>@\<^bold>|ws\<^bold>|"
  by (simp add: concat_sing_list_pow) 

lemma root_pref_cancel': assumes "x\<cdot>y \<in> t*" and  "x \<in> t*" shows "y \<in> t*" 
proof-
  obtain n m where "t\<^sup>@m = x \<cdot> y" and "t\<^sup>@n = x"
  using \<open>x\<cdot>y \<in> t*\<close>[unfolded root_def] \<open>x \<in> t*\<close>[unfolded root_def] by blast 
  from root_pref_cancel[of t n y m, unfolded this]
  show "y \<in> t*"
    using rootI by auto
qed

lemma root_rev_iff[reversal_rule]: "rev u \<in> rev t* \<longleftrightarrow> u \<in> t*"
  unfolding root_def[reversed] using root_def..

section Commutation

text\<open>The solution of the easiest nontrivial word equation, @{term "x \<cdot> y = y \<cdot> x"}, is in fact already contained in List.thy as the fact @{thm comm_append_are_replicate[no_vars]}.\<close>

theorem comm:  "x \<cdot> y = y \<cdot> x  \<longleftrightarrow>  (\<exists> t m k. x = t\<^sup>@k \<and> y = t\<^sup>@m)"
 using  comm_append_are_replicate[of x y, folded pow_is_concat_replicate] pow_comm by auto 
  
corollary comm_root:  "x \<cdot> y = y \<cdot> x   \<longleftrightarrow>  (\<exists> t. x \<in> t* \<and> y \<in> t*)"
  unfolding root_def comm by fast

lemma commD[elim]:  "x \<in> t* \<Longrightarrow> y \<in> t* \<Longrightarrow> x \<cdot> y = y \<cdot> x"
  using comm_root by auto

lemma commE[elim]: assumes  "x \<cdot> y = y \<cdot> x"
  obtains  t m k where "x = t\<^sup>@k" and "y = t\<^sup>@m"
  using assms[unfolded comm] by blast 

lemma comm_rootE: assumes  "x \<cdot> y = y \<cdot> x"
  obtains  t where "x \<in>  t*" and "y \<in> t*"
    using assms[unfolded comm_root] by blast 

section \<open>Periods\<close>

text\<open>Periodicity is probably the most studied property of words. It captures the fact that a word overlaps with itself.
Another possible point of view is that the periodic word is a prefix of an (infinite) power of some nonempty 
word, which can be called its period word. Both these points of view are expressed by the following definition.
\<close>

subsection "Periodic root"

definition period_root :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<le>p _\<^sup>\<omega>" [51,51] 60 )
  where [simp]: "period_root u r = (u \<le>p r \<cdot> u \<and> r \<noteq> \<epsilon>)"

lemma per_rootI[simp,intro]: "u \<le>p r \<cdot> u \<Longrightarrow> r \<noteq> \<epsilon> \<Longrightarrow> u \<le>p r\<^sup>\<omega>"
 by simp               

lemma per_rootI': assumes "u \<le>p r\<^sup>@k" and  "r \<noteq> \<epsilon>" shows  "u \<le>p r\<^sup>\<omega>"
  using per_rootI[OF  pref_prod_pref[OF pref_pow_ext'[OF \<open>u \<le>p r\<^sup>@k\<close>] \<open>u \<le>p r\<^sup>@k\<close>] \<open>r\<noteq>\<epsilon>\<close>].

lemma per_rootD[elim]: "u \<le>p r\<^sup>\<omega> \<Longrightarrow> u \<le>p r \<cdot> u"
  by simp

lemma per_rootD': "u \<le>p r\<^sup>\<omega> \<Longrightarrow> r \<noteq> \<epsilon>"
  by simp

text \<open>Empty word is not a periodic root but it has all nonempty periodic roots.\<close>

lemma emp_any_per: "r \<noteq> \<epsilon> \<Longrightarrow> (\<epsilon> \<le>p r\<^sup>\<omega> )"
  by simp

lemma emp_not_per: "\<not> (x \<le>p \<epsilon>\<^sup>\<omega>)"
  by simp 

text \<open>Any nonempty word is its own periodic root.\<close>

lemma root_self: "w \<noteq> \<epsilon> \<Longrightarrow> w \<le>p w\<^sup>\<omega>"
  by simp

text\<open>"Short roots are prefixes"\<close>

lemma root_is_take: "w \<le>p r\<^sup>\<omega> \<Longrightarrow> \<^bold>|r\<^bold>| \<le> \<^bold>|w\<^bold>| \<Longrightarrow>  r \<le>p w"
  unfolding period_root_def using pref_prod_long[of w r w] by fastforce

text \<open>Periodic words are prefixes of the power of the root, which motivates the notation\<close>

lemma pref_pow_ext_take: assumes "u \<le>p r\<^sup>@k" shows "u \<le>p take \<^bold>|r\<^bold>| u \<cdot> r\<^sup>@k"
proof (rule le_cases[of "\<^bold>|u\<^bold>|" "\<^bold>|r\<^bold>|"])
  assume "\<^bold>|r\<^bold>| \<le> \<^bold>|u\<^bold>|"
  show "u \<le>p take \<^bold>|r\<^bold>| u \<cdot> r \<^sup>@ k"
    unfolding pref_take[OF pref_prod_long[OF pref_pow_ext'[OF \<open>u \<le>p r\<^sup>@k\<close>] \<open>\<^bold>|r\<^bold>| \<le> \<^bold>|u\<^bold>|\<close>]]  using pref_pow_ext'[OF \<open>u \<le>p r\<^sup>@k\<close>].
qed simp

lemma pref_pow_take: assumes "u \<le>p r\<^sup>@k" shows "u \<le>p take \<^bold>|r\<^bold>| u \<cdot> u"
  using pref_prod_pref[of u "take \<^bold>|r\<^bold>| u" "r\<^sup>@k", OF pref_pow_ext_take \<open>u \<le>p r\<^sup>@k\<close>, OF \<open>u \<le>p r\<^sup>@k\<close>].
                                                                           
lemma per_exp: assumes "u \<le>p r\<^sup>\<omega>" shows "u \<le>p r\<^sup>@k \<cdot> u"
  using  per_exp_pref[OF per_rootD[OF assms]].

lemma per_root_spref_powE: assumes "u \<le>p r\<^sup>\<omega>" 
  obtains k where "u <p r\<^sup>@k"
  using pref_prod_short'[OF per_exp[OF assms, of "Suc \<^bold>|u\<^bold>|"] long_power'[of r u, OF per_rootD'[OF assms]]] by blast

lemma period_rootE [elim]: assumes "u \<le>p t\<^sup>\<omega>" obtains n r where "r <p t" and "t\<^sup>@n \<cdot> r = u"
proof-
  obtain m where "u <p t\<^sup>@m" using \<open>u \<le>p t\<^sup>\<omega>\<close>
    using per_root_spref_powE by blast
  from pref_mod_power[OF this that, of "\<lambda> x y. y" "\<lambda> x y. x"]
  show ?thesis by blast
qed

lemma per_add_exp: assumes "u \<le>p r\<^sup>\<omega>" and "m \<noteq> 0" shows "u \<le>p (r\<^sup>@m)\<^sup>\<omega>"
  using per_exp_pref[OF per_rootD, OF \<open>u \<le>p r\<^sup>\<omega>\<close>, of m]  per_rootD'[OF \<open>u \<le>p r\<^sup>\<omega>\<close>, folded nonzero_pow_emp[OF \<open>m \<noteq> 0\<close>, of r]]
  unfolding period_root_def..

lemma per_pref_ex: assumes "u \<le>p r\<^sup>\<omega>" 
  obtains n where "u \<le>p r\<^sup>@n" and "n \<noteq> 0"
  using pcomp_shorter[OF ruler_pref[OF per_exp[OF \<open>u \<le>p r\<^sup>\<omega>\<close>]]] long_pow_ex[of r "\<^bold>|u\<^bold>|", OF per_rootD'[OF \<open>u \<le>p r\<^sup>\<omega>\<close>], of thesis]
  by blast

theorem per_pref: "x \<le>p r\<^sup>\<omega> \<longleftrightarrow> (\<exists> k. x \<le>p r\<^sup>@k) \<and> r \<noteq> \<epsilon>"
  using per_pref_ex period_root_def pref_pow_ext' pref_prod_pref by metis

lemma pref_pow_conv: "(\<exists> k. x \<le>p r\<^sup>@k) \<longleftrightarrow> (\<exists> k z. r\<^sup>@k\<cdot>z = x \<and> z \<le>p r)" 
proof
  assume "\<exists>k z. r \<^sup>@ k \<cdot> z = x \<and> z \<le>p r"
  then obtain k z where "r\<^sup>@k \<cdot> z = x" and "z \<le>p r" by blast  
  thus "\<exists> k. x \<le>p r\<^sup>@k"
    using pref_cancel'[OF \<open>z \<le>p r\<close>, of "r\<^sup>@k", unfolded \<open>r\<^sup>@k \<cdot> z = x\<close>, folded pow_Suc2_list] by fast 
next 
  assume "\<exists> k. x \<le>p r\<^sup>@k" then obtain k where "x \<le>p r\<^sup>@k" by blast 
  {assume "r = \<epsilon>" 
    have "x = \<epsilon>"
      using pref_emp[OF \<open>x \<le>p r \<^sup>@ k\<close>[unfolded \<open>r = \<epsilon>\<close> emp_pow]].
    hence "\<exists> k z. r\<^sup>@k\<cdot>z = x \<and> z \<le>p r"
      using \<open>r = \<epsilon>\<close> emp_pow by auto} 
  moreover
  {assume "r \<noteq> \<epsilon>"  have "x <p r\<^sup>@(Suc k)"
      using pref_ext_nemp[OF \<open>x \<le>p r\<^sup>@k\<close> \<open>r \<noteq> \<epsilon>\<close>, folded pow_Suc2_list]. 
    then have "\<exists> k z. r\<^sup>@k\<cdot>z = x \<and> z \<le>p r"
      using pref_mod_power[OF pref_ext_nemp[OF \<open>x \<le>p r\<^sup>@k\<close> \<open>r \<noteq> \<epsilon>\<close>, folded pow_Suc2_list], of "\<exists> k z. r\<^sup>@k\<cdot>z = x \<and> z \<le>p r"] 
      by auto}
  ultimately show "\<exists> k z. r\<^sup>@k\<cdot>z = x \<and> z \<le>p r" by blast
qed

lemma per_eq: "x \<le>p r\<^sup>\<omega> \<longleftrightarrow> (\<exists> k z. r\<^sup>@k\<cdot>z = x \<and> z \<le>p r) \<and> r \<noteq> \<epsilon>"
  using per_pref[unfolded pref_pow_conv]. 

text\<open>The previous theorem allows to prove some basic relations between powers, periods and commutation\<close>

lemma per_drop_exp: "u \<le>p (r\<^sup>@m)\<^sup>\<omega>  \<Longrightarrow> u \<le>p r\<^sup>\<omega>" 
  using per_pref[of u "r\<^sup>@m"] pow_mult_list[of r m, symmetric] unfolding per_pref[of u r] 
  using nemp_pow'[of r m] by auto

lemma per_drop_exp': "i \<noteq> 0 \<Longrightarrow> p \<le>p e\<^sup>@i \<cdot> p \<Longrightarrow>  p \<le>p  e \<cdot> p"
  by (metis period_root_def eq_pow_exp per_drop_exp pow_zero) 

lemma per_drop_exp_rev: assumes "i \<noteq> 0" "p \<le>s p \<cdot> e\<^sup>@i" shows "p \<le>s p \<cdot> e"
  using per_drop_exp'[OF \<open>i \<noteq> 0\<close> \<open>p \<le>s p \<cdot> e\<^sup>@i\<close>[unfolded suffix_to_prefix rev_append rev_pow], folded rev_append suffix_to_prefix].

corollary comm_drop_exp: assumes "m \<noteq> 0" and "u \<cdot> r\<^sup>@m = r\<^sup>@m \<cdot> u" shows "r \<cdot> u = u \<cdot> r"
proof-
  {assume "r \<noteq> \<epsilon>" "u \<noteq> \<epsilon>"
    hence "u\<cdot>r \<le>p u\<cdot>r\<^sup>@m" using pop_pow_one \<open>m \<noteq> 0\<close>
      by (simp add: pop_pow_one)
    have "u\<cdot>r \<le>p r\<^sup>@m\<cdot>(u\<cdot>r)" 
      using pref_ext[of "u \<cdot> r" "r\<^sup>@m \<cdot> u" r, unfolded append_assoc[of "r\<^sup>@m" u r], OF  \<open>u\<cdot>r \<le>p u\<cdot>r\<^sup>@m\<close>[unfolded \<open>u \<cdot> r\<^sup>@m = r\<^sup>@m \<cdot> u\<close>]].
    hence "u\<cdot>r \<le>p r\<cdot>(u\<cdot>r)" 
      using per_drop_exp[of "u\<cdot>r" r m] \<open>m \<noteq> 0\<close> per_drop_exp' by blast
    from comm_ruler[OF self_pref[of "r \<cdot> u"], of "r \<cdot> u \<cdot> r", OF this]
    have "r \<cdot> u = u \<cdot> r" by auto
  }
  thus "r \<cdot> u = u \<cdot> r"
    by fastforce 
qed

corollary pow_comm_comm: assumes "x\<^sup>@j = y\<^sup>@k" and "j \<noteq> 0" shows "x\<cdot>y = y\<cdot>x"
proof(cases "k = 0")
  assume "k = 0"
  from \<open>x\<^sup>@j = y\<^sup>@k\<close>[unfolded zero_exp[OF this, of y], unfolded  nonzero_pow_emp[OF \<open>j \<noteq> 0\<close>]]
  show "x \<cdot> y = y \<cdot> x" by simp
next
  assume "k \<noteq> 0" show "x \<cdot> y = y \<cdot> x"
    using comm_drop_exp[of j y x, OF \<open>j \<noteq> 0\<close>, OF
        comm_drop_exp[of k "x\<^sup>@j" y, OF \<open>k \<noteq> 0\<close> , unfolded \<open>x\<^sup>@j = y\<^sup>@k\<close>, OF refl, folded \<open>x\<^sup>@j = y\<^sup>@k\<close>]].
qed            

corollary comm_pow_roots: assumes "m \<noteq> 0" "k \<noteq> 0" 
  shows "u\<^sup>@m \<cdot> v\<^sup>@k = v\<^sup>@k \<cdot> u\<^sup>@m \<longleftrightarrow> u \<cdot> v = v \<cdot> u"
  using comm_drop_exp[OF \<open>k \<noteq> 0\<close>, of "u\<^sup>@m" v, THEN comm_drop_exp[OF \<open>m \<noteq> 0\<close>, of v u]]
        comm_add_exps[of u v m k] by blast 

lemma pow_comm_comm': assumes comm: "u\<^sup>@(Suc k) = v\<^sup>@(Suc l)" shows "u \<cdot> v = v \<cdot> u"
  using comm pow_comm_comm by blast

lemma comm_trans: assumes uv: "u\<cdot>v =  v\<cdot>u" and vw: "w\<cdot>v = v\<cdot>w" and nemp: "v \<noteq> \<epsilon>" shows "u \<cdot> w = w \<cdot> u"
proof -
  consider (u_emp) "u = \<epsilon>" | (w_emp) "w = \<epsilon>" | (nemp') "u \<noteq> \<epsilon>" and "w \<noteq> \<epsilon>" by blast
  then show ?thesis proof (cases)
    case nemp'
      have eq: "u\<^sup>@(\<^bold>|v\<^bold>| * \<^bold>|w\<^bold>|) = w\<^sup>@(\<^bold>|v\<^bold>| * \<^bold>|u\<^bold>|)"
        unfolding power_mult comm_common_power[OF uv] comm_common_power[OF vw]
        unfolding pow_mult_list[symmetric] mult.commute[of "\<^bold>|u\<^bold>|"]..
      obtain k l where k: "\<^bold>|v\<^bold>| * \<^bold>|w\<^bold>| = Suc k" and l: "\<^bold>|v\<^bold>| * \<^bold>|u\<^bold>| = Suc l"
        using nemp nemp' unfolding length_0_conv[symmetric]
        using not0_implies_Suc[OF no_zero_divisors]
        by presburger
      show ?thesis
        using pow_comm_comm'[OF eq[unfolded k l]].
  qed simp+
qed

theorem per_all_exps: "\<lbrakk> m \<noteq> 0; k \<noteq> 0 \<rbrakk> \<Longrightarrow> (u \<le>p (r\<^sup>@m)\<^sup>\<omega>) \<longleftrightarrow> (u \<le>p (r\<^sup>@k)\<^sup>\<omega>)"
  using per_drop_exp[of u r m, THEN per_add_exp[of u r k]] per_drop_exp[of u r k, THEN per_add_exp[of u r m]] by blast

lemma drop_per_pref: assumes "w \<le>p u\<^sup>\<omega>" shows "drop \<^bold>|u\<^bold>| w \<le>p w"
  using pref_drop[OF per_rootD[OF \<open>w \<le>p u\<^sup>\<omega>\<close>], of "\<^bold>|u\<^bold>|", unfolded drop_pref[of u w]].

lemma per_root_trans[trans]: "w \<le>p u\<^sup>\<omega> \<Longrightarrow> u \<in> t* \<Longrightarrow> w \<le>p t\<^sup>\<omega>"
  using root_def[of u t] per_drop_exp[of w t] by blast

text\<open>Note that 
@{term "w \<le>p u\<^sup>\<omega> \<Longrightarrow> u \<le>p t\<^sup>\<omega> \<Longrightarrow> w \<le>p t\<^sup>\<omega>"}
does not hold.
\<close>

lemma per_root_same_prefix:"w \<le>p r\<^sup>\<omega> \<Longrightarrow> w' \<le>p r\<^sup>\<omega> \<Longrightarrow>  w \<bowtie> w"
  by blast

lemma take_after_drop:  "\<^bold>|u\<^bold>| + q \<le> \<^bold>|w\<^bold>| \<Longrightarrow> w \<le>p u\<^sup>\<omega> \<Longrightarrow> take q (drop \<^bold>|u\<^bold>| w) = take q w"
  using pref_share_take[OF drop_per_pref[of w u] len_after_drop[of "\<^bold>|u\<^bold>|" q w]].

text\<open>The following lemmas are a weak version of the Periodicity lemma\<close>

lemma two_pers':
  assumes pu: "w \<le>p u \<cdot> w" and pv: "w \<le>p v \<cdot> w" and len: "\<^bold>|u\<^bold>| + \<^bold>|v\<^bold>| \<le> \<^bold>|w\<^bold>|"
  shows "u \<cdot> v = v \<cdot> u" 
proof-
  have uv: "w \<le>p (u \<cdot> v) \<cdot> w" using pref_prolong[OF pu pv] unfolding lassoc.
  have vu: "w \<le>p (v \<cdot> u) \<cdot> w" using pref_prolong[OF pv pu] unfolding lassoc.
  have "u \<cdot> v \<le>p w" using len pref_prod_long[OF uv] by simp 
  moreover have "v \<cdot> u \<le>p w" using len pref_prod_long[OF vu] by simp
  ultimately show "u \<cdot> v = v \<cdot> u" by (rule pref_comp_eq[unfolded prefix_comparable_def, OF ruler swap_len])
qed

lemma two_pers: assumes "w \<le>p u\<^sup>\<omega>" and  "w \<le>p v\<^sup>\<omega>" and "\<^bold>|u\<^bold>|+\<^bold>|v\<^bold>| \<le> \<^bold>|w\<^bold>|" shows "u\<cdot>v = v\<cdot>u"
  using two_pers'[OF per_rootD[OF assms(1)] per_rootD[OF assms(2)] assms(3)].  

subsection "Period - numeric"

text\<open>Definition of a period as the length of the periodic root is often offered as the basic one. From our point of view, 
it is secondary, and less convenient for reasoning.\<close>

definition periodN :: "'a list \<Rightarrow> nat \<Rightarrow> bool" 
  where [simp]: "periodN w n =  w \<le>p (take n w)\<^sup>\<omega>"

lemma periodN_I: "w \<noteq> \<epsilon> \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> w \<le>p (take n w) \<cdot> w \<Longrightarrow> periodN w n"
  unfolding periodN_def period_root_def by fastforce

text\<open>The numeric definition respects the following convention about empty words and empty periods.\<close>

lemma emp_no_periodN: "\<not> periodN \<epsilon> n"
  by simp

lemma zero_not_per: "\<not> periodN w 0"
  by simp

(* lemma periodN_I [intro]: assumes "u \<le>p r\<^sup>@k" and  "u \<noteq> \<epsilon>" shows  "periodN u \<^bold>|r\<^bold>|" *)
  (* unfolding periodN_def period_root_def *)
  (* using  pref_pow_take[OF \<open>u \<le>p r\<^sup>@k\<close>] take_nemp_len[OF \<open>u \<noteq> \<epsilon>\<close>] \<open>u \<le>p r\<^sup>@k\<close> by force *)

(* lemma periodNI' [intro]: "u \<le>np r\<^sup>@k \<Longrightarrow> periodN u \<^bold>|r\<^bold>|" *)
  (* unfolding nonempty_prefix_def by blast *)

lemma periodN_D1: "periodN w n \<Longrightarrow>  w \<noteq> \<epsilon>"
  by simp

lemma periodN_D2: "periodN w n \<Longrightarrow>  n \<noteq> 0"
  by simp

lemma periodN_D3: "periodN w n \<Longrightarrow>  w \<le>p take n w \<cdot> w"
  by simp

text\<open>A nonempty word has all "long" periods\<close>

lemma all_long_pers: "\<lbrakk> w \<noteq> \<epsilon>; \<^bold>|w\<^bold>| \<le> n \<rbrakk> \<Longrightarrow> periodN w n"
  by simp

lemmas per_nemp = periodN_D1

lemmas per_positive = periodN_D2

text\<open>The standard numeric definition of a period uses indeces.\<close>

lemma periodN_indeces: assumes "periodN w n" and "i + n < \<^bold>|w\<^bold>|" shows "w!i = w!(i+n)"
proof-
  have "w ! i = (take n w \<cdot> w) ! (n + i)"
    using nth_append_length_plus[of "take n w" w i, symmetric]
    unfolding take_len[OF less_imp_le[OF add_lessD2[OF \<open>i + n < \<^bold>|w\<^bold>|\<close>]]]. 
  also have "... = w ! (i + n)"
    using pref_index[OF periodN_D3[OF \<open>periodN w n\<close>] \<open>i + n < \<^bold>|w\<^bold>|\<close>, symmetric] unfolding add.commute[of n i].  
  finally show ?thesis.
qed

lemma indeces_periodN: 
  assumes  "w \<noteq> \<epsilon>" and "n \<noteq> 0" and  forall: "\<And> i. i + n < \<^bold>|w\<^bold>| \<Longrightarrow> w!i = w!(i+n)" 
  shows "periodN w n"
proof-
  have "\<^bold>|w\<^bold>| \<le> \<^bold>|take n w \<cdot> w\<^bold>|" 
    by auto
  {fix j assume "j < \<^bold>|w\<^bold>|"
    have "w ! j = (take n w \<cdot> w) ! j"
    proof (cases "j < \<^bold>|take n w\<^bold>|")
      assume "j < \<^bold>|take n w\<^bold>|" show "w ! j = (take n w \<cdot> w) ! j"
        using pref_index[OF take_is_prefix \<open>j < \<^bold>|take n w\<^bold>|\<close>, symmetric] 
        unfolding pref_index[OF triv_pref \<open>j < \<^bold>|take n w\<^bold>|\<close>, of w].
    next
      assume "\<not> j < \<^bold>|take n w\<^bold>|" 
      from leI[OF this] \<open>j < \<^bold>|w\<^bold>|\<close>
      have "\<^bold>|take n w\<^bold>| = n" 
        by force
      hence "j = (j - n) + n" and "(j - n) + n < \<^bold>|w\<^bold>|"
        using  leI[OF \<open>\<not> j < \<^bold>|take n w\<^bold>|\<close>] \<open>j < \<^bold>|w\<^bold>|\<close> by simp+
      hence "w!j = w!(j - n)"
        using forall by simp
      from this[folded nth_append_length_plus[of "take n w" w "j-n", unfolded \<open>\<^bold>|take n w\<^bold>| = n\<close>]]
      show "w ! j = (take n w \<cdot> w) ! j" 
        using \<open>j = (j - n) + n\<close> by simp 
    qed}
  with index_pref[OF \<open>\<^bold>|w\<^bold>| \<le> \<^bold>|take n w \<cdot> w\<^bold>|\<close>]
  have "w \<le>p take n w \<cdot> w" by blast
  thus ?thesis 
    using assms by force
qed

text\<open>In some cases, the numeric definition is more useful than the definition using the period root.\<close>

lemma periodN_rev: assumes "periodN w p" shows "periodN (rev w) p"  
proof (rule indeces_periodN[of "rev w" p, OF _ periodN_D2[OF assms]])
  show "rev w \<noteq> \<epsilon>"
    using assms[unfolded periodN_def period_root_def] by force 
next
  fix i assume "i + p < \<^bold>|rev w\<^bold>|" 
  from this[unfolded length_rev] add_lessD1
  have "i < \<^bold>|w\<^bold>|" and "i + p < \<^bold>|w\<^bold>|" by blast+
  have e: "\<^bold>|w\<^bold>| - Suc (i + p) + p = \<^bold>|w\<^bold>| - Suc i" using \<open>i + p < \<^bold>|rev w\<^bold>|\<close> by simp
  have "\<^bold>|w\<^bold>| - Suc (i + p) + p < \<^bold>|w\<^bold>|"  using \<open>i + p < \<^bold>|w\<^bold>|\<close> by linarith   
  from periodN_indeces[OF assms this] rev_nth[OF \<open>i  < \<^bold>|w\<^bold>|\<close>, folded e] rev_nth[OF \<open>i + p < \<^bold>|w\<^bold>|\<close>]  
  show "rev w ! i = rev w !(i+p)" by presburger
qed

lemma periodN_rev_conv [reversal_rule]: "periodN (rev w) n \<longleftrightarrow> periodN w n"
  using periodN_rev periodN_rev[of "rev w"] unfolding rev_rev_ident by (intro iffI)

lemma periodN_fac: assumes "periodN (u\<cdot>w\<cdot>v) p" and "w \<noteq> \<epsilon>"
  shows "periodN w p"
proof (rule indeces_periodN, simp add: \<open>w \<noteq> \<epsilon>\<close>)
  show "p \<noteq> 0" using periodN_D2[OF \<open>periodN (u\<cdot>w\<cdot>v) p\<close>]. 
  fix i assume "i + p < \<^bold>|w\<^bold>|"
  hence "\<^bold>|u\<^bold>| + i + p  < \<^bold>|u\<cdot>w\<cdot>v\<^bold>|" 
    by simp
  from periodN_indeces[OF \<open>periodN (u\<cdot>w\<cdot>v) p\<close> this]
  have "(u\<cdot>w\<cdot>v)!(\<^bold>|u\<^bold>| + i) = (u\<cdot>w\<cdot>v)! (\<^bold>|u\<^bold>| + (i + p))"
    by (simp add: add.assoc)   
  thus "w!i = w!(i+p)"  
    using nth_append_length_plus[of u "w\<cdot>v" , unfolded lassoc] \<open>i + p < \<^bold>|w\<^bold>|\<close> add_lessD1[OF \<open>i + p < \<^bold>|w\<^bold>|\<close>]
      nth_append[of w v] by auto      
qed

lemma periodN_fac': "periodN v p \<Longrightarrow> u \<le>f v \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> periodN u p"
  by (elim facE, hypsubst, rule periodN_fac)

lemma assumes "y \<noteq> \<epsilon>" and "k \<noteq> 0" shows "y\<^sup>@k \<noteq> \<epsilon>"
  by (simp add: assms(1) assms(2) nemp_emp_power)


lemma pow_per: assumes "y \<noteq> \<epsilon>" and "k \<noteq> 0" shows "periodN (y\<^sup>@k) \<^bold>|y\<^bold>|"
  using periodN_I[OF \<open>k \<noteq> 0\<close>[folded nemp_emp_power[OF \<open>y \<noteq> \<epsilon>\<close>]] nemp_len[OF \<open>y \<noteq> \<epsilon>\<close>]] pref_pow_ext_take by blast  



lemma per_fac: assumes "y \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" and "y\<^sup>@k = u\<cdot>v\<cdot>w" shows "periodN v \<^bold>|y\<^bold>|"
proof-
  have "k \<noteq> 0"
    using nemp_pow suf_nemp[OF pref_nemp[OF \<open>v \<noteq> \<epsilon>\<close>, of w], of u, folded \<open>y\<^sup>@k = u\<cdot>v\<cdot>w\<close>] by blast
  from pow_per[OF \<open>y \<noteq> \<epsilon>\<close> this, unfolded \<open>y\<^sup>@k = u\<cdot>v\<cdot>w\<close>]
  have "periodN (u \<cdot> v \<cdot> w) \<^bold>|y\<^bold>|".
  from periodN_fac[OF this \<open>v \<noteq> \<epsilon>\<close>]
  show "periodN v \<^bold>|y\<^bold>|".
qed

text\<open>The numeric definition is equivalent to being prefix of a power.\<close>

theorem periodN_pref: "periodN w n \<longleftrightarrow> (\<exists>k r. w \<le>np r\<^sup>@k \<and> \<^bold>|r\<^bold>| = n)" (is "_ \<longleftrightarrow> ?R")
proof(cases "w = \<epsilon>", simp)
  assume "w \<noteq> \<epsilon>"
  show "periodN w n \<longleftrightarrow> ?R"
  proof
    assume "periodN w n" 
    consider (short) "\<^bold>|w\<^bold>| \<le> n" |  (long) "n < \<^bold>|w\<^bold>|"
      by linarith
    then show ?R
    proof(cases)
      assume "\<^bold>|w\<^bold>| \<le> n"
      from le_add_diff_inverse[OF this]
      obtain z where "\<^bold>|w \<cdot> z\<^bold>| = n" 
        unfolding length_append using exE[OF Ex_list_of_length[of "n - \<^bold>|w\<^bold>|"]] by metis     
      thus ?R
        using  pow_one_id npI'[OF \<open>w \<noteq> \<epsilon>\<close>] by metis
    next
      assume "n < \<^bold>|w\<^bold>|"
      then show ?R 
        using \<open>periodN w n\<close>[unfolded periodN_def per_pref[of w "take n w"]] 
          \<open>w \<noteq> \<epsilon>\<close> take_len[OF less_imp_le[OF \<open>n < \<^bold>|w\<^bold>|\<close>]] by blast
    qed 
  next 
    assume ?R 
    then obtain k r where "w \<le>np r\<^sup>@k" and "n = \<^bold>|r\<^bold>|" by blast
    have "w \<le>p take n w \<cdot> w"
        using  pref_pow_take[OF npD[OF \<open>w \<le>np r \<^sup>@ k\<close>], folded \<open>n = \<^bold>|r\<^bold>|\<close>].
    have "n \<noteq> 0" 
      unfolding length_0_conv[of r, folded \<open>n = \<^bold>|r\<^bold>|\<close>] using \<open>w \<le>np r \<^sup>@ k\<close> by force
    hence "take n w \<noteq> \<epsilon>" 
      unfolding \<open>n = \<^bold>|r\<^bold>|\<close> using \<open>w \<noteq> \<epsilon>\<close> by simp
    thus "periodN w n" 
      unfolding periodN_def period_root_def using \<open>w \<le>p take n w \<cdot> w\<close> by blast
  qed
qed

text \<open>Two more characterizations of a period\<close>

theorem per_shift: assumes "w \<noteq> \<epsilon>" "n \<noteq> 0" 
  shows "periodN w n \<longleftrightarrow> drop n w \<le>p w"
proof
  assume "periodN w n" show "drop n w \<le>p w"
  using drop_per_pref[OF \<open>periodN w n\<close>[unfolded periodN_def]]
  append_take_drop_id[of n w, unfolded append_eq_conv_conj] by argo
next
  assume "drop n w \<le>p w" 
  show "periodN w n"
    using conjI[OF pref_cancel'[OF \<open>drop n w \<le>p w\<close>, of "take n w"] take_nemp[OF \<open>w \<noteq> \<epsilon>\<close> \<open>n \<noteq> 0\<close>]]
    unfolding  append_take_drop_id period_root_def by force
qed

lemma rotate_per_root: assumes "w \<noteq> \<epsilon>" and "n \<noteq> 0" and "w = rotate n w" 
  shows "periodN w n" 
proof (cases "\<^bold>|w\<^bold>| \<le> n")
  assume "\<^bold>|w\<^bold>| \<le> n"
  from all_long_pers[OF \<open>w \<noteq> \<epsilon>\<close>, OF this]
  show "periodN w n".
next
  assume not: "\<not> \<^bold>|w\<^bold>| \<le> n"
  have "drop (n mod \<^bold>|w\<^bold>|) w \<le>p w"
    using prefI[OF rotate_drop_take[symmetric, of n w]]
    unfolding \<open>w = rotate n w\<close>[symmetric].
  from per_shift[OF \<open>w \<noteq> \<epsilon>\<close> \<open>n \<noteq> 0\<close>] this[unfolded mod_less[OF not[unfolded not_le]]]
  show "periodN w n".. 
qed

subsubsection \<open>Various lemmas on periods\<close>

lemma periodN_drop: assumes "periodN w p" and "p < \<^bold>|w\<^bold>|"
  shows "periodN (drop p w) p"
  using periodN_fac[of "take p w" "drop p w" \<epsilon> p] \<open>p < \<^bold>|w\<^bold>|\<close> \<open>periodN w p\<close> 
  unfolding append_take_drop_id drop_eq_Nil not_le append_Nil2 by blast  

lemma ext_per_left: assumes "periodN w p" and  "p \<le> \<^bold>|w\<^bold>|" 
  shows "periodN (take p w \<cdot> w) p"
proof-
  have f: "take p (take p w \<cdot> w) = take p w" 
    using \<open>p \<le> \<^bold>|w\<^bold>|\<close> by simp
  show ?thesis
    using  \<open>periodN w p\<close> pref_cancel'[of w "take p w \<cdot> w" "take p w" ] unfolding f periodN_def period_root_def
    by blast
qed

lemma ext_per_left_power: "periodN w p \<Longrightarrow> p \<le> \<^bold>|w\<^bold>| \<Longrightarrow> periodN ((take p w)\<^sup>@k \<cdot> w) p"
proof (induction k)
  case (Suc k)
  show ?case 
    using ext_per_left[OF Suc.IH[OF \<open>periodN w p\<close> \<open>p \<le> \<^bold>|w\<^bold>|\<close>]] \<open>p \<le> \<^bold>|w\<^bold>|\<close>
    unfolding pref_share_take[OF per_exp_pref[OF periodN_D3[OF \<open>periodN w p\<close>]] \<open>p \<le> \<^bold>|w\<^bold>|\<close>,symmetric] 
      lassoc pow_Suc_list[symmetric] by fastforce
qed auto

lemma take_several_pers: assumes "periodN w n" and "m*n \<le> \<^bold>|w\<^bold>|"
  shows "(take n w)\<^sup>@m = take (m*n) w"
proof (cases "m = 0", simp)
  assume "m \<noteq> 0" 
  have "\<^bold>|(take n w)\<^sup>@m\<^bold>| = m*n"
    unfolding pow_len nat_prod_le[OF \<open>m \<noteq> 0\<close> \<open>m*n \<le> \<^bold>|w\<^bold>|\<close>, THEN take_len] by blast 
  have "(take n w)\<^sup>@m \<le>p w"
    using  \<open>periodN w n\<close>[unfolded periodN_def, THEN  per_exp[of w "take n w" m], THEN 
      ruler_le[of "take n w\<^sup>@m" "take n w\<^sup>@m \<cdot> w" w, OF triv_pref], OF  \<open>m * n \<le> \<^bold>|w\<^bold>|\<close>[folded \<open>\<^bold>|take n w\<^sup>@m\<^bold>| = m * n\<close>]].
  show ?thesis                                   
    using pref_take[OF \<open>take n w\<^sup>@m \<le>p w\<close>, unfolded  \<open>\<^bold>|take n w\<^sup>@m\<^bold>| = m * n\<close>, symmetric].
qed

lemma per_mult: assumes "periodN w n" and "m \<noteq> 0" shows "periodN w (m*n)"
proof (cases "m*n \<le> \<^bold>|w\<^bold>|")
  have "w \<noteq> \<epsilon>" using periodN_D1[OF \<open>periodN w n\<close>]. 
  assume "\<not> m * n \<le> \<^bold>|w\<^bold>|" thus "periodN w (m*n)"
    using all_long_pers[of  w "m * n", OF \<open>w \<noteq> \<epsilon>\<close>] by linarith
next 
  assume "m * n \<le> \<^bold>|w\<^bold>|"
  show "periodN w (m*n)"
    using  per_add_exp[of w "take n w", OF _ \<open>m \<noteq> 0\<close>] \<open>periodN w n\<close> 
    unfolding periodN_def period_root_def take_several_pers[OF \<open>periodN w n\<close> \<open>m*n \<le> \<^bold>|w\<^bold>|\<close>, symmetric] by blast
qed

lemma root_periodN: assumes "w \<noteq> \<epsilon>" and  "w \<le>p r\<^sup>\<omega>" shows "periodN w \<^bold>|r\<^bold>|"
  unfolding periodN_def period_root_def using  per_pref_ex[OF \<open>w \<le>p r\<^sup>\<omega>\<close> 
  pref_pow_take[of w r], of "\<lambda> x. x"] take_nemp_len[OF \<open>w \<noteq> \<epsilon>\<close>  per_rootD'[OF \<open>w \<le>p r\<^sup>\<omega>\<close>]] by blast  

theorem  two_periodsN:
  assumes "periodN w p" "periodN w q"  "p + q \<le> \<^bold>|w\<^bold>|" 
  shows "periodN w (gcd p q)"
proof-
  obtain t where "take p w \<in> t*" "take q w \<in> t*" 
    using two_pers[OF \<open>periodN w p\<close>[unfolded periodN_def] \<open>periodN w q\<close>[unfolded periodN_def],
        unfolded take_len[OF add_leD1[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]] take_len[OF add_leD2[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]],
        OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>, unfolded comm_root[of "take p w" "take q w"]] by blast
  hence "w \<le>p t\<^sup>\<omega>"
    using \<open>periodN w p\<close> periodN_def per_root_trans by blast
  have "periodN w \<^bold>|t\<^bold>|"
    using  root_periodN[OF  per_nemp[OF \<open>periodN w p\<close>] \<open>w \<le>p t\<^sup>\<omega>\<close>]. 
  have "\<^bold>|t\<^bold>| dvd (gcd p q)"
    using gcd_nat.boundedI[OF root_len_dvd[OF \<open>take p w \<in> t*\<close>] root_len_dvd[OF \<open>take q w \<in> t*\<close>]] 
    unfolding take_len[OF add_leD1[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]] take_len[OF add_leD2[OF \<open>p + q \<le> \<^bold>|w\<^bold>|\<close>]]. 
  thus ?thesis 
    using  per_mult[OF \<open>periodN w \<^bold>|t\<^bold>|\<close>, of "gcd p q div \<^bold>|t\<^bold>|", unfolded dvd_div_mult_self[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>]]
      dvd_div_mult_self[OF \<open>\<^bold>|t\<^bold>| dvd (gcd p q)\<close>]
      gcd_eq_0_iff[of p q] mult_zero_left[of "\<^bold>|t\<^bold>|"] periodN_D2[OF \<open>periodN w p\<close>] by argo
qed

lemma index_mod_per_root: assumes "r \<noteq> \<epsilon>" and i: "\<forall> i < \<^bold>|w\<^bold>|. w!i = r!(i mod \<^bold>|r\<^bold>|)" shows  "w \<le>p r\<^sup>\<omega>"
proof-
  have "i < \<^bold>|w\<^bold>| \<Longrightarrow> (r \<cdot> w) ! i = r ! (i mod \<^bold>|r\<^bold>|)" for i
    by (simp add: i mod_if nth_append)
  hence "w \<le>p r \<cdot> w"
    using index_pref[of w "r \<cdot> w"] i
    by simp 
  thus ?thesis unfolding period_root_def using \<open>r \<noteq> \<epsilon>\<close> by auto 
qed

lemma index_pref_pow_mod: "w \<le>p r\<^sup>@k \<Longrightarrow> i < \<^bold>|w\<^bold>| \<Longrightarrow>  w!i = r!(i mod \<^bold>|r\<^bold>| )"
  using  index_pow_mod[of i r k] less_le_trans[of i "\<^bold>|w\<^bold>|" "\<^bold>|r\<^sup>@k\<^bold>|"] prefix_length_le[of w "r\<^sup>@k"] pref_index[of w "r\<^sup>@k" i] by argo

lemma index_per_root_mod: "w \<le>p r\<^sup>\<omega> \<Longrightarrow> i < \<^bold>|w\<^bold>| \<Longrightarrow>  w!i = r!(i mod \<^bold>|r\<^bold>|)"
  using index_pref_pow_mod[of w r _ i] per_pref[of w r ] by blast

lemma root_divisor: assumes "periodN w k" and  "k dvd \<^bold>|w\<^bold>|" shows "w \<in> (take k w)*"
  using rootI[of "take k w" "(\<^bold>|w\<^bold>| div k)"] unfolding 
    take_several_pers[OF \<open>periodN w k\<close>, of "\<^bold>|w\<^bold>| div k", unfolded dvd_div_mult_self[OF \<open>k dvd \<^bold>|w\<^bold>|\<close>] take_self, OF , OF order_refl]. 

lemma per_pref': assumes "u \<noteq> \<epsilon>" and "periodN v k" and  "u \<le>p v" shows "periodN u k" 
proof-
  { assume "k \<le> \<^bold>|u\<^bold>|"
    have "take k v = take k u"
      using  pref_share_take[OF \<open>u \<le>p v\<close> \<open>k \<le> \<^bold>|u\<^bold>|\<close>]  by auto
    hence "take k v \<noteq> \<epsilon>"
      using \<open>periodN v k\<close> by auto
    hence "take k u \<noteq> \<epsilon>"
      by (simp add: \<open>take k v = take k u\<close>)
    have "u \<le>p take k u \<cdot> v" 
      using  \<open>periodN v k\<close>  
      unfolding periodN_def period_root_def \<open>take k v = take k u\<close> 
      using pref_trans[OF \<open>u \<le>p v\<close>, of "take k u \<cdot> v"]
      by blast 
    hence "u \<le>p take k u \<cdot> u"
      using \<open>u \<le>p v\<close> pref_prod_pref by blast 
    hence ?thesis
      using \<open>take k u \<noteq> \<epsilon>\<close> periodN_def by fast
  }
  thus ?thesis
    using \<open>u \<noteq> \<epsilon>\<close> all_long_pers nat_le_linear by blast
qed

subsection "Period: overview"
notepad
begin
  fix w r::"'a list" 
  fix n::nat
  assume "w \<noteq> \<epsilon>" "r \<noteq> \<epsilon>" "n > 0"
  have "\<not> w \<le>p \<epsilon>\<^sup>\<omega>"
    by simp
  have "\<not> \<epsilon> \<le>p \<epsilon>\<^sup>\<omega>"
    by simp
  have "\<epsilon> \<le>p r\<^sup>\<omega>"
    by (simp add: \<open>r \<noteq> \<epsilon>\<close>)
  have "\<not> periodN w 0"
    by simp
  have "\<not> periodN \<epsilon> 0"
    by simp
  have "\<not> periodN \<epsilon> n"
    by simp
end

subsection \<open>Singleton and its power\<close>

lemma concat_len_one: assumes "\<^bold>|us\<^bold>| = 1" shows "concat us = hd us"
  using concat_sing[OF sing_word[OF \<open>\<^bold>|us\<^bold>| = 1\<close>, symmetric]].   

lemma sing_pow_hd_tl: "c # w \<in> [a]* \<longleftrightarrow> c = a \<and> w \<in> [a]*"
proof
  assume "c = a \<and> w \<in> [a]*"
  thus "c # w \<in> [a]*"
    unfolding  hd_word[of _ w]  using add_root[of "[c]" w] by simp
next
  assume "c # w \<in> [a]*"
  then obtain k where "[a]\<^sup>@k = c # w" unfolding root_def by blast 
  thus "c = a \<and> w \<in> [a]*"
  proof (cases "k = 0", simp)
    assume "[a] \<^sup>@ k = c # w" and "k \<noteq> 0"
    from eqd_equal[of "[a]", OF this(1)[unfolded hd_word[of _ w] pop_pow_one[OF \<open>k \<noteq> 0\<close>]]]
    show ?thesis 
      unfolding root_def by auto
  qed
qed

lemma pref_sing_power: assumes "w \<le>p [a]\<^sup>@m" shows "w = [a]\<^sup>@(\<^bold>|w\<^bold>|)"
proof-
  have  "[a]\<^sup>@m = [a]\<^sup>@(\<^bold>|w\<^bold>|)\<cdot>[a]\<^sup>@(m-\<^bold>|w\<^bold>|)"
    using pop_pow[OF prefix_length_le[OF assms, unfolded sing_pow_len], of "[a]", symmetric].
  show ?thesis
    using  conjunct1[OF eqd_equal[of w "w\<inverse>\<^sup>>[a]\<^sup>@m" "[a]\<^sup>@(\<^bold>|w\<^bold>|)""[a]\<^sup>@(m-\<^bold>|w\<^bold>|)", 
          unfolded lq_pref[OF assms] sing_pow_len, 
          OF \<open>[a]\<^sup>@m = [a]\<^sup>@(\<^bold>|w\<^bold>|)\<cdot>[a]\<^sup>@(m-\<^bold>|w\<^bold>|)\<close> refl]]. 
qed

lemma sing_pow_palindrom: assumes "w = [a]\<^sup>@k" shows "rev w = w"
  using rev_pow[of "[a]" "\<^bold>|w\<^bold>|", unfolded rev_sing] 
  unfolding pref_sing_power[of w a k, unfolded assms[unfolded root_def, symmetric], OF self_pref, symmetric].

lemma suf_sing_power: assumes "w \<le>s [a]\<^sup>@m" shows "w \<in> [a]*"
  using sing_pow_palindrom[of "rev w" a "\<^bold>|rev w\<^bold>|", unfolded rev_rev_ident]
    pref_sing_power[of "rev w" a m, OF \<open>w \<le>s [a]\<^sup>@m\<close>[unfolded suffix_to_prefix rev_pow rev_rev_ident rev_sing]] 
    rootI[of "[a]" "\<^bold>|rev w\<^bold>|"]  by auto

lemma sing_fac_pow: assumes "w \<in> [a]*" and  "v \<le>f w" shows "v \<in> [a]*"
proof-
  obtain k where "w = [a]\<^sup>@k" using \<open>w \<in> [a]*\<close>[unfolded root_def] by blast
  obtain p where "p \<le>p w" and "v \<le>s p" 
    using fac_pref_suf[OF \<open> v \<le>f w\<close>] by blast
  hence "v \<le>s [a]\<^sup>@ \<^bold>|p\<^bold>|"
     using pref_sing_power[OF \<open>p \<le>p w\<close>[unfolded \<open>w = [a]\<^sup>@k\<close>]] by argo
  from suf_sing_power[OF this]
  show ?thesis.
qed

lemma sing_pow_fac': assumes "a \<noteq> b" and  "w \<in> [a]*" shows "\<not> ([b] \<le>f w)"
  using sing_fac_pow[OF \<open> w \<in> [a]*\<close>, of "[b]"] unfolding sing_pow_hd_tl[of b \<epsilon>] 
  using \<open>a \<noteq> b\<close> by auto  

lemma all_set_sing_pow: "(\<forall> b. b \<in> set w \<longrightarrow> b = a) \<longleftrightarrow> w \<in> [a]*" (is "?All \<longleftrightarrow> _")
proof
  assume ?All
  then show "w \<in> [a]*"
  proof (induct w, simp)
    case (Cons c w)
    then show ?case
      by (simp add: sing_pow_hd_tl)
  qed
  next
  assume "w \<in> [a]*"
  then show ?All
  proof (induct w, simp)
    case (Cons c w)
    then show ?case
      unfolding sing_pow_hd_tl by simp 
  qed
qed

lemma sing_pow_set: "u \<in> [a]* \<Longrightarrow> u \<noteq> \<epsilon> \<Longrightarrow> set u = {a}"
  unfolding all_set_sing_pow[symmetric]
  using hd_in_set[of u] is_singletonI'[unfolded is_singleton_the_elem, of "set u"]
     singleton_iff[of a "the_elem (set u)"]
  by auto

lemma takeWhile_sing_root: "takeWhile (\<lambda> x. x = a) w \<in> [a]*"
  unfolding all_set_sing_pow[symmetric] using set_takeWhileD[of _ "\<lambda> x. x = a" w] by blast

lemma takeWhile_sing_pow: "takeWhile (\<lambda> x. x = a) w = w \<longleftrightarrow> w = [a]\<^sup>@\<^bold>|w\<^bold>|"
  by(induct w,  auto)

lemma dropWhile_sing_pow: "dropWhile (\<lambda> x. x = a) w = \<epsilon> \<longleftrightarrow> w = [a]\<^sup>@\<^bold>|w\<^bold>|"
  by(induct w,  auto)

lemma distinct_letter_in: assumes "\<not> w \<in> [a]*" 
  obtains m b q where "[a]\<^sup>@m \<cdot> [b] \<cdot> q = w" and "b \<noteq> a"
proof-
  have "dropWhile (\<lambda> x. x = a) w \<noteq> \<epsilon>"
    unfolding dropWhile_sing_pow using assms rootI[of "[a]" "\<^bold>|w\<^bold>|"] by auto    
  hence eq: "takeWhile (\<lambda> x. x = a) w \<cdot> [hd (dropWhile (\<lambda> x. x = a) w)] \<cdot> tl (dropWhile (\<lambda> x. x = a) w) = w"
    by simp
  have root:"takeWhile (\<lambda> x. x = a) w \<in> [a]*"
    by (simp add: takeWhile_sing_root)   
  have  "hd (dropWhile (\<lambda> x. x = a) w) \<noteq> a" 
    using hd_dropWhile[OF \<open>dropWhile (\<lambda>x. x = a) w \<noteq> \<epsilon>\<close>].
  from that[OF _  this] 
  show thesis
    using eq root unfolding root_def by metis
qed

lemma distinct_letter_in_hd: assumes "\<not> w \<in>  [hd w]*"
  obtains m b q where  "[hd w]\<^sup>@m \<cdot> [b] \<cdot> q = w" and "b \<noteq> hd w" and "m \<noteq> 0"
proof-
  obtain m b q where a1: "[hd w]\<^sup>@m \<cdot> [b] \<cdot> q = w" and a2: "b \<noteq> hd w"
    using distinct_letter_in[OF assms].   
  hence "m \<noteq> 0"
    using power_eq_if[of "[hd w]" m] list.sel(1) by fastforce 
  from that a1 a2 this 
  show thesis by blast
qed

lemma distinct_letter_in_suf: assumes "\<not> w \<in>  [a]*" shows "\<exists> m b. [b] \<cdot> [a]\<^sup>@m  \<le>s w \<and> b \<noteq> a" 
proof-
  have  "\<not> rev w \<in>  [a]*"
    using rev_pow[of "[a]"] unfolding  rev_sing using assms root_def rev_rev_ident[of w]
    by metis
  obtain m b q where "[a]\<^sup>@m \<cdot> [b] \<cdot> q = rev w" and "b \<noteq> a"
    using distinct_letter_in[OF \<open>\<not> rev w \<in>  [a]*\<close>]  by blast
  have eq: "rev ([b] \<cdot> [a]\<^sup>@m) = [a]\<^sup>@m \<cdot> [b]"
    by (simp add: rev_pow) 
  have "[b] \<cdot> [a]\<^sup>@m \<le>s w"
    using  \<open>[a]\<^sup>@m \<cdot> [b] \<cdot> q = rev w\<close> unfolding suf_rev_pref_iff eq lassoc 
    using prefI by blast
  thus ?thesis
    using \<open>b \<noteq> a\<close> by blast
qed

lemma sing_pow_exp: assumes "w \<in> [a]*" shows "w = [a]\<^sup>@\<^bold>|w\<^bold>|"
proof-
  obtain k where "[a] \<^sup>@ k = w"
    using rootE[OF assms].
  from this[folded  sing_pow_len[of a k, folded this, unfolded this], symmetric]
  show ?thesis.
qed

lemma sing_power': assumes "w \<in> [a]*" and "i < \<^bold>|w\<^bold>|" shows "w ! i = a"
  using  sing_pow[OF \<open>i < \<^bold>|w\<^bold>|\<close>, of a, folded sing_pow_exp[OF \<open>w \<in> [a]*\<close>]]. 

lemma rev_sing_power: "x \<in> [a]* \<Longrightarrow> rev x = x"
  unfolding root_def using rev_pow rev_singleton_conv  by metis

lemma lcp_letter_power: 
  assumes "w \<noteq> \<epsilon>" and "w \<in> [a]*" and "[a]\<^sup>@m \<cdot> [b] \<le>p z" and  "a \<noteq> b" 
  shows "w \<cdot> z \<and>\<^sub>p z \<cdot> w = [a]\<^sup>@m"                     
proof-
  obtain k z' where "w = [a]\<^sup>@k" "z = [a]\<^sup>@m \<cdot> [b] \<cdot> z'" "k \<noteq> 0"
    using \<open>w \<in> [a]*\<close> \<open>[a]\<^sup>@m \<cdot> [b] \<le>p z\<close> \<open>w \<noteq> \<epsilon>\<close> nemp_pow[of "[a]"]   
    unfolding root_def
    by auto 
  hence eq1: "w \<cdot> z = [a]\<^sup>@m \<cdot> ([a]\<^sup>@k \<cdot> [b] \<cdot> z')" and eq2: "z \<cdot> w = [a]\<^sup>@m \<cdot> ([b] \<cdot> z'\<cdot> [a]\<^sup>@k)"
    by (simp add: \<open>w = [a]\<^sup>@k\<close> \<open>z = [a]\<^sup>@m \<cdot> [b] \<cdot> z'\<close> pow_comm)+
  have "hd ([a]\<^sup>@k \<cdot> [b] \<cdot> z') = a" 
    using hd_append2[OF \<open>w \<noteq> \<epsilon>\<close>, of "[b]\<cdot>z'", 
        unfolded \<open>w = (a # \<epsilon>)\<^sup>@k\<close> hd_sing_power[OF \<open>k \<noteq> 0\<close>, of a]].
  moreover have "hd([b] \<cdot> z'\<cdot> [a]\<^sup>@k) = b"
    by simp 
  ultimately have "[a]\<^sup>@k \<cdot> [b] \<cdot> z' \<and>\<^sub>p [b] \<cdot> z'\<cdot> [a]\<^sup>@k = \<epsilon>"
    by (simp add: \<open>a \<noteq> b\<close> lcp_distinct_hd) 
  thus ?thesis using eq1 eq2 lcp_ext_left[of "[a]\<^sup>@m" "[a]\<^sup>@k \<cdot> [b] \<cdot> z'" "[b] \<cdot> z'\<cdot> [a]\<^sup>@k"]
    by simp
qed

lemma per_one: assumes "w \<le>p [a]\<^sup>\<omega>" shows "w \<in> [a]*"
proof-
  have "w \<le>p (a # \<epsilon>) \<^sup>@ n \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> w \<in> [a]*" for n
    using pref_sing_power[of w a] rootI[of "[a]" "\<^bold>|w\<^bold>|"] by auto
  with per_pref_ex[OF \<open>w \<le>p [a]\<^sup>\<omega>\<close>]
  show ?thesis by auto
qed 

lemma per_one': "w \<in> [a]* \<Longrightarrow> w \<le>p [a]\<^sup>\<omega>"
  by (metis append_Nil2 not_Cons_self2 per_pref prefI root_def)

lemma per_sing_one: assumes "w \<noteq> \<epsilon>" "w \<le>p [a]\<^sup>\<omega>" shows "periodN w 1"
  using root_periodN[OF \<open>w \<noteq> \<epsilon>\<close> \<open>w \<le>p [a]\<^sup>\<omega>\<close>] unfolding sing_len[of a].

section "Border"

text\<open>A non-empty word  $x \neq w$ is a \emph{border} of a word $w$ if it is both its prefix and suffix. This elementary property captures how much the word $w$ overlaps
with itself, and it is in the obvious way related to a period of $w$. However, in many cases it is much easier to reason about borders than about periods.\<close>

definition border :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<le>b _" [51,51] 60 )
  where [simp]: "border x w = (x \<le>p w \<and> x \<le>s w \<and> x \<noteq> w \<and> x \<noteq> \<epsilon>)"

definition bordered :: "'a list \<Rightarrow> bool" 
  where [simp]: "bordered w = (\<exists>b. b \<le>b w)"

lemma borderI[intro]: "x \<le>p w \<Longrightarrow> x \<le>s w \<Longrightarrow> x \<noteq> w \<Longrightarrow> x \<noteq> \<epsilon> \<Longrightarrow> x \<le>b w"
  unfolding border_def by blast

lemma borderD_pref: "x \<le>b w \<Longrightarrow> x \<le>p w"
  unfolding border_def by blast

lemma borderD_spref: "x \<le>b w \<Longrightarrow> x <p w"
  unfolding border_def  by simp

lemma borderD_suf: "x \<le>b w \<Longrightarrow> x \<le>s w"
  unfolding border_def by blast

lemma borderD_ssuf: "x \<le>b w \<Longrightarrow> x <s w"
  unfolding border_def by blast

lemma borderD_nemp: "x \<le>b w \<Longrightarrow> x \<noteq> \<epsilon>"
  using border_def by blast

lemma borderD_neq: "x \<le>b w \<Longrightarrow> x \<noteq> w"
  unfolding border_def by blast

lemma border_lq_nemp: assumes "x \<le>b w" shows "x\<inverse>\<^sup>>w \<noteq> \<epsilon>"
  using assms borderD_spref lq_spref by blast 

lemma border_rq_nemp: assumes "x \<le>b w" shows "w\<^sup><\<inverse>x \<noteq> \<epsilon>"
  using assms borderD_ssuf rq_ssuf by blast

lemma border_trans[trans]: assumes "t \<le>b x" "x \<le>b w"
  shows "t \<le>b w"
  using assms unfolding border_def 
  using suffix_order.order.antisym pref_trans[of t x w] suf_trans[of t x w] by blast
    
lemma border_rev_conv[reversal_rule]: "rev x \<le>b rev w \<longleftrightarrow> x \<le>b w"
  unfolding border_def
  using rev_is_Nil_conv[of x] rev_swap[of w] rev_swap[of x]
    suf_rev_pref_iff[of x w] pref_rev_suf_iff[of x w]
  by fastforce

lemma border_lq_comp: "x \<le>b w \<Longrightarrow> (w\<^sup><\<inverse>x) \<bowtie> x"
  unfolding border_def using rq_suf ruler by blast

lemmas border_lq_suf_comp = border_lq_comp[reversed]

subsection "The shortest border"

lemma border_len:  assumes "x \<le>b w"
  shows "1 < \<^bold>|w\<^bold>|" and "0 < \<^bold>|x\<^bold>|" and "\<^bold>|x\<^bold>| < \<^bold>|w\<^bold>|" 
proof-
  show "\<^bold>|x\<^bold>| < \<^bold>|w\<^bold>|"
    using assms prefix_length_less unfolding border_def strict_prefix_def
    by blast
  show "0 < \<^bold>|x\<^bold>|"
    using assms unfolding border_def by blast
  thus "1 < \<^bold>|w\<^bold>|"
    using assms \<open>\<^bold>|x\<^bold>| < \<^bold>|w\<^bold>|\<close> unfolding border_def
    by linarith 
qed

lemma borders_compare: assumes "x \<le>b w" and "x' \<le>b w" and "\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|"
  shows "x' \<le>b x"
  using ruler_le[OF borderD_pref[OF \<open>x' \<le>b w\<close>] borderD_pref[OF \<open>x \<le>b w\<close>] less_imp_le_nat[OF \<open>\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|\<close>]]
    suf_ruler_le[OF borderD_suf[OF \<open>x' \<le>b w\<close>] borderD_suf[OF \<open>x \<le>b w\<close>] less_imp_le_nat[OF \<open>\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|\<close>]]
    borderD_nemp[OF \<open>x' \<le>b w\<close>] \<open>\<^bold>|x'\<^bold>| < \<^bold>|x\<^bold>|\<close>
    borderI by blast

lemma unbordered_border: 
  "bordered w \<Longrightarrow>  \<exists> x. x \<le>b w \<and> \<not> bordered x"
proof (induction "\<^bold>|w\<^bold>|" arbitrary: w rule: less_induct)
  case less
  obtain x' where "x' \<le>b w"
    using bordered_def less.prems by blast
  show ?case 
  proof (cases "bordered x'")
    assume "\<not> bordered x'" 
    thus ?case 
      using \<open>x' \<le>b w\<close> by blast
  next 
    assume "bordered x'"
    from less.hyps[OF border_len(3)[OF \<open>x' \<le>b w\<close>] this]
    show ?case 
      using  border_trans[of _ x' w] \<open>x' \<le>b w\<close> by blast 
  qed
qed

lemma unbordered_border_shortest: "x \<le>b w \<Longrightarrow> \<not> bordered x \<Longrightarrow>  y \<le>b w \<Longrightarrow> \<^bold>|x\<^bold>| \<le> \<^bold>|y\<^bold>|"
  using bordered_def[of x] borders_compare[of x w y] not_le_imp_less[of "\<^bold>|x\<^bold>|" "\<^bold>|y\<^bold>|"] by blast

lemma long_border_bordered: assumes long: "\<^bold>|w\<^bold>| < \<^bold>|x\<^bold>| + \<^bold>|x\<^bold>|" and border: "x \<le>b w" 
  shows "(w\<^sup><\<inverse>x)\<inverse>\<^sup>>x \<le>b x"
proof-
  define p s where "p = w\<^sup><\<inverse>x" and "s = x\<inverse>\<^sup>>w"
  hence eq: "p\<cdot>x = x\<cdot>s"   
    using assms unfolding border_def using lq_pref[of x w] rq_suf[of x w]  by simp
  have "\<^bold>|p\<^bold>| < \<^bold>|x\<^bold>|"
    using p_def long[folded rq_len[OF borderD_suf[OF border]]] by simp
  have px: "p \<cdot> p\<inverse>\<^sup>>x = x" and sx: "p\<inverse>\<^sup>>x \<cdot> s = x"  
    using eqd_pref[OF eq less_imp_le, OF \<open>\<^bold>|p\<^bold>| < \<^bold>|x\<^bold>|\<close>] by blast+
  have "p\<inverse>\<^sup>>x \<noteq> \<epsilon>"
    using \<open>\<^bold>|p\<^bold>| < \<^bold>|x\<^bold>|\<close> px by fastforce
  have "p \<noteq> \<epsilon>"
    using border_rq_nemp[OF border] p_def
    by presburger
  have "p\<inverse>\<^sup>>x \<noteq> x"
    using \<open>p \<noteq> \<epsilon>\<close> px by force
  have "(p\<inverse>\<^sup>>x) \<le>b x" 
    unfolding border_def 
    using eqd_pref[OF eq less_imp_le, OF \<open>\<^bold>|p\<^bold>| < \<^bold>|x\<^bold>|\<close>] \<open>p\<inverse>\<^sup>>x \<noteq> \<epsilon>\<close> \<open>p\<inverse>\<^sup>>x \<noteq> x\<close> by blast
  thus ?thesis 
    unfolding p_def.
qed

thm long_border_bordered[reversed]

lemma border_short_dec: assumes border: "x \<le>b w" and short: "\<^bold>|x\<^bold>| + \<^bold>|x\<^bold>| \<le> \<^bold>|w\<^bold>|"
  shows "x \<cdot> x\<inverse>\<^sup>>(w\<^sup><\<inverse>x) \<cdot> x = w"
proof-
  have eq: "x\<cdot>x\<inverse>\<^sup>>w = w\<^sup><\<inverse>x\<cdot>x"
    using lq_pref[OF borderD_pref[OF border]] rq_suf[OF borderD_suf[OF border]] by simp  
  have "\<^bold>|x\<^bold>| \<le> \<^bold>|w\<^sup><\<inverse>x\<^bold>|"
    using short[folded rq_len[OF borderD_suf[OF border]]] by simp
  from  lq_pref[of x w, OF borderD_pref[OF border], folded conjunct2[OF eqd_pref[OF eq this]]]
  show ?thesis.
qed

lemma bordered_dec: assumes "bordered w" 
  obtains u v where "u\<cdot>v\<cdot>u = w" and "u \<noteq> \<epsilon>"
proof-
  obtain u where "u \<le>b w" and "\<not> bordered u"
    using unbordered_border[OF assms] by blast
  have "\<^bold>|u\<^bold>| + \<^bold>|u\<^bold>| \<le> \<^bold>|w\<^bold>|"
    using long_border_bordered[OF _ \<open>u \<le>b w\<close>] \<open>\<not> bordered u\<close> bordered_def leI by blast 
  from border_short_dec[OF \<open>u \<le>b w\<close> this, THEN that, OF borderD_nemp[OF \<open>u \<le>b w\<close>]]
  show thesis.
qed

subsection "Relation to period and conjugation"

lemma border_conjug_eq: "x \<le>b w \<Longrightarrow> (w\<^sup><\<inverse>x) \<cdot> w = w \<cdot> (x\<inverse>\<^sup>>w)"
  using lq_rq_reassoc_suf[OF borderD_pref borderD_suf, symmetric] by blast

lemma border_per_root: "x \<le>b w \<Longrightarrow> w \<le>p (w\<^sup><\<inverse>x) \<cdot> w"
  using border_conjug_eq by blast

lemma per_root_border: assumes "\<^bold>|r\<^bold>| < \<^bold>|w\<^bold>|" and "r \<noteq> \<epsilon>" and "w \<le>p r \<cdot> w" 
  shows "r\<inverse>\<^sup>>w \<le>b w"  
proof   
  have "\<^bold>|r\<^bold>| \<le> \<^bold>|w\<^bold>|" and "r \<le>p w"
    using less_imp_le[OF \<open>\<^bold>|r\<^bold>| < \<^bold>|w\<^bold>|\<close>] pref_prod_long[OF \<open>w \<le>p r \<cdot> w\<close>] by blast+
  show "r\<inverse>\<^sup>>w \<le>p w"
    using pref_lq[OF \<open>r \<le>p w\<close> \<open>w \<le>p r \<cdot> w\<close>] unfolding lq_triv.
  show "r\<inverse>\<^sup>>w \<le>s w"
    using \<open>r \<le>p w\<close> by auto
  show "r\<inverse>\<^sup>>w \<noteq> w"
    using \<open>r \<le>p w\<close> \<open>r \<noteq> \<epsilon>\<close> by force 
  show "r\<inverse>\<^sup>>w \<noteq> \<epsilon>"
    using lq_pref[OF \<open>r \<le>p w\<close>] \<open>\<^bold>|r\<^bold>| < \<^bold>|w\<^bold>|\<close> by force
qed

lemma border_per: assumes "x \<le>b w" shows "periodN w (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|)" 
proof-
  have "w = (w\<^sup><\<inverse>x)\<cdot>x"  
    using rq_suf[OF borderD_suf[OF assms]] by simp
  have "w = x\<cdot>(x\<inverse>\<^sup>>w)"  
    using lq_pref[OF borderD_pref[OF assms]] by simp
  have take: "take (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|) w = w\<^sup><\<inverse>x"
    using borderD_suf[OF assms] by auto
  have nemp: "take (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|) w \<noteq> \<epsilon>"
    using assms by auto 
  have "w \<le>p take (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|) w \<cdot> w"
    unfolding take  lassoc[of "w\<^sup><\<inverse>x" x "x\<inverse>\<^sup>>w", folded \<open>w = x \<cdot> x\<inverse>\<^sup>>w\<close> \<open>w = w\<^sup><\<inverse>x \<cdot> x\<close>] 
    using  triv_pref[of w "x\<inverse>\<^sup>>w"].
  thus "periodN w (\<^bold>|w\<^bold>|-\<^bold>|x\<^bold>|)" 
    unfolding periodN_def period_root_def using nemp by blast 
qed

lemma per_border: assumes "n < \<^bold>|w\<^bold>|" and "periodN w n" 
  shows "take (\<^bold>|w\<^bold>| - n) w  \<le>b w"
proof-
  have eq: "take (\<^bold>|w\<^bold>| - n) w = drop n w" 
    using pref_take[OF \<open>periodN w n\<close>[unfolded per_shift[OF periodN_D1[OF \<open>periodN w n\<close>] per_positive[OF \<open>periodN w n\<close>]]], unfolded length_drop].
  have "take (\<^bold>|w\<^bold>| - n) w \<noteq> \<epsilon>"
    using \<open>n < \<^bold>|w\<^bold>|\<close> take_eq_Nil by fastforce
  moreover have "take (\<^bold>|w\<^bold>| - n) w \<noteq> w" 
    using  periodN_D2[OF \<open>periodN w n\<close>] \<open>n < \<^bold>|w\<^bold>|\<close> unfolding take_all_iff[of "\<^bold>|w\<^bold>|-n" w] by fastforce
  ultimately show ?thesis 
    unfolding border_def using take_is_prefix[of "\<^bold>|w\<^bold>|-n" w] suffix_drop[of n w, folded eq] by blast
qed


section \<open>Primitive words\<close>

text\<open>If a word $w$ is not a non-trivial power of some other word, we say it is primitive.\<close>

definition primitive :: "'a list \<Rightarrow> bool" 
  where  "primitive u = (\<forall> r k. r\<^sup>@k = u \<longrightarrow> k = 1)"

lemma primI: "(\<And> r k. r\<^sup>@k = u \<Longrightarrow> k = 1) \<Longrightarrow> primitive u"
  by (simp add: primitive_def)

lemma prim_nemp: "primitive u \<Longrightarrow> u \<noteq> \<epsilon>"
proof-
  have "u = \<epsilon> \<Longrightarrow> \<epsilon>\<^sup>@0 = u" by simp
  thus "primitive u \<Longrightarrow> u \<noteq> \<epsilon>"
    using primitive_def zero_neq_one by blast
qed

lemma prim_exp_one: "primitive u \<Longrightarrow> r\<^sup>@k = u \<Longrightarrow> k = 1"
  using primitive_def by blast

lemma prim_exp_eq: "primitive u \<Longrightarrow> r\<^sup>@k = u \<Longrightarrow> u = r"
  using prim_exp_one power_one_right by blast

lemma prim_triv_root: "primitive u \<Longrightarrow> u \<in> t* \<Longrightarrow> t = u"
  using prim_exp_eq unfolding root_def 
  unfolding primitive_def root_def by fastforce

lemma prim_comm_exp[elim]: assumes "primitive v" and "v\<cdot>u = u\<cdot>v" obtains k where "u = v\<^sup>@k"
  using \<open>v\<cdot>u = u\<cdot>v\<close>[unfolded comm] prim_exp_eq[OF \<open>primitive v\<close>] by metis

lemma pow_non_prim: "1 < k \<Longrightarrow> \<not> primitive (w\<^sup>@k)"
  using prim_exp_one by auto

lemma comm_non_prim: assumes "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>" "u\<cdot>v = v\<cdot>u" shows "\<not> primitive (u\<cdot>v)"
proof-
  obtain t k m where "u = t\<^sup>@k"  "v = t\<^sup>@m" 
    using \<open>u\<cdot>v = v\<cdot>u\<close>[unfolded comm] by blast
  show ?thesis using pow_non_prim[of "k+m" "t"]
    unfolding \<open>u = t\<^sup>@k\<close> \<open>v = t\<^sup>@m\<close> pow_add_list[of t k m] 
    using nemp_pow[OF \<open>u \<noteq> \<epsilon>\<close>[unfolded \<open>u = t\<^sup>@k\<close>]] nemp_pow[OF \<open>v \<noteq> \<epsilon>\<close>[unfolded \<open>v = t\<^sup>@m\<close>]] 
    by linarith
qed

lemma prim_rotate_conv: "primitive w \<longleftrightarrow> primitive (rotate n w)"
proof
  assume "primitive w" show "primitive (rotate n w)"
  proof (rule primI)
  fix r k assume "r\<^sup>@k = rotate n w" 
  obtain l where "(rotate l r)\<^sup>@k = w"
    using rotate_back[of n w, folded \<open>r\<^sup>@k = rotate n w\<close>, unfolded rotate_pow_comm] by blast
  from prim_exp_one[OF \<open>primitive w\<close> this]
  show "k = 1".
qed
next 
  assume "primitive (rotate n w)"  show "primitive w"
   proof (rule primI)
     fix r k assume "r\<^sup>@k = w"
     from prim_exp_one[OF \<open>primitive (rotate n w)\<close>, OF rotate_pow_comm[of n r k, unfolded this, symmetric]]
     show "k = 1".
   qed
 qed

lemma non_prim: assumes "\<not> primitive w" and "w \<noteq> \<epsilon>"
  obtains r k where "r \<noteq> \<epsilon>" and "1 < k" and "r\<^sup>@k = w" and "w \<noteq> r"
proof-
  from \<open>\<not> primitive w\<close>[unfolded primitive_def]
  obtain r k where "k \<noteq> 1" and "r\<^sup>@k = w"  by blast
  have "r \<noteq> \<epsilon>"
    using \<open>w \<noteq> \<epsilon>\<close> \<open>r\<^sup>@k = w\<close> emp_pow by blast 
  have "k \<noteq> 0"
    using \<open>w \<noteq> \<epsilon>\<close> \<open>r\<^sup>@k = w\<close> pow_zero[of r] by meson
  have "w \<noteq> r"
    using \<open>k \<noteq> 1\<close>[folded eq_pow_exp[OF \<open>r \<noteq> \<epsilon>\<close>, of k 1, unfolded \<open>r \<^sup>@ k = w\<close>]] by simp
  show thesis
    using that[OF \<open>r \<noteq> \<epsilon>\<close> _ \<open>r\<^sup>@k = w\<close> \<open>w \<noteq> r\<close>] \<open>k \<noteq> 0\<close> \<open>k \<noteq> 1\<close> less_linear by blast
qed

lemma prim_no_rotate: assumes "primitive w" and "0 < n" and "n < \<^bold>|w\<^bold>|" 
  shows "rotate n w \<noteq> w"
proof
  assume "rotate n w = w"
  have "take n w \<cdot> drop n w = drop n w \<cdot> take n w"
    using rotate_append[of "take n w" "drop n w"] 
    unfolding take_len[OF less_imp_le_nat[OF \<open>n < \<^bold>|w\<^bold>|\<close>]] append_take_drop_id \<open>rotate n w = w\<close>.
  have "take n w \<noteq> \<epsilon>" "drop n w \<noteq> \<epsilon>"
    using \<open>0 < n\<close> \<open>n < \<^bold>|w\<^bold>|\<close> by auto+
  from \<open>primitive w\<close> show False
    using comm_non_prim[OF \<open>take n w \<noteq> \<epsilon>\<close> \<open>drop n w \<noteq> \<epsilon>\<close> \<open>take n w \<cdot> drop n w = drop n w \<cdot> take n w\<close>, unfolded append_take_drop_id]
    by simp
qed

lemma no_rotate_prim: assumes  "w \<noteq> \<epsilon>" and "\<And> n. 0 < n \<Longrightarrow> n < \<^bold>|w\<^bold>| \<Longrightarrow> rotate n w \<noteq> w"
  shows "primitive w"
proof (rule ccontr)
  assume "\<not> primitive w"
  from non_prim[OF this \<open>w \<noteq> \<epsilon>\<close>]
    obtain r l where "r \<noteq> \<epsilon>" and "1 < l" and "r\<^sup>@l = w" and "w \<noteq> r" by blast
    have "rotate \<^bold>|r\<^bold>| w = w"
      using rotate_root_self[of r l, unfolded \<open>r\<^sup>@l = w\<close>].
    moreover have "0 < \<^bold>|r\<^bold>|"
      by (simp add: \<open>r \<noteq> \<epsilon>\<close>)
    moreover have "\<^bold>|r\<^bold>| < \<^bold>|w\<^bold>|" 
      unfolding pow_len[of r l, unfolded \<open>r\<^sup>@l = w\<close>]  using  \<open>1 < l\<close> \<open>0 < \<^bold>|r\<^bold>|\<close>  by auto
   ultimately show False
     using assms(2) by blast
qed

corollary prim_iff_rotate: assumes "w \<noteq> \<epsilon>" shows 
   "primitive w \<longleftrightarrow> (\<forall> n. 0 < n \<and> n < \<^bold>|w\<^bold>| \<longrightarrow> rotate n w \<noteq> w)"
  using no_rotate_prim[OF \<open>w \<noteq> \<epsilon>\<close>] prim_no_rotate by blast

lemma prim_sing: "primitive [a]" 
  using prim_iff_rotate[of "[a]"] by fastforce

lemma prim_rev_iff[reversal_rule]: "primitive (rev u) \<longleftrightarrow> primitive u"
  unfolding primitive_def[reversed] using primitive_def..

section \<open>Primitive root\<close>

text\<open>Given a non-empty word $w$ which is not primitive, it is natural to look for the shortest $u$ such that $w = u^k$.
Such a word is primitive, and it is the primitive root of $w$.\<close>

definition primitive_rootP :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" ("_ \<in>\<^sub>p _ *" [51,51] 60)
  where  "primitive_rootP x r = (x \<noteq> \<epsilon> \<and> x \<in> r* \<and> primitive r)"

lemma prim_rootD [dest]: "x \<in>\<^sub>p r* \<Longrightarrow> x \<in> r*"
  unfolding primitive_rootP_def by (elim conjE)

lemma prim_rootI [intro]: "u \<noteq> \<epsilon> \<Longrightarrow>  u \<in> r* \<Longrightarrow> primitive r \<Longrightarrow> u \<in>\<^sub>p r*"
  unfolding primitive_rootP_def by (intro conjI)

lemma prim_root_rev_conv [reversal_rule]: "rev x \<in>\<^sub>p rev r* \<longleftrightarrow>  x \<in>\<^sub>p r*"
  unfolding primitive_rootP_def[reversed] using primitive_rootP_def..

fun primitive_root :: "'a list \<Rightarrow> 'a list" ("\<rho>") where "primitive_root x = (THE r. x \<in>\<^sub>p r*)"  

lemma primrootE: assumes "x \<in>\<^sub>p r*"
  obtains k where "k \<noteq> 0" and "r\<^sup>@k = x"
  using assms  unfolding primitive_rootP_def root_def using nemp_pow[of r] by auto

lemma primroot_of_root: "\<lbrakk> x \<noteq> \<epsilon>; x \<in> u*; u \<in>\<^sub>p r*\<rbrakk> \<Longrightarrow> x \<in>\<^sub>p r*"
  unfolding primitive_rootP_def using root_trans by blast 

lemma comm_prim: assumes "primitive r" and  "primitive s" and "r\<cdot>s = s\<cdot>r"
      shows "r = s"
  using \<open>r\<cdot>s = s\<cdot>r\<close>[unfolded comm] assms[unfolded primitive_def, rule_format] by metis

lemma primroot_ex: assumes "x \<noteq> \<epsilon>" shows "\<exists> r k.  x \<in>\<^sub>p r* \<and> k \<noteq> 0 \<and> x = r\<^sup>@k"
  using \<open>x \<noteq> \<epsilon>\<close>
proof(induction "\<^bold>|x\<^bold>|" arbitrary: x rule: less_induct)
  case less
  then show "\<exists> r k.  x \<in>\<^sub>p r* \<and> k \<noteq> 0 \<and> x = r\<^sup>@k"
  proof (cases "primitive x")
    assume "\<not> primitive x"
    from non_prim[OF this \<open>x \<noteq> \<epsilon>\<close>]
    obtain r l where "r \<noteq> \<epsilon>" and "1 < l" and "r\<^sup>@l = x" and "x \<noteq> r" by blast
    then obtain pr k where "r \<in>\<^sub>p pr*" "k \<noteq> 0" "r = pr\<^sup>@k"
      using \<open>x \<noteq> \<epsilon>\<close> less.hyps rootI root_shorter by blast  
    hence "x \<in>\<^sub>p pr*"
      using \<open>r \<^sup>@ l = x\<close> less.prems primroot_of_root rootI by blast
    show "\<exists> r k.  x \<in>\<^sub>p r* \<and> k \<noteq> 0 \<and> x = r\<^sup>@k"
      using  \<open>x \<in>\<^sub>p pr*\<close>[unfolded primitive_rootP_def root_def]
        \<open>x \<in>\<^sub>p pr *\<close> nemp_pow by blast
  next
    assume "primitive x"
    have "x \<in>\<^sub>p x*"
      by (simp add: \<open>primitive x\<close> less.prems prim_rootI self_root) 
    thus "\<exists> r k.  x \<in>\<^sub>p r* \<and> k \<noteq> 0 \<and> x = r\<^sup>@k"
      by force
  qed
qed

lemma primroot_exE: assumes"x \<noteq> \<epsilon>" 
  obtains r k where "primitive r" and "k \<noteq> 0" and "x = r\<^sup>@k"
  using assms primitive_rootP_def primroot_ex[OF \<open> x \<noteq> \<epsilon>\<close>] by blast

text\<open>Uniqueness of the primitive root follows from the following lemma\<close>

lemma primroot_unique: assumes "u \<in>\<^sub>p r*" shows "\<rho> u = r" 
proof-
  obtain kr where "kr \<noteq> 0" and "r\<^sup>@kr = u"
    using primrootE[OF \<open>u \<in>\<^sub>p r*\<close>].
  have "u \<in>\<^sub>p s* \<Longrightarrow> s = r" for s
  proof-
   fix s assume "u \<in>\<^sub>p s*"
    obtain ks where "ks \<noteq> 0" and "s\<^sup>@ks = u"
      using primrootE[OF \<open>u \<in>\<^sub>p s*\<close>].
    obtain t where "s \<in> t*" and "r \<in> t*"
      using comm_rootE[OF pow_comm_comm[of r kr s ks, OF _ \<open>kr \<noteq> 0\<close>, unfolded \<open>r\<^sup>@kr = u\<close> \<open>s\<^sup>@ks = u\<close>, OF refl]].  
    have "primitive r" and "primitive s"
      using \<open>u \<in>\<^sub>p r *\<close> \<open>u \<in>\<^sub>p s *\<close> primitive_rootP_def by blast+
    from prim_exp_eq[OF \<open>primitive r\<close>, of t] prim_exp_eq[OF \<open>primitive s\<close>, of t]
    show "s = r"
      using rootE[OF \<open>s \<in> t*\<close>, of "s=r"] rootE[OF \<open>r \<in> t*\<close>, of "r = t"] by fastforce
  qed
  from the_equality[of "\<lambda> r. u \<in>\<^sub>p r*",OF \<open>u \<in>\<^sub>p r*\<close> this]
  show "\<rho> u = r"
    by auto 
qed

lemma prim_self_root: "primitive x \<Longrightarrow> \<rho> x  = x"
  using prim_nemp prim_rootI primroot_unique self_root by blast

text\<open>Existence and uniqueness of the primitive root justifies the function @{term "\<rho>"}: it indeed yields the primitive root of a nonempty word.\<close>

lemma primroot_is_primroot[intro]: assumes "x \<noteq> \<epsilon>" shows "x \<in>\<^sub>p (\<rho> x)*"
  using primroot_ex[OF \<open>x \<noteq> \<epsilon>\<close>] primroot_unique[of x]
  by force

lemma primroot_is_root[intro]: "x \<noteq> \<epsilon> \<Longrightarrow> x \<in> (\<rho> x)*"
  using primroot_is_primroot by auto

lemma primrootI [intro]: assumes "x \<noteq> \<epsilon>" shows primroot_prim: "primitive (\<rho> x)" and primroot_nemp: "\<rho> x \<noteq> \<epsilon>"
  using assms prim_nemp primitive_rootP_def by blast+

lemma primroot_root: assumes "u \<noteq> \<epsilon>" "u \<in> q*" shows "\<rho> q = \<rho> u"
  using primroot_unique[OF primroot_of_root[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> q*\<close> primroot_is_primroot, OF root_nemp[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> q*\<close>]], symmetric].

lemma primroot_len_mult: assumes "u \<noteq> \<epsilon>" "u \<in> q*" obtains k where "\<^bold>|q\<^bold>| = k*\<^bold>|\<rho> u\<^bold>|"
  using primroot_is_primroot[OF root_nemp[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> q*\<close>], unfolded primroot_root[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> q*\<close>]
      primitive_rootP_def] root_len[of q "\<rho> u"] by blast          

lemma primroot_shorter_root: assumes "u \<noteq> \<epsilon>" "u \<in> q*" shows "\<^bold>|\<rho> u\<^bold>| \<le> \<^bold>|q\<^bold>|"
  using quotient_smaller[OF root_nemp[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> q*\<close>, folded length_0_conv], of _ "\<^bold>|\<rho> u\<^bold>|"] 
    primroot_len_mult[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> q*\<close>] by blast

lemma primroot_shortest_root: assumes "u \<noteq> \<epsilon>" shows "\<^bold>|\<rho> u\<^bold>| = (LEAST d. (\<exists> r. (u \<in> r*) \<and> \<^bold>|r\<^bold>| = d))"
  using  Least_equality[of "\<lambda> k. (\<exists> r. (u \<in> r*) \<and> \<^bold>|r\<^bold>| = k)" "\<^bold>|\<rho> u\<^bold>|"]
proof
  show "\<exists>r. u \<in> r* \<and> \<^bold>|r\<^bold>| = \<^bold>|\<rho> u\<^bold>|"
    using assms primitive_rootP_def primroot_is_primroot by blast 
  show "\<And>y. \<exists>r. u \<in> r* \<and> \<^bold>|r\<^bold>| = y \<Longrightarrow> \<^bold>|\<rho> u\<^bold>| \<le> y"
    using assms primroot_shorter_root by fastforce
qed

lemma primroot_shorter_eq: "u \<noteq> \<epsilon> \<Longrightarrow> \<^bold>|\<rho> u\<^bold>| \<le> \<^bold>|u\<^bold>|"
  using primroot_shorter_root self_root by auto


lemma primroot_take: assumes "u \<noteq> \<epsilon>" shows "\<rho> u = (take ( \<^bold>|\<rho> u\<^bold>| ) u)"
proof-
  obtain k where "(\<rho> u)\<^sup>@k = u" and "k \<noteq> 0"
    using primrootE[OF primroot_is_primroot[OF \<open>u \<noteq> \<epsilon>\<close>]].
  show "\<rho> u = (take ( \<^bold>|\<rho> u\<^bold>| ) u)"
    using take_root[of _ "(\<rho> u)", OF \<open>k \<noteq> 0\<close>, unfolded \<open>(\<rho> u)\<^sup>@k = u\<close>].
qed

lemma primroot_take_shortest: assumes "u \<noteq> \<epsilon>" shows "\<rho> u = (take (LEAST d. (\<exists> r. (u \<in> r*) \<and> \<^bold>|r\<^bold>| = d)) u)"
  using primroot_take[OF assms, unfolded primroot_shortest_root[OF assms]].

lemma primroot_rotate_comm: assumes "w \<noteq> \<epsilon>" shows "\<rho> (rotate n w) = rotate n (\<rho> w)"
proof-
  obtain l where  "w = (\<rho> w)\<^sup>@l"
    using pow_zero primrootE primroot_is_primroot by metis
  hence "rotate n w \<in> (rotate n (\<rho> w))*"
    using rotate_pow_comm root_def by metis
  moreover have "rotate n w \<noteq> \<epsilon>"
    using assms by auto
  moreover have "primitive (rotate n (\<rho> w))"
    using assms prim_rotate_conv primitive_rootP_def primroot_is_primroot by blast
  ultimately have "rotate n w \<in>\<^sub>p (rotate n (\<rho> w))*"
    unfolding primitive_rootP_def  by blast
  thus  ?thesis
    using primroot_unique by blast
qed

lemma primrootI1 [intro]: assumes pow: "u = r\<^sup>@(Suc k)" and prim: "primitive r" shows "\<rho> u = r"
proof-
  have "u \<noteq> \<epsilon>"
    using pow prim prim_nemp by auto 
  have "u \<in> r*"
    using pow rootI by blast
  show "\<rho> u = r"
    using primroot_unique[OF prim_rootI[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> r*\<close> \<open>primitive r\<close>]].
qed

lemma prim_root_power [elim]: assumes "x \<noteq> \<epsilon>" obtains i where "(\<rho> x)\<^sup>@(Suc i) = x"
  using prim_rootD[OF primroot_is_primroot[OF \<open>x \<noteq> \<epsilon>\<close>], unfolded root_def] assms pow_zero[of "\<rho> x"] not0_implies_Suc
  by metis

lemma prim_root_cases: obtains "u = \<epsilon>" | "primitive u" | "\<^bold>|\<rho> u\<^bold>| < \<^bold>|u\<^bold>|"
  using primroot_is_primroot[THEN prim_rootD[of u "\<rho> u"]]  
        primroot_prim[of u] root_shorter[of u "\<rho> u"] by fastforce

text\<open>We also have the standard characterization of commutation for nonempty words.\<close>

theorem comm_primroots: assumes "u \<noteq> \<epsilon>" "v \<noteq> \<epsilon>" shows "u \<cdot> v = v \<cdot> u \<longleftrightarrow> \<rho> u = \<rho> v"
proof
  assume "u \<cdot> v = v \<cdot> u"
  then obtain t where "u \<in> t*" and "v \<in> t*"
    using comm_root by blast
  show "\<rho> u = \<rho> v"
    using primroot_root[OF \<open>v \<noteq> \<epsilon>\<close> \<open>v \<in> t*\<close>, unfolded primroot_root[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> t*\<close>]]. 
next
  assume "\<rho> u = \<rho> v"
  show "u \<cdot> v = v \<cdot> u"
    using primroot_is_primroot[OF \<open>u \<noteq> \<epsilon>\<close>, unfolded \<open>\<rho> u = \<rho> v\<close>] primroot_is_primroot[OF \<open>v \<noteq> \<epsilon>\<close>] unfolding primitive_rootP_def
    comm_root  by blast
qed

lemma prim_comm_short_emp: assumes "primitive p" and "u\<cdot>p=p\<cdot>u" and "\<^bold>|u\<^bold>| < \<^bold>|p\<^bold>|"
  shows "u = \<epsilon>"
proof (rule ccontr)
  assume "u \<noteq> \<epsilon>"
  from \<open>u \<cdot> p = p \<cdot> u\<close>
  have "\<rho> u = \<rho> p"
    unfolding comm_primroots[OF \<open>u \<noteq> \<epsilon>\<close> prim_nemp, OF \<open>primitive p\<close>].
  have "\<rho> u = p"
    using prim_self_root[OF \<open>primitive p\<close>, folded \<open>\<rho> u = \<rho> p\<close>].
  from \<open>\<^bold>|u\<^bold>| < \<^bold>|p\<^bold>|\<close>[folded this]
  show False
    using primroot_shorter_eq[OF \<open>u \<noteq> \<epsilon>\<close>] by auto
qed

section \<open>Conjugation\<close>

text\<open>Two words $x$ and $y$ are conjugated if one is a rotation of the other.
Or, equivalently, there exists $z$ such that
\[
xz = zy.
\]
\<close>

definition conjugate ("_ \<sim> _" [50,50] 51) where "u \<sim> v \<equiv> \<exists>r s. r \<cdot> s = u \<and> s \<cdot> r = v"

lemma conjug_rev_conv [reversal_rule]: "rev u \<sim> rev v \<longleftrightarrow> u \<sim> v"
  unfolding conjugate_def[reversed] using conjugate_def by blast

lemma conjug_rotate_iff: "u \<sim> v \<longleftrightarrow> (\<exists> n. v = rotate n u)"
  unfolding conjugate_def
  using rotate_drop_take[of _ u] takedrop[of _ u] rotate_append
  by metis

lemma conjugI [intro]: "r \<cdot> s = u \<Longrightarrow> s \<cdot> r = v \<Longrightarrow> u \<sim> v"
  unfolding conjugate_def by (intro exI conjI)

lemma conjugI' [intro!]: "r \<cdot> s \<sim> s \<cdot> r"
  unfolding conjugate_def by (intro exI conjI, standard+)

lemma conjugE [elim]: 
  assumes "u \<sim> v"
  obtains r s where "r \<cdot> s = u" and "s \<cdot> r = v"
  using assms unfolding conjugate_def by (elim exE conjE)

lemma conjugE1 [elim]:
  assumes "u \<sim> v"
  obtains r where "u \<cdot> r = r \<cdot> v"
proof -
  obtain r s where u: "r \<cdot> s = u" and v: "s \<cdot> r = v" using assms..
  have "u \<cdot> r = r \<cdot> v" unfolding u[symmetric] v[symmetric] using rassoc.
  then show thesis by fact
qed

lemma conjug_refl: "u \<sim> u"
  by standard+

lemma conjug_sym [sym]: "u \<sim> v \<Longrightarrow> v \<sim> u"
  by (elim conjugE, intro conjugI) assumption+

lemma conjug_nemp_iff: "u \<sim> v \<Longrightarrow> u = \<epsilon> \<longleftrightarrow> v = \<epsilon>"
  by (elim conjugE1, intro iffI) simp+

lemma conjug_len: "u \<sim> v  \<Longrightarrow> \<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
  by (elim conjugE, hypsubst, rule swap_len)

lemma pow_conjug:
  assumes eq: "t\<^sup>@i \<cdot> r \<cdot> u = t\<^sup>@k" and t: "r \<cdot> s = t"
  shows "u \<cdot> t\<^sup>@i \<cdot> r = (s \<cdot> r)\<^sup>@k"
proof -
  have "t\<^sup>@i \<cdot> r \<cdot> u \<cdot> t\<^sup>@i \<cdot> r = t\<^sup>@i \<cdot> t\<^sup>@k \<cdot> r" unfolding eq[unfolded lassoc] lassoc append_same_eq pow_comm.. 
  also have "\<dots>  = t\<^sup>@i \<cdot> r \<cdot> (s \<cdot> r)\<^sup>@k" unfolding conjug_pow[OF rassoc, symmetric] t..
  finally show "u \<cdot> t\<^sup>@i \<cdot> r = (s \<cdot> r)\<^sup>@k" unfolding same_append_eq.  
qed

text\<open>The solution of the equation 
\[
xz = zy
\]
is given by the next lemma.
\<close>

lemma conjug_eqE [elim, consumes 2]:
  assumes eq: "x \<cdot> z = z \<cdot> y" and "x \<noteq> \<epsilon>"
  obtains u v k where "u \<cdot> v = x" and "v \<cdot> u = y" and "(u \<cdot> v)\<^sup>@k \<cdot> u = z" and "v \<noteq> \<epsilon>"
proof -
  have "z \<le>p x \<cdot> z" using eq[symmetric]..
  from this \<open>x \<noteq> \<epsilon>\<close> have "z \<le>p x\<^sup>\<omega>"..
  then obtain k u where "x\<^sup>@k \<cdot> u = z" and "u <p x"..
  from \<open>u <p x\<close> obtain v where x: "u \<cdot> v = x" and "v \<noteq> \<epsilon>"..
  have z: "(u\<cdot>v)\<^sup>@k \<cdot> u = z" unfolding x \<open>x\<^sup>@k \<cdot> u = z\<close>..
  have "z \<cdot> y = (u\<cdot>v) \<cdot> ((u\<cdot>v)\<^sup>@k \<cdot> u)" unfolding z unfolding x eq..
  also have "\<dots> = (u\<cdot>v)\<^sup>@k \<cdot> u \<cdot> (v \<cdot> u)" unfolding lassoc pow_commutes_list[symmetric]..
  finally have y: "v \<cdot> u = y" unfolding z[symmetric] rassoc same_append_eq..
  from x y z \<open>v \<noteq> \<epsilon>\<close> show thesis..
qed

theorem conjugation: assumes "x\<cdot>z = z\<cdot>y" and "x \<noteq> \<epsilon>" 
  shows "\<exists> u v k. u \<cdot> v = x \<and> v \<cdot> u  = y \<and> (u \<cdot> v)\<^sup>@k \<cdot> u = z"
  using assms by blast

lemma conjug_eq_prim_rootE [elim, consumes 2]:
  assumes eq: "x \<cdot> z = z \<cdot> y" and "x \<noteq> \<epsilon>"
  obtains r s i n where
    "(r \<cdot> s)\<^sup>@Suc i = x" and
    "(s \<cdot> r)\<^sup>@Suc i = y" and 
    "(r \<cdot> s)\<^sup>@n \<cdot> r = z" and
    "s \<noteq> \<epsilon>" and "primitive (r \<cdot> s)"
proof -
  from \<open>x \<noteq> \<epsilon>\<close> obtain i where "(\<rho> x)\<^sup>@(Suc i) = x"..
  also have "z \<le>p x\<^sup>\<omega>" using prefI[OF \<open>x \<cdot> z = z \<cdot> y\<close>[symmetric]] \<open>x \<noteq> \<epsilon>\<close>..
  finally have "z \<le>p (\<rho> x)\<^sup>\<omega>" by (elim per_drop_exp)
  then obtain n r where "(\<rho> x)\<^sup>@n \<cdot> r = z" and "r <p \<rho> x"..
  from \<open>r <p \<rho> x\<close> obtain s where "r \<cdot> s = \<rho> x" and "s \<noteq> \<epsilon>"..
  define j where "j = Suc i"
  have x: "(r\<cdot>s)\<^sup>@j = x" unfolding \<open>r \<cdot> s = \<rho> x\<close> \<open>j = Suc i\<close> \<open>(\<rho> x)\<^sup>@(Suc i) = x\<close>..
  have z: "(r\<cdot>s)\<^sup>@n \<cdot> r = z" unfolding \<open>r \<cdot> s = \<rho> x\<close> \<open>(\<rho> x)\<^sup>@n \<cdot> r = z\<close>..
  have "z \<cdot> y = ((r\<cdot>s)\<^sup>@j \<cdot> (r\<cdot>s)\<^sup>@n) \<cdot> r" using eq[symmetric] unfolding rassoc x z.
  also have "(r\<cdot>s)\<^sup>@j \<cdot> (r\<cdot>s)\<^sup>@n = (r\<cdot>s)\<^sup>@n \<cdot> (r\<cdot>s)\<^sup>@j" using pow_comm.
  also have "\<dots> \<cdot> r = (r\<cdot>s)\<^sup>@n \<cdot> r \<cdot> (s\<cdot>r)\<^sup>@j" unfolding rassoc unfolding shift_pow..
  finally have y: "y = (s\<cdot>r)\<^sup>@j" unfolding z[symmetric] rassoc cancel. 
  from \<open>x \<noteq> \<epsilon>\<close> have "primitive (r \<cdot> s)" unfolding \<open>r \<cdot> s = \<rho> x\<close>..
  with that x y z \<open>s \<noteq> \<epsilon>\<close>  show thesis unfolding \<open>j = Suc i\<close> by blast 
qed

lemma conjug_eq_prim_root:
  assumes "x \<cdot> z = z \<cdot> y" and "x \<noteq> \<epsilon>"
  shows "\<exists> r s i n. (r \<cdot> s)\<^sup>@(Suc i) = x \<and> (s \<cdot> r)\<^sup>@(Suc i) = y \<and> (r \<cdot> s)\<^sup>@n \<cdot> r = z \<and> s \<noteq> \<epsilon> \<and> primitive (r \<cdot> s)"
  using conjug_eq_prim_rootE[OF assms, of ?thesis] by blast

lemma conjugI1 [intro]:
  assumes eq: "u \<cdot> r = r \<cdot> v"
  shows "u \<sim> v"
proof (cases)
  assume "u = \<epsilon>"
  have "v = \<epsilon>" using eq unfolding \<open>u = \<epsilon>\<close> by simp
  show "u \<sim> v" unfolding \<open>u = \<epsilon>\<close> \<open>v = \<epsilon>\<close> using conjug_refl.
next
  assume "u \<noteq> \<epsilon>"
  show "u \<sim> v" using eq \<open>u \<noteq> \<epsilon>\<close> by (cases rule: conjug_eqE, intro conjugI)
qed

lemma conjug_trans [trans]:
  assumes uv: "u \<sim> v" and vw: "v \<sim> w"
    shows "u \<sim> w"
  using assms  unfolding conjug_rotate_iff using rotate_rotate by blast

lemma conjug_trans': assumes uv': "u \<cdot> r = r \<cdot> v" and vw': "v \<cdot> s = s \<cdot> w" shows "u \<cdot> (r \<cdot> s) = (r \<cdot> s) \<cdot> w"
proof -
  have "u \<cdot> (r \<cdot> s) = (r \<cdot> v) \<cdot> s" unfolding uv'[symmetric] rassoc..
  also have "\<dots> = r \<cdot> (s \<cdot> w)" unfolding vw'[symmetric] rassoc..
  finally show "u \<cdot> (r \<cdot> s) = (r \<cdot> s) \<cdot> w" unfolding rassoc.
qed

lemma nconjug_neq: "\<not> u \<sim> v \<Longrightarrow> u \<noteq> v"
  by blast

lemma prim_conjug:
  assumes prim: "primitive u" and conjug: "u \<sim> v"
  shows "primitive v"
proof -
  have "v \<noteq> \<epsilon>" using prim_nemp[OF prim] unfolding conjug_nemp_iff[OF conjug].
  from conjug[symmetric] obtain t where "v \<cdot> t = t \<cdot> u"..
  from this \<open>v \<noteq> \<epsilon>\<close> obtain r s i where
    v: "(r \<cdot> s)\<^sup>@(Suc i) = v" and u: "(s \<cdot> r)\<^sup>@(Suc i) = u" and prim': "primitive (r \<cdot> s)"..
  have "r \<cdot> s = v" using v unfolding prim_exp_one[OF prim u] pow_one_id.
  show "primitive v" using prim' unfolding \<open>r \<cdot> s = v\<close>.
qed

lemma root_conjug: "u \<le>p r \<cdot> u \<Longrightarrow> u\<inverse>\<^sup>>(r\<cdot>u) \<sim> r"
  using conjugI1 conjug_sym lq_pref by metis

lemma conjug_prim_root:
  assumes conjug: "u \<sim> v" and "u \<noteq> \<epsilon>"
  shows "\<rho> u \<sim> \<rho> v"
proof -
  from conjug obtain t where "u \<cdot> t = t \<cdot> v"..
  from this \<open>u \<noteq> \<epsilon>\<close> obtain r s i where
    u: "(r \<cdot> s)\<^sup>@(Suc i) = u" and v: "(s \<cdot> r)\<^sup>@(Suc i) = v" and prim: "primitive (r \<cdot> s)"..
  have rs: "\<rho> u = r \<cdot> s" and sr: "\<rho> v = s \<cdot> r"
    using prim prim_conjug u v by blast+
  show "\<rho> u \<sim> \<rho> v" using conjugI' unfolding rs sr.
qed

lemma conjug_add_exp: "u \<sim> v \<Longrightarrow>  u\<^sup>@k \<sim> v\<^sup>@k"
 by (elim conjugE1, intro conjugI1, rule conjug_pow)

lemma conjug_prim_root_iff:
  assumes nemp:"u \<noteq> \<epsilon>" and len: "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|"
  shows "\<rho> u  \<sim> \<rho> v \<longleftrightarrow> u \<sim> v"
proof
  show "u \<sim> v \<Longrightarrow> \<rho> u  \<sim> \<rho> v" using conjug_prim_root[OF _ nemp].
  assume conjug: "\<rho> u  \<sim> \<rho> v"
  have "v \<noteq> \<epsilon>" using nemp_len[OF nemp] unfolding len length_0_conv.
  with nemp obtain k l where roots: "(\<rho> u)\<^sup>@k = u" "(\<rho> v)\<^sup>@l = v" by (elim prim_root_power)
  have "\<^bold>|(\<rho> u)\<^sup>@k\<^bold>| = \<^bold>|(\<rho> v)\<^sup>@l\<^bold>|" using len unfolding roots.
  then have "k = l" using primroot_nemp[OF \<open>v \<noteq> \<epsilon>\<close>]
    unfolding pow_len conjug_len[OF conjug] by simp
  show "u \<sim> v" using conjug_add_exp[OF conjug, of l] unfolding roots[unfolded \<open>k = l\<close>].
qed

lemma fac_pow_pref_conjug:
  assumes "u \<le>f t\<^sup>@k"
  obtains t' where "t \<sim> t'" and "u \<le>p t'\<^sup>@k"
proof (cases "u = \<epsilon>")
  assume "u \<noteq> \<epsilon>"
  obtain p q where eq: "p \<cdot> u \<cdot> q = t\<^sup>@k" using facE'[OF assms].
  obtain i r where "i < k" and "r <p t" and p: "t\<^sup>@i \<cdot> r = p"
    using pref_mod_power[OF sprefI1'[OF eq pref_nemp[OF \<open>u \<noteq> \<epsilon>\<close>]]].
  from \<open>r <p t\<close> obtain s where t: "r \<cdot> s = t"..
  have eq': "t\<^sup>@i \<cdot> r \<cdot> (u \<cdot> q) = t\<^sup>@k" using eq unfolding lassoc p.
  have  "u \<le>p (s \<cdot> r)\<^sup>@k" using pow_conjug[OF eq' t] unfolding rassoc..
  with conjugI'[of r s] show thesis unfolding t..
qed blast

lemma fac_pow_len_conjug: assumes  "\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|" and "u \<le>f v\<^sup>@k" shows "v \<sim> u"
proof-
  obtain t where "v \<sim> t" and "u \<le>p t\<^sup>@k" 
    using fac_pow_pref_conjug assms by blast
  have "u = t"
    using pref_equal[OF pref_prod_root[OF \<open>u \<le>p t\<^sup>@k\<close>] conjug_len[OF \<open>v \<sim> t\<close>,folded \<open>\<^bold>|u\<^bold>| = \<^bold>|v\<^bold>|\<close>]].
  from \<open>v \<sim> t\<close>[folded this]
  show "v \<sim> u".
qed

lemma border_conjug: "x \<le>b w \<Longrightarrow> w\<^sup><\<inverse>x \<sim>  x\<inverse>\<^sup>>w"
  using border_conjug_eq conjugI1 by blast

lemmas fac_pow_suf_conjug = fac_pow_pref_conjug[reversed]
   
end