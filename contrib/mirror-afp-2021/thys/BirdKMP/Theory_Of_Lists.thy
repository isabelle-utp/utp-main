(*<*)
theory Theory_Of_Lists
imports
  HOLCF_ROOT
begin

(*>*)
section\<open> Strict lists \label{sec:theory_of_lists} \<close>

text\<open>

Head- and tail-strict lists. Many technical Isabelle details are
lifted from \<open>HOLCF-Prelude.Data_List\<close>; names follow
HOL, prefixed with \<open>s\<close>.

\<close>

domain 'a slist ("[:_:]") =
  snil ("[::]")
| scons (shead :: "'a") (stail :: "'a slist") (infixr ":#" 65)

lemma scons_strict[simp]: "scons\<cdot>\<bottom> = \<bottom>"
by (clarsimp simp: cfun_eq_iff)

lemma shead_bottom_iff[simp]: "(shead\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom> \<or> xs = [::])"
by (cases xs) simp_all

lemma stail_bottom_iff[simp]: "(stail\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom> \<or> xs = [::])"
by (cases xs) simp_all

lemma match_snil_match_scons_slist_case: "match_snil\<cdot>xs\<cdot>k1 +++ match_scons\<cdot>xs\<cdot>k2 = slist_case\<cdot>k1\<cdot>k2\<cdot>xs"
by (cases xs) simp_all

lemma slist_bottom': "slist_case\<cdot>\<bottom>\<cdot>\<bottom>\<cdot>xs = \<bottom>"
by (cases xs; simp)

lemma slist_bottom[simp]: "slist_case\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
by (simp add: cfun_eq_iff slist_bottom')

lemma slist_case_distr:
  "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> f\<cdot>(slist_case\<cdot>g\<cdot>h\<cdot>xs) = slist_case\<cdot>(f\<cdot>g)\<cdot>(\<Lambda> x xs. f\<cdot>(h\<cdot>x\<cdot>xs))\<cdot>xs"
  "slist_case\<cdot>g'\<cdot>h'\<cdot>xs\<cdot>z = slist_case\<cdot>(g'\<cdot>z)\<cdot>(\<Lambda> x xs. h'\<cdot>x\<cdot>xs\<cdot>z)\<cdot>xs"
by (case_tac [!] xs) simp_all

lemma slist_case_cong:
  assumes "xs = xs'"
  assumes "xs' = [::] \<Longrightarrow> n = n'"
  assumes "\<And>y ys. \<lbrakk>xs' = y :# ys; y \<noteq> \<bottom>; ys \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> c y ys = c' y ys"
  assumes "cont (\<lambda>(x, y). c x y)"
  assumes "cont (\<lambda>(x, y). c' x y)"
  shows "slist_case\<cdot>n\<cdot>(\<Lambda> x xs. c x xs)\<cdot>xs = slist_case\<cdot>n'\<cdot>(\<Lambda> x xs. c' x xs)\<cdot>xs'"
using assms by (cases xs; cases xs'; clarsimp simp: prod_cont_iff)


text\<open>

Section syntax for @{const \<open>scons\<close>} ala Haskell.

\<close>

syntax
  "_scons_section" :: "'a \<rightarrow> [:'a:] \<rightarrow> [:'a:]" ("'(:#')")
  "_scons_section_left" :: "'a \<Rightarrow> [:'a:] \<rightarrow> [:'a:]" ("'(_:#')")
translations
  "(x:#)" == "(CONST Rep_cfun) (CONST scons) x"

abbreviation scons_section_right :: "[:'a:] \<Rightarrow> 'a \<rightarrow> [:'a:]" ("'(:#_')") where
  "(:#xs) \<equiv> \<Lambda> x. x :# xs"

syntax
  "_strict_list" :: "args \<Rightarrow> [:'a:]" ("[:(_):]")
translations
  "[:x, xs:]" == "x :# [:xs:]"
  "[:x:]" == "x :# [::]"


text\<open>

Class instances.

\<close>

instantiation slist :: (Eq) Eq_strict
begin

fixrec eq_slist :: "[:'a:] \<rightarrow> [:'a:] \<rightarrow> tr" where
  "eq_slist\<cdot>[::]\<cdot>[::] = TT"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> eq_slist\<cdot>(x :# xs)\<cdot>[::] = FF"
| "\<lbrakk>y \<noteq> \<bottom>; ys \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> eq_slist\<cdot>[::]\<cdot>(y :# ys) = FF"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>; y \<noteq> \<bottom>; ys \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> eq_slist\<cdot>(x :# xs)\<cdot>(y :# ys) = (eq\<cdot>x\<cdot>y andalso eq_slist\<cdot>xs\<cdot>ys)"

instance proof
  fix xs :: "[:'a:]"
  show "eq\<cdot>xs\<cdot>\<bottom> = \<bottom>"
    by (cases xs) (subst eq_slist.unfold; simp)+
  show "eq\<cdot>\<bottom>\<cdot>xs = \<bottom>"
    by (cases xs) (subst eq_slist.unfold; simp)+
qed

end

instance slist :: (Eq_sym) Eq_sym
proof
  fix xs ys :: "[:'a:]"
  show "eq\<cdot>xs\<cdot>ys = eq\<cdot>ys\<cdot>xs"
  proof (induct xs arbitrary: ys)
    case snil
    show ?case by (cases ys; simp)
  next
    case scons
    then show ?case by (cases ys; simp add: eq_sym)
  qed simp_all
qed

instance slist :: (Eq_equiv) Eq_equiv
proof
  fix xs ys zs :: "[:'a:]"
  show "eq\<cdot>xs\<cdot>xs \<noteq> FF"
    by (induct xs) simp_all
  assume "eq\<cdot>xs\<cdot>ys = TT" and "eq\<cdot>ys\<cdot>zs = TT" then show "eq\<cdot>xs\<cdot>zs = TT"
  proof (induct xs arbitrary: ys zs)
    case (snil ys zs) then show ?case by (cases ys, simp_all)
  next
    case (scons x xs ys zs) with eq_trans show ?case
      by (cases ys; cases zs) auto
  qed simp_all
qed

instance slist :: (Eq_eq) Eq_eq
proof
  fix xs ys :: "[:'a:]"
  show "eq\<cdot>xs\<cdot>xs \<noteq> FF"
    by (induct xs) simp_all
  assume "eq\<cdot>xs\<cdot>ys = TT" then show "xs = ys"
  proof (induct xs arbitrary: ys)
    case (snil ys) then show ?case by (cases ys) simp_all
  next
    case (scons x xs ys) then show ?case by (cases ys) auto
  qed simp
qed

instance slist :: (Eq_def) Eq_def
proof
  fix xs ys :: "[:'a:]"
  assume "xs \<noteq> \<bottom>" and "ys \<noteq> \<bottom>"
  then show "eq\<cdot>xs\<cdot>ys \<noteq> \<bottom>"
  proof(induct xs arbitrary: ys)
    case (snil ys) then show ?case by (cases ys) simp_all
  next
    case (scons a xs) then show ?case by (cases ys) simp_all
  qed simp
qed

lemma slist_eq_TT_snil[simp]:
  fixes xs :: "[:'a::Eq:]"
  shows "(eq\<cdot>xs\<cdot>[::] = TT) \<longleftrightarrow> (xs = [::])"
        "(eq\<cdot>[::]\<cdot>xs = TT) \<longleftrightarrow> (xs = [::])"
by (cases xs; simp)+

lemma slist_eq_FF_snil[simp]:
  fixes xs :: "[:'a::Eq:]"
  shows "(eq\<cdot>xs\<cdot>[::] = FF) \<longleftrightarrow> (\<exists>y ys. y \<noteq> \<bottom> \<and> ys \<noteq> \<bottom> \<and> xs = y :# ys)"
        "(eq\<cdot>[::]\<cdot>xs = FF) \<longleftrightarrow> (\<exists>y ys. y \<noteq> \<bottom> \<and> ys \<noteq> \<bottom> \<and> xs = y :# ys)"
by (cases xs; force)+


subsection\<open> Some of the usual reasoning infrastructure \<close>

inductive slistmem :: "'a \<Rightarrow> [:'a:] \<Rightarrow> bool" where
  "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> slistmem x (x :# xs)"
| "\<lbrakk>slistmem x xs; y \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> slistmem x (y :# xs)"

lemma slistmem_bottom1[iff]:
  fixes x :: "'a"
  shows "\<not> slistmem x \<bottom>"
by rule (induct x "\<bottom>::[:'a:]" rule: slistmem.induct; fastforce)

lemma slistmem_bottom2[iff]:
  fixes xs :: "[:'a:]"
  shows "\<not> slistmem \<bottom> xs"
by rule (induct "\<bottom>::'a" xs rule: slistmem.induct; fastforce)

lemma slistmem_nil[iff]:
  shows "\<not> slistmem x [::]"
by (fastforce elim: slistmem.cases)

lemma slistmem_scons[simp]:
  shows "slistmem x (y :# ys) \<longleftrightarrow> (x = y \<and> x \<noteq> \<bottom> \<and> ys \<noteq> \<bottom>) \<or> (slistmem x ys \<and> y \<noteq> \<bottom>)"
proof -
  have "x = y \<or> slistmem x ys" if "slistmem x (y :# ys)"
    using that by (induct "x" "y :# ys" arbitrary: y ys rule: slistmem.induct; force)
  then show ?thesis by (auto elim: slistmem.cases intro: slistmem.intros)
qed

definition sset :: "[:'a:] \<Rightarrow> 'a set" where
  "sset xs = {x. slistmem x xs}"

lemma sset_simp[simp]:
  shows "sset \<bottom> = {}"
    and "sset [::] = {}"
    and "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sset (x :# xs) = insert x (sset xs)"
unfolding sset_def by (auto elim: slistmem.cases intro: slistmem.intros)

lemma sset_defined[simp]:
  assumes "x \<in> sset xs"
  shows "x \<noteq> \<bottom>"
using assms sset_def by force

lemma sset_below:
  assumes "y \<in> sset ys"
  assumes "xs \<sqsubseteq> ys"
  assumes "xs \<noteq> \<bottom>"
  obtains x where "x \<in> sset xs" and "x \<sqsubseteq> y"
using assms
proof(induct ys arbitrary: xs)
  case (scons y ys xs) then show ?case by (cases xs) auto
qed simp_all


subsection\<open> Some of the usual operations \<close>

text\<open>

A variety of functions on lists. Drawn from @{cite [cite_macro=citet]
"Bird:1987"}, @{theory \<open>HOL.List\<close>} and
@{theory \<open>HOLCF-Prelude.Data_List\<close>}. The definitions vary because,
for instance, the strictness of some of those in
@{theory \<open>HOLCF-Prelude.Data_List\<close>} correspond neither to those in
Haskell nor Bird's expectations (specifically \<open>stails\<close>,
\<open>inits\<close>, \<open>sscanl\<close>).

\<close>

fixrec snull :: "[:'a:] \<rightarrow> tr" where
  "snull\<cdot>[::] = TT"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> snull\<cdot>(x :# xs) = FF"

lemma snull_strict[simp]: "snull\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma snull_bottom_iff[simp]: "(snull\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom>)"
by (cases xs) simp_all

lemma snull_FF_conv: "(snull\<cdot>xxs = FF) \<longleftrightarrow> (\<exists>x xs. xxs \<noteq> \<bottom> \<and> xxs = x :# xs)"
by (cases xxs) simp_all

lemma snull_TT_conv[simp]: "(snull\<cdot>xs = TT) \<longleftrightarrow> (xs = [::])"
by (cases xs) simp_all

lemma snull_eq_snil: "snull\<cdot>xs = eq\<cdot>xs\<cdot>[::]"
by (cases xs) simp_all

fixrec smap :: "('a \<rightarrow> 'b) \<rightarrow> [:'a:] \<rightarrow> [:'b:]" where
  "smap\<cdot>f\<cdot>[::] = [::]"
| "\<lbrakk>x \<noteq>\<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> smap\<cdot>f\<cdot>(x :# xs) = f\<cdot>x :# smap\<cdot>f\<cdot>xs"

lemma smap_strict[simp]: "smap\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma smap_bottom_iff[simp]: "(smap\<cdot>f\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom> \<or> (\<exists>x\<in>sset xs. f\<cdot>x = \<bottom>))"
by (induct xs) simp_all

lemma smap_is_snil_conv[simp]:
  "(smap\<cdot>f\<cdot>xs = [::]) \<longleftrightarrow> (xs = [::])"
  "( [::] = smap\<cdot>f\<cdot>xs) \<longleftrightarrow> (xs = [::])"
by (cases xs; simp)+

lemma smap_strict_scons[simp]:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  shows "smap\<cdot>f\<cdot>(x :# xs) = f\<cdot>x :# smap\<cdot>f\<cdot>xs"
using assms by (cases "x :# xs = \<bottom>"; fastforce)

lemma smap_ID': "smap\<cdot>ID\<cdot>xs = xs"
by (induct xs) simp_all

lemma smap_ID[simp]: "smap\<cdot>ID = ID"
by (clarsimp simp: cfun_eq_iff smap_ID')

lemma smap_cong:
  assumes "xs = xs'"
  assumes "\<And>x. x \<in> sset xs \<Longrightarrow> f\<cdot>x = f'\<cdot>x"
  shows "smap\<cdot>f\<cdot>xs = smap\<cdot>f'\<cdot>xs'"
using assms by (induct xs arbitrary: xs') auto

lemma smap_smap'[simp]:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  shows "smap\<cdot>f\<cdot>(smap\<cdot>g\<cdot>xs) = smap\<cdot>(f oo g)\<cdot>xs"
using assms by (induct xs) simp_all

lemma smap_smap[simp]:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  shows "smap\<cdot>f oo smap\<cdot>g = smap\<cdot>(f oo g)"
using assms by (clarsimp simp: cfun_eq_iff)

lemma sset_smap[simp]:
  assumes "\<And>x. x \<in> sset xs \<Longrightarrow> f\<cdot>x \<noteq> \<bottom>"
  shows "sset (smap\<cdot>f\<cdot>xs) = { f\<cdot>x | x. x \<in> sset xs }"
using assms by (induct xs) auto

lemma shead_smap_distr:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  assumes "\<And>x. x\<in>sset xs \<Longrightarrow> f\<cdot>x \<noteq> \<bottom>"
  shows "shead\<cdot>(smap\<cdot>f\<cdot>xs) = f\<cdot>(shead\<cdot>xs)"
using assms by (induct xs) simp_all

fixrec sappend :: "[:'a:] \<rightarrow> [:'a:] \<rightarrow> [:'a:]" where
  "sappend\<cdot>[::]\<cdot>ys = ys"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sappend\<cdot>(x :# xs)\<cdot>ys = x :# sappend\<cdot>xs\<cdot>ys"

abbreviation sappend_syn :: "'a slist \<Rightarrow> 'a slist \<Rightarrow> 'a slist" (infixr ":@" 65) where
  "xs :@ ys \<equiv> sappend\<cdot>xs\<cdot>ys"

lemma sappend_strict[simp]: "sappend\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma sappend_strict2[simp]: "xs :@ \<bottom> = \<bottom>"
by (induct xs) simp_all

lemma sappend_bottom_iff[simp]: "(xs :@ ys = \<bottom>) \<longleftrightarrow> (xs = \<bottom> \<or> ys = \<bottom>)"
by (induct xs) simp_all

lemma sappend_scons[simp]: "(x :# xs) :@ ys = x :# xs :@ ys"
by (cases "x :# xs = \<bottom>"; fastforce)

lemma sappend_assoc[simp]: "(xs :@ ys) :@ zs = xs :@ (ys :@ zs)"
by (induct xs) simp_all

lemma sappend_snil_id_left[simp]: "sappend\<cdot>[::] = ID"
by (simp add: cfun_eq_iff)

lemma sappend_snil_id_right[iff]: "xs :@ [::] = xs"
by (induct xs) simp_all

lemma snil_append_iff[iff]: "xs :@ ys = [::] \<longleftrightarrow> xs = [::] \<and> ys = [::]"
by (induct xs) simp_all

lemma smap_sappend[simp]: "smap\<cdot>f\<cdot>(xs :@ ys) = smap\<cdot>f\<cdot>xs :@ smap\<cdot>f\<cdot>ys"
by (induct xs; cases "ys = \<bottom>"; simp)

lemma stail_sappend: "stail\<cdot>(xs :@ ys) = (case xs of [::] \<Rightarrow> stail\<cdot>ys | z :# zs \<Rightarrow> zs :@ ys)"
by (induct xs) simp_all

lemma stail_append2[simp]: "xs \<noteq> [::] \<Longrightarrow> stail\<cdot>(xs :@ ys) = stail\<cdot>xs :@ ys"
by (induct xs) simp_all

lemma slist_case_snoc:
  "g\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom> \<Longrightarrow> slist_case\<cdot>f\<cdot>g\<cdot>(xs :@ [:x:]) = g\<cdot>(shead\<cdot>(xs :@ [:x:]))\<cdot>(stail\<cdot>(xs :@ [:x:]))"
by (cases "x = \<bottom>"; cases xs; clarsimp)

fixrec sall :: "('a \<rightarrow> tr) \<rightarrow> [:'a:] \<rightarrow> tr" where
  "sall\<cdot>p\<cdot>[::] = TT"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sall\<cdot>p\<cdot>(x :# xs) = (p\<cdot>x andalso sall\<cdot>p\<cdot>xs)"

lemma sall_strict[simp]: "sall\<cdot>p\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma sall_const_TT[simp]:
  assumes "xs \<noteq> \<bottom>"
  shows "sall\<cdot>(\<Lambda> x. TT)\<cdot>xs = TT"
using assms by (induct xs) simp_all

lemma sall_const_TT_conv[simp]: "(sall\<cdot>(\<Lambda> x. TT)\<cdot>xs = TT) \<longleftrightarrow> (xs \<noteq> \<bottom>)"
by auto

lemma sall_TT[simp]: "(sall\<cdot>p\<cdot>xs = TT) \<longleftrightarrow> (xs \<noteq> \<bottom> \<and> (\<forall>x\<in>sset xs. p\<cdot>x = TT))"
by (induct xs) simp_all

fixrec sfilter :: "('a \<rightarrow> tr) \<rightarrow> [:'a:] \<rightarrow> [:'a:]" where
  "sfilter\<cdot>p\<cdot>[::] = [::]"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sfilter\<cdot>p\<cdot>(x :# xs) = If p\<cdot>x then x :# sfilter\<cdot>p\<cdot>xs else sfilter\<cdot>p\<cdot>xs"

lemma sfilter_strict[simp]: "sfilter\<cdot>p\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma sfilter_bottom_iff[simp]: "(sfilter\<cdot>p\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom> \<or> (\<exists>x\<in>sset xs. p\<cdot>x = \<bottom>))"
by (induct xs) (use trE in auto)

lemma sset_sfilter[simp]:
  assumes "\<And>x. x \<in> sset xs \<Longrightarrow> p\<cdot>x \<noteq> \<bottom>"
  shows "sset (sfilter\<cdot>p\<cdot>xs) = {x |x. x \<in> sset xs \<and> p\<cdot>x = TT}"
using assms by (induct xs) (fastforce simp: If2_def[symmetric] split: If2_splits)+

lemma sfilter_strict_scons[simp]:
  assumes "p\<cdot>\<bottom> = \<bottom>"
  shows "sfilter\<cdot>p\<cdot>(x :# xs) = If p\<cdot>x then x :# sfilter\<cdot>p\<cdot>xs else sfilter\<cdot>p\<cdot>xs"
using assms by (cases "x = \<bottom>"; cases "xs = \<bottom>"; simp)

lemma sfilter_scons_let:
  assumes "p\<cdot>\<bottom> = \<bottom>"
  shows "sfilter\<cdot>p\<cdot>(x :# xs) = (let xs' = sfilter\<cdot>p\<cdot>xs in If p\<cdot>x then x :# xs' else xs')"
unfolding Let_def using assms by simp

lemma sfilter_sappend[simp]: "sfilter\<cdot>p\<cdot>(xs :@ ys) = sfilter\<cdot>p\<cdot>xs :@ sfilter\<cdot>p\<cdot>ys"
by (cases "ys"; clarsimp) (induct xs; fastforce simp: If2_def[symmetric] split: If2_splits)

lemma sfilter_const_FF[simp]:
  assumes "xs \<noteq> \<bottom>"
  shows "sfilter\<cdot>(\<Lambda> x. FF)\<cdot>xs = [::]"
using assms by (induct xs) simp_all

lemma sfilter_const_FF_conv[simp]: "(sfilter\<cdot>(\<Lambda> x. FF)\<cdot>xs = [::]) \<longleftrightarrow> (xs \<noteq> \<bottom>)"
by auto

lemma sfilter_const_TT[simp]: "sfilter\<cdot>(\<Lambda> x. TT)\<cdot>xs = xs"
by (induct xs) simp_all

lemma sfilter_cong:
  assumes "xs = xs'"
  assumes "\<And>x. x \<in> sset xs \<Longrightarrow> p\<cdot>x = p'\<cdot>x"
  shows "sfilter\<cdot>p\<cdot>xs = sfilter\<cdot>p'\<cdot>xs'"
using assms by (induct xs arbitrary: xs') auto

lemma sfilter_snil_conv[simp]: "sfilter\<cdot>p\<cdot>xs = [::] \<longleftrightarrow> sall\<cdot>(neg oo p)\<cdot>xs = TT"
by (induct xs; force simp: If2_def[symmetric] split: If2_splits)

lemma sfilter_sfilter': "sfilter\<cdot>p\<cdot>(sfilter\<cdot>q\<cdot>xs) = sfilter\<cdot>(\<Lambda> x. q\<cdot>x andalso p\<cdot>x)\<cdot>xs"
proof(induct xs)
  case (scons x xs) from scons(1, 2) show ?case
    by (cases "sfilter\<cdot>q\<cdot>xs = \<bottom>")
       (simp_all add: If_distr If_andalso scons(3)[symmetric] del: sfilter_bottom_iff)
qed simp_all

lemma sfilter_sfilter: "sfilter\<cdot>p oo sfilter\<cdot>q = sfilter\<cdot>(\<Lambda> x. q\<cdot>x andalso p\<cdot>x)"
by (clarsimp simp: cfun_eq_iff sfilter_sfilter')

lemma sfilter_smap':
  assumes "p\<cdot>\<bottom> = \<bottom>"
  shows "sfilter\<cdot>p\<cdot>(smap\<cdot>f\<cdot>xs) = smap\<cdot>f\<cdot>(sfilter\<cdot>(p oo f)\<cdot>xs)"
using assms by (induct xs; simp add: If2_def[symmetric] split: If2_splits) (metis slist.con_rews(2) smap.simps(2) smap_strict)

lemma sfilter_smap:
  assumes "p\<cdot>\<bottom> = \<bottom>"
  shows "sfilter\<cdot>p oo smap\<cdot>f = smap\<cdot>f oo sfilter\<cdot>(p oo f)"
using assms by (clarsimp simp: cfun_eq_iff sfilter_smap')

fixrec sfoldl :: "('a::pcpo \<rightarrow> 'b::domain \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> [:'b:] \<rightarrow> 'a" where
  "sfoldl\<cdot>f\<cdot>z\<cdot>[::] = z"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sfoldl\<cdot>f\<cdot>z\<cdot>(x :# xs) = sfoldl\<cdot>f\<cdot>(f\<cdot>z\<cdot>x)\<cdot>xs"

lemma sfoldl_strict[simp]: "sfoldl\<cdot>f\<cdot>z\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma sfoldl_strict_f[simp]:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  shows "sfoldl\<cdot>f\<cdot>\<bottom>\<cdot>xs = \<bottom>"
using assms by (induct xs) simp_all

lemma sfoldl_cong:
  assumes "xs = xs'"
  assumes "z = z'"
  assumes "\<And>x z. x \<in> sset xs \<Longrightarrow> f\<cdot>z\<cdot>x = f'\<cdot>z\<cdot>x"
  shows "sfoldl\<cdot>f\<cdot>z\<cdot>xs = sfoldl\<cdot>f'\<cdot>z'\<cdot>xs'"
using assms by (induct xs arbitrary: xs' z z') auto

lemma sfoldl_sappend[simp]:
  assumes "f\<cdot>\<bottom> = \<bottom>"
  shows "sfoldl\<cdot>f\<cdot>z\<cdot>(xs :@ ys) = sfoldl\<cdot>f\<cdot>(sfoldl\<cdot>f\<cdot>z\<cdot>xs)\<cdot>ys"
using assms by (cases "ys = \<bottom>", force) (induct xs arbitrary: z; simp)

fixrec sfoldr :: "('b \<rightarrow> 'a::pcpo \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> [:'b:] \<rightarrow> 'a" where
  "sfoldr\<cdot>f\<cdot>z\<cdot>[::] = z"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sfoldr\<cdot>f\<cdot>z\<cdot>(x :# xs) = f\<cdot>x\<cdot>(sfoldr\<cdot>f\<cdot>z\<cdot>xs)"

lemma sfoldr_strict[simp]: "sfoldr\<cdot>f\<cdot>z\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec sconcat :: "[:[:'a:]:] \<rightarrow> [:'a:]" where
  "sconcat\<cdot>[::] = [::]"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sconcat\<cdot>(x :# xs) = x :@ sconcat\<cdot>xs"

lemma sconcat_strict[simp]: "sconcat\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma sconcat_scons[simp]:
  shows "sconcat\<cdot>(x :# xs) = x :@ sconcat\<cdot>xs"
by (cases "x = \<bottom>", force) (induct xs; fastforce)

lemma sconcat_sfoldl_aux: "sfoldl\<cdot>sappend\<cdot>z\<cdot>xs = z :@ sconcat\<cdot>xs"
by (induct xs arbitrary: z) simp_all

lemma sconcat_sfoldl: "sconcat = sfoldl\<cdot>sappend\<cdot>[::]"
by (clarsimp simp: cfun_eq_iff sconcat_sfoldl_aux)

lemma sconcat_sappend[simp]: "sconcat\<cdot>(xs :@ ys) = sconcat\<cdot>xs :@ sconcat\<cdot>ys"
by (induct xs) simp_all

fixrec slength :: "[:'a:] \<rightarrow> Integer"
where
  "slength\<cdot>[::] = 0"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> slength\<cdot>(x :# xs) = slength\<cdot>xs + 1"

lemma slength_strict[simp]: "slength\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma slength_bottom_iff[simp]: "(slength\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom>)"
by (induct xs) force+

lemma slength_ge_0: "slength\<cdot>xs = MkI\<cdot>n \<Longrightarrow> n \<ge> 0"
by (induct xs arbitrary: n) (simp add: one_Integer_def plus_eq_MkI_conv; force)+

lemma slengthE:
  shows "\<lbrakk>xs \<noteq> \<bottom>; \<And>n. \<lbrakk>slength\<cdot>xs = MkI\<cdot>n; 0 \<le> n\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
by (meson Integer.exhaust slength_bottom_iff slength_ge_0)

lemma slength_0_conv[simp]:
  "(slength\<cdot>xs = 0) \<longleftrightarrow> (xs = [::])"
  "(slength\<cdot>xs = MkI\<cdot>0) \<longleftrightarrow> (xs = [::])"
  "eq\<cdot>0\<cdot>(slength\<cdot>xs) = snull\<cdot>xs"
  "eq\<cdot>(slength\<cdot>xs)\<cdot>0 = snull\<cdot>xs"
by (induct xs) (auto simp: one_Integer_def elim: slengthE)

lemma le_slength_0[simp]: "(le\<cdot>0\<cdot>(slength\<cdot>xs) = TT) \<longleftrightarrow> (xs \<noteq> \<bottom>)"
by (cases "slength\<cdot>xs") (auto simp: slength_ge_0 zero_Integer_def)

lemma lt_slength_0[simp]:
  "xs \<noteq> \<bottom> \<Longrightarrow> lt\<cdot>(slength\<cdot>xs)\<cdot>0 = FF"
  "xs \<noteq> \<bottom> \<Longrightarrow> lt\<cdot>(slength\<cdot>xs)\<cdot>(slength\<cdot>xs + 1) = TT"
unfolding zero_Integer_def one_Integer_def by (auto elim: slengthE)

lemma slength_smap[simp]:
  assumes "\<And>x. x \<noteq> \<bottom> \<Longrightarrow> f\<cdot>x \<noteq> \<bottom>"
  shows "slength\<cdot>(smap\<cdot>f\<cdot>xs) = slength\<cdot>xs"
using assms by (induct xs) simp_all

lemma slength_sappend[simp]: "slength\<cdot>(xs :@ ys) = slength\<cdot>xs + slength\<cdot>ys"
by (cases "ys = \<bottom>", force) (induct xs; force simp: ac_simps)

lemma slength_sfoldl_aux: "sfoldl\<cdot>(\<Lambda> i _. i + 1)\<cdot>z\<cdot>xs = z + slength\<cdot>xs"
by (induct xs arbitrary: z) (simp_all add: ac_simps)

lemma slength_sfoldl: "slength = sfoldl\<cdot>(\<Lambda> i _. i + 1)\<cdot>0"
by (clarsimp simp: cfun_eq_iff slength_sfoldl_aux)

lemma le_slength_plus:
  assumes "xs \<noteq> \<bottom>"
  assumes "n \<noteq> \<bottom>"
  shows "le\<cdot>n\<cdot>(slength\<cdot>xs + n) = TT"
using assms by (cases n; force elim: slengthE)

fixrec srev :: "[:'a:] \<rightarrow> [:'a:]" where
  "srev\<cdot>[::] = [::]"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> srev\<cdot>(x :# xs) = srev\<cdot>xs :@ [:x:]"

lemma srev_strict[simp]: "srev\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma srev_bottom_iff[simp]: "(srev\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom>)"
by (induct xs) simp_all

lemma srev_scons[simp]: "srev\<cdot>(x :# xs) = srev\<cdot>xs :@ [:x:]"
by (cases "x = \<bottom>", clarsimp) (induct xs; force)

lemma srev_sappend[simp]: "srev\<cdot>(xs :@ ys) = srev\<cdot>ys :@ srev\<cdot>xs"
by (induct xs) simp_all

lemma srev_srev_ident[simp]: "srev\<cdot>(srev\<cdot>xs) = xs"
by (induct xs) auto

lemma srev_cases[case_names bottom snil ssnoc]:
  assumes "xs = \<bottom> \<Longrightarrow> P"
  assumes "xs = [::] \<Longrightarrow> P"
  assumes "\<And>y ys. \<lbrakk>y \<noteq> \<bottom>; ys \<noteq> \<bottom>; xs = ys :@ [:y:]\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms by (metis slist.exhaust srev.simps(1) srev_scons srev_srev_ident srev_strict)

lemma srev_induct[case_names bottom snil ssnoc]:
  assumes "P \<bottom>"
  assumes "P [::]"
  assumes "\<And>x xs. \<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>; P xs\<rbrakk> \<Longrightarrow> P (xs :@ [:x:])"
  shows "P xs"
proof -
  have "P (srev\<cdot>(srev\<cdot>xs))" by (rule slist.induct[where x="srev\<cdot>xs"]; simp add: assms)
  then show ?thesis by simp
qed

lemma sfoldr_conv_sfoldl:
  assumes "\<And>x. f\<cdot>x\<cdot>\<bottom> = \<bottom>" \<comment>\<open>\<open>f\<close> must be strict in the accumulator.\<close>
  shows "sfoldr\<cdot>f\<cdot>z\<cdot>xs = sfoldl\<cdot>(\<Lambda> acc x. f\<cdot>x\<cdot>acc)\<cdot>z\<cdot>(srev\<cdot>xs)"
using assms by (induct xs arbitrary: z) simp_all

fixrec stake :: "Integer \<rightarrow> [:'a:] \<rightarrow> [:'a:]" where \<comment>\<open> Note: strict in both parameters. \<close>
  "stake\<cdot>\<bottom>\<cdot>\<bottom> = \<bottom>"
| "i \<noteq> \<bottom> \<Longrightarrow> stake\<cdot>i\<cdot>[::] = [::]"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> stake\<cdot>i\<cdot>(x :# xs) = If le\<cdot>i\<cdot>0 then [::] else x :# stake\<cdot>(i - 1)\<cdot>xs"

lemma stake_strict[simp]:
  "stake\<cdot>\<bottom> = \<bottom>"
  "stake\<cdot>i\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

lemma stake_bottom_iff[simp]: "(stake\<cdot>i\<cdot>xs = \<bottom>) \<longleftrightarrow> (i = \<bottom> \<or> xs = \<bottom>)"
by (induct xs arbitrary: i; clarsimp; case_tac i; clarsimp)

lemma stake_0[simp]:
  "xs \<noteq> \<bottom> \<Longrightarrow> stake\<cdot>0\<cdot>xs = [::]"
  "xs \<noteq> \<bottom> \<Longrightarrow> stake\<cdot>(MkI\<cdot>0)\<cdot>xs = [::]"
  "stake\<cdot>0\<cdot>xs \<sqsubseteq> [::]"
by (cases xs; simp add: zero_Integer_def)+

lemma stake_scons[simp]: "le\<cdot>1\<cdot>i = TT \<Longrightarrow> stake\<cdot>i\<cdot>(x :# xs) = x :# stake\<cdot>(i - 1)\<cdot>xs"
by (cases i; cases "x = \<bottom>"; cases "xs = \<bottom>";
    simp add: zero_Integer_def one_Integer_def split: if_splits)

lemma take_MkI_scons[simp]:
  "0 < n \<Longrightarrow> stake\<cdot>(MkI\<cdot>n)\<cdot>(x :# xs) = x :# stake\<cdot>(MkI\<cdot>(n - 1))\<cdot>xs"
by (cases "x = \<bottom>"; cases "xs = \<bottom>"; simp add: zero_Integer_def one_Integer_def)

lemma stake_numeral_scons[simp]:
  "xs \<noteq> \<bottom> \<Longrightarrow> stake\<cdot>1\<cdot>(x :# xs) = [:x:]"
  "stake\<cdot>(numeral (Num.Bit0 k))\<cdot>(x :# xs) = x :# stake\<cdot>(numeral (Num.BitM k))\<cdot>xs"
  "stake\<cdot>(numeral (Num.Bit1 k))\<cdot>(x :# xs) = x :# stake\<cdot>(numeral (Num.Bit0 k))\<cdot>xs"
by (cases "x = \<bottom>"; cases xs; simp add: zero_Integer_def one_Integer_def numeral_Integer_eq)+

lemma stake_all:
  assumes "le\<cdot>(slength\<cdot>xs)\<cdot>i = TT"
  shows "stake\<cdot>i\<cdot>xs = xs"
using assms
proof(induct xs arbitrary: i)
  case (scons x xs i) then show ?case
    by (cases i; clarsimp simp: If2_def[symmetric] zero_Integer_def one_Integer_def split: If2_splits if_splits elim!: slengthE)
qed (simp_all add: le_defined)

lemma stake_all_triv[simp]: "stake\<cdot>(slength\<cdot>xs)\<cdot>xs = xs"
by (cases "xs = \<bottom>") (auto simp: stake_all)

lemma stake_append[simp]: "stake\<cdot>i\<cdot>(xs :@ ys) = stake\<cdot>i\<cdot>xs :@ stake\<cdot>(i - slength\<cdot>xs)\<cdot>ys"
proof(induct xs arbitrary: i)
  case (snil i) then show ?case by (cases i; simp add: zero_Integer_def)
next
  case (scons x xs i) then show ?case
    by (cases i; cases ys; clarsimp simp: If2_def[symmetric] zero_Integer_def one_Integer_def split: If2_splits  elim!: slengthE)
qed simp_all

fixrec sdrop :: "Integer \<rightarrow> [:'a:] \<rightarrow> [:'a:]" where \<comment>\<open> Note: strict in both parameters. \<close>
  [simp del]: "sdrop\<cdot>i\<cdot>xs = If le\<cdot>i\<cdot>0 then xs else (case xs of [::] \<Rightarrow> [::] | y :# ys \<Rightarrow> sdrop\<cdot>(i - 1)\<cdot>ys)"

lemma sdrop_strict[simp]:
  "sdrop\<cdot>\<bottom> = \<bottom>"
  "sdrop\<cdot>i\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

lemma sdrop_bottom_iff[simp]: "(sdrop\<cdot>i\<cdot>xs = \<bottom>) \<longleftrightarrow> (i = \<bottom> \<or> xs = \<bottom>)"
proof(induct xs arbitrary: i)
  case (snil i) then show ?case by (subst sdrop.unfold) (cases i; simp)
next
  case (scons x xs i) then show ?case by (subst sdrop.unfold) fastforce
qed simp

lemma sdrop_snil[simp]:
  assumes "i \<noteq> \<bottom>"
  shows "sdrop\<cdot>i\<cdot>[::] = [::]"
using assms by (subst sdrop.unfold; fastforce)

lemma sdrop_snil_conv[simp]: "(sdrop\<cdot>i\<cdot>[::] = [::]) \<longleftrightarrow> (i \<noteq> \<bottom>)"
by (subst sdrop.unfold; fastforce)

lemma sdrop_0[simp]:
  "sdrop\<cdot>0\<cdot>xs = xs"
  "sdrop\<cdot>(MkI\<cdot>0)\<cdot>xs = xs"
by (subst sdrop.simps, simp add: zero_Integer_def)+

lemma sdrop_pos:
  "le\<cdot>i\<cdot>0 = FF \<Longrightarrow> sdrop\<cdot>i\<cdot>xs = (case xs of [::] \<Rightarrow> [::] | y :# ys \<Rightarrow> sdrop\<cdot>(i - 1)\<cdot>ys)"
by (subst sdrop.simps, simp)

lemma sdrop_neg:
  "le\<cdot>i\<cdot>0 = TT \<Longrightarrow> sdrop\<cdot>i\<cdot>xs = xs"
by (subst sdrop.simps, simp)

lemma sdrop_numeral_scons[simp]:
  "x \<noteq> \<bottom> \<Longrightarrow> sdrop\<cdot>1\<cdot>(x :# xs) = xs"
  "x \<noteq> \<bottom> \<Longrightarrow> sdrop\<cdot>(numeral (Num.Bit0 k))\<cdot>(x :# xs) = sdrop\<cdot>(numeral (Num.BitM k))\<cdot>xs"
  "x \<noteq> \<bottom> \<Longrightarrow> sdrop\<cdot>(numeral (Num.Bit1 k))\<cdot>(x :# xs) = sdrop\<cdot>(numeral (Num.Bit0 k))\<cdot>xs"
by (subst sdrop.simps,
    simp add: zero_Integer_def one_Integer_def numeral_Integer_eq; cases xs; simp)+

lemma sdrop_sappend[simp]:
  "sdrop\<cdot>i\<cdot>(xs :@ ys) = sdrop\<cdot>i\<cdot>xs :@ sdrop\<cdot>(i - slength\<cdot>xs)\<cdot>ys"
proof(induct xs arbitrary: i)
  case (snil i) then show ?case by (cases i; simp add: zero_Integer_def)
next
  case (scons x xs i) then show ?case
    by (cases "ys = \<bottom>"; cases "le\<cdot>i\<cdot>0"; cases i;
        clarsimp simp: zero_Integer_def one_Integer_def sdrop_neg sdrop_pos add.commute diff_diff_add
                split: if_splits elim!: slengthE)
qed simp

lemma sdrop_all:
  assumes "le\<cdot>(slength\<cdot>xs)\<cdot>i = TT"
  shows "sdrop\<cdot>i\<cdot>xs = [::]"
using assms
proof(induct xs arbitrary: i)
  case (scons x xs i) then show ?case
    by (subst sdrop.unfold; cases i;
        clarsimp simp: If2_def[symmetric] zero_Integer_def one_Integer_def split: If2_splits if_splits elim!: slengthE)
qed (simp_all add: le_defined)

lemma slength_sdrop[simp]:
  "slength\<cdot>(sdrop\<cdot>i\<cdot>xs) = If le\<cdot>i\<cdot>0 then slength\<cdot>xs else If le\<cdot>(slength\<cdot>xs)\<cdot>i then 0 else slength\<cdot>xs - i"
proof(induct xs arbitrary: i)
  case (snil i) then show ?case by (cases i; simp add: zero_Integer_def)
next
  case (scons x xs i) then show ?case
    by (subst sdrop.unfold; cases i; clarsimp simp: zero_Integer_def one_Integer_def elim!: slengthE)
qed simp

lemma sdrop_not_snilD:
  assumes "sdrop\<cdot>(MkI\<cdot>i)\<cdot>xs \<noteq> [::]"
  assumes "xs \<noteq> \<bottom>"
  shows "lt\<cdot>(MkI\<cdot>i)\<cdot>(slength\<cdot>xs) = TT \<and> xs \<noteq> [::]"
using assms
proof(induct xs arbitrary: i)
  case (scons x xs i) then show ?case
    by (subst (asm) (2) sdrop.unfold, clarsimp simp: zero_Integer_def one_Integer_def not_le sdrop_all elim!: slengthE)
qed simp_all

lemma sdrop_sappend_same:
  assumes "xs \<noteq> \<bottom>"
  shows "sdrop\<cdot>(slength\<cdot>xs)\<cdot>(xs :@ ys) = ys"
using assms
proof(induct xs arbitrary: ys)
  case (scons x xs ys) then show ?case
    by (cases "ys = \<bottom>"; subst sdrop.unfold; clarsimp simp: zero_Integer_def one_Integer_def elim!: slengthE)
qed simp_all

fixrec sscanl :: "('a \<rightarrow> 'b \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> [:'b:] \<rightarrow> [:'a:]" where
  "sscanl\<cdot>f\<cdot>z\<cdot>[::] = z :# [::]"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sscanl\<cdot>f\<cdot>z\<cdot>(x :# xs) = z :# sscanl\<cdot>f\<cdot>(f\<cdot>z\<cdot>x)\<cdot>xs"

lemma sscanl_strict[simp]:
  "sscanl\<cdot>f\<cdot>\<bottom>\<cdot>xs = \<bottom>"
  "sscanl\<cdot>f\<cdot>z\<cdot>\<bottom> = \<bottom>"
by (cases xs) fixrec_simp+

lemma sscanl_cong:
  assumes "xs = xs'"
  assumes "z = z'"
  assumes "\<And>x z. x \<in> sset xs \<Longrightarrow> f\<cdot>z\<cdot>x = f'\<cdot>z\<cdot>x"
  shows "sscanl\<cdot>f\<cdot>z\<cdot>xs = sscanl\<cdot>f'\<cdot>z'\<cdot>xs'"
using assms by (induct xs arbitrary: xs' z z') auto

lemma sscanl_lfp_fusion':
  assumes "g\<cdot>\<bottom> = \<bottom>"
  assumes *: "\<And>acc x. x \<noteq> \<bottom> \<Longrightarrow> g\<cdot>(f\<cdot>acc\<cdot>x) = f'\<cdot>(g\<cdot>acc)\<cdot>x"
  shows "smap\<cdot>g\<cdot>(sscanl\<cdot>f\<cdot>z\<cdot>xs) = sscanl\<cdot>f'\<cdot>(g\<cdot>z)\<cdot>xs"
using assms by (induct xs arbitrary: z) simp_all

lemma sscanl_lfp_fusion:
  assumes "g\<cdot>\<bottom> = \<bottom>"
  assumes *: "\<And>acc x. x \<noteq> \<bottom> \<Longrightarrow> g\<cdot>(f\<cdot>acc\<cdot>x) = f'\<cdot>(g\<cdot>acc)\<cdot>x"
  shows "smap\<cdot>g oo sscanl\<cdot>f\<cdot>z = sscanl\<cdot>f'\<cdot>(g\<cdot>z)"
using assms by (clarsimp simp: cfun_eq_iff sscanl_lfp_fusion')

lemma sscanl_ww_fusion': \<comment>\<open> Worker/wrapper @{cite [cite_macro=citep] "GillHutton:2009" and "Gammie:2011"} specialised to @{const \<open>sscanl\<close>} \<close>
  fixes wrap :: "'b \<rightarrow> 'a"
  fixes unwrap :: "'a \<rightarrow> 'b"
  fixes z :: "'a"
  fixes f :: "'a \<rightarrow> 'c \<rightarrow> 'a"
  fixes f' :: "'b \<rightarrow> 'c \<rightarrow> 'b"
  assumes ww: "wrap oo unwrap = ID"
  assumes wb: "\<And>z x. x \<noteq> \<bottom> \<Longrightarrow> unwrap\<cdot>(f\<cdot>(wrap\<cdot>z)\<cdot>x) = f'\<cdot>(unwrap\<cdot>(wrap\<cdot>z))\<cdot>x"
  shows "sscanl\<cdot>f\<cdot>z\<cdot>xs = smap\<cdot>wrap\<cdot>(sscanl\<cdot>f'\<cdot>(unwrap\<cdot>z)\<cdot>xs)"
using assms
by (induct xs arbitrary: z) (simp add: cfun_eq_iff retraction_cfcomp_strict | metis)+

lemma sscanl_ww_fusion: \<comment>\<open> Worker/wrapper @{cite [cite_macro=citep] "GillHutton:2009" and "Gammie:2011"} specialised to @{const \<open>sscanl\<close>} \<close>
  fixes wrap :: "'b \<rightarrow> 'a"
  fixes unwrap :: "'a \<rightarrow> 'b"
  fixes z :: "'a"
  fixes f :: "'a \<rightarrow> 'c \<rightarrow> 'a"
  fixes f' :: "'b \<rightarrow> 'c \<rightarrow> 'b"
  assumes ww: "wrap oo unwrap = ID"
  assumes wb: "\<And>z x. x \<noteq> \<bottom> \<Longrightarrow> unwrap\<cdot>(f\<cdot>(wrap\<cdot>z)\<cdot>x) = f'\<cdot>(unwrap\<cdot>(wrap\<cdot>z))\<cdot>x"
  shows "sscanl\<cdot>f\<cdot>z = smap\<cdot>wrap oo sscanl\<cdot>f'\<cdot>(unwrap\<cdot>z)"
using assms by (clarsimp simp: cfun_eq_iff sscanl_ww_fusion')

fixrec sinits :: "[:'a:] \<rightarrow> [:[:'a:]:]" where
  "sinits\<cdot>[::] = [::] :# [::]"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sinits\<cdot>(x :# xs) = [::] :# smap\<cdot>(scons\<cdot>x)\<cdot>(sinits\<cdot>xs)"

lemma sinits_strict[simp]: "sinits\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma sinits_bottom_iff[simp]: "(sinits\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom>)"
by (induct xs) simp_all

lemma sinits_not_snil[iff]: "sinits\<cdot>xs \<noteq> [::]"
by (cases xs) simp_all

lemma sinits_empty_bottom[simp]: "(sset (sinits\<cdot>xs) = {}) \<longleftrightarrow> (xs = \<bottom>)"
by (cases xs) simp_all

lemma sinits_scons[simp]: "sinits\<cdot>(x :# xs) = [::] :# smap\<cdot>(x :#)\<cdot>(sinits\<cdot>xs)"
by (cases "x = \<bottom>", force) (induct xs; force)

lemma sinits_length[simp]: "slength\<cdot>(sinits\<cdot>xs) = slength\<cdot>xs + 1"
by (induct xs) simp_all

lemma sinits_snoc[simp]: "sinits\<cdot>(xs :@ [:x:]) = sinits\<cdot>xs :@ [:xs :@ [:x:]:]"
by (induct xs) simp_all

lemma sinits_foldr': \<comment>\<open> @{cite [cite_macro=citet] \<open>p30\<close> "Bird:1987"} \<close>
  shows "sinits\<cdot>xs = sfoldr\<cdot>(\<Lambda> x xs. [:[::]:] :@ smap\<cdot>(x :#)\<cdot>xs)\<cdot>[:[::]:]\<cdot>xs"
by (induct xs) simp_all

lemma sinits_sscanl':
  shows "smap\<cdot>(sfoldl\<cdot>f\<cdot>z)\<cdot>(sinits\<cdot>xs) = sscanl\<cdot>f\<cdot>z\<cdot>xs"
by (induct xs arbitrary: z) (simp_all cong: smap_cong add: oo_def eta_cfun)

lemma sinits_sscanl: \<comment>\<open> @{cite [cite_macro=citet] \<open>Lemma~5\<close> "Bird:1987"}, @{cite [cite_macro=citet] \<open>p118 ``the scan lemma''\<close> "Bird:PearlsofFAD:2010"} \<close>
  shows "smap\<cdot>(sfoldl\<cdot>f\<cdot>z) oo sinits = sscanl\<cdot>f\<cdot>z"
by (simp add: sinits_sscanl' cfun_eq_iff)

lemma sinits_all[simp]: "(xs \<in> sset (sinits\<cdot>xs)) \<longleftrightarrow> (xs \<noteq> \<bottom>)"
by (induct xs) simp_all

fixrec stails :: "[:'a:] \<rightarrow> [:[:'a:]:]" where
  "stails\<cdot>[::] = [::] :# [::]"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> stails\<cdot>(x :# xs) = (x :# xs) :# stails\<cdot>xs"

lemma stails_strict[simp]: "stails\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma stails_bottom_iff[simp]: "(stails\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom>)"
by (induct xs) simp_all

lemma stails_not_snil[iff]: "stails\<cdot>xs \<noteq> [::]"
by (cases xs) simp_all

lemma stails_scons[simp]: "stails\<cdot>(x :# xs) = (x :# xs) :# stails\<cdot>xs"
by (induct xs) (cases "x = \<bottom>"; simp)+

lemma stails_slength[simp]: "slength\<cdot>(stails\<cdot>xs) = slength\<cdot>xs + 1"
by (induct xs) simp_all

lemma stails_snoc[simp]:
  shows "stails\<cdot>(xs :@ [:x:]) = smap\<cdot>(\<Lambda> ys. ys :@ [:x:])\<cdot>(stails\<cdot>xs) :@ [:[::]:]"
by (induct xs) simp_all

lemma stails_sfoldl':
  shows "stails\<cdot>xs = sfoldl\<cdot>(\<Lambda> xs x. smap\<cdot>(\<Lambda> ys. ys :@ [:x:])\<cdot>xs :@ [:[::]:])\<cdot>[:[::]:]\<cdot>xs"
by (induct xs rule: srev_induct) simp_all

lemma stails_sfoldl:
  shows "stails = sfoldl\<cdot>(\<Lambda> xs x. smap\<cdot>(\<Lambda> ys. ys :@ [:x:])\<cdot>xs :@ [:[::]:])\<cdot>[:[::]:]"
by (clarsimp simp: cfun_eq_iff stails_sfoldl')

lemma stails_all[simp]: "(xs \<in> sset (stails\<cdot>xs)) \<longleftrightarrow> (xs \<noteq> \<bottom>)"
by (cases xs) simp_all

fixrec selem :: "'a::Eq_def \<rightarrow> [:'a:] \<rightarrow> tr" where
  "selem\<cdot>x\<cdot>[::] = FF"
| "\<lbrakk>y \<noteq> \<bottom>; ys \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> selem\<cdot>x\<cdot>(y :# ys) = (eq\<cdot>x\<cdot>y orelse selem\<cdot>x\<cdot>ys)"

lemma selem_strict[simp]: "selem\<cdot>x\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma selem_bottom_iff[simp]: "(selem\<cdot>x\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom> \<or> (xs \<noteq> [::] \<and> x = \<bottom>))"
by (induct xs) auto

lemma selem_sappend[simp]:
  assumes "ys \<noteq> \<bottom>"
  shows "selem\<cdot>x\<cdot>(xs :@ ys) = (selem\<cdot>x\<cdot>xs orelse selem\<cdot>x\<cdot>ys)"
using assms by (induct xs) simp_all

lemma elem_TT[simp]: "(selem\<cdot>x\<cdot>xs = TT) \<longleftrightarrow> (x \<in> sset xs)"
by (induct xs; auto) (metis sset_defined)+

lemma elem_FF[simp]: "(selem\<cdot>x\<cdot>xs = FF) \<longleftrightarrow> (xs = [::] \<or> (x \<noteq> \<bottom> \<and> xs \<noteq> \<bottom> \<and> x \<notin> sset xs))"
by (induct xs) auto

lemma selem_snil_stails[iff]:
  assumes "xs \<noteq> \<bottom>"
  shows "selem\<cdot>[::]\<cdot>(stails\<cdot>xs) = TT"
using assms by (induct xs) simp_all

fixrec sconcatMap :: "('a \<rightarrow> [:'b:]) \<rightarrow> [:'a:] \<rightarrow> [:'b:]" where
[simp del]: "sconcatMap\<cdot>f = sconcat oo smap\<cdot>f"

lemma sconcatMap_strict[simp]: "sconcatMap\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma sconcatMap_snil[simp]: "sconcatMap\<cdot>f\<cdot>[::] = [::]"
by fixrec_simp

lemma sconcatMap_scons[simp]: "x \<noteq> \<bottom> \<Longrightarrow> sconcatMap\<cdot>f\<cdot>(x :# xs) = f\<cdot>x :@ sconcatMap\<cdot>f\<cdot>xs"
by (cases "xs = \<bottom>"; simp add: sconcatMap.unfold)

lemma sconcatMap_bottom_iff[simp]: "(sconcatMap\<cdot>f\<cdot>xs = \<bottom>) \<longleftrightarrow> (xs = \<bottom> \<or> (\<exists>x\<in>sset xs. f\<cdot>x = \<bottom>))"
by (induct xs) simp_all

lemma sconcatMap_sappend[simp]: "sconcatMap\<cdot>f\<cdot>(xs :@ ys) = sconcatMap\<cdot>f\<cdot>xs :@ sconcatMap\<cdot>f\<cdot>ys"
by (induct xs) simp_all

lemma sconcatMap_monad_laws:
  "sconcatMap\<cdot>(\<Lambda> x. [:x:])\<cdot>xs = xs"
  "sconcatMap\<cdot>g\<cdot>(sconcatMap\<cdot>f\<cdot>xs) = sconcatMap\<cdot>(\<Lambda> x. sconcatMap\<cdot>g\<cdot>(f\<cdot>x))\<cdot>xs"
by (induct xs) simp_all

fixrec supto :: "Integer \<rightarrow> Integer \<rightarrow> [:Integer:]" where
  [simp del]: "supto\<cdot>i\<cdot>j = If le\<cdot>i\<cdot>j then i :# supto\<cdot>(i+1)\<cdot>j else [::]"

lemma upto_strict[simp]:
  "supto\<cdot>\<bottom> = \<bottom>"
  "supto\<cdot>m\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

lemma supto_is_snil_conv[simp]:
  "(supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j) = [::]) \<longleftrightarrow> (j < i)"
  "([::] = supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j)) \<longleftrightarrow> (j < i)"
by (subst supto.unfold; simp)+

lemma supto_simp[simp]:
  "j < i \<Longrightarrow> supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j) = [::]"
  "i \<le> j \<Longrightarrow> supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j) = MkI\<cdot>i :# supto\<cdot>(MkI\<cdot>i+1)\<cdot>(MkI\<cdot>j)"
  "supto\<cdot>0\<cdot>0 = [:0:]"
by (subst supto.simps, simp)+

lemma supto_defined[simp]: "supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j) \<noteq> \<bottom>" (is "?P i j")
proof (cases "j - i")
  fix d
  assume "j - i = int d"
  then show "?P i j"
  proof (induct d arbitrary: i j)
    case (Suc d i j)
    then have "j - (i + 1) = int d" and le: "i \<le> j" by simp_all
    from Suc(1)[OF this(1)] have IH: "?P (i+1) j" .
    then show ?case using le by (simp add: one_Integer_def)
  qed (simp add: one_Integer_def)
next
  fix d
  assume "j - i = - int d"
  then have "j \<le> i" by auto
  moreover
  { assume "j = i" then have "?P i j" by (simp add: one_Integer_def) }
  moreover
  { assume "j < i" then have "?P i j" by (simp add: one_Integer_def) }
  ultimately show ?thesis by arith
qed

lemma supto_bottom_iff[simp]:
  "(supto\<cdot>i\<cdot>j = \<bottom>) \<longleftrightarrow> (i = \<bottom> \<or> j = \<bottom>)"
by (cases i; simp; cases j; simp)

lemma supto_snoc[simp]:
  "i \<le> j \<Longrightarrow> supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j) = supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j-1) :@ [:MkI\<cdot>j:]"
proof(induct "nat(j - i)" arbitrary: i j)
  case 0 then show ?case by (simp add: one_Integer_def)
next
  case (Suc k i j)
  then have "k = nat (j - (i + 1))" "i < j" by linarith+
  from this(2) Suc.hyps(1)[OF this(1)] Suc(2,3) show ?case by (simp add: one_Integer_def)
qed

lemma slength_supto[simp]: "slength\<cdot>(supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j)) = MkI\<cdot>(if j < i then 0 else j - i + 1)" (is "?P i j")
proof (cases "j - i")
  fix d
  assume "j - i = int d"
  then show "?P i j"
  proof (induct d arbitrary: i j)
    case (Suc d i j)
    then have "j - (i + 1) = int d" and le: "i \<le> j" by simp_all
    from Suc(1)[OF this(1)] have IH: "?P (i+1) j" .
    then show ?case using le by (simp add: one_Integer_def)
  qed (simp add: one_Integer_def)
next
  fix d
  assume "j - i = - int d"
  then have "j \<le> i" by auto
  moreover
  { assume "j = i" then have "?P i j" by (simp add: one_Integer_def) }
  moreover
  { assume "j < i" then have "?P i j" by (simp add: one_Integer_def) }
  ultimately show ?thesis by arith
qed

lemma sset_supto[simp]:
  "sset (supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j)) = {MkI\<cdot>k |k. i \<le> k \<and> k \<le> j}" (is "sset (?u i j) = ?R i j")
proof (cases "j - i")
  case (nonneg k)
  then show ?thesis
  proof (induct k arbitrary: i j)
    case (Suc k)
    then have *: "j - (i + 1) = int k" by simp
    from Suc(1)[OF *] have IH: "sset (?u (i+1) j) = ?R (i+1) j" .
    from * have "i \<le> j" by simp
    then have "sset (?u i j) = sset (MkI\<cdot>i :# ?u (i+1) j)" by (simp add: one_Integer_def)
    also have "\<dots> = insert (MkI\<cdot>i) (?R (i+1) j)" by (simp add: IH)
    also have "\<dots> = ?R i j" using \<open>i \<le> j\<close> by auto
    finally show ?case .
  qed (force simp: one_Integer_def)
qed simp

lemma supto_split1: \<comment>\<open>From \<open>HOL.List\<close>\<close>
  assumes "i \<le> j"
  assumes "j \<le> k"
  shows "supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>k) = supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>(j - 1)) :@ supto\<cdot>(MkI\<cdot>j)\<cdot>(MkI\<cdot>k)"
using assms
proof (induct j rule: int_ge_induct)
  case (step l) with supto_simp(2) supto_snoc show ?case by (clarsimp simp: one_Integer_def)
qed simp

lemma supto_split2: \<comment>\<open>From \<open>HOL.List\<close>\<close>
  assumes "i \<le> j"
  assumes "j \<le> k"
  shows "supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>k) = supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>j) :@ supto\<cdot>(MkI\<cdot>(j + 1))\<cdot>(MkI\<cdot>k)"
proof(cases "j + 1 \<le> k")
  case True with assms show ?thesis
    by (subst supto_split1[where j="j + 1" and k=k]; clarsimp simp: one_Integer_def)
next
  case False with assms show ?thesis by (clarsimp simp: one_Integer_def not_le)
qed

lemma supto_split3: \<comment>\<open>From \<open>HOL.List\<close>\<close>
  assumes "i \<le> j"
  assumes "j \<le> k"
  shows "supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>k) = supto\<cdot>(MkI\<cdot>i)\<cdot>(MkI\<cdot>(j - 1)) :@ MkI\<cdot>j :# supto\<cdot>(MkI\<cdot>(j + 1))\<cdot>(MkI\<cdot>k)"
using assms supto_simp(2) supto_split1 by (metis one_Integer_def plus_MkI_MkI)

lemma sinits_stake':
  shows "sinits\<cdot>xs = smap\<cdot>(\<Lambda> i. stake\<cdot>i\<cdot>xs)\<cdot>(supto\<cdot>0\<cdot>(slength\<cdot>xs))"
proof(induct xs rule: srev_induct)
  case (ssnoc x xs) then show ?case
    apply (clarsimp simp: zero_Integer_def one_Integer_def stake_all
                simp del: supto_simp
                   elim!: slengthE)
    apply (rule arg_cong, rule smap_cong[OF refl])
    apply clarsimp
    done
qed simp_all

lemma stails_sdrop':
  shows "stails\<cdot>xs = smap\<cdot>(\<Lambda> i. sdrop\<cdot>i\<cdot>xs)\<cdot>(supto\<cdot>0\<cdot>(slength\<cdot>xs))"
proof(induct xs rule: srev_induct)
  case (ssnoc x xs) then show ?case
    apply (clarsimp simp: zero_Integer_def one_Integer_def sdrop_all
                simp del: supto_simp
                   elim!: slengthE)
    apply (rule arg_cong, rule smap_cong[OF refl])
    apply clarsimp
    apply (subst (3) sdrop_neg; fastforce simp: zero_Integer_def)
    done
qed simp_all

lemma sdrop_elem_stails[iff]:
  assumes "xs \<noteq> \<bottom>"
  shows "sdrop\<cdot>(MkI\<cdot>i)\<cdot>xs \<in> sset (stails\<cdot>xs)"
using assms
by (clarsimp simp: stails_sdrop' zero_Integer_def one_Integer_def elim!: slengthE)
   (metis add.left_neutral le_MkI_MkI le_cases not_less sdrop_all sdrop_neg zero_Integer_def zless_imp_add1_zle)

fixrec slast :: "[:'a:] \<rightarrow> 'a" where
  "slast\<cdot>[::] = \<bottom>"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> slast\<cdot>(x :# xs) = (case xs of [::] \<Rightarrow> x | y :# ys \<Rightarrow> slast\<cdot>xs)"

lemma slast_strict[simp]:
  "slast\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma slast_singleton[simp]: "slast\<cdot>[:x:] = x"
by (cases "x = \<bottom>"; simp)

lemma slast_sappend_ssnoc[simp]:
  assumes "xs \<noteq> \<bottom>"
  shows "slast\<cdot>(xs :@ [:x:]) = x"
using assms
proof(induct xs)
  case (scons y ys) then show ?case by (cases "x = \<bottom>"; simp; cases ys; simp)
qed simp_all

fixrec sbutlast :: "[:'a:] \<rightarrow> [:'a:]" where
  "sbutlast\<cdot>[::] = [::]"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> sbutlast\<cdot>(x :# xs) = (case xs of [::] \<Rightarrow> [::] | y :# ys \<Rightarrow> x :# sbutlast\<cdot>xs)"

lemma sbutlast_strict[simp]:
  "sbutlast\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma sbutlast_sappend_ssnoc[simp]:
  assumes "x \<noteq> \<bottom>"
  shows "sbutlast\<cdot>(xs :@ [:x:]) = xs"
using assms
proof(induct xs)
  case (scons y ys) then show ?case by (cases ys; simp)
qed simp_all

fixrec prefix :: "[:'a::Eq_def:] \<rightarrow> [:'a:] \<rightarrow> tr" where
  "prefix\<cdot>xs\<cdot>\<bottom> = \<bottom>"
| "ys \<noteq> \<bottom> \<Longrightarrow> prefix\<cdot>[::]\<cdot>ys = TT"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> prefix\<cdot>(x :# xs)\<cdot>[::] = FF"
| "\<lbrakk>x \<noteq> \<bottom>; xs \<noteq> \<bottom>; y \<noteq> \<bottom>; ys \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> prefix\<cdot>(x :# xs)\<cdot>(y :# ys) = (eq\<cdot>x\<cdot>y andalso prefix\<cdot>xs\<cdot>ys)"

lemma prefix_strict[simp]: "prefix\<cdot>\<bottom> = \<bottom>"
by (clarsimp simp: cfun_eq_iff) fixrec_simp

lemma prefix_bottom_iff[simp]: "(prefix\<cdot>xs\<cdot>ys = \<bottom>) \<longleftrightarrow> (xs = \<bottom> \<or> ys = \<bottom>)"
proof(induct xs arbitrary: ys)
  case (snil ys) then show ?case by (cases ys) simp_all
next
  case (scons a xs) then show ?case by (cases ys) simp_all
qed simp

lemma prefix_definedD:
  assumes "prefix\<cdot>xs\<cdot>ys = TT"
  shows "xs \<noteq> \<bottom> \<and> ys \<noteq> \<bottom>"
using assms by (induct xs arbitrary: ys) auto

lemma prefix_refl[simp]:
  assumes "xs \<noteq> \<bottom>"
  shows "prefix\<cdot>xs\<cdot>xs = TT"
using assms by (induct xs) simp_all

lemma prefix_refl_conv[simp]: "(prefix\<cdot>xs\<cdot>xs = TT) \<longleftrightarrow> (xs \<noteq> \<bottom>)"
by auto

lemma  prefix_of_snil[simp]: "prefix\<cdot>xs\<cdot>[::] = (case xs of [::] \<Rightarrow> TT | x :# xs \<Rightarrow> FF)"
by (cases xs) simp_all

lemma prefix_singleton_TT:
  shows "prefix\<cdot>[:x:]\<cdot>ys = TT \<longleftrightarrow> (x \<noteq> \<bottom> \<and> (\<exists>zs. zs \<noteq> \<bottom> \<and> ys = x :# zs))"
by (cases "x = \<bottom>"; clarsimp; cases ys; fastforce)

lemma prefix_singleton_FF:
  shows "prefix\<cdot>[:x:]\<cdot>ys = FF \<longleftrightarrow> (x \<noteq> \<bottom> \<and> (ys = [::] \<or> (\<exists>z zs. z \<noteq> \<bottom> \<and> zs \<noteq> \<bottom> \<and> ys = z :# zs \<and> x \<noteq> z)))"
by (cases "x = \<bottom>"; clarsimp; cases ys; fastforce)

lemma prefix_FF_not_snilD:
  assumes "prefix\<cdot>xs\<cdot>ys = FF"
  shows "xs \<noteq> [::]"
using assms by (cases xs; cases ys; simp)

lemma prefix_slength:
  assumes "prefix\<cdot>xs\<cdot>ys = TT"
  shows "le\<cdot>(slength\<cdot>xs)\<cdot>(slength\<cdot>ys) = TT"
using assms
proof(induct ys arbitrary: xs)
  case (snil xs) then show ?case by (cases xs) simp_all
next
  case (scons a ys) then show ?case by (cases xs) (simp_all add: le_plus_1)
qed simp

lemma prefix_slength_strengthen: "prefix\<cdot>xs\<cdot>ys = (le\<cdot>(slength\<cdot>xs)\<cdot>(slength\<cdot>ys) andalso prefix\<cdot>xs\<cdot>ys)"
by (rule andalso_weaken_left) (auto dest: prefix_slength)

lemma prefix_scons_snil[simp]: "prefix\<cdot>(x :# xs)\<cdot>[::] \<noteq> TT"
by (cases "x :# xs \<noteq> \<bottom>") auto

lemma scons_prefix_scons[simp]:
  "(prefix\<cdot>(x :# xs)\<cdot>(y :# ys) = TT) \<longleftrightarrow> (eq\<cdot>x\<cdot>y = TT \<and> prefix\<cdot>xs\<cdot>ys = TT)"
by (cases "x :# xs \<noteq> \<bottom> \<and> y :# ys \<noteq> \<bottom>") auto

lemma append_prefixD:
  assumes "prefix\<cdot>(xs :@ ys)\<cdot>zs = TT"
  shows "prefix\<cdot>xs\<cdot>zs = TT"
using assms
proof(induct xs arbitrary: zs)
  case (snil zs) then show ?case using prefix.simps(2) by force
next
  case (scons x xs zs) then show ?case
    by (metis prefix.simps(1) prefix_scons_snil sappend_scons scons_prefix_scons slist.exhaust)
qed simp

lemma same_prefix_prefix[simp]:
  assumes "xs \<noteq> \<bottom>"
  shows "prefix\<cdot>(xs :@ ys)\<cdot>(xs :@ zs) = prefix\<cdot>ys\<cdot>zs"
using assms
proof(cases "ys = \<bottom>" "zs = \<bottom>" rule: bool.exhaust[case_product bool.exhaust])
  case False_False with assms show ?thesis by (induct xs) simp_all
qed simp_all

lemma eq_prefix_TT:
  assumes "eq\<cdot>xs\<cdot>ys = TT"
  shows "prefix\<cdot>xs\<cdot>ys = TT"
using assms by (induct xs arbitrary: ys) (case_tac ys; simp)+

lemma prefix_eq_FF:
  assumes "prefix\<cdot>xs\<cdot>ys = FF"
  shows "eq\<cdot>xs\<cdot>ys = FF"
using assms by (induct xs arbitrary: ys) (case_tac ys; auto)+

lemma prefix_slength_eq:
  shows "eq\<cdot>xs\<cdot>ys = (eq\<cdot>(slength\<cdot>xs)\<cdot>(slength\<cdot>ys) andalso prefix\<cdot>xs\<cdot>ys)"
proof(induct xs arbitrary: ys)
  case (snil ys) then show ?case
    by (cases ys; clarsimp simp: one_Integer_def elim!: slengthE)
next
  case (scons x xs ys) then show ?case
    by (cases ys; clarsimp simp: zero_Integer_def one_Integer_def elim!: slengthE)
qed simp

lemma stake_slength_plus_1:
  shows "stake\<cdot>(slength\<cdot>xs + 1)\<cdot>(y :# ys) = y :# stake\<cdot>(slength\<cdot>xs)\<cdot>ys"
by (cases "xs = \<bottom>" "y = \<bottom>" "ys = \<bottom>" rule: bool.exhaust[case_product bool.exhaust bool.exhaust]; clarsimp)
   (auto simp: If2_def[symmetric] zero_Integer_def one_Integer_def split: If2_splits elim!: slengthE)

lemma sdrop_slength_plus_1:
  assumes "y \<noteq> \<bottom>"
  shows "sdrop\<cdot>(slength\<cdot>xs + 1)\<cdot>(y :# ys) = sdrop\<cdot>(slength\<cdot>xs)\<cdot>ys"
using assms
by (subst sdrop.simps;
    cases "xs = \<bottom>"; clarsimp; cases "ys = \<bottom>";
    clarsimp simp: If2_def[symmetric] zero_Integer_def one_Integer_def split: If2_splits elim!: slengthE)

lemma eq_take_length_prefix: "prefix\<cdot>xs\<cdot>ys = eq\<cdot>xs\<cdot>(stake\<cdot>(slength\<cdot>xs)\<cdot>ys)"
proof (induct xs arbitrary: ys)
  case (snil ys) show ?case by (cases ys; clarsimp)
next
  case (scons x xs ys)
  note IH = this
  show ?case
  proof (cases "slength\<cdot>xs = \<bottom>")
    case True then show ?thesis by simp
  next
    case False
    show ?thesis
    proof (cases ys)
      case bottom
      then show ?thesis using False
        using le_slength_plus[of xs 1] by simp
    next
      case snil then show ?thesis using False and IH(1,2) by simp
    next
      case (scons z zs)
      then show ?thesis
        using False and IH(1,2) IH(3)[of zs]
        by (simp add: stake_slength_plus_1 monofun_cfun_arg)
    qed
  qed
qed simp

lemma prefix_sdrop_slength:
  assumes "prefix\<cdot>xs\<cdot>ys = TT"
  shows "xs :@ sdrop\<cdot>(slength\<cdot>xs)\<cdot>ys = ys"
using assms by (induct xs arbitrary: ys) (case_tac ys; simp add: sdrop_slength_plus_1)+

lemma prefix_sdrop_prefix_eq:
  assumes "prefix\<cdot>xs\<cdot>ys = TT"
  shows "eq\<cdot>(sdrop\<cdot>(slength\<cdot>xs)\<cdot>ys)\<cdot>[::] = eq\<cdot>ys\<cdot>xs"
using assms by (induct xs arbitrary: ys) (case_tac ys; simp add: sdrop_slength_plus_1)+
(*<*)

end
(*>*)
