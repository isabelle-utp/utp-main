chapter \<open>Arithmetic Constructs\<close>

text \<open>Less genereric syntax, more committed towards embedding arithmetics\<close>

(*<*)
theory Syntax_Arith imports Syntax
begin
(*>*)

text \<open>(An embedding of) the syntax of arithmetic, obtained by adding plus and times\<close>

locale Syntax_Arith_aux =
Syntax_with_Connectives_Rename
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
+
Syntax_with_Numerals_and_Connectives_False_Disj
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
+
fixes
zer :: "'trm"
and
suc :: "'trm \<Rightarrow> 'trm"
and
pls :: "'trm \<Rightarrow> 'trm \<Rightarrow> 'trm"
and
tms :: "'trm \<Rightarrow> 'trm \<Rightarrow> 'trm"
assumes
Fvars_zero[simp,intro!]: "FvarsT zer = {}"
and
substT_zer[simp]: "\<And> t x. t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  substT zer t x = zer"
and
suc[simp]: "\<And>t. t \<in> trm \<Longrightarrow> suc t \<in> trm"
and
FvarsT_suc[simp]: "\<And> t. t \<in> trm \<Longrightarrow>
  FvarsT (suc t) = FvarsT t"
and
substT_suc[simp]: "\<And> t1 t x. t1 \<in> trm \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  substT (suc t1) t x = suc (substT t1 t x)"
and
pls[simp]: "\<And> t1 t2. t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> pls t1 t2 \<in> trm"
and
Fvars_pls[simp]: "\<And> t1 t2. t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow>
  FvarsT (pls t1 t2) = FvarsT t1 \<union> FvarsT t2"
and
substT_pls[simp]: "\<And> t1 t2 t x. t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  substT (pls t1 t2) t x = pls (substT t1 t x) (substT t2 t x)"
and
tms[simp]: "\<And> t1 t2. t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> tms t1 t2 \<in> trm"
and
Fvars_tms[simp]: "\<And> t1 t2. t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow>
  FvarsT (tms t1 t2) = FvarsT t1 \<union> FvarsT t2"
and
substT_tms[simp]: "\<And> t1 t2 t x. t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  substT (tms t1 t2) t x = tms (substT t1 t x) (substT t2 t x)"
begin

text \<open>The embedding of numbers into our abstract notion of numerals
(not required to be surjective)\<close>
fun Num :: "nat \<Rightarrow> 'trm" where
 "Num 0 = zer"
|"Num (Suc n) = suc (Num n)"

end \<comment> \<open>context @{locale Syntax_Arith_aux}\<close>


locale Syntax_Arith =
Syntax_Arith_aux
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  zer suc pls tms
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and eql cnj imp all exi
and fls
and dsj
and num
zer suc pls tms
+
assumes
\<comment> \<open>We assume that numbers are the only numerals:\<close>
num_Num: "num = range Num"
begin

lemma Num[simp,intro!]: "Num n \<in> num"
  using num_Num by auto

lemma FvarsT_Num[simp]: "FvarsT (Num n) = {}"
  by auto

lemma substT_Num[simp]: "x \<in> var \<Longrightarrow> t \<in> trm \<Longrightarrow> substT (Num n) t x = Num n"
  by auto

lemma zer[simp,intro!]: "zer \<in> num"
and suc_num[simp]: "\<And>n. n \<in> num \<Longrightarrow> suc n \<in> num"
by (metis Num Num.simps(1), metis Num Num.simps(2) imageE num_Num)


section \<open>Arithmetic Terms\<close>

text \<open>Arithmetic terms are inductively defined to contain the numerals and the variables
and be closed under the arithmetic operators:\<close>

inductive_set atrm :: "'trm set" where
 atrm_num[simp]: "n \<in> num \<Longrightarrow> n \<in> atrm"
|atrm_Var[simp,intro]: "x \<in> var \<Longrightarrow> Var x \<in> atrm"
|atrm_suc[simp,intro]: "t \<in> atrm \<Longrightarrow> suc t \<in> atrm"
|atrm_pls[simp,intro]: "t \<in> atrm \<Longrightarrow> t' \<in> atrm \<Longrightarrow> pls t t' \<in> atrm"
|atrm_tms[simp,intro]: "t \<in> atrm \<Longrightarrow> t' \<in> atrm \<Longrightarrow> tms t t' \<in> atrm"

lemma atrm_imp_trm[simp]: assumes "t \<in> atrm" shows "t \<in> trm"
using assms by induct auto

lemma atrm_trm: "atrm \<subseteq> trm"
using atrm_imp_trm by auto

lemma zer_atrm[simp]: "zer \<in> atrm" by auto

lemma Num_atrm[simp]: "Num n \<in> atrm"
by auto

lemma substT_atrm[simp]:
assumes "r \<in> atrm" and "x \<in> var" and "t \<in> atrm"
shows "substT r t x \<in> atrm"
using assms by (induct) auto

text \<open>Whereas we did not assume the rich set of formula-substitution properties to hold
for all terms, we can prove that these properties hold for arithmetic terms.\<close>

text \<open>Properties for arithmetic terms corresponding to the axioms for formulas:\<close>

lemma FvarsT_substT:
assumes "s \<in> atrm" "t \<in> trm" "x \<in> var"
shows "FvarsT (substT s t x) = (FvarsT s - {x}) \<union> (if x \<in> FvarsT s then FvarsT t else {})"
using assms by induct auto

lemma substT_compose_eq_or:
assumes "s \<in> atrm" "t1 \<in> trm" "t2 \<in> trm" "x1 \<in> var" "x2 \<in> var"
and "x1 = x2 \<or> x2 \<notin> FvarsT s"
shows "substT (substT s t1 x1) t2 x2 = substT s (substT t1 t2 x2) x1"
using assms apply induct
subgoal by auto
subgoal by auto
subgoal by (metis FvarsT_suc atrm_imp_trm substT substT_suc)
subgoal by (metis Fvars_pls UnCI atrm_imp_trm substT substT_pls)
subgoal by (metis Fvars_tms UnCI atrm_imp_trm substT substT_tms) .

lemma substT_compose_diff:
assumes "s \<in> atrm" "t1 \<in> trm" "t2 \<in> trm" "x1 \<in> var" "x2 \<in> var"
and "x1 \<noteq> x2" "x1 \<notin> FvarsT t2"
shows "substT (substT s t1 x1) t2 x2 = substT (substT s t2 x2) (substT t1 t2 x2) x1"
using assms apply induct
subgoal by auto
subgoal by auto
subgoal by (metis atrm_imp_trm substT substT_suc)
subgoal by (metis atrm_imp_trm substT substT_pls)
subgoal by (metis atrm_imp_trm substT substT_tms) .

lemma substT_same_Var[simp]:
assumes "s \<in> atrm" "x \<in> var"
shows "substT s (Var x) x = s"
using assms by induct auto

text \<open>... and corresponding to some corollaries we proved for formulas
(with essentially the same proofs):\<close>

lemma in_FvarsT_substTD:
"y \<in> FvarsT (substT r t x) \<Longrightarrow> r \<in> atrm \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var
   \<Longrightarrow> y \<in> (FvarsT r - {x}) \<union> (if x \<in> FvarsT r then FvarsT t else {})"
using FvarsT_substT by auto

lemma substT_compose_same:
"\<And> s t1 t2 x. s \<in> atrm \<Longrightarrow> t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  substT (substT s t1 x) t2 x = substT s (substT t1 t2 x) x"
  using substT_compose_eq_or by blast

lemma substT_substT[simp]:
assumes s[simp]: "s \<in> atrm" and t[simp]:"t \<in> trm" and x[simp]:"x \<in> var" and y[simp]:"y \<in> var"
assumes yy: "x \<noteq> y" "y \<notin> FvarsT s"
shows "substT (substT s (Var y) x) t y = substT s t x"
  using substT_compose_eq_or[OF s _ t x y, of "Var y"] using subst_notIn yy by simp

lemma substT_comp:
"\<And> x y s t. s \<in> atrm \<Longrightarrow> t \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow>
  x \<noteq> y \<Longrightarrow> y \<notin> FvarsT t \<Longrightarrow>
  substT (substT s (Var x) y) t x = substT (substT s t x) t y"
  by (simp add: substT_compose_diff)

text \<open>Now the corresponding development of parallel substitution for arithmetic terms:\<close>

lemma rawpsubstT_atrm[simp,intro]:
assumes "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
shows "rawpsubstT r txs \<in> atrm"
using assms by (induct txs arbitrary: r) auto

lemma psubstT_atrm[simp,intro]:
assumes "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
shows "psubstT r txs \<in> atrm"
proof-
  have txs_trm: "fst ` (set txs) \<subseteq> trm" using assms atrm_trm by auto
  define us where us: "us \<equiv> getFrN (map snd txs) (r # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT r = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms(1,2) txs_trm unfolding us
  using getFrN_FvarsT[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "r # map fst txs" "[]" "length txs"]
        getFrN_distinct[of "map snd txs" "r # map fst txs" "[]" "length txs"]
  apply -
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by force
    by auto
  (* *)
  show ?thesis using assms us_facts unfolding psubstT_def
    by (force simp: Let_def us[symmetric]
      intro!: rawpsubstT_atrm[of _ "zip (map fst txs) us"] dest!: set_zip_D)
qed

lemma Fvars_rawpsubst_su:
assumes "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
shows "FvarsT (rawpsubstT r txs) \<subseteq>
       (FvarsT r - snd ` (set txs)) \<union> (\<Union> {FvarsT t | t x . (t,x) \<in> set txs})"
using assms proof(induction txs arbitrary: r)
  case (Cons tx txs r)
  then obtain t x where tx: "tx = (t,x)" by force
  have t: "t \<in> trm" and x: "x \<in> var" using Cons.prems unfolding tx by auto
  define \<chi> where "\<chi> \<equiv> substT r t x"
  have 0: "FvarsT \<chi> =  FvarsT r - {x} \<union> (if x \<in> FvarsT r then FvarsT t else {})"
  using Cons.prems unfolding \<chi>_def by (auto simp: tx t FvarsT_substT)
  have \<chi>: "\<chi> \<in> trm" "\<chi> \<in> atrm" unfolding \<chi>_def using Cons.prems t x  by (auto simp add: tx)
  have "FvarsT (rawpsubstT \<chi> txs) \<subseteq>
       (FvarsT \<chi> - snd ` (set txs)) \<union>
       (\<Union> {FvarsT t | t x . (t,x) \<in> set txs})"
    using Cons.prems \<chi> by (intro Cons.IH) auto
  also have "\<dots> \<subseteq> FvarsT r - insert x (snd ` set txs) \<union> \<Union>{FvarsT ta |ta. \<exists>xa. ta = t \<and> xa = x \<or> (ta, xa) \<in> set txs}"
  (is "_ \<subseteq> ?R") by(auto simp: 0 tx Cons.prems)
  finally have 1: "FvarsT (rawpsubstT \<chi> txs) \<subseteq> ?R" .
  have 2: "FvarsT \<chi> = FvarsT r - {x} \<union> (if x \<in> FvarsT r then FvarsT t else {})"
    using Cons.prems t x unfolding \<chi>_def using FvarsT_substT by auto
  show ?case using 1 by (simp add: tx \<chi>_def[symmetric] 2)
qed auto

lemma in_FvarsT_rawpsubstT_imp:
  assumes "y \<in> FvarsT (rawpsubstT r txs)"
and "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
shows "(y \<in> FvarsT r - snd ` (set txs)) \<or>
     (y \<in> \<Union> { FvarsT t | t x . (t,x) \<in> set txs})"
using Fvars_rawpsubst_su[OF assms(2-4)]
using assms(1) by blast

lemma FvarsT_rawpsubstT:
assumes "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)" and "\<forall> x \<in> snd ` (set txs). \<forall> t \<in> fst ` (set txs). x \<notin> FvarsT t"
shows "FvarsT (rawpsubstT r txs) =
       (FvarsT r - snd ` (set txs)) \<union>
       (\<Union> {if x \<in> FvarsT r then FvarsT t else {} | t x . (t,x) \<in> set txs})"
using assms proof(induction txs arbitrary: r)
  case (Cons a txs r)
  then obtain t x where a: "a = (t,x)" by force
  have t: "t \<in> trm" and x: "x \<in> var" using Cons.prems unfolding a by auto
  have xt: "x \<notin> FvarsT t \<and> snd ` set txs \<inter> FvarsT t = {}" using Cons.prems unfolding a by auto
  hence 0: "FvarsT r - {x} \<union> FvarsT t - snd ` set txs = FvarsT r - insert x (snd ` set txs) \<union> FvarsT t"
  by auto
  have x_txs: "\<And>ta xa. (ta, xa) \<in> set txs \<Longrightarrow> x \<noteq> xa" using \<open>distinct (map snd (a # txs))\<close>
  unfolding a by (auto simp: rev_image_eqI)

  define \<chi> where \<chi>_def: "\<chi> \<equiv> substT r t x"
  have \<chi>: "\<chi> \<in> trm" "\<chi> \<in> atrm" unfolding \<chi>_def using Cons.prems t x  by (auto simp: a)
  have 1: "FvarsT (rawpsubstT \<chi> txs) =
       (FvarsT \<chi> - snd ` (set txs)) \<union>
       (\<Union> {if x \<in> FvarsT \<chi> then FvarsT t else {} | t x . (t,x) \<in> set txs})"
    using Cons.prems \<chi> by (intro Cons.IH) auto
  have 2: "FvarsT \<chi> = FvarsT r - {x} \<union> (if x \<in> FvarsT r then FvarsT t else {})"
    using Cons.prems t x unfolding \<chi>_def using FvarsT_substT by auto

  define f where "f \<equiv> \<lambda>ta xa. if xa \<in> FvarsT r then FvarsT ta else {}"

  have 3: "\<Union> {f ta xa  |ta xa. (ta, xa) \<in> set ((t, x) # txs)} =
        f t x \<union> (\<Union> {f ta xa  |ta xa. (ta, xa) \<in> set txs})" by auto
  have 4: "snd ` set ((t, x) # txs) = {x} \<union> snd ` set txs" by auto
  have 5: "f t x \<inter> snd ` set txs = {}" unfolding f_def using xt by auto
  have 6: "\<Union> {if xa \<in> FvarsT r - {x} \<union> f t x then FvarsT ta else {} | ta xa. (ta, xa) \<in> set txs}
     = (\<Union> {f ta xa | ta xa. (ta, xa) \<in> set txs})"
  unfolding f_def using xt x_txs by (fastforce split: if_splits)

  have "FvarsT r - {x} \<union> f t x  - snd ` set txs \<union>
    \<Union> {if xa \<in> FvarsT r - {x} \<union> f t x then FvarsT ta else {}
         | ta xa. (ta, xa) \<in> set txs} =
        FvarsT r - snd ` set ((t, x) # txs) \<union>
    \<Union> {f ta xa  |ta xa. (ta, xa) \<in> set ((t, x) # txs)}"
  unfolding 3 4 6 unfolding Un_Diff2[OF 5] Un_assoc unfolding Diff_Diff_Un ..

  thus ?case unfolding a rawpsubstT.simps 1 2 \<chi>_def[symmetric] f_def by simp
qed auto

lemma in_FvarsT_rawpsubstTD:
assumes "y \<in> FvarsT (rawpsubstT r txs)"
and "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)" and "\<forall> x \<in> snd ` (set txs). \<forall> t \<in> fst ` (set txs). x \<notin> FvarsT t"
shows "(y \<in> FvarsT r - snd ` (set txs)) \<or>
     (y \<in> \<Union> {if x \<in> FvarsT r then FvarsT t else {} | t x . (t,x) \<in> set txs})"
  using FvarsT_rawpsubstT assms by auto

lemma FvarsT_psubstT:
assumes "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)"
shows "FvarsT (psubstT r txs) =
       (FvarsT r - snd ` (set txs)) \<union>
       (\<Union> {if x \<in> FvarsT r then FvarsT t else {} | t x . (t,x) \<in> set txs})"
proof-
  have txs_trm: "fst ` (set txs) \<subseteq> trm" using assms by auto
  define us where us: "us \<equiv> getFrN (map snd txs) (r # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT r = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms(1,2) txs_trm unfolding us
  using getFrN_FvarsT[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "r # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "r # map fst txs" "[]" "length txs"]
  apply -
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by force
    by auto
  have [simp]: "\<And> aa b. b \<in> set (map snd txs) \<Longrightarrow>
     aa \<in> set (map Var us) \<Longrightarrow> b \<notin> FvarsT aa"
  using us_facts by (fastforce simp: image_def Int_def)
  have [simp]:
   "\<And>b ac bc. b \<in> set us \<Longrightarrow> b \<in> FvarsT ac \<Longrightarrow> (ac, bc) \<notin> set txs"
   using us_facts(3) by (fastforce simp: image_def Int_def)

  define \<chi> where \<chi>_def: "\<chi> \<equiv> rawpsubstT r (zip (map Var us) (map snd txs))"
  have \<chi>: "\<chi> \<in> atrm" unfolding \<chi>_def
  using assms using us_facts by (intro rawpsubstT_atrm) (force dest!: set_zip_D)+

  hence "\<chi> \<in> trm" by auto
  note \<chi> = \<chi> this
  have set_us: "set us = snd ` (set (zip (map fst txs) us))"
    using us_facts by (intro snd_set_zip[symmetric]) auto
  have set_txs: "snd ` set txs = snd ` (set (zip (map Var us) (map snd txs)))"
    using us_facts by (intro snd_set_zip_map_snd[symmetric]) auto
  have "\<And> t x. (t, x) \<in> set (zip (map Var us) (map snd txs)) \<Longrightarrow> \<exists> u. t = Var u"
    using us_facts set_zip_leftD by fastforce
  hence 00: "\<And> t x. (t, x) \<in> set (zip (map Var us) (map snd txs))
     \<longleftrightarrow>  (\<exists> u \<in> var. t = Var u \<and> (Var u, x) \<in> set (zip (map Var us) (map snd txs)))"
    using us_facts set_zip_leftD by fastforce
  have "FvarsT \<chi> =
        FvarsT r - snd ` set txs \<union>
        \<Union>{if x \<in> FvarsT r then FvarsT t else {} |t x.
             (t, x) \<in> set (zip (map Var us) (map snd txs))}"
    unfolding \<chi>_def set_txs using assms us_facts set_txs
    by (intro FvarsT_rawpsubstT) (force dest!: set_zip_D)+
  also have "\<dots> =
    FvarsT r - snd ` set txs \<union>
    \<Union>{if x \<in> FvarsT r then {u} else {} |u x. u \<in> var \<and> (Var u, x) \<in> set (zip (map Var us) (map snd txs))}"
  (is "\<dots> = ?R")
  apply(subst 00)
  by (metis (no_types, hide_lams) FvarsT_Var)
  finally have 0: "FvarsT \<chi> = ?R" .
  have 1: "FvarsT (rawpsubstT \<chi> (zip (map fst txs) us)) =
        (FvarsT \<chi> - set us) \<union>
        (\<Union> {if u \<in> FvarsT \<chi> then FvarsT t else {} | t u . (t,u) \<in> set (zip (map fst txs) us)})"
  unfolding us_facts set_us using assms \<chi> apply (intro FvarsT_rawpsubstT)
  subgoal by auto
  subgoal using us_facts by (auto dest!: set_zip_D)
  subgoal using us_facts by (auto dest!: set_zip_D)
  subgoal using us_facts by (auto dest!: set_zip_D)
  subgoal by (auto dest!: set_zip_D) .

  have 2: "FvarsT \<chi> - set us = FvarsT r - snd ` set txs"
  unfolding 0 apply auto
  using set_zip_leftD us_facts(1) apply fastforce
  using set_zip_leftD us_facts(1) apply fastforce
  using us_facts(2) by auto
  have 3:
  "(\<Union> {if u \<in> FvarsT \<chi> then FvarsT t else {} | t u . (t,u) \<in> set (zip (map fst txs) us)}) =
   (\<Union> {if x \<in> FvarsT r then FvarsT t else {} | t x . (t,x) \<in> set txs})"
  proof safe
    fix xx tt y
    assume xx: "xx \<in> (if y \<in> FvarsT \<chi> then FvarsT tt else {})"
    and ty: "(tt, y) \<in> set (zip (map fst txs) us)"
    have ttin: "tt \<in> fst ` set txs" using ty using set_zip_leftD by fastforce
    have yin: "y \<in> set us" using ty by (meson set_zip_D)
    have yvar: "y \<in> var" using us_facts yin by auto
    have ynotin: "y \<notin> snd ` set txs" "y \<notin> FvarsT r" using yin us_facts by auto
    show "xx \<in> \<Union>{if x \<in> FvarsT r then FvarsT t else {} |t x. (t, x) \<in> set txs}"
    proof(cases "y \<in> FvarsT \<chi>")
      case True note y = True
      hence xx: "xx \<in> FvarsT tt" using xx by simp
      obtain x where xr: "x \<in> FvarsT r"
      and yx: "(Var y, x) \<in> set (zip (map Var us) (map snd txs))"
        using y ynotin unfolding 0 by (auto split: if_splits)
      have yx: "(y, x) \<in> set (zip us (map snd txs))"
      using yvar us_facts by (intro inj_on_set_zip_map[OF inj_on_Var yx]) auto
      have "(tt, x) \<in> set txs" apply(rule set_zip_map_fst_snd[OF yx ty])
      using  \<open>distinct (map snd txs)\<close> us_facts by auto
      thus ?thesis using xx xr by auto
    qed(insert xx, auto)
  next
    fix y tt xx
    assume y: "y \<in> (if xx \<in> FvarsT r then FvarsT tt else {})"
    and tx: "(tt, xx) \<in> set txs"
    hence xxsnd: "xx \<in> snd ` set txs" by force
    obtain u where uin: "u \<in> set us" and uxx: "(u, xx) \<in> set (zip us (map snd txs))"
      by (metis xxsnd in_set_impl_in_set_zip2 length_map set_map set_zip_leftD us_facts(5))
    hence uvar: "u \<in> var" using us_facts by auto
    show "y \<in> \<Union>{if u \<in> FvarsT \<chi> then FvarsT t else {} |t u. (t, u) \<in> set (zip (map fst txs) us)}"
    proof(cases "xx \<in> FvarsT r")
      case True note xx = True
      hence y: "y \<in> FvarsT tt" using y by auto
      have "(Var u, xx) \<in> set (zip (map Var us) (map snd txs))"
      apply(rule set_zip_length_map[OF uxx]) using us_facts by auto
      hence u\<chi>: "u \<in> FvarsT \<chi>" using uin xx uvar unfolding 0 by auto
      have ttu: "(tt, u) \<in> set (zip (map fst txs) us)"
      apply(rule set_zip_map_fst_snd2[OF uxx tx]) using assms us_facts by auto
      show ?thesis using u\<chi> ttu y by auto
    qed(insert y, auto)
  qed
  show ?thesis
  by (simp add: psubstT_def Let_def us[symmetric] \<chi>_def[symmetric] 1 2 3)
qed


lemma in_FvarsT_psubstTD:
assumes "y \<in> FvarsT (psubstT r txs)"
and "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)"
shows "y \<in> (FvarsT r - snd ` (set txs)) \<union>
           (\<Union> {if x \<in> FvarsT r then FvarsT t else {} | t x . (t,x) \<in> set txs})"
using assms FvarsT_psubstT by auto

lemma substT2_fresh_switch:
  assumes "r \<in> atrm" "t \<in> trm" "s \<in> trm" "x \<in> var" "y \<in> var"
and "x \<noteq> y" "x \<notin> FvarsT s" "y \<notin> FvarsT t"
shows "substT (substT r s y) t x = substT (substT r t x) s y"   (is "?L = ?R")
  using assms by (simp add: substT_compose_diff[of r s t y x])

lemma rawpsubst2_fresh_switch:
  assumes "r \<in> atrm" "t \<in> trm" "s \<in> trm" "x \<in> var" "y \<in> var"
and "x \<noteq> y" "x \<notin> FvarsT s" "y \<notin> FvarsT t"
shows "rawpsubstT r ([(s,y),(t,x)]) = rawpsubstT r ([(t,x),(s,y)])"
  using assms by (simp add: substT2_fresh_switch)

(* this actually works for any trms, does not need atrms: *)
lemma rawpsubstT_compose:
  assumes "t \<in> trm" and "snd ` (set txs1) \<subseteq> var" and "fst ` (set txs1) \<subseteq> atrm"
and "snd ` (set txs2) \<subseteq> var" and "fst ` (set txs2) \<subseteq> atrm"
shows "rawpsubstT (rawpsubstT t txs1) txs2 = rawpsubstT t (txs1 @ txs2)"
  using assms apply (induct txs1 arbitrary: txs2 t)
  subgoal by simp
  subgoal for tx1 txs1 txs2 t apply (cases tx1) by auto .

lemma rawpsubstT_subst_fresh_switch:
assumes "r \<in> atrm" "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "\<forall> x \<in> snd ` (set txs). x \<notin> FvarsT s"
and "\<forall> t \<in> fst ` (set txs). y \<notin> FvarsT t"
and "distinct (map snd txs)"
and "s \<in> atrm" and "y \<in> var" "y \<notin> snd ` (set txs)"
shows "rawpsubstT (substT r s y) txs = rawpsubstT r (txs @ [(s,y)])"
using assms proof(induction txs arbitrary: r s y)
  case (Cons tx txs)
  obtain t x where tx[simp]: "tx = (t,x)" by force
  have x: "x \<in> var" and t: "t \<in> trm" using Cons unfolding tx by auto
  have "rawpsubstT r ((s, y) # (t, x) # txs) = rawpsubstT r ([(s, y),(t, x)] @ txs)" by simp
  also have "\<dots> = rawpsubstT (rawpsubstT r [(s, y),(t, x)]) txs"
    using Cons by auto
  also have "rawpsubstT r [(s, y),(t, x)] = rawpsubstT r [(t, x),(s, y)]"
    using Cons by (intro rawpsubst2_fresh_switch) auto
  also have "rawpsubstT (rawpsubstT r [(t, x),(s, y)]) txs = rawpsubstT r ([(t, x),(s, y)] @ txs)"
    using Cons by (intro rawpsubstT_compose) auto
  also have "\<dots> = rawpsubstT (substT r t x) (txs @ [(s,y)])" using Cons by auto
  also have "\<dots> = rawpsubstT r (((t, x) # txs) @ [(s, y)])" by simp
  finally show ?case unfolding tx by auto
qed auto

lemma substT_rawpsubstT_fresh_switch:
assumes "r \<in> atrm" "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "\<forall> x \<in> snd ` (set txs). x \<notin> FvarsT s"
and "\<forall> t \<in> fst ` (set txs). y \<notin> FvarsT t"
and "distinct (map snd txs)"
and "s \<in> atrm" and "y \<in> var" "y \<notin> snd ` (set txs)"
shows "substT (rawpsubstT r txs) s y = rawpsubstT r ((s,y) # txs)"
using assms proof(induction txs arbitrary: r s y)
  case (Cons tx txs)
  obtain t x where tx[simp]: "tx = (t,x)" by force
  have x: "x \<in> var" and t: "t \<in> trm" using Cons unfolding tx by auto
  have "substT (rawpsubstT (substT r t x) txs) s y = rawpsubstT (substT r t x) ((s,y) # txs)"
    using Cons.prems by (intro Cons.IH) auto
  also have "\<dots> = rawpsubstT (rawpsubstT r [(t,x)]) ((s,y) # txs)" by simp
  also have "\<dots> = rawpsubstT r ([(t,x)] @ ((s,y) # txs))"
    using Cons.prems by (intro rawpsubstT_compose) auto
  also have "\<dots> = rawpsubstT r ([(t,x),(s,y)] @ txs)" by simp
  also have "\<dots> = rawpsubstT (rawpsubstT r [(t,x),(s,y)]) txs"
    using Cons.prems by (intro rawpsubstT_compose[symmetric]) auto
  also have "rawpsubstT r [(t,x),(s,y)] = rawpsubstT r [(s,y),(t,x)]"
    using Cons.prems by (intro rawpsubst2_fresh_switch) auto
  also have "rawpsubstT (rawpsubstT r [(s,y),(t,x)]) txs = rawpsubstT r ([(s,y),(t,x)] @ txs)"
    using Cons.prems by (intro rawpsubstT_compose) auto
  finally show ?case by simp
qed auto

lemma rawpsubstT_compose_freshVar:
assumes "r \<in> atrm" "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)"
and "\<And> i j. i < j \<Longrightarrow> j < length txs \<Longrightarrow> snd (txs!j) \<notin> FvarsT (fst (txs!i))"
and us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT r = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
shows "rawpsubstT (rawpsubstT r (zip (map Var us) (map snd txs))) (zip (map fst txs) us) = rawpsubstT r txs"
using assms proof(induction txs arbitrary: us r)
  case (Cons tx txs uus r)
  obtain t x where tx[simp]: "tx = (t,x)" by force
  obtain u us where uus[simp]: "uus = u # us" using Cons by (cases uus) auto
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT r = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us" and u_facts: "u \<in> var" "u \<notin> FvarsT r"
  "u \<notin> \<Union> (FvarsT ` (fst ` (set txs)))"
  "u \<notin> snd ` (set txs)" "u \<notin> set us"
    using Cons by auto
  have [simp]: "\<And> bb xaa ab. bb \<in> FvarsT (Var xaa) \<Longrightarrow>
        (ab, bb) \<in> set txs \<Longrightarrow> xaa \<notin> set us"
  using us_facts(1,4) by force

  let ?uxs = "zip (map Var us) (map snd txs)"
  have 1: "rawpsubstT (substT r (Var u) x) ?uxs = rawpsubstT r (?uxs @ [(Var u,x)])"
  using Cons.prems u_facts apply(intro rawpsubstT_subst_fresh_switch)
  subgoal by auto
  subgoal by (auto dest!: set_zip_D)
  subgoal by (fastforce dest!: set_zip_D)
  subgoal by (auto dest!: set_zip_D)
  subgoal by (fastforce dest!: set_zip_D)
  by (auto dest!: set_zip_D)

  let ?uuxs = "zip (map Var uus) (map snd (tx # txs))"
  let ?tus = "zip (map fst txs) us"  let ?ttxs = "zip (map fst (tx # txs)) uus"
  have 2: "u \<in> FvarsT (rawpsubstT r (zip (map Var us) (map snd txs))) \<Longrightarrow> False"
  apply(drule in_FvarsT_rawpsubstTD) apply-
  subgoal using Cons.prems by auto
  subgoal using Cons.prems by (auto dest!: set_zip_D)
  subgoal using Cons.prems  by (force dest!: set_zip_D)
  subgoal using Cons.prems by (auto dest!: set_zip_D)
  subgoal by (auto dest!: set_zip_D)
  subgoal using us_facts(1,4,5) Cons.prems(7)
    by(fastforce dest!: set_zip_D split: if_splits simp: u_facts(5)) .

  have 3: "(tt, xx) \<notin> set txs" if "xx \<in> FvarsT t" for tt xx
    unfolding set_conv_nth mem_Collect_eq
  proof safe
    fix i
    assume "(tt, xx) = txs ! i" "i < length txs"
    then show False
      using that Cons.prems(4) Cons.prems(5)[of 0 "Suc i"] tx
      by (auto simp: nth_Cons' split: if_splits dest: sym)
  qed

  have 00: "rawpsubstT (rawpsubstT r ?uuxs) ?ttxs = rawpsubstT (substT (rawpsubstT r (?uxs @ [(Var u, x)])) t u) ?tus"
    by (simp add: 1)

  have "rawpsubstT r (?uxs @ [(Var u, x)]) = rawpsubstT (rawpsubstT r ?uxs) [(Var u, x)]"
    using Cons.prems
    by (intro rawpsubstT_compose[symmetric]) (auto 0 3 dest!: set_zip_D)
  also have "rawpsubstT (rawpsubstT r ?uxs) [(Var u, x)] = substT (rawpsubstT r ?uxs) (Var u) x" by simp
  finally have "substT (rawpsubstT r (?uxs @ [(Var u, x)])) t u =
                substT (substT (rawpsubstT r ?uxs) (Var u) x) t u" by simp
  also have "\<dots> = substT (rawpsubstT r ?uxs) t x"
    using Cons 2 by (intro substT_substT) (auto 0 3 intro!: rawpsubstT_atrm[of r] dest!: set_zip_D)
  also have "\<dots> = rawpsubstT r ((t,x) # ?uxs)"
    using Cons.prems 3
    by (intro substT_rawpsubstT_fresh_switch) (auto 0 3 dest!: set_zip_D FvarsT_VarD)
  also have "\<dots> =  rawpsubstT r ([(t,x)] @ ?uxs)" by simp
  also have "\<dots> = rawpsubstT (rawpsubstT r [(t,x)]) ?uxs"
    using Cons.prems by (intro rawpsubstT_compose[symmetric]) (auto 0 3 dest!: set_zip_D)
  finally have "rawpsubstT (substT (rawpsubstT r (?uxs @ [(Var u, x)])) t u) ?tus =
                rawpsubstT (rawpsubstT (rawpsubstT r [(t,x)]) ?uxs) ?tus" by auto
  hence "rawpsubstT (rawpsubstT r ?uuxs) ?ttxs = rawpsubstT (rawpsubstT (rawpsubstT r [(t,x)]) ?uxs) ?tus"
    using 00 by auto
  also have "\<dots> = rawpsubstT (rawpsubstT r [(t,x)]) txs"
  using Cons.prems apply(intro Cons.IH)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (metis Suc_leI le_imp_less_Suc length_Cons nth_Cons_Suc)
  subgoal by auto
  subgoal by (auto intro!: rawpsubstT dest!: set_zip_D in_FvarsT_substTD
             split: if_splits)
  by auto
  finally show ?case by simp
qed auto

lemma rawpsubstT_compose_freshVar2_aux:
assumes r[simp]: "r \<in> atrm"
and ts: "set ts \<subseteq> atrm"
and xs: "set xs \<subseteq> var"  "distinct xs"
and us_facts: "set us \<subseteq> var"  "distinct us"
  "set us \<inter> FvarsT r = {}"
  "set us \<inter> \<Union> (FvarsT ` (set ts)) = {}"
  "set us \<inter> set xs = {}"
and vs_facts: "set vs \<subseteq> var"  "distinct vs"
  "set vs \<inter> FvarsT r = {}"
  "set vs \<inter> \<Union> (FvarsT ` (set ts)) = {}"
  "set vs \<inter> set xs = {}"
and l: "length us = length xs" "length vs = length xs" "length ts = length xs"
and (* Extra hypothesis, only to get induction through: *) d: "set us \<inter> set vs = {}"
shows "rawpsubstT (rawpsubstT r (zip (map Var us) xs)) (zip ts us) =
       rawpsubstT (rawpsubstT r (zip (map Var vs) xs)) (zip ts vs)"
using assms proof(induction xs arbitrary: r ts us vs)
  case (Cons x xs r tts uus vvs)
  obtain t ts u us v vs where tts[simp]: "tts = t # ts" and lts[simp]: "length ts = length xs"
  and uus[simp]: "uus = u # us" and lus[simp]: "length us = length xs"
  and vvs[simp]: "vvs = v # vs" and lvs[simp]: "length vs = length xs"
  using \<open>length uus = length (x # xs)\<close> \<open>length vvs = length (x # xs)\<close> \<open>length tts = length (x # xs)\<close>
  apply(cases tts)
  subgoal by auto
  subgoal apply(cases uus)
    subgoal by auto
    subgoal by (cases vvs) auto . .

  let ?rux = "substT r (Var u) x"   let ?rvx = "substT r (Var v) x"

  have 0: "rawpsubstT (rawpsubstT ?rux (zip (map Var us) xs)) (zip ts us) =
           rawpsubstT (rawpsubstT ?rux (zip (map Var vs) xs)) (zip ts vs)"
  using Cons.prems by (intro Cons.IH) (auto intro!: rawpsubstT dest!: set_zip_D simp: FvarsT_substT)

  have 1: "rawpsubstT ?rux (zip (map Var vs) xs) =
           substT (rawpsubstT r (zip (map Var vs) xs)) (Var u) x"
  using Cons.prems
  by (intro substT_rawpsubstT_fresh_switch[simplified,symmetric])
     (auto intro!: rawpsubstT dest!: set_zip_D simp: subset_eq)

  have 11: "rawpsubstT ?rvx (zip (map Var vs) xs) =
           substT (rawpsubstT r (zip (map Var vs) xs)) (Var v) x"
  using Cons.prems
  by (intro substT_rawpsubstT_fresh_switch[simplified,symmetric])
     (auto intro!: rawpsubstT dest!: set_zip_D simp: subset_eq)

  have "substT (substT (rawpsubstT r (zip (map Var vs) xs)) (Var u) x) t u =
        substT (rawpsubstT r (zip (map Var vs) xs)) t x"
  using Cons.prems
  by (intro substT_substT)
     (auto 0 3 intro!: rawpsubstT_atrm[of r]
           dest!: set_zip_D in_FvarsT_rawpsubstT_imp FvarsT_VarD simp: FvarsT_rawpsubstT)
  also have "\<dots> = substT (substT (rawpsubstT r (zip (map Var vs) xs)) (Var v) x) t v"
  using Cons.prems
  by (intro substT_substT[symmetric])
     (auto 0 3 intro!: rawpsubstT_atrm[of r] dest!: set_zip_D in_FvarsT_rawpsubstT_imp FvarsT_VarD
           simp: FvarsT_rawpsubstT)
  finally have
  2: "substT (substT (rawpsubstT r (zip (map Var vs) xs)) (Var u) x) t u =
      substT (substT (rawpsubstT r (zip (map Var vs) xs)) (Var v) x) t v"  .

  have "rawpsubstT (substT (rawpsubstT ?rux (zip (map Var us) xs)) t u) (zip ts us) =
        substT (rawpsubstT (rawpsubstT ?rux (zip (map Var us) xs)) (zip ts us)) t u"
  using Cons.prems
  by (intro substT_rawpsubstT_fresh_switch[simplified,symmetric])
     (auto 0 3 intro!: rawpsubstT_atrm[of ?rux] substT_atrm dest!: set_zip_D)
  also have "\<dots> = substT (rawpsubstT (rawpsubstT ?rux (zip (map Var vs) xs)) (zip ts vs)) t u"
    unfolding 0 ..
  also have "\<dots> = rawpsubstT (substT (rawpsubstT ?rux (zip (map Var vs) xs)) t u) (zip ts vs)"
  using Cons.prems
  by (intro substT_rawpsubstT_fresh_switch[simplified])
     (auto 0 3 intro!: rawpsubstT_atrm[of ?rux] dest!: set_zip_D)
  also have "\<dots> = rawpsubstT (substT (substT (rawpsubstT r (zip (map Var vs) xs)) (Var u) x) t u) (zip ts vs)"
   unfolding 1 ..
  also have "\<dots> = rawpsubstT (substT (substT (rawpsubstT r (zip (map Var vs) xs)) (Var v) x) t v) (zip ts vs)"
   unfolding 2 ..
  also have "\<dots> = rawpsubstT (substT (rawpsubstT ?rvx (zip (map Var vs) xs)) t v) (zip ts vs)"
    unfolding 11 ..
  finally have "rawpsubstT (substT (rawpsubstT ?rux (zip (map Var us) xs)) t u) (zip ts us) =
        rawpsubstT (substT (rawpsubstT ?rvx (zip (map Var vs) xs)) t v) (zip ts vs)" .
  thus ?case by simp
qed auto

(* ... now getting rid of the disjointness hypothesis: *)
lemma rawpsubstT_compose_freshVar2:
assumes r[simp]: "r \<in> atrm"
and ts: "set ts \<subseteq> atrm"
and xs: "set xs \<subseteq> var"  "distinct xs"
and us_facts: "set us \<subseteq> var"  "distinct us"
  "set us \<inter> FvarsT r = {}"
  "set us \<inter> \<Union> (FvarsT ` (set ts)) = {}"
  "set us \<inter> set xs = {}"
and vs_facts: "set vs \<subseteq> var"  "distinct vs"
  "set vs \<inter> FvarsT r = {}"
  "set vs \<inter> \<Union> (FvarsT ` (set ts)) = {}"
  "set vs \<inter> set xs = {}"
and l: "length us = length xs" "length vs = length xs" "length ts = length xs"
shows "rawpsubstT (rawpsubstT r (zip (map Var us) xs)) (zip ts us) =
       rawpsubstT (rawpsubstT r (zip (map Var vs) xs)) (zip ts vs)"  (is "?L = ?R")
proof-
  have ts_trm: "set ts \<subseteq> trm" using ts by auto
  define ws where "ws = getFrN (xs @ us @ vs) (r # ts) [] (length xs)"
  have ws_facts: "set ws \<subseteq> var"  "distinct ws"
  "set ws \<inter> FvarsT r = {}"
  "set ws \<inter> \<Union> (FvarsT ` (set ts)) = {}"
  "set ws \<inter> set xs = {}" "set ws \<inter> set us = {}" "set ws \<inter> set vs = {}"
  "length ws = length xs" using assms(1) ts_trm assms(3-17) unfolding ws_def
   using getFrN_Fvars[of "xs @ us @ vs" "r # ts" "[]" _ "length xs"]
        getFrN_FvarsT[of "xs @ us @ vs" "r # ts" "[]" _ "length xs"]
        getFrN_var[of "xs @ us @ vs" "r # ts" "[]" _ "length xs"]
        getFrN_length[of "xs @ us @ vs" "r # ts" "[]" "length xs"]
  apply -
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by force
  by auto
  have "?L = rawpsubstT (rawpsubstT r (zip (map Var ws) xs)) (zip ts ws)"
  using assms ws_facts by (intro rawpsubstT_compose_freshVar2_aux) auto
  also have "\<dots> = ?R"
  using assms ws_facts by (intro rawpsubstT_compose_freshVar2_aux) auto
  finally show ?thesis .
qed

lemma in_fst_image: "a \<in> fst ` AB \<longleftrightarrow> (\<exists>b. (a,b) \<in> AB)" by force

(* For many cases, the simpler rawpsubstT can replace psubst: *)
lemma psubstT_eq_rawpsubstT:
assumes "r \<in> atrm" "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)"
(* ... namely, when the substituted variables do not belong to trms substituted for previous variables: *)
and "\<And> i j. i < j \<Longrightarrow> j < length txs \<Longrightarrow> snd (txs!j) \<notin> FvarsT (fst (txs!i))"
shows "psubstT r txs = rawpsubstT r txs"
proof-
  have txs_trm: "r \<in> trm" "fst ` (set txs) \<subseteq> trm" using assms by auto

  note frt = getFrN_FvarsT[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
  and fr = getFrN_Fvars[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
  and var =  getFrN_var[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
  and l = getFrN_length[of "map snd txs" "r # map fst txs" "[]" "length txs"]
  define us where us: "us \<equiv> getFrN (map snd txs) (r # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT r = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms(2,4,5) txs_trm unfolding us

  apply -
  subgoal by auto
  subgoal using frt by auto
  subgoal using frt by (simp add: in_fst_image Int_def) (metis prod.collapse)
  subgoal using var by (simp add: in_fst_image Int_def) (metis)
  subgoal using l by auto
  subgoal by auto .

  show ?thesis
    using rawpsubstT_compose_freshVar assms us_facts
    by (simp add: psubstT_def Let_def us[symmetric])
qed

(* Some particular cases: *)
lemma psubstT_eq_substT:
assumes "r \<in> atrm" "x \<in> var" and "t \<in> atrm"
shows "psubstT r [(t,x)] = substT r t x"
proof-
  have "psubstT r [(t,x)] = rawpsubstT r [(t,x)]"
    using assms by (intro psubstT_eq_rawpsubstT) auto
  thus ?thesis by auto
qed

lemma psubstT_eq_rawpsubst2:
assumes "r \<in> atrm" "x1 \<in> var" "x2 \<in> var" "t1 \<in> atrm" "t2 \<in> atrm"
and "x1 \<noteq> x2" "x2 \<notin> FvarsT t1"
shows "psubstT r [(t1,x1),(t2,x2)] = rawpsubstT r [(t1,x1),(t2,x2)]"
  using assms using less_SucE by (intro psubstT_eq_rawpsubstT) force+

lemma psubstT_eq_rawpsubst3:
assumes "r \<in> atrm" "x1 \<in> var" "x2 \<in> var" "x3 \<in> var" "t1 \<in> atrm" "t2 \<in> atrm" "t3 \<in> atrm"
and "x1 \<noteq> x2" "x1 \<noteq> x3" "x2 \<noteq> x3"
"x2 \<notin> FvarsT t1" "x3 \<notin> FvarsT t1" "x3 \<notin> FvarsT t2"
shows "psubstT r [(t1,x1),(t2,x2),(t3,x3)] = rawpsubstT r [(t1,x1),(t2,x2),(t3,x3)]"
using assms less_SucE less_Suc_eq_0_disj
by (intro psubstT_eq_rawpsubstT) auto

lemma psubstT_eq_rawpsubst4:
assumes "r \<in> atrm" "x1 \<in> var" "x2 \<in> var" "x3 \<in> var" "x4 \<in> var"
"t1 \<in> atrm" "t2 \<in> atrm" "t3 \<in> atrm" "t4 \<in> atrm"
and "x1 \<noteq> x2" "x1 \<noteq> x3" "x2 \<noteq> x3" "x1 \<noteq> x4" "x2 \<noteq> x4" "x3 \<noteq> x4"
"x2 \<notin> FvarsT t1" "x3 \<notin> FvarsT t1" "x3 \<notin> FvarsT t2" "x4 \<notin> FvarsT t1" "x4 \<notin> FvarsT t2" "x4 \<notin> FvarsT t3"
shows "psubstT r [(t1,x1),(t2,x2),(t3,x3),(t4,x4)] = rawpsubstT r [(t1,x1),(t2,x2),(t3,x3),(t4,x4)]"
using assms less_SucE less_Suc_eq_0_disj
by (intro psubstT_eq_rawpsubstT) auto

lemma rawpsubstT_same_Var[simp]:
assumes "r \<in> atrm" "set xs \<subseteq> var"
shows "rawpsubstT r (map (\<lambda>x. (Var x,x)) xs) = r"
using assms by (induct xs) auto

lemma psubstT_same_Var[simp]:
assumes "r \<in> atrm" "set xs \<subseteq> var" and "distinct xs"
shows "psubstT r (map (\<lambda>x. (Var x,x)) xs) = r"
proof-
  have "psubstT r (map (\<lambda>x. (Var x,x)) xs) = rawpsubstT r (map (\<lambda>x. (Var x,x)) xs)"
    using assms FvarsT_Var[of "xs ! _"] nth_mem[of _ xs]
    by (intro psubstT_eq_rawpsubstT)
       (auto simp: o_def distinct_conv_nth dest!: FvarsT_VarD)
  thus ?thesis using assms by auto
qed

(* The following holds for all trms, so no need to prove it for a trms: *)
thm psubstT_notIn

(***)

(* Behavior of psubst w.r.t. equality formulas: *)

lemma rawpsubst_eql:
assumes "t1 \<in> trm" "t2 \<in> trm"
and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
shows "rawpsubst (eql t1 t2) txs = eql (rawpsubstT t1 txs) (rawpsubstT t2 txs)"
using assms apply (induct txs arbitrary: t1 t2)
  subgoal by auto
  subgoal for tx txs t1 t2 by (cases tx) auto .

lemma psubst_eql[simp]:
assumes "t1 \<in> atrm" "t2 \<in> atrm"
and "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)"
shows "psubst (eql t1 t2) txs = eql (psubstT t1 txs) (psubstT t2 txs)"
proof-
  have t12: "fst ` (set txs) \<subseteq> trm"  using assms by auto
  define us where us: "us \<equiv> getFrN (map snd txs) (map fst txs) [eql t1 t2] (length txs)"
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT t1 = {}"
  "set us \<inter> FvarsT t2 = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms(1-3) t12 unfolding us
  using getFrN_Fvars[of "map snd txs" "map fst txs" "[eql t1 t2]" _ "length txs"]
        getFrN_FvarsT[of "map snd txs" "map fst txs" "[eql t1 t2]" _ "length txs"]
        getFrN_var[of "map snd txs" "map fst txs" "[eql t1 t2]" _ "length txs"]
        getFrN_length[of "map snd txs" "map fst txs" "[eql t1 t2]" "length txs"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by force
  subgoal by fastforce
  subgoal by (fastforce simp: image_iff)
  by auto

  define vs1 where vs1: "vs1 \<equiv> getFrN (map snd txs) (t1 # map fst txs) [] (length txs)"
  have vs1_facts: "set vs1  \<subseteq> var"
  "set vs1 \<inter> FvarsT t1 = {}"
  "set vs1 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set vs1 \<inter> snd ` (set txs) = {}"
  "length vs1 = length txs"
  "distinct vs1"
  using assms(1-3) t12 unfolding vs1
  using getFrN_Fvars[of "map snd txs" "t1 # map fst txs" "[]" _ "length txs"]
        getFrN_FvarsT[of "map snd txs" "t1 # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "t1 # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "t1 # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by auto
  subgoal by force
  subgoal by (fastforce simp: image_iff)
  by auto

  define vs2 where vs2: "vs2 \<equiv> getFrN (map snd txs) (t2 # map fst txs) [] (length txs)"
  have vs2_facts: "set vs2  \<subseteq> var"
  "set vs2 \<inter> FvarsT t2 = {}"
  "set vs2 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set vs2 \<inter> snd ` (set txs) = {}"
  "length vs2 = length txs"
  "distinct vs2"
  using assms(1-3) t12 unfolding vs2
  using getFrN_Fvars[of "map snd txs" "t2 # map fst txs" "[]" _ "length txs"]
        getFrN_FvarsT[of "map snd txs" "t2 # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "t2 # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "t2 # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by auto
  subgoal by force
  subgoal by (fastforce simp: image_iff)
  by auto

  let ?tus = "zip (map fst txs) us"
  let ?uxs = "zip (map Var us) (map snd txs)"
  let ?e = "rawpsubst (eql t1 t2) ?uxs"
  have e: "?e = eql (rawpsubstT t1 ?uxs) (rawpsubstT t2 ?uxs)"
  apply(rule rawpsubst_eql) using assms us_facts apply auto
   apply(drule set_zip_rightD) apply simp apply blast
   apply(drule set_zip_leftD) apply simp apply blast .
  have 0: "rawpsubst ?e ?tus =
     eql (rawpsubstT (rawpsubstT t1 ?uxs) ?tus) (rawpsubstT (rawpsubstT t2 ?uxs) ?tus)"
  unfolding e using assms us_facts apply(intro rawpsubst_eql)
  subgoal by (auto intro!: rawpsubstT dest!: set_zip_D)
  subgoal by (auto intro!: rawpsubstT dest!: set_zip_D)
  subgoal by (auto intro!: rawpsubstT dest!: set_zip_D)
  subgoal by (fastforce intro!: rawpsubstT dest!: set_zip_D) .
  have 1: "rawpsubstT (rawpsubstT t1 ?uxs) ?tus =
          rawpsubstT (rawpsubstT t1 (zip (map Var vs1) (map snd txs))) (zip (map fst txs) vs1)"
    using assms us_facts vs1_facts
    by (intro rawpsubstT_compose_freshVar2) auto
  have 2: "rawpsubstT (rawpsubstT t2 ?uxs) ?tus =
         rawpsubstT (rawpsubstT t2 (zip (map Var vs2) (map snd txs))) (zip (map fst txs) vs2)"
    using assms us_facts vs2_facts
    by (intro rawpsubstT_compose_freshVar2) auto
  show ?thesis unfolding psubstT_def psubst_def
    by (simp add: Let_def us[symmetric] vs1[symmetric] vs2[symmetric] 0 1 2)
qed

(* psubst versus the exists-unique quantifier: *)

lemma psubst_exu[simp]:
assumes "\<phi> \<in> fmla" "x \<in> var" "snd ` set txs \<subseteq> var" "fst ` set txs \<subseteq> atrm"
"x \<notin> snd ` set txs" "x \<notin> (\<Union>t \<in> fst ` set txs. FvarsT t)" "distinct (map snd txs)"
shows "psubst (exu x \<phi>) txs = exu x (psubst \<phi> txs)"
proof-
  have f: "fst ` set txs \<subseteq> trm" using assms by (meson atrm_trm subset_trans)
  note assms1 = assms(1-3) assms(5-7) f
  define u where u: "u \<equiv> getFr (x # map snd txs) (map fst txs) [\<phi>]"
  have u_facts:  "u \<in> var" "u \<noteq> x"
  "u \<notin> snd ` set txs" "u \<notin> (\<Union>t \<in> fst ` set txs. FvarsT t)" "u \<notin> Fvars \<phi>"
  unfolding u using f getFr_FvarsT_Fvars[of "x # map snd txs" "map fst txs" "[\<phi>]"] by (auto simp: assms)
  hence [simp]: "psubst (subst \<phi> (Var u) x) txs = subst (psubst \<phi> txs) (Var u) x"
  using assms apply(intro psubst_subst_fresh_switch f) by auto
  show ?thesis using f assms u_facts
  by (subst exu_def_var[of _ u "psubst \<phi> txs"])
     (auto dest!: in_Fvars_psubstD split: if_splits simp: exu_def_var[of _ u] )
qed

(* psubst versus the arithmetic trm constructors: *)

(* We already have: *)
thm psubstT_Var_not[no_vars]

lemma rawpsubstT_Var_in:
assumes "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
and "distinct (map snd txs)" and "(s,y) \<in> set txs"
and "\<And> i j. i < j \<Longrightarrow> j < length txs \<Longrightarrow> snd (txs!j) \<notin> FvarsT (fst (txs!i))"
shows "rawpsubstT (Var y) txs = s"
using assms proof(induction txs)
  case (Cons tx txs)
  obtain t x where tx[simp]: "tx = (t,x)" by (cases tx) auto

  have 00: "FvarsT t \<inter> snd ` set txs = {}"
  using Cons.prems(5)[of 0 "Suc _"] by (auto simp: set_conv_nth)

  have "rawpsubstT (substT (Var y) t x) txs = s"
  proof(cases "y = x")
    case [simp]:True hence [simp]: "s = t" using \<open>distinct (map snd (tx # txs))\<close>
    \<open>(s, y) \<in> set (tx # txs)\<close> using image_iff by fastforce
    show ?thesis using Cons.prems 00 by auto
  next
    case False
    hence [simp]: "substT (Var y) t x = Var y"
    using Cons.prems by (intro substT_notIn) auto
    have "rawpsubstT (Var y) txs = s"
    using Cons.prems apply(intro Cons.IH)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using False by auto
    subgoal by (metis length_Cons less_Suc_eq_0_disj nth_Cons_Suc) .
    thus ?thesis by simp
  qed
  thus ?case by simp
qed auto

lemma psubstT_Var_in:
assumes "y \<in> var" "snd ` (set txs) \<subseteq> var" "fst ` (set txs) \<subseteq> trm"
and "distinct (map snd txs)" and "(s,y) \<in> set txs"
shows "psubstT (Var y) txs = s"
proof-
  define us where us: "us \<equiv> getFrN (map snd txs) (Var y # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "y \<notin> set us"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms unfolding us
  using getFrN_FvarsT[of "map snd txs" "Var y # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "Var y # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "Var y # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by auto
  subgoal by force
  subgoal by force
  by auto
  obtain i where i[simp]: "i < length txs" "txs!i = (s,y)" using \<open>(s,y) \<in> set txs\<close>
    by (metis in_set_conv_nth)
  hence 00[simp]: "\<And> j. j < length txs \<Longrightarrow> txs ! j = txs ! i \<Longrightarrow> j = i"
   using \<open>distinct (map snd txs)\<close> distinct_Ex1 nth_mem by fastforce
  have 000[simp]: "\<And> j ia. j < length txs \<Longrightarrow> ia < length txs \<Longrightarrow> snd (txs ! j) \<noteq> us ! ia"
   using assms us_facts
   by (metis IntI empty_iff length_map list.set_map nth_map nth_mem)
  have [simp]: "\<And>ii jj. ii < jj \<Longrightarrow> jj < length txs \<Longrightarrow> us ! ii \<in> var"
    using nth_mem us_facts(1) us_facts(5) by auto
  have [simp]: "\<And>i j. i < j \<Longrightarrow> j < length txs \<Longrightarrow> us ! j \<notin> FvarsT (fst (txs ! i))"
    using us_facts(2,5) by (auto simp: Int_def)

  have 0: "rawpsubstT (Var y) (zip (map Var us) (map snd txs)) = Var (us!i)"
  using assms us_facts
  by (intro rawpsubstT_Var_in)
     (auto dest!: set_zip_D simp: in_set_conv_nth intro!: exI[of _ i])

  have "rawpsubstT (rawpsubstT (Var y) (zip (map Var us) (map snd txs))) (zip (map fst txs) us) = s"
  unfolding 0 using assms us_facts
  by (intro rawpsubstT_Var_in)
     (auto dest!: set_zip_D simp: in_set_conv_nth intro!: exI[of _ i])
  thus ?thesis unfolding psubstT_def by (simp add: Let_def us[symmetric])
qed

lemma psubstT_Var_Cons_aux:
assumes "y \<in> var" "x \<in> var" "t \<in> atrm"
"snd ` set txs \<subseteq> var" "fst ` set txs \<subseteq> atrm" "x \<notin> snd ` set txs"
"distinct (map snd txs)"  "y \<noteq> x"
shows "psubstT (Var y) ((t, x) # txs) = psubstT (Var y) txs"
proof-
  have txs_trm: "t \<in> trm" "fst ` set txs \<subseteq> trm" using assms by auto
  note assms1 = assms(1,2) assms(4) assms(6-8) txs_trm

  note fvt = getFrN_FvarsT[of "x # map snd txs" "Var y # t # map fst txs" "[]" _ "Suc (length txs)"]
  and var = getFrN_var[of "x # map snd txs" "Var y # t # map fst txs" "[]" _ "Suc (length txs)"]
  and l = getFrN_length[of "x # map snd txs" "Var y # t # map fst txs" "[]" "Suc (length txs)"]
  define uus where uus:
  "uus \<equiv> getFrN (x # map snd txs) (Var y # t # map fst txs) [] (Suc (length txs))"
  have uus_facts: "set uus \<subseteq> var"
  "set uus \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set uus \<inter> snd ` (set txs) = {}"
  "set uus \<inter> FvarsT t = {}"
  "x \<notin> set uus"
  "y \<notin> set uus"
  "length uus = Suc (length txs)"
  "distinct uus"
  using assms1 unfolding uus
  apply -
  subgoal by auto
  subgoal using fvt by (simp add: in_fst_image Int_def) (metis prod.collapse)
  subgoal using var by (force simp add: in_fst_image Int_def)
  subgoal using fvt by auto
  subgoal using var by (fastforce simp: in_fst_image Int_def)
  subgoal using fvt by (force simp: in_fst_image Int_def)
  subgoal using l by auto
  subgoal by auto .

  obtain u us where uus_us[simp]: "uus = u # us" using uus_facts by (cases uus) auto

  have us_facts: "set us \<subseteq> var"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "set us \<inter> FvarsT t = {}"
  "x \<notin> set us"
  "y \<notin> set us"
  "length us = length txs"
  "distinct us"
  and u_facts: "u \<in> var"
  "u \<notin> \<Union> (FvarsT ` (fst ` (set txs)))"
  "u \<notin> snd ` (set txs)"
  "u \<notin>FvarsT t"
  "u \<noteq> x"
  "u \<noteq> y"
  "u \<notin> set us"
  using uus_facts by auto

  note fvt = getFrN_FvarsT[of "map snd txs" "Var y # map fst txs" "[]" _ "length txs"]
  and var = getFrN_var[of "map snd txs" "Var y # map fst txs" "[]" _ "length txs"]
  and l = getFrN_length[of "map snd txs" "Var y # map fst txs" "[]" "length txs"]
  define vs where vs: "vs \<equiv> getFrN (map snd txs) (Var y #  map fst txs) [] (length txs)"
  have vs_facts: "set vs \<subseteq> var"
  "set vs \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "y \<notin> set vs"
  "set vs \<inter> snd ` (set txs) = {}"
  "length vs = length txs"
  "distinct vs"
  using assms1 unfolding vs
  apply -
  subgoal by auto
  subgoal using fvt by (simp add: in_fst_image Int_def) (metis prod.collapse)
  subgoal using fvt l by fastforce
  subgoal using var by (force simp: Int_def in_fst_image)
  subgoal using l by auto
  subgoal by auto .

  have 0: "substT (Var y) (Var u) x = Var y"
    using assms u_facts by auto
  have 1: "substT (rawpsubstT (Var y) (zip (map Var us) (map snd txs))) t u =
           rawpsubstT (Var y) (zip (map Var us) (map snd txs))"
  using assms u_facts us_facts
  by (intro substT_notIn)
     (auto 0 3 intro!: rawpsubstT dest!: set_zip_D in_FvarsT_rawpsubstT_imp FvarsT_VarD)

  have "rawpsubstT (rawpsubstT (Var y) (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
    rawpsubstT (rawpsubstT (Var y) (zip (map Var vs) (map snd txs))) (zip (map fst txs) vs)"
  using assms vs_facts us_facts by (intro rawpsubstT_compose_freshVar2) auto
  thus ?thesis unfolding psubstT_def
  by (simp add: Let_def uus[symmetric] vs[symmetric] 0 1)
qed

text \<open>Simplification rules for parallel substitution:\<close>

lemma psubstT_Var_Cons[simp]:
"y \<in> var \<Longrightarrow> x \<in> var \<Longrightarrow> t \<in> atrm \<Longrightarrow>
 snd ` set txs \<subseteq> var \<Longrightarrow> fst ` set txs \<subseteq> atrm \<Longrightarrow> distinct (map snd txs) \<Longrightarrow> x \<notin> snd ` set txs \<Longrightarrow>
 psubstT (Var y) ((t,x) # txs) = (if y = x then t else psubstT (Var y) txs)"
apply(cases "y = x")
subgoal by (rule psubstT_Var_in) auto
subgoal by (auto intro!: psubstT_Var_Cons_aux) .

lemma psubstT_zer[simp]:
assumes "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
shows "psubstT zer txs = zer"
using assms by (intro psubstT_num) auto

lemma rawpsubstT_suc:
assumes "r \<in> trm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
shows "rawpsubstT (suc r) txs = suc (rawpsubstT r txs)"
using assms apply(induct txs arbitrary: r)
subgoal by simp
subgoal for tx txs r by (cases tx) auto .

lemma psubstT_suc[simp]:
assumes "r \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)"
shows "psubstT (suc r) txs = suc (psubstT r txs)"
proof-
  have 000: "r \<in> trm" "fst ` (set txs) \<subseteq> trm" using assms by auto
  define us where us: "us \<equiv> getFrN (map snd txs) (suc r # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT r = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms(2) 000 unfolding us
  using getFrN_FvarsT[of "map snd txs" "suc r # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "suc r # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "suc r # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "suc r # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "suc r # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by auto
  subgoal by force
  by auto
  define vs where vs: "vs \<equiv> getFrN (map snd txs) (r # map fst txs) [] (length txs)"
  have vs_facts: "set vs \<subseteq> var"
  "set vs \<inter> FvarsT r = {}"
  "set vs \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set vs \<inter> snd ` (set txs) = {}"
  "length vs = length txs"
  "distinct vs"
  using assms(2) 000 unfolding vs
  using getFrN_FvarsT[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "r # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "r # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "r # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by force
  by auto
  have 0: "rawpsubstT (suc r) (zip (map Var vs) (map snd txs)) =
           suc (rawpsubstT r (zip (map Var vs) (map snd txs)))"
  using assms vs_facts by (intro rawpsubstT_suc) (auto dest!: set_zip_D)

  have "rawpsubstT (rawpsubstT (suc r) (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
        rawpsubstT (rawpsubstT (suc r) (zip (map Var vs) (map snd txs))) (zip (map fst txs) vs)"
  using assms us_facts vs_facts by (intro rawpsubstT_compose_freshVar2) auto
  also have "\<dots> = suc (rawpsubstT (rawpsubstT r (zip (map Var vs) (map snd txs))) (zip (map fst txs) vs))"
  unfolding 0 using assms vs_facts apply(intro rawpsubstT_suc)
  subgoal by (auto dest!: set_zip_D intro!: rawpsubstT)
  subgoal by (auto dest!: set_zip_D)
  subgoal by (fastforce dest!: set_zip_D simp: Int_def) .
  finally show ?thesis
  by (simp add: Let_def us[symmetric] vs[symmetric] psubstT_def)
qed

lemma rawpsubstT_pls:
assumes "r1 \<in> trm" "r2 \<in> trm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
shows "rawpsubstT (pls r1 r2) txs = pls (rawpsubstT r1 txs) (rawpsubstT r2 txs)"
using assms apply(induct txs arbitrary: r1 r2)
subgoal by simp
subgoal for tx txs r by (cases tx) auto .

lemma psubstT_pls[simp]:
assumes "r1 \<in> atrm" "r2 \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)"
shows "psubstT (pls r1 r2) txs = pls (psubstT r1 txs) (psubstT r2 txs)"
proof-
  have 000: "fst ` (set txs) \<subseteq> trm" using assms by auto
  define us where us: "us \<equiv> getFrN (map snd txs) (pls r1 r2 # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT r1 = {}"
  "set us \<inter> FvarsT r2 = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms(1-3) 000 unfolding us
  using getFrN_FvarsT[of "map snd txs" "pls r1 r2 # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "pls r1 r2 # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "pls r1 r2 # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "pls r1 r2 # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "pls r1 r2 # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by force
  subgoal by auto
  subgoal by force
  by auto
  define vs1 where vs1: "vs1 \<equiv> getFrN (map snd txs) (r1 # map fst txs) [] (length txs)"
  have vs1_facts: "set vs1 \<subseteq> var"
  "set vs1 \<inter> FvarsT r1 = {}"
  "set vs1 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set vs1 \<inter> snd ` (set txs) = {}"
  "length vs1 = length txs"
  "distinct vs1"
  using assms(1-3) 000 unfolding vs1
  using getFrN_FvarsT[of "map snd txs" "r1 # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "r1 # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "r1 # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "r1 # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "r1 # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by force
  by auto
  define vs2 where vs2: "vs2 \<equiv> getFrN (map snd txs) (r2 # map fst txs) [] (length txs)"
  have vs2_facts: "set vs2 \<subseteq> var"
  "set vs2 \<inter> FvarsT r2 = {}"
  "set vs2 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set vs2 \<inter> snd ` (set txs) = {}"
  "length vs2 = length txs"
  "distinct vs2"
  using assms(1-3) 000 unfolding vs2
  using getFrN_FvarsT[of "map snd txs" "r2 # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "r2 # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "r2 # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "r2 # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "r2 # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by force
  by auto
  have 0: "rawpsubstT (pls r1 r2) (zip (map Var us) (map snd txs)) =
           pls (rawpsubstT r1 (zip (map Var us) (map snd txs)))
               (rawpsubstT r2 (zip (map Var us) (map snd txs)))"
  using assms us_facts by (intro rawpsubstT_pls) (auto dest!: set_zip_D)

  have 1: "rawpsubstT (rawpsubstT r1 (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
           rawpsubstT (rawpsubstT r1 (zip (map Var vs1) (map snd txs))) (zip (map fst txs) vs1)"
  using assms us_facts vs1_facts by (intro rawpsubstT_compose_freshVar2) auto

  have 2: "rawpsubstT (rawpsubstT r2 (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
           rawpsubstT (rawpsubstT r2 (zip (map Var vs2) (map snd txs))) (zip (map fst txs) vs2)"
  using assms us_facts vs2_facts by (intro rawpsubstT_compose_freshVar2) auto

  have 3: "rawpsubstT (rawpsubstT (pls r1 r2) (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
    pls (rawpsubstT (rawpsubstT r1 (zip (map Var us) (map snd txs))) (zip (map fst txs) us))
     (rawpsubstT (rawpsubstT r2 (zip (map Var us) (map snd txs))) (zip (map fst txs) us))"
  unfolding 0 using assms us_facts apply(intro rawpsubstT_pls)
  subgoal by (auto dest!: set_zip_D intro!: rawpsubstT)
  subgoal by (force dest!: set_zip_D intro!: rawpsubstT simp: Int_def)
  subgoal by (auto dest!: set_zip_D intro!: rawpsubstT)
  subgoal by (fastforce dest!: set_zip_D intro!: rawpsubstT simp: Int_def) .
  show ?thesis unfolding psubstT_def
  by (simp add: Let_def us[symmetric] vs1[symmetric] vs2[symmetric] 1 2 3)
qed

lemma rawpsubstT_tms:
assumes "r1 \<in> trm" "r2 \<in> trm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> trm"
shows "rawpsubstT (tms r1 r2) txs = tms (rawpsubstT r1 txs) (rawpsubstT r2 txs)"
using assms apply(induct txs arbitrary: r1 r2)
subgoal by simp
subgoal for tx txs r by (cases tx) auto .

lemma psubstT_tms[simp]:
assumes "r1 \<in> atrm" "r2 \<in> atrm" and "snd ` (set txs) \<subseteq> var" and "fst ` (set txs) \<subseteq> atrm"
and "distinct (map snd txs)"
shows "psubstT (tms r1 r2) txs = tms (psubstT r1 txs) (psubstT r2 txs)"
proof-
  have 000: "fst ` (set txs) \<subseteq> trm" using assms by auto
  define us where us: "us \<equiv> getFrN (map snd txs) (tms r1 r2 # map fst txs) [] (length txs)"
  have us_facts: "set us \<subseteq> var"
  "set us \<inter> FvarsT r1 = {}"
  "set us \<inter> FvarsT r2 = {}"
  "set us \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set us \<inter> snd ` (set txs) = {}"
  "length us = length txs"
  "distinct us"
  using assms(1-3) 000 unfolding us
  using getFrN_FvarsT[of "map snd txs" "tms r1 r2 # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "tms r1 r2 # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "tms r1 r2 # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "tms r1 r2 # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "tms r1 r2 # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by force
  subgoal by auto
  subgoal by force
  by auto
  define vs1 where vs1: "vs1 \<equiv> getFrN (map snd txs) (r1 # map fst txs) [] (length txs)"
  have vs1_facts: "set vs1 \<subseteq> var"
  "set vs1 \<inter> FvarsT r1 = {}"
  "set vs1 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set vs1 \<inter> snd ` (set txs) = {}"
  "length vs1 = length txs"
  "distinct vs1"
  using assms(1-3) 000 unfolding vs1
  using getFrN_FvarsT[of "map snd txs" "r1 # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "r1 # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "r1 # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "r1 # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "r1 # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by auto
  subgoal by force
  subgoal by force
  by auto
  define vs2 where vs2: "vs2 \<equiv> getFrN (map snd txs) (r2 # map fst txs) [] (length txs)"
  have vs2_facts: "set vs2 \<subseteq> var"
  "set vs2 \<inter> FvarsT r2 = {}"
  "set vs2 \<inter> \<Union> (FvarsT ` (fst ` (set txs))) = {}"
  "set vs2 \<inter> snd ` (set txs) = {}"
  "length vs2 = length txs"
  "distinct vs2"
  using assms(1-3) 000 unfolding vs2
  using getFrN_FvarsT[of "map snd txs" "r2 # map fst txs" "[]" _ "length txs"]
        getFrN_Fvars[of "map snd txs" "r2 # map fst txs" "[]" _ "length txs"]
        getFrN_var[of "map snd txs" "r2 # map fst txs" "[]" _ "length txs"]
        getFrN_length[of "map snd txs" "r2 # map fst txs" "[]" "length txs"]
        getFrN_length[of "map snd txs" "r2 # map fst txs" "[]" "length txs"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by auto
  subgoal by force
  subgoal by force
  by auto
  have 0: "rawpsubstT (tms r1 r2) (zip (map Var us) (map snd txs)) =
           tms (rawpsubstT r1 (zip (map Var us) (map snd txs)))
               (rawpsubstT r2 (zip (map Var us) (map snd txs)))"
  using assms us_facts by (intro rawpsubstT_tms) (auto dest!: set_zip_D)

  have 1: "rawpsubstT (rawpsubstT r1 (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
           rawpsubstT (rawpsubstT r1 (zip (map Var vs1) (map snd txs))) (zip (map fst txs) vs1)"
  using assms us_facts vs1_facts by (intro rawpsubstT_compose_freshVar2) auto

  have 2: "rawpsubstT (rawpsubstT r2 (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
           rawpsubstT (rawpsubstT r2 (zip (map Var vs2) (map snd txs))) (zip (map fst txs) vs2)"
  using assms us_facts vs2_facts by (intro rawpsubstT_compose_freshVar2) auto

  have 3: "rawpsubstT (rawpsubstT (tms r1 r2) (zip (map Var us) (map snd txs))) (zip (map fst txs) us) =
    tms (rawpsubstT (rawpsubstT r1 (zip (map Var us) (map snd txs))) (zip (map fst txs) us))
     (rawpsubstT (rawpsubstT r2 (zip (map Var us) (map snd txs))) (zip (map fst txs) us))"
  unfolding 0 using assms us_facts apply(intro rawpsubstT_tms)
  subgoal by (auto dest!: set_zip_D intro!: rawpsubstT)
  subgoal by (force dest!: set_zip_D intro!: rawpsubstT simp: Int_def)
  subgoal by (auto dest!: set_zip_D intro!: rawpsubstT)
  subgoal by (fastforce dest!: set_zip_D intro!: rawpsubstT simp: Int_def) .

  show ?thesis unfolding psubstT_def
  by (simp add: Let_def us[symmetric] vs1[symmetric] vs2[symmetric] 1 2 3)
qed


section \<open>The (Nonstrict and Strict) Order Relations\<close>

text \<open>Lq (less than or equal to) is a formula with free vars xx and yy.
NB: Out of the two possible ways, adding zz to the left or to the right,
we choose the former, since this seems to enable Q (Robinson arithmetic)
to prove as many useful properties as possible.\<close>

definition Lq :: "'fmla" where
"Lq \<equiv> exi zz (eql (Var yy) (pls (Var zz) (Var xx)))"

text \<open>Alternative, more flexible definition , for any non-capturing bound variable:\<close>
lemma Lq_def2: "z \<in> var \<Longrightarrow> z \<noteq> yy \<Longrightarrow> z \<noteq> xx \<Longrightarrow> Lq = exi z (eql (Var yy) (pls  (Var z) (Var xx)))"
unfolding Lq_def using exi_rename[of "eql (Var yy) (pls (Var zz) (Var xx))" zz z] by auto

lemma Lq[simp,intro!]: "Lq \<in> fmla"
unfolding Lq_def by auto

lemma Fvars_Lq[simp]: "Fvars Lq = {xx,yy}"
unfolding Lq_def by auto

text \<open>As usual, we also define a predicate version:\<close>
definition LLq where "LLq \<equiv> \<lambda> t1 t2. psubst Lq [(t1,xx), (t2,yy)]"

lemma LLq[simp,intro]:
assumes "t1 \<in> trm" "t2 \<in> trm"
shows "LLq t1 t2 \<in> fmla"
  using assms unfolding LLq_def by auto

lemma LLq2[simp,intro!]:
"n \<in> num \<Longrightarrow> LLq n (Var yy') \<in> fmla"
  by auto

lemma Fvars_LLq[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow>
Fvars (LLq t1 t2) = FvarsT t1 \<union> FvarsT t2"
unfolding LLq_def apply(subst Fvars_psubst)
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal apply safe
  subgoal by auto
  subgoal by auto
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by force . .

text \<open>This lemma will be the working definition of LLq:\<close>
lemma LLq_pls:
assumes [simp]: "t1 \<in> atrm" "t2 \<in> atrm" "z \<in> var" "z \<notin> FvarsT t1" "z \<notin> FvarsT t2"
shows "LLq t1 t2 = exi z (eql t2 (pls (Var z) t1))"
proof-
  define z' where "z' \<equiv> getFr [xx,yy,z] [t1,t2] []"
  have z_facts[simp]: "z' \<in> var" "z' \<noteq> yy" "z' \<noteq> xx" "z' \<noteq> z" "z \<noteq> z'" "z' \<notin> FvarsT t1" "z' \<notin> FvarsT t2"
  using getFr_FvarsT_Fvars[of "[xx,yy,z]" "[t1,t2]" "[]"] unfolding z'_def by auto
  have "LLq t1 t2 = exi z' (eql t2 (pls (Var z') t1))"
  by (simp add: LLq_def Lq_def2[of z'])
  also have "\<dots> = exi z (eql t2 (pls (Var z) t1))"
  using exi_rename[of "eql t2 (pls (Var z') t1)" z' z, simplified] .
  finally show ?thesis .
qed

lemma LLq_pls_zz:
assumes "t1 \<in> atrm" "t2 \<in> atrm" "zz \<notin> FvarsT t1" "zz \<notin> FvarsT t2"
shows "LLq t1 t2 = exi zz (eql t2 (pls (Var zz) t1))"
using assms by (intro LLq_pls) auto

text \<open>If we restrict attention to arithmetic terms, we can prove a uniform
substitution property for LLq:\<close>
lemma subst_LLq[simp]:
assumes [simp]: "t1 \<in> atrm" "t2 \<in> atrm" "s \<in> atrm" "x \<in> var"
shows "subst (LLq t1 t2) s x = LLq (substT t1 s x) (substT t2 s x)"
proof-
  define z where "z \<equiv> getFr [xx,yy,x] [t1,t2,s] []"
  have z_facts[simp]: "z \<in> var" "z \<noteq> xx" "z \<noteq> yy" "z \<noteq> x" "z \<notin> FvarsT t1" "z \<notin> FvarsT t2" "z \<notin> FvarsT s"
  using getFr_FvarsT_Fvars[of "[xx,yy,x]" "[t1,t2,s]" "[]"] unfolding z_def by auto
  show ?thesis
  by(simp add: FvarsT_substT LLq_pls[of _ _ z] subst2_fresh_switch Lq_def)
qed

lemma psubst_LLq[simp]:
assumes 1: "t1 \<in> atrm" "t2 \<in> atrm" "fst ` set txs \<subseteq> atrm"
and 2: "snd ` set txs \<subseteq> var"
and 3: "distinct (map snd txs)"
shows "psubst (LLq t1 t2) txs = LLq (psubstT t1 txs) (psubstT t2 txs)"
proof-
  have 0: "t1 \<in> trm" "t2 \<in> trm" "fst ` set txs \<subseteq> trm" using 1 by auto
  define z where z: "z \<equiv> getFr ([xx,yy] @ map snd txs) ([t1,t2] @ map fst txs) []"
  have us_facts: "z \<in> var"  "z \<noteq> xx" "z \<noteq> yy"
  "z \<notin> FvarsT t1" "z \<notin> FvarsT t2"
  "z \<notin> \<Union> (FvarsT ` (fst ` (set txs)))"
  "z \<notin> snd ` (set txs)"
  using 0 2 unfolding z
  using getFr_FvarsT[of "[xx,yy] @  map snd txs" "[t1,t2] @ map fst txs" "[]" ]
        getFr_Fvars[of "[xx,yy] @  map snd txs" "[t1,t2] @ map fst txs" "[]" ]
        getFr_var[of "[xx,yy] @  map snd txs" "[t1,t2] @ map fst txs" "[]"]
  apply -
  subgoal by auto
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by auto
  subgoal by (force simp: image_iff) .

  note in_FvarsT_psubstTD[dest!]
  note if_splits[split]
  show ?thesis
  using assms 0 us_facts apply(subst LLq_pls[of _ _ z])
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal apply(subst LLq_pls[of _ _ z]) by auto .
qed


text \<open>Lq less than) is the strict version of the order relation.
We prove similar facts as for Lq\<close>

definition Ls :: "'fmla" where
"Ls \<equiv> cnj Lq (neg (eql (Var xx) (Var yy)))"

lemma Ls[simp,intro!]: "Ls \<in> fmla"
unfolding Ls_def by auto

lemma Fvars_Ls[simp]: "Fvars Ls = {xx,yy}"
unfolding Ls_def by auto

definition LLs where "LLs \<equiv> \<lambda> t1 t2. psubst Ls [(t1,xx), (t2,yy)]"

lemma LLs[simp,intro]:
assumes "t1 \<in> trm" "t2 \<in> trm"
shows "LLs t1 t2 \<in> fmla"
  using assms unfolding LLs_def by auto

lemma LLs2[simp,intro!]:
"n \<in> num \<Longrightarrow> LLs n (Var yy') \<in> fmla"
  by auto

lemma Fvars_LLs[simp]: "t1 \<in> trm \<Longrightarrow> t2 \<in> trm \<Longrightarrow>
Fvars (LLs t1 t2) = FvarsT t1 \<union> FvarsT t2"
unfolding LLs_def apply(subst Fvars_psubst)
subgoal by auto
subgoal by auto
subgoal by auto
subgoal by auto
subgoal apply safe
  subgoal by auto
  subgoal by auto
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by force . .

text \<open>The working definition of LLs:\<close>
lemma LLs_LLq:
"t1 \<in> atrm \<Longrightarrow> t2 \<in> atrm \<Longrightarrow>
 LLs t1 t2 = cnj (LLq t1 t2) (neg (eql t1 t2))"
by (simp add: LLs_def Ls_def LLq_def)

lemma subst_LLs[simp]:
assumes [simp]: "t1 \<in> atrm" "t2 \<in> atrm" "s \<in> atrm" "x \<in> var"
shows "subst (LLs t1 t2) s x = LLs (substT t1 s x) (substT t2 s x)"
by(simp add: LLs_LLq subst2_fresh_switch Ls_def)

lemma psubst_LLs[simp]:
assumes 1: "t1 \<in> atrm" "t2 \<in> atrm" "fst ` set txs \<subseteq> atrm"
and 2: "snd ` set txs \<subseteq> var"
and 3: "distinct (map snd txs)"
shows "psubst (LLs t1 t2) txs = LLs (psubstT t1 txs) (psubstT t2 txs)"
proof-
  have 0: "t1 \<in> trm" "t2 \<in> trm" "fst ` set txs \<subseteq> trm" using 1 by auto
  define z where z: "z \<equiv> getFr ([xx,yy] @ map snd txs) ([t1,t2] @ map fst txs) []"
  have us_facts: "z \<in> var"  "z \<noteq> xx" "z \<noteq> yy"
  "z \<notin> FvarsT t1" "z \<notin> FvarsT t2"
  "z \<notin> \<Union> (FvarsT ` (fst ` (set txs)))"
  "z \<notin> snd ` (set txs)"
  using 0 2 unfolding z
  using getFr_FvarsT[of "[xx,yy] @  map snd txs" "[t1,t2] @ map fst txs" "[]" ]
        getFr_Fvars[of "[xx,yy] @  map snd txs" "[t1,t2] @ map fst txs" "[]" ]
        getFr_var[of "[xx,yy] @  map snd txs" "[t1,t2] @ map fst txs" "[]"]
   apply -
  subgoal by auto
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by force
  subgoal by auto
  subgoal by (force simp: image_iff) .
  show ?thesis
  using assms 0 us_facts by (simp add: LLs_LLq)
qed


section \<open>Bounded Quantification\<close>

text \<open>Bounded forall\<close>

definition ball :: "'var \<Rightarrow> 'trm \<Rightarrow> 'fmla \<Rightarrow> 'fmla" where
"ball x t \<phi> \<equiv> all x (imp (LLq (Var x) t) \<phi>)"

lemma ball[simp, intro]: "x \<in> var \<Longrightarrow> t \<in> trm \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> ball x t \<phi> \<in> fmla"
unfolding ball_def by auto

lemma Fvars_ball[simp]:
"x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> Fvars (ball x t \<phi>) = (Fvars \<phi> \<union> FvarsT t) - {x}"
unfolding ball_def by auto

lemma subst_ball:
"\<phi> \<in> fmla \<Longrightarrow> t \<in> atrm \<Longrightarrow> t1 \<in> atrm \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<notin> FvarsT t1 \<Longrightarrow>
 subst (ball x t \<phi>) t1 y = ball x (substT t t1 y) (subst \<phi> t1 y)"
  unfolding ball_def by simp

lemma psubst_ball:
"\<phi> \<in> fmla \<Longrightarrow> y \<in> var \<Longrightarrow> snd ` set txs \<subseteq> var \<Longrightarrow> t \<in> atrm \<Longrightarrow>
 fst ` set txs \<subseteq> trm \<Longrightarrow> fst ` set txs \<subseteq> atrm \<Longrightarrow> y \<notin> snd ` set txs \<Longrightarrow> y \<notin> (\<Union>t \<in> fst ` set txs. FvarsT t) \<Longrightarrow>
 distinct (map snd txs) \<Longrightarrow>
 psubst (ball y t \<phi>) txs = ball y (psubstT t txs) (psubst \<phi> txs)"
unfolding ball_def by simp

text \<open>Bounded exists\<close>

definition bexi :: "'var \<Rightarrow> 'trm \<Rightarrow> 'fmla \<Rightarrow> 'fmla" where
"bexi x t \<phi> \<equiv> exi x (cnj (LLq (Var x) t) \<phi>)"

lemma bexi[simp, intro]: "x \<in> var \<Longrightarrow> t \<in> trm \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> bexi x t \<phi> \<in> fmla"
unfolding bexi_def by auto

lemma Fvars_bexi[simp]:
"x \<in> var \<Longrightarrow> \<phi> \<in> fmla \<Longrightarrow> t \<in> trm \<Longrightarrow> Fvars (bexi x t \<phi>) = (Fvars \<phi> \<union> FvarsT t) - {x}"
unfolding bexi_def by auto

lemma subst_bexi:
"\<phi> \<in> fmla \<Longrightarrow> t \<in> atrm \<Longrightarrow> t1 \<in> atrm \<Longrightarrow> x \<in> var \<Longrightarrow> y \<in> var \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<notin> FvarsT t1 \<Longrightarrow>
 subst (bexi x t \<phi>) t1 y = bexi x (substT t t1 y) (subst \<phi> t1 y)"
unfolding bexi_def by simp

lemma psubst_bexi:
"\<phi> \<in> fmla \<Longrightarrow> y \<in> var \<Longrightarrow> snd ` set txs \<subseteq> var \<Longrightarrow> t \<in> atrm \<Longrightarrow>
 fst ` set txs \<subseteq> trm \<Longrightarrow> fst ` set txs \<subseteq> atrm \<Longrightarrow> y \<notin> snd ` set txs \<Longrightarrow> y \<notin> (\<Union>t \<in> fst ` set txs. FvarsT t) \<Longrightarrow>
 distinct (map snd txs) \<Longrightarrow>
 psubst (bexi y t \<phi>) txs = bexi y (psubstT t txs) (psubst \<phi> txs)"
unfolding bexi_def by simp

end \<comment> \<open>context @{locale Syntax_Arith}\<close>

(*<*)
end
(*>*)
