(*
(C) Copyright Andreas Viktor Hess, DTU, 2015-2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      Example_Keyserver.thy
    Author:     Andreas Viktor Hess, DTU
*)


section \<open>The Keyserver Example\<close>
text \<open>\label{sec:Example-Keyserver}\<close>
theory Example_Keyserver
imports "../Stateful_Compositionality"
begin

declare [[code_timing]]

subsection \<open>Setup\<close>
subsubsection \<open>Datatypes and functions setup\<close>
datatype ex_lbl = Label1 ("\<one>") | Label2 ("\<two>")

datatype ex_atom =
  Agent | Value | Attack | PrivFunSec
| Bot

datatype ex_fun =
  ring | valid | revoked | events | beginauth nat | endauth nat | pubkeys | seen
| invkey | tuple | tuple' | attack nat
| sign | crypt | update | pw
| encodingsecret | pubkey nat
| pubconst ex_atom nat

type_synonym ex_type = "(ex_fun, ex_atom) term_type"
type_synonym ex_var = "ex_type \<times> nat"

lemma ex_atom_UNIV:
  "(UNIV::ex_atom set) = {Agent, Value, Attack, PrivFunSec, Bot}"
by (auto intro: ex_atom.exhaust)

instance ex_atom::finite
by intro_classes (metis ex_atom_UNIV finite.emptyI finite.insertI)

lemma ex_lbl_UNIV:
  "(UNIV::ex_lbl set) = {Label1, Label2}"
by (auto intro: ex_lbl.exhaust)

type_synonym ex_term = "(ex_fun, ex_var) term"
type_synonym ex_terms = "(ex_fun, ex_var) terms"

primrec arity::"ex_fun \<Rightarrow> nat" where
  "arity ring = 2"
| "arity valid = 3"
| "arity revoked = 3"
| "arity events = 1"
| "arity (beginauth _) = 3"
| "arity (endauth _) = 3"
| "arity pubkeys = 2"
| "arity seen = 2"
| "arity invkey = 2"
| "arity tuple = 2"
| "arity tuple' = 2"
| "arity (attack _) = 0"
| "arity sign = 2"
| "arity crypt = 2"
| "arity update = 4"
| "arity pw = 2"
| "arity (pubkey _) = 0"
| "arity encodingsecret = 0"
| "arity (pubconst _ _) = 0"

fun public::"ex_fun \<Rightarrow> bool" where
  "public (pubkey _) = False"
| "public encodingsecret = False"
| "public _ = True"

fun Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t::"ex_term list \<Rightarrow> (ex_term list \<times> ex_term list)" where
  "Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t [k,m] = ([Fun invkey [Fun encodingsecret [], k]], [m])"
| "Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t _ = ([], [])"

fun Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n::"ex_term list \<Rightarrow> (ex_term list \<times> ex_term list)" where
  "Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n [k,m] = ([], [m])"
| "Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n _ = ([], [])"

fun Ana::"ex_term \<Rightarrow> (ex_term list \<times> ex_term list)" where
  "Ana (Fun tuple T) = ([], T)"
| "Ana (Fun tuple' T) = ([], T)"
| "Ana (Fun sign T) = Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n T"
| "Ana (Fun crypt T) = Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t T"
| "Ana _ = ([], [])"


subsubsection \<open>Keyserver example: Locale interpretation\<close>
lemma assm1:
  "Ana t = (K,M) \<Longrightarrow> fv\<^sub>s\<^sub>e\<^sub>t (set K) \<subseteq> fv t"
  "Ana t = (K,M) \<Longrightarrow> (\<And>g S'. Fun g S' \<sqsubseteq> t \<Longrightarrow> length S' = arity g)
                \<Longrightarrow> k \<in> set K \<Longrightarrow> Fun f T' \<sqsubseteq> k \<Longrightarrow> length T' = arity f"
  "Ana t = (K,M) \<Longrightarrow> K \<noteq> [] \<or> M \<noteq> [] \<Longrightarrow> Ana (t \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>, M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
by (rule Ana.cases[of "t"], auto elim!: Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t.elims Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n.elims)+

lemma assm2: "Ana (Fun f T) = (K, M) \<Longrightarrow> set M \<subseteq> set T"
by (rule Ana.cases[of "Fun f T"]) (auto elim!: Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t.elims Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n.elims)

lemma assm6: "0 < arity f \<Longrightarrow> public f" by (cases f) simp_all

global_interpretation im: intruder_model arity public Ana
  defines wf\<^sub>t\<^sub>r\<^sub>m = "im.wf\<^sub>t\<^sub>r\<^sub>m"
by unfold_locales (metis assm1(1), metis assm1(2),rule Ana.simps, metis assm2, metis assm1(3))

type_synonym ex_strand_step = "(ex_fun,ex_var) strand_step"
type_synonym ex_strand = "(ex_fun,ex_var) strand"


subsubsection \<open>Typing function\<close>
definition \<Gamma>\<^sub>v::"ex_var \<Rightarrow> ex_type" where
  "\<Gamma>\<^sub>v v = (if (\<forall>t \<in> subterms (fst v). case t of
                (TComp f T) \<Rightarrow> arity f > 0 \<and> arity f = length T
              | _ \<Rightarrow> True)
           then fst v else TAtom Bot)"

fun \<Gamma>::"ex_term \<Rightarrow> ex_type" where
  "\<Gamma> (Var v) = \<Gamma>\<^sub>v v"
| "\<Gamma> (Fun (attack _) _) = TAtom Attack"
| "\<Gamma> (Fun (pubkey _) _) = TAtom Value"
| "\<Gamma> (Fun encodingsecret _) = TAtom PrivFunSec"
| "\<Gamma> (Fun (pubconst \<tau> _) _) = TAtom \<tau>"
| "\<Gamma> (Fun f T) = TComp f (map \<Gamma> T)"


subsubsection \<open>Locale interpretation: typed model\<close>
lemma assm7: "arity c = 0 \<Longrightarrow> \<exists>a. \<forall>X. \<Gamma> (Fun c X) = TAtom a" by (cases c) simp_all

lemma assm8: "0 < arity f \<Longrightarrow> \<Gamma> (Fun f X) = TComp f (map \<Gamma> X)" by (cases f) simp_all

lemma assm9: "infinite {c. \<Gamma> (Fun c []) = TAtom a \<and> public c}"
proof -
  let ?T = "(range (pubconst a))::ex_fun set"
  have *:
      "\<And>x y::nat. x \<in> UNIV \<Longrightarrow> y \<in> UNIV \<Longrightarrow> (pubconst a x = pubconst a y) = (x = y)"
      "\<And>x::nat. x \<in> UNIV \<Longrightarrow> pubconst a x \<in> ?T"
      "\<And>y::ex_fun. y \<in> ?T \<Longrightarrow> \<exists>x \<in> UNIV. y = pubconst a x"
    by auto
  have "?T \<subseteq> {c. \<Gamma> (Fun c []) = TAtom a \<and> public c}" by auto
  moreover have "\<exists>f::nat \<Rightarrow> ex_fun. bij_betw f UNIV ?T"
    using bij_betwI'[OF *] by blast
  hence "infinite ?T" by (metis nat_not_finite bij_betw_finite)
  ultimately show ?thesis using infinite_super by blast
qed

lemma assm10: "TComp f T \<sqsubseteq> \<Gamma> t \<Longrightarrow> arity f > 0"
proof (induction rule: \<Gamma>.induct)
  case (1 x)
  hence *: "TComp f T \<sqsubseteq> \<Gamma>\<^sub>v x" by simp
  hence "\<Gamma>\<^sub>v x \<noteq> TAtom Bot" unfolding \<Gamma>\<^sub>v_def by force
  hence "\<forall>t \<in> subterms (fst x). case t of
            (TComp f T) \<Rightarrow> arity f > 0 \<and> arity f = length T
          | _ \<Rightarrow> True"
    unfolding \<Gamma>\<^sub>v_def by argo
  thus ?case using * unfolding \<Gamma>\<^sub>v_def by fastforce 
qed auto

lemma assm11: "im.wf\<^sub>t\<^sub>r\<^sub>m (\<Gamma> (Var x))"
proof -
  have "im.wf\<^sub>t\<^sub>r\<^sub>m (\<Gamma>\<^sub>v x)" unfolding \<Gamma>\<^sub>v_def im.wf\<^sub>t\<^sub>r\<^sub>m_def by auto 
  thus ?thesis by simp
qed

lemma assm12: "\<Gamma> (Var (\<tau>, n)) = \<Gamma> (Var (\<tau>, m))"
apply (cases "\<forall>t \<in> subterms \<tau>. case t of
                (TComp f T) \<Rightarrow> arity f > 0 \<and> arity f = length T
              | _ \<Rightarrow> True")
by (auto simp add: \<Gamma>\<^sub>v_def)

lemma Ana_const: "arity c = 0 \<Longrightarrow> Ana (Fun c T) = ([], [])"
by (cases c) simp_all

lemma Ana_subst': "Ana (Fun f T) = (K,M) \<Longrightarrow> Ana (Fun f T \<cdot> \<delta>) = (K \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>,M \<cdot>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<delta>)"
by (cases f) (auto elim!: Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t.elims Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n.elims)

global_interpretation tm: typed_model' arity public Ana \<Gamma>
by (unfold_locales, unfold wf\<^sub>t\<^sub>r\<^sub>m_def[symmetric])
   (metis assm7, metis assm8, metis assm9, metis assm10, metis assm11, metis assm6,
    metis assm12, metis Ana_const, metis Ana_subst')


subsubsection \<open>Locale interpretation: labeled stateful typed model\<close>
global_interpretation stm: labeled_stateful_typed_model' arity public Ana \<Gamma> tuple \<one> \<two>
by standard (rule arity.simps, metis Ana_subst', metis assm12, metis Ana_const, simp)

type_synonym ex_stateful_strand_step = "(ex_fun,ex_var) stateful_strand_step"
type_synonym ex_stateful_strand = "(ex_fun,ex_var) stateful_strand"

type_synonym ex_labeled_stateful_strand_step =
  "(ex_fun,ex_var,ex_lbl) labeled_stateful_strand_step"

type_synonym ex_labeled_stateful_strand =
  "(ex_fun,ex_var,ex_lbl) labeled_stateful_strand"


subsection \<open>Theorem: Type-flaw resistance of the keyserver example from the CSF18 paper\<close>
abbreviation "PK n \<equiv> Var (TAtom Value,n)"
abbreviation "A n \<equiv> Var (TAtom Agent,n)"
abbreviation "X n \<equiv> (TAtom Agent,n)"

abbreviation "ringset t \<equiv> Fun ring [Fun encodingsecret [], t]"
abbreviation "validset t t' \<equiv> Fun valid [Fun encodingsecret [], t, t']"
abbreviation "revokedset t t' \<equiv> Fun revoked [Fun encodingsecret [], t, t']"
abbreviation "eventsset \<equiv> Fun events [Fun encodingsecret []]"

(* Note: We will use S\<^sub>k\<^sub>s as a constraint, but it actually represents all steps that might occur
         in the protocol *)
abbreviation S\<^sub>k\<^sub>s::"(ex_fun,ex_var) stateful_strand_step list" where
  "S\<^sub>k\<^sub>s \<equiv> [
    insert\<langle>Fun (attack 0) [], eventsset\<rangle>,
    delete\<langle>PK 0, validset (A 0) (A 0)\<rangle>,
    \<forall>(TAtom Agent,0)\<langle>PK 0 not in revokedset (A 0) (A 0)\<rangle>,
    \<forall>(TAtom Agent,0)\<langle>PK 0 not in validset (A 0) (A 0)\<rangle>,
    insert\<langle>PK 0, validset (A 0) (A 0)\<rangle>,
    insert\<langle>PK 0, ringset (A 0)\<rangle>,
    insert\<langle>PK 0, revokedset (A 0) (A 0)\<rangle>,
    select\<langle>PK 0, validset (A 0) (A 0)\<rangle>,
    select\<langle>PK 0, ringset (A 0)\<rangle>,
    receive\<langle>Fun invkey [Fun encodingsecret [], PK 0]\<rangle>,
    receive\<langle>Fun sign [Fun invkey [Fun encodingsecret [], PK 0], Fun tuple' [A 0, PK 0]]\<rangle>,
    send\<langle>Fun invkey [Fun encodingsecret [], PK 0]\<rangle>,
    send\<langle>Fun sign [Fun invkey [Fun encodingsecret [], PK 0], Fun tuple' [A 0, PK 0]]\<rangle>
]"

theorem "stm.tfr\<^sub>s\<^sub>s\<^sub>t S\<^sub>k\<^sub>s"
proof -
  let ?M = "concat (map subterms_list (trms_list\<^sub>s\<^sub>s\<^sub>t S\<^sub>k\<^sub>s@map (pair' tuple) (setops_list\<^sub>s\<^sub>s\<^sub>t S\<^sub>k\<^sub>s)))"
  have "comp_tfr\<^sub>s\<^sub>s\<^sub>t arity Ana \<Gamma> tuple ?M S\<^sub>k\<^sub>s" by eval
  thus ?thesis by (rule stm.tfr\<^sub>s\<^sub>s\<^sub>t_if_comp_tfr\<^sub>s\<^sub>s\<^sub>t)
qed


subsection \<open>Theorem: Type-flaw resistance of the keyserver examples from the ESORICS18 paper\<close>
abbreviation "signmsg t t' \<equiv> Fun sign [t, t']"
abbreviation "cryptmsg t t' \<equiv> Fun crypt [t, t']"
abbreviation "invkeymsg t \<equiv> Fun invkey [Fun encodingsecret [], t]"
abbreviation "updatemsg a b c d \<equiv> Fun update [a,b,c,d]"
abbreviation "pwmsg t t' \<equiv> Fun pw [t, t']"

abbreviation "beginauthset n t t' \<equiv> Fun (beginauth n) [Fun encodingsecret [], t, t']"
abbreviation "endauthset n t t' \<equiv> Fun (endauth n) [Fun encodingsecret [], t, t']"
abbreviation "pubkeysset t \<equiv> Fun pubkeys [Fun encodingsecret [], t]"
abbreviation "seenset t \<equiv> Fun seen [Fun encodingsecret [], t]"

declare [[coercion "Var::ex_var \<Rightarrow> ex_term"]]
declare [[coercion_enabled]]

(* Note: S'\<^sub>k\<^sub>s contains the (slightly over-approximated) steps that can occur in the
         reachable constraints of \<P>\<^sub>k\<^sub>s,\<^sub>1 and \<P>\<^sub>k\<^sub>s,\<^sub>2 modulo variable renaming *)
definition S'\<^sub>k\<^sub>s::"ex_labeled_stateful_strand_step list" where
  "S'\<^sub>k\<^sub>s \<equiv> [
\<^cancel>\<open>constraint steps from the first protocol (duplicate steps are ignored)\<close>

    \<^cancel>\<open>rule R^1_1\<close>
    \<langle>\<one>, send\<langle>invkeymsg (PK 0)\<rangle>\<rangle>,
    \<langle>\<star>, \<langle>PK 0 in validset (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<one>, receive\<langle>Fun (attack 0) []\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^2_1\<close>
    \<langle>\<one>, send\<langle>signmsg (invkeymsg (PK 0)) (Fun tuple' [A 0, PK 0])\<rangle>\<rangle>,
    \<langle>\<star>, \<langle>PK 0 in validset (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<star>, \<forall>X 0, X 1\<langle>PK 0 not in validset (Var (X 0)) (Var (X 1))\<rangle>\<rangle>,
    \<langle>\<one>, \<forall>X 0, X 1\<langle>PK 0 not in revokedset (Var (X 0)) (Var (X 1))\<rangle>\<rangle>,
    \<langle>\<star>, \<langle>PK 0 not in beginauthset 0 (A 0) (A 1)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^3_1\<close>
    \<langle>\<star>, \<langle>PK 0 in beginauthset 0 (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<star>, \<langle>PK 0 in endauthset 0 (A 0) (A 1)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^4_1\<close>
    \<langle>\<star>, receive\<langle>PK 0\<rangle>\<rangle>,
    \<langle>\<star>, receive\<langle>invkeymsg (PK 0)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^5_1\<close>
    \<langle>\<one>, insert\<langle>PK 0, ringset (A 0)\<rangle>\<rangle>,
    \<langle>\<star>, insert\<langle>PK 0, validset (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<star>, insert\<langle>PK 0, beginauthset 0 (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<star>, insert\<langle>PK 0, endauthset 0 (A 0) (A 1)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^6_1\<close>
    \<langle>\<one>, select\<langle>PK 0, ringset (A 0)\<rangle>\<rangle>,
    \<langle>\<one>, delete\<langle>PK 0, ringset (A 0)\<rangle>\<rangle>,
    
    \<^cancel>\<open>rule R^7_1\<close>
    \<langle>\<star>, \<langle>PK 0 not in endauthset 0 (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<star>, delete\<langle>PK 0, validset (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<one>, insert\<langle>PK 0, revokedset (A 0) (A 1)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^8_1\<close>
    \<^cancel>\<open>nothing new\<close>

    \<^cancel>\<open>rule R^9_1\<close>
    \<langle>\<one>, send\<langle>PK 0\<rangle>\<rangle>,
    
    \<^cancel>\<open>rule R^10_1\<close>
    \<langle>\<one>, send\<langle>Fun (attack 0) []\<rangle>\<rangle>,

\<^cancel>\<open>constraint steps from the second protocol (duplicate steps are ignored)\<close>
    \<^cancel>\<open>rule R^2_1\<close>
    \<langle>\<two>, send\<langle>invkeymsg (PK 0)\<rangle>\<rangle>,
    \<langle>\<star>, \<langle>PK 0 in validset (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<two>, receive\<langle>Fun (attack 1) []\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^2_2\<close>
    \<langle>\<two>, send\<langle>cryptmsg (PK 0) (updatemsg (A 0) (A 1) (PK 1) (pwmsg (A 0) (A 1)))\<rangle>\<rangle>,
    \<langle>\<two>, select\<langle>PK 0, pubkeysset (A 0)\<rangle>\<rangle>,
    \<langle>\<two>, \<forall>X 0\<langle>PK 0 not in pubkeysset (Var (X 0))\<rangle>\<rangle>,
    \<langle>\<two>, \<forall>X 0\<langle>PK 0 not in seenset (Var (X 0))\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^3_2\<close>
    \<langle>\<star>, \<langle>PK 0 in beginauthset 1 (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<star>, \<langle>PK 0 in endauthset 1 (A 0) (A 1)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^4_2\<close>
    \<langle>\<star>, receive\<langle>PK 0\<rangle>\<rangle>,
    \<langle>\<star>, receive\<langle>invkeymsg (PK 0)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^5_2\<close>
    \<langle>\<two>, select\<langle>PK 0, pubkeysset (A 0)\<rangle>\<rangle>,
    \<langle>\<star>, insert\<langle>PK 0, beginauthset 1 (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<two>, receive\<langle>cryptmsg (PK 0) (updatemsg (A 0) (A 1) (PK 1) (pwmsg (A 0) (A 1)))\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^6_2\<close>
    \<langle>\<star>, \<langle>PK 0 not in endauthset 1 (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<star>, insert\<langle>PK 0, validset (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<star>, insert\<langle>PK 0, endauthset 1 (A 0) (A 1)\<rangle>\<rangle>,
    \<langle>\<two>, insert\<langle>PK 0, seenset (A 0)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^7_2\<close>
    \<langle>\<two>, receive\<langle>pwmsg (A 0) (A 1)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^8_2\<close>
    \<^cancel>\<open>nothing new\<close>

    \<^cancel>\<open>rule R^9_2\<close>
    \<langle>\<two>, insert\<langle>PK 0, pubkeysset (A 0)\<rangle>\<rangle>,

    \<^cancel>\<open>rule R^10_2\<close>
    \<langle>\<two>, send\<langle>Fun (attack 1) []\<rangle>\<rangle>
]"

theorem "stm.tfr\<^sub>s\<^sub>s\<^sub>t (unlabel S'\<^sub>k\<^sub>s)"
proof -
  let ?S = "unlabel S'\<^sub>k\<^sub>s"
  let ?M = "concat (map subterms_list (trms_list\<^sub>s\<^sub>s\<^sub>t ?S@map (pair' tuple) (setops_list\<^sub>s\<^sub>s\<^sub>t ?S)))"
  have "comp_tfr\<^sub>s\<^sub>s\<^sub>t arity Ana \<Gamma> tuple ?M ?S" by eval
  thus ?thesis by (rule stm.tfr\<^sub>s\<^sub>s\<^sub>t_if_comp_tfr\<^sub>s\<^sub>s\<^sub>t)
qed


subsection \<open>Theorem: The steps of the keyserver protocols from the ESORICS18 paper satisfy the conditions for parallel composition\<close>
theorem
  fixes S f
  defines "S \<equiv> [PK 0, invkeymsg (PK 0), Fun encodingsecret []]@concat (
                map (\<lambda>s. [s, Fun tuple [PK 0, s]])
                    [validset (A 0) (A 1), beginauthset 0 (A 0) (A 1), endauthset 0 (A 0) (A 1),
                     beginauthset 1 (A 0) (A 1), endauthset 1 (A 0) (A 1)])@
                [A 0]"
    and "f \<equiv> \<lambda>M. {t \<cdot> \<delta> | t \<delta>. t \<in> M \<and> tm.wt\<^sub>s\<^sub>u\<^sub>b\<^sub>s\<^sub>t \<delta> \<and> im.wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s (subst_range \<delta>) \<and> fv (t \<cdot> \<delta>) = {}}"
    and "Sec \<equiv> (f (set S)) - {m. im.intruder_synth {} m}"
  shows "stm.par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t S'\<^sub>k\<^sub>s Sec"
proof -
  let ?N = "\<lambda>P. concat (map subterms_list (trms_list\<^sub>s\<^sub>s\<^sub>t P@map (pair' tuple) (setops_list\<^sub>s\<^sub>s\<^sub>t P)))"
  let ?M = "\<lambda>l. ?N (proj_unl l S'\<^sub>k\<^sub>s)"
  have "comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t public arity Ana \<Gamma> tuple S'\<^sub>k\<^sub>s ?M S"
    unfolding S_def by eval
  thus ?thesis
    using stm.par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t_if_comp_par_comp\<^sub>l\<^sub>s\<^sub>s\<^sub>t[of S'\<^sub>k\<^sub>s ?M S]
    unfolding Sec_def f_def wf\<^sub>t\<^sub>r\<^sub>m_def[symmetric] by blast
qed

end
