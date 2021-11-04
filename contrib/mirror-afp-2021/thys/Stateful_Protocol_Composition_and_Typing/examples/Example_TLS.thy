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

(*  Title:      Example_TLS.thy
    Author:     Andreas Viktor Hess, DTU
*)

section \<open>Proving Type-Flaw Resistance of the TLS Handshake Protocol\<close>
text \<open>\label{sec:Example-TLS}\<close>
theory Example_TLS
imports "../Typed_Model"
begin

declare [[code_timing]]

subsection \<open>TLS example: Datatypes and functions setup\<close>
datatype ex_atom = PrivKey | SymKey | PubConst | Agent | Nonce | Bot

datatype ex_fun =
  clientHello | clientKeyExchange | clientFinished
| serverHello | serverCert | serverHelloDone
| finished | changeCipher | x509 | prfun | master | pmsForm
| sign | hash | crypt | pub | concat | privkey nat
| pubconst ex_atom nat

type_synonym ex_type = "(ex_fun, ex_atom) term_type"
type_synonym ex_var = "ex_type \<times> nat"

instance ex_atom::finite
proof
  let ?S = "UNIV::ex_atom set"
  have "?S = {PrivKey, SymKey, PubConst, Agent, Nonce, Bot}" by (auto intro: ex_atom.exhaust)
  thus "finite ?S" by (metis finite.emptyI finite.insertI) 
qed

type_synonym ex_term = "(ex_fun, ex_var) term"
type_synonym ex_terms = "(ex_fun, ex_var) terms"

primrec arity::"ex_fun \<Rightarrow> nat" where
  "arity changeCipher = 0"
| "arity clientFinished = 4"
| "arity clientHello = 5"
| "arity clientKeyExchange = 1"
| "arity concat = 5"
| "arity crypt = 2"
| "arity finished = 1"
| "arity hash = 1"
| "arity master = 3"
| "arity pmsForm = 1"
| "arity prfun = 1"
| "arity (privkey _) = 0"
| "arity pub = 1"
| "arity (pubconst _ _) = 0"
| "arity serverCert = 1"
| "arity serverHello = 5"
| "arity serverHelloDone = 0"
| "arity sign = 2"
| "arity x509 = 2"

fun public::"ex_fun \<Rightarrow> bool" where
  "public (privkey _) = False"
| "public _ = True"

fun Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t::"ex_term list \<Rightarrow> (ex_term list \<times> ex_term list)" where
  "Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t [Fun pub [k],m] = ([k], [m])"
| "Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t _ = ([], [])"

fun Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n::"ex_term list \<Rightarrow> (ex_term list \<times> ex_term list)" where
  "Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n [k,m] = ([], [m])"
| "Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n _ = ([], [])"

fun Ana::"ex_term \<Rightarrow> (ex_term list \<times> ex_term list)" where
  "Ana (Fun crypt T) = Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t T"
| "Ana (Fun finished T) = ([], T)"
| "Ana (Fun master T) = ([], T)"
| "Ana (Fun pmsForm T) = ([], T)"
| "Ana (Fun serverCert T) = ([], T)"
| "Ana (Fun serverHello T) = ([], T)"
| "Ana (Fun sign T) = Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n T"
| "Ana (Fun x509 T) = ([], T)"
| "Ana _ = ([], [])"


subsection \<open>TLS example: Locale interpretation\<close>
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
    and wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s = "im.wf\<^sub>t\<^sub>r\<^sub>m\<^sub>s"
by unfold_locales (metis assm1(1), metis assm1(2), rule Ana.simps, metis assm2, metis assm1(3))


subsection \<open>TLS Example: Typing function\<close>
definition \<Gamma>\<^sub>v::"ex_var \<Rightarrow> ex_type" where
  "\<Gamma>\<^sub>v v = (if (\<forall>t \<in> subterms (fst v). case t of
                (TComp f T) \<Rightarrow> arity f > 0 \<and> arity f = length T
              | _ \<Rightarrow> True)
           then fst v else TAtom Bot)"

fun \<Gamma>::"ex_term \<Rightarrow> ex_type" where
  "\<Gamma> (Var v) = \<Gamma>\<^sub>v v"
| "\<Gamma> (Fun (privkey _) _) = TAtom PrivKey"
| "\<Gamma> (Fun changeCipher _) = TAtom PubConst"
| "\<Gamma> (Fun serverHelloDone _) = TAtom PubConst"
| "\<Gamma> (Fun (pubconst \<tau> _) _) = TAtom \<tau>"
| "\<Gamma> (Fun f T) = TComp f (map \<Gamma> T)"


subsection \<open>TLS Example: Locale interpretation (typed model)\<close>
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

lemma Ana_const: "arity c = 0 \<Longrightarrow> Ana (Fun c T) = ([],[])"
by (cases c) simp_all

lemma Ana_keys_subterm: "Ana t = (K,T) \<Longrightarrow> k \<in> set K \<Longrightarrow> k \<sqsubset> t"
proof (induct t rule: Ana.induct)
  case (1 U)
  then obtain m where "U = [Fun pub [k], m]" "K = [k]" "T = [m]"
    by (auto elim!: Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t.elims Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n.elims)
  thus ?case using Fun_subterm_inside_params[of k crypt U] by auto
qed (auto elim!: Ana\<^sub>c\<^sub>r\<^sub>y\<^sub>p\<^sub>t.elims Ana\<^sub>s\<^sub>i\<^sub>g\<^sub>n.elims)

global_interpretation tm: typed_model' arity public Ana \<Gamma>
by (unfold_locales, unfold wf\<^sub>t\<^sub>r\<^sub>m_def[symmetric],
    metis assm7, metis assm8, metis assm9, metis assm10, metis assm11, metis assm6,
    metis assm12, metis Ana_const, metis Ana_keys_subterm)

subsection \<open>TLS example: Proving type-flaw resistance\<close>
abbreviation \<Gamma>\<^sub>v_clientHello where
  "\<Gamma>\<^sub>v_clientHello \<equiv>
    TComp clientHello [TAtom Nonce, TAtom Nonce, TAtom Nonce, TAtom Nonce, TAtom Nonce]"

abbreviation \<Gamma>\<^sub>v_serverHello where
  "\<Gamma>\<^sub>v_serverHello \<equiv>
    TComp serverHello [TAtom Nonce, TAtom Nonce, TAtom Nonce, TAtom Nonce, TAtom Nonce]"

abbreviation \<Gamma>\<^sub>v_pub where
  "\<Gamma>\<^sub>v_pub \<equiv> TComp pub [TAtom PrivKey]"

abbreviation \<Gamma>\<^sub>v_x509 where
  "\<Gamma>\<^sub>v_x509 \<equiv> TComp x509 [TAtom Agent, \<Gamma>\<^sub>v_pub]"

abbreviation \<Gamma>\<^sub>v_sign where
  "\<Gamma>\<^sub>v_sign \<equiv> TComp sign [TAtom PrivKey, \<Gamma>\<^sub>v_x509]"

abbreviation \<Gamma>\<^sub>v_serverCert where
  "\<Gamma>\<^sub>v_serverCert \<equiv> TComp serverCert [\<Gamma>\<^sub>v_sign]"

abbreviation \<Gamma>\<^sub>v_pmsForm where
  "\<Gamma>\<^sub>v_pmsForm \<equiv> TComp pmsForm [TAtom SymKey]"

abbreviation \<Gamma>\<^sub>v_crypt where
  "\<Gamma>\<^sub>v_crypt \<equiv> TComp crypt [\<Gamma>\<^sub>v_pub, \<Gamma>\<^sub>v_pmsForm]"

abbreviation \<Gamma>\<^sub>v_clientKeyExchange where
  "\<Gamma>\<^sub>v_clientKeyExchange \<equiv>
    TComp clientKeyExchange [\<Gamma>\<^sub>v_crypt]"

abbreviation \<Gamma>\<^sub>v_HSMsgs where
  "\<Gamma>\<^sub>v_HSMsgs \<equiv> TComp concat [
    \<Gamma>\<^sub>v_clientHello,
    \<Gamma>\<^sub>v_serverHello,
    \<Gamma>\<^sub>v_serverCert,
    TAtom PubConst,
    \<Gamma>\<^sub>v_clientKeyExchange]"

(* Variables from TLS *)
abbreviation "T\<^sub>1 n \<equiv> Var (TAtom Nonce,n)"
abbreviation "T\<^sub>2 n \<equiv> Var (TAtom Nonce,n)"
abbreviation "R\<^sub>A n \<equiv> Var (TAtom Nonce,n)"
abbreviation "R\<^sub>B n \<equiv> Var (TAtom Nonce,n)"
abbreviation "S n \<equiv> Var (TAtom Nonce,n)"
abbreviation "Cipher n \<equiv> Var (TAtom Nonce,n)"
abbreviation "Comp n \<equiv> Var (TAtom Nonce,n)"
abbreviation "B n \<equiv> Var (TAtom Agent,n)"
abbreviation "Pr\<^sub>c\<^sub>a n \<equiv> Var (TAtom PrivKey,n)"
abbreviation "PMS n \<equiv> Var (TAtom SymKey,n)"
abbreviation "P\<^sub>B n \<equiv> Var (TComp pub [TAtom PrivKey],n)"
abbreviation "HSMsgs n \<equiv> Var (\<Gamma>\<^sub>v_HSMsgs,n)"

subsubsection \<open>Defining the over-approximation set\<close>
abbreviation clientHello\<^sub>t\<^sub>r\<^sub>m where
  "clientHello\<^sub>t\<^sub>r\<^sub>m \<equiv> Fun clientHello [T\<^sub>1 0, R\<^sub>A 1, S 2, Cipher 3, Comp 4]"

abbreviation serverHello\<^sub>t\<^sub>r\<^sub>m where
  "serverHello\<^sub>t\<^sub>r\<^sub>m \<equiv> Fun serverHello [T\<^sub>2 0, R\<^sub>B 1, S 2, Cipher 3, Comp 4]"

abbreviation serverCert\<^sub>t\<^sub>r\<^sub>m where
  "serverCert\<^sub>t\<^sub>r\<^sub>m \<equiv> Fun serverCert [Fun sign [Pr\<^sub>c\<^sub>a 0, Fun x509 [B 1, P\<^sub>B 2]]]"

abbreviation serverHelloDone\<^sub>t\<^sub>r\<^sub>m where
  "serverHelloDone\<^sub>t\<^sub>r\<^sub>m \<equiv> Fun serverHelloDone []"

abbreviation clientKeyExchange\<^sub>t\<^sub>r\<^sub>m where
  "clientKeyExchange\<^sub>t\<^sub>r\<^sub>m \<equiv> Fun clientKeyExchange [Fun crypt [P\<^sub>B 0, Fun pmsForm [PMS 1]]]"

abbreviation changeCipher\<^sub>t\<^sub>r\<^sub>m where
  "changeCipher\<^sub>t\<^sub>r\<^sub>m \<equiv> Fun changeCipher []"

abbreviation finished\<^sub>t\<^sub>r\<^sub>m where
  "finished\<^sub>t\<^sub>r\<^sub>m \<equiv> Fun finished [Fun prfun [
      Fun clientFinished [
          Fun prfun [Fun master [PMS 0, R\<^sub>A 1, R\<^sub>B 2]],
          R\<^sub>A 3, R\<^sub>B 4, Fun hash [HSMsgs 5]
      ]
  ]]"

definition M\<^sub>T\<^sub>L\<^sub>S::"ex_term list" where
  "M\<^sub>T\<^sub>L\<^sub>S \<equiv> [
    clientHello\<^sub>t\<^sub>r\<^sub>m,
    serverHello\<^sub>t\<^sub>r\<^sub>m,
    serverCert\<^sub>t\<^sub>r\<^sub>m,
    serverHelloDone\<^sub>t\<^sub>r\<^sub>m,
    clientKeyExchange\<^sub>t\<^sub>r\<^sub>m,
    changeCipher\<^sub>t\<^sub>r\<^sub>m,
    finished\<^sub>t\<^sub>r\<^sub>m
]"


subsection \<open>Theorem: The TLS handshake protocol is type-flaw resistant\<close>
theorem "tm.tfr\<^sub>s\<^sub>e\<^sub>t (set M\<^sub>T\<^sub>L\<^sub>S)"
by (rule tm.tfr\<^sub>s\<^sub>e\<^sub>t_if_comp_tfr\<^sub>s\<^sub>e\<^sub>t') eval

end
