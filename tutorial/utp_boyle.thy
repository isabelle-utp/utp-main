section {* Example UTP theory: Boyle's laws *}
(*<*)
theory utp_boyle
imports "../utp/utp_theory"
begin
(*>*)

text {* In order to exemplify the use of Isabelle/UTP, we mechanise a simple theory representing
        Boyle's law. Boyle's law states that, for an ideal gas at fixed temperature, pressure @{term p} is inversely
        proportional to volume @{term V}, or more formally that for @{term "k = p*V"} is invariant, for
        constant @{term k}. We here encode this as a simple UTP theory. We first create a record to
        represent the alphabet of the theory consisting of the three variables \emph{k}, \emph{p}
        and \emph{V}. *}

alphabet boyle =
  k :: real
  p :: real
  V :: real

type_synonym boyle_rel = "boyle hrel"

declare boyle.splits [alpha_splits]

text {*
  The two locale interpretations below are a technicality to improve automatic
  proof support via the predicate and relational tactics. This is to enable the
  (re-)interpretation of state spaces to remove any occurrences of lens types
  after the proof tactics @{method pred_simp} and @{method rel_simp}, or any
  of their derivatives have been applied. Eventually, it would be desirable to
  automate both interpretations as part of a custom outer command for defining
  alphabets.
*}

interpretation boyle_prd: -- {* Closed records are sufficient here. *}
  lens_interp "\<lambda>r::boyle. (k\<^sub>v r, p\<^sub>v r, V\<^sub>v r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation boyle_rel: -- {* Closed records are sufficient here. *}
  lens_interp "\<lambda>(r::boyle, r'::boyle).
    (k\<^sub>v r, k\<^sub>v r', p\<^sub>v r, p\<^sub>v r', V\<^sub>v r, V\<^sub>v r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

lemma boyle_var_ords [usubst]:
  "k \<prec>\<^sub>v p" "p \<prec>\<^sub>v V"
  by (simp_all add: var_name_ord_def)

subsection {* Static invariant *}

text {* We first create a simple UTP theory representing Boyle's laws on a single state, as a static
        invariant healthiness condition. We state Boyle's law using the function \emph{B}, which recalculates
        the value of the constant @{term k} based on @{term p} and @{term V}. *}

definition "B(\<phi>) = ((\<exists> k \<bullet> \<phi>) \<and> (&k =\<^sub>u &p*&V))"
(*<*)
declare B_def [upred_defs]
(*>*)

text {* \noindent We can then prove that B is both idempotent and monotone simply by application of
        the predicate tactic. Idempotence means that healthy predicates cannot be made
        more healthy. Together with idempotence, monotonicity ensures that image of the healthiness functions
        forms a complete lattice, which is useful to allow the representation of recursive and
        iterative constructions with the theory. *}

lemma B_idempotent: "B(B(P)) = B(P)"
  by pred_auto

lemma B_monotone: "X \<sqsubseteq> Y \<Longrightarrow> B(X) \<sqsubseteq> B(Y)"
  by pred_blast

text {* We also create some example observations; the first (@{term "\<phi>\<^sub>1"}) satisfies Boyle's law and
        the second doesn't (@{term "\<phi>\<^sub>2"}). *}

definition(*<*)[upred_defs]:(*>*) "\<phi>\<^sub>1 = ((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 50))"
definition(*<*)[upred_defs]:(*>*) "\<phi>\<^sub>2 = ((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 100))"

text {* We first prove an obvious property: that these two predicates are different observations. We must
        show that there exists a valuation of one which is not of the other. This is achieved through
        application of \emph{pred-tac}, followed by \emph{sledgehammer}~\cite{Blanchette2011} which yields a \emph{metis} proof. *}

lemma \<phi>\<^sub>1_diff_\<phi>\<^sub>2: "\<phi>\<^sub>1 \<noteq> \<phi>\<^sub>2"
  by (pred_simp, fastforce)

text {* We prove that @{const "\<phi>\<^sub>1"} satisfies Boyle's law by application of the predicate calculus
        tactic, \emph{pred-tac}. *}

lemma B_\<phi>\<^sub>1: "\<phi>\<^sub>1 is B"
  by (pred_auto)

text {* We prove that @{const "\<phi>\<^sub>2"} does not satisfy Boyle's law by showing that applying \emph{B} to
        it results in @{const "\<phi>\<^sub>1"}. We prove this using Isabelle's natural proof language, Isar. *}

lemma B_\<phi>\<^sub>2: "B(\<phi>\<^sub>2) = \<phi>\<^sub>1"
proof -
  have "B(\<phi>\<^sub>2) = B(&p =\<^sub>u 10 \<and> &V =\<^sub>u 5 \<and> &k =\<^sub>u 100)"
    by (simp add: \<phi>\<^sub>2_def)
  also have "... = ((\<exists> k \<bullet> &p =\<^sub>u 10 \<and> &V =\<^sub>u 5 \<and> &k =\<^sub>u 100) \<and> &k =\<^sub>u &p*&V)"
    by (simp add: B_def)
  also have "... = (&p =\<^sub>u 10 \<and> &V =\<^sub>u 5 \<and> &k =\<^sub>u &p*&V)"
    by pred_auto
  also have "... = (&p =\<^sub>u 10 \<and> &V =\<^sub>u 5 \<and> &k =\<^sub>u 50)"
    by pred_auto
  also have "... = \<phi>\<^sub>1"
    by (simp add: \<phi>\<^sub>1_def)
  finally show ?thesis .
qed

subsection {* Dynamic invariants *}

text {* Next we build a relational theory that allows the pressure and volume to be changed,
        whilst still respecting Boyle's law. We create two dynamic invariants for this purpose. *}

definition "D1(P) = (($k =\<^sub>u $p*$V \<Rightarrow> $k\<acute> =\<^sub>u $p\<acute>*$V\<acute>) \<and> P)"
definition "D2(P) = ($k\<acute> =\<^sub>u $k \<and> P)"
(*<*)
declare D1_def [upred_defs]
declare D2_def [upred_defs]
(*>*)

text {* @{term "D1"} states that if Boyle's law satisfied in the previous state, then it should
        be satisfied in the next state. We define this by conjunction of the formal specification
        of this property with the predicate. The annotations @{term "$p"} and @{term "$p\<acute>"} refer to
        relational variables $p$ and $p'$. @{term "D2"} states that the constant @{term k} indeed
        remains constant throughout the evolution of the system, which is also specified as a conjunctive
        healthiness condition. As before we demonstrate that @{term D1} and @{term D2} are both idempotent
        and monotone. *}

lemma D1_idempotent: "D1(D1(P)) = D1(P)" by rel_auto
lemma D2_idempotent: "D2(D2(P)) = D2(P)" by rel_auto

lemma D1_monotone: "X \<sqsubseteq> Y \<Longrightarrow> D1(X) \<sqsubseteq> D1(Y)" by rel_auto
lemma D2_monotone: "X \<sqsubseteq> Y \<Longrightarrow> D2(X) \<sqsubseteq> D2(Y)" by rel_auto

text {* Since these properties are relational, we discharge them using our relational calculus tactic
        \emph{rel-tac}. Next we specify three operations that make up the signature of the theory. *}

definition InitSys :: "real \<Rightarrow> real \<Rightarrow> boyle_rel" where
  (*<*)[upred_defs]:(*>*) "InitSys ip iV
  = (\<guillemotleft>ip\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>iV\<guillemotright> >\<^sub>u 0)\<^sup>\<top> ;; p,V,k := \<guillemotleft>ip\<guillemotright>,\<guillemotleft>iV\<guillemotright>,(\<guillemotleft>ip\<guillemotright>*\<guillemotleft>iV\<guillemotright>)"

definition ChPres :: "real \<Rightarrow> boyle_rel" where
  (*<*)[upred_defs]:(*>*) "ChPres dp
  = ((&p + \<guillemotleft>dp\<guillemotright> >\<^sub>u 0)\<^sup>\<top> ;; p := &p + \<guillemotleft>dp\<guillemotright> ;; V := (&k/&p))"

definition ChVol :: "real \<Rightarrow> boyle_rel" where
  (*<*)[upred_defs]:(*>*) "ChVol dV
  = ((&V + \<guillemotleft>dV\<guillemotright> >\<^sub>u 0)\<^sup>\<top> ;; V := &V + \<guillemotleft>dV\<guillemotright> ;; p := (&k/&V))"

text {* @{const InitSys} initialises the system with a given initial pressure ($ip$) and volume ($iV$).
        It assumes that both are greater than 0 using the assumption construct @{term "c\<^sup>\<top>"} which equates to @{term II}
        if @{term c} is true and @{term false} (i.e. errant) otherwise. It then creates a state assignment
        for $p$ and $V$, uses the @{term B} healthiness condition to make it healthy (by calculating $k$),
        and finally turns the predicate into a postcondition using the @{term "\<lceil>P\<rceil>\<^sub>>"} function.

        @{const ChPres} raises or lowers the pressure based on an input \emph{dp}. It assumes
        that the resulting pressure change would not result in a zero or negative pressure,
        i.e. $p + dp > 0$. It assigns the updated value to $p$ and recalculates $V$ using the original
        value of $k$. @{const ChVol} is similar but updates the volume.
 *}

lemma D1_InitSystem: "D1 (InitSys ip iV) = InitSys ip iV"
  by rel_auto

text {* @{const InitSys} is @{const D1}, since it establishes the invariant for the system. However,
  it is not @{const D2} since it sets the global value of $k$ and thus can change its value. We can
  however show that both @{const ChPres} and @{const ChVol} are healthy relations. *}

lemma D1: "D1 (ChPres dp) = ChPres dp" and "D1 (ChVol dV) = ChVol dV"
  by (rel_auto, rel_auto)

lemma D2: "D2 (ChPres dp) = ChPres dp" and "D2 (ChVol dV) = ChVol dV"
  by (rel_auto, rel_auto)

text {* Finally we show a calculation a simple animation of Boyle's law, where the initial pressure
  and volume are set to 10 and 4, respectively, and then the pressure is lowered by 2. *}

(* There are some ambiguities warnings below; fix this! [TODO] *)

lemma ChPres_example:
  "(InitSys 10 4 ;; ChPres (-2)) = p,V,k := 8,5,40"
proof -
  -- {* @{const InitSys} yields an assignment to the three variables *}
  have "InitSys 10 4 = p,V,k := 10,4,40"
    by (rel_auto)
  -- {* This assignment becomes a substitution *}
  hence "(InitSys 10 4 ;; ChPres (-2))
          = (ChPres (-2))\<lbrakk>10,4,40/$p,$V,$k\<rbrakk>"
    by (simp add: assigns_r_comp alpha)
  -- {* Unfold definition of @{const ChPres} *}
  also have "... = ((&p - 2 >\<^sub>u 0)\<^sup>\<top>\<lbrakk>10,4,40/$p,$V,$k\<rbrakk>
                        ;; p := &p - 2 ;; V := &k / &p)"
    by (simp add: ChPres_def lit_num_simps usubst unrest)
  -- {* Unfold definition of assumption *}
  also have "... = ((p,V,k := 10,4,40 \<triangleleft> (8 :\<^sub>u real) >\<^sub>u 0 \<triangleright> false)
                        ;; p := &p - 2 ;; V := &k / &p)"
    by (simp add: rassume_def usubst alpha unrest)
  -- {* @{term "8 > 0"} is true; simplify conditional  *}
  also have "... = (p,V,k := 10,4,40 ;; p := &p - 2 ;; V := &k / &p)"
    by rel_auto
  -- {* Application of both assignments *}
  also have "... = p,V,k := 8,5,40"
    by rel_auto
  finally show ?thesis .
qed

hide_const k
hide_const p
hide_const V
hide_const B

(************************)
(* Added by Frank Zeyda *)
(************************)

(*
lemma "(<x::nat> := 1 ;; <x::nat> := &<x::nat> + 1) = <x::nat> := 2"
apply (rel_auto)
apply (simp add: numeral_2_eq_2)
apply (simp add: numeral_2_eq_2)
done

lemma "({x::nat} := 1 ;; {x::nat} := &{x::nat} + 1) = {x::nat} := 2"
apply (rel_auto)
apply (simp add: numeral_2_eq_2)
apply (simp add: numeral_2_eq_2)
done
*)
(*<*)
end
(*>*)