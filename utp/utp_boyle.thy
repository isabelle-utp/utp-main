section {* Example UTP theory: Boyle's laws *}

theory utp_boyle
imports utp_theory
begin

text {* Boyle's law states that k = p * V is invariant. We here encode this as a simple UTP theory.
        We first create a record to represent the alphabet of the theory consisting of the three
        variables k, p and V. *}

record alpha_boyle =
  boyle_k :: real
  boyle_p :: real
  boyle_V :: real

text {* For now we have to explicitly cast the fields to UTP variables using the VAR syntactic
        transformation function -- in future we'd like to automate this. We also have to
        add the definition equations for these variables to the simplification set for predicates
        to enable automated proof through our tactics. *}

definition "k = VAR boyle_k"
definition "p = VAR boyle_p"
definition "V = VAR boyle_V"

declare k_def [upred_defs] and p_def [upred_defs] and V_def [upred_defs]

text {* Next we state Boyle's law using the healthiness condition B and likewise add it to
        the UTP predicate definitional equation set. The syntax differs a little from UTP;
        we try not to override HOL constants and so UTP predicate equality is subscripted.
        Moreover to distinguish variables standing for a predicate (like $\phi$) from variables
        standing for UTP variables we have to prepend the latter with an ampersand. *}

definition "B(\<phi>) = ((\<exists> k \<bullet> \<phi>) \<and> (&k =\<^sub>u &p * &V))"

declare B_def [upred_defs]

text {* We can then prove that B is both idempotent and monotone simply by application of
        the predicate tactic. *}

lemma B_idempotent:
  "B(B(P)) = B(P)"
  by pred_tac

lemma B_monotone:
  "X \<sqsubseteq> Y \<Longrightarrow> B(X) \<sqsubseteq> B(Y)"
  by pred_tac

text {* We also create some example observations; the first satisfies Boyle's law and the second
        doesn't. *}

definition "\<phi>\<^sub>1 = ((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 50))"

definition "\<phi>\<^sub>2 = ((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 100))"

text {* We prove that @{const "\<phi>\<^sub>1"} satisfied by Boyle's law by simplication of its definitional
        equation and then application of the predicate tactic. *}

lemma B_\<phi>\<^sub>1: "\<phi>\<^sub>1 is B"
  by (simp add: \<phi>\<^sub>1_def, pred_tac)

text {* We prove that @{const "\<phi>\<^sub>2"} does not satisfy Boyle's law by showing it's in fact equal
        to @{const "\<phi>\<^sub>1"}. We do this via an automated Isar proof. *}

lemma B_\<phi>\<^sub>2: "B(\<phi>\<^sub>2) = \<phi>\<^sub>1"
proof -
  have "B(\<phi>\<^sub>2) = B((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 100))"
    by (simp add: \<phi>\<^sub>2_def) 
  also have "... = ((\<exists> k \<bullet> (&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 100)) \<and> (&k =\<^sub>u &p * &V))"
    by pred_tac
  also have "... = ((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u &p * &V))"
    by pred_tac
  also have "... = ((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 50))"
    by pred_tac
  also have "... = \<phi>\<^sub>1"
    by (simp add: \<phi>\<^sub>1_def)
  finally show ?thesis .
qed 

end