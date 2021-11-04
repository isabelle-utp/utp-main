theory sse_boolean_algebra_quantification
  imports sse_boolean_algebra
begin
hide_const(open) List.list.Nil no_notation List.list.Nil ("[]")  (*We have no use for lists... *)
hide_const(open) Relation.converse no_notation Relation.converse ("(_\<inverse>)" [1000] 999) (*..nor for relations in this work*)
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)


subsection \<open>Obtaining a complete Boolean Algebra\<close>

text\<open>\noindent{Our aim is to obtain a complete Boolean algebra which we can use to interpret
quantified formulas (in the spirit of Boolean-valued models for set theory).}\<close>

text\<open>\noindent{We start by defining infinite meet (infimum) and infinite join (supremum) operations,}\<close>
definition infimum:: "(\<sigma>\<Rightarrow>bool)\<Rightarrow>\<sigma>" ("\<^bold>\<And>_") where "\<^bold>\<And>S \<equiv> \<lambda>w. \<forall>X. S X \<longrightarrow> X w"
definition supremum::"(\<sigma>\<Rightarrow>bool)\<Rightarrow>\<sigma>" ("\<^bold>\<Or>_") where "\<^bold>\<Or>S \<equiv> \<lambda>w. \<exists>X. S X  \<and>  X w"

text\<open>\noindent{and show that the corresponding lattice is complete.}\<close>
abbreviation "upper_bound U S \<equiv> \<forall>X. (S X) \<longrightarrow> X \<^bold>\<preceq> U"
abbreviation "lower_bound L S \<equiv> \<forall>X. (S X) \<longrightarrow> L \<^bold>\<preceq> X"
abbreviation "is_supremum U S \<equiv> upper_bound U S \<and> (\<forall>X. upper_bound X S \<longrightarrow> U \<^bold>\<preceq> X)"
abbreviation "is_infimum  L S \<equiv> lower_bound L S \<and> (\<forall>X. lower_bound X S \<longrightarrow> X \<^bold>\<preceq> L)"

lemma sup_char: "is_supremum \<^bold>\<Or>S S" unfolding supremum_def by auto
lemma sup_ext: "\<forall>S. \<exists>X. is_supremum X S" by (metis supremum_def)
lemma inf_char: "is_infimum \<^bold>\<And>S S" unfolding infimum_def by auto
lemma inf_ext: "\<forall>S. \<exists>X. is_infimum X S" by (metis infimum_def)

text\<open>\noindent{We can check that being closed under supremum/infimum entails being closed under join/meet.}\<close>
abbreviation "meet_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)"
abbreviation "join_closed S \<equiv>  \<forall>X Y. (S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)"

abbreviation "nonEmpty S \<equiv> \<exists>x. S x"
abbreviation "contains S D \<equiv>  \<forall>X. D X \<longrightarrow> S X"
abbreviation "infimum_closed S  \<equiv> \<forall>D. nonEmpty D \<and> contains S D \<longrightarrow> S(\<^bold>\<And>D)"
abbreviation "supremum_closed S \<equiv> \<forall>D. nonEmpty D \<and> contains S D \<longrightarrow> S(\<^bold>\<Or>D)"

lemma inf_meet_closed: "\<forall>S. infimum_closed S \<longrightarrow> meet_closed S" proof -
  { fix S
    { assume inf_closed: "infimum_closed S"
      hence "meet_closed S" proof -
        { fix X::"\<sigma>" and Y::"\<sigma>"
          let ?D="\<lambda>Z. Z=X \<or> Z=Y"
          { assume "S X \<and> S Y"
            hence "contains S ?D" by simp
            moreover have "nonEmpty ?D" by auto
            ultimately have "S(\<^bold>\<And>?D)" using inf_closed by simp
            hence "S(\<lambda>w. \<forall>Z. (Z=X \<or> Z=Y) \<longrightarrow> Z w)" unfolding infimum_def by simp
            moreover have "(\<lambda>w. \<forall>Z. (Z=X \<or> Z=Y) \<longrightarrow> Z w) = (\<lambda>w. X w \<and> Y w)" by auto
            ultimately have "S(\<lambda>w. X w \<and> Y w)" by simp
          } hence "(S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<and> Y)" unfolding conn by (rule impI)
        } thus ?thesis by simp  qed
    } hence "infimum_closed S \<longrightarrow> meet_closed S" by simp
  } thus ?thesis by (rule allI)
qed
lemma sup_join_closed: "\<forall>P. supremum_closed P \<longrightarrow> join_closed P" proof -
  { fix S
    { assume sup_closed: "supremum_closed S"
      hence "join_closed S" proof -
        { fix X::"\<sigma>" and Y::"\<sigma>"
          let ?D="\<lambda>Z. Z=X \<or> Z=Y"
          { assume "S X \<and> S Y"
            hence "contains S ?D" by simp
            moreover have "nonEmpty ?D" by auto
            ultimately have "S(\<^bold>\<Or>?D)" using sup_closed by simp
            hence "S(\<lambda>w. \<exists>Z. (Z=X \<or> Z=Y) \<and> Z w)" unfolding supremum_def by simp
            moreover have "(\<lambda>w. \<exists>Z. (Z=X \<or> Z=Y) \<and> Z w) = (\<lambda>w. X w \<or> Y w)" by auto
            ultimately have "S(\<lambda>w. X w \<or> Y w)" by simp
          } hence "(S X \<and> S Y) \<longrightarrow> S(X \<^bold>\<or> Y)" unfolding conn by (rule impI)
        } thus ?thesis by simp qed
    } hence "supremum_closed S \<longrightarrow> join_closed S" by simp
  } thus ?thesis by (rule allI)
qed


subsection \<open>Adding quantifiers (restricted and unrestricted)\<close>

text\<open>\noindent{We can harness HOL to define quantification over individuals of arbitrary type (using polymorphism).
These (unrestricted) quantifiers take a propositional function and give a proposition.}\<close>  
abbreviation mforall::"('t\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>_" [55]56) where "\<^bold>\<forall>\<pi> \<equiv> \<lambda>w. \<forall>X. (\<pi> X) w"
abbreviation mexists::"('t\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>_" [55]56) where "\<^bold>\<exists>\<pi> \<equiv> \<lambda>w. \<exists>X. (\<pi> X) w"
text\<open>\noindent{To improve readability, we introduce for them an useful binder notation.}\<close>
abbreviation mforallB (binder"\<^bold>\<forall>"[55]56) where "\<^bold>\<forall>X. \<pi> X \<equiv> \<^bold>\<forall>\<pi>"
abbreviation mexistsB (binder"\<^bold>\<exists>"[55]56) where "\<^bold>\<exists>X. \<pi> X \<equiv> \<^bold>\<exists>\<pi>"

(*TODO: is it possible to also add binder notation to the ones below?*)
text\<open>\noindent{Moreover, we define restricted quantifiers which take a 'functional domain' as additional parameter.
The latter is a propositional function that maps each element 'e' to the proposition 'e exists'.}\<close>
abbreviation mforall_restr::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>\<^sup>R(_)_") where "\<^bold>\<forall>\<^sup>R(\<delta>)\<pi> \<equiv> \<lambda>w.\<forall>X. (\<delta> X) w \<longrightarrow> (\<pi> X) w" 
abbreviation mexists_restr::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>\<^sup>R(_)_") where "\<^bold>\<exists>\<^sup>R(\<delta>)\<pi> \<equiv> \<lambda>w.\<exists>X. (\<delta> X) w  \<and>  (\<pi> X) w"


subsection \<open>Relating quantifiers with further operators\<close>

text\<open>\noindent{The following 'type-lifting' function is useful for converting sets into 'rigid' propositional functions.}\<close>
abbreviation lift_conv::"('t\<Rightarrow>bool)\<Rightarrow>('t\<Rightarrow>\<sigma>)" ("\<lparr>_\<rparr>") where "\<lparr>S\<rparr> \<equiv> \<lambda>X. \<lambda>w. S X"

text\<open>\noindent{We introduce an useful operator: the range of a propositional function (resp. restricted over a domain),}\<close>
definition pfunRange::"('t\<Rightarrow>\<sigma>)\<Rightarrow>(\<sigma>\<Rightarrow>bool)" ("Ra(_)") where "Ra(\<pi>) \<equiv> \<lambda>Y. \<exists>x. (\<pi> x) = Y"
definition pfunRange_restr::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>bool)\<Rightarrow>(\<sigma>\<Rightarrow>bool)" ("Ra[_|_]") where "Ra[\<pi>|D] \<equiv> \<lambda>Y. \<exists>x. (D x) \<and> (\<pi> x) = Y"

text\<open>\noindent{and check that taking infinite joins/meets (suprema/infima) over the range of a propositional function
can be equivalently codified by using quantifiers. This is a quite useful simplifying relationship.}\<close>
lemma Ra_all: "\<^bold>\<And>Ra(\<pi>) = \<^bold>\<forall>\<pi>" by (metis (full_types) infimum_def pfunRange_def)
lemma Ra_ex:  "\<^bold>\<Or>Ra(\<pi>) = \<^bold>\<exists>\<pi>" by (metis (full_types) pfunRange_def supremum_def)
lemma Ra_restr_all: "\<^bold>\<And>Ra[\<pi>|D] = \<^bold>\<forall>\<^sup>R\<lparr>D\<rparr>\<pi>" by (metis (full_types) pfunRange_restr_def infimum_def)
lemma Ra_restr_ex:  "\<^bold>\<Or>Ra[\<pi>|D] = \<^bold>\<exists>\<^sup>R\<lparr>D\<rparr>\<pi>" by (metis pfunRange_restr_def supremum_def)

text\<open>\noindent{We further introduce the positive (negative) restriction of a propositional function wrt. a domain,}\<close>
abbreviation pfunRestr_pos::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)" ("[_|_]\<^sup>P") where "[\<pi>|\<delta>]\<^sup>P \<equiv> \<lambda>X. \<lambda>w. (\<delta> X) w \<longrightarrow> (\<pi> X) w"
abbreviation pfunRestr_neg::"('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)\<Rightarrow>('t\<Rightarrow>\<sigma>)" ("[_|_]\<^sup>N") where "[\<pi>|\<delta>]\<^sup>N \<equiv> \<lambda>X. \<lambda>w. (\<delta> X) w  \<and>  (\<pi> X) w"

text\<open>\noindent{and check that some additional simplifying relationships obtain.}\<close>
lemma all_restr: "\<^bold>\<forall>\<^sup>R(\<delta>)\<pi> = \<^bold>\<forall>[\<pi>|\<delta>]\<^sup>P" by simp
lemma ex_restr:  "\<^bold>\<exists>\<^sup>R(\<delta>)\<pi> = \<^bold>\<exists>[\<pi>|\<delta>]\<^sup>N" by simp
lemma Ra_all_restr: "\<^bold>\<And>Ra[\<pi>|D] = \<^bold>\<forall>[\<pi>|\<lparr>D\<rparr>]\<^sup>P" using Ra_restr_all by blast
lemma Ra_ex_restr:  "\<^bold>\<Or>Ra[\<pi>|D] = \<^bold>\<exists>[\<pi>|\<lparr>D\<rparr>]\<^sup>N" by (simp add: Ra_restr_ex)

text\<open>\noindent{Observe that using these operators has the advantage of allowing for binder notation,}\<close>
lemma "\<^bold>\<forall>X. [\<pi>|\<delta>]\<^sup>P X = \<^bold>\<forall>[\<pi>|\<delta>]\<^sup>P" by simp
lemma "\<^bold>\<exists>X. [\<pi>|\<delta>]\<^sup>N X = \<^bold>\<exists>[\<pi>|\<delta>]\<^sup>N" by simp

text\<open>\noindent{noting that extra care should be taken when working with complements or negations;
always remember to switch P/N (positive/negative restriction) accordingly.}\<close>
lemma "\<^bold>\<forall>\<^sup>R(\<delta>)\<pi>  = \<^bold>\<forall>X.  [\<pi>|\<delta>]\<^sup>P X" by simp
lemma "\<^bold>\<forall>\<^sup>R(\<delta>)\<pi>\<^sup>c = \<^bold>\<forall>X. \<^bold>\<midarrow>[\<pi>|\<delta>]\<^sup>N X" by (simp add: compl_def)
lemma "\<^bold>\<exists>\<^sup>R(\<delta>)\<pi>  = \<^bold>\<exists>X.  [\<pi>|\<delta>]\<^sup>N X" by simp
lemma "\<^bold>\<exists>\<^sup>R(\<delta>)\<pi>\<^sup>c = \<^bold>\<exists>X. \<^bold>\<midarrow>[\<pi>|\<delta>]\<^sup>P X" by (simp add: compl_def)

text\<open>\noindent{The previous definitions allow us to nicely characterize the interaction
between function composition and (restricted) quantification:}\<close>
lemma Ra_all_comp1: "\<^bold>\<forall>(\<pi>\<circ>\<gamma>) = \<^bold>\<forall>[\<pi>|\<lparr>Ra \<gamma>\<rparr>]\<^sup>P" by (metis comp_apply pfunRange_def)
lemma Ra_all_comp2: "\<^bold>\<forall>(\<pi>\<circ>\<gamma>) = \<^bold>\<forall>\<^sup>R\<lparr>Ra \<gamma>\<rparr> \<pi>" by (metis comp_apply pfunRange_def)
lemma Ra_ex_comp1:  "\<^bold>\<exists>(\<pi>\<circ>\<gamma>) = \<^bold>\<exists>[\<pi>|\<lparr>Ra \<gamma>\<rparr>]\<^sup>N" by (metis comp_apply pfunRange_def)
lemma Ra_ex_comp2:  "\<^bold>\<exists>(\<pi>\<circ>\<gamma>) = \<^bold>\<exists>\<^sup>R\<lparr>Ra \<gamma>\<rparr> \<pi>" by (metis comp_apply pfunRange_def)

text\<open>\noindent{This useful operator returns for a given domain of propositions the domain of their complements:}\<close>
definition dom_compl::"(\<sigma>\<Rightarrow>bool)\<Rightarrow>(\<sigma>\<Rightarrow>bool)" ("(_\<inverse>)") where "D\<inverse> \<equiv> \<lambda>X. \<exists>Y. (D Y) \<and> (X = \<^bold>\<midarrow>Y)"
lemma dom_compl_def2: "D\<inverse> = (\<lambda>X. D(\<^bold>\<midarrow>X))" unfolding dom_compl_def by (metis comp_symm fun_upd_same)
lemma dom_compl_invol: "D = (D\<inverse>)\<inverse>" unfolding dom_compl_def by (metis comp_symm fun_upd_same)

text\<open>\noindent{We can now check an infinite variant of the De Morgan laws,}\<close>
lemma iDM_a: "\<^bold>\<midarrow>(\<^bold>\<And>S) = \<^bold>\<Or>S\<inverse>" unfolding dom_compl_def2 infimum_def supremum_def using compl_def by force
lemma iDM_b:" \<^bold>\<midarrow>(\<^bold>\<Or>S) = \<^bold>\<And>S\<inverse>" unfolding dom_compl_def2 infimum_def supremum_def using compl_def by force

text\<open>\noindent{and some useful dualities regarding the range of propositional functions (restricted wrt. a domain).}\<close>
lemma Ra_compl: "Ra[\<pi>\<^sup>c|D]  = Ra[\<pi>|D]\<inverse>" unfolding pfunRange_restr_def dom_compl_def by auto
lemma Ra_dual1: "Ra[\<pi>\<^sup>d|D]  = Ra[\<pi>|D\<inverse>]\<inverse>" unfolding pfunRange_restr_def dom_compl_def using dual_def by auto
lemma Ra_dual2: "Ra[\<pi>\<^sup>d|D]  = Ra[\<pi>\<^sup>c|D\<inverse>]" unfolding pfunRange_restr_def dom_compl_def using dual_def by auto
lemma Ra_dual3: "Ra[\<pi>\<^sup>d|D]\<inverse> = Ra[\<pi>|D\<inverse>]" unfolding pfunRange_restr_def dom_compl_def using dual_def comp_symm by metis
lemma Ra_dual4: "Ra[\<pi>\<^sup>d|D\<inverse>] = Ra[\<pi>|D]\<inverse>" using Ra_dual3 dual_symm by metis

text\<open>\noindent{Finally, we check some facts concerning duality for quantifiers.}\<close>
lemma "\<^bold>\<exists>\<pi>\<^sup>c = \<^bold>\<midarrow>(\<^bold>\<forall>\<pi>)" using compl_def by auto
lemma "\<^bold>\<forall>\<pi>\<^sup>c = \<^bold>\<midarrow>(\<^bold>\<exists>\<pi>)" using compl_def by auto
lemma "\<^bold>\<exists>X. \<^bold>\<midarrow>\<pi> X = \<^bold>\<midarrow>(\<^bold>\<forall>X. \<pi> X)" using compl_def by auto
lemma "\<^bold>\<forall>X. \<^bold>\<midarrow>\<pi> X = \<^bold>\<midarrow>(\<^bold>\<exists>X. \<pi> X)" using compl_def by auto

lemma "\<^bold>\<exists>\<^sup>R(\<delta>)\<pi>\<^sup>c = \<^bold>\<midarrow>(\<^bold>\<forall>\<^sup>R(\<delta>)\<pi>)" using compl_def by auto
lemma "\<^bold>\<forall>\<^sup>R(\<delta>)\<pi>\<^sup>c = \<^bold>\<midarrow>(\<^bold>\<exists>\<^sup>R(\<delta>)\<pi>)" using compl_def by auto
lemma "\<^bold>\<exists>X. \<^bold>\<midarrow>[\<pi>|\<delta>]\<^sup>P X = \<^bold>\<midarrow>(\<^bold>\<forall>X. [\<pi>|\<delta>]\<^sup>P X)" using compl_def by auto
lemma "\<^bold>\<forall>X. \<^bold>\<midarrow>[\<pi>|\<delta>]\<^sup>P X = \<^bold>\<midarrow>(\<^bold>\<exists>X. [\<pi>|\<delta>]\<^sup>P X)" using compl_def by auto
lemma "\<^bold>\<exists>X. \<^bold>\<midarrow>[\<pi>|\<delta>]\<^sup>N X = \<^bold>\<midarrow>(\<^bold>\<forall>X. [\<pi>|\<delta>]\<^sup>N X)" using compl_def by auto
lemma "\<^bold>\<forall>X. \<^bold>\<midarrow>[\<pi>|\<delta>]\<^sup>N X = \<^bold>\<midarrow>(\<^bold>\<exists>X. [\<pi>|\<delta>]\<^sup>N X)" using compl_def by auto

text\<open>\noindent{Warning: Do not switch P and N when passing to the dual form.}\<close>
lemma "\<^bold>\<forall>X. [\<pi>|\<delta>]\<^sup>P X = \<^bold>\<midarrow>(\<^bold>\<exists>X. \<^bold>\<midarrow>[\<pi>|\<delta>]\<^sup>N X)" nitpick oops \<comment>\<open> wrong: counterexample \<close>
lemma "\<^bold>\<forall>X. [\<pi>|\<delta>]\<^sup>P X = \<^bold>\<midarrow>(\<^bold>\<exists>X. \<^bold>\<midarrow>[\<pi>|\<delta>]\<^sup>P X)" using compl_def by auto \<comment>\<open> correct \<close>

end
