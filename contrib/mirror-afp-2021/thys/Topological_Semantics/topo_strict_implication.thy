theory topo_strict_implication
  imports topo_frontier_algebra
begin
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)

section \<open>Strict implication\<close>

text\<open>\noindent{We can also employ the closure and interior operations to define different sorts of implications.
In this section we preliminary explore a sort of strict implication and check some relevant properties.}\<close>

text\<open>\noindent{A 'strict' implication should entail the classical one. Hence we define it using the interior operator.}\<close>
definition imp_I::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infix "\<^bold>\<Rightarrow>" 51) where "\<alpha> \<^bold>\<Rightarrow> \<beta> \<equiv> \<I>(\<alpha> \<^bold>\<rightarrow> \<beta>)"
abbreviation imp_I'::"\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infix "\<^bold>\<Leftarrow>" 51) where "\<beta> \<^bold>\<Leftarrow> \<alpha> \<equiv> \<alpha> \<^bold>\<Rightarrow> \<beta>"
declare imp_I_def[conn]

lemma imp_rel: "\<forall>a b. a \<^bold>\<Rightarrow> b \<^bold>\<preceq> a \<^bold>\<rightarrow> b" by (simp add: Int_fr_def conn)

text\<open>\noindent{Under appropriate conditions this implication satisfies a weak variant of the deduction theorem (DT),}\<close>
lemma DTw1: "\<forall>a b. a \<^bold>\<Rightarrow> b \<^bold>\<approx> \<^bold>\<top> \<longrightarrow> a \<^bold>\<preceq> b" by (simp add: Int_fr_def conn)
lemma DTw2: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b.  a \<^bold>\<preceq> b \<longrightarrow> a \<^bold>\<Rightarrow> b \<^bold>\<approx> \<^bold>\<top>" using IF3 dNOR_def unfolding conn by auto
text\<open>\noindent{and a variant of modus ponens and modus tollens resp.}\<close>
lemma MP: "\<forall>a b. a \<^bold>\<and> (a \<^bold>\<Rightarrow> b) \<^bold>\<preceq> b" by (simp add: Int_fr_def conn)
lemma MT: "\<forall>a b. (a \<^bold>\<Rightarrow> b) \<^bold>\<and> \<^bold>\<midarrow>b \<^bold>\<preceq> \<^bold>\<midarrow>a" using MP conn by auto

text\<open>\noindent{However the full DT (actually right-to-left: implication introduction) is not valid.}\<close>
lemma DT1: "\<forall>a b X. X \<^bold>\<preceq> a \<^bold>\<Rightarrow> b \<longrightarrow> X \<^bold>\<and> a \<^bold>\<preceq> b" by (simp add: Int_fr_def conn)
lemma DT2: "\<FF> \<F> \<Longrightarrow> \<forall>a b X. X \<^bold>\<and> a \<^bold>\<preceq> b \<longrightarrow> X \<^bold>\<preceq> a \<^bold>\<Rightarrow> b" nitpick oops (*counterexample*)

text\<open>\noindent{This implication has thus a sort of 'relevant' behaviour. For instance, the following are not valid:}\<close>
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> (b \<^bold>\<Rightarrow> a)) \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*counterexample*)
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> ((a \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> b)) \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*counterexample*)
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> b) \<^bold>\<or> (b \<^bold>\<Rightarrow> c) \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*counterexample*)
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b. ((a \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> a) \<^bold>\<Rightarrow> a \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*counterexample*) 

text\<open>\noindent{In contrast the properties below are valid for appropriate conditions.}\<close>
lemma iprop0: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a. a \<^bold>\<Rightarrow> a \<^bold>\<approx> \<^bold>\<top>" using DTw2 pI2 by fastforce
lemma iprop1: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b. a \<^bold>\<and> (a \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> b  \<^bold>\<approx> \<^bold>\<top>" using DTw2 pI2 unfolding conn by fastforce
lemma iprop2: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b. a \<^bold>\<Rightarrow> (b \<^bold>\<Rightarrow> b) \<^bold>\<approx> \<^bold>\<top>" using DTw2 pI2 unfolding conn by fastforce
lemma iprop3: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b. ((a \<^bold>\<Rightarrow> a) \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> b \<^bold>\<approx> \<^bold>\<top>" using DTw2 pI2 unfolding conn by fastforce
lemma iprop4: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<and> b) \<^bold>\<Rightarrow> a \<^bold>\<approx> \<^bold>\<top>" using DTw2 pI2 unfolding conn by fastforce
lemma iprop5: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b. a \<^bold>\<Rightarrow> (a \<^bold>\<or> b) \<^bold>\<approx> \<^bold>\<top>" using DTw2 pI2 unfolding conn by fastforce
lemma iprop6a: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<and> (b \<^bold>\<or> c)) \<^bold>\<Rightarrow> ((a \<^bold>\<and> b) \<^bold>\<or> (a \<^bold>\<and> c)) \<^bold>\<approx> \<^bold>\<top>" using DTw2 pI2 unfolding conn by fastforce
lemma iprop6b: "Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<and> (b \<^bold>\<or> c)) \<^bold>\<Leftarrow> ((a \<^bold>\<and> b) \<^bold>\<or> (a \<^bold>\<and> c)) \<^bold>\<approx> \<^bold>\<top>" using DTw2 unfolding conn by fastforce

lemma iprop7': "Fr_1 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> b) \<^bold>\<and> (b \<^bold>\<Rightarrow> c) \<^bold>\<preceq> (a \<^bold>\<Rightarrow> c)" proof -
 assume fr1: "Fr_1 \<F>"
  { fix a b c
    have "(a \<^bold>\<rightarrow> b) \<^bold>\<and> (b \<^bold>\<rightarrow> c) \<^bold>\<preceq> (a \<^bold>\<rightarrow> c)" unfolding conn by simp
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> (b \<^bold>\<rightarrow> c)) \<^bold>\<preceq> \<I>(a \<^bold>\<rightarrow> c)" using MONO_def PF1 fr1 monI by simp 
    moreover from fr1 have "let A=(a \<^bold>\<rightarrow> b); B=(b \<^bold>\<rightarrow> c) in  \<I>(A \<^bold>\<and> B) \<^bold>\<approx> \<I> A \<^bold>\<and> \<I> B" using IF1 MULT_def by simp
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<I>(b \<^bold>\<rightarrow> c) \<^bold>\<preceq> \<I>(a \<^bold>\<rightarrow> c)" unfolding conn by simp
  } thus ?thesis unfolding conn by blast
qed
lemma iprop7: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. ((a \<^bold>\<Rightarrow> b) \<^bold>\<and> (b \<^bold>\<Rightarrow> c)) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> c) \<^bold>\<approx> \<^bold>\<top>" by (simp add: DTw2 iprop7')

lemma iprop8a': "Fr_1 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> b) \<^bold>\<and> (a \<^bold>\<Rightarrow> c) \<^bold>\<preceq> a \<^bold>\<Rightarrow> (b \<^bold>\<and> c)" proof -
  assume fr1: "Fr_1 \<F>"
  { fix a b c
    have "(a \<^bold>\<rightarrow> b) \<^bold>\<and> (a \<^bold>\<rightarrow> c) \<^bold>\<preceq> (a \<^bold>\<rightarrow> (b \<^bold>\<and> c))" unfolding conn by simp
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> (a \<^bold>\<rightarrow> c)) \<^bold>\<preceq> \<I>(a \<^bold>\<rightarrow> (b \<^bold>\<and> c))" using MONO_def PF1 fr1 monI by simp
    moreover from fr1 have "let A=(a \<^bold>\<rightarrow> b); B=(a \<^bold>\<rightarrow> c) in  \<I>(A \<^bold>\<and> B) \<^bold>\<approx> \<I> A \<^bold>\<and> \<I> B" using IF1 MULT_def by simp
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<I>(a \<^bold>\<rightarrow> c) \<^bold>\<preceq> \<I>(a \<^bold>\<rightarrow> (b \<^bold>\<and> c))" unfolding conn by simp
  } thus ?thesis unfolding conn by simp
qed
lemma iprop8b': "Fr_1b \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> b) \<^bold>\<and> (a \<^bold>\<Rightarrow> c) \<^bold>\<succeq> a \<^bold>\<Rightarrow> (b \<^bold>\<and> c)" by (smt MONO_def monI conn)
lemma iprop8a: "Fr_1 \<F>  \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. ((a \<^bold>\<Rightarrow> b) \<^bold>\<and> (a \<^bold>\<Rightarrow> c)) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> (b \<^bold>\<and> c)) \<^bold>\<approx> \<^bold>\<top>" by (simp add: DTw2 iprop8a')
lemma iprop8b: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. ((a \<^bold>\<Rightarrow> b) \<^bold>\<and> (a \<^bold>\<Rightarrow> c)) \<^bold>\<Leftarrow> (a \<^bold>\<Rightarrow> (b \<^bold>\<and> c)) \<^bold>\<approx> \<^bold>\<top>" by (simp add: DTw2 iprop8b')

lemma iprop9a': "Fr_1 \<F> \<Longrightarrow> \<forall>a b c. ((a \<^bold>\<Rightarrow> b) \<^bold>\<and> (c \<^bold>\<Rightarrow> b)) \<^bold>\<preceq> ((a \<^bold>\<or> c) \<^bold>\<Rightarrow> b)" proof -
  assume fr1: "Fr_1 \<F>"
  { fix a b c
    have "(a \<^bold>\<rightarrow> b) \<^bold>\<and> (c \<^bold>\<rightarrow> b) \<^bold>\<preceq> (a \<^bold>\<or> c) \<^bold>\<rightarrow> b" unfolding conn by simp
    hence "\<I>((a \<^bold>\<rightarrow> b) \<^bold>\<and> (c \<^bold>\<rightarrow> b)) \<^bold>\<preceq> \<I>((a \<^bold>\<or> c) \<^bold>\<rightarrow> b)" using MONO_def PF1 fr1 monI by simp
    moreover from fr1 have "let A=(a \<^bold>\<rightarrow> b); B=(c \<^bold>\<rightarrow> b) in  \<I>(A \<^bold>\<and> B) \<^bold>\<approx> \<I> A \<^bold>\<and> \<I> B" using IF1 MULT_def by simp
    ultimately have "\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<and> \<I>(c \<^bold>\<rightarrow> b) \<^bold>\<preceq> \<I>((a \<^bold>\<or> c) \<^bold>\<rightarrow> b)" unfolding conn by simp
  } thus ?thesis unfolding conn by simp
qed
lemma iprop9b': "Fr_1b \<F> \<Longrightarrow> \<forall>a b c. ((a \<^bold>\<Rightarrow> b) \<^bold>\<and> (c \<^bold>\<Rightarrow> b)) \<^bold>\<succeq> ((a \<^bold>\<or> c) \<^bold>\<Rightarrow> b)" by (smt MONO_def monI conn)
lemma iprop9a: "Fr_1 \<F>  \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. ((a \<^bold>\<Rightarrow> b) \<^bold>\<and> (c \<^bold>\<Rightarrow> b)) \<^bold>\<Rightarrow> ((a \<^bold>\<or> c) \<^bold>\<Rightarrow> b) \<^bold>\<approx> \<^bold>\<top>" by (simp add: DTw2 iprop9a')
lemma iprop9b: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. ((a \<^bold>\<Rightarrow> b) \<^bold>\<and> (c \<^bold>\<Rightarrow> b)) \<^bold>\<Leftarrow> ((a \<^bold>\<or> c) \<^bold>\<Rightarrow> b) \<^bold>\<approx> \<^bold>\<top>" by (simp add: DTw2 iprop9b')

lemma iprop10': "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>a b c. a \<^bold>\<Rightarrow> (b \<^bold>\<Rightarrow> c) \<^bold>\<preceq> (a \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> c)" proof -
  assume fr1: "Fr_1 \<F>" and fr2: "Fr_2 \<F>" and fr4: "Fr_4 \<F>"
  { fix a b c
    have "a \<^bold>\<rightarrow> (b \<^bold>\<rightarrow> c) \<^bold>\<preceq> (a \<^bold>\<rightarrow> b) \<^bold>\<rightarrow> (a \<^bold>\<rightarrow> c)" unfolding conn by simp
    hence "a \<^bold>\<rightarrow> (b \<^bold>\<Rightarrow> c) \<^bold>\<preceq> (a \<^bold>\<rightarrow> b) \<^bold>\<rightarrow> (a \<^bold>\<rightarrow> c)" using Int_fr_def conn by auto
    hence "\<I>(a \<^bold>\<rightarrow> (b \<^bold>\<Rightarrow> c)) \<^bold>\<preceq> \<I>((a \<^bold>\<rightarrow> b) \<^bold>\<rightarrow> (a \<^bold>\<rightarrow> c))" using MONO_def PF1 fr1 monI by simp
    moreover from fr1 have "let A=(a \<^bold>\<rightarrow> b); B=(a \<^bold>\<rightarrow> c) in \<I>(A \<^bold>\<rightarrow> B) \<^bold>\<preceq> \<I> A \<^bold>\<rightarrow> \<I> B" using IF1 Int_7_def PI7 by auto
    ultimately have "\<I>(a \<^bold>\<rightarrow> (b \<^bold>\<Rightarrow> c)) \<^bold>\<preceq> \<I>(a \<^bold>\<rightarrow> b) \<^bold>\<rightarrow> \<I>(a \<^bold>\<rightarrow> c)" by (metis (full_types))
    hence "\<I>(\<I>(a \<^bold>\<rightarrow> (b \<^bold>\<Rightarrow> c))) \<^bold>\<preceq> \<I>(\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<rightarrow> \<I>(a \<^bold>\<rightarrow> c))" using MONO_def PF1 fr1 monI by simp
    hence "\<I>(a \<^bold>\<rightarrow> (b \<^bold>\<Rightarrow> c)) \<^bold>\<preceq> \<I>(\<I>(a \<^bold>\<rightarrow> b) \<^bold>\<rightarrow> \<I>(a \<^bold>\<rightarrow> c))" using Int_Open PF1 fr1 fr2 fr4 by blast
    hence "(a \<^bold>\<Rightarrow> (b \<^bold>\<Rightarrow> c)) \<^bold>\<preceq> (a \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> c)" using Int_Open PF1 fr1 fr2 fr4 unfolding conn by blast
  } thus ?thesis by blast
qed
lemma iprop10: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> (b \<^bold>\<Rightarrow> c)) \<^bold>\<Rightarrow> ((a \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> c)) \<^bold>\<approx> \<^bold>\<top>" by (simp add: DTw2 iprop10')
lemma "\<FF> \<F> \<Longrightarrow> \<forall>a b c. a \<^bold>\<Rightarrow> (b \<^bold>\<Rightarrow> c) \<^bold>\<succeq> (a \<^bold>\<Rightarrow> b) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> c)" nitpick oops (*counterexample*)

lemma iprop11a': "Fr_1 \<F> \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> b)) \<^bold>\<preceq> (a \<^bold>\<Rightarrow> b)" by (smt MONO_def PF1 imp_rel monI conn)
lemma iprop11b': "\<FF> \<F>    \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> b)) \<^bold>\<succeq> (a \<^bold>\<Rightarrow> b)" unfolding PF1 by (metis Int_Open MONO_def imp_I_def impl_def monI)
lemma iprop11a: "Fr_1 \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F>  \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> b)) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> b) \<^bold>\<approx> \<^bold>\<top>" using DTw2 iprop11a' by blast
lemma iprop11b: "\<FF> \<F>                            \<Longrightarrow> \<forall>a b. (a \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> b)) \<^bold>\<Leftarrow> (a \<^bold>\<Rightarrow> b) \<^bold>\<approx> \<^bold>\<top>" using DTw2 iprop11b' by blast

text\<open>\noindent{In particular, 'strenghening the antecedent' is valid only under certain conditions:}\<close>
lemma SA':"Fr_1b \<F>                        \<Longrightarrow> \<forall>a b c.  a \<^bold>\<Rightarrow> c  \<^bold>\<preceq>  (a \<^bold>\<and> b) \<^bold>\<Rightarrow> c" by (smt MONO_def monI conn)
lemma SA: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> c) \<^bold>\<Rightarrow> ((a \<^bold>\<and> b) \<^bold>\<Rightarrow> c) \<^bold>\<approx> \<^bold>\<top>" using SA' using DTw2 by fastforce 
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>a b c.  a \<^bold>\<Rightarrow> c  \<^bold>\<preceq>  (a \<^bold>\<and> b) \<^bold>\<Rightarrow> c" nitpick oops (*counterexample*)
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> c) \<^bold>\<Rightarrow> ((a \<^bold>\<and> b) \<^bold>\<Rightarrow> c) \<^bold>\<approx> \<^bold>\<top>" nitpick oops  (*counterexample*)

text\<open>\noindent{Similarly, 'weakening the consequent' is valid only under certain conditions.}\<close>
lemma WC':"Fr_1b \<F> \<Longrightarrow>                        \<forall>a b c.  a \<^bold>\<Rightarrow> c  \<^bold>\<preceq>  a \<^bold>\<Rightarrow> (c \<^bold>\<or> b)" by (smt MONO_def monI conn)
lemma WC: "Fr_1b \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> c) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> (c \<^bold>\<or> b)) \<^bold>\<approx> \<^bold>\<top>" using DTw2 WC' by fastforce
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>a b c.  a \<^bold>\<Rightarrow> c  \<^bold>\<preceq>  a \<^bold>\<Rightarrow> (c \<^bold>\<or> b)" nitpick oops (*counterexample*)
lemma "Fr_1a \<F> \<Longrightarrow> Fr_2 \<F> \<Longrightarrow> Fr_3 \<F> \<Longrightarrow> Fr_4 \<F> \<Longrightarrow> \<forall>a b c. (a \<^bold>\<Rightarrow> c) \<^bold>\<Rightarrow> (a \<^bold>\<Rightarrow> (c \<^bold>\<or> b)) \<^bold>\<approx> \<^bold>\<top>" nitpick oops (*counterexample*)

end
