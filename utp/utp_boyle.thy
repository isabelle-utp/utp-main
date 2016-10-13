section {* Example UTP theory: Boyle's laws *}
(*<*)
theory utp_boyle
imports utp_theory
begin
(*>*)

text {* Boyle's law states that k = p * V is invariant. We here encode this as a simple UTP theory.
        We first create a record to represent the alphabet of the theory consisting of the three
        variables k, p and V. *}

record alpha_boyle =
  boyle_k :: real
  boyle_p :: real
  boyle_V :: real

text {* For now we have to explicitly cast the fields to UTP variables using the VAR syntactic
        transformation function -- in future this will be automated. We also have to
        add the definitional equations for these variables to the simplification set for predicates
        to enable automated proof through our tactics. *}

definition k :: "real \<Longrightarrow> alpha_boyle" where "k = VAR boyle_k"
definition p :: "real \<Longrightarrow> alpha_boyle" where "p = VAR boyle_p"
definition V :: "real \<Longrightarrow> alpha_boyle" where "V = VAR boyle_V"

declare k_def [upred_defs] and p_def [upred_defs] and V_def [upred_defs]

lemma vwb_lens_k [simp]: "vwb_lens k"
  by (unfold_locales, simp_all add: k_def)

lemma vwb_lens_p [simp]: "vwb_lens p"
  by (unfold_locales, simp_all add: p_def)

lemma vwb_lens_V [simp]: "vwb_lens V"
  by (unfold_locales, simp_all add: V_def)

lemma boyle_indeps [simp]:
  "k \<bowtie> p" "p \<bowtie> k" "k \<bowtie> V" "V \<bowtie> k" "p \<bowtie> V" "V \<bowtie> p"
  by (simp_all add: k_def p_def V_def lens_indep_def)

lemma boyle_var_ords [usubst]:
  "k \<prec>\<^sub>v p" "p \<prec>\<^sub>v V"
  by (simp_all add: var_name_ord_def)


text {* Next we state Boyle's law using the healthiness condition B and likewise add it to
        the UTP predicate definitional equation set. The syntax differs a little from UTP;
        we try not to override HOL constants and so UTP predicate equality is subscripted.
        Moreover to distinguish variables denoting a predicate (like $\phi$) from variables
        denoting UTP variables we have to prepend the latter with an ampersand. *}

definition "B(\<phi>) = ((\<exists> k \<bullet> \<phi>) \<and> (&k =\<^sub>u &p * &V))"
declare B_def [upred_defs]

definition "D1(P) = (($k =\<^sub>u $p * $V \<Rightarrow> $k\<acute> =\<^sub>u $p\<acute> * $V\<acute>) \<and> P)"
definition "D2(P) = ($k\<acute> =\<^sub>u $k \<and> P)"

declare D1_def [upred_defs]
declare D2_def [upred_defs]

definition [upred_defs]: "InitSystem ip iV = \<lceil>B(&p =\<^sub>u \<guillemotleft>ip\<guillemotright> \<and> &V =\<^sub>u \<guillemotleft>iV\<guillemotright>)\<rceil>\<^sub>>"
definition [upred_defs]: "ChangePressure dp = ((&p + \<guillemotleft>dp\<guillemotright> >\<^sub>u 0)\<^sup>\<top> ;; p := &p + \<guillemotleft>dp\<guillemotright> ;; V := (&k/&p))"
definition [upred_defs]: "ChangeVolume dV = ((&V + \<guillemotleft>dV\<guillemotright> >\<^sub>u 0)\<^sup>\<top> ;; V := &V + \<guillemotleft>dV\<guillemotright> ;; p := (&k/&V))"

text {* We can then prove that B is both idempotent and monotone simply by application of
        the predicate tactic. *}

lemma B_idempotent: "B(B(P)) = B(P)"
  by pred_tac

lemma D1_idempotent: "D1(D1(P)) = D1(P)"
  by rel_tac

lemma D2_idempotent: "D2(D2(P)) = D2(P)"
  by rel_tac

lemma B_monotone: "X \<sqsubseteq> Y \<Longrightarrow> B(X) \<sqsubseteq> B(Y)"
  by pred_tac

lemma D1_monotone: "X \<sqsubseteq> Y \<Longrightarrow> D1(X) \<sqsubseteq> D1(Y)"
  by rel_tac

lemma D2_monotone: "X \<sqsubseteq> Y \<Longrightarrow> D2(X) \<sqsubseteq> D2(Y)"
  by rel_tac

text {* We also create some example observations; the first satisfies Boyle's law and the second
        doesn't. *}

definition [upred_defs]: "\<phi>\<^sub>1 = ((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 50))"

definition [upred_defs]: "\<phi>\<^sub>2 = ((&p =\<^sub>u 10) \<and> (&V =\<^sub>u 5) \<and> (&k =\<^sub>u 100))"

text {* We prove that @{const "\<phi>\<^sub>1"} satisfied by Boyle's law by simplication of its definitional
        equation and then application of the predicate tactic. *}

lemma B_\<phi>\<^sub>1: "\<phi>\<^sub>1 is B"
  by (pred_tac)

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

lemma D1_ChangePressure: "D1 (ChangePressure dp) = ChangePressure dp"
  by rel_tac
  
lemma D2_ChangePressure: "D2 (ChangePressure dp) = ChangePressure dp"
  by rel_tac

lemma D1_ChangeVolume: "D1 (ChangeVolume dV) = ChangeVolume dV"
  by rel_tac

lemma D2_ChangeVolume: "D2 (ChangeVolume dV) = ChangeVolume dV"
  by rel_tac

lemma ChangePressure_example: "(InitSystem 10 5 ;; ChangePressure (-5)) = p,V,k := 5,10,50"
proof -
  have "InitSystem 10 5 = p,V,k := 10,5,50"
    by (rel_tac)
  hence "(InitSystem 10 5 ;; ChangePressure (-5)) = (ChangePressure (-5))\<lbrakk>10,5,50/$p,$V,$k\<rbrakk>"
    by (simp add: assigns_r_comp alpha)
  also have "... = ((&p - 5 >\<^sub>u 0)\<^sup>\<top>\<lbrakk>10,5,50/$p,$V,$k\<rbrakk> ;; p := &p - 5 ;; V := &k / &p)"
    by (simp add: ChangePressure_def lit_num_simps usubst unrest)
  also have "... = ((\<langle>[p \<mapsto>\<^sub>s 10, V \<mapsto>\<^sub>s 5, k \<mapsto>\<^sub>s 50]\<rangle>\<^sub>a \<triangleleft> (5 :\<^sub>u real) >\<^sub>u 0 \<triangleright> false) ;; p := &p - 5 ;; V := &k / &p)"
    by (simp add: rassume_def usubst alpha unrest)
  also have "... = (p,V,k := 10,5,50 ;; p := &p - 5 ;; V := &k / &p)"
    by rel_tac
  also have "... = p,V,k := 5,10,50"
    by rel_tac
  finally show ?thesis .
qed


end