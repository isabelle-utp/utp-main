section {* Theory of CSP *}

theory utp_csp
  imports utp_rea_designs utp_procedure
begin

subsection {* Preliminaries *}

text {* The following function defines the parallel composition of two CSP event traces *}

fun trpar :: "'\<theta> event set \<Rightarrow> '\<theta> event list \<Rightarrow> '\<theta> event list \<Rightarrow> '\<theta> event list set" where
"trpar cs [] [] = {[]}" |
"trpar cs (e # t) [] = (if e \<in> cs then {[]} else {x. hd(x) = e \<and> tl(x) \<in> (trpar cs t [])})" |
"trpar cs [] (e # t) = (if e \<in> cs then {[]} else {x. hd(x) = e \<and> tl(x) \<in> (trpar cs [] t)})" |
"trpar cs (e\<^sub>1 # t\<^sub>1) (e\<^sub>2 # t\<^sub>2) =
    (if (e\<^sub>1 = e\<^sub>2)
       then 
         if e\<^sub>1 \<in> cs
         then {e\<^sub>1 # t | t. t \<in> (trpar cs t\<^sub>1 t\<^sub>2)}
         else {e\<^sub>1 # t | t. t \<in> (trpar cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))} \<union> {e\<^sub>1 # t | t. t \<in> (trpar cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2)}
       else
         if e\<^sub>1 \<in> cs
           then
             if e\<^sub>2 \<in> cs
               then {[]}
               else {e\<^sub>2 # t | t. t \<in> trpar cs (e\<^sub>1 # t\<^sub>1) (t\<^sub>2)}
           else
             if e\<^sub>2 \<in> cs
               then {e\<^sub>1 # t | t. t \<in> trpar cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)}
               else {e\<^sub>1 # t | t. t \<in> trpar cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)} \<union> {e\<^sub>2 # t | t. t \<in> trpar cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2})"

syntax
  "_utrpar" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("trpar\<^sub>u'(_,_,_')")

translations
  "trpar\<^sub>u(cs,t1,t2)" == "CONST trop CONST trpar cs t1 t2"

subsection {* Healthiness conditions *}

definition "CSP1(P) = (P \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

text {* CSP2 is just H2 since the type system will automatically have J identifying the reactive
        variables as required. *}

definition "CSP2(P) = H2(P)"

abbreviation "CSP(P) \<equiv> CSP1(CSP2(RH(P)))"

definition "STOP = CSP1($ok\<acute> \<and> R3c($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition "SKIP = RH(\<exists> $ref \<bullet> CSP1(II))"

definition "CSP3(P) = (SKIP ;; P)"

definition "CSP4(P) = (P ;; SKIP)"

declare 
  CSP1_def [upred_defs] and 
  CSP2_def [upred_defs] and 
  SKIP_def [upred_defs] and
  CSP3_def [upred_defs] and 
  CSP4_def [upred_defs]

lemma CSP1_idem:
  "CSP1(CSP1(P)) = CSP1(P)"
  by pred_tac

lemma CSP2_idem:
  "CSP2(CSP2(P)) = CSP2(P)"
  by (simp add: CSP2_def H2_idem)

lemma CSP1_CSP2_commute:
  "CSP1(CSP2(P)) = CSP2(CSP1(P))"
  by (simp add: CSP1_def CSP2_def H2_split usubst, rel_tac)

lemma CSP1_via_H1: "R1(H1(P)) = R1(CSP1(P))"
  by rel_tac

lemma CSP1_R3c: "CSP1(R3(P)) = R3c(CSP1(P))"
  by rel_tac

lemma CSP1_reactive_design: "CSP1(RH(P \<turnstile> Q)) = RH(P \<turnstile> Q)"
  by rel_tac

lemma CSP2_reactive_design:
  assumes "$ok \<sharp> P" "$ok\<acute> \<sharp> P" "$ok \<sharp> Q" "$ok\<acute> \<sharp> Q"
  shows "CSP2(RH(P \<turnstile> Q)) = RH(P \<turnstile> Q)"
  using assms
  by (simp add: CSP2_def H2_R1_comm H2_R2_comm H2_R3_comm H2_design RH_def H2_R2s_comm)

lemma CSP1_R1_H1: 
  "R1(H1(P)) = CSP1(R1(P))"
  by rel_tac

lemma CSP_reactive_design:
  assumes "P is CSP"
  shows "P = RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "P = CSP1(CSP2(R1(R2s(R3c(P)))))"
    by (metis Healthy_def' RH_def assms)
  also have "... = CSP1(H2(R1(R2s(R3c(P)))))"
    by (simp add: CSP2_def)
  also have "... = CSP1(R1(H2(R2s(R3c(P)))))"
    by (simp add: R1_H2_commute)
  also have "... = R1(H1(R1(H2(R2s(R3c(P))))))"
    by (simp add: CSP1_R1_H1 R1_idem)
  also have "... = R1(H1(H2(R2s(R3c(R1(P))))))"
    by (metis CSP1_R1_H1 R1_H2_commute R1_R2_commute R1_idem R2_R3c_commute R2_def)
  also have "... = R1(R2s(H1(H2(R3c(R1(P))))))"
    by (simp add: R2s_H1_commute R2s_H2_commute)
  also have "... = R1(R2s(H1(R3c(H2(R1(P))))))"
    by (simp add: R3c_H2_commute)
  also have "... = R2(R1(H1(R3c(H2(R1(P))))))"
    by (metis R1_R2_commute R1_idem R2_def)
  also have "... = R2(R3c(R1(H1(H2(R1(P))))))"
    by (simp add: R1_H1_R3c_commute)
  also have "... = RH(H1_H2(R1(P)))"
    by (metis R1_R2_commute R1_idem R2_R3c_commute R2_def RH_def)
  also have "... = RH(H1_H2(P))"
    by (metis R1_idem RH_def calculation)
  also have "... = RH((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
  proof -
    have 0:"(\<not> (H1_H2(P))\<^sup>f) = ($ok \<and> \<not> P\<^sup>f)"
      by (simp add: H1_def H2_split, pred_tac)
    have 1:"(H1_H2(P))\<^sup>t = ($ok \<Rightarrow> (P\<^sup>f \<or> P\<^sup>t))"
      by (simp add: H1_def H2_split, pred_tac)
    have "(\<not> (H1_H2(P))\<^sup>f) \<turnstile> (H1_H2(P))\<^sup>t = ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
      by (simp add: 0 1, pred_tac)
    thus ?thesis
      by (metis H1_H2_commute H1_H2_is_design H1_idem H2_idem Healthy_def')
  qed
  also have "... = RH((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (metis R3c_subst_wait RH_def subst_not wait_false_design)
  finally show ?thesis .
qed

subsection {* Process constructs *}

definition "Stop = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition "Skip = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> (\<not> $wait\<acute>) \<and> \<lceil>II\<rceil>\<^sub>R))"

definition "Chaos = RH(false \<turnstile> true)"

definition Guard :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infix "&\<^sub>u" 65)
where "g &\<^sub>u A = RH((g \<Rightarrow> \<not> A\<^sup>f\<^sub>f) \<turnstile> ((g \<and> A\<^sup>t\<^sub>f) \<or> ((\<not> g) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"

definition ExtChoice :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infixl "\<box>" 65)
where "A\<^sub>1 \<box> A\<^sub>2 = RH(\<not> A\<^sub>1\<^sup>f\<^sub>f \<and> \<not> A\<^sub>2\<^sup>f\<^sub>f \<turnstile> (A\<^sub>1\<^sup>t\<^sub>f \<and> A\<^sub>2\<^sup>t\<^sub>f) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (A\<^sub>1\<^sup>t\<^sub>f \<or> A\<^sub>2\<^sup>t\<^sub>f))"

definition do\<^sub>u :: "('\<theta> event, ('\<theta>,'\<alpha>) alphabet_rp \<times> ('\<theta>,'\<alpha>) alphabet_rp) uexpr \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" where
"do\<^sub>u(e) = ($tr\<acute> =\<^sub>u $tr \<and> e \<notin>\<^sub>u $ref\<acute> \<triangleleft> $wait\<acute> \<triangleright> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>e\<rangle>)"

definition OutputCSP ::
  "('a, '\<theta>) chan \<Rightarrow> 
    ('a, ('\<theta>,'\<alpha>) alphabet_rp \<times> ('\<theta>,'\<alpha>) alphabet_rp) uexpr \<Rightarrow> 
    ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_rp" where
"OutputCSP c v A = (RH(true \<turnstile> do\<^sub>u (c, v)\<^sub>e) ;; A)"

definition do\<^sub>I :: 
  "('a, '\<theta>) chan \<Rightarrow> 
    ('a, ('\<theta>,'\<alpha>) alphabet_rp) uvar \<Rightarrow>
    ('a \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp) \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_rp"
where "do\<^sub>I c x P = (($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c,\<guillemotleft>e\<guillemotright>)\<^sub>e}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
                   \<triangleleft> $wait\<acute> \<triangleright>
                   (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c,\<guillemotleft>e\<guillemotright>)\<^sub>e\<rangle>}\<^sub>u \<and> (c, $x\<acute>)\<^sub>e =\<^sub>u last\<^sub>u($tr\<acute>)))"

definition InputCSP :: 
  "('a::two, '\<theta>) chan \<Rightarrow> _ \<Rightarrow>
    ('a \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp) \<Rightarrow> 
    (_ \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp) \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_rp"
where "InputCSP c x P A = (var x \<bullet> RH(true \<turnstile> do\<^sub>I c x P \<and> \<lceil>II\<rceil>\<^sub>R) ;; A(x))"

syntax
  "_csp_event"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>u _" [80,79] 80)
  "_csp_output" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!\<^sub>u'(_') \<rightarrow> _" [80,0,79] 80)
  "_csp_input"  :: "('a, '\<theta>) chan \<Rightarrow> id \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" ("_?\<^sub>u'(_ :/ _') \<rightarrow> _" [80,0,0,79] 80)

translations
  "c!\<^sub>u(v) \<rightarrow> A"     == "CONST OutputCSP c v A"
  "c \<rightarrow>\<^sub>u A"         == "CONST OutputCSP c ()\<^sub>u A"
  "c?\<^sub>u(x : P) \<rightarrow> A" => "CONST InputCSP c \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. P) (\<lambda> x. A)"

text {* Merge predicate for CSP *}

definition
  "CSPMerge(cs) =
    ((true \<turnstile>\<^sub>r (($wait\<^sub>r\<acute> =\<^sub>u ($0-wait\<^sub>r \<or> $1-wait\<^sub>r) \<and>
      $ref\<^sub>r\<acute> =\<^sub>u ($0-ref\<^sub>r \<union>\<^sub>u $1-ref\<^sub>r) \<and>
      ($tr\<^sub>r\<acute> - $tr\<^sub>r\<^sub><) \<in>\<^sub>u (trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, $0-tr\<^sub>r - $tr\<^sub>r\<^sub><, $1-tr\<^sub>r - $tr\<^sub>r\<^sub><)) \<and> 
      $0-tr\<^sub>r \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u $1-tr\<^sub>r \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>))) ;; SKIP)"

definition ParCSP :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> '\<theta> event set \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infixl "\<parallel>[_]\<^sub>C\<^sub>S\<^sub>P" 85)
where "P \<parallel>[cs]\<^sub>C\<^sub>S\<^sub>P Q = P \<parallel>\<^bsub>CSPMerge(cs)\<^esub> Q"

subsection {* CSP laws *}

lemma Stop_left_zero:
  assumes "P is R2s" "Q is R2s"
  shows "(Stop ;; RH(P \<turnstile> Q)) = Stop"
proof -
  from assms
  have "(Stop ;; RH(P \<turnstile> Q)) =
        RH ((\<not> ($ok\<acute> \<and> \<not> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> ;; R1 (\<not> P))) \<turnstile>
            ($wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> \<or> ($ok\<acute> \<and> \<not> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> ;; R1 Q)))"
       (is "_ = RH (?P \<turnstile> ?Q)")
  proof -
    have "$tr\<acute> =\<^sub>u $tr \<and> $wait\<acute> is R2s"
      apply (simp add: Healthy_def R2s_def usubst, rel_tac)
      using list_minus_anhil by blast
    moreover have "true is R2s"
      by (simp add: Healthy_def' R2s_true)
    ultimately show ?thesis using assms
      apply (simp add: Stop_def unrest)
      apply (subst reactive_design_composition)
      apply (simp_all add: unrest)
    done
  qed
  moreover have "?P = true"
    by pred_tac
  moreover have "?Q = ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)"
    by pred_tac
  ultimately show ?thesis
    by (simp add: Stop_def)
qed

lemma tr_rea_alpha_id:
  "(($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;; P) = (\<exists> $ok \<bullet> \<exists> $wait \<bullet> \<exists> $ref \<bullet> P)"
  apply (rel_tac)
  apply (rule_tac x="des_ok y" in exI)
  apply (rule_tac x="rp_wait (alpha_d.more y)" in exI)
  apply (rule_tac x="rp_ref (alpha_d.more y)" in exI)
  apply (smt alpha_d.surjective alpha_d.update_convs(1) alpha_d.update_convs(2) alpha_rp'.surjective alpha_rp'.update_convs(1) alpha_rp'.update_convs(3))
  using alpha_rp'.surjective apply fastforce
done

(*  
lemma Skip_left_unit:
  assumes "P is R2s" "Q is R2s"
  shows "(Skip ;; RH(P \<turnstile> Q)) = RH(P \<turnstile> Q)"
proof -
  have "(Skip ;; RH(P \<turnstile> Q)) = 
        RH ((\<not> ($ok\<acute> \<and> \<not> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R ;; R1 (\<not> P))) \<turnstile>
            ($wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R \<or>
            ($ok\<acute> \<and> \<not> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R ;; R1 Q)))"
  using assms
    apply (simp add: Skip_def)
    apply (subst reactive_design_composition)
    apply (simp_all add: unrest R2s_true R2s_conj Healthy_def R2s_tr'_eq_tr R2s_lift_rea R2s_not R2s_wait')
  done
  have "($ok\<acute> \<and> \<not> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R ;; R1 (\<not> P))
       = (\<exists> $ok \<bullet> \<exists> $wait \<bullet> \<exists> $ref \<bullet> $ok \<and> \<not> $wait \<and> R1 (\<not> P))"
  proof -
    have "($ok\<acute> \<and> \<not> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<and> \<not> $wait\<acute> \<and> \<lceil>II\<rceil>\<^sub>R ;; R1 (\<not> P))
       = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>II\<rceil>\<^sub>R ;; ($ok \<and> \<not> $wait \<and> R1 (\<not> P)))"
      by rel_tac
    also have "... = (($tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;; ($ok \<and> \<not> $wait \<and> R1 (\<not> P)))"
      by rel_tac
    also have "... = (\<exists> $ok \<bullet> \<exists> $wait \<bullet> \<exists> $ref \<bullet> $ok \<and> \<not> $wait \<and> R1 (\<not> P))"
      using tr_rea_alpha_id by blast
    also have "... = (\<exists> $ok \<bullet> (\<exists> $wait \<bullet> \<exists> $ref \<bullet> (R1 (\<not> P) \<and> $wait =\<^sub>u false)) \<and> $ok =\<^sub>u true)"
      by pred_tac
    also have "... = (\<exists> $wait \<bullet> \<exists> $ref \<bullet> (R1 (\<not> P\<lbrakk>true/$ok\<rbrakk>)) \<and> $wait =\<^sub>u false)"
      apply (subst one_point[of "in_var ok" _, simplified])
      apply (simp_all add: usubst unrest R1_def)
    done
    also have "... = (\<exists> $wait \<bullet> (\<exists> $ref \<bullet> (R1 (\<not> P\<lbrakk>true/$ok\<rbrakk>))) \<and> $wait =\<^sub>u false)"
      by (pred_tac)
    also have "... = (\<exists> $ref \<bullet> (R1 (\<not> P\<lbrakk>true/$ok\<rbrakk>\<lbrakk>false/$wait\<rbrakk>)))"
      apply (subst one_point[of "in_var wait" _, simplified])
      apply (simp_all add: usubst unrest R1_def)
    done

      term "utp_expr.var (in_var x) =\<^sub>u $x"
      apply (subst one_point[of "in_var ok"])

    also have "... = (\<exists> $wait \<bullet> \<exists> $ref \<bullet> R1 (\<not> P\<lbrakk>true/$ok\<rbrakk>))"
      
      thm one_point
      using tr_rea_alpha_id by blast


    finally show ?thesis .
  qed
*)    


(*
(* TODO : Circus merge predicate: *)

finition "MSt = undefined"

definition "M(cs) = ((($tr\<acute> - $\<^sub><tr) \<in>\<^sub>u (trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, $0.tr - $\<^sub><tr, $1.tr - $\<^sub><tr)) \<and> $0.tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u $1.tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<and> 
                    (  (($0.wait \<or> $1.wait) \<and> $ref\<acute> \<subseteq>\<^sub>u (($0.ref \<union>\<^sub>u $1.ref) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u (($0.ref \<inter>\<^sub>u $1.ref) - \<guillemotleft>cs\<guillemotright>))
                       \<triangleleft> $wait\<acute> \<triangleright>
                       (\<not> $1.wait \<and> \<not> $2.wait \<and> MSt)
                    ))"
*)

end