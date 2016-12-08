section {* Hybrid reactive designs *}

theory utp_hrd
imports 
  utp_designs
  utp_local
  utp_rea_designs
begin

subsection {* Alphabet and types *}

class time = linordered_idom + linordered_ring

instance real :: time ..

record 't::time htime =
  htime :: 't

typedef (overloaded) 'a nz = "{n::'a::time. n > 0}" morphisms nz_of nz
  by (metis mem_Collect_eq zero_less_one)

lemma real_of_nz_gez [simp]: "nz_of x > 0"
  by (metis mem_Collect_eq nz_of)

context notes [[typedef_overloaded]]
begin

datatype ('t, '\<theta>) tevent = Tock "'t nz" "'\<theta> set" | Event '\<theta>

end

fun period :: "('t::time,'\<theta>) tevent list \<Rightarrow> 't" where
"period [] = 0" |
"period (Tock n A # t) = nz_of n + period t" |
"period (Event x # t) = period(t)"

lemma period_ge_zero [simp]: "period t \<ge> 0"
  apply (induct t, simp_all)
  apply (rename_tac a t, case_tac a)
  apply (auto, metis add_nonneg_nonneg le_less real_of_nz_gez)
done

lemma Cons_prefixE: "\<lbrakk> (x # xs) \<le> ys; \<And> ys'. \<lbrakk> ys = x # ys'; xs \<le> ys' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis Cons_prefix_Cons append_Cons strict_prefixE)

lemma period_mono: "t1 \<le> t2 \<Longrightarrow> period t1 \<le> period t2"
  apply (induct t1 arbitrary: t2, auto)
  apply (rename_tac a t1 t2)
  apply (erule Cons_prefixE)
  apply (case_tac a)
  apply (auto)
done

lemma minus_list_Cons [simp]:
  "(x # ys) - (x # xs) = ys - xs"
  by (simp add: minus_list_def)

lemma period_minus [simp]: "t2 \<le> t1 \<Longrightarrow> period (t1 - t2) = period(t1) - period(t2)"
  apply (induct t1 arbitrary: t2, auto)
  apply (simp add: prefix_Cons)
  apply (auto)
  apply (rename_tac a t1 t2')
  apply (case_tac a)
  apply (simp_all)
done

fun events :: "('t, '\<theta>) tevent list \<Rightarrow> '\<theta> list" where
"events [] = []" |
"events (Tock n A # t) = events t" |
"events (Event x # t) = (x # events t)"

fun refusals :: "('t, '\<theta>) tevent list \<Rightarrow> '\<theta> set" where
"refusals [] = {}" |
"refusals (Tock n A # t) = A \<union> refusals t" |
"refusals (Event x # t) = refusals t"

fun idleprefix :: "('t, '\<theta>) tevent list \<Rightarrow> ('t, '\<theta>) tevent list" where
"idleprefix [] = []" |
"idleprefix (Tock n A # t) = (Tock n A # idleprefix t)" |
"idleprefix (Event x # t) = []"

syntax 
  "_period" :: "logic \<Rightarrow> logic" ("period\<^sub>u'(_')")
  "_events" :: "logic \<Rightarrow> logic" ("events\<^sub>u'(_')")
  "_refusals" :: "logic \<Rightarrow> logic" ("refusals\<^sub>u'(_')")
  "_idleprefix" :: "logic \<Rightarrow> logic" ("idleprefix\<^sub>u'(_')")
  "_ev"         :: "logic \<Rightarrow> logic" ("ev\<^sub>u'(_')")
  "_tock"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("tock\<^sub>u'(_,_')")

translations
  "period\<^sub>u(t)" == "CONST uop CONST period t"
  "events\<^sub>u(t)" == "CONST uop CONST events t"
  "refusals\<^sub>u(t)" == "CONST uop CONST refusals t"
  "idleprefix\<^sub>u(t)" == "CONST uop CONST idleprefix t"
  "ev\<^sub>u(e)" == "CONST uop CONST Event e"
  "tock\<^sub>u(t,A)" == "CONST bop CONST Tock t A"

type_synonym ('t, '\<theta>, '\<alpha>) alphabet_hrd = "(('t, '\<theta>) tevent, ('t, '\<alpha>) htime_scheme) alphabet_rp"
type_synonym ('a, 't, '\<theta>, '\<alpha>) hrde = "('a, ('t, '\<theta>, '\<alpha>) alphabet_hrd) uexpr"
type_synonym ('t, '\<theta>, '\<alpha>) hrdp = "(('t, '\<theta>, '\<alpha>) alphabet_hrd) upred"
type_synonym ('t, '\<theta>, '\<alpha>, '\<beta>) hrd = "(('t, '\<theta>, '\<alpha>) alphabet_hrd, ('t, '\<theta>, '\<beta>) alphabet_hrd) relation"
type_synonym ('t, '\<theta>, '\<alpha>) hhrd = "(('t, '\<theta>, '\<alpha>) alphabet_hrd, ('t, '\<theta>, '\<alpha>) alphabet_hrd) relation"

definition [upred_defs]: "time\<^sub>h = VAR htime"

definition [upred_defs]: "time = time\<^sub>h ;\<^sub>L \<Sigma>\<^sub>R"

definition [upred_defs]: "\<Sigma>\<^sub>h = VAR more"

definition [upred_defs]: "\<Sigma>\<^sub>H = \<Sigma>\<^sub>h ;\<^sub>L \<Sigma>\<^sub>R"

lemma time\<^sub>h_uvar [simp]: "uvar time\<^sub>h"
  by (unfold_locales, simp_all add: time\<^sub>h_def)

lemma \<Sigma>\<^sub>h_uvar [simp]: "uvar \<Sigma>\<^sub>h"
  by (unfold_locales, simp_all add: \<Sigma>\<^sub>h_def)

lemma time_uvar [simp]: "uvar time"
  by (metis comp_vwb_lens rea_lens_under_des_lens sublens_pres_vwb time\<^sub>h_uvar time_def uvar_des_lens)

lemma \<Sigma>\<^sub>H_uvar [simp]: "uvar \<Sigma>\<^sub>H"
  by (metis \<Sigma>\<^sub>H_def \<Sigma>\<^sub>h_uvar comp_vwb_lens rea_lens_under_des_lens sublens_pres_vwb uvar_des_lens)

lemma hy_lens_under_des_lens: "\<Sigma>\<^sub>H \<subseteq>\<^sub>L \<Sigma>\<^sub>R"
  by (simp add: \<Sigma>\<^sub>H_def lens_comp_lb) 

lemma time_ok_indep [simp]: "time \<bowtie> ok" "ok \<bowtie> time"
  by (simp_all add: lens_indep_left_ext lens_indep_sym time_def)

lemma time_wait_indep [simp]: "time \<bowtie> wait" "wait \<bowtie> time"
  by (simp_all add: lens_indep_left_ext lens_indep_sym time_def)

lemma time_tr_indep [simp]: "time \<bowtie> tr" "tr \<bowtie> time"
  by (simp_all add: lens_indep_left_ext lens_indep_sym time_def)

lemma time_ref_indep [simp]: "time \<bowtie> ref" "ref \<bowtie> time"
  by (simp_all add: lens_indep_left_ext lens_indep_sym time_def)

lemma time_hy_indep [simp]: "time\<^sub>h \<bowtie> \<Sigma>\<^sub>h" "\<Sigma>\<^sub>h \<bowtie> time\<^sub>h"
  by (auto intro!:lens_indepI simp add: time\<^sub>h_def \<Sigma>\<^sub>h_def)

lemma time_hy_lens_indep [simp]: "time \<bowtie> \<Sigma>\<^sub>H" "\<Sigma>\<^sub>H \<bowtie> time"
  by (auto intro: lens_indep_left_comp simp add: time_def \<Sigma>\<^sub>H_def)

lemma hy_lens_indep_ok [simp]:
  "\<Sigma>\<^sub>H \<bowtie> ok" "ok \<bowtie> \<Sigma>\<^sub>H"
  using hy_lens_under_des_lens rea_lens_indep_ok(1) sublens_pres_indep apply blast
  using hy_lens_under_des_lens lens_indep_sym rea_lens_indep_ok(1) sublens_pres_indep apply blast
done

lemma hy_lens_indep_tr [simp]:
  "\<Sigma>\<^sub>H \<bowtie> tr" "tr \<bowtie> \<Sigma>\<^sub>H"
using hy_lens_under_des_lens rea_lens_indep_tr(1) sublens_pres_indep apply blast
using hy_lens_under_des_lens lens_indep_sym rea_lens_indep_tr(1) sublens_pres_indep apply blast
done

lemma hy_lens_indep_wait [simp]:
  "\<Sigma>\<^sub>H \<bowtie> wait" "wait \<bowtie> \<Sigma>\<^sub>H"
  apply (simp_all add: \<Sigma>\<^sub>H_def lens_indep_left_ext)
  using lens_indep_left_ext lens_indep_sym rea_lens_indep_wait(1) apply blast
done

lemma hy_lens_indep_ref [simp]:
  "\<Sigma>\<^sub>H \<bowtie> ref" "ref \<bowtie> \<Sigma>\<^sub>H"
  by (simp_all add: \<Sigma>\<^sub>H_def lens_indep_left_ext lens_indep_sym)

abbreviation lift_hrd :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>H") where
"\<lceil>P\<rceil>\<^sub>H \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>H \<times>\<^sub>L \<Sigma>\<^sub>H)"

abbreviation drop_hrd :: "_ \<Rightarrow> _" ("\<lfloor>_\<rfloor>\<^sub>H") where
"\<lfloor>P\<rfloor>\<^sub>H \<equiv> P \<restriction>\<^sub>p (\<Sigma>\<^sub>H \<times>\<^sub>L \<Sigma>\<^sub>H)"

abbreviation "\<L> \<equiv> $time\<acute> - $time"

lemma lift_hrd_unrests [unrest]:
  "$ok \<sharp> \<lceil>P\<rceil>\<^sub>H" "$ok\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H" "$wait \<sharp> \<lceil>P\<rceil>\<^sub>H" "$wait\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H"
  "$tr \<sharp> \<lceil>P\<rceil>\<^sub>H" "$tr\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H" "$ref \<sharp> \<lceil>P\<rceil>\<^sub>H" "$ref\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H"
  "$time \<sharp> \<lceil>P\<rceil>\<^sub>H" "$time\<acute> \<sharp> \<lceil>P\<rceil>\<^sub>H"
  by (simp_all add: unrest_aext_indep)

lemma time_ords [usubst]: "$time \<prec>\<^sub>v $time\<acute>"
  by (simp add: var_name_ord_def)

lemma ok_time_ords [usubst]:
  "$ok \<prec>\<^sub>v $time" "$ok\<acute> \<prec>\<^sub>v $time" "$ok \<prec>\<^sub>v $time\<acute>" "$ok\<acute> \<prec>\<^sub>v $time\<acute>"
  by (simp_all add: var_name_ord_def)

lemma time_tr_ords [usubst]:
  "$time \<prec>\<^sub>v $tr" "$time\<acute> \<prec>\<^sub>v $tr\<acute>" "$time \<prec>\<^sub>v $tr\<acute>" "$time\<acute> \<prec>\<^sub>v $tr"
  by (simp_all add: var_name_ord_def)

lemma time_wait_ords [usubst]: 
  "$time \<prec>\<^sub>v $wait" "$time\<acute> \<prec>\<^sub>v $wait\<acute>" "$time \<prec>\<^sub>v $wait\<acute>" "$time\<acute> \<prec>\<^sub>v $wait"
  by (simp_all add: var_name_ord_def)

lemma time_ref_ords [usubst]: 
  "$time \<prec>\<^sub>v $ref" "$time\<acute> \<prec>\<^sub>v $ref\<acute>" "$time \<prec>\<^sub>v $ref\<acute>" "$time\<acute> \<prec>\<^sub>v $ref"
  by (simp_all add: var_name_ord_def)

subsection {* Healthiness conditions *}

definition [upred_defs]: "TI1(P) = (P \<and> $time \<le>\<^sub>u $time\<acute>)"

definition [upred_defs]: "HTI(P) = (P \<and> period\<^sub>u($tr\<acute> - $tr) =\<^sub>u $time\<acute> - $time)"

definition [upred_defs]: "HR1(P) = HTI(TI1(R1(P)))"

definition [upred_defs]: "TI2(P) = P\<lbrakk>0,($time\<acute>-$time)/$time,$time\<acute>\<rbrakk>"

definition [upred_defs]: "TI2c(P) = (P\<lbrakk>0,($time\<acute>-$time)/$time,$time\<acute>\<rbrakk> \<triangleleft> TI1(true) \<triangleright> P)"

definition [upred_defs]: "HR2(P) = R2(TI2(P))"

definition [upred_defs]: "HR2s(P) = R2s(TI2(P))"

definition [upred_defs]: "HR2c(P) = R2c(TI2(P))"

definition [urel_defs]: "II\<^sub>H = (II \<or> (\<not> $ok \<and> HR1(true)))"

definition [upred_defs]: "HR3(P) = (II\<^sub>H \<triangleleft> $wait \<triangleright> P)" 

definition [upred_defs]: "HR(P) = HR1(HR2s(HR3(P)))"

definition [upred_defs]: "HCSP1(P) = (P \<or> \<not> $ok \<and> HR1(true))"

abbreviation (input) "HCSP2(P) \<equiv> H2(P)"

definition "HCSP(P) = HCSP1(HCSP2(HR(P)))"

lemma TI1_idem: "TI1(TI1(P)) = TI1(P)"
  by rel_auto

lemma TI1_conj_left:
  "TI1(P \<and> Q) = (TI1(P) \<and> Q)"
  by rel_auto

lemma TI1_conj_right:
  "TI1(P \<and> Q) = (P \<and> TI1(Q))"
  by rel_auto

lemma TI1_conj:
  "TI1(P \<and> Q) = (TI1(P) \<and> TI1(Q))"
  by rel_auto

lemma TI1_disj:
  "TI1(P \<or> Q) = (TI1(P) \<or> TI1(Q))"
  by (rel_auto)

lemma TI1_USUP:
  "TI1(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> TI1(P(i)))"
  by (rel_auto)

lemma TI1_UINF:
  assumes "A \<noteq> {}"
  shows "TI1(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> TI1(P(i)))"
  using assms by (rel_auto)

lemma TI1_HR1:
  "TI1(HR1(P)) = HR1(P)"
  by (rel_auto)

lemma TI1_TI2_commute:
  "TI1(TI2(P)) = TI2(TI1(P))"
  by rel_auto

lemma TI1_R1_commute:
  "TI1(R1(P)) = R1(TI1(P))"
  by rel_auto

lemma TI1_HR3_commute:
  "TI1(HR3(P)) = HR3(TI1(P))"
  by rel_auto

lemma TI1_skip_ti:
  "TI1(II\<^sub>H) = II\<^sub>H"
  by rel_auto

lemma TI1_H2_commute: "TI1(H2(P)) = H2(TI1(P))"
  by (rel_auto)

lemma TI1_unrest [unrest]: "\<lbrakk> x \<sharp> P; in_var time \<bowtie> x; out_var time \<bowtie> x \<rbrakk> \<Longrightarrow> x \<sharp> TI1(P)"
  by (simp add: TI1_def R1_def unrest)

lemma TI1_time_diff_abs: "TI1($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) = ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
  by (rel_auto)

lemma TI2_idem: "TI2(TI2(P)) = TI2(P)"
  by rel_auto

lemma TI2_not:
  "TI2(\<not> P) = (\<not> TI2(P))"
  by (rel_auto)

lemma TI2_conj:
  "TI2(P \<and> Q) = (TI2(P) \<and> TI2(Q))"
  by (rel_auto)
  
lemma TI2_disj:
  "TI2(P \<or> Q) = (TI2(P) \<or> TI2(Q))"
  by (rel_auto)

lemma TI2_cond:
  "TI2(P \<triangleleft> b \<triangleright> Q) = (TI2(P) \<triangleleft> TI2(b) \<triangleright> TI2(Q))"
  by (simp add: cond_def TI2_disj TI2_conj TI2_not)

lemma TI2_USUP:
  "TI2(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> TI2(P(i)))"
  by (simp add: TI2_def usubst)

lemma TI2_UINF:
  "TI2(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> TI2(P(i)))"
  by (simp add: TI2_def usubst)

lemma TI2_ok:
  "TI2($ok) = $ok"
  by (rel_auto)
  
lemma TI2_wait:
  "TI2($wait) = $wait"
  by (rel_auto)

lemma TI2_wait':
  "TI2($wait\<acute>) = $wait\<acute>"
  by (rel_auto)

lemma TI2_skip:
  "TI2(II) = II"
proof -
  have "TI2(II) = TI2 ($time\<acute> =\<^sub>u $time \<and> II \<restriction>\<^sub>\<alpha> time)"
    by (metis skip_r_unfold time_uvar)
  also have "... = ($time\<acute>-$time =\<^sub>u 0 \<and> II \<restriction>\<^sub>\<alpha> time)" 
    by (simp add: TI2_def usubst unrest)
  also have "... = ($time\<acute> =\<^sub>u $time \<and> II \<restriction>\<^sub>\<alpha> time)"
    by (rel_auto)
  also have "... = II"
    by (metis skip_r_unfold time_uvar)
  finally show ?thesis .
qed

lemma TI2_form:
  "TI2(P) = (\<^bold>\<exists> t \<bullet> P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<guillemotright>/$time\<acute>\<rbrakk> \<and> $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<guillemotright>)"
  by (rel_auto)

lemma TI1_TI2_form:
  "TI1(TI2(P)) = (\<^bold>\<exists> t \<bullet> P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<guillemotright>/$time\<acute>\<rbrakk> \<and> $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<ge>\<^sub>u 0)"
  by (rel_auto)

lemma TI2_seqr_form: 
  shows "(TI2(P) ;; TI2(Q)) = 
         (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                        \<and> ($time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>))"
proof -
  have "(TI2(P) ;; TI2(Q)) = (\<^bold>\<exists> t\<^sub>0 \<bullet> (TI2(P))\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/$time\<acute>\<rbrakk> ;; (TI2(Q))\<lbrakk>\<guillemotleft>t\<^sub>0\<guillemotright>/$time\<rbrakk>)"
    by (subst seqr_middle[of time], simp_all)
  also have "... =
       (\<^bold>\<exists> t\<^sub>0 \<bullet> \<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk> \<and> \<guillemotleft>t\<^sub>0\<guillemotright> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright>) ;; 
                             (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk> \<and> $time\<acute> =\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>)))"
    by (simp add: TI2_form usubst unrest, rel_auto)
  also have "... =
       (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> \<^bold>\<exists> t\<^sub>0 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                             \<and> \<guillemotleft>t\<^sub>0\<guillemotright> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> \<and> $time\<acute> =\<^sub>u \<guillemotleft>t\<^sub>0\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>)"
    by rel_auto
  also have "... =
       (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                        \<and> (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> \<and> $time\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>))"
    by rel_auto
  also have "... =
       (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                        \<and> ($time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>))"
    by rel_auto
  finally show ?thesis .
qed

lemma TI1_TI2_seqr_form:
  "(TI1(TI2(P)) ;; TI1(TI2(Q))) 
        = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ((P\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>1\<guillemotright>/$time\<acute>\<rbrakk>) ;; (Q\<lbrakk>0/$time\<rbrakk>\<lbrakk>\<guillemotleft>t\<^sub>2\<guillemotright>/$time\<acute>\<rbrakk>)) 
                       \<and> ($time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright>) \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
  apply (simp add: TI1_TI2_commute TI2_seqr_form)
  apply (simp add: TI1_def usubst)
  apply (rel_auto)
done
 
lemma time'_minus_form: "($time\<acute> - $time =\<^sub>u v) = ($time\<acute> =\<^sub>u $time + v)"
  by (pred_auto)

lemma TI2_HR1_true: "TI2(HR1(true)) = HR1(true)"
  by (rel_auto)

lemma TI2_skip_ti:
  "TI2(II\<^sub>H) = II\<^sub>H"
  by (simp add: II\<^sub>H_def TI2_conj TI2_disj TI2_skip TI2_not TI2_ok TI2_HR1_true TI1_TI2_commute[THEN sym] usubst)

lemma TI2_R1_commute:
  "TI2(R1(P)) = R1(TI2(P))"
  by rel_auto

lemma TI2_seq:
  "TI2(TI2(P) ;; TI2(Q)) = (TI2(P) ;; TI2(Q))"
  apply (simp add: TI2_seqr_form)
  apply (simp add: TI2_def usubst unrest time'_minus_form add.assoc)
done

lemma TI2_H2_commute: "TI2(H2(P)) = H2(TI2(P))"
  by (simp add: H2_split TI2_def usubst unrest)

lemma R2s_TI2_commute: "R2s(TI2(P)) = TI2(R2s(P))"
  by (simp add: R2s_def TI2_def usubst)
  
lemma R2_TI2_commute: "R2(TI2(P)) = TI2(R2(P))"
  by (simp add: R2_def R2s_TI2_commute TI2_R1_commute)

lemma TI2_HR3_commute:
  "TI2(HR3(P)) = HR3(TI2(P))"
  by (simp add: HR3_def usubst TI2_cond TI2_skip_ti TI2_wait)

lemma HTI_idem: "HTI(HTI(P)) = HTI(P)"
  by rel_auto

lemma HTI_R1_commute: "HTI(R1(P)) = R1(HTI(P))"
  by rel_auto

lemma HTI_TI1_commute: "HTI(TI1(P)) = TI1(HTI(P))"
  by rel_auto

lemma HTI_H2_commute: "HTI(H2(P)) = H2(HTI(P))"
  by rel_auto

lemma HTI_USUP:
  "HTI(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> HTI(P(i)))"
  by rel_auto

lemma HTI_UINF:
  assumes "A \<noteq> {}"
  shows "HTI(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> HTI(P(i)))"
  using assms by rel_auto

lemma HR1_idem: "HR1(HR1(P)) = HR1(P)"
  by (rel_auto)

lemma HR1_mono: "P \<sqsubseteq> Q \<Longrightarrow> HR1(P) \<sqsubseteq> HR1(Q)"
  by (rel_auto)

lemma HR1_disj: "HR1(P \<or> Q) = (HR1(P) \<or> HR1(Q))"
  by (rel_auto)

lemma HR1_cond: "HR1(P \<triangleleft> b \<triangleright> Q) = (HR1(P) \<triangleleft> b \<triangleright> HR1(Q))"
  by (rel_auto)

lemma HR1_conj: "HR1(P \<and> Q) = (HR1(P) \<and> HR1(Q))"
  by (rel_auto)

lemma HR1_extend_conj: "HR1(P \<and> Q) = (HR1(P) \<and> Q)"
  by (rel_auto)

lemma HR1_extend_conj': "HR1(P \<and> Q) = (P \<and> HR1(Q))"
  by (rel_auto)

lemma HR1_USUP:
  "HR1(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> HR1(P(i)))"
  by (simp add: HR1_def TI1_USUP HTI_USUP R1_USUP)

lemma HR1_UINF:
  assumes "A \<noteq> {}"
  shows "HR1(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> HR1(P(i)))"
  by (simp add: HR1_def R1_UINF HTI_UINF TI1_UINF assms)

lemma HR1_not_HR1: "HR1(\<not> HR1(P)) = HR1(\<not> P)"
  by (rel_auto)

lemma HR1_true_comp: "(HR1(true) ;; HR1(true)) = HR1(true)"
proof (rel_auto)
  fix a :: "(('a, 'b) tevent, ('a, 'c) htime_scheme) alpha_rp'_ext alpha_d_ext" and b :: "(('a, 'b) tevent, ('a, 'd) htime_scheme) alpha_rp'_ext alpha_d_ext"
  assume a1: "rp_tr (alpha_d.more a) \<le> rp_tr (alpha_d.more b)"
  assume a2: "htime (alpha_rp'.more (alpha_d.more a)) \<le> htime (alpha_rp'.more (alpha_d.more b))"
  assume a3: "period (rp_tr (alpha_d.more b)) - period (rp_tr (alpha_d.more a)) = htime (alpha_rp'.more (alpha_d.more b)) - htime (alpha_rp'.more (alpha_d.more a))"
  have f4: "period (rp_tr (alpha_d.more b) - rp_tr (alpha_d.more a)) = period (rp_tr (alpha_d.more b)) - period (rp_tr (alpha_d.more a))"
    using a1 by (metis period_minus)
  have "\<And>ts. period ((ts::('a, 'b) tevent list) - ts) = 0"
    by (metis cancel_comm_monoid_add_class.diff_cancel order_refl period_minus)
  then show "\<exists>aa. rp_tr (alpha_d.more a) \<le> rp_tr (alpha_d.more aa) \<and> htime (alpha_rp'.more (alpha_d.more a)) \<le> htime (alpha_rp'.more (alpha_d.more aa)::('a, 'e) htime_scheme) \<and> period (rp_tr (alpha_d.more aa) - rp_tr (alpha_d.more a)) = htime (alpha_rp'.more (alpha_d.more aa)) - htime (alpha_rp'.more (alpha_d.more a)) \<and> rp_tr (alpha_d.more aa) \<le> rp_tr (alpha_d.more b) \<and> htime (alpha_rp'.more (alpha_d.more aa)) \<le> htime (alpha_rp'.more (alpha_d.more b)) \<and> period (rp_tr (alpha_d.more b) - rp_tr (alpha_d.more aa)) = htime (alpha_rp'.more (alpha_d.more b)) - htime (alpha_rp'.more (alpha_d.more aa))"
    using f4 a3 a2 a1 by (metis alpha_d.select_convs(2) alpha_rp'.select_convs(2) alpha_rp'.select_convs(4) cancel_comm_monoid_add_class.diff_cancel htime.select_convs(1) order_refl)
qed

lemma HR1_not_ok_true:
  "((HR1(\<not> $ok) :: ('t::time,'\<theta>,'\<alpha>,'\<beta>) hrd) ;; HR1(true)) = 
        (HR1(\<not> $ok) :: ('t,'\<theta>,'\<alpha>,'\<gamma>) hrd)" 
proof (rel_auto)
  fix a :: "(('t, '\<theta>) tevent, ('t, '\<alpha>) htime_scheme) alpha_rp'_ext alpha_d_ext" and b :: "(('t, '\<theta>) tevent, ('t, '\<gamma>) htime_scheme) alpha_rp'_ext alpha_d_ext"
  assume a1: "rp_tr (alpha_d.more a) \<le> rp_tr (alpha_d.more b)"
  assume a2: "htime (alpha_rp'.more (alpha_d.more a)) \<le> htime (alpha_rp'.more (alpha_d.more b))"
  assume a3: "period (rp_tr (alpha_d.more b)) - period (rp_tr (alpha_d.more a)) = htime (alpha_rp'.more (alpha_d.more b)) - htime (alpha_rp'.more (alpha_d.more a))"
  have f4: "period (rp_tr (alpha_d.more b)) - period (rp_tr (alpha_d.more a)) = period (rp_tr (alpha_d.more b) - rp_tr (alpha_d.more a))"
    using a1 by (metis period_minus)
  have "\<And>ts. 0 = period ((ts::('t, '\<theta>) tevent list) - ts)"
    by (metis cancel_comm_monoid_add_class.diff_cancel order_refl period_minus)
  then show "\<exists>aa. rp_tr (alpha_d.more a) \<le> rp_tr (alpha_d.more aa) \<and> htime (alpha_rp'.more (alpha_d.more a)) \<le> htime (alpha_rp'.more (alpha_d.more aa)::('t, '\<beta>) htime_scheme) \<and> period (rp_tr (alpha_d.more aa) - rp_tr (alpha_d.more a)) = htime (alpha_rp'.more (alpha_d.more aa)) - htime (alpha_rp'.more (alpha_d.more a)) \<and> rp_tr (alpha_d.more aa) \<le> rp_tr (alpha_d.more b) \<and> htime (alpha_rp'.more (alpha_d.more aa)) \<le> htime (alpha_rp'.more (alpha_d.more b)) \<and> period (rp_tr (alpha_d.more b) - rp_tr (alpha_d.more aa)) = htime (alpha_rp'.more (alpha_d.more b)) - htime (alpha_rp'.more (alpha_d.more aa))"
    using f4 a3 a2 a1 by (metis alpha_d.select_convs(2) alpha_rp'.select_convs(2) alpha_rp'.select_convs(4) cancel_comm_monoid_add_class.diff_cancel htime.select_convs(1) order_refl)
qed

lemma HR1_HR3_commute: "HR1(HR3(P)) = HR3(HR1(P))"
  by (rel_auto)

lemma HR2s_TI1_commute: "HR2s(TI1(P)) = TI1(HR2s(P))"
  by (rel_auto)

lemma HR_R2c_def: "HR(P) = HR1(HR2c(HR3(P)))"
  by (rel_auto)

lemma HR1_hskip:"HR1(II\<^sub>H) = II\<^sub>H"
  by (rel_auto)

lemma R2c_HR1_true:
  "R2c(HR1(true)) = HR1(true)"
  by (rel_auto)

lemma R2c_hskip:
  "R2c(II\<^sub>H) = II\<^sub>H"
  by (simp add: II\<^sub>H_def R2c_disj R2c_skip_r, rel_auto)

lemma HR2c_hskip:
  "HR2c(II\<^sub>H) = II\<^sub>H"
  by (simp add: II\<^sub>H_def HR2c_def TI2_disj TI2_conj TI2_not TI2_ok TI2_HR1_true TI2_skip  
                R2c_disj R2c_and R2c_skip_r R2c_HR1_true R2c_not R2c_ok)

lemma HR2c_ok: "HR2c($ok) = $ok"
  by (simp add: HR2c_def TI2_ok R2c_ok)

lemma HR2c_wait: "HR2c($wait) = $wait"
  by (simp add: HR2c_def TI2_wait R2c_wait)

lemma R2c_wait': "R2c($wait\<acute>) = $wait\<acute>"
  by (rel_auto)

lemma HR2c_wait': "HR2c($wait\<acute>) = $wait\<acute>"
  by (simp add: HR2c_def TI2_wait' R2c_wait')

lemma HR2c_cond: "HR2c(P \<triangleleft> b \<triangleright> Q) = (HR2c(P) \<triangleleft> HR2c(b) \<triangleright> HR2c(Q))"
  by (simp add: HR2c_def TI2_cond R2c_condr)

lemma HR3_hskip: "HR3(II\<^sub>H) = II\<^sub>H"
  by (rel_auto)

lemma HR_hskip: "HR(II\<^sub>H) = II\<^sub>H"
  by (simp add: HR_R2c_def HR3_hskip HR2c_hskip HR1_hskip)

lemma H2_hskip: "H2(II\<^sub>H) = II\<^sub>H"
  by (rel_auto, simp add: alpha_d.equality)

lemma HCSP1_idem: "HCSP1(HCSP1(P)) = HCSP1(P)"
  by (rel_auto)

lemma HCSP1_hskip: "HCSP1(II\<^sub>H) = II\<^sub>H"
  by (rel_auto)

lemma HR1_H2_commute: "HR1(H2(P)) = H2(HR1(P))"
  by (simp add: HR1_def R1_H2_commute TI1_H2_commute HTI_H2_commute)

lemma HCSP1_HR1_H1: 
  "HR1(H1(P)) = HCSP1(HR1(P))"
  by rel_auto

lemma HR1_HR3_design:
  "HR1(HR3(P \<turnstile> Q)) = HR1(R3c_pre(P) \<turnstile> R3c_post(Q))"
  by (rel_auto, simp_all add: alpha_d.equality)

lemma HR1_seq: "HR1(HR1(P) ;; HR1(Q)) = (HR1(P) ;; HR1(Q))"
  by (rel_auto)

lemma HR1_design_composition:
  fixes P Q :: "('t::time, '\<theta>, '\<alpha>, '\<beta>) hrd"
  and R S :: "('t, '\<theta>, '\<beta>, '\<gamma>) hrd"
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows
  "(HR1(P \<turnstile> Q) ;; HR1(R \<turnstile> S)) = 
   HR1((\<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> (HR1(Q) ;; HR1(\<not> R))) \<turnstile> (HR1(Q) ;; HR1(S)))"
proof -
  have "(HR1(P \<turnstile> Q) ;; HR1(R \<turnstile> S)) = (\<^bold>\<exists> ok\<^sub>0 \<bullet> (HR1(P \<turnstile> Q))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<acute>\<rbrakk> ;; (HR1(R \<turnstile> S))\<lbrakk>\<guillemotleft>ok\<^sub>0\<guillemotright>/$ok\<rbrakk>)"
    using seqr_middle uvar_ok by blast
  also from assms have "... = (\<^bold>\<exists> ok\<^sub>0 \<bullet> HR1(($ok \<and> P) \<Rightarrow> (\<guillemotleft>ok\<^sub>0\<guillemotright> \<and> Q)) ;; HR1((\<guillemotleft>ok\<^sub>0\<guillemotright>  \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))"
    by (simp add: design_def HR1_def TI1_def R1_def HTI_def usubst unrest)
  also from assms have "... = ((HR1(($ok \<and> P) \<Rightarrow> (true \<and> Q)) ;; HR1((true \<and> R) \<Rightarrow> ($ok\<acute> \<and> S)))
                             \<or> (HR1(($ok \<and> P) \<Rightarrow> (false \<and> Q)) ;; HR1((false \<and> R) \<Rightarrow> ($ok\<acute> \<and> S))))"
    by (simp add: false_alt_def true_alt_def)
  also from assms have "... = ((HR1(($ok \<and> P) \<Rightarrow> Q) ;; HR1(R \<Rightarrow> ($ok\<acute> \<and> S))) 
                             \<or> (HR1(\<not> ($ok \<and> P)) ;; HR1(true)))"
    by simp
  also from assms have "... = ((HR1(\<not> $ok \<or> \<not> P \<or> Q) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                             \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by (simp add: impl_alt_def utp_pred.sup.assoc)
  also from assms have "... = (((HR1(\<not> $ok \<or> \<not> P) \<or> HR1(Q)) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by (simp add: HR1_disj utp_pred.disj_assoc)
  also from assms have "... = ((HR1(\<not> $ok \<or> \<not> P) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S)))
                               \<or> (HR1(Q) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by (simp add: seqr_or_distl utp_pred.sup.assoc)
  also from assms have "... = ((HR1(Q) ;; HR1(\<not> R \<or> ($ok\<acute> \<and> S))) 
                               \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by rel_auto (* Slow *)
  also from assms have "... = ((HR1(Q) ;; (HR1(\<not> R) \<or> HR1(S) \<and> $ok\<acute>)) 
                               \<or> (HR1(\<not> $ok \<or> \<not> P) ;; HR1(true)))"
    by (simp add: HR1_disj HR1_extend_conj utp_pred.inf_commute)
  also have "... = ((HR1(Q) ;; (HR1(\<not> R) \<or> HR1(S) \<and> $ok\<acute>)) 
                  \<or> ((HR1(\<not> $ok) :: ('t,'\<theta>,'\<alpha>,'\<beta>) hrd) ;; HR1(true)) 
                  \<or> (HR1(\<not> P) ;; HR1(true)))"
    by (simp add: HR1_disj seqr_or_distl)
  also have "... = ((HR1(Q) ;; (HR1(\<not> R) \<or> HR1(S) \<and> $ok\<acute>)) 
                  \<or> (HR1(\<not> $ok))
                  \<or> (HR1(\<not> P) ;; HR1(true)))"
  proof -
    have "((HR1(\<not> $ok) :: ('t,'\<theta>,'\<alpha>,'\<beta>) hrd) ;; HR1(true)) = 
           (HR1(\<not> $ok) :: ('t,'\<theta>,'\<alpha>,'\<gamma>) hrd)"
      by (metis HR1_not_ok_true)
    thus ?thesis
      by simp
  qed
  also have "... = ((HR1(Q) ;; (HR1(\<not> R) \<or> (HR1(S \<and> $ok\<acute>)))) 
                  \<or> HR1(\<not> $ok)
                  \<or> (HR1(\<not> P) ;; HR1(true)))"
    by (simp add: HR1_extend_conj)
  also have "... = ( (HR1(Q) ;; (HR1 (\<not> R)))
                   \<or> (HR1(Q) ;; (HR1(S \<and> $ok\<acute>)))
                   \<or> HR1(\<not> $ok)
                   \<or> (HR1(\<not> P) ;; HR1(true)))"
    by (simp add: seqr_or_distr utp_pred.sup.assoc)
  also have "... = HR1( (HR1(Q) ;; (HR1 (\<not> R)))
                     \<or> (HR1(Q) ;; (HR1(S \<and> $ok\<acute>)))
                     \<or> (\<not> $ok)
                     \<or> (HR1(\<not> P) ;; HR1(true)))"
    by (simp add: HR1_disj HR1_seq)
  also have "... = HR1( (HR1(Q) ;; (HR1 (\<not> R)))
                     \<or> ((HR1(Q) ;; HR1(S)) \<and> $ok\<acute>)
                     \<or> (\<not> $ok)
                     \<or> (HR1(\<not> P) ;; HR1(true)))"
  proof -
    have "(HR1(Q) ;; (HR1(S \<and> $ok\<acute>))) = ((HR1(Q) ;; HR1(S)) \<and> $ok\<acute>)"
      by (simp add: HR1_extend_conj, rel_auto)
    thus ?thesis
      by (simp)
  qed
  also have "... = HR1(\<not>($ok \<and> \<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> (HR1(Q) ;; (HR1 (\<not> R))))
                     \<or>  ((HR1(Q) ;; HR1(S)) \<and> $ok\<acute>))"
    by (simp add: utp_pred.sup_commute utp_pred.sup_left_commute)
    
  also have "... = HR1(($ok \<and> \<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> (HR1(Q) ;; (HR1 (\<not> R))))
                      \<Rightarrow> ($ok\<acute> \<and> (HR1(Q) ;; HR1(S))))"
    by (simp add: impl_alt_def utp_pred.inf_commute)
  also have "... = HR1((\<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> (HR1(Q) ;; HR1(\<not> R))) \<turnstile> (HR1(Q) ;; HR1(S)))"
    by (simp add: design_def)
  finally show ?thesis .
qed

lemma HR3_semir_form:
  "(HR3 P ;; HR3(HR1(Q))) = HR3 (P ;; HR3(HR1(Q)))"
  by (rel_auto)

lemma HR3_HR1_design_composition: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(HR3(HR1(P \<turnstile> Q)) ;; HR3(HR1(R \<turnstile> S))) = 
       HR3(HR1((\<not> (HR1(\<not> P) ;; HR1(true)) \<and> \<not> ((HR1(Q) \<and> \<not> $wait\<acute>) ;; HR1(\<not> R))) 
       \<turnstile> (HR1(Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1(S)))))"
proof -
  have 1:"(\<not> (HR1 (\<not> R3c_pre P) ;; HR1 true)) = (R3c_pre (\<not> (HR1 (\<not> P) ;; HR1 true)))"
    by rel_auto
  have 2:"(\<not> (HR1 (R3c_post Q) ;; HR1 (\<not> R3c_pre R))) = R3c_pre(\<not> (HR1 Q \<and> \<not> $wait\<acute> ;; HR1 (\<not> R)))"
    by rel_auto
  have 3:"(HR1 (R3c_post Q) ;; HR1 (R3c_post S)) = R3c_post (HR1 Q ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 S))"
    by rel_auto
  show ?thesis
    apply (simp add: HR3_semir_form HR1_HR3_commute[THEN sym] HR1_HR3_design unrest)
    apply (subst HR1_design_composition)
    apply (simp_all add: unrest assms R3c_pre_conj 1 2 3)
  done
qed

lemma HR2s_design: "HR2s(P \<turnstile> Q) = (HR2s(P) \<turnstile> HR2s(Q))"
  by (simp add: design_def HR2s_def R2s_def usubst TI2_def)

lemma HR2c_design: "HR2c(P \<turnstile> Q) = (HR2c(P) \<turnstile> HR2c(Q))"
  by (rel_auto)

lemma HR2c_conj: "HR2c(P \<and> Q) = (HR2c(P) \<and> HR2c(Q))"
  by (simp add: HR2c_def TI2_conj R2c_and)

lemma HR2c_disj: "HR2c(P \<or> Q) = (HR2c(P) \<or> HR2c(Q))"
  by (simp add: HR2c_def TI2_disj R2c_disj)

lemma HR2s_true: "HR2s(true) = true"
  by rel_auto

lemma HR2s_false: "HR2s(false) = false"
  by rel_auto

lemma HR2s_disj: "HR2s(P \<or> Q) = (HR2s(P) \<or> HR2s(Q))"
  by (rel_auto)

lemma HR2s_conj: "HR2s(P \<and> Q) = (HR2s(P) \<and> HR2s(Q))"
  by (rel_auto)

lemma HR2s_USUP:
  "HR2s(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> HR2s(P(i)))"
  by (simp add: HR2s_def TI2_USUP R2s_USUP)

lemma HR2s_UINF:
  "HR2s(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> HR2s(P(i)))"
  by (simp add: HR2s_def TI2_UINF R2s_UINF)

lemma HR2s_not: "HR2s(\<not> P) = (\<not> (HR2s P))"
  by (rel_auto)

lemma R2s_HTI_commute: "R2s(HTI(P)) = HTI(R2s(P))"
  by (rel_auto)

lemma R2_skip_ti: "R2(II\<^sub>H) = II\<^sub>H"
  apply (simp add: II\<^sub>H_def R2_def R2s_conj R2s_disj R2s_skip_r R2s_not R2s_ok)
  apply (rel_auto)
done

lemma R2_HR3_commute: "R2(HR3(P)) = HR3(R2(P))"
  by (simp add: HR3_def R2_skip_ti R2_condr' R2s_wait)

lemma HR2_alt_def: "HR2(P) = R1(HR2s(P))"
  by (rel_auto)

lemma HR2_HR3_commute: "HR2(HR3(P)) = HR3(HR2(P))"
  by (simp add: HR2_def R2_HR3_commute TI2_HR3_commute)

lemma R1_HR3_commute: "R1(HR3(P)) = HR3(R1(P))"
  by (rel_auto)

lemma HR2c_HR1_true: "HR2c(HR1(true)) = HR1(true)"
  by (rel_auto)

lemma unrest_ok_HR2s [unrest]: "$ok \<sharp> P \<Longrightarrow> $ok \<sharp> HR2s(P)"
  by (simp add: HR2s_def R2s_def TI2_def unrest)

lemma unrest_ok'_HR2s [unrest]: "$ok\<acute> \<sharp> P \<Longrightarrow> $ok\<acute> \<sharp> HR2s(P)"
  by (simp add: HR2s_def R2s_def TI2_def unrest)

lemma HR2_seq:
  "HR2(HR2(P) ;; HR2(Q)) = (HR2(P) ;; HR2(Q))"
  by (metis (no_types, lifting) HR2_def R2_TI2_commute R2_seqr_distribute TI2_seq)

lemma HR2_HR1_true: "HR2(HR1(true)) = HR1(true)"
  by (rel_auto)

lemma HR1_HR2s: "HR1(HR2s(P)) = HR1(HR2(P))"
  by (simp add: HR1_def HR2_alt_def R1_idem)

lemma HR2c_false: "HR2c(false) = false"
  by (rel_auto)

lemma HR2c_true: "HR2c(true) = true"
  by (rel_auto)

lemma HR2c_not: "HR2c(\<not> P) = (\<not> HR2c(P))"
  by (rel_auto)

lemma HR2c_and: "HR2c(P \<and> Q) = (HR2c(P) \<and> HR2c(Q))"
  by (rel_auto)

lemma HR2c_HR1: "HR2c(HR1(P)) = HR2(HR1(P))"
  by (rel_auto)

lemma HR1_HR2_commute: "HR1(HR2(P)) = HR2(HR1(P))"
  by (rel_auto)

lemma HR2s_wait: "HR2s($wait) = $wait"
  by (rel_auto)

lemma HR2s_wait': "HR2s($wait\<acute>) = $wait\<acute>"
  by (rel_auto)

lemma HR2s_skip_lift_d: "HR2s(\<lceil>II\<rceil>\<^sub>D) = \<lceil>II\<rceil>\<^sub>D"
apply (rel_auto)
by (smt alpha_rp'.ext_inject alpha_rp'.surjective alpha_rp'.update_convs(2) alpha_rp'.update_convs(4) eq_iff_diff_eq_0 htime.ext_inject htime.surjective htime.update_convs(1) list_minus_anhil)

lemma HR2s_cond: "HR2s(P \<triangleleft> b \<triangleright> Q) = (HR2s(P) \<triangleleft> HR2s(b) \<triangleright> HR2s(Q))"
  by (simp add: cond_def HR2s_conj HR2s_disj HR2s_not)
  
lemma HR_HR2c_def: "HR(P) = HR3(HR1(HR2c(P)))"
  by (metis (no_types, hide_lams) HR1_HR2_commute HR1_HR2s HR1_HR3_commute HR1_extend_conj' HR2_HR3_commute HR2c_HR1 HR2c_HR1_true HR2c_and HR_def utp_pred.inf_top_right)

lemma HR1_HR2s_HR2c: "HR1(HR2s(P)) = HR1(HR2c(P))"
  by (metis HR1_def HR2_alt_def HR2_def HR2c_def R1_R2c_is_R2)

lemma HR_design_composition: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q" "$ok \<sharp> R" "$ok \<sharp> S"
  shows "(HR(P \<turnstile> Q) ;; HR(R \<turnstile> S)) = 
       HR((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                       (HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S))))"
proof -
  have 1: "HR2c (HR1 (\<not> HR2s P) ;; HR1 true) = (HR1 (\<not> HR2s P) ;; HR1 true)"
    by (metis (no_types, lifting) HR1_HR2_commute HR1_HR2s HR1_seq HR2_HR1_true HR2_seq HR2c_HR1 HR2s_not)


  have 2:"HR2c (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R)) = (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))"
  proof -
    have "HR2c (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R)) = HR1 (HR2 (HR1 (HR2s (Q \<and> \<not> $wait\<acute>)) ;; HR1 (\<not> HR2s R)))"
      by (metis (no_types, lifting) HR1_HR2_commute HR1_extend_conj HR1_seq HR2c_HR1 HR2s_conj HR2s_not HR2s_wait') 
    also have "... = HR1 (HR2 (HR2 (HR1 (Q \<and> \<not> $wait\<acute>)) ;; HR2 (HR1 (\<not> R))))"
      by (metis (no_types, hide_lams) HR1_HR2_commute HR1_HR2s HR2s_not)
    also have "... = (HR2 (HR1 (Q \<and> \<not> $wait\<acute>)) ;; HR2 (HR1 (\<not> R)))"
      by (metis (no_types, lifting) HR1_HR2_commute HR1_seq HR2_seq)
    also have "... = (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))"
      by (metis (no_types, lifting) HR1_HR2_commute HR1_HR2s HR1_extend_conj HR2s_conj HR2s_not HR2s_wait')
    finally show ?thesis .
  qed

  have 3: "HR2c(HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S))) = (HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S)))"
    sorry

  have "(HR1(HR2s(HR3(P \<turnstile> Q))) ;; HR1(HR2s(HR3(R \<turnstile> S)))) =
        (HR3(HR1(HR2s(P) \<turnstile> HR2s(Q))) ;; HR3(HR1(HR2s(R) \<turnstile> HR2s(S))))"
    by (metis (no_types, lifting) HR1_def HR2_HR3_commute HR1_HR3_commute R1_HR3_commute HR2_alt_def HR2s_design)
  also have "... = HR3 (HR1 ((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                       (HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S)))))"
    by (simp add: HR3_HR1_design_composition unrest assms)

  also have "... = HR3(HR1(HR2c((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                              (HR1 (HR2s Q) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S))))))"
    by (simp add: HR2c_design HR2c_and HR2c_not 1 2 3)
  finally show ?thesis
    by (metis HR_HR2c_def HR_def)
qed

lemma HR1_false: "HR1(false) = false"
  by (pred_auto)

lemma HR2s_not_wait': "HR2s(\<not>$wait\<acute>) = (\<not>$wait\<acute>)"
  by rel_auto

lemma HR2s_tr'_eq_tr: "HR2s($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  apply (rel_auto)
  using list_minus_anhil apply blast
done

lemma HR2s_ref'_eq_ref: "HR2s($ref\<acute> =\<^sub>u $ref) = ($ref\<acute> =\<^sub>u $ref)"
  by (rel_auto)

lemma HR2s_hy'_eq_hy: "HR2s ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H) = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H)"
  by (rel_auto)

lemma HR_des_eqI: "\<lbrakk> P = R; Q = S \<rbrakk> \<Longrightarrow> HR(P \<turnstile> Q) = HR(R \<turnstile> S)"
  by (simp)

lemma HR_des_tri_eqI: "\<lbrakk> P = R; Q\<^sub>1 = S\<^sub>1; Q\<^sub>2 = S\<^sub>2 \<rbrakk> \<Longrightarrow> HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) = HR(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)"
  by (simp)

lemma HR2s_dur: "HR2s(\<L>) = \<L>"
  by (rel_auto)

lemma HR2s_bop: "HR2s(bop f u v) = bop f (HR2s(u)) (HR2s(v))"
  by (pred_auto)

lemma HR2s_ueq: "HR2s(u =\<^sub>u v) = (HR2s(u) =\<^sub>u HR2s(v))"
  by pred_auto

lemma HR2s_pre_lit: "HR2s \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub>< = \<lceil>\<guillemotleft>x\<guillemotright>\<rceil>\<^sub><"
  by (pred_auto)

lemma HR1_subst_wait'_true [usubst]: "(HR1(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = (HR1(P\<lbrakk>true/$wait\<acute>\<rbrakk>))"
  by (rel_auto)

lemma HR1_subst_wait'_false [usubst]: "(HR1(P))\<lbrakk>false/$wait\<acute>\<rbrakk> = (HR1(P\<lbrakk>false/$wait\<acute>\<rbrakk>))"
  by (rel_auto)

lemma HR2s_subst_wait'_true [usubst]: "(HR2s(P))\<lbrakk>true/$wait\<acute>\<rbrakk> = (HR2s(P\<lbrakk>true/$wait\<acute>\<rbrakk>))"
  by (simp add: HR2s_def usubst R2s_def TI2_def)

lemma HR2s_subst_wait'_false [usubst]: "(HR2s(P))\<lbrakk>false/$wait\<acute>\<rbrakk> = (HR2s(P\<lbrakk>false/$wait\<acute>\<rbrakk>))"
  by (simp add: HR2s_def usubst R2s_def TI2_def)

lemma HR1_wait'_cond: "HR1(P \<diamondop> Q) = HR1(P) \<diamondop> HR1(Q)"
  by rel_auto

lemma HR2s_wait'_cond: "HR2s(P \<diamondop> Q) = HR2s(P) \<diamondop> HR2s(Q)"
  by (simp add: wait'_cond_def HR2s_def R2s_def TI2_def usubst)

lemma HR1_unrest [unrest]: "\<lbrakk> x \<sharp> P; in_var tr \<bowtie> x; out_var tr \<bowtie> x; in_var time \<bowtie> x; out_var time \<bowtie> x \<rbrakk> \<Longrightarrow> x \<sharp> HR1(P)"
  by (simp add: HR1_def TI1_def R1_def HTI_def unrest)

lemma HR2s_unrest [unrest]: "\<lbrakk> uvar x; x \<sharp> P; in_var tr \<bowtie> x; out_var tr \<bowtie> x; in_var time \<bowtie> x; out_var time \<bowtie> x \<rbrakk> \<Longrightarrow> x \<sharp> HR2s(P)"
  by (simp add: HR2s_def R2s_def TI2_def unrest lens_indep_sym)

lemma HR2s_H1_commute: "HR2s(H1(P)) = H1(HR2s(P))"
  by (rel_auto)

lemma HR2s_H2_commute: "HR2s(H2(P)) = H2(HR2s(P))"
  by (simp add: HR2s_def TI2_H2_commute R2s_H2_commute)

lemma hskip_non_term:
  "II\<^sub>H\<^sup>f = (\<not> $ok \<and> HR1(true))"
  by (rel_auto)

lemma HR3_H2_commute: "HR3(H2(P)) = H2(HR3(P))"
  by (rel_auto, simp_all add: alpha_d.equality)

lemma HR1_H1_HR3_commute: "HR1(H1(HR3(P))) = HR3(HR1(H1(P)))"
  by (rel_auto)

lemma HR3_subst_wait: "HR3(P) = HR3(P\<lbrakk>false/$wait\<rbrakk>)"
  by (metis HR3_def cond_var_subst_right wait_uvar)

lemma HR1_H1_HR1: "HR1(H1(HR1(P))) = HR1(H1(P))"
  by (rel_auto)

lemma HR2c_unrest [unrest]:
  assumes "uvar x" "x \<sharp> P" "x \<bowtie> in_var tr" "x \<bowtie> out_var tr" "x \<bowtie> in_var time" "x \<bowtie> out_var time"
  shows "x \<sharp> HR2c(P)"
  using assms by (simp add: HR2c_def R2c_def TI2_def R2s_def R1_def unrest usubst lens_indep_sym)

lemma HR1_HCSP1_commute: "HR1(HCSP1(P)) = HCSP1(HR1(P))"
  by (rel_auto)

lemma HR2c_HCSP1_commute: "HR2c(HCSP1(P)) = HCSP1(HR2c(P))"
  by (rel_auto)

lemma HR2c_H2_commute:"HR2c(H2(P)) = H2(HR2c(P))"
  by (simp add: H2_split HR2c_def usubst R2c_def TI2_def R2s_def R1_def, rel_auto)

lemma R2c_TI2_commute: "R2c(TI2(P)) = TI2(R2c(P))"
  by (simp add: R2c_def TI2_def R2s_def R1_def usubst)

lemma HR2c_idem: "HR2c(HR2c(P)) = HR2c(P)"
  by (simp add: HR2c_def R2c_TI2_commute R2c_idem TI2_idem)

lemma HR2c_mono: "P \<sqsubseteq> Q \<Longrightarrow> HR2c(P) \<sqsubseteq> HR2c(Q)"
  by (rel_auto)

lemma HR1_HR2c_commute: "HR1(HR2c(P)) = HR2c(HR1(P))"
  by (metis HR1_HR2_commute HR1_HR2s HR1_HR2s_HR2c HR2c_HR1)

lemma HR2c_HR3_commute: "HR2c(HR3(P)) = HR3(HR2c(P))"
  by (simp add: HR2c_def HR3_def usubst TI2_cond R2c_condr TI2_skip_ti R2c_hskip TI2_wait R2c_wait)

lemma HR1_HR: "HR1(HR(P)) = HR(P)"
  by (simp add: HR_def HR1_idem)

lemma HR1_HCSP: "HR1(HCSP(P)) = HCSP(P)"
  by (simp add: HCSP_def HR1_HCSP1_commute HR1_H2_commute HR1_HR)

lemma HR2c_HR: "HR2c(HR(P)) = HR(P)"
  by (simp add: HR_HR2c_def HR2c_HR3_commute HR1_HR2c_commute HR2c_idem)

lemma HR2c_HCSP: "HR2c(HCSP(P)) = HCSP(P)"
  by (simp add: HCSP_def HR2c_HCSP1_commute HR2c_H2_commute HR2c_HR)

lemma list_ge_nil [simp]: "(x \<ge>\<^sub>u \<langle>\<rangle>) = true"
  by (pred_auto)

lemma HR2c_subst [usubst]: 
  "\<lbrakk> $time \<sharp> \<sigma>; $time\<acute> \<sharp> \<sigma>; $tr \<sharp> \<sigma>; $tr\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow> (\<sigma> \<dagger> (HR2c P)) = HR2c(\<sigma> \<dagger> P)"
  by (simp add: HR2c_def TI2_def R2c_def R2s_def R1_def usubst unrest)

lemma HCSP_is_HR1:
  assumes "P is HCSP" 
  shows "P is HR1"
proof -
  from assms have "P = HCSP(P)"
    by (simp add: Healthy_def')
  moreover have "... = HR1(HCSP(P))"
    by (simp add: HR1_HCSP)
  ultimately show ?thesis
    by (simp add: Healthy_def')
qed

lemma HCSP_is_HR2c:
  assumes "P is HCSP" 
  shows "P is HR2c"
proof -
  from assms have "P = HCSP(P)"
    by (simp add: Healthy_def')
  moreover have "... = HR2c(HCSP(P))"
    by (simp add: HR2c_HCSP)
  ultimately show ?thesis
    by (simp add: Healthy_def')
qed

lemma HR3_idem: "HR3(HR3(P)) = HR3(P)"
  by (rel_auto)

lemma HR3_mono: "P \<sqsubseteq> Q \<Longrightarrow> HR3(P) \<sqsubseteq> HR3(Q)"
  by (rel_auto)

lemma HR3_disj: "HR3(P \<or> Q) = (HR3(P) \<or> HR3(Q))"
  by (rel_auto)

lemma HR3_USUP:
  assumes "A \<noteq> {}"
  shows "HR3(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> HR3(P(i)))"
  using assms by (rel_auto)

lemma HR3_UINF:
  assumes "A \<noteq> {}"
  shows "HR3(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> HR3(P(i)))"
  using assms by (rel_auto)

lemma HR_idem: "HR(HR(P)) = HR(P)"
  by (simp add: HR_R2c_def HR1_HR2c_commute HR1_HR3_commute HR1_idem HR2c_HR3_commute HR2c_idem HR3_idem)

lemma HR_mono: "P \<sqsubseteq> Q \<Longrightarrow> HR(P) \<sqsubseteq> HR(Q)"
  by (simp add: HR_R2c_def HR3_mono HR2c_mono HR1_mono)

lemma HR_disj: "HR(P \<or> Q) = (HR(P) \<or> HR(Q))"
  by (simp add: HR_def HR1_disj HR2s_disj HR3_disj)

lemma HR_USUP:
  assumes "A \<noteq> {}"
  shows "HR(\<Sqinter> i \<in> A \<bullet> P(i)) = (\<Sqinter> i \<in> A \<bullet> HR(P(i)))"
  using assms by (simp add: HR_def HR1_USUP HR2s_USUP HR3_USUP)

lemma HR_UINF:
  assumes "A \<noteq> {}"
  shows "HR(\<Squnion> i \<in> A \<bullet> P(i)) = (\<Squnion> i \<in> A \<bullet> HR(P(i)))"
  using assms by (simp add: HR_def HR1_UINF HR2s_UINF HR3_UINF)

lemma HCSP1_HR1_commute: "HCSP1(HR1(P)) = HR1(HCSP1(P))"
  by (rel_auto)

lemma HCSP1_HR2c_commute: "HCSP1(HR2c(P)) = HR2c(HCSP1(P))"
  by (rel_auto)

lemma HCSP1_HR3_commute: "HCSP1(HR3(P)) = HR3(HCSP1(P))"
  by (rel_auto)

lemma HCSP1_HR_commute: "HCSP1(HR(P)) = HR(HCSP1(P))"
  by (simp add: HR_R2c_def HCSP1_HR1_commute HCSP1_HR2c_commute HCSP1_HR3_commute)

lemma H2_HR1_commute: "H2(HR1(P)) = HR1(H2(P))"
  by (rel_auto)

lemma hskip_J: "(II\<^sub>H ;; J) = II\<^sub>H"
  by (rel_auto, simp add: alpha_d.equality)

lemma H2_HR3_commute: "H2(HR3(P)) = HR3(H2(P))"
  by (simp add: H2_def HR3_def cond_def seqr_or_distl hskip_J seqr_pre_out unrest)
  
lemma H2_HR_commute: "H2(HR(P)) = HR(H2(P))"
  by (simp add: HR_R2c_def H2_HR1_commute HR2c_H2_commute[THEN sym] H2_HR3_commute)

lemma HCSP1_H2_commute: "HCSP1(H2(P)) = H2(HCSP1(P))"
  by (rel_auto)

lemma HCSP_idem: "HCSP(HCSP(P)) = HCSP(P)"
  by (simp add: HCSP_def H2_HR_commute HCSP1_HR_commute HCSP1_H2_commute HR_idem H2_idem HCSP1_idem)

lemma H1_HR2s_commute: "H1(HR2s(P)) = HR2s(H1(P))"
  by (simp add: HR2s_def R2s_def TI2_def H1_def usubst)

lemma H1_HR2c_commute: "H1(HR2c(P)) = HR2c(H1(P))"
  by (simp add: H1_def HR2c_def R2c_def R2s_def TI2_def usubst, rel_auto)

lemma HCSP1_HR_H1: "HCSP1(HR(P)) = HR(H1(P))"
  apply (simp add: HR_R2c_def HCSP1_HR1_H1[THEN sym] HR2c_HR3_commute HR1_H1_HR3_commute)
  apply (simp add: H1_HR2c_commute HR1_HR3_commute)
done

lemma HCSP_hybrid_reactive_design_form:
  "HCSP(P) = HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
proof -
  have "HCSP(P) = HCSP1(H2(HR1(HR2s(HR3(P)))))"
    by (metis HCSP_def HR_def assms)
  also have "... = HCSP1(HR1(H2(HR2s(HR3(P)))))"
    by (simp add: HR1_H2_commute)
  also have "... = HR1(H1(HR1(H2(HR2s(HR3(P))))))"
    by (simp add: HCSP1_HR1_H1 HR1_idem)
  also have "... = HR1(H1(H2(HR2s(HR3(HR1(P))))))"
    by (simp add: HCSP1_HR1_H1 HR1_H2_commute HR1_HR2_commute HR1_HR2s HR1_HR3_commute)
  also have "... = HR1(HR2s(H1(H2(HR3(HR1(P))))))"
    by (simp add: HR2s_H1_commute HR2s_H2_commute)
  also have "... = HR1(HR2s(H1(HR3(H2(HR1(P))))))"
    by (simp add: HR3_H2_commute)
  also have "... = HR2(HR1(H1(HR3(H2(HR1(P))))))"
    by (simp add: HR1_HR2_commute HR1_HR2s)
  also have "... = HR2(HR3(HR1(H1(H2(HR1(P))))))"
    by (simp add: HR1_H1_HR3_commute)
  also have "... = HR2(HR3(HR1(H1(H2(P)))))"
    by (simp add: HCSP1_HR1_H1 HR1_H2_commute HR1_idem)
  also have "... = HR(H1_H2(P))"
    by (simp add: HR1_HR2_commute HR1_HR2s HR1_HR3_commute HR_def)
  also have "... = HR((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
  proof -
    have 0:"(\<not> (H1_H2(P))\<^sup>f) = ($ok \<and> \<not> P\<^sup>f)"
      by (simp add: H1_def H2_split, pred_auto)
    have 1:"(H1_H2(P))\<^sup>t = ($ok \<Rightarrow> (P\<^sup>f \<or> P\<^sup>t))"
      by (simp add: H1_def H2_split, pred_auto)
    have "(\<not> (H1_H2(P))\<^sup>f) \<turnstile> (H1_H2(P))\<^sup>t = ((\<not> P\<^sup>f) \<turnstile> P\<^sup>t)"
      by (simp add: 0 1, pred_auto)
    thus ?thesis
      by (metis H1_H2_commute H1_H2_is_design H1_idem H2_idem Healthy_def')
  qed
  also have "... = HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (metis HR3_subst_wait HR_def subst_not wait_false_design)
  finally show ?thesis .
qed

lemma HCSP_hybrid_reactive_design:
  assumes "P is HCSP"
  shows "P = HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
  by (metis HCSP_hybrid_reactive_design_form Healthy_def' assms)

abbreviation "pre\<^sub>s  \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s false, $wait \<mapsto>\<^sub>s false]"
abbreviation "peri\<^sub>s \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s true]"
abbreviation "post\<^sub>s \<equiv> [$ok \<mapsto>\<^sub>s true, $ok\<acute> \<mapsto>\<^sub>s true, $wait \<mapsto>\<^sub>s false, $wait\<acute> \<mapsto>\<^sub>s false]"

abbreviation "npre\<^sub>H(P) \<equiv> pre\<^sub>s \<dagger> P"

definition [upred_defs]: "pre\<^sub>H(P)  = (\<not> (npre\<^sub>H(P)))" 
definition [upred_defs]: "peri\<^sub>H(P) = (peri\<^sub>s \<dagger> P)"
definition [upred_defs]: "post\<^sub>H(P) = (post\<^sub>s \<dagger> P)"

lemma HCSP_hybrid_reactive_tri_design:
  assumes "P is HCSP"
  shows "P = HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> P\<^sup>t\<^sub>f\<lbrakk>false/$wait\<acute>\<rbrakk>)"
  by (simp add: HCSP_hybrid_reactive_design assms wait'_cond_split)

lemma HCSP_hybrid_reactive_tri_design':
  assumes "P is HCSP"
  shows "P = HR(pre\<^sub>H(P) \<turnstile> peri\<^sub>H(P) \<diamondop> post\<^sub>H(P))"
  apply (subst HCSP_hybrid_reactive_tri_design[OF assms])
  apply (simp add: usubst)
  apply (subst design_subst_ok_ok'[THEN sym])
  apply (simp add: pre\<^sub>H_def peri\<^sub>H_def post\<^sub>H_def usubst unrest)
done

(* TODO: Do this proof properly *)

lemma hskip_reactive_design:
  "II\<^sub>H = HR(true \<turnstile> II)"
proof -
  have 1:"TI2 (true \<turnstile> II) = (true \<turnstile> II)"
    by (simp add: design_def impl_alt_def TI2_disj TI2_not TI2_ok TI2_conj TI2_skip, rel_auto)
  have 2:"R2c (true \<turnstile> II) = (true \<turnstile> II)"
    by (rel_auto, smt alpha_d.surjective alpha_d.update_convs(2) alpha_rp'.surjective alpha_rp'.update_convs(2) append_Nil2 prefix_subst1 strict_prefixE)
  have 3: "HR1(II\<^sub>H \<triangleleft> $wait \<triangleright> true \<turnstile> II) = II\<^sub>H"
    by (rel_auto)
  show ?thesis
    by (simp add: HR2c_def TI2_cond TI2_wait TI2_skip_ti HR_R2c_def HR3_def R2c_condr R2c_hskip R2c_wait 1 2 3)
qed

lemma HR_design_wait_false: "HR(P \<^sub>f \<turnstile> Q \<^sub>f) = HR(P \<turnstile> Q)"
  by (metis HR3_subst_wait HR_R2c_def wait_false_design)

lemma design_okay_true: "(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true/$ok\<rbrakk>) = (P \<turnstile> Q)"
proof -
  have "(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true/$ok\<rbrakk>) = ($ok \<and> P\<lbrakk>true/$ok\<rbrakk> \<Rightarrow> $ok\<acute> \<and> Q\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: design_def)
  also have "... = ($ok \<and> P \<Rightarrow> $ok\<acute> \<and> Q\<lbrakk>true/$ok\<rbrakk>)"
    by (metis conj_pos_var_subst uvar_ok)
  also have "... = ($ok \<and> P \<Rightarrow> $ok\<acute> \<and> $ok \<and> Q\<lbrakk>true/$ok\<rbrakk>)"
    by (pred_auto)
  also have "... = ($ok \<and> P \<Rightarrow> $ok\<acute> \<and> $ok \<and> Q)"
    by (metis conj_pos_var_subst uvar_ok)
  also have "... = ($ok \<and> P \<Rightarrow> $ok\<acute> \<and> Q)"
    by (pred_auto)
  also have "... = (P \<turnstile> Q)"
    by (simp add: design_def)
  finally show ?thesis .
qed

lemma HR_design_okay_true: "HR(P\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> Q\<lbrakk>true,false/$ok,$wait\<rbrakk>) = HR(P \<turnstile> Q)"
proof -
  have "HR(P \<turnstile> Q) = HR(P\<lbrakk>true/$ok\<rbrakk> \<turnstile> Q\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: design_okay_true)
  also have "... = HR(P\<lbrakk>true/$ok\<rbrakk>\<^sub>f \<turnstile> Q\<lbrakk>true/$ok\<rbrakk>\<^sub>f)"
    by (simp add: HR_design_wait_false)
  also have "... = HR(P\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> Q\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
    by (simp add: usubst)
  finally show ?thesis ..
qed

lemma hskip_reactive_tri_design:
  "II\<^sub>H = HR(true \<turnstile> false \<diamondop> II)"
proof -
  have "II\<^sub>H = HR(true \<turnstile> II)" 
    by (simp add: hskip_reactive_design)
  also have "... = HR(true \<^sub>f \<turnstile> II \<^sub>f)"
    by (metis HR_design_wait_false)
  also have "... = HR(true \<^sub>f \<turnstile> (\<not> $wait\<acute> \<and> II) \<^sub>f)" (is "HR(_ \<turnstile> ?II) = ?rhs")
  proof -
    have "?II = ($wait\<acute> =\<^sub>u $wait \<and> II\<restriction>\<^sub>\<alpha>wait) \<^sub>f"
      by (subst skip_r_unfold[of wait], simp_all)
    also have "... = ($wait\<acute> =\<^sub>u false \<and> $wait\<acute> =\<^sub>u $wait \<and> II\<restriction>\<^sub>\<alpha>wait) \<^sub>f"
      by (simp add: usubst)
    also have "... = ($wait\<acute> =\<^sub>u false \<and> II) \<^sub>f"
      by (metis (no_types, lifting) skip_r_unfold upred_eq_false utp_pred.conj_assoc wait_uvar)
    finally show ?thesis by simp
  qed
  also have "... = HR(true \<turnstile> false \<diamondop> II)"
    by (simp add: wait'_cond_def cond_def HR_design_wait_false)
  finally show ?thesis .
qed
   
lemma HR_design_lemma1:
  "HR(P \<turnstile> (HR1(HR2c(Q)) \<or> R) \<diamondop> S) = HR(P \<turnstile> (Q \<or> R) \<diamondop> S)"
  by (simp add: design_def impl_alt_def wait'_cond_def HR_R2c_def HR2c_HR3_commute HR1_HR3_commute HR1_disj HR2c_disj HR2c_conj HR1_cond HR2c_cond HR1_HR2c_commute HR2c_idem HR1_extend_conj' HR1_idem)

lemma HR_design_tri_composition: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait\<acute> \<sharp> Q\<^sub>1" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; HR(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) = 
       HR((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                       ((Q\<^sub>1 \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> ((HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))))"
proof -
  have 1:"(\<not> (HR1 (HR2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) = 
        (\<not> (HR1 (HR2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R)))"
    by (metis (no_types, lifting) HR1_extend_conj HR2s_conj HR2s_not_wait' wait'_cond_false)
  have 2: "(HR1 (HR2s (Q\<^sub>1 \<diamondop> Q\<^sub>2)) ;; (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s (S\<^sub>1 \<diamondop> S\<^sub>2)))) =
                 ((HR1 (HR2s Q\<^sub>1) \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))"
  proof -
    have "(HR1 (HR2s Q\<^sub>1) ;; $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))
                       = (HR1 (HR2s Q\<^sub>1) \<and> $wait\<acute>)"
    proof -
      have "(HR1 (HR2s Q\<^sub>1) ;; $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2))) 
           = (HR1 (HR2s Q\<^sub>1) ;; $wait \<and> \<lceil>II\<rceil>\<^sub>D)"
        by (rel_auto)
      also have "... = ((HR1 (HR2s Q\<^sub>1) ;; \<lceil>II\<rceil>\<^sub>D) \<and> $wait\<acute>)"
        by (rel_auto)
      also from assms(2) have "... = ((HR1 (HR2s Q\<^sub>1)) \<and> $wait\<acute>)"
        by (simp add: lift_des_skip_dr_unit_unrest unrest)
      finally show ?thesis .
    qed
 
    moreover have "(HR1 (HR2s Q\<^sub>2) ;; \<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))
                  = ((HR1 (HR2s Q\<^sub>2)) ;; (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))"
    proof - 
      have "(HR1 (HR2s Q\<^sub>2) ;; \<not> $wait \<and> (\<lceil>II\<rceil>\<^sub>D \<triangleleft> $wait \<triangleright> HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))
            = (HR1 (HR2s Q\<^sub>2) ;; \<not> $wait \<and> (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))"
        by (metis (no_types, lifting) cond_def conj_disj_not_abs utp_pred.double_compl utp_pred.inf.left_idem utp_pred.sup_assoc utp_pred.sup_inf_absorb)

      also have "... = ((HR1 (HR2s Q\<^sub>2))\<lbrakk>false/$wait\<acute>\<rbrakk> ;; (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2))\<lbrakk>false/$wait\<rbrakk>)"
        by (metis false_alt_def seqr_right_one_point upred_eq_false wait_uvar)

      also have "... = ((HR1 (HR2s Q\<^sub>2)) ;; (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2)))"
        by (simp add: wait'_cond_def usubst unrest assms)
      
      finally show ?thesis .
    qed
      
    moreover
    have "((HR1 (HR2s Q\<^sub>1) \<and> $wait\<acute>) \<or> ((HR1 (HR2s Q\<^sub>2)) ;; (HR1 (HR2s S\<^sub>1) \<diamondop> HR1 (HR2s S\<^sub>2))))
          = (HR1 (HR2s Q\<^sub>1) \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> ((HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))"
      by (simp add: wait'_cond_def cond_seq_right_distr cond_and_T_integrate unrest)

    ultimately show ?thesis
      by (simp add: HR2s_wait'_cond HR1_wait'_cond wait'_cond_seq)
  qed

  show ?thesis
    apply (subst HR_design_composition)
    apply (simp_all add: assms)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: assms wait'_cond_def unrest)
    apply (simp add: 1 2)
    apply (simp add: HR1_HR2s_HR2c HR_design_lemma1)
  done
qed

abbreviation hseqr :: "'\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" (infixr ";;\<^sub>h" 15) where
"(P ;;\<^sub>h Q) \<equiv> ((P::'\<alpha> hrelation) ;; (Q::'\<alpha> hrelation))"

lemma HR_design_tri_composition': 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait\<acute> \<sharp> Q\<^sub>1" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; HR(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) = 
       HR((\<not> (HR1 (\<not> HR2c P) ;; HR1 true) \<and> \<not> (HR1 (HR2c Q\<^sub>2) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2c R))) \<turnstile>
                       ((Q\<^sub>1 \<or> (HR1 (HR2c Q\<^sub>2) ;; HR1 (HR2c S\<^sub>1))) \<diamondop> ((HR1 (HR2c Q\<^sub>2) ;; HR1 (HR2c S\<^sub>2)))))"
proof -
  have f1: "(HR (P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) ;; HR (R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) = HR (((\<not> (HR1 (\<not> HR2s P) ;;\<^sub>h HR1 true)) \<and> \<not> (HR1 (HR2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) 
                                                        \<turnstile> (Q\<^sub>1 \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))"
    by (simp add: HR_design_tri_composition assms) 
  have f2: "HR1 (\<not> HR2s P) = HR1 (HR2c (\<not> P))"
    by (metis (no_types) HR1_HR2s_HR2c HR2s_not)
  have "HR1 (\<not> HR2s R) = HR1 (HR2c (\<not> R))"
    by (metis (full_types) HR1_HR2s_HR2c HR2s_not)
  then show ?thesis
    using f2 f1 by (simp add: HR1_HR2s_HR2c HR2c_not)
qed

(*
lemma HR_design_tri_composition_frame: 
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> Q\<^sub>1" "$ok\<acute> \<sharp> Q\<^sub>2" "$ok \<sharp> R" "$ok \<sharp> S\<^sub>1" "$ok \<sharp> S\<^sub>2"
          "$wait\<acute> \<sharp> Q\<^sub>1" "$wait\<acute> \<sharp> Q\<^sub>2" "$wait \<sharp> S\<^sub>1" "$wait \<sharp> S\<^sub>2"
  shows "(HR(w:\<lbrakk>P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2\<rbrakk>) ;; HR(w:\<lbrakk>R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2\<rbrakk>)) = 
       HR((\<not> (HR1 (\<not> HR2s P) ;; HR1 true) \<and> \<not> (HR1 (HR2s Q\<^sub>2) \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2s R))) \<turnstile>
                       ((HR1 (HR2s Q\<^sub>1) \<or> (HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>1))) \<diamondop> ((HR1 (HR2s Q\<^sub>2) ;; HR1 (HR2s S\<^sub>2)))))"
*)

lemma HR2s_time'_time_eq: "HR2s ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) = ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
  by (rel_auto)

lemma HR2s_time'_time_less: "HR2s ($time\<acute> - $time <\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) = ($time\<acute> - $time <\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
  by (rel_auto)

lemma HR2c_hyst'_eq_hyst: "HR2c($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H) = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H)"
  by (simp add: HR2c_def TI2_def usubst R2c_def R2s_def, rel_auto)

lemma HR2c_tr'_eq_tr: "HR2c($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr)"
  by (simp add: HR2c_def TI2_def usubst R2c_tr'_minus_tr)

lemma HR1_tr'_eq_tr: "HR1($tr\<acute> =\<^sub>u $tr) = ($tr\<acute> =\<^sub>u $tr \<and> $time =\<^sub>u $time\<acute>)"
  by (rel_auto)
 
lemma hy_lift_unrest [unrest]: "$\<Sigma>\<^sub>H\<acute> \<sharp> \<lceil>\<lceil>P\<rceil>\<^sub><\<rceil>\<^sub>H"
  by (rel_auto)

lemma skip_h_lift_def:
  "\<lceil>II\<rceil>\<^sub>H = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H)"
  by (rel_auto)


lemma HR1_HR2c_frame:
  "HR1 (HR2c ($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>P\<rceil>\<^sub>H)) =
       ($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>P\<rceil>\<^sub>H)"
    apply (simp add: HR2c_def R2c_def R2s_def TI2_def usubst unrest HR1_def TI1_def R1_def)
    apply (rel_auto)
    using list_minus_anhil apply blast
done

lemma assigns_lift_hy_unfold:
  "($time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H) =  \<lceil>\<langle>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>h\<rangle>\<^sub>a\<rceil>\<^sub>R"
  by (rel_auto)

lemma assigns_lift_rea_unfold:
  "($wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>R) = \<lceil>\<langle>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>r\<rangle>\<^sub>a\<rceil>\<^sub>D"
  by (rel_auto)

lemma assigns_lift_des_unfold:
  "($ok\<acute> =\<^sub>u $ok \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>D) = \<langle>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>D\<rangle>\<^sub>a"
  by (rel_auto)

lemma assigns_hy_comp_lemma: 
  assumes "$ok \<sharp> P" "$wait \<sharp> P"
  shows "(($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H) ;; P)
         = (\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> P)"
proof -
  have "(($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H) ;; P) = 
        (($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H) ;; P)"
    by (simp add: seqr_insert_ident unrest assms)
  also have "... = (\<langle>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rangle>\<^sub>a ;; P)"
    by (simp add: assigns_lift_hy_unfold assigns_lift_rea_unfold assigns_lift_des_unfold, rel_auto)
  also have "... = (\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> P)"
    by (simp add: assigns_r_comp)
  finally show ?thesis .
qed

lemma hrd_HR1_neg_precond: "HR((\<not> HR1(\<not> P)) \<turnstile> Q) = HR(P \<turnstile> Q)"
  by (rel_auto)

  
lemma hybrid_reactive_design_is_HCSP:
  "\<lbrakk> $ok\<acute> \<sharp> P; $ok\<acute> \<sharp> Q \<rbrakk> \<Longrightarrow> HCSP(HR(P \<turnstile> Q)) = HR(P \<turnstile> Q)"
  by (simp add: HCSP_def HR_idem H2_HR_commute H2_design HCSP1_HR_H1 H1_design)

lemma HR1_peri: "HR1(peri\<^sub>H(P)) = peri\<^sub>H(HR1(P))"
  by (rel_auto)
  
lemma HR1_post: "HR1(post\<^sub>H(P)) = post\<^sub>H(HR1(P))"
  by (rel_auto)

lemma HR1_peri_post:
  assumes "P is HR1"
  shows "peri\<^sub>H(P) is HR1" "post\<^sub>H(P) is HR1"
  using assms
  by (metis HR1_peri HR1_post Healthy_def')+

lemma HR2c_pre: "HR2c(pre\<^sub>H(P)) = pre\<^sub>H(HR2c(P))"
  by (simp add: HR2c_not HR2c_subst HR2c_idem pre\<^sub>H_def unrest)

lemma HR2c_peri: "HR2c(peri\<^sub>H(P)) = peri\<^sub>H(HR2c(P))"
  by (simp add: HR2c_subst HR2c_idem peri\<^sub>H_def unrest)

lemma HR2c_post: "HR2c(post\<^sub>H(P)) = post\<^sub>H(HR2c(P))"
  by (simp add: HR2c_subst HR2c_idem post\<^sub>H_def unrest)

lemma HR2c_pre_peri_post:
  assumes "P is HR2c"
  shows "pre\<^sub>H(P) is HR2c" "peri\<^sub>H(P) is HR2c" "post\<^sub>H(P) is HR2c"
  using assms
  by (metis HR2c_pre HR2c_peri HR2c_post Healthy_def')+

lemma pre\<^sub>H_HR3: "pre\<^sub>H(HR3(P)) = pre\<^sub>H(P)"
  by (simp add: HR3_def pre\<^sub>H_def usubst unrest cond_unit_F)

lemma peri\<^sub>H_HR3: "peri\<^sub>H(HR3(P)) = peri\<^sub>H(P)"
  by (simp add: HR3_def peri\<^sub>H_def usubst unrest cond_unit_F)

lemma post\<^sub>H_HR3: "post\<^sub>H(HR3(P)) = post\<^sub>H(P)"
  by (simp add: HR3_def post\<^sub>H_def usubst unrest cond_unit_F)
  
lemma prog_subst_HR1: 
  "\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> HR1(P) = HR1(\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> P)"
  by (simp add: HR_def HR1_def TI1_def HTI_def R1_def usubst unrest)

lemma prog_subst_H2c [usubst]:
  "\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> HR2c(P) = HR2c(\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> P)"
  by (simp add: HR2c_def R2c_def R2s_def R1_def TI2_def usubst unrest)

lemma npre\<^sub>H_HR:
  "npre\<^sub>H(HR(P)) = HR1(HR2s(npre\<^sub>H(P)))"
  by (simp add: HR_def HR1_def TI1_def HTI_def R1_def R2s_def TI2_def usubst cond_unit_F HR2c_def HR2s_def HR3_def)

lemma npre\<^sub>H_tri_design: "npre\<^sub>H(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) = (\<not> P\<lbrakk>true,false/$ok,$ok\<acute>\<rbrakk>\<lbrakk>false/$wait\<rbrakk>)"
  by (simp add: pre\<^sub>H_def design_def usubst)

lemma pre\<^sub>H_hrd: "pre\<^sub>H(HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) = (\<not> (HR1(HR2s(\<not> P\<lbrakk>true,false/$ok,$ok\<acute>\<rbrakk>\<lbrakk>false/$wait\<rbrakk>))))"
  by (simp add: pre\<^sub>H_def usubst npre\<^sub>H_HR design_def)

lemma peri\<^sub>H_hrd:
  "peri\<^sub>H(HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) = HR1(HR2c(peri\<^sub>H(P) \<Rightarrow> peri\<^sub>H(Q\<^sub>1)))"
  apply (simp add: HR1_peri[THEN sym] HR2c_peri[THEN sym] HR_HR2c_def peri\<^sub>H_HR3)
  apply (simp add: design_def peri\<^sub>H_def usubst wait'_cond_def cond_unit_T)
done

lemma post\<^sub>H_hrd:
  "post\<^sub>H(HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) = HR1(HR2c(post\<^sub>H(P) \<Rightarrow> post\<^sub>H(Q\<^sub>2)))"
  apply (simp add: HR1_post[THEN sym] HR2c_post[THEN sym] HR_HR2c_def post\<^sub>H_HR3)
  apply (simp add: design_def post\<^sub>H_def usubst wait'_cond_def cond_unit_F)
done


lemma HR_start_instant:
  "($ok \<and> \<not> $wait \<and> HR(true \<turnstile> false \<diamondop> Q\<^sub>2)) = ($ok \<and> \<not> $wait \<and> HR(true \<turnstile> false \<diamondop> Q\<^sub>2) \<and> \<not> $wait\<acute>)"
  by (rel_auto)

lemma nok_HR_design: "(\<not> $ok \<and> HR(P \<turnstile> Q)) = (\<not> $ok \<and> HR(true))"
  by (rel_auto)

lemma wait_HR3: "($wait \<and> HR3(P)) = ($wait \<and> II\<^sub>H)"
  by (rel_auto)

lemma wait_HR: "($wait \<and> HR(P)) = ($wait \<and> II\<^sub>H)"
proof -
  have "($wait \<and> HR(P)) = HR1($wait \<and> HR2c(HR3(P)))"
    by (simp add: HR_R2c_def HR1_extend_conj')
  also have "... = HR1(HR2c($wait \<and> HR3(P)))"
    by (simp add: HR2c_conj HR2c_wait)
  also have "... = HR1(HR2c($wait \<and> II\<^sub>H))"
    by (simp add: wait_HR3)
  also have "... = HR1($wait \<and> II\<^sub>H)"
    by (simp add: HR2c_conj HR2c_wait HR2c_hskip)
  also have "... = ($wait \<and> II\<^sub>H)"
    by (simp add: HR1_extend_conj' HR1_hskip)
  finally show ?thesis .
qed

lemma subst_hyb_apply_lift [usubst]:
  "\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> \<lceil>P\<rceil>\<^sub>H = \<lceil>\<lceil>\<sigma>\<rceil>\<^sub>s \<dagger> P\<rceil>\<^sub>H"
  by (rel_auto)

lemma unrest_wait'_cond [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> Q; (out_var wait) \<bowtie> x \<rbrakk> \<Longrightarrow> x \<sharp> (P \<diamondop> Q)"
  by (simp add: wait'_cond_def unrest)

definition assigns_h :: "'\<alpha> usubst \<Rightarrow> ('t::time, '\<theta>, '\<alpha>) hhrd" ("\<langle>_\<rangle>\<^sub>H") where
"assigns_h \<sigma> = HR(true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H))"

definition "Miracle = HR(true \<turnstile> false \<diamondop> false)"

definition "Chaos = HR(false \<turnstile> true \<diamondop> true)"

definition "Stop = HR(true \<turnstile> (events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"

definition "Prefix a = HR(true \<turnstile> (events\<^sub>u($tr\<acute>-$tr) =\<^sub>u \<langle>\<rangle> \<and> a \<notin>\<^sub>u refusals\<^sub>u($tr\<acute>-$tr) \<and> ev\<^sub>u(a) \<notin>\<^sub>u $ref\<acute>) 
                               \<diamondop> ($tr\<acute>-$tr =\<^sub>u idleprefix\<^sub>u($tr\<acute>-$tr) ^\<^sub>u \<langle>ev\<^sub>u(a)\<rangle> \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> a \<notin>\<^sub>u refusals\<^sub>u($tr\<acute>-$tr)))"

definition Guard :: "('t::time, '\<theta>, '\<alpha>) hrdp \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd" (infix "&\<^sub>u" 65)
where "g &\<^sub>u A = HR((\<lceil>g\<rceil>\<^sub>< \<Rightarrow> pre\<^sub>H(A)) \<turnstile> ((peri\<^sub>H(A) \<triangleleft> \<lceil>g\<rceil>\<^sub>< \<triangleright> (events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>)) \<diamondop> (\<lceil>g\<rceil>\<^sub>< \<and> post\<^sub>H(A))))"

definition ExtChoice :: "('t::time, '\<theta>, '\<alpha>) hhrd \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd" (infixl "\<box>" 65)
where "P \<box> Q = HR((\<not> P\<^sup>f\<^sub>f \<and> \<not> Q\<^sup>f\<^sub>f) \<turnstile> ((P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f)))"

definition hrd_sup :: "('t::time, '\<theta>, '\<alpha>) hhrd set \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd" ("\<Sqinter>\<^sub>H") where
"\<Sqinter>\<^sub>H A = (if (A = {}) then Miracle else \<Sqinter> A)"

definition hrd_inf :: "('t::time, '\<theta>, '\<alpha>) hhrd set \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd" ("\<Squnion>\<^sub>H") where
"\<Squnion>\<^sub>H A = (if (A = {}) then Chaos else \<Squnion> A)"

definition
  "Wait n = HR(true \<turnstile> ((($ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> TI1(\<L> <\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)) \<diamondop> 
                        ($ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1(\<L> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)))))"

fun time_trel :: "_ \<times> _ \<Rightarrow> _ \<Rightarrow> _ \<times> _ \<Rightarrow> bool" (infix "\<leadsto>[_]\<^sub>h" 85) where
"(\<sigma>, P) \<leadsto>[t]\<^sub>h (\<rho>, Q) \<longleftrightarrow> (\<langle>\<sigma>\<rangle>\<^sub>H ;; P) \<sqsubseteq> (Wait t ;; \<langle>\<rho>\<rangle>\<^sub>H ;; Q)"

lemma Miracle_greatest:
  assumes "P is HCSP"
  shows "P \<sqsubseteq> Miracle"
proof -
  have "P = HR (pre\<^sub>H(P) \<turnstile> peri\<^sub>H(P) \<diamondop> post\<^sub>H(P))"
    by (metis HCSP_hybrid_reactive_tri_design' assms)
  also have "... \<sqsubseteq> HR(true \<turnstile> false)"
    by (rule HR_mono, rel_auto)
  also have "HR(true \<turnstile> false) = HR(true \<turnstile> false \<diamondop> false)"
    by (simp add: wait'_cond_def cond_def)
  finally show ?thesis
    by (simp add: Miracle_def)
qed
   
lemma Chaos_least:
  assumes "P is HCSP"
  shows "Chaos \<sqsubseteq> P"
proof -
  have "Chaos = HR(true)"
    by (simp add: Chaos_def design_def)   
  also have "... \<sqsubseteq> HR(pre\<^sub>H(P) \<turnstile> peri\<^sub>H(P) \<diamondop> post\<^sub>H(P))"
    by (simp add: HR_mono)
  also have "HR(pre\<^sub>H(P) \<turnstile> peri\<^sub>H(P) \<diamondop> post\<^sub>H(P)) = P"
    using HCSP_hybrid_reactive_tri_design' assms by fastforce
  finally show ?thesis .
qed

lemma Miracle_left_zero:
  assumes "P is HCSP"
  shows "(Miracle ;; P) = Miracle"
proof -
  have "(Miracle ;; P) = (HR(true \<turnstile> false \<diamondop> false) ;; HR (pre\<^sub>H(P) \<turnstile> peri\<^sub>H(P) \<diamondop> post\<^sub>H(P)))"
    by (metis Miracle_def HCSP_hybrid_reactive_tri_design' assms)
  also have "... = HR (true \<turnstile> false \<diamondop> false)"
    by (simp add: HR_design_tri_composition' HR1_false HR2c_false HR2c_true HR1_true_comp  pre\<^sub>H_def post\<^sub>H_def peri\<^sub>H_def unrest usubst)
  also have "... = Miracle"
    by (simp add: Miracle_def)
  finally show ?thesis .
qed

lemma Chaos_left_zero:
  assumes "P is HCSP"
  shows "(Chaos ;; P) = Chaos"
proof -
  have "(Chaos ;; P) = (HR(false \<turnstile> true \<diamondop> true) ;; HR (pre\<^sub>H(P) \<turnstile> peri\<^sub>H(P) \<diamondop> post\<^sub>H(P)))"
    by (metis Chaos_def HCSP_hybrid_reactive_tri_design' assms)
  also have "... = HR ((\<not> HR1 true \<and> \<not> (HR1 true \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2c (pre\<^sub>H P)))) \<turnstile>
                       (true \<or> (HR1 true ;; HR1 (HR2c (peri\<^sub>H P)))) \<diamondop> (HR1 true ;; HR1 (HR2c (post\<^sub>H P))))"
    by (simp add: HR_design_tri_composition' HR2c_false HR2c_true HR1_true_comp  pre\<^sub>H_def post\<^sub>H_def peri\<^sub>H_def unrest usubst)
  also have "... = HR ((\<not> $ok \<or> HR1 true \<or> (HR1 true \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2c (pre\<^sub>H P)))) \<or>
                       $ok\<acute> \<and> (true \<or> (HR1 true ;; HR1 (HR2c (peri\<^sub>H P)))) \<diamondop> (HR1 true ;; HR1 (HR2c (post\<^sub>H P))))"
    by (simp add: design_def impl_alt_def)
  also have "... = HR(HR1((\<not> $ok \<or> HR1 true \<or> (HR1 true \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2c (pre\<^sub>H P)))) \<or>
                      $ok\<acute> \<and> (true \<or> (HR1 true ;; HR1 (HR2c (peri\<^sub>H P)))) \<diamondop> (HR1 true ;; HR1 (HR2c (post\<^sub>H P)))))"
    by (simp add: HR1_HR2_commute HR1_HR2s HR1_HR3_commute HR1_idem HR_def)
  also have "... = HR(HR1((\<not> $ok \<or> true \<or> (HR1 true \<and> \<not> $wait\<acute> ;; HR1 (\<not> HR2c (pre\<^sub>H P)))) \<or>
                      $ok\<acute> \<and> (true \<or> (HR1 true ;; HR1 (HR2c (peri\<^sub>H P)))) \<diamondop> (HR1 true ;; HR1 (HR2c (post\<^sub>H P)))))"
    by (metis (no_types, hide_lams) HR1_disj HR1_idem)
  also have "... = HR(true)"
    by (simp add: HR1_HR2_commute HR1_HR2s HR1_HR3_commute HR1_idem HR_def)
  also have "... = Chaos"
    by (simp add: Chaos_def design_def)
  finally show ?thesis .
qed

lemma hybrid_design_choice:
  "(HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<sqinter> HR(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) = HR((P \<and> R) \<turnstile> ((Q\<^sub>1 \<or> S\<^sub>1) \<diamondop> (Q\<^sub>2 \<or> S\<^sub>2)))"
proof -
  have "(HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<sqinter> HR(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2)) = HR((P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<sqinter> (R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2))"
    by (simp add: disj_upred_def[THEN sym] HR_disj[THEN sym])
  also have "... = HR ((P \<and> R) \<turnstile> (Q\<^sub>1 \<diamondop> Q\<^sub>2 \<or> S\<^sub>1 \<diamondop> S\<^sub>2))"
    by (simp add: design_choice)
  also have "... = HR ((P \<and> R) \<turnstile> ((Q\<^sub>1 \<or> S\<^sub>1) \<diamondop> (Q\<^sub>2 \<or> S\<^sub>2)))"
  proof -
    have "(Q\<^sub>1 \<diamondop> Q\<^sub>2 \<or> S\<^sub>1 \<diamondop> S\<^sub>2) = ((Q\<^sub>1 \<or> S\<^sub>1) \<diamondop> (Q\<^sub>2 \<or> S\<^sub>2))"
      by (rel_auto)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma USUP_HCSP_closed:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is HCSP"
  shows "(\<Sqinter> A) is HCSP"
proof -
  from assms have A: "A = HCSP ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Sqinter> ...) = (\<Sqinter> P \<in> A. HCSP(P))"
    by auto
  also have "... = (\<Sqinter> P \<in> A \<bullet> HCSP(P))"
    by (simp add: USUP_as_Sup_collect)
  also have "... = (\<Sqinter> P \<in> A \<bullet> HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f))"
    by (simp add: HCSP_hybrid_reactive_design_form)
  also have "... = HR(\<Sqinter> P \<in> A \<bullet> (\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: HR_USUP assms(1))
  also have "... = HR((\<Squnion> P \<in> A \<bullet> \<not> P\<^sup>f\<^sub>f) \<turnstile> (\<Sqinter> P \<in> A \<bullet> P\<^sup>t\<^sub>f))"
    by (simp add: design_USUP assms)
  also have "... = HCSP(...)"
    by (simp add: hybrid_reactive_design_is_HCSP unrest)
  finally show ?thesis
    by (simp add: Healthy_def HCSP_idem)
qed

lemma UINF_HCSP_closed:
  assumes "A \<noteq> {}" "\<forall> P \<in> A. P is HCSP"
  shows "(\<Squnion> A) is HCSP"
proof -
  from assms have A: "A = HCSP ` A"
    by (auto simp add: Healthy_def rev_image_eqI)
  also have "(\<Squnion> ...) = (\<Squnion> P \<in> A. HCSP(P))"
    by auto
  also have "... = (\<Squnion> P \<in> A \<bullet> HCSP(P))"
    by (simp add: UINF_as_Inf_collect)
  also have "... = (\<Squnion> P \<in> A \<bullet> HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f))"
    by (simp add: HCSP_hybrid_reactive_design_form)
  also have "... = HR(\<Squnion> P \<in> A \<bullet> (\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: HR_UINF assms(1))
  also have "... = HR ((\<Sqinter> P \<in> A \<bullet> \<not> P\<^sup>f\<^sub>f) \<turnstile> (\<Squnion> P \<in> A \<bullet> \<not> P\<^sup>f\<^sub>f \<Rightarrow> P\<^sup>t\<^sub>f))"
    by (simp add: design_UINF)
  also have "... = HCSP(...)"
    by (simp add: hybrid_reactive_design_is_HCSP unrest)
  finally show ?thesis
    by (simp add: Healthy_def HCSP_idem)
qed

lemma HCSP_sup_closed:
  assumes "\<forall> P \<in> A. P is HCSP"
  shows "(\<Sqinter>\<^sub>H A) is HCSP"
proof (cases "A = {}")
  case True
  moreover have "Miracle is HCSP"
    by (simp add: Miracle_def Healthy_def hybrid_reactive_design_is_HCSP unrest)
  ultimately show ?thesis
    by (simp add: hrd_sup_def)
next
  case False
  with USUP_HCSP_closed assms show ?thesis
    by (auto simp add: hrd_sup_def)
qed

lemma HCSP_sup_below:
  assumes "\<forall> Q \<in> A. Q is HCSP" "P \<in> A"
  shows "\<Sqinter>\<^sub>H A \<sqsubseteq> P"
  using assms
  by (auto simp add: hrd_sup_def Sup_upper)

lemma HCSP_sup_upper_bound:
  assumes "\<forall> Q \<in> A. Q is HCSP" "\<forall> Q \<in> A. P \<sqsubseteq> Q" "P is HCSP"
  shows "P \<sqsubseteq> \<Sqinter>\<^sub>H A"
proof (cases "A = {}")
  case True
  thus ?thesis
    by (simp add: hrd_sup_def Miracle_greatest assms)
next
  case False
  thus ?thesis
    by (simp add: hrd_sup_def cSup_least assms)
qed

lemma HCSP_inf_closed:
  assumes "\<forall> P \<in> A. P is HCSP"
  shows "(\<Squnion>\<^sub>H A) is HCSP"
proof (cases "A = {}")
  case True
  moreover have "Chaos is HCSP"
    by (simp add: Chaos_def Healthy_def hybrid_reactive_design_is_HCSP unrest)
  ultimately show ?thesis
    by (simp add: hrd_inf_def)
next
  case False
  with UINF_HCSP_closed assms show ?thesis
    by (auto simp add: hrd_inf_def)
qed

lemma HCSP_inf_above:
  assumes "\<forall> Q \<in> A. Q is HCSP" "P \<in> A"
  shows "P \<sqsubseteq> \<Squnion>\<^sub>H A"
  using assms
  by (auto simp add: hrd_inf_def Inf_lower)

lemma HCSP_inf_lower_bound:
  assumes "\<forall> P \<in> A. P is HCSP" "\<forall> P \<in> A. P \<sqsubseteq> Q" "Q is HCSP"
  shows "\<Squnion>\<^sub>H A \<sqsubseteq> Q"
proof (cases "A = {}")
  case True
  thus ?thesis
    by (simp add: hrd_inf_def Chaos_least assms)
next
  case False
  thus ?thesis
    by (simp add: hrd_inf_def cInf_greatest assms)
qed

lemma Wait_pericondition_lemma1:
  "(($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)) ;;\<^sub>h 
        (TI1(\<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time)))
       = (TI1(\<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<le>\<^sub>u $time\<acute> - $time \<and> $time\<acute> - $time <\<^sub>u \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (TI1(TI2($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))) ;;\<^sub>h 
                TI1(TI2(\<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time)))"
    by (simp add: TI1_conj_right TI2_def usubst unrest)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by (simp add: alpha skip_h_lift_def TI1_TI2_seqr_form usubst unrest)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by (simp add: conj_comm)
  
  have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>(II \<and> \<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< \<and> \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub>>) ;; true\<rceil>\<^sub>H) \<and>
              $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h (\<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub>< \<and> true\<^sub>h)\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
      by simp
    also have "... = ?rhs"
      by (subst seqr_post_transfer, simp_all add: seqr_post_transfer unrest conj_assoc)
    finally show ?thesis .
  qed

  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< \<and> \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub>< ;; true\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by (rel_auto)

  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>\<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< \<and> \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub>< \<and> (II ;; true)\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by (rel_auto)

  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>\<lceil>\<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<bar>m\<bar>\<rceil>\<^sub>< \<and> \<lceil>\<bar>n\<bar> >\<^sub>u \<guillemotleft>t\<^sub>2\<guillemotright>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)"
    by simp

  also have "... = (\<^bold>\<exists> t \<bullet> \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub>< >\<^sub>u \<guillemotleft>t\<guillemotright>\<rceil>\<^sub>H \<and> $time\<acute> =\<^sub>u $time + \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<ge>\<^sub>u 0)"
    by (rel_auto)
    
  also have "... = (\<^bold>\<exists> t \<bullet> (\<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u \<guillemotleft>t\<guillemotright>) \<and> $time\<acute> =\<^sub>u $time + \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<ge>\<^sub>u 0)"
    by (simp add: alpha skip_h_lift_def)

  also have "... = (\<^bold>\<exists> t \<bullet> (\<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u \<guillemotleft>t\<guillemotright>) \<and> $time\<acute> - $time - \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H =\<^sub>u \<guillemotleft>t\<guillemotright> \<and> \<guillemotleft>t\<guillemotright> \<ge>\<^sub>u 0)"
    by (rel_auto)

  also have "... = ((\<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time - \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and> $time\<acute> - $time - \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<ge>\<^sub>u 0)"
    by (rel_auto)

  also have "... = ((\<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time) \<and> $time\<acute> - $time  \<ge>\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
    by (rel_auto)

  also have "... = ((\<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time) \<and> $time\<acute> - $time  \<ge>\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)"
    by (simp add: alpha)

  also have "... = (TI1($time\<acute> - $time  \<ge>\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<and> \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time))"
    by (rel_auto)

  finally show ?thesis .
qed    

lemma Wait_pericondition_lemma2:
  "(TI1 (\<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time) \<or>
        (TI1(\<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<le>\<^sub>u $time\<acute> - $time \<and> $time\<acute> - $time <\<^sub>u \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))) =
    (TI1 (\<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time))"
  by (rel_auto)

lemma Wait_postcondition_lemma:
  "($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 (\<L> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) ;;\<^sub>h
    $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 (\<L> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)) =
   ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 (\<L> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (TI1(TI2($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<L> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)) ;;\<^sub>h TI1(TI2($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<L> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H)))"
    by (simp add: TI1_conj_right TI2_def usubst unrest)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H ;;\<^sub>h $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: TI1_TI2_seqr_form usubst unrest)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h II \<and> \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: alpha skip_h_lift_def)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<bar>m\<bar>\<rceil>\<^sub>< ;;\<^sub>h \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<bar>n\<bar>\<rceil>\<^sub>< \<and> II\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: conj_comm)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> (\<lceil>II \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<bar>m\<bar>\<rceil>\<^sub>< \<and> \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<bar>n\<bar>\<rceil>\<^sub>>\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: seqr_post_transfer unrest conj_assoc)
  also have "... = (\<^bold>\<exists> t\<^sub>1 \<bullet> \<^bold>\<exists> t\<^sub>2 \<bullet> ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<guillemotleft>t\<^sub>1\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H \<and> \<guillemotleft>t\<^sub>2\<guillemotright> =\<^sub>u \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub>>\<rceil>\<^sub>H) \<and>
                       $time\<acute> =\<^sub>u $time + \<guillemotleft>t\<^sub>1\<guillemotright> + \<guillemotleft>t\<^sub>2\<guillemotright> \<and> \<guillemotleft>t\<^sub>1\<guillemotright> \<ge>\<^sub>u 0 \<and> \<guillemotleft>t\<^sub>2\<guillemotright> \<ge>\<^sub>u 0)" 
    by (simp add: alpha skip_h_lift_def)
  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time + \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub>>\<rceil>\<^sub>H)" 
    by (rel_auto)
  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>m\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H + \<lceil>\<lceil>\<bar>n\<bar>\<rceil>\<^sub>>\<rceil>\<^sub>H =\<^sub>u $time\<acute> - $time)"
    by (rel_auto)
  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H =\<^sub>u $time\<acute> - $time)"
    by (simp add: alpha skip_h_lift_def, rel_auto)
  also have "... = ($\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1(\<L> =\<^sub>u \<lceil>\<lceil>\<bar>m\<bar> + \<bar>n\<bar>\<rceil>\<^sub><\<rceil>\<^sub>H))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma Wait_m_plus_n:
  "(Wait m ;; Wait n) = Wait (\<bar>m\<bar> + \<bar>n\<bar>)"
  apply (simp add: Wait_def)
  apply (subst HR_design_tri_composition)
  apply (simp_all add: unrest)
  apply (simp add: HR2s_true HR1_false HR2s_conj HR2s_cond HR2s_tr'_eq_tr HR2s_ref'_eq_ref HR2s_hy'_eq_hy
                   HR2s_wait' HR2s_dur HR2s_pre_lit HR2s_time'_time_eq HR2s_time'_time_less HR2s_TI1_commute)
  apply (rule HR_des_tri_eqI)
  apply (simp)
  apply (simp add: HR1_def R1_extend_conj_unrest R1_extend_conj_unrest' R1_tr'_eq_tr TI1_conj_right unrest)
  apply (simp add: seq_var_ident_lift HR1_extend_conj' unrest eq_cong_left conj_disj_distr[THEN sym] TI1_idem)
oops
(*
  apply (simp add: Wait_pericondition_lemma1 Wait_pericondition_lemma2)
  apply (simp add: HR1_def R1_extend_conj_unrest R1_extend_conj_unrest' R1_tr'_eq_tr TI1_conj_right unrest)
  apply (simp add: seq_var_ident_lift HR1_extend_conj' unrest eq_cong_left conj_disj_distr[THEN sym] TI1_idem)
  using Wait_postcondition_lemma by blast
*)

lemma skip_hy_conj:
  "($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time) = II"
  by (rel_auto, simp_all add: alpha_d.equality alpha_rp'.equality)

lemma Wait_0: "Wait 0 = (II\<^sub>H :: ('t::time, '\<theta>, '\<alpha>) hhrd)" (is "?lhs = ?rhs")
proof -
  have 1:"TI1 (\<lceil>\<lceil>0\<rceil>\<^sub><\<rceil>\<^sub>H >\<^sub>u $time\<acute> - $time) = (false :: ('t, '\<theta>, '\<alpha>) hhrd)"
    by (rel_auto)
  have 2:"($ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> TI1 ($time\<acute> - $time =\<^sub>u \<lceil>\<lceil>0::('t, '\<alpha>) uexpr\<rceil>\<^sub><\<rceil>\<^sub>H))
         = (($ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time) :: ('t, '\<theta>, '\<alpha>) hhrd)"
    by (rel_auto)

  have "?lhs = HR (true \<turnstile> (\<not> $wait\<acute> \<and> $ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time))"
    by (simp add:  Wait_def 1 2 wait'_cond_left_false)
  also have "... = HR (true \<turnstile> ($ok\<acute> =\<^sub>u $ok \<and> $wait\<acute> =\<^sub>u $wait \<and> $ref\<acute> =\<^sub>u $ref \<and> $tr\<acute> =\<^sub>u $tr \<and> $\<Sigma>\<^sub>H\<acute> =\<^sub>u $\<Sigma>\<^sub>H \<and> $time\<acute> =\<^sub>u $time))"
    by (rel_auto) (* REDO -- too slow! *)
  also have "... = ?rhs"
    by (simp add: skip_hy_conj hskip_reactive_design)
  finally show ?thesis .
qed

lemma assigns_h_HCSP:
  "\<langle>\<sigma>\<rangle>\<^sub>H is HCSP"
  by (simp add: Healthy_def' assigns_h_def hybrid_reactive_design_is_HCSP unrest)

lemma assigns_h_comp:
  assumes "$ok \<sharp> P" "$ok \<sharp> Q\<^sub>1" "$ok \<sharp> Q\<^sub>2" "$wait \<sharp> P" "$wait \<sharp> Q\<^sub>1" "$wait \<sharp> Q\<^sub>2"
          "Q\<^sub>1 is HR1" "Q\<^sub>2 is HR1" "P is HR2c" "Q\<^sub>1 is HR2c" "Q\<^sub>2 is HR2c"
  shows "(\<langle>\<sigma>\<rangle>\<^sub>H ;; HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) = HR(\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> P \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
proof -
  have "(\<langle>\<sigma>\<rangle>\<^sub>H ;; HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2)) = 
        (HR (true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H)) ;; HR (P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2))"
    by (simp add: assigns_h_def)
  also have "... = HR ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H) \<and> \<not> $wait\<acute> ;; 
                       HR1 (\<not> HR2c P))) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> HR1 (HR2c Q\<^sub>1) \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> HR1 (HR2c Q\<^sub>2))"
    by (simp add: HR_design_tri_composition' unrest assms HR2c_true HR1_false HR1_HR2c_frame HR2c_false assigns_hy_comp_lemma)
  also have "... = HR ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H) \<and> \<not> $wait\<acute> ;; 
                       HR1 (\<not> P))) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    using assms by (simp add: Healthy_def)
  also have "... = HR ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H) \<and> $wait\<acute> =\<^sub>u \<guillemotleft>False\<guillemotright> ;; 
                       HR1 (\<not> P))) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: false_alt_def[THEN sym])
  also have "... = HR ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H)\<lbrakk>false/$wait\<acute>\<rbrakk> ;; 
                       (HR1 (\<not> P))\<lbrakk>false/$wait\<rbrakk>)) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: seqr_left_one_point false_alt_def)
  also have "... = HR ((\<not> (($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H) ;; 
                       (HR1 (\<not> P)))) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: usubst unrest HR1_def TI1_def HTI_def R1_def assms)
  also have "... = HR ((\<not> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> HR1 (\<not> P)) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: assigns_hy_comp_lemma assms unrest)
  also have "... = HR ((\<not> HR1 (\<not> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> P)) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: HR1_def TI1_def R1_def HTI_def usubst unrest)
  also have "... = HR ((\<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> P) \<turnstile> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>1 \<diamondop> \<lceil>\<sigma> \<oplus>\<^sub>s \<Sigma>\<^sub>H\<rceil>\<^sub>s \<dagger> Q\<^sub>2)"
    by (simp add: hrd_HR1_neg_precond)
  finally show ?thesis .
qed


lemma assigns_h_merge:
  "(\<langle>\<sigma>\<rangle>\<^sub>H ;; \<langle>\<rho>\<rangle>\<^sub>H) = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>H"
proof -
  have "(\<langle>\<sigma>\<rangle>\<^sub>H ;; \<langle>\<rho>\<rangle>\<^sub>H) = (\<langle>\<sigma>\<rangle>\<^sub>H ;; HR (true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<rho>\<rangle>\<^sub>a\<rceil>\<^sub>H)))"
    by (simp add: assigns_h_def)
  also have "... = HR (true \<turnstile> false \<diamondop> ($tr\<acute> =\<^sub>u $tr \<and> $ref\<acute> =\<^sub>u $ref \<and> $time\<acute> =\<^sub>u $time \<and> \<lceil>\<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>H))"
      apply (subst assigns_h_comp)
      apply (simp_all add: unrest usubst Healthy_def' HR1_false HR2c_false HR2c_true)
      apply (rel_auto)[1]
      apply (simp add: HR2c_def R2c_def R2s_def TI2_def usubst R1_def unrest)
      apply (rel_auto)[1]
      using list_minus_anhil apply blast
  done
  also have "... = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>H"
    by (simp add: assigns_h_def)
  finally show ?thesis .
qed

typedef HRD = "UNIV :: unit set" ..

abbreviation "HRD \<equiv> TYPE(HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd)"

overloading
  hrd_hcond   == "utp_hcond :: (HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd) itself \<Rightarrow> (('t, '\<theta>, '\<alpha>) alphabet_hrd \<times> ('t, '\<theta>, '\<alpha>) alphabet_hrd) Healthiness_condition"
  hrd_unit    == "utp_unit :: (HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd) itself \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd"
  hrd_pvar    == "pvar :: '\<alpha> \<Longrightarrow> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd"
  hrd_assigns == "pvar_assigns :: (HRD \<times> ('t, '\<theta>, '\<alpha>) alphabet_hrd) itself \<Rightarrow> '\<alpha> usubst \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd"
begin
  definition hrd_hcond :: "(HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd) itself \<Rightarrow> (('t, '\<theta>, '\<alpha>) alphabet_hrd \<times> ('t, '\<theta>, '\<alpha>) alphabet_hrd) Healthiness_condition" where
  [upred_defs]: "hrd_hcond T = HCSP"
  definition hrd_unit :: "(HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd) itself \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd" where
  [upred_defs]: "hrd_unit T = II\<^sub>H"
  definition hrd_pvar :: "'\<alpha> \<Longrightarrow> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd" where
  [upred_defs]: "hrd_pvar = \<Sigma>\<^sub>H"
  definition hrd_assigns :: "(HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd) itself \<Rightarrow> '\<alpha> usubst \<Rightarrow> ('t, '\<theta>, '\<alpha>) hhrd" where
  [upred_defs]: "hrd_assigns T \<sigma> = \<langle>\<sigma>\<rangle>\<^sub>H"
end

interpretation hrd_theory: utp_theory "TYPE(HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd)"
  by (unfold_locales, simp_all add: hrd_hcond_def HCSP_idem)

lemma Miracle_is_top: "\<top>\<^bsub>utp_order HRD\<^esub> = Miracle"
  apply (auto intro!:some_equality simp add: atop_def some_equality greatest_def utp_order_def hrd_hcond_def)
  apply (metis HCSP_sup_closed emptyE hrd_sup_def)
  using Miracle_greatest apply blast
  apply (metis HCSP_sup_closed dual_order.antisym equals0D hrd_sup_def Miracle_greatest)
done

lemma Chaos_is_bot: "\<bottom>\<^bsub>utp_order HRD\<^esub> = Chaos"
  apply (auto intro!:some_equality simp add: abottom_def some_equality least_def utp_order_def hrd_hcond_def)
  apply (metis HCSP_inf_closed emptyE hrd_inf_def)
  using Chaos_least apply blast
  apply (metis Chaos_least HCSP_inf_closed dual_order.antisym equals0D hrd_inf_def)
done

interpretation hrd_lattice: utp_theory_lattice "TYPE(HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd)"
  rewrites "carrier (utp_order HRD) = \<lbrakk>HCSP\<rbrakk>"
  and "\<top>\<^bsub>utp_order HRD\<^esub> = Miracle"
  and "\<bottom>\<^bsub>utp_order HRD\<^esub> = Chaos"
  apply (unfold_locales)
  apply (simp_all add: Miracle_is_top Chaos_is_bot)
  apply (simp_all add: utp_order_def hrd_hcond_def)
  apply (rename_tac A)
  apply (rule_tac x="\<Squnion>\<^sub>H A" in exI, auto intro:HCSP_inf_above HCSP_inf_lower_bound HCSP_inf_closed simp add: least_def Upper_def HCSP_inf_above)
  apply (rename_tac A)
  apply (rule_tac x="\<Sqinter>\<^sub>H A" in exI, auto intro:HCSP_sup_below HCSP_sup_upper_bound HCSP_sup_closed simp add: greatest_def Lower_def HCSP_inf_above)
done

abbreviation hrd_lfp :: "_ \<Rightarrow> _" ("\<mu>\<^sub>H") where
"\<mu>\<^sub>H F \<equiv> \<mu>\<^bsub>utp_order HRD\<^esub> F"

abbreviation hrd_gfp :: "_ \<Rightarrow> _" ("\<nu>\<^sub>H") where
"\<nu>\<^sub>H F \<equiv> \<nu>\<^bsub>utp_order HRD\<^esub> F"

interpretation hrd_prog_var: utp_prog_var "TYPE(HRD \<times> ('t::time, '\<theta>, '\<alpha>) alphabet_hrd)" "TYPE('\<alpha>::vst)"
  by (unfold_locales, simp_all add: hrd_pvar_def hrd_assigns_def hrd_hcond_def assigns_h_HCSP assigns_h_merge)

lemma Stop_left_unit:
  assumes "P is HCSP"
  shows "(Stop ;; P) = Stop"
proof -
  have "(Stop ;; P) = (Stop ;; HR (pre\<^sub>H P \<turnstile> peri\<^sub>H P \<diamondop> post\<^sub>H P))"
    using HCSP_hybrid_reactive_tri_design' assms by force
  also have "... = (HR(true \<turnstile> (events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>) \<diamondop> false) ;; HR (pre\<^sub>H P \<turnstile> peri\<^sub>H P \<diamondop> post\<^sub>H P))"
    by (simp add: Stop_def)
  also have "... = HR (true \<turnstile> (events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"
    by (simp add: HR_design_tri_composition' unrest pre\<^sub>H_def peri\<^sub>H_def post\<^sub>H_def usubst HR2c_true HR1_false HR2c_false)
  also have "... = Stop"
    by (simp add: Stop_def)
  finally show ?thesis .
qed

lemma Guard_false: "false &\<^sub>u P = Stop"
  by (simp add: Guard_def Stop_def alpha cond_unit_F)

lemma Guard_true:
  assumes "P is HCSP"
  shows "true &\<^sub>u P = P"
proof -
  have "true &\<^sub>u P = HR (pre\<^sub>H P \<turnstile> (peri\<^sub>H P \<triangleleft> true \<triangleright> (events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>)) \<diamondop> post\<^sub>H P)"
    by (simp add: Guard_def alpha)
  also have "... = HR (pre\<^sub>H P \<turnstile> peri\<^sub>H P \<diamondop> post\<^sub>H P)"
    by (simp add: cond_unit_T)
  also have "... = P"
    using HCSP_hybrid_reactive_tri_design' assms by force
  finally show ?thesis .
qed

lemma peri\<^sub>H_true: "peri\<^sub>H(true) = true"
  by (simp add: peri\<^sub>H_def usubst)

lemma peri\<^sub>H_false: "peri\<^sub>H(false) = false"
  by (simp add: peri\<^sub>H_def usubst)

lemma post\<^sub>H_true: "post\<^sub>H(true) = true"
  by (simp add: post\<^sub>H_def usubst)

lemma post\<^sub>H_false: "post\<^sub>H(false) = false"
  by (simp add: post\<^sub>H_def usubst)


lemma pre\<^sub>H_Stop: "pre\<^sub>H(Stop) = true"
  by (simp add: Stop_def pre\<^sub>H_hrd peri\<^sub>H_hrd post\<^sub>H_hrd usubst HR2s_false HR1_false)

lemma peri\<^sub>H_Stop: "peri\<^sub>H(Stop) = HR1(events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>)"
  apply (simp add: Stop_def pre\<^sub>H_hrd peri\<^sub>H_hrd post\<^sub>H_hrd usubst peri\<^sub>H_true)
  apply (simp add: peri\<^sub>H_def usubst HR2c_conj HR2c_tr'_eq_tr HR2c_hyst'_eq_hyst HR1_extend_conj HR1_tr'_eq_tr)
  apply (rel_auto)
done

lemma post\<^sub>H_Stop: "post\<^sub>H(Stop) = false"
  by (simp add: Stop_def post\<^sub>H_hrd usubst post\<^sub>H_true post\<^sub>H_false HR2c_false HR1_false)

lemma pre\<^sub>H_Skip: "pre\<^sub>H(II\<^sub>H) = true"
  by (simp add: hskip_reactive_tri_design pre\<^sub>H_hrd usubst HR2s_false HR1_false)

lemma peri\<^sub>H_Skip: "peri\<^sub>H(II\<^sub>H) = false"
  by (simp add: hskip_reactive_tri_design peri\<^sub>H_hrd peri\<^sub>H_true peri\<^sub>H_false usubst HR2c_false HR1_false)

lemma ExtChoice_tri_form:
  "P \<box> Q = HR((pre\<^sub>H(P) \<and> pre\<^sub>H(Q)) \<turnstile> ((peri\<^sub>H(P) \<and> peri\<^sub>H(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>H(P) \<or> peri\<^sub>H(Q))) 
                                      \<diamondop> (post\<^sub>H(P) \<or> post\<^sub>H(Q)))" (is "?lhs = ?rhs")
proof -                                    
  have "?rhs =
        HR((pre\<^sub>H(P) \<and> pre\<^sub>H(Q))\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> 
           (((peri\<^sub>H(P) \<and> peri\<^sub>H(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>H(P) \<or> peri\<^sub>H(Q))) \<diamondop> 
             (post\<^sub>H(P) \<or> post\<^sub>H(Q)))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
    by (simp add: HR_design_okay_true)
  also have "... =
        HR((\<not> P\<^sup>f\<^sub>f \<and> \<not> Q\<^sup>f\<^sub>f)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> 
           (((peri\<^sub>H(P) \<and> peri\<^sub>H(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>H(P) \<or> peri\<^sub>H(Q))) \<diamondop> 
             (post\<^sub>H(P) \<or> post\<^sub>H(Q)))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
    by (simp add: usubst pre\<^sub>H_def)
  also have "... =
        HR((\<not> P\<^sup>f\<^sub>f \<and> \<not> Q\<^sup>f\<^sub>f)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> 
           (((peri\<^sub>H(P) \<and> peri\<^sub>H(Q)) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (peri\<^sub>H(P) \<or> peri\<^sub>H(Q)))\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> 
             (post\<^sub>H(P) \<or> post\<^sub>H(Q))\<lbrakk>false/$wait\<acute>\<rbrakk>)\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
    by (simp add: subst_wait'_left_subst subst_wait'_right_subst)
  also have "... =
        HR((\<not> P\<^sup>f\<^sub>f \<and> \<not> Q\<^sup>f\<^sub>f)\<lbrakk>true,false/$ok,$wait\<rbrakk> \<turnstile> 
           (((P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f))\<lbrakk>true/$wait\<acute>\<rbrakk> \<diamondop> 
             ((P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f)\<lbrakk>false/$wait\<acute>\<rbrakk>))\<lbrakk>true,false/$ok,$wait\<rbrakk>)"
    by (simp add: post\<^sub>H_def peri\<^sub>H_def usubst unrest)
  also have "... =
        HR((\<not> P\<^sup>f\<^sub>f \<and> \<not> Q\<^sup>f\<^sub>f) \<turnstile> 
           (((P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f)) \<diamondop> 
             ((P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f))))"
    by (simp add: subst_wait'_left_subst subst_wait'_right_subst HR_design_okay_true)
  also have "... = HR ((\<not> P\<^sup>f\<^sub>f \<and> \<not> Q\<^sup>f\<^sub>f) \<turnstile> (P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f)))"
  proof -
    have "(((P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f)) \<diamondop> ((P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f))) =
          (P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f))"
      by (simp add: wait'_cond_def cond_assoc cond_idem conj_comm)
    thus ?thesis by simp
  qed
  also have "... = P \<box> Q"
    by (simp add: ExtChoice_def)
  finally show ?thesis ..
qed

lemma design_pre_ff: "(P \<turnstile> Q)\<^sup>f\<^sub>f = ($ok \<Rightarrow> \<not> P\<^sup>f\<^sub>f)"
  by (simp add: design_def usubst impl_alt_def)

lemma design_post_tf: "(P \<turnstile> Q)\<^sup>t\<^sub>f = ($ok \<and> P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f)"
  by (simp add: design_def usubst impl_alt_def)

lemma HR_pre_ff: "(HR(P))\<^sup>f\<^sub>f = HR1(HR2c(P\<^sup>f\<^sub>f))"
  by (simp add: HR_R2c_def HR1_def TI1_def R1_def HTI_def R2c_def TI2_def R2s_def HR2c_def HR3_def usubst cond_unit_F)

lemma HR_post_tf: "(HR(P))\<^sup>t\<^sub>f = HR1(HR2c(P\<^sup>t\<^sub>f))"
  by (simp add: HR_R2c_def HR1_def TI1_def R1_def HTI_def R2c_def TI2_def R2s_def HR2c_def HR3_def usubst cond_unit_F)

lemma Stop_pre_ff: "Stop\<^sup>f\<^sub>f = HR1 (\<not> $ok)"
  apply (simp add: Stop_def HR_pre_ff design_pre_ff impl_alt_def HR2c_disj HR2c_not HR2c_ok)
  apply (simp add: usubst HR2c_true)
done

lemma HR2c_events_empty: "HR2c(events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>) = (events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>)"
  by (simp add: HR2c_def TI2_def usubst R2c_def R2s_def usubst, rel_auto)

lemma Stop_post_tf: "Stop\<^sup>t\<^sub>f = (HR1(\<not> $ok) \<or> $wait\<acute> \<and> HR1(events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>))"
  apply (simp add: Stop_def HR_post_tf design_post_tf impl_alt_def HR2c_disj HR2c_not HR2c_ok)
  apply (simp add: usubst wait'_cond_def cond_def HR2c_true HR2c_conj HR2c_wait HR2c_events_empty HR2c_wait' HR1_extend_conj' HR1_disj HR1_tr'_eq_tr)
done

lemma HR_neg_healthy_pre: "HR((\<not> HR1(HR2c(P))) \<turnstile> Q) = HR((\<not> P) \<turnstile> Q)"
  by (simp add: design_def impl_alt_def HR_R2c_def HR1_HR3_commute HR2c_HR3_commute HR1_disj HR2c_disj HR1_HR2c_commute[THEN sym] HR2c_idem HR1_idem)

lemma HR_healthy_post: "HR(P \<turnstile> HR1(HR2c(Q))) = HR(P \<turnstile> Q)"
  by (simp add: design_def impl_alt_def HR_R2c_def HR1_HR3_commute HR2c_HR3_commute HR1_disj HR2c_disj HR1_conj HR2c_conj HR1_HR2c_commute[THEN sym] HR2c_idem HR1_idem)

lemma HR1_subst [usubst]:
  "\<lbrakk> $tr \<sharp> \<sigma>; $tr\<acute> \<sharp> \<sigma>; $time \<sharp> \<sigma>; $time\<acute> \<sharp> \<sigma> \<rbrakk> \<Longrightarrow>  \<sigma> \<dagger> HR1(P) = HR1(\<sigma> \<dagger> P)"
  by (simp add: HR1_def TI1_def R1_def HTI_def usubst)

lemma HR_design_ExtChoice:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> R"
  shows "HR(P \<turnstile> Q) \<box> HR(R \<turnstile> S) = HR ((P \<and> R) \<turnstile> (Q \<and> S \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> Q \<or> S))"
proof -
  have "HR(P \<turnstile> Q) \<box> HR(R \<turnstile> S) =
        HR ((\<not> HR1 (HR2c ($ok \<Rightarrow> \<not> P\<^sup>f\<^sub>f)) \<and> \<not> HR1 (HR2c ($ok \<Rightarrow> \<not> R\<^sup>f\<^sub>f)))\<lbrakk>true/$ok\<rbrakk> \<turnstile>
               (HR1 (HR2c ($ok \<and> P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f)) \<and> HR1 (HR2c ($ok \<and> R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f)) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  HR1 (HR2c ($ok \<and> P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f)) \<or> HR1 (HR2c ($ok \<and> R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f)))\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: ExtChoice_def HR_pre_ff HR_post_tf design_pre_ff design_post_tf design_okay_true)
  also have "... =
        HR ((\<not> HR1 (HR2c (\<not> P\<^sup>f\<^sub>f)) \<and> \<not> HR1 (HR2c (\<not> R\<^sup>f\<^sub>f)))\<lbrakk>true/$ok\<rbrakk> \<turnstile>
               (HR1 (HR2c (P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f)) \<and> HR1 (HR2c (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f)) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  HR1 (HR2c (P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f)) \<or> HR1 (HR2c (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f)))\<lbrakk>true/$ok\<rbrakk>)"
    by (simp add: usubst unrest)
  also have "... =
        HR ((\<not> HR1 (HR2c (\<not> P\<^sup>f\<^sub>f)) \<and> \<not> HR1 (HR2c (\<not> R\<^sup>f\<^sub>f))) \<turnstile>
               (HR1 (HR2c (P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f)) \<and> HR1 (HR2c (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f)) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  HR1 (HR2c (P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f)) \<or> HR1 (HR2c (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f))))"
    by (simp add: design_okay_true)
  also have "... =
        HR ((\<not> (HR1 (HR2c (\<not> P\<^sup>f\<^sub>f \<or> \<not> R\<^sup>f\<^sub>f)))) \<turnstile>
               (HR1 (HR2c ((P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f) \<and> (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f))) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright>
                  HR1 (HR2c ((P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f) \<or> (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f)))))"
    by (simp add: HR1_disj HR1_conj HR2c_disj HR2c_conj)
  also have "... =
        HR ((\<not> (HR1 (HR2c (\<not> P\<^sup>f\<^sub>f \<or> \<not> R\<^sup>f\<^sub>f)))) \<turnstile>
               (HR1 (HR2c (((P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f) \<and> (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f)) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> ((P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f) \<or> (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f))))))"
    by (simp add: HR1_cond HR2c_cond HR2c_conj HR2c_wait' HR2c_tr'_eq_tr)
  also have "... = HR ((P\<^sup>f\<^sub>f \<and> R\<^sup>f\<^sub>f) \<turnstile> ((P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f) \<and> (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t\<^sub>f \<Rightarrow> Q\<^sup>t\<^sub>f) \<or> (R\<^sup>t\<^sub>f \<Rightarrow> S\<^sup>t\<^sub>f)))"
    by (simp add: HR_neg_healthy_pre HR_healthy_post)
  also have "... = HR ((P \<and> R) \<^sub>f \<turnstile> ((P\<^sup>t \<Rightarrow> Q\<^sup>t) \<and> (R\<^sup>t \<Rightarrow> S\<^sup>t) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t \<Rightarrow> Q\<^sup>t) \<or> (R\<^sup>t \<Rightarrow> S\<^sup>t)) \<^sub>f)"
    by (simp add: usubst assms)
  also have "... = HR ((P \<and> R) \<turnstile> ((P\<^sup>t \<Rightarrow> Q\<^sup>t) \<and> (R\<^sup>t \<Rightarrow> S\<^sup>t) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t \<Rightarrow> Q\<^sup>t) \<or> (R\<^sup>t \<Rightarrow> S\<^sup>t)))"
    by (simp add: HR_design_wait_false)
  also have "... = HR ((P \<and> R) \<turnstile> ((P\<^sup>t \<Rightarrow> Q\<^sup>t) \<and> (R\<^sup>t \<Rightarrow> S\<^sup>t) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P\<^sup>t \<Rightarrow> Q\<^sup>t) \<or> (R\<^sup>t \<Rightarrow> S\<^sup>t))\<^sup>t)"
    by (simp add: design_subst_ok')
  also have "... = HR ((P \<and> R) \<turnstile> ((P \<Rightarrow> Q) \<and> (R \<Rightarrow> S) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P \<Rightarrow> Q) \<or> (R \<Rightarrow> S))\<^sup>t)"
    by (simp add: usubst)
  also have "... = HR ((P \<and> R) \<turnstile> ((P \<Rightarrow> Q) \<and> (R \<Rightarrow> S) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> (P \<Rightarrow> Q) \<or> (R \<Rightarrow> S)))"
    by (simp add: design_subst_ok')
  also have "... = HR ((P \<and> R) \<turnstile> (Q \<and> S \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> Q \<or> S))" (is "HR(?P) = HR(?Q)")
  proof -
    have "?P = ?Q" by rel_auto
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed
   
lemma HR_tri_design_ExtChoice:
  assumes "$ok\<acute> \<sharp> P" "$ok\<acute> \<sharp> R"
  shows "HR(P \<turnstile> Q\<^sub>1 \<diamondop> Q\<^sub>2) \<box> HR(R \<turnstile> S\<^sub>1 \<diamondop> S\<^sub>2) = HR((P \<and> R) \<turnstile> ((Q\<^sub>1 \<and> S\<^sub>1) \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> (Q\<^sub>1 \<or> S\<^sub>1)) \<diamondop> (Q\<^sub>2 \<or> S\<^sub>2))"
proof -
  have "(Q\<^sub>1 \<diamondop> Q\<^sub>2 \<and> S\<^sub>1 \<diamondop> S\<^sub>2 \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> Q\<^sub>1 \<diamondop> Q\<^sub>2 \<or> S\<^sub>1 \<diamondop> S\<^sub>2) =
        ((Q\<^sub>1 \<and> S\<^sub>1 \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> Q\<^sub>1 \<or> S\<^sub>1) \<diamondop> (Q\<^sub>2 \<or> S\<^sub>2))"
    by (rel_auto)
  thus ?thesis
    by (simp add: HR_design_ExtChoice assms)
qed

lemma pre\<^sub>H_unrest_ok' [unrest]: "$ok\<acute> \<sharp> pre\<^sub>H(P)"
  by (simp add: pre\<^sub>H_def unrest usubst)

lemma ExtChoice_idem: "P is HCSP \<Longrightarrow> P \<box> P = P"
  by (simp add: ExtChoice_def cond_idem HCSP_hybrid_reactive_design[THEN sym])

lemma ExtChoice_comm: "P \<box> Q = Q \<box> P"
  by (simp add: ExtChoice_def conj_comm disj_comm)

lemma cond_conj_distl: "((P \<triangleleft> b \<triangleright> Q) \<and> R) = ((P \<and> R) \<triangleleft> b \<triangleright> (Q \<and> R))"
  by (rel_auto)

lemma cond_disj_distl: "((P \<triangleleft> b \<triangleright> Q) \<or> R) = ((P \<or> R) \<triangleleft> b \<triangleright> (Q \<or> R))"
  by (rel_auto)

lemma cond_unr_left: "(P \<triangleleft> b \<triangleright> Q \<triangleleft> b \<triangleright> R) = (P \<triangleleft> b \<triangleright> R)"
  by (rel_auto)

lemma ExtChoice_assoc: 
  assumes "P is HCSP" "Q is HCSP" "R is HCSP"
  shows "P \<box> Q \<box> R = P \<box> (Q \<box> R)"
proof -
  have "P \<box> Q \<box> R = HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) \<box> HR((\<not> Q\<^sup>f\<^sub>f) \<turnstile> Q\<^sup>t\<^sub>f) \<box> HR((\<not> R\<^sup>f\<^sub>f) \<turnstile> R\<^sup>t\<^sub>f)"
    by (simp add: HCSP_hybrid_reactive_design[THEN sym] assms)

  also have "... = HR (((\<not> P\<^sup>f\<^sub>f \<and> \<not> Q\<^sup>f\<^sub>f) \<and> \<not> R\<^sup>f\<^sub>f) \<turnstile>
                        ((P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f) \<and> R\<^sup>t\<^sub>f \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright>
                         (P\<^sup>t\<^sub>f \<and> Q\<^sup>t\<^sub>f \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> P\<^sup>t\<^sub>f \<or> Q\<^sup>t\<^sub>f) \<or> R\<^sup>t\<^sub>f))"
    by (simp add: HR_design_ExtChoice unrest)

  also have "... = HR ((\<not> P\<^sup>f\<^sub>f \<and> \<not> Q\<^sup>f\<^sub>f \<and> \<not> R\<^sup>f\<^sub>f) \<turnstile>
                       (P\<^sup>t\<^sub>f \<and> (Q\<^sup>t\<^sub>f \<and> R\<^sup>t\<^sub>f \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> Q\<^sup>t\<^sub>f \<or> R\<^sup>t\<^sub>f) \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright>
                        P\<^sup>t\<^sub>f \<or> (Q\<^sup>t\<^sub>f \<and> R\<^sup>t\<^sub>f \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> Q\<^sup>t\<^sub>f \<or> R\<^sup>t\<^sub>f)))" 
                   (is "HR(?pre1 \<turnstile> ?post1) = HR(?pre2 \<turnstile> ?post2)")
  proof -
    have "?pre1 = ?pre2"
      by (simp add: conj_assoc)
    moreover have "?post1 = ?post2"
      by (simp add: cond_conj_distl cond_conj_distr cond_unr_left cond_L6 cond_disj_distr cond_disj_distl conj_assoc disj_assoc)
    ultimately show ?thesis by simp
  qed
  
  also have "... = HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f) \<box> (HR((\<not> Q\<^sup>f\<^sub>f) \<turnstile> Q\<^sup>t\<^sub>f) \<box> HR((\<not> R\<^sup>f\<^sub>f) \<turnstile> R\<^sup>t\<^sub>f))"
    by (simp add: HR_design_ExtChoice unrest)
  
  also have "... = P \<box> (Q \<box> R)"
    by (simp add: HCSP_hybrid_reactive_design[THEN sym] assms)

  finally show ?thesis .
qed

lemma Chaos_HR_true:
  "Chaos = HR(true)"
  by (simp add: Chaos_def design_def)

(*
lemma Stop_ExtChoice_unit:
  assumes "P is HCSP"
  shows "Stop \<box> P = P"
proof -
  have "Stop \<box> P = HR (true \<turnstile> (events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle>) \<diamondop> false) \<box> HR(pre\<^sub>H(P) \<turnstile> peri\<^sub>H(P) \<diamondop> post\<^sub>H(P))"
    by (simp add: Stop_def HCSP_hybrid_reactive_tri_design'[THEN sym] assms)
  also have "... = 
             HR ((true \<and> pre\<^sub>H P) \<turnstile> (events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle> \<and> peri\<^sub>H P 
                                     \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> 
                                    events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle> \<or> peri\<^sub>H P) 
                                 \<diamondop> (false \<or> post\<^sub>H P))"
    by (simp add: HR_tri_design_ExtChoice unrest)
  also have "... = HR(pre\<^sub>H(P) \<turnstile> peri\<^sub>H(P) \<diamondop> post\<^sub>H(P))"
  proof -
    have "(events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle> \<and> peri\<^sub>H P \<triangleleft> $tr\<acute> =\<^sub>u $tr \<triangleright> events\<^sub>u($tr\<acute> - $tr) =\<^sub>u \<langle>\<rangle> \<or> peri\<^sub>H P) = peri\<^sub>H(P)"
      apply (rel_auto)
    thus ?thesis by simp
  qed
  also have "... = P"
    by (simp add: HCSP_hybrid_reactive_tri_design'[THEN sym] assms)
  finally show ?thesis .
qed
*)

lemma Chaos_ExtChoice_zero:
  assumes "P is HCSP"
  shows "Chaos \<box> P = Chaos"
proof -
  have "Chaos \<box> P = HR (false \<turnstile> true) \<box> HR((\<not> P\<^sup>f\<^sub>f) \<turnstile> P\<^sup>t\<^sub>f)"
    by (simp add: Chaos_def wait'_cond_def cond_idem HCSP_hybrid_reactive_design[THEN sym] assms)
  also have "... = HR (false \<turnstile> (P\<^sup>t\<^sub>f \<triangleleft> $wait\<acute> \<and> $tr\<acute> =\<^sub>u $tr \<triangleright> true))"
    by (simp add: HR_design_ExtChoice unrest)
  also have "... = HR (true)"
    by (simp add: design_def)
  also have "... = Chaos"
    by (simp add: Chaos_HR_true)
  finally show ?thesis .
qed

end
