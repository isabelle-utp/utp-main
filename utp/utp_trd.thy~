section {* Continuous time reactive designs *}

theory utp_trd
imports utp_rea_designs
begin

type_synonym ('d, 'c) alpha_trd_scheme = "('c ttrace, 'd \<times> 'c) alpha_rp_scheme"

type_synonym ('d,'c) alphabet_trd  = "('d,'c) alpha_trd_scheme alphabet"
type_synonym ('d,'c) relation_trd = "(('d,'c) alphabet_trd, ('d,'c) alphabet_trd) relation"
type_synonym ('a,'d,'c) expr_trd  = "('a, ('d,'c) alphabet_trd \<times> ('d,'c) alphabet_trd) uexpr"
type_synonym ('a,'d,'c) cond_trd  = "('a, ('d,'c) alphabet_trd) uexpr"
type_synonym ('d,'c) predicate_cml  = "('d,'c) alphabet_trd upred"

syntax
  "_ulens_expr" :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("_:'(_')" [100,100] 100)

translations
  "_ulens_expr e x" == "CONST uop get\<^bsub>x\<^esub> e"                                                                                                                                       

abbreviation trace :: "('c::topological_space ttrace, 'd, 'c) expr_trd" ("\<phi>") where
"\<phi> \<equiv> $tr\<acute> - $tr"

abbreviation time_length :: "_" ("\<^bold>l")
where "\<^bold>l \<equiv> uop end\<^sub>t trace"

no_notation Not  ("~ _" [40] 40)

abbreviation cvar :: 
  "('a \<Longrightarrow> 'c::topological_space) \<Rightarrow> (real, 'd, 'c) expr_trd \<Rightarrow> ('a, 'd, 'c) expr_trd" ("_~'(_')" [999,0] 999) where
"x~(t) \<equiv> \<phi>\<lparr>t\<rparr>\<^sub>u:(x)"

translations
  "\<phi>" <= "CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))"
  "x~(t)" <= "CONST uop (CONST lens_get x) (CONST bop (CONST uapply) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))) t)"
  "\<^bold>l" <= "CONST uop end\<^sub>t (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr)))"

definition disc_alpha :: "_" ("\<^bold>d") where
[uvar_defs]: "disc_alpha = fst\<^sub>L ;\<^sub>L \<Sigma>\<^sub>R"

definition cont_alpha :: "_" ("\<^bold>c") where
[uvar_defs]: "cont_alpha = snd\<^sub>L ;\<^sub>L \<Sigma>\<^sub>R"

lemma disc_alpha_vwb_lens [simp]: "vwb_lens \<^bold>d"
  by (simp add: comp_vwb_lens disc_alpha_def fst_vwb_lens)

lemma disc_indep_ok [simp]: "\<^bold>d \<bowtie> ok" "ok \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_left_ext lens_indep_sym)

lemma disc_indep_wait [simp]: "\<^bold>d \<bowtie> wait" "wait \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_left_ext lens_indep_sym)

lemma disc_indep_tr [simp]: "\<^bold>d \<bowtie> tr" "tr \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_left_ext lens_indep_sym)

lemma cont_alpha_uvar [simp]: "vwb_lens \<^bold>c"
  by (simp add: comp_vwb_lens cont_alpha_def snd_vwb_lens)

lemma cont_indep_ok [simp]: "\<^bold>c \<bowtie> ok" "ok \<bowtie> \<^bold>c"
  by (simp_all add: cont_alpha_def lens_indep_left_ext lens_indep_sym)

lemma cont_indep_wait [simp]: "\<^bold>c \<bowtie> wait" "wait \<bowtie> \<^bold>c"
  by (simp_all add: cont_alpha_def lens_indep_left_ext lens_indep_sym)

lemma cont_indep_tr [simp]: "\<^bold>c \<bowtie> tr" "tr \<bowtie> \<^bold>c"
  by (simp_all add: cont_alpha_def lens_indep_left_ext lens_indep_sym)

lemma cont_indep_disc [simp]: "\<^bold>c \<bowtie> \<^bold>d" "\<^bold>d \<bowtie> \<^bold>c"
  apply (simp_all add: disc_alpha_def cont_alpha_def lens_indep_left_ext)
  using fst_snd_lens_indep lens_indep_left_comp lens_indep_sym rea_lens_vwb_lens vwb_lens_mwb apply blast
  using fst_snd_lens_indep lens_indep_left_comp lens_indep_sym rea_lens_vwb_lens vwb_lens_mwb apply blast
done

abbreviation disc_lift :: "('a, 'd \<times> 'd) uexpr \<Rightarrow> ('a, 'd, 'c::topological_space) expr_trd" ("\<lceil>_\<rceil>\<^sub>\<delta>") where
"\<lceil>P\<rceil>\<^sub>\<delta> \<equiv> P \<oplus>\<^sub>p (\<^bold>d \<times>\<^sub>L \<^bold>d)"

abbreviation cont_lift :: "('a, 'c \<times> 'c) uexpr \<Rightarrow> ('a, 'd, 'c::topological_space) expr_trd" ("\<lceil>_\<rceil>\<^sub>C") where
"\<lceil>P\<rceil>\<^sub>C \<equiv> P \<oplus>\<^sub>p (\<^bold>c \<times>\<^sub>L \<^bold>c)"

abbreviation cont_pre_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c::topological_space) expr_trd" ("\<lceil>_\<rceil>\<^sub>C\<^sub><") where
"\<lceil>P\<rceil>\<^sub>C\<^sub>< \<equiv> P \<oplus>\<^sub>p (ivar \<^bold>c)"

syntax
  "_cont_alpha" :: "svid" ("\<^bold>c")
  "_disc_alpha" :: "svid" ("\<^bold>d")

translations
  "_cont_alpha" == "CONST cont_alpha"
  "_disc_alpha" == "CONST disc_alpha"
  "\<lceil>P\<rceil>\<^sub>C\<^sub><" <= "CONST aext P (CONST ivar CONST cont_alpha)"

lemma var_in_var_prod [simp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "var ((in_var x) ;\<^sub>L X \<times>\<^sub>L Y) = $X:(x)"
  by (pred_auto)

lemma var_out_var_prod [simp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "var ((out_var x) ;\<^sub>L X \<times>\<^sub>L Y) = $Y\<acute>:(x)"
  by (pred_auto)

definition ufloor :: "'a::{floor_ceiling} \<Rightarrow> 'a" 
where [upred_defs]: "ufloor = of_int \<circ> floor"

definition uceiling :: "'a::{floor_ceiling} \<Rightarrow> 'a"
where [upred_defs]: "uceiling = of_int \<circ> floor"

syntax
  "_ufloor"   :: "logic \<Rightarrow> logic" ("\<lfloor>_\<rfloor>\<^sub>u")
  "_uceiling" :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>u")

translations
  "\<lfloor>x\<rfloor>\<^sub>u" == "CONST uop CONST ufloor x"
  "\<lceil>x\<rceil>\<^sub>u" == "CONST uop CONST uceiling x"

lemma rea_var_ords [usubst]:
  "$\<^bold>c \<prec>\<^sub>v $tr" "$\<^bold>c \<prec>\<^sub>v $tr\<acute>" "$\<^bold>c\<acute> \<prec>\<^sub>v $tr" "$\<^bold>c\<acute> \<prec>\<^sub>v $tr\<acute>"
  by (simp_all add: var_name_ord_def)

lemma zero_least_uexpr [simp]:
  "0 \<le>\<^sub>u (x::('a::ordered_cancel_monoid_diff, '\<alpha>) uexpr) = true"
  by (rel_auto)

syntax
  "_uend" :: "logic \<Rightarrow> logic" ("end\<^sub>u'(_')")
  "_time" :: "logic" ("time")
  "_time'" :: "logic" ("time'")

translations
  "time"  == "CONST uop end\<^sub>t (CONST var (CONST ivar CONST tr))"
  "time'" == "CONST uop end\<^sub>t (CONST var (CONST ovar CONST tr))"
  "end\<^sub>u(t)" == "CONST uop end\<^sub>t t"

(* Need to lift the continuous predicate to a relation *)

definition at :: "('a, 'c::topological_space) uexpr \<Rightarrow> real \<Rightarrow> ('a, 'd, 'c) expr_trd" (infix "@\<^sub>u" 60) where
[upred_defs]: "P @\<^sub>u t = [$\<^bold>c \<mapsto>\<^sub>s \<phi>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u] \<dagger> \<lceil>P\<rceil>\<^sub>C\<^sub><" 

lemma R2c_at: "R2c(P @\<^sub>u t) = P @\<^sub>u t"
  by (simp add: at_def R2c_def cond_idem usubst unrest R2s_def)

definition until ("_ until _" [85,86] 85) where
[upred_defs]: "P until l = ((\<^bold>\<forall> t \<in> {0..<\<^bold>l}\<^sub>u \<bullet> (P t) @\<^sub>u t) \<and> $tr \<le>\<^sub>u $tr\<acute> \<and> \<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright>)"

lemma R2_until:
  "R2(P until t) = P until t"
  by (rel_auto)

lemma at_unrest_cont [unrest]: "$\<^bold>c \<sharp> (P @\<^sub>u t)"
  by (simp add: at_def unrest)

lemma at_unrest_ok [unrest]: "$ok \<sharp> (P @\<^sub>u t)" "$ok\<acute> \<sharp> (P @\<^sub>u t)"
  by (simp_all add: at_def unrest alpha)

lemma at_unrest_wait [unrest]: "$wait \<sharp> (P @\<^sub>u t)" "$wait\<acute> \<sharp> (P @\<^sub>u t)"
  by (simp_all add: at_def unrest alpha)

lemma at_true [simp]: "true @\<^sub>u t = true"
  by (simp add: at_def alpha usubst)

lemma at_false [simp]: "false @\<^sub>u t = false"
  by (simp add: at_def alpha usubst)

lemma at_conj [simp]: "(P \<and> Q) @\<^sub>u t = (P @\<^sub>u t \<and> Q @\<^sub>u t)"
  by (simp add: at_def alpha usubst)

lemma at_disj [simp]: "(P \<or> Q) @\<^sub>u t = (P @\<^sub>u t \<or> Q @\<^sub>u t)"
  by (simp add: at_def alpha usubst)

lemma at_ueq [simp]: "(x =\<^sub>u y) @\<^sub>u t = (x @\<^sub>u t =\<^sub>u y @\<^sub>u t)"
  by (simp add: at_def usubst alpha)

lemma at_plus [simp]:
  "(x + y) @\<^sub>u t = ((x @\<^sub>u t) + (y @\<^sub>u t))"
  by (simp add: at_def alpha usubst)

lemma at_var [simp]:
  fixes x :: "('a, 'c::topological_space) uvar"
  shows "var x @\<^sub>u t = \<phi>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u:(x)"
  by (pred_auto)

definition hInt :: "(real \<Rightarrow> 'c::topological_space upred) \<Rightarrow> ('d,'c) relation_trd" where
[urel_defs]: "hInt P = ($tr <\<^sub>u $tr\<acute> \<and> (\<^bold>\<forall> t \<in> {0..<\<^bold>l}\<^sub>u \<bullet> (P t) @\<^sub>u t))"

lemma hInt_unrest_ok [unrest]: "$ok \<sharp> hInt P" "$ok\<acute> \<sharp> hInt P"
  by (simp_all add: hInt_def unrest)

lemma hInt_unrest_wait [unrest]: "$wait \<sharp> hInt P" "$wait\<acute> \<sharp> hInt P"
  by (simp_all add: hInt_def unrest)

definition hDisInt :: "(real \<Rightarrow> 'c::t2_space upred) \<Rightarrow> ('d, 'c) relation_trd" where 
[urel_defs]: "hDisInt P = (hInt P \<and> $\<^bold>c =\<^sub>u \<phi>\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> \<^bold>l\<^sup>-)(\<phi>\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"

syntax
  "_time_var" :: "logic"
  "_hInt"     :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>H")
  "_hDisInt"  :: "logic \<Rightarrow> logic" ("\<^bold>\<lceil>_\<^bold>\<rceil>\<^sub>H")

parse_translation {*
let
  fun time_var_tr [] = Syntax.free "\<tau>"
    | time_var_tr _  = raise Match;
in
[(@{syntax_const "_time_var"}, K time_var_tr)]
end
*}

translations
  "\<lceil>P\<rceil>\<^sub>H" == "CONST hInt (\<lambda> _time_var. P)"
  "\<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>H" == "CONST hDisInt (\<lambda> _time_var. P)"

definition hPreempt :: 
  "('d, 'c::topological_space) relation_trd \<Rightarrow> 'c upred \<Rightarrow> 
    ('d,'c) relation_trd \<Rightarrow> ('d,'c) relation_trd" ("_ \<lbrakk>_\<rbrakk>\<^sub>H _" [64,0,65] 64)
where "P \<lbrakk>B\<rbrakk>\<^sub>H Q = (((Q \<triangleleft> B @\<^sub>u 0 \<triangleright> (P \<and> \<lceil>\<not> B\<rceil>\<^sub>H)) \<or> ((\<lceil>\<not> B\<rceil>\<^sub>H \<and> P) ;; ((B @\<^sub>u 0) \<and> Q))))"

lemma uend_0 [simp]: "end\<^sub>u(0) = 0"
  by (simp add: upred_defs lit_def uop_def Abs_uexpr_inverse)

lemma R2c_time_range: "R2c (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<time'-time}\<^sub>u) = (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<time'-time}\<^sub>u)"
  by (rel_auto ; simp add: tt_end_minus)

lemma R2c_time_length: "R2c (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u) = (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u)"
  by (rel_auto ; simp add: tt_end_minus)

lemma R2c_tr_less_tr': "R2c($tr <\<^sub>u $tr\<acute>) = ($tr <\<^sub>u $tr\<acute>)"
  apply (rel_auto)
  using le_imp_less_or_eq apply fastforce
  using dual_order.strict_iff_order minus_zero_eq apply fastforce
done

lemma R2c_shAll: "R2c (\<^bold>\<forall> x \<bullet> P x) = (\<^bold>\<forall> x \<bullet> R2c(P x))"
  by (rel_auto)

lemma R2c_impl: "R2c(P \<Rightarrow> Q) = (R2c(P) \<Rightarrow> R2c(Q))"
  by (metis (no_types, lifting) R2c_and R2c_not double_negation impl_alt_def not_conj_deMorgans)

lemma R1_tr_less_tr': "R1($tr <\<^sub>u $tr\<acute>) = ($tr <\<^sub>u $tr\<acute>)"
  by (rel_auto)

lemma hInt_unrest_cont [unrest]: "$\<^bold>c \<sharp> \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (simp add: hInt_def unrest)

lemma R1_hInt: "R1(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (simp add: hInt_def R1_extend_conj R1_tr_less_tr')

lemma R2s_hInt: "R2c(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (simp add: hInt_def R2c_and R2c_tr_less_tr' R2c_shAll R2c_impl R2c_time_length R2c_at)

lemma R2_hInt: "R2(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (metis R1_R2c_is_R2 R1_hInt R2s_hInt)

lemma hInt_false: "\<lceil>false\<rceil>\<^sub>H = false"
  by (simp add: hInt_def, rel_auto, metis dual_order.strict_iff_order minus_zero_eq tt_end_0_iff tt_end_ge_0)

lemma seqr_to_conj: "\<lbrakk> out\<alpha> \<sharp> P; in\<alpha> \<sharp> Q \<rbrakk> \<Longrightarrow> (P ;; Q) = (P \<and> Q)"
  by (metis postcond_left_unit seqr_pre_out utp_pred.inf_top.right_neutral)

lemma unrest_lift_cont_subst [unrest]:
  "\<lbrakk> vwb_lens x; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> (\<lceil>P\<rceil>\<^sub>C\<^sub><)\<lbrakk>v/$\<^bold>c\<rbrakk>"
  by (rel_auto)

lemma hInt_refine: "`\<^bold>\<forall> \<tau> \<bullet> P(\<tau>) \<Rightarrow> Q(\<tau>)` \<Longrightarrow> \<lceil>Q(\<tau>)\<rceil>\<^sub>H \<sqsubseteq> \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (rel_auto)

lemma hInt_seq_r: "(\<lceil>P\<rceil>\<^sub>H ;; \<lceil>P\<rceil>\<^sub>H) = \<lceil>P\<rceil>\<^sub>H"
proof -
  have "(\<lceil>P\<rceil>\<^sub>H ;; \<lceil>P\<rceil>\<^sub>H) = (R2(\<lceil>P\<rceil>\<^sub>H) ;; R2(\<lceil>P\<rceil>\<^sub>H))"
    by (simp add: R2_hInt)
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<lceil>P\<rceil>\<^sub>H)\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; (\<lceil>P\<rceil>\<^sub>H)\<lbrakk>0/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (simp add: R2_seqr_form)
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<guillemotleft>tt\<^sub>1\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>) ;;
                                     \<guillemotleft>tt\<^sub>2\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>)) \<and>
                         $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (simp add: hInt_def at_def usubst unrest)
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tt\<^sub>1\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>)) \<and>
                                     (\<guillemotleft>tt\<^sub>2\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and>
                         $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (simp add: seqr_to_conj unrest)
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tt\<^sub>1\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>tt\<^sub>2\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>(\<guillemotleft>tt\<^sub>1\<guillemotright>+\<guillemotleft>tt\<^sub>2\<guillemotright>)\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and>
                         $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<^sub>1\<guillemotright> + \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    apply (rule shEx_cong)
    apply (rule shEx_cong)
    apply (rel_auto)
    apply (auto simp add: tt_end_cat)
    apply (rename_tac x xa P xb)
    apply (case_tac "xb < end\<^sub>t x")
    apply (auto simp add: tt_cat_ext_first tt_cat_ext_last)
    apply (metis add.right_neutral add_less_le_mono tt_cat_ext_first tt_end_ge_0)
    apply (rename_tac x xa P xb)
    apply (drule_tac x="end\<^sub>t x + xb" in spec)
    apply (simp)
  done
  also have "... = (\<^bold>\<exists> tt \<bullet> ((\<guillemotleft>tt\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>(\<guillemotleft>tt\<guillemotright>)\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<guillemotright>)"
  proof (rel_auto)
    fix P tr and tt\<^sub>1 tt\<^sub>2 :: "'a ttrace"
    assume  "0 < tt\<^sub>1" "0 < tt\<^sub>2" "\<forall>i. 0 \<le> i \<and> i < end\<^sub>t (tt\<^sub>1 + tt\<^sub>2) \<longrightarrow> P (\<langle>tt\<^sub>1 + tt\<^sub>2\<rangle>\<^sub>t i)"
    thus "\<exists> tt. 0 < tt \<and> (\<forall> i. 0 \<le> i \<and> i < end\<^sub>t tt \<longrightarrow> P (\<langle>tt\<rangle>\<^sub>ti)) \<and> tr + tt\<^sub>1 + tt\<^sub>2 = tr + tt"
      using add.assoc le_add less_le_trans by blast
  next
    fix P tr and tt :: "'a ttrace"
    assume "0 < tt" "\<forall>i. 0 \<le> i \<and> i < end\<^sub>t tt \<longrightarrow> P (\<langle>tt\<rangle>\<^sub>t i)"
    moreover then obtain tt\<^sub>1 tt\<^sub>2 where "tt = tt\<^sub>1 + tt\<^sub>2" "end\<^sub>t tt\<^sub>1 > 0" "end\<^sub>t tt\<^sub>2 > 0"
      by (metis dual_order.strict_iff_order tt_end_0_iff tt_end_ge_0 ttrace_divisible)
    moreover hence "tt\<^sub>1 > 0" "tt\<^sub>2 > 0"
      by (simp_all add: least_zero less_le tt_end_0_iff)
    ultimately show 
      "\<exists>tt\<^sub>1. 0 < tt\<^sub>1 \<and>
            (\<exists>tt\<^sub>2. 0 < tt\<^sub>2 \<and>
                  (\<forall>i. 0 \<le> i \<and> i < end\<^sub>t (tt\<^sub>1 + tt\<^sub>2) \<longrightarrow> P (\<langle>tt\<^sub>1 + tt\<^sub>2\<rangle>\<^sub>t i)) \<and> tr + tt = tr + tt\<^sub>1 + tt\<^sub>2)"
      by (metis add.assoc)
  qed
  also have "... = R2(\<lceil>P\<rceil>\<^sub>H)"
    by (simp add: R2_form hInt_def at_def usubst unrest)
  also have "... = \<lceil>P\<rceil>\<^sub>H"
    by (simp add: R2_hInt)
  finally show ?thesis .
qed

lemma hInt_true: "\<lceil>true\<rceil>\<^sub>H = ($tr <\<^sub>u $tr\<acute>)"
  by (rel_auto)

lemma "P \<lbrakk>true\<rbrakk>\<^sub>H Q = Q"
  by (simp add: hPreempt_def hInt_false)

lemma "P \<lbrakk>false\<rbrakk>\<^sub>H Q = (P \<and> $tr <\<^sub>u $tr\<acute>)"
  by (simp add: hPreempt_def hInt_true)

lemma hInt_conj: "\<lceil>P(\<tau>) \<and> Q(\<tau>)\<rceil>\<^sub>H = (\<lceil>P(\<tau>)\<rceil>\<^sub>H \<and> \<lceil>Q(\<tau>)\<rceil>\<^sub>H)"
  by (rel_auto)

type_synonym 'c ODE = "real \<times> 'c \<Rightarrow> 'c"

lift_definition hasDerivAt :: 
  "((real \<Rightarrow> 'c :: real_normed_vector), '\<alpha>) uexpr \<Rightarrow> 
   ('c ODE, '\<alpha>) uexpr \<Rightarrow> real \<Rightarrow> real \<Rightarrow> '\<alpha> upred" ("_ has-deriv _ at _ < _" [90, 0, 91] 90)
is "\<lambda> \<F> \<F>' \<tau> l A. (\<F> A has_vector_derivative (\<F>' A (\<tau>, \<F> A \<tau>))) (at \<tau> within {0..l})" .

lemma hasDerivAt_unrest [unrest]: "\<lbrakk> vwb_lens x; x \<sharp> f; x \<sharp> f' \<rbrakk> \<Longrightarrow> x \<sharp> f has-deriv f' at \<tau> < l"
  by (pred_auto, presburger+)

definition mk_IVP ("IVP'(_,_,_')") where
[upred_defs]: "mk_IVP = trop (\<lambda> f t' x\<^sub>0. ivp.make f 0 x\<^sub>0 {0..t'} UNIV)"

definition is_solution ("_ has-solution _" [90, 91] 90) where 
[upred_defs]: "is_solution = bop ivp.is_solution"

definition hODE :: "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a ODE, 'c) uexpr \<Rightarrow> ('d, 'c) relation_trd" ("\<langle>_ \<bullet> _\<rangle>\<^sub>H") where
[urel_defs]: "\<langle>x \<bullet> \<F>'\<rangle>\<^sub>H = (\<^bold>\<exists> \<F>, l \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> \<^bold>\<lceil> \<guillemotleft>\<F>\<guillemotright> has-deriv \<F>' at \<tau> < l \<and> &x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u \<^bold>\<rceil>\<^sub>H)"

(*
definition hODE_ivp :: "('a, 'd, 'c) cond_trd \<Rightarrow> ('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a ODE, 'c) uexpr \<Rightarrow> ('d, 'c) relation_trd" ("_ \<Turnstile> \<langle>_ \<bullet> _\<rangle>\<^sub>H") where
[urel_defs]: "\<I> \<Turnstile> \<langle>x \<bullet> \<F>'\<rangle>\<^sub>H = \<langle>x \<bullet> \<F>'\<rangle>\<^sub>H\<lbrakk>\<lceil>\<I>\<rceil>\<^sub></$\<^bold>c:x\<rbrakk>"


definition hODE :: 
  "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> 
   ('a ODE, 'c) uexpr \<Rightarrow> ('d, 'c) relation_trd" ("\<langle>_ \<bullet> _\<rangle>\<^sub>H") where
  [upred_defs]:
  "hODE x \<F>' = (\<^bold>\<exists> \<F> \<bullet> ($tr <\<^sub>u $tr\<acute>
                       \<and> IVP(\<lceil>\<F>'\<rceil>\<^sub>C\<^sub><, \<^bold>l, $\<^bold>c:x) has-solution \<guillemotleft>\<F>\<guillemotright>
                       \<and> (\<^bold>\<forall> t\<in>{0..<\<^bold>l}\<^sub>u \<bullet> x~(\<guillemotleft>t\<guillemotright>) =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u)
                       \<and> $\<^bold>c:x\<acute> =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<^bold>l\<rparr>\<^sub>u))"
*)

abbreviation hODE_IVP ("\<langle>_ := _ \<bullet> _\<rangle>\<^sub>H") where
"\<langle>x := x\<^sub>0 \<bullet> \<F>'\<rangle>\<^sub>H \<equiv> (\<^bold>c:x := x\<^sub>0 ;; \<langle>x \<bullet> \<F>'\<rangle>\<^sub>H)"

lemma is_ivp_make: "0 \<in> T \<Longrightarrow> ivp (ivp.make \<F>' 0 x\<^sub>0 T UNIV)"
  by (unfold_locales, simp_all add: ivp.make_def)

lemma at_left_from_zero:
  "n > 0 \<Longrightarrow> at_left n = at n within {0::real ..< n}"
  by (rule at_within_nhd[of _ "{0<..<n+1}"], auto)

lemma ivp_solution_refine:
  "\<lbrakk> vwb_lens x; \<forall> l > 0. ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV) \<F> \<rbrakk> 
   \<Longrightarrow> \<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H \<sqsubseteq> (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H)"
proof (rel_auto)
  fix x :: "'a \<Longrightarrow> 'b" and \<F>' x\<^sub>0 \<F> tr b tr' v
  assume assms:
    "vwb_lens x" "\<forall>l>0. ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV) \<F>"
    "tr < tr'" "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = \<F> t"
    "put\<^bsub>x\<^esub> b v = \<langle>tr'\<rangle>\<^sub>t(end\<^sub>t tr)"

  let ?l = "end\<^sub>t (tr' - tr)"

  have etr_nz: "?l > 0"
    by (metis assms less_le minus_zero_eq tt_end_0_iff tt_end_ge_0)

  have tr_f: "\<forall>t. 0 \<le> t \<and> t < ?l \<longrightarrow> (get\<^bsub>x\<^esub> \<circ> \<langle>tr' - tr\<rangle>\<^sub>t) t = \<F> t"
    by (simp add: assms less_imp_le)

(*
  obtain L where L:"(\<langle>tr' - tr\<rangle>\<^sub>t \<longlongrightarrow> L) (at ?l within {0..<?l})"
    using at_left_from_zero etr_nz ttrace_convergent_end by fastforce

  hence "((get\<^bsub>x\<^esub> \<circ> \<langle>tr' - tr\<rangle>\<^sub>t) \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at ?l within {0..<?l})"
    by (force intro: continuous_on_tendsto_compose[of UNIV "get\<^bsub>x\<^esub>"] simp add: comp_def assms) 

  moreover have "((get\<^bsub>x\<^esub> \<circ> \<langle>tr' - tr\<rangle>\<^sub>t) \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at ?l within {0..<?l}) 
                 \<longleftrightarrow>
                 (\<F> \<longlongrightarrow> get\<^bsub>x\<^esub> L) (at ?l within {0..<?l})"
    using tr_f by (rule_tac Lim_cong_within, auto)

  moreover have "(\<F> \<longlongrightarrow> \<F> (end\<^sub>t (tr' - tr))) (at ?l within {0..<?l})"
  proof -
    have "continuous_on {0..end\<^sub>t(tr'-tr)} \<F>"
    proof -
      have 1:"ivp (ivp.make \<F>' 0 x\<^sub>0 {0..end\<^sub>t (tr' - tr)} UNIV)"
        by (simp add: is_ivp_make)  
      have 2:"ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..end\<^sub>t (tr' - tr)} UNIV) \<F>"
        using assms(3) etr_nz by blast
      show ?thesis
        using ivp.solution_continuous_on[OF 1 2] by (simp add: ivp.make_def)
    qed
    thus ?thesis
      by (simp add: etr_nz at_left_from_zero, meson atLeastAtMost_iff atLeastLessThan_subseteq_atLeastAtMost_iff continuous_on etr_nz less_le order_refl tendsto_within_subset)
  qed

  ultimately have "get\<^bsub>x\<^esub> L = \<F> (end\<^sub>t (tr' - tr))"
    by (metis at_left_from_zero etr_nz tendsto_Lim trivial_limit_at_left_real)
*)

  have ivp:"ivp (ivp.make \<F>' 0 x\<^sub>0 {0..end\<^sub>t (tr' - tr)} UNIV)"
    by (simp add: is_ivp_make)

  have sol: "ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..end\<^sub>t (tr' - tr)} UNIV) \<F>"
    using assms etr_nz by blast
    
  have "get\<^bsub>x\<^esub> (\<langle>tr' - tr\<rangle>\<^sub>t 0) = x\<^sub>0"
    using sol etr_nz tr_f
    by (auto simp add: ivp.is_solution_def[OF ivp, of \<F>], simp add: ivp.make_def)
  thus "put\<^bsub>x\<^esub> b x\<^sub>0 = \<langle>tr'\<rangle>\<^sub>t(end\<^sub>t tr)"
    by (metis add.left_neutral assms(1) assms(4) assms(5) comp_def etr_nz mwb_lens.axioms(1) order_refl tr_f vwb_lens.axioms(2) weak_lens.put_get)

  with etr_nz assms show
    "\<exists> f. \<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow>
            (f has_vector_derivative \<F>' (t, f t)) (at t within {0..?l}) \<and> \<F> t = f t"
  proof (rule_tac x="\<F>" in exI, safe)
    fix t
    assume t: "0 \<le> t" "t < end\<^sub>t (tr' - tr)"
    
    show "(\<F> has_vector_derivative \<F>' (t, \<F> t)) (at t within {0..?l})"
      using sol t
      by (auto simp add: ivp.is_solution_def[OF ivp, of \<F>], simp add: ivp.make_def)
  qed
qed

lemma "(\<^bold>\<lceil>P(\<tau>)\<^bold>\<rceil>\<^sub>H ;; \<^bold>\<lceil>P(\<tau>)\<^bold>\<rceil>\<^sub>H) = \<^bold>\<lceil>P(\<tau>)\<^bold>\<rceil>\<^sub>H"
  apply (rel_auto)
oops

lemma ivp_uniq_solution_refine:
  "\<lbrakk> vwb_lens x; 
     \<forall> l > 0. ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV) \<F>;
     \<forall> l > 0. unique_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV) \<rbrakk> 
   \<Longrightarrow> (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H) \<sqsubseteq> (\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H)"
proof (rel_auto)
  fix x :: "'a \<Longrightarrow> 'b" and \<F>' x\<^sub>0 \<F> tr b tr' \<G> t
  assume assms:
    "vwb_lens x" "\<forall>l>0. ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV) \<F>"
    "\<forall>l>0. unique_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV)"
    "tr < tr'"
    "put\<^bsub>x\<^esub> b x\<^sub>0 = \<langle>tr'\<rangle>\<^sub>t (end\<^sub>t tr)"
    "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow>
         (\<G> has_vector_derivative \<F>' (t, \<G> t)) (at t within {0..end\<^sub>t (tr' - tr)}) \<and>
         get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t (t + end\<^sub>t tr)) = \<G> t"
    "0 \<le> t" "t < end\<^sub>t (tr' - tr)"

  let ?l = "end\<^sub>t (tr' - tr)"

  have etr_nz: "?l > 0"
    by (metis assms less_le minus_zero_eq tt_end_0_iff tt_end_ge_0)

  interpret usol: unique_solution "(ivp.make \<F>' 0 x\<^sub>0 {0..?l} UNIV)"
    using assms(3) etr_nz by blast

  have init: "get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t (end\<^sub>t tr)) = x\<^sub>0"
    by (subst assms(5)[THEN sym], simp add: assms(1))

  have ivp: "ivp (ivp.make \<F>' 0 x\<^sub>0 {0..<?l} UNIV)"
    by (simp add: etr_nz is_ivp_make)

  have G_sol: "ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..<?l} UNIV) \<G>"
  proof (rule ivp.is_solutionI, simp add: is_ivp_make etr_nz, auto simp add: ivp.make_def)
    show "\<G> 0 = x\<^sub>0"
      using assms(6) etr_nz init by auto
  next
    fix t
    assume "0 \<le> t" "t < end\<^sub>t (tr' - tr)"
    thus "(\<G> has_vector_derivative \<F>' (t, \<G> t)) (at t within {0..<end\<^sub>t (tr' - tr)})"
      by (meson assms(6) atLeastLessThan_subseteq_atLeastAtMost_iff has_vector_derivative_within_subset order_refl)
  qed

  have F_0: "\<F>(0) = x\<^sub>0"
  proof -
    have "ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..?l} UNIV) \<F>"
      using assms(2) etr_nz by blast
    thus ?thesis
      by (simp add: usol.is_solution_def, simp add: ivp.make_def)
  qed
      
  have G_0: "\<G>(0) = x\<^sub>0"
    using assms(6) etr_nz init by auto

  show "\<G> t = \<F> t"
  proof (cases "t = 0")
    case True thus ?thesis
      by (simp add: F_0 G_0)
  next
    case False 
    hence t: "t > 0"
      using assms(7) by linarith
    have "ivp.is_solution ((ivp.make \<F>' 0 x\<^sub>0 {0..<?l} UNIV)\<lparr>ivp_T := {0..t}\<rparr>) \<G>"
      using G_sol assms(8) by (auto intro!: ivp.solution_on_subset simp add: ivp, auto simp add: ivp.make_def, simp add: assms)
    hence 1:"ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..t} UNIV) \<G>"  
      by (simp add: ivp.make_def)
    have 2: "ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..t} UNIV) \<F>"
      using assms(2) t by blast
    have 3:"unique_solution (ivp.make \<F>' 0 x\<^sub>0 {0..t} UNIV)"
      using assms(3) t by blast
    show ?thesis
      using unique_solution.unique_solution[OF 3 1, of t] unique_solution.unique_solution[OF 3 2, of t]
      by (simp add: ivp.make_def assms)
  qed
qed

theorem ivp_to_solution:
  fixes \<F> :: "real \<Rightarrow> 'a::ordered_euclidean_space"
  assumes
    "vwb_lens x"  
    "\<forall> l > 0. ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV) \<F>"
    "\<forall> l > 0. unique_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV)"
  shows "(\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H) = (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H)"
proof (rule antisym)
  from assms show "(\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H) \<sqsubseteq> (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H)"
    by (blast intro: ivp_solution_refine)
next
  from assms show "(\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H) \<sqsubseteq> (\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H)"
    by (rule ivp_uniq_solution_refine)
qed

theorem ivp_to_solution':
  fixes \<F> :: "real \<Rightarrow> 'a::ordered_euclidean_space"
  assumes
    "vwb_lens x"  
    "\<forall> l > 0. ivp.is_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV) \<F>"
    "\<forall> l > 0. unique_solution (ivp.make \<F>' 0 x\<^sub>0 {0..l} UNIV)"
  shows "(\<langle>x := \<guillemotleft>x\<^sub>0\<guillemotright> \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H) = (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>(\<tau>)\<guillemotright>\<^bold>\<rceil>\<^sub>H)"
proof -
  have "(\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>\<guillemotright>\<lparr>\<guillemotleft>\<tau>\<guillemotright>\<rparr>\<^sub>u\<^bold>\<rceil>\<^sub>H) = (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil>&x =\<^sub>u \<guillemotleft>\<F>(\<tau>)\<guillemotright>\<^bold>\<rceil>\<^sub>H)"
    by (rel_auto)
  thus ?thesis
    by (subst ivp_to_solution, simp_all add: assms)
qed

lemma uos_impl_uniq_sol:
  assumes "unique_on_strip i x y"
  shows "unique_solution i"
proof -
  interpret uos: unique_on_strip i x y
    by (simp add: assms)
  show ?thesis
    by (simp add: uos.unique_solution_axioms)
qed

(* Example of solving an ODE *)

lemma gravity_ode_example:
  assumes "vwb_lens x"
  shows "(\<langle>x := \<guillemotleft>(v\<^sub>0, h\<^sub>0)\<guillemotright> \<bullet> \<guillemotleft>(\<lambda> (t, v, h). (- g, v))\<guillemotright>\<rangle>\<^sub>H) =
         (\<exists> $\<^bold>c:x \<bullet> \<^bold>\<lceil> &x =\<^sub>u \<guillemotleft>(v\<^sub>0 - g * \<tau>, v\<^sub>0*\<tau> - g*(\<tau>*\<tau>) / 2 + h\<^sub>0)\<guillemotright> \<^bold>\<rceil>\<^sub>H)"
proof (rule ivp_to_solution')
  have "\<forall>l>0. unique_on_strip (ivp.make (\<lambda>(t, v, h). (- g, v)) 0 (v\<^sub>0, h\<^sub>0) {0..l} UNIV) l 1"
    by (auto, unfold_locales, auto intro!: continuous_on_Pair continuous_on_const Product_Vector.continuous_on_fst continuous_on_snd simp add: ivp.make_def lipschitz_def dist_Pair_Pair prod.case_eq_if)
  thus "\<forall>l>0. unique_solution (ivp.make (\<lambda>(t, v, h). (- g, v)) 0 (v\<^sub>0, h\<^sub>0) {0..l} UNIV)"
    using uos_impl_uniq_sol by blast
  show "\<forall>l>0. ivp.is_solution (ivp.make (\<lambda>(t, v, h). (- g, v)) 0 (v\<^sub>0, h\<^sub>0) {0..l} UNIV)
                              (\<lambda>\<tau>. (v\<^sub>0 - g \<cdot> \<tau>, v\<^sub>0 \<cdot> \<tau> - g \<cdot> (\<tau> \<cdot> \<tau>) / 2 + h\<^sub>0))"
    apply (simp add: ivp.is_solution_def is_ivp_make, auto intro: derivative_intros simp add: ivp.make_def)
    apply (rule has_vector_derivative_eq_rhs) 
    apply (rule derivative_intros)+
    apply (auto intro!: derivative_intros)
  done
  show "vwb_lens x"
    by (simp add: assms)
qed

end
