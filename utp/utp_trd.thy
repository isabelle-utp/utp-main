section {* Continuous time reactive designs *}

theory utp_trd
imports utp_rea_designs
begin

type_synonym ('d, 'c) alpha_trd_scheme = "('c cgf, 'd \<times> 'c) alpha_rp_scheme"

type_synonym ('d,'c) alphabet_trd  = "('d,'c) alpha_trd_scheme alphabet"
type_synonym ('d,'c) relation_trd = "(('d,'c) alphabet_trd, ('d,'c) alphabet_trd) relation"
type_synonym ('a,'d,'c) expr_trd  = "('a, ('d,'c) alphabet_trd \<times> ('d,'c) alphabet_trd) uexpr"
type_synonym ('d,'c) predicate_cml  = "('d,'c) alphabet_trd upred"

syntax
  "_ulens_expr" :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("_:'(_')" [100,100] 100)

translations
  "_ulens_expr e x" == "CONST uop get\<^bsub>x\<^esub> e"

abbreviation trace :: "('c cgf, 'd, 'c) expr_trd" ("\<phi>") where
"\<phi> \<equiv> $tr\<acute> - $tr"

abbreviation time_length :: "_" ("\<^bold>l")
where "\<^bold>l \<equiv> uop end\<^sub>C trace"

no_notation Not  ("~ _" [40] 40)

abbreviation cvar :: "_ \<Rightarrow> _ \<Rightarrow> _" ("_~'(_')" [999,0] 999) where
"x~(t) \<equiv> \<phi>\<lparr>t\<rparr>\<^sub>u:(x)"

translations
  "\<phi>" <= "CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))"
  "x~(t)" <= "CONST uop (CONST lens_get x) (CONST bop (CONST uapply) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))) t)"
  "\<^bold>l" <= "CONST uop end\<^sub>C (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr)))"

definition disc_alpha :: "_" ("\<^bold>d") where
[upred_defs]: "disc_alpha = fst\<^sub>L ;\<^sub>L \<Sigma>\<^sub>R"

definition cont_alpha :: "_" ("\<^bold>c") where
[upred_defs]: "cont_alpha = snd\<^sub>L ;\<^sub>L \<Sigma>\<^sub>R"

lemma disc_alpha_uvar [simp]: "uvar \<^bold>d"
  by (simp add: comp_vwb_lens disc_alpha_def fst_vwb_lens)

lemma disc_indep_tr [simp]: "\<^bold>d \<bowtie> tr" "tr \<bowtie> \<^bold>d"
  by (simp_all add: disc_alpha_def lens_indep_left_ext lens_indep_sym)

lemma cont_alpha_uvar [simp]: "uvar \<^bold>c"
  by (simp add: comp_vwb_lens cont_alpha_def snd_vwb_lens)

lemma cont_indep_tr [simp]: "\<^bold>c \<bowtie> tr" "tr \<bowtie> \<^bold>c"
  by (simp_all add: cont_alpha_def lens_indep_left_ext lens_indep_sym)

abbreviation disc_lift :: "('a, 'd \<times> 'd) uexpr \<Rightarrow> ('a, 'd, 'c) expr_trd" ("\<lceil>_\<rceil>\<^sub>\<delta>") where
"\<lceil>P\<rceil>\<^sub>\<delta> \<equiv> P \<oplus>\<^sub>p (\<^bold>d \<times>\<^sub>L \<^bold>d)"

abbreviation cont_lift :: "('a, 'c \<times> 'c) uexpr \<Rightarrow> ('a, 'd, 'c) expr_trd" ("\<lceil>_\<rceil>\<^sub>C") where
"\<lceil>P\<rceil>\<^sub>C \<equiv> P \<oplus>\<^sub>p (\<^bold>c \<times>\<^sub>L \<^bold>c)"

abbreviation cont_pre_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c) expr_trd" ("\<lceil>_\<rceil>\<^sub>C\<^sub><") where
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
  by (pred_tac)

lemma var_out_var_prod [simp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "var ((out_var x) ;\<^sub>L X \<times>\<^sub>L Y) = $Y\<acute>:(x)"
  by (pred_tac)

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
  by (rel_tac)

syntax
  "_uend" :: "logic \<Rightarrow> logic" ("end\<^sub>u'(_')")
  "_time" :: "logic" ("time")
  "_time'" :: "logic" ("time'")

translations
  "time"  == "CONST uop end\<^sub>C (CONST var (CONST ivar CONST tr))"
  "time'" == "CONST uop end\<^sub>C (CONST var (CONST ovar CONST tr))"
  "end\<^sub>u(t)" == "CONST uop end\<^sub>C t"

(* Need to lift the continuous predicate to a relation *)

definition at :: "('a, 'c) uexpr \<Rightarrow> real \<Rightarrow> ('a, 'd, 'c) expr_trd" (infix "@\<^sub>u" 60) where
[upred_defs]: "P @\<^sub>u t = [$\<^bold>c \<mapsto>\<^sub>s \<phi>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u] \<dagger> \<lceil>P\<rceil>\<^sub>C\<^sub><" 

lemma R2c_at: "R2c(P @\<^sub>u t) = P @\<^sub>u t"
  by (simp add: at_def R2c_def cond_idem usubst unrest R2s_def)

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
  fixes x :: "('a, 'c) uvar"
  shows "var x @\<^sub>u t = \<phi>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u:(x)"
  by (pred_tac)

definition hInt :: "(real \<Rightarrow> 'c upred) \<Rightarrow> ('d,'c) relation_trd" where
[urel_defs]: "hInt P = ($tr <\<^sub>u $tr\<acute> \<and> (\<^bold>\<forall> t \<in> {0..<\<^bold>l}\<^sub>u \<bullet> (P t) @\<^sub>u t))"

definition hDisInt :: "(real \<Rightarrow> 'c::t2_space upred) \<Rightarrow> ('d, 'c) relation_trd" where 
[urel_defs]: "hDisInt P = (hInt P \<and> $\<^bold>c =\<^sub>u \<phi>\<lparr>0\<rparr>\<^sub>u \<and> $\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(x \<rightarrow> \<^bold>l\<^sup>-)(\<phi>\<lparr>\<guillemotleft>x\<guillemotright>\<rparr>\<^sub>u) \<and> $\<^bold>d\<acute> =\<^sub>u $\<^bold>d)"

syntax
  "_time_var" :: "logic"
  "_hInt"     :: "logic \<Rightarrow> logic" ("\<lceil>_\<rceil>\<^sub>H")
  "_hDisInt"  :: "logic \<Rightarrow> logic" ("\<lceil>|_|\<rceil>\<^sub>H")

parse_translation {*
let
  fun time_var_tr [] = Syntax.free "\<tau>"
    | time_var_tr _  = raise Match;
in
[(@{syntax_const "_time_var"}, K time_var_tr)]
end
*}

translations
  "\<lceil>P\<rceil>\<^sub>H"   == "CONST hInt (\<lambda> _time_var. P)"
  "\<lceil>|P|\<rceil>\<^sub>H" == "CONST hDisInt (\<lambda> _time_var. P)"

definition hPreempt :: 
  "('d, 'c::topological_space) relation_trd \<Rightarrow> 'c upred \<Rightarrow> 
    ('d,'c) relation_trd \<Rightarrow> ('d,'c) relation_trd" ("_ \<lbrakk>_\<rbrakk>\<^sub>H _" [64,0,65] 64)
where "P \<lbrakk>B\<rbrakk>\<^sub>H Q = (((Q \<triangleleft> B @\<^sub>u 0 \<triangleright> (P \<and> \<lceil>\<not> B\<rceil>\<^sub>H)) \<or> ((\<lceil>\<not> B\<rceil>\<^sub>H \<and> P) ;; ((B @\<^sub>u 0) \<and> Q))))"

lemma uend_0 [simp]: "end\<^sub>u(0) = 0"
  by (simp add: upred_defs lit_def uop_def Abs_uexpr_inverse)

lemma R2c_time_range: "R2c (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<time'-time}\<^sub>u) = (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<time'-time}\<^sub>u)"
  by (rel_tac ; simp add: cgf_end_minus)

lemma R2c_time_length: "R2c (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u) = (\<guillemotleft>t\<guillemotright> \<in>\<^sub>u {0..<\<^bold>l}\<^sub>u)"
  by (rel_tac ; simp add: cgf_end_minus)

lemma R2c_tr_less_tr': "R2c($tr <\<^sub>u $tr\<acute>) = ($tr <\<^sub>u $tr\<acute>)"
  apply (rel_tac)
  using le_imp_less_or_eq apply fastforce
  using dual_order.strict_iff_order minus_zero_eq apply fastforce
done

lemma R2c_shAll: "R2c (\<^bold>\<forall> x \<bullet> P x) = (\<^bold>\<forall> x \<bullet> R2c(P x))"
  by (rel_tac)

lemma R2c_impl: "R2c(P \<Rightarrow> Q) = (R2c(P) \<Rightarrow> R2c(Q))"
  by (metis (no_types, lifting) R2c_and R2c_not double_negation impl_alt_def not_conj_deMorgans)

lemma R1_tr_less_tr': "R1($tr <\<^sub>u $tr\<acute>) = ($tr <\<^sub>u $tr\<acute>)"
  by (rel_tac)

lemma R1_hInt: "R1(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (simp add: hInt_def R1_extend_conj R1_tr_less_tr')

lemma R2s_hInt: "R2c(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (simp add: hInt_def R2c_and R2c_tr_less_tr' R2c_shAll R2c_impl R2c_time_length R2c_at)

lemma R2_hInt: "R2(\<lceil>P(\<tau>)\<rceil>\<^sub>H) = \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (metis R1_R2c_is_R2 R1_hInt R2s_hInt)

lemma hInt_false: "\<lceil>false\<rceil>\<^sub>H = false"
  apply (simp add: hInt_def, rel_tac)
by (metis cgf_end_0_iff cgf_end_ge_0 cgf_end_minus dual_order.strict_iff_order minus_zero_eq)


lemma seqr_to_conj: "\<lbrakk> out\<alpha> \<sharp> P; in\<alpha> \<sharp> Q \<rbrakk> \<Longrightarrow> (P ;; Q) = (P \<and> Q)"
  by (metis postcond_left_unit seqr_pre_out utp_pred.inf_top.right_neutral)

lemma unrest_lift_cont_subst [unrest]:
  "\<lbrakk> uvar x; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> (\<lceil>P\<rceil>\<^sub>C\<^sub><)\<lbrakk>v/$\<^bold>c\<rbrakk>"
  by (rel_tac)

lemma hInt_refine: "`\<^bold>\<forall> \<tau> \<bullet> P(\<tau>) \<Rightarrow> Q(\<tau>)` \<Longrightarrow> \<lceil>Q(\<tau>)\<rceil>\<^sub>H \<sqsubseteq> \<lceil>P(\<tau>)\<rceil>\<^sub>H"
  by (rel_tac)

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
    apply (rel_tac)
    apply (auto simp add: cgf_end_cat)
    apply (case_tac "xb < end\<^sub>C x")
    apply (auto simp add: cgf_cat_ext_first cgf_cat_ext_last)
    apply (metis add.right_neutral add_less_le_mono cgf_cat_ext_first cgf_end_ge_0)
    apply (smt cgf_apply_minus cgf_cat_minus cgf_end_ge_0 cgf_prefix_cat)
  done
  also have "... = (\<^bold>\<exists> tt \<bullet> ((\<guillemotleft>tt\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>(\<guillemotleft>tt\<guillemotright>)\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and> $tr\<acute> =\<^sub>u $tr + \<guillemotleft>tt\<guillemotright>)"
    apply (rel_tac)
    using add.assoc cgf_prefix_cat less_le_trans apply blast
    sorry (* Need to show that any non-zero length trajectory can be divided into two non-zero length parts *)
  also have "... = R2(\<lceil>P\<rceil>\<^sub>H)"
    by (simp add: R2_form hInt_def at_def usubst unrest)
  also have "... = \<lceil>P\<rceil>\<^sub>H"
    by (simp add: R2_hInt)
  finally show ?thesis .
qed

lemma hInt_true: "\<lceil>true\<rceil>\<^sub>H = ($tr <\<^sub>u $tr\<acute>)"
  by (rel_tac)

lemma "P \<lbrakk>true\<rbrakk>\<^sub>H Q = Q"
  by (simp add: hPreempt_def hInt_false)

lemma "P \<lbrakk>false\<rbrakk>\<^sub>H Q = (P \<and> $tr <\<^sub>u $tr\<acute>)"
  by (simp add: hPreempt_def hInt_true)

lemma hInt_conj: "\<lceil>P(\<tau>) \<and> Q(\<tau>)\<rceil>\<^sub>H = (\<lceil>P(\<tau>)\<rceil>\<^sub>H \<and> \<lceil>Q(\<tau>)\<rceil>\<^sub>H)"
  by (rel_tac)

type_synonym 'c ODE = "real \<times> 'c \<Rightarrow> 'c"

lift_definition hasDerivAt :: 
  "((real \<Rightarrow> 'c :: real_normed_vector), '\<alpha>) uexpr \<Rightarrow> ('c ODE, '\<alpha>) uexpr \<Rightarrow> real \<Rightarrow> '\<alpha> upred" ("_ has-deriv _ at _" [90, 0, 91] 90)
is "\<lambda> \<F> \<F>' \<tau> A. (\<F> A has_vector_derivative (\<F>' A (\<tau>, \<F> A \<tau>))) (at \<tau> within {0..})" .

end