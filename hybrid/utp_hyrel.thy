section {* Hybrid relational calculus *}

theory utp_hyrel
imports utp_fix_syntax_2
begin

adhoc_overloading uapply cgf_apply and uapply tt_apply
  
type_synonym ('d,'c) hybs = "('d \<times> 'c, 'c ttrace, unit) rsp"
type_synonym ('d,'c) hyrel  = "('d,'c) hybs hrel"
type_synonym ('a,'d,'c) hyexpr = "('a,('d,'c) hybs \<times> ('d,'c) hybs) uexpr"
  
syntax
  "_ulens_expr" :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("_:'(_')" [100,100] 100)

translations
  "_ulens_expr e x" == "CONST uop get\<^bsub>x\<^esub> e"                                                                                                                                                                 

abbreviation trace :: "('c::topological_space ttrace, 'd, 'c) hyexpr" ("\<phi>") where
"\<phi> \<equiv> $tr\<acute> - $tr"

abbreviation time_length :: "_" ("\<^bold>l")
where "\<^bold>l \<equiv> uop end\<^sub>t trace"

abbreviation cvar :: 
  "('a \<Longrightarrow> 'c::topological_space) \<Rightarrow> (real, 'd, 'c) hyexpr \<Rightarrow> ('a, 'd, 'c) hyexpr" 
  ("_~'(_')" [999,0] 999) 
where "x~(t) \<equiv> \<phi>\<lparr>t\<rparr>\<^sub>u:(x)"

translations
  "\<phi>" <= "CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))"
  "x~(t)" <= "CONST uop (CONST lens_get x) (CONST bop (CONST uapply) (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr))) t)"
  "\<^bold>l" <= "CONST uop end\<^sub>t (CONST minus (CONST utp_expr.var (CONST ovar CONST tr)) (CONST utp_expr.var (CONST ivar CONST tr)))"

definition disc_alpha :: "'d \<Longrightarrow> ('d, 'c::topological_space) hybs" ("\<^bold>d") where
[lens_defs]: "disc_alpha = fst\<^sub>L ;\<^sub>L st"

definition cont_alpha :: "'c \<Longrightarrow> ('d, 'c::topological_space) hybs" ("\<^bold>c") where
[lens_defs]: "cont_alpha = snd\<^sub>L ;\<^sub>L st"

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
   apply (simp_all add: disc_alpha_def cont_alpha_def)
   apply (rule lens_indep_sym)
   apply (auto intro: lens_indep_sym split_prod_lens_indep)
done

abbreviation disc_lift :: "('a, 'd \<times> 'd) uexpr \<Rightarrow> ('a, 'd, 'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>\<delta>") where
"\<lceil>P\<rceil>\<^sub>\<delta> \<equiv> P \<oplus>\<^sub>p (\<^bold>d \<times>\<^sub>L \<^bold>d)"

abbreviation cont_lift :: "('a, 'c \<times> 'c) uexpr \<Rightarrow> ('a, 'd, 'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C") where
"\<lceil>P\<rceil>\<^sub>C \<equiv> P \<oplus>\<^sub>p (\<^bold>c \<times>\<^sub>L \<^bold>c)"

abbreviation cont_pre_lift :: "('a, 'c) uexpr \<Rightarrow> ('a,'d,'c::topological_space) hyexpr" ("\<lceil>_\<rceil>\<^sub>C\<^sub><") where
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
  shows "utp_expr.var ((in_var x) ;\<^sub>L X \<times>\<^sub>L Y) = $X:(x)"
  by (pred_auto)

lemma var_out_var_prod [simp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "utp_expr.var ((out_var x) ;\<^sub>L X \<times>\<^sub>L Y) = $Y\<acute>:(x)"
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
  "time"  == "CONST uop end\<^sub>t (CONST utp_expr.var (CONST ivar CONST tr))"
  "time'" == "CONST uop end\<^sub>t (CONST utp_expr.var (CONST ovar CONST tr))"
  "end\<^sub>u(t)" == "CONST uop end\<^sub>t t"

(* Need to lift the continuous predicate to a relation *)

definition at :: "('a, 'c::topological_space) uexpr \<Rightarrow> real \<Rightarrow> ('a, 'd, 'c) hyexpr" (infix "@\<^sub>u" 60) where
[upred_defs]: "P @\<^sub>u t = [$\<^bold>c \<mapsto>\<^sub>s \<phi>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u] \<dagger> \<lceil>P\<rceil>\<^sub>C\<^sub><" 

lemma R2c_at: "R2c(P @\<^sub>u t) = P @\<^sub>u t"
  by (simp add: at_def R2c_def cond_idem usubst unrest R2s_def)

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
  shows "utp_expr.var x @\<^sub>u t = \<phi>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u:(x)"
  by (pred_auto)

definition hInt :: "(real \<Rightarrow> 'c::topological_space upred) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "hInt P = ($tr <\<^sub>u $tr\<acute> \<and> (\<^bold>\<forall> t \<in> {0..<\<^bold>l}\<^sub>u \<bullet> (P t) @\<^sub>u t))"

lemma hInt_unrest_ok [unrest]: "$ok \<sharp> hInt P" "$ok\<acute> \<sharp> hInt P"
  by (simp_all add: hInt_def unrest)

lemma hInt_unrest_wait [unrest]: "$wait \<sharp> hInt P" "$wait\<acute> \<sharp> hInt P"
  by (simp_all add: hInt_def unrest)

definition hDisInt :: "(real \<Rightarrow> 'c::t2_space upred) \<Rightarrow> ('d, 'c) hyrel" where 
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
  "\<lceil>P\<rceil>\<^sub>H"   == "CONST hInt (\<lambda> _time_var. P)"
  "\<^bold>\<lceil>P\<^bold>\<rceil>\<^sub>H" == "CONST hDisInt (\<lambda> _time_var. P)"

definition hPreempt :: 
  "('d, 'c::topological_space) hyrel \<Rightarrow> 'c upred \<Rightarrow> 
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" ("_ \<lbrakk>_\<rbrakk>\<^sub>H _" [64,0,65] 64)
where "P \<lbrakk>b\<rbrakk>\<^sub>H Q = (((Q \<triangleleft> b @\<^sub>u 0 \<triangleright> (P \<and> \<lceil>\<not> b\<rceil>\<^sub>H)) \<or> ((\<lceil>\<not> b\<rceil>\<^sub>H \<and> P) ;; ((b @\<^sub>u 0) \<and> Q))))"

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
  also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tt\<^sub>1\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>)) ;;
                                     (\<guillemotleft>tt\<^sub>2\<guillemotright> >\<^sub>u 0 \<and> (\<^bold>\<forall> t \<in> {0..<end\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)}\<^sub>u \<bullet> \<lceil>P\<rceil>\<^sub>C\<^sub><\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>\<lparr>\<guillemotleft>t\<guillemotright>\<rparr>\<^sub>u/$\<^bold>c\<rbrakk>))) \<and>
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
    
end
