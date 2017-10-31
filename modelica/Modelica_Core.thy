section {* Modelica Core *}

theory Modelica_Core
imports "../hybrid/utp_hrd"
begin
  
named_theorems mo_defs
  
alphabet 'l mst =
  mtime   :: real
  mintern :: "'l" -- {* Internal continuous variables *}
  
setup_lifting type_definition_mst_ext

text {* Syntax for internal variables *}
  
notation mintern ("\<^bold>i")
  
syntax
  "_svid_mintern"  :: "svid" ("\<^bold>i")
  
translations
  "_svid_mintern" => "CONST mintern"
  
instantiation mst_ext :: (t2_space,t2_space) t2_space
begin
  lift_definition open_mst_ext :: "('a, 'b) mst_scheme set \<Rightarrow> bool" is "open" .
  instance by (intro_classes, (transfer, auto simp add: separation_t2)+)
end
  
definition map_mst ::
  "('\<sigma> \<Rightarrow> '\<tau>) \<Rightarrow>
   ('\<sigma>, 'c) mst_scheme \<Rightarrow> ('\<tau>, 'c) mst_scheme" where
[lens_defs]: "map_mst f = (\<lambda>r. \<lparr>mtime\<^sub>v = mtime\<^sub>v r, mintern\<^sub>v = f (mintern\<^sub>v r), \<dots> = more r\<rparr>)"

definition map_mst_lens ::
  "('\<sigma> \<Longrightarrow> '\<tau>) \<Rightarrow> 
   (('\<sigma>, 'b) mst_scheme, 't::trace, 'c) rsp \<Longrightarrow> (('\<tau>, 'b) mst_scheme, 't, 'c) rsp" ("map'_mst\<^sub>L") where
[lens_defs]:
"map_mst_lens l = map_st\<^sub>L \<lparr>
  lens_get = map_mst (get\<^bsub>l\<^esub>),
  lens_put = map_mst o (put\<^bsub>l\<^esub>) o mintern\<^sub>v\<rparr>"


lemma map_mst_vwb [simp]: "vwb_lens X \<Longrightarrow> vwb_lens (map_mst\<^sub>L X)"
  apply (unfold_locales, simp_all add: lens_defs des_vars.defs rp_vars.defs rsp_vars.defs)
  apply (metis des_vars.surjective mst.surjective rp_vars.surjective rsp_vars.surjective)+
done

abbreviation "abs_mst\<^sub>L \<equiv> (map_mst\<^sub>L 0\<^sub>L) \<times>\<^sub>L (map_mst\<^sub>L 0\<^sub>L)"

type_synonym ('l, 'c) mrel = "(('l, 'c) mst_ext, ('l, 'c) mst_ext) hyrel"
type_synonym ('d, 'l, 'c) mpred = "('d, ('l, 'c) mst_ext) hybs upred"
type_synonym ('a, 'l, 'c) mexpr = "('a, ('l, 'c) mst_ext) uexpr"  
  
translations
  (type) "('l,'c) mrel" <= (type) "(('l, 'c) mst_scheme, ('l', 'c') mst_scheme) hyrel"
  (type) "('d,'l,'c) mpred" <= (type) "('d, ('l, 'c) mst_scheme) hybs upred"
  (type) "('a,'l,'c) mexpr" <= (type) "('a, ('l, 'c) mst_scheme) uexpr"
  
text {* Preconditions are captured by negating the continuous divergences, that is the set of
  trajectories that eventually violate the precondition. Every divergence can be extended
  aribtrarily. The precondition effectively states that no trace must violate the precondition
  at the limit. *}
  
definition ModelicaPre ("\<lceil>_\<rceil>\<^sub>M") where
[upred_defs]: "\<lceil>P\<rceil>\<^sub>M = (\<not>\<^sub>r (\<lceil>\<not> P\<rceil>\<^sup>\<rightarrow> ;; true\<^sub>r))"
  
lemma true_ModelicaPre [rpred]: "\<lceil>true\<rceil>\<^sub>M = true\<^sub>r"
  by (rel_auto)

lemma ModelicaPre_RC [closure]: "\<lceil>P\<rceil>\<^sub>M is RC"
  apply (rel_auto)
  apply (meson less_iff minus_gr_zero_iff order_refl)
  apply (metis (no_types, lifting) diff_add_cancel_left' minus_gr_zero_iff order.trans trace_class.add_diff_cancel_left trace_class.add_left_mono)
done

definition ModelicaBlock ("[_ | _]\<^sub>M") where
"[P | Q]\<^sub>M = \<^bold>R\<^sub>s(\<lceil>P\<rceil>\<^sub>M \<turnstile> Q \<diamondop> false)"

lemma preR_simple_block [rdes]: "pre\<^sub>R([P\<^sub>1 | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M) = \<lceil>P\<^sub>1\<rceil>\<^sub>M"
  by (simp add: ModelicaBlock_def preR_rdes closure)

lemma periR_simple_block [rdes]: "peri\<^sub>R([P\<^sub>1 | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M) = (\<lceil>P\<^sub>1\<rceil>\<^sub>M \<Rightarrow>\<^sub>r \<lceil>Q\<^sub>1\<rceil>\<^sub>h)"
  by (simp add: ModelicaBlock_def rdes closure)
  
lemma postR_simple_block [rdes]: "post\<^sub>R([P | \<lceil>Q\<rceil>\<^sub>h]\<^sub>M) = (\<not>\<^sub>r \<lceil>P\<rceil>\<^sub>M)"
  by (simp add: ModelicaBlock_def rdes closure)
    
lemma NSRD_simple_block [closure]: "[P\<^sub>1 | \<lceil>Q\<^sub>1\<rceil>\<^sub>h]\<^sub>M is NSRD"
  apply (rule NSRD_intro)
  apply (simp add: ModelicaBlock_def)
  apply (rule RHS_tri_design_is_SRD)
  apply (simp_all add: unrest rdes closure neg_hInt_R1_true)
  apply (metis (no_types, lifting) ModelicaPre_RC R1_seqr_closure rea_not_R1 rea_not_false rea_not_not wpR_RC_false wpR_def)
done
    
end
