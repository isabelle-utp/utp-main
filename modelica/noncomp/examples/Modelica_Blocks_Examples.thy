theory Modelica_Blocks_Examples
  imports "../Modelica_Blocks"
begin

alphabet 'l hst = "'l mst" +
  v1 :: real
  v2 :: real
  v3 :: real
  v4 :: real

setup_lifting type_definition_hst_ext

instantiation hst_ext :: (t2_space) t2_space
begin
  lift_definition open_hst_ext :: "('l, 'a) hst_scheme set \<Rightarrow> bool" is "open" .
  instance by (intro_classes, (transfer, auto simp add: separation_t2)+)
end    
    
lemma mo_block_ex1: "\<lbrakk>Constant 1 v1 \<oplus>\<^sub>m Constant 2 v2\<rbrakk>\<^sub>m = {&time,&v1,&v2} \<leftarrow>\<^sub>H (\<guillemotleft>ti\<guillemotright>, 1, 2)\<^sub>u"
  by (simp add: mo_defs srd_mu_equiv closure unrest gfp_const hrdPreempt_nz_false hrdPred_non_term rpred, rdes_simp, rel_auto)

lemma mo_block_ex2: "\<lbrakk>Constant 3 v1 \<oplus>\<^sub>m Add 1 1 time v1 v2\<rbrakk>\<^sub>m = {&time,&v1,&v2} \<leftarrow>\<^sub>H (\<guillemotleft>ti\<guillemotright>, 3, $v1\<acute>+\<guillemotleft>ti\<guillemotright>)\<^sub>u"
  by (simp add: mo_defs srd_mu_equiv closure unrest gfp_const hrdPreempt_nz_false hrdPred_non_term rpred, rdes_simp, rel_auto)
        
lemma mo_block_ex3: "\<lbrakk>Step 1 0 5 v1\<rbrakk>\<^sub>m = {&time,&v1} \<leftarrow>[5,5]\<^sub>H (\<guillemotleft>ti\<guillemotright>, 0)\<^sub>u ;; {&time,&v1} \<leftarrow>[5,5]\<^sub>H (\<guillemotleft>ti\<guillemotright>+5, 1)\<^sub>u"
proof -
  have "\<lbrakk>Step 1 0 5 v1\<rbrakk>\<^sub>m =
        \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> false \<diamondop> [&time =\<^sub>u 0 \<and> &v1 =\<^sub>u 0]\<^sub>C\<^sub>>) ;;
        (\<mu> X \<bullet> \<^bold>d :=\<^sub>R &\<^bold>c ;;
               ({&time, &v1} \<leftarrow>\<^sub>H ($time + \<guillemotleft>ti\<guillemotright>, $v1)\<^sub>u inv true until\<^sub>H \<guillemotleft>\<lambda>ti. ti = 5\<guillemotright>($time\<acute>)\<^sub>a ;; 
                (\<^bold>c:v1 :=\<^sub>R \<guillemotleft>1\<guillemotright> \<triangleleft> \<guillemotleft>\<lambda>ti. ti = 5\<guillemotright>(&\<^bold>c:time)\<^sub>a \<triangleright>\<^sub>R II\<^sub>R)) ;;
                SRD X)"
    by (simp add: mo_defs closure unrest rpred srd_mu_equiv gfp_const seqr_assoc SRD_left_unit 
        NSRD_right_unit hrdPreempt_nz_def hrdPred_hEvolve zero_uexpr_def)
  oops
        
lemma subst_hEvolve_dis [usubst]: "\<lceil>\<sigma>(\<^bold>d \<mapsto>\<^sub>s &\<^bold>c)\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> x \<leftarrow>\<^sub>h f(ti) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> x \<leftarrow>\<^sub>h f(ti)"
  by (rel_auto)
  
lemma subst_der_dis [usubst]: "\<lceil>\<sigma>(\<^bold>d \<mapsto>\<^sub>s &\<^bold>c)\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> (x has-der v) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> (x has-der v)"
  by (rel_auto)
        
lemma mo_block_ex4: 
  "\<lbrakk>Constant 1 v1 \<oplus>\<^sub>m Integrator InitialState 1 2 v1 v2\<rbrakk>\<^sub>m = {&time,&v1,&v2} \<leftarrow>\<^sub>H (\<guillemotleft>ti\<guillemotright>, 1, 2*\<guillemotleft>ti\<guillemotright>)\<^sub>u"
  apply (simp add: mo_defs srd_mu_equiv closure unrest gfp_const hrdPreempt_nz_false hrdPred_non_term rpred)
  apply (simp add: lit_num_simps true_alt_def[THEN sym] false_alt_def[THEN sym])
  apply (rdes_simp)
  apply (rule srdes_tri_eq_intro)
    apply (simp_all)
oops
  
end