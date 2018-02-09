section \<open> Reactive Programs \<close>

theory utp_rea_prog
  imports utp_rea_cond
begin

subsection \<open> Stateful reactive alphabet \<close>

text \<open> @{term R3} as presented in the UTP book and related publications is not sensitive to state, 
  although reactive programs often need this property. Thus is is necessary to use a modification 
  of @{term R3} from Butterfield et al.~\cite{BGW09} that explicitly states that intermediate
  waiting states do not propogate final state variables. In order to do this we need an additional
  observational variable that capture the program state that we call $st$. Upon this foundation,
  we can define operators for reactive programs. \<close>

alphabet 's rsp_vars = "'t rp_vars" +
  st :: 's

type_synonym ('s,'t,'\<alpha>) rsp = "('t, ('s, '\<alpha>) rsp_vars_scheme) rp"
type_synonym ('s,'t,'\<alpha>,'\<beta>) rel_rsp  = "(('s,'t,'\<alpha>) rsp, ('s,'t,'\<beta>) rsp) urel"
type_synonym ('s,'t,'\<alpha>) hrel_rsp  = "('s,'t,'\<alpha>) rsp hrel"
type_synonym ('s,'t) rdes = "('s,'t,unit) hrel_rsp"
  
translations
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "('t, ('s, '\<alpha>) rsp_vars_ext) rp"
  (type) "('s,'t,'\<alpha>) rsp" <= (type) "('t, ('s, '\<alpha>) rsp_vars_scheme) rp"
  (type) "('s,'t,unit) rsp" <= (type) "('t, 's rsp_vars) rp"
  (type) "('s,'t,'\<alpha>,'\<beta>) rel_rsp" <= (type) "(('s,'t,'\<alpha>) rsp, ('s1,'t1,'\<beta>) rsp) urel"
  (type) "('s,'t,'\<alpha>) hrel_rsp"  <= (type) "('s, 't, '\<alpha>) rsp hrel"
  (type) "('s,'t) rdes" <= (type) "('s, 't, unit) hrel_rsp"
  
notation rsp_vars_child_lens\<^sub>a ("\<Sigma>\<^sub>s")
notation rsp_vars_child_lens ("\<Sigma>\<^sub>S")

abbreviation lift_state_rel ("\<lceil>_\<rceil>\<^sub>S")
where "\<lceil>P\<rceil>\<^sub>S \<equiv> P \<oplus>\<^sub>p (st \<times>\<^sub>L st)"

abbreviation drop_state_rel ("\<lfloor>_\<rfloor>\<^sub>S")
where "\<lfloor>P\<rfloor>\<^sub>S \<equiv> P \<restriction>\<^sub>e (st \<times>\<^sub>L st)"

abbreviation lift_state_pre ("\<lceil>_\<rceil>\<^sub>S\<^sub><")
where "\<lceil>p\<rceil>\<^sub>S\<^sub>< \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub><\<rceil>\<^sub>S"

abbreviation drop_state_pre ("\<lfloor>_\<rfloor>\<^sub>S\<^sub><")
where "\<lfloor>p\<rfloor>\<^sub>S\<^sub>< \<equiv> \<lfloor>\<lfloor>p\<rfloor>\<^sub>S\<rfloor>\<^sub><"

abbreviation lift_state_post ("\<lceil>_\<rceil>\<^sub>S\<^sub>>")
where "\<lceil>p\<rceil>\<^sub>S\<^sub>> \<equiv> \<lceil>\<lceil>p\<rceil>\<^sub>>\<rceil>\<^sub>S"

abbreviation drop_state_post ("\<lfloor>_\<rfloor>\<^sub>S\<^sub>>")
where "\<lfloor>p\<rfloor>\<^sub>S\<^sub>> \<equiv> \<lfloor>\<lfloor>p\<rfloor>\<^sub>S\<rfloor>\<^sub>>"

text \<open> Lifting substitutions on the reactive state \<close>

definition usubst_st_lift :: 
  "'s usubst \<Rightarrow> (('s,'t::trace,'\<alpha>) rsp \<times> ('s,'t,'\<beta>) rsp) usubst"  ("\<lceil>_\<rceil>\<^sub>S\<^sub>\<sigma>") where
[upred_defs]: "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> = \<lceil>\<sigma> \<oplus>\<^sub>s st\<rceil>\<^sub>s"

abbreviation st_subst :: "'s usubst \<Rightarrow> ('s,'t::trace,'\<alpha>) hrel_rsp \<Rightarrow> ('s, 't, '\<alpha>) hrel_rsp" (infixr "\<dagger>\<^sub>S" 80) where
"\<sigma> \<dagger>\<^sub>S P \<equiv> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"

translations
  "\<sigma> \<dagger>\<^sub>S P" <= "\<lceil>\<sigma> \<oplus>\<^sub>s st\<rceil>\<^sub>s \<dagger> P"
  "\<sigma> \<dagger>\<^sub>S P" <= "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"
  
syntax
  "_svid_st_alpha"  :: "svid" ("\<Sigma>\<^sub>S")

translations
  "_svid_st_alpha" => "CONST rsp_vars_child_lens"

interpretation alphabet_state:
  lens_interp "\<lambda>(ok, wait, tr, r). (ok, wait, tr, st\<^sub>v r, more r)"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

interpretation alphabet_state_rel: lens_interp "\<lambda>(ok, ok', wait, wait', tr, tr', r, r').
  (ok, ok', wait, wait', tr, tr', st\<^sub>v r, st\<^sub>v r', more r, more r')"
apply (unfold_locales)
apply (rule injI)
apply (clarsimp)
done

lemma st'_unrest_st_lift_pred [unrest]:
  "$st\<acute> \<sharp> \<lceil>a\<rceil>\<^sub>S\<^sub><"
  by (pred_auto)

lemma out_alpha_unrest_st_lift_pre [unrest]:
  "out\<alpha> \<sharp> \<lceil>a\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)

lemma R1_st'_unrest [unrest]: "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> R1(P)"
  by (simp add: R1_def unrest)

lemma R2c_st'_unrest [unrest]: "$st\<acute> \<sharp> P \<Longrightarrow> $st\<acute> \<sharp> R2c(P)"
  by (simp add: R2c_def unrest)

lemma st_lift_lemma:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> = \<sigma> \<oplus>\<^sub>s (fst\<^sub>L ;\<^sub>L (st \<times>\<^sub>L st))"
  by (auto simp add: upred_defs lens_defs prod.case_eq_if)
    
lemma unrest_st_lift [unrest]:
  fixes x :: "'a \<Longrightarrow> ('s, 't::trace, '\<alpha>) rsp \<times> ('s, 't, '\<alpha>) rsp"
  assumes "x \<bowtie> ($st)\<^sub>v"
  shows "x \<sharp> \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma>" (is "?P")
  by (simp add: st_lift_lemma)
     (metis assms in_var_def in_var_prod_lens lens_comp_left_id st_vwb_lens unrest_subst_alpha_ext vwb_lens_wb)
  
lemma st_lift_R1_true_right: "\<lceil>b\<rceil>\<^sub>S\<^sub>< ;; R1(true) = \<lceil>b\<rceil>\<^sub>S\<^sub><"
  by (rel_auto)
    
lemma st_bij_lemma: "bij_lens (st\<^sub>a +\<^sub>L \<Sigma>\<^sub>s)"
  by (unfold_locales, auto simp add: lens_defs)

lemma rea_lens_equiv_st_rest: "\<Sigma>\<^sub>R \<approx>\<^sub>L st +\<^sub>L \<Sigma>\<^sub>S"
proof -
  have "st +\<^sub>L \<Sigma>\<^sub>S = (st\<^sub>a +\<^sub>L \<Sigma>\<^sub>s) ;\<^sub>L \<Sigma>\<^sub>R"
    by (simp add: plus_lens_distr st_def rsp_vars_child_lens_def)
  also have "... \<approx>\<^sub>L 1\<^sub>L ;\<^sub>L \<Sigma>\<^sub>R"
    using lens_equiv_via_bij st_bij_lemma by auto
  also have "... = \<Sigma>\<^sub>R"
    by (simp)
  finally show ?thesis
    using lens_equiv_sym by blast
qed

lemma srea_lens_bij: "bij_lens (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L \<Sigma>\<^sub>S)"
proof -
  have "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L st +\<^sub>L \<Sigma>\<^sub>S \<approx>\<^sub>L ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<Sigma>\<^sub>R"
    by (auto intro!:lens_plus_cong, rule lens_equiv_sym, simp add: rea_lens_equiv_st_rest)
  also have "... \<approx>\<^sub>L 1\<^sub>L"
    using bij_lens_equiv_id[of "ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L \<Sigma>\<^sub>R"] by (simp add: rea_lens_bij)
  finally show ?thesis
    by (simp add: bij_lens_equiv_id)
qed

lemma st_qual_alpha [alpha]: "x ;\<^sub>L fst\<^sub>L ;\<^sub>L st \<times>\<^sub>L st = ($st:x)\<^sub>v"
  by (metis (no_types, hide_lams) in_var_def in_var_prod_lens lens_comp_assoc st_vwb_lens vwb_lens_wb)
  
text {* Reactive state assignment *}
    
definition rea_assigns :: "('s \<Rightarrow> 's) \<Rightarrow> ('s, 't::trace, '\<alpha>) hrel_rsp" ("\<langle>_\<rangle>\<^sub>r") where
[upred_defs]: "\<langle>\<sigma>\<rangle>\<^sub>r = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S \<and> $\<Sigma>\<^sub>S\<acute> =\<^sub>u $\<Sigma>\<^sub>S)"

syntax
  "_assign_rea" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  ("'(_') :=\<^sub>r '(_')")  
  "_assign_rea" :: "svids \<Rightarrow> uexprs \<Rightarrow> logic"  (infixr ":=\<^sub>r" 90)

translations
  "_assign_rea xs vs" => "CONST rea_assigns (_mk_usubst (CONST id) xs vs)"
  "_assign_rea x v" <= "CONST rea_assigns (CONST subst_upd (CONST id) x v)"
  "_assign_rea x v" <= "_assign_rea (_spvar x) v"
  "x,y :=\<^sub>r u,v" <= "CONST rea_assigns (CONST subst_upd (CONST subst_upd (CONST id) (CONST svar x) u) (CONST svar y) v)"
  
lemma rea_assigns_RR_closed [closure]: 
  "\<langle>\<sigma>\<rangle>\<^sub>r is RR"
  apply (rel_auto) using minus_zero_eq by auto
    
lemma id_st_subst [usubst]: 
  "\<lceil>id\<rceil>\<^sub>S\<^sub>\<sigma> = id"
  by (pred_auto)
    
lemma st_subst_comp [usubst]:
  "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<circ> \<lceil>\<rho>\<rceil>\<^sub>S\<^sub>\<sigma> = \<lceil>\<sigma> \<circ> \<rho>\<rceil>\<^sub>S\<^sub>\<sigma>"
  by (rel_auto)
    
lemma st_subst_assigns_rea [usubst]:
  "\<sigma> \<dagger>\<^sub>S \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
    
lemma st_subst_rea_skip [usubst]:
  "\<sigma> \<dagger>\<^sub>S II\<^sub>r = \<langle>\<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
    
lemma rea_assigns_comp [rpred]:
  assumes "P is RR"
  shows "\<langle>\<sigma>\<rangle>\<^sub>r ;; P = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> P"
proof -
  have "\<langle>\<sigma>\<rangle>\<^sub>r ;; (RR P) = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> (RR P)"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_def assms)
qed
  
lemma st_subst_RR [closure]:
  assumes "P is RR"
  shows "(\<sigma> \<dagger>\<^sub>S P) is RR"
proof -
  have "(\<sigma> \<dagger>\<^sub>S RR(P)) is RR"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
  
text {* We guard the reactive conditional condition so that it can't be simplified by alphabet
  laws unless explicitly simplified. *}

definition lift_cond_srea ("\<lceil>_\<rceil>\<^sub>S\<^sub>\<leftarrow>") where
[upred_defs]: "\<lceil>b\<rceil>\<^sub>S\<^sub>\<leftarrow> = \<lceil>b\<rceil>\<^sub>S\<^sub><"

lemma unrest_lift_cond_srea [unrest]:
  "x \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub>< \<Longrightarrow> x \<sharp> \<lceil>b\<rceil>\<^sub>S\<^sub>\<leftarrow>"
  by (simp add: lift_cond_srea_def)

lemma subst_lift_cond_srea [usubst]: "\<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> \<lceil>s\<rceil>\<^sub>S\<^sub>\<leftarrow> = \<lceil>\<sigma> \<dagger> s\<rceil>\<^sub>S\<^sub>\<leftarrow>"
  by (rel_auto)
    
abbreviation cond_srea ::
  "('s,'t::trace,'\<alpha>,'\<beta>) rel_rsp \<Rightarrow>
  's upred \<Rightarrow>
  ('s,'t,'\<alpha>,'\<beta>) rel_rsp \<Rightarrow>
  ('s,'t,'\<alpha>,'\<beta>) rel_rsp" ("(3_ \<triangleleft> _ \<triangleright>\<^sub>R/ _)" [52,0,53] 52) where
"cond_srea P b Q \<equiv> P \<triangleleft> \<lceil>b\<rceil>\<^sub>S\<^sub>\<leftarrow> \<triangleright> Q"

text {* We introduce state abstraction by creating some lens functors that allow us to lift
  a lens on the state-space to one on the whole stateful reactive alphabet. *}

definition lmap\<^sub>R :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('t::trace, 'a) rp \<Longrightarrow> ('t, 'b) rp" where
[lens_defs]: "lmap\<^sub>R = lmap\<^sub>D \<circ> lmap[rp_vars]"

definition map_rsp_st ::
  "('\<sigma> \<Rightarrow> '\<tau>) \<Rightarrow>
   ('\<sigma>, '\<alpha>) rsp_vars_scheme \<Rightarrow> ('\<tau>, '\<alpha>) rsp_vars_scheme" where
[lens_defs]: "map_rsp_st f = (\<lambda>r. \<lparr>st\<^sub>v = f (st\<^sub>v r), \<dots> = rsp_vars.more r\<rparr>)"

definition map_st_lens ::
  "('\<sigma> \<Longrightarrow> '\<psi>) \<Rightarrow>
   (('\<sigma>, '\<tau>::trace, '\<alpha>) rsp \<Longrightarrow> ('\<psi>, '\<tau>::trace, '\<alpha>) rsp)" ("map'_st\<^sub>L") where
[lens_defs]:
"map_st_lens l = lmap\<^sub>R \<lparr>
  lens_get = map_rsp_st (get\<^bsub>l\<^esub>),
  lens_put = map_rsp_st o (put\<^bsub>l\<^esub>) o rsp_vars.st\<^sub>v\<rparr>"

lemma map_set_vwb [simp]: "vwb_lens X \<Longrightarrow> vwb_lens (map_st\<^sub>L X)"
  apply (unfold_locales, simp_all add: lens_defs des_vars.defs rp_vars.defs rsp_vars.defs)
  apply (metis des_vars.surjective rp_vars.surjective rsp_vars.surjective)+
done

abbreviation "abs_st\<^sub>L \<equiv> (map_st\<^sub>L 0\<^sub>L) \<times>\<^sub>L (map_st\<^sub>L 0\<^sub>L)"
  
abbreviation abs_st ("\<langle>_\<rangle>\<^sub>S") where
"abs_st P \<equiv> P \<restriction>\<^sub>e abs_st\<^sub>L"
  
text {* Reactive Frames and Extensions *}
  
definition rea_frame :: "('a \<Longrightarrow> '\<alpha>) \<Rightarrow> ('\<alpha>, 't::trace) rdes \<Rightarrow> ('\<alpha>, 't) rdes" where
[upred_defs]: "rea_frame x P = frame (ok +\<^sub>L wait +\<^sub>L tr +\<^sub>L (x ;\<^sub>L st)) P"

definition rea_frame_ext :: "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha>, 't::trace) rdes \<Rightarrow> ('\<beta>, 't) rdes" where
[upred_defs]: "rea_frame_ext a P = rea_frame a (rel_aext P (map_st\<^sub>L a))"

syntax
  "_rea_frame"     :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>r" [99,0] 100)
  "_rea_frame_ext" :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_:[_]\<^sub>r\<^sup>+" [99,0] 100)

translations
  "_rea_frame x P" => "CONST rea_frame x P"
  "_rea_frame (_salphaset (_salphamk x)) P" <= "CONST rea_frame x P"
  "_rea_frame_ext x P" => "CONST rea_frame_ext x P"
  "_rea_frame_ext (_salphaset (_salphamk x)) P" <= "CONST rea_frame_ext x P"

lemma rea_frame_RR_closed [closure]: 
  assumes "P is RR"
  shows "x:[P]\<^sub>r is RR"
proof -
  have "RR(x:[RR P]\<^sub>r) = x:[RR P]\<^sub>r"
    by (rel_auto)
  thus ?thesis
    by (metis Healthy_if Healthy_intro assms)
qed
  
lemma rea_aext_RR [closure]:
  assumes "P is RR"
  shows "rel_aext P (map_st\<^sub>L x) is RR"
proof -
  have "rel_aext (RR P) (map_st\<^sub>L x) is RR"
    by (rel_auto)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
  
lemma rea_frame_ext_RR_closed [closure]:
  "P is RR \<Longrightarrow> x:[P]\<^sub>r\<^sup>+ is RR"
  by (simp add: rea_frame_ext_def closure)
  
lemma rel_aext_st_Instant_closed [closure]:
  "P is Instant \<Longrightarrow> rel_aext P (map_st\<^sub>L x) is Instant"
  by (rel_auto)

(*
lemma rea_frame_commute:
  assumes "P is RR" "Q is RR" "vwb_lens x" "vwb_lens y"
          "$st:y \<sharp> P" "$st:x \<sharp> Q" "$st:y\<acute> \<sharp> P" "$st:x\<acute> \<sharp> Q" 
          "P is Instant" "Q is Instant" "x \<bowtie> y"
  shows "x:[P]\<^sub>r ;; y:[Q]\<^sub>r = y:[Q]\<^sub>r ;; x:[P]\<^sub>r"     
proof -
  have "x:[P]\<^sub>r ;; y:[Q]\<^sub>r = {&tr,&ok,&wait,&st:x}:[P] ;; {&tr,&ok,&wait,&st:y}:[Q]"
    by (rel_auto)
  also have "... = {&ok,&wait,&st:x}:[P] ;; {&ok,&wait,&st:y}:[Q]"
    by (simp add: frame_contract_RID closure assms)
  also have "... = {&ok,&wait,&st:x}:[RR(P)] ;; {&ok,&wait,&st:y}:[RR(Q)]"
    by (simp add: assms Healthy_if)
  also have "... = {&ok,&wait,&st:x}:[RR(P)] ;; {&ok,&wait,&st:y}:[RR(Q)]"
    by (simp add: assms Healthy_if)    
  also have "... = {&ok,&wait,&st:y}:[RR(Q)] ;; {&ok,&wait,&st:x}:[RR(P)]"
    using assms(3-8,11) apply (rel_auto)

  also have "... = {&ok,&wait,&st:y}:[RR(Q)] ;; {&ok,&wait,&st:x}:[RR(P)]"      
    using assms(3-8,11)
    apply (rel_auto)
    
  also have "... = {&ok,&wait,&st:y}:[Q] ;; {&ok,&wait,&st:x}:[P]"      
    by (simp add: assms Healthy_if)
  also have "... = {&tr,&ok,&wait,&st:y}:[Q] ;; {&tr,&ok,&wait,&st:x}:[P]"
    by (simp add: frame_contract_RID closure assms)
  also have "... = y:[Q]\<^sub>r ;; x:[P]\<^sub>r"
    by (rel_auto)
  finally show ?thesis .
qed
  
lemma rea_frame_ext_commute:
  assumes "P is RR" "Q is RR" "vwb_lens x" "vwb_lens y"
          "P is Instant" "Q is Instant" "x \<bowtie> y"
  shows "x:[P]\<^sub>r\<^sup>+ ;; y:[Q]\<^sub>r\<^sup>+ = y:[Q]\<^sub>r\<^sup>+ ;; x:[P]\<^sub>r\<^sup>+"
  apply (simp add: rea_frame_ext_def)
  apply (rule rea_frame_commute)
  apply (simp_all add: closure assms)
  apply (rel_auto, simp_all add: assms)
  apply (rel_auto, simp_all add: assms lens_indep_sym)
done
*)    
  
lemma rea_frame_ext_false [frame]:
  "x:[false]\<^sub>r\<^sup>+ = false"
  by (rel_auto)
  
lemma rea_frame_ext_skip [frame]:
  "vwb_lens x \<Longrightarrow> x:[II\<^sub>r]\<^sub>r\<^sup>+ = II\<^sub>r"
  by (rel_auto)

lemma rea_frame_ext_assigns [frame]:
  "vwb_lens x \<Longrightarrow> x:[\<langle>\<sigma>\<rangle>\<^sub>r]\<^sub>r\<^sup>+ = \<langle>\<sigma> \<oplus>\<^sub>s x\<rangle>\<^sub>r"
  by (rel_auto)

lemma rea_frame_ext_cond [frame]:
  "x:[P \<triangleleft> b \<triangleright>\<^sub>R Q]\<^sub>r\<^sup>+ = x:[P]\<^sub>r\<^sup>+ \<triangleleft> (b \<oplus>\<^sub>p x) \<triangleright>\<^sub>R x:[Q]\<^sub>r\<^sup>+"
  by (rel_auto)
    
lemma rea_frame_ext_seq [frame]:
  "vwb_lens x \<Longrightarrow> x:[P ;; Q]\<^sub>r\<^sup>+ = x:[P]\<^sub>r\<^sup>+ ;; x:[Q]\<^sub>r\<^sup>+"
  apply (simp add: rea_frame_ext_def rea_frame_def alpha frame)
  apply (subst frame_seq)
  apply (simp_all add: plus_vwb_lens closure)
  apply (rel_auto)+
done
    
lemma rea_assigns_st_subst [usubst]:
  "\<lceil>\<sigma> \<oplus>\<^sub>s st\<rceil>\<^sub>s \<dagger> \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<rho> \<circ> \<sigma>\<rangle>\<^sub>r"
  by (rel_auto)
    
lemma st_cond_assigns [rpred]:
  "\<langle>\<sigma>\<rangle>\<^sub>r \<triangleleft> b \<triangleright>\<^sub>R \<langle>\<rho>\<rangle>\<^sub>r = \<langle>\<sigma> \<triangleleft> b \<triangleright>\<^sub>s \<rho>\<rangle>\<^sub>r"
  by (rel_auto)
    
lemma rea_frame_ext_subst_indep [usubst]:
  assumes "x \<bowtie> y" "\<Sigma> \<sharp> v" "P is RR"
  shows "\<sigma>(y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+) ;; y :=\<^sub>r v"
proof -
  from assms(1-2) have "\<sigma>(y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+) ;; y :=\<^sub>r v"
    by (rel_auto, (metis (no_types, lifting) lens_indep.lens_put_comm lens_indep_get)+)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma rea_frame_ext_subst_within [usubst]:
  assumes "vwb_lens x" "vwb_lens y" "\<Sigma> \<sharp> v" "P is RR"
  shows "\<sigma>(x:y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[y :=\<^sub>r (v \<restriction>\<^sub>e x) ;; P]\<^sub>r\<^sup>+)"
proof -
  from assms(1,3) have "\<sigma>(x:y \<mapsto>\<^sub>s v) \<dagger>\<^sub>S x:[RR P]\<^sub>r\<^sup>+ = (\<sigma> \<dagger>\<^sub>S x:[y :=\<^sub>r (v \<restriction>\<^sub>e x) ;; RR(P)]\<^sub>r\<^sup>+)"
    by (rel_auto, metis+)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed
    
lemma st_subst_lift_cond [usubst]:
  "\<sigma> \<dagger>\<^sub>S \<lceil>P\<rceil>\<^sub>S\<^sub>\<leftarrow> = \<lceil>\<sigma> \<dagger> P\<rceil>\<^sub>S\<^sub>\<leftarrow>"
  by (rel_auto)

end