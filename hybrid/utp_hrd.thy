section {* Hybrid Reactive Designs *}

theory utp_hrd
  imports
    utp_rea_designs
    utp_differential
begin
  
subsection {* Constructs *}
  
text {* Lift an arbitrary hybrid relation to the peri condition of a reactive design. Usually used
  to specify constraints on continuous variables. *}
  
definition hrdPred :: "('d,'c::topological_space) hyrel \<Rightarrow> ('d,'c) hyrel" ("[_]\<^sub>H") where
[upred_defs, rdes_def]: "hrdPred P = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> P \<diamondop> false)"
  
definition hrdEvolve :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real \<Rightarrow> ('a, 'c) hexpr) \<Rightarrow> ('d,'c) hyrel" where
[upred_defs, rdes_def]: "hrdEvolve x f = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> x \<leftarrow>\<^sub>h f(ti) \<diamondop> false)"

definition hrdEvolveBounds :: 
  "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> 
   (real, 'd \<times> 'c) uexpr \<Rightarrow> 
   (real, 'd \<times> 'c) uexpr \<Rightarrow>
   (real \<Rightarrow> ('a, 'c) hexpr) \<Rightarrow> 
   ('d,'c) hyrel" where
[upred_defs, rdes_def]: "hrdEvolveBounds x l u f = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> (x \<leftarrow>\<^sub>h\<le>(u) f(ti)) \<diamondop> ((x \<leftarrow>[l,u]\<^sub>h f(ti)) \<triangleleft> u >\<^sub>u 0 \<triangleright>\<^sub>R II\<^sub>r))"

text {* Evolve according to a continuous function for a definite time length. Currently this
  duplicates the state where t = l as the pre-emption operator does as well. *}
  
abbreviation hrdEvolveTil :: "('a::t2_space \<Longrightarrow> 'c::t2_space) \<Rightarrow> (real, 'd \<times> 'c) uexpr \<Rightarrow> (real \<Rightarrow> ('a, 'c) hexpr) \<Rightarrow> ('d,'c) hyrel" where
"hrdEvolveTil x t f \<equiv> hrdEvolveBounds x t t f"

definition hrdUntil :: "('d, 'c::t2_space) hyrel \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow> ('d,'c) hyrel"
  where [upred_defs]: 
"hrdUntil P b c = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (peri\<^sub>R(P) \<and> \<lceil>b(ti)\<rceil>\<^sub>h) \<diamondop> (post\<^sub>R(P) \<or> hUntil (peri\<^sub>R(P)) b c))"

definition hrdPreempt_nz ::
    "('d, 'c::t2_space) hyrel \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hrdPreempt_nz P b c Q = (hrdUntil P b c) ;; Q"

definition hrdPreempt ::
    "('d, 'c::t2_space) hyrel \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow> (real \<Rightarrow> 'c hrel) \<Rightarrow>
    ('d,'c) hyrel \<Rightarrow> ('d,'c) hyrel" where
[upred_defs]: "hrdPreempt P b c Q = (Q \<triangleleft> (\<^bold>\<exists> l \<bullet> \<guillemotleft>l\<guillemotright> =\<^sub>u \<^bold>l \<and> \<lceil>b(l)\<lbrakk>$\<^bold>v/$\<^bold>v\<acute>\<rbrakk>\<rceil>\<^sub>C) \<triangleright> (hrdPreempt_nz P b c Q))"

definition hrdODE ::
  "('a::ordered_euclidean_space \<Longrightarrow> 'c::t2_space) \<Rightarrow>
   ('a ODE, 'c \<times> 'c) uexpr \<Rightarrow> ('d, 'c) hyrel" where
[upred_defs, rdes_def]: "hrdODE x \<F>' = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<langle>x \<bullet> \<F>'\<rangle>\<^sub>h \<diamondop> false)"

subsection {* Syntax Translations *} 

syntax
  "_hrdEvolve"       :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>H _" [90,91] 90)
  "_hrdEvolveBounds" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>[_,_]\<^sub>H _" [90,0,0,91] 90)
  "_hrdEvolveTil"    :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<leftarrow>\<^sub>H'(_') _" [90,0,91] 90)  
  "_hrdODE"          :: "salpha \<Rightarrow> logic \<Rightarrow> logic" ("\<langle>_ \<bullet> _\<rangle>\<^sub>H")
  "_hrdUntil_inv"  :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ inv _ until\<^sub>H _" [74,0,75] 74)
  "_hrdUntil"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ until\<^sub>H _" [74,75] 74)
  "_hrdPreempt_nz" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ [_|_]\<^sub>H\<^sup>+ _" [64,0,0,65] 64)
  "_hrdPreempt"    :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ [_|_]\<^sub>H _" [64,0,0,65] 64)
  
translations
  "_hrdEvolve a f" => "CONST hrdEvolve a (\<lambda> _time_var. f)"
  "_hrdEvolve a f" <= "CONST hrdEvolve a (\<lambda> ti. f)"
  "_hrdEvolveBounds a l u f" => "CONST hrdEvolveBounds a l u (\<lambda> _time_var. f)"
  "_hrdEvolveBounds a l u f" <= "CONST hrdEvolveBounds a l u (\<lambda> ti. f)"
  "_hrdEvolveTil a t f" => "CONST hrdEvolveTil a t (\<lambda> _time_var. f)"
  "_hrdEvolveTil a t f" <= "CONST hrdEvolveTil a t (\<lambda> ti. f)"
  "_hrdODE a P" == "CONST hrdODE a P"
  "_hrdUntil_inv P b c" => "CONST hrdUntil P (\<lambda> _time_var. b) (\<lambda> _time_var. c)"
  "_hrdUntil_inv P b c" <= "CONST hrdUntil P (\<lambda> t. b) (\<lambda> t'. c)"
  "_hrdUntil P b"       => "CONST hrdUntil P (\<lambda> _time_var. \<not> b) (\<lambda> _time_var. b)"
  "_hrdPreempt_nz P b c Q" => "CONST hrdPreempt_nz P (\<lambda> _time_var. b) (\<lambda> _time_var. c) Q"
  "_hrdPreempt_nz P b c Q" <= "CONST hrdPreempt_nz P (\<lambda> t. b) (\<lambda> t'. c) Q"
  "_hrdPreempt P b c Q" => "CONST hrdPreempt P (\<lambda> _time_var. b) (\<lambda> _time_var. c) Q"
  "_hrdPreempt P b c Q" <= "CONST hrdPreempt P (\<lambda> t. b) (\<lambda> t'. c) Q"

subsection {* Contract Calculations *}
  
lemma preR_hrdPred [rdes]: "pre\<^sub>R([P]\<^sub>H) = true\<^sub>r"
  by (rel_auto)
    
lemma periR_hrdPred [rdes]: 
  "P is RR \<Longrightarrow> peri\<^sub>R([P]\<^sub>H) = P"
  by (simp add: hrdPred_def rdes closure rpred)

lemma postR_hrdPred [rdes]: 
  "P is RR \<Longrightarrow> post\<^sub>R([P]\<^sub>H) = false"
  by (simp add: hrdPred_def rdes closure rpred)
    
lemma preR_hrdEvolve [rdes]: "pre\<^sub>R(x \<leftarrow>\<^sub>H f(ti)) = true\<^sub>r"
  by (rel_auto)
    
lemma periR_hrdEvolve [rdes]: "peri\<^sub>R(x \<leftarrow>\<^sub>H f(ti)) = (x \<leftarrow>\<^sub>h f(ti))"
  by (rel_auto)

lemma postR_hrdEvolve [rdes]: "post\<^sub>R(x \<leftarrow>\<^sub>H f(ti)) = false"
  by (rel_auto)
    
lemma preR_hrdEvolveBounds [rdes]: "pre\<^sub>R(x \<leftarrow>[l,u]\<^sub>H f(ti)) = true\<^sub>r"
  by (rel_auto)
    
lemma periR_hrdEvolveBounds [rdes]: "peri\<^sub>R(x \<leftarrow>[l,u]\<^sub>H f(ti)) = (x \<leftarrow>\<^sub>h\<le>(u) f(ti)) "
  by (rel_auto)

declare minus_zero_eq [dest]
    
lemma postR_hrdEvolveBounds [rdes]: 
  "post\<^sub>R(x \<leftarrow>[l,u]\<^sub>H f(ti)) = ((x \<leftarrow>[l,u]\<^sub>h f(ti)) \<triangleleft> u >\<^sub>u 0 \<triangleright>\<^sub>R II\<^sub>r)"
  by (rel_auto)

lemma preR_hrdODE [rdes]:
  "pre\<^sub>R(\<langle>x \<bullet> \<F>'\<rangle>\<^sub>H) = true\<^sub>r"
  by (simp add: hrdODE_def rdes closure)

lemma periR_hrdODE [rdes]:
  "peri\<^sub>R(\<langle>x \<bullet> \<F>'\<rangle>\<^sub>H) = \<langle>x \<bullet> \<F>'\<rangle>\<^sub>h"
  by (simp add: hrdODE_def rdes closure rpred)

lemma postR_hrdODE [rdes]:
  "post\<^sub>R(\<langle>x \<bullet> \<F>'\<rangle>\<^sub>H) = false"
  by (simp add: hrdODE_def rdes closure rpred)

lemma hrdUntil_rdes_def [rdes_def]:
  assumes "P\<^sub>1 is RR" "P\<^sub>2 is RR" "P\<^sub>3 is RR"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) inv b(ti) until\<^sub>H c(ti) =
         \<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> (P\<^sub>2 \<and> \<lceil>b(ti)\<rceil>\<^sub>h) \<diamondop> (P\<^sub>3 \<or> P\<^sub>2 inv b(ti) until\<^sub>h c(ti)))"
  by (simp add: hrdUntil_def rdes assms, rel_auto)
    
lemma preR_hrdUntil [rdes]: 
  "P is SRD \<Longrightarrow> pre\<^sub>R(P inv b(ti) until\<^sub>H c(ti)) = pre\<^sub>R(P)"
  by (simp add: hrdUntil_def rea_pre_RHS_design unrest usubst R1_R2c_is_R2 preR_R2 Healthy_if)

lemma periR_hrdUntil [rdes]: 
  "P is NSRD \<Longrightarrow> peri\<^sub>R(P inv b(ti) until\<^sub>H c(ti)) = (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R(P) \<and> \<lceil>b(ti)\<rceil>\<^sub>h)"
  by (simp add: hrdUntil_def rea_peri_RHS_design unrest usubst impl_alt_def
      NSRD_is_SRD R1_disj R1_extend_conj' R1_hInt  R2c_and R2c_disj 
      R2c_not R2c_peri_SRD R2s_hInt  R1_rea_impl R2c_preR R2c_rea_impl)

lemma postR_hrdUntil [rdes]:
  "P is NSRD \<Longrightarrow>
   post\<^sub>R(P inv b(ti) until\<^sub>H c(ti)) = 
  (pre\<^sub>R P \<Rightarrow>\<^sub>r (post\<^sub>R(P) \<or> (peri\<^sub>R(P) inv b(ti) until\<^sub>h c(ti))))"
  by (simp add: hrdUntil_def rdes closure unrest)
    
text {* It should be possible to simplify this surely. *}
  
lemma hrdPreempt_nz_rdes_def [rdes_def]:
  assumes "P\<^sub>1 is RC" "P\<^sub>2 is RR" "$st\<acute> \<sharp> P\<^sub>2" "P\<^sub>3 is RR" "Q\<^sub>1 is RR" "Q\<^sub>2 is RR" "Q\<^sub>3 is RR"
  shows "(\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) [b(ti)|c(ti)]\<^sub>H\<^sup>+ \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3)) =
          \<^bold>R\<^sub>s ( (P\<^sub>1 \<and> (P\<^sub>3 \<or> P\<^sub>2 inv b(ti) until\<^sub>h c(ti)) wp\<^sub>R Q\<^sub>1) 
             \<turnstile> (P\<^sub>2 \<and> hInt b \<or> (P\<^sub>3 \<or> P\<^sub>2 inv b(ti) until\<^sub>h c(ti)) ;; Q\<^sub>2) 
             \<diamondop> (P\<^sub>3 \<or> P\<^sub>2 inv b(ti) until\<^sub>h c(ti)) ;; Q\<^sub>3)"
  by (simp add: hrdPreempt_nz_def rdes_def assms closure unrest)
    
subsection {* Closure Laws *}
    
lemma hrdPred_NSRD [closure]: 
  "\<lbrakk> P is RR; $st\<acute> \<sharp> P \<rbrakk> \<Longrightarrow> [P]\<^sub>H is NSRD"
  by (simp add: hrdPred_def closure unrest)
  
lemma hrdEvolve_SRD [closure]: "x \<leftarrow>\<^sub>H f(ti) is SRD"
  by (simp add: hrdEvolve_def init_cont_def closure unrest)
    
lemma hrdEvolve_NSRD [closure]: "x \<leftarrow>\<^sub>H f(ti) is NSRD"
  by (rule NSRD_intro, simp_all add: init_cont_def rdes closure unrest)
        
lemma hrdEvolveBounds_SRD [closure]: "x \<leftarrow>[l,u]\<^sub>H f(ti) is SRD"
  by (simp add: hrdEvolveBounds_def init_cont_def final_cont_def closure unrest)
    
lemma hrdEvolveBounds_NSRD [closure]: "x \<leftarrow>[l,u]\<^sub>H f(ti) is NSRD"
  by (rule NSRD_intro, simp_all add: init_cont_def final_cont_def rdes closure unrest)    
   
lemma hrdODE_SRD [closure]: "\<langle>x \<bullet> \<F>'\<rangle>\<^sub>H is SRD"
  by (simp add: hrdODE_def closure unrest)

lemma hrdODE_NSRD [closure]: "\<langle>x \<bullet> \<F>'\<rangle>\<^sub>H is NSRD"
  by (simp add: hrdODE_def closure unrest)
    
lemma hrdUntil_SRD [closure]: "P is SRD \<Longrightarrow> P inv b(ti) until\<^sub>H c(ti) is SRD"
  by (simp add: hrdUntil_def closure unrest)
    
lemma hrdUntil_NSRD [closure]: "P is NSRD \<Longrightarrow> P inv b(ti) until\<^sub>H c(ti) is NSRD"
  by (rule NSRD_intro, simp_all add: closure rdes unrest NSRD_neg_pre_unit)

lemma hrdPreempt_nz_NSRD [closure]:
  assumes "P is NSRD" "Q is NSRD"
  shows "P [b|c]\<^sub>H\<^sup>+ Q is NSRD"
  by (simp add: hrdPreempt_nz_def closure assms)

subsection {* Algebraic Laws *}
   
lemma hrdPred_non_term: 
  assumes "P is RR" "$st\<acute> \<sharp> P" "Q is SRD"
  shows "[P]\<^sub>H ;; Q = [P]\<^sub>H"
  by (simp add: NSRD_is_SRD NSRD_seq_post_false assms hrdPred_NSRD postR_hrdPred)

lemma hrdPred_conj: "([P]\<^sub>H \<and> [Q]\<^sub>H) = [P \<and> Q]\<^sub>H"
  by (rel_auto)
  
lemma hrdPred_hEvolve: "[x \<leftarrow>\<^sub>h f(ti)]\<^sub>H = x \<leftarrow>\<^sub>H f(ti)"
  by (simp add: hrdEvolve_def hrdPred_def)
    
lemma hrdEvolve_non_term [simp]:
  assumes "P is SRD"
  shows "(x \<leftarrow>\<^sub>H f(ti)) ;; P = (x \<leftarrow>\<^sub>H f(ti))"
  by (simp add: NSRD_is_SRD NSRD_seq_post_false assms hrdEvolve_NSRD postR_hrdEvolve)
                
lemma hrdEvolve_conj [simp]: 
  "(x \<leftarrow>\<^sub>H f(ti) \<and> y \<leftarrow>\<^sub>H g(ti)) = {&x, &y} \<leftarrow>\<^sub>H (f ti, g ti)\<^sub>u"
  by (simp add: rdes_def rpred closure)
    
lemma hrdUntil_false: 
  assumes "P is SRD"
  shows "P inv true until\<^sub>H false = P"
proof -
  have "(peri\<^sub>R P \<and> \<lceil>true\<rceil>\<^sub>h) = peri\<^sub>R P"
    by (metis R1_extend_conj' R1_peri_SRD assms hInt_true utp_pred_laws.inf_top_right)
  thus ?thesis 
    by (simp add: hUntil_false hrdUntil_def alpha SRD_reactive_tri_design assms)
qed
    
lemma hrdUntil_true: 
  assumes "P is SRD"
  shows "P until\<^sub>H true = \<^bold>R\<^sub>s(pre\<^sub>R P \<turnstile> (peri\<^sub>R P \<and> $tr\<acute> =\<^sub>u $tr) \<diamondop> (post\<^sub>R P))"
  by (simp add: hrdUntil_def hInt_false alpha, rel_auto)
           
text {* This isn't quite right; if $P$ terminates $Q$ should not be enabled. However, since for
  what we do $P$ actually never terminates this is fine for now but should be fixed later. *}
    
lemma hrdPreempt_nz_false:
  assumes "P is NSRD" "Q is NSRD"
  shows "(P [true|false]\<^sub>H\<^sup>+ Q) = P ;; Q"
  by (simp add: hrdPreempt_nz_def hrdUntil_false assms closure)
      
lemma hrdIntF_zero: "x \<leftarrow>\<^sub>H(0) f(ti) = II\<^sub>R"
  by (simp add: hrdEvolveBounds_def alpha, rel_auto)

theorem hrdODE_solution:
  assumes 
    "vwb_lens x" "\<forall> x. \<forall> l > 0. (\<F>(x) usolves_ode \<F>' from 0) {0..l} UNIV" "\<forall> x. \<F>(x)(0) = x"
  shows "\<langle>x \<bullet> \<guillemotleft>\<F>'\<guillemotright>\<rangle>\<^sub>H = x \<leftarrow>\<^sub>H \<guillemotleft>\<F>\<guillemotright>($x)\<^sub>a(\<guillemotleft>ti\<guillemotright>)\<^sub>a"
  by (rule SRD_eq_intro, simp_all add: closure assms rdes rpred ode_solution)
  
theorem hrdUntil_inv_solve:
  assumes 
    "vwb_lens x" "0 < k" "k \<le> l" "continuous_on {0..l} f" "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall> t \<in> {0..<l}. b\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = true" "b\<lbrakk>\<guillemotleft>f(l)\<guillemotright>/$x\<acute>\<rbrakk> = false"
    "\<forall> t \<in> {0..<k}. c\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = false" "\<forall> t \<in> {k..l}. c\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = true"
  shows "(x \<leftarrow>\<^sub>H \<guillemotleft>f(ti)\<guillemotright>) inv b until\<^sub>H c = x \<leftarrow>[\<guillemotleft>k\<guillemotright>,\<guillemotleft>l\<guillemotright>]\<^sub>H \<guillemotleft>f(ti)\<guillemotright>"
proof (rule SRD_eq_intro, simp_all add: closure assms rdes rpred)
  from assms(6-9) 
  have a: 
    "\<forall>t\<in>{0..<l}. \<forall>s s'. \<lbrakk>b\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> s' (f t))"
    "\<forall>s s'. \<not> \<lbrakk>b\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> s' (f l))"
    "\<forall>t\<in>{0..<k}. \<forall>s s'. \<not> \<lbrakk>c\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> s' (f t))"
    "\<forall>t\<in>{k..l}. \<forall>s s'. \<lbrakk>c\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> s' (f t))"
    by (rel_auto)+
  show "(x \<leftarrow>\<^sub>h \<guillemotleft>f ti\<guillemotright> \<and> \<lceil>b\<rceil>\<^sub>h) = x \<leftarrow>\<^sub>h\<le>(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>" (is "?lhs = ?rhs")
  proof (rule antisym)
    show "?lhs \<sqsubseteq> ?rhs"
    proof (rel_simp)
      fix tr tr' s t
      assume b:
        "tr < tr'"
        "end\<^sub>t (tr' - tr) \<le> l"
        "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t"
        "0 \<le> t" "t < end\<^sub>t (tr' - tr)"
      from a(1) b(2,4-5) have "\<lbrakk>b\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) (f t))"
        by (auto)
      moreover have "put\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) (f t) = (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))"
        by (metis assms(1) b(3) b(4) b(5) vwb_lens.put_eq)
      ultimately show "\<lbrakk>b\<rbrakk>\<^sub>e (s, \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))"
        by simp
    qed
    show "?rhs \<sqsubseteq> ?lhs"
    proof (rel_simp)
      fix tr tr' s t
      assume b:
        "tr < tr'"
        "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) = f t"
        "\<forall>t. 0 \<le> t \<and> t < end\<^sub>t (tr' - tr) \<longrightarrow> \<lbrakk>b\<rbrakk>\<^sub>e (s, \<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr))"
      have 1:"\<not> \<lbrakk>b\<rbrakk>\<^sub>e (s, put\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t(t + end\<^sub>t tr)) (f l))"
        using a(2) by auto
      show "end\<^sub>t (tr' - tr) \<le> l"
      proof (rule ccontr)
        assume l: "\<not> end\<^sub>t (tr' - tr) \<le> l"
        with assms(2-3) b(3) have 1:"\<lbrakk>b\<rbrakk>\<^sub>e (s, (\<langle>tr'\<rangle>\<^sub>t(l + end\<^sub>t tr)))"
          by (auto)
        have "get\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t (l + end\<^sub>t tr)) = f l"
          using assms(2) assms(3) b(2) l by auto
        hence "put\<^bsub>x\<^esub> (\<langle>tr'\<rangle>\<^sub>t (l + end\<^sub>t tr)) (f l) = (\<langle>tr'\<rangle>\<^sub>t (l + end\<^sub>t tr))"
          by (metis assms(1) vwb_lens.put_eq) 
        hence "\<not> \<lbrakk>b\<rbrakk>\<^sub>e (s, (\<langle>tr'\<rangle>\<^sub>t (l + end\<^sub>t tr)))"
          by (metis a(2))
        with 1 show False
          by auto
      qed
    qed
  qed
  show "x \<leftarrow>\<^sub>h \<guillemotleft>f ti\<guillemotright> inv b until\<^sub>h c = x \<leftarrow>[\<guillemotleft>k\<guillemotright>,\<guillemotleft>l\<guillemotright>]\<^sub>h \<guillemotleft>f ti\<guillemotright> \<triangleleft> 0 <\<^sub>u \<guillemotleft>l\<guillemotright> \<triangleright>\<^sub>R II\<^sub>r" (is "?lhs = ?rhs")
  proof -
    have "?lhs = x \<leftarrow>[\<guillemotleft>k\<guillemotright>,\<guillemotleft>l\<guillemotright>]\<^sub>h \<guillemotleft>f ti\<guillemotright>"
      by (rule hUntil_inv_solve, simp_all add: assms)
    with assms(2-3) show ?thesis
      by (simp, rel_auto)
  qed
qed
  
lemma hrdUntil_solve:
  assumes 
    "vwb_lens x" "k > 0" "continuous_on {0..k} f" "continuous_on UNIV get\<^bsub>x\<^esub>"
    "\<forall> t \<in> {0..<k}. c\<lbrakk>\<guillemotleft>f(t)\<guillemotright>/$x\<acute>\<rbrakk> = false" "c\<lbrakk>\<guillemotleft>f(k)\<guillemotright>/$x\<acute>\<rbrakk> = true"
  shows "(x \<leftarrow>\<^sub>H \<guillemotleft>f(ti)\<guillemotright>) until\<^sub>H c = x \<leftarrow>\<^sub>H(\<guillemotleft>k\<guillemotright>) \<guillemotleft>f(ti)\<guillemotright>"
  using assms
  by (rule_tac hrdUntil_inv_solve, simp_all, rel_auto+)
  
subsection {* Stepping a Hybrid Reactive Design *}

definition hrdStepRel :: "real \<Rightarrow> ('d, 'c::t2_space) hyrel \<Rightarrow> 'c hrel" ("Step[_]\<^sub>H") where
[upred_defs]: "Step[t]\<^sub>H P = HyStep[t](peri\<^sub>R(P))"

lemma hrdStep_hrdEvolve:
  assumes "n > 0" "continuous_on {0..n} f"
  shows "Step[n]\<^sub>H(&\<^bold>v \<leftarrow>\<^sub>H \<guillemotleft>f(ti)\<guillemotright>) = (\<^bold>v := \<guillemotleft>f n\<guillemotright>)"
  by (simp add: hrdStepRel_def rdes assms HyStep_hEvolve)
  
(*
lemma tt_eq_iff_end_same:
  "\<lbrakk> s \<le> t; end\<^sub>t(s) = end\<^sub>t(t) \<rbrakk> \<Longrightarrow> s = t"
  using tt_end_minus by fastforce

lemma hrdStep_hrdEvolveAt_le:
  fixes P :: "('d, 'c::t2_space) hyrel"
  assumes "n > 0" "l \<ge> n" "continuous_on {0..n} f" "P is NSRD" "pre\<^sub>R(P) = true\<^sub>r"
  shows "Step[n]\<^sub>H(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(ti)\<guillemotright> ;; P) = (\<^bold>v := \<guillemotleft>f n\<guillemotright>)"
proof -
  from assms(1,2) 
  have 1:"peri\<^sub>R(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(ti)\<guillemotright> ;; P) = (&\<^bold>v \<leftarrow>\<^sub>h\<le>(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright> \<or> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright> ;; RR(peri\<^sub>R P))"
    (is "?lhs = ?rhs")
    by (simp add: hrdStepRel_def hStepRel_def rdes closure assms rpred wp Healthy_if, rel_auto)
  from assms(1,2) have "(?lhs \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d) = (&\<^bold>v \<leftarrow>\<^sub>h\<le>(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright> \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)"
    by (simp add: 1, rel_auto, simp add: tt_end_minus, metis eq_iff tt_eq_iff_end_same tt_sub_end)
  also from assms(1,2) have "... = &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>n\<guillemotright>) \<guillemotleft>f ti\<guillemotright>"
    by (rel_auto)
  finally have "HyStep[n](?lhs) = HyStep[n](&\<^bold>v \<leftarrow>\<^sub>h \<guillemotleft>f ti\<guillemotright> :: ('d, 'c) hyrel)"
    using assms(1,2) by (simp add: hStepRel_def, rel_auto)
  thus ?thesis
    by (simp add: hrdStepRel_def HyStep_hEvolve assms)
qed 
  
lemma time_length_conj_seq:
  assumes "m < n" "P is R1" "Q is R1"
  shows  "((\<^bold>l =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> P) ;; Q \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright>) = ((\<^bold>l =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> P) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-m\<guillemotright> \<and> Q))"
proof -
  from assms(1) have "((\<^bold>l =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> R1(P)) ;; R1(Q) \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright>) = ((\<^bold>l =\<^sub>u \<guillemotleft>m\<guillemotright> \<and> R1(P)) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-m\<guillemotright> \<and> R1(Q)))"
    apply (rel_auto, simp_all add: tt_end_minus)
    using tt_end_minus apply blast+
  done
  thus ?thesis
    by (simp add: Healthy_if assms)
qed
  
lemma lim_tt_minus:
  "g < f \<Longrightarrow> lim\<^sub>t(f - g) = lim\<^sub>t f"
  by (metis diff_add_cancel_left' less_imp_le lim_tt_cat tt_end_gr_zero_iff)
  
lemma final_cont_seq_right:
  assumes "P is RR" "Q is RR"
  shows "(P ;; ($tr <\<^sub>u $tr\<acute> \<and> Q) \<and> rl(&\<^bold>v)) = P ;; ($tr <\<^sub>u $tr\<acute> \<and> Q \<and> rl(&\<^bold>v))" (is "?lhs = ?rhs")
proof -
  have "(RR(P) ;; ($tr <\<^sub>u $tr\<acute> \<and> RR(Q)) \<and> rl(&\<^bold>v)) = RR(P) ;; ($tr <\<^sub>u $tr\<acute> \<and> RR(Q) \<and> rl(&\<^bold>v))" 
    apply (rel_auto)
    apply (metis lim_tt_minus)
    apply blast
    apply (simp_all add: lim_tt_minus)
    apply (metis less_iff minus_gr_zero_iff minus_zero_eq neq_zero_impl_greater)
    apply blast 
    apply (metis le_zero_iff minus_cancel_le minus_gr_zero_iff minus_zero_eq neq_zero_impl_greater)
  done
  thus ?thesis
    by (simp add: Healthy_if assms) 
qed

lemma final_cont_seq_right_length_eq:
  assumes "P is RR" "Q is RR" "n > 0"
  shows "(P ;; (\<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> Q) \<and> rl(&\<^bold>v)) = P ;; (\<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> Q \<and> rl(&\<^bold>v))" (is "?lhs = ?rhs")
proof -
  from assms(3) have "(RR(P) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> RR(Q)) \<and> rl(&\<^bold>v)) = RR(P) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> RR(Q) \<and> rl(&\<^bold>v))" 
    apply (rel_auto)
    apply (metis lim_tt_minus)
    apply blast
    apply (simp add: lim_tt_minus)
    apply (simp add: lim_tt_minus)
    apply (metis less_iff minus_gr_zero_iff minus_zero_eq neq_zero_impl_greater)
    apply blast
    apply (metis le_zero_iff minus_cancel_le minus_gr_zero_iff minus_zero_eq neq_zero_impl_greater)
  done
  thus ?thesis
    by (simp add: Healthy_if assms) 
qed
        
lemma hrdStep_hrdEvolveAt_lemma1:
  assumes "0 < l" "l < n"  
  shows "(\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> rl(&\<^bold>v)) = (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> $st:\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(&tt(\<guillemotleft>t\<guillemotright>)\<^sub>a))"
  using assms
  by (rel_auto)
  
lemma hrdStep_hrdEvolveAt_greater:
  fixes P :: "('d, 'c::t2_space) hyrel"
  assumes "0 < l" "l < n" "continuous_on {0..n} f" "P is NSRD" "pre\<^sub>R(P) = true\<^sub>r"
  shows "Step[n]\<^sub>H(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(ti)\<guillemotright> ;; P) = (\<^bold>v := \<guillemotleft>f n\<guillemotright> ;; Step[n-l]\<^sub>H(P))"
proof -
  from assms(1,2)
  have 1:"peri\<^sub>R(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(ti)\<guillemotright> ;; P) = (&\<^bold>v \<leftarrow>\<^sub>h\<le>(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright> \<or> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright> ;; RR(peri\<^sub>R P))"
    (is "?lhs = ?rhs")
    by (simp add: hrdStepRel_def hStepRel_def rdes closure assms rpred wp Healthy_if, rel_auto)
  from assms(1,2) 
  have "(?lhs \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright> \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d) = 
        (((\<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>) ;; RR(peri\<^sub>R P) \<and> \<^bold>l =\<^sub>u \<guillemotleft>n\<guillemotright>) \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)"
    by (simp add: 1, rel_auto)
  also from assms(1,2) 
  have "... = ((\<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> RR(peri\<^sub>R P)) \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)"
    by (subst time_length_conj_seq, simp_all add: assms closure) 
  also
  have "... = (((\<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> RR(peri\<^sub>R P)) \<and> rl(&\<^bold>v)) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)"
    by (simp add: conj_assoc)
  also from assms(1-2)
  have "... = ((\<^bold>l =\<^sub>u \<guillemotleft>l\<guillemotright> \<and> &\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> rl(&\<^bold>v)) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)"
    by (subst final_cont_seq_right_length_eq, (rel_auto)+)
  also
  have "... = ((&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>) ;; ((\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> rl(&\<^bold>v)) \<and> RR(peri\<^sub>R P) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d))"
    by (rel_auto)
  also
  have "... = ((&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>) ;; ((\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> $st:\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(&tt(\<guillemotleft>t\<guillemotright>)\<^sub>a)) \<and> RR(peri\<^sub>R P) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d))"
    by (simp add: hrdStep_hrdEvolveAt_lemma1 assms)  
  also
  have "... = ((&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n-l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> $st:\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(&tt(\<guillemotleft>t\<guillemotright>)\<^sub>a) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d))"
    by (rel_auto)
  finally 
  have "Step[n]\<^sub>H(&\<^bold>v \<leftarrow>\<^sub>H(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f(ti)\<guillemotright> ;; P) = 
        \<lfloor>((&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright>) ;; (\<^bold>l =\<^sub>u \<guillemotleft>n - l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> $st:\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(&tt(\<guillemotleft>t\<guillemotright>)\<^sub>a) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d)) \<restriction>\<^sub>v (&st:\<^bold>c \<times> &st:\<^bold>c)\<rfloor>\<^sub>C"
    using assms(1-2)
    by (simp add: hrdStepRel_def hStepRel_def 1 Healthy_if closure assms, rel_auto)
  also have "... = (\<lfloor>(&\<^bold>v \<leftarrow>\<^sub>h(\<guillemotleft>l\<guillemotright>) \<guillemotleft>f ti\<guillemotright> :: ('d, 'c::t2_space) hyrel) \<restriction>\<^sub>v (&st:\<^bold>c \<times> &st:\<^bold>c)\<rfloor>\<^sub>C) ;;\<^sub>h \<lfloor>(\<^bold>l =\<^sub>u \<guillemotleft>n - l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> $st:\<^bold>c\<acute> =\<^sub>u lim\<^sub>u(t \<rightarrow> \<^bold>l\<^sup>-)(&tt(\<guillemotleft>t\<guillemotright>)\<^sub>a) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d) \<restriction>\<^sub>v (&st:\<^bold>c \<times> &st:\<^bold>c)\<rfloor>\<^sub>C"
    apply (rel_auto)
    apply (rename_tac tr tr' tr'' d tr''')
    apply (rule_tac x="tr" in exI)
    apply (rule_tac x="d" in exI)
    apply (rule_tac x="tr'' + (tr''' - tr')" in exI)
    apply (rule_tac x="d" in exI)    
    apply (rule_tac x="tr''" in exI)
    apply (auto)
  done
  also have "... = \<^bold>v := \<guillemotleft>f n\<guillemotright> ;;\<^sub>h \<lfloor>(\<^bold>l =\<^sub>u \<guillemotleft>n - l\<guillemotright> \<and> RR(peri\<^sub>R P) \<and> rl(&\<^bold>v) \<and> $st:\<^bold>d\<acute> =\<^sub>u $st:\<^bold>d) \<restriction>\<^sub>v (&st:\<^bold>c \<times> &st:\<^bold>c)\<rfloor>\<^sub>C"
oops
*)  
    
end