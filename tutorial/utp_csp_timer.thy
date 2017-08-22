section {* FMI Timer (Simplified) *}

theory utp_csp_timer
  imports "../theories/utp_csp"
begin

  
definition wpr :: "'a hrel \<Rightarrow> 'a hrel \<Rightarrow> 'a hrel" (infixl "\\" 70) where
  [upred_defs]: "Q \\ R = \<Sqinter> { Y. R \<sqsubseteq> Y ;; Q}"
  
definition spr :: "'a hrel \<Rightarrow> 'a hrel \<Rightarrow> 'a hrel" where
  [upred_defs]: "spr Q R = \<Sqinter> { Y. R \<sqsubseteq> Y ;; Q}"


  
lemma "R \<sqsubseteq> P ;; Q \<longleftrightarrow> Q \\ R \<sqsubseteq> P"
  by (rel_blast)
 
    
type_synonym TIME = nat
  
datatype ch_timer = 
  setT TIME |
  updateSS TIME |
  step "TIME \<times> TIME" |
  endc
  
alphabet st_timer =
  currentTime :: TIME
  stepSize    :: TIME
  
type_synonym timer = "(st_timer, ch_timer) action"
  
abbreviation TimerBody :: "TIME \<Rightarrow> timer" where
"TimerBody tN \<equiv> (setT?(t:\<guillemotleft>t\<guillemotright> <\<^sub>u \<guillemotleft>tN\<guillemotright>) \<^bold>\<rightarrow> currentTime :=\<^sub>C \<guillemotleft>t\<guillemotright>
           \<box> updateSS?(ss) \<^bold>\<rightarrow> stepSize :=\<^sub>C \<guillemotleft>ss\<guillemotright>
           \<box> step!(&currentTime)!(&stepSize) \<^bold>\<rightarrow>
               currentTime :=\<^sub>C min\<^sub>u(&currentTime + &stepSize, \<guillemotleft>tN\<guillemotright>)
           \<box> (&currentTime =\<^sub>u \<guillemotleft>tN\<guillemotright>) &\<^sub>u endc \<^bold>\<rightarrow> Stop)"
  
definition Timer :: "TIME \<Rightarrow> TIME \<Rightarrow> TIME \<Rightarrow> timer" where
"Timer ct hc tN =
  (currentTime, stepSize) :=\<^sub>C (\<guillemotleft>ct\<guillemotright>, \<guillemotleft>hc\<guillemotright>) ;;
  (\<mu>\<^sub>C Step \<bullet> TimerBody(tN) ;; Step)"  

lemma wpR_assign [wp]:
  assumes "P is NCSP"
  shows "($tr\<acute> =\<^sub>u $tr \<and> \<lceil>\<langle>\<sigma>\<rangle>\<^sub>a\<rceil>\<^sub>S) wp\<^sub>R pre\<^sub>R P = \<lceil>\<sigma>\<rceil>\<^sub>S\<^sub>\<sigma> \<dagger> pre\<^sub>R(P)"
  by (simp add: wpR_def unrest rdes assms closure R1_neg_preR usubst)
    
lemma "[true \<turnstile> \<^bold>\<forall> t \<bullet> \<guillemotleft>t\<guillemotright> <\<^sub>u \<guillemotleft>tN\<guillemotright> \<and> \<guillemotleft>trace\<guillemotright> =\<^sub>u \<langle>\<rangle> \<Rightarrow> (setT\<cdot>\<guillemotleft>t\<guillemotright>)\<^sub>u \<notin>\<^sub>u \<guillemotleft>refs\<guillemotright> | false]\<^sub>C 
  \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> TimerBody tN ;; X)"
  apply (rule CRD_mu_basic_refine)    
  apply (simp_all add: closure unrest rdes wp usubst alpha)
  apply (rel_auto)
  apply (rel_auto)
  apply (metis Prefix_Order.same_prefix_nil less_eq_list_def list_append_prefixD prefix_concat_minus)+
  done
   
declare list_concat_minus_list_concat [simp]

lemma list_Cons_minus [simp]: "(x # y) - (x # z) = y - z"
  by (simp add: minus_list_def)
    
lemma "[true 
       \<turnstile> \<^bold>\<forall> t \<bullet> \<guillemotleft>tN\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>trace\<guillemotright> =\<^sub>u \<langle>(setT\<cdot>\<guillemotleft>t\<guillemotright>)\<^sub>u\<rangle> \<Rightarrow> \<guillemotleft>t\<guillemotright> <\<^sub>u \<guillemotleft>tN\<guillemotright> 
       | false]\<^sub>C
       \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> TimerBody tN ;; X)"
  apply (rule CRD_mu_basic_refine)    
      apply (simp_all add: closure unrest rdes wp usubst alpha)
  apply (rel_auto)
  apply (simp_all add: zero_list_def)
  apply (rel_auto)
    apply (metis Prefix_Order.prefix_snoc Prefix_Order.same_prefix_nil append1_eq_conv ch_timer.inject(1) list.discI minus_list_def prefix_concat_minus)
  apply (metis Prefix_Order.prefix_snoc Prefix_Order.same_prefix_nil append1_eq_conv ch_timer.distinct(1) list.discI minus_list_def prefix_concat_minus)
  by (metis Prefix_Order.prefix_snoc Prefix_Order.same_prefix_nil append1_eq_conv ch_timer.distinct(3) list.discI minus_list_def prefix_concat_minus)
    
    
lemma "[true 
       \<turnstile> \<^bold>\<forall> (t,s) \<bullet> \<guillemotleft>tN\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>trace\<guillemotright> =\<^sub>u \<langle>(setT\<cdot>\<guillemotleft>t\<guillemotright>)\<^sub>u, (updateSS\<cdot>\<guillemotleft>s\<guillemotright>)\<^sub>u\<rangle> \<Rightarrow> (step\<cdot>\<guillemotleft>(t, s)\<guillemotright>)\<^sub>u \<notin>\<^sub>u \<guillemotleft>refs\<guillemotright> 
       | false]\<^sub>C
       \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> TimerBody tN ;; X)"
  apply (rule CRD_mu_basic_refine)    
  apply (simp_all add: closure unrest rdes wp usubst alpha)
  apply (rel_auto)
  apply (simp_all add: zero_list_def)
  apply (rel_auto)
  apply (drule_tac x="a" in spec)
    apply (drule_tac x="b" in spec)
  apply (simp)
    apply (erule prefixE)
    apply (auto)
  oops
    
  

end