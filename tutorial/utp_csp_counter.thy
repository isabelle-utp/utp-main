section {* Counter in CSP *}

theory utp_csp_counter
  imports "../theories/utp_csp"
begin
  
datatype ch_counter = count (get_val: nat)

alphabet st_counter =
  ctr :: nat

lemma get_val_count [simp]: "get_val \<circ> count = id"
  by (auto)
  
text {* This one of the simplest possible stateful CSP processes. It starts from a given number
  and keeps outputting the next number when asked. *}
  
abbreviation "CtrBdy \<equiv> (count.(&ctr) \<^bold>\<rightarrow> ctr :=\<^sub>C (&ctr + 1))"
  
definition "Counter(n) = (ctr :=\<^sub>C \<guillemotleft>n\<guillemotright> ;; (\<mu>\<^sub>C X \<bullet> CtrBdy ;; X))"
  
text {* We calculate the pre, peri-, and postconditions of @{term "CtrBdy"} below. Nothing 
  surprising I think. *}
  
lemma preR_CtrBdy: "pre\<^sub>R(CtrBdy) = true"
  by (simp add: rdes closure usubst)
  
lemma periR_CtrBdy [rdes]: "peri\<^sub>R(CtrBdy) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>(count\<cdot>&ctr)\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (simp add: rdes closure usubst alpha unrest)
    
lemma postR_CtrBdy [rdes]: "post\<^sub>R(CtrBdy) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>(count\<cdot>&ctr)\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>ctr := (&ctr + 1)\<rceil>\<^sub>S)"
  by (simp add: rdes closure usubst unrest)
    
text {* The recursive case is a little more interesting. *}
    
lemma preR_Counter [rdes]: "pre\<^sub>R(Counter(n)) = true"
  by (simp add: Counter_def rdes closure unrest wp usubst)
  
text {* The pericondition consists of three sequential composed parts. We use the homogeneous
  composition operation @{term "op ;;\<^sub>h"} to ensure that the Isabelle type system does not
  try to insert additional type variables into the alphabets. The first part sets up the initial
  value for @{term ctr}. The second and third parts are within an internal choice of a natural
  number $i$. The second states that the trace is extended by count and the state
  variable is updated $i \<ge> 0$ times. The power operator corresponds to iteration. The third part 
  states that after this the next count communication is not being refused. *}
  
lemma periR_Counter': 
  "peri\<^sub>R(Counter(n)) = 
    ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>ctr := \<guillemotleft>n\<guillemotright>\<rceil>\<^sub>S) ;;\<^sub>h
    (\<Sqinter> i \<bullet> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>(count\<cdot>&ctr)\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>ctr := (&ctr + 1)\<rceil>\<^sub>S) \<^bold>^ i ;;\<^sub>h
            ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>(count\<cdot>&ctr)\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>))"
  by (simp add: Counter_def rdes closure usubst unrest wp seq_UINF_distr)

text {* This pericondition can be substantially simplified by an inductive proof. We show below
  that it is really the second part is really equivalent to stating that the trace is updated
  by all the count communications between $ctr$ and $ctr+k$, and then next count is not being
  refused. *}
    
lemma tr_count_prop:
  "($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>(count\<cdot>&ctr)\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>ctr := (&ctr + 1)\<rceil>\<^sub>S) \<^bold>^ k ;; ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>(count\<cdot>&ctr)\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>) =
       ($tr\<acute> =\<^sub>u $tr ^\<^sub>u map\<^sub>u \<guillemotleft>count\<guillemotright> \<langle>$st:ctr..<$st:ctr+\<guillemotleft>k\<guillemotright>\<rangle> \<and> \<lceil>(count\<cdot>&ctr+\<guillemotleft>k\<guillemotright>)\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  apply (induct k)
   apply (rel_auto)
  apply (simp)
  apply (subst seqr_assoc[THEN sym])
  apply (simp add:usubst unrest closure)
  apply (rel_auto)
   apply (simp add: upt_conv_Cons)
  apply (simp add: upt_rec)
done
    
text {* Thus we can simplify the pericondition as follows. Effectively we have eliminated
  the iteration (the power operator is gone). *}
  
lemma periR_Counter [rdes]: 
  "peri\<^sub>R(Counter(n)) = (\<Sqinter> i \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u map\<^sub>u \<guillemotleft>count\<guillemotright> \<langle>\<guillemotleft>n\<guillemotright>..<\<guillemotleft>n+i\<guillemotright>\<rangle> \<and> \<lceil>(count\<cdot>\<guillemotleft>n+i\<guillemotright>)\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  apply (simp add: Counter_def rdes closure usubst unrest wp seq_UINF_distr tr_count_prop[simplified])
  apply (rel_auto)
done
    
text {* Like many reactive systems the postcondition is @{term false}, as it never terminates. *}
  
lemma postR_Counter [rdes]:
  "post\<^sub>R(Counter(n)) = false"
  by (simp add: Counter_def rdes closure unrest usubst wp)
      
text {* From these calculations we can prove a simple property of the counter -- any output
  on count must hold a number greater than the starting value. *}
        
lemma Counter_property_1: 
  "[true \<turnstile> \<^bold>\<forall> i \<bullet> (count\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u \<in>\<^sub>u elems\<^sub>u(\<guillemotleft>trace\<guillemotright>) \<Rightarrow> \<guillemotleft>i\<guillemotright> \<ge>\<^sub>u &ctr | false]\<^sub>C \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> CtrBdy ;; X)"
  apply (rule CRD_mu_basic_refine)
  apply (simp_all add: closure rdes usubst alpha unrest)
  apply (rel_simp)
    apply (simp add: zero_list_def)  
   apply (rel_simp)
  apply (smt Suc_leD append.assoc append_Cons append_Nil append_minus ch_counter.inject less_eq_list_def order_refl prefix_concat_minus set_ConsD)
done    

lemma Counter_property_2: 
  "[true \<turnstile> \<Sqinter> i \<bullet> \<guillemotleft>i\<guillemotright> \<ge>\<^sub>u &ctr \<and> \<guillemotleft>trace\<guillemotright> =\<^sub>u map\<^sub>u \<guillemotleft>count\<guillemotright> \<langle>&ctr..<\<guillemotleft>i\<guillemotright>\<rangle> | false ]\<^sub>C \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> CtrBdy ;; X)"
  apply (rule CRD_mu_basic_refine)
  apply (simp_all add: closure rdes usubst alpha unrest)
  apply (rel_simp, simp add: zero_list_def)
  apply auto[1]
  apply (rel_simp)
  apply (metis Prefix_Order.prefixE Suc_leD Suc_le_lessD append_Cons append_Nil append_assoc append_minus list.simps(9) upt_rec)
done
    
lemma Counter_property_3: 
  "[true \<turnstile> sorted\<^sub>u(map\<^sub>u \<guillemotleft>get_val\<guillemotright> \<guillemotleft>trace\<guillemotright>) | false ]\<^sub>C \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> CtrBdy ;; X)"
  (is "?lhs \<sqsubseteq> ?rhs")
proof -
  have "?lhs \<sqsubseteq> [true \<turnstile> \<Sqinter> i \<bullet> \<guillemotleft>i\<guillemotright> \<ge>\<^sub>u &ctr \<and> \<guillemotleft>trace\<guillemotright> =\<^sub>u map\<^sub>u \<guillemotleft>count\<guillemotright> \<langle>&ctr..<\<guillemotleft>i\<guillemotright>\<rangle> | false ]\<^sub>C"
    by (rule CRD_refine_CRD, simp_all add: alpha, rel_simp)
  thus ?thesis
    using Counter_property_2 dual_order.trans by blast
qed

end
  