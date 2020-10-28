section \<open> Counter in CSP \<close>

theory utp_csp_counter
  imports "UTP-Circus.utp_circus"
begin

utp_lift_notation csp_enable
utp_lift_notation csp_do
utp_const chan_apply (0)
  
chantype ch_counter = 
  count :: nat

alphabet st_counter =
  ctr :: nat

lemma get_val_count [simp]: "un_count_C \<circ> count_C = id"
  by (auto)
  
text \<open> This one of the simplest possible stateful CSP processes. It starts from a given number
  and keeps outputting the next number when asked. \<close>
  
abbreviation "CtrBdy \<equiv> (count.(&ctr) \<^bold>\<rightarrow> ctr :=\<^sub>C (&ctr + 1))"
  
definition "Counter(n) = (ctr :=\<^sub>C \<guillemotleft>n\<guillemotright> ;; (\<mu>\<^sub>C X \<bullet> CtrBdy ;; X))"
  
text \<open> We calculate the pre, peri-, and postconditions of @{term "CtrBdy"} below. \<close>

lemma CtrBdy_contract:
  "CtrBdy =  
    \<^bold>R\<^sub>s(true\<^sub>r 
       \<turnstile> \<E>(true,[], {(count\<cdot>&ctr)\<^sub>u}) 
       \<diamondop> \<Phi>(true,[&ctr \<mapsto>\<^sub>s &ctr + 1],[(count\<cdot>&ctr)\<^sub>u]))"
  by (rdes_simp)
    
text \<open> The precondition is simply true because there is no possibility of divergence.
  The pericondition states that in all initial states (true), and after doing no events
  (trace is empty), the count event is not being refused. The postcondition states that 
  the counter is incremented by one, and the trace is increased
  by the count event. \<close>
    
    text \<open> The recursive case is a little more interesting. \<close>
    
lemma preR_Counter [rdes]: "pre\<^sub>R(Counter(n)) = true\<^sub>r"
  by (simp add: Counter_def rdes closure rpred unrest wp usubst)
  
text \<open> The pericondition consists of three sequential composed parts. The first part sets up the initial
  value for @{term ctr}. The second and third parts are within an internal choice of a natural
  number $i$. The second states that the trace is extended by count and the state
  variable is updated $i \<ge> 0$ times. The power operator corresponds to iteration. The third part 
  states that after this the next count communication is not being refused. \<close>
  
lemma periR_Counter': 
  "peri\<^sub>R(Counter(n)) = 
    \<Phi>(true,[ctr \<mapsto>\<^sub>s \<guillemotleft>n\<guillemotright>],\<langle>\<rangle>) ;; (\<Sqinter> i \<bullet> \<Phi>(true,[ctr \<mapsto>\<^sub>s &ctr + 1], \<langle>(count\<cdot>&ctr)\<^sub>u\<rangle>) \<^bold>^ i ;; \<E>(true,\<langle>\<rangle>, {(count\<cdot>&ctr)\<^sub>u}\<^sub>u))"
  by (simp add: Counter_def rdes rpred alpha closure usubst unrest wp seq_UINF_distr)

text \<open> This pericondition can be substantially simplified by an inductive proof. We show below
  that it is really the second part is really equivalent to stating that the trace is updated
  by all the count communications between $ctr$ and $ctr+k$, and then next count is not being
  refused. \<close>
    
lemma tr_count_prop:
  "(\<Phi>(true, [ctr \<mapsto>\<^sub>s &ctr + 1], \<langle>(count\<cdot>&ctr)\<^sub>u\<rangle>)) \<^bold>^ k ;; \<E>(true,\<langle>\<rangle>,{(count\<cdot>&ctr)\<^sub>u}\<^sub>u) =
    \<E>(true,map\<^sub>u \<guillemotleft>count\<guillemotright> \<langle>&ctr..<&ctr+\<guillemotleft>k\<guillemotright>\<rangle>,{(count\<cdot>&ctr+\<guillemotleft>k\<guillemotright>)\<^sub>u}\<^sub>u)"
  apply (induct k)
   apply (rel_auto)
  apply (simp)
  apply (subst seqr_assoc[THEN sym])
  apply (simp add:usubst unrest closure)
  apply (rel_auto)
   apply (simp add: upt_conv_Cons)
  apply (simp add: upt_rec)
done
    
text \<open> Thus we can simplify the pericondition as follows. Effectively we have eliminated
  the iteration (the power operator is gone). \<close>
  
lemma periR_Counter [rdes]: 
  "peri\<^sub>R(Counter(n)) = (\<Sqinter> i \<bullet> \<E>(true,map\<^sub>u \<guillemotleft>count\<guillemotright> \<langle>\<guillemotleft>n\<guillemotright>..<\<guillemotleft>n\<guillemotright> + \<guillemotleft>i\<guillemotright>\<rangle>, {(count\<cdot>\<guillemotleft>n\<guillemotright> + \<guillemotleft>i\<guillemotright>)\<^sub>u}\<^sub>u))"
  by (simp add: Counter_def rdes rpred alpha closure usubst unrest wp seq_UINF_distr tr_count_prop[simplified])
    
text \<open> Like many reactive systems the postcondition is @{term false}, as it never terminates. \<close>
  
lemma postR_Counter [rdes]:
  "post\<^sub>R(Counter(n)) = false"
  by (simp add: Counter_def rdes rpred closure unrest usubst wp)
      
text \<open> From these calculations we can prove a simple property of the counter -- any output
  on count must hold a number greater than the starting value. \<close>
        
lemma Counter_property_1: 
  "[true \<turnstile> \<^bold>\<forall> i \<bullet> (count\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u \<in>\<^sub>u elems\<^sub>u(\<guillemotleft>trace\<guillemotright>) \<Rightarrow> \<guillemotleft>i\<guillemotright> \<ge>\<^sub>u &ctr | false]\<^sub>C \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> CtrBdy ;; X)"
  apply (rule CRD_mu_basic_refine)
  apply (simp_all add: closure rdes usubst rpred alpha unrest)
  apply (rel_simp)
    apply (simp add: zero_list_def)  
   apply (rel_simp)
  apply (smt Suc_leD append.assoc append_Cons append_Nil append_minus ch_counter.inject less_eq_list_def order_refl prefix_concat_minus set_ConsD)
done    

lemma Counter_property_2: 
  "[true \<turnstile> \<Sqinter> i \<bullet> \<guillemotleft>i\<guillemotright> \<ge>\<^sub>u &ctr \<and> \<guillemotleft>trace\<guillemotright> =\<^sub>u map\<^sub>u \<guillemotleft>count\<guillemotright> \<langle>&ctr..<\<guillemotleft>i\<guillemotright>\<rangle> | false ]\<^sub>C \<sqsubseteq> (\<mu>\<^sub>C X \<bullet> CtrBdy ;; X)"
  apply (rule CRD_mu_basic_refine)
  apply (simp_all add: closure rdes rpred usubst alpha unrest)
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
  