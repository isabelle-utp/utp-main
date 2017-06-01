section {* Counter in CSP *}

theory utp_csp_counter
  imports "../theories/utp_csp"
begin
  
datatype ch_counter = count nat
alphabet st_counter =
  ctr :: nat
  
abbreviation "CtrBdy(n) \<equiv> (count.(&ctr) \<^bold>\<rightarrow> ctr :=\<^sub>C (&ctr + 1))"
  
definition "Counter(n) = (ctr :=\<^sub>C \<guillemotleft>n\<guillemotright> ;; (\<mu>\<^sub>C X \<bullet> CtrBdy(n) ;; X))"
  
lemma preR_CtrBdy: "pre\<^sub>R(CtrBdy(n)) = true"
  by (simp add: rdes closure usubst)
  
lemma periR_CtrBdy [rdes]: "peri\<^sub>R(CtrBdy(n)) = ($tr\<acute> =\<^sub>u $tr \<and> \<lceil>(count\<cdot>&ctr)\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  by (simp add: rdes closure usubst alpha unrest)
    
lemma postR_CtrBdy [rdes]: "post\<^sub>R(CtrBdy(n)) = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>(count\<cdot>&ctr)\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>ctr := (&ctr + 1)\<rceil>\<^sub>S)"
  by (simp add: rdes closure usubst unrest)
    
lemma preR_Counter [rdes]: "pre\<^sub>R(Counter(n)) = true"
  by (simp add: Counter_def rdes closure unrest wp usubst)
  
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
    
lemma periR_Counter [rdes]: 
  "peri\<^sub>R(Counter(n)) = (\<Sqinter> i \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u map\<^sub>u \<guillemotleft>count\<guillemotright> \<langle>\<guillemotleft>n\<guillemotright>..<\<guillemotleft>n+i\<guillemotright>\<rangle> \<and> \<lceil>(count\<cdot>\<guillemotleft>n+i\<guillemotright>)\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>)"
  apply (simp add: Counter_def rdes closure usubst unrest wp seq_UINF_distr tr_count_prop[simplified])
  apply (rel_auto)
done
    
lemma postR_Counter [rdes]:
  "post\<^sub>R(Counter(n)) = false"
  by (simp add: Counter_def rdes closure unrest usubst wp)
      
lemma Counter_property: 
  "[true \<turnstile> \<^bold>\<forall> i \<bullet> (count\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u \<in>\<^sub>u elems\<^sub>u(\<guillemotleft>trace\<guillemotright>) \<Rightarrow> \<guillemotleft>i\<guillemotright> \<ge>\<^sub>u \<guillemotleft>n\<guillemotright> | false]\<^sub>R \<sqsubseteq> Counter(n)"
  apply (rule RD_contract_refine)
  apply (simp add: Counter_def closure unrest)
  apply (simp add: rdes closure unrest alpha usubst wp)
  apply (simp add: rdes closure unrest alpha usubst wp)
  apply (rel_simp)
  apply (simp add: rdes)
done
  
end
  