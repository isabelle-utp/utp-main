section \<open> Programs with memory \<close>

theory utp_mem_prog
  imports utp_mem_prelim
begin

text \<open> Heap allocation takes a lens $x$ within the store that holds an address, and an expression
  $e$ over store variables whose return type is countable. The semantics of allocation selects
  an arbitrary memory location not currently allocated in the heap, places the said address
  in $x$, and injects the expression $e$ into the heap at this memory location. \<close>

definition
  heap_alloc :: "(addr \<Longrightarrow> 's) \<Rightarrow> ('a::{countable,infinite}, 's) uexpr \<Rightarrow> 's mprog"
  ("_ := alloc'(_')" [74,0] 75) 
  where [upred_defs, ndes_simp]: 
    "x := alloc(e) = 
     (true \<turnstile>\<^sub>n (\<Sqinter> l | \<guillemotleft>l\<guillemotright> \<notin>\<^sub>u dom\<^sub>u($hp) \<bullet> str:x := \<guillemotleft>l\<guillemotright> ;; hp := &hp(&str:x \<mapsto> uop to_nat_bij (e \<oplus>\<^sub>p str))\<^sub>u))"

text \<open> Heap lookup retrieves data from the heap and places it into a store variable. If the memory
  location $l$ is unallocated then an abort is the result. \<close>

definition 
  heap_lookup :: "('a::{countable,infinite} \<Longrightarrow> 's) \<Rightarrow> (addr, 's) uexpr \<Rightarrow> 's mprog" 
  ("_ := *_" [74,75] 75)
  where [upred_defs, ndes_simp]: 
    "x := *l = (((l \<oplus>\<^sub>p str) \<in>\<^sub>u dom\<^sub>u(&hp)) \<turnstile>\<^sub>n str:x := uop from_nat_bij (&hp(l \<oplus>\<^sub>p str)\<^sub>a))"

text \<open> Heap mutation updates the value of an already allocated address in the heap. \<close>

definition
  heap_mutate :: "(addr, 's) uexpr \<Rightarrow> ('a::{countable,infinite}, 's) uexpr \<Rightarrow> 's mprog"
  ("*_ := _" [0, 74] 75)
  where [upred_defs, ndes_simp]:
    "*l := e = (((l \<oplus>\<^sub>p str) \<in>\<^sub>u dom\<^sub>u(&hp)) \<turnstile>\<^sub>n hp := &hp((l \<oplus>\<^sub>p str) \<mapsto> uop to_nat_bij (e \<oplus>\<^sub>p str))\<^sub>u)"

text \<open> Heap deallocation removes an area of memory from the heap. \<close>

definition
  heap_dealloc :: "(addr, 's) uexpr \<Rightarrow> 's mprog" ("dealloc'(_')")
  where [upred_defs, ndes_simp]:
  "dealloc(l) = (((l \<oplus>\<^sub>p str) \<in>\<^sub>u dom\<^sub>u(&hp)) \<turnstile>\<^sub>n hp := (dom\<^sub>u(&hp) - {l \<oplus>\<^sub>p str}\<^sub>u) \<lhd>\<^sub>u &hp)"

subsection \<open> Weakest Precondition Semantics \<close>

lemma wp_UINF_pred [wp]:
  "\<lbrakk> \<And> l. out\<alpha> \<sharp> P(l) \<rbrakk> \<Longrightarrow> (\<Sqinter> l | P(l) \<bullet> Q(l)) wp q = (\<^bold>\<forall> l \<bullet> \<lfloor>P(l)\<rfloor>\<^sub>< \<Rightarrow> (Q(l) wp q))"
  by (rel_blast)

lemma wp_heap_alloc [wp]:
  "\<lbrakk> vwb_lens x; x \<sharp> e \<rbrakk> \<Longrightarrow> 
   x := alloc(e) wp\<^sub>D p = (\<^bold>\<forall> l \<in> -dom\<^sub>u(&hp) \<bullet> p\<lbrakk>\<guillemotleft>l\<guillemotright>,&hp(\<guillemotleft>l\<guillemotright> \<mapsto> uop to_nat_bij (e \<oplus>\<^sub>p str))\<^sub>u/&str:x,&hp\<rbrakk>)"
  by (simp add: ndes_simp wp usubst unrest, rel_auto)

lemma wp_heap_dealloc [wp]: 
  "dealloc(e) wp\<^sub>D p = (e \<oplus>\<^sub>p str \<in>\<^sub>u dom\<^sub>u(&hp) \<and> p\<lbrakk>(dom\<^sub>u(&hp) - {e \<oplus>\<^sub>p str}\<^sub>u) \<lhd>\<^sub>u &hp/&hp\<rbrakk>)"
  by (rel_auto)

subsection \<open> Example properties \<close>

lemma least_nat_Compl_not_in [simp]:
  fixes A :: "nat set"
  assumes "finite A"
  shows "Inf(- A) \<notin> A"
  by (metis ComplD ComplI Inf_nat_def assms ex_new_if_finite infinite_UNIV wellorder_Least_lemma(1))

lemma [simp]: "\<D>(\<guillemotleft>Some v\<guillemotright>) = true"
  by (rel_auto)

lemma "vwb_lens x \<Longrightarrow> (x := alloc(\<guillemotleft>u\<guillemotright>) ;; *x :=\<^sub>\<D> \<guillemotleft>Some v\<guillemotright>) = (x := alloc(\<guillemotleft>v\<guillemotright>))"  
  by (ndes_simp, rel_auto)

lemma "dealloc(e) ;; dealloc(e) = \<bottom>\<^sub>D"
  by (ndes_simp, rel_auto)

lemma "vwb_lens x \<Longrightarrow> dealloc(&x) ;; *x :=\<^sub>\<D> \<guillemotleft>v\<guillemotright> = \<bottom>\<^sub>D"
  by (ndes_simp, rel_auto)

lemma "vwb_lens x \<Longrightarrow> (x := alloc(\<guillemotleft>5 :: int\<guillemotright>) ;; dealloc(&x) ;; str:x :=\<^sub>D 0) = str:x :=\<^sub>D 0"
  apply (ndes_simp, rel_auto)
  apply (rename_tac ok hp st ok')
  apply (rule_tac x="hp(Inf(- fdom(hp)) \<mapsto> to_nat_bij 5)\<^sub>f" in exI)
  apply (rule_tac x="put\<^bsub>x\<^esub> st (\<Squnion>(- fdom(hp)))" in exI, simp)
  apply (auto)
  done

end
  