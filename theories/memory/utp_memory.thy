section \<open> Programs with memory \<close>

theory utp_memory
  imports "UTP-Designs.utp_designs"
begin

text \<open> For now we represent addresses and data as naturals. We can therefore inject
  countable data structures into our memory model. \<close>

type_synonym addr = nat
type_synonym data = nat

text \<open> As usual, the memory consists of the store and the heap. The store is an abstract
  type, and will usually be another alphabet. The heap is modelled as a finite function
  from addresses to data. \<close>

alphabet 's mem =
  st :: "'s"
  hp :: "(addr, data) ffun"

text \<open> We define an order on memory by lifting of the containment order on finite functions. \<close>

instantiation mem_ext :: (type, type) order
begin
  definition less_eq_mem_ext :: "('a, 'b) mem_scheme \<Rightarrow> ('a, 'b) mem_scheme \<Rightarrow> bool" where
  [upred_defs]: "less_eq_mem_ext x y = (st\<^sub>v x = st\<^sub>v y \<and> mem.more x = mem.more y \<and> hp\<^sub>v x \<le> hp\<^sub>v y)"

  definition less_mem_ext :: "('a, 'b) mem_scheme \<Rightarrow> ('a, 'b) mem_scheme \<Rightarrow> bool" where
  [upred_defs]: "less_mem_ext x y = (st\<^sub>v x = st\<^sub>v y \<and> mem.more x = mem.more y \<and> hp\<^sub>v x < hp\<^sub>v y)"

  instance by (intro_classes, (rel_auto)+)
end

text \<open> A program is simply a homogeneous design with a memory state space. \<close>

type_synonym 's sprog = "'s mem hrel_des"

text \<open> An abort is currently just the empty relation. In future we could use the theory
  of designs instead and model aborts differently. \<close>

abbreviation abort_mp :: "'s sprog" ("abort") where
"abort \<equiv> true"

text \<open> Heap allocation takes a lens $x$ within the store that holds an address, and an expression
  $e$ over store variables whose return type is countable. The semantics of allocation selects
  an arbitrary memory location not currently allocated in the heap, places the said address
  in $x$, and injects the expression $e$ into the heap at this memory location. \<close>

definition
  heap_alloc :: "(addr \<Longrightarrow> 's) \<Rightarrow> ('a::countable, 's) uexpr \<Rightarrow> 's sprog"
  ("_ := alloc'(_')" [74,0] 75) 
  where [upred_defs, ndes_simp]: 
    "x := alloc(e) = 
     (true \<turnstile>\<^sub>n (\<Sqinter> l | \<guillemotleft>l\<guillemotright> \<notin>\<^sub>u dom\<^sub>u($hp) \<bullet> st:x := \<guillemotleft>l\<guillemotright> ;; hp := &hp(&st:x \<mapsto> uop to_nat (e \<oplus>\<^sub>p st))\<^sub>u))"

text \<open> Heap lookup retrieves data from the heap and places it into a store variable. If the memory
  location $l$ is unallocated then an abort is the result. \<close>

definition 
  heap_lookup :: "('a::countable \<Longrightarrow> 's) \<Rightarrow> (addr, 's) uexpr \<Rightarrow> 's sprog" 
  ("_ := *_" [74,75] 75)
  where [upred_defs, ndes_simp]: 
    "x := *l = (((l \<oplus>\<^sub>p st) \<in>\<^sub>u dom\<^sub>u(&hp)) \<turnstile>\<^sub>n st:x := uop from_nat (&hp(l \<oplus>\<^sub>p st)\<^sub>a))"

text \<open> Heap mutation updates the value of an already allocated address in the heap. \<close>

definition
  heap_mutate :: "(addr, 's) uexpr \<Rightarrow> ('a::countable, 's) uexpr \<Rightarrow> 's sprog"
  ("*_ := _" [0, 74] 75)
  where [upred_defs, ndes_simp]:
    "*l := e = (((l \<oplus>\<^sub>p st) \<in>\<^sub>u dom\<^sub>u(&hp)) \<turnstile>\<^sub>n hp := &hp((l \<oplus>\<^sub>p st) \<mapsto> uop to_nat (e \<oplus>\<^sub>p st))\<^sub>u)"

text \<open> Heap deallocation removes an area of memory from the heap. \<close>

definition
  heap_dealloc :: "(addr, 's) uexpr \<Rightarrow> 's sprog" ("dealloc'(_')")
  where [upred_defs, ndes_simp]:
  "dealloc(l) = (((l \<oplus>\<^sub>p st) \<in>\<^sub>u dom\<^sub>u(&hp)) \<turnstile>\<^sub>n hp := (dom\<^sub>u(&hp) - {l \<oplus>\<^sub>p st}\<^sub>u) \<lhd>\<^sub>u &hp)"

subsection \<open> Weakest Precondition Semantics \<close>

lemma wp_UINF_pred [wp]:
  "\<lbrakk> \<And> l. out\<alpha> \<sharp> P(l) \<rbrakk> \<Longrightarrow> (\<Sqinter> l | P(l) \<bullet> Q(l)) wp q = (\<^bold>\<forall> l \<bullet> \<lfloor>P(l)\<rfloor>\<^sub>< \<Rightarrow> (Q(l) wp q))"
  by (rel_blast)

lemma wp_heap_alloc [wp]:
  "\<lbrakk> vwb_lens x; x \<sharp> e \<rbrakk> \<Longrightarrow> 
   x := alloc(e) wp\<^sub>D p = (\<^bold>\<forall> l \<in> -dom\<^sub>u(&hp) \<bullet> p\<lbrakk>\<guillemotleft>l\<guillemotright>,&hp(\<guillemotleft>l\<guillemotright> \<mapsto> uop to_nat (e \<oplus>\<^sub>p st))\<^sub>u/&st:x,&hp\<rbrakk>)"
  by (simp add: ndes_simp wp usubst unrest, rel_auto)

lemma wp_heap_dealloc [wp]: 
  "dealloc(e) wp\<^sub>D p = (e \<oplus>\<^sub>p st \<in>\<^sub>u dom\<^sub>u(&hp) \<and> p\<lbrakk>(dom\<^sub>u(&hp) - {e \<oplus>\<^sub>p st}\<^sub>u) \<lhd>\<^sub>u &hp/&hp\<rbrakk>)"
  by (rel_auto)

subsection \<open> Example properties \<close>

lemma least_nat_Compl_not_in [simp]:
  fixes A :: "nat set"
  assumes "finite A"
  shows "Inf(- A) \<notin> A"
  by (metis ComplD ComplI Inf_nat_def assms ex_new_if_finite infinite_UNIV wellorder_Least_lemma(1))

lemma "(x := alloc(\<guillemotleft>u\<guillemotright>) ;; *&x := \<guillemotleft>v\<guillemotright>) = (x := alloc(\<guillemotleft>v\<guillemotright>))"  
  by (rel_auto, fastforce)

lemma "dealloc(e) ;; dealloc(e) = abort"
  by (ndes_simp, rel_auto)

lemma "dealloc(e) ;; *e := \<guillemotleft>v\<guillemotright> = abort"
  by (ndes_simp, rel_auto)

lemma "vwb_lens x \<Longrightarrow> (x := alloc(\<guillemotleft>5 :: int\<guillemotright>) ;; dealloc(&x) ;; st:x :=\<^sub>D 0) = st:x :=\<^sub>D 0"
  apply (ndes_simp, rel_auto)
  apply (rename_tac ok st hp ok')
  apply (rule_tac x="put\<^bsub>x\<^esub> st (\<Squnion>(- fdom(hp)))" in exI, simp)
  apply (rule_tac x="hp(Inf(- fdom(hp)) \<mapsto> to_nat 5)\<^sub>f" in exI)
  apply (auto)
  done

end
  