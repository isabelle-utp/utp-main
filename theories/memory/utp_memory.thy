section \<open> Programs with memory \<close>

theory utp_memory
  imports "UTP.utp"
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

text \<open> A program is simply a homogeneous relation with a memory state space. \<close>

type_synonym 's sprog = "'s mem hrel"

text \<open> An abort is currently just the empty relation. In future we could use the theory
  of designs instead and model aborts differently. \<close>

abbreviation abort_mp :: "'s sprog" ("abort") where
"abort \<equiv> false"

text \<open> Heap allocation takes a lens $x$ within the store that holds an address, and an expression
  $e$ over store variables whose return type is countable. The semantics of allocation selects
  an arbitrary memory location not currently allocated in the heap, places the said address
  in $x$, and injects the expression $e$ into the heap at this memory location. \<close>

definition
  heap_alloc :: "(addr \<Longrightarrow> 's) \<Rightarrow> ('a::countable, 's) uexpr \<Rightarrow> 's sprog"
  ("_ := alloc'(_')" [74,0] 75) 
  where [upred_defs]: 
    "x := alloc(e) = 
     (\<Sqinter> l | \<guillemotleft>l\<guillemotright> \<notin>\<^sub>u dom\<^sub>u($hp) \<bullet> st:x := \<guillemotleft>l\<guillemotright> ;; hp := &hp(&st:x \<mapsto> uop to_nat (e \<oplus>\<^sub>p st))\<^sub>u)"

text \<open> Heap lookup retrieves data from the heap and places it into a store variable. If the memory
  location $l$ is unallocated then an abort is the result. \<close>

definition 
  heap_lookup :: "('a::countable \<Longrightarrow> 's) \<Rightarrow> (addr, 's) uexpr \<Rightarrow> 's mem hrel" 
  ("_ := *_" [74,75] 75)
  where [upred_defs]: 
    "x := *l = (\<lceil>(l \<oplus>\<^sub>p st) \<in>\<^sub>u dom\<^sub>u(&hp)\<rceil>\<^sub>< \<and> st:x := uop from_nat (&hp(l \<oplus>\<^sub>p st)\<^sub>a))"

text \<open> Heap mutation updates the value of an already allocated address in the heap. \<close>

definition
  heap_mutate :: "(addr, 's) uexpr \<Rightarrow> ('a::countable, 's) uexpr \<Rightarrow> 's mem hrel"
  ("*_ := _" [0, 74] 75)
  where [upred_defs]:
    "*l := e = (\<lceil>(l \<oplus>\<^sub>p st) \<in>\<^sub>u dom\<^sub>u(&hp)\<rceil>\<^sub>< \<and> hp := &hp((l \<oplus>\<^sub>p st) \<mapsto> uop to_nat (e \<oplus>\<^sub>p st))\<^sub>u)"

text \<open> Heap deallocation removes an area of memory from the heap. \<close>

definition
  heap_dealloc :: "(addr, 's) uexpr \<Rightarrow> 's mem hrel" ("dealloc'(_')")
  where [upred_defs]:
  "dealloc(l) = (\<lceil>(l \<oplus>\<^sub>p st) \<in>\<^sub>u dom\<^sub>u(&hp)\<rceil>\<^sub>< \<and> hp := (dom\<^sub>u(&hp) - {l \<oplus>\<^sub>p st}\<^sub>u) \<lhd>\<^sub>u &hp)"

text \<open> Some example properties \<close>

lemma least_nat_Compl_not_in [simp]:
  fixes A :: "nat set"
  assumes "finite A"
  shows "Inf(- A) \<notin> A"
  by (metis ComplD ComplI Inf_nat_def assms ex_new_if_finite infinite_UNIV wellorder_Least_lemma(1))

lemma "(x := alloc(\<guillemotleft>u\<guillemotright>) ;; *&x := \<guillemotleft>v\<guillemotright>) = (x := alloc(\<guillemotleft>v\<guillemotright>))"
  by (rel_auto)

lemma "dealloc(e) ;; dealloc(e) = abort"
  by (rel_auto)

lemma "dealloc(e) ;; *e := \<guillemotleft>v\<guillemotright> = abort"
  by (rel_auto)

lemma "vwb_lens x \<Longrightarrow> (x := alloc(\<guillemotleft>5 :: int\<guillemotright>) ;; dealloc(&x) ;; st:x := 0) = st:x := 0"
  apply (rel_auto)
  apply (rename_tac st hp)
  apply (rule_tac x="put\<^bsub>x\<^esub> st (\<Squnion>(- fdom(hp)))" in exI, simp)
  apply (rule_tac x="hp(Inf(- fdom(hp)) \<mapsto> to_nat 5)\<^sub>f" in exI)
  apply (auto)
  done

end
  