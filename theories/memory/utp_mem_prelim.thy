theory utp_mem_prelim
  imports "UTP-Designs.utp_designs"
begin

text \<open> As usual, the memory consists of the store and the heap. The store is an abstract
  type, and will usually be another alphabet. \<close>

alphabet ('s, 'h) mem =
  st :: "'s"
  hp :: "'h"

text \<open> We define an order on memory by lifting of the containment order on finite functions. \<close>

instantiation mem_ext :: (type, order, type) order
begin
  definition less_eq_mem_ext :: "('a, 'b, 'c) mem_scheme \<Rightarrow> ('a, 'b, 'c) mem_scheme \<Rightarrow> bool" where
  [upred_defs]: "less_eq_mem_ext x y = (st\<^sub>v x = st\<^sub>v y \<and> mem.more x = mem.more y \<and> hp\<^sub>v x \<le> hp\<^sub>v y)"

  definition less_mem_ext :: "('a, 'b, 'c) mem_scheme \<Rightarrow> ('a, 'b, 'c) mem_scheme \<Rightarrow> bool" where
  [upred_defs]: "less_mem_ext x y = (st\<^sub>v x = st\<^sub>v y \<and> mem.more x = mem.more y \<and> hp\<^sub>v x < hp\<^sub>v y)"

  instance by (intro_classes, (rel_auto)+)
end

text \<open> We set up some useful syntax \<close>

syntax
  "_ucompat" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "##\<^sub>u" 60)

translations
  "f ##\<^sub>u g" == "CONST bop (op ##) f g"

type_synonym ('s, 'h) spred = "('s, 'h) mem upred"
type_synonym ('s, 'h) sprog = "('s, 'h) mem hrel_des"

type_synonym 's mpred = "('s, (nat, nat) ffun) spred"
type_synonym 's mprog = "('s, (nat, nat) ffun) sprog"

end