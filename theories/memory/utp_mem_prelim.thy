theory utp_mem_prelim
  imports "UTP-Designs.utp_designs" "UTP.utp_full"
begin

text \<open> As usual, the memory consists of the store and the heap. The store is an abstract
  type, and will usually be another alphabet. \<close>

alphabet 'h mem =
  hp :: "'h"

abbreviation str :: "'s \<Longrightarrow> ('a :: sep_alg, 's) mem_ext" where
"str \<equiv> mem_child_lens"

text \<open> We define an order on memory by lifting of the containment order on finite functions. \<close>

instantiation mem_ext :: (order, type) order
begin
  definition less_eq_mem_ext :: "('a, 'b) mem_scheme \<Rightarrow> ('a, 'b) mem_scheme \<Rightarrow> bool" where
  [upred_defs]: "less_eq_mem_ext x y = (hp\<^sub>v x \<le> hp\<^sub>v y \<and> mem.more x = mem.more y)"

  definition less_mem_ext :: "('a, 'b) mem_scheme \<Rightarrow> ('a, 'b) mem_scheme \<Rightarrow> bool" where
  [upred_defs]: "less_mem_ext x y = (hp\<^sub>v x < hp\<^sub>v y \<and> mem.more x = mem.more y)"

  instance by (intro_classes, (rel_auto)+)
end

text \<open> We set up some useful syntax \<close>

syntax
  "_ucompat" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "##\<^sub>u" 60)

translations
  "f ##\<^sub>u g" == "CONST bop (##) f g"

type_synonym ('h, 's) spred = "('h, 's) mem_ext upred"
type_synonym ('h, 's) sprog = "('h, 's) mem_ext hrel_des"

type_synonym 's mpred = "((nat, nat) ffun, 's) spred"
type_synonym 's mprog = "((nat, nat) ffun, 's) sprog"

end