section \<open> Examples using Prisms \<close>

theory Prisms_Examples
  imports Prisms
begin

text \<open> We demonstrate prisms for manipulating an algebraic data type with three constructors . \<close>

datatype D = A int | B string | C bool

fun fromA :: "D \<Rightarrow> int option" where "fromA (A x) = Some x" | "fromA _ = None"
fun fromB :: "D \<Rightarrow> string option" where "fromB (B x) = Some x" | "fromB _ = None"
fun fromC :: "D \<Rightarrow> bool option" where "fromC (C x) = Some x" | "fromC _ = None"

text \<open> We create a prism for each of the three constructors. \<close>

definition A\<^sub>_prism :: "int \<Longrightarrow>\<^sub>\<triangle> D" ("A\<^sub>\<triangle>") where
[lens_defs]: "A\<^sub>\<triangle> = \<lparr> prism_match = fromA, prism_build = A \<rparr>"

definition B_prism :: "string \<Longrightarrow>\<^sub>\<triangle> D" ("B\<^sub>\<triangle>") where
[lens_defs]: "B\<^sub>\<triangle> = \<lparr> prism_match = fromB, prism_build = B \<rparr>"

definition C_prism :: "bool \<Longrightarrow>\<^sub>\<triangle> D" ("C\<^sub>\<triangle>") where
[lens_defs]: "C\<^sub>\<triangle> = \<lparr> prism_match = fromC, prism_build = C \<rparr>"

text \<open> All three are well-behaved. \<close>

lemma A_wb_prism [simp]: "wb_prism A\<^sub>\<triangle>"
  using fromA.elims by (unfold_locales, auto simp add: lens_defs)

lemma B_wb_prism [simp]: "wb_prism B\<^sub>\<triangle>"
  using fromB.elims by (unfold_locales, auto simp add: lens_defs)

lemma C_wb_prism [simp]: "wb_prism C\<^sub>\<triangle>"
  using fromC.elims by (unfold_locales, auto simp add: lens_defs)

text \<open> All three prisms are codependent with each other. \<close>

lemma D_codeps: "A\<^sub>\<triangle> \<nabla> B\<^sub>\<triangle>" "A\<^sub>\<triangle> \<nabla> C\<^sub>\<triangle>" "B\<^sub>\<triangle> \<nabla> C\<^sub>\<triangle>"
  by (rule prism_diff_intro, simp add: lens_defs)+

end