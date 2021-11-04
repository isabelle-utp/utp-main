(* Copyright 2021 (C) Manuel Eberl *)

section\<open>Mutliway If\<close>
theory CZH_Sets_MIF
  imports Main
begin

text\<open>
The code that is presented in this section was originally written 
by Manuel Eberl and appeared in a post on the mailing list of Isabelle:
\cite{eberl_syntax_2021}.
The code was ported with minor amendments by the author of this work.
\<close>

abbreviation multi_If :: "bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "multi_If \<equiv> If"

nonterminal if_clauses and if_clause

syntax
  "_if_block" :: "if_clauses \<Rightarrow> 'a" ("(1if _)" [12] 10)
  "_if_clause"  :: "bool \<Rightarrow> 'a \<Rightarrow> if_clause" ("(2_ \<Rightarrow>/ _)" 13)
  "_if_final" :: "'a \<Rightarrow> if_clauses" ("otherwise \<Rightarrow> _")
  "_if_cons" :: "[if_clause, if_clauses] \<Rightarrow> if_clauses" ("_ /| _" [13, 12] 12)

syntax (ASCII)
  "_if_clause" :: "[pttrn, 'a] \<Rightarrow> if_clause" ("(2_ =>/ _)" 13)

translations
  "_if_block (_if_cons (_if_clause b t) (_if_final e))"
    \<rightleftharpoons> "CONST multi_If b t e"
  "_if_block (_if_cons b (_if_cons c cs))"
    \<rightleftharpoons> "_if_block (_if_cons b (_if_final (_if_block (_if_cons c cs))))"
  "_if_block (_if_final e)" \<rightharpoonup> "e"

text\<open>\newpage\<close>

end