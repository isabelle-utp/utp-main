section \<open> Simple UTP Test \<close>
  
theory utp_hello_world
  imports "UTP.utp_easy_parser"
begin
  
text \<open> Create a basic state space with one variable \<close>
  
alphabet state =
  x :: int

text \<open> Prove a simple relational equality \<close>
  
theorem hello_world: "(x := 1 ;; x := x + 2) = (x := 3)"
  by (rel_auto)

end