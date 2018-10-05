section {* Simple UTP Test *}
  
theory utp_hello_world
  imports "UTP.utp_easy_parser"
begin
  
text {* Create a basic state space with one variable *}
  
alphabet state =
  x :: int

text {* Prove a simple relational equality *}
  
theorem hello_world: "(x := 1 ;; x := x + 2) = (x := 3)"
  by (rel_auto)

end