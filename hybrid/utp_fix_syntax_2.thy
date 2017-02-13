section {* Override HOL syntax *}

theory utp_fix_syntax_2
  imports
    "../utp/utp"
    "../contrib/Ordinary_Differential_Equations/ODE_Analysis"
    "../dynamics/Derivative_extra"
    "../dynamics/Timed_Traces"
begin

text {* In order to add more HOL theories to the UTP we need to override the syntax again. *}
  
no_notation 
  le (infixl "\<sqsubseteq>\<index>" 50) and
  asup ("\<Squnion>\<index>_" [90] 90) and
  ainf ("\<Sqinter>\<index>_" [90] 90) and
  conj (infixr "\<and>" 35) and
  disj (infixr "\<or>" 30) and
  Not ("\<not> _" [40] 40) and
  Not  ("~ _" [40] 40) and 
  BNF_Def.convol ("\<langle>(_,/ _)\<rangle>")
  
no_notation inf (infixl "\<sqinter>" 70)
notation inf (infixl "\<squnion>" 70)
no_notation sup (infixl "\<squnion>" 65)
notation sup (infixl "\<sqinter>" 65)

no_notation Inf ("\<Sqinter>_" [900] 900)
notation Inf ("\<Squnion>_" [900] 900)
no_notation Sup ("\<Squnion>_" [900] 900)
notation Sup ("\<Sqinter>_" [900] 900)

no_notation bot ("\<bottom>")
notation bot ("\<top>")
no_notation top ("\<top>")
notation top ("\<bottom>")

no_syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)

hide_type rel
  
end