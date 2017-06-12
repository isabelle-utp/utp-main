section {* Modelica Core *}

theory Modelica_Core
imports "../hybrid/utp_hrd"
begin

abbreviation ModelicaBlock ("[_ | _]\<^sub>M") where
"[P | Q]\<^sub>M \<equiv> \<^bold>R\<^sub>s(P \<turnstile> ($tr <\<^sub>u $tr\<acute> \<and> Q) \<diamondop> false)"
  
end
