section {* Mini-mondex example *}

theory utp_csp_mini_mondex
  imports "../theories/utp_csp"
begin

type_synonym index = nat
type_synonym money = int
  
alphabet st_mdx =
  valueseq :: "money list"
  
datatype ch_mdx = 
  pay "index \<times> index \<times> money" |
  transfer "index \<times> index \<times> money" |
  accept index |
  reject index
  
type_synonym action_mdx = "(st_mdx, ch_mdx) action"
  
definition Pay :: "index \<Rightarrow> index \<Rightarrow> money \<Rightarrow> action_mdx" where
"Pay i j n = 
  pay.(\<guillemotleft>i\<guillemotright>).(\<guillemotleft>j\<guillemotright>).(\<guillemotleft>n\<guillemotright>) \<^bold>\<rightarrow> 
    (reject.(\<guillemotleft>i\<guillemotright>) \<^bold>\<rightarrow> Skip) 
      \<triangleleft> \<guillemotleft>n\<guillemotright> >\<^sub>u &valueseq\<lparr>\<guillemotleft>i\<guillemotright>\<rparr>\<^sub>u \<triangleright>\<^sub>R 
    Skip"

definition Cycle :: "index \<Rightarrow> action_mdx" where
"Cycle cardNum = (\<mu> X \<bullet> (\<Sqinter> (i, j, n) | \<guillemotleft>i\<guillemotright> <\<^sub>u \<guillemotleft>cardNum\<guillemotright> \<and> \<guillemotleft>j\<guillemotright> <\<^sub>u \<guillemotleft>cardNum\<guillemotright> \<and> \<guillemotleft>i\<guillemotright> \<noteq>\<^sub>u \<guillemotleft>j\<guillemotright> \<bullet> Pay i j n) ;; X)"

definition Mondex :: "index \<Rightarrow> action_mdx" where
"Mondex(cardNum) = (valueseq :=\<^sub>C \<guillemotleft>replicate cardNum 10\<guillemotright> ;; Cycle(cardNum))"
  
end