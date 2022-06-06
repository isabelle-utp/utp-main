section {* Refinement Calculus Examples *}

theory utp_rcalc_ex
  imports "../utp_rcalc"
begin

subsection {* Initial Setup -- Example State Space *}
  
alphabet exstate =
  x :: int
  y :: int
  z :: int
  
text {* The examples in the section are taken from Carol Morgan's "Programming from Specifications". *}
  
subsection {* Examples from Figure 1.5 on p7 *}
  
term "&x:[true, &y\<^sup>2 =\<^sub>u &x]"

term "&x:[&x \<ge>\<^sub>u 0, &y\<^sup>2 =\<^sub>u &x]"

term "&e:[&s \<noteq>\<^sub>u {}\<^sub>u, &e \<in>\<^sub>u &s]"

term "&x:[&b\<^sup>2 \<ge>\<^sub>u 4*&a*&c, &a*&x\<^sup>2 + &b*&x + &c =\<^sub>u 0]"

subsection {* Exercise 1.4, first 4 questions *}
  
lemma "&x:[true, &x \<ge>\<^sub>u 0] \<sqsubseteq> &x:[true, &x =\<^sub>u 0]"
  by (prefine)
  
lemma "&x:[&x \<ge>\<^sub>u 0, true] \<sqsubseteq> &x:[&x =\<^sub>u 0, true]"
  apply (prefine)
  nitpick
  oops

lemma "&x:[&x \<ge>\<^sub>u 0, &x =\<^sub>u 0] \<sqsubseteq> &x:[&x =\<^sub>u 0, &x \<ge>\<^sub>u 0]"
  apply (prefine)
  nitpick
  oops
    
lemma "&x:[&x =\<^sub>u 0, &x \<ge>\<^sub>u 0] \<sqsubseteq> &x:[&x \<ge>\<^sub>u 0, &x =\<^sub>u 0]"
  by (prefine) 
  
end