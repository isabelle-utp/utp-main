section \<open> Channel Types \<close>

theory Channel_Type
  imports Prisms
  keywords "chantype" :: "thy_defn"
begin

text \<open> A channel type is a simplified algebraic datatype where each constructor has exactly 
  one parameter, and it is wrapped up as a prism. It a dual of an alphabet type. \<close>

definition ctor_prism :: "('a \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('a \<Longrightarrow>\<^sub>\<triangle> 'd)" where
[lens_defs]: 
"ctor_prism ctor disc sel = \<lparr> prism_match = (\<lambda> d. if (disc d) then Some (sel d) else None)
                            , prism_build = ctor \<rparr>"

lemma wb_ctor_prism_intro:
  assumes 
    "\<And> v. disc (ctor v)" 
    "\<And> v. sel (ctor v) = v"
    "\<And> s. disc s \<Longrightarrow> ctor (sel s) = s"
  shows "wb_prism (ctor_prism ctor disc sel)"
  by (unfold_locales, simp_all add: lens_defs assms)
     (metis assms(3) option.distinct(1) option.sel)

lemma ctor_codep_intro:
  assumes "\<And> x y. ctor1 x \<noteq> ctor2 y"
  shows "ctor_prism ctor1 disc1 sel1 \<nabla> ctor_prism ctor2 disc2 sel2"
  by (rule prism_diff_intro, simp add: lens_defs assms)

ML_file "Channel_Type.ML"

end