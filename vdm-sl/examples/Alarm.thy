section {* Encoding of the Alarm example in Isabelle/UTP *}

theory Alarm
  imports "../VDM"
begin

type_synonym Period = real
type_synonym Expert = real

alphabet Plant = vlocal +
  staff    :: "Expert set"
  schedule :: "Period \<rightharpoonup> Expert set"

declare Plant.defs [simp]

abbreviation "mk_Plant \<equiv> vuop (bpfun' Plant.make)"

abbreviation 
  "inv_Plant \<equiv> (\<Union>\<^sub>v (rng\<^sub>v(&\<^sub>vschedule)) \<subseteq>\<^sub>v &\<^sub>vstaff \<and>\<^sub>v (\<forall>\<^sub>v exs \<in> rng\<^sub>v(&\<^sub>vschedule) \<bullet> \<guillemotleft>exs\<guillemotright>\<^sub>v <>\<^sub>v {}\<^sub>v))"

abbreviation
  "init_Plant \<equiv> (staff :=\<^sub>v {}\<^sub>v ;; schedule :=\<^sub>v \<lbrace>\<mapsto>\<rbrace>\<^sub>v)"

text {* init_Plant establishes the invariant *}

lemma init_Plant_est: "(true \<turnstile>\<^sub>r \<lceil> \<lfloor> inv_Plant \<rfloor>\<^sub>v \<rceil>\<^sub>>) \<sqsubseteq> init_Plant"
  by (rel_auto, simp add: ran_def)

abbreviation
  "addExpert \<equiv> val e :: Expert \<bullet>\<^sub>D [pre &\<^sub>ve \<notin>\<^sub>v &\<^sub>vstaff post true\<^sub>v body staff :=\<^sub>v &\<^sub>vstaff \<union>\<^sub>v {&\<^sub>ve}\<^sub>v]\<^sub>v"

abbreviation
  "Assign \<equiv> val e :: Expert, val p :: Period \<bullet>\<^sub>D 
              [pre (&\<^sub>ve \<in>\<^sub>v &\<^sub>vstaff \<and>\<^sub>v &\<^sub>vp \<in>\<^sub>v dom\<^sub>v(&\<^sub>vschedule))
               post $\<^sub>ve\<acute> \<in>\<^sub>v $\<^sub>vschedule\<acute>($\<^sub>vp)\<^sub>v
               body schedule(&\<^sub>vp) :=\<^sub>v ({&\<^sub>ve}\<^sub>v \<union>\<^sub>v (&\<^sub>vschedule(&\<^sub>vp)\<^sub>v))]\<^sub>v"

lemma Assign_pres_inv:
  "Assign(e,p) \<sqsubseteq> \<lfloor> inv_Plant \<rfloor>\<^sub>v \<turnstile>\<^sub>n \<lceil> \<lfloor> inv_Plant \<rfloor>\<^sub>v \<rceil>\<^sub>>"
  oops

lemma "(\<lfloor> inv_Plant \<and>\<^sub>v \<guillemotleft>p\<guillemotright>\<^sub>v \<in>\<^sub>v dom\<^sub>v(&\<^sub>vschedule) \<rfloor>\<^sub>v \<turnstile>\<^sub>n \<lceil> \<lfloor> inv_Plant \<rfloor>\<^sub>v \<rceil>\<^sub>>)
       \<sqsubseteq> (schedule(\<guillemotleft>p\<guillemotright>\<^sub>v) :=\<^sub>v ({\<guillemotleft>e\<guillemotright>\<^sub>v}\<^sub>v \<union>\<^sub>v (&\<^sub>vschedule(\<guillemotleft>p\<guillemotright>\<^sub>v)\<^sub>v)))"
   apply (simp add: vassign_uvar_def)
   apply (rule ndesign_refine_intro)
   apply (pred_auto)
oops

end
