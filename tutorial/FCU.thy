theory FCU
imports "../theories/utp_csp"
begin
 
text {*
  The room has a temperature, and then it has three HVAC inputs: 
  the Air Handling Unit that feeds the central air duct system,
  and two Fan Coil Units that provide direct heating or cooling
  to this room using centrally supplied hot or cold water.
  It also interacts with the surrounding air in the Atrium,
  and only one temperature for that is modelled here, although
  it is instrumented at multiple points around the workroom.
*}
  
datatype ev_room = 
  env "real * real * real * real" | meas real
  
alphabet st_room =
  temp :: real
(*
  AHU\<^sub>t :: real
  FCU1\<^sub>t :: real
  FCU2\<^sub>t :: real
  Atrium\<^sub>t :: real
*)  

definition ldb :: "st_room upred" where
[urel_defs]: "ldb \<equiv> &temp <\<^sub>u 18"
definition udb :: "st_room upred" where
[urel_defs]: "udb \<equiv> &temp >\<^sub>u 22"
definition pasdb :: "st_room upred" where
[urel_defs]: "pasdb \<equiv> &temp \<ge>\<^sub>u 18 \<and> &temp \<le>\<^sub>u 22"

definition \<alpha>\<^sub>p :: "real" where [upred_defs]: "\<alpha>\<^sub>p \<equiv> 1"  
definition \<alpha>\<^sub>h :: "real" where [upred_defs]: "\<alpha>\<^sub>h \<equiv> 1"  
definition \<alpha>\<^sub>c :: "real" where [upred_defs]: "\<alpha>\<^sub>c \<equiv> 1"  
  
definition \<beta>\<^sub>h :: "real" where [upred_defs]: "\<beta>\<^sub>h \<equiv> 1"  
definition \<beta>\<^sub>c :: "real" where [upred_defs]: "\<beta>\<^sub>c \<equiv> 1"  

type_synonym prog = "(st_room, ev_room) action"

term "&temp + 1"
  
definition passive_room :: "prog" where
  [urel_defs]:
  "passive_room \<equiv> env?(Atrium\<^sub>t)?(FCU1\<^sub>t)?(FCU2\<^sub>t)?(AHU\<^sub>t)
   \<^bold>\<rightarrow> temp :=\<^sub>C (&temp + \<guillemotleft>\<alpha>\<^sub>p\<guillemotright> * (\<guillemotleft>Atrium\<^sub>t\<guillemotright> - &temp))
   ;; meas!(&temp) \<^bold>\<rightarrow> Skip"

definition heating_room :: "prog" where
  [urel_defs]:
  "heating_room \<equiv> env?(Atrium\<^sub>t)?(FCU1\<^sub>t)?(FCU2\<^sub>t)?(AHU\<^sub>t)
   \<^bold>\<rightarrow> temp :=\<^sub>C (&temp + \<guillemotleft>\<alpha>\<^sub>h\<guillemotright> * (\<guillemotleft>Atrium\<^sub>t\<guillemotright> - &temp) + \<guillemotleft>\<beta>\<^sub>h\<guillemotright> * (\<guillemotleft>AHU\<^sub>t\<guillemotright> - &temp))
   ;; meas!(&temp) \<^bold>\<rightarrow> Skip"

definition cooling_room :: "prog" where
  [urel_defs]:
  "cooling_room \<equiv> env?(Atrium\<^sub>t)?(FCU1\<^sub>t)?(FCU2\<^sub>t)?(AHU\<^sub>t)
   \<^bold>\<rightarrow> temp :=\<^sub>C (&temp + \<guillemotleft>\<alpha>\<^sub>c\<guillemotright> * (\<guillemotleft>Atrium\<^sub>t\<guillemotright> - &temp) + \<guillemotleft>\<beta>\<^sub>c\<guillemotright> * (\<guillemotleft>AHU\<^sub>t\<guillemotright> - &temp))
   ;; meas!(&temp) \<^bold>\<rightarrow> Skip"
        
abbreviation 
  "DoControl \<equiv> (cooling_room \<triangleleft> udb \<triangleright>\<^sub>R (heating_room \<triangleleft> ldb \<triangleright>\<^sub>R passive_room))"
    
definition Control :: "prog" 
  where [urel_defs]: 
    "Control \<equiv> (\<mu> C \<bullet> DoControl ;; CSP(C))"
  
lemmas room_defs = cooling_room_def heating_room_def passive_room_def Control_def
  
lemma preR_cooling_room [rdes]: "pre\<^sub>R(cooling_room) = true"
  by (simp add: cooling_room_def, rdes_calc)
    
lemma periR_cooling_room: 
  "peri\<^sub>R(cooling_room) = 
  ((\<Squnion> v \<bullet> (env\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute>) \<and> $tr\<acute> =\<^sub>u $tr \<or> 
   (\<Sqinter> (r,f1,f2,a) \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>(env\<cdot>\<guillemotleft>(r,f1,f2,a)\<guillemotright>)\<^sub>u\<rangle> 
                  \<and> \<lceil>(meas\<cdot>(&temp + \<guillemotleft>\<alpha>\<^sub>c\<guillemotright>*(\<guillemotleft>r\<guillemotright>-&temp) + \<guillemotleft>\<beta>\<^sub>c\<guillemotright>*(\<guillemotleft>a\<guillemotright>-&temp)))\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>))"
  by (simp add: cooling_room_def, rdes_calc, rel_auto)

lemma postR_cooling_room: 
  "post\<^sub>R(cooling_room) = 
   (\<Sqinter> (r,f1,f2,a) \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>(env\<cdot>\<guillemotleft>(r,f1,f2,a)\<guillemotright>)\<^sub>u, \<lceil>(meas\<cdot>(&temp + \<guillemotleft>\<alpha>\<^sub>c\<guillemotright>*(\<guillemotleft>r\<guillemotright>-&temp) + \<guillemotleft>\<beta>\<^sub>c\<guillemotright>*(\<guillemotleft>a\<guillemotright>-&temp)))\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> 
                  \<and> \<lceil>temp := (&temp + \<guillemotleft>\<alpha>\<^sub>c\<guillemotright> * (\<guillemotleft>r\<guillemotright> - &temp) + \<guillemotleft>\<beta>\<^sub>c\<guillemotright> * (\<guillemotleft>a\<guillemotright> - &temp))\<rceil>\<^sub>S)"
  by (simp add: cooling_room_def, rdes_calc, rel_auto)
    
lemma preR_heating_room [rdes]: "pre\<^sub>R(heating_room) = true"
  by (simp add: heating_room_def, rdes_calc)

lemma periR_heating_room: 
  "peri\<^sub>R(heating_room) = 
  ((\<Squnion> v \<bullet> (env\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute>) \<and> $tr\<acute> =\<^sub>u $tr \<or> 
   (\<Sqinter> (r,f1,f2,a) \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>(env\<cdot>\<guillemotleft>(r,f1,f2,a)\<guillemotright>)\<^sub>u\<rangle> 
                  \<and> \<lceil>(meas\<cdot>(&temp + \<guillemotleft>\<alpha>\<^sub>h\<guillemotright>*(\<guillemotleft>r\<guillemotright>-&temp) + \<guillemotleft>\<beta>\<^sub>h\<guillemotright>*(\<guillemotleft>a\<guillemotright>-&temp)))\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>))"
  by (simp add: heating_room_def, rdes_calc, rel_auto)

lemma postR_heating_room: 
  "post\<^sub>R(heating_room) = 
   (\<Sqinter> (r,f1,f2,a) \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>(env\<cdot>\<guillemotleft>(r,f1,f2,a)\<guillemotright>)\<^sub>u, \<lceil>(meas\<cdot>(&temp + \<guillemotleft>\<alpha>\<^sub>h\<guillemotright>*(\<guillemotleft>r\<guillemotright>-&temp) + \<guillemotleft>\<beta>\<^sub>h\<guillemotright>*(\<guillemotleft>a\<guillemotright>-&temp)))\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> 
                  \<and> \<lceil>temp := (&temp + \<guillemotleft>\<alpha>\<^sub>h\<guillemotright> * (\<guillemotleft>r\<guillemotright> - &temp) + \<guillemotleft>\<beta>\<^sub>h\<guillemotright> * (\<guillemotleft>a\<guillemotright> - &temp))\<rceil>\<^sub>S)"
  by (simp add: heating_room_def, rdes_calc, rel_auto)
    
lemma preR_passive_room [rdes]: "pre\<^sub>R(passive_room) = true"
  by (simp add: passive_room_def, rdes_calc)

lemma periR_passive_room: 
  "peri\<^sub>R(passive_room) = 
  ((\<Squnion> v \<bullet> (env\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute>) \<and> $tr\<acute> =\<^sub>u $tr \<or> 
   (\<Sqinter> (r,f1,f2,a) \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>(env\<cdot>\<guillemotleft>(r,f1,f2,a)\<guillemotright>)\<^sub>u\<rangle> 
                  \<and> \<lceil>(meas\<cdot>(&temp + \<guillemotleft>\<alpha>\<^sub>p\<guillemotright>*(\<guillemotleft>r\<guillemotright>-&temp)))\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>))"
  by (simp add: passive_room_def, rdes_calc, rel_auto)

lemma postR_passive_room: 
  "post\<^sub>R(passive_room) = 
   (\<Sqinter> (r,f1,f2,a) \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>(env\<cdot>\<guillemotleft>(r,f1,f2,a)\<guillemotright>)\<^sub>u, \<lceil>(meas\<cdot>(&temp + \<guillemotleft>\<alpha>\<^sub>p\<guillemotright>*(\<guillemotleft>r\<guillemotright>-&temp)))\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> 
                  \<and> \<lceil>temp := (&temp + \<guillemotleft>\<alpha>\<^sub>p\<guillemotright> * (\<guillemotleft>r\<guillemotright> - &temp))\<rceil>\<^sub>S)"
  by (simp add: passive_room_def, rdes_calc, rel_auto)
          
lemma DoControl_NCSP [closure]: "DoControl is NCSP"
  by (simp add: room_defs closure prod.case_eq_if)
    
lemma DoControl_Productive [closure]: "DoControl is Productive"
  by (simp add: room_defs closure prod.case_eq_if)    
    
lemma Control_NCSP [closure]: "Control is NSRD"
  by (simp add: Control_def closure)
    
lemma postR_Control [rdes]: "post\<^sub>R(Control) = false"
  by (simp add: Control_def rdes closure wp)
  
lemma control_never_terminates: 
  "X is NCSP \<Longrightarrow> Control ;; X \<equiv> Control"
  by (simp_all add: NSRD_seq_post_false closure rdes)
    
abbreviation "ExampleControl \<equiv> (temp :=\<^sub>C 20 ;; Control)"
  
lemma prop1:
  "[&temp <\<^sub>u 22 \<turnstile> true | (\<^bold>\<forall> (r,f1,f2,a,t) \<bullet> (\<guillemotleft>trace\<guillemotright> =\<^sub>u \<langle>\<guillemotleft>env(r,f1,f2,a)\<guillemotright>,\<guillemotleft>meas(t)\<guillemotright>\<rangle>) \<and> \<guillemotleft>r\<guillemotright> <\<^sub>u 30 \<and> \<guillemotleft>a\<guillemotright> <\<^sub>u 15 \<Rightarrow> \<guillemotleft>t\<guillemotright> <\<^sub>u 22)]\<^sub>R
   \<sqsubseteq> DoControl"
  -- {* Apply contract refinement introduction law *}
  apply (rule RD_contract_refine)
  -- {* Prove well-formedness of DoControl *}
  apply (simp add: closure unrest rdes alpha usubst)
  -- {* Precondition proviso (trivial) *}
  apply (simp add: closure unrest rdes alpha usubst)
  -- {* Pericondition proviso (trivial) *}    
  apply (simp add: closure unrest rdes alpha usubst)
  -- {* Postcondition proviso (not trivial) *}

  -- {* Simplify and distribute $temp < 22$ throughout disjunction *}
  apply (simp add: closure unrest rdes alpha usubst conj_disj_distr)
  -- {* Break down refinement into the three scenarios (cooling, heating, passive) *}
  apply (auto intro!: impl_disjI)

  -- {* Cooling -- trivial *}  
  apply (simp add: closure unrest rdes alpha usubst udb_def postR_cooling_room)
  apply (rel_auto)
    
  -- {* Heating -- not true *}    
  apply (simp add: closure unrest rdes alpha usubst udb_def ldb_def postR_heating_room)    

  -- {* rel_simp simplifies down to a pure HOL predicate we need to prove, but it isn't true *}
  apply (rel_simp)
  
  -- {* Unfortunately it seems nitpick can't handle real numbers. Actually a = 23, ac = 0, temp = 0 will do *}
  nitpick
oops
  
end