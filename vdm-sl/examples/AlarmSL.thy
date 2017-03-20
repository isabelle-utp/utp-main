section {*Encoding of the AlarmSL example in Isabelle/UTP.*}

theory AlarmSL
  imports "../VDM"
begin

(*token vs real*)  
type_synonym ExpertId = real
type_synonym Period = real
datatype Qualification = Elec | Mech | Bio | Chem
  
record Expert = 
  expertid :: ExpertId
  quali :: "Qualification set"
  
definition inv_Expert :: "Expert \<Rightarrow> bool" where
  "inv_Expert expert = (Expert.quali expert \<noteq> {})"

definition ExpertSet :: "Expert set" where
  "ExpertSet = {expert . inv_Expert expert}"
  
type_synonym Schedule = "Period \<rightharpoonup> Expert set"
(* TODO: \<forall>ex1 \<in> exs . \<forall> ex2 \<in> exs vs \<forall>ex1,ex2 \<in> exs *)
definition inv_Schedule :: "Schedule \<Rightarrow> bool" where
  "inv_Schedule sch = 
    (\<forall> exs \<in> ran sch . 
      ((exs \<noteq> {}) \<and> 
      (\<forall>ex1 \<in> exs . 
        (\<forall>ex2\<in>exs .
         ((ex1 \<noteq> ex2) \<longrightarrow> ((Expert.expertid ex1) \<noteq> (Expert.expertid ex2)))))))"

(*Required to prove Schedule type invariant satisfiable*)
definition ScheduleSet :: "Schedule set" where
"ScheduleSet = {s . inv_Schedule s}"  
  
record Alarm = 
  alarmtext :: "char set"
  quali :: Qualification
  
record Plant = 
  schedule :: Schedule
  alarm :: "Alarm set"

definition QualificationOK :: "Expert set \<Rightarrow> Qualification \<Rightarrow> bool" where
  "QualificationOK exs reqquali = (\<exists> (ex::Expert) \<in> exs . reqquali \<in> (Expert.quali ex))"
  
(*TODO: Usage of "the"*)
definition inv_Plant :: "Plant \<Rightarrow> bool" where
  "inv_Plant pl = (\<forall> a \<in> (alarm pl) . \<forall>peri\<in>(dom (schedule pl)) 
      . QualificationOK (the ((schedule pl) peri)) (Alarm.quali a))"

(*Required to prove Plant type invariant satisfiable*)
definition PlantSet :: "Plant set" where
" PlantSet = {p . inv_Plant p}"
  
(*TODO: Usage of 'the'*)
(*definition NumberOfExperts :: "Period \<Rightarrow> Plant \<Rightarrow> nat" where
"NumberOfExperts peri plant = card (the ((schedule plant) peri))"*)

definition NumberOfExperts :: "Period option \<Rightarrow> Plant option \<Rightarrow> nat option" where
"NumberOfExperts peri plant = vcard ((schedule plant) peri)"

(*TODO: Pattern matching on records? e.g. VDM syntax: ExpertIsOnDuty(ex,mk_Plant(sch,-)) *)
(*TODO: Usage of 'the'*)
(*TODO: ex is keyword? *)
definition ExpertIsOnDuty :: "Expert \<Rightarrow> Plant \<Rightarrow> Period set" where
"ExpertIsOnDuty expert pl = {peri . peri \<in> (dom (Plant.schedule pl)) \<and> expert \<in> (the ((Plant.schedule pl) peri))}"

(*TODO: Implement ExpertToPage. Function without body, just write true*)

lemma Plant_legalMapApplication :
  "\<forall>pl\<in>PlantSet . \<forall>a\<in>(Plant.alarm pl) . \<forall>peri\<in>dom(Plant.schedule pl) . peri\<in>dom(Plant.schedule pl)"
  apply(simp add:PlantSet_def)
  done
    
lemma Plant_typeInvariantSatisfiable :
  "\<forall>pl\<in>PlantSet . \<forall>a\<in>(Plant.alarm pl) . \<forall>peri\<in>dom(Plant.schedule pl) . (QualificationOK (the ((Plant.schedule pl) peri)) (Alarm.quali a))"
  apply(simp add:PlantSet_def)
  apply(simp add:inv_Plant_def)
  done

(*TODO: Prove*)    
lemma Schedule_typeInvariantSatisfiable :
  "\<exists>sch \<in> ScheduleSet .
     (\<forall>exs \<in> ran sch .
      ((exs \<noteq> {}) \<and>
       (\<forall>ex1 \<in> exs .
         (\<forall>ex2 \<in> exs .
           ((ex1 \<noteq> ex2) \<longrightarrow> ((Expert.expertid ex1) \<noteq> (Expert.expertid ex2)))))))"
  apply(simp add:ScheduleSet_def)
  apply(simp add:inv_Schedule_def)
  oops
    
(*TODO: Prove*)
lemma Expert_typeInvariantSatisfiable : 
  "\<exists>expert\<in>ExpertSet . Expert.quali expert \<noteq> {}"
  apply(simp add: ExpertSet_def)
  apply(simp add: inv_Expert_def)
  oops    

lemma NumberOfExperts_legalMapApplication : 
  "\<forall>peri \<in> Period . \<forall>plant \<in> PlantSet . ((peri \<in> dom (Plant.schedule plant)) \<longrightarrow> (peri \<in> dom(Plant.schedule plant)))"
  apply(simp add: PlantSet_def)
  done

lemma ExpertIsOnDuty_legalMapApplication :
  "\<forall> ex\<in>ExpertSet . \<forall>plant\<in>PlantSet . \<forall>peri\<in>dom(Plant.schedule plant) . peri \<in> dom(Plant.schedule plant)"
  apply(simp add: ExpertSet_def)
  done

(*TODO: Implement ExpertToPage_legalMapApplication*)    
(*TODO: Implement ExpertToPage_functionPostconditionSatisfiable*)

    
end