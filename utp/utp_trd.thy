section {* Timed reactive designs *}

theory utp_trd
imports utp_rea_designs
begin

subsection {* Time events *}

class time = linordered_semidom

record 't::time htime =
  htime :: 't

typedef (overloaded) 'a nz = "{n::'a::time. n > 0}" morphisms nz_of nz
  by (metis mem_Collect_eq zero_less_one)

lemma real_of_nz_gez [simp]: "nz_of x > 0"
  by (metis mem_Collect_eq nz_of)

context notes [[typedef_overloaded]]
begin
datatype ('t, '\<theta>) tevent = Tock "'t nz" "'\<theta> set" | Event '\<theta>
end

fun period :: "('t::time,'\<theta>) tevent list \<Rightarrow> 't" where
"period [] = 0" |
"period (Tock n A # t) = nz_of n + period t" |
"period (Event x # t) = period(t)"

lemma period_ge_zero [simp]: "period t \<ge> 0"
  apply (induct t, simp_all)
  apply (rename_tac a t, case_tac a)
  apply (auto, metis add_nonneg_nonneg le_less real_of_nz_gez)
done

lemma Cons_prefixE: "\<lbrakk> (x # xs) \<le> ys; \<And> ys'. \<lbrakk> ys = x # ys'; xs \<le> ys' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis Cons_prefix_Cons append_Cons strict_prefixE)

lemma period_mono: "t1 \<le> t2 \<Longrightarrow> period t1 \<le> period t2"
  apply (induct t1 arbitrary: t2, auto)
  apply (rename_tac a t1 t2)
  apply (erule Cons_prefixE)
  apply (case_tac a)
  apply (auto)
done

lemma minus_list_Cons [simp]:
  "(x # ys) - (x # xs) = ys - xs"
  by (simp add: minus_list_def)

lemma period_minus [simp]: "t2 \<le> t1 \<Longrightarrow> period (t1 - t2) = period(t1) - period(t2)"
  apply (induct t1 arbitrary: t2, auto)
  apply (simp add: prefix_Cons)
  apply (auto)
  apply (rename_tac a t1 t2')
  apply (case_tac a)
  apply (simp_all)
done

fun events :: "('t, '\<theta>) tevent list \<Rightarrow> '\<theta> list" where
"events [] = []" |
"events (Tock n A # t) = events t" |
"events (Event x # t) = (x # events t)"

fun refusals :: "('t, '\<theta>) tevent list \<Rightarrow> '\<theta> set" where
"refusals [] = {}" |
"refusals (Tock n A # t) = A \<union> refusals t" |
"refusals (Event x # t) = refusals t"

fun idleprefix :: "('t, '\<theta>) tevent list \<Rightarrow> ('t, '\<theta>) tevent list" where
"idleprefix [] = []" |
"idleprefix (Tock n A # t) = (Tock n A # idleprefix t)" |
"idleprefix (Event x # t) = []"

syntax 
  "_period" :: "logic \<Rightarrow> logic" ("period\<^sub>u'(_')")
  "_events" :: "logic \<Rightarrow> logic" ("events\<^sub>u'(_')")
  "_refusals" :: "logic \<Rightarrow> logic" ("refusals\<^sub>u'(_')")
  "_idleprefix" :: "logic \<Rightarrow> logic" ("idleprefix\<^sub>u'(_')")
  "_ev"         :: "logic \<Rightarrow> logic" ("ev\<^sub>u'(_')")
  "_tock"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("tock\<^sub>u'(_,_')")

translations
  "period\<^sub>u(t)" == "CONST uop CONST period t"
  "events\<^sub>u(t)" == "CONST uop CONST events t"
  "refusals\<^sub>u(t)" == "CONST uop CONST refusals t"
  "idleprefix\<^sub>u(t)" == "CONST uop CONST idleprefix t"
  "ev\<^sub>u(e)" == "CONST uop CONST Event e"
  "tock\<^sub>u(t,A)" == "CONST bop CONST Tock t A"

subsection {* Signature *}

abbreviation "tt \<equiv> $tr\<acute> - $tr"

abbreviation time_length :: "_" ("\<^bold>l")
where "\<^bold>l \<equiv> period\<^sub>u(tt)"

definition "Stop = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"

definition "Prefix a = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> a \<notin>\<^sub>u refusals\<^sub>u(tt) \<and> ev\<^sub>u(a) \<notin>\<^sub>u $ref\<acute>) 
                               \<diamondop> (tt =\<^sub>u idleprefix\<^sub>u(tt) ^\<^sub>u \<langle>ev\<^sub>u(a)\<rangle> \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R \<and> a \<notin>\<^sub>u refusals\<^sub>u(tt)))"

end