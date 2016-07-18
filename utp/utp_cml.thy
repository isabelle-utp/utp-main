section {* COMPASS Modelling Language *}

theory utp_cml
imports utp_csp
begin

subsection {* Preliminaries *}

hide_const Stop

datatype '\<theta> tevent = Tock "'\<theta> set" | Event '\<theta>

fun events :: "'\<theta> tevent list \<Rightarrow> '\<theta> list" where
"events [] = []" |
"events (Tock A # t) = events t" |
"events (Event x # t) = (x # events t)"

lemma events_append [simp]: "events (xs @ ys) = events(xs) @ events(ys)"
  apply (induct xs, simp_all)
  apply (rename_tac x xs)
  apply (case_tac x)
  apply (simp_all)
done

fun tocks :: "'\<theta> tevent list \<Rightarrow> '\<theta> tevent list" where
"tocks [] = []" |
"tocks (Tock A # xs) = Tock A # tocks xs" |
"tocks (Event x # xs) = tocks xs"

fun refusals :: "'\<theta> tevent list \<Rightarrow> '\<theta> set" where
"refusals [] = {}" |
"refusals (Tock A # t) = A \<union> refusals t" |
"refusals (Event x # t) = refusals t"

fun idleprefix :: "'\<theta> tevent list \<Rightarrow> '\<theta> tevent list" where
"idleprefix [] = []" |
"idleprefix (Tock A # t) = (Tock A # idleprefix t)" |
"idleprefix (Event x # t) = []"

definition "idlesuffix = idleprefix \<circ> rev"

syntax 
  "_events"     :: "logic \<Rightarrow> logic" ("events\<^sub>u'(_')")
  "_tocks"      :: "logic \<Rightarrow> logic" ("tocks\<^sub>u'(_')")
  "_refusals"   :: "logic \<Rightarrow> logic" ("refusals\<^sub>u'(_')")
  "_idleprefix" :: "logic \<Rightarrow> logic" ("idleprefix\<^sub>u'(_')")
  "_idlesuffix" :: "logic \<Rightarrow> logic" ("idlesuffix\<^sub>u'(_')")
  "_ev"         :: "logic \<Rightarrow> logic" ("ev\<^sub>u'(_')")
  "_tock"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("tock\<^sub>u'(_,_')")

translations
  "events\<^sub>u(t)" == "CONST uop CONST events t"
  "tocks\<^sub>u(t)" == "CONST uop CONST tocks t"
  "refusals\<^sub>u(t)" == "CONST uop CONST refusals t"
  "idleprefix\<^sub>u(t)" == "CONST uop CONST idleprefix t"
  "idlesuffix\<^sub>u(t)" == "CONST uop CONST idlesuffix t"  
  "ev\<^sub>u(e)" == "CONST uop CONST Event e"
  "tock\<^sub>u(t,A)" == "CONST bop CONST Tock t A"

subsection {* Signature *}

subsection {* Signature *}

abbreviation trace :: "_" ("tt") where
"tt \<equiv> $tr\<acute> - $tr"

abbreviation time_length :: "_" ("\<^bold>l")
where "\<^bold>l \<equiv> #\<^sub>u(tocks\<^sub>u(tt))"


abbreviation csp_pre_lift :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>C\<^sub><") where "\<lceil>n\<rceil>\<^sub>C\<^sub>< \<equiv> \<lceil>\<lceil>n\<rceil>\<^sub><\<rceil>\<^sub>C"

definition "Stop = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"

definition "Prefix a = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> a \<notin>\<^sub>u refusals\<^sub>u(tt) \<and> ev\<^sub>u(a) \<notin>\<^sub>u $ref\<acute>) 
                               \<diamondop> (tt =\<^sub>u idleprefix\<^sub>u(tt) ^\<^sub>u \<langle>ev\<^sub>u(a)\<rangle> \<and> $\<Sigma>\<^sub>C\<acute> =\<^sub>u $\<Sigma>\<^sub>C \<and> a \<notin>\<^sub>u refusals\<^sub>u(tt)))"

definition "Wait n = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) <\<^sub>u \<lceil>n\<rceil>\<^sub>C\<^sub><) 
                             \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> #\<^sub>u(tt) =\<^sub>u \<lceil>n\<rceil>\<^sub>C\<^sub>< \<and> $\<Sigma>\<^sub>C\<acute> =\<^sub>u $\<Sigma>\<^sub>C))"

end