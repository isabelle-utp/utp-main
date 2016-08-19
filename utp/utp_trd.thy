section {* Timed reactive designs *}

theory utp_trd
imports utp_rea_designs
begin

subsection {* Time events *}

class time = linordered_semidom

typedef (overloaded) 'a nz = "{n::'a::time. n > 0}" morphisms nz_of nz
  by (metis mem_Collect_eq zero_less_one)

setup_lifting type_definition_nz

instantiation nz :: (time) linorder
begin
 
lift_definition less_eq_nz :: "'a nz \<Rightarrow> 'a nz \<Rightarrow> bool" is "op \<le>" .
lift_definition less_nz :: "'a nz \<Rightarrow> 'a nz \<Rightarrow> bool" is "op <" .

instance by (intro_classes, (transfer, auto)+)

end

instantiation nz :: (time) ordered_ab_semigroup_add
begin

lift_definition plus_nz :: "'a nz \<Rightarrow> 'a nz \<Rightarrow> 'a nz" is "op +"
  by (metis pos_add_strict)

instance
  apply (intro_classes)
  apply (transfer, auto simp add: add.assoc)
  apply (transfer, auto simp add: add.commute)
  apply (transfer, auto simp add: add.commute)
done

end

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

lemma period_append [simp]: "period (t1 @ t2) = period(t1) + period(t2)"
  apply (induct t1)
  apply (simp_all)
  apply (rename_tac x t1)
  apply (case_tac x)
  apply (auto simp add: add.assoc)
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

lemma events_append [simp]: "events (xs @ ys) = events(xs) @ events(ys)"
  apply (induct xs, simp_all)
  apply (rename_tac x xs)
  apply (case_tac x)
  apply (simp_all)
done

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

subsection {* Types *}

type_synonym ('t, '\<theta>, '\<alpha>) alphabet_trd = "(('t, '\<theta>) tevent, '\<alpha>) alphabet_rp"
type_synonym ('a, 't, '\<theta>, '\<alpha>) trde = "('a, ('t, '\<theta>, '\<alpha>) alphabet_trd) uexpr"
type_synonym ('t, '\<theta>, '\<alpha>) trdp = "(('t, '\<theta>, '\<alpha>) alphabet_trd) upred"
type_synonym ('t, '\<theta>, '\<alpha>, '\<beta>) trd = "(('t, '\<theta>, '\<alpha>) alphabet_trd, ('t, '\<theta>, '\<beta>) alphabet_trd) relation"
type_synonym ('t, '\<theta>, '\<alpha>) htrd = "(('t, '\<theta>, '\<alpha>) alphabet_trd, ('t, '\<theta>, '\<alpha>) alphabet_trd) relation"

subsection {* Signature *}

abbreviation trace :: "_" ("tt") where
"tt \<equiv> $tr\<acute> - $tr"

abbreviation time_length :: "_" ("\<^bold>l")
where "\<^bold>l \<equiv> period\<^sub>u(tt)"

abbreviation rea_pre_lift :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>R\<^sub><") where "\<lceil>n\<rceil>\<^sub>R\<^sub>< \<equiv> \<lceil>\<lceil>n\<rceil>\<^sub><\<rceil>\<^sub>R"

translations
  "\<^bold>l" <= "CONST uop CONST period (CONST minus (CONST var (CONST ovar CONST tr)) (CONST var (CONST ivar CONST tr)))"
  "tt" <= "CONST minus (CONST var (CONST ovar CONST tr)) (CONST var (CONST ivar CONST tr))"


definition "Stop = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) \<diamondop> false)"

definition "Prefix a = RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> a \<notin>\<^sub>u refusals\<^sub>u(tt) \<and> ev\<^sub>u(a) \<notin>\<^sub>u $ref\<acute>) 
                               \<diamondop> (tt =\<^sub>u idleprefix\<^sub>u(tt) ^\<^sub>u \<langle>ev\<^sub>u(a)\<rangle> \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R \<and> a \<notin>\<^sub>u refusals\<^sub>u(tt)))"

fun Wait :: "('t::time, '\<alpha>) uexpr \<times> ('t, '\<alpha>) uexpr \<Rightarrow> ('t, '\<theta>, '\<alpha>) htrd" where
"Wait (m, n) = (RH(true \<turnstile> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<^bold>l <\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub><)
                        \<diamondop> (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<^bold>l \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<^bold>l <\<^sub>u \<lceil>n\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)))"

lemma ulist_minus_empty [simp]: "e - \<langle>\<rangle> = e"
  by (rel_tac)

lemma R2s_events_tt_empty:
  "R2s(events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>) = (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle>)"
  by (simp add: R2s_def usubst unrest)

lemma R2s_time_length_eq: "R2s (\<^bold>l =\<^sub>u \<lceil>m\<rceil>\<^sub>R) = (\<^bold>l =\<^sub>u \<lceil>m\<rceil>\<^sub>R)"
  by (simp add: R2s_def usubst unrest)

lemma R2s_time_length_geq: "R2s (\<^bold>l \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R) = (\<^bold>l \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R)"
  by (simp add: R2s_def usubst unrest)

lemma R2s_time_length_less: "R2s (\<^bold>l <\<^sub>u \<lceil>m\<rceil>\<^sub>R) = (\<^bold>l <\<^sub>u \<lceil>m\<rceil>\<^sub>R)"
  by (simp add: R2s_def usubst unrest)

abbreviation hseqr :: "'\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation \<Rightarrow> '\<alpha> hrelation" (infixr ";;\<^sub>h" 15) where
"(P ;;\<^sub>h Q) \<equiv> ((P::'\<alpha> hrelation) ;; (Q::'\<alpha> hrelation))"

lemma rea_lift_skip_alpha [alpha]: "\<lceil>II\<rceil>\<^sub>R = ($\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R)"
  by (rel_tac)

lemma Wait_m_plus_n: "(Wait (m\<^sub>1, m\<^sub>2) ;; Wait (n\<^sub>1, n\<^sub>2)) = (Wait (m\<^sub>1 + n\<^sub>1, m\<^sub>2 + n\<^sub>2))"
  apply (simp)
  apply (subst RH_tri_design_composition)
  apply (simp_all add: unrest R2s_true R1_false R2_def[THEN sym])

proof -
  have "(R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<^sub>1\<rceil>\<^sub>R\<^sub>< \<le>\<^sub>u \<^bold>l \<and> \<^bold>l <\<^sub>u \<lceil>m\<^sub>2\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R) ;; R2 (events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<^bold>l <\<^sub>u \<lceil>n\<^sub>1\<rceil>\<^sub>R\<^sub><)) =
        R2(events\<^sub>u(tt) =\<^sub>u \<langle>\<rangle> \<and> \<lceil>m\<^sub>1\<rceil>\<^sub>R\<^sub>< \<le>\<^sub>u \<^bold>l \<and> \<^bold>l <\<^sub>u \<lceil>m\<^sub>2\<rceil>\<^sub>R\<^sub>< + \<lceil>n\<^sub>1\<rceil>\<^sub>R\<^sub><)" (is "?lhs = ?rhs")
    apply (simp add: R2_seqr_form usubst unrest)

  proof -
    have "?lhs = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> period\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h
                                   \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle>) \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: R2_seqr_form conj_comm usubst unrest)        
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> period\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)) \<and>
                                   events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_post_out unrest conj_assoc)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (period\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> $\<Sigma>\<^sub>R\<acute> =\<^sub>u $\<Sigma>\<^sub>R ;;\<^sub>h \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)) 
                                    \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_pre_out unrest, subst conj_comm, simp add: conj_assoc)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>period\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>< \<and> II ;; \<lceil>n\<rceil>\<^sub>< >\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)\<rceil>\<^sub>R) 
                                    \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (\<lceil>II \<and> period\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>> ;; \<lceil>n\<rceil>\<^sub>< >\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)\<rceil>\<^sub>R) 
                                    \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: cond_skip unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<lceil>period\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>< >\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)\<rceil>\<^sub>R 
                                    \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: seqr_pre_transfer unrest)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> period\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) 
                                    \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (simp add: alpha conj_assoc)
    also have "... = (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> period\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright>) \<ge>\<^sub>u \<lceil>m\<rceil>\<^sub>R\<^sub>< \<and> \<lceil>n\<rceil>\<^sub>R\<^sub>< >\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>2\<guillemotright>)
                                    \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by ((rule shEx_cong)+, rel_tac)
    also have "... = (\<^bold>\<exists> tt\<^sub>0 \<bullet> \<lceil>m\<rceil>\<^sub>R\<^sub>< \<le>\<^sub>u period\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> period\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) <\<^sub>u (\<lceil>m\<rceil>\<^sub>R\<^sub>< + \<lceil>n\<rceil>\<^sub>R\<^sub><)
                                    \<and> events\<^sub>u(\<guillemotleft>tt\<^sub>0\<guillemotright>) =\<^sub>u \<langle>\<rangle> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>)"
      apply (rel_tac)
      apply (simp add: add_increasing2)
      


oops

end