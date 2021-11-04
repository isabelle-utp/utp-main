(*  Title:       The Relational Method with Message Anonymity for the Verification of Cryptographic Protocols
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Possibility properties"

theory Possibility
  imports Anonymity
begin

text \<open>
\label{Possibility}
\<close>


type_synonym seskey_tuple = "key_id \<times> key_id \<times> key_id \<times> key_id \<times> key_id"

type_synonym stage = "state \<times> seskey_tuple"


abbreviation pred_asset_i :: "agent_id \<Rightarrow> state \<Rightarrow> stage \<Rightarrow> bool" where
"pred_asset_i n s x \<equiv>
  \<exists>S. PriKey S \<notin> used s \<and> x = (insert (Asset n, PriKey S) s \<union>
    {Asset n, Spy} \<times> {Crypt (Auth_ShaKey n) (PriKey S)} \<union>
    {(Spy, Log (Crypt (Auth_ShaKey n) (PriKey S)))},
    S, 0, 0, 0, 0)"

definition run_asset_i :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_asset_i n s \<equiv> SOME x. pred_asset_i n s x"


abbreviation pred_owner_ii :: "agent_id \<Rightarrow> stage \<Rightarrow> stage \<Rightarrow> bool" where
"pred_owner_ii n x y \<equiv> case x of (s, S, _) \<Rightarrow>
  \<exists>A. PriKey A \<notin> used s \<and> y = (insert (Owner n, PriKey A) s \<union>
    {Owner n, Spy} \<times> {\<lbrace>Num 1, PubKey A\<rbrace>} \<union>
    {Spy} \<times> Log ` {Crypt (Auth_ShaKey n) (PriKey S), \<lbrace>Num 1, PubKey A\<rbrace>},
    S, A, 0, 0, 0)"

definition run_owner_ii :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_owner_ii n s \<equiv> SOME x. pred_owner_ii n (run_asset_i n s) x"


abbreviation pred_asset_ii :: "agent_id \<Rightarrow> stage \<Rightarrow> stage \<Rightarrow> bool" where
"pred_asset_ii n x y \<equiv> case x of (s, S, A, _) \<Rightarrow>
  \<exists>B. PriKey B \<notin> used s \<and> y = (insert (Asset n, PriKey B) s \<union>
    {Asset n, Spy} \<times> {\<lbrace>Num 2, PubKey B\<rbrace>} \<union>
    {Spy} \<times> Log ` {\<lbrace>Num 1, PubKey A\<rbrace>, \<lbrace>Num 2, PubKey B\<rbrace>},
    S, A, B, 0, 0)"

definition run_asset_ii :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_asset_ii n s \<equiv> SOME x. pred_asset_ii n (run_owner_ii n s) x"


abbreviation pred_owner_iii :: "agent_id \<Rightarrow> stage \<Rightarrow> stage \<Rightarrow> bool" where
"pred_owner_iii n x y \<equiv> case x of (s, S, A, B, _) \<Rightarrow>
  \<exists>C. PriKey C \<notin> used s \<and> y = (insert (Owner n, PriKey C) s \<union>
    {Owner n, Spy} \<times> {\<lbrace>Num 3, PubKey C\<rbrace>} \<union>
    {Spy} \<times> Log ` {\<lbrace>Num 2, PubKey B\<rbrace>, \<lbrace>Num 3, PubKey C\<rbrace>},
    S, A, B, C, 0)"

definition run_owner_iii :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_owner_iii n s \<equiv> SOME x. pred_owner_iii n (run_asset_ii n s) x"


abbreviation pred_asset_iii :: "agent_id \<Rightarrow> stage \<Rightarrow> stage \<Rightarrow> bool" where
"pred_asset_iii n x y \<equiv> case x of (s, S, A, B, C, _) \<Rightarrow>
  \<exists>D. PriKey D \<notin> used s \<and> y = (insert (Asset n, PriKey D) s \<union>
    {Asset n, Spy} \<times> {\<lbrace>Num 4, PubKey D\<rbrace>} \<union>
    {Spy} \<times> Log ` {\<lbrace>Num 3, PubKey C\<rbrace>, \<lbrace>Num 4, PubKey D\<rbrace>},
    S, A, B, C, D)"

definition run_asset_iii :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_asset_iii n s \<equiv> SOME x. pred_asset_iii n (run_owner_iii n s) x"


abbreviation stage_owner_iv :: "agent_id \<Rightarrow> stage \<Rightarrow> stage" where
"stage_owner_iv n x \<equiv> let (s, S, A, B, C, D) = x;
  SK = (Some S, {A, B}, {C, D}) in
  (insert (Owner n, SesKey SK) s \<union>
    {Owner n, Spy} \<times> {Crypt (SesK SK) (PubKey D)} \<union>
    {Spy} \<times> Log ` {\<lbrace>Num 4, PubKey D\<rbrace>, Crypt (SesK SK) (PubKey D)},
    S, A, B, C, D)"

definition run_owner_iv :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_owner_iv n s \<equiv> stage_owner_iv n (run_asset_iii n s)"


abbreviation stage_asset_iv :: "agent_id \<Rightarrow> stage \<Rightarrow> stage" where
"stage_asset_iv n x \<equiv> let (s, S, A, B, C, D) = x;
  SK = (Some S, {A, B}, {C, D}) in
  (s \<union> {Asset n} \<times> {SesKey SK, PubKey B} \<union>
    {Asset n, Spy} \<times> {Token n (Auth_PriK n) B C SK} \<union>
    {Spy} \<times> Log ` {Crypt (SesK SK) (PubKey D),
      Token n (Auth_PriK n) B C SK},
    S, A, B, C, D)"

definition run_asset_iv :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_asset_iv n s \<equiv> stage_asset_iv n (run_owner_iv n s)"


abbreviation stage_owner_v :: "agent_id \<Rightarrow> stage \<Rightarrow> stage" where
"stage_owner_v n x \<equiv> let (s, S, A, B, C, D) = x;
  SK = (Some S, {A, B}, {C, D}) in
  (s \<union> {Owner n, Spy} \<times> {Crypt (SesK SK) (Pwd n)} \<union>
    {Spy} \<times> Log ` {Token n (Auth_PriK n) B C SK, Crypt (SesK SK) (Pwd n)},
    S, A, B, C, D)"

definition run_owner_v :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_owner_v n s \<equiv> stage_owner_v n (run_asset_iv n s)"


abbreviation stage_asset_v :: "agent_id \<Rightarrow> stage \<Rightarrow> stage" where
"stage_asset_v n x \<equiv> let (s, S, A, B, C, D) = x;
  SK = (Some S, {A, B}, {C, D}) in
  (s \<union> {Asset n, Spy} \<times> {Crypt (SesK SK) (Num 0)} \<union>
    {Spy} \<times> Log ` {Crypt (SesK SK) (Pwd n), Crypt (SesK SK) (Num 0)},
    S, A, B, C, D)"

definition run_asset_v :: "agent_id \<Rightarrow> state \<Rightarrow> stage" where
"run_asset_v n s \<equiv> stage_asset_v n (run_owner_v n s)"


lemma prikey_unused_1:
 "infinite {A. PriKey A \<notin> used s\<^sub>0}"
by (rule infinite_super [of "- range Auth_PriK"], rule subsetI, simp add:
 image_def bad_prik_def, rule someI2 [of _ "{}"], simp, blast, subst Auth_PriK_def,
 rule someI [of _ "\<lambda>n. 0"], simp)

lemma prikey_unused_2:
 "\<lbrakk>s \<turnstile> s'; infinite {A. PriKey A \<notin> used s}\<rbrakk> \<Longrightarrow>
    infinite {A. PriKey A \<notin> used s'}"
by (simp add: rel_def, ((erule disjE)?, (erule exE)+, simp add: image_iff,
 (((subst conj_commute | subst Int_commute), simp add: Collect_conj_eq Collect_neg_eq
 Diff_eq [symmetric])+)?, ((rule Diff_infinite_finite, rule msg.induct, simp_all,
 rule key.induct, simp_all)+)?)+)

proposition prikey_unused:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> \<exists>A. PriKey A \<notin> used s"
by (subgoal_tac "infinite {A. PriKey A \<notin> used s}", drule infinite_imp_nonempty,
 simp, erule rtrancl_induct, rule prikey_unused_1, rule prikey_unused_2)


lemma pubkey_unused_1:
 "\<lbrakk>s \<turnstile> s'; PubKey A \<in> parts (used s) \<longrightarrow> PriKey A \<in> used s;
    PubKey A \<in> parts (used s')\<rbrakk> \<Longrightarrow>
  PriKey A \<in> used s'"
by (simp add: rel_def, ((erule disjE)?, ((erule exE)+)?, simp add: parts_insert
 image_iff split: if_split_asm, ((erule conjE)+, drule RangeI, (drule parts_used,
 drule parts_snd)?, simp | (subst (asm) disj_assoc [symmetric])?, erule disjE,
 (drule parts_dec | drule parts_enc | drule parts_sep | drule parts_con), simp)?)+)

proposition pubkey_unused [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    PriKey A \<notin> used s \<longrightarrow>
  PubKey A \<notin> parts (used s)"
by (erule rtrancl_induct, subst parts_init, simp add: Range_iff image_def, rule impI,
 erule contrapos_nn [OF _ pubkey_unused_1], blast+)


proposition run_asset_i_ex:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> pred_asset_i n s (run_asset_i n s)"
by (drule prikey_unused, erule exE, subst run_asset_i_def, rule someI_ex, blast)

proposition run_asset_i_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_asset_i n s)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (drule run_asset_i_ex [of _ n], rule r_into_rtrancl,
 subgoal_tac "(s, ?t) \<in> rel_asset_i", simp_all add: rel_def, erule exE, auto)

proposition run_asset_i_msg:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    case run_asset_i n s of (s', S, _) \<Rightarrow>
      (Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s'"
by (drule run_asset_i_ex [of _ n], auto)

proposition run_asset_i_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_asset_i n s))) \<notin> used s"
by (drule run_asset_i_ex [of _ n], auto)

proposition run_asset_i_unused:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> \<exists>A. PriKey A \<notin> used (fst (run_asset_i n s))"
by (rule prikey_unused, rule rtrancl_trans, simp, rule run_asset_i_rel)


proposition run_owner_ii_ex:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> pred_owner_ii n (run_asset_i n s) (run_owner_ii n s)"
by (drule run_asset_i_unused, erule exE, subst run_owner_ii_def, rule someI_ex,
 auto simp add: split_def)

proposition run_owner_ii_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_owner_ii n s)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule run_asset_i_rel [of _ n], frule run_asset_i_msg,
 drule run_owner_ii_ex, subgoal_tac "(fst (run_asset_i n s), ?t) \<in> rel_owner_ii",
 simp_all add: rel_def split_def, erule exE, (rule exI)+, auto)

proposition run_owner_ii_msg:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    case run_owner_ii n s of (s', S, A, _) \<Rightarrow>
      {(Asset n, Crypt (Auth_ShaKey n) (PriKey S)),
        (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>)} \<subseteq> s'"
by (frule run_asset_i_msg [of _ n], drule run_owner_ii_ex [of _ n], auto)

proposition run_owner_ii_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_owner_ii n s))) \<notin> used s"
by (frule run_asset_i_nonce [of _ n], drule run_owner_ii_ex [of _ n], auto)

proposition run_owner_ii_unused:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> \<exists>B. PriKey B \<notin> used (fst (run_owner_ii n s))"
by (rule prikey_unused, rule rtrancl_trans, simp, rule run_owner_ii_rel)


proposition run_asset_ii_ex:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> pred_asset_ii n (run_owner_ii n s) (run_asset_ii n s)"
by (drule run_owner_ii_unused, erule exE, subst run_asset_ii_def, rule someI_ex,
 auto simp add: split_def)

proposition run_asset_ii_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_asset_ii n s)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule run_owner_ii_rel [of _ n], frule run_owner_ii_msg,
 drule run_asset_ii_ex, subgoal_tac "(fst (run_owner_ii n s), ?t) \<in> rel_asset_ii",
 simp_all add: rel_def split_def, erule exE, (rule exI)+, auto)

proposition run_asset_ii_msg:
  assumes A: "s\<^sub>0 \<Turnstile> s"
  shows "case run_asset_ii n s of (s', S, A, B, _) \<Rightarrow>
    insert (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>)
      ({Asset n} \<times> {Crypt (Auth_ShaKey n) (PriKey S),
       \<lbrace>Num 2, PubKey B\<rbrace>}) \<subseteq> s' \<and>
    (Asset n, PubKey B) \<notin> s'"
by (insert run_owner_ii_msg [OF A, of n], insert run_asset_ii_ex [OF A, of n],
 simp add: split_def, erule exE, simp, insert run_owner_ii_rel [OF A, of n],
 drule rtrancl_trans [OF A], drule pubkey_unused, auto)

proposition run_asset_ii_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_asset_ii n s))) \<notin> used s"
by (frule run_owner_ii_nonce [of _ n], drule run_asset_ii_ex [of _ n], auto)

proposition run_asset_ii_unused:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> \<exists>C. PriKey C \<notin> used (fst (run_asset_ii n s))"
by (rule prikey_unused, rule rtrancl_trans, simp, rule run_asset_ii_rel)


proposition run_owner_iii_ex:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> pred_owner_iii n (run_asset_ii n s) (run_owner_iii n s)"
by (drule run_asset_ii_unused, erule exE, subst run_owner_iii_def, rule someI_ex,
 auto simp add: split_def)

proposition run_owner_iii_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_owner_iii n s)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule run_asset_ii_rel [of _ n], frule run_asset_ii_msg,
 drule run_owner_iii_ex, subgoal_tac "(fst (run_asset_ii n s), ?t) \<in> rel_owner_iii",
 simp_all add: rel_def split_def, erule exE, (rule exI)+, auto)

proposition run_owner_iii_msg:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    case run_owner_iii n s of (s', S, A, B, C, _) \<Rightarrow>
      {Asset n} \<times> {Crypt (Auth_ShaKey n) (PriKey S), \<lbrace>Num 2, PubKey B\<rbrace>} \<union>
      {Owner n} \<times> {\<lbrace>Num 1, PubKey A\<rbrace>, \<lbrace>Num 3, PubKey C\<rbrace>} \<subseteq> s' \<and>
      (Asset n, PubKey B) \<notin> s'"
by (frule run_asset_ii_msg [of _ n], drule run_owner_iii_ex [of _ n], auto)

proposition run_owner_iii_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_owner_iii n s))) \<notin> used s"
by (frule run_asset_ii_nonce [of _ n], drule run_owner_iii_ex [of _ n], auto)

proposition run_owner_iii_unused:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> \<exists>D. PriKey D \<notin> used (fst (run_owner_iii n s))"
by (rule prikey_unused, rule rtrancl_trans, simp, rule run_owner_iii_rel)


proposition run_asset_iii_ex:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> pred_asset_iii n (run_owner_iii n s) (run_asset_iii n s)"
by (drule run_owner_iii_unused, erule exE, subst run_asset_iii_def, rule someI_ex,
 auto simp add: split_def)

proposition run_asset_iii_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_asset_iii n s)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule run_owner_iii_rel [of _ n], frule run_owner_iii_msg,
 drule run_asset_iii_ex, subgoal_tac "(fst (run_owner_iii n s), ?t) \<in> rel_asset_iii",
 simp_all add: rel_def split_def, erule exE, (rule exI)+, auto)

proposition run_asset_iii_msg:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    case run_asset_iii n s of (s', S, A, B, C, D) \<Rightarrow>
      {Asset n} \<times> {Crypt (Auth_ShaKey n) (PriKey S), \<lbrace>Num 2, PubKey B\<rbrace>,
        \<lbrace>Num 4, PubKey D\<rbrace>} \<union>
      {Owner n} \<times> {\<lbrace>Num 1, PubKey A\<rbrace>, \<lbrace>Num 3, PubKey C\<rbrace>} \<subseteq> s' \<and>
      (Asset n, PubKey B) \<notin> s'"
by (frule run_owner_iii_msg [of _ n], drule run_asset_iii_ex [of _ n], auto)

proposition run_asset_iii_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_asset_iii n s))) \<notin> used s"
by (frule run_owner_iii_nonce [of _ n], drule run_asset_iii_ex [of _ n], auto)


lemma run_owner_iv_rel_1:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; run_asset_iii n s = (s', S, A, B, C, D)\<rbrakk> \<Longrightarrow>
    s \<Turnstile> fst (run_owner_iv n s)"
      (is "\<lbrakk>_; _\<rbrakk> \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule run_asset_iii_rel [of _ n], drule run_asset_iii_msg
 [of _ n], subgoal_tac "(s', ?t) \<in> rel_owner_iv", simp_all add: rel_def run_owner_iv_def
 Let_def, rule exI [of _ n], rule exI [of _ S], rule exI [of _ A], rule exI [of _ B],
 rule exI [of _ C], rule exI [of _ D], rule exI [of _ "Auth_ShaKey n"], auto)

proposition run_owner_iv_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_owner_iv n s)"
by (insert run_owner_iv_rel_1, cases "run_asset_iii n s", simp)

proposition run_owner_iv_msg:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    let (s', S, A, B, C, D) = run_owner_iv n s;
      SK = (Some S, {A, B}, {C, D}) in
      {Asset n} \<times> {Crypt (Auth_ShaKey n) (PriKey S), \<lbrace>Num 2, PubKey B\<rbrace>,
        \<lbrace>Num 4, PubKey D\<rbrace>} \<union>
      {Owner n} \<times> {\<lbrace>Num 1, PubKey A\<rbrace>, \<lbrace>Num 3, PubKey C\<rbrace>, SesKey SK,
        Crypt (SesK SK) (PubKey D)} \<subseteq> s' \<and>
      (Asset n, PubKey B) \<notin> s'"
by (drule run_asset_iii_msg [of _ n], simp add: run_owner_iv_def split_def Let_def)

proposition run_owner_iv_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_owner_iv n s))) \<notin> used s"
by (drule run_asset_iii_nonce [of _ n], simp add: run_owner_iv_def split_def Let_def)


proposition run_asset_iv_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_asset_iv n s)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule run_owner_iv_rel [of _ n], drule run_owner_iv_msg
 [of _ n], subgoal_tac "(fst (run_owner_iv n s), ?t) \<in> rel_asset_iv", simp_all add:
 rel_def run_asset_iv_def split_def Let_def, blast)

proposition run_asset_iv_msg:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    let (s', S, A, B, C, D) = run_asset_iv n s; SK = (Some S, {A, B}, {C, D}) in
      insert (Owner n, SesKey SK)
        ({Asset n} \<times> {SesKey SK, Token n (Auth_PriK n) B C SK}) \<subseteq> s'"
by (drule run_owner_iv_msg [of _ n], simp add: run_asset_iv_def split_def Let_def)

proposition run_asset_iv_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_asset_iv n s))) \<notin> used s"
by (drule run_owner_iv_nonce [of _ n], simp add: run_asset_iv_def split_def Let_def)


proposition run_owner_v_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_owner_v n s)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule run_asset_iv_rel [of _ n], drule run_asset_iv_msg
 [of _ n], subgoal_tac "(fst (run_asset_iv n s), ?t) \<in> rel_owner_v", simp_all add:
 rel_def run_owner_v_def split_def Let_def, blast)

proposition run_owner_v_msg:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    let (s', S, A, B, C, D) = run_owner_v n s;
      SK = (Some S, {A, B}, {C, D}) in
      {(Asset n, SesKey SK),
        (Owner n, Crypt (SesK SK) (Pwd n))} \<subseteq> s'"
by (drule run_asset_iv_msg [of _ n], simp add: run_owner_v_def split_def Let_def)

proposition run_owner_v_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_owner_v n s))) \<notin> used s"
by (drule run_asset_iv_nonce [of _ n], simp add: run_owner_v_def split_def Let_def)


proposition run_asset_v_rel:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> s \<Turnstile> fst (run_asset_v n s)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule run_owner_v_rel [of _ n], drule run_owner_v_msg
 [of _ n], subgoal_tac "(fst (run_owner_v n s), ?t) \<in> rel_asset_v", simp_all add:
 rel_def run_asset_v_def split_def Let_def, blast)

proposition run_asset_v_msg:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    let (s', S, A, B, C, D) = run_asset_v n s; SK = (Some S, {A, B}, {C, D}) in
      {(Owner n, Crypt (SesK SK) (Pwd n)),
        (Asset n, Crypt (SesK SK) (Num 0))} \<subseteq> s'"
by (drule run_owner_v_msg [of _ n], simp add: run_asset_v_def split_def Let_def)

proposition run_asset_v_nonce:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> PriKey (fst (snd (run_asset_v n s))) \<notin> used s"
by (drule run_owner_v_nonce [of _ n], simp add: run_asset_v_def split_def Let_def)


lemma runs_unbounded_1:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; run_asset_v n s = (s', S, A, B, C, D)\<rbrakk> \<Longrightarrow>
    \<exists>s' S SK. (Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<notin> s \<and>
      {(Owner n, Crypt (SesK SK) (Pwd n)),
       (Asset n, Crypt (SesK SK) (Num 0))} \<subseteq> s' \<and>
      s \<Turnstile> s' \<and> fst SK = Some S"
by (rule exI [of _ s'], rule exI [of _ S], rule exI [of _ "(Some S, {A, B}, {C, D})"],
 rule conjI, rule notI, frule run_asset_v_nonce [of _ n], frule asset_i_used [of _ n S],
 simp, frule run_asset_v_rel [of _ n], drule run_asset_v_msg [of _ n],
 simp add: Let_def)

theorem runs_unbounded:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> \<exists>s' S SK. s \<Turnstile> s' \<and> fst SK = Some S \<and>
    (Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<notin> s \<and>
    {(Owner n, Crypt (SesK SK) (Pwd n)),
     (Asset n, Crypt (SesK SK) (Num 0))} \<subseteq> s'"
by (insert runs_unbounded_1, cases "run_asset_v n s", blast)


definition pwd_spy_i :: "agent_id \<Rightarrow> stage" where
"pwd_spy_i n \<equiv>
  (insert (Spy, Crypt (Auth_ShaKey n) (Auth_PriKey n)) s\<^sub>0,
    Auth_PriK n, 0, 0, 0, 0)"

definition pwd_owner_ii :: "agent_id \<Rightarrow> stage" where
"pwd_owner_ii n \<equiv> SOME x. pred_owner_ii n (pwd_spy_i n) x"

definition pwd_spy_ii :: "agent_id \<Rightarrow> stage" where
"pwd_spy_ii n \<equiv>
  case pwd_owner_ii n of (s, S, A, _) \<Rightarrow>
    (insert (Spy, \<lbrace>Num 2, PubKey S\<rbrace>) s, S, A, S, 0, 0)"

definition pwd_owner_iii :: "agent_id \<Rightarrow> stage" where
"pwd_owner_iii n \<equiv> SOME x. pred_owner_iii n (pwd_spy_ii n) x"

definition pwd_spy_iii :: "agent_id \<Rightarrow> stage" where
"pwd_spy_iii n \<equiv>
  case pwd_owner_iii n of (s, S, A, B, C, _) \<Rightarrow>
    (insert (Spy, \<lbrace>Num 4, PubKey S\<rbrace>) s, S, A, B, C, S)"

definition pwd_owner_iv :: "agent_id \<Rightarrow> stage" where
"pwd_owner_iv n \<equiv> stage_owner_iv n (pwd_spy_iii n)"


definition pwd_spy_sep_map :: "agent_id \<Rightarrow> stage" where
"pwd_spy_sep_map n \<equiv>
  case pwd_owner_iv n of (s, S, A, B, C, D) \<Rightarrow>
    (insert (Spy, PubKey A) s, S, A, B, C, D)"

definition pwd_spy_sep_agr :: "agent_id \<Rightarrow> stage" where
"pwd_spy_sep_agr n \<equiv>
  case pwd_spy_sep_map n of (s, S, A, B, C, D) \<Rightarrow>
    (insert (Spy, PubKey C) s, S, A, B, C, D)"

definition pwd_spy_sesk :: "agent_id \<Rightarrow> stage" where
"pwd_spy_sesk n \<equiv>
  let (s, S, A, B, C, D) = pwd_spy_sep_agr n;
    SK = (Some S, {A, B}, {C, D}) in
    (insert (Spy, SesKey SK) s, S, A, B, C, D)"

definition pwd_spy_mult :: "agent_id \<Rightarrow> stage" where
"pwd_spy_mult n \<equiv>
  case pwd_spy_sesk n of (s, S, A, B, C, D) \<Rightarrow>
    (insert (Spy, Auth_PriK n \<otimes> B) s, S, A, B, C, D)"

definition pwd_spy_enc_pubk :: "agent_id \<Rightarrow> stage" where
"pwd_spy_enc_pubk n \<equiv>
  let (s, S, A, B, C, D) = pwd_spy_mult n; SK = (Some S, {A, B}, {C, D}) in
    (insert (Spy, Crypt (SesK SK) (PubKey C)) s, S, A, B, C, D)"

definition pwd_spy_enc_mult :: "agent_id \<Rightarrow> stage" where
"pwd_spy_enc_mult n \<equiv>
  let (s, S, A, B, C, D) = pwd_spy_enc_pubk n;
    SK = (Some S, {A, B}, {C, D}) in
    (insert (Spy, Crypt (SesK SK) (Auth_PriK n \<otimes> B)) s, S, A, B, C, D)"

definition pwd_spy_enc_sign :: "agent_id \<Rightarrow> stage" where
"pwd_spy_enc_sign n \<equiv>
  let (s, S, A, B, C, D) = pwd_spy_enc_mult n;
    SK = (Some S, {A, B}, {C, D}) in
    (insert (Spy, Crypt (SesK SK) (Sign n (Auth_PriK n))) s, S, A, B, C, D)"

definition pwd_spy_con :: "agent_id \<Rightarrow> stage" where
"pwd_spy_con n \<equiv>
  let (s, S, A, B, C, D) = pwd_spy_enc_sign n;
    SK = (Some S, {A, B}, {C, D}) in
    (insert (Spy, \<lbrace>Crypt (SesK SK) (Auth_PriK n \<otimes> B),
      Crypt (SesK SK) (Sign n (Auth_PriK n))\<rbrace>) s, S, A, B, C, D)"

definition pwd_spy_iv :: "agent_id \<Rightarrow> stage" where
"pwd_spy_iv n \<equiv>
  let (s, S, A, B, C, D) = pwd_spy_con n; SK = (Some S, {A, B}, {C, D}) in
    (insert (Spy, Token n (Auth_PriK n) B C SK) s, S, A, B, C, D)"


definition pwd_owner_v :: "agent_id \<Rightarrow> stage" where
"pwd_owner_v n \<equiv> stage_owner_v n (pwd_spy_iv n)"

definition pwd_spy_dec :: "agent_id \<Rightarrow> stage" where
"pwd_spy_dec n \<equiv>
  case pwd_owner_v n of (s, S, A, B, C, D) \<Rightarrow>
    (insert (Spy, Pwd n) s, S, A, B, C, D)"

definition pwd_spy_id_prik :: "agent_id \<Rightarrow> stage" where
"pwd_spy_id_prik n \<equiv>
  case pwd_spy_dec n of (s, S, A, B, C, D) \<Rightarrow>
    (insert (Spy, \<langle>n, PriKey S\<rangle>) s, S, A, B, C, D)"

definition pwd_spy_id_pubk :: "agent_id \<Rightarrow> stage" where
"pwd_spy_id_pubk n \<equiv>
  case pwd_spy_id_prik n of (s, S, A, B, C, D) \<Rightarrow>
    (insert (Spy, \<langle>n, PubKey S\<rangle>) s, S, A, B, C, D)"

definition pwd_spy_id_sesk :: "agent_id \<Rightarrow> stage" where
"pwd_spy_id_sesk n \<equiv>
  let (s, S, A, B, C, D) = pwd_spy_id_pubk n;
    SK = (Some S, {A, B}, {C, D}) in
    (insert (Spy, \<langle>n, SesKey SK\<rangle>) s, S, A, B, C, D)"

definition pwd_spy_id_pwd :: "agent_id \<Rightarrow> stage" where
"pwd_spy_id_pwd n \<equiv>
  case pwd_spy_id_sesk n of (s, S, A, B, C, D) \<Rightarrow>
    (insert (Spy, \<langle>n, Pwd n\<rangle>) s, S, A, B, C, D)"


proposition key_sets_crypts_subset:
 "\<lbrakk>U \<in> key_sets X (crypts (Log -` spied H)); H \<subseteq> H'\<rbrakk> \<Longrightarrow>
    U \<in> key_sets X (crypts (Log -` spied H'))"
      (is "\<lbrakk>_ \<in> ?A; _\<rbrakk> \<Longrightarrow> _")
by (rule subsetD [of ?A], rule key_sets_mono, rule crypts_mono, blast)


fun pwd_spy_i_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_i_state n (S, _) = {Spy} \<times> ({PriKey S, PubKey S, Key (Auth_ShaKey n),
  Auth_PriKey n, Sign n (Auth_PriK n), Crypt (Auth_ShaKey n) (PriKey S),
  \<langle>n, Key (Auth_ShaKey n)\<rangle>} \<union> range Num)"

proposition pwd_spy_i_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_i n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule r_into_rtrancl, subgoal_tac "(s\<^sub>0, ?t) \<in> rel_enc", simp_all add: rel_def
 pwd_spy_i_def, blast)

proposition pwd_spy_i_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_i n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_i_state n (S, A, B, C, D) \<subseteq> s"
by (simp add: pwd_spy_i_def, blast)

proposition pwd_spy_i_unused:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> \<exists>A. PriKey A \<notin> used (fst (pwd_spy_i n))"
by (drule pwd_spy_i_rel, rule prikey_unused)


fun pwd_owner_ii_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_owner_ii_state n (S, A, B, C, D) =
  pwd_spy_i_state n (S, A, B, C, D) \<union> {Owner n, Spy} \<times> {\<lbrace>Num 1, PubKey A\<rbrace>}"

proposition pwd_owner_ii_ex:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    pred_owner_ii n (pwd_spy_i n) (pwd_owner_ii n)"
by (drule pwd_spy_i_unused, erule exE, subst pwd_owner_ii_def, rule someI_ex,
 auto simp add: split_def)

proposition pwd_owner_ii_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_owner_ii n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_i_rel, frule pwd_spy_i_msg,
 drule pwd_owner_ii_ex, subgoal_tac "(fst (pwd_spy_i n), ?t) \<in> rel_owner_ii",
 simp_all add: rel_def split_def, erule exE, rule exI, auto)

proposition pwd_owner_ii_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_owner_ii n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_owner_ii_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (frule pwd_spy_i_msg, drule pwd_owner_ii_ex, simp add: split_def, erule exE,
 simp add: Image_def, simp only: Collect_disj_eq crypts_union key_sets_union,
 simp add: crypts_insert key_sets_insert, blast)


fun pwd_spy_ii_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_ii_state n (S, A, B, C, D) =
  pwd_owner_ii_state n (S, A, B, C, D) \<union> {Spy} \<times> {PriKey B,
    \<lbrace>Num 2, PubKey B\<rbrace>}"

proposition pwd_spy_ii_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_ii n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_owner_ii_rel, drule pwd_owner_ii_msg,
 subgoal_tac "(fst (pwd_owner_ii n), ?t) \<in> rel_con", simp_all add: rel_def
 pwd_spy_ii_def split_def, blast)

proposition pwd_spy_ii_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_ii n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_ii_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_owner_ii_msg, simp add: pwd_spy_ii_def split_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)

proposition pwd_spy_ii_unused:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> \<exists>C. PriKey C \<notin> used (fst (pwd_spy_ii n))"
by (drule pwd_spy_ii_rel, rule prikey_unused)


fun pwd_owner_iii_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_owner_iii_state n (S, A, B, C, D) =
  pwd_spy_ii_state n (S, A, B, C, D) \<union> {Owner n, Spy} \<times> {\<lbrace>Num 3, PubKey C\<rbrace>}"

proposition pwd_owner_iii_ex:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    pred_owner_iii n (pwd_spy_ii n) (pwd_owner_iii n)"
by (drule pwd_spy_ii_unused, erule exE, subst pwd_owner_iii_def, rule someI_ex,
 auto simp add: split_def)

proposition pwd_owner_iii_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_owner_iii n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_ii_rel, frule pwd_spy_ii_msg,
 drule pwd_owner_iii_ex, subgoal_tac "(fst (pwd_spy_ii n), ?t) \<in> rel_owner_iii",
 simp_all add: rel_def split_def, rule exI, rule exI, auto)

proposition pwd_owner_iii_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_owner_iii n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_owner_iii_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (frule pwd_spy_ii_msg, drule pwd_owner_iii_ex, simp add: split_def, erule exE,
 simp, (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_iii_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_iii_state n (S, A, B, C, D) =
  pwd_owner_iii_state n (S, A, B, C, D) \<union> {Spy} \<times> {PriKey D,
    \<lbrace>Num 4, PubKey D\<rbrace>}"

proposition pwd_spy_iii_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_iii n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_owner_iii_rel, drule pwd_owner_iii_msg,
 subgoal_tac "(fst (pwd_owner_iii n), ?t) \<in> rel_con", simp_all add: rel_def
 pwd_spy_iii_def split_def, blast)

proposition pwd_spy_iii_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_iii n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_iii_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_owner_iii_msg, simp add: pwd_spy_iii_def split_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_owner_iv_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_owner_iv_state n (S, A, B, C, D) = (let SK = (Some S, {A, B}, {C, D}) in
  insert (Owner n, SesKey SK) (pwd_spy_iii_state n (S, A, B, C, D)))"

lemma pwd_owner_iv_rel_1:
 "\<lbrakk>n \<in> bad_prikey \<inter> bad_id_shakey; pwd_spy_iii n = (s, S, A, B, C, D)\<rbrakk> \<Longrightarrow>
    s\<^sub>0 \<Turnstile> fst (pwd_owner_iv n)"
      (is "\<lbrakk>_; _\<rbrakk> \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_iii_rel, drule pwd_spy_iii_msg,
 subgoal_tac "(s, ?t) \<in> rel_owner_iv", simp_all add: rel_def pwd_owner_iv_def
 Let_def, rule exI [of _ n], rule exI [of _ S], rule exI [of _ A], rule exI [of _ B],
 rule exI [of _ C], rule exI [of _ D], rule exI [of _ "Auth_ShaKey n"], auto)

proposition pwd_owner_iv_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_owner_iv n)"
by (insert pwd_owner_iv_rel_1, cases "pwd_spy_iii n", simp)

proposition pwd_owner_iv_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_owner_iv n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_owner_iv_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_iii_msg, simp add: pwd_owner_iv_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_sep_map_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_sep_map_state n (S, A, B, C, D) =
  insert (Spy, PubKey A) (pwd_owner_iv_state n (S, A, B, C, D))"

proposition pwd_spy_sep_map_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_sep_map n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_owner_iv_rel, drule pwd_owner_iv_msg,
 subgoal_tac "(fst (pwd_owner_iv n), ?t) \<in> rel_sep", simp_all add: rel_def
 pwd_spy_sep_map_def split_def, blast)

proposition pwd_spy_sep_map_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_sep_map n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_sep_map_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_owner_iv_msg, simp add: pwd_spy_sep_map_def split_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_sep_agr_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_sep_agr_state n (S, A, B, C, D) =
  insert (Spy, PubKey C) (pwd_spy_sep_map_state n (S, A, B, C, D))"

proposition pwd_spy_sep_agr_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_sep_agr n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_sep_map_rel, drule pwd_spy_sep_map_msg,
 subgoal_tac "(fst (pwd_spy_sep_map n), ?t) \<in> rel_sep", simp_all add: rel_def
 pwd_spy_sep_agr_def split_def, blast)

proposition pwd_spy_sep_agr_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_sep_agr n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_sep_agr_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_sep_map_msg, simp add: pwd_spy_sep_agr_def split_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_sesk_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_sesk_state n (S, A, B, C, D) = (let SK = (Some S, {A, B}, {C, D}) in
  insert (Spy, SesKey SK) (pwd_spy_sep_agr_state n (S, A, B, C, D)))"

proposition pwd_spy_sesk_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_sesk n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_sep_agr_rel, drule pwd_spy_sep_agr_msg,
 subgoal_tac "(fst (pwd_spy_sep_agr n), ?t) \<in> rel_sesk", simp_all add: rel_def
 pwd_spy_sesk_def split_def Let_def, blast)

proposition pwd_spy_sesk_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_sesk n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_sesk_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_sep_agr_msg, simp add: pwd_spy_sesk_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_mult_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_mult_state n (S, A, B, C, D) =
  insert (Spy, Auth_PriK n \<otimes> B) (pwd_spy_sesk_state n (S, A, B, C, D))"

proposition pwd_spy_mult_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_mult n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_sesk_rel, drule pwd_spy_sesk_msg,
 subgoal_tac "(fst (pwd_spy_sesk n), ?t) \<in> rel_mult", simp_all add: rel_def
 pwd_spy_mult_def split_def, blast)

proposition pwd_spy_mult_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_mult n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_mult_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_sesk_msg, simp add: pwd_spy_mult_def split_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_enc_pubk_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_enc_pubk_state n (S, A, B, C, D) =
  (let SK = (Some S, {A, B}, {C, D}) in
  insert (Spy, Crypt (SesK SK) (PubKey C))
    (pwd_spy_mult_state n (S, A, B, C, D)))"

proposition pwd_spy_enc_pubk_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_enc_pubk n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_mult_rel, drule pwd_spy_mult_msg,
 subgoal_tac "(fst (pwd_spy_mult n), ?t) \<in> rel_enc", simp_all add: rel_def
 pwd_spy_enc_pubk_def split_def Let_def, blast)

proposition pwd_spy_enc_pubk_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_enc_pubk n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_enc_pubk_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_mult_msg, simp add: pwd_spy_enc_pubk_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_enc_mult_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_enc_mult_state n (S, A, B, C, D) =
  (let SK = (Some S, {A, B}, {C, D}) in
  insert (Spy, Crypt (SesK SK) (Auth_PriK n \<otimes> B))
    (pwd_spy_enc_pubk_state n (S, A, B, C, D)))"

proposition pwd_spy_enc_mult_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_enc_mult n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_enc_pubk_rel, drule pwd_spy_enc_pubk_msg,
 subgoal_tac "(fst (pwd_spy_enc_pubk n), ?t) \<in> rel_enc", simp_all add: rel_def
 pwd_spy_enc_mult_def split_def Let_def, blast)

proposition pwd_spy_enc_mult_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_enc_mult n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_enc_mult_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_enc_pubk_msg, simp add: pwd_spy_enc_mult_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_enc_sign_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_enc_sign_state n (S, A, B, C, D) =
  (let SK = (Some S, {A, B}, {C, D}) in
  insert (Spy, Crypt (SesK SK) (Sign n (Auth_PriK n)))
    (pwd_spy_enc_mult_state n (S, A, B, C, D)))"

proposition pwd_spy_enc_sign_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_enc_sign n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_enc_mult_rel, drule pwd_spy_enc_mult_msg,
 subgoal_tac "(fst (pwd_spy_enc_mult n), ?t) \<in> rel_enc", simp_all add: rel_def
 pwd_spy_enc_sign_def split_def Let_def, blast)

proposition pwd_spy_enc_sign_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_enc_sign n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_enc_sign_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_enc_mult_msg, simp add: pwd_spy_enc_sign_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_con_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_con_state n (S, A, B, C, D) = (let SK = (Some S, {A, B}, {C, D}) in
  insert (Spy, \<lbrace>Crypt (SesK SK) (Auth_PriK n \<otimes> B),
    Crypt (SesK SK) (Sign n (Auth_PriK n))\<rbrace>)
    (pwd_spy_enc_sign_state n (S, A, B, C, D)))"

proposition pwd_spy_con_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_con n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_enc_sign_rel, drule pwd_spy_enc_sign_msg,
 subgoal_tac "(fst (pwd_spy_enc_sign n), ?t) \<in> rel_con", simp_all add: rel_def
 pwd_spy_con_def split_def Let_def, blast)

proposition pwd_spy_con_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_con n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_con_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_enc_sign_msg, simp add: pwd_spy_con_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_iv_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_iv_state n (S, A, B, C, D) = (let SK = (Some S, {A, B}, {C, D}) in
  insert (Spy, Token n (Auth_PriK n) B C SK)
    (pwd_spy_con_state n (S, A, B, C, D)))"

proposition pwd_spy_iv_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_iv n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_con_rel, drule pwd_spy_con_msg,
 subgoal_tac "(fst (pwd_spy_con n), ?t) \<in> rel_con", simp_all add: rel_def
 pwd_spy_iv_def split_def Let_def, blast)

proposition pwd_spy_iv_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_iv n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_iv_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s))"
by (drule pwd_spy_con_msg, simp add: pwd_spy_iv_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_owner_v_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_owner_v_state n (S, A, B, C, D) = (let SK = (Some S, {A, B}, {C, D}) in
  insert (Spy, Crypt (SesK SK) (Pwd n)) (pwd_spy_iv_state n (S, A, B, C, D)))"

proposition pwd_owner_v_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_owner_v n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_iv_rel, drule pwd_spy_iv_msg,
 subgoal_tac "(fst (pwd_spy_iv n), ?t) \<in> rel_owner_v", simp_all add: rel_def
 pwd_owner_v_def split_def Let_def, (rule exI)+, blast)

proposition pwd_owner_v_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    let (s, S, A, B, C, D) = pwd_owner_v n; SK = (Some S, {A, B}, {C, D}) in
      pwd_owner_v_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s)) \<and>
      {SesKey SK} \<in> key_sets (Pwd n) (crypts (Log -` spied s))"
by (drule pwd_spy_iv_msg, simp add: pwd_owner_v_def split_def Let_def, (erule conjE)+,
 (rule conjI, (erule key_sets_crypts_subset)?, blast)+, simp add: Image_def, simp
 only: Collect_disj_eq crypts_union key_sets_union, simp add: crypts_insert
 key_sets_insert)


abbreviation pwd_spy_dec_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_dec_state n x \<equiv> insert (Spy, Pwd n) (pwd_owner_v_state n x)"

proposition pwd_spy_dec_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_dec n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_owner_v_rel, drule pwd_owner_v_msg,
 subgoal_tac "(fst (pwd_owner_v n), ?t) \<in> rel_dec", simp_all add: rel_def
 pwd_spy_dec_def split_def Let_def, (rule exI)+, auto)

proposition pwd_spy_dec_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    let (s, S, A, B, C, D) = pwd_spy_dec n; SK = (Some S, {A, B}, {C, D}) in
      pwd_spy_dec_state n (S, A, B, C, D) \<subseteq> s \<and>
      {Key (Auth_ShaKey n)} \<in> key_sets (PriKey S) (crypts (Log -` spied s)) \<and>
      {SesKey SK} \<in> key_sets (Pwd n) (crypts (Log -` spied s))"
by (drule pwd_owner_v_msg, simp add: pwd_spy_dec_def split_def Let_def,
 (erule conjE)+, ((rule conjI)?, (erule key_sets_crypts_subset)?, blast)+)


fun pwd_spy_id_prik_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_id_prik_state n (S, A, B, C, D) =
  insert (Spy, \<langle>n, PriKey S\<rangle>) (pwd_spy_dec_state n (S, A, B, C, D))"

proposition pwd_spy_id_prik_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_id_prik n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_dec_rel, drule pwd_spy_dec_msg,
 subgoal_tac "(fst (pwd_spy_dec n), ?t) \<in> rel_id_crypt", simp_all add: rel_def
 pwd_spy_id_prik_def split_def Let_def, (rule exI)+, blast)

proposition pwd_spy_id_prik_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    let (s, S, A, B, C, D) = pwd_spy_id_prik n;
      SK = (Some S, {A, B}, {C, D}) in
      pwd_spy_id_prik_state n (S, A, B, C, D) \<subseteq> s \<and>
      {SesKey SK} \<in> key_sets (Pwd n) (crypts (Log -` spied s))"
by (drule pwd_spy_dec_msg, simp add: pwd_spy_id_prik_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_id_pubk_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_id_pubk_state n (S, A, B, C, D) =
  insert (Spy, \<langle>n, PubKey S\<rangle>) (pwd_spy_id_prik_state n (S, A, B, C, D))"

proposition pwd_spy_id_pubk_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_id_pubk n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_id_prik_rel, drule pwd_spy_id_prik_msg,
 subgoal_tac "(fst (pwd_spy_id_prik n), ?t) \<in> rel_id_invk", simp_all add: rel_def
 pwd_spy_id_pubk_def split_def Let_def, (rule exI)+, auto)

proposition pwd_spy_id_pubk_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    let (s, S, A, B, C, D) = pwd_spy_id_pubk n;
      SK = (Some S, {A, B}, {C, D}) in
      pwd_spy_id_pubk_state n (S, A, B, C, D) \<subseteq> s \<and>
      {SesKey SK} \<in> key_sets (Pwd n) (crypts (Log -` spied s))"
by (drule pwd_spy_id_prik_msg, simp add: pwd_spy_id_pubk_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


fun pwd_spy_id_sesk_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_id_sesk_state n (S, A, B, C, D) =
  (let SK = (Some S, {A, B}, {C, D}) in
  insert (Spy, \<langle>n, SesKey SK\<rangle>) (pwd_spy_id_pubk_state n (S, A, B, C, D)))"

proposition pwd_spy_id_sesk_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_id_sesk n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_id_pubk_rel, drule pwd_spy_id_pubk_msg,
 subgoal_tac "(fst (pwd_spy_id_pubk n), ?t) \<in> rel_id_sesk", simp_all add: rel_def
 pwd_spy_id_sesk_def split_def Let_def, rule exI, rule exI, rule exI
 [of _ "Some (fst (snd (pwd_spy_id_pubk n)))"], auto)

proposition pwd_spy_id_sesk_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    let (s, S, A, B, C, D) = pwd_spy_id_sesk n;
      SK = (Some S, {A, B}, {C, D}) in
      pwd_spy_id_sesk_state n (S, A, B, C, D) \<subseteq> s \<and>
      {SesKey SK} \<in> key_sets (Pwd n) (crypts (Log -` spied s))"
by (drule pwd_spy_id_pubk_msg, simp add: pwd_spy_id_sesk_def split_def Let_def,
 (erule conjE)+, ((rule conjI | erule key_sets_crypts_subset), blast)+)


abbreviation pwd_spy_id_pwd_state :: "agent_id \<Rightarrow> seskey_tuple \<Rightarrow> state" where
"pwd_spy_id_pwd_state n x \<equiv> insert (Spy, \<langle>n, Pwd n\<rangle>) (pwd_spy_id_sesk_state n x)"

proposition pwd_spy_id_pwd_rel:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> s\<^sub>0 \<Turnstile> fst (pwd_spy_id_pwd n)"
    (is "_ \<Longrightarrow> _ \<Turnstile> ?t")
by (rule rtrancl_into_rtrancl, erule pwd_spy_id_sesk_rel, drule pwd_spy_id_sesk_msg,
 subgoal_tac "(fst (pwd_spy_id_sesk n), ?t) \<in> rel_id_crypt", simp_all add: rel_def
 pwd_spy_id_pwd_def split_def Let_def, (rule exI)+, blast)

proposition pwd_spy_id_pwd_msg:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow>
    case pwd_spy_id_pwd n of (s, S, A, B, C, D) \<Rightarrow>
      pwd_spy_id_pwd_state n (S, A, B, C, D) \<subseteq> s"
by (drule pwd_spy_id_sesk_msg, simp add: pwd_spy_id_pwd_def split_def Let_def,
 blast)


theorem pwd_compromised:
 "n \<in> bad_prikey \<inter> bad_id_shakey \<Longrightarrow> \<exists>s. s\<^sub>0 \<Turnstile> s \<and> {Pwd n, \<langle>n, Pwd n\<rangle>} \<subseteq> spied s"
by (rule exI [of _ "fst (pwd_spy_id_pwd n)"], rule conjI, erule pwd_spy_id_pwd_rel,
 drule pwd_spy_id_pwd_msg, simp add: split_def)


end