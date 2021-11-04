(*  Title:       Logging-independent Message Anonymity in the Relational Method
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Possibility of anonymity compromise for token pseudonymous identifiers"

theory Possibility
  imports Anonymity
begin

text \<open>
\null

This section proves possibility properties @{text tok_id_identified}, @{text sec_id_identified},
which altogether state that the spy can map a token pseudonymous identifier to the related token if
either attack option described in section \ref{Protocol} is viable. Both properties are proven by
construction, namely by creating as many sample protocol runs such as to satisfy their conclusions
if their assumptions are fulfilled.

\null
\<close>

definition tok_id_pubk_prik :: "agent_id \<Rightarrow> agent_id \<Rightarrow> state" where
"tok_id_pubk_prik n m \<equiv>
  insert (Spy, \<langle>n, ID n (Sec_PubKey m)\<rangle>) s\<^sub>0"

definition tok_id_hash :: "agent_id \<Rightarrow> agent_id \<Rightarrow> state" where
"tok_id_hash n m \<equiv>
  insert (Spy, \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle>) (tok_id_pubk_prik n m)"


proposition tok_id_pubk_prik_rel:
 "n \<in> bad_tok_prik \<Longrightarrow> s\<^sub>0 \<Turnstile> tok_id_pubk_prik n m"
by (subgoal_tac "(s\<^sub>0, tok_id_pubk_prik n m) \<in> rel_id_pubk_prik",
 rule r_into_rtrancl, auto simp: tok_id_pubk_prik_def rel_def image_def, blast)

proposition tok_id_pubk_prik_msg:
 "n \<in> bad_tok_prik \<Longrightarrow>
    {ID n (Sec_PubKey m), Hash (ID n (Sec_PubKey m)),
      \<langle>n, ID n (Sec_PubKey m)\<rangle>} \<subseteq> spied (tok_id_pubk_prik n m)"
by (auto simp: tok_id_pubk_prik_def)

proposition tok_id_hash_rel:
 "n \<in> bad_tok_prik \<Longrightarrow> s\<^sub>0 \<Turnstile> tok_id_hash n m"
by (rule rtrancl_into_rtrancl, erule tok_id_pubk_prik_rel [of _ m],
 subgoal_tac "(tok_id_pubk_prik n m, tok_id_hash n m) \<in> rel_id_hash",
 frule_tac [2] tok_id_pubk_prik_msg [of _ m], auto simp: tok_id_hash_def rel_def)


theorem tok_id_identified:
 "n \<in> bad_tok_prik \<Longrightarrow> \<exists>s. s\<^sub>0 \<Turnstile> s \<and> \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle> \<in> spied s"
by (rule exI [of _ "tok_id_hash n m"], drule tok_id_hash_rel [of _ m],
 simp add: tok_id_hash_def)


definition sec_pubk_less :: "agent_id \<Rightarrow> state" where
"sec_pubk_less n \<equiv>
  insert (Spy, PubKey {Tok_PriK n, Rev_PriK}) s\<^sub>0"

definition sec_id_pubk_less :: "agent_id \<Rightarrow> state" where
"sec_id_pubk_less n \<equiv>
  insert (Spy, \<langle>n, PubKey {Tok_PriK n, Rev_PriK}\<rangle>) (sec_pubk_less n)"

definition sec_id_pubk_more :: "agent_id \<Rightarrow> agent_id \<Rightarrow> state" where
"sec_id_pubk_more n m \<equiv>
  insert (Spy, \<langle>n, ID n (Sec_PubKey m)\<rangle>) (sec_id_pubk_less n)"

definition sec_id_hash :: "agent_id \<Rightarrow> agent_id \<Rightarrow> state" where
"sec_id_hash n m \<equiv>
  insert (Spy, \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle>) (sec_id_pubk_more n m)"


lemma sec_id_identified_1:
 "{Tok_PriK n, Sec_PriK m, Rev_PriK} \<noteq> {Tok_PriK n', Rev_PriK}"
by (simp add: set_eq_iff, rule exI [of _ "Sec_PriK m"], insert
 sec_prik_rev sec_prik_tok_prik, simp add: image_def, drule spec [of _ m], auto)

lemma sec_id_identified_2:
 "(Spy, PubKey {Tok_PriK n, Rev_PriK}) \<notin> s\<^sub>0"
by (insert tok_prik_rev sec_id_identified_1, simp add: image_def,
 drule spec [of _ n], auto simp: set_eq_iff)

lemma sec_id_identified_3:
 "{Tok_PriK n, Rev_PriK} =
    {Tok_PriK n, Sec_PriK m, Rev_PriK} - {Sec_PriK m}"
by (insert sec_prik_rev sec_prik_tok_prik, auto)

lemma sec_id_identified_4:
 "PubK {Tok_PriK n, Sec_PriK m, Rev_PriK} =
    PubK (insert (Sec_PriK m) {Tok_PriK n, Rev_PriK})"
by auto

proposition sec_pubk_less_rel:
 "\<lbrakk>{m, m'} \<subseteq> bad_sec_prik; (n, m) \<notin> bad_id; (n, m') \<in> bad_id\<rbrakk> \<Longrightarrow>
    s\<^sub>0 \<Turnstile> sec_pubk_less n"
by (subgoal_tac "(s\<^sub>0, sec_pubk_less n) \<in> rel_pubk_less", rule r_into_rtrancl,
 simp add: rel_def, subst sec_pubk_less_def, subst sec_id_identified_3 [of _ m'],
 simp, (rule exI)+, subst insert_ident, subst sec_id_identified_3 [symmetric],
 insert sec_id_identified_2, auto)

proposition sec_pubk_less_msg:
 "\<lbrakk>{m, m'} \<subseteq> bad_sec_prik; (n, m) \<notin> bad_id; (n, m') \<in> bad_id\<rbrakk> \<Longrightarrow>
    {Sec_PriKey m, Sec_PriKey m', PubKey {Tok_PriK n, Rev_PriK},
      ID n (Sec_PubKey m), Hash (ID n (Sec_PubKey m)),
      \<langle>n, ID n (Sec_PubKey m')\<rangle>} \<subseteq> spied (sec_pubk_less n) \<and>
    {\<langle>n, PubKey {Tok_PriK n, Rev_PriK}\<rangle>, \<langle>n, ID n (Sec_PubKey m)\<rangle>,
      \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle>} \<inter>
      spied (sec_pubk_less n) = {}"
by (insert sec_id_identified_2, auto simp: sec_pubk_less_def image_def
 dest: sec_prik_eq)

proposition sec_id_pubk_less_rel:
 "\<lbrakk>{m, m'} \<subseteq> bad_sec_prik; (n, m) \<notin> bad_id; (n, m') \<in> bad_id\<rbrakk> \<Longrightarrow>
    s\<^sub>0 \<Turnstile> sec_id_pubk_less n"
by (rule rtrancl_into_rtrancl, erule sec_pubk_less_rel, assumption+,
 subgoal_tac "(sec_pubk_less n, sec_id_pubk_less n) \<in> rel_id_pubk_less",
 frule_tac [2] sec_pubk_less_msg, simp_all add: sec_id_pubk_less_def rel_def,
 (rule exI)+, subst sec_id_identified_3 [of _ m'], subst (asm) (1 2)
 sec_id_identified_3, subst insert_ident, insert sec_prik_tok_prik, auto)

proposition sec_id_pubk_less_msg:
 "\<lbrakk>{m, m'} \<subseteq> bad_sec_prik; (n, m) \<notin> bad_id; (n, m') \<in> bad_id\<rbrakk> \<Longrightarrow>
    {Sec_PriKey m, ID n (Sec_PubKey m), Hash (ID n (Sec_PubKey m)),
      \<langle>n, PubKey {Tok_PriK n, Rev_PriK}\<rangle>} \<subseteq>
      spied (sec_id_pubk_less n) \<and>
    {\<langle>n, ID n (Sec_PubKey m)\<rangle>, \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle>} \<inter>
      spied (sec_id_pubk_less n) = {}"
by (drule sec_pubk_less_msg, insert sec_id_identified_1,
 auto simp: sec_id_pubk_less_def)

proposition sec_id_pubk_more_rel:
 "\<lbrakk>{m, m'} \<subseteq> bad_sec_prik; (n, m) \<notin> bad_id; (n, m') \<in> bad_id\<rbrakk> \<Longrightarrow>
    s\<^sub>0 \<Turnstile> sec_id_pubk_more n m"
by (rule rtrancl_into_rtrancl, erule sec_id_pubk_less_rel, assumption+,
 subgoal_tac "(sec_id_pubk_less n, sec_id_pubk_more n m) \<in> rel_id_pubk_more",
 frule_tac [2] sec_id_pubk_less_msg, simp_all add: sec_id_pubk_more_def rel_def,
 (rule exI)+, subst sec_id_identified_4, subst (asm) (1 3) sec_id_identified_4,
 subst insert_ident, simp_all)

proposition sec_id_pubk_more_msg:
 "\<lbrakk>{m, m'} \<subseteq> bad_sec_prik; (n, m) \<notin> bad_id; (n, m') \<in> bad_id\<rbrakk> \<Longrightarrow>
    {ID n (Sec_PubKey m), Hash (ID n (Sec_PubKey m)),
      \<langle>n, ID n (Sec_PubKey m)\<rangle>} \<subseteq> spied (sec_id_pubk_more n m) \<and>
    \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle> \<notin> spied (sec_id_pubk_more n m)"
by (drule sec_id_pubk_less_msg, auto simp: sec_id_pubk_more_def)

proposition sec_id_hash_rel:
 "\<lbrakk>{m, m'} \<subseteq> bad_sec_prik; (n, m) \<notin> bad_id; (n, m') \<in> bad_id\<rbrakk> \<Longrightarrow>
    s\<^sub>0 \<Turnstile> sec_id_hash n m"
by (rule rtrancl_into_rtrancl, erule sec_id_pubk_more_rel, assumption+,
 subgoal_tac "(sec_id_pubk_more n m, sec_id_hash n m) \<in> rel_id_hash",
 frule_tac [2] sec_id_pubk_more_msg, auto simp: sec_id_hash_def rel_def)


theorem sec_id_identified:
 "\<lbrakk>{m, m'} \<subseteq> bad_sec_prik; (n, m') \<in> bad_id\<rbrakk> \<Longrightarrow>
    \<exists>s. s\<^sub>0 \<Turnstile> s \<and> \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle> \<in> spied s"
by (cases "(n, m) \<in> bad_id", blast, rule exI [of _ "sec_id_hash n m"],
 drule sec_id_hash_rel, simp_all add: sec_id_hash_def)

end
