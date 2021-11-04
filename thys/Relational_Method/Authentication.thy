(*  Title:       The Relational Method with Message Anonymity for the Verification of Cryptographic Protocols
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Confidentiality and authenticity properties"

theory Authentication
  imports Definitions
begin

text \<open>
\label{Authentication}
\<close>


proposition rtrancl_start [rule_format]:
 "(x, y) \<in> r\<^sup>* \<Longrightarrow> P y \<longrightarrow> \<not> P x \<longrightarrow>
    (\<exists>u v. (x, u) \<in> r\<^sup>* \<and> (u, v) \<in> r \<and> (v, y) \<in> r\<^sup>* \<and> \<not> P u \<and> P v)"
  (is "_ \<Longrightarrow> _ \<longrightarrow> _ \<longrightarrow> (\<exists>u v. ?Q x y u v)")
proof (erule rtrancl_induct, simp, (rule impI)+)
  fix y z
  assume
    A: "(x, y) \<in> r\<^sup>*" and
    B: "(y, z) \<in> r" and
    C: "P z"
  assume "P y \<longrightarrow> \<not> P x \<longrightarrow>(\<exists>u v. ?Q x y u v)" and "\<not> P x"
  hence D: "P y \<longrightarrow> (\<exists>u v. ?Q x y u v)" by simp
  show "\<exists>u v. ?Q x z u v"
  proof (cases "P y")
    case True
    with D obtain u v where "?Q x y u v" by blast
    moreover from this and B have "(v, z) \<in> r\<^sup>*" by auto
    ultimately show ?thesis by blast
  next
    case False
    with A and B and C have "?Q x z y z" by simp
    thus ?thesis by blast
  qed
qed


proposition state_subset:
 "s \<Turnstile> s' \<Longrightarrow> s \<subseteq> s'"
by (erule rtrancl_induct, auto simp add: rel_def image_def)

proposition spied_subset:
 "s \<Turnstile> s' \<Longrightarrow> spied s \<subseteq> spied s'"
by (rule Image_mono, erule state_subset, simp)

proposition used_subset:
 "s \<Turnstile> s' \<Longrightarrow> used s \<subseteq> used s'"
by (rule Range_mono, rule state_subset)

proposition asset_ii_init:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; (Asset n, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s\<rbrakk> \<Longrightarrow>
    PriKey A \<notin> spied s\<^sub>0"
by (drule rtrancl_start, assumption, simp add: image_def, (erule exE)+,
 erule conjE, rule notI, drule spied_subset, drule subsetD, assumption,
 auto simp add: rel_def)

proposition auth_prikey_used:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> Auth_PriKey n \<in> used s"
by (drule used_subset, erule subsetD, simp add: Range_iff image_def, blast)

proposition asset_i_used:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset n, Crypt (Auth_ShaKey n) (PriKey A)) \<in> s \<longrightarrow>
  PriKey A \<in> used s"
by (erule rtrancl_induct, auto simp add: rel_def image_def)

proposition owner_ii_used:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  PriKey A \<in> used s"
by (erule rtrancl_induct, auto simp add: rel_def image_def)

proposition asset_ii_used:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset n, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  PriKey A \<in> used s"
by (erule rtrancl_induct, auto simp add: rel_def image_def)

proposition owner_iii_used:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Owner n, \<lbrace>Num 3, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  PriKey A \<in> used s"
by (erule rtrancl_induct, auto simp add: rel_def image_def)

proposition asset_iii_used:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset n, \<lbrace>Num 4, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  PriKey A \<in> used s"
by (erule rtrancl_induct, auto simp add: rel_def image_def)

proposition asset_i_unique [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset m, Crypt (Auth_ShaKey m) (PriKey A)) \<in> s \<longrightarrow>
    (Asset n, Crypt (Auth_ShaKey n) (PriKey A)) \<in> s \<longrightarrow>
  m = n"
by (erule rtrancl_induct, simp add: image_def, frule asset_i_used [of _ m A],
 drule asset_i_used [of _ n A], auto simp add: rel_def)

proposition owner_ii_unique [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Owner m, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<longrightarrow>
    (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  m = n"
by (erule rtrancl_induct, simp add: image_def, frule owner_ii_used [of _ m A],
 drule owner_ii_used [of _ n A], auto simp add: rel_def)

proposition asset_ii_unique [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset m, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s \<longrightarrow>
    (Asset n, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  m = n"
by (erule rtrancl_induct, simp add: image_def, frule asset_ii_used [of _ m A],
 drule asset_ii_used [of _ n A], auto simp add: rel_def)

proposition auth_prikey_asset_i [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset m, Crypt (Auth_ShaKey m) (Auth_PriKey n)) \<in> s \<longrightarrow>
  False"
by (erule rtrancl_induct, simp add: image_def, drule auth_prikey_used [of _ n],
 auto simp add: rel_def)

proposition auth_pubkey_owner_ii [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Owner m, \<lbrace>Num 1, Auth_PubKey n\<rbrace>) \<in> s \<longrightarrow>
  False"
by (erule rtrancl_induct, simp add: image_def, drule auth_prikey_used [of _ n],
 auto simp add: rel_def)

proposition auth_pubkey_asset_ii [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset m, \<lbrace>Num 2, Auth_PubKey n\<rbrace>) \<in> s \<longrightarrow>
  False"
by (erule rtrancl_induct, simp add: image_def, drule auth_prikey_used [of _ n],
 auto simp add: rel_def)

proposition asset_i_owner_ii [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset m, Crypt (Auth_ShaKey m) (PriKey A)) \<in> s \<longrightarrow>
    (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  False"
by (erule rtrancl_induct, simp add: image_def, frule asset_i_used [of _ m A],
 drule owner_ii_used [of _ n A], auto simp add: rel_def)

proposition asset_i_asset_ii [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset m, Crypt (Auth_ShaKey m) (PriKey A)) \<in> s \<longrightarrow>
    (Asset n, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  False"
by (erule rtrancl_induct, simp add: image_def, frule asset_i_used [of _ m A],
 drule asset_ii_used [of _ n A], auto simp add: rel_def)

proposition asset_ii_owner_ii [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset m, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s \<longrightarrow>
    (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  False"
by (erule rtrancl_induct, simp add: image_def, frule asset_ii_used [of _ m A],
 drule owner_ii_used [of _ n A], auto simp add: rel_def)

proposition asset_iii_owner_iii [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset m, \<lbrace>Num 4, PubKey A\<rbrace>) \<in> s \<longrightarrow>
    (Owner n, \<lbrace>Num 3, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  False"
by (erule rtrancl_induct, simp add: image_def, frule asset_iii_used [of _ m A],
 drule owner_iii_used [of _ n A], auto simp add: rel_def)

proposition asset_iv_state [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset n, Token n (Auth_PriK n) B C SK) \<in> s \<longrightarrow>
  (\<exists>A D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
    (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s \<and> (Asset n, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> s \<and>
    Crypt (SesK SK) (PubKey D) \<in> used s \<and> (Asset n, PubKey B) \<in> s)"
by (erule rtrancl_induct, auto simp add: rel_def)

proposition owner_v_state [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Owner n, Crypt (SesK SK) (Pwd n)) \<in> s \<longrightarrow>
  (Owner n, SesKey SK) \<in> s \<and>
  (\<exists>A B C. Token n A B C SK \<in> used s \<and> B \<in> fst (snd SK))"
by (erule rtrancl_induct, auto simp add: rel_def, blast)

proposition asset_v_state [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset n, Crypt (SesK SK) (Num 0)) \<in> s \<longrightarrow>
  (Asset n, SesKey SK) \<in> s \<and> Crypt (SesK SK) (Pwd n) \<in> used s"
by (erule rtrancl_induct, simp_all add: rel_def image_def,
 ((erule disjE)?, (erule exE)+, simp add: Range_Un_eq)+)

lemma owner_seskey_nonce_1:
 "\<lbrakk>s \<turnstile> s';
    (Owner n, SesKey SK) \<in> s \<longrightarrow>
      (\<exists>S. fst SK = Some S \<and> Crypt (Auth_ShaKey n) (PriKey S) \<in> used s) \<or>
      fst SK = None;
    (Owner n, SesKey SK) \<in> s'\<rbrakk> \<Longrightarrow>
  (\<exists>S. fst SK = Some S \<and> Crypt (Auth_ShaKey n) (PriKey S) \<in> used s') \<or>
  fst SK = None"
by (simp add: rel_def, (erule disjE, (erule exE)+, simp+)+,
 split if_split_asm, auto)

proposition owner_seskey_nonce [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Owner n, SesKey SK) \<in> s \<longrightarrow>
  (\<exists>S. fst SK = Some S \<and> Crypt (Auth_ShaKey n) (PriKey S) \<in> used s) \<or>
  fst SK = None"
by (erule rtrancl_induct, simp add: image_def, rule impI, rule owner_seskey_nonce_1)

proposition owner_seskey_other [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Owner n, SesKey SK) \<in> s \<longrightarrow>
  (\<exists>A B C D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
    (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<and>
    (Owner n, \<lbrace>Num 3, PubKey C\<rbrace>) \<in> s \<and>
    (Owner n, Crypt (SesK SK) (PubKey D)) \<in> s)"
by (erule rtrancl_induct, auto simp add: rel_def, blast+)

proposition asset_seskey_nonce [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset n, SesKey SK) \<in> s \<longrightarrow>
  (\<exists>S. fst SK = Some S \<and> (Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s)"
by (erule rtrancl_induct, auto simp add: rel_def)

proposition asset_seskey_other [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Asset n, SesKey SK) \<in> s \<longrightarrow>
  (\<exists>A B C D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
    (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s \<and> (Asset n, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> s \<and>
    (Asset n, Token n (Auth_PriK n) B C SK) \<in> s)"
by (erule rtrancl_induct, auto simp add: rel_def, blast)


declare Range_Un_eq [simp]

proposition used_prod [simp]:
 "A \<noteq> {} \<Longrightarrow> used (A \<times> H) = H"
by (simp add: Range_snd)

proposition parts_idem [simp]:
 "parts (parts H) = parts H"
by (rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_mono:
 "H \<subseteq> H' \<Longrightarrow> parts H \<subseteq> parts H'"
by (rule subsetI, erule parts.induct, auto)

proposition parts_msg_mono:
 "X \<in> H \<Longrightarrow> parts_msg X \<subseteq> parts H"
by (subgoal_tac "{X} \<subseteq> H", subst parts_msg_def, erule parts_mono, simp)

lemma parts_union_1:
 "parts (H \<union> H') \<subseteq> parts H \<union> parts H'"
by (rule subsetI, erule parts.induct, auto)

lemma parts_union_2:
 "parts H \<union> parts H' \<subseteq> parts (H \<union> H')"
by (rule subsetI, erule UnE, erule_tac [!] parts.induct, auto)

proposition parts_union [simp]:
 "parts (H \<union> H') = parts H \<union> parts H'"
by (rule equalityI, rule parts_union_1, rule parts_union_2)

proposition parts_insert:
 "parts (insert X H) = parts_msg X \<union> parts H"
by (simp only: insert_def parts_union, subst parts_msg_def, simp)

proposition parts_msg_num [simp]:
 "parts_msg (Num n) = {Num n}"
by (subst parts_msg_def, rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_msg_pwd [simp]:
 "parts_msg (Pwd n) = {Pwd n}"
by (subst parts_msg_def, rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_msg_key [simp]:
 "parts_msg (Key K) = {Key K}"
by (subst parts_msg_def, rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_msg_mult [simp]:
 "parts_msg (A \<otimes> B) = {A \<otimes> B}"
by (subst parts_msg_def, rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_msg_hash [simp]:
 "parts_msg (Hash X) = {Hash X}"
by (subst parts_msg_def, rule equalityI, rule subsetI, erule parts.induct, auto)

lemma parts_crypt_1:
 "parts {Crypt K X} \<subseteq> insert (Crypt K X) (parts {X})"
by (rule subsetI, erule parts.induct, auto)

lemma parts_crypt_2:
 "insert (Crypt K X) (parts {X}) \<subseteq> parts {Crypt K X}"
by (rule subsetI, simp, erule disjE, blast, erule parts.induct, auto)

proposition parts_msg_crypt [simp]:
 "parts_msg (Crypt K X) = insert (Crypt K X) (parts_msg X)"
by (simp add: parts_msg_def, rule equalityI, rule parts_crypt_1, rule parts_crypt_2)

lemma parts_mpair_1:
 "parts {\<lbrace>X, Y\<rbrace>} \<subseteq> insert \<lbrace>X, Y\<rbrace> (parts {X} \<union> parts {Y})"
by (rule subsetI, erule parts.induct, auto)

lemma parts_mpair_2:
 "insert \<lbrace>X, Y\<rbrace> (parts {X} \<union> parts {Y}) \<subseteq> parts {\<lbrace>X, Y\<rbrace>}"
by (rule subsetI, simp, erule disjE, blast, erule disjE, erule_tac [!] parts.induct,
 auto)

proposition parts_msg_mpair [simp]:
 "parts_msg \<lbrace>X, Y\<rbrace> = insert \<lbrace>X, Y\<rbrace> (parts_msg X \<union> parts_msg Y)"
by (simp add: parts_msg_def, rule equalityI, rule parts_mpair_1, rule parts_mpair_2)

proposition parts_msg_idinfo [simp]:
 "parts_msg \<langle>n, X\<rangle> = {\<langle>n, X\<rangle>}"
by (subst parts_msg_def, rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_msg_trace [simp]:
 "parts_msg (Log X) = {Log X}"
by (subst parts_msg_def, rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_idinfo [simp]:
 "parts (IDInfo n ` H) = IDInfo n ` H"
by (rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_trace [simp]:
 "parts (Log ` H) = Log ` H"
by (rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_dec:
 "\<lbrakk>s' = insert (Spy, X) s \<and> (Spy, Crypt K X) \<in> s \<and> (Spy, Key (InvK K)) \<in> s;
    Y \<in> parts_msg X\<rbrakk> \<Longrightarrow>
  Y \<in> parts (used s)"
by (subgoal_tac "X \<in> parts (used s)", drule parts_msg_mono [of X], auto)

proposition parts_enc:
 "\<lbrakk>s' = insert (Spy, Crypt K X) s \<and> (Spy, X) \<in> s \<and> (Spy, Key K) \<in> s;
    Y \<in> parts_msg X\<rbrakk> \<Longrightarrow>
  Y \<in> parts (used s)"
by (subgoal_tac "X \<in> parts (used s)", drule parts_msg_mono [of X], auto)

proposition parts_sep:
 "\<lbrakk>s' = insert (Spy, X) (insert (Spy, Y) s) \<and> (Spy, \<lbrace>X, Y\<rbrace>) \<in> s;
    Z \<in> parts_msg X \<or> Z \<in> parts_msg Y\<rbrakk> \<Longrightarrow>
  Z \<in> parts (used s)"
by (erule disjE, subgoal_tac "X \<in> parts (used s)", drule parts_msg_mono [of X],
 subgoal_tac [3] "Y \<in> parts (used s)", drule_tac [3] parts_msg_mono [of Y], auto)

proposition parts_con:
 "\<lbrakk>s' = insert (Spy, \<lbrace>X, Y\<rbrace>) s \<and> (Spy, X) \<in> s \<and> (Spy, Y) \<in> s;
    Z \<in> parts_msg X \<or> Z \<in> parts_msg Y\<rbrakk> \<Longrightarrow>
  Z \<in> parts (used s)"
by (erule disjE, subgoal_tac "X \<in> parts (used s)", drule parts_msg_mono [of X],
 subgoal_tac [3] "Y \<in> parts (used s)", drule_tac [3] parts_msg_mono [of Y], auto)

lemma parts_init_1:
 "parts (used s\<^sub>0) \<subseteq> used s\<^sub>0 \<union> range (Hash \<circ> Agent) \<union>
    range (Hash \<circ> Auth_PubKey) \<union>
    range (\<lambda>n. \<lbrace>Hash (Agent n), Hash (Auth_PubKey n)\<rbrace>)"
by (rule subsetI, erule parts.induct, (clarify | simp add: Range_iff image_def)+)

lemma parts_init_2:
 "used s\<^sub>0 \<union> range (Hash \<circ> Agent) \<union> range (Hash \<circ> Auth_PubKey) \<union>
    range (\<lambda>n. \<lbrace>Hash (Agent n), Hash (Auth_PubKey n)\<rbrace>) \<subseteq> parts (used s\<^sub>0)"
by (rule subsetI, auto simp add: parts_insert)

proposition parts_init:
 "parts (used s\<^sub>0) = used s\<^sub>0 \<union> range (Hash \<circ> Agent) \<union>
    range (Hash \<circ> Auth_PubKey) \<union>
    range (\<lambda>n. \<lbrace>Hash (Agent n), Hash (Auth_PubKey n)\<rbrace>)"
by (rule equalityI, rule parts_init_1, rule parts_init_2)


proposition parts_crypt_prikey_start:
 "\<lbrakk>s \<turnstile> s'; Crypt K (PriKey A) \<in> parts (used s');
    Crypt K (PriKey A) \<notin> parts (used s)\<rbrakk> \<Longrightarrow>
  (\<exists>n. K = Auth_ShaKey n \<and>
    (Asset n, Crypt (Auth_ShaKey n) (PriKey A)) \<in> s') \<or>
  {PriKey A, Key K} \<subseteq> spied s'"
by (simp add: rel_def, erule disjE, (erule exE)+, simp add: parts_insert, blast,
 (((erule disjE)?, (erule exE)+, simp add: parts_insert image_iff)+,
 ((drule parts_dec | erule disjE, simp, drule parts_enc |
 drule parts_sep | drule parts_con), simp+)?)+)

proposition parts_crypt_prikey:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Crypt K (PriKey A) \<in> parts (used s)\<rbrakk> \<Longrightarrow>
    (\<exists>n. K = Auth_ShaKey n \<and>
      (Asset n, Crypt (Auth_ShaKey n) (PriKey A)) \<in> s) \<or>
    {PriKey A, Key K} \<subseteq> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, frule parts_crypt_prikey_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_crypt_pubkey_start:
 "\<lbrakk>s \<turnstile> s'; Crypt (SesK SK) (PubKey C) \<in> parts (used s');
    Crypt (SesK SK) (PubKey C) \<notin> parts (used s)\<rbrakk> \<Longrightarrow>
  C \<in> snd (snd SK) \<and> ((\<exists>n. (Owner n, SesKey SK) \<in> s') \<or>
    (\<exists>n B. (Asset n, Token n (Auth_PriK n) B C SK) \<in> s')) \<or>
  SesKey SK \<in> spied s'"
by (simp add: rel_def, (erule disjE, (erule exE)+, simp add: parts_insert image_iff)+,
 blast, erule disjE, (erule exE)+, simp add: parts_insert image_iff, blast,
 (((erule disjE)?, ((erule exE)+)?, simp add: parts_insert image_iff)+,
 ((drule parts_dec | drule parts_enc | drule parts_sep | drule parts_con), simp+)?)+)

proposition parts_crypt_pubkey:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Crypt (SesK SK) (PubKey C) \<in> parts (used s)\<rbrakk> \<Longrightarrow>
    C \<in> snd (snd SK) \<and> ((\<exists>n. (Owner n, SesKey SK) \<in> s) \<or>
      (\<exists>n B. (Asset n, Token n (Auth_PriK n) B C SK) \<in> s)) \<or>
    SesKey SK \<in> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, frule parts_crypt_pubkey_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_crypt_key_start:
 "\<lbrakk>s \<turnstile> s'; Crypt K (Key K') \<in> parts (used s');
    Crypt K (Key K') \<notin> parts (used s); K' \<notin> range PriK \<union> range PubK\<rbrakk> \<Longrightarrow>
  {Key K', Key K} \<subseteq> spied s'"
by (simp add: rel_def, (((erule disjE)?, ((erule exE)+)?, simp add: parts_insert
 image_iff)+, ((drule parts_dec | drule parts_enc | drule parts_sep | drule parts_con),
 simp+)?)+)

proposition parts_crypt_key:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Crypt K (Key K') \<in> parts (used s);
    K' \<notin> range PriK \<union> range PubK\<rbrakk> \<Longrightarrow>
  {Key K', Key K} \<subseteq> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, frule parts_crypt_key_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_crypt_sign_start:
 "\<lbrakk>s \<turnstile> s'; Crypt (SesK SK) (Sign n A) \<in> parts (used s');
    Crypt (SesK SK) (Sign n A) \<notin> parts (used s)\<rbrakk> \<Longrightarrow>
  (Asset n, SesKey SK) \<in> s' \<or> SesKey SK \<in> spied s'"
by (simp add: rel_def, (((erule disjE)?, ((erule exE)+)?, simp add: parts_insert
 image_iff)+, ((drule parts_dec | drule parts_enc | drule parts_sep | drule parts_con),
 simp+)?)+)

proposition parts_crypt_sign:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Crypt (SesK SK) (Sign n A) \<in> parts (used s)\<rbrakk> \<Longrightarrow>
    (Asset n, SesKey SK) \<in> s \<or> SesKey SK \<in> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, frule parts_crypt_sign_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_crypt_pwd_start:
 "\<lbrakk>s \<turnstile> s'; Crypt K (Pwd n) \<in> parts (used s');
    Crypt K (Pwd n) \<notin> parts (used s)\<rbrakk> \<Longrightarrow>
  (\<exists>SK. K = SesK SK \<and> (Owner n, Crypt (SesK SK) (Pwd n)) \<in> s') \<or>
  {Pwd n, Key K} \<subseteq> spied s'"
by (simp add: rel_def, (((erule disjE)?, ((erule exE)+)?, simp add: parts_insert
 image_iff)+, ((drule parts_dec | drule parts_enc | drule parts_sep | drule parts_con),
 simp+)?)+)

proposition parts_crypt_pwd:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Crypt K (Pwd n) \<in> parts (used s)\<rbrakk> \<Longrightarrow>
    (\<exists>SK. K = SesK SK \<and> (Owner n, Crypt (SesK SK) (Pwd n)) \<in> s) \<or>
    {Pwd n, Key K} \<subseteq> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, frule parts_crypt_pwd_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_crypt_num_start:
 "\<lbrakk>s \<turnstile> s'; Crypt (SesK SK) (Num 0) \<in> parts (used s');
    Crypt (SesK SK) (Num 0) \<notin> parts (used s)\<rbrakk> \<Longrightarrow>
  (\<exists>n. (Asset n, Crypt (SesK SK) (Num 0)) \<in> s') \<or> SesKey SK \<in> spied s'"
by (simp add: rel_def, (erule disjE, (erule exE)+, simp add: parts_insert image_iff)+,
 blast, (((erule disjE)?, (erule exE)+, simp add: parts_insert image_iff)+,
 ((drule parts_dec | erule disjE, simp, drule parts_enc |
 drule parts_sep | drule parts_con), simp+)?)+)

proposition parts_crypt_num:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Crypt (SesK SK) (Num 0) \<in> parts (used s)\<rbrakk> \<Longrightarrow>
    (\<exists>n. (Asset n, Crypt (SesK SK) (Num 0)) \<in> s) \<or> SesKey SK \<in> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, frule parts_crypt_num_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_crypt_mult_start:
 "\<lbrakk>s \<turnstile> s'; Crypt (SesK SK) (A \<otimes> B) \<in> parts (used s');
    Crypt (SesK SK) (A \<otimes> B) \<notin> parts (used s)\<rbrakk> \<Longrightarrow>
  B \<in> fst (snd SK) \<and> (\<exists>n C. (Asset n, Token n (Auth_PriK n) B C SK) \<in> s') \<or>
  {A \<otimes> B, SesKey SK} \<subseteq> spied s"
by (simp add: rel_def, (erule disjE, (erule exE)+, simp add: parts_insert image_iff)+,
 blast, (((erule disjE)?, (erule exE)+, simp add: parts_insert image_iff)+,
 ((drule parts_dec | erule disjE, simp, drule parts_enc |
 drule parts_sep | drule parts_con), simp+)?)+)

proposition parts_crypt_mult:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Crypt (SesK SK) (A \<otimes> B) \<in> parts (used s)\<rbrakk> \<Longrightarrow>
    B \<in> fst (snd SK) \<and> (\<exists>n C. (Asset n, Token n (Auth_PriK n) B C SK) \<in> s) \<or>
    {A \<otimes> B, SesKey SK} \<subseteq> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, frule parts_crypt_mult_start, assumption+,
 drule converse_rtrancl_into_rtrancl, assumption, drule state_subset [of _ s],
 drule spied_subset [of _ s], blast)


proposition parts_mult_start:
 "\<lbrakk>s \<turnstile> s'; A \<otimes> B \<in> parts (used s'); A \<otimes> B \<notin> parts (used s)\<rbrakk> \<Longrightarrow>
    (\<exists>n SK. A = Auth_PriK n \<and> (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s' \<and>
      Crypt (SesK SK) (A \<otimes> B) \<in> parts (used s')) \<or>
    {PriKey A, PriKey B} \<subseteq> spied s'"
by (simp add: rel_def, (erule disjE, (erule exE)+, simp add: parts_insert image_iff)+,
 blast, (((erule disjE)?, (erule exE)+, simp add: parts_insert image_iff)+,
 ((drule parts_dec | drule parts_enc | drule parts_sep | drule parts_con), simp+)?)+)

proposition parts_mult:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; A \<otimes> B \<in> parts (used s)\<rbrakk> \<Longrightarrow>
    (\<exists>n. A = Auth_PriK n \<and> (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s) \<or>
    {PriKey A, PriKey B} \<subseteq> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, frule parts_mult_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_mpair_key_start:
 "\<lbrakk>s \<turnstile> s'; \<lbrace>X, Y\<rbrace> \<in> parts (used s'); \<lbrace>X, Y\<rbrace> \<notin> parts (used s);
    X = Key K \<or> Y = Key K \<and> K \<notin> range PubK\<rbrakk> \<Longrightarrow>
  {X, Y} \<subseteq> spied s'"
by (erule disjE, simp_all add: rel_def,
 (((erule disjE)?, (erule exE)+, simp add: parts_insert image_iff)+,
 ((drule parts_dec | drule parts_enc |
 drule parts_sep | erule disjE, simp, drule parts_con), simp+)?)+)

proposition parts_mpair_key:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; \<lbrace>X, Y\<rbrace> \<in> parts (used s);
    X = Key K \<or> Y = Key K \<and> K \<notin> range PubK\<rbrakk> \<Longrightarrow>
  {X, Y} \<subseteq> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 blast, (erule exE)+, (erule conjE)+, frule parts_mpair_key_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_mpair_pwd_start:
 "\<lbrakk>s \<turnstile> s'; \<lbrace>X, Y\<rbrace> \<in> parts (used s'); \<lbrace>X, Y\<rbrace> \<notin> parts (used s);
    X = Pwd n \<or> Y = Pwd n\<rbrakk> \<Longrightarrow>
  {X, Y} \<subseteq> spied s'"
by (erule disjE, simp_all add: rel_def,
 (((erule disjE)?, (erule exE)+, simp add: parts_insert image_iff)+,
 ((drule parts_dec | drule parts_enc |
 drule parts_sep | erule disjE, simp, drule parts_con), simp+)?)+)

proposition parts_mpair_pwd:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; \<lbrace>X, Y\<rbrace> \<in> parts (used s); X = Pwd n \<or> Y = Pwd n\<rbrakk> \<Longrightarrow>
    {X, Y} \<subseteq> spied s"
by (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 blast, (erule exE)+, (erule conjE)+, frule parts_mpair_pwd_start, assumption+,
 (drule state_subset)+, blast)


proposition parts_pubkey_false_start:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "Crypt (SesK SK) (PubKey C) \<in> parts (used s')" and
    D: "Crypt (SesK SK) (PubKey C) \<notin> parts (used s)" and
    E: "\<forall>n. (Owner n, SesKey SK) \<notin> s'" and
    F: "SesKey SK \<notin> spied s'"
  shows False
proof -
  have "C \<in> snd (snd SK) \<and> ((\<exists>n. (Owner n, SesKey SK) \<in> s') \<or>
    (\<exists>n B. (Asset n, Token n (Auth_PriK n) B C SK) \<in> s')) \<or>
    SesKey SK \<in> spied s'"
    (is "?P C \<and> ((\<exists>n. ?Q n s') \<or> (\<exists>n B. ?R n B C s')) \<or> ?S s'")
    by (rule parts_crypt_pubkey_start [OF B C D])
  then obtain n B where "?P C" and "?R n B C s'"
    using E and F by blast
  moreover have "\<not> ?R n B C s"
    using D by blast
  ultimately have "\<exists>D. Crypt (SesK SK) (PubKey D) \<in> used s"
    (is "\<exists>D. ?U D")
    using B by (auto simp add: rel_def)
  then obtain D where "?U D" ..
  hence "?P D \<and> ((\<exists>n. ?Q n s) \<or> (\<exists>n B. ?R n B D s)) \<or> ?S s"
    by (rule_tac parts_crypt_pubkey [OF A], blast)
  moreover have G: "s \<subseteq> s'"
    by (rule state_subset, insert B, simp)
  have "\<forall>n. (Owner n, SesKey SK) \<notin> s"
    by (rule allI, rule notI, drule subsetD [OF G], insert E, simp)
  moreover have H: "spied s \<subseteq> spied s'"
    by (rule Image_mono [OF G], simp)
  have "SesKey SK \<notin> spied s"
    by (rule notI, drule subsetD [OF H], insert F, contradiction)
  ultimately obtain n' B' where "?R n' B' D s" by blast
  have "\<exists>A' D'. fst (snd SK) = {A', B'} \<and> snd (snd SK) = {D, D'} \<and>
    (Asset n', \<lbrace>Num 2, PubKey B'\<rbrace>) \<in> s \<and>
    (Asset n', \<lbrace>Num 4, PubKey D'\<rbrace>) \<in> s \<and>
    ?U D' \<and> (Asset n', PubKey B') \<in> s"
    by (rule asset_iv_state [OF A \<open>?R n' B' D s\<close>])
  then obtain D' where "snd (snd SK) = {D, D'}" and "?U D'" by blast
  hence "Crypt (SesK SK) (PubKey C) \<in> parts (used s)"
    using \<open>?P C\<close> and \<open>?U D\<close> by auto
  thus False
    using D by contradiction
qed

proposition parts_pubkey_false:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Crypt (SesK SK) (PubKey C) \<in> parts (used s);
    \<forall>n. (Owner n, SesKey SK) \<notin> s; SesKey SK \<notin> spied s\<rbrakk> \<Longrightarrow>
  False"
proof (drule rtrancl_start, assumption, subst parts_init, simp add: Range_iff image_def,
 (erule exE)+, (erule conjE)+, erule parts_pubkey_false_start, assumption+,
 rule allI, rule_tac [!] notI)
  fix v n
  assume "(Owner n, SesKey SK) \<in> v" and "v \<Turnstile> s"
  hence "(Owner n, SesKey SK) \<in> s"
    by (erule_tac rev_subsetD, rule_tac state_subset)
  moreover assume "\<forall>n. (Owner n, SesKey SK) \<notin> s"
  ultimately show False by simp
next
  fix v
  assume "SesKey SK \<in> spied v" and "v \<Turnstile> s"
  hence "SesKey SK \<in> spied s"
    by (erule_tac rev_subsetD, rule_tac spied_subset)
  moreover assume "SesKey SK \<notin> spied s"
  ultimately show False by contradiction
qed


proposition asset_ii_spied_start:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "PriKey B \<in> spied s'" and
    D: "PriKey B \<notin> spied s" and
    E: "(Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s"
  shows "Auth_PriKey n \<in> spied s \<and>
    (\<exists>C SK. (Asset n, Token n (Auth_PriK n) B C SK) \<in> s)"
    (is "_ \<and> (\<exists>C SK. ?P n C SK s)")
proof -
  have "\<exists>A. (A \<otimes> B \<in> spied s \<or> B \<otimes> A \<in> spied s) \<and> PriKey A \<in> spied s"
  proof (insert B C D, auto simp add: rel_def, rule_tac [!] FalseE)
    assume "Key (PriK B) \<notin> used s"
    moreover have "PriKey B \<in> used s"
      by (rule asset_ii_used [OF A, THEN mp, OF E])
    ultimately show False by simp
  next
    fix K
    assume "(Spy, Crypt K (Key (PriK B))) \<in> s"
    hence "Crypt K (PriKey B) \<in> parts (used s)" by auto
    hence "(\<exists>m. K = Auth_ShaKey m \<and>
      (Asset m, Crypt (Auth_ShaKey m) (PriKey B)) \<in> s) \<or>
      {PriKey B, Key K} \<subseteq> spied s"
      (is "(\<exists>m. _ \<and> ?P m) \<or> _")
      by (rule parts_crypt_prikey [OF A])
    then obtain m where "?P m"
      using D by blast
    thus False
      by (rule asset_i_asset_ii [OF A _ E])
  next
    fix Y
    assume "(Spy, \<lbrace>Key (PriK B), Y\<rbrace>) \<in> s"
    hence "\<lbrace>PriKey B, Y\<rbrace> \<in> parts (used s)" by auto
    hence "{PriKey B, Y} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "PriK B"], simp)
    thus False
      using D by simp
  next
    fix X
    assume "(Spy, \<lbrace>X, Key (PriK B)\<rbrace>) \<in> s"
    hence "\<lbrace>X, PriKey B\<rbrace> \<in> parts (used s)" by auto
    hence "{X, PriKey B} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "PriK B"], simp add: image_def)
    thus False
      using D by simp
  qed
  then obtain A where F: "PriKey A \<in> spied s" and
    "A \<otimes> B \<in> spied s \<or> B \<otimes> A \<in> spied s"
    by blast
  hence "A \<otimes> B \<in> parts (used s) \<or> B \<otimes> A \<in> parts (used s)" by blast
  moreover have "B \<otimes> A \<notin> parts (used s)"
  proof
    assume "B \<otimes> A \<in> parts (used s)"
    hence "(\<exists>m. B = Auth_PriK m \<and> (Asset m, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s) \<or>
      {PriKey B, PriKey A} \<subseteq> spied s"
      by (rule parts_mult [OF A])
    then obtain m where "B = Auth_PriK m"
      using D by blast
    hence "(Asset n, \<lbrace>Num 2, Auth_PubKey m\<rbrace>) \<in> s"
      using E by simp
    thus False
      by (rule auth_pubkey_asset_ii [OF A])
  qed
  ultimately have "A \<otimes> B \<in> parts (used s)" by simp
  with A have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> s \<and>
    A \<otimes> B \<notin> parts (used u) \<and> A \<otimes> B \<in> parts (used v)"
    by (rule rtrancl_start, subst parts_init, simp add: Range_iff image_def)
  then obtain u v where G: "u \<turnstile> v" and H: "v \<Turnstile> s" and
    I: "A \<otimes> B \<notin> parts (used u)" and "A \<otimes> B \<in> parts (used v)"
    by blast
  hence "(\<exists>m SK. A = Auth_PriK m \<and> (Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> v \<and>
    Crypt (SesK SK) (A \<otimes> B) \<in> parts (used v)) \<or>
    {PriKey A, PriKey B} \<subseteq> spied v"
    by (rule_tac parts_mult_start, simp_all)
  moreover have "PriKey B \<notin> spied v"
  proof
    assume "PriKey B \<in> spied v"
    hence "PriKey B \<in> spied s"
      by (rule rev_subsetD, rule_tac spied_subset [OF H])
    thus False
      using D by contradiction
  qed
  ultimately obtain m SK where
    J: "Crypt (SesK SK) (A \<otimes> B) \<in> parts (used v)" and
    "A = Auth_PriK m" and "(Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> v"
    by blast
  moreover from this have "(Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s"
    by (erule_tac rev_subsetD, rule_tac state_subset [OF H])
  hence "m = n"
    by (rule asset_ii_unique [OF A _ E])
  ultimately have K: "Auth_PriKey n \<in> spied s"
    using F by simp
  have "Crypt (SesK SK) (A \<otimes> B) \<notin> parts (used u)"
    using I by blast
  hence "B \<in> fst (snd SK) \<and> (\<exists>m C. ?P m C SK v) \<or>
    {A \<otimes> B, SesKey SK} \<subseteq> spied u"
    by (rule parts_crypt_mult_start [OF G J])
  moreover have "A \<otimes> B \<notin> spied u"
    using I by blast
  ultimately obtain m' C where "?P m' C SK v" by blast
  hence "?P m' C SK s"
    by (rule rev_subsetD, rule_tac state_subset [OF H])
  moreover from this have "\<exists>A' D. fst (snd SK) = {A', B} \<and>
    snd (snd SK) = {C, D} \<and> (Asset m', \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s \<and>
    (Asset m', \<lbrace>Num 4, PubKey D\<rbrace>) \<in> s \<and>
    Crypt (SesK SK) (PubKey D) \<in> used s \<and> (Asset m', PubKey B) \<in> s"
    by (rule asset_iv_state [OF A])
  hence "(Asset m', \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s" by blast
  hence "m' = n"
    by (rule asset_ii_unique [OF A _ E])
  ultimately show ?thesis
    using K by blast
qed

proposition asset_ii_spied:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "PriKey B \<in> spied s" and
    C: "(Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s"
  shows "Auth_PriKey n \<in> spied s \<and>
    (\<exists>C SK. (Asset n, Token n (Auth_PriK n) B C SK) \<in> s)"
    (is "?P s")
proof -
  have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> s \<and>
    (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<notin> u \<and> (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> v"
    using A and C by (rule rtrancl_start, auto)
  then obtain u v where "v \<Turnstile> s" and "(Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<notin> u" and
    D: "s\<^sub>0 \<Turnstile> u" and E: "u \<turnstile> v" and F: "(Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> v"
    by blast
  moreover from this have "PriKey B \<notin> spied v"
    by (auto simp add: rel_def)
  ultimately have "\<exists>w x. v \<Turnstile> w \<and> w \<turnstile> x \<and> x \<Turnstile> s \<and>
    PriKey B \<notin> spied w \<and> PriKey B \<in> spied x"
    using B by (rule_tac rtrancl_start, simp_all)
  then obtain w x where "PriKey B \<notin> spied w" and "PriKey B \<in> spied x" and
    G: "v \<Turnstile> w" and H: "w \<turnstile> x" and I: "x \<Turnstile> s"
    by blast
  moreover from this have "s\<^sub>0 \<Turnstile> w"
    using D and E by simp
  moreover have "(Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> w"
    by (rule rev_subsetD [OF F], rule state_subset [OF G])
  ultimately have "?P w"
    by (rule_tac asset_ii_spied_start, simp_all)
  moreover have "w \<subseteq> s"
    using H and I by (rule_tac state_subset, simp)
  ultimately show ?thesis by blast
qed


proposition asset_iv_unique:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "(Asset m, Token m (Auth_PriK m) B C' SK') \<in> s" and
    C: "(Asset n, Token n (Auth_PriK n) B C SK) \<in> s"
      (is "?P n C SK s")
  shows "m = n \<and> C' = C \<and> SK' = SK"
proof (subst (2) cases_simp [of "m = n", symmetric], simp, rule conjI, rule impI,
 rule ccontr)
  assume D: "\<not> (C' = C \<and> SK' = SK)" and "m = n"
  moreover have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> s \<and>
    \<not> (?P m C' SK' u \<and> ?P n C SK u) \<and> ?P m C' SK' v \<and> ?P n C SK v"
    using B and C by (rule_tac rtrancl_start [OF A], auto)
  ultimately obtain u v where E: "s\<^sub>0 \<Turnstile> u" and F: "u \<turnstile> v" and
    G: "?P n C' SK' v" and H: "?P n C SK v" and
    "\<not> ?P n C' SK' u \<or> \<not> ?P n C SK u"
    by blast
  moreover {
    assume I: "\<not> ?P n C' SK' u"
    hence "?P n C SK u"
      by (insert D F G H, auto simp add: rel_def)
    hence "\<exists>A D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
      (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> u \<and> (Asset n, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> u \<and>
      Crypt (SesK SK) (PubKey D) \<in> used u \<and> (Asset n, PubKey B) \<in> u"
      by (rule asset_iv_state [OF E])
    moreover have "(Asset n, PubKey B) \<notin> u"
      by (insert F G I, auto simp add: rel_def)
    ultimately have False by simp
  }
  moreover {
    assume I: "\<not> ?P n C SK u"
    hence "?P n C' SK' u"
      by (insert D F G H, auto simp add: rel_def)
    hence "\<exists>A D. fst (snd SK') = {A, B} \<and> snd (snd SK') = {C', D} \<and>
      (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> u \<and> (Asset n, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> u \<and>
      Crypt (SesK SK') (PubKey D) \<in> used u \<and> (Asset n, PubKey B) \<in> u"
      by (rule asset_iv_state [OF E])
    moreover have "(Asset n, PubKey B) \<notin> u"
      by (insert F H I, auto simp add: rel_def)
    ultimately have False by simp
  }
  ultimately show False by blast
next
  have "\<exists>A D. fst (snd SK') = {A, B} \<and> snd (snd SK') = {C', D} \<and>
    (Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s \<and> (Asset m, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> s \<and>
    Crypt (SesK SK') (PubKey D) \<in> used s \<and> (Asset m, PubKey B) \<in> s"
    (is "?Q m C' SK'")
    by (rule asset_iv_state [OF A B])
  hence "(Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s" by blast
  moreover have "?Q n C SK"
    by (rule asset_iv_state [OF A C])
  hence "(Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s" by blast
  ultimately show "m = n"
    by (rule asset_ii_unique [OF A])
qed


theorem sigkey_secret:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> SigKey \<notin> spied s"
proof (erule rtrancl_induct, simp add: image_def)
  fix s s'
  assume
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "SigKey \<notin> spied s"
  show "SigKey \<notin> spied s'"
  proof (insert B C, auto simp add: rel_def)
    fix K
    assume "(Spy, Crypt K SigKey) \<in> s"
    hence "Crypt K SigKey \<in> parts (used s)" by blast
    hence "{SigKey, Key K} \<subseteq> spied s"
      by (rule parts_crypt_key [OF A], simp add: image_def)
    with C show False by simp
  next
    fix Y
    assume "(Spy, \<lbrace>SigKey, Y\<rbrace>) \<in> s"
    hence "\<lbrace>SigKey, Y\<rbrace> \<in> parts (used s)" by blast
    hence "{SigKey, Y} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "SigK"], simp)
    with C show False by simp
  next
    fix X
    assume "(Spy, \<lbrace>X, SigKey\<rbrace>) \<in> s"
    hence "\<lbrace>X, SigKey\<rbrace> \<in> parts (used s)" by blast
    hence "{X, SigKey} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "SigK"], simp add: image_def)
    with C show False by simp
  qed
qed

proposition parts_sign_start:
  assumes A: "s\<^sub>0 \<Turnstile> s"
  shows "\<lbrakk>s \<turnstile> s'; Sign n A \<in> parts (used s'); Sign n A \<notin> parts (used s)\<rbrakk> \<Longrightarrow>
    A = Auth_PriK n"
by (simp add: rel_def, (((erule disjE)?, (erule exE)+, simp add: parts_insert image_iff)+,
 ((drule parts_dec | erule disjE, insert sigkey_secret [OF A], simp, drule parts_enc |
 drule parts_sep | drule parts_con), simp+)?)+)

proposition parts_sign:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; Sign n A \<in> parts (used s)\<rbrakk> \<Longrightarrow>
    A = Auth_PriK n"
by (rule classical, drule rtrancl_start, assumption, subst parts_init, simp add:
 Range_iff image_def, (erule exE)+, (erule conjE)+, drule parts_sign_start)


theorem auth_shakey_secret:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; n \<notin> bad_shakey\<rbrakk> \<Longrightarrow>
    Key (Auth_ShaKey n) \<notin> spied s"
proof (erule rtrancl_induct, simp add: image_def)
  fix s s'
  assume
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "Key (Auth_ShaKey n) \<notin> spied s"
  show "Key (Auth_ShaKey n) \<notin> spied s'"
  proof (insert B C, auto simp add: rel_def)
    fix K
    assume "(Spy, Crypt K (Key (ShaK (Auth_ShaK n)))) \<in> s"
    hence "Crypt K (Key (Auth_ShaKey n)) \<in> parts (used s)" by auto
    hence "{Key (Auth_ShaKey n), Key K} \<subseteq> spied s"
      by (rule parts_crypt_key [OF A], simp add: image_def)
    with C show False by simp
  next
    fix Y
    assume "(Spy, \<lbrace>Key (ShaK (Auth_ShaK n)), Y\<rbrace>) \<in> s"
    hence "\<lbrace>Key (Auth_ShaKey n), Y\<rbrace> \<in> parts (used s)" by auto
    hence "{Key (Auth_ShaKey n), Y} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "Auth_ShaKey n"], simp)
    with C show False by simp
  next
    fix X
    assume "(Spy, \<lbrace>X, Key (ShaK (Auth_ShaK n))\<rbrace>) \<in> s"
    hence "\<lbrace>X, Key (Auth_ShaKey n)\<rbrace> \<in> parts (used s)" by auto
    hence "{X, Key (Auth_ShaKey n)} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "Auth_ShaKey n"],
       simp add: image_def)
    with C show False by simp
  qed
qed


theorem auth_prikey_secret:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_prikey"
  shows "Auth_PriKey n \<notin> spied s"
proof
  assume "Auth_PriKey n \<in> spied s"
  moreover have "Auth_PriKey n \<notin> spied s\<^sub>0"
    using B by auto
  ultimately have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> s \<and>
    Auth_PriKey n \<notin> spied u \<and> Auth_PriKey n \<in> spied v"
    by (rule rtrancl_start [OF A])
  then obtain u v where C: "s\<^sub>0 \<Turnstile> u" and D: "u \<turnstile> v" and
    E: "Auth_PriKey n \<notin> spied u" and F: "Auth_PriKey n \<in> spied v"
    by blast
  have "\<exists>B. (Auth_PriK n \<otimes> B \<in> spied u \<or> B \<otimes> Auth_PriK n \<in> spied u) \<and>
    PriKey B \<in> spied u"
  proof (insert D E F, auto simp add: rel_def, rule_tac [!] FalseE)
    assume "Key (PriK (Auth_PriK n)) \<notin> used u"
    moreover have "Auth_PriKey n \<in> used u"
      by (rule auth_prikey_used [OF C])
    ultimately show False by simp
  next
    fix K
    assume "(Spy, Crypt K (Key (PriK (Auth_PriK n)))) \<in> u"
    hence "Crypt K (PriKey (Auth_PriK n)) \<in> parts (used u)" by auto
    hence "(\<exists>m. K = Auth_ShaKey m \<and>
      (Asset m, Crypt (Auth_ShaKey m) (PriKey (Auth_PriK n))) \<in> u) \<or>
      {PriKey (Auth_PriK n), Key K} \<subseteq> spied u"
      by (rule parts_crypt_prikey [OF C])
    then obtain m where
      "(Asset m, Crypt (Auth_ShaKey m) (Auth_PriKey n)) \<in> u"
      using E by auto
    thus False
      by (rule auth_prikey_asset_i [OF C])
  next
    fix Y
    assume "(Spy, \<lbrace>Key (PriK (Auth_PriK n)), Y\<rbrace>) \<in> u"
    hence "\<lbrace>Auth_PriKey n, Y\<rbrace> \<in> parts (used u)" by auto
    hence "{Auth_PriKey n, Y} \<subseteq> spied u"
      by (rule parts_mpair_key [OF C, where K = "PriK (Auth_PriK n)"], simp)
    thus False
      using E by simp
  next
    fix X
    assume "(Spy, \<lbrace>X, Key (PriK (Auth_PriK n))\<rbrace>) \<in> u"
    hence "\<lbrace>X, Auth_PriKey n\<rbrace> \<in> parts (used u)" by auto
    hence "{X, Auth_PriKey n} \<subseteq> spied u"
      by (rule parts_mpair_key [OF C, where K = "PriK (Auth_PriK n)"], simp
       add: image_def)
    thus False
      using E by simp
  qed
  then obtain B where G: "PriKey B \<in> spied u" and
    "Auth_PriK n \<otimes> B \<in> spied u \<or> B \<otimes> Auth_PriK n \<in> spied u"
    by blast
  hence "Auth_PriK n \<otimes> B \<in> parts (used u) \<or> B \<otimes> Auth_PriK n \<in> parts (used u)"
    by blast
  moreover have "B \<otimes> Auth_PriK n \<notin> parts (used u)"
  proof
    assume "B \<otimes> Auth_PriK n \<in> parts (used u)"
    hence "(\<exists>m. B = Auth_PriK m \<and>
      (Asset m, \<lbrace>Num 2, PubKey (Auth_PriK n)\<rbrace>) \<in> u) \<or>
      {PriKey B, PriKey (Auth_PriK n)} \<subseteq> spied u"
      by (rule parts_mult [OF C])
    then obtain m where "(Asset m, \<lbrace>Num 2, Auth_PubKey n\<rbrace>) \<in> u"
      using E by auto
    thus False
      by (rule auth_pubkey_asset_ii [OF C])
  qed
  ultimately have "Auth_PriK n \<otimes> B \<in> parts (used u)" by simp
  hence "(\<exists>m. Auth_PriK n = Auth_PriK m \<and>
    (Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> u) \<or>
    {PriKey (Auth_PriK n), PriKey B} \<subseteq> spied u"
    by (rule parts_mult [OF C])
  then obtain m where "Auth_PriK n = Auth_PriK m" and
    "(Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> u"
    using E by auto
  moreover from this have "Auth_PriKey m \<in> spied u \<and>
    (\<exists>C SK. (Asset m, Token m (Auth_PriK m) B C SK) \<in> u)"
    by (rule_tac asset_ii_spied [OF C G])
  ultimately show False
    using E by simp
qed

proposition asset_ii_secret:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; n \<notin> bad_prikey; (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s\<rbrakk> \<Longrightarrow>
    PriKey B \<notin> spied s"
by (rule notI, frule asset_ii_spied, assumption+, drule auth_prikey_secret, simp+)


proposition asset_i_secret [rule_format]:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey"
  shows "(Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s \<longrightarrow>
    PriKey S \<notin> spied s"
proof (rule rtrancl_induct [OF A], simp add: image_def, rule impI)
  fix s s'
  assume
    C: "s\<^sub>0 \<Turnstile> s" and
    D: "s \<turnstile> s'" and
    E: "(Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s \<longrightarrow>
      PriKey S \<notin> spied s" and
    F: "(Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s'"
  show "PriKey S \<notin> spied s'"
  proof (insert D E F, auto simp add: rel_def)
    assume "(Asset n, Crypt (ShaK (Auth_ShaK n)) (Key (PriK S))) \<in> s"
    hence "(Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s" by simp
    hence "PriKey S \<in> used s"
      by (rule asset_i_used [OF C, THEN mp])
    moreover assume "Key (PriK S) \<notin> used s"
    ultimately show False by simp
  next
    fix K
    assume "(Spy, Crypt K (Key (PriK S))) \<in> s"
    hence "Crypt K (PriKey S) \<in> parts (used s)" by auto
    hence "(\<exists>m. K = Auth_ShaKey m \<and>
      (Asset m, Crypt (Auth_ShaKey m) (PriKey S)) \<in> s) \<or>
      {PriKey S, Key K} \<subseteq> spied s"
      (is "(\<exists>m. ?P m \<and> ?Q m) \<or> _")
      by (rule parts_crypt_prikey [OF C])
    moreover assume "(Spy, Key (PriK S)) \<notin> s"
    ultimately obtain m where G: "?P m \<and> ?Q m" by auto
    hence "?Q m" ..
    moreover assume
      "(Asset n, Crypt (ShaK (Auth_ShaK n)) (Key (PriK S))) \<in> s"
    hence "(Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s" by simp
    ultimately have "m = n"
      by (rule asset_i_unique [OF C])
    moreover assume "(Spy, Key (InvK K)) \<in> s"
    ultimately have "Key (Auth_ShaKey n) \<in> spied s"
      using G by simp
    moreover have "Key (Auth_ShaKey n) \<notin> spied s"
      by (rule auth_shakey_secret [OF C B])
    ultimately show False by contradiction
  next
    fix B
    assume "(Spy, S \<otimes> B) \<in> s"
    hence "S \<otimes> B \<in> parts (used s)" by blast
    hence "(\<exists>m. S = Auth_PriK m \<and> (Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s) \<or>
      {PriKey S, PriKey B} \<subseteq> spied s"
      (is "(\<exists>m. ?P m \<and> _) \<or> _")
      by (rule parts_mult [OF C])
    moreover assume "(Spy, Key (PriK S)) \<notin> s"
    ultimately obtain m where "?P m" by auto
    moreover assume
      "(Asset n, Crypt (ShaK (Auth_ShaK n)) (Key (PriK S))) \<in> s"
    ultimately have "(Asset n, Crypt (Auth_ShaKey n) (Auth_PriKey m)) \<in> s"
      by simp
    thus False
      by (rule auth_prikey_asset_i [OF C])
  next
    fix A
    assume "(Spy, A \<otimes> S) \<in> s"
    hence "A \<otimes> S \<in> parts (used s)" by blast
    hence "(\<exists>m. A = Auth_PriK m \<and> (Asset m, \<lbrace>Num 2, PubKey S\<rbrace>) \<in> s) \<or>
      {PriKey A, PriKey S} \<subseteq> spied s"
      (is "(\<exists>m. _ \<and> ?P m) \<or> _")
      by (rule parts_mult [OF C])
    moreover assume "(Spy, Key (PriK S)) \<notin> s"
    ultimately obtain m where "?P m" by auto
    assume "(Asset n, Crypt (ShaK (Auth_ShaK n)) (Key (PriK S))) \<in> s"
    hence "(Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s" by simp
    thus False
      by (rule asset_i_asset_ii [OF C _ \<open>?P m\<close>])
  next
    fix Y
    assume "(Spy, \<lbrace>Key (PriK S), Y\<rbrace>) \<in> s"
    hence "\<lbrace>PriKey S, Y\<rbrace> \<in> parts (used s)" by auto
    hence "{PriKey S, Y} \<subseteq> spied s"
      by (rule parts_mpair_key [OF C, where K = "PriK S"], simp)
    moreover assume "(Spy, Key (PriK S)) \<notin> s"
    ultimately show False by simp
  next
    fix X
    assume "(Spy, \<lbrace>X, Key (PriK S)\<rbrace>) \<in> s"
    hence "\<lbrace>X, PriKey S\<rbrace> \<in> parts (used s)" by auto
    hence "{X, PriKey S} \<subseteq> spied s"
      by (rule parts_mpair_key [OF C, where K = "PriK S"], simp add: image_def)
    moreover assume "(Spy, Key (PriK S)) \<notin> s"
    ultimately show False by simp
  qed
qed

proposition owner_ii_secret [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<longrightarrow>
  PriKey A \<notin> spied s"
proof (erule rtrancl_induct, simp add: image_def, rule impI)
  fix s s'
  assume
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "(Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<longrightarrow> PriKey A \<notin> spied s" and
    D: "(Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s'"
  show "PriKey A \<notin> spied s'"
  proof (insert B C D, auto simp add: rel_def)
    assume "(Owner n, \<lbrace>Num (Suc 0), Key (PubK A)\<rbrace>) \<in> s"
    hence "(Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s" by simp
    hence "PriKey A \<in> used s"
      by (rule owner_ii_used [OF A, THEN mp])
    moreover assume "Key (PriK A) \<notin> used s"
    ultimately show False by simp
  next
    fix K
    assume "(Spy, Crypt K (Key (PriK A))) \<in> s"
    hence "Crypt K (PriKey A) \<in> parts (used s)" by auto
    hence "(\<exists>m. K = Auth_ShaKey m \<and>
      (Asset m, Crypt (Auth_ShaKey m) (PriKey A)) \<in> s) \<or>
      {PriKey A, Key K} \<subseteq> spied s"
      (is "(\<exists>m. _ \<and> ?P m) \<or> _")
      by (rule parts_crypt_prikey [OF A])
    moreover assume "(Spy, Key (PriK A)) \<notin> s"
    ultimately obtain m where "?P m" by auto
    moreover assume "(Owner n, \<lbrace>Num (Suc 0), Key (PubK A)\<rbrace>) \<in> s"
    hence "(Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s" by simp
    ultimately show False
      by (rule asset_i_owner_ii [OF A])
  next
    fix B
    assume "(Spy, A \<otimes> B) \<in> s"
    hence "A \<otimes> B \<in> parts (used s)" by blast
    hence "(\<exists>m. A = Auth_PriK m \<and> (Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s) \<or>
      {PriKey A, PriKey B} \<subseteq> spied s"
      (is "(\<exists>m. ?P m \<and> _) \<or> _")
      by (rule parts_mult [OF A])
    moreover assume "(Spy, Key (PriK A)) \<notin> s"
    ultimately obtain m where "?P m" by auto
    moreover assume "(Owner n, \<lbrace>Num (Suc 0), Key (PubK A)\<rbrace>) \<in> s"
    ultimately have "(Owner n, \<lbrace>Num 1, Auth_PubKey m\<rbrace>) \<in> s" by simp
    thus False
      by (rule auth_pubkey_owner_ii [OF A])
  next
    fix B
    assume "(Spy, B \<otimes> A) \<in> s"
    hence "B \<otimes> A \<in> parts (used s)" by blast
    hence "(\<exists>m. B = Auth_PriK m \<and> (Asset m, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s) \<or>
      {PriKey B, PriKey A} \<subseteq> spied s"
      (is "(\<exists>m. _ \<and> ?P m) \<or> _")
      by (rule parts_mult [OF A])
    moreover assume "(Spy, Key (PriK A)) \<notin> s"
    ultimately obtain m where "?P m" by auto
    moreover assume "(Owner n, \<lbrace>Num (Suc 0), Key (PubK A)\<rbrace>) \<in> s"
    hence "(Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s" by simp
    ultimately show False
      by (rule asset_ii_owner_ii [OF A])
  next
    fix Y
    assume "(Spy, \<lbrace>Key (PriK A), Y\<rbrace>) \<in> s"
    hence "\<lbrace>PriKey A, Y\<rbrace> \<in> parts (used s)" by auto
    hence "{PriKey A, Y} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "PriK A"], simp)
    moreover assume "(Spy, Key (PriK A)) \<notin> s"
    ultimately show False by simp
  next
    fix X
    assume "(Spy, \<lbrace>X, Key (PriK A)\<rbrace>) \<in> s"
    hence "\<lbrace>X, PriKey A\<rbrace> \<in> parts (used s)" by auto
    hence "{X, PriKey A} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "PriK A"], simp add: image_def)
    moreover assume "(Spy, Key (PriK A)) \<notin> s"
    ultimately show False by simp
  qed
qed

proposition seskey_spied [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    SesKey SK \<in> spied s \<longrightarrow>
  (\<exists>S A C. fst SK = Some S \<and> A \<in> fst (snd SK) \<and> C \<in> snd (snd SK) \<and>
    {PriKey S, PriKey A, PriKey C} \<subseteq> spied s)"
  (is "_ \<Longrightarrow> _ \<longrightarrow> (\<exists>S A C. ?P S A C s)")
proof (erule rtrancl_induct, simp add: image_def, rule impI)
  fix s s'
  assume
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "SesKey SK \<in> spied s \<longrightarrow> (\<exists>S A C. ?P S A C s)" and
    D: "SesKey SK \<in> spied s'"
  show "\<exists>S A C. ?P S A C s'"
  proof (insert B C D, auto simp add: rel_def, blast, rule_tac [!] FalseE)
    fix K
    assume "(Spy, Crypt K (Key (SesK SK))) \<in> s"
    hence "Crypt K (Key (SesK SK)) \<in> parts (used s)" by blast
    hence "{Key (SesK SK), Key K} \<subseteq> spied s"
      by (rule parts_crypt_key [OF A], simp add: image_def)
    moreover assume "(Spy, Key (SesK SK)) \<notin> s"
    ultimately show False by simp
  next
    fix Y
    assume "(Spy, \<lbrace>Key (SesK SK), Y\<rbrace>) \<in> s"
    hence "\<lbrace>SesKey SK, Y\<rbrace> \<in> parts (used s)" by auto
    hence "{SesKey SK, Y} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "SesK SK"], simp)
    moreover assume "(Spy, Key (SesK SK)) \<notin> s"
    ultimately show False by simp
  next
    fix X
    assume "(Spy, \<lbrace>X, Key (SesK SK)\<rbrace>) \<in> s"
    hence "\<lbrace>X, SesKey SK\<rbrace> \<in> parts (used s)" by auto
    hence "{X, SesKey SK} \<subseteq> spied s"
      by (rule parts_mpair_key [OF A, where K = "SesK SK"], simp add: image_def)
    moreover assume "(Spy, Key (SesK SK)) \<notin> s"
    ultimately show False by simp
  qed
qed

proposition owner_seskey_shakey:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey" and
    C: "(Owner n, SesKey SK) \<in> s"
  shows "SesKey SK \<notin> spied s"
proof
  have "(\<exists>S. fst SK = Some S \<and> Crypt (Auth_ShaKey n) (PriKey S) \<in> used s) \<or>
    fst SK = None"
    (is "(\<exists>S. ?P S) \<or> _")
    by (rule owner_seskey_nonce [OF A C])
  moreover assume "SesKey SK \<in> spied s"
  hence D: "\<exists>S A C. fst SK = Some S \<and> A \<in> fst (snd SK) \<and>
    C \<in> snd (snd SK) \<and> {PriKey S, PriKey A, PriKey C} \<subseteq> spied s"
    by (rule seskey_spied [OF A])
  ultimately obtain S where "?P S" by auto
  hence "Crypt (Auth_ShaKey n) (PriKey S) \<in> parts (used s)" by blast
  hence "(\<exists>m. Auth_ShaKey n = Auth_ShaKey m \<and>
    (Asset m, Crypt (Auth_ShaKey m) (PriKey S)) \<in> s) \<or>
    {PriKey S, Key (Auth_ShaKey n)} \<subseteq> spied s"
    (is "(\<exists>m. ?Q m \<and> ?R m) \<or> _")
    by (rule parts_crypt_prikey [OF A])
  moreover have "Key (Auth_ShaKey n) \<notin> spied s"
    by (rule auth_shakey_secret [OF A B])
  ultimately obtain m where "?Q m" and "?R m" by blast
  hence "m \<notin> bad_shakey"
    using B by simp
  hence "PriKey S \<notin> spied s"
    by (rule asset_i_secret [OF A _ \<open>?R m\<close>])
  moreover have "PriKey S \<in> spied s"
    using D and \<open>?P S\<close> by auto
  ultimately show False by contradiction
qed

proposition owner_seskey_prikey:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_prikey" and
    C: "(Owner m, SesKey SK) \<in> s" and
    D: "(Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s" and
    E: "B \<in> fst (snd SK)"
  shows "SesKey SK \<notin> spied s"
proof
  have "\<exists>A B C D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
    (Owner m, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<and>
    (Owner m, \<lbrace>Num 3, PubKey C\<rbrace>) \<in> s \<and>
    (Owner m, Crypt (SesK SK) (PubKey D)) \<in> s"
    (is "\<exists>A B C D. ?P A B \<and> _ \<and> ?Q A \<and> _")
    by (rule owner_seskey_other [OF A C])
  then obtain A B' where "?P A B'" and "?Q A" by blast
  assume "SesKey SK \<in> spied s"
  hence "\<exists>S A' C. fst SK = Some S \<and> A' \<in> fst (snd SK) \<and> C \<in> snd (snd SK) \<and>
    {PriKey S, PriKey A', PriKey C} \<subseteq> spied s"
    (is "\<exists>S A' C. _ \<and> ?R A' \<and> _")
    by (rule seskey_spied [OF A])
  then obtain A' where "A' \<in> fst (snd SK)" and "PriKey A' \<in> spied s" (is "?R A'")
    by blast
  hence "{A', A, B} \<subseteq> {A, B'}"
    using E and \<open>?P A B'\<close> by simp
  hence "card {A', A, B} \<le> card {A, B'}"
    by (rule_tac card_mono, simp)
  also have "\<dots> \<le> Suc (Suc 0)"
    by (rule card_insert_le_m1, simp_all)
  finally have "card {A', A, B} \<le> Suc (Suc 0)" .
  moreover have "card {A', A, B} = Suc (card {A, B})"
  proof (rule card_insert_disjoint, simp_all, rule conjI, rule_tac [!] notI)
    assume "A' = A"
    hence "?R A"
      using \<open>?R A'\<close> by simp
    moreover have "\<not> ?R A"
      by (rule owner_ii_secret [OF A \<open>?Q A\<close>])
    ultimately show False by contradiction
  next
    assume "A' = B"
    hence "?R B"
      using \<open>?R A'\<close> by simp
    moreover have "\<not> ?R B"
      by (rule asset_ii_secret [OF A B D])
    ultimately show False by contradiction
  qed
  moreover have "card {A, B} = Suc (card {B})"
  proof (rule card_insert_disjoint, simp_all, rule notI)
    assume "A = B"
    hence "(Asset n, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s"
      using D by simp
    thus False
      by (rule asset_ii_owner_ii [OF A _ \<open>?Q A\<close>])
  qed
  ultimately show False by simp
qed

proposition asset_seskey_shakey:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey" and
    C: "(Asset n, SesKey SK) \<in> s"
  shows "SesKey SK \<notin> spied s"
proof
  have "\<exists>S. fst SK = Some S \<and>
    (Asset n, Crypt (Auth_ShaKey n) (PriKey S)) \<in> s"
    (is "\<exists>S. ?P S \<and> ?Q S")
    by (rule asset_seskey_nonce [OF A C])
  then obtain S where "?P S" and "?Q S" by blast
  have "PriKey S \<notin> spied s"
    by (rule asset_i_secret [OF A B \<open>?Q S\<close>])
  moreover assume "SesKey SK \<in> spied s"
  hence "\<exists>S A C. fst SK = Some S \<and> A \<in> fst (snd SK) \<and> C \<in> snd (snd SK) \<and>
    {PriKey S, PriKey A, PriKey C} \<subseteq> spied s"
    by (rule seskey_spied [OF A])
  hence "PriKey S \<in> spied s"
    using \<open>?P S\<close> by auto
  ultimately show False by contradiction
qed


theorem owner_seskey_unique:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "(Owner m, Crypt (SesK SK) (Pwd m)) \<in> s" and
    C: "(Owner n, Crypt (SesK SK) (Pwd n)) \<in> s"
  shows "m = n"
proof (rule ccontr)
  have D: "(Owner m, SesKey SK) \<in> s \<and>
    (\<exists>A B C. Token m A B C SK \<in> used s \<and> B \<in> fst (snd SK))"
    (is "?P m \<and> (\<exists>A B C. ?Q m A B C)")
    by (rule owner_v_state [OF A B])
  hence "?P m" by blast
  hence "\<exists>A B C D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
    (Owner m, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<and>
    (Owner m, \<lbrace>Num 3, PubKey C\<rbrace>) \<in> s \<and>
    (Owner m, Crypt (SesK SK) (PubKey D)) \<in> s"
    (is "\<exists>A B C D. ?R A B \<and> ?S C D \<and> ?T m A \<and> ?U m C D")
    by (rule owner_seskey_other [OF A])
  then obtain A B where "?R A B" and "?T m A" by blast
  have "?P n \<and> (\<exists>A B C. ?Q n A B C)"
    by (rule owner_v_state [OF A C])
  hence "?P n" by blast
  hence "\<exists>A B C D. ?R A B \<and> ?S C D \<and> ?T n A \<and> ?U n C D"
    by (rule owner_seskey_other [OF A])
  then obtain A' B' where "?R A' B'" and "?T n A'" by blast
  from D obtain A'' B'' C where "?Q m A'' B'' C" by blast
  hence "Token m A'' B'' C SK \<in> parts (used s)" by blast
  hence "Crypt (SesK SK) (A'' \<otimes> B'') \<in> parts (used s)" by blast
  hence "B'' \<in> fst (snd SK) \<and>
    (\<exists>i C'. (Asset i, Token i (Auth_PriK i) B'' C' SK) \<in> s) \<or>
    {A'' \<otimes> B'', SesKey SK} \<subseteq> spied s"
    (is "?V B'' \<and> (\<exists>i C'. ?W i B'' C') \<or> _")
    by (rule parts_crypt_mult [OF A])
  hence "\<exists>D. ?V D \<and> D \<notin> {A, A'}"
  proof (rule disjE, (erule_tac conjE, ((erule_tac exE)+)?)+)
    fix i C'
    assume "?V B''" and "?W i B'' C'"
    have "\<exists>A D. ?R A B'' \<and> ?S C' D \<and>
      (Asset i, \<lbrace>Num 2, PubKey B''\<rbrace>) \<in> s \<and> (Asset i, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> s \<and>
      Crypt (SesK SK) (PubKey D) \<in> used s \<and> (Asset i, PubKey B'') \<in> s"
      (is "\<exists>A D. _ \<and> _ \<and> ?X i B'' \<and> _")
      by (rule asset_iv_state [OF A \<open>?W i B'' C'\<close>])
    hence "?X i B''" by blast
    have "B'' \<noteq> A"
    proof
      assume "B'' = A"
      hence "?X i A"
        using \<open>?X i B''\<close> by simp
      thus False
        by (rule asset_ii_owner_ii [OF A _ \<open>?T m A\<close>])
    qed
    moreover have "B'' \<noteq> A'"
    proof
      assume "B'' = A'"
      hence "?X i A'"
        using \<open>?X i B''\<close> by simp
      thus False
        by (rule asset_ii_owner_ii [OF A _ \<open>?T n A'\<close>])
    qed
    ultimately show ?thesis
      using \<open>?V B''\<close> by blast
  next
    assume "{A'' \<otimes> B'', SesKey SK} \<subseteq> spied s"
    hence "SesKey SK \<in> spied s" by simp
    hence "\<exists>S D E. fst SK = Some S \<and> ?V D \<and> E \<in> snd (snd SK) \<and>
      {PriKey S, PriKey D, PriKey E} \<subseteq> spied s"
      by (rule seskey_spied [OF A])
    then obtain D where "?V D" and "PriKey D \<in> spied s" (is "?X D")
      by blast
    moreover have "D \<noteq> A"
    proof
      assume "D = A"
      hence "?X A"
        using \<open>?X D\<close> by simp
      moreover have "\<not> ?X A"
        by (rule owner_ii_secret [OF A \<open>?T m A\<close>])
      ultimately show False by contradiction
    qed
    moreover have "D \<noteq> A'"
    proof
      assume "D = A'"
      hence "?X A'"
        using \<open>?X D\<close> by simp
      moreover have "\<not> ?X A'"
        by (rule owner_ii_secret [OF A \<open>?T n A'\<close>])
      ultimately show False by contradiction
    qed
    ultimately show ?thesis by blast
  qed
  then obtain D where "?V D" and E: "D \<notin> {A, A'}" by blast
  hence "{D, A, A'} \<subseteq> {A, B}"
    using \<open>?R A B\<close> and \<open>?R A' B'\<close> by blast
  hence "card {D, A, A'} \<le> card {A, B}"
    by (rule_tac card_mono, simp)
  also have "\<dots> \<le> Suc (Suc 0)"
    by (rule card_insert_le_m1, simp_all)
  finally have "card {D, A, A'} \<le> Suc (Suc 0)" .
  moreover have "card {D, A, A'} = Suc (card {A, A'})"
    by (rule card_insert_disjoint [OF _ E], simp)
  moreover assume "m \<noteq> n"
  hence "card {A, A'} = Suc (card {A'})"
  proof (rule_tac card_insert_disjoint, simp_all, erule_tac contrapos_nn)
    assume "A = A'"
    hence "?T n A"
      using \<open>?T n A'\<close> by simp
    thus "m = n"
      by (rule owner_ii_unique [OF A \<open>?T m A\<close>])
  qed
  ultimately show False by simp
qed


theorem owner_seskey_secret:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey \<inter> bad_prikey" and
    C: "(Owner n, Crypt (SesK SK) (Pwd n)) \<in> s"
  shows "SesKey SK \<notin> spied s"
proof -
  have "(Owner n, SesKey SK) \<in> s \<and>
    (\<exists>A B C. Token n A B C SK \<in> used s \<and> B \<in> fst (snd SK))"
    (is "?P \<and> (\<exists>A B C. ?Q A B C \<and> ?R B)")
    by (rule owner_v_state [OF A C])
  then obtain A B C where "?P" and "?Q A B C" and "?R B" by blast
  have "n \<in> bad_shakey \<or> n \<notin> bad_shakey" by simp
  moreover {
    assume "n \<in> bad_shakey"
    hence D: "n \<notin> bad_prikey"
      using B by simp
    hence "Auth_PriKey n \<notin> spied s"
      by (rule auth_prikey_secret [OF A])
    moreover have "Sign n A \<in> parts (used s)"
      using \<open>?Q A B C\<close> by blast
    hence "A = Auth_PriK n"
      by (rule parts_sign [OF A])
    hence "?Q (Auth_PriK n) B C"
      using \<open>?Q A B C\<close> by simp
    hence "Auth_PriK n \<otimes> B \<in> parts (used s)" by blast
    hence "(\<exists>m. Auth_PriK n = Auth_PriK m \<and>
      (Asset m, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s) \<or>
      {PriKey (Auth_PriK n), PriKey B} \<subseteq> spied s"
      (is "(\<exists>m. ?S m \<and> ?T m) \<or> _")
      by (rule parts_mult [OF A])
    ultimately obtain m where "?S m" and "?T m" by auto
    hence "m \<notin> bad_prikey"
      using D by simp
    hence ?thesis
      by (rule owner_seskey_prikey [OF A _ \<open>?P\<close> \<open>?T m\<close> \<open>?R B\<close>])
  }
  moreover {
    assume "n \<notin> bad_shakey"
    hence ?thesis
      by (rule owner_seskey_shakey [OF A _ \<open>?P\<close>])
  }
  ultimately show ?thesis ..
qed


theorem owner_num_genuine:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey \<inter> bad_prikey" and
    C: "(Owner n, Crypt (SesK SK) (Pwd n)) \<in> s" and
    D: "Crypt (SesK SK) (Num 0) \<in> used s"
  shows "(Asset n, Crypt (SesK SK) (Num 0)) \<in> s"
proof -
  have "Crypt (SesK SK) (Num 0) \<in> parts (used s)"
    using D ..
  hence "(\<exists>m. (Asset m, Crypt (SesK SK) (Num 0)) \<in> s) \<or>
    SesKey SK \<in> spied s"
    by (rule parts_crypt_num [OF A])
  moreover have E: "SesKey SK \<notin> spied s"
    by (rule owner_seskey_secret [OF A B C])
  ultimately obtain m where "(Asset m, Crypt (SesK SK) (Num 0)) \<in> s"
    by blast
  moreover from this have "(Asset m, SesKey SK) \<in> s \<and>
    Crypt (SesK SK) (Pwd m) \<in> used s"
    by (rule asset_v_state [OF A])
  hence "Crypt (SesK SK) (Pwd m) \<in> parts (used s)" by blast
  hence "(\<exists>SK'. SesK SK = SesK SK' \<and>
    (Owner m, Crypt (SesK SK') (Pwd m)) \<in> s) \<or>
    {Pwd m, Key (SesK SK)} \<subseteq> spied s"
    by (rule parts_crypt_pwd [OF A])
  hence "(Owner m, Crypt (SesK SK) (Pwd m)) \<in> s"
    using E by simp
  hence "m = n"
    by (rule owner_seskey_unique [OF A _ C])
  ultimately show ?thesis by simp
qed


theorem owner_token_genuine:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey \<inter> bad_prikey" and
    C: "(Owner n, \<lbrace>Num 3, PubKey C\<rbrace>) \<in> s" and
    D: "(Owner n, Crypt (SesK SK) (Pwd n)) \<in> s" and
    E: "Token n A B C SK \<in> used s"
  shows "A = Auth_PriK n \<and> B \<in> fst (snd SK) \<and> C \<in> snd (snd SK) \<and>
    (Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s \<and> (Asset n, Token n A B C SK) \<in> s"
    (is "?P n A \<and> ?Q B \<and> ?R C \<and> ?S n B \<and> _")
proof -
  have "Crypt (SesK SK) (Sign n A) \<in> parts (used s)"
    using E by blast
  hence "(Asset n, SesKey SK) \<in> s \<or> SesKey SK \<in> spied s"
    by (rule parts_crypt_sign [OF A])
  moreover have "SesKey SK \<notin> spied s"
    by (rule owner_seskey_secret [OF A B D])
  ultimately have "(Asset n, SesKey SK) \<in> s" by simp
  hence "\<exists>A B C D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
    ?S n B \<and> (Asset n, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> s \<and>
    (Asset n, Token n (Auth_PriK n) B C SK) \<in> s"
    (is "\<exists>A B C D. ?T A B \<and> ?U C D \<and> _ \<and> ?V n D \<and> ?W n B C")
    by (rule asset_seskey_other [OF A])
  then obtain A' B' C' D where
   "?T A' B'" and "?U C' D" and "?S n B'" and "?V n D" and "?W n B' C'"
    by blast
  have "Sign n A \<in> parts (used s)"
    using E by blast
  hence "?P n A"
    by (rule parts_sign [OF A])
  have "Crypt (SesK SK) (A \<otimes> B) \<in> parts (used s)"
    using E by blast
  hence "?Q B \<and> (\<exists>m C''. ?W m B C'') \<or> {A \<otimes> B, SesKey SK} \<subseteq> spied s"
    by (rule parts_crypt_mult [OF A])
  moreover have F: "SesKey SK \<notin> spied s"
    by (rule owner_seskey_secret [OF A B D])
  ultimately obtain m C'' where "?Q B" and "?W m B C''" by blast
  have "\<exists>A D. ?T A B \<and> ?U C'' D \<and> ?S m B \<and> ?V m D \<and>
    Crypt (SesK SK) (PubKey D) \<in> used s \<and> (Asset m, PubKey B) \<in> s"
    by (rule asset_iv_state [OF A \<open>?W m B C''\<close>])
  hence "?S m B" by blast
  have "(Owner n, SesKey SK) \<in> s \<and>
    (\<exists>A B C. Token n A B C SK \<in> used s \<and> B \<in> fst (snd SK))"
    by (rule owner_v_state [OF A D])
  hence "(Owner n, SesKey SK) \<in> s" by blast
  hence "\<exists>A B C D. ?T A B \<and> ?U C D \<and>
    (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<and>
    (Owner n, \<lbrace>Num 3, PubKey C\<rbrace>) \<in> s \<and>
    (Owner n, Crypt (SesK SK) (PubKey D)) \<in> s"
    (is "\<exists>A B C D. _ \<and> _ \<and> ?X A \<and> _")
    by (rule owner_seskey_other [OF A])
  then obtain A'' where "?Q A''" and "?X A''" by blast
  have G: "B' = B"
  proof (rule ccontr)
    have "{A'', B', B} \<subseteq> {A', B'}"
      using \<open>?T A' B'\<close> and \<open>?Q B\<close> and \<open>?Q A''\<close> by simp
    hence "card {A'', B', B} \<le> card {A', B'}"
      by (rule_tac card_mono, simp)
    also have "\<dots> \<le> Suc (Suc 0)"
      by (rule card_insert_le_m1, simp_all)
    finally have "card {A'', B', B} \<le> Suc (Suc 0)" .
    moreover have "A'' \<notin> {B', B}"
    proof (simp, rule conjI, rule_tac [!] notI)
      assume "A'' = B'"
      hence "?S n A''"
        using \<open>?S n B'\<close> by simp
      thus False
        by (rule asset_ii_owner_ii [OF A _ \<open>?X A''\<close>])
    next
      assume "A'' = B"
      hence "?S m A''"
        using \<open>?S m B\<close> by simp
      thus False
        by (rule asset_ii_owner_ii [OF A _ \<open>?X A''\<close>])
    qed
    hence "card {A'', B', B} = Suc (card {B', B})"
      by (rule_tac card_insert_disjoint, simp)
    moreover assume "B' \<noteq> B"
    hence "card {B', B} = Suc (card {B})"
      by (rule_tac card_insert_disjoint, simp_all)
    ultimately show False by simp
  qed
  hence "?S n B"
    using \<open>?S n B'\<close> by simp
  have "Crypt (SesK SK) (PubKey C) \<in> parts (used s)"
    using E by blast
  hence "?R C \<and> ((\<exists>n. (Owner n, SesKey SK) \<in> s) \<or> (\<exists>n B. ?W n B C)) \<or>
    SesKey SK \<in> spied s"
    by (rule parts_crypt_pubkey [OF A])
  hence "?R C"
    using F by simp
  hence "C \<in> {C', D}"
    using \<open>?U C' D\<close> by simp
  moreover have "C \<noteq> D"
  proof
    assume "C = D"
    hence "?V n C"
      using \<open>?V n D\<close> by simp
    thus False
      by (rule asset_iii_owner_iii [OF A _ C])
  qed
  ultimately have "C = C'" by simp
  hence "(Asset n, Token n A B C SK) \<in> s"
    using G and \<open>?P n A\<close> and \<open>?W n B' C'\<close> by simp
  thus ?thesis
    using \<open>?P n A\<close> and \<open>?Q B\<close> and \<open>?R C\<close> and \<open>?S n B\<close> by simp
qed


theorem pwd_secret:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_pwd \<union> bad_shakey \<inter> bad_prikey"
  shows "Pwd n \<notin> spied s"
proof (rule rtrancl_induct [OF A], insert B, simp add: image_def)
  fix s s'
  assume
    C: "s\<^sub>0 \<Turnstile> s" and
    D: "s \<turnstile> s'" and
    E: "Pwd n \<notin> spied s"
  show "Pwd n \<notin> spied s'"
  proof (insert D E, auto simp add: rel_def)
    fix K
    assume "(Spy, Crypt K (Pwd n)) \<in> s"
    hence "Crypt K (Pwd n) \<in> parts (used s)" by blast
    hence "(\<exists>SK. K = SesK SK \<and> (Owner n, Crypt (SesK SK) (Pwd n)) \<in> s) \<or>
      {Pwd n, Key K} \<subseteq> spied s"
      (is "(\<exists>SK. ?P SK \<and> ?Q SK) \<or> _")
      by (rule parts_crypt_pwd [OF C])
    then obtain SK where "?P SK" and "?Q SK"
      using E by blast
    have "n \<notin> bad_shakey \<inter> bad_prikey"
      using B by simp
    hence "SesKey SK \<notin> spied s"
      by (rule owner_seskey_secret [OF C _ \<open>?Q SK\<close>])
    moreover assume "(Spy, Key (InvK K)) \<in> s"
    ultimately show False
      using \<open>?P SK\<close> by simp
  next
    fix Y
    assume "(Spy, \<lbrace>Pwd n, Y\<rbrace>) \<in> s"
    hence "\<lbrace>Pwd n, Y\<rbrace> \<in> parts (used s)" by blast
    hence "{Pwd n, Y} \<subseteq> spied s"
      by (rule parts_mpair_pwd [OF C, where n = n], simp)
    with E show False by simp
  next
    fix X
    assume "(Spy, \<lbrace>X, Pwd n\<rbrace>) \<in> s"
    hence "\<lbrace>X, Pwd n\<rbrace> \<in> parts (used s)" by blast
    hence "{X, Pwd n} \<subseteq> spied s"
      by (rule parts_mpair_pwd [OF C, where n = n], simp)
    with E show False by simp
  qed
qed


theorem asset_seskey_unique:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "(Asset m, Token m (Auth_PriK m) B' C' SK) \<in> s" and
    C: "(Asset n, Token n (Auth_PriK n) B C SK) \<in> s"
      (is "?P n B C SK s")
  shows "m = n \<and> B' = B \<and> C' = C"
proof (subst (2) cases_simp [of "B' = B", symmetric], simp, rule conjI, rule impI,
 insert B C, simp only:, drule asset_iv_unique [OF A], simp, simp, rule ccontr)
  assume "B' \<noteq> B"
  moreover have "\<exists>A D. fst (snd SK) = {A, B'} \<and> snd (snd SK) = {C', D} \<and>
    (Asset m, \<lbrace>Num 2, PubKey B'\<rbrace>) \<in> s \<and> (Asset m, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> s \<and>
    Crypt (SesK SK) (PubKey D) \<in> used s \<and> (Asset m, PubKey B') \<in> s"
    (is "?Q m B' C'")
    by (rule asset_iv_state [OF A B])
  then obtain A where "fst (snd SK) = {A, B'}" and
    "(Asset m, \<lbrace>Num 2, PubKey B'\<rbrace>) \<in> s"
    by blast
  moreover have "?Q n B C"
    by (rule asset_iv_state [OF A C])
  hence "B \<in> fst (snd SK)" and "(Asset n, \<lbrace>Num 2, PubKey B\<rbrace>) \<in> s"
    by auto
  ultimately have D: "\<forall>A \<in> fst (snd SK).
    \<exists>i C. (Asset i, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s \<and> ?P i A C SK s"
    using B and C by auto
  have "Crypt (SesK SK) (PubKey C) \<in> parts (used s)"
    using C by blast
  thus False
  proof (rule parts_pubkey_false [OF A], rule_tac allI, rule_tac [!] notI)
    fix i
    assume "(Owner i, SesKey SK) \<in> s"
    hence "\<exists>A B C D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
      (Owner i, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<and>
      (Owner i, \<lbrace>Num 3, PubKey C\<rbrace>) \<in> s \<and>
      (Owner i, Crypt (SesK SK) (PubKey D)) \<in> s"
      by (rule owner_seskey_other [OF A])
    then obtain A where "A \<in> fst (snd SK)" and
      E: "(Owner i, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s"
      by blast
    then obtain j where "(Asset j, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s"
      using D by blast
    thus False
      by (rule asset_ii_owner_ii [OF A _ E])
  next
    assume "SesKey SK \<in> spied s"
    hence "\<exists>S A C. fst SK = Some S \<and> A \<in> fst (snd SK) \<and> C \<in> snd (snd SK) \<and>
      {PriKey S, PriKey A, PriKey C} \<subseteq> spied s"
      (is "?R s")
      by (rule seskey_spied [OF A])
    moreover have "\<not> (\<exists>A \<in> fst (snd SK). PriKey A \<in> spied s)"
      (is "\<not> ?S s")
    proof
      assume "?S s"
      moreover have "\<not> ?S s\<^sub>0"
        by (subst bex_simps, rule ballI, drule bspec [OF D], (erule exE)+,
         erule conjE, rule asset_ii_init [OF A])
      ultimately have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> s \<and> \<not> ?S u \<and> ?S v"
        by (rule rtrancl_start [OF A])
      then obtain u v A where E: "s\<^sub>0 \<Turnstile> u" and F: "u \<turnstile> v" and G: "v \<Turnstile> s" and
        H: "\<not> ?S u" and I: "A \<in> fst (snd SK)" and J: "PriKey A \<notin> spied u" and
        K: "PriKey A \<in> spied v"
        by blast
      then obtain i where "(Asset i, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s"
        using D by blast
      hence "(Asset i, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> v"
      proof (rule_tac ccontr, drule_tac rtrancl_start [OF G], simp,
       (erule_tac exE)+, (erule_tac conjE)+)
        fix w x
        assume "w \<turnstile> x" and "(Asset i, \<lbrace>Num 2, PubKey A\<rbrace>) \<notin> w" and
          "(Asset i, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> x"
        hence "PriKey A \<notin> spied w"
          by (auto simp add: rel_def)
        moreover assume "v \<Turnstile> w"
        hence "PriKey A \<in> spied w"
          by (rule_tac rev_subsetD [OF K], rule spied_subset)
        ultimately show False by contradiction
      qed
      hence "(Asset i, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> u"
        using F and K by (auto simp add: rel_def)
      hence "Auth_PriKey i \<in> spied u \<and> (\<exists>C SK. ?P i A C SK u)"
        by (rule asset_ii_spied_start [OF E F K J])
      then obtain C' SK' where L: "?P i A C' SK' u" by blast
      moreover have M: "u \<Turnstile> s"
        using F and G by simp
      ultimately have "?P i A C' SK' s"
        by (erule_tac rev_subsetD, rule_tac state_subset)
      moreover obtain j C where "?P j A C SK s"
        using D and I by blast
      ultimately have "i = j \<and> C' = C \<and> SK' = SK"
        by (rule asset_iv_unique [OF A])
      hence "Crypt (SesK SK) (PubKey C) \<in> parts (used u)"
        using L by blast
      thus False
      proof (rule parts_pubkey_false [OF E], rule_tac allI, rule_tac [!] notI)
        fix i
        assume "(Owner i, SesKey SK) \<in> u"
        hence "\<exists>A B C D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
          (Owner i, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> u \<and>
          (Owner i, \<lbrace>Num 3, PubKey C\<rbrace>) \<in> u \<and>
          (Owner i, Crypt (SesK SK) (PubKey D)) \<in> u"
          by (rule owner_seskey_other [OF E])
        then obtain A where "A \<in> fst (snd SK)" and
          N: "(Owner i, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> u"
          by blast
        then obtain j where "(Asset j, \<lbrace>Num 2, PubKey A\<rbrace>) \<in> s"
          using D by blast
        moreover have "(Owner i, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s"
          by (rule rev_subsetD [OF N], rule state_subset [OF M])
        ultimately show False
          by (rule asset_ii_owner_ii [OF A])
      next
        assume "SesKey SK \<in> spied u"
        hence "?R u"
          by (rule seskey_spied [OF E])
        thus False
          using H by blast
      qed
    qed
    ultimately show False by blast
  qed
qed


theorem asset_seskey_secret:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey \<inter> (bad_pwd \<union> bad_prikey)" and
    C: "(Asset n, Crypt (SesK SK) (Num 0)) \<in> s"
  shows "SesKey SK \<notin> spied s"
proof -
  have D: "(Asset n, SesKey SK) \<in> s \<and> Crypt (SesK SK) (Pwd n) \<in> used s"
    by (rule asset_v_state [OF A C])
  have "n \<in> bad_shakey \<or> n \<notin> bad_shakey" by simp
  moreover {
    assume "n \<in> bad_shakey"
    hence "Pwd n \<notin> spied s"
      using B by (rule_tac pwd_secret [OF A], simp)
    moreover have "Crypt (SesK SK) (Pwd n) \<in> parts (used s)"
      using D by blast
    hence "(\<exists>SK'. SesK SK = SesK SK' \<and>
      (Owner n, Crypt (SesK SK') (Pwd n)) \<in> s) \<or>
      {Pwd n, Key (SesK SK)} \<subseteq> spied s"
      by (rule parts_crypt_pwd [OF A])
    ultimately have "(Owner n, Crypt (SesK SK) (Pwd n)) \<in> s" by simp
    hence ?thesis
      using B by (rule_tac owner_seskey_secret [OF A], simp_all)
  }
  moreover {
    assume "n \<notin> bad_shakey"
    hence ?thesis
      using D by (rule_tac asset_seskey_shakey [OF A], simp_all)
  }
  ultimately show ?thesis ..
qed


theorem asset_pwd_genuine:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey \<inter> (bad_pwd \<union> bad_prikey)" and
    C: "(Asset n, Crypt (SesK SK) (Num 0)) \<in> s"
  shows "(Owner n, Crypt (SesK SK) (Pwd n)) \<in> s"
proof -
  have "(Asset n, SesKey SK) \<in> s \<and> Crypt (SesK SK) (Pwd n) \<in> used s"
    by (rule asset_v_state [OF A C])
  hence "Crypt (SesK SK) (Pwd n) \<in> parts (used s)" by blast
  hence "(\<exists>SK'. SesK SK = SesK SK' \<and>
    (Owner n, Crypt (SesK SK') (Pwd n)) \<in> s) \<or>
    {Pwd n, Key (SesK SK)} \<subseteq> spied s"
    by (rule parts_crypt_pwd [OF A])
  moreover have "SesKey SK \<notin> spied s"
    by (rule asset_seskey_secret [OF A B C])
  ultimately show ?thesis by simp
qed


theorem asset_token_genuine:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_shakey \<inter> (bad_pwd \<union> bad_prikey)" and
    C: "(Asset n, \<lbrace>Num 4, PubKey D\<rbrace>) \<in> s" and
    D: "(Asset n, Crypt (SesK SK) (Num 0)) \<in> s" and
    E: "D \<in> snd (snd SK)"
  shows "(Owner n, Crypt (SesK SK) (PubKey D)) \<in> s"
proof -
  have "(Owner n, Crypt (SesK SK) (Pwd n)) \<in> s"
    by (rule asset_pwd_genuine [OF A B D])
  hence "(Owner n, SesKey SK) \<in> s \<and>
    (\<exists>A B C. Token n A B C SK \<in> used s \<and> B \<in> fst (snd SK))"
    by (rule owner_v_state [OF A])
  hence "(Owner n, SesKey SK) \<in> s" ..
  hence "\<exists>A B C D. fst (snd SK) = {A, B} \<and> snd (snd SK) = {C, D} \<and>
    (Owner n, \<lbrace>Num 1, PubKey A\<rbrace>) \<in> s \<and>
    (Owner n, \<lbrace>Num 3, PubKey C\<rbrace>) \<in> s \<and>
    (Owner n, Crypt (SesK SK) (PubKey D)) \<in> s"
    (is "\<exists>A B C D. _ \<and> ?P C D \<and> _ \<and> ?Q C \<and> ?R D")
    by (rule owner_seskey_other [OF A])
  then obtain C D' where "?P C D'" and "?Q C" and "?R D'" by blast
  have "D \<noteq> C"
  proof
    assume "D = C"
    hence "?Q D"
      using \<open>?Q C\<close> by simp
    thus False
      by (rule asset_iii_owner_iii [OF A C])
  qed
  hence "D = D'"
    using E and \<open>?P C D'\<close> by simp
  thus ?thesis
    using \<open>?R D'\<close> by simp
qed


end