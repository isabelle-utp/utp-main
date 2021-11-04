(*  Title:       The Relational Method with Message Anonymity for the Verification of Cryptographic Protocols
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Anonymity properties"

theory Anonymity
  imports Authentication
begin

text \<open>
\label{Anonymity}
\<close>


proposition crypts_empty [simp]:
 "crypts {} = {}"
by (rule equalityI, rule subsetI, erule crypts.induct, simp_all)

proposition crypts_mono:
 "H \<subseteq> H' \<Longrightarrow> crypts H \<subseteq> crypts H'"
by (rule subsetI, erule crypts.induct, auto)

lemma crypts_union_1:
 "crypts (H \<union> H') \<subseteq> crypts H \<union> crypts H'"
by (rule subsetI, erule crypts.induct, auto)

lemma crypts_union_2:
 "crypts H \<union> crypts H' \<subseteq> crypts (H \<union> H')"
by (rule subsetI, erule UnE, erule_tac [!] crypts.induct, auto)

proposition crypts_union:
 "crypts (H \<union> H') = crypts H \<union> crypts H'"
by (rule equalityI, rule crypts_union_1, rule crypts_union_2)

proposition crypts_insert:
 "crypts (insert X H) = crypts_msg X \<union> crypts H"
by (simp only: insert_def crypts_union, subst crypts_msg_def, simp)

proposition crypts_msg_num [simp]:
 "crypts_msg (Num n) = {Num n}"
by (subst crypts_msg_def, rule equalityI, rule subsetI, erule crypts.induct, simp,
 rotate_tac [1-3], erule_tac [1-3] rev_mp, rule_tac [1-3] list.induct, simp_all,
 blast)

proposition crypts_msg_agent [simp]:
 "crypts_msg (Agent n) = {Agent n}"
by (subst crypts_msg_def, rule equalityI, rule subsetI, erule crypts.induct, simp,
 rotate_tac [1-3], erule_tac [1-3] rev_mp, rule_tac [1-3] list.induct, simp_all,
 blast)

proposition crypts_msg_pwd [simp]:
 "crypts_msg (Pwd n) = {Pwd n}"
by (subst crypts_msg_def, rule equalityI, rule subsetI, erule crypts.induct, simp,
 rotate_tac [1-3], erule_tac [1-3] rev_mp, rule_tac [1-3] list.induct, simp_all,
 blast)

proposition crypts_msg_key [simp]:
 "crypts_msg (Key K) = {Key K}"
by (subst crypts_msg_def, rule equalityI, rule subsetI, erule crypts.induct, simp,
 rotate_tac [1-3], erule_tac [1-3] rev_mp, rule_tac [1-3] list.induct, simp_all,
 blast)

proposition crypts_msg_mult [simp]:
 "crypts_msg (A \<otimes> B) = {A \<otimes> B}"
by (subst crypts_msg_def, rule equalityI, rule subsetI, erule crypts.induct, simp,
 rotate_tac [1-3], erule_tac [1-3] rev_mp, rule_tac [1-3] list.induct, simp_all,
 blast)

lemma crypts_hash_1:
 "crypts {Hash X} \<subseteq> insert (Hash X) (crypts {X})"
by (rule subsetI, erule crypts.induct, simp_all, (erule disjE, rotate_tac, erule rev_mp,
 rule list.induct, simp_all, blast, (drule crypts_hash, simp)?)+)

lemma crypts_hash_2:
 "insert (Hash X) (crypts {X}) \<subseteq> crypts {Hash X}"
by (rule subsetI, simp, erule disjE, blast, erule crypts.induct, simp,
 subst id_apply [symmetric], subst foldr_Nil [symmetric], rule crypts_hash, simp,
 blast+)

proposition crypts_msg_hash [simp]:
 "crypts_msg (Hash X) = insert (Hash X) (crypts_msg X)"
by (simp add: crypts_msg_def, rule equalityI, rule crypts_hash_1, rule crypts_hash_2)

proposition crypts_comp:
 "X \<in> crypts H \<Longrightarrow> Crypt K X \<in> crypts (Crypt K ` H)"
by (erule crypts.induct, blast, (simp only: comp_apply
 [symmetric, where f = "Crypt K"] foldr_Cons [symmetric],
 (erule crypts_hash | erule crypts_fst | erule crypts_snd))+)

lemma crypts_crypt_1:
 "crypts {Crypt K X} \<subseteq> Crypt K ` crypts {X}"
by (rule subsetI, erule crypts.induct, fastforce, rotate_tac [!], erule_tac [!] rev_mp,
 rule_tac [!] list.induct, auto)

lemma crypts_crypt_2:
 "Crypt K ` crypts {X} \<subseteq> crypts {Crypt K X}"
by (rule subsetI, simp add: image_iff, erule bexE, drule crypts_comp, simp)

proposition crypts_msg_crypt [simp]:
 "crypts_msg (Crypt K X) = Crypt K ` crypts_msg X"
by (simp add: crypts_msg_def, rule equalityI, rule crypts_crypt_1, rule crypts_crypt_2)

lemma crypts_mpair_1:
 "crypts {\<lbrace>X, Y\<rbrace>} \<subseteq> insert \<lbrace>X, Y\<rbrace> (crypts {X} \<union> crypts {Y})"
by (rule subsetI, erule crypts.induct, simp_all, (erule disjE, rotate_tac, erule rev_mp,
 rule list.induct, (simp+, blast)+)+)

lemma crypts_mpair_2:
 "insert \<lbrace>X, Y\<rbrace> (crypts {X} \<union> crypts {Y}) \<subseteq> crypts {\<lbrace>X, Y\<rbrace>}"
by (rule subsetI, simp, erule disjE, blast, erule disjE, (erule crypts.induct, simp,
 subst id_apply [symmetric], subst foldr_Nil [symmetric], (rule crypts_fst [of _ X] |
 rule crypts_snd), rule crypts_used, simp, blast+)+)

proposition crypts_msg_mpair [simp]:
 "crypts_msg \<lbrace>X, Y\<rbrace> = insert \<lbrace>X, Y\<rbrace> (crypts_msg X \<union> crypts_msg Y)"
by (simp add: crypts_msg_def, rule equalityI, rule crypts_mpair_1, rule crypts_mpair_2)


proposition foldr_crypt_size:
 "size (foldr Crypt KS X) = size X + length KS"
by (induction KS, simp_all)

proposition key_sets_empty [simp]:
 "key_sets X {} = {}"
by (simp add: key_sets_def)

proposition key_sets_mono:
 "H \<subseteq> H' \<Longrightarrow> key_sets X H \<subseteq> key_sets X H'"
by (auto simp add: key_sets_def)

proposition key_sets_union:
 "key_sets X (H \<union> H') = key_sets X H \<union> key_sets X H'"
by (auto simp add: key_sets_def)

proposition key_sets_insert:
 "key_sets X (insert Y H) = key_sets_msg X Y \<union> key_sets X H"
by (simp only: insert_def key_sets_union, subst key_sets_msg_def, simp)

proposition key_sets_msg_eq:
 "key_sets_msg X X = {{}}"
by (simp add: key_sets_msg_def key_sets_def, rule equalityI, rule subsetI, simp,
 erule exE, erule rev_mp, rule list.induct, simp, rule impI, erule conjE,
 drule arg_cong [of _ X size], simp_all add: foldr_crypt_size)

proposition key_sets_msg_num [simp]:
 "key_sets_msg X (Num n) = (if X = Num n then {{}} else {})"
by (simp add: key_sets_msg_eq, simp add: key_sets_msg_def key_sets_def, rule impI,
 rule allI, rule list.induct, simp_all)

proposition key_sets_msg_agent [simp]:
 "key_sets_msg X (Agent n) = (if X = Agent n then {{}} else {})"
by (simp add: key_sets_msg_eq, simp add: key_sets_msg_def key_sets_def, rule impI,
 rule allI, rule list.induct, simp_all)

proposition key_sets_msg_pwd [simp]:
 "key_sets_msg X (Pwd n) = (if X = Pwd n then {{}} else {})"
by (simp add: key_sets_msg_eq, simp add: key_sets_msg_def key_sets_def, rule impI,
 rule allI, rule list.induct, simp_all)

proposition key_sets_msg_key [simp]:
 "key_sets_msg X (Key K) = (if X = Key K then {{}} else {})"
by (simp add: key_sets_msg_eq, simp add: key_sets_msg_def key_sets_def, rule impI,
 rule allI, rule list.induct, simp_all)

proposition key_sets_msg_mult [simp]:
 "key_sets_msg X (A \<otimes> B) = (if X = A \<otimes> B then {{}} else {})"
by (simp add: key_sets_msg_eq, simp add: key_sets_msg_def key_sets_def, rule impI,
 rule allI, rule list.induct, simp_all)

proposition key_sets_msg_hash [simp]:
 "key_sets_msg X (Hash Y) = (if X = Hash Y then {{}} else {})"
by (simp add: key_sets_msg_eq, simp add: key_sets_msg_def key_sets_def, rule impI,
 rule allI, rule list.induct, simp_all)

lemma key_sets_crypt_1:
 "X \<noteq> Crypt K Y \<Longrightarrow>
    key_sets X {Crypt K Y} \<subseteq> insert (InvKey K) ` key_sets X {Y}"
by (rule subsetI, simp add: key_sets_def, erule exE, rotate_tac, erule rev_mp,
 rule list.induct, auto)

lemma key_sets_crypt_2:
 "insert (InvKey K) ` key_sets X {Y} \<subseteq> key_sets X {Crypt K Y}"
by (rule subsetI, simp add: key_sets_def image_iff, (erule exE, erule conjE)+,
 drule arg_cong [where f = "Crypt K"], simp only: comp_apply
 [symmetric, of "Crypt K"] foldr_Cons [symmetric], subst conj_commute,
 rule exI, rule conjI, assumption, simp)

proposition key_sets_msg_crypt [simp]:
 "key_sets_msg X (Crypt K Y) = (if X = Crypt K Y then {{}} else
    insert (InvKey K) ` key_sets_msg X Y)"
by (simp add: key_sets_msg_eq, simp add: key_sets_msg_def, rule impI,
 rule equalityI, erule key_sets_crypt_1 [simplified],
 rule key_sets_crypt_2 [simplified])

proposition key_sets_msg_mpair [simp]:
 "key_sets_msg X \<lbrace>Y, Z\<rbrace> = (if X = \<lbrace>Y, Z\<rbrace> then {{}} else {})"
by (simp add: key_sets_msg_eq, simp add: key_sets_msg_def key_sets_def, rule impI,
 rule allI, rule list.induct, simp_all)

proposition key_sets_range:
 "U \<in> key_sets X H \<Longrightarrow> U \<subseteq> range Key"
by (simp add: key_sets_def, blast)

proposition key_sets_crypts_hash:
 "key_sets (Hash X) (crypts H) \<subseteq> key_sets X (crypts H)"
by (simp add: key_sets_def, blast)

proposition key_sets_crypts_fst:
 "key_sets \<lbrace>X, Y\<rbrace> (crypts H) \<subseteq> key_sets X (crypts H)"
by (simp add: key_sets_def, blast)

proposition key_sets_crypts_snd:
 "key_sets \<lbrace>X, Y\<rbrace> (crypts H) \<subseteq> key_sets Y (crypts H)"
by (simp add: key_sets_def, blast)


lemma log_spied_1:
 "\<lbrakk>s \<turnstile> s';
    Log X \<in> parts (used s) \<longrightarrow> Log X \<in> spied s;
    Log X \<in> parts (used s')\<rbrakk> \<Longrightarrow>
  Log X \<in> spied s'"
by (simp add: rel_def, ((erule disjE)?, ((erule exE)+)?, simp add: parts_insert,
 ((subst (asm) disj_assoc [symmetric])?, erule disjE, (drule parts_dec |
 drule parts_enc | drule parts_sep | drule parts_con), simp+)?)+)

proposition log_spied [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    Log X \<in> parts (used s) \<longrightarrow>
  Log X \<in> spied s"
by (erule rtrancl_induct, subst parts_init, simp add: Range_iff image_def, rule impI,
 rule log_spied_1)


proposition log_dec:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; s' = insert (Spy, X) s \<and> (Spy, Crypt K X) \<in> s \<and>
    (Spy, Key (InvK K)) \<in> s\<rbrakk> \<Longrightarrow>
  key_sets Y (crypts {Y. Log Y = X}) \<subseteq> key_sets Y (crypts (Log -` spied s))"
by (rule key_sets_mono, rule crypts_mono, rule subsetI, simp, drule parts_dec
 [where Y = X], drule_tac [!] sym, simp_all, rule log_spied [simplified])

proposition log_sep:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; s' = insert (Spy, X) (insert (Spy, Y) s) \<and> (Spy, \<lbrace>X, Y\<rbrace>) \<in> s\<rbrakk> \<Longrightarrow>
    key_sets Z (crypts {Z. Log Z = X}) \<subseteq> key_sets Z (crypts (Log -` spied s)) \<and>
    key_sets Z (crypts {Z. Log Z = Y}) \<subseteq> key_sets Z (crypts (Log -` spied s))"
by (rule conjI, (rule key_sets_mono, rule crypts_mono, rule subsetI, simp,
 frule parts_sep [where Z = X], drule_tac [2] parts_sep [where Z = Y],
 simp_all add: parts_msg_def, blast+, drule sym, simp,
 rule log_spied [simplified], assumption+)+)


lemma idinfo_spied_1:
 "\<lbrakk>s \<turnstile> s';
    \<langle>n, X\<rangle> \<in> parts (used s) \<longrightarrow> \<langle>n, X\<rangle> \<in> spied s;
    \<langle>n, X\<rangle> \<in> parts (used s')\<rbrakk> \<Longrightarrow>
  \<langle>n, X\<rangle> \<in> spied s'"
by (simp add: rel_def, (erule disjE, (erule exE)+, simp add: parts_insert,
 ((subst (asm) disj_assoc [symmetric])?, erule disjE, (drule parts_dec |
 drule parts_enc | drule parts_sep | drule parts_con), simp+)?)+,
 auto simp add: parts_insert)

proposition idinfo_spied [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    \<langle>n, X\<rangle> \<in> parts (used s) \<longrightarrow>
  \<langle>n, X\<rangle> \<in> spied s"
by (erule rtrancl_induct, subst parts_init, simp add: Range_iff image_def, rule impI,
 rule idinfo_spied_1)


proposition idinfo_dec:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; s' = insert (Spy, X) s \<and> (Spy, Crypt K X) \<in> s \<and>
    (Spy, Key (InvK K)) \<in> s; \<langle>n, Y\<rangle> = X\<rbrakk> \<Longrightarrow>
  \<langle>n, Y\<rangle> \<in> spied s"
by (drule parts_dec [where Y = "\<langle>n, Y\<rangle>"], drule sym, simp, rule idinfo_spied)

proposition idinfo_sep:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; s' = insert (Spy, X) (insert (Spy, Y) s) \<and> (Spy, \<lbrace>X, Y\<rbrace>) \<in> s;
    \<langle>n, Z\<rangle> = X \<or> \<langle>n, Z\<rangle> = Y\<rbrakk> \<Longrightarrow>
  \<langle>n, Z\<rangle> \<in> spied s"
by (drule parts_sep [where Z = "\<langle>n, Z\<rangle>"], erule disjE, (drule sym, simp)+,
 rule idinfo_spied)


lemma idinfo_msg_1:
  assumes A: "s\<^sub>0 \<Turnstile> s"
  shows "\<lbrakk>s \<turnstile> s'; \<langle>n, X\<rangle> \<in> spied s \<longrightarrow> X \<in> spied s; \<langle>n, X\<rangle> \<in> spied s'\<rbrakk> \<Longrightarrow>
    X \<in> spied s'"
by (simp add: rel_def, (erule disjE, (erule exE)+, simp, ((subst (asm) disj_assoc
 [symmetric])?, erule disjE, (drule idinfo_dec [OF A] | drule idinfo_sep [OF A]),
 simp+ | erule disjE, (simp add: image_iff)+, blast?)?)+)

proposition idinfo_msg [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    \<langle>n, X\<rangle> \<in> spied s \<longrightarrow>
  X \<in> spied s"
by (erule rtrancl_induct, simp, blast, rule impI, rule idinfo_msg_1)


proposition parts_agent:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; n \<notin> bad_agent\<rbrakk> \<Longrightarrow> Agent n \<notin> parts (used s)"
  apply (erule rtrancl_induct)
  subgoal
    apply (subst parts_init)
    apply (simp add: Range_iff image_def)
    done
  subgoal
    apply (simp add: rel_def)
    apply ((erule disjE)?, (erule exE)+, simp add: parts_insert image_iff,
 (rule ccontr, (drule parts_dec | drule parts_enc | drule parts_sep |
 drule parts_con), simp+)?)+
    done
  done

lemma idinfo_init_1 [rule_format]:
  assumes A: "s\<^sub>0 \<Turnstile> s"
  shows "\<lbrakk>s \<turnstile> s'; n \<notin> bad_id_password \<union> bad_id_pubkey \<union> bad_id_shakey;
    \<forall>X. \<langle>n, X\<rangle> \<notin> spied s\<rbrakk> \<Longrightarrow>
  \<langle>n, X\<rangle> \<notin> spied s'"
by (rule notI, simp add: rel_def, ((erule disjE)?, (erule exE)+, (blast | simp,
 ((drule idinfo_dec [OF A] | drule idinfo_sep [OF A]), simp, blast |
 (erule conjE)+, drule parts_agent [OF A], blast))?)+)

proposition idinfo_init:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; n \<notin> bad_id_password \<union> bad_id_pubkey \<union> bad_id_shakey\<rbrakk> \<Longrightarrow>
  \<langle>n, X\<rangle> \<notin> spied s"
by (induction arbitrary: X rule: rtrancl_induct, simp add: image_def, blast,
 rule idinfo_init_1)


lemma idinfo_mpair_1 [rule_format]:
 "\<lbrakk>(s, s') \<in> rel_id_hash \<union> rel_id_crypt \<union> rel_id_sep \<union> rel_id_con;
    \<forall>X Y. \<langle>n, \<lbrace>X, Y\<rbrace>\<rangle> \<in> spied s \<longrightarrow>
      key_sets \<lbrace>X, Y\<rbrace> (crypts (Log -` spied s)) \<noteq> {};
    \<langle>n, \<lbrace>X, Y\<rbrace>\<rangle> \<in> spied s'\<rbrakk> \<Longrightarrow>
  key_sets \<lbrace>X, Y\<rbrace> (crypts (Log -` spied s')) \<noteq> {}"
by ((erule disjE)?, clarify?, simp add: image_iff Image_def, (drule subsetD
 [OF key_sets_crypts_hash] | drule key_sets_range, blast | (drule spec)+,
 drule mp, simp, simp add: ex_in_conv [symmetric], erule exE, frule subsetD
 [OF key_sets_crypts_fst], drule subsetD [OF key_sets_crypts_snd])?)+

lemma idinfo_mpair_2 [rule_format]:
  assumes A: "s\<^sub>0 \<Turnstile> s"
  shows "\<lbrakk>s \<turnstile> s'; (s, s') \<notin> rel_id_hash \<union> rel_id_crypt \<union> rel_id_sep \<union> rel_id_con;
    \<forall>X Y. \<langle>n, \<lbrace>X, Y\<rbrace>\<rangle> \<in> spied s \<longrightarrow>
      key_sets \<lbrace>X, Y\<rbrace> (crypts (Log -` spied s)) \<noteq> {};
    \<langle>n, \<lbrace>X, Y\<rbrace>\<rangle> \<in> spied s'\<rbrakk> \<Longrightarrow>
  key_sets \<lbrace>X, Y\<rbrace> (crypts (Log -` spied s')) \<noteq> {}"
by (simp only: rel_def Un_iff de_Morgan_disj, simp, ((erule disjE)?, (erule exE)+,
 simp add: Image_def, (simp only: Collect_disj_eq crypts_union key_sets_union, simp)?,
 ((subst (asm) disj_assoc [symmetric])?, erule disjE, (drule idinfo_dec [OF A] |
 drule idinfo_sep [OF A]), simp+)?)+)

proposition idinfo_mpair [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    \<langle>n, \<lbrace>X, Y\<rbrace>\<rangle> \<in> spied s \<longrightarrow>
  key_sets \<lbrace>X, Y\<rbrace> (crypts (Log -` spied s)) \<noteq> {}"
proof (induction arbitrary: X Y rule: rtrancl_induct, simp add: image_def,
 rule impI)
  fix s s' X Y
  assume
   "s\<^sub>0 \<Turnstile> s" and
   "s \<turnstile> s'" and
   "\<And>X Y. \<langle>n, \<lbrace>X, Y\<rbrace>\<rangle> \<in> spied s \<longrightarrow>
      key_sets \<lbrace>X, Y\<rbrace> (crypts (Log -` spied s)) \<noteq> {}" and
   "\<langle>n, \<lbrace>X, Y\<rbrace>\<rangle> \<in> spied s'"
  thus "key_sets \<lbrace>X, Y\<rbrace> (crypts (Log -` spied s')) \<noteq> {}"
    by (cases "(s, s') \<in> rel_id_hash \<union> rel_id_crypt \<union> rel_id_sep \<union> rel_id_con",
     erule_tac [2] idinfo_mpair_2, erule_tac idinfo_mpair_1, simp_all)
qed


proposition key_sets_pwd_empty:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    key_sets (Hash (Pwd n)) (crypts (Log -` spied s)) = {} \<and>
    key_sets \<lbrace>Pwd n, X\<rbrace> (crypts (Log -` spied s)) = {} \<and>
    key_sets \<lbrace>X, Pwd n\<rbrace> (crypts (Log -` spied s)) = {}"
  (is "_ \<Longrightarrow> key_sets ?X (?H s) = _ \<and> key_sets ?Y _ = _ \<and> key_sets ?Z _ = _")
proof (erule rtrancl_induct, simp add: image_iff Image_def)
  fix s s'
  assume
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "key_sets (Hash (Pwd n)) (?H s) = {} \<and>
      key_sets \<lbrace>Pwd n, X\<rbrace> (?H s) = {} \<and>
      key_sets \<lbrace>X, Pwd n\<rbrace> (?H s) = {}"
  show "key_sets (Hash (Pwd n)) (?H s') = {} \<and>
    key_sets \<lbrace>Pwd n, X\<rbrace> (?H s') = {} \<and>
    key_sets \<lbrace>X, Pwd n\<rbrace> (?H s') = {}"
    by (insert B C, simp add: rel_def, ((erule disjE)?, ((erule exE)+)?, simp add:
     image_iff Image_def, (simp only: Collect_disj_eq crypts_union
     key_sets_union, simp add: crypts_insert key_sets_insert)?,
     (frule log_dec [OF A, where Y = "?X"],
     frule log_dec [OF A, where Y = "?Y"], drule log_dec [OF A, where Y = "?Z"] |
     frule log_sep [OF A, where Z = "?X"], frule log_sep [OF A, where Z = "?Y"],
     drule log_sep [OF A, where Z = "?Z"])?)+)
qed

proposition key_sets_pwd_seskey [rule_format]:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow>
    U \<in> key_sets (Pwd n) (crypts (Log -` spied s)) \<longrightarrow>
  (\<exists>SK. U = {SesKey SK} \<and>
    ((Owner n, Crypt (SesK SK) (Pwd n)) \<in> s \<or>
     (Asset n, Crypt (SesK SK) (Num 0)) \<in> s))"
  (is "_ \<Longrightarrow> _ \<longrightarrow> ?P s")
proof (erule rtrancl_induct, simp add: image_iff Image_def, rule impI)
  fix s s'
  assume
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "U \<in> key_sets (Pwd n) (crypts (Log -` spied s)) \<longrightarrow> ?P s" and
    D: "U \<in> key_sets (Pwd n) (crypts (Log -` spied s'))"
  show "?P s'"
    by (insert B C D, simp add: rel_def, ((erule disjE)?, ((erule exE)+)?, simp
     add: image_iff Image_def, (simp only: Collect_disj_eq crypts_union
     key_sets_union, simp add: crypts_insert key_sets_insert split: if_split_asm,
     blast?)?, (erule disjE, (drule log_dec [OF A] | drule log_sep [OF A]),
     (erule conjE)?, drule subsetD, simp)?)+)
qed


lemma pwd_anonymous_1 [rule_format]:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; n \<notin> bad_id_password\<rbrakk> \<Longrightarrow>
    \<langle>n, Pwd n\<rangle> \<in> spied s \<longrightarrow>
  (\<exists>SK. SesKey SK \<in> spied s \<and>
    ((Owner n, Crypt (SesK SK) (Pwd n)) \<in> s \<or>
     (Asset n, Crypt (SesK SK) (Num 0)) \<in> s))"
  (is "\<lbrakk>_; _\<rbrakk> \<Longrightarrow> _ \<longrightarrow> ?P s")
proof (erule rtrancl_induct, simp add: image_def, rule impI)
  fix s s'
  assume
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "s \<turnstile> s'" and
    C: "\<langle>n, Pwd n\<rangle> \<in> spied s \<longrightarrow> ?P s" and
    D: "\<langle>n, Pwd n\<rangle> \<in> spied s'"
  show "?P s'"
    by (insert B C D, simp add: rel_def, ((erule disjE)?, (erule exE)+, simp add:
     image_iff, blast?, ((subst (asm) disj_assoc [symmetric])?, erule disjE,
     (drule idinfo_dec [OF A] | drule idinfo_sep [OF A]), simp, blast+ |
     insert key_sets_pwd_empty [OF A], clarsimp)?, (((erule disjE)?, erule
     conjE, drule sym, simp, (drule key_sets_pwd_seskey [OF A] | drule
     idinfo_mpair [OF A, simplified]), simp)+ | drule key_sets_range, blast)?)+)
qed

theorem pwd_anonymous:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_id_password" and
    C: "n \<notin> bad_shakey \<inter> (bad_pwd \<union> bad_prikey) \<inter> (bad_id_pubkey \<union> bad_id_shak)"
  shows "\<langle>n, Pwd n\<rangle> \<notin> spied s"
proof
  assume D: "\<langle>n, Pwd n\<rangle> \<in> spied s"
  hence "n \<in> bad_id_password \<union> bad_id_pubkey \<union> bad_id_shakey"
    by (rule contrapos_pp, rule_tac idinfo_init [OF A])
  moreover have "\<exists>SK. SesKey SK \<in> spied s \<and>
    ((Owner n, Crypt (SesK SK) (Pwd n)) \<in> s \<or>
     (Asset n, Crypt (SesK SK) (Num 0)) \<in> s)"
    (is "\<exists>SK. ?P SK \<and> (?Q SK \<or> ?R SK)")
    by (rule pwd_anonymous_1 [OF A B D])
  then obtain SK where "?P SK" and "?Q SK \<or> ?R SK" by blast
  moreover {
    assume "?Q SK"
    hence "n \<in> bad_shakey \<inter> bad_prikey"
      by (rule_tac contrapos_pp [OF \<open>?P SK\<close>], rule_tac owner_seskey_secret [OF A])
  }
  moreover {
    assume "?R SK"
    hence "n \<in> bad_shakey \<inter> (bad_pwd \<union> bad_prikey)"
      by (rule_tac contrapos_pp [OF \<open>?P SK\<close>], rule_tac asset_seskey_secret [OF A])
  }
  ultimately show False
    using B and C by blast
qed


proposition idinfo_pwd_start:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_agent"
  shows "\<lbrakk>s \<turnstile> s'; \<exists>X. \<langle>n, X\<rangle> \<in> spied s' \<and> X \<noteq> Pwd n;
    \<not> (\<exists>X. \<langle>n, X\<rangle> \<in> spied s \<and> X \<noteq> Pwd n)\<rbrakk> \<Longrightarrow>
      \<exists>SK. SesKey SK \<in> spied s \<and>
        ((Owner n, Crypt (SesK SK) (Pwd n)) \<in> s \<or>
         (Asset n, Crypt (SesK SK) (Num 0)) \<in> s)"
proof (simp add: rel_def, insert parts_agent [OF A B], insert key_sets_pwd_empty
 [OF A], (erule disjE, (erule exE)+, simp, erule conjE, (subst (asm) disj_assoc
 [symmetric])?, (erule disjE)?, (drule idinfo_dec [OF A] | drule idinfo_sep
 [OF A] | drule spec, drule mp), simp+)+, auto, rule FalseE, rule_tac [3] FalseE)
  fix X U K
  assume "\<forall>X. (Spy, \<langle>n, X\<rangle>) \<in> s \<longrightarrow> X = Pwd n" and "(Spy, \<langle>n, K\<rangle>) \<in> s"
  hence "K = Pwd n" by simp
  moreover assume "U \<in> key_sets X (crypts (Log -` spied s))"
  hence "U \<subseteq> range Key"
    by (rule key_sets_range)
  moreover assume "K \<in> U"
  ultimately show False by blast
next
  fix X U
  assume "\<forall>X. (Spy, \<langle>n, X\<rangle>) \<in> s \<longrightarrow> X = Pwd n" and "(Spy, \<langle>n, X\<rangle>) \<in> s"
  hence C: "X = Pwd n" by simp
  moreover assume "U \<in> key_sets X (crypts (Log -` spied s))"
  ultimately have "U \<in> key_sets (Pwd n) (crypts (Log -` spied s))" by simp
  hence "\<exists>SK. U = {SesKey SK} \<and>
    ((Owner n, Crypt (SesK SK) (Pwd n)) \<in> s \<or>
     (Asset n, Crypt (SesK SK) (Num 0)) \<in> s)"
    by (rule key_sets_pwd_seskey [OF A])
  moreover assume "U \<subseteq> spied s"
  ultimately show "\<exists>x U V. (Spy, Key (SesK (x, U, V))) \<in> s \<and>
    ((Owner n, Crypt (SesK (x, U, V)) X) \<in> s \<or>
     (Asset n, Crypt (SesK (x, U, V)) (Num 0)) \<in> s)"
    using C by auto
next
  fix X U K
  assume "\<forall>X. (Spy, \<langle>n, X\<rangle>) \<in> s \<longrightarrow> X = Pwd n" and "(Spy, \<langle>n, K\<rangle>) \<in> s"
  hence "K = Pwd n" by simp
  moreover assume "U \<in> key_sets X (crypts (Log -` spied s))"
  hence "U \<subseteq> range Key"
    by (rule key_sets_range)
  moreover assume "K \<in> U"
  ultimately show False by blast
qed

proposition idinfo_pwd:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; \<exists>X. \<langle>n, X\<rangle> \<in> spied s \<and> X \<noteq> Pwd n;
    n \<notin> bad_id_pubkey \<union> bad_id_shakey\<rbrakk> \<Longrightarrow>
  \<exists>SK. SesKey SK \<in> spied s \<and>
    ((Owner n, Crypt (SesK SK) (Pwd n)) \<in> s \<or>
     (Asset n, Crypt (SesK SK) (Num 0)) \<in> s)"
by (drule rtrancl_start, assumption, simp, blast, (erule exE)+, (erule conjE)+,
 frule idinfo_pwd_start [of _ n], simp+, drule r_into_rtrancl, drule rtrancl_trans,
 assumption, (drule state_subset)+, blast)


theorem auth_prikey_anonymous:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_id_prikey" and
    C: "n \<notin> bad_shakey \<inter> bad_prikey \<inter> (bad_id_password \<union> bad_id_shak)"
  shows "\<langle>n, Auth_PriKey n\<rangle> \<notin> spied s"
proof
  assume D: "\<langle>n, Auth_PriKey n\<rangle> \<in> spied s"
  hence "n \<in> bad_id_password \<union> bad_id_pubkey \<union> bad_id_shakey"
    by (rule contrapos_pp, rule_tac idinfo_init [OF A])
  moreover have "Auth_PriKey n \<in> spied s"
    by (rule idinfo_msg [OF A D])
  hence "n \<in> bad_prikey"
    by (rule contrapos_pp, rule_tac auth_prikey_secret [OF A])
  moreover from this have E: "n \<notin> bad_id_pubkey"
    using B by simp
  moreover have "n \<in> bad_shakey"
  proof (cases "n \<in> bad_id_shakey", simp)
    case False
    with D and E have "\<exists>SK. SesKey SK \<in> spied s \<and>
      ((Owner n, Crypt (SesK SK) (Pwd n)) \<in> s \<or>
       (Asset n, Crypt (SesK SK) (Num 0)) \<in> s)"
      (is "\<exists>SK. ?P SK \<and> (?Q SK \<or> ?R SK)")
      by (rule_tac idinfo_pwd [OF A], rule_tac exI [of _ "Auth_PriKey n"], simp_all)
    then obtain SK where "?P SK" and "?Q SK \<or> ?R SK" by blast
    moreover {
      assume "?Q SK"
      hence "n \<in> bad_shakey \<inter> bad_prikey"
        by (rule_tac contrapos_pp [OF \<open>?P SK\<close>], rule_tac owner_seskey_secret
         [OF A])
    }
    moreover {
      assume "?R SK"
      hence "n \<in> bad_shakey \<inter> (bad_pwd \<union> bad_prikey)"
        by (rule_tac contrapos_pp [OF \<open>?P SK\<close>], rule_tac asset_seskey_secret
         [OF A])
    }
    ultimately show ?thesis by blast
  qed
  ultimately show False
    using C by blast
qed


theorem auth_shakey_anonymous:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "n \<notin> bad_id_shakey" and
    C: "n \<notin> bad_shakey \<inter> (bad_id_password \<union> bad_id_pubkey)"
  shows "\<langle>n, Key (Auth_ShaKey n)\<rangle> \<notin> spied s"
proof
  assume D: "\<langle>n, Key (Auth_ShaKey n)\<rangle> \<in> spied s"
  hence "n \<in> bad_id_password \<union> bad_id_pubkey \<union> bad_id_shakey"
    by (rule contrapos_pp, rule_tac idinfo_init [OF A])
  moreover have "Key (Auth_ShaKey n) \<in> spied s"
    by (rule idinfo_msg [OF A D])
  hence "n \<in> bad_shakey"
    by (rule contrapos_pp, rule_tac auth_shakey_secret [OF A])
  ultimately show False
    using B and C by blast
qed


end