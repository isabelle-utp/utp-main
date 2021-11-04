(*  Title:       Logging-independent Message Anonymity in the Relational Method
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Anonymity of token pseudonymous identifiers"

theory Anonymity
  imports Definitions
begin

text \<open>
\null

This section contains a proof of anonymity property @{text id_anonymous}, which states that a token
pseudonymous identifier remains anonymous if its anonymity is not compromised by means other than
attacking the protocol and neither attack option described in section \ref{Protocol} is viable. As
shown here below, this property can be proven by applying rules @{thm [source] rtrancl_induct} and
@{text rtrancl_start} in a suitable combination @{cite "Noce20"}.

\null
\<close>

proposition rtrancl_start [rule_format]:
 "(x, y) \<in> r\<^sup>* \<Longrightarrow> P y \<longrightarrow> \<not> P x \<longrightarrow>
    (\<exists>u v. (x, u) \<in> r\<^sup>* \<and> (u, v) \<in> r \<and> (v, y) \<in> r\<^sup>* \<and> \<not> P u \<and> P v)"
  (is "_ \<Longrightarrow> _ \<longrightarrow> _ \<longrightarrow> (\<exists>u v. ?P\<^sub>2 x y u v)")
proof (erule rtrancl_induct, simp, (rule impI)+)
  fix y z
  assume
    A: "(x, y) \<in> r\<^sup>*" and
    B: "(y, z) \<in> r" and
    C: "P z"
  assume "P y \<longrightarrow> \<not> P x \<longrightarrow>(\<exists>u v. ?P\<^sub>2 x y u v)" and "\<not> P x"
  hence D: "P y \<longrightarrow> (\<exists>u v. ?P\<^sub>2 x y u v)" by simp
  show "\<exists>u v. ?P\<^sub>2 x z u v"
  proof (cases "P y")
    case True
    with D obtain u v where "?P\<^sub>2 x y u v" by blast
    moreover from this and B have "(v, z) \<in> r\<^sup>*" by auto
    ultimately show ?thesis by blast
  next
    case False
    with A and B and C have "?P\<^sub>2 x z y z" by simp
    thus ?thesis by blast
  qed
qed

proposition state_subset:
 "s \<Turnstile> s' \<Longrightarrow> s \<subseteq> s'"
by (erule rtrancl_induct, auto simp add: rel_def image_def)

proposition spied_subset:
 "s \<Turnstile> s' \<Longrightarrow> spied s \<subseteq> spied s'"
by (rule Image_mono, erule state_subset, simp)


proposition parts_init:
 "parts (used s\<^sub>0) = used s\<^sub>0"
by (rule equalityI, rule_tac [!] subsetI, erule_tac [2] parts_used,
 erule parts.induct, auto)

proposition parts_idem [simp]:
 "parts (parts H) = parts H"
by (rule equalityI, rule subsetI, erule parts.induct, auto)

proposition parts_mono:
 "H \<subseteq> H' \<Longrightarrow> parts H \<subseteq> parts H'"
by (rule subsetI, erule parts.induct, auto)

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


proposition parts_msg_mono:
 "X \<in> H \<Longrightarrow> parts_msg X \<subseteq> parts H"
by (subgoal_tac "{X} \<subseteq> H", subst parts_msg_def, erule parts_mono, simp)

proposition parts_msg_agrkey [simp]:
 "parts_msg (AgrKey K) = {AgrKey K}"
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

proposition parts_msg_parts:
 "\<lbrakk>(A, X) \<in> s; Y \<in> parts_msg X\<rbrakk> \<Longrightarrow> Y \<in> parts (used s)"
by (subgoal_tac "X \<in> parts (used s)", drule parts_msg_mono [of X], auto)


proposition prikey_spied:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; PriKey K \<in> parts (used s)\<rbrakk> \<Longrightarrow> PriKey K \<in> spied s"
by (induction rule: rtrancl_induct, subst (asm) parts_init,
 auto simp: rel_def parts_insert dest!: parts_msg_parts)

proposition prikey_crypt [simplified]:
 "\<lbrakk>(Spy, Crypt K (PriKey K')) \<in> s; s\<^sub>0 \<Turnstile> s\<rbrakk> \<Longrightarrow> PriKey K' \<in> spied s"
by (erule prikey_spied, blast)

proposition prikey_mpair_fst [simplified]:
 "\<lbrakk>(Spy, \<lbrace>PriKey K, Y\<rbrace>) \<in> s; s\<^sub>0 \<Turnstile> s\<rbrakk> \<Longrightarrow> PriKey K \<in> spied s"
by (erule prikey_spied, blast)

proposition prikey_mpair_snd [simplified]:
 "\<lbrakk>(Spy, \<lbrace>Y, PriKey K\<rbrace>) \<in> s; s\<^sub>0 \<Turnstile> s\<rbrakk> \<Longrightarrow> PriKey K \<in> spied s"
by (erule prikey_spied, blast)

proposition rev_prikey_secret:
 "s\<^sub>0 \<Turnstile> s \<Longrightarrow> Rev_PriKey \<notin> spied s"
by (induction rule: rtrancl_induct, insert sec_prik_rev tok_prik_rev,
 auto simp: rel_def dest: prikey_crypt prikey_mpair_fst prikey_mpair_snd)

proposition sec_prikey_secret:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; n \<notin> bad_sec_prik\<rbrakk> \<Longrightarrow> Sec_PriKey n \<notin> spied s"
by (induction rule: rtrancl_induct, insert sec_prik_inj sec_prik_tok_prik, auto simp:
 rel_def inj_on_def image_def dest: prikey_crypt prikey_mpair_fst prikey_mpair_snd)

proposition tok_prikey_secret:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; n \<notin> bad_tok_prik\<rbrakk> \<Longrightarrow> Tok_PriKey n \<notin> spied s"
by (induction rule: rtrancl_induct, insert tok_prik_inj sec_prik_tok_prik, auto simp:
 rel_def inj_on_def image_def dest: prikey_crypt prikey_mpair_fst prikey_mpair_snd)


proposition idinfo_spied:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; \<langle>n, X\<rangle> \<in> parts (used s)\<rbrakk> \<Longrightarrow> \<langle>n, X\<rangle> \<in> spied s"
by (induction rule: rtrancl_induct, subst (asm) parts_init,
 auto simp: rel_def parts_insert dest!: parts_msg_parts)

proposition idinfo_crypt:
 "\<lbrakk>(Spy, Crypt K \<langle>n, X\<rangle>) \<in> s; s\<^sub>0 \<Turnstile> s\<rbrakk> \<Longrightarrow> \<langle>n, X\<rangle> \<in> spied s"
by (erule idinfo_spied, blast)

proposition idinfo_mpair_fst:
 "\<lbrakk>(Spy, \<lbrace>\<langle>n, X\<rangle>, Y\<rbrace>) \<in> s; s\<^sub>0 \<Turnstile> s\<rbrakk> \<Longrightarrow> \<langle>n, X\<rangle> \<in> spied s"
by (erule idinfo_spied, blast)

proposition idinfo_mpair_snd:
 "\<lbrakk>(Spy, \<lbrace>Y, \<langle>n, X\<rangle>\<rbrace>) \<in> s; s\<^sub>0 \<Turnstile> s\<rbrakk> \<Longrightarrow> \<langle>n, X\<rangle> \<in> spied s"
by (erule idinfo_spied, blast)

proposition idinfo_hash_hash [rotated]:
 "\<lbrakk>s\<^sub>0 \<Turnstile> s; (Spy, \<langle>n, Hash (Hash X)\<rangle>) \<in> s\<rbrakk> \<Longrightarrow> \<langle>n, Hash X\<rangle> \<in> spied s"
by (induction arbitrary: X rule: rtrancl_induct, auto simp: rel_def
 dest: idinfo_crypt idinfo_mpair_fst idinfo_mpair_snd)


proposition sec_prik_eq:
 "{Tok_PriK n, Sec_PriK m, Rev_PriK} =
    {Tok_PriK n, Sec_PriK m', Rev_PriK} \<Longrightarrow> m' = m"
by (erule equalityE, drule subsetD [where c = "Sec_PriK m"], simp, insert
 sec_prik_inj sec_prik_rev sec_prik_tok_prik, auto simp: inj_on_def image_def)

proposition id_identified:
  assumes
    A: "s\<^sub>0 \<Turnstile> s" and
    B: "(n, m) \<notin> bad_id" and
    C: "n \<notin> bad_tok_prik" and
    D: "\<langle>n, Hash (ID n (Sec_PubKey m))\<rangle> \<in> spied s"
  shows "m \<in> bad_sec_prik \<and>
    (\<exists>m'. m' \<noteq> m \<and> m' \<in> bad_sec_prik \<and> (n, m') \<in> bad_id)"
proof -
  let ?P\<^sub>1 = "\<lambda>s. \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle> \<in> spied s"
  let ?P\<^sub>2 = "\<lambda>s. \<exists>S. \<langle>n, PubKey S\<rangle> \<in> spied s \<and> Sec_PriK m \<in> S"
  let ?P\<^sub>3 = "\<lambda>S s. \<langle>n, Hash (PubKey S)\<rangle> \<in> spied s"
  let ?P\<^sub>4 = "\<lambda>S s. \<langle>n, PubKey S\<rangle> \<in> spied s \<and> Rev_PriK \<in> S \<and>
    (\<forall>m. Sec_PriK m \<in> S \<longrightarrow> (n, m) \<notin> bad_id)"
  have E: "\<forall>m. Sec_PriK m \<noteq> Rev_PriK"
    by (rule allI, rule notI, subgoal_tac "Rev_PriK \<in> range Sec_PriK",
     simp add: sec_prik_rev, rule range_eqI, rule sym)
  have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> s \<and> \<not> ?P\<^sub>1 u \<and> ?P\<^sub>1 v"
    using A and B and D by (rule_tac rtrancl_start, auto dest: sec_prik_eq)
  then obtain u\<^sub>1 v\<^sub>1 where F: "s\<^sub>0 \<Turnstile> u\<^sub>1 \<and> u\<^sub>1 \<turnstile> v\<^sub>1 \<and> \<not> ?P\<^sub>1 u\<^sub>1 \<and> ?P\<^sub>1 v\<^sub>1"
    by blast
  moreover from this have G: "\<langle>n, ID n (Sec_PubKey m)\<rangle> \<in> spied u\<^sub>1"
    by (auto simp: rel_def dest: idinfo_crypt idinfo_mpair_fst idinfo_mpair_snd
     idinfo_hash_hash)
  ultimately have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> u\<^sub>1 \<and> \<not> ?P\<^sub>2 u \<and> ?P\<^sub>2 v"
    using B and E by (rule_tac rtrancl_start, insert
     sec_prik_inj sec_prik_tok_prik, auto simp: inj_on_def image_def)
  then obtain u\<^sub>2 v\<^sub>2 where H: "s\<^sub>0 \<Turnstile> u\<^sub>2 \<and> u\<^sub>2 \<turnstile> v\<^sub>2 \<and> \<not> ?P\<^sub>2 u\<^sub>2 \<and> ?P\<^sub>2 v\<^sub>2"
    by blast
  moreover from this have "Tok_PriKey n \<notin> spied u\<^sub>2"
    using C by (rule_tac tok_prikey_secret, simp)
  ultimately have "Sec_PriKey m \<in> spied u\<^sub>2"
  proof (auto simp: rel_def dest: idinfo_crypt idinfo_mpair_fst idinfo_mpair_snd)
    fix S
    assume "(Spy, \<langle>n, Hash (AgrKey (PubK S))\<rangle>) \<in> u\<^sub>2"
    moreover assume I: "Sec_PriK m \<in> S"
    hence "\<langle>n, Hash (PubKey S)\<rangle> \<notin> spied s\<^sub>0"
      using B and E by (insert sec_prik_inj sec_prik_tok_prik,
       auto simp: inj_on_def image_def)
    ultimately have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> u\<^sub>2 \<and> \<not> ?P\<^sub>3 S u \<and> ?P\<^sub>3 S v"
      using H by (rule_tac rtrancl_start, simp_all)
    then obtain u\<^sub>3 v\<^sub>3 where "s\<^sub>0 \<Turnstile> u\<^sub>3 \<and> u\<^sub>3 \<turnstile> v\<^sub>3 \<and> v\<^sub>3 \<Turnstile> u\<^sub>2 \<and>
      \<not> ?P\<^sub>3 S u\<^sub>3 \<and> ?P\<^sub>3 S v\<^sub>3"
      by blast
    moreover from this have "\<langle>n, PubKey S\<rangle> \<in> spied v\<^sub>3"
      by (auto simp: rel_def dest: idinfo_crypt idinfo_mpair_fst idinfo_mpair_snd
       idinfo_hash_hash)
    ultimately have "\<langle>n, PubKey S\<rangle> \<in> spied u\<^sub>2"
      by (rule_tac subsetD [of "spied v\<^sub>3"], rule_tac spied_subset, simp)
    hence "Sec_PriK m \<notin> S"
      using H by simp
    thus "(Spy, AgrKey (PriK (Sec_PriK m))) \<in> u\<^sub>2"
      using I by contradiction
  qed
  hence I: "m \<in> bad_sec_prik"
    using H by (erule_tac contrapos_pp, rule_tac sec_prikey_secret, simp)
  from B and E and G have "\<exists>S. ?P\<^sub>4 S u\<^sub>1"
    by (rule_tac exI [of _ "{Tok_PriK n, Sec_PriK m, Rev_PriK}"],
     insert sec_prik_inj sec_prik_tok_prik, auto simp: inj_on_def image_def)
  moreover have "\<not> (\<exists>S. ?P\<^sub>4 S s\<^sub>0)"
    by (insert tok_prik_rev, auto)
  ultimately have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> u\<^sub>1 \<and>
    \<not> (\<exists>S. ?P\<^sub>4 S u) \<and> (\<exists>S. ?P\<^sub>4 S v)"
    using F by (rule_tac rtrancl_start, simp)
  then obtain u\<^sub>4 v\<^sub>4 S where
    J: "s\<^sub>0 \<Turnstile> u\<^sub>4" and K: "u\<^sub>4 \<turnstile> v\<^sub>4" and L: "\<not> (\<exists>S. ?P\<^sub>4 S u\<^sub>4) \<and> ?P\<^sub>4 S v\<^sub>4"
    by blast
  have M: "\<lbrakk>(Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4; Rev_PriK \<in> S;
    \<forall>m. Sec_PriK m \<in> S \<longrightarrow> (n, m) \<notin> bad_id;
    \<forall>S. Rev_PriK \<in> S \<longrightarrow> (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4 \<longrightarrow>
      (\<exists>m. Sec_PriK m \<in> S \<and> (n, m) \<in> bad_id)\<rbrakk> \<Longrightarrow> False"
    by blast
  from K and L have "\<exists>m'. m' \<noteq> m \<and> m' \<in> bad_sec_prik \<and> (n, m') \<in> bad_id"
  proof (simp add: rel_def, (erule_tac disjE, (clarsimp, (erule_tac disjE,
   drule_tac sym, simp, (drule_tac idinfo_crypt [OF _ J] | drule_tac
   idinfo_mpair_fst [OF _ J] | drule_tac idinfo_mpair_snd [OF _ J]), blast)+)?,
   blast)+, (erule_tac disjE, erule_tac [2] disjE, erule_tac [3] disjE; clarsimp))
    fix n' S' A
    assume
      N: "\<forall>S. Rev_PriK \<in> S \<longrightarrow> (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4 \<longrightarrow>
        (\<exists>m. Sec_PriK m \<in> S \<and> (n, m) \<in> bad_id)" and
      O: "\<forall>m. Sec_PriK m \<in> S \<longrightarrow> (n, m) \<notin> bad_id" and
      P: "Rev_PriK \<in> S" and
      Q: "(Spy, \<langle>n', AgrKey (PubK S')\<rangle>) \<in> u\<^sub>4" and
      R: "(Spy, AgrKey (PriK A)) \<in> u\<^sub>4"
    assume "n = n' \<and> S = S' - {A} \<or> (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4"
    thus ?thesis
    proof (rule disjE, drule_tac [2] M [OF _ P O N]; clarsimp)
      assume S: "n = n'" and "S = S' - {A}"
      moreover from this obtain m' where
       "Sec_PriK m' \<in> S'" and T: "(n, m') \<in> bad_id"
        using N and P and Q by blast
      ultimately have "A = Sec_PriK m'"
        using O by (rule_tac ccontr, simp)
      hence "Sec_PriKey m' \<in> spied u\<^sub>4"
        using R by simp
      hence "m' \<in> bad_sec_prik"
        by (rule contrapos_pp, rule_tac sec_prikey_secret [OF J])
      thus "\<exists>m'. m' \<noteq> m \<and> m' \<in> bad_sec_prik \<and> (n', m') \<in> bad_id"
        using B and S and T by auto
    qed
  next
    fix n' S' A
    assume
      N: "\<forall>S. Rev_PriK \<in> S \<longrightarrow> (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4 \<longrightarrow>
        (\<exists>m. Sec_PriK m \<in> S \<and> (n, m) \<in> bad_id)" and
      O: "\<forall>m. Sec_PriK m \<in> S \<longrightarrow> (n, m) \<notin> bad_id" and
      P: "Rev_PriK \<in> S" and
      Q: "(Spy, \<langle>n', AgrKey (PubK S')\<rangle>) \<in> u\<^sub>4" and
      R: "(Spy, AgrKey (PriK A)) \<in> u\<^sub>4"
    assume "n = n' \<and> S = insert A S' \<or> (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4"
    thus ?thesis
    proof (rule disjE, drule_tac [2] M [OF _ P O N]; clarsimp)
      assume "n = n'" and S: "S = insert A S'"
      moreover have "A \<noteq> Rev_PriK"
        using R by (rule contrapos_pn, insert rev_prikey_secret [OF J], simp)
      ultimately obtain m' where "Sec_PriK m' \<in> S'" and T: "(n, m') \<in> bad_id"
        using N and P and Q by blast
      hence "(n, m') \<notin> bad_id"
        using O and S by simp
      thus "\<exists>m'. m' \<noteq> m \<and> m' \<in> bad_sec_prik \<and> (n', m') \<in> bad_id"
        using T by contradiction
    qed
  next
    fix n' S'
    assume
      N: "\<forall>S. Rev_PriK \<in> S \<longrightarrow> (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4 \<longrightarrow>
        (\<exists>m. Sec_PriK m \<in> S \<and> (n, m) \<in> bad_id)" and
      O: "\<forall>m. Sec_PriK m \<in> S \<longrightarrow> (n, m) \<notin> bad_id" and
      P: "Rev_PriK \<in> S"
    assume "n = n' \<and> S = S' \<or> (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4" and
      "(Spy, AgrKey (PriK (Tok_PriK n'))) \<in> u\<^sub>4"
    thus ?thesis
      by (erule_tac disjE, drule_tac [2] M [OF _ P O N],
       insert tok_prikey_secret [OF J C], simp_all)
  next
    fix n' X
    assume
      N: "\<forall>S. Rev_PriK \<in> S \<longrightarrow> (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4 \<longrightarrow>
        (\<exists>m. Sec_PriK m \<in> S \<and> (n, m) \<in> bad_id)" and
      O: "\<forall>m. Sec_PriK m \<in> S \<longrightarrow> (n, m) \<notin> bad_id" and
      P: "Rev_PriK \<in> S" and
      Q: "(Spy, \<langle>n', X\<rangle>) \<in> u\<^sub>4 \<or> (Spy, \<langle>n', Hash X\<rangle>) \<in> u\<^sub>4"
    assume "n = n' \<and> AgrKey (PubK S) = X \<or>
      (Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4"
    thus ?thesis
    proof (rule disjE, drule_tac [2] M [OF _ P O N]; clarsimp)
      assume R: "n = n'" and S: "X = AgrKey (PubK S)"
      {
        assume "(Spy, \<langle>n', X\<rangle>) \<in> u\<^sub>4"
        hence "(Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4"
          using R and S by simp
      }
      moreover {
        assume "(Spy, \<langle>n', Hash X\<rangle>) \<in> u\<^sub>4"
        hence "?P\<^sub>3 S u\<^sub>4"
          using R and S by simp
        moreover have "\<not> ?P\<^sub>3 S s\<^sub>0"
          using O by auto
        ultimately have "\<exists>u v. s\<^sub>0 \<Turnstile> u \<and> u \<turnstile> v \<and> v \<Turnstile> u\<^sub>4 \<and> \<not> ?P\<^sub>3 S u \<and> ?P\<^sub>3 S v"
          using J by (rule_tac rtrancl_start)
        then obtain u\<^sub>3 v\<^sub>3 where "s\<^sub>0 \<Turnstile> u\<^sub>3 \<and> u\<^sub>3 \<turnstile> v\<^sub>3 \<and> v\<^sub>3 \<Turnstile> u\<^sub>4 \<and>
          \<not> ?P\<^sub>3 S u\<^sub>3 \<and> ?P\<^sub>3 S v\<^sub>3"
          by blast
        moreover from this have "\<langle>n, AgrKey (PubK S)\<rangle> \<in> spied v\<^sub>3"
          by (auto simp: rel_def dest: idinfo_crypt idinfo_mpair_fst idinfo_mpair_snd
           idinfo_hash_hash)
        ultimately have "\<langle>n, AgrKey (PubK S)\<rangle> \<in> spied u\<^sub>4"
          by (rule_tac subsetD [of "spied v\<^sub>3"], rule_tac spied_subset, simp)
      }
      ultimately have "(Spy, \<langle>n, AgrKey (PubK S)\<rangle>) \<in> u\<^sub>4"
        using Q by blast
      thus "\<exists>m'. m' \<noteq> m \<and> m' \<in> bad_sec_prik \<and> (n', m') \<in> bad_id"
        by (drule_tac M [OF _ P O N], simp)
    qed
  qed
  thus ?thesis
    using I by simp
qed


theorem id_anonymous [rotated]:
 "\<lbrakk>m \<notin> bad_sec_prik \<or> \<not> (\<exists>m'. m' \<noteq> m \<and> m' \<in> bad_sec_prik \<and> (n, m') \<in> bad_id);
    s\<^sub>0 \<Turnstile> s; (n, m) \<notin> bad_id; n \<notin> bad_tok_prik\<rbrakk> \<Longrightarrow>
  \<langle>n, Hash (ID n (Sec_PubKey m))\<rangle> \<notin> spied s"
by (erule contrapos_pn, drule id_identified, blast+)

end
