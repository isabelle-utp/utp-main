section \<open>Example\<close>

text \<open>We provide an example in order to prove that our locale is non-vacuous.
This example corresponds to the computation and associated snapshot described
in Section 4 of~\cite{chandy}.\<close>

theory Example
  imports
    Snapshot

begin

datatype PType = P | Q
datatype MType = M | M'
datatype SType = S_Wait | S_Send | T_Wait | T_Send

fun trans :: "PType \<Rightarrow> SType \<Rightarrow> SType \<Rightarrow> bool" where
  "trans p s s' = False"

fun send :: "channel_id \<Rightarrow> PType \<Rightarrow> PType \<Rightarrow> SType
             \<Rightarrow> SType \<Rightarrow> MType \<Rightarrow> bool" where
  "send c p q s s' m = ((c = 0 \<and> p = P \<and> q = Q
                          \<and> s = S_Send \<and> s' = S_Wait \<and> m = M)
                     \<or> (c = 1 \<and> p = Q \<and> q = P
                          \<and> s = T_Send \<and> s' = T_Wait \<and> m = M'))"

fun recv :: "channel_id \<Rightarrow> PType \<Rightarrow> PType \<Rightarrow> SType
             \<Rightarrow> SType \<Rightarrow> MType \<Rightarrow> bool" where
  "recv c p q s s' m = ((c = 1 \<and> p = P \<and> q = Q
                          \<and> s = S_Wait \<and> s' = S_Send \<and> m = M')
                     \<or> (c = 0 \<and> p = Q \<and> q = P
                          \<and> s = T_Wait \<and> s' = T_Send \<and> m = M))"

fun chan :: "nat \<Rightarrow> (PType * PType) option" where
 "chan n = (if n = 0 then Some (P, Q)
            else if n = 1 then Some (Q, P)
            else None)"

abbreviation init :: "(PType, SType, MType) configuration" where
  "init \<equiv> \<lparr>
       states = (%p. if p = P then S_Send else T_Send),
       msgs = (%d. []),
       process_snapshot = (%p. None),
       channel_snapshot = (%d. ([], NotStarted))
    \<rparr>"

abbreviation t0 where "t0 \<equiv> Snapshot P"

abbreviation s1 :: "(PType, SType, MType) configuration" where
  "s1 \<equiv> \<lparr>
       states = (%p. if p = P then S_Send else T_Send),
       msgs = (%d. if d = 0 then [Marker] else []),
       process_snapshot = (%p. if p = P then Some S_Send else None),
       channel_snapshot = (%d. if d = 1 then ([], Recording) else ([], NotStarted))
    \<rparr>"

abbreviation t1 where "t1 \<equiv> Send 0 P Q S_Send S_Wait M"

abbreviation s2 :: "(PType, SType, MType) configuration" where
  "s2 \<equiv> \<lparr>
       states = (%p. if p = P then S_Wait else T_Send),
       msgs = (%d. if d = 0 then [Marker, Msg M] else []),
       process_snapshot = (%p. if p = P then Some S_Send else None),
       channel_snapshot = (%d. if d = 1 then ([], Recording) else ([], NotStarted))
    \<rparr>"

abbreviation t2 where "t2 \<equiv> Send 1 Q P T_Send T_Wait M'"

abbreviation s3 :: "(PType, SType, MType) configuration" where
  "s3 \<equiv> \<lparr>
       states = (%p. if p = P then S_Wait else T_Wait),
       msgs = (%d. if d = 0 then [Marker, Msg M] else if d = 1 then [Msg M'] else []),
       process_snapshot = (%p. if p = P then Some S_Send else None),
       channel_snapshot = (%d. if d = 1 then ([], Recording) else ([], NotStarted))
    \<rparr>"

abbreviation t3 where "t3 \<equiv> Snapshot Q"

abbreviation s4 :: "(PType, SType, MType) configuration" where
  "s4 \<equiv> \<lparr>
       states = (%p. if p = P then S_Wait else T_Wait),
       msgs = (%d. if d = 0 then [Marker, Msg M] else if d = 1 then [Msg M', Marker] else []),
       process_snapshot = (%p. if p = P then Some S_Send else Some T_Wait),
       channel_snapshot = (%d. if d = 1 then ([], Recording) else if d = 0 then ([], Recording) else ([], NotStarted))
    \<rparr>"

abbreviation t4 where "t4 \<equiv> RecvMarker 0 Q P"

abbreviation s5 :: "(PType, SType, MType) configuration" where
  "s5 \<equiv> \<lparr>
       states = (%p. if p = P then S_Wait else T_Wait),
       msgs = (%d. if d = 0 then [Msg M] else if d = 1 then [Msg M', Marker] else []),
       process_snapshot = (%p. if p = P then Some S_Send else Some T_Wait),
       channel_snapshot = (%d. if d = 0 then ([], Done) else if d = 1 then ([], Recording) else ([], NotStarted))
    \<rparr>"

abbreviation t5 where "t5 \<equiv> Recv 1 P Q S_Wait S_Send M'"

abbreviation s6 :: "(PType, SType, MType) configuration" where
  "s6 \<equiv> \<lparr>
       states = (%p. if p = P then S_Send else T_Wait),
       msgs = (%d. if d = 0 then [Msg M] else if d = 1 then [Marker] else []),
       process_snapshot = (%p. if p = P then Some S_Send else Some T_Wait),
       channel_snapshot = (%d. if d = 0 then ([], Done) else if d = 1 then ([M'], Recording) else ([], NotStarted))
    \<rparr>"

abbreviation t6 where "t6 \<equiv> RecvMarker 1 P Q"

abbreviation s7 :: "(PType, SType, MType) configuration" where
  "s7 \<equiv> \<lparr>
       states = (%p. if p = P then S_Send else T_Wait),
       msgs = (%d. if d = 0 then [Msg M] else if d = 1 then [] else []),
       process_snapshot = (%p. if p = P then Some S_Send else Some T_Wait),
       channel_snapshot = (%d. if d = 0 then ([], Done) else if d = 1 then ([M'], Done) else ([], NotStarted))
    \<rparr>"

lemma s7_no_marker:
  shows
    "\<forall>cid. Marker \<notin> set (msgs s7 cid)"
  by simp

interpretation computation chan trans send recv init s7
proof
  have "distributed_system chan"
  proof
    show "\<forall>i. \<nexists>p. chan i = Some (p, p)" by simp
  qed
  show "\<forall>p q. p \<noteq> q \<longrightarrow> (\<lambda>p q. \<exists>i. chan i = Some (p, q))\<^sup>+\<^sup>+ p q"
  proof ((rule allI)+, rule impI)
    fix p q :: PType assume "p \<noteq> q"
    then have "(p = P \<and> q = Q) \<or> (p = Q \<and> q = P)"
      using PType.exhaust by auto
    then have "\<exists>i. chan i = Some (p, q)" by (elim disjE) auto
    then show "(\<lambda>p q. \<exists>i. chan i = Some (p, q))\<^sup>+\<^sup>+ p q" by blast
  qed
  show "finite {i. \<exists>p q. chan i = Some (p, q)}"
  proof -
    have "{i. \<exists>p q. chan i = Some (p, q)} = {0,1}" by auto
    then show ?thesis by simp
  qed
  show "1 < card (UNIV :: PType set)"
  proof -
    have "(UNIV :: PType set) = {P, Q}"
      using PType.exhaust by blast
    then have "card (UNIV :: PType set) = 2" 
      by (metis One_nat_def PType.distinct(1) Suc_1 card.insert card.empty finite.emptyI finite.insertI insert_absorb insert_not_empty singletonD)
    then show ?thesis by auto
  qed
  show "finite (UNIV :: PType set)"
  proof -
    have "(UNIV :: PType set) = {P, Q}"
      using PType.exhaust by blast
    then show ?thesis 
      by (metis finite.emptyI finite.insertI)
  qed
  show "\<forall>i. \<nexists>p. chan i = Some (p, p)" by simp
  show "\<forall>i. (\<exists>p q. chan i = Some (p, q)) \<longrightarrow> Marker \<notin> set (msgs init i)" by auto
  show "\<forall>i. chan i = None \<longrightarrow> msgs init i = []" by auto
  show "\<forall>p. \<not> ps init p \<noteq> None" by auto
  show "\<forall>i. cs init i = ([], NotStarted)" by auto
  show "\<exists>t. distributed_system.trace chan Example.trans send recv init t s7"
  proof -
    let ?t = "[t0, t1, t2, t3, t4, t5, t6]"
    have "distributed_system.next chan trans send recv init t0 s1"
    proof -
      have "distributed_system.can_occur chan trans send recv t0 init"
        using \<open>distributed_system chan\<close> distributed_system.can_occur_def by fastforce
      then show ?thesis 
        by (simp add: \<open>distributed_system chan\<close> distributed_system.next_snapshot)
    qed
    moreover have "distributed_system.next chan trans send recv s1 t1 s2"
    proof -
      have "distributed_system.can_occur chan trans send recv t1 s1"
        using \<open>distributed_system chan\<close> distributed_system.can_occur_def by fastforce
      then show ?thesis 
        by (simp add: \<open>distributed_system chan\<close> distributed_system.next_send)
    qed
    moreover have "distributed_system.next chan trans send recv s2 t2 s3"
    proof -
      have "distributed_system.can_occur chan trans send recv t2 s2"
        using \<open>distributed_system chan\<close> distributed_system.can_occur_def by fastforce
      moreover have "\<forall>r. r \<noteq> P \<longrightarrow> r = Q" using PType.exhaust by auto
      ultimately show ?thesis by (simp add: \<open>distributed_system chan\<close> distributed_system.next_send)
    qed
    moreover have "distributed_system.next chan trans send recv s3 t3 s4"
    proof -
      have "distributed_system.can_occur chan trans send recv t3 s3"
        using \<open>distributed_system chan\<close> distributed_system.can_occur_def by fastforce
      moreover have "\<forall>p'. p' \<noteq> P \<longrightarrow> p' = Q" using PType.exhaust by auto
      ultimately show ?thesis by (simp add: \<open>distributed_system chan\<close> distributed_system.next_snapshot)
    qed
    moreover have "distributed_system.next chan trans send recv s4 t4 s5"
    proof -
      have "distributed_system.can_occur chan trans send recv t4 s4"
        using \<open>distributed_system chan\<close> distributed_system.can_occur_def by fastforce
      then show ?thesis
        by (simp add: \<open>distributed_system chan\<close> distributed_system.next_def)
    qed
    moreover have "distributed_system.next chan trans send recv s5 t5 s6"
    proof -
      have "distributed_system.can_occur chan trans send recv t5 s5"
        using \<open>distributed_system chan\<close> distributed_system.can_occur_def by fastforce
      then show ?thesis
        by (simp add: \<open>distributed_system chan\<close> distributed_system.next_def)
    qed
    moreover have "distributed_system.next chan trans send recv s6 t6 s7"
    proof -
      have "distributed_system.can_occur chan trans send recv t6 s6"
        using \<open>distributed_system chan\<close> distributed_system.can_occur_def by fastforce
      then show ?thesis
        by (simp add: \<open>distributed_system chan\<close> distributed_system.next_def)
    qed
    ultimately have "distributed_system.trace chan trans send recv init ?t s7" 
      by (meson \<open>distributed_system chan\<close> distributed_system.trace.simps)
    then show ?thesis by blast
  qed
  show "\<forall>t i cid. distributed_system.trace chan Example.trans send recv init t s7 \<and>
       Marker \<in> set (msgs (distributed_system.s chan Example.trans send recv init t i) cid) \<longrightarrow>
       (\<exists>j\<ge>i. Marker \<notin> set (msgs (distributed_system.s chan Example.trans send recv init t j) cid))"
  proof ((rule allI)+, (rule impI)+)
    fix t i cid
    assume asm: "distributed_system.trace chan Example.trans send recv init t s7 \<and>
                 Marker \<in> set (msgs (distributed_system.s chan Example.trans send recv init t i) cid)"
    have tr_exists: "distributed_system.trace chan Example.trans send recv init t s7" using asm by blast
    have marker_in_channel: "Marker \<in> set (msgs (distributed_system.s chan Example.trans send recv init t i) cid)" using asm by simp
    have s7_is_fin: "s7 = (distributed_system.s chan Example.trans send recv init t (length t))" 
      by (metis (no_types, lifting) \<open>distributed_system chan\<close> \<open>distributed_system.trace chan Example.trans send recv init t s7\<close> distributed_system.exists_trace_for_any_i distributed_system.trace_and_start_determines_end order_refl take_all)
    have "i < length t"
    proof (rule ccontr)
      assume "~ i < length t"
      then have "distributed_system.trace chan Example.trans send recv
                (distributed_system.s chan Example.trans send recv init t (length t))
                []
                (distributed_system.s chan Example.trans send recv init t i)" 
        by (metis (no_types, lifting) \<open>distributed_system chan\<close> distributed_system.exists_trace_for_any_i distributed_system.trace.simps distributed_system.trace_and_start_determines_end not_less s7_is_fin take_all tr_exists)
      then have "Marker \<notin> set (msgs (distributed_system.s chan Example.trans send recv init t i) cid)"
      proof -
        have "distributed_system.s chan Example.trans send recv init t i = s7" 
          using \<open>distributed_system chan\<close> \<open>distributed_system.trace chan Example.trans send recv (distributed_system.s chan Example.trans send recv init t (length t)) [] (distributed_system.s chan Example.trans send recv init t i)\<close> distributed_system.trace.simps s7_is_fin by fastforce
        then show ?thesis using s7_no_marker by simp
      qed
      then show False using marker_in_channel by simp
    qed
    then show "(\<exists>j\<ge>i. Marker \<notin> set (msgs (distributed_system.s chan Example.trans send recv init t j) cid))"
    proof -
      have "distributed_system.trace chan Example.trans send recv
            (distributed_system.s chan Example.trans send recv init t i)
            (take ((length t) - i) (drop i t))
            (distributed_system.s chan Example.trans send recv init t (length t))" 
        using \<open>distributed_system chan\<close> \<open>i < length t\<close> distributed_system.exists_trace_for_any_i_j less_imp_le_nat tr_exists by blast
      then have "Marker \<notin> set (msgs (distributed_system.s chan Example.trans send recv init t (length t)) cid)"
      proof -
        have "distributed_system.s chan Example.trans send recv init t (length t) = s7" 
          by (simp add: s7_is_fin)
        then show ?thesis using s7_no_marker by simp
      qed
      then show ?thesis 
        using \<open>i < length t\<close> less_imp_le_nat by blast
    qed
  qed
  show "\<forall>t p. distributed_system.trace chan Example.trans send recv init t s7 \<longrightarrow>
              (\<exists>i. ps (distributed_system.s chan Example.trans send recv init t i) p \<noteq> None \<and> i \<le> length t)"
  proof ((rule allI)+, rule impI)
    fix t p
    assume "distributed_system.trace chan Example.trans send recv init t s7"
    have s7_is_fin: "s7 = (distributed_system.s chan Example.trans send recv init t (length t))" 
      by (metis (no_types, lifting) \<open>distributed_system chan\<close> \<open>distributed_system.trace chan Example.trans send recv init t s7\<close> distributed_system.exists_trace_for_any_i distributed_system.trace_and_start_determines_end order_refl take_all)
    moreover have "has_snapshotted s7 p" by simp
    ultimately show "(\<exists>i. ps (distributed_system.s chan Example.trans send recv init t i) p \<noteq> None \<and> i \<le> length t)"
      by auto
  qed
qed

end
