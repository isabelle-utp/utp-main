(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Binary relation as a finite sequence\<close>
theory CZH_Sets_FBRelations
  imports CZH_Sets_FSequences
begin



subsection\<open>Background\<close>


text\<open>
This section exposes the theory of binary relations that are represented by
a two element finite sequence \<open>[a, b]\<^sub>\<circ>\<close> (as opposed to a pair \<open>\<langle>a, b\<rangle>\<close>).
Many results were adapted from the theory \<open>CZH_Sets_BRelations\<close>. 

As previously, many of the results that are presented in this 
section can be assumed to have been adapted (with amendments) from the 
theory \<^text>\<open>Relation\<close> in the main library.
\<close>

lemma fpair_iff[simp]: "([a, b]\<^sub>\<circ> = [a', b']\<^sub>\<circ>) = (a = a' \<and> b = b')" by simp

lemmas fpair_inject[elim!] = fpair_iff[THEN iffD1, THEN conjE]



subsection\<open>\<open>fpairs\<close>\<close>

definition fpairs :: "V \<Rightarrow> V" where
  "fpairs r = set {x. x \<in>\<^sub>\<circ> r \<and> (\<exists>a b. x = [a, b]\<^sub>\<circ>)}"

lemma small_fpairs[simp]: "small {x. x \<in>\<^sub>\<circ> r \<and> (\<exists>a b. x = [a, b]\<^sub>\<circ>)}"
  by (rule down[of _ r]) clarsimp


text\<open>Rules.\<close>

lemma fpairsI[intro]: 
  assumes "x \<in>\<^sub>\<circ> r" and "x = [a, b]\<^sub>\<circ>" 
  shows "x \<in>\<^sub>\<circ> fpairs r"
  using assms unfolding fpairs_def by auto

lemma fpairsD[dest]:
  assumes "x \<in>\<^sub>\<circ> fpairs r" 
  shows "x \<in>\<^sub>\<circ> r" and "\<exists>a b. x = [a, b]\<^sub>\<circ>" 
  using assms unfolding fpairs_def by auto

lemma fpairsE[elim]:
  assumes "x \<in>\<^sub>\<circ> fpairs r"
  obtains a b where "x = [a, b]\<^sub>\<circ>" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding fpairs_def by auto

lemma fpairs_iff: "x \<in>\<^sub>\<circ> fpairs r \<longleftrightarrow> x \<in>\<^sub>\<circ> r \<and> (\<exists>a b. x = [a, b]\<^sub>\<circ>)" by auto


text\<open>Elementary properties.\<close>

lemma fpairs_iff_elts: "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> fpairs r \<longleftrightarrow> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" by auto


text\<open>Set operations.\<close>

lemma fpairs_vempty[simp]: "fpairs 0 = 0" by auto

lemma fpairs_vsingleton[simp]: "fpairs (set {[a, b]\<^sub>\<circ>}) = set {[a, b]\<^sub>\<circ>}" by auto

lemma fpairs_vinsert: "fpairs (vinsert [a, b]\<^sub>\<circ> A) = set {[a, b]\<^sub>\<circ>} \<union>\<^sub>\<circ> fpairs A" 
  by auto

lemma fpairs_mono:
  assumes "r \<subseteq>\<^sub>\<circ> s"
  shows "fpairs r \<subseteq>\<^sub>\<circ> fpairs s"
  using assms by blast

lemma fpairs_vunion: "fpairs (A \<union>\<^sub>\<circ> B) = fpairs A \<union>\<^sub>\<circ> fpairs B" by auto

lemma fpairs_vintersection: "fpairs (A \<inter>\<^sub>\<circ> B) = fpairs A \<inter>\<^sub>\<circ> fpairs B" by auto

lemma fpairs_vdiff: "fpairs (A -\<^sub>\<circ> B) = fpairs A -\<^sub>\<circ> fpairs B" by auto


text\<open>Special properties.\<close>

lemma fpairs_ex_vfst:
  assumes "x \<in>\<^sub>\<circ> fpairs r"
  shows "\<exists>b. [x\<lparr>0\<^sub>\<nat>\<rparr>, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
proof-
  from assms have xr: "x \<in>\<^sub>\<circ> r" by auto
  moreover from assms obtain b where x_def: "x = [x\<lparr>0\<^sub>\<nat>\<rparr>, b]\<^sub>\<circ>" by auto
  ultimately have "[x\<lparr>0\<^sub>\<nat>\<rparr>, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" by auto
  then show ?thesis by auto
qed

lemma fpairs_ex_vsnd:
  assumes "x \<in>\<^sub>\<circ> fpairs r"
  shows "\<exists>a. [a, x\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
proof-
  from assms have xr: "x \<in>\<^sub>\<circ> r" by auto
  moreover from assms obtain a where x_def: "x = [a, x\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ>" 
    by (auto simp: nat_omega_simps)
  ultimately have "[a, x\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ> \<in>\<^sub>\<circ> r" by auto
  then show ?thesis by auto
qed

lemma fpair_vcpower2I[intro]:
  assumes "a \<in>\<^sub>\<circ> A ^\<^sub>\<times> 1\<^sub>\<nat>" and "b \<in>\<^sub>\<circ> A ^\<^sub>\<times> 1\<^sub>\<nat>"
  shows "vconcat [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat>"
proof-
  from assms obtain a' b' 
    where a_def: "a = [a']\<^sub>\<circ>" and b_def: "b = [b']\<^sub>\<circ>" and "a'\<in>\<^sub>\<circ> A" and "b'\<in>\<^sub>\<circ> A"
    by (force elim: vcons_vcpower1E)
  then show ?thesis by (auto simp: nat_omega_simps)
qed



subsection\<open>Constructors\<close>


subsubsection\<open>Identity relation\<close>

definition fid_on :: "V \<Rightarrow> V"
  where "fid_on A = set {[a, a]\<^sub>\<circ> | a. a \<in>\<^sub>\<circ> A}"

lemma fid_on_small[simp]: "small {[a, a]\<^sub>\<circ> | a. a \<in>\<^sub>\<circ> A}"
proof(rule down[of _ \<open>A ^\<^sub>\<times> (2\<^sub>\<nat>)\<close>], intro subsetI)  
  fix x assume "x \<in> {[a, a]\<^sub>\<circ> |a. a \<in>\<^sub>\<circ> A}"
  then obtain a where x_def: "x = [a, a]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> A" by clarsimp
  interpret vfsequence \<open>[a, a]\<^sub>\<circ>\<close> by simp
  have vcard_aa: "2\<^sub>\<nat> = vcard [a, a]\<^sub>\<circ>" by (simp add: nat_omega_simps)
  from \<open>a \<in>\<^sub>\<circ> A\<close> show "x \<in>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat>"
    unfolding x_def vcard_aa by (intro vfsequence_vrange_vcpower) auto
qed


text\<open>Rules.\<close>

lemma fid_on_eqI: 
  assumes "a = b" and "a \<in>\<^sub>\<circ> A"
  shows "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> fid_on A"
  using assms by (simp add: fid_on_def)

lemma fid_onI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "[a, a]\<^sub>\<circ> \<in>\<^sub>\<circ> fid_on A"
  by (rule fid_on_eqI) (simp_all add: assms)

lemma fid_onD[dest!]: 
  assumes "[a, a]\<^sub>\<circ> \<in>\<^sub>\<circ> fid_on A"
  shows "a \<in>\<^sub>\<circ> A"
  using assms unfolding fid_on_def by auto

lemma fid_onE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> fid_on A" and "\<exists>a\<in>\<^sub>\<circ>A. x = [a, a]\<^sub>\<circ> \<Longrightarrow> P" 
  shows P
  using assms unfolding fid_on_def by auto

lemma fid_on_iff: "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> fid_on A \<longleftrightarrow> a = b \<and> a \<in>\<^sub>\<circ> A" by auto


text\<open>Set operations.\<close>

lemma fid_on_vempty[simp]: "fid_on 0 = 0" by auto

lemma fid_on_vsingleton[simp]: "fid_on (set {a}) = set {[a, a]\<^sub>\<circ>}" by auto

lemma fid_on_vdoubleton: "fid_on (set {a, b}) = set {[a, a]\<^sub>\<circ>, [b, b]\<^sub>\<circ>}" by force

lemma fid_on_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B" 
  shows "fid_on A \<subseteq>\<^sub>\<circ> fid_on B"
  using assms by auto

lemma fid_on_vinsert: "vinsert [a, a]\<^sub>\<circ> (fid_on A) = fid_on (vinsert a A)" 
  by auto

lemma fid_on_vintersection: "fid_on (A \<inter>\<^sub>\<circ> B) = fid_on A \<inter>\<^sub>\<circ> fid_on B" by auto

lemma fid_on_vunion: "fid_on (A \<union>\<^sub>\<circ> B) = fid_on A \<union>\<^sub>\<circ> fid_on B" by auto

lemma fid_on_vdiff: "fid_on (A -\<^sub>\<circ> B) = fid_on A -\<^sub>\<circ> fid_on B" by auto


text\<open>Special properties.\<close>

lemma fid_on_vsubset_vcpower: "fid_on A \<subseteq>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat>" by force


subsubsection\<open>Constant function\<close>

definition fconst_on :: "V \<Rightarrow> V \<Rightarrow> V"
  where "fconst_on A c = set {[a, c]\<^sub>\<circ> | a. a \<in>\<^sub>\<circ> A}"

lemma small_fconst_on[simp]: "small {[a, c]\<^sub>\<circ> | a. a \<in>\<^sub>\<circ> A}"
  by (rule down[of _ \<open>A \<times>\<^sub>\<bullet> set {c}\<close>]) blast


text\<open>Rules.\<close>

lemma fconst_onI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "[a, c]\<^sub>\<circ> \<in>\<^sub>\<circ> fconst_on A c"
  using assms unfolding fconst_on_def by simp

lemma fconst_onD[dest!]: 
  assumes "[a, c]\<^sub>\<circ> \<in>\<^sub>\<circ> fconst_on A c"
  shows "a \<in>\<^sub>\<circ> A" 
  using assms unfolding fconst_on_def by simp

lemma fconst_onE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> fconst_on A c"
  obtains a where "a \<in>\<^sub>\<circ> A" and "x = [a, c]\<^sub>\<circ>"
  using assms unfolding fconst_on_def by auto

lemma fconst_on_iff: "[a, c]\<^sub>\<circ> \<in>\<^sub>\<circ> fconst_on A c \<longleftrightarrow> a \<in>\<^sub>\<circ> A" by auto


text\<open>Set operations.\<close>

lemma fconst_on_vempty[simp]: "fconst_on 0 c = 0"
  unfolding fconst_on_def by auto

lemma fconst_on_vsingleton[simp]: "fconst_on (set {a}) c = set {[a, c]\<^sub>\<circ>}" 
  by auto

lemma fconst_on_vdoubleton: "fconst_on (set {a, b}) c = set {[a, c]\<^sub>\<circ>, [b, c]\<^sub>\<circ>}" 
  by force

lemma fconst_on_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B" 
  shows "fconst_on A c \<subseteq>\<^sub>\<circ> fconst_on B c"
  using assms by auto

lemma fconst_on_vinsert:
  "(vinsert [a, c]\<^sub>\<circ> (fconst_on A c)) = (fconst_on (vinsert a A) c)" 
  by auto

lemma fconst_on_vintersection: 
  "fconst_on (A \<inter>\<^sub>\<circ> B) c = fconst_on A c \<inter>\<^sub>\<circ> fconst_on B c"
  by auto

lemma fconst_on_vunion: "fconst_on (A \<union>\<^sub>\<circ> B) c = fconst_on A c \<union>\<^sub>\<circ> fconst_on B c"
  by auto

lemma fconst_on_vdiff: "fconst_on (A -\<^sub>\<circ> B) c = fconst_on A c -\<^sub>\<circ> fconst_on B c"
  by auto


text\<open>Special properties.\<close>

lemma fconst_on_eq_ftimes: "fconst_on A c = A \<times>\<^sub>\<bullet> set {c}" by blast


subsubsection\<open>Composition\<close>

definition fcomp :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<circ>\<^sub>\<bullet>\<close> 75)
  where "r \<circ>\<^sub>\<bullet> s = set {[a, c]\<^sub>\<circ> | a c. \<exists>b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> s \<and> [b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
notation fcomp (infixr "\<circ>\<^sub>\<bullet>" 75)

lemma fcomp_small[simp]: "small {[a, c]\<^sub>\<circ> | a c. \<exists>b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> s \<and> [b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> r}" 
  (is \<open>small ?s\<close>)
proof-
  define comp' where "comp' = (\<lambda>\<langle>ab, cd\<rangle>. [ab\<lparr>0\<^sub>\<nat>\<rparr>, cd\<lparr>1\<^sub>\<nat>\<rparr>]\<^sub>\<circ>)"
  have "small (elts (vpairs (s \<times>\<^sub>\<circ> r)))" by simp
  then have small_comp: "small (comp' ` elts (vpairs (s \<times>\<^sub>\<circ> r)))" by simp
  have ss: "?s \<subseteq> (comp' ` elts (vpairs (s \<times>\<^sub>\<circ> r)))" 
  proof
    fix x assume "x \<in> ?s"
    then obtain a b c where x_def: "x = [a, c]\<^sub>\<circ>" 
      and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> s" 
      and "[b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
      by auto
    then have abbc: "\<langle>[a, b]\<^sub>\<circ>, [b, c]\<^sub>\<circ>\<rangle> \<in>\<^sub>\<circ> vpairs (s \<times>\<^sub>\<circ> r)"
      by (simp add: vpairs_iff_elts)
    have x_def': "x = comp' \<langle>[a, b]\<^sub>\<circ>, [b, c]\<^sub>\<circ>\<rangle>" 
      unfolding comp'_def x_def by (auto simp: nat_omega_simps)
    then show "x \<in> comp' ` elts (vpairs (s \<times>\<^sub>\<circ> r))"
      unfolding x_def' using abbc by auto
  qed
  with small_comp show ?thesis by (meson smaller_than_small)
qed


text\<open>Rules.\<close>

lemma fcompI[intro]: 
  assumes "[b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> r" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> s" 
  shows "[a, c]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<circ>\<^sub>\<bullet> s"
  using assms unfolding fcomp_def by auto

lemma fcompD[dest]: 
  assumes "[a, c]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<circ>\<^sub>\<bullet> s"
  shows "\<exists>b. [b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<and> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> s" 
  using assms unfolding fcomp_def by auto

lemma fcompE[elim]:
  assumes "ac \<in>\<^sub>\<circ> r \<circ>\<^sub>\<bullet> s" 
  obtains a b c where "ac = [a, c]\<^sub>\<circ>" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> s" and "[b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding fcomp_def by clarsimp


text\<open>Elementary properties.\<close>

lemma fcomp_assoc: "(r \<circ>\<^sub>\<bullet> s) \<circ>\<^sub>\<bullet> t = r \<circ>\<^sub>\<bullet> (s \<circ>\<^sub>\<bullet> t)" by fast


text\<open>Set operations.\<close>

lemma fcomp_vempty_left[simp]: "0 \<circ>\<^sub>\<bullet> r = 0" unfolding vcomp_def by force

lemma fcomp_vempty_right[simp]: "r \<circ>\<^sub>\<bullet> 0 = 0" unfolding vcomp_def by force

lemma fcomp_mono:
  assumes "r' \<subseteq>\<^sub>\<circ> r" and "s' \<subseteq>\<^sub>\<circ> s" 
  shows "r' \<circ>\<^sub>\<bullet> s' \<subseteq>\<^sub>\<circ> r \<circ>\<^sub>\<bullet> s"
  using assms by force

lemma fcomp_vinsert_left[simp]: 
  "vinsert ([a, b]\<^sub>\<circ>) s \<circ>\<^sub>\<bullet> r = (set {[a, b]\<^sub>\<circ>} \<circ>\<^sub>\<bullet> r) \<union>\<^sub>\<circ> (s \<circ>\<^sub>\<bullet> r)" 
  by auto

lemma fcomp_vinsert_right[simp]: 
  "r \<circ>\<^sub>\<bullet> vinsert [a, b]\<^sub>\<circ> s = (r \<circ>\<^sub>\<bullet> set {[a, b]\<^sub>\<circ>}) \<union>\<^sub>\<circ> (r \<circ>\<^sub>\<bullet> s)"
  by auto

lemma fcomp_vunion_left[simp]: "(s \<union>\<^sub>\<circ> t) \<circ>\<^sub>\<bullet> r = (s \<circ>\<^sub>\<bullet> r) \<union>\<^sub>\<circ> (t \<circ>\<^sub>\<bullet> r)" by auto

lemma fcomp_vunion_right[simp]: "r \<circ>\<^sub>\<bullet> (s \<union>\<^sub>\<circ> t) = (r \<circ>\<^sub>\<bullet> s) \<union>\<^sub>\<circ> (r \<circ>\<^sub>\<bullet> t)" by auto


text\<open>Connections.\<close>

lemma fcomp_fid_on_idem[simp]: "fid_on A \<circ>\<^sub>\<bullet> fid_on A = fid_on A" by auto

lemma fcomp_fid_on[simp]: "fid_on A \<circ>\<^sub>\<bullet> fid_on B = fid_on (A \<inter>\<^sub>\<circ> B)" by auto

lemma fcomp_fconst_on_fid_on[simp]: "fconst_on A c \<circ>\<^sub>\<bullet> fid_on A = fconst_on A c" 
  by auto


text\<open>Special properties.\<close>

lemma fcomp_vsubset_vtimes:
  assumes "r \<subseteq>\<^sub>\<circ> B \<times>\<^sub>\<bullet> C" and "s \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B" 
  shows "r \<circ>\<^sub>\<bullet> s \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<bullet> C"
  using assms by blast

lemma fcomp_obtain_middle[elim]:
  assumes "[a, c]\<^sub>\<circ> \<in>\<^sub>\<circ> f \<circ>\<^sub>\<bullet> g"
  obtains b where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> g" and "[b, c]\<^sub>\<circ> \<in>\<^sub>\<circ> f"
  using assms by auto


subsubsection\<open>Converse relation\<close>

definition fconverse :: "V \<Rightarrow> V" (\<open>(_\<inverse>\<^sub>\<bullet>)\<close> [1000] 999)
  where "r\<inverse>\<^sub>\<bullet> = set {[b, a]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"

lemma fconverse_small[simp]: "small {[b, a]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
proof-
  have eq: 
    "{[b, a]\<^sub>\<circ> | a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r} = (\<lambda>x. [x\<lparr>1\<^sub>\<nat>\<rparr>, x\<lparr>0\<^sub>\<nat>\<rparr>]\<^sub>\<circ>) ` elts (fpairs r)"
  proof(rule subset_antisym; rule subsetI, unfold mem_Collect_eq)
    fix x assume "x \<in> (\<lambda>x. [x\<lparr>1\<^sub>\<nat>\<rparr>, x\<lparr>0\<^sub>\<nat>\<rparr>]\<^sub>\<circ>) ` elts (fpairs r)" 
    then obtain a b where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> fpairs r" 
      and "x = (\<lambda>x. [x\<lparr>1\<^sub>\<nat>\<rparr>, x\<lparr>0\<^sub>\<nat>\<rparr>]\<^sub>\<circ>) [a, b]\<^sub>\<circ>"
      by blast
    then show "\<exists>a b. x = [b, a]\<^sub>\<circ> \<and> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" by (auto simp: nat_omega_simps)
  qed (use image_iff fpairs_iff_elts in \<open>fastforce simp: nat_omega_simps\<close>)
  show ?thesis unfolding eq by (rule replacement) auto
qed


text\<open>Rules.\<close>

lemma fconverseI[sym, intro!]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  shows "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<bullet>"
  using assms unfolding fconverse_def by simp

lemma fconverseD[sym, dest]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<bullet>"
  shows "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> r" 
  using assms unfolding fconverse_def by simp

lemma fconverseE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<bullet>" 
  obtains a b where "x = [b, a]\<^sub>\<circ>" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding fconverse_def by auto

lemma fconverse_iff: "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<bullet> \<longleftrightarrow> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" by auto


text\<open>Set operations.\<close>

lemma fconverse_vempty[simp]: "0\<inverse>\<^sub>\<bullet> = 0" by auto

lemma fconverse_vsingleton: "(set {[a, b]\<^sub>\<circ>})\<inverse>\<^sub>\<bullet> = set {[b, a]\<^sub>\<circ>}" by auto

lemma fconverse_vdoubleton: "(set {[a, b]\<^sub>\<circ>, [c, d]\<^sub>\<circ>})\<inverse>\<^sub>\<bullet> = set {[b, a]\<^sub>\<circ>, [d, c]\<^sub>\<circ>}" 
  by force

lemma fconverse_vinsert: "(vinsert [a, b]\<^sub>\<circ> r)\<inverse>\<^sub>\<bullet> = vinsert [b, a]\<^sub>\<circ> (r\<inverse>\<^sub>\<bullet>)" by auto

lemma fconverse_vintersection: "(r \<inter>\<^sub>\<circ> s)\<inverse>\<^sub>\<bullet> = r\<inverse>\<^sub>\<bullet> \<inter>\<^sub>\<circ> s\<inverse>\<^sub>\<bullet>" by auto

lemma fconverse_vunion: "(r \<union>\<^sub>\<circ> s)\<inverse>\<^sub>\<bullet> = r\<inverse>\<^sub>\<bullet> \<union>\<^sub>\<circ> s\<inverse>\<^sub>\<bullet>" by auto


text\<open>Connections.\<close>

lemma fconverse_fid_on[simp]: "(fid_on A)\<inverse>\<^sub>\<bullet> = fid_on A" by auto

lemma fconverse_fconst_on[simp]: "(fconst_on A c)\<inverse>\<^sub>\<bullet> = set {c} \<times>\<^sub>\<bullet> A" by blast

lemma fconverse_fcomp: "(r \<circ>\<^sub>\<bullet> s)\<inverse>\<^sub>\<bullet> = s\<inverse>\<^sub>\<bullet> \<circ>\<^sub>\<bullet> r\<inverse>\<^sub>\<bullet>" by auto

lemma fconverse_ftimes: "(A \<times>\<^sub>\<bullet> B)\<inverse>\<^sub>\<bullet> = (B \<times>\<^sub>\<bullet> A)" by auto


text\<open>Special properties.\<close>

lemma fconverse_pred:
  assumes "small {[a, b]\<^sub>\<circ> | a b. P a b}"
  shows "(set {[a, b]\<^sub>\<circ> | a b. P a b})\<inverse>\<^sub>\<bullet> = set {[b, a]\<^sub>\<circ> | a b. P a b}"
  using assms unfolding fconverse_def by simp


subsubsection\<open>Left restriction\<close>

definition flrestriction :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<restriction>\<^sup>l\<^sub>\<bullet>\<close> 80)
  where "r \<restriction>\<^sup>l\<^sub>\<bullet> A = set {[a, b]\<^sub>\<circ> | a b. a \<in>\<^sub>\<circ> A \<and> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"

lemma flrestriction_small[simp]: "small {[a, b]\<^sub>\<circ> | a b. a \<in>\<^sub>\<circ> A \<and> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
  by (rule down[of _ r]) auto


text\<open>Rules.\<close>

lemma flrestrictionI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" 
  shows "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<bullet> A" 
  using assms unfolding flrestriction_def by simp

lemma flrestrictionD[dest]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<bullet> A"  
  shows "a \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding flrestriction_def by auto

lemma flrestrictionE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<bullet> A"
  obtains a b where "x = [a, b]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding flrestriction_def by auto


text\<open>Set operations.\<close>

lemma flrestriction_on_vempty[simp]: "r \<restriction>\<^sup>l\<^sub>\<bullet> 0 = 0" by auto

lemma flrestriction_vempty[simp]: "0 \<restriction>\<^sup>l\<^sub>\<bullet> A = 0" by auto

lemma flrestriction_vsingleton_in[simp]: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} \<restriction>\<^sup>l\<^sub>\<bullet> A = set {[a, b]\<^sub>\<circ>}" 
  using assms by auto

lemma flrestriction_vsingleton_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} \<restriction>\<^sup>l\<^sub>\<bullet> A = 0" 
  using assms by auto

lemma flrestriction_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "r \<restriction>\<^sup>l\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> r \<restriction>\<^sup>l\<^sub>\<bullet> B"
  using assms by auto

lemma flrestriction_vinsert_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "(vinsert [a, b]\<^sub>\<circ> r) \<restriction>\<^sup>l\<^sub>\<bullet> A = r \<restriction>\<^sup>l\<^sub>\<bullet> A" 
  using assms by auto

lemma flrestriction_vinsert_in: 
  assumes "a \<in>\<^sub>\<circ> A"
  shows "(vinsert [a, b]\<^sub>\<circ> r) \<restriction>\<^sup>l\<^sub>\<bullet> A = vinsert [a, b]\<^sub>\<circ> (r \<restriction>\<^sup>l\<^sub>\<bullet> A)" 
  using assms by auto

lemma flrestriction_vintersection: "(r \<inter>\<^sub>\<circ> s) \<restriction>\<^sup>l\<^sub>\<bullet> A = r \<restriction>\<^sup>l\<^sub>\<bullet> A \<inter>\<^sub>\<circ> s \<restriction>\<^sup>l\<^sub>\<bullet> A" by auto

lemma flrestriction_vunion: "(r \<union>\<^sub>\<circ> s) \<restriction>\<^sup>l\<^sub>\<bullet> A = r \<restriction>\<^sup>l\<^sub>\<bullet> A \<union>\<^sub>\<circ> s \<restriction>\<^sup>l\<^sub>\<bullet> A" by auto

lemma flrestriction_vdiff: "(r -\<^sub>\<circ> s) \<restriction>\<^sup>l\<^sub>\<bullet> A = r \<restriction>\<^sup>l\<^sub>\<bullet> A -\<^sub>\<circ> s \<restriction>\<^sup>l\<^sub>\<bullet> A" by auto


text\<open>Connections.\<close>

lemma flrestriction_fid_on[simp]: "(fid_on A) \<restriction>\<^sup>l\<^sub>\<bullet> B = fid_on (A \<inter>\<^sub>\<circ> B)" by auto

lemma flrestriction_fconst_on: "(fconst_on A c) \<restriction>\<^sup>l\<^sub>\<bullet> B = (fconst_on B c) \<restriction>\<^sup>l\<^sub>\<bullet> A"
  by auto

lemma flrestriction_fconst_on_commute:
  assumes "x \<in>\<^sub>\<circ> fconst_on A c \<restriction>\<^sup>l\<^sub>\<bullet> B"
  shows "x \<in>\<^sub>\<circ> fconst_on B c \<restriction>\<^sup>l\<^sub>\<bullet> A"
  using assms by auto

lemma flrestriction_fcomp[simp]: "(r \<circ>\<^sub>\<bullet> s) \<restriction>\<^sup>l\<^sub>\<bullet> A = r \<circ>\<^sub>\<bullet> (s \<restriction>\<^sup>l\<^sub>\<bullet> A)" by auto


text\<open>Previous connections.\<close>

lemma fcomp_rel_fid_on[simp]: "r \<circ>\<^sub>\<bullet> fid_on A = r \<restriction>\<^sup>l\<^sub>\<bullet> A" by auto

lemma fcomp_fconst_on: 
  "r \<circ>\<^sub>\<bullet> (fconst_on A c) = (r \<restriction>\<^sup>l\<^sub>\<bullet> set {c}) \<circ>\<^sub>\<bullet> (fconst_on A c)" 
  by auto


text\<open>Special properties.\<close>

lemma flrestriction_vsubset_fpairs: "r \<restriction>\<^sup>l\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> fpairs r"
  by (rule vsubsetI) (metis fpairs_iff_elts flrestrictionE)

lemma flrestriction_vsubset_frel: "r \<restriction>\<^sup>l\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> r" by auto


subsubsection\<open>Right restriction\<close>

definition frrestriction :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<restriction>\<^sup>r\<^sub>\<bullet>\<close> 80)
  where "r \<restriction>\<^sup>r\<^sub>\<bullet> A = set {[a, b]\<^sub>\<circ> | a b. b \<in>\<^sub>\<circ> A \<and> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"

lemma frrestriction_small[simp]: "small {[a, b]\<^sub>\<circ> | a b. b \<in>\<^sub>\<circ> A \<and> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
  by (rule down[of _ r]) auto


text\<open>Rules.\<close>

lemma frrestrictionI[intro!]: 
  assumes "b \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" 
  shows "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<bullet> A" 
  using assms unfolding frrestriction_def by simp

lemma frrestrictionD[dest]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<bullet> A"  
  shows "b \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding frrestriction_def by auto

lemma frrestrictionE[elim!]: 
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<bullet> A"
  obtains a b where "x = [a, b]\<^sub>\<circ>" and "b \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding frrestriction_def by auto


text\<open>Set operations.\<close>

lemma frrestriction_on_vempty[simp]: "r \<restriction>\<^sup>r\<^sub>\<bullet> 0 = 0" by auto

lemma frrestriction_vempty[simp]: "0 \<restriction>\<^sup>r\<^sub>\<bullet> A = 0" by auto

lemma frrestriction_vsingleton_in[simp]: 
  assumes "b \<in>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} \<restriction>\<^sup>r\<^sub>\<bullet> A = set {[a, b]\<^sub>\<circ>}" 
  using assms by auto

lemma frrestriction_vsingleton_nin[simp]: 
  assumes "b \<notin>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} \<restriction>\<^sup>r\<^sub>\<bullet> A = 0" 
  using assms by auto

lemma frrestriction_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "r \<restriction>\<^sup>r\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> r \<restriction>\<^sup>r\<^sub>\<bullet> B"
  using assms by auto

lemma frrestriction_vinsert_nin[simp]:
  assumes "b \<notin>\<^sub>\<circ> A"
  shows "(vinsert [a, b]\<^sub>\<circ> r) \<restriction>\<^sup>r\<^sub>\<bullet> A = r \<restriction>\<^sup>r\<^sub>\<bullet> A" 
  using assms by auto

lemma frrestriction_vinsert_in: 
  assumes "b \<in>\<^sub>\<circ> A"
  shows "(vinsert [a, b]\<^sub>\<circ> r) \<restriction>\<^sup>r\<^sub>\<bullet> A = vinsert [a, b]\<^sub>\<circ> (r \<restriction>\<^sup>r\<^sub>\<bullet> A)" 
  using assms by auto

lemma frrestriction_vintersection: "(r \<inter>\<^sub>\<circ> s) \<restriction>\<^sup>r\<^sub>\<bullet> A = r \<restriction>\<^sup>r\<^sub>\<bullet> A \<inter>\<^sub>\<circ> s \<restriction>\<^sup>r\<^sub>\<bullet> A" by auto

lemma frrestriction_vunion: "(r \<union>\<^sub>\<circ> s) \<restriction>\<^sup>r\<^sub>\<bullet> A = r \<restriction>\<^sup>r\<^sub>\<bullet> A \<union>\<^sub>\<circ> s \<restriction>\<^sup>r\<^sub>\<bullet> A" by auto

lemma frrestriction_vdiff: "(r -\<^sub>\<circ> s) \<restriction>\<^sup>r\<^sub>\<bullet> A = r \<restriction>\<^sup>r\<^sub>\<bullet> A -\<^sub>\<circ> s \<restriction>\<^sup>r\<^sub>\<bullet> A" by auto


text\<open>Connections.\<close>

lemma frrestriction_fid_on[simp]: "(fid_on A) \<restriction>\<^sup>r\<^sub>\<bullet> B = fid_on (A \<inter>\<^sub>\<circ> B)" by auto

lemma frrestriction_fconst_on:
  assumes "c \<in>\<^sub>\<circ> B"
  shows "(fconst_on A c) \<restriction>\<^sup>r\<^sub>\<bullet> B = fconst_on A c"  
  using assms by auto

lemma frrestriction_fcomp[simp]: "(r \<circ>\<^sub>\<bullet> s) \<restriction>\<^sup>r\<^sub>\<bullet> A = (r \<restriction>\<^sup>r\<^sub>\<bullet> A) \<circ>\<^sub>\<bullet> s" by auto


text\<open>Previous connections.\<close>

lemma fcomp_fid_on_rel[simp]: "fid_on A \<circ>\<^sub>\<bullet> r = r \<restriction>\<^sup>r\<^sub>\<bullet> A" by force

lemma fcomp_fconst_on_rel: "(fconst_on A c) \<circ>\<^sub>\<bullet> r = (fconst_on A c) \<circ>\<^sub>\<bullet> (r \<restriction>\<^sup>r\<^sub>\<bullet> A)" 
  by auto

lemma flrestriction_fconverse: "r\<inverse>\<^sub>\<bullet> \<restriction>\<^sup>l\<^sub>\<bullet> A = (r \<restriction>\<^sup>r\<^sub>\<bullet> A)\<inverse>\<^sub>\<bullet>" by auto

lemma frrestriction_fconverse: "r\<inverse>\<^sub>\<bullet> \<restriction>\<^sup>r\<^sub>\<bullet> A = (r \<restriction>\<^sup>l\<^sub>\<bullet> A)\<inverse>\<^sub>\<bullet>" by auto


text\<open>Special properties.\<close>

lemma frrestriction_vsubset_rel: "r \<restriction>\<^sup>r\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> r" by auto

lemma frrestriction_vsubset_vpairs: "r \<restriction>\<^sup>r\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> fpairs r" by auto


subsubsection\<open>Restriction\<close>

definition frestriction :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>\<restriction>\<^sub>\<bullet>\<close> 80)
  where "r \<restriction>\<^sub>\<bullet> A = set {[a, b]\<^sub>\<circ> | a b. a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"

lemma frestriction_small[simp]: 
  "small {[a, b]\<^sub>\<circ> | a b. a \<in>\<^sub>\<circ> A \<and> b \<in>\<^sub>\<circ> A \<and> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
  by (rule down[of _ r]) auto


text\<open>Rules.\<close>

lemma frestrictionI[intro!]: 
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" 
  shows "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<restriction>\<^sub>\<bullet> A" 
  using assms unfolding frestriction_def by simp

lemma frestrictionD[dest]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<restriction>\<^sub>\<bullet> A"  
  shows "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding frestriction_def by auto

lemma frestrictionE[elim!]:
  assumes "x \<in>\<^sub>\<circ> r \<restriction>\<^sub>\<bullet> A"
  obtains a b where "x = [a, b]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A" and "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding frestriction_def by clarsimp


text\<open>Set operations.\<close>

lemma frestriction_on_vempty[simp]: "r \<restriction>\<^sub>\<bullet> 0 = 0" by auto

lemma frestriction_vempty[simp]: "0 \<restriction>\<^sub>\<bullet> A = 0" by auto

lemma frestriction_vsingleton_in[simp]: 
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} \<restriction>\<^sub>\<bullet> A = set {[a, b]\<^sub>\<circ>}" 
  using assms by auto

lemma frestriction_vsingleton_nin_left[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} \<restriction>\<^sub>\<bullet> A = 0" 
  using assms by auto

lemma frestriction_vsingleton_nin_right[simp]: 
  assumes "b \<notin>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} \<restriction>\<^sub>\<bullet> A = 0" 
  using assms by auto

lemma frestriction_mono: 
  assumes "A \<subseteq>\<^sub>\<circ> B"
  shows "r \<restriction>\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> r \<restriction>\<^sub>\<bullet> B"
  using assms by auto

lemma frestriction_vinsert_nin[simp]: 
  assumes "a \<notin>\<^sub>\<circ> A" and "b \<notin>\<^sub>\<circ> A"
  shows "(vinsert [a, b]\<^sub>\<circ> r) \<restriction>\<^sub>\<bullet> A = r \<restriction>\<^sub>\<bullet> A" 
  using assms by auto

lemma frestriction_vinsert_in: 
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A"
  shows "(vinsert [a, b]\<^sub>\<circ> r) \<restriction>\<^sub>\<bullet> A = vinsert [a, b]\<^sub>\<circ> (r \<restriction>\<^sub>\<bullet> A)" 
  using assms by auto

lemma frestriction_vintersection: "(r \<inter>\<^sub>\<circ> s) \<restriction>\<^sub>\<bullet> A = r \<restriction>\<^sub>\<bullet> A \<inter>\<^sub>\<circ> s \<restriction>\<^sub>\<bullet> A" by auto

lemma frestriction_vunion: "(r \<union>\<^sub>\<circ> s) \<restriction>\<^sub>\<bullet> A = r \<restriction>\<^sub>\<bullet> A \<union>\<^sub>\<circ> s \<restriction>\<^sub>\<bullet> A" by auto

lemma frestriction_vdiff: "(r -\<^sub>\<circ> s) \<restriction>\<^sub>\<bullet> A = r \<restriction>\<^sub>\<bullet> A -\<^sub>\<circ> s \<restriction>\<^sub>\<bullet> A" by auto


text\<open>Connections.\<close>

lemma fid_on_frestriction[simp]: "(fid_on A) \<restriction>\<^sub>\<bullet> B = fid_on (A \<inter>\<^sub>\<circ> B)" by auto

lemma frestriction_fconst_on_ex:
  assumes "c \<in>\<^sub>\<circ> B"
  shows "(fconst_on A c) \<restriction>\<^sub>\<bullet> B = fconst_on (A \<inter>\<^sub>\<circ> B) c"  
  using assms by auto

lemma frestriction_fconst_on_nex:
  assumes "c \<notin>\<^sub>\<circ> B"
  shows "(fconst_on A c) \<restriction>\<^sub>\<bullet> B = 0"  
  using assms by auto

lemma frestriction_fcomp[simp]: "(r \<circ>\<^sub>\<bullet> s) \<restriction>\<^sub>\<bullet> A = (r \<restriction>\<^sup>r\<^sub>\<bullet> A) \<circ>\<^sub>\<bullet> (s \<restriction>\<^sup>l\<^sub>\<bullet> A)" by auto

lemma frestriction_fconverse: "r\<inverse>\<^sub>\<bullet> \<restriction>\<^sub>\<bullet> A = (r \<restriction>\<^sub>\<bullet> A)\<inverse>\<^sub>\<bullet>" by auto


text\<open>Previous connections.\<close>

lemma frrestriction_flrestriction[simp]: "(r \<restriction>\<^sup>r\<^sub>\<bullet> A) \<restriction>\<^sup>l\<^sub>\<bullet> A = r \<restriction>\<^sub>\<bullet> A" by auto

lemma flrestriction_frrestriction[simp]: "(r \<restriction>\<^sup>l\<^sub>\<bullet> A) \<restriction>\<^sup>r\<^sub>\<bullet> A = r \<restriction>\<^sub>\<bullet> A" by auto

lemma frestriction_flrestriction[simp]: "(r \<restriction>\<^sub>\<bullet> A) \<restriction>\<^sup>l\<^sub>\<bullet> A = r \<restriction>\<^sub>\<bullet> A" by auto

lemma frestriction_frrestriction[simp]: "(r \<restriction>\<^sub>\<bullet> A) \<restriction>\<^sup>r\<^sub>\<bullet> A = r \<restriction>\<^sub>\<bullet> A" by auto


text\<open>Special properties.\<close>

lemma frestriction_vsubset_fpairs: "r \<restriction>\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> fpairs r" by auto

lemma frestriction_vsubset_ftimes: "r \<restriction>\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat>" by force

lemma frestriction_vsubset_rel: "r \<restriction>\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> r" by auto



subsection\<open>Properties\<close>


subsubsection\<open>Domain\<close>

definition fdomain :: "V \<Rightarrow> V" (\<open>\<D>\<^sub>\<bullet>\<close>)
  where "\<D>\<^sub>\<bullet> r = set {a. \<exists>b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
notation fdomain (\<open>\<D>\<^sub>\<bullet>\<close>)

lemma fdomain_small[simp]: "small {a. \<exists>b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
proof-
  have ss: "{a. \<exists>b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r} \<subseteq> (\<lambda>x. x\<lparr>0\<^sub>\<nat>\<rparr>) ` elts r" 
    using image_iff by force
  have small: "small ((\<lambda>x. x\<lparr>0\<^sub>\<nat>\<rparr>) ` elts r)" by (rule replacement) simp
  show ?thesis by (rule smaller_than_small, rule small, rule ss)
qed


text\<open>Rules.\<close>

lemma fdomainI[intro]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  shows "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> r"
  using assms unfolding fdomain_def by auto

lemma fdomainD[dest]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> r"
  shows "\<exists>b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" 
  using assms unfolding fdomain_def by auto

lemma fdomainE[elim]:
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> r"
  obtains b where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding fdomain_def by clarsimp

lemma fdomain_iff: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> r \<longleftrightarrow> (\<exists>y. [a, y]\<^sub>\<circ> \<in>\<^sub>\<circ> r)" by auto


text\<open>Set operations.\<close>

lemma fdomain_vempty[simp]: "\<D>\<^sub>\<bullet> 0 = 0" by force

lemma fdomain_vsingleton[simp]: "\<D>\<^sub>\<bullet> (set {[a, b]\<^sub>\<circ>}) = set {a}" by auto

lemma fdomain_vdoubleton[simp]: "\<D>\<^sub>\<bullet> (set {[a, b]\<^sub>\<circ>, [c, d]\<^sub>\<circ>}) = set {a, c}" 
  by force

lemma fdomain_mono: 
  assumes "r \<subseteq>\<^sub>\<circ> s"
  shows "\<D>\<^sub>\<bullet> r \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<bullet> s"
  using assms by blast

lemma fdomain_vinsert[simp]: "\<D>\<^sub>\<bullet> (vinsert [a, b]\<^sub>\<circ> r) = vinsert a (\<D>\<^sub>\<bullet> r)" 
  by force

lemma fdomain_vunion: "\<D>\<^sub>\<bullet> (A \<union>\<^sub>\<circ> B) = \<D>\<^sub>\<bullet> A \<union>\<^sub>\<circ> \<D>\<^sub>\<bullet> B" by force

lemma fdomain_vintersection_vsubset: "\<D>\<^sub>\<bullet> (A \<inter>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<bullet> A \<inter>\<^sub>\<circ> \<D>\<^sub>\<bullet> B" by auto

lemma fdomain_vdiff_vsubset: "\<D>\<^sub>\<bullet> A -\<^sub>\<circ> \<D>\<^sub>\<bullet> B \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<bullet> (A -\<^sub>\<circ> B)" by auto


text\<open>Connections.\<close>

lemma fdomain_fid_on[simp]: "\<D>\<^sub>\<bullet> (fid_on A) = A" by force

lemma fdomain_fconst_on[simp]: "\<D>\<^sub>\<bullet> (fconst_on A c) = A" by force

lemma fdomain_flrestriction: "\<D>\<^sub>\<bullet> (r \<restriction>\<^sup>l\<^sub>\<bullet> A) = \<D>\<^sub>\<bullet> r \<inter>\<^sub>\<circ> A" by auto


text\<open>Special properties.\<close>

lemma fdomain_vsubset_ftimes:
  assumes "fpairs r \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B"
  shows "\<D>\<^sub>\<bullet> r \<subseteq>\<^sub>\<circ> A"
  using assms by blast

lemma fdomain_vsubset_VUnion2: "\<D>\<^sub>\<bullet> r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r))"
proof(intro vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> r"
  then obtain y where "[x, y]\<^sub>\<circ> \<in>\<^sub>\<circ> r" by auto
  then have "set {\<langle>0\<^sub>\<nat>, x\<rangle>, \<langle>1\<^sub>\<nat>, y\<rangle>} \<in>\<^sub>\<circ> r" unfolding vcons_vdoubleton by simp
  with insert_commute have "\<langle>0\<^sub>\<nat>, x\<rangle> \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>r" by auto
  then show "x \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r))" 
    unfolding vpair_def 
    by (metis (full_types) VUnion_iff insert_commute vintersection_vdoubleton)
qed


subsubsection\<open>Range\<close>

definition frange :: "V \<Rightarrow> V" (\<open>\<R>\<^sub>\<bullet>\<close>)
  where "frange r = set {b. \<exists>a. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
notation frange (\<open>\<R>\<^sub>\<bullet>\<close>)

lemma frange_small[simp]: "small {b. \<exists>a. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
proof-
  have ss: "{b. \<exists>a. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r} \<subseteq> (\<lambda>x. x\<lparr>1\<^sub>\<nat>\<rparr>) ` elts r" 
    using image_iff by (fastforce simp: nat_omega_simps)
  have small: "small ((\<lambda>x. x\<lparr>1\<^sub>\<nat>\<rparr>) ` elts r)" by (rule replacement) simp
  show ?thesis by (rule smaller_than_small, rule small, rule ss)
qed


text\<open>Rules.\<close>

lemma frangeI[intro]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  shows "b \<in>\<^sub>\<circ> \<R>\<^sub>\<bullet> r"
  using assms unfolding frange_def by auto

lemma frangeD[dest]: 
  assumes "b \<in>\<^sub>\<circ> \<R>\<^sub>\<bullet> r"
  shows "\<exists>a. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" 
  using assms unfolding frange_def by simp

lemma frangeE[elim!]:
  assumes "b \<in>\<^sub>\<circ> \<R>\<^sub>\<bullet> r"
  obtains a where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  using assms unfolding frange_def by clarsimp

lemma frange_iff: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<bullet> r \<longleftrightarrow> (\<exists>a. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r)" by auto


text\<open>Set operations.\<close>

lemma frange_vempty[simp]: "\<R>\<^sub>\<bullet> 0 = 0" by auto

lemma frange_vsingleton[simp]: "\<R>\<^sub>\<bullet> (set {[a, b]\<^sub>\<circ>}) = set {b}" by auto

lemma frange_vdoubleton[simp]: "\<R>\<^sub>\<bullet> (set {[a, b]\<^sub>\<circ>, [c, d]\<^sub>\<circ>}) = set {b, d}" 
  by force

lemma frange_mono: 
  assumes "r \<subseteq>\<^sub>\<circ> s" 
  shows "\<R>\<^sub>\<bullet> r \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<bullet> s"
  using assms by force

lemma frange_vinsert[simp]: "\<R>\<^sub>\<bullet> (vinsert [a, b]\<^sub>\<circ> r) = vinsert b (\<R>\<^sub>\<bullet> r)" by auto

lemma frange_vunion: "\<R>\<^sub>\<bullet> (r \<union>\<^sub>\<circ> s) = \<R>\<^sub>\<bullet> r \<union>\<^sub>\<circ> \<R>\<^sub>\<bullet> s" by auto

lemma frange_vintersection_vsubset: "\<R>\<^sub>\<bullet> (r \<inter>\<^sub>\<circ> s) \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<bullet> r \<inter>\<^sub>\<circ> \<R>\<^sub>\<bullet> s" by auto

lemma frange_vdiff_vsubset: "\<R>\<^sub>\<bullet> r -\<^sub>\<circ> \<R>\<^sub>\<bullet> s \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<bullet> (r -\<^sub>\<circ> s)" by auto


text\<open>Connections.\<close>

lemma frange_fid_on[simp]: "\<R>\<^sub>\<bullet> (fid_on A) = A" by force

lemma frange_fconst_on_vempty[simp]: "\<R>\<^sub>\<bullet> (fconst_on 0 c) = 0" by auto

lemma frange_fconst_on_ne[simp]: 
  assumes "A \<noteq> 0"
  shows "\<R>\<^sub>\<bullet> (fconst_on A c) = set {c}"
  using assms by force

lemma frange_vrrestriction: "\<R>\<^sub>\<bullet> (r \<restriction>\<^sup>r\<^sub>\<bullet> A) = \<R>\<^sub>\<bullet> r \<inter>\<^sub>\<circ> A" by auto


text\<open>Previous connections\<close>

lemma fdomain_fconverse[simp]: "\<D>\<^sub>\<bullet> (r\<inverse>\<^sub>\<bullet>) = \<R>\<^sub>\<bullet> r" by auto

lemma frange_fconverse[simp]: "\<R>\<^sub>\<bullet> (r\<inverse>\<^sub>\<bullet>) = \<D>\<^sub>\<bullet> r" by force


text\<open>Special properties.\<close>

lemma frange_iff_vdomain: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<bullet> r \<longleftrightarrow> (\<exists>a\<in>\<^sub>\<circ>\<D>\<^sub>\<bullet> r. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r)" by auto

lemma frange_vsubset_ftimes:
  assumes "fpairs r \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B"
  shows "\<R>\<^sub>\<bullet> r \<subseteq>\<^sub>\<circ> B"
  using assms by blast

lemma fpairs_vsubset_fdomain_frange[simp]: "fpairs r \<subseteq>\<^sub>\<circ> (\<D>\<^sub>\<bullet> r) \<times>\<^sub>\<bullet> (\<R>\<^sub>\<bullet> r)" 
  by blast

lemma frange_vsubset_VUnion2: "\<R>\<^sub>\<bullet> r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r))"
proof(intro vsubsetI)
  fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<bullet> r"
  then obtain x where "[x, y]\<^sub>\<circ> \<in>\<^sub>\<circ> r" by auto
  then have "set {\<langle>0\<^sub>\<nat>, x\<rangle>, \<langle>1\<^sub>\<nat>, y\<rangle>} \<in>\<^sub>\<circ> r" unfolding vcons_vdoubleton by simp
  with insert_commute have "\<langle>1\<^sub>\<nat>, y\<rangle> \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>r" by auto
  then show "y \<in>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r))" 
    unfolding vpair_def 
    by (metis (full_types) VUnion_iff insert_commute vintersection_vdoubleton)
qed
  

subsubsection\<open>Field\<close>

definition ffield :: "V \<Rightarrow> V"
  where "ffield r = \<D>\<^sub>\<bullet> r \<union>\<^sub>\<circ> \<R>\<^sub>\<bullet> r"

abbreviation app_ffield :: "V \<Rightarrow> V" (\<open>\<F>\<^sub>\<bullet>\<close>)
  where "\<F>\<^sub>\<bullet> r \<equiv> ffield r"


text\<open>Rules.\<close>

lemma ffieldI1[intro]: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> r \<union>\<^sub>\<circ> \<R>\<^sub>\<bullet> r"
  shows "a \<in>\<^sub>\<circ> ffield r"
  using assms unfolding ffield_def by simp

lemma ffieldI2[intro]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  shows "a \<in>\<^sub>\<circ> ffield r"
  using assms by auto

lemma ffieldI3[intro]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  shows "b \<in>\<^sub>\<circ> ffield r"
  using assms by auto

lemma ffieldD[intro]: 
  assumes "a \<in>\<^sub>\<circ> ffield r"
  shows "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> r \<union>\<^sub>\<circ> \<R>\<^sub>\<bullet> r"
  using assms unfolding ffield_def by simp

lemma ffieldE[elim]:  
  assumes "a \<in>\<^sub>\<circ> ffield r" and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> r \<union>\<^sub>\<circ> \<R>\<^sub>\<bullet> r \<Longrightarrow> P"
  shows P
  using assms by (auto dest: ffieldD)

lemma ffield_pair[elim]:
  assumes "a \<in>\<^sub>\<circ> ffield r"
  obtains b where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<or> [b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> r "
  using assms by auto

lemma ffield_iff: "a \<in>\<^sub>\<circ> ffield r \<longleftrightarrow> (\<exists>b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<or> [b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> r)" by auto


text\<open>Set operations.\<close>

lemma ffield_vempty[simp]: "ffield 0 = 0" by force

lemma ffield_vsingleton[simp]: "ffield (set {[a, b]\<^sub>\<circ>}) = set {a, b}" by force

lemma ffield_vdoubleton[simp]: 
  "ffield (set {[a, b]\<^sub>\<circ>, [c, d]\<^sub>\<circ>}) = set {a, b, c, d}" 
  by force

lemma ffield_mono:
  assumes "r \<subseteq>\<^sub>\<circ> s" 
  shows "ffield r \<subseteq>\<^sub>\<circ> ffield s"
  using assms by fastforce

lemma ffield_vinsert[simp]: 
  "ffield (vinsert [a, b]\<^sub>\<circ> r) = set {a, b} \<union>\<^sub>\<circ> (ffield r)"
  apply (intro vsubset_antisym; intro vsubsetI)
  subgoal by auto
  subgoal by (metis ffield_iff vinsert_iff vinsert_vinsert)
  done

lemma ffield_vunion[simp]: "ffield (r \<union>\<^sub>\<circ> s) = ffield r \<union>\<^sub>\<circ> ffield s" 
  unfolding ffield_def by auto


text\<open>Connections.\<close>

lemma fid_on_ffield[simp]: "ffield (fid_on A) = A" by force

lemma fconst_on_ffield_ne[intro, simp]:
  assumes "A \<noteq> 0" 
  shows "ffield (fconst_on A c) = vinsert c A" 
  using assms by force

lemma fconst_on_ffield_vempty[simp]: "ffield (fconst_on 0 c) = 0" by auto

lemma ffield_fconverse[simp]: "ffield (r\<inverse>\<^sub>\<bullet>) = ffield r" by force


text\<open>Special properties.\<close>

lemma ffield_vsubset_VUnion2: "\<F>\<^sub>\<bullet> r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>(\<Union>\<^sub>\<circ>r))"
  using fdomain_vsubset_VUnion2 frange_vsubset_VUnion2 by (auto simp: ffield_def)


subsubsection\<open>Image\<close>

definition fimage :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>`\<^sub>\<bullet>\<close> 90)
  where "r `\<^sub>\<bullet> A = \<R>\<^sub>\<bullet> (r \<restriction>\<^sup>l\<^sub>\<bullet> A)"
notation fimage (infixr "`\<^sub>\<bullet>" 90)

lemma fimage_small[simp]: "small {b. \<exists>a\<in>\<^sub>\<circ>A. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
proof-
  from image_iff ord_of_nat_succ_vempty have ss: 
    "{b. \<exists>a\<in>\<^sub>\<circ>A. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r} \<subseteq> (\<lambda>x. x\<lparr>1\<^sub>\<nat>\<rparr>) ` elts r"         
    by fastforce
  have small: "small ((\<lambda>x. x\<lparr>1\<^sub>\<nat>\<rparr>) ` elts r)" by (rule replacement) simp
  show ?thesis by (rule smaller_than_small, rule small, rule ss)
qed


text\<open>Rules.\<close>

lemma fimageI1: 
  assumes "x \<in>\<^sub>\<circ> \<R>\<^sub>\<bullet> (r \<restriction>\<^sup>l\<^sub>\<bullet> A)"
  shows "x \<in>\<^sub>\<circ> r `\<^sub>\<bullet> A" 
  using assms unfolding fimage_def by simp

lemma fimageI2[intro]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A" 
  shows "b \<in>\<^sub>\<circ> r `\<^sub>\<bullet> A"
  using assms fimageI1 by auto

lemma fimageD[dest]: 
  assumes "x \<in>\<^sub>\<circ> r `\<^sub>\<bullet> A"
  shows "x \<in>\<^sub>\<circ> \<R>\<^sub>\<bullet> (r \<restriction>\<^sup>l\<^sub>\<bullet> A)"
  using assms unfolding fimage_def by simp

lemma fimageE[elim]:
  assumes "b \<in>\<^sub>\<circ> r `\<^sub>\<bullet> A"
  obtains a where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" and "a \<in>\<^sub>\<circ> A"
  using assms unfolding fimage_def by auto

lemma fimage_iff: "b \<in>\<^sub>\<circ> r `\<^sub>\<bullet> A \<longleftrightarrow> (\<exists>a\<in>\<^sub>\<circ>A. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r)" by auto


text\<open>Set operations.\<close>

lemma fimage_vempty[simp]: "0 `\<^sub>\<bullet> A = 0" by force

lemma fimage_of_vempty[simp]: "r `\<^sub>\<bullet> 0 = 0" by force

lemma fimage_vsingleton_in[intro, simp]: 
  assumes "a \<in>\<^sub>\<circ> A" 
  shows "set {[a, b]\<^sub>\<circ>} `\<^sub>\<bullet> A = set {b}" 
  using assms by auto

lemma fimage_vsingleton_nin[intro, simp]: 
  assumes "a \<notin>\<^sub>\<circ> A" 
  shows "set {[a, b]\<^sub>\<circ>} `\<^sub>\<bullet> A = 0" 
  using assms by auto

lemma fimage_vsingleton_vinsert[intro, simp]: 
  "set {[a, b]\<^sub>\<circ>} `\<^sub>\<bullet> vinsert a A = set {b}" 
  by auto

lemma fimage_mono: 
  assumes "r' \<subseteq>\<^sub>\<circ> r" and "A' \<subseteq>\<^sub>\<circ> A" 
  shows "(r' `\<^sub>\<bullet> A') \<subseteq>\<^sub>\<circ> (r `\<^sub>\<bullet> A)" 
  using assms by fastforce

lemma fimage_vinsert: "r `\<^sub>\<bullet> (vinsert a A) = r `\<^sub>\<bullet> set {a} \<union>\<^sub>\<circ> r `\<^sub>\<bullet> A" by auto

lemma fimage_vunion_left: "(r \<union>\<^sub>\<circ> s) `\<^sub>\<bullet> A = r `\<^sub>\<bullet> A \<union>\<^sub>\<circ> s `\<^sub>\<bullet> A" by auto

lemma fimage_vunion_right: "r `\<^sub>\<bullet> (A \<union>\<^sub>\<circ> B) = r `\<^sub>\<bullet> A \<union>\<^sub>\<circ> r `\<^sub>\<bullet> B" by auto

lemma fimage_vintersection: "r `\<^sub>\<bullet> (A \<inter>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> r `\<^sub>\<bullet> A \<inter>\<^sub>\<circ> r `\<^sub>\<bullet> B" by auto

lemma fimage_vdiff: "r `\<^sub>\<bullet> A -\<^sub>\<circ> r `\<^sub>\<bullet> B \<subseteq>\<^sub>\<circ> r `\<^sub>\<bullet> (A -\<^sub>\<circ> B)" by auto


text\<open>Special properties.\<close>

lemma fimage_vsingleton_iff[iff]: "b \<in>\<^sub>\<circ> r `\<^sub>\<bullet> set {a} \<longleftrightarrow> [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" by auto

lemma fimage_is_vempty[iff]: "r `\<^sub>\<bullet> A = 0 \<longleftrightarrow> vdisjnt (\<D>\<^sub>\<bullet> r) A" by fastforce


text\<open>Connections.\<close>

lemma fid_on_fimage[simp]: "(fid_on A) `\<^sub>\<bullet> B = A \<inter>\<^sub>\<circ> B" by force

lemma fimage_fconst_on_ne[simp]: 
  assumes "B \<inter>\<^sub>\<circ> A \<noteq> 0" 
  shows "(fconst_on A c) `\<^sub>\<bullet> B = set {c}" 
  using assms by auto

lemma fimage_fconst_on_vempty[simp]: 
  assumes "vdisjnt A B"
  shows "(fconst_on A c) `\<^sub>\<bullet> B = 0" 
  using assms by auto

lemma fimage_fconst_on_vsubset_const[simp]: "(fconst_on A c) `\<^sub>\<bullet> B \<subseteq>\<^sub>\<circ> set {c}" 
  by auto

lemma fcomp_frange: "\<R>\<^sub>\<bullet> (r \<circ>\<^sub>\<bullet> s) = r `\<^sub>\<bullet> (\<R>\<^sub>\<bullet> s)" by blast

lemma fcomp_fimage: "(r \<circ>\<^sub>\<bullet> s) `\<^sub>\<bullet> A = r `\<^sub>\<bullet> (s `\<^sub>\<bullet> A)" by blast

lemma fimage_flrestriction[simp]: "(r \<restriction>\<^sup>l\<^sub>\<bullet> A) `\<^sub>\<bullet> B = r `\<^sub>\<bullet> (A \<inter>\<^sub>\<circ> B)" by auto

lemma fimage_frrestriction[simp]: "(r \<restriction>\<^sup>r\<^sub>\<bullet> A) `\<^sub>\<bullet> B = A \<inter>\<^sub>\<circ> r `\<^sub>\<bullet> B" by auto

lemma fimage_frestriction[simp]: "(r \<restriction>\<^sub>\<bullet> A) `\<^sub>\<bullet> B = A \<inter>\<^sub>\<circ> (r `\<^sub>\<bullet> (A \<inter>\<^sub>\<circ> B))" by auto

lemma fimage_fdomain: "r `\<^sub>\<bullet> \<D>\<^sub>\<bullet> r = \<R>\<^sub>\<bullet> r" by auto

lemma fimage_eq_imp_fcomp: 
  assumes "f `\<^sub>\<bullet> A = g `\<^sub>\<bullet> B" 
  shows "(h \<circ>\<^sub>\<bullet> f) `\<^sub>\<bullet> A = (h \<circ>\<^sub>\<bullet> g) `\<^sub>\<bullet> B"
  using assms by (metis fcomp_fimage)


text\<open>Previous connections.\<close>

lemma fcomp_rel_fconst_on_ftimes: "r \<circ>\<^sub>\<bullet> (fconst_on A c) = A \<times>\<^sub>\<bullet> (r `\<^sub>\<bullet> set {c})" 
  by blast


text\<open>Further special properties.\<close>

lemma fimage_vsubset: 
  assumes "r \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B" 
  shows "r `\<^sub>\<bullet> C \<subseteq>\<^sub>\<circ> B" 
  using assms by blast

lemma fimage_set_def: "r `\<^sub>\<bullet> A = set {b. \<exists>a\<in>\<^sub>\<circ>A. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
  unfolding fimage_def frange_def by auto

lemma fimage_vsingleton: "r `\<^sub>\<bullet> set {a} = set {b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
proof-
  have "{b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r} \<subseteq> {b. \<exists>a. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}" by auto
  then have [simp]: "small {b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}" 
    by (rule smaller_than_small[OF frange_small[of r]])
  show ?thesis by auto
qed

lemma fimage_strict_vsubset: "f `\<^sub>\<bullet> A \<subseteq>\<^sub>\<circ> f `\<^sub>\<bullet> \<D>\<^sub>\<bullet> f" by auto


subsubsection\<open>Inverse image\<close>

definition finvimage :: "V \<Rightarrow> V \<Rightarrow> V" (infixr \<open>-`\<^sub>\<bullet>\<close> 90)
  where "r -`\<^sub>\<bullet> A = r\<inverse>\<^sub>\<bullet> `\<^sub>\<bullet> A"

lemma finvimage_small[simp]: "small {a. \<exists>b\<in>\<^sub>\<circ>A. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}"
proof-
  have ss: "{a. \<exists>b\<in>\<^sub>\<circ>A. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r} \<subseteq> (\<lambda>x. x\<lparr>0\<^sub>\<nat>\<rparr>) ` elts r" 
    using image_iff by fastforce
  have small: "small ((\<lambda>x. x\<lparr>0\<^sub>\<nat>\<rparr>) ` elts r)" by (rule replacement) simp
  show ?thesis by (rule smaller_than_small, rule small, rule ss)
qed


text\<open>Rules.\<close>

lemma finvimageI[intro]:
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> A" 
  shows "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A"
  using assms finvimage_def by auto

lemma finvimageD[dest]: 
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A"
  shows "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> (r \<restriction>\<^sup>r\<^sub>\<bullet> A)"
  using assms using finvimage_def by auto

lemma finvimageE[elim]:
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A"
  obtains b where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r" and "b \<in>\<^sub>\<circ> A"
  using assms unfolding finvimage_def by auto

lemma finvimageI1: 
  assumes "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> (r \<restriction>\<^sup>r\<^sub>\<bullet> A)"
  shows "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A" 
  using assms unfolding fimage_def 
  by (simp add: finvimage_def fimageI1 flrestriction_fconverse)

lemma finvimageD1: 
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A"
  shows "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> (r \<restriction>\<^sup>r\<^sub>\<bullet> A)"
  using assms by fastforce

lemma finvimageE1:
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A " and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> (r \<restriction>\<^sup>r\<^sub>\<bullet> A) \<Longrightarrow> P"
  shows P
  using assms by auto

lemma finvimageI2: 
  assumes "a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<bullet> `\<^sub>\<bullet> A"
  shows "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A" 
  using assms unfolding finvimage_def by simp

lemma finvimageD2:
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A"
  shows "a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<bullet> `\<^sub>\<bullet> A"
  using assms unfolding finvimage_def by simp

lemma finvimageE2:
  assumes "a \<in>\<^sub>\<circ> r -`\<^sub>\<circ> A" and "a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<circ> `\<^sub>\<circ> A \<Longrightarrow> P"
  shows P
  unfolding vimage_def using assms by blast

lemma finvimage_iff: "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A \<longleftrightarrow> (\<exists>b\<in>\<^sub>\<circ>A. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r)" by auto

lemma finvimage_iff1: "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A \<longleftrightarrow> a \<in>\<^sub>\<circ> \<D>\<^sub>\<bullet> (r \<restriction>\<^sup>r\<^sub>\<bullet> A)" by auto

lemma finvimage_iff2: "a \<in>\<^sub>\<circ> r -`\<^sub>\<bullet> A \<longleftrightarrow> a \<in>\<^sub>\<circ> r\<inverse>\<^sub>\<bullet> `\<^sub>\<bullet> A" by auto


text\<open>Set operations.\<close>

lemma finvimage_vempty[simp]: "0 -`\<^sub>\<bullet> A = 0" by force

lemma finvimage_of_vempty[simp]: "r -`\<^sub>\<bullet> 0 = 0" by force

lemma finvimage_vsingleton_in[intro, simp]: 
  assumes "b \<in>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} -`\<^sub>\<bullet> A = set {a}" 
  using assms by auto

lemma finvimage_vsingleton_nin[intro, simp]: 
  assumes "b \<notin>\<^sub>\<circ> A"
  shows "set {[a, b]\<^sub>\<circ>} -`\<^sub>\<bullet> A = 0" 
  using assms by auto

lemma finvimage_vsingleton_vinsert[intro, simp]: 
  "set {[a, b]\<^sub>\<circ>} -`\<^sub>\<bullet> vinsert b A = set {a}" 
  by auto

lemma finvimage_mono: 
  assumes "r' \<subseteq>\<^sub>\<circ> r" and "A' \<subseteq>\<^sub>\<circ> A"
  shows "(r' -`\<^sub>\<bullet> A') \<subseteq>\<^sub>\<circ> (r -`\<^sub>\<bullet> A)" 
  using assms by fastforce

lemma finvimage_vinsert: "r -`\<^sub>\<bullet> (vinsert a A) = r -`\<^sub>\<bullet> set {a} \<union>\<^sub>\<circ> r -`\<^sub>\<bullet> A" by auto

lemma finvimage_vunion_left: "(r \<union>\<^sub>\<circ> s) -`\<^sub>\<bullet> A = r -`\<^sub>\<bullet> A \<union>\<^sub>\<circ> s -`\<^sub>\<bullet> A" by auto

lemma finvimage_vunion_right: "r -`\<^sub>\<bullet> (A \<union>\<^sub>\<circ> B) = r -`\<^sub>\<bullet> A \<union>\<^sub>\<circ> r -`\<^sub>\<bullet> B" by auto

lemma finvimage_vintersection: "r -`\<^sub>\<bullet> (A \<inter>\<^sub>\<circ> B) \<subseteq>\<^sub>\<circ> r -`\<^sub>\<bullet> A \<inter>\<^sub>\<circ> r -`\<^sub>\<bullet> B" by auto

lemma finvimage_vdiff: "r -`\<^sub>\<bullet> A -\<^sub>\<circ> r -`\<^sub>\<bullet> B \<subseteq>\<^sub>\<circ> r -`\<^sub>\<bullet> (A -\<^sub>\<circ> B)" by auto


text\<open>Special properties.\<close>

lemma finvimage_set_def: "r -`\<^sub>\<bullet> A = set {a. \<exists>b\<in>\<^sub>\<circ>A. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r}" by fastforce

lemma finvimage_eq_fdomain_frestriction: "r -`\<^sub>\<bullet> A = \<D>\<^sub>\<bullet> (r \<restriction>\<^sup>r\<^sub>\<bullet> A)" by fastforce

lemma finvimage_frange[simp]: "r -`\<^sub>\<bullet> \<R>\<^sub>\<bullet> r = \<D>\<^sub>\<bullet> r"
  unfolding invimage_def by force

lemma finvimage_frange_vsubset[simp]: 
  assumes "\<R>\<^sub>\<bullet> r \<subseteq>\<^sub>\<circ> B" 
  shows "r -`\<^sub>\<bullet> B = \<D>\<^sub>\<bullet> r"
  using assms unfolding finvimage_def by force


text\<open>Connections.\<close>

lemma finvimage_fid_on[simp]: "(fid_on A) -`\<^sub>\<bullet> B = A \<inter>\<^sub>\<circ> B" by force

lemma finvimage_fconst_on_vsubset_fdomain[simp]: "(fconst_on A c) -`\<^sub>\<bullet> B \<subseteq>\<^sub>\<circ> A" 
  unfolding finvimage_def by blast

lemma finvimage_fconst_on_ne[simp]: 
  assumes "c \<in>\<^sub>\<circ> B"
  shows "(fconst_on A c) -`\<^sub>\<bullet> B = A" 
  by (simp add: assms finvimage_eq_fdomain_frestriction frrestriction_fconst_on)

lemma finvimage_fconst_on_vempty[simp]: 
  assumes "c \<notin>\<^sub>\<circ> B"
  shows "(fconst_on A c) -`\<^sub>\<bullet> B = 0" 
  using assms by auto

lemma finvimage_fcomp: "(g \<circ>\<^sub>\<bullet> f) -`\<^sub>\<bullet> x = f -`\<^sub>\<bullet> (g -`\<^sub>\<bullet> x) "
  by (simp add: finvimage_def fconverse_fcomp fcomp_fimage)

lemma finvimage_fconverse[simp]: "r\<inverse>\<^sub>\<bullet> -`\<^sub>\<bullet> A = r `\<^sub>\<bullet> A" by auto

lemma finvimage_flrestriction[simp]: "(r \<restriction>\<^sup>l\<^sub>\<bullet> A) -`\<^sub>\<bullet> B = A \<inter>\<^sub>\<circ> r -`\<^sub>\<bullet> B" by auto

lemma finvimage_frrestriction[simp]: "(r \<restriction>\<^sup>r\<^sub>\<bullet> A) -`\<^sub>\<bullet> B = (r -`\<^sub>\<bullet> (A \<inter>\<^sub>\<circ> B))" by auto

lemma finvimage_frestriction[simp]: "(r \<restriction>\<^sub>\<bullet> A) -`\<^sub>\<bullet> B = A \<inter>\<^sub>\<circ> (r -`\<^sub>\<bullet> (A \<inter>\<^sub>\<circ> B))" 
  by blast


text\<open>Previous connections.\<close>

lemma fdomain_fcomp[simp]: "\<D>\<^sub>\<bullet> (r \<circ>\<^sub>\<bullet> s) = s -`\<^sub>\<bullet> \<D>\<^sub>\<bullet> r" by force



subsection\<open>Classification of relations\<close>


subsubsection\<open>Binary relation\<close>

locale fbrelation = 
  fixes r :: V
  assumes fbrelation[simp]: "fpairs r = r"

locale fbrelation_pair = r\<^sub>1: fbrelation r\<^sub>1 + r\<^sub>2: fbrelation r\<^sub>2 for r\<^sub>1 r\<^sub>2


text\<open>Rules.\<close>

lemma fpairs_eqI[intro!]:
  assumes "\<And>x. x \<in>\<^sub>\<circ> r \<Longrightarrow> \<exists>a b. x = [a, b]\<^sub>\<circ>"
  shows "fpairs r = r"
  using assms by auto

lemma fpairs_eqD[dest]: 
  assumes "fpairs r = r"
  shows "\<And>x. x \<in>\<^sub>\<circ> r \<Longrightarrow> \<exists>a b. x = [a, b]\<^sub>\<circ>"
  using assms by auto

lemma fpairs_eqE[elim!]: 
  assumes "fpairs r = r" and "(\<And>x. x \<in>\<^sub>\<circ> r \<Longrightarrow> \<exists>a b. x = [a, b]\<^sub>\<circ>) \<Longrightarrow> P"
  shows P
  using assms by auto

lemmas fbrelationI[intro!] = fbrelation.intro 
lemmas fbrelationD[dest!] = fbrelation.fbrelation

lemma fbrelationE[elim!]: 
  assumes "fbrelation r" and "(fpairs r = r) \<Longrightarrow> P"
  shows P
  using assms unfolding fbrelation_def by auto

lemma fbrelationE1:
  assumes "fbrelation r" and "x \<in>\<^sub>\<circ> r" 
  obtains a b where "x = [a, b]\<^sub>\<circ>"
  using assms by auto

lemma fbrelationD1[dest]:
  assumes "fbrelation r" and "x \<in>\<^sub>\<circ> r" 
  shows "\<exists>a b. x = [a, b]\<^sub>\<circ>"
  using assms by auto


text\<open>Set operations.\<close>

lemma fbrelation_vsubset:
  assumes "fbrelation s" and "r \<subseteq>\<^sub>\<circ> s" 
  shows "fbrelation r"
  using assms by auto

lemma fbrelation_vinsert: "fbrelation (vinsert [a, b]\<^sub>\<circ> r) \<longleftrightarrow> fbrelation r"  
  by auto

lemma (in fbrelation) fbrelation_vinsertI: "fbrelation (vinsert [a, b]\<^sub>\<circ> r)"
  using fbrelation_axioms by auto

lemma fbrelation_vinsertD[dest]:
  assumes "fbrelation (vinsert \<langle>a, b\<rangle> r)"
  shows "fbrelation r"
  using assms by auto

lemma fbrelation_vunion: "fbrelation (r \<union>\<^sub>\<circ> s) \<longleftrightarrow> fbrelation r \<and> fbrelation s"
  by auto

lemma (in fbrelation_pair) fbrelation_vunionI: "fbrelation (r\<^sub>1 \<union>\<^sub>\<circ> r\<^sub>2)"
  using r\<^sub>1.fbrelation_axioms r\<^sub>2.fbrelation_axioms by auto

lemma fbrelation_vunionD[dest]: 
  assumes "fbrelation (r \<union>\<^sub>\<circ> s)"
  shows "fbrelation r" and "fbrelation s"
  using assms by auto

lemma (in fbrelation) fbrelation_vintersectionI: "fbrelation (r \<inter>\<^sub>\<circ> s)"
  using fbrelation_axioms by auto

lemma (in fbrelation) fbrelation_vdiffI: "fbrelation (r -\<^sub>\<circ> s)"
  using fbrelation_axioms by auto


text\<open>Connections.\<close>

lemma fbrelation_vempty: "fbrelation 0" by auto

lemma fbrelation_vsingleton: "fbrelation (set {[a, b]\<^sub>\<circ>})" by auto

global_interpretation frel_vsingleton: fbrelation \<open>set {[a, b]\<^sub>\<circ>}\<close> 
  by (rule fbrelation_vsingleton)

lemma fbrelation_vdoubleton: "fbrelation (set {[a, b]\<^sub>\<circ>, [c, d]\<^sub>\<circ>})" by auto

lemma fbrelation_sid_on[simp]: "fbrelation (fid_on A)" by auto

lemma fbrelation_fconst_on[simp]: "fbrelation (fconst_on A c)" by auto

lemma (in fbrelation_pair) fbrelation_fcomp: "fbrelation (r\<^sub>1 \<circ>\<^sub>\<bullet> r\<^sub>2)" 
  using r\<^sub>1.fbrelation_axioms r\<^sub>2.fbrelation_axioms by auto

sublocale fbrelation_pair \<subseteq> fcomp\<^sub>2\<^sub>1: fbrelation \<open>r\<^sub>2 \<circ>\<^sub>\<bullet> r\<^sub>1\<close>
  by 
    (
      simp add: 
        fbrelation_pair.fbrelation_fcomp 
        fbrelation_pair_def 
        r\<^sub>1.fbrelation_axioms 
        r\<^sub>2.fbrelation_axioms
     )

sublocale fbrelation_pair \<subseteq> fcomp\<^sub>1\<^sub>2: fbrelation \<open>r\<^sub>1 \<circ>\<^sub>\<bullet> r\<^sub>2\<close> 
  by (rule fbrelation_fcomp)

lemma (in fbrelation) fbrelation_fconverse: "fbrelation (r\<inverse>\<^sub>\<bullet>)"
  using fbrelation_axioms by clarsimp

lemma fbrelation_flrestriction[intro, simp]: "fbrelation (r \<restriction>\<^sup>l\<^sub>\<bullet> A)" by auto

lemma fbrelation_frrestriction[intro, simp]: "fbrelation (r \<restriction>\<^sup>r\<^sub>\<bullet> A)" by auto

lemma fbrelation_frestriction[intro, simp]: "fbrelation (r \<restriction>\<^sub>\<bullet> A)" by auto


text\<open>Previous connections.\<close>

lemma (in fbrelation) fconverse_fconverse[simp]: "(r\<inverse>\<^sub>\<bullet>)\<inverse>\<^sub>\<bullet> = r"
  using fbrelation_axioms by auto

lemma (in fbrelation_pair) fconverse_mono[simp]: "r\<^sub>1\<inverse>\<^sub>\<bullet> \<subseteq>\<^sub>\<circ> r\<^sub>2\<inverse>\<^sub>\<bullet> \<longleftrightarrow> r\<^sub>1 \<subseteq>\<^sub>\<circ> r\<^sub>2"
  using r\<^sub>1.fbrelation_axioms r\<^sub>2.fbrelation_axioms 
  by (force intro: fconverse_vunion)+

lemma (in fbrelation_pair) fconverse_inject[simp]: "r\<^sub>1\<inverse>\<^sub>\<bullet> = r\<^sub>2\<inverse>\<^sub>\<bullet> \<longleftrightarrow> r\<^sub>1 = r\<^sub>2"
  using r\<^sub>1.fbrelation_axioms r\<^sub>2.fbrelation_axioms by fast

lemma (in fbrelation) fconverse_vsubset_swap_2: 
  assumes "r\<inverse>\<^sub>\<bullet> \<subseteq>\<^sub>\<circ> s"
  shows "r \<subseteq>\<^sub>\<circ> s\<inverse>\<^sub>\<bullet>" 
  using assms fbrelation_axioms by auto

lemma (in fbrelation) flrestriction_fdomain[simp]: "r \<restriction>\<^sup>l\<^sub>\<bullet> \<D>\<^sub>\<bullet> r = r"
  using fbrelation_axioms by (elim fbrelationE) blast

lemma (in fbrelation) frrestriction_frange[simp]: "r \<restriction>\<^sup>r\<^sub>\<bullet> \<R>\<^sub>\<bullet> r = r"
  using fbrelation_axioms by (elim fbrelationE) blast


text\<open>Special properties.\<close>

lemma vsubset_vtimes_fbrelation: 
  assumes "r \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<bullet> B"
  shows "fbrelation r" 
  using assms by blast

lemma (in fbrelation) fbrelation_vintersection_vdomain:
  assumes "vdisjnt (\<D>\<^sub>\<bullet> r) (\<D>\<^sub>\<bullet> s)"
  shows "vdisjnt r s"
proof(rule vsubset_antisym; rule vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
  then obtain a b where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
    by (metis fbrelationE1 fbrelation_vintersectionI)
  with assms show "x \<in>\<^sub>\<circ> 0" by auto
qed simp

lemma (in fbrelation) fbrelation_vintersection_vrange:
  assumes "vdisjnt (\<R>\<^sub>\<bullet> r) (\<R>\<^sub>\<bullet> s)"
  shows "vdisjnt r s"
proof(rule vsubset_antisym; rule vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
  then obtain a b where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
    by (metis fbrelationE1 fbrelation_vintersectionI)
  with assms show "x \<in>\<^sub>\<circ> 0" by auto
qed simp

lemma (in fbrelation) fbrelation_vintersection_vfield:
  assumes "vdisjnt (ffield r) (ffield s)"
  shows "vdisjnt r s"
proof(rule vsubset_antisym; rule vsubsetI)
  fix x assume "x \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
  then obtain a b where "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<inter>\<^sub>\<circ> s"
    by (metis fbrelationE1 fbrelation_vintersectionI)
  with assms show "x \<in>\<^sub>\<circ> 0" by auto
qed auto

lemma (in fbrelation) vdomain_vrange_vtimes: "r \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<bullet> r \<times>\<^sub>\<bullet> \<R>\<^sub>\<bullet> r"
  using fbrelation by blast

lemma (in fbrelation) fconverse_eq_frel[intro, simp]:
  assumes "\<And>a b. [a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> r \<Longrightarrow> [b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> r"
  shows "r\<inverse>\<^sub>\<bullet> = r"
  using assms
  apply (intro vsubset_antisym; intro vsubsetI)
  subgoal by blast
  subgoal by (metis fconverseE fconverseI fconverse_fconverse)
  done

lemma fcomp_fconverse_frel_eq_frel_fbrelationI:
  assumes "r\<inverse>\<^sub>\<bullet> \<circ>\<^sub>\<bullet> r = r"
  shows "fbrelation r"
  using assms by (intro fbrelationI, elim vequalityE vsubsetE) force


text\<open>Alternative forms of existing results.\<close>

lemmas [intro, simp] = fbrelation.fconverse_fconverse
  and fconverse_eq_frel[intro, simp] = fbrelation.fconverse_eq_frel

context
  fixes r\<^sub>1 r\<^sub>2
  assumes r\<^sub>1: "fbrelation r\<^sub>1"
    and r\<^sub>2: "fbrelation r\<^sub>2"
begin

lemmas_with[OF fbrelation_pair.intro[OF r\<^sub>1 r\<^sub>2]] :
  fbrelation_fconverse_mono[intro, simp] = fbrelation_pair.fconverse_mono
  and fbrelation_frrestriction_srange[intro, simp] = 
    fbrelation_pair.fconverse_inject

end

text\<open>\newpage\<close>

end