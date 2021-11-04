(*  Title:      JinjaDCI/Compiler/Correctness1.thy
    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   TUM 2003, UIUC 2019-20

    Based on the Jinja theory Compiler/Correctness1.thy by Tobias Nipkow
*)

section \<open> Correctness of Stage 1 \<close>

theory Correctness1
imports J1WellForm Compiler1
begin

subsection\<open>Correctness of program compilation \<close>

primrec unmod :: "expr\<^sub>1 \<Rightarrow> nat \<Rightarrow> bool"
  and unmods :: "expr\<^sub>1 list \<Rightarrow> nat \<Rightarrow> bool" where
"unmod (new C) i = True" |
"unmod (Cast C e) i = unmod e i" |
"unmod (Val v) i = True" |
"unmod (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) i = (unmod e\<^sub>1 i \<and> unmod e\<^sub>2 i)" |
"unmod (Var i) j = True" |
"unmod (i:=e) j = (i \<noteq> j \<and> unmod e j)" |
"unmod (e\<bullet>F{D}) i = unmod e i" |
"unmod (C\<bullet>\<^sub>sF{D}) i = True" |
"unmod (e\<^sub>1\<bullet>F{D}:=e\<^sub>2) i = (unmod e\<^sub>1 i \<and> unmod e\<^sub>2 i)" |
"unmod (C\<bullet>\<^sub>sF{D}:=e\<^sub>2) i = unmod e\<^sub>2 i" |
"unmod (e\<bullet>M(es)) i = (unmod e i \<and> unmods es i)" |
"unmod (C\<bullet>\<^sub>sM(es)) i = unmods es i" |
"unmod {j:T; e} i = unmod e i" |
"unmod (e\<^sub>1;;e\<^sub>2) i = (unmod e\<^sub>1 i \<and>  unmod e\<^sub>2 i)" |
"unmod (if (e) e\<^sub>1 else e\<^sub>2) i = (unmod e i \<and> unmod e\<^sub>1 i \<and> unmod e\<^sub>2 i)" |
"unmod (while (e) c) i = (unmod e i \<and> unmod c i)" |
"unmod (throw e) i = unmod e i" |
"unmod (try e\<^sub>1 catch(C i) e\<^sub>2) j = (unmod e\<^sub>1 j \<and> (if i=j then False else unmod e\<^sub>2 j))" |
"unmod (INIT C (Cs,b) \<leftarrow> e) i = unmod e i" |
"unmod (RI(C,e);Cs \<leftarrow> e') i = (unmod e i \<and> unmod e' i)" |

"unmods ([]) i = True" |
"unmods (e#es) i = (unmod e i \<and> unmods es i)"

lemma hidden_unmod: "\<And>Vs. hidden Vs i \<Longrightarrow> unmod (compE\<^sub>1 Vs e) i" and
 "\<And>Vs. hidden Vs i \<Longrightarrow> unmods (compEs\<^sub>1 Vs es) i"
(*<*)
apply(induct e and es rule: compE\<^sub>1.induct compEs\<^sub>1.induct)
apply (simp_all add:hidden_inacc)
apply(auto simp add:hidden_def)
done
(*>*)


lemma eval\<^sub>1_preserves_unmod:
  "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>e,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>e',(h',ls',sh')\<rangle>; unmod e i; i < size ls \<rbrakk>
  \<Longrightarrow> ls ! i = ls' ! i"
and "\<lbrakk> P \<turnstile>\<^sub>1 \<langle>es,(h,ls,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',ls',sh')\<rangle>; unmods es i; i < size ls \<rbrakk>
      \<Longrightarrow> ls ! i = ls' ! i"
(*<*)
proof(induct rule:eval\<^sub>1_evals\<^sub>1_inducts)
  case (RInitInitFail\<^sub>1 e h l sh a h' l' sh' C sfs i sh'' D Cs e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1)
  have "final (throw a)" using eval\<^sub>1_final[OF RInitInitFail\<^sub>1.hyps(1)] by simp
  then show ?case using RInitInitFail\<^sub>1 by(auto simp: eval\<^sub>1_preserves_len)
qed(auto dest!:eval\<^sub>1_preserves_len evals\<^sub>1_preserves_len split:if_split_asm)
(*>*)


lemma LAss_lem:
  "\<lbrakk>x \<in> set xs; size xs \<le> size ys \<rbrakk>
  \<Longrightarrow> m\<^sub>1 \<subseteq>\<^sub>m m\<^sub>2(xs[\<mapsto>]ys) \<Longrightarrow> m\<^sub>1(x\<mapsto>y) \<subseteq>\<^sub>m m\<^sub>2(xs[\<mapsto>]ys[last_index xs x := y])"
(*<*)
by(simp add:map_le_def fun_upds_apply eq_sym_conv)
(*>*)
lemma Block_lem:
fixes l :: "'a \<rightharpoonup> 'b"
assumes 0: "l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls]"
    and 1: "l' \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V\<mapsto>v]"
    and hidden: "V \<in> set Vs \<Longrightarrow> ls ! last_index Vs V = ls' ! last_index Vs V"
    and size: "size ls = size ls'"    "size Vs < size ls'"
shows "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
(*<*)
proof -
  have "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V\<mapsto>v](V := l V)"
    using 1 by(rule map_le_upd)
  also have "\<dots> = [Vs [\<mapsto>] ls'](V := l V)" by simp
  also have "\<dots> \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
  proof (cases "l V")
    case None thus ?thesis by simp
  next
    case (Some w)
    hence "[Vs [\<mapsto>] ls] V = Some w"
      using 0 by(force simp add: map_le_def split:if_splits)
    hence VinVs: "V \<in> set Vs" and w: "w = ls ! last_index Vs V"
      using size by(auto simp add:fun_upds_apply split:if_splits)
    hence "w = ls' ! last_index Vs V" using hidden[OF VinVs] by simp
    hence "[Vs [\<mapsto>] ls'](V := l V) = [Vs [\<mapsto>] ls']" using Some size VinVs
      by(simp add: map_upds_upd_conv_last_index)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed
(*>*)

(*<*)
declare fun_upd_apply[simp del]
(*>*)


text\<open>\noindent The main theorem: \<close>

theorem assumes wf: "wwf_J_prog P"
shows eval\<^sub>1_eval: "P \<turnstile> \<langle>e,(h,l,sh)\<rangle> \<Rightarrow> \<langle>e',(h',l',sh')\<rangle>
  \<Longrightarrow> (\<And>Vs ls. \<lbrakk> fv e \<subseteq> set Vs;  l \<subseteq>\<^sub>m [Vs[\<mapsto>]ls]; size Vs + max_vars e \<le> size ls \<rbrakk>
       \<Longrightarrow> \<exists>ls'. compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 Vs e,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h',ls',sh')\<rangle> \<and> l' \<subseteq>\<^sub>m [Vs[\<mapsto>]ls'])"
(*<*)
  (is "_ \<Longrightarrow> (\<And>Vs ls. PROP ?P e h l sh e' h' l' sh' Vs ls)"
   is "_ \<Longrightarrow> (\<And>Vs ls. \<lbrakk> _; _; _ \<rbrakk> \<Longrightarrow> \<exists>ls'. ?Post e h l sh e' h' l' sh' Vs ls ls')")
(*>*)

and evals\<^sub>1_evals: "P \<turnstile> \<langle>es,(h,l,sh)\<rangle> [\<Rightarrow>] \<langle>es',(h',l',sh')\<rangle>
    \<Longrightarrow> (\<And>Vs ls. \<lbrakk> fvs es \<subseteq> set Vs;  l \<subseteq>\<^sub>m [Vs[\<mapsto>]ls]; size Vs + max_varss es \<le> size ls \<rbrakk>
         \<Longrightarrow> \<exists>ls'. compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compEs\<^sub>1 Vs es,(h,ls,sh)\<rangle> [\<Rightarrow>] \<langle>compEs\<^sub>1 Vs es',(h',ls',sh')\<rangle> \<and>
                      l' \<subseteq>\<^sub>m [Vs[\<mapsto>]ls'])"
(*<*)
  (is "_ \<Longrightarrow> (\<And>Vs ls. PROP ?Ps es h l sh es' h' l' sh' Vs ls)"
   is "_ \<Longrightarrow> (\<And>Vs ls. \<lbrakk> _; _; _\<rbrakk> \<Longrightarrow> \<exists>ls'. ?Posts es h l sh es' h' l' sh' Vs ls ls')")
proof (induct rule:eval_evals_inducts)
  case Nil thus ?case by(fastforce intro!:Nil\<^sub>1)
next
  case (Cons e h l sh v h' l' sh' es es' h\<^sub>2 l\<^sub>2 sh\<^sub>2)
  have "PROP ?P e h l sh (Val v) h' l' sh' Vs ls" by fact
  with Cons.prems
  obtain ls' where 1: "?Post e h l sh (Val v) h' l' sh' Vs ls ls'"
    "size ls = size ls'" by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?Ps es h' l' sh' es' h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls'" by fact
  with 1 Cons.prems
  obtain ls\<^sub>2 where 2: "?Posts es h' l' sh' es' h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls' ls\<^sub>2" by(auto)
  from 1 2 Cons show ?case by(auto intro!:Cons\<^sub>1)
next
  case ConsThrow thus ?case
    by(fastforce intro!:ConsThrow\<^sub>1 dest: eval_final)
next
  case (Block e h l V sh e' h' l' sh' T)
  let ?Vs = "Vs @ [V]"
  have IH:
  "\<lbrakk>fv e \<subseteq> set ?Vs; l(V := None) \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls];
    size ?Vs + max_vars e \<le> size ls\<rbrakk>
   \<Longrightarrow> \<exists>ls'. compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 ?Vs e,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h', ls',sh')\<rangle> \<and>
             l' \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls']" and
  fv: "fv {V:T; e} \<subseteq> set Vs" and rel: "l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls]" and
  len: "length Vs + max_vars {V:T; e} \<le> length ls" by fact+
  have len': "length Vs < length ls" using len by auto
  have "fv e \<subseteq> set ?Vs" using fv by auto
  moreover have "l(V := None) \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls]" using rel len' by simp
  moreover have "size ?Vs + max_vars e \<le> size ls" using len by simp
  ultimately obtain ls' where
   1: "compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 ?Vs e,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h',ls',sh')\<rangle>"
   and rel': "l' \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls']" using IH by blast
  have [simp]: "length ls = length ls'" by(rule eval\<^sub>1_preserves_len[OF 1])
  show "\<exists>ls'. compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 Vs {V:T; e},(h,ls,sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h',ls',sh')\<rangle>
              \<and> l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']" (is "\<exists>ls'. ?R ls'")
  proof
    show "?R ls'"
    proof
      show "compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 Vs {V:T; e},(h,ls,sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h',ls',sh')\<rangle>"
        using 1 by(simp add:Block\<^sub>1)
    next
      show "l'(V := l V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls']"
      proof -
        have "l' \<subseteq>\<^sub>m [Vs [\<mapsto>] ls', V \<mapsto> ls' ! length Vs]"
          using len' rel' by simp
        moreover
        { assume VinVs: "V \<in> set Vs"
          hence "hidden (Vs @ [V]) (last_index Vs V)"
            by(rule hidden_last_index)
          hence "unmod (compE\<^sub>1 (Vs @ [V]) e) (last_index Vs V)"
            by(rule hidden_unmod)
          moreover have "last_index Vs V < length ls"
            using len' VinVs by simp
          ultimately have "ls ! last_index Vs V = ls' ! last_index Vs V"
            by(rule eval\<^sub>1_preserves_unmod[OF 1])
        }
        ultimately show ?thesis using Block_lem[OF rel] len' by auto
      qed
    qed
  qed
next
  case (TryThrow e' h l sh a h' l' sh' D fs C V e\<^sub>2)
  have "PROP ?P e' h l sh (Throw a) h' l' sh' Vs ls" by fact
  with TryThrow.prems
  obtain ls' where 1: "?Post e' h l sh (Throw a) h' l' sh' Vs ls ls'"  by(auto)
  show ?case using 1 TryThrow.hyps by(auto intro!:eval\<^sub>1_evals\<^sub>1.TryThrow\<^sub>1)
next
  case (TryCatch e\<^sub>1 h l sh a h\<^sub>1 l\<^sub>1 sh\<^sub>1 D fs C e\<^sub>2 V e' h\<^sub>2 l\<^sub>2 sh\<^sub>2)
  let ?e = "try e\<^sub>1 catch(C V) e\<^sub>2"
  have IH\<^sub>1: "\<lbrakk>fv e\<^sub>1 \<subseteq> set Vs; l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls];
              size Vs + max_vars e\<^sub>1 \<le> length ls\<rbrakk>
          \<Longrightarrow> \<exists>ls\<^sub>1. compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 Vs e\<^sub>1,(h,ls,sh)\<rangle> \<Rightarrow>
                                \<langle>fin\<^sub>1 (Throw a),(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle> \<and>
                    l\<^sub>1 \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^sub>1]" and
    fv: "fv ?e \<subseteq> set Vs" and
    rel: "l \<subseteq>\<^sub>m [Vs [\<mapsto>] ls]" and
    len: "length Vs + max_vars ?e \<le> length ls" by fact+
  have "fv e\<^sub>1 \<subseteq> set Vs" using fv by auto
  moreover have "length Vs + max_vars e\<^sub>1 \<le> length ls" using len by(auto)
  ultimately obtain ls\<^sub>1 where
    1: "compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 Vs e\<^sub>1,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>Throw a,(h\<^sub>1,ls\<^sub>1,sh\<^sub>1)\<rangle>"
    and rel\<^sub>1: "l\<^sub>1 \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^sub>1]" using IH\<^sub>1 rel by fastforce
  from 1 have [simp]: "size ls = size ls\<^sub>1" by(rule eval\<^sub>1_preserves_len)
  let ?Vs = "Vs @ [V]" let ?ls = "(ls\<^sub>1[size Vs:=Addr a])"
  have IH\<^sub>2: "\<lbrakk>fv e\<^sub>2 \<subseteq> set ?Vs; l\<^sub>1(V \<mapsto> Addr a) \<subseteq>\<^sub>m [?Vs [\<mapsto>] ?ls];
              length ?Vs + max_vars e\<^sub>2 \<le> length ?ls\<rbrakk> \<Longrightarrow> \<exists>ls\<^sub>2.
       compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 ?Vs e\<^sub>2,(h\<^sub>1,?ls,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle> \<and>
       l\<^sub>2 \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls\<^sub>2]" by fact
  have len\<^sub>1: "size Vs < size ls\<^sub>1" using len by(auto)
  have "fv e\<^sub>2 \<subseteq> set ?Vs" using fv by auto
  moreover have "l\<^sub>1(V \<mapsto> Addr a) \<subseteq>\<^sub>m [?Vs [\<mapsto>] ?ls]" using rel\<^sub>1 len\<^sub>1 by simp
  moreover have "length ?Vs + max_vars e\<^sub>2 \<le> length ?ls" using len by(auto)
  ultimately obtain ls\<^sub>2 where
    2: "compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 ?Vs e\<^sub>2,(h\<^sub>1,?ls,sh\<^sub>1)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h\<^sub>2, ls\<^sub>2, sh\<^sub>2)\<rangle>"
    and rel\<^sub>2: "l\<^sub>2 \<subseteq>\<^sub>m [?Vs [\<mapsto>] ls\<^sub>2]"  using IH\<^sub>2 by blast
  from 2 have [simp]: "size ls\<^sub>1 = size ls\<^sub>2"
    by(fastforce dest: eval\<^sub>1_preserves_len)
  show "\<exists>ls\<^sub>2. compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 Vs ?e,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle> \<and>
              l\<^sub>2(V := l\<^sub>1 V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^sub>2]"  (is "\<exists>ls\<^sub>2. ?R ls\<^sub>2")
  proof
    show "?R ls\<^sub>2"
    proof
      have hp: "h\<^sub>1 a = Some (D, fs)" by fact
      have "P \<turnstile> D \<preceq>\<^sup>* C" by fact hence caught: "compP\<^sub>1 P \<turnstile> D \<preceq>\<^sup>* C" by simp
      from TryCatch\<^sub>1[OF 1 _ caught len\<^sub>1 2, OF hp]
      show "compP\<^sub>1 P \<turnstile>\<^sub>1 \<langle>compE\<^sub>1 Vs ?e,(h,ls,sh)\<rangle> \<Rightarrow> \<langle>fin\<^sub>1 e',(h\<^sub>2,ls\<^sub>2,sh\<^sub>2)\<rangle>" by simp
    next
      show "l\<^sub>2(V := l\<^sub>1 V) \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^sub>2]"
      proof -
        have "l\<^sub>2 \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^sub>2, V \<mapsto> ls\<^sub>2 ! length Vs]"
          using len\<^sub>1 rel\<^sub>2 by simp
        moreover
        { assume VinVs: "V \<in> set Vs"
          hence "hidden (Vs @ [V]) (last_index Vs V)" by(rule hidden_last_index)
          hence "unmod (compE\<^sub>1 (Vs @ [V]) e\<^sub>2) (last_index Vs V)"
            by(rule hidden_unmod)
          moreover have "last_index Vs V < length ?ls"
            using len\<^sub>1 VinVs by simp
          ultimately have "?ls ! last_index Vs V = ls\<^sub>2 ! last_index Vs V"
            by(rule eval\<^sub>1_preserves_unmod[OF 2])
          moreover have "last_index Vs V < size Vs" using VinVs by simp
          ultimately have "ls\<^sub>1 ! last_index Vs V = ls\<^sub>2 ! last_index Vs V"
            using len\<^sub>1 by(simp del:size_last_index_conv)
        }
        ultimately show ?thesis using Block_lem[OF rel\<^sub>1] len\<^sub>1  by simp
      qed
    qed
  qed
next
  case Try thus ?case by(fastforce intro!:Try\<^sub>1)
next
  case Throw thus ?case by(fastforce intro!:Throw\<^sub>1)
next
  case ThrowNull thus ?case by(fastforce intro!:ThrowNull\<^sub>1)
next
  case ThrowThrow thus ?case  by(fastforce intro!:ThrowThrow\<^sub>1)
next
  case (CondT e h l sh h\<^sub>1 l\<^sub>1 sh\<^sub>1 e\<^sub>1 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2 e\<^sub>2)
  have "PROP ?P e h l sh true h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with CondT.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh true h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"  by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 CondT.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 show ?case by(auto intro!:CondT\<^sub>1)
next
  case (CondF e h l sh h\<^sub>1 l\<^sub>1 sh\<^sub>1 e\<^sub>2 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2 e\<^sub>1 Vs ls)
  have "PROP ?P e h l sh false h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with CondF.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh false h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"  by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>2 h\<^sub>1 l\<^sub>1 sh\<^sub>1 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 CondF.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>2 h\<^sub>1 l\<^sub>1 sh\<^sub>1 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 show ?case by(auto intro!:CondF\<^sub>1)
next
  case CondThrow thus ?case by(fastforce intro!:CondThrow\<^sub>1)
next
  case (Seq e h l sh v h\<^sub>1 l\<^sub>1 sh\<^sub>1 e\<^sub>1 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2)
  have "PROP ?P e h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with Seq.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"  by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 Seq.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 e' h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 Seq show ?case by(auto intro!:Seq\<^sub>1)
next
  case SeqThrow thus ?case by(fastforce intro!:SeqThrow\<^sub>1)
next
  case WhileF thus ?case by(fastforce intro!:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (WhileT e h l sh h\<^sub>1 l\<^sub>1 sh\<^sub>1 c v h\<^sub>2 l\<^sub>2 sh\<^sub>2 e' h\<^sub>3 l\<^sub>3 sh\<^sub>3)
  have "PROP ?P e h l sh true h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with WhileT.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh true h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"   by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P c h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 WhileT.prems
  obtain ls\<^sub>2 where 2: "?Post c h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"
    "size ls\<^sub>1 = size ls\<^sub>2"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P (While (e) c) h\<^sub>2 l\<^sub>2 sh\<^sub>2 e' h\<^sub>3 l\<^sub>3 sh\<^sub>3 Vs ls\<^sub>2" by fact
  with 1 2 WhileT.prems
  obtain ls\<^sub>3 where 3: "?Post (While (e) c) h\<^sub>2 l\<^sub>2 sh\<^sub>2 e' h\<^sub>3 l\<^sub>3 sh\<^sub>3 Vs ls\<^sub>2 ls\<^sub>3" by(auto)
  from 1 2 3 show ?case by(auto intro!:WhileT\<^sub>1)
next
  case (WhileBodyThrow e h l sh h\<^sub>1 l\<^sub>1 sh\<^sub>1 c e' h\<^sub>2 l\<^sub>2 sh\<^sub>2)
  have "PROP ?P e h l sh true h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with WhileBodyThrow.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh true h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P c h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw e') h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 WhileBodyThrow.prems
  obtain ls\<^sub>2 where 2: "?Post c h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw e') h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2" by auto
  from 1 2 show ?case by(auto intro!:WhileBodyThrow\<^sub>1)
next
  case WhileCondThrow thus ?case by(fastforce intro!:WhileCondThrow\<^sub>1)
next
  case New thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case NewFail thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case NewInit then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case NewInitOOM then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case NewInitThrow then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case Cast thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case CastNull thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case CastThrow thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (CastFail e h l sh a h\<^sub>1 l\<^sub>1 sh\<^sub>1 D fs C)
  have "PROP ?P e h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with CastFail.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1" by auto
  show ?case using 1 CastFail.hyps
    by(auto intro!:CastFail\<^sub>1[where D=D])
next
  case Val thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (BinOp e h l sh v\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 e\<^sub>1 v\<^sub>2 h\<^sub>2 l\<^sub>2 sh\<^sub>2 bop v)
  have "PROP ?P e h l sh (Val v\<^sub>1) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with BinOp.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (Val v\<^sub>1) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v\<^sub>2) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 BinOp.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v\<^sub>2) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 BinOp show ?case by(auto intro!:BinOp\<^sub>1)
next
  case (BinOpThrow2 e\<^sub>0 h l sh v\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 e\<^sub>1 e h\<^sub>2 l\<^sub>2 sh\<^sub>2 bop)
  have "PROP ?P e\<^sub>0 h l sh (Val v\<^sub>1) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with BinOpThrow2.prems
  obtain ls\<^sub>1 where 1: "?Post e\<^sub>0 h l sh (Val v\<^sub>1) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw e) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 BinOpThrow2.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw e) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 BinOpThrow2 show ?case by(auto intro!:BinOpThrow\<^sub>2\<^sub>1)
next
  case BinOpThrow1 thus ?case  by(fastforce intro!:eval\<^sub>1_evals\<^sub>1.intros)
next
  case Var thus ?case
    by(force intro!:Var\<^sub>1 simp add: map_le_def fun_upds_apply)
next
  case LAss thus ?case
    by(fastforce simp add: LAss_lem intro:eval\<^sub>1_evals\<^sub>1.intros
                dest:eval\<^sub>1_preserves_len)
next
  case LAssThrow thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case FAcc thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case FAccNull thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case FAccThrow thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (FAccNone e h l sh a h' l' sh' C fs F D)
  have "PROP ?P e h l sh (addr a) h' l' sh' Vs ls" by fact
  with FAccNone.prems
  obtain ls\<^sub>2 where 2: "?Post e h l sh (addr a) h' l' sh' Vs ls ls\<^sub>2" by(auto)
  from 2 FAccNone show ?case by(rule_tac x = ls\<^sub>2 in exI, auto elim!: FAccNone\<^sub>1)
next
  case (FAccStatic e h l sh a h' l' sh' C fs F t D)
  have "PROP ?P e h l sh (addr a) h' l' sh' Vs ls" by fact
  with FAccStatic.prems
  obtain ls\<^sub>2 where 2: "?Post e h l sh (addr a) h' l' sh' Vs ls ls\<^sub>2" by(auto)
  from 2 FAccStatic show ?case by(rule_tac x = ls\<^sub>2 in exI, auto elim!: FAccStatic\<^sub>1)
next
  case SFAcc then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (SFAccInit C F t D sh h l v' h' l' sh' sfs i v)
  have "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h l sh (Val v') h' l' sh' Vs ls" by fact
  with SFAccInit.prems
  obtain ls\<^sub>2 where 1: "?Post (INIT D ([D],False) \<leftarrow> unit) h l sh (Val v') h' l' sh' Vs ls ls\<^sub>2" by(auto)
  from 1 SFAccInit show ?case by(rule_tac x = ls\<^sub>2 in exI, auto intro: SFAccInit\<^sub>1)
next
  case (SFAccInitThrow C F t D sh h l a h' l' sh')
  have "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h l sh (throw a) h' l' sh' Vs ls" by fact
  with SFAccInitThrow.prems
  obtain ls\<^sub>2 where 1: "?Post (INIT D ([D],False) \<leftarrow> unit) h l sh (throw a) h' l' sh' Vs ls ls\<^sub>2" by(auto)
  from 1 SFAccInitThrow show ?case by(rule_tac x = ls\<^sub>2 in exI, auto intro: SFAccInitThrow\<^sub>1)
next
  case SFAccNone then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case SFAccNonStatic then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (FAss e\<^sub>1 h l sh a h\<^sub>1 l\<^sub>1 sh\<^sub>1 e\<^sub>2 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs fs' F D h\<^sub>2')
  have "PROP ?P e\<^sub>1 h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with FAss.prems
  obtain ls\<^sub>1 where 1: "?Post e\<^sub>1 h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>2 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 FAss.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>2 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 FAss show ?case by(auto intro!:FAss\<^sub>1)
next
  case (FAssNull e\<^sub>1 h l sh h\<^sub>1 l\<^sub>1 sh\<^sub>1 e\<^sub>2 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 F D)
  have "PROP ?P e\<^sub>1 h l sh null h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with FAssNull.prems
  obtain ls\<^sub>1 where 1: "?Post e\<^sub>1 h l sh null h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>2 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 FAssNull.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>2 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2" by(auto)
  from 1 2 FAssNull show ?case by(auto intro!:FAssNull\<^sub>1)
next
  case FAssThrow1 thus ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (FAssThrow2 e\<^sub>1 h l sh v h\<^sub>1 l\<^sub>1 sh\<^sub>1 e\<^sub>2 e h\<^sub>2 l\<^sub>2 sh\<^sub>2 F D)
  have "PROP ?P e\<^sub>1 h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with FAssThrow2.prems
  obtain ls\<^sub>1 where 1: "?Post e\<^sub>1 h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"   by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>2 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw e) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 FAssThrow2.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>2 h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw e) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 FAssThrow2 show ?case by(auto intro!:FAssThrow\<^sub>2\<^sub>1)
next
  case (FAssNone e\<^sub>1 h l sh a h' l' sh' e\<^sub>2 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs F D)
  have "PROP ?P e\<^sub>1 h l sh (addr a) h' l' sh' Vs ls" by fact
  with FAssNone.prems
  obtain ls\<^sub>1 where 1: "?Post e\<^sub>1 h l sh (addr a) h' l' sh' Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"   by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>2 h' l' sh' (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 FAssNone.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>2 h' l' sh' (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 FAssNone show ?case by(auto intro!:FAssNone\<^sub>1)
next
  case (FAssStatic e\<^sub>1 h l sh a h' l' sh' e\<^sub>2 v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs F t D)
  have "PROP ?P e\<^sub>1 h l sh (addr a) h' l' sh' Vs ls" by fact
  with FAssStatic.prems
  obtain ls\<^sub>1 where 1: "?Post e\<^sub>1 h l sh (addr a) h' l' sh' Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"   by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P e\<^sub>2 h' l' sh' (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 FAssStatic.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>2 h' l' sh' (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"  by(auto)
  from 1 2 FAssStatic show ?case by(auto intro!:FAssStatic\<^sub>1)
next
  case SFAss then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (SFAssInit e\<^sub>2 h l sh v h\<^sub>1 l\<^sub>1 sh\<^sub>1 C F t D v' h' l' sh' sfs i sfs' sh'')
  have "PROP ?P e\<^sub>2 h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with SFAssInit.prems
  obtain ls\<^sub>1 where 1: "?Post e\<^sub>2 h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1" "length ls = length ls\<^sub>1"
    by(auto intro!:eval\<^sub>1_preserves_len)
  then have Init_size: "length Vs \<le> length ls\<^sub>1" using SFAssInit.prems(3) by linarith
  have "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v') h' l' sh' Vs ls\<^sub>1" by fact
  with 1 Init_size SFAssInit.prems
  obtain ls\<^sub>2 where 2: "?Post (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v') h' l' sh' Vs ls\<^sub>1 ls\<^sub>2"
    by auto
  from 1 2 SFAssInit show ?case
    by(auto simp add: comp_def
                intro!: SFAssInit\<^sub>1 dest!:evals_final)
next
  case (SFAssInitThrow e\<^sub>2 h l sh v h\<^sub>1 l\<^sub>1 sh\<^sub>1 C F t D a h\<^sub>2 l\<^sub>2 sh\<^sub>2)
  have "PROP ?P e\<^sub>2 h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with SFAssInitThrow.prems
  obtain ls\<^sub>1 where 1: "?Post e\<^sub>2 h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1" "length ls = length ls\<^sub>1"
    by(auto intro!:eval\<^sub>1_preserves_len)
  then have Init_size: "length Vs \<le> length ls\<^sub>1" using SFAssInitThrow.prems(3) by linarith
  have "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw a) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 Init_size SFAssInitThrow.prems
  obtain ls\<^sub>2 where 2: "?Post (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw a) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"
    by auto
  from 1 2 SFAssInitThrow show ?case
    by(auto simp add: comp_def
                intro!: SFAssInitThrow\<^sub>1 dest!:evals_final)
next
  case SFAssThrow then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (SFAssNone e\<^sub>2 h l sh v h\<^sub>2 l\<^sub>2 sh\<^sub>2 C F D)
  have "PROP ?P e\<^sub>2 h l sh (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls" by fact
  with SFAssNone.prems
  obtain ls\<^sub>2 where 2: "?Post e\<^sub>2 h l sh (Val v) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls ls\<^sub>2" by(auto)
  from 2 SFAssNone show ?case by(rule_tac x = ls\<^sub>2 in exI, auto elim!: SFAssNone\<^sub>1)
next
  case SFAssNonStatic then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (CallNull e h l sh h\<^sub>1 l\<^sub>1 sh\<^sub>1 es vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 M)
  have "PROP ?P e h l sh null h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with CallNull.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh null h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?Ps es h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 CallNull.prems
  obtain ls\<^sub>2 where 2: "?Posts es h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2" by(auto)
  from 1 2 CallNull show ?case
    by (auto simp add: comp_def elim!: CallNull\<^sub>1)
next
  case CallObjThrow thus ?case  by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (CallParamsThrow e h l sh v h\<^sub>1 l\<^sub>1 sh\<^sub>1 es vs ex es' h\<^sub>2 l\<^sub>2 sh\<^sub>2 M)
  have "PROP ?P e h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with CallParamsThrow.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (Val v) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?Ps es h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs @ throw ex # es') h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 CallParamsThrow.prems
  obtain ls\<^sub>2 where 2: "?Posts es h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs @ throw ex # es') h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2" by(auto)
  from 1 2 CallParamsThrow show ?case
    by (auto simp add: comp_def
             elim!: CallParamsThrow\<^sub>1 dest!:evals_final)
next
  case (CallNone e h l sh a h\<^sub>1 l\<^sub>1 sh\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs M)
  have "PROP ?P e h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with CallNone.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?Ps ps h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 CallNone.prems
  obtain ls\<^sub>2 where 2: "?Posts ps h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2" by(auto)
  from 1 2 CallNone show ?case
    by (auto simp add: comp_def
             elim!: CallNone\<^sub>1 dest!:evals_final sees_method_compPD)
next
  case (CallStatic e h l sh a h\<^sub>1 l\<^sub>1 sh\<^sub>1 ps vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs M Ts T pns body D)
  have "PROP ?P e h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with CallStatic.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  let ?Vs = pns
  have mdecl: "P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (pns, body) in D" by fact
  have mdecl\<^sub>1: "compP\<^sub>1 P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (compE\<^sub>1 ?Vs body) in D"
    using sees_method_compP[OF mdecl, of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  have "PROP ?Ps ps h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 CallStatic.prems
  obtain ls\<^sub>2 where 2: "?Posts ps h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2" by(auto)
  from 1 2 mdecl\<^sub>1 CallStatic show ?case
    by (auto simp add: comp_def
             elim!: CallStatic\<^sub>1 dest!:evals_final)
next
  case (Call e h l sh a h\<^sub>1 l\<^sub>1 sh\<^sub>1 es vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C fs M Ts T pns body D l\<^sub>2' b' h\<^sub>3 l\<^sub>3 sh\<^sub>3)
  have "PROP ?P e h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with Call.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (addr a) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?Ps es h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 Call.prems
  obtain ls\<^sub>2 where 2: "?Posts es h\<^sub>1 l\<^sub>1 sh\<^sub>1 (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"
    "size ls\<^sub>1 = size ls\<^sub>2"    by(auto intro!:evals\<^sub>1_preserves_len)
  let ?Vs = "this#pns"
  let ?ls = "Addr a # vs @ replicate (max_vars body) undefined"
  have mdecl: "P \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (pns, body) in D" by fact
  have fv_body: "fv body \<subseteq> set ?Vs" and wf_size: "size Ts = size pns"
    using wf mdecl by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have mdecl\<^sub>1: "compP\<^sub>1 P \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (compE\<^sub>1 ?Vs body) in D"
    using sees_method_compP[OF mdecl, of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  have [simp]: "l\<^sub>2' = [this \<mapsto> Addr a, pns [\<mapsto>] vs]" by fact
  have Call_size: "size vs = size pns" by fact
  have "PROP ?P body h\<^sub>2 l\<^sub>2' sh\<^sub>2 b' h\<^sub>3 l\<^sub>3 sh\<^sub>3 ?Vs ?ls" by fact
  with 1 2 fv_body Call_size Call.prems
  obtain ls\<^sub>3 where 3: "?Post body h\<^sub>2 l\<^sub>2' sh\<^sub>2 b' h\<^sub>3 l\<^sub>3 sh\<^sub>3 ?Vs ?ls ls\<^sub>3"  by(auto)
  have hp: "h\<^sub>2 a = Some (C, fs)" by fact
  from 1 2 3 hp mdecl\<^sub>1 wf_size Call_size show ?case
    by(fastforce simp add: comp_def
                intro!: Call\<^sub>1 dest!:evals_final)
next
  case (SCallParamsThrow es h l sh vs ex es' h\<^sub>2 l\<^sub>2 sh\<^sub>2 C M)
  have "PROP ?Ps es h l sh (map Val vs @ throw ex # es') h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls" by fact
  with SCallParamsThrow.prems
  obtain ls\<^sub>2 where 2: "?Posts es h l sh (map Val vs @ throw ex # es') h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls ls\<^sub>2" by(auto)
  from 2 SCallParamsThrow show ?case
    by (fastforce simp add: comp_def
             elim!: SCallParamsThrow\<^sub>1 dest!:evals_final)
next
  case (SCall ps h l sh vs h\<^sub>2 l\<^sub>2 sh\<^sub>2 C M Ts T pns body D sfs l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3)
  have "PROP ?Ps ps h l sh (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls" by fact
  with SCall.prems
  obtain ls\<^sub>2 where 2: "?Posts ps h l sh (map Val vs) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls ls\<^sub>2"
    "size ls = size ls\<^sub>2"    by(auto intro!:evals\<^sub>1_preserves_len)
  let ?Vs = "pns"
  let ?ls = "vs @ replicate (max_vars body) undefined"
  have mdecl: "P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (pns, body) in D" by fact
  have fv_body: "fv body \<subseteq> set ?Vs" and wf_size: "size Ts = size pns"
    using wf mdecl by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have mdecl\<^sub>1: "compP\<^sub>1 P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (compE\<^sub>1 ?Vs body) in D"
    using sees_method_compP[OF mdecl, of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  have [simp]: "l\<^sub>2' = [pns [\<mapsto>] vs]" by fact
  have SCall_size: "size vs = size pns" by fact
  have "PROP ?P body h\<^sub>2 l\<^sub>2' sh\<^sub>2 e' h\<^sub>3 l\<^sub>3 sh\<^sub>3 ?Vs ?ls" by fact
  with 2 fv_body SCall_size SCall.prems
  obtain ls\<^sub>3 where 3: "?Post body h\<^sub>2 l\<^sub>2' sh\<^sub>2 e' h\<^sub>3 l\<^sub>3 sh\<^sub>3 ?Vs ?ls ls\<^sub>3"  by(auto)
  have shp: "sh\<^sub>2 D = \<lfloor>(sfs, Done)\<rfloor> \<or> M = clinit \<and> sh\<^sub>2 D = \<lfloor>(sfs, Processing)\<rfloor>" by fact
  from 2 3 shp mdecl\<^sub>1 wf_size SCall_size show ?case
    by(fastforce simp add: comp_def
                intro!: SCall\<^sub>1 dest!:evals_final)
next
  case (SCallNone ps h l sh vs h' l' sh' C M)
  have "PROP ?Ps ps h l sh (map Val vs) h' l' sh' Vs ls" by fact
  with SCallNone.prems
  obtain ls\<^sub>2 where 2: "?Posts ps h l sh (map Val vs) h' l' sh' Vs ls ls\<^sub>2" by(auto)
  from 2 SCallNone show ?case
    by(rule_tac x = ls\<^sub>2 in exI,
       auto simp add: comp_def elim!: SCallNone\<^sub>1 dest!:evals_final sees_method_compPD)
next
  case (SCallNonStatic ps h l sh vs h' l' sh' C M Ts T pns body D)
  let ?Vs = "this#pns"
  have mdecl: "P \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (pns, body) in D" by fact
  have mdecl\<^sub>1: "compP\<^sub>1 P \<turnstile> C sees M,NonStatic: Ts\<rightarrow>T = (compE\<^sub>1 ?Vs body) in D"
    using sees_method_compP[OF mdecl, of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  have "PROP ?Ps ps h l sh (map Val vs) h' l' sh' Vs ls" by fact
  with SCallNonStatic.prems
  obtain ls\<^sub>2 where 2: "?Posts ps h l sh (map Val vs) h' l' sh' Vs ls ls\<^sub>2" by(auto)
  from 2 mdecl\<^sub>1 SCallNonStatic show ?case
    by (auto simp add: comp_def
             elim!: SCallNonStatic\<^sub>1 dest!:evals_final)
next
  case (SCallInitThrow ps h l sh vs h\<^sub>1 l\<^sub>1 sh\<^sub>1 C M Ts T pns body D a h\<^sub>2 l\<^sub>2 sh\<^sub>2)
  have "PROP ?Ps ps h l sh (map Val vs) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with SCallInitThrow.prems
  obtain ls\<^sub>1 where 1: "?Posts ps h l sh (map Val vs) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1" "length ls = length ls\<^sub>1"
    by(auto intro!:evals\<^sub>1_preserves_len)
  then have Init_size: "length Vs \<le> length ls\<^sub>1" using SCallInitThrow.prems(3) by linarith
  have "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw a) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 Init_size SCallInitThrow.prems
  obtain ls\<^sub>2 where 2: "?Post (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 l\<^sub>1 sh\<^sub>1 (throw a) h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"
    by auto
  let ?Vs = "pns"
  have mdecl: "P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (pns, body) in D" by fact
  have mdecl\<^sub>1: "compP\<^sub>1 P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (compE\<^sub>1 ?Vs body) in D"
    using sees_method_compP[OF mdecl, of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  from 1 2 mdecl\<^sub>1 SCallInitThrow show ?case
    by(auto simp add: comp_def
                intro!: SCallInitThrow\<^sub>1 dest!:evals_final)
next
  case (SCallInit ps h l sh vs h\<^sub>1 l\<^sub>1 sh\<^sub>1 C M Ts T pns body D v' h\<^sub>2 l\<^sub>2 sh\<^sub>2 l\<^sub>2' e' h\<^sub>3 l\<^sub>3 sh\<^sub>3)
  have "PROP ?Ps ps h l sh (map Val vs) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls" by fact
  with SCallInit.prems
  obtain ls\<^sub>1 where 1: "?Posts ps h l sh (map Val vs) h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls ls\<^sub>1" "length ls = length ls\<^sub>1"
    by(auto intro!:evals\<^sub>1_preserves_len)
  then have Init_size: "length Vs \<le> length ls\<^sub>1" using SCallInit.prems(3) by linarith
  have "PROP ?P (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v') h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1" by fact
  with 1 Init_size SCallInit.prems
  obtain ls\<^sub>2 where 2: "?Post (INIT D ([D],False) \<leftarrow> unit) h\<^sub>1 l\<^sub>1 sh\<^sub>1 (Val v') h\<^sub>2 l\<^sub>2 sh\<^sub>2 Vs ls\<^sub>1 ls\<^sub>2"
    by auto
  let ?Vs = "pns"
  let ?ls = "vs @ replicate (max_vars body) undefined"
  have mdecl: "P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (pns, body) in D" by fact
  have fv_body: "fv body \<subseteq> set ?Vs" and wf_size: "size Ts = size pns"
    using wf mdecl by(auto dest!:sees_wf_mdecl simp:wf_mdecl_def)
  have mdecl\<^sub>1: "compP\<^sub>1 P \<turnstile> C sees M,Static: Ts\<rightarrow>T = (compE\<^sub>1 ?Vs body) in D"
    using sees_method_compP[OF mdecl, of "\<lambda>b (pns,e). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) e"]
    by(simp)
  have [simp]: "l\<^sub>2' = [pns [\<mapsto>] vs]" by fact
  have SCall_size: "size vs = size pns" by fact
  have nclinit: "M \<noteq> clinit" by fact
  have "PROP ?P body h\<^sub>2 l\<^sub>2' sh\<^sub>2 e' h\<^sub>3 l\<^sub>3 sh\<^sub>3 ?Vs ?ls" by fact
  with 2 fv_body SCall_size SCallInit.prems
  obtain ls\<^sub>3 where 3: "?Post body h\<^sub>2 l\<^sub>2' sh\<^sub>2 e' h\<^sub>3 l\<^sub>3 sh\<^sub>3 ?Vs ?ls ls\<^sub>3"  by(auto)
  have shp: "\<nexists>sfs. sh\<^sub>1 D = \<lfloor>(sfs, Done)\<rfloor>" by fact
  from 1 2 3 shp mdecl\<^sub>1 wf_size SCall_size nclinit show ?case
    by(auto simp add: comp_def
                intro!: SCallInit\<^sub>1 dest!:evals_final)
next
\<comment> \<open> init cases \<close>
  case InitFinal then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (InitNone sh C C' Cs e h l e' h' l' sh')
  let ?sh1 = "sh(C \<mapsto> (sblank P C, Prepared))"
  have "PROP ?P (INIT C' (C # Cs,False) \<leftarrow> e) h l ?sh1 e' h' l' sh' Vs ls" by fact
  with InitNone.prems
  obtain ls\<^sub>2 where 2: "?Post (INIT C' (C # Cs,False) \<leftarrow> e) h l ?sh1 e' h' l' sh' Vs ls ls\<^sub>2" by(auto)
  from 2 InitNone show ?case by (auto elim!: InitNone\<^sub>1)
next
  case InitDone then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case InitProcessing then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case InitError then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case InitObject then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (InitNonObject sh C sfs D fs ms sh' C' Cs e h l e' h1 l1 sh1)
  let ?f = "(\<lambda>b (pns,body). compE\<^sub>1 (case b of NonStatic \<Rightarrow> this#pns | Static \<Rightarrow> pns) body)"
  have cls: "class (compP ?f P) C = \<lfloor>(D,fs,map (compM ?f) ms)\<rfloor>"
    by(rule class_compP[OF InitNonObject.hyps(3)])
  have "PROP ?P (INIT C' (D # C # Cs,False) \<leftarrow> e) h l sh' e' h1 l1 sh1 Vs ls" by fact
  with InitNonObject.prems
  obtain ls\<^sub>2 where 2: "?Post (INIT C' (D # C # Cs,False) \<leftarrow> e) h l sh' e' h1 l1 sh1 Vs ls ls\<^sub>2" by(auto)
  from 2 cls InitNonObject show ?case by (auto elim!: InitNonObject\<^sub>1)
next
  case InitRInit then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
next
  case (RInit e h l sh v h' l' sh' C sfs i sh'' C' Cs e' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1)
  have "PROP ?P e h l sh (Val v) h' l' sh' Vs ls" by fact
  with RInit.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (Val v) h' l' sh' Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have "PROP ?P (INIT C' (Cs,True) \<leftarrow> e') h' l' sh'' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls\<^sub>1" by fact
  with 1 RInit.prems
  obtain ls\<^sub>2 where 2: "?Post (INIT C' (Cs,True) \<leftarrow> e') h' l' sh'' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls\<^sub>1 ls\<^sub>2" by(auto)
  from 1 2 RInit show ?case by (auto elim!: RInit\<^sub>1)
next
  case (RInitInitFail e h l sh a h' l' sh' C sfs i sh'' D Cs e' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1)
  have "PROP ?P e h l sh (throw a) h' l' sh' Vs ls" by fact
  with RInitInitFail.prems
  obtain ls\<^sub>1 where 1: "?Post e h l sh (throw a) h' l' sh' Vs ls ls\<^sub>1"
    "size ls = size ls\<^sub>1"    by(auto intro!:eval\<^sub>1_preserves_len)
  have fv: "fv (RI (D,throw a) ; Cs \<leftarrow> e') \<subseteq> set Vs"
    using RInitInitFail.hyps(1) eval_final RInitInitFail.prems(1) subset_eq by fastforce
  have l': "l' \<subseteq>\<^sub>m [Vs [\<mapsto>] ls\<^sub>1]" by (simp add: "1"(1))
  have "PROP ?P (RI (D,throw a) ; Cs \<leftarrow> e') h' l' sh'' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls\<^sub>1" by fact
  with 1 eval_final[OF RInitInitFail.hyps(1)] RInitInitFail.prems
  obtain ls\<^sub>2 where 2: "?Post (RI (D,throw a) ; Cs \<leftarrow> e') h' l' sh'' e\<^sub>1 h\<^sub>1 l\<^sub>1 sh\<^sub>1 Vs ls\<^sub>1 ls\<^sub>2"
    by fastforce
  from 1 2 RInitInitFail show ?case
    by(fastforce simp add: comp_def
                intro!: RInitInitFail\<^sub>1 dest!:eval_final)
next
  case RInitFailFinal then show ?case by(fastforce intro:eval\<^sub>1_evals\<^sub>1.intros)
qed
(*>*)


subsection\<open>Preservation of well-formedness\<close>

text\<open> The compiler preserves well-formedness. Is less trivial than it
may appear. We start with two simple properties: preservation of
well-typedness \<close>

lemma compE\<^sub>1_pres_wt: "\<And>Vs Ts U.
  \<lbrakk> P,[Vs[\<mapsto>]Ts] \<turnstile> e :: U; size Ts = size Vs \<rbrakk>
  \<Longrightarrow> compP f P,Ts \<turnstile>\<^sub>1 compE\<^sub>1 Vs e :: U"
and  "\<And>Vs Ts Us.
  \<lbrakk> P,[Vs[\<mapsto>]Ts] \<turnstile> es [::] Us; size Ts = size Vs \<rbrakk>
  \<Longrightarrow> compP f P,Ts \<turnstile>\<^sub>1 compEs\<^sub>1 Vs es [::] Us"
(*<*)
apply(induct e and es rule: compE\<^sub>1.induct compEs\<^sub>1.induct)
apply clarsimp
apply(fastforce)
apply clarsimp
apply(fastforce split:bop.splits)
apply (fastforce simp:map_upds_apply_eq_Some split:if_split_asm)
apply (fastforce simp:map_upds_apply_eq_Some split:if_split_asm)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply(fastforce)
apply (fastforce dest!: sees_method_compP[where f = f])
apply (fastforce dest!: sees_method_compP[where f = f])
apply (fastforce simp:nth_append)
apply (fastforce)
apply (fastforce)
apply (fastforce)
apply (fastforce)
apply (fastforce simp:nth_append)
apply simp
apply simp
apply simp
apply (fastforce)
done
(*>*)

text\<open>\noindent and the correct block numbering: \<close>

lemma \<B>: "\<And>Vs n. size Vs = n \<Longrightarrow> \<B> (compE\<^sub>1 Vs e) n"
and \<B>s: "\<And>Vs n. size Vs = n \<Longrightarrow> \<B>s (compEs\<^sub>1 Vs es) n"
(*<*)by (induct e and es rule: \<B>.induct \<B>s.induct)
        (force | simp,metis length_append_singleton)+(*>*)

text\<open> The main complication is preservation of definite assignment
@{term"\<D>"}. \<close>

lemma image_last_index: "A \<subseteq> set(xs@[x]) \<Longrightarrow> last_index (xs @ [x]) ` A =
  (if x \<in> A then insert (size xs) (last_index xs ` (A-{x})) else last_index xs ` A)"
(*<*)
by(auto simp:image_def)
(*>*)


lemma A_compE\<^sub>1_None[simp]:
      "\<And>Vs. \<A> e = None \<Longrightarrow> \<A> (compE\<^sub>1 Vs e) = None"
and "\<And>Vs. \<A>s es = None \<Longrightarrow> \<A>s (compEs\<^sub>1 Vs es) = None"
(*<*)by(induct e and es rule: compE\<^sub>1.induct compEs\<^sub>1.induct)(auto simp:hyperset_defs)(*>*)


lemma A_compE\<^sub>1:
      "\<And>A Vs. \<lbrakk> \<A> e = \<lfloor>A\<rfloor>; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<A> (compE\<^sub>1 Vs e) = \<lfloor>last_index Vs ` A\<rfloor>"
and "\<And>A Vs. \<lbrakk> \<A>s es = \<lfloor>A\<rfloor>; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow> \<A>s (compEs\<^sub>1 Vs es) = \<lfloor>last_index Vs ` A\<rfloor>"
(*<*)
proof(induct e and es rule: fv.induct fvs.induct)
  case (Block V' T e)
  hence "fv e \<subseteq> set (Vs@[V'])" by fastforce
  moreover obtain B where "\<A> e = \<lfloor>B\<rfloor>"
    using Block.prems by(simp add: hyperset_defs)
  moreover from calculation have "B \<subseteq> set (Vs@[V'])" by(auto dest!:A_fv)
  ultimately show ?case using Block
    by(auto simp add: hyperset_defs image_last_index last_index_size_conv)
next
  case (TryCatch e\<^sub>1 C V' e\<^sub>2)
  hence fve\<^sub>2: "fv e\<^sub>2 \<subseteq> set (Vs@[V'])" by auto
  show ?case
  proof (cases "\<A> e\<^sub>1")
    assume A\<^sub>1: "\<A> e\<^sub>1 = None"
    then obtain A\<^sub>2 where A\<^sub>2: "\<A> e\<^sub>2 = \<lfloor>A\<^sub>2\<rfloor>" using TryCatch
      by(simp add:hyperset_defs)
    hence "A\<^sub>2 \<subseteq> set (Vs@[V'])" using TryCatch.prems A_fv[OF A\<^sub>2] by simp blast
    thus ?thesis using TryCatch fve\<^sub>2 A\<^sub>1 A\<^sub>2
      by(auto simp add:hyperset_defs image_last_index last_index_size_conv)
  next
    fix A\<^sub>1 assume A\<^sub>1: "\<A> e\<^sub>1 =  \<lfloor>A\<^sub>1\<rfloor>"
    show ?thesis
    proof (cases  "\<A> e\<^sub>2")
      assume A\<^sub>2: "\<A> e\<^sub>2 = None"
      then show ?case using TryCatch A\<^sub>1 by(simp add:hyperset_defs)
    next
      fix A\<^sub>2 assume A\<^sub>2: "\<A> e\<^sub>2 = \<lfloor>A\<^sub>2\<rfloor>"
      have "A\<^sub>1 \<subseteq> set Vs" using TryCatch.prems A_fv[OF A\<^sub>1] by simp blast
      moreover
      have "A\<^sub>2 \<subseteq> set (Vs@[V'])" using TryCatch.prems A_fv[OF A\<^sub>2] by simp blast
      ultimately show ?thesis using TryCatch A\<^sub>1 A\<^sub>2
        by (auto simp add: Diff_subset_conv last_index_size_conv subsetD hyperset_defs
                 dest!: sym [of _ A])
    qed
  qed
next
  case (Cond e e\<^sub>1 e\<^sub>2)
  { assume "\<A> e = None \<or> \<A> e\<^sub>1 = None \<or> \<A> e\<^sub>2 = None"
    hence ?case using Cond by(auto simp add:hyperset_defs image_Un)
  }
  moreover
  { fix A A\<^sub>1 A\<^sub>2
    assume "\<A> e = \<lfloor>A\<rfloor>" and A\<^sub>1: "\<A> e\<^sub>1 = \<lfloor>A\<^sub>1\<rfloor>" and A\<^sub>2: "\<A> e\<^sub>2 = \<lfloor>A\<^sub>2\<rfloor>"
    moreover
    have "A\<^sub>1 \<subseteq> set Vs" using Cond.prems A_fv[OF A\<^sub>1] by simp blast
    moreover
    have "A\<^sub>2 \<subseteq> set Vs" using Cond.prems A_fv[OF A\<^sub>2] by simp blast
    ultimately have ?case using Cond
      by(auto simp add:hyperset_defs image_Un
          inj_on_image_Int[OF inj_on_last_index])
  }
  ultimately show ?case by fastforce
qed (auto simp add:hyperset_defs)
(*>*)


lemma D_None[iff]: "\<D> (e::'a exp) None" and [iff]: "\<D>s (es::'a exp list) None"
(*<*)by(induct e and es rule: \<D>.induct \<D>s.induct)(simp_all)(*>*)


lemma D_last_index_compE\<^sub>1:
      "\<And>A Vs. \<lbrakk> A \<subseteq> set Vs; fv e \<subseteq> set Vs \<rbrakk> \<Longrightarrow>
                \<D> e \<lfloor>A\<rfloor> \<Longrightarrow> \<D> (compE\<^sub>1 Vs e) \<lfloor>last_index Vs ` A\<rfloor>"
and "\<And>A Vs. \<lbrakk> A \<subseteq> set Vs; fvs es \<subseteq> set Vs \<rbrakk> \<Longrightarrow>
                \<D>s es \<lfloor>A\<rfloor> \<Longrightarrow> \<D>s (compEs\<^sub>1 Vs es) \<lfloor>last_index Vs ` A\<rfloor>"
(*<*)
proof(induct e and es rule: \<D>.induct \<D>s.induct)
  case (BinOp e\<^sub>1 bop e\<^sub>2)
  hence IH\<^sub>1: "\<D> (compE\<^sub>1 Vs e\<^sub>1) \<lfloor>last_index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^sub>1")
    case None thus ?thesis using BinOp by simp
  next
    case (Some A\<^sub>1)
    have indexA\<^sub>1: "\<A> (compE\<^sub>1 Vs e\<^sub>1) = \<lfloor>last_index Vs ` A\<^sub>1\<rfloor>"
      using A_compE\<^sub>1[OF Some] BinOp.prems  by auto
    have "A \<union> A\<^sub>1 \<subseteq> set Vs" using BinOp.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` (A \<union> A\<^sub>1)\<rfloor>" using BinOp Some by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` A \<union> last_index Vs ` A\<^sub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^sub>1 indexA\<^sub>1 by auto
  qed
next
  case (FAss e\<^sub>1 F D e\<^sub>2)
  hence IH\<^sub>1: "\<D> (compE\<^sub>1 Vs e\<^sub>1) \<lfloor>last_index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^sub>1")
    case None thus ?thesis using FAss by simp
  next
    case (Some A\<^sub>1)
    have indexA\<^sub>1: "\<A> (compE\<^sub>1 Vs e\<^sub>1) = \<lfloor>last_index Vs ` A\<^sub>1\<rfloor>"
      using A_compE\<^sub>1[OF Some] FAss.prems  by auto
    have "A \<union> A\<^sub>1 \<subseteq> set Vs" using FAss.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` (A \<union> A\<^sub>1)\<rfloor>" using FAss Some by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` A \<union> last_index Vs ` A\<^sub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^sub>1 indexA\<^sub>1 by auto
  qed
next
  case (Call e\<^sub>1 M es)
  hence IH\<^sub>1: "\<D> (compE\<^sub>1 Vs e\<^sub>1) \<lfloor>last_index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^sub>1")
    case None thus ?thesis using Call by simp
  next
    case (Some A\<^sub>1)
    have indexA\<^sub>1: "\<A> (compE\<^sub>1 Vs e\<^sub>1) = \<lfloor>last_index Vs ` A\<^sub>1\<rfloor>"
      using A_compE\<^sub>1[OF Some] Call.prems  by auto
    have "A \<union> A\<^sub>1 \<subseteq> set Vs" using Call.prems A_fv[OF Some] by auto
    hence "\<D>s (compEs\<^sub>1 Vs es) \<lfloor>last_index Vs ` (A \<union> A\<^sub>1)\<rfloor>" using Call Some by auto
    hence "\<D>s (compEs\<^sub>1 Vs es) \<lfloor>last_index Vs ` A \<union> last_index Vs ` A\<^sub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^sub>1 indexA\<^sub>1 by auto
  qed
next
  case (TryCatch e\<^sub>1 C V e\<^sub>2)
  have "\<lbrakk> A\<union>{V} \<subseteq> set(Vs@[V]); fv e\<^sub>2 \<subseteq> set(Vs@[V]); \<D> e\<^sub>2 \<lfloor>A\<union>{V}\<rfloor>\<rbrakk> \<Longrightarrow>
        \<D> (compE\<^sub>1 (Vs@[V]) e\<^sub>2) \<lfloor>last_index (Vs@[V]) ` (A\<union>{V})\<rfloor>" by fact
  hence "\<D> (compE\<^sub>1 (Vs@[V]) e\<^sub>2) \<lfloor>last_index (Vs@[V]) ` (A\<union>{V})\<rfloor>"
    using TryCatch.prems by(simp add:Diff_subset_conv)
  moreover have "last_index (Vs@[V]) ` A \<subseteq> last_index Vs ` A \<union> {size Vs}"
    using TryCatch.prems by(auto simp add: image_last_index split:if_split_asm)
  ultimately show ?case using TryCatch
    by(auto simp:hyperset_defs elim!:D_mono')
next
  case (Seq e\<^sub>1 e\<^sub>2)
  hence IH\<^sub>1: "\<D> (compE\<^sub>1 Vs e\<^sub>1) \<lfloor>last_index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^sub>1")
    case None thus ?thesis using Seq by simp
  next
    case (Some A\<^sub>1)
    have indexA\<^sub>1: "\<A> (compE\<^sub>1 Vs e\<^sub>1) = \<lfloor>last_index Vs ` A\<^sub>1\<rfloor>"
      using A_compE\<^sub>1[OF Some] Seq.prems  by auto
    have "A \<union> A\<^sub>1 \<subseteq> set Vs" using Seq.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` (A \<union> A\<^sub>1)\<rfloor>" using Seq Some by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` A \<union> last_index Vs ` A\<^sub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^sub>1 indexA\<^sub>1 by auto
  qed
next
  case (Cond e e\<^sub>1 e\<^sub>2)
  hence IH\<^sub>1: "\<D> (compE\<^sub>1 Vs e) \<lfloor>last_index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e")
    case None thus ?thesis using Cond by simp
  next
    case (Some B)
    have indexB: "\<A> (compE\<^sub>1 Vs e) = \<lfloor>last_index Vs ` B\<rfloor>"
      using A_compE\<^sub>1[OF Some] Cond.prems  by auto
    have "A \<union> B \<subseteq> set Vs" using Cond.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>1) \<lfloor>last_index Vs ` (A \<union> B)\<rfloor>"
      and "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` (A \<union> B)\<rfloor>"
      using Cond Some by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>1) \<lfloor>last_index Vs ` A \<union> last_index Vs ` B\<rfloor>"
      and "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` A \<union> last_index Vs ` B\<rfloor>"
      by(simp add: image_Un)+
    thus ?thesis using IH\<^sub>1 indexB by auto
  qed
next
  case (While e\<^sub>1 e\<^sub>2)
  hence IH\<^sub>1: "\<D> (compE\<^sub>1 Vs e\<^sub>1) \<lfloor>last_index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^sub>1")
    case None thus ?thesis using While by simp
  next
    case (Some A\<^sub>1)
    have indexA\<^sub>1: "\<A> (compE\<^sub>1 Vs e\<^sub>1) = \<lfloor>last_index Vs ` A\<^sub>1\<rfloor>"
      using A_compE\<^sub>1[OF Some] While.prems  by auto
    have "A \<union> A\<^sub>1 \<subseteq> set Vs" using While.prems A_fv[OF Some] by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` (A \<union> A\<^sub>1)\<rfloor>" using While Some by auto
    hence "\<D> (compE\<^sub>1 Vs e\<^sub>2) \<lfloor>last_index Vs ` A \<union> last_index Vs ` A\<^sub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^sub>1 indexA\<^sub>1 by auto
  qed
next
  case (Block V T e)
  have "\<lbrakk> A-{V} \<subseteq> set(Vs@[V]); fv e \<subseteq> set(Vs@[V]); \<D> e \<lfloor>A-{V}\<rfloor> \<rbrakk> \<Longrightarrow>
        \<D> (compE\<^sub>1 (Vs@[V]) e) \<lfloor>last_index (Vs@[V]) ` (A-{V})\<rfloor>" by fact
  hence "\<D> (compE\<^sub>1 (Vs@[V]) e) \<lfloor>last_index (Vs@[V]) ` (A-{V})\<rfloor>"
    using Block.prems by(simp add:Diff_subset_conv)
  moreover have "size Vs \<notin> last_index Vs ` A"
    using Block.prems by(auto simp add:image_def size_last_index_conv)
  ultimately show ?case using Block
    by(auto simp add: image_last_index Diff_subset_conv hyperset_defs elim!: D_mono')
next
  case (Cons_exp e\<^sub>1 es)
  hence IH\<^sub>1: "\<D> (compE\<^sub>1 Vs e\<^sub>1) \<lfloor>last_index Vs ` A\<rfloor>" by simp
  show ?case
  proof (cases "\<A> e\<^sub>1")
    case None thus ?thesis using Cons_exp by simp
  next
    case (Some A\<^sub>1)
    have indexA\<^sub>1: "\<A> (compE\<^sub>1 Vs e\<^sub>1) = \<lfloor>last_index Vs ` A\<^sub>1\<rfloor>"
      using A_compE\<^sub>1[OF Some] Cons_exp.prems  by auto
    have "A \<union> A\<^sub>1 \<subseteq> set Vs" using Cons_exp.prems A_fv[OF Some] by auto
    hence "\<D>s (compEs\<^sub>1 Vs es) \<lfloor>last_index Vs ` (A \<union> A\<^sub>1)\<rfloor>" using Cons_exp Some by auto
    hence "\<D>s (compEs\<^sub>1 Vs es) \<lfloor>last_index Vs ` A \<union> last_index Vs ` A\<^sub>1\<rfloor>"
      by(simp add: image_Un)
    thus ?thesis using IH\<^sub>1 indexA\<^sub>1 by auto
  qed
qed (simp_all add:hyperset_defs)
(*>*)


lemma last_index_image_set: "distinct xs \<Longrightarrow> last_index xs ` set xs = {..<size xs}"
(*<*)by(induct xs rule:rev_induct) (auto simp add: image_last_index)(*>*)


lemma D_compE\<^sub>1:
  "\<lbrakk> \<D> e \<lfloor>set Vs\<rfloor>; fv e \<subseteq> set Vs; distinct Vs \<rbrakk> \<Longrightarrow> \<D> (compE\<^sub>1 Vs e) \<lfloor>{..<length Vs}\<rfloor>"
(*<*)by(fastforce dest!: D_last_index_compE\<^sub>1[OF subset_refl] simp add:last_index_image_set)(*>*)


lemma D_compE\<^sub>1':
assumes "\<D> e \<lfloor>set(V#Vs)\<rfloor>" and "fv e \<subseteq> set(V#Vs)" and "distinct(V#Vs)"
shows "\<D> (compE\<^sub>1 (V#Vs) e) \<lfloor>{..length Vs}\<rfloor>"
(*<*)
proof -
  have "{..size Vs} = {..<size(V#Vs)}" by auto
  thus ?thesis using assms by (simp only:)(rule D_compE\<^sub>1)
qed
(*>*)

lemma compP\<^sub>1_pres_wf: "wf_J_prog P \<Longrightarrow> wf_J\<^sub>1_prog (compP\<^sub>1 P)"
(*<*)
apply simp
apply(rule wf_prog_compPI)
 prefer 2 apply assumption
apply(case_tac m)
apply(simp add:wf_mdecl_def wf_J\<^sub>1_mdecl_def)
apply(clarify) apply(rename_tac C M b Ts T x1 x2 pns body)
apply(case_tac b)
 apply clarsimp
 apply(frule WT_fv)
 apply(auto intro!: compE\<^sub>1_pres_wt D_compE\<^sub>1 \<B>)[1]
apply clarsimp
apply(frule WT_fv)
apply(fastforce intro!: compE\<^sub>1_pres_wt D_compE\<^sub>1' \<B>)
done
(*>*)


end
