(*  Title:      JinjaDCI/JVM/JVMExceptions.thy
    Author:     Gerwin Klein, Martin Strecker, Susannah Mansky
    Copyright   2001 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory JVM/JVMExceptions.thy by Gerwin Klein and Martin Strecker
*)

section \<open> Exception handling in the JVM \<close>

theory JVMExceptions imports "../Common/Exceptions" JVMInstructions
begin

definition matches_ex_entry :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool"
where
  "matches_ex_entry P C pc xcp \<equiv>
                 let (s, e, C', h, d) = xcp in
                 s \<le> pc \<and> pc < e \<and> P \<turnstile> C \<preceq>\<^sup>* C'"


primrec match_ex_table :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> (pc \<times> nat) option"
where
  "match_ex_table P C pc []     = None"
| "match_ex_table P C pc (e#es) = (if matches_ex_entry P C pc e
                                   then Some (snd(snd(snd e)))
                                   else match_ex_table P C pc es)"

abbreviation
  ex_table_of :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table" where
  "ex_table_of P C M == snd (snd (snd (snd (snd (snd (snd (method P C M)))))))"


fun find_handler :: "jvm_prog \<Rightarrow> addr \<Rightarrow> heap \<Rightarrow> frame list \<Rightarrow> sheap \<Rightarrow> jvm_state"
where
  "find_handler P a h [] sh = (Some a, h, [], sh)"
| "find_handler P a h (fr#frs) sh = 
       (let (stk,loc,C,M,pc,ics) = fr in
         case match_ex_table P (cname_of h a) pc (ex_table_of P C M) of
           None \<Rightarrow> 
              (case M = clinit of
                 True \<Rightarrow> (case frs of (stk',loc',C',M',pc',ics')#frs'
                                  \<Rightarrow> (case ics' of Called Cs \<Rightarrow> (None, h, (stk',loc',C',M',pc',Throwing (C#Cs) a)#frs', sh)
                                                 | _ \<Rightarrow> (None, h, (stk',loc',C',M',pc',ics')#frs', sh) \<comment> \<open>this won't happen in wf code\<close>
                                     )
                              | [] \<Rightarrow> (Some a, h, [], sh)
                    )
               | _ \<Rightarrow> find_handler P a h frs sh
              )
         | Some pc_d \<Rightarrow> (None, h, (Addr a # drop (size stk - snd pc_d) stk, loc, C, M, fst pc_d, No_ics)#frs, sh))"

lemma find_handler_cases:
 "find_handler P a h frs sh = js
  \<Longrightarrow> (\<exists>frs'. frs' \<noteq> [] \<and> js = (None, h, frs', sh)) \<or> (js = (Some a, h, [], sh))"
proof(induct P a h frs sh rule: find_handler.induct)
  case 1 then show ?case by clarsimp
next
  case (2 P a h fr frs sh) then show ?case
    by(cases fr, auto split: bool.splits list.splits init_call_status.splits)
qed

lemma find_handler_heap[simp]:
"find_handler P a h frs sh = (xp',h',frs',sh') \<Longrightarrow> h' = h"
 by(auto dest: find_handler_cases)

lemma find_handler_sheap[simp]:
"find_handler P a h frs sh = (xp',h',frs',sh') \<Longrightarrow> sh' = sh"
 by(auto dest: find_handler_cases)

lemma find_handler_frames[simp]:
"find_handler P a h frs sh = (xp',h',frs',sh') \<Longrightarrow> length frs' \<le> length frs"
proof(induct frs)
  case Nil then show ?case by simp
next
  case (Cons a frs) then show ?case
    by(auto simp: split_beta split: bool.splits list.splits init_call_status.splits)
qed

lemma find_handler_None:
 "find_handler P a h frs sh = (None, h, frs', sh') \<Longrightarrow> frs' \<noteq> []"
 by (drule find_handler_cases, clarsimp)

lemma find_handler_Some:
 "find_handler P a h frs sh = (Some x, h, frs', sh') \<Longrightarrow> frs' = []"
 by (drule find_handler_cases, clarsimp)

lemma find_handler_Some_same_error_same_heap[simp]:
 "find_handler P a h frs sh = (Some x, h', frs', sh') \<Longrightarrow> x = a \<and> h = h' \<and> sh = sh'"
 by(auto dest: find_handler_cases)

lemma find_handler_prealloc_pres:
assumes "preallocated h"
and fh: "find_handler P a h frs sh = (xp',h',frs',sh')"
shows "preallocated h'"
using assms find_handler_heap[OF fh] by simp

lemma find_handler_frs_tl_neq:
 "ics_of f \<noteq> No_ics
  \<Longrightarrow> (xp, h, f#frs, sh) \<noteq> find_handler P xa h' (f' # frs) sh'"
proof(induct frs arbitrary: f f')
  case Nil then show ?case by(auto simp: split_beta split: bool.splits)
next
  case (Cons a frs)
  obtain xp1 h1 frs1 sh1 where fh: "find_handler P xa h' (a # frs) sh' = (xp1,h1,frs1,sh1)"
   by(cases "find_handler P xa h' (a # frs) sh'")
  then have "length frs1 \<le> length (a#frs)"
    by(rule find_handler_frames[where P=P and a=xa and h=h' and frs="a#frs" and sh=sh'])
  then have neq: "f#a#frs \<noteq> frs1" by(clarsimp dest: impossible_Cons)
  then show ?case
  proof(cases "find_handler P xa h' (f' # a # frs) sh' = find_handler P xa h' (a # frs) sh'")
    case True then show ?thesis using neq fh by simp
  next
    case False then show ?thesis using Cons.prems
      by(fastforce simp: split_beta split: bool.splits init_call_status.splits list.splits)
  qed
qed

end
