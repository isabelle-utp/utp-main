(* Title: RTS/Common/RTS_safe.thy *)
(* Author: Susannah Mansky, UIUC 2020 *)

section "Regression Test Selection algorithm model"

theory RTS_safe
imports Main
begin

text \<open> This describes an \emph{existence safe} RTS algorithm: if a test
 is deselected based on an output, there is SOME equivalent output
 under the changed program. \<close>
locale RTS_safe =
 fixes
  out :: "'prog \<Rightarrow> 'test \<Rightarrow> 'prog_out set" and
  equiv_out :: "'prog_out \<Rightarrow> 'prog_out \<Rightarrow> bool" and
  deselect :: "'prog \<Rightarrow> 'prog_out \<Rightarrow> 'prog \<Rightarrow> bool" and
  progs :: "'prog set" and
  tests :: "'test set"
 assumes
  existence_safe: "\<lbrakk> P \<in> progs; P' \<in> progs; t \<in> tests; o1 \<in> out P t; deselect P o1 P' \<rbrakk>
   \<Longrightarrow> (\<exists>o2 \<in> out P' t. equiv_out o1 o2)" and
  equiv_out_equiv: "equiv UNIV {(x,y). equiv_out x y}" and
  equiv_out_deselect: "\<lbrakk> equiv_out o1 o2; deselect P o1 P' \<rbrakk> \<Longrightarrow> deselect P o2 P'"

context RTS_safe begin

lemma equiv_out_refl: "equiv_out a a"
using equiv_class_eq_iff equiv_out_equiv by fastforce

lemma equiv_out_trans: "\<lbrakk> equiv_out a b; equiv_out b c \<rbrakk> \<Longrightarrow> equiv_out a c"
using equiv_class_eq_iff equiv_out_equiv by fastforce

text "This shows that it is safe to continue deselecting a test based
 on its output under a previous program, to an arbitrary number of
 program changes, as long as the test is continually deselected. This
 is useful because it means changed programs don't need to generate new
 outputs for deselected tests to ensure safety of future deselections."
lemma existence_safe_trans:
assumes Pst_in: "Ps \<noteq> []" "set Ps \<subseteq> progs" "t \<in> tests" and
 o0: "o\<^sub>0 \<in> out (Ps!0) t" and
 des: "\<forall>n < (length Ps) - 1. deselect (Ps!n) o\<^sub>0 (Ps!(Suc n))"
shows "\<exists>o\<^sub>n \<in> out (last Ps) t. equiv_out o\<^sub>0 o\<^sub>n"
using assms proof(induct "length Ps" arbitrary: Ps)
  case 0 with Pst_in show ?case by simp
next
  case (Suc x) then show ?case
  proof(induct x)
  case z: 0
    from z.prems(2,3) have "Ps ! (length Ps - 2) = last Ps"
      by (simp add: last_conv_nth numeral_2_eq_2)
    with equiv_out_refl z.prems(2,6) show ?case by auto
  next
    case Suc':(Suc x')
    let ?Ps = "take (Suc x') Ps"
    have len': "Suc x' = length (take (Suc x') Ps)" using Suc'.prems(2) by auto
    moreover have nmt': "take (Suc x') Ps \<noteq> []" using len' by auto
    moreover have sub': "set (take (Suc x') Ps) \<subseteq> progs" using Suc.prems(2)
      by (meson order_trans set_take_subset)
    moreover have "t \<in> tests" using Pst_in(3) by simp
    moreover have "o\<^sub>0 \<in> out (take (Suc x') Ps ! 0) t" using Suc.prems(4) by simp
    moreover have "\<forall>n<length (take (Suc x') Ps) - 1.
     deselect (take (Suc x') Ps ! n) o\<^sub>0 (take (Suc x') Ps ! (Suc n))"
      using Suc.prems(5) len' by simp
    ultimately have "\<exists>o'\<in>out (last ?Ps) t. equiv_out o\<^sub>0 o'" by(rule Suc'.prems(1)[of ?Ps])
    then obtain o' where o': "o' \<in> out (last ?Ps) t" and eo: "equiv_out o\<^sub>0 o'" by clarify
    from Suc.prems(1) Suc'.prems(2) len' nmt'
    have "last (take (Suc x') Ps) = Ps!x'" "last Ps = Ps!(Suc x')"
      by (metis diff_Suc_1 last_conv_nth lessI nth_take)+
    moreover have "x' < length Ps - 1" using Suc'.prems(2) by linarith
    ultimately have des':"deselect (last (take (Suc x') Ps)) o\<^sub>0 (last Ps)"
      using Suc.prems(5) by simp
    from Suc.prems(1,2) sub' nmt' last_in_set
    have Ps_in: "last (take (Suc x') Ps) \<in> progs" "last Ps \<in> progs" by blast+
    have "\<exists>o\<^sub>n \<in> out (last Ps) t. equiv_out o' o\<^sub>n"
      by(rule existence_safe[where P="last (take (Suc x') Ps)" and P'="last Ps" and t=t,
                    OF Ps_in Pst_in(3) o' equiv_out_deselect[OF eo des']])
    then obtain o\<^sub>n where oN: "o\<^sub>n \<in> out (last Ps) t" and eo': "equiv_out o' o\<^sub>n" by clarify
    moreover from eo eo' have "equiv_out o\<^sub>0 o\<^sub>n" by(rule equiv_out_trans)
    ultimately show ?case by auto
  qed
qed

end \<comment> \<open> @{text RTS_safe} \<close>

end