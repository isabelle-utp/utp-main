section \<open> Simple Buffer in UTP CSP \<close>

theory utp_csp_buffer
  imports "UTP-Circus.utp_circus"
begin

subsection \<open> Definitions \<close>

text \<open> A stateful CSP (Circus) process is parametrised over two alphabets: one for the state-space,
  which consists of the state variables, and one for events, which consists of channels. We first
  define the statespace using the \textbf{alphabet} command. The single state variable $buf$ is
  a list of natural numbers that is currently in the buffer. \<close>

alphabet st_buffer =
  buff :: "nat list"

text \<open> Channels are created using the \textbf{datatype} command. In this case we can either input
  a value to go in the buffer, or output one presently in the buffer. \<close>

datatype ch_buffer =
  inp nat | outp nat

text \<open> We create a useful type to describe an action of the buffer as a CSP action parametrised
  by the state and event alphabet. \<close>

type_synonym act_buffer = "(st_buffer, ch_buffer) action"

text \<open> We define an action that initialises the buffer state by setting it to empty. \<close>

abbreviation Init :: act_buffer where
"Init \<equiv> buff :=\<^sub>C \<langle>\<rangle>"

text \<open> We define the main body of behaviour for the buffer as an abbreviation. We can either
  input a value and then place it into the buffer, or else, provided that the buffer is non-empty,
  we can output a value presently in the buffer. \<close>

abbreviation DoBuff :: act_buffer where
"DoBuff \<equiv> (inp?(v) \<^bold>\<rightarrow> buff :=\<^sub>C (&buff ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>)
           \<box> (#\<^sub>u(&buff) >\<^sub>u 0) &\<^sub>u outp!(head\<^sub>u(&buff)) \<^bold>\<rightarrow> buff :=\<^sub>C tail\<^sub>u(&buff))"

text \<open> The main action of the buffer first initialises the single state variable $buff$, and
  enters a recursive loop where it does \emph{DoBuff} over and over. \<close>

definition Buffer :: act_buffer where
[rdes_def]: "Buffer = Init ;; while\<^sub>R true do DoBuff od"

subsection \<open> Calculations \<close>

text \<open> The @{term Init} action is represented by a simple contract with a true precondition,
  false pericondition (i.e. there is no intermediate behaviour), and finally sets the state
  variable to be empty, whilst leaving the state unchanged. There are no constraints on
  the initial state. \<close>

lemma Init_contract:
  "Init = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> \<Phi>(true,[&buff \<mapsto>\<^sub>s \<langle>\<rangle>],\<langle>\<rangle>))"
  by (rdes_simp)

lemma DoBuff_contract:
  "DoBuff = \<^bold>R\<^sub>s (true\<^sub>r \<turnstile>
                \<E>(true,\<langle>\<rangle>, (\<Sqinter> x \<bullet> {(inp\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u) \<union>\<^sub>u ({(outp\<cdot>head\<^sub>u(&buff))\<^sub>u}\<^sub>u \<triangleleft> 0 <\<^sub>u #\<^sub>u(&buff) \<triangleright> {}\<^sub>u)) \<diamondop>
                ((\<Sqinter> x \<bullet> \<Phi>(true,[&buff \<mapsto>\<^sub>s &buff ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>],\<langle>(inp\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>)) \<or>
                 \<Phi>(0 <\<^sub>u #\<^sub>u(&buff), [&buff \<mapsto>\<^sub>s tail\<^sub>u(&buff)], \<langle>(outp\<cdot>head\<^sub>u(&buff))\<^sub>u\<rangle>)))"
  by (rdes_eq)

lemma Buffer_contract:
  "Buffer = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<Phi>(true,[&buff \<mapsto>\<^sub>s \<langle>\<rangle>],\<langle>\<rangle>) ;;
                       ((\<Sqinter> x \<bullet> \<Phi>(true, [&buff \<mapsto>\<^sub>s &buff ^\<^sub>u \<langle>\<guillemotleft>x\<guillemotright>\<rangle>], \<langle>(inp\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>)) \<or>
                        \<Phi>(0 <\<^sub>u #\<^sub>u(&buff), [&buff \<mapsto>\<^sub>s tail\<^sub>u(&buff)], \<langle>(outp\<cdot>head\<^sub>u(&buff))\<^sub>u\<rangle>))\<^sup>\<star>\<^sup>r ;;
                        \<E>(true,\<langle>\<rangle>, (\<Sqinter> x \<bullet> {(inp\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u) \<union>\<^sub>u ({(outp\<cdot>head\<^sub>u(&buff))\<^sub>u}\<^sub>u \<triangleleft> 0 <\<^sub>u #\<^sub>u(&buff) \<triangleright> {}\<^sub>u)) \<diamondop>
                       false)"
  unfolding Buffer_def DoBuff_contract by rdes_eq

subsection \<open> Verifications \<close>

text \<open> We first show that the buffer always outputs the same elements that were input first. \<close>

abbreviation "inps t \<equiv> [x. inp x \<leftarrow> t]"
abbreviation "outps t \<equiv> [x. outp x \<leftarrow> t]"

lemma P1_lemma:
  "[true \<turnstile> \<guillemotleft>outps(trace)\<guillemotright> \<le>\<^sub>u &buff ^\<^sub>u \<guillemotleft>inps(trace)\<guillemotright> | true]\<^sub>C \<sqsubseteq> while\<^sub>R true do DoBuff od"
  apply (rdes_refine_split)
    apply (simp_all add: rpred closure usubst)
   apply (rule rrel_thy.Star_inductl)
    apply (simp add: closure)
   apply (rule RR_refine_intro)
  apply (simp_all add: closure)
   apply (rel_auto)
  apply (smt Prefix_Order.Cons_prefix_Cons Prefix_Order.prefix_Nil append_Cons append_Nil ch_buffer.simps(6) concat_map_maps hd_Cons_tl maps_simps(1) not_Cons_self2)
  done 

lemma P1: "[true \<turnstile> \<guillemotleft>outps(trace)\<guillemotright> \<le>\<^sub>u \<guillemotleft>inps(trace)\<guillemotright> | true]\<^sub>C \<sqsubseteq> Buffer"
proof -
  have "[true \<turnstile> \<guillemotleft>outps(trace)\<guillemotright> \<le>\<^sub>u \<guillemotleft>inps(trace)\<guillemotright> | true]\<^sub>C
        \<sqsubseteq>
        Init ;; [true \<turnstile> \<guillemotleft>outps(trace)\<guillemotright> \<le>\<^sub>u &buff ^\<^sub>u \<guillemotleft>inps(trace)\<guillemotright> | true]\<^sub>C"
    by (rdes_refine)
  thus ?thesis
    by (metis (no_types, lifting) Buffer_def P1_lemma dual_order.trans urel_dioid.mult_isol)
qed

end