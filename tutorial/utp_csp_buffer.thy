section \<open> Simple Buffer in UTP CSP \<close>

theory utp_csp_buffer
  imports "UTP-Circus.utp_circus_easy_parser"
begin

subsection \<open> Definitions \<close>

text \<open> A stateful CSP (Circus) process is parametrised over two alphabets: one for the state-space,
  which consists of the state variables, and one for events, which consists of channels. We first
  define the statespace using the \textbf{alphabet} command. The single state variable $buf$ is
  a list of natural numbers that is currently in the buffer. \<close>

alphabet st_buffer =
  buff :: "nat list"
  val  :: "nat"

text \<open> Channels are created using the \textbf{datatype} command. In this case we can either input
  a value to go in the buffer, or output one presently in the buffer. \<close>

datatype ch_buffer =
  inp nat | outp nat

text \<open> We create a useful type to describe an action of the buffer as a CSP action parametrised
  by the state and event alphabet. \<close>

type_synonym act_buffer = "(st_buffer, ch_buffer) action"

text \<open> We define an action that initialises the buffer state by setting it to empty. \<close>

abbreviation Init :: act_buffer where
"Init \<equiv> buff :=\<^sub>C []"

text \<open> We define the main body of behaviour for the buffer as an abbreviation. We can either
  input a value and then place it into the buffer, or else, provided that the buffer is non-empty,
  we can output a value presently in the buffer. \<close>

term OutputCSP

utp_lift_notation chan_apply (1)

abbreviation DoBuff :: act_buffer where
"DoBuff \<equiv> (inp?(val) ;; buff := buff @ [val]
           \<box> (length(&buff) > 0) && outp!(hd(buff)) ;; buff := tl(buff))"

text \<open> The main action of the buffer first initialises the single state variable $buff$, and
  enters a recursive loop where it does \emph{DoBuff} over and over. \<close>

definition Buffer :: act_buffer where
[rdes_def]: "Buffer = Init ;; while true do DoBuff od"

subsection \<open> Calculations \<close>

text \<open> The @{term Init} action is represented by a simple contract with a true precondition,
  false pericondition (i.e. there is no intermediate behaviour), and finally sets the state
  variable to be empty, whilst leaving the state unchanged. There are no constraints on
  the initial state. \<close>

lemma Init_contract:
  "Init = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> \<Phi>(true,[&buff \<mapsto>\<^sub>s []],\<langle>\<rangle>))"
  by (rdes_simp)

term chan_apply

lemma DoBuff_contract:
  "DoBuff = \<^bold>R\<^sub>s (true\<^sub>r \<turnstile>
                \<E>(true,\<langle>\<rangle>, (\<Sqinter> x \<bullet> {(inp\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u) \<union>\<^sub>u ({(outp\<cdot>(hd(&buff)))\<^sub>u}\<^sub>u \<triangleleft> 0 <\<^sub>u #\<^sub>u(&buff) \<triangleright> {}\<^sub>u)) \<diamondop>
                ((\<Sqinter> x \<bullet> \<Phi>(true,[&buff \<mapsto>\<^sub>s buff @ [\<guillemotleft>x\<guillemotright>], val \<mapsto>\<^sub>s \<guillemotleft>x\<guillemotright>],\<langle>(inp\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>)) \<or>
                 \<Phi>(0 <\<^sub>u #\<^sub>u(&buff), [&buff \<mapsto>\<^sub>s tl(buff)], \<langle>(outp\<cdot>(hd(&buff)))\<^sub>u\<rangle>)))"
  by (rdes_eq)

lemma Buffer_contract:
  "Buffer = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<Phi>(true,[&buff \<mapsto>\<^sub>s []],\<langle>\<rangle>) ;;
                       ((\<Sqinter> x \<bullet> \<Phi>(true, [&buff \<mapsto>\<^sub>s buff @ [\<guillemotleft>x\<guillemotright>], val \<mapsto>\<^sub>s \<guillemotleft>x\<guillemotright>], \<langle>(inp\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u\<rangle>)) \<or>
                        \<Phi>(0 <\<^sub>u #\<^sub>u(&buff), [&buff \<mapsto>\<^sub>s tl(buff)], \<langle>(outp\<cdot>hd(&buff))\<^sub>u\<rangle>))\<^sup>\<star>\<^sup>c ;;
                        \<E>(true,\<langle>\<rangle>, (\<Sqinter> x \<bullet> {(inp\<cdot>\<guillemotleft>x\<guillemotright>)\<^sub>u}\<^sub>u) \<union>\<^sub>u ({(outp\<cdot>hd(&buff))\<^sub>u}\<^sub>u \<triangleleft> 0 <\<^sub>u #\<^sub>u(&buff) \<triangleright> {}\<^sub>u)) \<diamondop>
                       false)"
  unfolding Buffer_def DoBuff_contract by (rdes_simp)

subsection \<open> Verifications \<close>

text \<open> We first show that the buffer always outputs the same elements that were input first. \<close>

abbreviation "inps t \<equiv> [x. inp x \<leftarrow> t]"
abbreviation "outps t \<equiv> [x. outp x \<leftarrow> t]"

lemma P1_lemma:
  "[true \<turnstile> U(outps(\<guillemotleft>trace\<guillemotright>) \<le> (buff @ inps(\<guillemotleft>trace\<guillemotright>))) | true]\<^sub>C \<sqsubseteq> while\<^sub>C true do DoBuff od"
  apply (rdes_refine_split)
    apply (simp_all add: rpred closure usubst)
  apply (rule conjI)
   apply (rule crf_star_inductl)
    apply (simp add: closure)
   apply (rule RR_refine_intro)
  apply (simp_all add: closure)
   apply (rel_auto)
   apply (smt Prefix_Order.Cons_prefix_Cons Prefix_Order.prefix_Nil append_Cons append_Nil ch_buffer.simps(6) concat_map_maps hd_Cons_tl maps_simps(1) not_Cons_self2)
   apply (rule crf_star_inductl)
    apply (simp add: closure)
   apply (rule RR_refine_intro)
  apply (simp_all add: closure)
   apply (rel_auto)
    apply (smt Prefix_Order.Cons_prefix_Cons append.left_neutral append_Cons ch_buffer.simps(6) concat_map_maps hd_Cons_tl less_eq_list_def maps_simps(1) prefix_code(2))
done 

lemma P1: "[true \<turnstile> U(outps(\<guillemotleft>trace\<guillemotright>) \<le> inps(\<guillemotleft>trace\<guillemotright>)) | true]\<^sub>C \<sqsubseteq> Buffer"
proof -
  have "[true \<turnstile> U(outps(\<guillemotleft>trace\<guillemotright>) \<le> inps(\<guillemotleft>trace\<guillemotright>)) | true]\<^sub>C
        \<sqsubseteq>
        Init ;; [true \<turnstile> U(outps(\<guillemotleft>trace\<guillemotright>) \<le> inps(\<guillemotleft>trace\<guillemotright>)) | true]\<^sub>C"
    by (rdes_refine)
  moreover have "Init ;; [true \<turnstile> U(outps(\<guillemotleft>trace\<guillemotright>) \<le> inps(\<guillemotleft>trace\<guillemotright>)) | true]\<^sub>C 
                 \<sqsubseteq>
                 Init ;; [true \<turnstile> U(outps(\<guillemotleft>trace\<guillemotright>) \<le> (buff @ inps(\<guillemotleft>trace\<guillemotright>))) | true]\<^sub>C"
    by (rdes_refine)
  moreover have "Init ;; [true \<turnstile> U(outps(\<guillemotleft>trace\<guillemotright>) \<le> (buff @ inps(\<guillemotleft>trace\<guillemotright>))) | true]\<^sub>C
                 \<sqsubseteq>
                 Buffer"
    by (simp add: Buffer_def P1_lemma urel_dioid.mult_isol)
  ultimately show ?thesis
    by (simp)
qed

lemma Buffer_deadlock_free: "CDF \<sqsubseteq> Buffer"
  unfolding Buffer_def
  by (rdes_refine; blast)

end