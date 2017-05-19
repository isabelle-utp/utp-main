section {* Simple Buffer in UTP CSP *}

theory utp_csp_buffer
  imports "../theories/utp_csp"
begin

subsection {* Definitions *}

text {* A stateful CSP (Circus) process is parametrised over two alphabets: one for the state-space,
  which consists of the state variables, and one for events, which consists of channels. We first
  define the statespace using the \textbf{alphabet} command. The single state variable $buf$ is
  a list of natural numbers that is currently in the buffer. *}

alphabet st_buffer =
  buff :: "nat list"

text {* Channels are created using the \textbf{datatype} command. In this case we can either input
  a value to go in the buffer, or output one presently in the buffer. *}

datatype ch_buffer =
  inp nat | outp nat

text {* We create a useful type to describe an action of the buffer as a CSP action parametrised
  by the state and event alphabet. *}

type_synonym act_buffer = "(st_buffer, ch_buffer) action"

text {* We define the main body of behaviour for the buffer as an abbreviation. We can either
  input a value and then place it into the buffer, or else, provided that the buffer is non-empty,
  we can output a value presently in the buffer. *}

abbreviation DoBuff :: act_buffer where
"DoBuff \<equiv> (inp?(v) \<^bold>\<rightarrow> buff :=\<^sub>C (&buff ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>)
           \<box> (#\<^sub>u(&buff) >\<^sub>u 0) &\<^sub>u outp!(head\<^sub>u(&buff)) \<^bold>\<rightarrow> buff :=\<^sub>C tail\<^sub>u(&buff))"

text {* The main action of the buffer first initialises the single state variable $buff$, and
  enters a recursive loop where it does \emph{DoBuff} over and over. *}

definition Buffer :: act_buffer where
[rdes]: "Buffer = buff :=\<^sub>C \<langle>\<rangle> ;; (\<mu>\<^sub>C X \<bullet> DoBuff ;; X)"

subsection {* Calculations *}

text {* The precondition of the main body is true because no divergence is possible. We calculate
  this using the reactive design calculation tactic, \textbf{rdes-calc}. *}

lemma preR_DoBuff: "pre\<^sub>R(DoBuff) = true"
  by (rdes_calc)

text {* The pericondition ensures that no input on channel $inp$ is being refused, the trace
  stays the same (no event has yet occurred), and provided the buffer is non-empty then outputting
  the head of the buffer is not refused either. *}

lemma periR_DoBuff:
  "peri\<^sub>R(DoBuff) =
     ((\<Squnion> v \<bullet> (inp\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u \<notin>\<^sub>u $ref\<acute>) \<and> $tr\<acute> =\<^sub>u $tr \<and>
      (#\<^sub>u($st:buff) >\<^sub>u 0 \<Rightarrow> \<lceil>(outp\<cdot>head\<^sub>u(&buff))\<^sub>u\<rceil>\<^sub>S\<^sub>< \<notin>\<^sub>u $ref\<acute>))"
  by (rdes_calc, rel_auto)

text {* The postcondition has two possibilities. In the first option a particular input $v$ was
  received and so the trace was extended, and the $buff$ variable is extended with $v$. In the second
  option the buffer is non-empty, the trace is extended to output the value at the head, and the head
  is removed from the buffer. *}

lemma postR_DoBuff:
  "post\<^sub>R(DoBuff) = ((\<Sqinter> v \<bullet> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>(inp\<cdot>\<guillemotleft>v\<guillemotright>)\<^sub>u\<rangle> \<and> \<lceil>buff := &buff ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>\<rceil>\<^sub>S) \<or>
                    #\<^sub>u($st:buff) >\<^sub>u 0 \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>\<lceil>(outp\<cdot>head\<^sub>u(&buff))\<^sub>u\<rceil>\<^sub>S\<^sub><\<rangle> \<and> \<lceil>buff := tail\<^sub>u(&buff)\<rceil>\<^sub>S)"
  by rdes_calc

text {* The precondition of the overall buffer is again true as no divergence can occur. *}

lemma preR_Buffer: "pre\<^sub>R(Buffer) = true"
  by rdes_calc

text {* The postcondition is false as it is a non-terminating process. *}

lemma postR_Buffer: "post\<^sub>R(Buffer) = false"
  by rdes_calc

text {* The pericondition is where the main behaviour of the buffer appears. Essentially this repeats
  the postcondition of the main body again and again, each time finishing in the pericondition. We do
  not reproduce it as it is a little long, but the calculation can be seen in Isabelle. *}

lemma periR_Buffer: "peri\<^sub>R(Buffer) = undefined"
    apply (simp add: Buffer_def rdes closure wp unrest usubst alpha seq_UINF_distr)
oops


end