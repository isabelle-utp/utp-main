section {* Mini-mondex example *}

theory utp_csp_mini_mondex
  imports "../theories/utp_csp"
begin

text {* This example is a modified version of the Mini-Mondex card example taken from the 2014
  paper "Contracts in CML" by Woodcock et al. *}
  
subsection {* Types and Statespace *}
  
type_synonym index = nat -- {* Card identifiers *}
type_synonym money = int -- {* Monetary amounts. *}

text {* In the paper money is represented as a nat, here we use an int so that we have the option
  of modelling negative balances. This also eases proof as integers form an algebraic ring. *}
  
alphabet st_mdx =
  accts :: "(index, money) pfun" -- {* Index record of each card's balance *}
  
datatype ch_mdx = 
  pay "index \<times> index \<times> money" | -- {* Request a payment between two cards *}
  transfer "index \<times> index \<times> money" | -- {* Effect the transfer *}
  accept index | -- {* Accept the payment *}
  reject index -- {* Reject it *}
  
type_synonym action_mdx = "(st_mdx, ch_mdx) action"
  
subsection {* Actions *}
  
text {* The Pay action describes the protocol when a payment of $n$ is requested between two cards,
  $i$ and $j$. It is slightly modified from the paper, as we firstly do not use operations but effect
  the transfer using indexed assignments directly, and secondly because before the transfer can proceed
  we need to check the balance is both sufficient, and that the transfer amount is greater than 0. It
  should also be noted that the indexed assignments give rise to preconditions that the list is
  defined at the given index. In other words, the given card records must be present. *}
  
definition Pay :: "index \<Rightarrow> index \<Rightarrow> money \<Rightarrow> action_mdx" where
"Pay i j n = 
  pay.((\<guillemotleft>i\<guillemotright>,\<guillemotleft>j\<guillemotright>,\<guillemotleft>n\<guillemotright>)\<^sub>u) \<^bold>\<rightarrow> 
    ((reject.(\<guillemotleft>i\<guillemotright>) \<^bold>\<rightarrow> Skip) 
      \<triangleleft> \<guillemotleft>i\<guillemotright> =\<^sub>u \<guillemotleft>j\<guillemotright> \<or> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> \<guillemotleft>n\<guillemotright> >\<^sub>u &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a \<triangleright>\<^sub>R 
    ({accts[\<guillemotleft>i\<guillemotright>]} :=\<^sub>C (&accts(\<guillemotleft>i\<guillemotright>)\<^sub>a - \<guillemotleft>n\<guillemotright>) ;;
     {accts[\<guillemotleft>j\<guillemotright>]} :=\<^sub>C (&accts(\<guillemotleft>j\<guillemotright>)\<^sub>a + \<guillemotleft>n\<guillemotright>) ;;
     accept.(\<guillemotleft>i\<guillemotright>) \<^bold>\<rightarrow> Skip))"
    
definition PaySet :: "index \<Rightarrow> (index \<times> index \<times> money) set" where
[upred_defs]: "PaySet cardNum = {(i,j,k). i < cardNum \<and> j < cardNum \<and> i \<noteq> j}"

definition AllPay :: "index \<Rightarrow> action_mdx" where
"AllPay cardNum = (\<Sqinter> (i, j, n) \<in> PaySet cardNum \<bullet> Pay i j n)"

text {* The Cycle action just repea the payments over and over for any extant and different card
  indices. In order to be well-formed we require that $cardNum \ge 2$. *}

definition Cycle :: "index \<Rightarrow> action_mdx" where
"Cycle cardNum = (\<mu>\<^sub>C X \<bullet> AllPay(cardNum) ;; X)"

text {* The Mondex action is a sample setup. It requires creates $cardNum$ cards each with 100 units
  present. *}

definition Mondex :: "index \<Rightarrow> action_mdx" where
"Mondex(cardNum) = (accts :=\<^sub>C entr\<^sub>u({0..10}\<^sub>u, \<lambda> x. 100) ;; Cycle(cardNum))"

subsection {* Pre/peri/post calculations *}

text {* The behaviour of a reactive program is described in three parts: (1) the precondition,
  that describes how the state and environment must behave to ensure valid behaviour; (2)
  the pericondition that describes the commitments the program makes whilst in an intermediate
  state in terms of events only; and (3) the postcondition that describes the commitments after
  the process terminates. The pericondition refers only to the trace, as the state is invisible
  in intermediate states -- it can only be observed through events. The pre- and postcondition
  can refer to both the state and the trace; although the form can only refer to a prefix
  of the trace and before state variables -- only the postcondition refers to after state. *}
  
lemma Pay_CSP [closure]: "Pay i j n is CSP"
  by (simp add: Pay_def closure)

text {* The precondition of pay requires that, under the assumption that a payment was requested
  by the environment (pay is present at the trace head), and that the given amount can be honoured by
  the sending card, then the two cards must exist. This arises directly from the indexed assignment
  preconditions. 

  The pericondition has three cases: (1) nothing has happened and we are not refusing the
  payment request, (2) the payment request happened, but there isn't enough (or non-positive) money
  and reject is being offered, or (3) there was enough money and accept is being offered.

  The postcondition has two options. Firstly, the amount was wrong, and 
  so the trace was extended by both pay and reject, with the state remaining 
  unchanged. Secondly, the payment was fine and so the trace was extended by pay 
  and accept, and the states of the two cards was updated appropriately.

*}

lemma Pay_contract:
  assumes "i \<noteq> j"
  shows
  "Pay i j n = 
    \<^bold>R\<^sub>s ( (\<I>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r 
           [(\<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright>) \<or> \<guillemotleft>i\<guillemotright> \<in>\<^sub>u dom\<^sub>u(&accts) \<and> \<guillemotleft>j\<guillemotright> \<in>\<^sub>u dom\<^sub>u(&accts)]\<^sub>S) 
       
       \<turnstile> (\<E>(true,\<langle>\<rangle>, {(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u}\<^sub>u) \<or>
            \<E>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>, {(reject\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u}\<^sub>u) 
               \<triangleleft> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R
            \<E>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>, {(accept\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u}\<^sub>u)) 

       \<diamondop> (\<Phi>(true,id,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u, (reject\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u\<rangle>) 
            \<triangleleft> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R
          \<Phi>(true,[&accts \<mapsto>\<^sub>s &accts(\<guillemotleft>i\<guillemotright> \<mapsto> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a - \<guillemotleft>n\<guillemotright>, \<guillemotleft>j\<guillemotright> \<mapsto> &accts(\<guillemotleft>j\<guillemotright>)\<^sub>a + \<guillemotleft>n\<guillemotright>)\<^sub>u]
                ,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u, (accept\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u\<rangle>)))"
  using assms by (simp add: Pay_def closure, rdes_simp)  
            
lemma Pay_wf [closure]:
  "Pay i j n is NCSP"
  by (simp add: Pay_def closure)
  
lemma Pay_Productive [closure]: "Pay i j n is Productive"
  by (simp add: Pay_def closure)
       
lemma PaySet_cardNum_nempty [closure]: 
  "cardNum \<ge> 2 \<Longrightarrow> \<not> PaySet cardNum = {}"
  by (rel_simp, presburger)
  
lemma AllPay_wf [closure]: 
  "cardNum \<ge> 2 \<Longrightarrow> AllPay cardNum is NCSP"
  by (simp add: AllPay_def closure)
    
lemma AllPay_Productive [closure]:
  "cardNum \<ge> 2 \<Longrightarrow> AllPay cardNum is Productive"
  by (simp add: AllPay_def closure)
    
lemma preR_AllPay [rdes]:
  "cardNum \<ge> 2 \<Longrightarrow> pre\<^sub>R(AllPay cardNum) = 
    (\<Squnion> (i, j, n) \<in> PaySet cardNum \<bullet> $tr\<acute> \<ge>\<^sub>u $tr ^\<^sub>u \<langle>(pay\<cdot>\<guillemotleft>(i, j, n)\<guillemotright>)\<^sub>u\<rangle> \<and> \<guillemotleft>i\<guillemotright> \<noteq>\<^sub>u \<guillemotleft>j\<guillemotright> \<and> \<guillemotleft>n\<guillemotright> >\<^sub>u 0 \<and> $st:accts(\<guillemotleft>i\<guillemotright>)\<^sub>a \<ge>\<^sub>u \<guillemotleft>n\<guillemotright> \<Rightarrow> {\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>}\<^sub>u \<subseteq>\<^sub>u dom\<^sub>u($st:accts))"
  by (simp add: AllPay_def rdes closure)    
    
subsection {* Verification *}

text {* We perform verification by writing contracts that specify desired behaviours of our
  system. A contract @{term "[P \<turnstile> Q | R]\<^sub>C"} consists of three predicates that correspond to
  the pre-, peri-, and postconditions, respectively. The precondition talks about initial state
  variables and the $trace$ contribution via a special variable. The pericondition likewise
  talks about initial states and traces. The postcondition also talks about final states.

  We first show that any payment leaves the total value shared between the cards unchanged.
  This is under the assumption that at least two cards exist. The contract has as its precondition
  that initially the number of cards is $cardNum$. The pericondition is $true$ as we don't
  care about intermediate behaviour here. The postcondition has that the summation of the 
  sequence of card values remains the same, though of course individual records will change. *}
  
theorem money_constant:
  assumes "i < cardNum" "j < cardNum" "i \<noteq> j"
  shows "[#\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cardNum\<guillemotright> \<turnstile> true | sum\<^sub>u($accts) =\<^sub>u sum\<^sub>u($accts\<acute>)]\<^sub>C \<sqsubseteq> Pay i j n"
-- {* We first apply the reactive design contract introduction law and discharge well-formedness of Pay *}
proof (rule CRD_contract_refine, simp add: closure)

  -- {* Three proof obligations result for the pre/peri/postconditions. The first requires us to
    show that the contract's precondition is weakened by the implementation precondition. 
    It is because the implementation's precondition is under the assumption of receiving an
    input and the money amount constraints. We discharge by first calculating the precondition, 
    as done above, and then using the relational calculus tactic. *}

  from assms show "`\<lceil>#\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cardNum\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<Rightarrow> pre\<^sub>R (Pay i j n)`"
    by (rdes_calc, rel_auto)

  -- {* The second is trivial as we don't care about intermediate states. *}
      
  show "`\<lceil>#\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cardNum\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<and> peri\<^sub>R (Pay i j n) \<Rightarrow> \<lceil>true\<rceil>\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk>`"
    by rel_auto

  -- {* The third requires that we show that the postcondition implies that the total amount remains
    unaltered. We calculate the postcondition, and then use relational calculus. In this case, this
    is not enough and an additional property of lists is required (@{thm listsum_update}) that can
    be retrieved by sledgehammer. However, we actually had to prove that property first and add it to our library. *}
      
  from assms
  show " `\<lceil>#\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cardNum\<guillemotright>\<rceil>\<^sub>S\<^sub>< \<and> post\<^sub>R (Pay i j n) \<Rightarrow> \<lceil>sum\<^sub>u($accts) =\<^sub>u sum\<^sub>u($accts\<acute>)\<rceil>\<^sub>S\<lbrakk>x\<rightarrow>tt\<rbrakk>`"
    by (rdes_calc, rel_auto, simp add: listsum_update)
qed

text {* The next property is that no card value can go below 0, assuming it was non-zero to start
  with. *}
  
theorem no_overdrafts:
  assumes "i < cardNum" "j < cardNum" "i \<noteq> j"
  shows "[#\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cardNum\<guillemotright> \<turnstile> true | (\<^bold>\<forall> k \<bullet> \<guillemotleft>k\<guillemotright> <\<^sub>u \<guillemotleft>cardNum\<guillemotright> \<and> $accts(\<guillemotleft>k\<guillemotright>)\<^sub>a \<ge>\<^sub>u 0 \<Rightarrow> $accts\<acute>(\<guillemotleft>k\<guillemotright>)\<^sub>a \<ge>\<^sub>u 0)]\<^sub>C \<sqsubseteq> Pay i j n"
  apply (rule CRD_contract_refine)
  apply (simp add: Pay_def closure)
  apply (simp add: rdes)
  using assms
  apply (rel_auto)
  apply (simp add: usubst alpha rdes)
  apply (simp add: usubst alpha rdes)
  using assms apply (rel_auto)
  apply (auto simp add: nth_list_update)
done
  
text {* The next property shows liveness of transfers. If a payment is accepted, and we have enough
  money, then the acceptance of the transfer cannot be refused. Unlike the previous two examples,
  this is specified using the pericondition as we are talking about intermediate states and refusals. *}
  
theorem transfer_live:
  assumes "i < cardNum" "j < cardNum" "i \<noteq> j" "n > 0"
  shows "[#\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cardNum\<guillemotright> 
         \<turnstile> \<guillemotleft>trace\<guillemotright> \<noteq>\<^sub>u \<langle>\<rangle> \<and> last\<^sub>u(\<guillemotleft>trace\<guillemotright>) =\<^sub>u (pay\<cdot>(\<guillemotleft>(i,j,k)\<guillemotright>))\<^sub>u \<and> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a \<Rightarrow> (accept\<cdot>(\<guillemotleft>(i)\<guillemotright>))\<^sub>u \<notin>\<^sub>u \<guillemotleft>refs\<guillemotright>
         | true]\<^sub>C \<sqsubseteq> Pay i j n"
  apply (rule_tac CRD_contract_refine)
  apply (simp add: Pay_def closure)
  apply (simp add: rdes)
  using assms apply (rel_auto)
  apply (simp add: rdes)    
  using assms apply (rel_auto)
  apply (simp add: zero_list_def)
  apply (rel_auto)
done
    
end