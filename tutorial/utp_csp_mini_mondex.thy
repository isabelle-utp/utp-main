section \<open> Mini-mondex example \<close>

theory utp_csp_mini_mondex
  imports "UTP-Circus.utp_circus" "UTP.utp_easy_parser"
begin

text \<open> This example is a modified version of the Mini-Mondex card example taken from the 2014
  paper "Contracts in CML" by Woodcock et al. \<close>
  
subsection \<open> Types and Statespace \<close>
  
type_synonym index = nat \<comment> \<open> Card identifiers \<close>
type_synonym money = int \<comment> \<open> Monetary amounts. \<close>

text \<open> In the paper money is represented as a nat, here we use an int so that we have the option
  of modelling negative balances. This also eases proof as integers form an algebraic ring. \<close>
  
alphabet st_mdx =
  accts :: "(index, money) pfun" \<comment> \<open> Index record of each card's balance \<close>
  
datatype ch_mdx = 
  pay "index \<times> index \<times> money" | \<comment> \<open> Request a payment between two cards \<close>
  transfer "index \<times> index \<times> money" | \<comment> \<open> Effect the transfer \<close>
  accept index | \<comment> \<open> Accept the payment \<close>
  reject index \<comment> \<open> Reject it \<close>
  
type_synonym action_mdx = "(st_mdx, ch_mdx) action"
  
subsection \<open> Actions \<close>
  
text \<open> The Pay action describes the protocol when a payment of $n$ is requested between two cards,
  $i$ and $j$. It is slightly modified from the paper, as we firstly do not use operations but effect
  the transfer using indexed assignments directly, and secondly because before the transfer can proceed
  we need to check the balance is both sufficient, and that the transfer amount is greater than 0. It
  should also be noted that the indexed assignments give rise to preconditions that the list is
  defined at the given index. In other words, the given card records must be present. \<close>

definition Pay :: "index \<Rightarrow> index \<Rightarrow> money \<Rightarrow> action_mdx" where
"Pay i j n = 
  pay.((\<guillemotleft>i\<guillemotright>,\<guillemotleft>j\<guillemotright>,\<guillemotleft>n\<guillemotright>)\<^sub>u) \<^bold>\<rightarrow> 
    ((reject.(\<guillemotleft>i\<guillemotright>) \<^bold>\<rightarrow> Skip) 
      \<triangleleft> \<guillemotleft>i\<guillemotright> =\<^sub>u \<guillemotleft>j\<guillemotright> \<or> \<guillemotleft>i\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accts) \<or> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> \<guillemotleft>n\<guillemotright> >\<^sub>u &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a \<triangleright>\<^sub>R 
    (accts[\<guillemotleft>i\<guillemotright>] :=\<^sub>C (&accts(\<guillemotleft>i\<guillemotright>)\<^sub>a - \<guillemotleft>n\<guillemotright>) ;;
     accts[\<guillemotleft>j\<guillemotright>] :=\<^sub>C (&accts(\<guillemotleft>j\<guillemotright>)\<^sub>a + \<guillemotleft>n\<guillemotright>) ;;
     accept.(\<guillemotleft>i\<guillemotright>) \<^bold>\<rightarrow> Skip))"
    
definition PaySet :: "index \<Rightarrow> (index \<times> index \<times> money) set" where
[upred_defs]: "PaySet cardNum = {(i,j,k). i < cardNum \<and> j < cardNum \<and> i \<noteq> j}"

definition AllPay :: "index \<Rightarrow> action_mdx" where
"AllPay cardNum = (\<Sqinter> (i, j, n) \<in> PaySet cardNum \<bullet> Pay i j n)"

text \<open> The Cycle action just repea the payments over and over for any extant and different card
  indices. In order to be well-formed we require that $cardNum \ge 2$. \<close>

definition Cycle :: "index \<Rightarrow> action_mdx" where
"Cycle cardNum = (\<mu>\<^sub>C X \<bullet> AllPay(cardNum) ;; X)"

text \<open> The Mondex action is a sample setup. It requires creates $cardNum$ cards each with 100 units
  present. \<close>

definition Mondex :: "index \<Rightarrow> action_mdx" where
"Mondex(cardNum) = (accts :=\<^sub>C entr\<^sub>u({0..10}\<^sub>u, \<lambda> x. 100) ;; Cycle(cardNum))"

subsection \<open> Pre/peri/post calculations \<close>

text \<open> The behaviour of a reactive program is described in three parts: (1) the precondition,
  that describes how the state and environment must behave to ensure valid behaviour; (2)
  the pericondition that describes the commitments the program makes whilst in an intermediate
  state in terms of events only; and (3) the postcondition that describes the commitments after
  the process terminates. The pericondition refers only to the trace, as the state is invisible
  in intermediate states -- it can only be observed through events. The pre- and postcondition
  can refer to both the state and the trace; although the form can only refer to a prefix
  of the trace and before state variables -- only the postcondition refers to after state. \<close>
  
lemma Pay_CSP [closure]: "Pay i j n is CSP"
  by (simp add: Pay_def closure)

text \<open> The precondition of pay requires that, under the assumption that a payment was requested
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

\<close>
  
lemma Pay_contract [rdes_def]:
  assumes "i \<noteq> j"
  shows
  "Pay i j n = 
    \<^bold>R\<^sub>s ( (\<I>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r 
           [(\<guillemotleft>i\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accts) \<or> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright>) \<or> \<guillemotleft>i\<guillemotright> \<in>\<^sub>u dom\<^sub>u(&accts) \<and> \<guillemotleft>j\<guillemotright> \<in>\<^sub>u dom\<^sub>u(&accts)]\<^sub>S\<^sub><) 
       
       \<turnstile> (\<E>(true,\<langle>\<rangle>, {(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u}\<^sub>u) \<or>
            \<E>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>, {(reject\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u}\<^sub>u) 
               \<triangleleft> \<guillemotleft>i\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accts) \<or> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R
            \<E>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>, {(accept\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u}\<^sub>u)) 

       \<diamondop> (\<Phi>(true,id,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u, (reject\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u\<rangle>) 
            \<triangleleft> \<guillemotleft>i\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accts) \<or> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R
          \<Phi>(true,[&accts \<mapsto>\<^sub>s &accts(\<guillemotleft>i\<guillemotright> \<mapsto> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a - \<guillemotleft>n\<guillemotright>, \<guillemotleft>j\<guillemotright> \<mapsto> &accts(\<guillemotleft>j\<guillemotright>)\<^sub>a + \<guillemotleft>n\<guillemotright>)\<^sub>u]
                ,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u, (accept\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u\<rangle>)))"
  using assms by (simp add: Pay_def closure, rdes_simp, simp add: pr_var_def, rel_auto)  
    
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
    
subsection \<open> Verification \<close>

text \<open> We perform verification by writing contracts that specify desired behaviours of our
  system. A contract @{term "[P \<turnstile> Q | R]\<^sub>C"} consists of three predicates that correspond to
  the pre-, peri-, and postconditions, respectively. The precondition talks about initial state
  variables and the $trace$ contribution via a special variable. The pericondition likewise
  talks about initial states and traces. The postcondition also talks about final states.

  We first show that any payment leaves the total value shared between the cards unchanged.
  This is under the assumption that at least two cards exist. The contract has as its precondition
  that initially the number of cards is $cardNum$. The pericondition is $true$ as we don't
  care about intermediate behaviour here. The postcondition has that the summation of the 
  sequence of card values remains the same, though of course individual records will change. \<close>

lemma uminus_inter_insert [simp]: 
  "(- A) \<inter> (- insert x B) = (- insert x A) \<inter> (- B)"
  by (auto)

theorem money_constant:
  assumes "finite cards" "i \<in> cards" "j \<in> cards" "i \<noteq> j" 
  shows "[dom\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cards\<guillemotright> \<turnstile> true | sum\<^sub>u($accts) =\<^sub>u sum\<^sub>u($accts\<acute>)]\<^sub>C \<sqsubseteq> Pay i j n"
\<comment> \<open> We first calculate the reactive design contract and apply refinement introduction \<close>
proof (simp add: assms Pay_contract, rule CRD_refine_rdes)    

  \<comment> \<open> Three proof obligations result for the pre/peri/postconditions. The first requires us to
    show that the contract's precondition is weakened by the implementation precondition. 
    It is because the implementation's precondition is under the assumption of receiving an
    input and the money amount constraints. We discharge by first calculating the precondition, 
    as done above, and then using the relational calculus tactic. \<close>

  from assms 
  show "`[dom\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cards\<guillemotright>]\<^sub>S\<^sub>< \<Rightarrow>
          \<I>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>) \<Rightarrow>\<^sub>r
          [(\<guillemotleft>i\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accts) \<or> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright>) \<or> 
            \<guillemotleft>i\<guillemotright> \<in>\<^sub>u dom\<^sub>u(&accts) \<and> \<guillemotleft>j\<guillemotright> \<in>\<^sub>u dom\<^sub>u(&accts)]\<^sub>S\<^sub><`"
    by (rel_auto)

  \<comment> \<open> The second is trivial as we don't care about intermediate states. \<close>
      
  show "[true]\<^sub>S\<^sub><\<lbrakk>x\<rightarrow>&tt\<rbrakk>\<lbrakk>r\<rightarrow>$ref\<acute>\<rbrakk> \<sqsubseteq>
    ([dom\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cards\<guillemotright>]\<^sub>S\<^sub>< \<and>
     (\<E>(true,\<langle>\<rangle>, {(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u}\<^sub>u) \<or>
      \<E>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>, {(reject\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u}\<^sub>u) \<triangleleft> \<guillemotleft>i\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accts) \<or> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R
         \<E>(true,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u\<rangle>, {(accept\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u}\<^sub>u)))"
    by (simp add: rpred usubst, rel_auto)

  \<comment> \<open> The third requires that we show that the postcondition implies that the total amount remains
    unaltered. We calculate the postcondition, and then use relational calculus. In this case, this
    is not enough and an additional property of lists is required (@{thm listsum_update}) that can
    be retrieved by sledgehammer. However, we actually had to prove that property first and add it to our library. \<close>
      
  from assms
  show "[sum\<^sub>u($accts) =\<^sub>u sum\<^sub>u($accts\<acute>)]\<^sub>S'\<lbrakk>x\<rightarrow>&tt\<rbrakk> \<sqsubseteq>
    ([dom\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cards\<guillemotright>]\<^sub>S\<^sub>< \<and>
     \<Phi>(true,id,\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u, (reject\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u\<rangle>) \<triangleleft> \<guillemotleft>i\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accts) \<or> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u 0 \<or> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a <\<^sub>u \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R
        \<Phi>(true,[&accts \<mapsto>\<^sub>s &accts(\<guillemotleft>i\<guillemotright> \<mapsto> &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a - \<guillemotleft>n\<guillemotright>, \<guillemotleft>j\<guillemotright> \<mapsto> &accts(\<guillemotleft>j\<guillemotright>)\<^sub>a + \<guillemotleft>n\<guillemotright>)\<^sub>u],\<langle>(pay\<cdot>(\<guillemotleft>i\<guillemotright>, \<guillemotleft>j\<guillemotright>, \<guillemotleft>n\<guillemotright>)\<^sub>u)\<^sub>u, (accept\<cdot>\<guillemotleft>i\<guillemotright>)\<^sub>u\<rangle>))"
    by (rel_auto, simp_all add: pfun_sums_upd_2)
qed
      
text \<open> The next property is that no card value can go below 0, assuming it was non-zero to start
  with. \<close>
  
theorem no_overdrafts:
  assumes "finite cards" "i \<in> cards" "j \<in> cards" "i \<noteq> j"
  shows "[dom\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cards\<guillemotright> \<turnstile> true | (\<^bold>\<forall> k \<bullet> \<guillemotleft>k\<guillemotright> \<in>\<^sub>u \<guillemotleft>cards\<guillemotright> \<and> $accts(\<guillemotleft>k\<guillemotright>)\<^sub>a \<ge>\<^sub>u 0 \<Rightarrow> $accts\<acute>(\<guillemotleft>k\<guillemotright>)\<^sub>a \<ge>\<^sub>u 0)]\<^sub>C \<sqsubseteq> Pay i j n"
  using assms
  apply (simp add: Pay_contract)
  apply (rule CRD_refine_rdes)
  apply (rel_auto)
  apply (rel_auto)
  apply (rel_simp)
  apply (metis diff_ge_0_iff_ge dual_order.trans le_add_same_cancel2 less_le not_le pfun_app_upd_1 pfun_app_upd_2)
done
  
text \<open> The next property shows liveness of transfers. If a payment is accepted, and we have enough
  money, then the acceptance of the transfer cannot be refused. Unlike the previous two examples,
  this is specified using the pericondition as we are talking about intermediate states and refusals. \<close>
  
theorem transfer_live:
  assumes "finite cards" "i \<in> cards" "j \<in> cards" "i \<noteq> j" "n > 0"
  shows "[dom\<^sub>u(&accts) =\<^sub>u \<guillemotleft>cards\<guillemotright>
         \<turnstile> \<guillemotleft>trace\<guillemotright> \<noteq>\<^sub>u \<langle>\<rangle> \<and> last\<^sub>u(\<guillemotleft>trace\<guillemotright>) =\<^sub>u (pay\<cdot>(\<guillemotleft>(i,j,k)\<guillemotright>))\<^sub>u \<and> \<guillemotleft>n\<guillemotright> \<le>\<^sub>u &accts(\<guillemotleft>i\<guillemotright>)\<^sub>a \<Rightarrow> (accept\<cdot>(\<guillemotleft>(i)\<guillemotright>))\<^sub>u \<notin>\<^sub>u \<guillemotleft>refs\<guillemotright>
         | true]\<^sub>C \<sqsubseteq> Pay i j n"
  using assms
  apply (simp add: Pay_contract)
  apply (rule CRD_refine_rdes)
  apply (rel_auto)+
done
    
end