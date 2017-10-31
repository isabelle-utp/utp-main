section {* Cash Machine Case Study *}

theory cash_machine
  imports "../utp_impl" Set
begin

datatype validateResult = PinOk | PinNotOk | Retained

type_synonym Name = string
type_synonym AccountId = nat
type_synonym Code = nat
type_synonym CardId = nat
type_synonym PinCode = nat

record Cardholder = 
  name :: Name

record Card = 
  code :: Code
  cardId :: CardId
  accountId :: AccountId

term "make"

record Account = 
  cards :: "(CardId, Cardholder) pfun"
  balance :: nat
  
alphabet cm_st =
  accounts     :: "(AccountId, Account) pfun"
  illegalCards :: "CardId set"
  curCard      :: "Card option"
  cardOk       :: "bool"
  retainedCards :: "Card set"
  (*TODO: How do I return this from getBalance()?*)
  balanceReturn :: nat

definition IsLegalCard :: "Card \<Rightarrow> CardId set \<Rightarrow> (AccountId, Account) pfun \<Rightarrow> bool" where
"IsLegalCard mcard pillegalCards paccounts = 
  (((cardId mcard) \<notin> pillegalCards) \<and> 
  ((accountId mcard) \<in> (pdom paccounts)) \<and> 
  ((cardId mcard) \<in> (pdom (cards (paccounts(accountId mcard)\<^sub>p)))))"

(* TODO: Should this be regular HOL or UTP? *)
definition Encode :: "PinCode \<Rightarrow> nat" where
"Encode pin = pin" (* TBD *)

definition InsertCard :: "Card \<Rightarrow> cm_st prog" where
[prog_defs]: "InsertCard(c) = ({&curCard =\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; curCard := \<guillemotleft>Some(c)\<guillemotright>)"

lemma "curCard := \<guillemotleft>Some undefined\<guillemotright> ; InsertCard(c) = abort" 
  by (peq)

lemma "curCard := \<guillemotleft>None\<guillemotright> ; InsertCard(c); InsertCard(d) = abort"
  by (peq)

term "the (\<lbrakk>&curCard\<rbrakk>\<^sub>e cm_st)"
term "\<guillemotleft>code o the\<guillemotright>(&curCard)\<^sub>a"

term "trop IsLegalCard"
term "(&curCard)"
term "\<guillemotleft>the\<guillemotright>"
term "\<guillemotleft>the\<guillemotright> (&curCard)\<^sub>a"


(* TODO: Return a value *)
definition Validate :: "PinCode \<Rightarrow> cm_st prog" where
"Validate pin = ( 
  let codeOK::bool = (\<guillemotleft>code o the\<guillemotright>(&curCard)\<^sub>a) = \<guillemotleft>(Encode(pin))\<guillemotright> in
      let cardLegal = (trop IsLegalCard) (\<guillemotleft>the\<guillemotright> (&curCard)\<^sub>a) (&illegalCards) (&accounts) in 
        if (\<not>cardLegal) then (retainedCards := (&retainedCards \<union>\<^sub>u {(&curCard)}\<^sub>u)) else (retainedCards := &retainedCards))"

definition ReturnCard :: "cm_st prog" where
[prog_defs]: "ReturnCard = ({&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p; cardOk := false ; curCard := \<guillemotleft>None\<guillemotright>)"

lemma "curCard := \<guillemotleft>None\<guillemotright> ; ReturnCard = abort"
  by (peq)

lemma "curCard := \<guillemotleft>Some(c)\<guillemotright> ; ReturnCard; ReturnCard = abort"
  by (peq)

(*lemma "curCard := \<guillemotleft>Some(c)\<guillemotright> ; ReturnCard \<noteq> abort"
  by (peq)*)

term "accountId o the"
term "(\<guillemotleft>accountId o the\<guillemotright> (&curCard)\<^sub>a) "
term "\<guillemotleft>1\<guillemotright>"

term "(&accounts ((\<guillemotleft>accountId o the\<guillemotright> (&curCard)\<^sub>a) )\<^sub>a )"
term "(\<guillemotleft>balance\<guillemotright> (&accounts ((\<guillemotleft>accountId o the\<guillemotright> (&curCard)\<^sub>a))\<^sub>a)\<^sub>a)"

definition GetBalance :: "cm_st prog" where
[prog_defs]: "GetBalance = {&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; balanceReturn := \<guillemotleft>balance\<guillemotright> (&accounts((\<guillemotleft>accountId o the\<guillemotright>(&curCard)\<^sub>a))\<^sub>a)\<^sub>a"

(*
definition GetBalanceFun :: "cm_st \<Rightarrow> nat" where
"GetBalanceFun = \<lbrakk>\<guillemotleft>balance\<guillemotright> (&accounts((\<guillemotleft>accountId o the\<guillemotright>(&curCard)\<^sub>a))\<^sub>a)\<^sub>a\<rbrakk>\<^sub>e"

definition GetBalanceApp :: "cm_st prog" where [prog_defs]:
"GetBalanceApp = {&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; balanceReturn := (Abs_uexpr GetBalanceFun)"*)

definition ReportIllegalCard :: "CardId \<Rightarrow> cm_st prog" where
[prog_defs]: "ReportIllegalCard cId = (illegalCards := (&illegalCards \<union>\<^sub>u {\<guillemotleft>cId\<guillemotright>}\<^sub>u))"

definition AddAccount :: "AccountId \<Rightarrow> Account \<Rightarrow> cm_st prog" where
[prog_defs]: "AddAccount accId acc = 
  ({\<guillemotleft>accId\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accounts)}\<^sub>p; 
  accounts := &accounts(\<guillemotleft>accId\<guillemotright> \<mapsto> \<guillemotleft>acc\<guillemotright>)\<^sub>u)"






end