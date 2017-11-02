section {* Cash Machine Case Study *}

theory cash_machine
  imports "../utp_impl" Set 
begin

text {*
  The following is necessary to step through alphabeths, 
  e.g. alphabet1field:alphabet2field
 *}
syntax
  "_ulens_expr" :: "logic \<Rightarrow> svid \<Rightarrow> logic" ("_:'(_')" [100,100] 100)

translations
  "_ulens_expr e x" == "CONST uop get\<^bsub>x\<^esub> e"

datatype ValidateResult = PinOk | PinNotOk | Retained
type_synonym Name = string
type_synonym AccountId = nat
type_synonym Code = nat
type_synonym CardId = nat
type_synonym PinCode = nat
type_synonym Date = string

alphabet Transaction_st = 
        dateT :: Date
        cardIdT :: CardId
        amountT :: nat

alphabet Cardholder = 
  name :: Name

alphabet Card_st = 
  code :: Code
  cardId :: CardId
  accountId :: AccountId

alphabet Account_st = 
  cards :: "(CardId, Cardholder) pfun"
  balance :: nat
  transactions :: "Transaction_st list"
  
alphabet cm_st =
  accounts     :: "(AccountId, Account_st) pfun"
  illegalCards :: "CardId set"
  curCard      :: "Card_st option"
  cardOk       :: "bool"
  retainedCards :: "Card_st set"
  local :: Card_st
  validateReturn :: ValidateResult
  balanceReturn :: nat

declare [[show_types]]

subsection {* Utilities *}
definition mk_transaction :: "char list * nat * nat \<Rightarrow> Transaction_st" where
[prog_defs]: "mk_transaction = (\<lambda> (xs, i, j). Transaction_st.make xs i j)"

subsection {* Functions and Invariants *}

(* TODO: cm_st_inv is to be replaced by SystemInvariant *)
definition [prog_defs]: "cm_st_inv = (
  &curCard =\<^sub>u \<guillemotleft>None\<guillemotright> \<Rightarrow> \<not> &cardOk 
)"

definition SystemInvariant :: "(AccountId, Account_st) pfun * Card_st option * bool \<Rightarrow> _" where
[prog_defs]: "SystemInvariant = (\<lambda>(accs, cardP, cardOkP) . 
  ((cardP = None \<longrightarrow> \<not> cardOkP) \<and> 
  (\<forall> id1  \<in> (pdom accs) . (\<forall> id2 \<in> (pdom accs) . (id1 \<noteq> id2) \<longrightarrow> 
  (pdom (cards\<^sub>v(accs(id1)\<^sub>p)) \<inter> pdom (cards\<^sub>v(accs(id1)\<^sub>p)) = {})))))"

definition DateTotal :: "Date * Transaction_st list \<Rightarrow> nat" where
[prog_defs]: "DateTotal  = (\<lambda>(d, ts) . foldl (\<lambda> (acc::nat) (x::Transaction_st) . 
  if (dateT\<^sub>v x = (d::Date)) then acc + amountT\<^sub>v x else acc) 
  (0::nat) (ts::Transaction_st list))"

definition TransactionsInvariant :: "Transaction_st list \<Rightarrow> bool" where
[prog_defs]: "TransactionsInvariant ts = (\<forall> d \<in> List.coset(map (\<lambda>x . dateT\<^sub>v x) ts) . DateTotal(d,ts) < 200)"

definition IsLegalCard :: "Card_st * CardId set * (AccountId, Account_st) pfun \<Rightarrow> bool" where
[prog_defs]: "IsLegalCard = (\<lambda>(mcard, pillegalCards, paccounts) .
  (((cardId\<^sub>v mcard) \<notin> pillegalCards) \<and> 
  ((accountId\<^sub>v mcard) \<in> (pdom paccounts)) \<and> 
  ((cardId\<^sub>v mcard) \<in> (pdom (cards\<^sub>v (paccounts(accountId\<^sub>v mcard)\<^sub>p))))))"

definition Encode :: "PinCode \<Rightarrow> PinCode" where
[prog_defs]: "Encode = id"

definition Sum :: "real list \<Rightarrow> real" where
[prog_defs]: "Sum = sum_list"

subsection {* Operations *}

definition InsertCard :: "Card_st \<Rightarrow> cm_st prog" where
[prog_defs]: "InsertCard c = ({&curCard =\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; curCard := (uop Some)\<guillemotleft>c\<guillemotright>)"

definition Validate :: "(ValidateResult \<Longrightarrow> 'a cm_st_scheme) \<Rightarrow> PinCode \<Rightarrow> 'a cm_st_scheme prog" where
[prog_defs]: "Validate ret p = ({&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and> \<not> &cardOk}\<^sub>p;(
  let codeOk =  (uop the)&curCard:(code) =\<^sub>u \<guillemotleft>Encode(p)\<guillemotright> in 
    let cardLegal = \<guillemotleft>IsLegalCard\<guillemotright>((\<guillemotleft>the\<guillemotright> (&curCard)\<^sub>a, &illegalCards, &accounts)\<^sub>u)\<^sub>a in
      if (\<not> cardLegal) 
      \<rightarrow> (retainedCards := (&retainedCards \<union>\<^sub>u {(uop the) &curCard}\<^sub>u);
        cardOk := false;curCard := \<guillemotleft>None\<guillemotright>; ret := \<guillemotleft>Retained\<guillemotright>) 
      else cardOk := codeOk;if &cardOk \<rightarrow> ret := \<guillemotleft>PinOk\<guillemotright>  else ret := \<guillemotleft>PinNotOk\<guillemotright> fi fi))"

definition ReturnCard :: "cm_st prog" where
[prog_defs]: "ReturnCard = ({&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p; cardOk := false ; curCard := \<guillemotleft>None\<guillemotright>)"

definition GetBalance :: "(nat \<Longrightarrow> cm_st) \<Rightarrow> cm_st prog" where
[prog_defs]: "GetBalance ret = (
  {&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and> &cardOk \<and> 
  \<guillemotleft>IsLegalCard\<guillemotright>((\<guillemotleft>the\<guillemotright> (&curCard)\<^sub>a, &illegalCards, &accounts)\<^sub>u)\<^sub>a}\<^sub>p; 
  ret := (&accounts((\<guillemotleft>the\<guillemotright>(&curCard)\<^sub>a):(accountId))\<^sub>a):(balance))"

(* TODO: MakeWithdrawal needs an implementation on 
  (&accounts(accountIdL)\<^sub>a):(balance) := \<guillemotleft>1\<guillemotright>
*)

definition MakeWithdrawal :: "nat \<Rightarrow> Date \<Rightarrow> _ \<Rightarrow> _" where
[prog_defs]: "MakeWithdrawal amountP dateP ret = 
   {&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and> &cardOk \<and> \<guillemotleft>IsLegalCard\<guillemotright>((\<guillemotleft>the\<guillemotright> (&curCard)\<^sub>a, &illegalCards, &accounts)\<^sub>u)\<^sub>a}\<^sub>p;
  (let cardIdL = (uop the)&curCard:(cardId) 
  in 
    let accountIdL = (uop the)&curCard:(accountId)
    in 
      let transactionL = \<guillemotleft>mk_transaction\<guillemotright>(\<guillemotleft>dateP\<guillemotright>, cardIdL, \<guillemotleft>amountP\<guillemotright>)\<^sub>a 
      in
        let allTransL = &accounts(accountIdL)\<^sub>a:(transactions) ^\<^sub>u \<langle>transactionL\<rangle> 
        in (
          if (((&accounts(accountIdL)\<^sub>a):(balance) - \<guillemotleft>amountP\<guillemotright> \<ge>\<^sub>u \<guillemotleft>0\<guillemotright>) \<and> (\<guillemotleft>DateTotal\<guillemotright>(\<guillemotleft>dateP\<guillemotright>, allTransL)\<^sub>a \<le>\<^sub>u \<guillemotleft>200\<guillemotright>)) \<rightarrow>
             (ret := true;undefined) 
          else ret := false;undefined
          fi ))"

definition RequestStatement :: "_" where 
[prog_defs]: "RequestStatement ret = 
  {&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and> &cardOk \<and> \<guillemotleft>IsLegalCard\<guillemotright>((\<guillemotleft>the\<guillemotright> (&curCard)\<^sub>a, &illegalCards, &accounts)\<^sub>u)\<^sub>a}\<^sub>p;
  (let acc = &accounts((uop the) &curCard:(accountId))\<^sub>a in 
    let c = acc:(cards) in 
      ret := (c(uop the &curCard:(accountId))\<^sub>a:(name), acc:(transactions), acc:(balance))\<^sub>u)"

definition ReportIllegalCard :: "(CardId, cm_st) uexpr \<Rightarrow> cm_st prog" where
[prog_defs]: "ReportIllegalCard cId = (illegalCards := (&illegalCards \<union>\<^sub>u {cId}\<^sub>u))"

definition AddAccount :: "(AccountId, cm_st) uexpr \<Rightarrow> (Account_st, cm_st) uexpr \<Rightarrow> cm_st prog" where
[prog_defs]: "AddAccount accId acc = ({accId \<notin>\<^sub>u uop pdom &accounts}\<^sub>p;accounts := &accounts(accId \<mapsto> acc)\<^sub>u)"

subsection {* Proofs *}

lemma "\<Sigma>:[cm_st_inv \<and> &curCard =\<^sub>u \<guillemotleft>None\<guillemotright>, cm_st_inv] \<sqsubseteq> InsertCard(c)"
  by (prefine)

lemma "curCard := \<guillemotleft>Some undefined\<guillemotright> ; InsertCard(c) = abort" 
  by (peq)

lemma "curCard := \<guillemotleft>None\<guillemotright> ; ReturnCard = abort"
  by (peq)

lemma "curCard := \<guillemotleft>Some(c)\<guillemotright> ; ReturnCard; ReturnCard = abort"
  by (peq)

subsection {* Notes *}
(* Example of forall in UTP *)
term
 "\<^bold>\<forall> id1\<in>dom\<^sub>u(accountsP::((nat, Account_st) pfun, 'a cm_st_scheme) uexpr) \<bullet>
  \<^bold>\<forall> id2\<in>dom\<^sub>u(accountsP::((nat, Account_st) pfun, 'a cm_st_scheme) uexpr) \<bullet> \<guillemotleft>id1\<guillemotright> \<noteq>\<^sub>u \<guillemotleft>id2\<guillemotright>"


(* Example of using mk_transaction *)
term "\<guillemotleft>mk_transaction\<guillemotright>(\<langle>\<rangle>, 0, &x)\<^sub>a"

(* Example of updating a mapping *)
term "accounts := &accounts(\<guillemotleft>aid\<guillemotright> \<mapsto> &accounts(\<guillemotleft>aid\<guillemotright>)\<^sub>a)\<^sub>u"

end