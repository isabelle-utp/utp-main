section {* Cash Machine Case Study *}
text {*
  Names ending with 2 represents a full utp approach, where alphabets are used.
  The other approach is using e.g. ordinary records.
*}
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

record Card = 
  code :: Code
  cardId :: CardId
  accountId :: AccountId

alphabet Card_st = 
  code2 :: Code
  cardId2 :: CardId
  accountId2 :: AccountId


term "make"

record Account = 
  cards :: "(CardId, Cardholder) pfun"
  balance :: nat

alphabet Account_st = 
  cards2 :: "(CardId, Cardholder) pfun"
  balance2 :: nat
  transactions2 :: "Transaction_st list"
  
alphabet cm_st =
  accounts     :: "(AccountId, Account) pfun"
  accounts2     :: "(AccountId, Account_st) pfun"
  illegalCards :: "CardId set"
  curCard      :: "Card option"
  curCard2      :: "Card_st option"
  cardOk       :: "bool"
  retainedCards :: "Card set"
  retainedCards2 :: "Card_st set"
  local         :: nat
  local2 :: Card_st
  validateReturn :: ValidateResult
  balanceReturn :: nat

definition [prog_defs]: "cm_st_inv = (
  &curCard =\<^sub>u \<guillemotleft>None\<guillemotright> \<Rightarrow> \<not> &cardOk 
)"

subsection {* todo: *}
text {* 
  mk_System_inv: forall x in ((nat set, 'a cm_st_scheme) uexpr) . pred x
  Withdrawal: Combining multiple alphabets in sequential composition? 
  Withdrawal: Creating a new instance of an alphabet?
*}

declare [[show_types]]

term
 "\<^bold>\<forall> id1\<in>dom\<^sub>u(accountsP::((nat, Account_st) pfun, 'a cm_st_scheme) uexpr) \<bullet>
  \<^bold>\<forall> id2\<in>dom\<^sub>u(accountsP::((nat, Account_st) pfun, 'a cm_st_scheme) uexpr) \<bullet> \<guillemotleft>id1\<guillemotright> \<noteq>\<^sub>u \<guillemotleft>id2\<guillemotright>"

(*
definition mk_System_inv :: "((nat, Account_st) pfun, 'a cm_st_scheme) uexpr \<Rightarrow> (Card_st option, 'a cm_st_scheme) uexpr \<Rightarrow> (bool, 'a cm_st_scheme) uexpr \<Rightarrow> (bool, 'a cm_st_scheme) uexpr" where
"mk_System_inv accountsP curCardP cardOkP = (
  (curCardP =\<^sub>u \<guillemotleft>None\<guillemotright> \<Rightarrow> \<not> cardOkP) \<and>
  (\<forall> (id1 \<in> (\<lbrakk>dom\<^sub>u(accountsP)\<rbrakk>\<^sub>e)) \<bullet> 
)"
*)

(* 
inv mk_System(accs,-,curCard,cardOk,-) == 
      (curCard = nil => not cardOk) and 
      (forall id1, id2 in set dom accs &
        id1 <> id2 =>
        dom accs(id1).cards inter dom accs(id2).cards = {})
*)

definition IsLegalCard2 :: "(Card_st, 'a cm_st_scheme) uexpr \<Rightarrow> (CardId set, 'a cm_st_scheme) uexpr \<Rightarrow> (((nat, Account_st) pfun, 'a cm_st_scheme) uexpr) \<Rightarrow> (bool, 'a cm_st_scheme) uexpr" where
[prog_defs]: "IsLegalCard2 c cSet acc = 
  (((c:(cardId2)) \<notin>\<^sub>u cSet) \<and> 
  ((c:(accountId2)) \<in>\<^sub>u dom\<^sub>u(acc)) \<and>
    ((c:(cardId2)) \<in>\<^sub>u dom\<^sub>u((acc(c:(accountId2))\<^sub>a):(cards2))))"

definition IsLegalCard :: "Card \<Rightarrow> CardId set \<Rightarrow> (AccountId, Account) pfun \<Rightarrow> bool" where
"IsLegalCard mcard pillegalCards paccounts = 
  (((cardId mcard) \<notin> pillegalCards) \<and> 
  ((accountId mcard) \<in> (pdom paccounts)) \<and> 
  ((cardId mcard) \<in> (pdom (cards (paccounts(accountId mcard)\<^sub>p)))))"

definition Encode2 :: "(PinCode, cm_st) uexpr \<Rightarrow> (PinCode, cm_st) uexpr" where
[prog_defs]: "Encode2 p = p"

definition Encode :: "PinCode \<Rightarrow> nat" where
"Encode pin = pin"
term "\<guillemotleft>Card\<guillemotright>"

definition InsertCard2 :: "(Card_st, cm_st) uexpr \<Rightarrow> cm_st prog" where
[prog_defs]: "InsertCard2 c = ({&curCard2 =\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; curCard2 := (uop Some)c)"

definition InsertCard :: "Card \<Rightarrow> cm_st prog" where
[prog_defs]: "InsertCard(c) = ({&curCard =\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; curCard := \<guillemotleft>Some(c)\<guillemotright>)"

term "x:[P, \<guillemotleft>iv\<guillemotright>:(local) >\<^sub>u &local]"

lemma "\<Sigma>:[cm_st_inv \<and> &curCard =\<^sub>u \<guillemotleft>None\<guillemotright>, cm_st_inv] \<sqsubseteq> InsertCard(c)"
  by (prefine)

lemma "curCard := \<guillemotleft>Some undefined\<guillemotright> ; InsertCard(c) = abort" 
  by (peq)


definition Validate2 :: "(PinCode, cm_st) uexpr \<Rightarrow> cm_st prog" where
[prog_defs]: "Validate2 pin_uexpr = (
  {&curCard2 \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and> &cardOk =\<^sub>u false}\<^sub>p;
  (let codeOk::cm_st upred = (uop the)&curCard2:(code2) =\<^sub>u Encode2(pin_uexpr) in 
    let cardLegal::(bool, cm_st) uexpr = IsLegalCard2 (\<guillemotleft>the\<guillemotright> (&curCard2)\<^sub>a) &illegalCards &accounts2 in 
      if (cardLegal = false) 
      then retainedCards2 := (&retainedCards2 \<union>\<^sub>u {(uop the) &curCard2}\<^sub>u);cardOk := false;curCard2 := \<guillemotleft>None\<guillemotright>;validateReturn := \<guillemotleft>Retained\<guillemotright>
      else cardOk := codeOk;
        (if (&cardOk = true)
        then (validateReturn := \<guillemotleft>PinOk\<guillemotright>)
        else (validateReturn := \<guillemotleft>PinNotOk\<guillemotright>))))"

definition Validate :: "PinCode \<Rightarrow> cm_st prog" where
[prog_defs]: "Validate pin =  (
  let codeOk = (\<guillemotleft>code o the\<guillemotright>(&curCard)\<^sub>a) =\<^sub>u \<guillemotleft>Encode(pin)\<guillemotright> in
    let cardLegal = (trop IsLegalCard) (\<guillemotleft>the\<guillemotright> (&curCard)\<^sub>a) (&illegalCards) (&accounts) in 
      ( if(cardLegal = false) 
        then (retainedCards := (&retainedCards \<union>\<^sub>u {\<guillemotleft>the\<guillemotright> (&curCard)\<^sub>a}\<^sub>u);
          cardOk := false; 
          curCard := \<guillemotleft>None\<guillemotright>; 
          validateReturn := \<guillemotleft>Retained\<guillemotright>)
        else (cardOk := codeOk;(
          if (&cardOk = true) 
          then (validateReturn := \<guillemotleft>PinOk\<guillemotright>) 
          else (validateReturn := \<guillemotleft>PinNotOk\<guillemotright>)))))"

definition ReturnCard2 :: "cm_st prog" where
[prog_defs]: "ReturnCard2 = ({&curCard2 \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p; cardOk := false ; curCard2 := \<guillemotleft>None\<guillemotright>)"

definition ReturnCard :: "cm_st prog" where
[prog_defs]: "ReturnCard = ({&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p; cardOk := false ; curCard := \<guillemotleft>None\<guillemotright>)"

lemma "curCard := \<guillemotleft>None\<guillemotright> ; ReturnCard = abort"
  by (peq)

lemma "curCard := \<guillemotleft>Some(c)\<guillemotright> ; ReturnCard; ReturnCard = abort"
  by (peq)

definition GetBalance2 :: "cm_st prog" where
[prog_defs]: "GetBalance2 = (
  {&curCard2 \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and> &cardOk =\<^sub>u true \<and> 
  IsLegalCard2 (uop the &curCard2) &illegalCards &accounts2 =\<^sub>u true}\<^sub>p; 
  balanceReturn := (&accounts2((\<guillemotleft>the\<guillemotright>(&curCard2)\<^sub>a):(accountId2))\<^sub>a):(balance2))"

definition GetBalance :: "cm_st prog" where
[prog_defs]: "GetBalance = {&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; balanceReturn := \<guillemotleft>balance\<guillemotright> (&accounts((\<guillemotleft>accountId o the\<guillemotright>(&curCard)\<^sub>a))\<^sub>a)\<^sub>a"

(* Example of passing a value to return in
definition GetBalance :: "(nat \<Longrightarrow> cm_st) \<Rightarrow> cm_st prog" where
[prog_defs]: "GetBalance balanceReturn = {&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; balanceReturn := \<guillemotleft>balance\<guillemotright> (&accounts((\<guillemotleft>accountId o the\<guillemotright>(&curCard)\<^sub>a))\<^sub>a)\<^sub>a"

definition Average :: "cm_st prog" where
[prog_defs]: "Average = GetBalance local"
*)
(*
 MakeWithdrawal : nat * Date ==> bool
  MakeWithdrawal(amount,date) ==
    let mk_Card(-,cardId,accountId) = curCard,
        transaction = mk_Transaction(date,cardId,amount)        
    in
      if accounts(accountId).balance - amount >= 0 and 
        DateTotal(date,accounts(accountId).transactions^[transaction])
        <= dailyLimit
      then
        (accounts(accountId).balance := 
           accounts(accountId).balance - amount;
         accounts(accountId).transactions := 
           accounts(accountId).transactions ^ [transaction];
         return true)
     else 
       return false
  pre curCard <> nil and cardOk and IsLegalCard(curCard,illegalCards,accounts);
*)
term "trop"
term "filter"
term "bop (filter)"
term "[x \<leftarrow> [1,2,3].x>1]"

text {* 
  This cannot be defined using uexpr, 
  because it is not possible to iterate over a uexpe containing a list 
*}


primrec Sum :: "(real, 'a Transaction_st_scheme) uexpr list \<Rightarrow> (real, 'a Transaction_st_scheme) uexpr" where
"Sum (x#xs) = x + Sum(xs)" |
"Sum [] = 0"

definition DateTotal :: "Date \<Rightarrow> ((Transaction_st, 'a Transaction_st_scheme) uexpr) list \<Rightarrow> (real, 'a Transaction_st_scheme) uexpr" where
"DateTotal dateP transactionsP = (
  let amounts::(real, 'a Transaction_st_scheme) uexpr list = 
    (foldl (\<lambda>xs x . if((x):(dateT) = \<guillemotleft>dateP\<guillemotright>) then ((x):(amountT))#xs else xs) 
      [] transactionsP)
  in Sum amounts)" 

definition DateTotal2 :: "(Date, 'a Transaction_st_scheme) uexpr \<Rightarrow> ((Transaction_st, 'a Transaction_st_scheme) uexpr) list \<Rightarrow> _" where
"DateTotal2 dateP transactionsP = (
  (let filteredTransactions = [x <- transactionsP . (x):(dateT) = dateP] in 
    let mappedTransactions = map (\<lambda>x . (x):(amountT)) filteredTransactions in
      Sum mappedTransactions))"

(* How do I filter  (Transaction_st list, 'a Transaction_st_scheme) uexpr? *)
(* How do I map (Transaction_st list, 'a Transaction_st_scheme) uexpr? *)
definition DateTotal3 :: "Date \<Rightarrow> (Transaction_st list, 'a ) uexpr \<Rightarrow> (nat, 'a ) uexpr" where
"DateTotal3 dateP transactionsP = (
  let filteredTransactions = uop (filter (\<lambda>x . dateT\<^sub>v x = dateP)) transactionsP in
   (uop (\<lambda>tlist . sum_list (map amountT\<^sub>v tlist))) transactionsP)"

term "(uop (\<lambda>tlist . sum_list (map amountT\<^sub>v tlist)))"

term "uop (\<lambda>x::'a Transaction_st_scheme list . sum_list (map amountT\<^sub>v x))"
term "(uop (\<lambda>x::'a Transaction_st_scheme list . sum_list (map amountT\<^sub>v x)))
 (x::(Transaction_st list, 'a Transaction_st_scheme) uexpr)"

typ "unit (Transaction_st list, 'a Transaction_st_scheme) uexpr"
term "unit x::'a Transaction_st_scheme list"
term "dateT"
term "x:(dateT)"
typ "unit ('a Transaction_st_scheme list)"

find_theorems name:collect
definition TotalAmount :: "'a Transaction_st_scheme list \<Rightarrow> nat" where
"TotalAmount tlist = sum_list (map amountT\<^sub>v tlist)"

definition TotalAmount2 :: "_" where
"TotalAmount2 = (uop (\<lambda>tlist . sum_list (map amountT\<^sub>v tlist)))"
term "amountT\<^sub>v"
term "filter (\<lambda>x::'a Transaction_st_scheme . dateT\<^sub>v x = ''a'')"
term "uop (filter (\<lambda>x::'a Transaction_st_scheme . dateT\<^sub>v x = ''a''))"

typ "unit Transaction_st_scheme"

term "uop TotalAmount"
term "(uop TotalAmount) (&accounts2(1)\<^sub>a:(transactions2))"
term "TotalAmount2 (&accounts2(1)\<^sub>a:(transactions2))"
term "(uop length) (x::(Transaction_st list, 'a Transaction_st_scheme) uexpr) = \<guillemotleft>0\<guillemotright>"




definition TransactionsInvariant :: "((Transaction_st, 'a Transaction_st_scheme) uexpr) list \<Rightarrow> bool" where
"TransactionsInvariant transactionsP = (
  let transactionDates = List.coset(map (\<lambda>x . (x):(dateT)) transactionsP) in
    \<forall> dateP \<in> transactionDates . ((DateTotal2 dateP transactionsP) \<le>\<^sub>u \<guillemotleft>200\<guillemotright> = true))"


(* Example of returning a nat from a state space *)
(*definition GetBalanceFun :: "cm_st \<Rightarrow> nat" where
"GetBalanceFun = \<lbrakk>\<guillemotleft>balance\<guillemotright> (&accounts((\<guillemotleft>accountId o the\<guillemotright>(&curCard)\<^sub>a))\<^sub>a)\<^sub>a\<rbrakk>\<^sub>e"

definition GetBalanceApp :: "cm_st prog" where [prog_defs]:
"GetBalanceApp = {&curCard \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright>}\<^sub>p ; balanceReturn := (Abs_uexpr GetBalanceFun)"*)

definition ReportIllegalCard2 :: "(CardId, cm_st) uexpr \<Rightarrow> cm_st prog" where
[prog_defs]: "ReportIllegalCard2 cId = (illegalCards := (&illegalCards \<union>\<^sub>u {cId}\<^sub>u))"

definition ReportIllegalCard :: "CardId \<Rightarrow> cm_st prog" where
[prog_defs]: "ReportIllegalCard cId = (illegalCards := (&illegalCards \<union>\<^sub>u {\<guillemotleft>cId\<guillemotright>}\<^sub>u))"

definition AddAccount2 :: "(AccountId, cm_st) uexpr \<Rightarrow> (Account, cm_st) uexpr \<Rightarrow> cm_st prog" where
[prog_defs]: "AddAccount2 accId acc = (
  {accId \<notin>\<^sub>u dom\<^sub>u(&accounts)}\<^sub>p; 
  accounts := &accounts(accId \<mapsto> acc)\<^sub>u)"

definition AddAccount :: "AccountId \<Rightarrow> Account \<Rightarrow> cm_st prog" where
[prog_defs]: "AddAccount accId acc = 
  ({\<guillemotleft>accId\<guillemotright> \<notin>\<^sub>u dom\<^sub>u(&accounts)}\<^sub>p; 
  accounts := &accounts(\<guillemotleft>accId\<guillemotright> \<mapsto> \<guillemotleft>acc\<guillemotright>)\<^sub>u)"
term "((uop the)&curCard2):(cardId2)"

term "fst"
term "snd"
term "snd o snd"

term "&accounts2((cardL):(accountId2))\<^sub>a"
term "((x::((Cardholder, 'a cm_st_scheme) uexpr))):(name)"
(*
definition RequestStatement :: " _" where
"RequestStatement = (
  let cardIdP_accountIdP = ((uop the)&curCard2:(cardId2),(uop the)&curCard2:(accountId2)) in
    let accountL = &accounts2((snd cardIdP_accountIdP):(accountId2))\<^sub>a in
      let cardsP_balanceP_transactionsP = (&accountL):(cards)
      in ( (accountL:(cards2))(cardL:(cardId2))\<^sub>a:(name),1 ))"
*)
(*definition RequestStatement :: "AccountId \<Rightarrow> _" where
"RequestStatement accIdP= (
  let cardL = (uop the) &curCard2 in
    let accountL = &accounts2(cardL:(accountId2))\<^sub>a
    in ( (accountL:(cards2))(cardL:(cardId2))\<^sub>a:(name),1 ))"*)



term "put\<^bsub>dateT +\<^sub>L cardIdT +\<^sub>L amountT\<^esub>"

definition mk_transaction :: "(char list, 'a) uexpr \<Rightarrow> (nat, 'a) uexpr \<Rightarrow>
  (nat, 'a) uexpr \<Rightarrow> ('b Transaction_st_scheme, 'a) uexpr" where
"mk_transaction =   trop (curry o curry (put\<^bsub>dateT +\<^sub>L cardIdT +\<^sub>L amountT\<^esub> undefined))"



term "(balance2) := (&balance2)"

(* TODO: How do I update balance2? *)
definition MakeWithdrawal :: "nat \<Rightarrow> Date \<Rightarrow> _" where
"MakeWithdrawal amountP dateP = (
  let cardIdL = (uop the)&curCard2:(cardId2) 
  in 
    let accountIdL = (uop the)&curCard2:(accountId2) 
    in 
      let transactionL = mk_transaction \<guillemotleft>dateP\<guillemotright> cardIdL \<guillemotleft>amountP\<guillemotright> 
      in
        let allTransL = &accounts2(accountIdL)\<^sub>a:(transactions2) ^\<^sub>u \<langle>transactionL\<rangle> 
        in ( 
          if ((((&accounts2(accountIdL)\<^sub>a):(balance2) - \<guillemotleft>amountP\<guillemotright> \<ge>\<^sub>u \<guillemotleft>0\<guillemotright>) \<and> (DateTotal3 dateP allTransL \<le>\<^sub>u \<guillemotleft>200\<guillemotright>)) = true)
          then true
          else false))"

end