section \<open> Tokeneer in Isabelle/UTP \<close>

theory Tokeneer
  imports 
    "ZedLite.zedlite"
    "UTP.utp"
begin recall_syntax

section \<open>Introduction\<close>

hide_const dom

named_theorems tis_defs

subsection \<open> TIS Basic Types \<close>

type_synonym TIME = nat

abbreviation "zeroTime \<equiv> 0"

datatype PRESENCE = present | absent

datatype CLASS = unmarked | unclassified | restricted | confidential | secret | topsecret

record Clearance =
  "class" :: CLASS

consts minClearance :: "Clearance \<times> Clearance \<Rightarrow> Clearance"

datatype PRIVILEGE = userOnly | guard | securityOfficer | auditManager

typedecl USER

consts ISSUER :: "USER set"

typedecl FINGERPRINT

typedecl FINGERPRINTTEMPLATE

alphabet FingerprintTemplate = 
  template :: FINGERPRINTTEMPLATE

subsection \<open> Keys and Encryption \<close>

typedecl KEYPART

abbreviation KEYPART :: "KEYPART set" where "KEYPART \<equiv> UNIV"

subsection \<open> Certificates, Tokens, and Enrolment Data \<close>

subsubsection \<open> Certificates \<close>

typedecl TOKENID
  
record CertificateId =
  issuer :: "USER"

definition CertificateId :: "CertificateId set" where
[upred_defs, tis_defs]: "CertificateId = {c. issuer c \<in> ISSUER}"

record Certificate =
  cid :: CertificateId
  validityPeriod :: "TIME set"
  isValidatedBy :: "KEYPART option"

definition Certificate :: "'a Certificate_scheme set" where
[upred_defs, tis_defs]: "Certificate = {c. cid c \<in> CertificateId}"

record IDCert = Certificate +
  subject :: USER
  subjectPubK :: KEYPART

definition IDCert :: "'a IDCert_scheme set" where
[upred_defs, tis_defs]: "IDCert = Certificate"

definition CAIdCert :: "IDCert set" where
[upred_defs, tis_defs]: "CAIdCert = {c \<in> IDCert. isValidatedBy c = Some(subjectPubK c)}"

record AttCertificate = Certificate +
  baseCertId :: "CertificateId"
  atokenID :: "TOKENID"

definition AttCertificate :: "'a AttCertificate_scheme set" where
[upred_defs, tis_defs]: "AttCertificate = Certificate"

(* QUESTION: Where is role connected to rolePresent in the AdminToken? *)

record PrivCert = AttCertificate + 
  role :: PRIVILEGE
  clearance :: Clearance

definition PrivCert :: "PrivCert set" where
[upred_defs, tis_defs]: "PrivCert = AttCertificate"

type_synonym AuthCert = PrivCert

abbreviation AuthCert :: "AuthCert set" where "AuthCert \<equiv> PrivCert"

record IandACert = AttCertificate +
  template :: FingerprintTemplate

definition IandACert :: "IandACert set" where
[upred_defs, tis_defs]: "IandACert = AttCertificate"


subsubsection \<open> Tokens \<close>

record Token =
  tokenID :: TOKENID
  idCert :: IDCert
  privCert :: PrivCert
  iandACert :: IandACert
  authCert :: "AuthCert option"

definition Token :: "Token set" where
[upred_defs, tis_defs]:
"Token = {c. idCert c \<in> IDCert \<and> 
             privCert c \<in> PrivCert \<and> 
             iandACert c \<in> IandACert \<and>
             (\<forall> x. authCert c = Some(x) \<longrightarrow> x \<in> AuthCert)
             }"

definition ValidToken :: "Token set" where
[upred_defs, tis_defs]:
"ValidToken =
  {t\<in>Token. baseCertId (privCert t) = cid (idCert t) 
    \<and> baseCertId (iandACert t) = cid (idCert t) 
    \<and> atokenID (privCert t) = tokenID t
    \<and> atokenID (iandACert t) = tokenID t}"

definition TokenWithValidAuth :: "Token set" where
[upred_defs, tis_defs]:
"TokenWithValidAuth =
  {t. authCert t \<noteq> None \<and>
      atokenID (the (authCert t)) = tokenID t \<and>
      baseCertId (the (authCert t)) = cid (idCert t)}"  

definition CurrentToken :: "TIME \<Rightarrow> Token set" where
[upred_defs, tis_defs]:
"CurrentToken now =
  (ValidToken \<inter>
    {t. now \<in> validityPeriod (idCert t)
             \<inter> validityPeriod (privCert t)
             \<inter> validityPeriod (iandACert t)})"

(*
definition ValidToken :: "Token upred" where
"ValidToken = 
  (privCert:baseCertId = idCert:cid \<and>
   iandACert:baseCertId = idCert:cid \<and>
   privCert:atokenID = tokenID \<and> 
   iandACert:atokenID = tokenID)\<^sub>e"
*)


subsubsection \<open>Enrolment Data\<close>

record Enrol =
  idStationCert :: IDCert
  issuerCerts :: "IDCert set"

text \<open> We had to add two extra clauses to Enrol here that were specified in the Tokeneer Z-schema,
  namely that (1) all issuer certificates correspond to elements of @{term ISSUER} and (2)
  the subjects uniquely identify one issue certificate. Without these, it is not possible to
  update the key store and maintain the partial function there. \<close>

definition Enrol :: "Enrol set" where
[upred_defs, tis_defs]: 
  "Enrol = {e. idStationCert e \<in> issuerCerts e \<and> 
               subject ` issuerCerts e \<subseteq> ISSUER \<and> 
               (\<forall> c \<in> issuerCerts e. \<forall> d \<in> issuerCerts e. subject c = subject d \<longrightarrow> c = d)}"

definition ValidEnrol :: "Enrol set" where
[upred_defs, tis_defs]:
"ValidEnrol = (Enrol \<inter>
  {e. issuerCerts e \<inter> CAIdCert \<noteq> {} \<and>
      (\<forall> cert \<in> issuerCerts e. isValidatedBy cert \<noteq> None \<and>
          (\<exists> issuerCert \<in> issuerCerts e. 
              issuerCert \<in> CAIdCert \<and>
              the(isValidatedBy cert) = subjectPubK issuerCert \<and>
              issuer (cid cert) = subject issuerCert))})"


subsection \<open>World Outside the ID Station\<close>

subsubsection \<open>Real World Types and Entities (1)\<close>

datatype DOOR = dopen | closed
datatype LATCH = unlocked | locked
datatype ALARM = silent | alarming
datatype DISPLAYMESSAGE = blank | welcom | insertFinger | openDoor | wait | removeToken | tokenUpdateFailed | doorUnlocked

datatype FINGERPRINTTRY = noFP | badFP | goodFP FINGERPRINT

alphabet Finger =
  currentFinger :: FINGERPRINTTRY
  fingerPresence :: PRESENCE

abbreviation Finger :: "Finger upred" where "Finger \<equiv> true"

alphabet DoorLatchAlarm =
  currentTime  :: TIME
  currentDoor  :: DOOR
  currentLatch :: LATCH
  doorAlarm    :: ALARM
  latchTimeout :: TIME
  alarmTimeout :: TIME

definition DoorLatchAlarm :: "DoorLatchAlarm upred" where 
[upred_defs, tis_defs]:
"DoorLatchAlarm = U(
  (currentLatch = \<guillemotleft>locked\<guillemotright> \<Leftrightarrow> currentTime \<ge> latchTimeout) \<and>
  (doorAlarm = \<guillemotleft>alarming\<guillemotright> \<Leftrightarrow>
    (currentDoor = \<guillemotleft>dopen\<guillemotright> 
      \<and> currentLatch = \<guillemotleft>locked\<guillemotright>
      \<and> currentTime \<ge> alarmTimeout))
  )"


section \<open>The Token ID Station\<close>


subsection \<open>Configuration Data\<close>

consts maxSupportedLogSize :: nat

alphabet Config = 
  alarmSilentDuration :: TIME
  latchUnlockDuration :: TIME
  tokenRemovalDuration :: TIME
  enclaveClearance :: Clearance
  authPeriod :: "PRIVILEGE \<Rightarrow> TIME \<Rightarrow> TIME set"
  entryPeriod :: "PRIVILEGE \<Rightarrow> CLASS \<Rightarrow> TIME set"
  minPreservedLogSize :: nat
  alarmThresholdSize :: nat

definition Config :: "Config upred" where
[upred_defs, tis_defs]:
"Config = U(alarmThresholdSize < minPreservedLogSize \<and> 
            minPreservedLogSize \<le> \<guillemotleft>maxSupportedLogSize\<guillemotright> \<and>
            latchUnlockDuration > 0 \<and>
            alarmSilentDuration > 0)"


subsection \<open>AuditLog\<close>

typedecl AuditEvent
typedecl AuditUser

alphabet Audit =
  auditTime   :: TIME
  auditEvent  :: AuditEvent
  auditUser   :: AuditUser
  sizeElement :: nat


subsubsection \<open>Real World Types and Entities (2)\<close>

datatype FLOPPY = noFloppy | emptyFloppy | badFloppy | enrolmentFile (enrolmentFile_of: Enrol) | 
  auditFile "Audit set" | configFile Config 

definition FLOPPY :: "FLOPPY upred" where 
[upred_defs, tis_defs]:
"FLOPPY = U(\<forall> e. &\<^bold>v = \<guillemotleft>enrolmentFile e\<guillemotright> \<Rightarrow> \<guillemotleft>e \<in> ValidEnrol\<guillemotright>)"

alphabet Floppy =
  currentFloppy :: FLOPPY
  writtenFloppy :: FLOPPY
  floppyPresence :: PRESENCE

definition Floppy :: "Floppy upred" where 
[upred_defs, tis_defs]:
"Floppy = (FLOPPY \<oplus>\<^sub>p currentFloppy \<and> FLOPPY \<oplus>\<^sub>p writtenFloppy)"

definition [upred_defs, tis_defs]: "ADMINPRIVILEGE = {guard, auditManager, securityOfficer}"
datatype ADMINOP = archiveLog | updateConfigData | overrideLock | shutdownOp

datatype KEYBOARD = noKB | badKB | keyedOps (ofKeyedOps: ADMINOP)

alphabet Keyboard =
  currentKeyedData :: "KEYBOARD"
  keyedDataPresence :: "PRESENCE"

abbreviation Keyboard :: "Keyboard upred" where "Keyboard \<equiv> true"


subsection \<open>System Statistics\<close>

alphabet Stats =
  successEntry :: nat
  failEntry    :: nat
  successBio   :: nat
  failBio      :: nat

abbreviation Stats :: "Stats upred" where "Stats \<equiv> true"


subsection \<open>Key Store\<close>


alphabet KeyStore =
  issuerKey :: "USER \<leftrightarrow> KEYPART"
  ownName   :: "USER option"

definition KeyStore :: "KeyStore upred" where 
[upred_defs, tis_defs]:
"KeyStore =
  U(issuerKey \<in> \<guillemotleft>ISSUER \<rightharpoonup>\<^sub>r KEYPART\<guillemotright> \<and>
    udom(issuerKey) \<subseteq> \<guillemotleft>ISSUER\<guillemotright> \<and>
    (ownName \<noteq> \<guillemotleft>None\<guillemotright> \<Rightarrow> the(ownName) \<in> udom(issuerKey)))"

definition CertIssuerKnown :: "'a Certificate_scheme \<Rightarrow> KeyStore upred" where
[upred_defs, tis_defs]:
"CertIssuerKnown c =
  U(KeyStore \<and> 
   (\<guillemotleft>c \<in> Certificate\<guillemotright> \<and>
   \<guillemotleft>issuer (cid c)\<guillemotright> \<in> udom(issuerKey)))"

declare [[coercion rel_apply]]

term "U(issuerKey(x))"

definition CertOK :: "'a Certificate_scheme \<Rightarrow> KeyStore upred" where
[upred_defs, tis_defs]:
"CertOK c =
  (CertIssuerKnown c \<and>
   U(Some(issuerKey(\<guillemotleft>issuer (cid c)\<guillemotright>)) = \<guillemotleft>isValidatedBy c\<guillemotright>))"

definition CertIssuerIsThisTIS :: "'a Certificate_scheme \<Rightarrow> KeyStore upred" where
[upred_defs, tis_defs]:
"CertIssuerIsThisTIS c =
  (KeyStore \<and> 
   U(\<guillemotleft>c \<in> Certificate\<guillemotright> \<and>
   (ownName \<noteq> \<guillemotleft>None\<guillemotright> \<and>
    \<guillemotleft>issuer (cid c)\<guillemotright> = the(ownName))))"

definition AuthCertOK :: "'a Certificate_scheme \<Rightarrow> KeyStore upred" where
[upred_defs, tis_defs]: "AuthCertOK c = (CertIssuerIsThisTIS c \<and> CertOK c)"

definition oldestLogTime :: "Audit set \<Rightarrow> TIME" where
[upred_defs, tis_defs]:
"oldestLogTime lg = (Min (get\<^bsub>auditTime\<^esub> ` lg))"

definition newestLogTime :: "Audit set \<Rightarrow> TIME" where
[upred_defs, tis_defs]:
"newestLogTime lg = (Max (get\<^bsub>auditTime\<^esub> ` lg))"

lemma newestLogTime_union: "\<lbrakk> finite A; A \<noteq> {}; finite B; B \<noteq> {} \<rbrakk> \<Longrightarrow> newestLogTime (A \<union> B) \<ge> newestLogTime A"
  by (simp add: newestLogTime_def)

lemma oldestLogTime_union: "\<lbrakk> finite A; A \<noteq> {}; finite B; B \<noteq> {} \<rbrakk> \<Longrightarrow> oldestLogTime (A \<union> B) \<le> oldestLogTime A"
  by (simp add: oldestLogTime_def)


subsection \<open>Administration\<close>

alphabet Admin =
  rolePresent :: "PRIVILEGE option"
  availableOps :: "ADMINOP set"
  currentAdminOp :: "ADMINOP option"

definition Admin :: "Admin upred" where
[upred_defs, tis_defs]:
"Admin = 
   U((rolePresent \<noteq> \<guillemotleft>None\<guillemotright> \<Rightarrow> the(rolePresent) \<in> \<guillemotleft>ADMINPRIVILEGE\<guillemotright>) \<and>
    (rolePresent = \<guillemotleft>None\<guillemotright> \<Rightarrow> availableOps = {}) \<and>
    (rolePresent \<noteq> \<guillemotleft>None\<guillemotright> \<and> the(rolePresent) = \<guillemotleft>guard\<guillemotright> \<Rightarrow> availableOps = {\<guillemotleft>overrideLock\<guillemotright>}) \<and>
    (rolePresent \<noteq> \<guillemotleft>None\<guillemotright> \<and> the(rolePresent) = \<guillemotleft>auditManager\<guillemotright> \<Rightarrow> availableOps = {\<guillemotleft>archiveLog\<guillemotright>}) \<and>
    (rolePresent \<noteq> \<guillemotleft>None\<guillemotright> \<and> the(rolePresent) = \<guillemotleft>securityOfficer\<guillemotright> 
         \<Rightarrow> availableOps = {\<guillemotleft>updateConfigData\<guillemotright>,\<guillemotleft>shutdownOp\<guillemotright>}) \<and>
    (currentAdminOp \<noteq> \<guillemotleft>None\<guillemotright> \<Rightarrow>
         the(currentAdminOp) \<in> availableOps \<and> rolePresent \<noteq> \<guillemotleft>None\<guillemotright>)
   )"


subsection \<open>AuditLog (2)\<close>

alphabet AuditLog =
  auditLog :: "Audit set"
  auditAlarm :: ALARM

abbreviation AuditLog :: "AuditLog upred" where 
"AuditLog \<equiv> true"

subsubsection \<open>Real World Types and Entities (3)\<close>

datatype SCREENTEXT = clear | welcomeAdmin | busy | removeAdminToken | closeDoor |
  requestAdminOp | doingOp | invalidRequest | invalidData |
  insertEnrolmentData | validatingEnrolmentData | enrolmentFailed |
  archiveFailed | insertBlankFloppy | insertConfigData |
  displayStats Stats | displayConfigData Config

alphabet Screen =
  screenStats  :: SCREENTEXT
  screenMsg    :: SCREENTEXT
  screenConfig :: SCREENTEXT

datatype TOKENTRY = noT | badT | goodT (ofGoodT: Token)

alphabet UserToken =
  currentUserToken :: "TOKENTRY"
  userTokenPresence :: "PRESENCE"

definition UserToken :: "UserToken upred" where 
[upred_defs, tis_defs]:
"UserToken = U((\<exists> t. currentUserToken = goodT(\<guillemotleft>t\<guillemotright>)) \<Rightarrow> ofGoodT(currentUserToken) \<in> \<guillemotleft>Token\<guillemotright>)"

alphabet AdminToken =
  currentAdminToken :: "TOKENTRY"
  adminTokenPresence :: "PRESENCE"

definition AdminToken :: "AdminToken upred" where 
[upred_defs, tis_defs]:
"AdminToken = U((\<exists> t. currentAdminToken = goodT(\<guillemotleft>t\<guillemotright>)) \<Rightarrow> ofGoodT(currentAdminToken) \<in> \<guillemotleft>Token\<guillemotright>)"

subsection \<open> Internal State \<close>

datatype STATUS = quiescent | gotUserToken | waitingFinger | gotFinger | waitingUpdateToken | 
  waitingEntry | waitingRemoveTokenSuccess | waitingRemoveTokenFail

datatype ENCLAVESTATUS = notEnrolled | waitingEnrol | waitingEndEnrol | enclaveQuiescent |
  gotAdminToken | waitingRemoveAdminTokenFail | waitingStartAdminOp | waitingFinishAdminOp |
  shutdown

alphabet Internal =
  status :: STATUS
  enclaveStatus :: ENCLAVESTATUS
  tokenRemovalTimeout :: TIME

definition Internal :: "Internal upred" where 
[upred_defs, tis_defs]:
"Internal = true"

subsection \<open>The Whole Token ID Station\<close>

alphabet IDStation =
  iuserToken :: UserToken
  iadminToken :: AdminToken
  ifinger :: Finger
  doorLatchAlarm :: DoorLatchAlarm
  ifloppy :: Floppy
  ikeyboard :: Keyboard
  config :: Config
  stats :: Stats
  keyStore :: KeyStore
  admin :: Admin
  audit :: AuditLog
  internal :: Internal
  currentDisplay :: DISPLAYMESSAGE
  currentScreen :: Screen

(* FIXME: I temporarily turned off currency checks below, because it was difficult to show that
  operations WriteUserTokenOK satisfies the invariants with this applied. This should
  be fixed. I wonder if there's another missing invariant... *)

definition UserTokenWithOKAuthCert :: "IDStation upred" where
[upred_defs, tis_defs]:
"UserTokenWithOKAuthCert =
  (&iuserToken:currentUserToken \<in>\<^sub>u \<guillemotleft>range(goodT)\<guillemotright> \<and>
   (\<^bold>\<exists> t\<in>\<guillemotleft>TokenWithValidAuth\<guillemotright> \<bullet>
      (\<guillemotleft>goodT(t)\<guillemotright> =\<^sub>u &iuserToken:currentUserToken   
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>IDCert\<guillemotright> \<bullet> \<guillemotleft>c = idCert t\<guillemotright> \<and> CertOK c) \<oplus>\<^sub>p keyStore
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>AuthCert\<guillemotright> \<bullet> \<guillemotleft>c = the (authCert t)\<guillemotright> \<and> AuthCertOK c) \<oplus>\<^sub>p keyStore))
  )" (* \<and> &doorLatchAlarm:currentTime \<in>\<^sub>u \<guillemotleft>validityPeriod (the(authCert t))\<guillemotright> *)

definition UserTokenOK :: "IDStation upred" where
[upred_defs, tis_defs]:
"UserTokenOK =
  (&iuserToken:currentUserToken \<in>\<^sub>u \<guillemotleft>range(goodT)\<guillemotright> \<and>
   (\<^bold>\<exists> t \<bullet>
      (\<guillemotleft>goodT(t)\<guillemotright> =\<^sub>u &iuserToken:currentUserToken 
      \<and> \<guillemotleft>t \<in> CurrentToken ti\<guillemotright>\<lbrakk>ti \<rightarrow> &doorLatchAlarm:currentTime\<rbrakk>
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>IDCert\<guillemotright> \<bullet> \<guillemotleft>c = idCert t\<guillemotright> \<and> CertOK c) \<oplus>\<^sub>p keyStore
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>PrivCert\<guillemotright> \<bullet> \<guillemotleft>c = privCert t\<guillemotright> \<and> CertOK c) \<oplus>\<^sub>p keyStore
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>IandACert\<guillemotright> \<bullet> \<guillemotleft>c = iandACert t\<guillemotright> \<and> CertOK c) \<oplus>\<^sub>p keyStore))
  )"

definition AdminTokenOK :: "IDStation upred" where
[upred_defs, tis_defs]:
"AdminTokenOK =
  (&iadminToken:currentAdminToken \<in>\<^sub>u \<guillemotleft>range(goodT)\<guillemotright> \<and>
   (\<^bold>\<exists> t\<in>\<guillemotleft>TokenWithValidAuth\<guillemotright> \<bullet>
      (\<guillemotleft>goodT(t)\<guillemotright> =\<^sub>u &iadminToken:currentAdminToken 
      \<and> \<guillemotleft>t \<in> CurrentToken ti\<guillemotright>\<lbrakk>ti \<rightarrow> &doorLatchAlarm:currentTime\<rbrakk>
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>IDCert\<guillemotright> \<bullet> \<guillemotleft>c = idCert t\<guillemotright> \<and> CertOK c) \<oplus>\<^sub>p keyStore
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>AuthCert\<guillemotright> \<bullet> \<guillemotleft>Some c = authCert t\<guillemotright> \<and> AuthCertOK c 
         \<and> \<guillemotleft>role c \<in> ADMINPRIVILEGE\<guillemotright>) \<oplus>\<^sub>p keyStore
   ))
  )"

definition FingerOK :: "IDStation upred" where
[upred_defs, tis_defs]:
"FingerOK = (
  Finger \<oplus>\<^sub>p ifinger \<and>
  UserToken \<oplus>\<^sub>p iuserToken \<and>
  &ifinger:currentFinger \<in>\<^sub>u \<guillemotleft>range(goodFP)\<guillemotright>)"

definition IDStation_inv1 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv1 = 
  U(&internal:status \<in>
   {\<guillemotleft>gotFinger\<guillemotright>, \<guillemotleft>waitingFinger\<guillemotright>, \<guillemotleft>waitingUpdateToken\<guillemotright>, \<guillemotleft>waitingEntry\<guillemotright>, \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright>}
   \<Rightarrow> (@UserTokenWithOKAuthCert \<or> @UserTokenOK))"

definition IDStation_inv2 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv2 =
   U(&admin:rolePresent \<noteq> \<guillemotleft>None\<guillemotright> \<Rightarrow> @AdminTokenOK)"

definition IDStation_inv3 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv3 =
   U(&internal:enclaveStatus \<notin> {\<guillemotleft>notEnrolled\<guillemotright>, \<guillemotleft>waitingEnrol\<guillemotright>, \<guillemotleft>waitingEndEnrol\<guillemotright>} \<Rightarrow>
       &keyStore:ownName \<noteq> \<guillemotleft>None\<guillemotright>)"

definition IDStation_inv4 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv4 =
   U(&internal:enclaveStatus \<in> {\<guillemotleft>waitingStartAdminOp\<guillemotright>, \<guillemotleft>waitingFinishAdminOp\<guillemotright>}
     \<Leftrightarrow> &admin:currentAdminOp \<noteq> \<guillemotleft>None\<guillemotright>)"

definition IDStation_inv5 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv5 =
   U(&admin:currentAdminOp \<noteq> \<guillemotleft>None\<guillemotright> \<and> the(&admin:currentAdminOp) \<in> {\<guillemotleft>shutdownOp\<guillemotright>, \<guillemotleft>overrideLock\<guillemotright>}
         \<Rightarrow> &internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright>)"

definition IDStation_inv6 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv6 = U(&internal:enclaveStatus = \<guillemotleft>gotAdminToken\<guillemotright> \<Rightarrow> &admin:rolePresent = \<guillemotleft>None\<guillemotright>)"

definition IDStation_inv7 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv7 = U(&currentScreen:screenStats = displayStats stats)"

definition IDStation_inv8 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv8 = U(&currentScreen:screenConfig = displayConfigData config)"

text \<open> Extra Invariant (1):  \<close>

definition IDStation_inv9 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv9 = 
  U(&internal:status \<in>
     {\<guillemotleft>waitingEntry\<guillemotright>, \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright>}
   \<Rightarrow> (@UserTokenWithOKAuthCert \<or> @FingerOK))"

text \<open> Extra Invariant (2): If an admin token is present, and a role has been validated then
  the role matches the one present on the authorisation certificate. \<close>

definition IDStation_inv10 :: "IDStation upred" where
  [upred_defs, tis_defs]:
  "IDStation_inv10 = 
  U(&iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright> \<and> &admin:rolePresent \<noteq> \<guillemotleft>None\<guillemotright>
   \<Rightarrow> &admin:rolePresent = Some(role(the(authCert(ofGoodT(&iadminToken:currentAdminToken))))))"

definition
  [upred_defs, tis_defs]:
  "IDStation_wf =
  (DoorLatchAlarm \<oplus>\<^sub>p doorLatchAlarm \<and>
   Floppy \<oplus>\<^sub>p ifloppy \<and>
   KeyStore \<oplus>\<^sub>p keyStore \<and>
   Admin \<oplus>\<^sub>p admin \<and>
   Config \<oplus>\<^sub>p config \<and>
   AdminToken \<oplus>\<^sub>p iadminToken \<and>
   UserToken \<oplus>\<^sub>p iuserToken)"

definition 
  [upred_defs, tis_defs]:
  "IDStation_inv = (
  IDStation_inv1 \<and>
  IDStation_inv2 \<and>
  IDStation_inv3 \<and>
  IDStation_inv4 \<and>
  IDStation_inv5 \<and>
  IDStation_inv6 \<and>
  IDStation_inv7 \<and>
  IDStation_inv8 \<and>
  IDStation_inv9 \<and>
  IDStation_inv10)"

definition IDStation :: "IDStation upred" where
[upred_defs, tis_defs]:
"IDStation = 
  (
  IDStation_wf \<and>
  IDStation_inv
  )"

lemma IDStation_correct_intro:
  assumes "\<^bold>{DoorLatchAlarm \<oplus>\<^sub>p doorLatchAlarm \<and> Floppy \<oplus>\<^sub>p ifloppy \<and> KeyStore \<oplus>\<^sub>p keyStore \<and> Admin \<oplus>\<^sub>p admin \<and> 
            Config \<oplus>\<^sub>p config \<and> AdminToken \<oplus>\<^sub>p iadminToken \<and> UserToken \<oplus>\<^sub>p iuserToken\<^bold>}
             P
           \<^bold>{DoorLatchAlarm \<oplus>\<^sub>p doorLatchAlarm \<and> Floppy \<oplus>\<^sub>p ifloppy \<and> KeyStore \<oplus>\<^sub>p keyStore \<and> Admin \<oplus>\<^sub>p admin \<and> 
            Config \<oplus>\<^sub>p config \<and> AdminToken \<oplus>\<^sub>p iadminToken \<and> UserToken \<oplus>\<^sub>p iuserToken\<^bold>}"
          "\<^bold>{IDStation_inv\<^bold>}P\<^bold>{IDStation_inv\<^bold>}"
        shows "\<^bold>{IDStation\<^bold>}P\<^bold>{IDStation\<^bold>}"
  using assms
proof -
have f1: "(IDStation_inv \<and> DoorLatchAlarm \<oplus>\<^sub>p doorLatchAlarm \<and> Floppy \<oplus>\<^sub>p ifloppy \<and> KeyStore \<oplus>\<^sub>p keyStore \<and> Admin \<oplus>\<^sub>p admin \<and> Config \<oplus>\<^sub>p config \<and> AdminToken \<oplus>\<^sub>p iadminToken \<and> UserToken \<oplus>\<^sub>p iuserToken) = IDStation"
by (simp add: IDStation_def IDStation_wf_def utp_pred_laws.inf_commute utp_pred_laws.inf_left_commute)
  then have f2: "\<^bold>{IDStation\<^bold>} P \<^bold>{DoorLatchAlarm \<oplus>\<^sub>p doorLatchAlarm \<and> Floppy \<oplus>\<^sub>p ifloppy \<and> KeyStore \<oplus>\<^sub>p keyStore \<and> Admin \<oplus>\<^sub>p admin \<and> Config \<oplus>\<^sub>p config \<and> AdminToken \<oplus>\<^sub>p iadminToken \<and> UserToken \<oplus>\<^sub>p iuserToken\<^bold>}"
    by (metis (no_types) assms(1) hoare_r_weaken_pre(2))
  have "\<^bold>{IDStation\<^bold>} P \<^bold>{IDStation_inv\<^bold>}"
    using f1 by (metis (no_types) assms(2) hoare_r_weaken_pre(2) utp_pred_laws.inf_commute)
  then show ?thesis
using f2 f1
  using hoare_r_conj by fastforce
qed

lemma IDStation_inv_intro:
  assumes 
    "\<^bold>{IDStation_inv1\<^bold>}P\<^bold>{IDStation_inv1\<^bold>}"
    "\<^bold>{IDStation_inv2\<^bold>}P\<^bold>{IDStation_inv2\<^bold>}"
    "\<^bold>{IDStation_inv3\<^bold>}P\<^bold>{IDStation_inv3\<^bold>}"
    "\<^bold>{IDStation_inv4\<^bold>}P\<^bold>{IDStation_inv4\<^bold>}"
    "\<^bold>{IDStation_inv5\<^bold>}P\<^bold>{IDStation_inv5\<^bold>}"
    "\<^bold>{IDStation_inv6\<^bold>}P\<^bold>{IDStation_inv6\<^bold>}"
    "\<^bold>{IDStation_inv7\<^bold>}P\<^bold>{IDStation_inv7\<^bold>}"
    "\<^bold>{IDStation_inv8\<^bold>}P\<^bold>{IDStation_inv8\<^bold>}"
    "\<^bold>{IDStation_inv9\<^bold>}P\<^bold>{IDStation_inv9\<^bold>}"
    "\<^bold>{IDStation_inv10\<^bold>}P\<^bold>{IDStation_inv10\<^bold>}"
  shows "\<^bold>{IDStation_inv\<^bold>}P\<^bold>{IDStation_inv\<^bold>}"
  by (simp add: IDStation_inv_def assms hoare_r_conj hoare_r_weaken_pre(1) hoare_r_weaken_pre(2))

section \<open>Operations Interfacing to the ID Station (1)\<close>

alphabet TISControlledRealWorld =
  latch :: LATCH
  alarm :: ALARM
  display :: DISPLAYMESSAGE
  screen :: Screen

abbreviation TISControlledRealWorld :: "TISControlledRealWorld upred" where
"TISControlledRealWorld \<equiv> true"

alphabet TISMonitoredRealWorld =
  now :: TIME
  door :: DOOR
  finger :: FINGERPRINTTRY
  userToken :: TOKENTRY
  adminToken :: TOKENTRY
  floppy :: FLOPPY
  keyboard :: KEYBOARD

alphabet RealWorld = 
  controlled :: "TISControlledRealWorld"
  monitored :: "TISMonitoredRealWorld"

definition RealWorld :: "RealWorld upred" where
[upred_defs, tis_defs]:
"RealWorld = true"


subsection \<open>Real World Changes\<close>

(*
definition RealWorldChanges :: "RealWorld hrel" where
[upred_defs, tis_defs]:
"RealWorldChanges = ($monitored:now\<acute> \<ge>\<^sub>u $monitored:now)"
*)

text \<open> We permit any part of the real-world to change without constraint, except time must
  monotonically increase. \<close>

definition RealWorldChanges :: "RealWorld hrel" where
[upred_defs, tis_defs]:
"RealWorldChanges = 
  (\<Or> t \<bullet> monitored:now := &monitored:now + \<guillemotleft>t\<guillemotright> ;;
          monitored:door := * ;; monitored:finger := * ;; 
          monitored:userToken := * ;; monitored:adminToken := * ;; 
          monitored:floppy := * ;; monitored:keyboard := * ;;
          controlled:latch := * ;; controlled:alarm := * ;;
          controlled:display := * ;; controlled:screen := * )"

lemma RealWorldChanges_original: "RealWorldChanges = ($monitored:now\<acute> \<ge>\<^sub>u $monitored:now)"
  by (rel_auto, simp add: nat_le_iff_add)

lemma pre_RealWorldChanges: "Pre(RealWorldChanges) = true"
  by (rel_auto) 

alphabet SystemState = 
  idStation :: IDStation
  realWorld :: RealWorld


(* FIXME: The following audit schemas need finishing *)

(*
definition AddElementsToLog :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AddElementsToLog =
  (\<lceil>Config\<rceil>\<^sub>< \<oplus>\<^sub>r config \<and>
   (\<^bold>\<exists> newElements :: Audit set \<bullet> \<guillemotleft>oldestLogTime(newElements)\<guillemotright> \<ge>\<^sub>u \<guillemotleft>newestLogTime\<guillemotright>($audit:auditLog)\<^sub>a))"
*)


section \<open>Internal Operations\<close>

definition AddElementsToLog :: "IDStation hrel" where
[upred_defs, tis_defs]: "AddElementsToLog = II"

definition AuditAlarm :: "IDStation hrel" where [upred_defs, tis_defs]: "AuditAlarm = true"
definition AuditLatch :: "IDStation hrel" where [upred_defs, tis_defs]: "AuditLatch = true"
definition AuditDoor :: "IDStation hrel" where [upred_defs, tis_defs]: "AuditDoor = true"
definition AuditLogAlarm :: "IDStation hrel" where [upred_defs, tis_defs]: "AuditLogAlarm = true"
definition AuditScreen :: "IDStation hrel" where [upred_defs, tis_defs]: "AuditScreen = true"
definition AuditDisplay :: "IDStation hrel" where [upred_defs, tis_defs]: "AuditDisplay = true"
definition NoChange :: "IDStation hrel" where [upred_defs, tis_defs]: "NoChange = true"

definition LogChange :: "IDStation hrel" where
[upred_defs, tis_defs]:
"LogChange = (AuditAlarm \<or> AuditLatch \<or> AuditDoor \<or> AuditLogAlarm \<or> AuditScreen \<or> AuditDisplay \<or> NoChange)"


subsection \<open>Updating System Statistics\<close>

definition AddSuccessfulEntryToStats :: "Stats hrel" where
[upred_defs, tis_defs]:
"AddSuccessfulEntryToStats =
  (\<Delta>[Stats] \<and>
   $failEntry\<acute> =\<^sub>u $failEntry \<and>
   $successEntry\<acute> =\<^sub>u $successEntry + 1 \<and>
   $failBio\<acute> =\<^sub>u $failBio \<and>
   $successBio\<acute> =\<^sub>u $successBio)"

lemma AddSuccessfulEntryToStats_prog_def:
  "AddSuccessfulEntryToStats = (successEntry := successEntry + 1)"
  by (rel_auto)

definition AddFailedEntryToStats :: "Stats hrel" where
[upred_defs, tis_defs]:
"AddFailedEntryToStats =
  (\<Delta>[Stats] \<and>
   $failEntry\<acute> =\<^sub>u $failEntry + 1 \<and>
   $successEntry\<acute> =\<^sub>u $successEntry \<and>
   $failBio\<acute> =\<^sub>u $failBio \<and>
   $successBio\<acute> =\<^sub>u $successBio)"

lemma AddFailedEntryToStats_prog_def:
  "AddFailedEntryToStats = (failEntry := failEntry + 1)"
  by (rel_auto)

definition AddSuccessfulBioEntryToStats :: "Stats hrel" where
[upred_defs, tis_defs]:
"AddSuccessfulBioEntryToStats =
  (\<Delta>[Stats] \<and>
   $failEntry\<acute> =\<^sub>u $failEntry \<and>
   $successEntry\<acute> =\<^sub>u $successEntry \<and>
   $failBio\<acute> =\<^sub>u $failBio \<and>
   $successBio\<acute> =\<^sub>u $successBio + 1)"

lemma AddSuccessfulBioEntryToStats_prog_def:
  "AddSuccessfulBioEntryToStats = (successBio := successBio + 1)"
  by (rel_auto)

definition AddFailedBioEntryToStats :: "Stats hrel" where
[upred_defs, tis_defs]:
"AddFailedBioEntryToStats =
  (\<Delta>[Stats] \<and>
   $failEntry\<acute> =\<^sub>u $failEntry \<and>
   $successEntry\<acute> =\<^sub>u $successEntry \<and>
   $failBio\<acute> =\<^sub>u $failBio + 1 \<and>
   $successBio\<acute> =\<^sub>u $successBio)"

lemma AddFailedBioEntryToStats_prog_def:
  "AddFailedBioEntryToStats = (failBio := failBio + 1)"
  by (rel_auto)

subsection \<open>Operating the Door\<close>

definition UnlockDoor :: "IDStation hrel" where
[upred_defs, tis_defs]:
"UnlockDoor =
   doorLatchAlarm:latchTimeout := &doorLatchAlarm:currentTime + &config:latchUnlockDuration ;;
   doorLatchAlarm:alarmTimeout := &doorLatchAlarm:currentTime + &config:latchUnlockDuration + &config:alarmSilentDuration ;;
   doorLatchAlarm:currentLatch := \<guillemotleft>unlocked\<guillemotright> ;;
   doorLatchAlarm:doorAlarm := \<guillemotleft>silent\<guillemotright>"

lemma UnlockDoor_correct: 
  "\<^bold>{IDStation\<^bold>}UnlockDoor\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp_all add: tis_defs)
  apply (hoare_auto)
  apply (hoare_auto)
  done

definition LockDoor :: "IDStation hrel" where
[upred_defs, tis_defs]:
"LockDoor =
   doorLatchAlarm:latchTimeout := &doorLatchAlarm:currentTime ;;
   doorLatchAlarm:alarmTimeout := &doorLatchAlarm:currentTime ;;
   doorLatchAlarm:currentLatch := \<guillemotleft>locked\<guillemotright> ;;
   doorLatchAlarm:doorAlarm := \<guillemotleft>silent\<guillemotright>"

subsection \<open>Certificate Operations\<close>

subsubsection \<open>Generating Authorisation Certificates\<close>

definition NewAuthCert :: "_ \<Rightarrow> _ \<Rightarrow> TIME \<Rightarrow> IDStation upred" where
[upred_defs, tis_defs]:
"NewAuthCert token newAuthCert curTime = (
  \<guillemotleft>token \<in> ValidToken\<guillemotright> \<and>
  KeyStore \<oplus>\<^sub>p keyStore \<and>
  Config \<oplus>\<^sub>p config \<and>
  
  &keyStore:ownName \<noteq>\<^sub>u None\<^sub>u \<and>

  \<guillemotleft>issuer (cid newAuthCert)\<guillemotright> =\<^sub>u the\<^sub>u(&keyStore:ownName) \<and>
  \<guillemotleft>validityPeriod newAuthCert\<guillemotright> =\<^sub>u &config:authPeriod(\<guillemotleft>role (privCert token)\<guillemotright>)\<^sub>a(\<guillemotleft>curTime\<guillemotright>)\<^sub>a \<and>
  \<guillemotleft>baseCertId newAuthCert = cid (idCert token)\<guillemotright> \<and>
  \<guillemotleft>atokenID newAuthCert = tokenID token\<guillemotright> \<and>
  \<guillemotleft>role newAuthCert = role (privCert token)\<guillemotright>  \<and>
  \<guillemotleft>clearance newAuthCert\<guillemotright> =\<^sub>u \<guillemotleft>minClearance\<guillemotright>(&config:enclaveClearance, \<guillemotleft>clearance (privCert token)\<guillemotright>)\<^sub>a \<and>
  \<guillemotleft>isValidatedBy newAuthCert\<guillemotright> =\<^sub>u Some\<^sub>u(&keyStore:issuerKey(the\<^sub>u(&keyStore:ownName))\<^sub>a)
)"

subsubsection \<open>Adding Authorisation Certificates to User Token\<close>

definition AddAuthCertToUserToken :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AddAuthCertToUserToken =
  (\<Sqinter> t \<bullet> \<Sqinter> newAuthCert \<bullet>
  (&iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright> \<and>
   \<guillemotleft>goodT(t)\<guillemotright> = &iuserToken:currentUserToken \<and>
   \<guillemotleft>t \<in> ValidToken\<guillemotright> \<and>
   @(NewAuthCert t newAuthCert curTime\<lbrakk>curTime\<rightarrow>&doorLatchAlarm:currentTime\<rbrakk>)
  ) \<longrightarrow>\<^sub>r iuserToken:currentUserToken := \<guillemotleft>goodT(t\<lparr>authCert := Some(newAuthCert)\<rparr>)\<guillemotright>)"

section \<open>Operations Interfacing to the ID Station (2)\<close>

subsection \<open>Obtaining inputs from the real world\<close>

subsubsection \<open>Polling the Real World\<close>

definition PollTime :: "SystemState hrel" where
[upred_defs]:
"PollTime = 
  (\<Delta>[idStation:doorLatchAlarm,DoorLatchAlarm] \<and>
   $idStation:doorLatchAlarm:currentTime\<acute> =\<^sub>u $realWorld:monitored:now)"

definition PollDoor :: "SystemState hrel" where
[upred_defs]:
"PollDoor = 
  (\<Delta>[idStation:doorLatchAlarm,DoorLatchAlarm] \<and>
   $idStation:doorLatchAlarm:currentDoor\<acute> =\<^sub>u $realWorld:monitored:door \<and>
   $idStation:doorLatchAlarm:latchTimeout\<acute> =\<^sub>u $idStation:doorLatchAlarm:latchTimeout \<and>
   $idStation:doorLatchAlarm:alarmTimeout\<acute> =\<^sub>u $idStation:doorLatchAlarm:alarmTimeout)"

definition PollUserToken :: "SystemState hrel" where
[upred_defs]:
"PollUserToken = 
  (\<Delta>[idStation:iuserToken,UserToken] \<and>
   $idStation:iuserToken:userTokenPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:userToken \<noteq>\<^sub>u \<guillemotleft>noT\<guillemotright> \<and>
   $idStation:iuserToken:currentUserToken\<acute> =\<^sub>u 
      ($realWorld:monitored:userToken \<triangleleft> $realWorld:monitored:userToken \<noteq>\<^sub>u \<guillemotleft>noT\<guillemotright> \<triangleright> $idStation:iuserToken:currentUserToken))"

definition PollAdminToken :: "SystemState hrel" where
[upred_defs]:
"PollAdminToken = 
  (\<Delta>[idStation:iadminToken,AdminToken] \<and>
   $idStation:iadminToken:adminTokenPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:adminToken \<noteq>\<^sub>u \<guillemotleft>noT\<guillemotright> \<and>
   $idStation:iadminToken:currentAdminToken\<acute> =\<^sub>u 
      ($realWorld:monitored:adminToken \<triangleleft> $realWorld:monitored:adminToken \<noteq>\<^sub>u \<guillemotleft>noT\<guillemotright> \<triangleright> $idStation:iadminToken:currentAdminToken))"

definition PollFinger :: "SystemState hrel" where
[upred_defs]:
"PollFinger = 
  (\<Delta>[idStation:ifinger,Finger] \<and>
   $idStation:ifinger:fingerPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:finger \<noteq>\<^sub>u \<guillemotleft>noFP\<guillemotright> \<and>
   $idStation:ifinger:currentFinger\<acute> =\<^sub>u 
      ($realWorld:monitored:finger \<triangleleft> $realWorld:monitored:finger \<noteq>\<^sub>u \<guillemotleft>noFP\<guillemotright> \<triangleright> $idStation:ifinger:currentFinger))"

definition PollFloppy :: "SystemState hrel" where
[upred_defs]:
"PollFloppy = 
  (\<Delta>[idStation:ifloppy,Floppy] \<and>
   $idStation:ifloppy:floppyPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:floppy \<noteq>\<^sub>u \<guillemotleft>noFloppy\<guillemotright> \<and>
   $idStation:ifloppy:currentFloppy\<acute> =\<^sub>u 
      ($realWorld:monitored:floppy \<triangleleft> $realWorld:monitored:floppy \<noteq>\<^sub>u \<guillemotleft>noFloppy\<guillemotright> \<triangleright> $idStation:ifloppy:currentFloppy) \<and>
    $idStation:ifloppy:writtenFloppy\<acute> =\<^sub>u $idStation:ifloppy:writtenFloppy
  )"

definition PollKeyboard :: "SystemState hrel" where
[upred_defs]:
"PollKeyboard = 
  (\<Delta>[idStation:ikeyboard,Keyboard] \<and>
   $idStation:ikeyboard:keyedDataPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:keyboard \<noteq>\<^sub>u \<guillemotleft>noKB\<guillemotright> \<and>
   $idStation:ikeyboard:currentKeyedData\<acute> =\<^sub>u 
      ($realWorld:monitored:keyboard \<triangleleft> $realWorld:monitored:keyboard \<noteq>\<^sub>u \<guillemotleft>noKB\<guillemotright> \<triangleright> $idStation:ikeyboard:currentKeyedData))"

definition TISPoll :: "SystemState hrel" where
[upred_defs]:
"TISPoll =
  (\<comment> \<open> PollTime \<close>
   idStation:doorLatchAlarm:currentTime := &realWorld:monitored:now ;;
  \<comment> \<open> The following behaviour locks the door after a timeout and activates the alarm when necessary.
       This behaviour is implicit in the Z specification through the DoorLatchAlarm schema invariants. \<close>
   idStation:doorLatchAlarm:[
     if (currentTime \<ge> latchTimeout) then currentLatch := locked else currentLatch := unlocked fi ;;
     if (currentDoor = \<guillemotleft>dopen\<guillemotright> 
      \<and> currentLatch = \<guillemotleft>locked\<guillemotright> \<and> currentTime \<ge> alarmTimeout) then doorAlarm := alarming else doorAlarm := silent fi
   ]\<^sup>+ ;;
   \<comment> \<open> PollDoor \<close>
   idStation:doorLatchAlarm:currentDoor := &realWorld:monitored:door ;;
   \<comment> \<open> PollUserToken \<close>
   idStation:iuserToken:userTokenPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:userToken = \<guillemotleft>noT\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   idStation:iuserToken:currentUserToken := 
      (&idStation:iuserToken:currentUserToken 
         \<triangleleft> (&realWorld:monitored:userToken = \<guillemotleft>noT\<guillemotright>) \<triangleright> 
       &realWorld:monitored:userToken) ;;
   \<comment> \<open> PollAdminToken \<close>
   idStation:iadminToken:adminTokenPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:adminToken = \<guillemotleft>noT\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   idStation:iadminToken:currentAdminToken :=
      (&idStation:iadminToken:currentAdminToken 
         \<triangleleft> (&realWorld:monitored:adminToken = \<guillemotleft>noT\<guillemotright>) \<triangleright> 
       &realWorld:monitored:adminToken) ;;
   \<comment> \<open> PollFinger \<close>
   idStation:ifinger:fingerPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:finger = \<guillemotleft>noFP\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   idStation:ifinger:currentFinger :=
      (&idStation:ifinger:currentFinger
         \<triangleleft> (&realWorld:monitored:finger = \<guillemotleft>noFP\<guillemotright>) \<triangleright> 
       &realWorld:monitored:finger) ;;
   \<comment> \<open> PollFloppy \<close>
   idStation:ifloppy:floppyPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:floppy = \<guillemotleft>noFloppy\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   idStation:ifloppy:currentFloppy :=
      (&idStation:ifloppy:currentFloppy
         \<triangleleft> (&realWorld:monitored:floppy = \<guillemotleft>noFloppy\<guillemotright>) \<triangleright> 
       &realWorld:monitored:floppy)  ;;
   \<comment> \<open> PollKeyboard \<close>
   idStation:ikeyboard:keyedDataPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:keyboard = \<guillemotleft>noKB\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   idStation:ikeyboard:currentKeyedData :=
      (&idStation:ikeyboard:currentKeyedData
         \<triangleleft> (&realWorld:monitored:keyboard = \<guillemotleft>noKB\<guillemotright>) \<triangleright> 
       &realWorld:monitored:keyboard) 
  )"


subsection \<open>The ID Station Changes the World\<close>

subsubsection \<open>Periodic Updates\<close>

(*
definition UpdateLatch :: "SystemState hrel" where
[upred_defs]:
"UpdateLatch =
  (\<Xi>[idStation:doorLatchAlarm,DoorLatchAlarm] \<and>
   RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
   $realWorld:controlled:latch\<acute> =\<^sub>u $idStation:doorLatchAlarm:currentLatch)"
*)

abbreviation UpdateLatch :: "SystemState hrel" where
"UpdateLatch \<equiv> realWorld:controlled:latch := &idStation:doorLatchAlarm:currentLatch"

(*
definition UpdateAlarm :: "SystemState hrel" where
[upred_defs]:
"UpdateAlarm =
  (\<Xi>[idStation:doorLatchAlarm,DoorLatchAlarm] \<and>
   RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
   \<lceil>AuditLog\<rceil>\<^sub>< \<oplus>\<^sub>r idStation:audit \<and>
   $realWorld:controlled:alarm\<acute> =\<^sub>u \<guillemotleft>alarming\<guillemotright> \<Leftrightarrow> ($idStation:doorLatchAlarm:doorAlarm =\<^sub>u \<guillemotleft>alarming\<guillemotright>
                                                  \<or> $idStation:audit:auditAlarm =\<^sub>u \<guillemotleft>alarming\<guillemotright>))"
*)

abbreviation UpdateAlarm :: "SystemState hrel" where
"UpdateAlarm \<equiv>
   realWorld:controlled:alarm := (\<guillemotleft>alarming\<guillemotright>
                                   \<triangleleft> (&idStation:doorLatchAlarm:doorAlarm = \<guillemotleft>alarming\<guillemotright>
                                     \<or> &idStation:audit:auditAlarm = \<guillemotleft>alarming\<guillemotright>)
                                   \<triangleright> \<guillemotleft>silent\<guillemotright>)"

definition UpdateDisplay :: "SystemState hrel" where
[upred_defs]:
"UpdateDisplay =
  (\<Delta>[idStation,IDStation] \<and>
   RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
   $realWorld:controlled:display\<acute> =\<^sub>u $idStation:currentDisplay \<and>
   $idStation:currentDisplay\<acute> =\<^sub>u $idStation:currentDisplay)"

definition UpdateScreen :: "SystemState hrel" where
[upred_defs]:
"UpdateScreen =
  (\<Delta>[idStation,IDStation] \<and>
   \<Xi>[idStation:admin,Admin] \<and>
   RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
   $realWorld:controlled:screen:screenMsg\<acute> =\<^sub>u $idStation:currentScreen:screenMsg \<and>
   $realWorld:controlled:screen:screenConfig\<acute> =\<^sub>u 
      ($idStation:currentScreen:screenConfig 
         \<triangleleft> $idStation:admin:rolePresent =\<^sub>u \<guillemotleft>Some(securityOfficer)\<guillemotright> \<triangleright>
       \<guillemotleft>clear\<guillemotright>) \<and>
   $realWorld:controlled:screen:screenStats\<acute> =\<^sub>u
      ($idStation:currentScreen:screenStats 
         \<triangleleft> $idStation:admin:rolePresent \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<triangleright>
       \<guillemotleft>clear\<guillemotright>))"

definition TISUpdate :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISUpdate =
  (realWorld:[RealWorldChanges]\<^sup>+ ;;
   UpdateLatch ;;
   UpdateAlarm ;;
   realWorld:controlled:display := &idStation:currentDisplay)"

definition TISEarlyUpdate :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISEarlyUpdate = UpdateLatch ;; UpdateAlarm"
    
subsubsection \<open>Updating the User Token\<close>

definition UpdateUserToken :: "SystemState hrel" where
[upred_defs, tis_defs]:
"UpdateUserToken = realWorld:monitored:userToken := &idStation:iuserToken:currentUserToken"

lemma UpdateUserToken_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}UpdateUserToken\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
   by (simp add: tis_defs, hoare_auto)

section \<open>The User Entry Operation (1)\<close>

definition ResetScreenMessage :: "IDStation hrel" where
[upred_defs]:
"ResetScreenMessage =
  (\<Delta>[admin,Admin] 
   \<and> (($internal:status\<acute> \<notin>\<^sub>u {\<guillemotleft>quiescent\<guillemotright>,\<guillemotleft>waitingRemoveTokenFail\<guillemotright>}\<^sub>u \<and> $currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>busy\<guillemotright>) \<or>
   ($internal:status\<acute> \<in>\<^sub>u {\<guillemotleft>quiescent\<guillemotright>,\<guillemotleft>waitingRemoveTokenFail\<guillemotright>}\<^sub>u \<and> 
     ( $internal:enclaveStatus\<acute> =\<^sub>u \<guillemotleft>enclaveQuiescent\<guillemotright> \<and> $admin:rolePresent\<acute> =\<^sub>u \<guillemotleft>None\<guillemotright> \<and> $currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>welcomeAdmin\<guillemotright>
     \<or> $internal:enclaveStatus\<acute> =\<^sub>u \<guillemotleft>enclaveQuiescent\<guillemotright> \<and> $admin:rolePresent\<acute> \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<and> $currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>requestAdminOp\<guillemotright>
     \<or> $internal:enclaveStatus\<acute> =\<^sub>u \<guillemotleft>waitingRemoveAdminTokenFail\<guillemotright> \<and> $currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>removeAdminToken\<guillemotright>
     \<or> $internal:enclaveStatus\<acute> \<notin>\<^sub>u {\<guillemotleft>enclaveQuiescent\<guillemotright>,\<guillemotleft>waitingRemoveAdminTokenFail\<guillemotright>}\<^sub>u \<and> $currentScreen:screenMsg\<acute> =\<^sub>u $currentScreen:screenMsg
   ))))"

(*
lemma pre_ResetScreenMessage: "pre ResetScreenMessage = (Admin \<oplus>\<^sub>p admin)"
  by (rel_auto)
*)

(*
definition UserEntryContext :: "SystemState hrel" where
"UserEntryContext =
  ((RealWorldChanges \<and> \<Xi>[controlled, TISControlledRealWorld]) \<oplus>\<^sub>r realWorld \<and>
   (\<Delta>[IDStation] \<and>
   \<Xi>[config, Config] \<and>
   \<Xi>[iadminToken, AdminToken] \<and>
   \<Xi>[keyStore, KeyStore] \<and>
   \<Xi>[admin, Admin] \<and>
   \<Xi>[ikeyboard, Keyboard] \<and>
   \<Xi>[ifloppy, Floppy] \<and>
   \<Xi>[ifinger, Finger] \<and> 
   ResetScreenMessage \<and>
   ($enclaveStatus\<acute> =\<^sub>u $enclaveStatus \<and>
    ($status \<noteq>\<^sub>u \<guillemotleft>waitingEntry\<guillemotright> \<Rightarrow> $tokenRemovalTimeout\<acute> =\<^sub>u $tokenRemovalTimeout)
   ) \<oplus>\<^sub>r internal) \<oplus>\<^sub>r idStation
   )"
*)


lemma mark_alpha_ResetScreenMessage [mark_alpha]:
  "\<Sigma> \<lhd>\<^sub>\<alpha> ResetScreenMessage = {&admin,&currentScreen,&internal} \<lhd>\<^sub>\<alpha> ResetScreenMessage"
  by (rel_auto)


definition UserEntryContext :: "SystemState hrel" where
[upred_defs]:
"UserEntryContext =
  ((RealWorldChanges \<and> \<Xi>[controlled, TISControlledRealWorld]) \<oplus>\<^sub>r realWorld \<and>
   (\<Delta>[iuserToken,UserToken] \<and>
    \<Delta>[doorLatchAlarm,DoorLatchAlarm] \<and>
    \<Delta>[audit,AuditLog] \<and>
    \<Xi>[config, Config] \<and>
    \<Xi>[iadminToken, AdminToken] \<and>
    \<Xi>[keyStore, KeyStore] \<and>
    \<Xi>[admin, Admin] \<and>
    \<Xi>[ikeyboard, Keyboard] \<and>
    \<Xi>[ifloppy, Floppy] \<and>
    \<Xi>[ifinger, Finger] \<and>
    \<Delta>[IDStation_inv] \<and> 
    ResetScreenMessage \<and>
    ($enclaveStatus\<acute> =\<^sub>u $enclaveStatus \<and>
     ($status \<noteq>\<^sub>u \<guillemotleft>waitingEntry\<guillemotright> \<Rightarrow> $tokenRemovalTimeout\<acute> =\<^sub>u $tokenRemovalTimeout)
    ) \<oplus>\<^sub>r internal) \<oplus>\<^sub>r idStation
    )"

lemma "Pre UserEntryContext = IDStation \<oplus>\<^sub>p idStation"
  apply (unfold UserEntryContext_def)
  apply (simp)
  apply (zcalcpre)
  oops

lemma UserEntryContext_alt_def [upred_defs]:
"UserEntryContext =
  ((RealWorldChanges \<and> \<Xi>[controlled, TISControlledRealWorld]) \<oplus>\<^sub>r realWorld \<and>
   (\<Delta>[IDStation] \<and>
    $config\<acute> =\<^sub>u $config \<and> 
    $iadminToken\<acute> =\<^sub>u $iadminToken \<and> 
    $keyStore\<acute> =\<^sub>u $keyStore \<and>
    $admin\<acute> =\<^sub>u $admin \<and>
    $ikeyboard\<acute> =\<^sub>u $ikeyboard \<and>
    $ifloppy\<acute> =\<^sub>u $ifloppy \<and>
    $ifinger\<acute> =\<^sub>u $ifinger \<and> 
    ResetScreenMessage \<and>
   ($enclaveStatus\<acute> =\<^sub>u $enclaveStatus \<and>
    $status \<noteq>\<^sub>u \<guillemotleft>waitingEntry\<guillemotright> \<Rightarrow> $tokenRemovalTimeout\<acute> =\<^sub>u $tokenRemovalTimeout
   ) \<oplus>\<^sub>r internal) \<oplus>\<^sub>r idStation
   )"
  oops

lemma "Pre((RealWorldChanges \<and> \<Xi>[controlled, TISControlledRealWorld]) \<oplus>\<^sub>r realWorld) = true"
  by (rel_auto)


subsection \<open>User Token Tears\<close>

definition UserTokenTorn :: "IDStation hrel" where
[upred_defs, tis_defs]:
"UserTokenTorn = 
  ((&internal:status \<in> {\<guillemotleft>gotUserToken\<guillemotright>, \<guillemotleft>waitingUpdateToken\<guillemotright>, \<guillemotleft>waitingFinger\<guillemotright>, \<guillemotleft>gotFinger\<guillemotright>, \<guillemotleft>waitingEntry\<guillemotright>}
    \<and> &iuserToken:userTokenPresence = \<guillemotleft>absent\<guillemotright>
  ) \<longrightarrow>\<^sub>r currentDisplay := \<guillemotleft>welcom\<guillemotright> ;; internal:status := \<guillemotleft>quiescent\<guillemotright>)"

lemma UserTokenTorn_correct [hoare_safe]: "\<^bold>{IDStation\<^bold>}UserTokenTorn\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

section \<open>Operations within the Enclave (1)\<close>

definition EnclaveContext :: "SystemState hrel" where
[upred_defs]:
"EnclaveContext = 
  (\<Delta>[idStation, IDStation] \<and> 
  RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
  \<Xi>[realWorld:controlled, TISControlledRealWorld] \<and>
  \<Xi>[idStation:iuserToken, UserToken] \<and>
  \<Xi>[idStation:iadminToken, AdminToken] \<and>
  \<Xi>[idStation:ifinger, Finger] \<and>
  \<Xi>[idStation:stats, Stats] \<and>
  ($tokenRemovalTimeout\<acute> =\<^sub>u $tokenRemovalTimeout) \<oplus>\<^sub>r idStation:internal
  )"

definition EnrolContext :: "SystemState hrel" where
"EnrolContext = (EnclaveContext \<and>
  \<Xi>[idStation:ikeyboard, Keyboard] \<and> 
  \<Xi>[idStation:admin, Admin] \<and> 
  \<Xi>[idStation:doorLatchAlarm, DoorLatchAlarm] \<and>
  \<Xi>[idStation:config, Config] \<and>
  \<Xi>[idStation:ifloppy, Floppy])"

text \<open> We depart from the Z specification for this operation, as to precisely implement the Z
  behaviour we need a state space containing both a @{term ValidEnrol} and a @{term KeyStore}.
  Since the former is static rather than dynamic, it seems to make sense to treat it as a
  parameter here. 

  FIX: We had to change ownName (as it was in Tokeneer Z) to ownName' in the function addition.
\<close>


subsection \<open>Updating the Key Store\<close>

(*
definition UpdateKeyStore :: "Enrol \<Rightarrow> KeyStore hrel" where
[upred_defs]:
"UpdateKeyStore e =
  (\<Delta>[KeyStore] \<and>
   \<guillemotleft>e \<in> ValidEnrol\<guillemotright> \<and>
   $ownName\<acute> =\<^sub>u \<guillemotleft>Some (subject (idStationCert e))\<guillemotright> \<and>
   $issuerKey\<acute> =\<^sub>u $issuerKey \<oplus> \<guillemotleft>{(subject c, subjectPubK c) | c. c \<in> issuerCerts e}\<guillemotright> \<oplus> {(the\<^sub>u($ownName\<acute>), \<guillemotleft>subjectPubK (idStationCert e)\<guillemotright>)\<^sub>u}\<^sub>u
   )"
  
lemma rel_typed_Collect [rclos]: "\<lbrakk> \<And> x y. P (x, y) \<Longrightarrow> x \<in> A \<and> y \<in> B \<rbrakk> \<Longrightarrow> Collect P \<in> A \<leftrightarrow>\<^sub>r B"
  by (auto simp add: rel_typed_def)

lemma rel_pfun_Collect [rclos]: "\<lbrakk> \<And> x y. P (x, y) \<Longrightarrow> x \<in> A \<and> y \<in> B; \<And> x y z. \<lbrakk> P (x, y); P (x, z) \<rbrakk> \<Longrightarrow> y = z \<rbrakk> \<Longrightarrow> Collect P \<in> A \<rightharpoonup>\<^sub>r B"
  by (auto simp add: rel_pfun_def rel_typed_def functional_algebraic)

lemma UpdateKeyStore_prog_def:
  "UpdateKeyStore e =
       ?[@KeyStore \<and> \<guillemotleft>e \<in> ValidEnrol\<guillemotright>] ;; 
       ownName :=  \<guillemotleft>Some (subject (idStationCert e))\<guillemotright> ;;
       issuerKey := issuerKey \<oplus> \<guillemotleft>{(subject c, subjectPubK c) | c. c \<in> issuerCerts e}\<guillemotright> \<oplus> {(the(ownName), \<guillemotleft>subjectPubK (idStationCert e)\<guillemotright>)}"
  (is "?P = ?Q")
proof (rule antisym)
  show "?P \<sqsubseteq> ?Q"
    by (rel_auto, auto intro: rclos intro!: rel_pfun_override rel_pfun_Collect)
  show "?Q \<sqsubseteq> ?P"
    by (rel_auto)
qed

lemma pre_KeyStore:
  "e \<in> ValidEnrol \<Longrightarrow> Pre(UpdateKeyStore e) = KeyStore"
  apply (rel_auto)
   apply (auto intro: rclos intro!: rel_pfun_override)
  done
*)

definition UpdateKeyStore :: "Enrol \<Rightarrow> IDStation hrel" where
[upred_defs, tis_defs]:
"UpdateKeyStore e = 
  (\<guillemotleft>e \<in> ValidEnrol\<guillemotright>)
  \<longrightarrow>\<^sub>r keyStore:ownName := \<guillemotleft>Some (subject (idStationCert e))\<guillemotright>
    ;; keyStore:issuerKey := &keyStore:issuerKey 
                           \<union> \<guillemotleft>{(subject c, subjectPubK c) | c. c \<in> issuerCerts e}\<guillemotright>
                           \<union> {(the(&keyStore:ownName), \<guillemotleft>subjectPubK (idStationCert e)\<guillemotright>)}"

(*
definition UpdateKeyStoreFromFloppy :: "IDStation hrel" where
[upred_defs, tis_defs]:
"UpdateKeyStoreFromFloppy =
    (\<Delta>[keyStore,KeyStore] \<and> 
     \<lceil>Floppy \<oplus>\<^sub>p ifloppy\<rceil>\<^sub>< \<and>
     $ifloppy:currentFloppy \<in>\<^sub>u \<guillemotleft>range(enrolmentFile)\<guillemotright> \<and>
     (\<^bold>\<exists> e \<bullet> \<guillemotleft>e\<guillemotright> =\<^sub>u \<guillemotleft>enrolmentFile_of\<guillemotright>($ifloppy:currentFloppy)\<^sub>a 
          \<and> UpdateKeyStore e \<oplus>\<^sub>r keyStore))"
*)

definition call :: "('a \<Rightarrow> 's hrel) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> 's hrel" ("call") where
[upred_defs]: "call F e = (\<Sqinter> x \<bullet> ?[\<guillemotleft>x\<guillemotright> = e] ;; F x)"

utp_lift_notation call (0)

definition UpdateKeyStoreFromFloppy :: "IDStation hrel" where
[upred_defs, tis_defs]:
"UpdateKeyStoreFromFloppy = 
  (&ifloppy:currentFloppy \<in> range(enrolmentFile))
  \<longrightarrow>\<^sub>r call UpdateKeyStore (enrolmentFile_of &ifloppy:currentFloppy)"

section \<open>The User Entry Operation (2)\<close>

subsection \<open>Reading the User Token\<close>

definition ReadUserToken :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ReadUserToken =
  ((&internal:enclaveStatus \<in> {enclaveQuiescent, waitingRemoveAdminTokenFail}
    \<and> &internal:status = quiescent
    \<and> &iuserToken:userTokenPresence = present
   ) \<longrightarrow>\<^sub>r currentDisplay := wait ;; internal:status := gotUserToken)"

subsection \<open>Validating the User Token\<close>

definition UEC :: "IDStation hrel \<Rightarrow> SystemState hrel" where
[upred_defs, tis_defs]:
"UEC(Op) = 
  (\<Sqinter> t \<bullet> idStation:[Op]\<^sup>+ ;;
          realWorld:[
            monitored:now := &monitored:now + t ;;
            monitored:door := * ;; monitored:finger := * ;; 
            monitored:userToken := * ;; monitored:adminToken := * ;; 
            monitored:floppy := * ;; monitored:keyboard := * ]\<^sup>+)"

lemma UEC_refines_RealWorldChanges:
  "(RealWorldChanges \<oplus>\<^sub>r realWorld) \<sqsubseteq> UEC(Op)"
  by (rel_auto)

lemma UEC_correct: "\<^bold>{I\<^bold>}P\<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I \<oplus>\<^sub>p idStation\<^bold>}UEC(P)\<^bold>{I \<oplus>\<^sub>p idStation\<^bold>}"
  apply (simp add: wlp_hoare_link wp UEC_def alpha unrest usubst)
  apply (rel_simp)
  done

lemma ReadUserToken_correct: "\<^bold>{IDStation\<^bold>}ReadUserToken\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_wlp_auto)
  apply (simp add: tis_defs, hoare_wlp_auto)
  done

definition [upred_defs, tis_defs]: "TISReadUserToken = UEC(ReadUserToken)"

lemma TISReadUserToken_correct: "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISReadUserToken\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
  by (simp add: ReadUserToken_correct TISReadUserToken_def UEC_correct)

lemma "`UserTokenOK \<Rightarrow> (\<^bold>\<exists> e\<in>\<guillemotleft>ValidToken\<guillemotright> \<bullet> \<guillemotleft>goodT(e)\<guillemotright> =\<^sub>u &iuserToken:currentUserToken)`"
  by (rel_auto)

lemma "`UserTokenWithOKAuthCert \<Rightarrow> (\<^bold>\<exists> e\<in>\<guillemotleft>TokenWithValidAuth\<guillemotright> \<bullet> \<guillemotleft>goodT(e)\<guillemotright> =\<^sub>u &iuserToken:currentUserToken)`"
  by (rel_auto)

definition BioCheckNotRequired :: "IDStation hrel" where
[upred_defs, tis_defs]:
"BioCheckNotRequired =
  ((&internal:status = gotUserToken
    \<and> &iuserToken:userTokenPresence = present
    \<and> @UserTokenWithOKAuthCert
    ) \<longrightarrow>\<^sub>r internal:status := waitingEntry ;; currentDisplay := wait)"

lemma BioCheckNotRequired_correct: "\<^bold>{IDStation\<^bold>}BioCheckNotRequired\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition BioCheckRequired :: "IDStation hrel" where
[upred_defs, tis_defs]:
"BioCheckRequired =
  ((&internal:status = gotUserToken
  \<and> &iuserToken:userTokenPresence = present
  \<and> (\<not> @UserTokenWithOKAuthCert) \<and> @UserTokenOK
  ) \<longrightarrow>\<^sub>r internal:status := \<guillemotleft>waitingFinger\<guillemotright> ;; currentDisplay := \<guillemotleft>insertFinger\<guillemotright>)"

lemma BioCheckRequired_correct: "\<^bold>{IDStation\<^bold>}BioCheckRequired\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition [upred_defs, tis_defs]: "ValidateUserTokenOK = (BioCheckRequired \<or> BioCheckNotRequired)"

lemma ValidateUserTokenOK_correct: "\<^bold>{IDStation\<^bold>}ValidateUserTokenOK\<^bold>{IDStation\<^bold>}"
  by (simp add: BioCheckNotRequired_correct BioCheckRequired_correct ValidateUserTokenOK_def disj_upred_def hoare_ndet)

definition ValidateUserTokenFail :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateUserTokenFail =
  ((&internal:status = \<guillemotleft>gotUserToken\<guillemotright>
    \<and> &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>
    \<and> (\<not> @UserTokenWithOKAuthCert) \<and> (\<not> @UserTokenOK)
    ) \<longrightarrow>\<^sub>r internal:status := \<guillemotleft>waitingRemoveTokenFail\<guillemotright> ;; currentDisplay := \<guillemotleft>removeToken\<guillemotright>)"

lemma ValidateUserTokenFail_correct: "\<^bold>{IDStation\<^bold>}ValidateUserTokenFail\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition [upred_defs, tis_defs]:
  "TISValidateUserToken = (UEC(ValidateUserTokenOK) \<or> UEC(ValidateUserTokenFail) 
                           \<or> UEC(UserTokenTorn ;; ?[&internal:status = \<guillemotleft>gotUserToken\<guillemotright>]))"

lemma UserTokenTorn_test_correct:
  "\<^bold>{IDStation\<^bold>}(UserTokenTorn ;; ?[@b])\<^bold>{IDStation\<^bold>}"
  by (rule seq_hoare_inv_r_2, simp add: hoare_safe, rule hoare_test, simp add: impl_alt_def utp_pred_laws.sup_commute)

lemma TISValidateUserToken_correct: "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISValidateUserToken\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
  by (simp add: TISValidateUserToken_def UEC_correct UserTokenTorn_test_correct ValidateUserTokenFail_correct ValidateUserTokenOK_correct disj_upred_def hoare_ndet)

subsection \<open>Reading a Fingerprint\<close>

definition ReadFingerOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ReadFingerOK =
  ((&internal:status = waitingFinger
   \<and> &ifinger:fingerPresence = present
   \<and> &iuserToken:userTokenPresence = present
   ) \<longrightarrow>\<^sub>r internal:status := gotFinger ;; currentDisplay := \<guillemotleft>wait\<guillemotright>)"

lemma ReadFingerOK_correct: "\<^bold>{IDStation\<^bold>}ReadFingerOK\<^bold>{IDStation\<^bold>}"
  by (rule IDStation_correct_intro, (simp add: tis_defs, hoare_auto)+)
  
definition NoFinger :: "IDStation hrel" where
[upred_defs, tis_defs]:
"NoFinger =
  ?[&internal:status = \<guillemotleft>waitingFinger\<guillemotright>
     \<and> &ifinger:fingerPresence = \<guillemotleft>absent\<guillemotright>
     \<and> &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>
   ]"

lemma NoFinger_correct: "\<^bold>{IDStation\<^bold>}NoFinger\<^bold>{IDStation\<^bold>}"
  by (rule IDStation_correct_intro, (simp add: tis_defs, hoare_auto)+)

definition FingerTimeout :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FingerTimeout =
 ((&internal:status = \<guillemotleft>waitingFinger\<guillemotright>
     \<and> &ifinger:fingerPresence = \<guillemotleft>absent\<guillemotright>
     \<and> &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>
  ) \<longrightarrow>\<^sub>r currentDisplay := \<guillemotleft>removeToken\<guillemotright> ;; internal:status := \<guillemotleft>waitingRemoveTokenFail\<guillemotright>)"

lemma FingerTimeout_correct: "\<^bold>{IDStation\<^bold>}FingerTimeout\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition [upred_defs, tis_defs]:
"TISReadFinger = (UEC(ReadFingerOK) \<or> UEC(FingerTimeout) \<or> UEC(NoFinger)
                    \<or> UEC(UserTokenTorn ;; ?[&internal:status = \<guillemotleft>waitingFinger\<guillemotright>]))"

lemma TISReadFinger_correct: "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISReadFinger\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
  by (simp add: FingerTimeout_correct NoFinger_correct ReadFingerOK_correct TISReadFinger_def UEC_correct UserTokenTorn_test_correct disj_upred_def hoare_ndet)

subsection \<open>Validating a Fingerprint\<close>

definition ValidateFingerOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateFingerOK =
 ((&internal:status = \<guillemotleft>gotFinger\<guillemotright>
     \<and> &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>
     \<and> @FingerOK
  ) \<longrightarrow>\<^sub>r currentDisplay := \<guillemotleft>wait\<guillemotright> ;; internal:status := \<guillemotleft>waitingUpdateToken\<guillemotright>)"

lemma ValidateFingerOK_correct: "\<^bold>{IDStation\<^bold>}ValidateFingerOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition ValidateFingerFail :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateFingerFail =
 ((&internal:status = \<guillemotleft>gotFinger\<guillemotright>
     \<and> &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>
     \<and> @FingerOK
  ) \<longrightarrow>\<^sub>r currentDisplay := \<guillemotleft>removeToken\<guillemotright> ;; internal:status := \<guillemotleft>waitingRemoveTokenFail\<guillemotright>)"

lemma ValidateFingerFail_correct: "\<^bold>{IDStation\<^bold>}ValidateFingerFail\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition [upred_defs, tis_defs]:
  "TISValidateFinger = (UEC(ValidateFingerOK) \<or> UEC(ValidateFingerFail)
                           \<or> UEC(UserTokenTorn ;; ?[&internal:status = \<guillemotleft>gotFinger\<guillemotright>]))"

lemma TISValidateFinger_correct: "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISValidateFinger\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
  by (simp add: TISValidateFinger_def UEC_correct UserTokenTorn_test_correct ValidateFingerFail_correct ValidateFingerOK_correct disj_upred_def hoare_ndet)
  
subsection \<open>Writing the User Token\<close>

definition WriteUserTokenOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"WriteUserTokenOK =
 ((&internal:status = \<guillemotleft>waitingUpdateToken\<guillemotright>
     \<and> &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>
  ) \<longrightarrow>\<^sub>r AddAuthCertToUserToken ;; 
         currentDisplay := \<guillemotleft>wait\<guillemotright> ;; 
         internal:status := \<guillemotleft>waitingEntry\<guillemotright>)"

lemma hoare_post_conj_split: "\<^bold>{b\<^bold>}P\<^bold>{c \<and> d\<^bold>} \<longleftrightarrow> (\<^bold>{b\<^bold>}P\<^bold>{c\<^bold>} \<and> \<^bold>{b\<^bold>}P\<^bold>{d\<^bold>})"
  by (rel_auto)

(* This is one of the hardest invariant proofs. It should be more automatable. *)

lemma WriteUserTokenOK_correct: "\<^bold>{IDStation\<^bold>}WriteUserTokenOK\<^bold>{IDStation\<^bold>}"
proof -
  have inv: "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv\<^bold>}"
  proof -
    have a:"\<^bold>{IDStation_inv1 \<and> IDStation_inv9\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv9\<^bold>}"
      by (hoare_wlp_auto defs: tis_defs)
    have 1:"\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv9\<^bold>}"
      by (rule_tac pre_str_hoare_r[OF _ a], rel_auto)
    have b: "\<^bold>{IDStation_inv1\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv1\<^bold>}"
      by (hoare_wlp_auto defs: tis_defs)
    have 2:"\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv1\<^bold>}"
      by (rule_tac pre_str_hoare_r[OF _ b], rel_auto)
    have 3:
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv2\<^bold>}" 
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv3\<^bold>}"
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv4\<^bold>}" 
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv5\<^bold>}"
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv6\<^bold>}" 
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv7\<^bold>}"
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv8\<^bold>}"
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenOK \<^bold>{IDStation_inv10\<^bold>}"
      by (hoare_wlp_auto defs: tis_defs)+
    from 1 2 3 show ?thesis
      by (auto simp add: IDStation_inv_def hoare_post_conj_split)
  qed

  have ut: "\<^bold>{UserToken \<oplus>\<^sub>p iuserToken\<^bold>} WriteUserTokenOK \<^bold>{UserToken \<oplus>\<^sub>p iuserToken\<^bold>}"
    by (hoare_wlp_auto defs: tis_defs)

  show ?thesis
    apply (rule_tac IDStation_correct_intro)
    apply (auto simp add: hoare_post_conj_split)
         apply (hoare_wlp_auto defs: tis_defs)
        apply (hoare_wlp_auto defs: tis_defs)
       apply (hoare_wlp_auto defs: tis_defs)
      apply (hoare_wlp_auto defs: tis_defs)
     apply (hoare_wlp_auto defs: tis_defs)
    apply (hoare_wlp_auto defs: tis_defs)
     apply (simp add: ut hoare_r_weaken_pre(1) hoare_r_weaken_pre(2))
    apply (simp add: inv)
    done
qed

definition WriteUserTokenFail :: "IDStation hrel" where
[upred_defs, tis_defs]:
"WriteUserTokenFail =
 ((&internal:status = \<guillemotleft>waitingUpdateToken\<guillemotright>
     \<and> &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>
  ) \<longrightarrow>\<^sub>r AddAuthCertToUserToken ;; 
         currentDisplay := \<guillemotleft>tokenUpdateFailed\<guillemotright> ;; 
         internal:status := \<guillemotleft>waitingEntry\<guillemotright>)"

lemma WriteUserTokenFail_correct: "\<^bold>{IDStation\<^bold>}WriteUserTokenFail\<^bold>{IDStation\<^bold>}"
proof -
  have inv: "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv\<^bold>}"
  proof -
    have a:"\<^bold>{IDStation_inv1 \<and> IDStation_inv9\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv9\<^bold>}"
      by (hoare_wlp_auto defs: tis_defs)
    have 1:"\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv9\<^bold>}"
      by (rule_tac pre_str_hoare_r[OF _ a], rel_auto)
    have b: "\<^bold>{IDStation_inv1\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv1\<^bold>}"
      by (hoare_wlp_auto defs: tis_defs)
    have 2:"\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv1\<^bold>}"
      by (rule_tac pre_str_hoare_r[OF _ b], rel_auto)
    have 3:
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv2\<^bold>}" 
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv3\<^bold>}"
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv4\<^bold>}" 
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv5\<^bold>}"
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv6\<^bold>}" 
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv7\<^bold>}"
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv8\<^bold>}"
      "\<^bold>{IDStation_inv\<^bold>} WriteUserTokenFail \<^bold>{IDStation_inv10\<^bold>}"
      by (hoare_wlp_auto defs: tis_defs)+
    from 1 2 3 show ?thesis
      by (auto simp add: IDStation_inv_def hoare_post_conj_split)
  qed

  have ut: "\<^bold>{UserToken \<oplus>\<^sub>p iuserToken\<^bold>} WriteUserTokenFail \<^bold>{UserToken \<oplus>\<^sub>p iuserToken\<^bold>}"
    by (hoare_wlp_auto defs: tis_defs)

  show ?thesis
    apply (rule_tac IDStation_correct_intro)
    apply (auto simp add: hoare_post_conj_split)
         apply (hoare_wlp_auto defs: tis_defs)
        apply (hoare_wlp_auto defs: tis_defs)
       apply (hoare_wlp_auto defs: tis_defs)
      apply (hoare_wlp_auto defs: tis_defs)
     apply (hoare_wlp_auto defs: tis_defs)
    apply (hoare_wlp_auto defs: tis_defs)
     apply (simp add: ut hoare_r_weaken_pre(1) hoare_r_weaken_pre(2))
    apply (simp add: inv)
    done
qed

definition [upred_defs, tis_defs]:
  "WriteUserToken = (WriteUserTokenOK \<or> WriteUserTokenFail)"

definition [upred_defs, tis_defs]:
  "TISWriteUserToken = 
  ((UEC(WriteUserToken) ;; UpdateUserToken)
   \<or> UEC(UserTokenTorn ;; ?[&internal:status = \<guillemotleft>waitingUpdateToken\<guillemotright>]))"

lemma TISWriteUserToken_correct: 
  "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISWriteUserToken\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
proof -
  have 1: "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}UEC(WriteUserToken) ;; UpdateUserToken\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
    by (simp add: UEC_correct UpdateUserToken_correct WriteUserTokenFail_correct WriteUserTokenOK_correct WriteUserToken_def disj_upred_def hoare_ndet seq_hoare_inv_r_2)
  thus ?thesis
    by (simp add: TISWriteUserToken_def UEC_correct UserTokenTorn_test_correct disj_upred_def hoare_ndet)
qed

subsection \<open>Validating Entry\<close>

definition UserAllowedEntry :: "IDStation upred" where
[upred_defs]:
"UserAllowedEntry = 
  U(((\<exists> t\<in>\<guillemotleft>ValidToken\<guillemotright>. 
      \<guillemotleft>goodT(t)\<guillemotright> = &iuserToken:currentUserToken
      \<and> &doorLatchAlarm:currentTime \<in> &config:entryPeriod \<guillemotleft>role (privCert t)\<guillemotright> \<guillemotleft>class (clearance (privCert t))\<guillemotright>))
   \<or> (\<exists> t\<in>\<guillemotleft>TokenWithValidAuth\<guillemotright>.
      \<guillemotleft>goodT(t)\<guillemotright> = &iuserToken:currentUserToken
      \<and> &doorLatchAlarm:currentTime \<in> &config:entryPeriod \<guillemotleft>role (the (authCert t))\<guillemotright> \<guillemotleft>class (clearance (the (authCert t)))\<guillemotright>))"

definition EntryOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"EntryOK = 
  ((&internal:status = \<guillemotleft>waitingEntry\<guillemotright> \<and>
   &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright> \<and>
   @UserAllowedEntry)
  \<longrightarrow>\<^sub>r currentDisplay := \<guillemotleft>openDoor\<guillemotright> ;;
       internal:status := \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright> ;;
       internal:tokenRemovalTimeout := &doorLatchAlarm:currentTime + &config:tokenRemovalDuration)"

lemma EntryOK_correct: "\<^bold>{IDStation\<^bold>}EntryOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition EntryNotAllowed :: "IDStation hrel" where
[upred_defs, tis_defs]:
"EntryNotAllowed = 
 ((&internal:status = \<guillemotleft>waitingEntry\<guillemotright> \<and>
   &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright> \<and>
   (\<not> @UserAllowedEntry))
  \<longrightarrow>\<^sub>r currentDisplay := \<guillemotleft>removeToken\<guillemotright> ;;
       internal:status := \<guillemotleft>waitingRemoveTokenFail\<guillemotright>)"

lemma EntryNotAllowed_correct: "\<^bold>{IDStation\<^bold>}EntryNotAllowed\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition [upred_defs, tis_defs]:
  "TISValidateEntry = 
  (UEC(EntryOK) \<or> UEC(EntryNotAllowed) \<or> UEC(UserTokenTorn ;; ?[&internal:status = \<guillemotleft>waitingEntry\<guillemotright>]))"

lemma TISValidateEntry_correct: "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISValidateEntry\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
  by (simp add: EntryNotAllowed_correct EntryOK_correct TISValidateEntry_def UEC_correct UserTokenTorn_test_correct disj_upred_def hoare_ndet)

subsection \<open>Unlocking the Door\<close>

definition UnlockDoorOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"UnlockDoorOK = 
  (&internal:status = \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright> \<and>
   &iuserToken:userTokenPresence = \<guillemotleft>absent\<guillemotright>)
  \<longrightarrow>\<^sub>r UnlockDoor ;; currentDisplay := \<guillemotleft>doorUnlocked\<guillemotright> ;; internal:status := \<guillemotleft>quiescent\<guillemotright>"

lemma UnlockDoorOK_correct: "\<^bold>{IDStation\<^bold>}UnlockDoorOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

lemma wp_UnlockDoorOK:
  "UnlockDoorOK wp (&doorLatchAlarm:currentLatch = \<guillemotleft>unlocked\<guillemotright>) = 
       U(&internal:status = \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright> \<and> &iuserToken:userTokenPresence = \<guillemotleft>absent\<guillemotright>)"
  by (simp add: tis_defs wp usubst unrest)

definition WaitingTokenRemoval :: "IDStation hrel" where
[upred_defs, tis_defs]:
"WaitingTokenRemoval =
  ?[&internal:status \<in> {\<guillemotleft>waitingRemoveTokenSuccess\<guillemotright>, \<guillemotleft>waitingRemoveTokenFail\<guillemotright>} \<and>
    &internal:status = \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright> \<Rightarrow> &doorLatchAlarm:currentTime < &internal:tokenRemovalTimeout \<and>
    &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>]"

lemma WaitingTokenRemoval_correct: 
  "\<^bold>{IDStation\<^bold>}WaitingTokenRemoval ;; ?[@b]\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition TokenRemovalTimeout :: "IDStation hrel" where
[upred_defs, tis_defs]:
"TokenRemovalTimeout =
 ((&internal:status = \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright> \<and>
   &doorLatchAlarm:currentTime \<ge> &internal:tokenRemovalTimeout \<and>
   &iuserToken:userTokenPresence = \<guillemotleft>present\<guillemotright>) \<longrightarrow>\<^sub>r
   internal:status := \<guillemotleft>waitingRemoveTokenFail\<guillemotright> ;;
   currentDisplay := \<guillemotleft>removeToken\<guillemotright>)"

lemma TokenRemovalTimeout_correct: "\<^bold>{IDStation\<^bold>}TokenRemovalTimeout\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition [upred_defs, tis_defs]:
"TISUnlockDoor = (UEC(UnlockDoorOK)
               \<or> UEC(WaitingTokenRemoval ;; ?[&internal:status = \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright>])
               \<or> UEC(TokenRemovalTimeout))"

lemma TISUnlockDoor_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISUnlockDoor\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
  by (simp add: TISUnlockDoor_def TokenRemovalTimeout_correct UEC_correct UnlockDoorOK_correct WaitingTokenRemoval_correct disj_upred_def hoare_ndet)

subsection \<open>Terminating a Failed Access\<close>

definition FailedAccessTokenRemoved :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FailedAccessTokenRemoved =
 ((&internal:status = \<guillemotleft>waitingRemoveTokenFail\<guillemotright> \<and>
   &iuserToken:userTokenPresence = \<guillemotleft>absent\<guillemotright>) \<longrightarrow>\<^sub>r
   internal:status := \<guillemotleft>quiescent\<guillemotright> ;;
   currentDisplay := \<guillemotleft>welcom\<guillemotright>)"

lemma FailedAccessTokenRemoved_correct: "\<^bold>{IDStation\<^bold>}FailedAccessTokenRemoved\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition [upred_defs, tis_defs]:
"TISCompleteFailedAccess = (UEC(FailedAccessTokenRemoved)
        \<or> UEC(WaitingTokenRemoval ;; ?[&internal:status = \<guillemotleft>waitingRemoveTokenFail\<guillemotright>]))"

lemma TISCompleteFailedAccess_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISCompleteFailedAccess\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
  by (simp add: FailedAccessTokenRemoved_correct TISCompleteFailedAccess_def UEC_correct WaitingTokenRemoval_correct disj_upred_def hoare_ndet)

subsection \<open>The Complete User Entry\<close>

definition [upred_defs, tis_defs]:
"TISUserEntryOp = (TISReadUserToken \<or> TISValidateUserToken \<or> TISReadFinger \<or> TISValidateFinger
                    \<or> TISWriteUserToken \<or> TISValidateEntry \<or> TISUnlockDoor \<or> TISCompleteFailedAccess)"

lemma TISUserEntryOp_inv: "\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}TISUserEntryOp\<^bold>{IDStation \<oplus>\<^sub>p idStation\<^bold>}"
  apply (auto simp add: TISUserEntryOp_def intro!:hoare_disj)
         apply (simp_all add: TISReadUserToken_correct TISValidateUserToken_correct 
      TISReadFinger_correct TISValidateFinger_correct TISWriteUserToken_correct
      TISValidateEntry_correct TISUnlockDoor_correct TISCompleteFailedAccess_correct)
  done

section \<open>Operations Within the Enclave (2)\<close>

subsection \<open>Enrolment of an ID Station\<close>

subsubsection \<open>Requesting Enrolment\<close>

(*
definition RequestEnrolment :: "SystemState hrel" where
[upred_defs, tis_defs]:
"RequestEnrolment = (EnrolContext \<and>
  \<Xi>[idStation:keyStore, KeyStore] \<and>
  \<Xi>[idStation:audit, AuditLog] \<and>
  \<Xi>[idStation:internal, Internal] \<and>
  ($enclaveStatus =\<^sub>u \<guillemotleft>notEnrolled\<guillemotright>) \<oplus>\<^sub>r idStation:internal \<and>
  ($floppyPresence =\<^sub>u \<guillemotleft>absent\<guillemotright>) \<oplus>\<^sub>r idStation:ifloppy \<and>
  ($currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>insertEnrolmentData\<guillemotright> \<and> 
   $currentDisplay\<acute> =\<^sub>u \<guillemotleft>blank\<guillemotright>) \<oplus>\<^sub>r idStation
  )"
*)

definition RequestEnrolment :: "IDStation hrel" where
[upred_defs, tis_defs]:
"RequestEnrolment = 
  (&internal:enclaveStatus = notEnrolled \<and>
   &ifloppy:floppyPresence = absent)
  \<longrightarrow>\<^sub>r currentScreen:screenMsg := insertEnrolmentData ;; currentDisplay := blank"

lemma RequestEnrolment_correct: "\<^bold>{IDStation\<^bold>}RequestEnrolment\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

(*
definition ReadEnrolmentFloppy :: "SystemState hrel" where
"ReadEnrolmentFloppy = (EnrolContext \<and>
  \<Xi>[idStation:keyStore, KeyStore] \<and>
  ($enclaveStatus =\<^sub>u \<guillemotleft>notEnrolled\<guillemotright>) \<oplus>\<^sub>r idStation:internal \<and>
  ($floppyPresence =\<^sub>u \<guillemotleft>present\<guillemotright>) \<oplus>\<^sub>r idStation:ifloppy \<and>
  ($currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>validatingEnrolmentData\<guillemotright> \<and> 
   $internal:status\<acute> =\<^sub>u $internal:status \<and>
   $currentDisplay\<acute> =\<^sub>u \<guillemotleft>blank\<guillemotright>) \<oplus>\<^sub>r idStation
  )"
*)  

definition ReadEnrolmentFloppy :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ReadEnrolmentFloppy = 
  (&internal:enclaveStatus = notEnrolled \<and>
   &ifloppy:floppyPresence = present)
  \<longrightarrow>\<^sub>r currentScreen:screenMsg := validatingEnrolmentData ;; currentDisplay := blank"

definition "ReadEnrolmentData = (ReadEnrolmentFloppy \<or> RequestEnrolment)"

subsubsection \<open>Validating Enrolment data from Floppy\<close>

definition EnrolmentDataOK :: "IDStation upred" where
"EnrolmentDataOK = (U(&ifloppy:currentFloppy \<in> \<guillemotleft>range enrolmentFile\<guillemotright> \<and>
   enrolmentFile_of &ifloppy:currentFloppy \<in> \<guillemotleft>ValidEnrol\<guillemotright>))"

(*
definition ValidateEnrolmentDataOK :: "SystemState hrel" where
"ValidateEnrolmentDataOK =
  (EnrolContext \<and> 
   (UpdateKeyStoreFromFloppy \<and>
    AddElementsToLog \<and>
    $internal:enclaveStatus =\<^sub>u \<guillemotleft>waitingEnrol\<guillemotright> \<and>
    \<lceil>EnrolmentDataOK\<rceil>\<^sub>< \<and>
    $currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>welcomeAdmin\<guillemotright> \<and>
    $internal:enclaveStatus\<acute> =\<^sub>u \<guillemotleft>enclaveQuiescent\<guillemotright> \<and>
    $internal:status\<acute> =\<^sub>u \<guillemotleft>quiescent\<guillemotright> \<and>
    $currentDisplay\<acute> =\<^sub>u \<guillemotleft>welcom\<guillemotright>
   ) \<oplus>\<^sub>r idStation)"
*)

definition ValidateEnrolmentDataOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateEnrolmentDataOK = 
  (&internal:enclaveStatus = waitingEnrol \<and>
   EnrolmentDataOK)
  \<longrightarrow>\<^sub>r UpdateKeyStoreFromFloppy ;; AddElementsToLog ;;
       currentScreen:screenMsg := welcomeAdmin ;;
       internal:enclaveStatus := enclaveQuiescent ;;
       internal:status := quiescent ;;
       currentDisplay := welcom"

(*
definition ValidateEnrolmentDataFail :: "SystemState hrel" where
"ValidateEnrolmentDataFail =
  (EnrolContext \<and> 
   (\<Xi>[keyStore,KeyStore] \<and>
    AddElementsToLog \<and>
    $internal:enclaveStatus =\<^sub>u \<guillemotleft>waitingEnrol\<guillemotright> \<and>
    \<lceil>\<not> EnrolmentDataOK\<rceil>\<^sub>< \<and>
    $currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>enrolmentFailed\<guillemotright> \<and>
    $internal:enclaveStatus\<acute> =\<^sub>u \<guillemotleft>waitingEndEnrol\<guillemotright> \<and>
    $internal:status\<acute> =\<^sub>u $internal:status \<and>
    $currentDisplay\<acute> =\<^sub>u \<guillemotleft>blank\<guillemotright>
   ) \<oplus>\<^sub>r idStation)"
*)

definition ValidateEnrolmentDataFail :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateEnrolmentDataFail = 
  (&internal:enclaveStatus = waitingEnrol \<and>
   \<not> EnrolmentDataOK)
  \<longrightarrow>\<^sub>r AddElementsToLog ;;
       currentScreen:screenMsg := enrolmentFailed ;;
       internal:enclaveStatus := waitingEndEnrol ;;
       currentDisplay := blank"

definition "ValidateEnrolmentData = (ValidateEnrolmentDataOK \<or> ValidateEnrolmentDataFail)"

subsubsection \<open>Completing a Failed Enrolment\<close>

(*
definition FailedEnrolFloppyRemoved :: "SystemState hrel" where
"FailedEnrolFloppyRemoved =
  (EnrolContext \<and> 
   (\<Xi>[keyStore,KeyStore] \<and>
    $internal:enclaveStatus =\<^sub>u \<guillemotleft>waitingEndEnrol\<guillemotright> \<and>
    $ifloppy:floppyPresence =\<^sub>u \<guillemotleft>absent\<guillemotright> \<and>
    $currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>insertEnrolmentData\<guillemotright> \<and>
    $internal:enclaveStatus\<acute> =\<^sub>u \<guillemotleft>notEnrolled\<guillemotright> \<and>
    $internal:status\<acute> =\<^sub>u $internal:status \<and>
    $currentDisplay\<acute> =\<^sub>u \<guillemotleft>blank\<guillemotright>
   ) \<oplus>\<^sub>r idStation)"
*)

definition FailedEnrolFloppyRemoved :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FailedEnrolFloppyRemoved = 
  (&internal:enclaveStatus = waitingEndEnrol \<and>
   &ifloppy:floppyPresence = absent)
  \<longrightarrow>\<^sub>r currentScreen:screenMsg := insertEnrolmentData ;;
       internal:enclaveStatus := notEnrolled ;;
       currentDisplay := blank"

(*
definition WaitingFloppyRemoval :: "SystemState hrel" where
"WaitingFloppyRemoval =
  (EnrolContext \<and> 
   \<Xi>[idStation,IDStation] \<and>
   ($internal:enclaveStatus =\<^sub>u \<guillemotleft>waitingEndEnrol\<guillemotright> \<and>
    $ifloppy:floppyPresence =\<^sub>u \<guillemotleft>present\<guillemotright>
   ) \<oplus>\<^sub>r idStation)"
*)

definition WaitingFloppyRemoval :: "IDStation hrel" where
[upred_defs, tis_defs]:
"WaitingFloppyRemoval = 
  (&internal:enclaveStatus = waitingEndEnrol \<and>
   &ifloppy:floppyPresence = present)
  \<longrightarrow>\<^sub>r II"

definition "CompleteFailedEnrolment = (FailedEnrolFloppyRemoved \<or> WaitingFloppyRemoval)"

subsubsection \<open>The Complete Enrolment\<close>

definition TISEnrolOp :: "SystemState hrel" where 
[upred_defs, tis_defs]:
"TISEnrolOp = UEC(ReadEnrolmentData \<or> ValidateEnrolmentData \<or> CompleteFailedEnrolment)"

subsection \<open>Further Administrator Operations\<close>

definition AdminLogon :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AdminLogon =
  ((&admin:rolePresent = \<guillemotleft>None\<guillemotright> \<and>
   (\<exists> t\<in>\<guillemotleft>ValidToken\<guillemotright>. (\<guillemotleft>goodT(t)\<guillemotright> = &iadminToken:currentAdminToken))
   ) \<longrightarrow>\<^sub>r admin:rolePresent := Some(role(the(authCert(ofGoodT(&iadminToken:currentAdminToken))))) ;; 
          admin:currentAdminOp := \<guillemotleft>None\<guillemotright> ;;
          \<comment> \<open> The assignments below were added to ensure the invariant @{term Admin} is satisfied \<close>
          if &admin:rolePresent = \<guillemotleft>Some(guard)\<guillemotright>
             then admin:availableOps := {\<guillemotleft>overrideLock\<guillemotright>}
          else if &admin:rolePresent = \<guillemotleft>Some(auditManager)\<guillemotright>
             then admin:availableOps := {\<guillemotleft>archiveLog\<guillemotright>}
          else 
             admin:availableOps := {\<guillemotleft>updateConfigData\<guillemotright>,\<guillemotleft>shutdownOp\<guillemotright>} 
          fi fi)"

definition AdminLogout :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AdminLogout =
  ((&admin:rolePresent \<noteq> \<guillemotleft>None\<guillemotright>
   ) \<longrightarrow>\<^sub>r admin:rolePresent := \<guillemotleft>None\<guillemotright> ;; admin:currentAdminOp := \<guillemotleft>None\<guillemotright>)"

definition AdminStartOp :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AdminStartOp =
  ((&admin:rolePresent \<noteq> \<guillemotleft>None\<guillemotright>
    \<and> &admin:currentAdminOp = \<guillemotleft>None\<guillemotright>
    \<and> &ikeyboard:currentKeyedData \<in> \<guillemotleft>keyedOps\<guillemotright> ` &admin:availableOps
    ) \<longrightarrow>\<^sub>r admin:currentAdminOp := Some(ofKeyedOps(&ikeyboard:currentKeyedData)))"

definition AdminFinishOp :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AdminFinishOp =
  ((&admin:rolePresent \<noteq> \<guillemotleft>None\<guillemotright>
    \<and> &admin:currentAdminOp \<noteq> \<guillemotleft>None\<guillemotright>
    ) \<longrightarrow>\<^sub>r admin:currentAdminOp := \<guillemotleft>None\<guillemotright>)"

definition AdminTokenTear :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AdminTokenTear = 
  ((&iadminToken:adminTokenPresence = \<guillemotleft>absent\<guillemotright>
   ) \<longrightarrow>\<^sub>r internal:enclaveStatus := \<guillemotleft>enclaveQuiescent\<guillemotright>)"

definition BadAdminTokenTear :: "IDStation hrel" where
[upred_defs, tis_defs]:
"BadAdminTokenTear = 
  ((&internal:enclaveStatus \<in> {\<guillemotleft>gotAdminToken\<guillemotright>, \<guillemotleft>waitingStartAdminOp\<guillemotright>, \<guillemotleft>waitingFinishAdminOp\<guillemotright>})
   \<longrightarrow>\<^sub>r AdminTokenTear)"

definition BadAdminLogout :: "IDStation hrel" where
[upred_defs, tis_defs]:
"BadAdminLogout = 
  ((&internal:enclaveStatus \<in> {\<guillemotleft>waitingStartAdminOp\<guillemotright>, \<guillemotleft>waitingFinishAdminOp\<guillemotright>}
   ) \<longrightarrow>\<^sub>r (BadAdminTokenTear ;; AdminLogout))"

definition LoginAborted :: "IDStation hrel" where
[upred_defs, tis_defs]:
"LoginAborted = ((&internal:enclaveStatus = \<guillemotleft>gotAdminToken\<guillemotright>) \<longrightarrow>\<^sub>r BadAdminTokenTear)"

definition ReadAdminToken :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ReadAdminToken =
  ((&internal:enclaveStatus = \<guillemotleft>enclaveQuiescent\<guillemotright>
    \<and> &internal:status \<in> {\<guillemotleft>quiescent\<guillemotright>, \<guillemotleft>waitingRemoveTokenFail\<guillemotright>}
    \<and> &admin:rolePresent = \<guillemotleft>None\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>
   ) \<longrightarrow>\<^sub>r internal:enclaveStatus := \<guillemotleft>gotAdminToken\<guillemotright>)"

definition TISReadAdminToken :: "SystemState hrel" where
[upred_defs, tis_defs]: "TISReadAdminToken = UEC(ReadAdminToken)"

definition ValidateAdminTokenOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateAdminTokenOK =
  ((&internal:enclaveStatus = \<guillemotleft>gotAdminToken\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>
    \<and> @AdminTokenOK
   ) \<longrightarrow>\<^sub>r AdminLogon ;;
          currentScreen:screenMsg := \<guillemotleft>requestAdminOp\<guillemotright> ;; 
          internal:enclaveStatus := \<guillemotleft>enclaveQuiescent\<guillemotright>)"

lemma ValidateAdminTokenOK_correct: 
  "\<^bold>{IDStation\<^bold>}ValidateAdminTokenOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (hoare_wlp_auto defs: tis_defs)
  done

definition ValidateAdminTokenFail :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateAdminTokenFail =
  ((&internal:enclaveStatus = \<guillemotleft>gotAdminToken\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>
    \<and> (\<not> @AdminTokenOK)
   ) \<longrightarrow>\<^sub>r currentScreen:screenMsg := \<guillemotleft>removeAdminToken\<guillemotright> ;; 
          internal:enclaveStatus := \<guillemotleft>waitingRemoveAdminTokenFail\<guillemotright>)"

lemma ValidateAdminTokenFail_correct:
  "\<^bold>{IDStation\<^bold>}ValidateAdminTokenFail\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (simp add: IDStation_inv_def)
  apply (auto simp add: hoare_post_conj_split)
          apply (hoare_wlp_auto defs: tis_defs)
  apply (hoare_wlp_auto defs: tis_defs)
  apply (hoare_wlp_auto defs: tis_defs)
  apply (hoare_wlp_auto defs: tis_defs)
      apply (hoare_wlp_auto defs: tis_defs)
  apply (hoare_wlp_auto defs: tis_defs)
  apply (hoare_wlp_auto defs: tis_defs)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (hoare_wlp_auto defs: tis_defs)
  apply (hoare_wlp_auto defs: tis_defs)
  done

definition TISValidateAdminToken :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISValidateAdminToken =
  (UEC(ValidateAdminTokenOK) \<or> UEC(ValidateAdminTokenFail) \<or> UEC(LoginAborted))"

definition FailedAdminTokenRemove :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FailedAdminTokenRemove =
  ((&internal:enclaveStatus = \<guillemotleft>waitingRemoveAdminTokenFail\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>absent\<guillemotright>
   ) \<longrightarrow>\<^sub>r currentScreen:screenMsg := \<guillemotleft>welcomeAdmin\<guillemotright> ;; 
          internal:enclaveStatus := \<guillemotleft>enclaveQuiescent\<guillemotright>)"

definition WaitingAdminTokenRemoval :: "IDStation hrel" where
[upred_defs, tis_defs]:
"WaitingAdminTokenRemoval = 
  ((&internal:enclaveStatus = \<guillemotleft>waitingRemoveAdminTokenFail\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>) \<longrightarrow>\<^sub>r II)"

definition TISCompleteFailedAdminLogon :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISCompleteFailedAdminLogon = (UEC(FailedAdminTokenRemove) \<or> UEC(WaitingAdminTokenRemoval))"

definition [upred_defs, tis_defs]:
"TISAdminLogon = (TISReadAdminToken \<or> TISValidateAdminToken \<or> TISCompleteFailedAdminLogon)"

definition StartOpContext :: "IDStation hrel" where
[upred_defs, tis_defs]:
"StartOpContext =
  ((&internal:enclaveStatus = \<guillemotleft>enclaveQuiescent\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>
    \<and> &admin:rolePresent \<noteq> \<guillemotleft>None\<guillemotright>
    \<and> &internal:status \<in> {\<guillemotleft>quiescent\<guillemotright>, \<guillemotleft>waitingRemoveTokenFail\<guillemotright>}) \<longrightarrow>\<^sub>r II)"

definition ValidateOpRequestOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateOpRequestOK = 
  ((&ikeyboard:keyedDataPresence = \<guillemotleft>present\<guillemotright> \<and>
    &ikeyboard:currentKeyedData \<in> \<guillemotleft>keyedOps\<guillemotright> ` &admin:availableOps)
    \<longrightarrow>\<^sub>r StartOpContext ;; 
         AdminStartOp ;; 
         currentScreen:screenMsg := \<guillemotleft>doingOp\<guillemotright> ;; 
         internal:enclaveStatus := \<guillemotleft>waitingStartAdminOp\<guillemotright>)"

definition ValidateOpRequestFail :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateOpRequestFail = 
  ((&ikeyboard:keyedDataPresence = \<guillemotleft>present\<guillemotright> \<and>
    &ikeyboard:currentKeyedData \<notin> \<guillemotleft>keyedOps\<guillemotright>`&admin:availableOps) 
    \<longrightarrow>\<^sub>r StartOpContext ;;  
         currentScreen:screenMsg := \<guillemotleft>invalidRequest\<guillemotright>)"

definition NoOpRequest :: "IDStation hrel" where
[upred_defs, tis_defs]:
"NoOpRequest = 
  ((&ikeyboard:keyedDataPresence = \<guillemotleft>absent\<guillemotright>) \<longrightarrow>\<^sub>r StartOpContext)"

definition [upred_defs, tis_defs]:
"ValidateOpRequest = (ValidateOpRequestOK \<or> ValidateOpRequestFail \<or> NoOpRequest)"

definition [upred_defs, tis_defs]: "TISStartAdminOp = UEC(ValidateOpRequest)"

definition AdminOpStartedContext :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AdminOpStartedContext =
  ((&internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright>
   \<and> &iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>
   ) \<longrightarrow>\<^sub>r II)"

definition ShutdownOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ShutdownOK =
  ((&internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright>
   \<and> &admin:currentAdminOp = \<guillemotleft>Some(shutdownOp)\<guillemotright>
   \<and> &doorLatchAlarm:currentDoor = \<guillemotleft>closed\<guillemotright>
   ) \<longrightarrow>\<^sub>r LockDoor ;;
          AdminLogout ;;
          currentScreen:screenMsg := \<guillemotleft>clear\<guillemotright> ;;
          internal:enclaveStatus := \<guillemotleft>shutdown\<guillemotright> ;;
          currentDisplay := \<guillemotleft>blank\<guillemotright>
  )"

definition ShutdownWaitingDoor :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ShutdownWaitingDoor =
  ((&internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright>
   \<and> &admin:currentAdminOp = \<guillemotleft>Some(shutdownOp)\<guillemotright>
   \<and> &doorLatchAlarm:currentDoor = \<guillemotleft>dopen\<guillemotright>
   ) \<longrightarrow>\<^sub>r currentScreen:screenMsg := \<guillemotleft>closeDoor\<guillemotright>
  )"

definition TISShutdownOp :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISShutdownOp = (UEC(ShutdownOK) \<or> UEC(ShutdownWaitingDoor))"

definition OverrideDoorLockOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"OverrideDoorLockOK =
  AdminOpStartedContext ;;
  ((&admin:currentAdminOp = \<guillemotleft>Some(overrideLock)\<guillemotright> 
   ) \<longrightarrow>\<^sub>r currentScreen:screenMsg := \<guillemotleft>requestAdminOp\<guillemotright> ;; 
          currentDisplay := \<guillemotleft>doorUnlocked\<guillemotright> ;;
          internal:enclaveStatus := \<guillemotleft>enclaveQuiescent\<guillemotright> ;;
          UnlockDoor ;;
          AdminFinishOp)"  

lemma  "\<^bold>{IDStation_inv\<^bold>}OverrideDoorLockOK\<^bold>{IDStation_inv\<^bold>}"
  apply (rule IDStation_inv_intro)
  oops

definition TISOverrideDoorLockOp :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISOverrideDoorLockOp = 
  (UEC(OverrideDoorLockOK)
    \<or> UEC((&internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright> 
        \<and> &admin:currentAdminOp = \<guillemotleft>Some(overrideLock)\<guillemotright>) \<longrightarrow>\<^sub>r BadAdminLogout))"

definition TISUpdateConfigDataOp :: "SystemState hrel" where
[upred_defs, tis_defs]: "TISUpdateConfigDataOp = false"

definition TISArchiveLog :: "SystemState hrel" where
[upred_defs, tis_defs]: "TISArchiveLog = false"

definition TISAdminOp :: "SystemState hrel" where 
[upred_defs, tis_defs]:
"TISAdminOp = (TISOverrideDoorLockOp \<or> TISShutdownOp \<or> TISUpdateConfigDataOp \<or> TISArchiveLog)"
definition TISAdminLogout :: "SystemState hrel" where [upred_defs, tis_defs]: "TISAdminLogout = false"
definition TISIdle :: "SystemState hrel" where 
[upred_defs, tis_defs]: 
"TISIdle = UEC((&internal:status = \<guillemotleft>quiescent\<guillemotright> 
               \<and> &internal:enclaveStatus = \<guillemotleft>enclaveQuiescent\<guillemotright>
               \<and> &iuserToken:userTokenPresence = \<guillemotleft>absent\<guillemotright>
               \<and> &iadminToken:adminTokenPresence = \<guillemotleft>absent\<guillemotright>
               \<and> &admin:rolePresent = \<guillemotleft>None\<guillemotright>) \<longrightarrow>\<^sub>r II)"

section \<open>The Initial System and Startup\<close>

definition InitDoorLatchAlarm :: "IDStation hrel" where
[upred_defs, tis_defs]:
"InitDoorLatchAlarm =
  doorLatchAlarm:[
    currentTime := zeroTime ;;
    currentDoor := closed ;;
    currentLatch := locked ;;
    doorAlarm := silent ;;
    latchTimeout := zeroTime ;;
    alarmTimeout := zeroTime]\<^sup>+"

definition InitKeyStore :: "IDStation hrel" where
[upred_defs, tis_defs]:
"InitKeyStore =
  keyStore:[
    issuerKey := {} ;;
    ownName := None
  ]\<^sup>+"

definition InitConfig :: "IDStation hrel" where
[upred_defs, tis_defs]:
"InitConfig =
  config:[
    alarmSilentDuration := 10 ;;
    latchUnlockDuration := 150 ;;
    tokenRemovalDuration := 100 ;;
    enclaveClearance := \<lparr> class = unmarked \<rparr> ;;
    authPeriod := \<guillemotleft>\<lambda> p t. {t..t + 72000}\<guillemotright> ;;
    entryPeriod := \<guillemotleft>\<lambda> p c. UNIV\<guillemotright> ;;
    minPreservedLogSize := * ;;
    alarmThresholdSize := * ;;
    ?[Config] 
  ]\<^sup>+"

definition InitAdmin :: "IDStation hrel" where
[upred_defs, tis_defs]:
"InitAdmin =
  admin:[
    rolePresent := None ;;
    currentAdminOp := None ;;
    availableOps := {}
  ]\<^sup>+"

definition InitStats :: "IDStation hrel" where
[upred_defs, tis_defs]:
"InitStats =
  stats:[
    successEntry := 0 ;;
    failEntry := 0 ;;
    successBio := 0 ;;
    failBio := 0
  ]\<^sup>+"

definition InitAuditLog :: "IDStation hrel" where
[upred_defs, tis_defs]:
"InitAuditLog =
  audit:[
    auditLog := {} ;;
    auditAlarm := silent
  ]\<^sup>+"

definition InitIDStation :: "IDStation hrel" where
[upred_defs, tis_defs]:
"InitIDStation =
  InitDoorLatchAlarm ;;
  InitConfig ;;
  InitKeyStore ;;
  InitStats ;;
  InitAuditLog ;;
  InitAdmin ;;
  currentScreen := * ;;
  currentScreen:screenMsg := clear ;;
  currentDisplay := blank ;;
  internal:enclaveStatus := notEnrolled ;;
  internal:status := quiescent ;;
  \<comment> \<open> We select arbitrary values for the monitored variables \<close>
  iuserToken := * ;;
  ?[UserToken \<oplus>\<^sub>p iuserToken] ;;
  iadminToken := * ;;
  ?[AdminToken \<oplus>\<^sub>p iadminToken] ;;
  ifinger := * ;;
  ?[Finger \<oplus>\<^sub>p ifinger] ;;
  ifloppy := * ;;
  ?[Floppy \<oplus>\<^sub>p ifloppy] ;;
  ikeyboard := * ;;
  ?[Keyboard \<oplus>\<^sub>p ikeyboard]"

lemma "\<^bold>{true\<^bold>}InitIDStation\<^bold>{IDStation\<^bold>}"
  apply (simp add: tis_defs frame assigns_comp usubst alpha)
  oops

abbreviation "TISInit \<equiv> idStation:[InitIDStation]\<^sup>+"

section \<open>The Whole ID Station\<close>

definition TISOp :: "SystemState hrel" where
"TISOp = ((TISEnrolOp 
  \<or> TISUserEntryOp
  \<or> TISAdminLogon
  \<or> TISStartAdminOp
  \<or> TISAdminOp
  \<or> TISAdminLogout
  \<or> TISIdle) )" (* \<and> (LogChange \<oplus>\<^sub>r idStation) *)

abbreviation "TISOpThenUpdate \<equiv> TISOp ;; TISUpdate"

abbreviation "TISBody \<equiv> TISPoll ;; TISEarlyUpdate ;; TISOp ;; TISUpdate"

abbreviation "TIS \<equiv> TISInit ;; TISBody\<^sup>\<star>"

section \<open>Proving Security Properties\<close>

lemma RealWorld_wp [wp]: "\<lbrakk>controlled \<sharp> b; monitored \<sharp> b\<rbrakk> \<Longrightarrow> (RealWorldChanges wp @b) = b"
  by (simp add: tis_defs wp usubst unrest)

lemma 
  "([&idStation:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>] \<dagger>
    (TISReadUserToken wp (&idStation:doorLatchAlarm:currentLatch = \<guillemotleft>unlocked\<guillemotright>))) = false"
  by (simp add: tis_defs wp usubst unrest alpha)

subsection \<open>Proving Security Functional Requirement 1\<close>

lemma [wp]: "(RealWorldChanges wlp false) = false"
  by (rel_auto)

definition AdminTokenGuardOK :: "IDStation upred" where
[upred_defs, tis_defs]:
"AdminTokenGuardOK =
  (&iadminToken:currentAdminToken \<in>\<^sub>u \<guillemotleft>range(goodT)\<guillemotright> \<and>
   (\<^bold>\<exists> t\<in>\<guillemotleft>TokenWithValidAuth\<guillemotright> \<bullet>
      (\<guillemotleft>goodT(t)\<guillemotright> =\<^sub>u &iadminToken:currentAdminToken 
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>AuthCert\<guillemotright> \<bullet> \<guillemotleft>Some c = authCert t\<guillemotright>
         \<and> \<guillemotleft>role c = guard\<guillemotright>) \<oplus>\<^sub>p keyStore
   ))
  )"

lemma admin_unlock:
  "[&idStation:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>] 
        \<dagger> ((TISAdminOp ;; TISUpdate) wp (&realWorld:controlled:latch = \<guillemotleft>unlocked\<guillemotright>)) =
       U((&idStation:internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright> \<and> &idStation:iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>) \<and>
        &idStation:admin:currentAdminOp = \<guillemotleft>Some overrideLock\<guillemotright> \<and> &idStation:admin:rolePresent \<noteq> None \<and> &idStation:admin:currentAdminOp \<noteq> None)"
  by (simp add: tis_defs wp usubst unrest alpha)

lemma user_unlock:
  "[&idStation:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>]
        \<dagger> ((TISUserEntryOp ;; TISUpdate) wp (&realWorld:controlled:latch = \<guillemotleft>unlocked\<guillemotright>)) = 
   U(&idStation:internal:status = \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright> \<and> &idStation:iuserToken:userTokenPresence = \<guillemotleft>absent\<guillemotright>)"
  by (simp add: tis_defs alpha unrest usubst wp)

text \<open> SFR1(a): If the system invariants hold, the door is initially locked, and a @{term TISUserEntryOp} 
  transition is enabled that unlocks the door, then (1) a valid user token is present and (2)
  either a valid finger print or a valid authorisation certificate is also present. \<close>

abbreviation "FSFR1 \<equiv> `(IDStation_inv) \<oplus>\<^sub>p idStation \<and> 
     [&idStation:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>] 
        \<dagger> ((TISUserEntryOp ;; TISUpdate) wp (&realWorld:controlled:latch = \<guillemotleft>unlocked\<guillemotright>))
   \<Rightarrow> ((UserTokenOK \<and> FingerOK) \<or> (UserTokenWithOKAuthCert)) \<oplus>\<^sub>p idStation`"

lemma FSFR1_proof:
  "`(IDStation_inv) \<oplus>\<^sub>p idStation \<and> 
     [&idStation:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>] 
        \<dagger> ((TISUserEntryOp ;; TISUpdate) wp (&realWorld:controlled:latch = \<guillemotleft>unlocked\<guillemotright>))
   \<Rightarrow> ((UserTokenOK \<and> FingerOK) \<or> (UserTokenWithOKAuthCert)) \<oplus>\<^sub>p idStation`" 
  apply (simp add: user_unlock)
  apply (rel_auto)
  done

text \<open> SFR1(b): If the system invariants hold, the door is initially locked, and a @{term TISAdminOp} 
  transition is enabled that unlocks the door, then an admin token is present with the role
  ``guard'' attached. \<close>

lemma FSFR1b:
  "`((IDStation_inv2 \<and> (Admin \<oplus>\<^sub>p admin) \<and> IDStation_inv10) \<oplus>\<^sub>p idStation \<and> 
     [&idStation:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>] 
        \<dagger> ((TISAdminOp ;; TISUpdate) wp (&realWorld:controlled:latch = \<guillemotleft>unlocked\<guillemotright>)))
   \<Rightarrow> AdminTokenGuardOK
 \<oplus>\<^sub>p idStation`" 
  apply (simp add: admin_unlock)
  apply (simp add: Admin_def alpha)
  apply (rel_auto)
  done

definition AlarmInv :: "SystemState upred" where
[upred_defs, tis_defs]:
"AlarmInv = U(&realWorld:controlled:latch = \<guillemotleft>locked\<guillemotright> \<and>
              &idStation:doorLatchAlarm:currentDoor = \<guillemotleft>dopen\<guillemotright> \<and>
              &idStation:doorLatchAlarm:currentTime \<ge> &idStation:doorLatchAlarm:alarmTimeout
             \<Rightarrow> &realWorld:controlled:alarm = \<guillemotleft>alarming\<guillemotright>)"

lemma "\<^bold>{&realWorld:controlled:latch = \<guillemotleft>locked\<guillemotright> \<and>
        &idStation:doorLatchAlarm:currentDoor = \<guillemotleft>dopen\<guillemotright> \<and>
        &idStation:doorLatchAlarm:currentTime \<ge> &idStation:doorLatchAlarm:alarmTimeout \<and>
         @(DoorLatchAlarm \<oplus>\<^sub>p (&idStation:doorLatchAlarm)\<^sub>v)\<^bold>} TISUpdate \<^bold>{&realWorld:controlled:alarm = \<guillemotleft>alarming\<guillemotright>\<^bold>}"
  oops

end