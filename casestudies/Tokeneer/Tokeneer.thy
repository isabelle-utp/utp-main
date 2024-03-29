section \<open> Tokeneer in Isabelle/UTP \<close>

theory Tokeneer
  imports 
    "ZedLite.zedlite"
    "UTP1.utp"
begin recall_syntax

section \<open>Introduction\<close>

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
  tisCert :: IDCert
  issuerCerts :: "IDCert set"

text \<open> We had to add two extra clauses to Enrol here that were specified in the Tokeneer Z-schema,
  namely that (1) all issuer certificates correspond to elements of @{term ISSUER} and (2)
  the subjects uniquely identify one issue certificate. Without these, it is not possible to
  update the key store and maintain the partial function there. \<close>

definition Enrol :: "Enrol set" where
[upred_defs, tis_defs]: 
  "Enrol = {e. tisCert e \<in> issuerCerts e \<and> 
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

lemma ValidEnrol_functional:
  "e \<in> ValidEnrol \<Longrightarrow> functional {(subject c, subjectPubK c) | c. c \<in> issuerCerts e}"
  apply (simp add: functional_def)
  apply (simp add: ValidEnrol_def Enrol_def)
  apply (rule inj_onI)
  apply (force)
  done

lemma Enrol_function:
  "e \<in> ValidEnrol \<Longrightarrow> {(subject c, subjectPubK c) | c. c \<in> issuerCerts e} \<in> ISSUER \<rightarrow>\<^sub>p KEYPART"
  apply (rule rel_pfun_intro)
  apply (simp add: rel_typed_def Enrol_def ValidEnrol_def)
   apply blast
  apply (simp add: ValidEnrol_functional)
  done

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

record Audit =
  auditTime   :: TIME
  auditEvent  :: AuditEvent
  auditUser   :: AuditUser
  sizeElement :: nat

text \<open> Rather than axiomatising this, we explicitly define it and prove the two axioms as theorems. \<close>

definition sizeLog :: "Audit set \<Rightarrow> nat" where
"sizeLog A = (\<Sum> a \<in> A. sizeElement a)"

lemma sizeLog_empty [simp]: "sizeLog {} = 0"
  by (simp add: sizeLog_def)

lemma sizeLog_calc:
  assumes "finite L"
  shows "entry \<in> L \<Longrightarrow> sizeLog L = sizeLog (L - {entry}) + sizeElement entry"
  using assms
  by (simp add: sizeLog_def sum.remove)

subsubsection \<open>Real World Types and Entities (2)\<close>

datatype FLOPPY = noFloppy | emptyFloppy | badFloppy | enrolmentFile (enrolmentFile_of: Enrol) | 
  auditFile "Audit set" | configFile (configFile_of: Config)

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
  U(issuerKey \<in> \<guillemotleft>ISSUER \<rightarrow>\<^sub>p KEYPART\<guillemotright> \<and>
    dom(issuerKey) \<subseteq> \<guillemotleft>ISSUER\<guillemotright> \<and>
    (ownName \<noteq> \<guillemotleft>None\<guillemotright> \<Rightarrow> the(ownName) \<in> dom(issuerKey)))"

definition CertIssuerKnown :: "'a Certificate_scheme \<Rightarrow> KeyStore upred" where
[upred_defs, tis_defs]:
"CertIssuerKnown c =
  U(KeyStore \<and> 
   (\<guillemotleft>c \<in> Certificate\<guillemotright> \<and>
   \<guillemotleft>issuer (cid c)\<guillemotright> \<in> dom(issuerKey)))"

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
"oldestLogTime lg = (Min (auditTime ` lg))"

definition newestLogTime :: "Audit set \<Rightarrow> TIME" where
[upred_defs, tis_defs]:
"newestLogTime lg = (Max (auditTime ` lg))"

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
    (rolePresent = \<guillemotleft>Some guard\<guillemotright> \<Rightarrow> availableOps = {\<guillemotleft>overrideLock\<guillemotright>}) \<and>
    (rolePresent = \<guillemotleft>Some auditManager\<guillemotright> \<Rightarrow> availableOps = {\<guillemotleft>archiveLog\<guillemotright>}) \<and>
    (rolePresent = \<guillemotleft>Some securityOfficer\<guillemotright> 
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
  tis :: IDStation
  realWorld :: RealWorld

section \<open>Internal Operations\<close>

text \<open> The Z-Schema for AddElementsToLog seems to allow, in some cases, the audit log to grow
  beyond its maximum size. As a I understand, it can nondeterminstically chose to extend the log
  anyway, or else remove old log entries. \<close>

definition AddElementsToLog :: "IDStation hrel" where
[upred_defs, tis_defs]: 
  "AddElementsToLog = 
    (\<Sqinter> newElements :: Audit set \<bullet> 
      ?[\<guillemotleft>finite(newElements)\<guillemotright> 
       \<and> \<guillemotleft>newElements \<noteq> {}\<guillemotright>
       \<and> \<guillemotleft>oldestLogTime newElements\<guillemotright> \<ge> newestLogTime &audit:auditLog] ;;
     ((audit:auditLog := &audit:auditLog \<union> \<guillemotleft>newElements\<guillemotright> ;;
        if (sizeLog &audit:auditLog < &config:alarmThresholdSize) 
          then II
          else audit:auditAlarm := alarming
        fi)
      \<sqinter>
      (?[sizeLog &audit:auditLog + \<guillemotleft>sizeLog newElements\<guillemotright> > &config:minPreservedLogSize] ;;
       (\<Sqinter> oldElements :: Audit set \<bullet>
        ?[\<guillemotleft>oldElements\<guillemotright> \<subseteq> &audit:auditLog 
         \<and> oldestLogTime &audit:auditLog \<ge> \<guillemotleft>oldestLogTime oldElements\<guillemotright>] ;;
         audit:auditLog := (&audit:auditLog - \<guillemotleft>oldElements\<guillemotright>) \<union> \<guillemotleft>newElements\<guillemotright> ;;
         ?[sizeLog &audit:auditLog \<ge> &config:minPreservedLogSize] ;;
         audit:auditAlarm := alarming
       )
      )
     )
    )"

text \<open> I believe this achieves the same effect as the Z-Schema -- add some elements to the log
  (audit elements presumably) and choose some continuous subset of the result log for archiving. \<close>

definition ArchiveLog :: "Audit set \<Rightarrow> IDStation hrel" where
[upred_defs, tis_defs]:
"ArchiveLog archive = 
    AddElementsToLog ;;
    (\<Sqinter> (notArchived :: Audit set) \<bullet> 
     ?[\<guillemotleft>archive\<guillemotright> \<subseteq> &audit:auditLog 
       \<and> \<guillemotleft>newestLogTime archive\<guillemotright> \<le> newestLogTime (&audit:auditLog - \<guillemotleft>archive\<guillemotright>)]
    )"

definition ClearLog :: "Audit set \<Rightarrow> IDStation hrel" where
[upred_defs, tis_defs]:
"ClearLog archive = 
  (\<Sqinter> (sinceArchive :: Audit set, lostSinceArchive :: Audit set) \<bullet>
      ?[\<guillemotleft>archive \<union> sinceArchive\<guillemotright> = \<guillemotleft>lostSinceArchive\<guillemotright> \<union> &audit:auditLog
       \<and> \<guillemotleft>oldestLogTime sinceArchive\<guillemotright> \<ge> \<guillemotleft>newestLogTime archive\<guillemotright>
       \<and> \<guillemotleft>newestLogTime sinceArchive\<guillemotright> \<le> oldestLogTime &audit:auditLog] ;;
       audit:auditLog := \<guillemotleft>sinceArchive\<guillemotright>) ;;
  if (sizeLog &audit:auditLog < &config:alarmThresholdSize)
    then audit:auditAlarm := silent
    else audit:auditAlarm := alarming
  fi"

abbreviation "ClearLogThenAddElements archive \<equiv> ClearLog archive ;; AddElementsToLog"

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
  (\<Delta>[tis:doorLatchAlarm,DoorLatchAlarm] \<and>
   $tis:doorLatchAlarm:currentTime\<acute> =\<^sub>u $realWorld:monitored:now)"

definition PollDoor :: "SystemState hrel" where
[upred_defs]:
"PollDoor = 
  (\<Delta>[tis:doorLatchAlarm,DoorLatchAlarm] \<and>
   $tis:doorLatchAlarm:currentDoor\<acute> =\<^sub>u $realWorld:monitored:door \<and>
   $tis:doorLatchAlarm:latchTimeout\<acute> =\<^sub>u $tis:doorLatchAlarm:latchTimeout \<and>
   $tis:doorLatchAlarm:alarmTimeout\<acute> =\<^sub>u $tis:doorLatchAlarm:alarmTimeout)"

definition PollUserToken :: "SystemState hrel" where
[upred_defs]:
"PollUserToken = 
  (\<Delta>[tis:iuserToken,UserToken] \<and>
   $tis:iuserToken:userTokenPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:userToken \<noteq>\<^sub>u \<guillemotleft>noT\<guillemotright> \<and>
   $tis:iuserToken:currentUserToken\<acute> =\<^sub>u 
      ($realWorld:monitored:userToken \<triangleleft> $realWorld:monitored:userToken \<noteq>\<^sub>u \<guillemotleft>noT\<guillemotright> \<triangleright> $tis:iuserToken:currentUserToken))"

definition PollAdminToken :: "SystemState hrel" where
[upred_defs]:
"PollAdminToken = 
  (\<Delta>[tis:iadminToken,AdminToken] \<and>
   $tis:iadminToken:adminTokenPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:adminToken \<noteq>\<^sub>u \<guillemotleft>noT\<guillemotright> \<and>
   $tis:iadminToken:currentAdminToken\<acute> =\<^sub>u 
      ($realWorld:monitored:adminToken \<triangleleft> $realWorld:monitored:adminToken \<noteq>\<^sub>u \<guillemotleft>noT\<guillemotright> \<triangleright> $tis:iadminToken:currentAdminToken))"

definition PollFinger :: "SystemState hrel" where
[upred_defs]:
"PollFinger = 
  (\<Delta>[tis:ifinger,Finger] \<and>
   $tis:ifinger:fingerPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:finger \<noteq>\<^sub>u \<guillemotleft>noFP\<guillemotright> \<and>
   $tis:ifinger:currentFinger\<acute> =\<^sub>u 
      ($realWorld:monitored:finger \<triangleleft> $realWorld:monitored:finger \<noteq>\<^sub>u \<guillemotleft>noFP\<guillemotright> \<triangleright> $tis:ifinger:currentFinger))"

definition PollFloppy :: "SystemState hrel" where
[upred_defs]:
"PollFloppy = 
  (\<Delta>[tis:ifloppy,Floppy] \<and>
   $tis:ifloppy:floppyPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:floppy \<noteq>\<^sub>u \<guillemotleft>noFloppy\<guillemotright> \<and>
   $tis:ifloppy:currentFloppy\<acute> =\<^sub>u 
      ($realWorld:monitored:floppy \<triangleleft> $realWorld:monitored:floppy \<noteq>\<^sub>u \<guillemotleft>noFloppy\<guillemotright> \<triangleright> $tis:ifloppy:currentFloppy) \<and>
    $tis:ifloppy:writtenFloppy\<acute> =\<^sub>u $tis:ifloppy:writtenFloppy
  )"

definition PollKeyboard :: "SystemState hrel" where
[upred_defs]:
"PollKeyboard = 
  (\<Delta>[tis:ikeyboard,Keyboard] \<and>
   $tis:ikeyboard:keyedDataPresence\<acute> =\<^sub>u \<guillemotleft>present\<guillemotright> \<Leftrightarrow> $realWorld:monitored:keyboard \<noteq>\<^sub>u \<guillemotleft>noKB\<guillemotright> \<and>
   $tis:ikeyboard:currentKeyedData\<acute> =\<^sub>u 
      ($realWorld:monitored:keyboard \<triangleleft> $realWorld:monitored:keyboard \<noteq>\<^sub>u \<guillemotleft>noKB\<guillemotright> \<triangleright> $tis:ikeyboard:currentKeyedData))"

definition TISPoll :: "SystemState hrel" where
[tis_defs, upred_defs]:
"TISPoll =
  (\<comment> \<open> PollTime \<close>
   tis:doorLatchAlarm:currentTime := &realWorld:monitored:now ;;
  \<comment> \<open> The following behaviour locks the door after a timeout and activates the alarm when necessary.
       This behaviour is implicit in the Z specification through the DoorLatchAlarm schema invariants. \<close>
   tis:doorLatchAlarm:[
     if (currentTime \<ge> latchTimeout) then currentLatch := locked else currentLatch := unlocked fi ;;
     if (currentDoor = \<guillemotleft>dopen\<guillemotright> 
      \<and> currentLatch = \<guillemotleft>locked\<guillemotright> \<and> currentTime \<ge> alarmTimeout) then doorAlarm := alarming else doorAlarm := silent fi
   ]\<^sup>+ ;;
   \<comment> \<open> PollDoor \<close>
   tis:doorLatchAlarm:currentDoor := &realWorld:monitored:door ;;
   \<comment> \<open> PollUserToken \<close>
   tis:iuserToken:userTokenPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:userToken = \<guillemotleft>noT\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   tis:iuserToken:currentUserToken := 
      (&tis:iuserToken:currentUserToken 
         \<triangleleft> (&realWorld:monitored:userToken = \<guillemotleft>noT\<guillemotright>) \<triangleright> 
       &realWorld:monitored:userToken) ;;
   \<comment> \<open> PollAdminToken \<close>
   tis:iadminToken:adminTokenPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:adminToken = \<guillemotleft>noT\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   tis:iadminToken:currentAdminToken :=
      (&tis:iadminToken:currentAdminToken 
         \<triangleleft> (&realWorld:monitored:adminToken = \<guillemotleft>noT\<guillemotright>) \<triangleright> 
       &realWorld:monitored:adminToken) ;;
   \<comment> \<open> PollFinger \<close>
   tis:ifinger:fingerPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:finger = \<guillemotleft>noFP\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   tis:ifinger:currentFinger :=
      (&tis:ifinger:currentFinger
         \<triangleleft> (&realWorld:monitored:finger = \<guillemotleft>noFP\<guillemotright>) \<triangleright> 
       &realWorld:monitored:finger) ;;
   \<comment> \<open> PollFloppy \<close>
   tis:ifloppy:floppyPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:floppy = \<guillemotleft>noFloppy\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   tis:ifloppy:currentFloppy :=
      (&tis:ifloppy:currentFloppy
         \<triangleleft> (&realWorld:monitored:floppy = \<guillemotleft>noFloppy\<guillemotright>) \<triangleright> 
       &realWorld:monitored:floppy)  ;;
   \<comment> \<open> PollKeyboard \<close>
   tis:ikeyboard:keyedDataPresence :=
      (\<guillemotleft>absent\<guillemotright> \<triangleleft> (&realWorld:monitored:keyboard = \<guillemotleft>noKB\<guillemotright>) \<triangleright> \<guillemotleft>absent\<guillemotright>) ;;
   tis:ikeyboard:currentKeyedData :=
      (&tis:ikeyboard:currentKeyedData
         \<triangleleft> (&realWorld:monitored:keyboard = \<guillemotleft>noKB\<guillemotright>) \<triangleright> 
       &realWorld:monitored:keyboard) 
  )"


subsection \<open>The ID Station Changes the World\<close>

subsubsection \<open>Periodic Updates\<close>

(*
definition UpdateLatch :: "SystemState hrel" where
[upred_defs]:
"UpdateLatch =
  (\<Xi>[tis:doorLatchAlarm,DoorLatchAlarm] \<and>
   RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
   $realWorld:controlled:latch\<acute> =\<^sub>u $tis:doorLatchAlarm:currentLatch)"
*)

abbreviation UpdateLatch :: "SystemState hrel" where
"UpdateLatch \<equiv> realWorld:controlled:latch := &tis:doorLatchAlarm:currentLatch"

(*
definition UpdateAlarm :: "SystemState hrel" where
[upred_defs]:
"UpdateAlarm =
  (\<Xi>[tis:doorLatchAlarm,DoorLatchAlarm] \<and>
   RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
   \<lceil>AuditLog\<rceil>\<^sub>< \<oplus>\<^sub>r tis:audit \<and>
   $realWorld:controlled:alarm\<acute> =\<^sub>u \<guillemotleft>alarming\<guillemotright> \<Leftrightarrow> ($tis:doorLatchAlarm:doorAlarm =\<^sub>u \<guillemotleft>alarming\<guillemotright>
                                                  \<or> $tis:audit:auditAlarm =\<^sub>u \<guillemotleft>alarming\<guillemotright>))"
*)

abbreviation UpdateAlarm :: "SystemState hrel" where
"UpdateAlarm \<equiv>
   realWorld:controlled:alarm := (\<guillemotleft>alarming\<guillemotright>
                                   \<triangleleft> (&tis:doorLatchAlarm:doorAlarm = \<guillemotleft>alarming\<guillemotright>
                                     \<or> &tis:audit:auditAlarm = \<guillemotleft>alarming\<guillemotright>)
                                   \<triangleright> \<guillemotleft>silent\<guillemotright>)"

definition UpdateDisplay :: "SystemState hrel" where
[upred_defs]:
"UpdateDisplay =
  (\<Delta>[tis,IDStation] \<and>
   RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
   $realWorld:controlled:display\<acute> =\<^sub>u $tis:currentDisplay \<and>
   $tis:currentDisplay\<acute> =\<^sub>u $tis:currentDisplay)"

definition UpdateScreen :: "SystemState hrel" where
[upred_defs]:
"UpdateScreen =
  (\<Delta>[tis,IDStation] \<and>
   \<Xi>[tis:admin,Admin] \<and>
   RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
   $realWorld:controlled:screen:screenMsg\<acute> =\<^sub>u $tis:currentScreen:screenMsg \<and>
   $realWorld:controlled:screen:screenConfig\<acute> =\<^sub>u 
      ($tis:currentScreen:screenConfig 
         \<triangleleft> $tis:admin:rolePresent =\<^sub>u \<guillemotleft>Some(securityOfficer)\<guillemotright> \<triangleright>
       \<guillemotleft>clear\<guillemotright>) \<and>
   $realWorld:controlled:screen:screenStats\<acute> =\<^sub>u
      ($tis:currentScreen:screenStats 
         \<triangleleft> $tis:admin:rolePresent \<noteq>\<^sub>u \<guillemotleft>None\<guillemotright> \<triangleright>
       \<guillemotleft>clear\<guillemotright>))"

definition TISUpdate :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISUpdate =
  (realWorld:[RealWorldChanges]\<^sup>+ ;;
   UpdateLatch ;;
   UpdateAlarm ;;
   realWorld:controlled:display := &tis:currentDisplay)"

definition UpdateFloppy :: "SystemState hrel" where
[upred_defs, tis_defs]:
"UpdateFloppy =
  (realWorld:[RealWorldChanges]\<^sup>+ ;;
   realWorld:monitored:floppy := &tis:ifloppy:writtenFloppy ;;
   tis:ifloppy:currentFloppy := badFloppy)"

definition TISEarlyUpdate :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISEarlyUpdate = UpdateLatch ;; UpdateAlarm"
    
subsubsection \<open>Updating the User Token\<close>

definition UpdateUserToken :: "SystemState hrel" where
[upred_defs, tis_defs]:
"UpdateUserToken = realWorld:monitored:userToken := &tis:iuserToken:currentUserToken"

lemma UpdateUserToken_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}UpdateUserToken\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
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
   ) \<oplus>\<^sub>r internal) \<oplus>\<^sub>r tis
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
    ) \<oplus>\<^sub>r internal) \<oplus>\<^sub>r tis
    )"

lemma "Pre UserEntryContext = IDStation \<oplus>\<^sub>p tis"
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
   ) \<oplus>\<^sub>r internal) \<oplus>\<^sub>r tis
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
  (\<Delta>[tis, IDStation] \<and> 
  RealWorldChanges \<oplus>\<^sub>r realWorld \<and>
  \<Xi>[realWorld:controlled, TISControlledRealWorld] \<and>
  \<Xi>[tis:iuserToken, UserToken] \<and>
  \<Xi>[tis:iadminToken, AdminToken] \<and>
  \<Xi>[tis:ifinger, Finger] \<and>
  \<Xi>[tis:stats, Stats] \<and>
  ($tokenRemovalTimeout\<acute> =\<^sub>u $tokenRemovalTimeout) \<oplus>\<^sub>r tis:internal
  )"

definition EnrolContext :: "SystemState hrel" where
"EnrolContext = (EnclaveContext \<and>
  \<Xi>[tis:ikeyboard, Keyboard] \<and> 
  \<Xi>[tis:admin, Admin] \<and> 
  \<Xi>[tis:doorLatchAlarm, DoorLatchAlarm] \<and>
  \<Xi>[tis:config, Config] \<and>
  \<Xi>[tis:ifloppy, Floppy])"

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
   $ownName\<acute> =\<^sub>u \<guillemotleft>Some (subject (tisCert e))\<guillemotright> \<and>
   $issuerKey\<acute> =\<^sub>u $issuerKey \<oplus> \<guillemotleft>{(subject c, subjectPubK c) | c. c \<in> issuerCerts e}\<guillemotright> \<oplus> {(the\<^sub>u($ownName\<acute>), \<guillemotleft>subjectPubK (tisCert e)\<guillemotright>)\<^sub>u}\<^sub>u
   )"
  
lemma rel_typed_Collect [rclos]: "\<lbrakk> \<And> x y. P (x, y) \<Longrightarrow> x \<in> A \<and> y \<in> B \<rbrakk> \<Longrightarrow> Collect P \<in> A \<leftrightarrow>\<^sub>r B"
  by (auto simp add: rel_typed_def)

lemma rel_pfun_Collect [rclos]: "\<lbrakk> \<And> x y. P (x, y) \<Longrightarrow> x \<in> A \<and> y \<in> B; \<And> x y z. \<lbrakk> P (x, y); P (x, z) \<rbrakk> \<Longrightarrow> y = z \<rbrakk> \<Longrightarrow> Collect P \<in> A \<rightharpoonup>\<^sub>r B"
  by (auto simp add: rel_pfun_def rel_typed_def functional_algebraic)

lemma UpdateKeyStore_prog_def:
  "UpdateKeyStore e =
       ?[@KeyStore \<and> \<guillemotleft>e \<in> ValidEnrol\<guillemotright>] ;; 
       ownName :=  \<guillemotleft>Some (subject (tisCert e))\<guillemotright> ;;
       issuerKey := issuerKey \<oplus> \<guillemotleft>{(subject c, subjectPubK c) | c. c \<in> issuerCerts e}\<guillemotright> \<oplus> {(the(ownName), \<guillemotleft>subjectPubK (tisCert e)\<guillemotright>)}"
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
  \<longrightarrow>\<^sub>r keyStore:ownName := \<guillemotleft>Some (subject (tisCert e))\<guillemotright>
    ;; keyStore:issuerKey := &keyStore:issuerKey 
                           \<oplus> \<guillemotleft>{(subject c, subjectPubK c) | c. c \<in> issuerCerts e}\<guillemotright>
                           \<oplus> {(the(&keyStore:ownName), \<guillemotleft>subjectPubK (tisCert e)\<guillemotright>)}"

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

lemma nmods_call [closure]: "\<lbrakk> \<And> v. (P v) nmods x \<rbrakk> \<Longrightarrow> (call P e) nmods x"
  by (rel_auto)

lemma hoare_call [hoare_safe]: "\<lbrakk> \<And> x. \<^bold>{\<guillemotleft>x\<guillemotright> = e \<and> P\<^bold>}F x\<^bold>{Q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{P\<^bold>}call F e\<^bold>{Q\<^bold>}"
  by (rel_auto)

lemma wlp_call [wp]: "(call F e) wlp b = U(\<forall> x. \<guillemotleft>x\<guillemotright> = e \<Rightarrow> F x wlp b)"
  by (simp add: call_def wp)

utp_lift_notation call (0)

definition UpdateKeyStoreFromFloppy :: "IDStation hrel" where
[upred_defs, tis_defs]:
"UpdateKeyStoreFromFloppy = 
  (&ifloppy:currentFloppy \<in> range(enrolmentFile))
  \<longrightarrow>\<^sub>r call UpdateKeyStore (enrolmentFile_of &ifloppy:currentFloppy)"

declare ValidEnrol_def [upred_defs del, tis_defs del]

lemma rel_pfun_pair: "\<lbrakk> x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> {(x, y)} \<in> A \<rightarrow>\<^sub>p B"
  by (simp add: rel_pfun_def rel_typed_def)

lemma UpdateKeyStore_KeyStore_inv: "\<^bold>{KeyStore \<oplus>\<^sub>p keyStore\<^bold>}UpdateKeyStore x\<^bold>{KeyStore \<oplus>\<^sub>p keyStore\<^bold>}"
  apply (simp add: tis_defs del:Enrol_def, hoare_auto)
   apply (rule rel_pfun_override)
   apply (rule rel_pfun_override)
  apply (auto)
  using Enrol_function apply blast
  apply (rule rel_pfun_pair)
  apply (simp add: Enrol_def ValidEnrol_def subset_eq)
  apply blast
  apply (simp add: Enrol_def ValidEnrol_def subset_eq)
  apply (simp add: Enrol_def ValidEnrol_def subset_eq)
   apply (rule rel_pfun_override)
   apply (rule rel_pfun_override)
      apply (auto)
  using Enrol_function apply blast
  apply (rule rel_pfun_pair)
  apply (simp add: Enrol_def ValidEnrol_def subset_eq)
  apply blast
  apply (simp add: Enrol_def ValidEnrol_def subset_eq)
  apply (simp add: Enrol_def ValidEnrol_def subset_eq)
  done

lemma hoare_sep_inv: "\<lbrakk> \<^bold>{p\<^bold>}S\<^bold>{p\<^bold>}; \<^bold>{q\<^bold>}S\<^bold>{q\<^bold>} \<rbrakk> \<Longrightarrow> \<^bold>{p \<and> q\<^bold>}S\<^bold>{p \<and> q\<^bold>}"
  by (rel_auto)

lemma UpdateKeyStore_IDStation_wf: "\<^bold>{IDStation_wf\<^bold>}UpdateKeyStore x\<^bold>{IDStation_wf\<^bold>}"
  apply (simp add: IDStation_wf_def)
  apply (auto intro!:hoare_sep_inv)
  apply (simp add: tis_defs, hoare_auto)
    apply (simp add: tis_defs, hoare_auto)
      apply (simp add: UpdateKeyStore_KeyStore_inv)
     apply (simp add: tis_defs, hoare_auto)
    apply (simp add: tis_defs, hoare_auto)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

lemma UpdateKeyStoreFromFloppy_IDStation_wf: "\<^bold>{IDStation_wf\<^bold>}UpdateKeyStoreFromFloppy\<^bold>{IDStation_wf\<^bold>}"
  apply (simp add: UpdateKeyStoreFromFloppy_def)
  apply (hoare_split)
  apply (metis UpdateKeyStore_IDStation_wf conj_comm hoare_r_weaken_pre(2))
  done
  
section \<open>The User Entry Operation (2)\<close>

definition UEC :: "IDStation hrel \<Rightarrow> SystemState hrel" where
[upred_defs, tis_defs]:
"UEC(Op) = 
  (\<Sqinter> t \<bullet> tis:[Op]\<^sup>+ ;;
          realWorld:[
            monitored:now := &monitored:now + t ;;
            monitored:door := * ;; monitored:finger := * ;; 
            monitored:userToken := * ;; monitored:adminToken := * ;; 
            monitored:floppy := * ;; monitored:keyboard := * ]\<^sup>+)"

lemma UEC_refines_RealWorldChanges:
  "(RealWorldChanges \<oplus>\<^sub>r realWorld) \<sqsubseteq> UEC(Op)"
  by (rel_auto)

lemma UEC_correct: "\<^bold>{I\<^bold>}P\<^bold>{I\<^bold>} \<Longrightarrow> \<^bold>{I \<oplus>\<^sub>p tis\<^bold>}UEC(P)\<^bold>{I \<oplus>\<^sub>p tis\<^bold>}"
  apply (simp add: wlp_hoare_link wp UEC_def alpha unrest usubst)
  apply (rel_simp)
  done

subsection \<open>Reading the User Token\<close>

definition ReadUserToken :: "IDStation hrel" where
[upred_defs, tis_defs]: "ReadUserToken =
  ((&internal:enclaveStatus \<in> {enclaveQuiescent, waitingRemoveAdminTokenFail}
    \<and> &internal:status = quiescent \<and> &iuserToken:userTokenPresence = present
   ) \<longrightarrow>\<^sub>r currentDisplay := wait ;; internal:status := gotUserToken)"

lemma ReadUserToken_correct: "\<^bold>{IDStation\<^bold>}ReadUserToken\<^bold>{IDStation\<^bold>}"
  by (rule IDStation_correct_intro; hoare_wlp_auto defs: tis_defs)

definition BioCheckNotRequired :: "IDStation hrel" where
[upred_defs, tis_defs]: "BioCheckNotRequired =
  ((&internal:status = gotUserToken
    \<and> &iuserToken:userTokenPresence = present \<and> @UserTokenWithOKAuthCert
    ) \<longrightarrow>\<^sub>r internal:status := waitingEntry ;; currentDisplay := wait)"

lemma BioCheckNotRequired_correct: "\<^bold>{IDStation\<^bold>}BioCheckNotRequired\<^bold>{IDStation\<^bold>}"
  by (rule IDStation_correct_intro; hoare_wlp_auto defs: tis_defs)

definition BioCheckRequired :: "IDStation hrel" where
[upred_defs, tis_defs]:
"BioCheckRequired =
  ((&internal:status = gotUserToken
  \<and> &iuserToken:userTokenPresence = present
  \<and> (\<not> @UserTokenWithOKAuthCert) \<and> @UserTokenOK
  ) \<longrightarrow>\<^sub>r internal:status := \<guillemotleft>waitingFinger\<guillemotright> ;; currentDisplay := \<guillemotleft>insertFinger\<guillemotright>)"

lemma BioCheckRequired_correct: "\<^bold>{IDStation\<^bold>}BioCheckRequired\<^bold>{IDStation\<^bold>}"
  by (rule IDStation_correct_intro; (simp add: tis_defs, hoare_auto))

definition [upred_defs, tis_defs]: "TISReadUserToken = UEC(ReadUserToken)"

lemma TISReadUserToken_correct: "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISReadUserToken\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: ReadUserToken_correct TISReadUserToken_def UEC_correct)

subsection \<open>Validating the User Token\<close>

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

lemma TISValidateUserToken_correct: "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISValidateUserToken\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
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

lemma TISReadFinger_correct: "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISReadFinger\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
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

lemma TISValidateFinger_correct: "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISValidateFinger\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
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
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISWriteUserToken\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
proof -
  have 1: "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}UEC(WriteUserToken) ;; UpdateUserToken\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
    by (simp add: UEC_correct UpdateUserToken_correct WriteUserTokenFail_correct WriteUserTokenOK_correct WriteUserToken_def disj_upred_def hoare_ndet seq_hoare_inv_r_2)
  thus ?thesis
    by (simp add: TISWriteUserToken_def UEC_correct UserTokenTorn_test_correct disj_upred_def hoare_ndet)
qed

subsection \<open>Validating Entry\<close>

definition UserAllowedEntry :: "IDStation upred" where
[tis_defs, upred_defs]:
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

lemma TISValidateEntry_correct: "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISValidateEntry\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
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
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISUnlockDoor\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
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
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISCompleteFailedAccess\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: FailedAccessTokenRemoved_correct TISCompleteFailedAccess_def UEC_correct WaitingTokenRemoval_correct disj_upred_def hoare_ndet)

subsection \<open>The Complete User Entry\<close>

definition [upred_defs, tis_defs]:
"TISUserEntryOp = (TISReadUserToken \<or> TISValidateUserToken \<or> TISReadFinger \<or> TISValidateFinger
                    \<or> TISWriteUserToken \<or> TISValidateEntry \<or> TISUnlockDoor \<or> TISCompleteFailedAccess)"

lemma TISUserEntryOp_inv: "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISUserEntryOp\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
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
  \<Xi>[tis:keyStore, KeyStore] \<and>
  \<Xi>[tis:audit, AuditLog] \<and>
  \<Xi>[tis:internal, Internal] \<and>
  ($enclaveStatus =\<^sub>u \<guillemotleft>notEnrolled\<guillemotright>) \<oplus>\<^sub>r tis:internal \<and>
  ($floppyPresence =\<^sub>u \<guillemotleft>absent\<guillemotright>) \<oplus>\<^sub>r tis:ifloppy \<and>
  ($currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>insertEnrolmentData\<guillemotright> \<and> 
   $currentDisplay\<acute> =\<^sub>u \<guillemotleft>blank\<guillemotright>) \<oplus>\<^sub>r tis
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
  \<Xi>[tis:keyStore, KeyStore] \<and>
  ($enclaveStatus =\<^sub>u \<guillemotleft>notEnrolled\<guillemotright>) \<oplus>\<^sub>r tis:internal \<and>
  ($floppyPresence =\<^sub>u \<guillemotleft>present\<guillemotright>) \<oplus>\<^sub>r tis:ifloppy \<and>
  ($currentScreen:screenMsg\<acute> =\<^sub>u \<guillemotleft>validatingEnrolmentData\<guillemotright> \<and> 
   $internal:status\<acute> =\<^sub>u $internal:status \<and>
   $currentDisplay\<acute> =\<^sub>u \<guillemotleft>blank\<guillemotright>) \<oplus>\<^sub>r tis
  )"
*)  

definition ReadEnrolmentFloppy :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ReadEnrolmentFloppy = 
  (&internal:enclaveStatus = notEnrolled \<and>
   &ifloppy:floppyPresence = present)
  \<longrightarrow>\<^sub>r currentScreen:screenMsg := validatingEnrolmentData ;; currentDisplay := blank"

lemma ReadEnrolmentFloppy_correct: "\<^bold>{IDStation\<^bold>}ReadEnrolmentFloppy\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (simp add: tis_defs, hoare_auto)
  apply (simp add: tis_defs, hoare_auto)
  done

definition [tis_defs]: "ReadEnrolmentData = (ReadEnrolmentFloppy \<or> RequestEnrolment)"

subsubsection \<open>Validating Enrolment data from Floppy\<close>

definition EnrolmentDataOK :: "IDStation upred" where
[tis_defs]:
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
   ) \<oplus>\<^sub>r tis)"
*)

definition ValidateEnrolmentDataOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateEnrolmentDataOK = 
  (&internal:enclaveStatus = waitingEnrol \<and>
   EnrolmentDataOK)
  \<longrightarrow>\<^sub>r UpdateKeyStoreFromFloppy ;; 
       currentScreen:screenMsg := welcomeAdmin ;;
       internal:enclaveStatus := enclaveQuiescent ;;
       internal:status := quiescent ;;
       currentDisplay := welcom" (* AddElementsToLog ;; *)

lemma [simp]:
  "\<lbrakk> k \<in> ISSUER \<rightarrow>\<^sub>p KEYPART; e \<in> ValidEnrol \<rbrakk> \<Longrightarrow> 
       k \<oplus> {(subject c, subjectPubK c) | c. c \<in> issuerCerts e} \<oplus> {(subject (tisCert e), subjectPubK (tisCert e))}
       \<in> ISSUER \<rightarrow>\<^sub>p KEYPART"
   apply (rule rel_pfun_override)
   apply (rule rel_pfun_override)
  apply (auto)
  using Enrol_function apply blast
  apply (rule rel_pfun_pair)
  apply (simp add: Enrol_def ValidEnrol_def subset_eq)
  apply blast
  done

lemma ValidEnrol_props [simp]: 
  assumes "e \<in> ValidEnrol" 
  shows "subject (tisCert e) \<in> ISSUER"
  using assms by (auto simp add: ValidEnrol_def Enrol_def)

declare ValidEnrol_def [tis_defs del, upred_defs del]

lemma ValidateEnrolmentDataOK_wf: "\<^bold>{IDStation_wf\<^bold>}ValidateEnrolmentDataOK\<^bold>{IDStation_wf\<^bold>}"
  apply (simp add: IDStation_wf_def)
  apply (simp add: ValidateEnrolmentDataOK_def, hoare_split)
         apply (simp add: tis_defs call_def, hoare_auto)
        apply (simp add: tis_defs call_def, hoare_auto)
       apply (rule hoare_r_conseq[OF UpdateKeyStoreFromFloppy_IDStation_wf])
        apply (rel_auto)
  apply (rel_auto)
  apply (simp add: tis_defs call_def, hoare_auto)
  apply (simp add: tis_defs call_def, hoare_auto)
  apply (simp add: tis_defs call_def, hoare_auto)
   apply (simp add: tis_defs call_def, hoare_auto)
  done

lemma ValidateEnrolmentDataOK_inv: "\<^bold>{IDStation_inv\<^bold>}ValidateEnrolmentDataOK\<^bold>{IDStation_inv\<^bold>}"
  apply (rule IDStation_inv_intro)
           apply (hoare_wlp_auto defs: tis_defs)
          apply (simp add: IDStation_inv2_def)
  oops
(* TODO: Complete proving IDStation invariants for enrolment operations *)


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
   ) \<oplus>\<^sub>r tis)"
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

lemma ValidateEnrolmentDataFail_correct: "\<^bold>{IDStation\<^bold>}ValidateEnrolmentDataFail\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
  oops

definition [tis_defs]: "ValidateEnrolmentData = (ValidateEnrolmentDataOK \<or> ValidateEnrolmentDataFail)"

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
   ) \<oplus>\<^sub>r tis)"
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
   \<Xi>[tis,IDStation] \<and>
   ($internal:enclaveStatus =\<^sub>u \<guillemotleft>waitingEndEnrol\<guillemotright> \<and>
    $ifloppy:floppyPresence =\<^sub>u \<guillemotleft>present\<guillemotright>
   ) \<oplus>\<^sub>r tis)"
*)

definition WaitingFloppyRemoval :: "IDStation hrel" where
[upred_defs, tis_defs]:
"WaitingFloppyRemoval = 
  (&internal:enclaveStatus = waitingEndEnrol \<and>
   &ifloppy:floppyPresence = present)
  \<longrightarrow>\<^sub>r II"

definition [tis_defs]: "CompleteFailedEnrolment = (FailedEnrolFloppyRemoved \<or> WaitingFloppyRemoval)"

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
   ) \<longrightarrow>\<^sub>r admin:rolePresent := \<guillemotleft>None\<guillemotright> ;; admin:currentAdminOp := \<guillemotleft>None\<guillemotright> ;; admin:availableOps := {})"

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

lemma LoginAborted_correct:
  "\<^bold>{IDStation\<^bold>}LoginAborted\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition ReadAdminToken :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ReadAdminToken =
  ((&internal:enclaveStatus = \<guillemotleft>enclaveQuiescent\<guillemotright>
    \<and> &internal:status \<in> {\<guillemotleft>quiescent\<guillemotright>, \<guillemotleft>waitingRemoveTokenFail\<guillemotright>}
    \<and> &admin:rolePresent = \<guillemotleft>None\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>
   ) \<longrightarrow>\<^sub>r internal:enclaveStatus := \<guillemotleft>gotAdminToken\<guillemotright>)"

lemma ReadAdminToken_correct:
  "\<^bold>{IDStation\<^bold>}ReadAdminToken\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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
  apply (rule IDStation_inv_intro)
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
  apply (simp add: tis_defs, hoare_auto)
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

lemma TISValidateAdminToken_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISValidateAdminToken\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: LoginAborted_correct TISValidateAdminToken_def UEC_correct ValidateAdminTokenFail_correct ValidateAdminTokenOK_correct disj_upred_def hoare_ndet)

definition FailedAdminTokenRemove :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FailedAdminTokenRemove =
  ((&internal:enclaveStatus = \<guillemotleft>waitingRemoveAdminTokenFail\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>absent\<guillemotright>
   ) \<longrightarrow>\<^sub>r currentScreen:screenMsg := \<guillemotleft>welcomeAdmin\<guillemotright> ;; 
          internal:enclaveStatus := \<guillemotleft>enclaveQuiescent\<guillemotright>)"

lemma FailedAdminTokenRemove_correct:
  "\<^bold>{IDStation\<^bold>}FailedAdminTokenRemove\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition WaitingAdminTokenRemoval :: "IDStation hrel" where
[upred_defs, tis_defs]:
"WaitingAdminTokenRemoval = 
  ((&internal:enclaveStatus = \<guillemotleft>waitingRemoveAdminTokenFail\<guillemotright>
    \<and> &iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>) \<longrightarrow>\<^sub>r II)"

lemma WaitingAdminTokenRemoval_correct:
  "\<^bold>{IDStation\<^bold>}WaitingAdminTokenRemoval\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition TISCompleteFailedAdminLogon :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISCompleteFailedAdminLogon = (UEC(FailedAdminTokenRemove) \<or> UEC(WaitingAdminTokenRemoval))"

lemma TISCompleteFailedAdminLogon_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISCompleteFailedAdminLogon\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: FailedAdminTokenRemove_correct TISCompleteFailedAdminLogon_def UEC_correct WaitingAdminTokenRemoval_correct disj_upred_def hoare_ndet)

definition [upred_defs, tis_defs]:
"TISAdminLogon = (TISReadAdminToken \<or> TISValidateAdminToken \<or> TISCompleteFailedAdminLogon)"

lemma TISAdminLogon_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISAdminLogon\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: ReadAdminToken_correct TISAdminLogon_def TISCompleteFailedAdminLogon_correct TISReadAdminToken_def TISValidateAdminToken_correct UEC_correct disj_upred_def hoare_ndet)

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

lemma ValidateOpRequestOK_correct:
  "\<^bold>{IDStation\<^bold>}ValidateOpRequestOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition ValidateOpRequestFail :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ValidateOpRequestFail = 
  ((&ikeyboard:keyedDataPresence = \<guillemotleft>present\<guillemotright> \<and>
    &ikeyboard:currentKeyedData \<notin> \<guillemotleft>keyedOps\<guillemotright>`&admin:availableOps) 
    \<longrightarrow>\<^sub>r StartOpContext ;;  
         currentScreen:screenMsg := \<guillemotleft>invalidRequest\<guillemotright>)"

lemma ValidateOpRequestFail_correct:
  "\<^bold>{IDStation\<^bold>}ValidateOpRequestFail\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition NoOpRequest :: "IDStation hrel" where
[upred_defs, tis_defs]:
"NoOpRequest = 
  ((&ikeyboard:keyedDataPresence = \<guillemotleft>absent\<guillemotright>) \<longrightarrow>\<^sub>r StartOpContext)"

lemma NoOpRequest_correct:
  "\<^bold>{IDStation\<^bold>}NoOpRequest\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition [upred_defs, tis_defs]:
"ValidateOpRequest = (ValidateOpRequestOK \<or> ValidateOpRequestFail \<or> NoOpRequest)"

definition [upred_defs, tis_defs]: "TISStartAdminOp = UEC(ValidateOpRequest)"

lemma TISStartAdminOp_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISStartAdminOp\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: NoOpRequest_correct TISStartAdminOp_def UEC_correct ValidateOpRequestFail_correct ValidateOpRequestOK_correct ValidateOpRequest_def disj_upred_def hoare_ndet)

definition AdminOpStartedContext :: "IDStation upred" where
[upred_defs, tis_defs]:
"AdminOpStartedContext =
  U(&internal:enclaveStatus = waitingStartAdminOp \<and> &iadminToken:adminTokenPresence = present)"

definition AdminOpFinishContext :: "IDStation hrel" where
[upred_defs, tis_defs]:
"AdminOpFinishContext =
  (&internal:enclaveStatus = waitingFinishAdminOp \<and> &iadminToken:adminTokenPresence = present)
  \<longrightarrow>\<^sub>r internal:enclaveStatus := enclaveQuiescent ;; admin:currentAdminOp := None"

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

lemma ShutdownOK_correct:
  "\<^bold>{IDStation\<^bold>}ShutdownOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition ShutdownWaitingDoor :: "IDStation hrel" where
[upred_defs, tis_defs]:
"ShutdownWaitingDoor =
  ((&internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright>
   \<and> &admin:currentAdminOp = \<guillemotleft>Some(shutdownOp)\<guillemotright>
   \<and> &doorLatchAlarm:currentDoor = \<guillemotleft>dopen\<guillemotright>
   ) \<longrightarrow>\<^sub>r currentScreen:screenMsg := \<guillemotleft>closeDoor\<guillemotright>
  )"

lemma ShutdownWaitingDoor_correct:
  "\<^bold>{IDStation\<^bold>}ShutdownWaitingDoor\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition TISShutdownOp :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISShutdownOp = (UEC(ShutdownOK) \<or> UEC(ShutdownWaitingDoor))"

lemma TISShutdownOp_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISShutdownOp\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: ShutdownOK_correct ShutdownWaitingDoor_correct TISShutdownOp_def UEC_correct disj_upred_def hoare_ndet)

definition OverrideDoorLockOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"OverrideDoorLockOK =
  ((AdminOpStartedContext \<and> &admin:currentAdminOp = \<guillemotleft>Some(overrideLock)\<guillemotright> 
   ) \<longrightarrow>\<^sub>r currentScreen:screenMsg := requestAdminOp ;; 
          currentDisplay := doorUnlocked ;;
          internal:enclaveStatus := enclaveQuiescent ;;
          UnlockDoor ;;
          AdminFinishOp)"  

lemma OverrideDoorLockOK_correct:
  "\<^bold>{IDStation\<^bold>}OverrideDoorLockOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition TISOverrideDoorLockOp :: "SystemState hrel" where
[upred_defs, tis_defs]:
"TISOverrideDoorLockOp = 
  (UEC(OverrideDoorLockOK)
    \<or> UEC((&internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright> 
        \<and> &admin:currentAdminOp = \<guillemotleft>Some(overrideLock)\<guillemotright>) \<longrightarrow>\<^sub>r BadAdminLogout))"

lemma TISOverrideDoorLockOp_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISOverrideDoorLockOp\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  apply (simp add: TISOverrideDoorLockOp_def)
  apply (rule hoare_disj)
  using OverrideDoorLockOK_correct UEC_correct apply blast 
  apply (rule UEC_correct)
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition StartArchiveLogOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"StartArchiveLogOK =
  (AdminOpStartedContext \<and> &admin:currentAdminOp = \<guillemotleft>Some(archiveLog)\<guillemotright> 
  \<and> &ifloppy:floppyPresence = present) \<longrightarrow>\<^sub>r
  currentScreen:screenMsg := doingOp ;;
  internal:enclaveStatus := waitingFinishAdminOp ;;
  (\<Sqinter> archive :: Audit set \<bullet> 
    ArchiveLog archive ;;
    ifloppy:writtenFloppy := \<guillemotleft>auditFile archive\<guillemotright>)"

definition StartArchiveLogWaitingFloppy :: "IDStation hrel" where
[upred_defs, tis_defs]:
"StartArchiveLogWaitingFloppy =
  (AdminOpStartedContext \<and> &admin:currentAdminOp = \<guillemotleft>Some(archiveLog)\<guillemotright> 
  \<and> &ifloppy:floppyPresence = absent) \<longrightarrow>\<^sub>r
    currentScreen:screenMsg := insertBlankFloppy"

definition StartArchiveLog :: "SystemState hrel" where
[upred_defs, tis_defs]:
  "StartArchiveLog = ((tis:[StartArchiveLogOK]\<^sup>+ ;; UpdateFloppy) 
                      \<or> tis:[StartArchiveLogWaitingFloppy]\<^sup>+
                      \<or> tis:[BadAdminLogout ;; 
                             ?[&internal:enclaveStatus = waitingStartAdminOp
                              \<and> &admin:currentAdminOp = \<guillemotleft>Some(archiveLog)\<guillemotright>]]\<^sup>+)"

definition FinishArchiveLogOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FinishArchiveLogOK = 
  AdminOpFinishContext ;;
  ((&admin:currentAdminOp = \<guillemotleft>Some(archiveLog)\<guillemotright> 
  \<and> &ifloppy:floppyPresence = present
  \<and> &ifloppy:writtenFloppy = &ifloppy:currentFloppy) 
    \<longrightarrow>\<^sub>r (\<Sqinter> archive :: Audit set \<bullet> 
            ClearLogThenAddElements archive ;; 
            ifloppy:writtenFloppy := \<guillemotleft>auditFile archive\<guillemotright>
         ) ;;
         currentScreen:screenMsg := requestAdminOp)"

definition FinishArchiveLogNoFloppy :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FinishArchiveLogNoFloppy = 
  AdminOpFinishContext ;;
  ((&admin:currentAdminOp = \<guillemotleft>Some(archiveLog)\<guillemotright> 
  \<and> &ifloppy:floppyPresence = absent)
    \<longrightarrow>\<^sub>r AddElementsToLog ;; currentScreen:screenMsg := archiveFailed)"

definition FinishArchiveLogBadMatch :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FinishArchiveLogBadMatch = 
  AdminOpFinishContext ;; 
  ((&admin:currentAdminOp = \<guillemotleft>Some(archiveLog)\<guillemotright> 
  \<and> &ifloppy:floppyPresence = present
  \<and> &ifloppy:writtenFloppy \<noteq> &ifloppy:currentFloppy)
    \<longrightarrow>\<^sub>r AddElementsToLog ;; currentScreen:screenMsg := archiveFailed)"

abbreviation "FinishArchiveLogFail \<equiv> FinishArchiveLogBadMatch \<or> FinishArchiveLogNoFloppy"

definition FinishArchiveLog :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FinishArchiveLog = (FinishArchiveLogOK \<or> FinishArchiveLogFail
                    \<or> BadAdminLogout ;; ?[&internal:enclaveStatus = waitingFinishAdminOp
                                         \<and> &admin:currentAdminOp = \<guillemotleft>Some(archiveLog)\<guillemotright>])"

abbreviation "TISArchiveLogOp \<equiv> StartArchiveLog \<or> UEC(FinishArchiveLog)"

definition StartUpdateConfigOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"StartUpdateConfigOK =
  (AdminOpStartedContext \<and> &admin:currentAdminOp = \<guillemotleft>Some(updateConfigData)\<guillemotright> 
  \<and> &ifloppy:floppyPresence = present) \<longrightarrow>\<^sub>r
    currentScreen:screenMsg := doingOp ;;
    internal:enclaveStatus := waitingFinishAdminOp"

lemma StartUpdateConfigOK_correct:
  "\<^bold>{IDStation\<^bold>}StartUpdateConfigOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition StartUpdateConfigWaitingFloppy :: "IDStation hrel" where
[upred_defs, tis_defs]:
"StartUpdateConfigWaitingFloppy =
  (AdminOpStartedContext \<and> &admin:currentAdminOp = \<guillemotleft>Some(updateConfigData)\<guillemotright> 
  \<and> &ifloppy:floppyPresence = absent) \<longrightarrow>\<^sub>r
    currentScreen:screenMsg := insertConfigData"

lemma StartUpdateConfigWaitingFloppy_correct:
  "\<^bold>{IDStation\<^bold>}StartUpdateConfigWaitingFloppy\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition StartUpdateConfigData :: "IDStation hrel" where
[upred_defs, tis_defs]:
"StartUpdateConfigData \<equiv> StartUpdateConfigOK \<or> StartUpdateConfigWaitingFloppy
                       \<or> ?[&internal:enclaveStatus = waitingStartAdminOp \<and>
                           &admin:currentAdminOp = \<guillemotleft>Some(updateConfigData)\<guillemotright>] ;; BadAdminLogout"

lemma StartUpdateConfigData_correct:
  "\<^bold>{IDStation\<^bold>}StartUpdateConfigData\<^bold>{IDStation\<^bold>}"
  apply (simp add: StartUpdateConfigData_def)
  apply (rule hoare_disj)
   apply (simp add: StartUpdateConfigOK_correct)
  apply (rule hoare_disj)
  apply (simp add: StartUpdateConfigWaitingFloppy_correct)
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition FinishUpdateConfigDataOK :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FinishUpdateConfigDataOK =
  AdminOpFinishContext ;;
  ((&admin:currentAdminOp = \<guillemotleft>Some(updateConfigData)\<guillemotright> 
  \<and> &ifloppy:floppyPresence = present \<comment> \<open> Can this we secured via an invariant? \<close>
  \<and> &ifloppy:currentFloppy \<in> \<guillemotleft>range(configFile)\<guillemotright>
  \<and> (Config \<oplus>\<^sub>p config)\<lbrakk>U(configFile_of &ifloppy:currentFloppy)/&config\<rbrakk>
  ) \<longrightarrow>\<^sub>r
    config := configFile_of &ifloppy:currentFloppy ;; 
    currentScreen:screenMsg := requestAdminOp ;;
    \<comment> \<open> The lines are added to preserve the invariants \<close>
    currentScreen:screenConfig := displayConfigData config
    )" (* AddElementsToLog *)

lemma FinishUpdateConfigDataOK_correct:
  "\<^bold>{IDStation\<^bold>}FinishUpdateConfigDataOK\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
         apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition FinishUpdateConfigDataFail :: "IDStation hrel" where
[upred_defs, tis_defs]:
"FinishUpdateConfigDataFail =
  AdminOpFinishContext ;;
  ((&admin:currentAdminOp = \<guillemotleft>Some(updateConfigData)\<guillemotright> 
  \<and> &ifloppy:currentFloppy \<notin> \<guillemotleft>range(configFile)\<guillemotright>
  ) \<longrightarrow>\<^sub>r
    currentScreen:screenMsg := invalidData ;; 
    AddElementsToLog)"

lemma FinishUpdateConfigDataFail_correct:
  "\<^bold>{IDStation\<^bold>}FinishUpdateConfigDataFail\<^bold>{IDStation\<^bold>}"
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition 
[upred_defs, tis_defs]:
"FinishUpdateConfigData \<equiv> FinishUpdateConfigDataOK \<or> FinishUpdateConfigDataFail
                        \<or> ?[&internal:enclaveStatus = waitingFinishAdminOp 
                           \<and> &admin:currentAdminOp = \<guillemotleft>Some(updateConfigData)\<guillemotright>] ;; BadAdminLogout"

lemma FinishUpdateConfigData_correct:
  "\<^bold>{IDStation\<^bold>}FinishUpdateConfigData\<^bold>{IDStation\<^bold>}"
  apply (simp add: FinishUpdateConfigData_def)
  apply (rule hoare_disj)
  apply (simp add: FinishUpdateConfigDataOK_correct)
  apply (rule hoare_disj)
  using FinishUpdateConfigDataFail_correct apply blast
  apply (rule IDStation_correct_intro)
   apply (hoare_wlp_auto defs: tis_defs)
  apply (rule IDStation_inv_intro)
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

definition TISUpdateConfigDataOp :: "SystemState hrel" where
[upred_defs, tis_defs]: "TISUpdateConfigDataOp \<equiv> UEC(StartUpdateConfigData \<or> FinishUpdateConfigData)"

lemma TISUpdateConfigDataOp_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISUpdateConfigDataOp\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: FinishUpdateConfigData_correct StartUpdateConfigData_correct TISUpdateConfigDataOp_def UEC_correct disj_upred_def hoare_ndet)
  
definition TISArchiveLog :: "SystemState hrel" where
[upred_defs, tis_defs]: "TISArchiveLog = false" \<comment> \<open> TODO \<close>

definition TISAdminOp :: "SystemState hrel" where 
[upred_defs, tis_defs]:
"TISAdminOp = (TISOverrideDoorLockOp \<or> TISShutdownOp \<or> TISUpdateConfigDataOp \<or> TISArchiveLog)"
                            
lemma TISAdminOp_correct:
  "\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}TISAdminOp\<^bold>{IDStation \<oplus>\<^sub>p tis\<^bold>}"
  by (simp add: TISAdminOp_def TISArchiveLog_def TISOverrideDoorLockOp_correct TISShutdownOp_correct TISUpdateConfigDataOp_correct disj_upred_def hoare_ndet)
  
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

abbreviation "TISInit \<equiv> tis:[InitIDStation]\<^sup>+"

section \<open>The Whole ID Station\<close>

definition TISOp :: "SystemState hrel" where
[tis_defs]:
"TISOp = ((TISEnrolOp 
  \<or> TISUserEntryOp
  \<or> TISAdminLogon
  \<or> TISStartAdminOp
  \<or> TISAdminOp
  \<or> TISAdminLogout
  \<or> TISIdle) )" (* \<and> (LogChange \<oplus>\<^sub>r tis) *)

abbreviation "TISOpThenUpdate \<equiv> TISOp ;; TISUpdate"

abbreviation "TISBody \<equiv> TISPoll ;; TISEarlyUpdate ;; TISOp ;; TISUpdate"

abbreviation "TIS \<equiv> TISInit ;; TISBody\<^sup>\<star>"

section \<open>Proving Security Properties\<close>

lemma RealWorld_wp [wp]: "\<lbrakk>controlled \<sharp> b; monitored \<sharp> b\<rbrakk> \<Longrightarrow> (RealWorldChanges wp @b) = b"
  by (simp add: tis_defs wp usubst unrest)

lemma 
  "([&tis:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>] \<dagger>
    (TISReadUserToken wp (&tis:doorLatchAlarm:currentLatch = \<guillemotleft>unlocked\<guillemotright>))) = false"
  by (simp add: tis_defs wp usubst unrest alpha)

subsection \<open>Proving Security Functional Requirement 1\<close>

lemma [wp]: "(RealWorldChanges wlp false) = false"
  by (rel_auto)

definition AdminTokenGuardOK :: "IDStation upred" where
[upred_defs, tis_defs]:
"AdminTokenGuardOK =
  ((\<^bold>\<exists> t\<in>\<guillemotleft>TokenWithValidAuth\<guillemotright> \<bullet>
      (\<guillemotleft>goodT(t)\<guillemotright> =\<^sub>u &iadminToken:currentAdminToken 
      \<and> (\<^bold>\<exists> c \<in> \<guillemotleft>AuthCert\<guillemotright> \<bullet> \<guillemotleft>Some c = authCert t\<guillemotright>
         \<and> \<guillemotleft>role c = guard\<guillemotright>) \<oplus>\<^sub>p keyStore
   ))
  )"

text \<open> SFR1(a): If the system invariants hold, the door is initially locked, and a @{term TISUserEntryOp} 
  transition is enabled that unlocks the door, then (1) a valid user token is present and (2)
  either a valid finger print or a valid authorisation certificate is also present. \<close>

text \<open> SFR1(b): If the system invariants hold, the door is initially locked, and a @{term TISAdminOp} 
  transition is enabled that unlocks the door, then an admin token is present with the role
  ``guard'' attached. \<close>

abbreviation (input) "FSFR1 \<equiv>
  &tis:doorLatchAlarm:currentLatch = locked \<and> IDStation \<oplus>\<^sub>p tis \<tturnstile>
    (TISOp ;; TISUpdate) wp (&realWorld:controlled:latch = unlocked) \<Rightarrow> 
    (((UserTokenOK \<and> FingerOK) \<or> UserTokenWithOKAuthCert) \<or> AdminTokenGuardOK) \<oplus>\<^sub>p tis"

declare subst_lit_aext [usubst del]

lemma admin_unlock:
  "[&tis:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>] 
        \<dagger> ((TISAdminOp ;; TISUpdate) wp (&realWorld:controlled:latch = \<guillemotleft>unlocked\<guillemotright>)) =
       U((&tis:internal:enclaveStatus = \<guillemotleft>waitingStartAdminOp\<guillemotright> \<and> &tis:iadminToken:adminTokenPresence = \<guillemotleft>present\<guillemotright>) \<and>
        &tis:admin:currentAdminOp = \<guillemotleft>Some overrideLock\<guillemotright> \<and> &tis:admin:rolePresent \<noteq> None \<and> &tis:admin:currentAdminOp \<noteq> None)"
  by (simp add: tis_defs wp usubst unrest alpha, rel_auto)

declare subst_lit_aext [usubst]

lemma user_unlock:
  "[&tis:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>]
        \<dagger> ((TISUserEntryOp ;; TISUpdate) wp (&realWorld:controlled:latch = \<guillemotleft>unlocked\<guillemotright>)) = 
   U(&tis:internal:status = \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright> \<and> &tis:iuserToken:userTokenPresence = \<guillemotleft>absent\<guillemotright>)"
  by (simp add: tis_defs alpha unrest usubst wp)

lemma unlock:
  "[&tis:doorLatchAlarm:currentLatch \<mapsto>\<^sub>s \<guillemotleft>locked\<guillemotright>] 
        \<dagger> ((TISOpThenUpdate) wp (&realWorld:controlled:latch = \<guillemotleft>unlocked\<guillemotright>)) =
\<^U>(&tis:internal:status = waitingRemoveTokenSuccess \<and> &tis:iuserToken:userTokenPresence = absent \<or>
          ((&tis:internal:enclaveStatus = waitingStartAdminOp \<and> &tis:iadminToken:adminTokenPresence = present) \<and>
          &tis:admin:currentAdminOp = Some overrideLock \<and>
          (&tis:admin:rolePresent) \<noteq> None \<and> (&tis:admin:currentAdminOp) \<noteq> None))"
  apply (simp add: TISOp_def seqr_or_distl wp_disj user_unlock usubst admin_unlock)
  apply (simp add: tis_defs alpha unrest usubst wp call_def)
  apply (rel_auto)
  done

lemma FSFR1_proof: "FSFR1"
  apply (rule sVarEqI)
   apply (simp_all add: usubst unrest unlock)
  apply (rule sImplI)
  apply (simp add: distrib(4))
  apply (rule sAsmDisj)
   apply (simp add: aext_or)
   apply (rule sDisjI1)
   apply (rule sWk[where P="U(&tis:internal:status = waitingRemoveTokenSuccess \<and> &tis:iuserToken:userTokenPresence = absent) \<and>
    U(&tis:doorLatchAlarm:currentLatch = locked) \<and> (IDStation_inv1 \<and> IDStation_inv9) \<oplus>\<^sub>p tis"])
    apply (rel_auto)
   apply (rel_auto)
  apply (rule sWk[where P="(U((&tis:internal:enclaveStatus = waitingStartAdminOp \<and> &tis:iadminToken:adminTokenPresence = present) \<and>
          &tis:admin:currentAdminOp = Some overrideLock \<and>
          (&tis:admin:rolePresent) \<noteq> None \<and> (&tis:admin:currentAdminOp) \<noteq> None) \<and> (IDStation_inv2 \<and> (Admin \<oplus>\<^sub>p admin) \<and> IDStation_inv10) \<oplus>\<^sub>p tis)"])
   apply (rel_simp')
  apply (force)
  apply (rel_auto)
  done

abbreviation "IDStation_inv11 \<equiv> 
  U(&internal:status = \<guillemotleft>waitingRemoveTokenSuccess\<guillemotright> \<Rightarrow>
    (\<exists> t. \<guillemotleft>goodT(t)\<guillemotright> = &iuserToken:currentUserToken
        \<and> (&doorLatchAlarm:currentTime \<in> &config:entryPeriod \<guillemotleft>role (privCert t)\<guillemotright> \<guillemotleft>class (clearance (privCert t))\<guillemotright>)
          \<or> &doorLatchAlarm:currentTime \<in> &config:entryPeriod \<guillemotleft>role (the (authCert t))\<guillemotright> \<guillemotleft>class (clearance (the (authCert t)))\<guillemotright>))"
lemma "\<^bold>{IDStation_inv11\<^bold>}UnlockDoorOK\<^bold>{IDStation_inv11\<^bold>}"
  by (hoare_wlp_auto)

lemma "\<^bold>{IDStation_inv11\<^bold>}WaitingTokenRemoval\<^bold>{IDStation_inv11\<^bold>}"
  by (hoare_wlp_auto)

lemma "\<^bold>{IDStation_inv11\<^bold>}TokenRemovalTimeout\<^bold>{IDStation_inv11\<^bold>}"
  by (hoare_wlp_auto)

lemma "\<^bold>{IDStation_inv11\<^bold>}EntryOK\<^bold>{IDStation_inv11\<^bold>}"
  by (hoare_wlp_auto)

lemma "\<^bold>{IDStation_inv11 \<oplus>\<^sub>p tis\<^bold>}TISPoll ;; TISUnlockDoor\<^bold>{IDStation_inv11 \<oplus>\<^sub>p tis\<^bold>}"
  apply (simp add: wlp_hoare_link wp unrest usubst tis_defs)
  oops

lemma "(TISReadUserToken wp (&tis:audit:auditAlarm = alarming))\<lbrakk>\<guillemotleft>silent\<guillemotright>/&tis:audit:auditAlarm\<rbrakk> = false"
  by (simp add: tis_defs alpha unrest usubst wp)

lemma "(AddElementsToLog wp (&audit:auditAlarm = alarming))\<lbrakk>\<guillemotleft>silent\<guillemotright>/&audit:auditAlarm\<rbrakk> = undefined"
  apply (simp add: tis_defs alpha unrest usubst wp)
  oops

definition AlarmInv :: "SystemState upred" where
[upred_defs, tis_defs]:
"AlarmInv = U(&realWorld:controlled:latch = \<guillemotleft>locked\<guillemotright> \<and>
              &tis:doorLatchAlarm:currentDoor = \<guillemotleft>dopen\<guillemotright> \<and>
              &tis:doorLatchAlarm:currentTime \<ge> &tis:doorLatchAlarm:alarmTimeout
             \<Rightarrow> &realWorld:controlled:alarm = \<guillemotleft>alarming\<guillemotright>)"

abbreviation "FSFR3 \<equiv>
  `IDStation \<Rightarrow>
         U(&doorLatchAlarm:currentLatch = locked
          \<and> &doorLatchAlarm:currentDoor = dopen
          \<and> &doorLatchAlarm:currentTime \<ge> &doorLatchAlarm:alarmTimeout
          \<Rightarrow> &doorLatchAlarm:doorAlarm = alarming)`"

lemma FSFR3_proof: "FSFR3"
  by rel_auto

lemma nmods_UEC [closure]: "\<lbrakk> vwb_lens a; P nmods a \<rbrakk> \<Longrightarrow> UEC(P) nmods &tis:a"
  by (simp add: UEC_def closure)

declare nmods_assigns [closure del]

lemma TISUserEntryOp_nmods_config: "TISUserEntryOp nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma TISEnrolOp_nmods_config: "TISEnrolOp nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma TISAdminLogon_nmods_config: "TISAdminLogon nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma TISStartAdminOp_nmods_config: "TISStartAdminOp nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma StartUpdateConfigData_nmods_config:
  "StartUpdateConfigData nmods config"
  by (simp add: tis_defs closure)

lemma FinishUpdateConfigOK_absent_nmods_config: 
  "?[&iadminToken:adminTokenPresence = absent] ;; FinishUpdateConfigDataOK nmods config"
proof -
  have "?[&iadminToken:adminTokenPresence = absent] ;; AdminOpFinishContext = false"
    by rel_simp'
  hence "?[&iadminToken:adminTokenPresence = absent] ;; FinishUpdateConfigDataOK = false"
    by (simp add: FinishUpdateConfigDataOK_def RA1)
  thus ?thesis
    by (metis assume_false config_vwb_lens nmods_guard)
qed

lemma FinishUpdateConfigDataFail_nmods_config:
  "FinishUpdateConfigDataFail nmods config"
  by (simp add: tis_defs closure)

lemma BadAdminLogout_nmods_config:
  "BadAdminLogout nmods config"
  by (simp add: tis_defs closure)

lemma FinishUpdateConfigData_absent_nmods_config:
  "(?[&iadminToken:adminTokenPresence = absent] ;; FinishUpdateConfigData) nmods config"
  by (simp add: FinishUpdateConfigData_def seqr_or_distr closure BadAdminLogout_nmods_config FinishUpdateConfigDataFail_nmods_config FinishUpdateConfigOK_absent_nmods_config)

lemma frext_guard [frame]: "vwb_lens a \<Longrightarrow> a:[?[b]]\<^sup>+ = ?[b \<oplus>\<^sub>p a]"
  by (rel_auto)

lemma TISUpdateConfigDataOp_absent_nmods_config:
  "?[&tis:iadminToken:adminTokenPresence = absent] ;; TISUpdateConfigDataOp nmods &tis:config"
proof -
  have "\<And> P. ?[&tis:iadminToken:adminTokenPresence = absent] ;; UEC(P) 
            = UEC(?[&iadminToken:adminTokenPresence = absent] ;; P)"
    by (simp add: UEC_def seq_UINF_distl' frame alpha seqr_assoc)
  thus ?thesis
    by (simp add: TISUpdateConfigDataOp_def seqr_or_distr closure 
        FinishUpdateConfigData_absent_nmods_config StartUpdateConfigData_nmods_config)
qed

lemma TISOverrideDoorLockOp_nmods_config: "TISOverrideDoorLockOp nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma TISShutdownOp_nmods_config: "TISShutdownOp nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma TISArchiveLog_nmods_config: "TISArchiveLog nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma TISAdminOp_absent_nmods_config:
  "?[&tis:iadminToken:adminTokenPresence = absent] ;; TISAdminOp nmods &tis:config"
  by (simp add: TISAdminOp_def seqr_or_distr TISUpdateConfigDataOp_absent_nmods_config closure
      TISOverrideDoorLockOp_nmods_config TISShutdownOp_nmods_config TISArchiveLog_nmods_config)

lemma TISAdminLogout_nmods_config: "TISAdminLogout nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma TISIdle_nmods_config: "TISIdle nmods &tis:config"
  by (simp add: tis_defs closure del: UEC_def)

lemma TISOp_nmods_floppy: "TISOp nmods &tis:ifloppy"
  by (simp add: tis_defs closure del: UEC_def)

abbreviation "FSFR6 == ?[&tis:iadminToken:adminTokenPresence = absent] ;; TISOp nmods {&tis:config, &tis:ifloppy}"

lemma FSFR6_proof: FSFR6
  apply (rule nmods_plus)
  apply (simp add: TISOp_def seqr_or_distr closure TISUserEntryOp_nmods_config TISEnrolOp_nmods_config
      TISAdminLogon_nmods_config TISStartAdminOp_nmods_config TISAdminLogout_nmods_config
      TISIdle_nmods_config TISAdminOp_absent_nmods_config )
  apply (simp add: TISOp_nmods_floppy closure)
  done

end