(*  Title:       Logging-independent Message Anonymity in the Relational Method
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Logging-independent message anonymity and Restricted Identification"

theory Definitions
  imports Main
begin


subsection "Introduction"

text \<open>
\emph{Logging-dependent message anonymity} is the property for a message exchanged or otherwise used
in a cryptographic protocol to remain anonymous although the attacker can log the messages generated
or accepted by legitimate agents, and map any two observable messages contained in any such message
to the same agent. An approach to modeling and verifying this security property according to the
\emph{relational method} for formal protocol verification has been described in @{cite "Noce20"},
along with the method itself. This approach makes use of two further type constructors for messages,
@{text IDInfo} and @{text Log}, as well as of two functions, @{text crypts} and @{text key_sets}.
Particularly, @{text IDInfo} is used to model message anonymity, while the remaining constants are
used to formalize the property for a message to be observable by the spy within some logged message.

\emph{Logging-independent message anonymity} rather is the property for a given message to remain
anonymous in spite of the attacker's capability of mapping messages of that sort to agents without
resorting to message logging, namely by means of some intrinsic feature of such messages. From the
above observation, it follows that @{text IDInfo} is the sole anonymity-related constant required if
the only kind of anonymity of interest for a given protocol is the logging-independent one, whereas
@{text Log}, @{text crypts}, and @{text key_sets} are unnecessary and can be left out of the model.
It is also possible to include both kinds of anonymity in the model, in which case some protocol
rule will enable the spy to map messages of some sort to agents only if they are observable within
logged messages, while some other protocol rule will enable the spy to do so independently of this
condition.

This paper illustrates how logging-independent message anonymity can be formalized according to the
relational method by considering a real-world protocol, namely the Restricted Identification one by
the BSI @{cite "BSI16-2"} @{cite "BSI16-3"}, whose very purpose is to allow for the exchange of
messages endowed with this security property.
\<close>


subsection "Case study: the Restricted Identification protocol"

text \<open>
\label{Protocol}

The Restricted Identification protocol enables \emph{user identification tokens} (e.g. electronic
documents) to generate and output unambiguous \emph{pseudonymous identifiers}, distinct for any
given group of terminals of arbitrary granularity, referred to as a \emph{sector}, and usable to
identify the tokens across different sessions taking place within the same sector. For example, such
identifiers allow for the creation of sector-specific revocation lists, at the same time preserving
the anonymity of the holder of any token included in such a list.

This protocol is based on a \emph{Public Key Infrastructure (PKI)} comprising the token issuer,
which owns a \emph{revocation key pair} $(SK_{Rev}, PK_{Rev})$ and generates a \emph{token key pair}
$(SK_{Tok}, PK_{Tok})$ for each token, and sectors, each one endowed with its own \emph{sector key
pair} $(SK_{Sec}, PK_{Sec})$, where $PK_{Sec} = [SK_{Sec}]PK_{Rev}$. This PKI may use either an
integer finite field or an elliptic curve group, as long as the selected domain parameters are
cryptographically secure. In a real-world PKI, each sector has actually two distinct key pairs,
which enables the tokens to generate as many different pseudonymous identifiers per sector, but this
detail is irrelevant to the anonymity of such identifiers and can then be omitted from the model.

According to @{cite "BSI16-2"} @{cite "BSI16-3"}, the Restricted Identification protocol may only be
executed using the session keys established via Chip Authentication version 2/3, after performing
Terminal Authentication version 2 with a terminal certificate containing both sector public keys'
hashes (including domain parameters), whose authenticity is ensured by the certificate's signature.
After requesting to start the protocol, which again is irrelevant and can be left out of the model,
the terminal sends either of its sector public keys $PK_{Sec}$ (including domain parameters) to the
token, which in turn verifies that $PK_{Sec}$'s hash matches the one contained in the certificate
and replies with its pseudonymous identifier $H([SK_{Tok}]PK_{Sec})$, where $H$ is a hash function.
If necessary (for instance, to insert it into a sector-specific revocation list), this identifier
can be recomputed in the external world as $H([SK_{Sec}]([SK_{Rev}]PK_{Tok}))$, with the concurrence
of both the token issuer and the entity responsible for the involved sector.

As a matter of fact, since the only purpose of the protocol model to be developed is to verify the
logging-independent anonymity of token pseudonymous identifiers, without any confidentiality or
authenticity concern, it is sufficient to model a simpler protocol in which the terminal and the
token exchange their messages in plain, without using any session key. Moreover, since both Chip and
Terminal Authentication are out of scope, the Restricted Identification protocol will be modeled as
a stand-alone one. Consequently, although both of them are exchanged during Terminal Authentication
in the real-world protocol, $PK_{Sec}$'s signature will be assumed to be exchanged with $PK_{Sec}$
in the model, while the related verification key will be assumed to be known by the token a priori.
The hash function used to sign $PK_{Sec}$ may differ from the one used to compute token pseudonymous
identifiers, but once more, this is just an omissible functional detail.

A further simplification, admissible for the same reason, is to let the token use domain parameters
known a priori rather than the input ones, whose presence in the input message can then be left out.
Indeed, this prevents the spy from snatching $SK_{Tok}$ by making an element of a smaller group pass
for an authentic sector public key, which could be done by signing it with a compromised signature
generation key. For example, if the PKI used a group of 128-bit order, $SK_{Tok}$ could be disclosed
by first searching the private key $SK'_{Tok}$ associated with a fake identifier ranging in a group
of 64-bit order $n$, and then detecting $SK_{Tok}$ as the unique private key associated with a given
genuine identifier among all those differing from $SK'_{Tok}$ by a multiple of $n$. So, two searches
within as many spaces of $2^{64}$ elements, which is a computationally feasible task nowadays, would
suffice to find $SK_{Tok}$. However, such \emph{small group attacks} can safely be ruled out as long
as the initial state @{text s\<^sub>0} comprises an arbitrary set of compromised token private keys, given
that verifying the conditions under which these keys remain secret is out of scope.

As a result of all the simplifications described above, the protocol that is going to be modeled is
as follows.

  \<^enum> Terminal $\rightarrow$ Token: \tabto{10em} $\{PK_{Sec}, \{H(PK_{Sec})\}_{SK_{Sign}}\}$\\

    The terminal sends the token a message consisting of its sector public key and a precomputed
    signature of this key.\\

  \<^enum> Token $\rightarrow$ Terminal: \tabto{10em} $H([SK_{Tok}]PK_{Sec})$\\

    The token verifies that the hash of the received public key matches the signed one, and then
    replies with the pseudonymous identifier resulting from this key.

Unless it is compromised by means other than attacking the protocol, the anonymity of a given token
pseudonymous identifier $H([SK_{Tok}]PK_{Sec})$ is expected to be vulnerable if and only if either
$SK_{Tok}$ is anonymity-compromised, or $SK_{Sec}$ is compromised and there is another compromised
sector private key $SK'_{Sec}$ such that $H([SK_{Tok}]PK'_{Sec})$ is anonymity-compromised. In fact,
the spy can detect the use of $SK_{Tok}$ in $H([SK_{Tok}]PK_{Sec})$ in the former case, whereas in
the latter one he can map $H([SK_{Tok}]PK_{Sec})$ to the same token as $H([SK_{Tok}]PK'_{Sec})$ by
recognizing that $[SK_{Tok}]PK_{Sec} = [SK_{Sec}\times(SK'_{Sec})^{-1}]([SK_{Tok}]PK'_{Sec})$.

The purpose of the following formal development is precisely to formally prove the correctness of
this expectation. In more detail, the \emph{only if} conditional implied by the previous statement
will be proven as an \emph{anonymity property} in the next section, while the \emph{if} conditional
will be proven in the form of two \emph{possibility properties} in the subsequent one. Since both
relevant attack options leverage the intrinsic features of token pseudonymous identifiers, namely
the private keys used to generate them, logging-independent message anonymity has to be considered
rather than logging-dependent one.

For further information about the formal definitions and proofs contained in this paper, see
Isabelle documentation, particularly @{cite "Paulson21"}, @{cite "Nipkow21"}, @{cite "Krauss21"},
and @{cite "Nipkow11"}.
\<close>


subsection "Agents, messages, protocol rules"

text \<open>
Agents consist of an infinite population of tokens and sectors, identified through natural numbers,
plus the spy. Actually, the model can safely ignore terminals altogether and assume that tokens are
presented to sectors as a whole, since all the terminal-side messages used in the protocol refer to
sectors rather than to individual terminals. The only possible exceptions are signature key pairs.
In fact, although the entity signing terminal certificates is the same for every terminal in a given
sector (in @{cite "BSI16-2"} and @{cite "BSI16-3"}, it is named \emph{Document Verifier}), nothing
prevents that entity to use distinct signature generation keys for different terminals (for example,
if their certificates are issued at different times). Nonetheless, the granularity of signature key
pairs is irrelevant to the anonymity of token pseudonymous identifiers according to the previous
considerations, so these key pairs can be associated with sectors as well.

As opposed to what happens in @{cite "Noce20"}, there is no correlation here between any two agents
@{text "Token n"} and @{text "Sector n"} marked with the same numeric identifier @{text n}. In fact,
tokens and sectors are independent of each other, and any token may be presented to whatever sector.

\null
\<close>

type_synonym agent_id = nat

datatype agent =
  Token agent_id |
  Sector agent_id |
  Spy

text \<open>
\null

As regards the key pairs for key agreement, private keys are identified by natural numbers, whereas
public keys by sets of natural numbers. The implied interpretation is that @{text "PubK S"} stands
for public key $[k]G$, where $G$ is the group generator and $k$ is the modular product of all the
private keys referred to by the numeric identifiers in $S$, each one occurring as a factor exactly
once. Using \emph{multisets} of natural numbers instead of sets would have allowed private keys to
be used as factors even more than once, but this option can be left out as the PKI does not provide
for any public key computed in this way. The need for this ad hoc message format, like those used to
represent session keys and Chip Authentication Data in @{cite "Noce20"}, confirms that reuse of the
spy's capabilities' model in the inductive method is hindered by the likely need for ad hoc message
formats in case of protocols using nontrivial public key cryptography @{cite "Noce20"}.

Besides key agreement keys, messages comprise signature generation/verification keys (identified by
the numeric identifiers of the respective sectors), hash values, cryptograms, and compound messages
built via message concatenation. Furthermore, message anonymity is modeled by means of constructor
@{text IDInfo} @{cite "Noce20"}. Since the anonymity of terminal-side messages is of no concern, the
interpretation of message @{text "\<langle>n, X\<rangle>"} is "message @{text X} is mapped to @{term "Token n"}",
namely @{text n} is always interpreted as a token's numeric identifier rather than a sector's one.

\null
\<close>

type_synonym key_id = nat

datatype agr_key =
  PriK key_id |
  PubK "key_id set"

datatype enc_key =
  SigK agent_id |
  VerK agent_id

datatype msg =
  AgrKey agr_key |
  EncKey enc_key |
  Hash msg |
  Crypt enc_key msg |
  MPair msg msg |
  IDInfo agent_id msg

syntax
  "_MPair"  :: "['a, args] \<Rightarrow> 'a * 'b"  ("(2\<lbrace>_,/ _\<rbrace>)")
  "_IDInfo" :: "[agent_id, msg] \<Rightarrow> msg"      ("(2\<langle>_,/ _\<rangle>)")
translations
  "\<lbrace>X, Y, Z\<rbrace>" \<rightleftharpoons> "\<lbrace>X, \<lbrace>Y, Z\<rbrace>\<rbrace>"
  "\<lbrace>X, Y\<rbrace>" \<rightleftharpoons> "CONST MPair X Y"
  "\<langle>n, X\<rangle>" \<rightleftharpoons> "CONST IDInfo n X"


abbreviation SigKey :: "agent_id \<Rightarrow> msg" where
"SigKey \<equiv> EncKey \<circ> SigK"

abbreviation VerKey :: "agent_id \<Rightarrow> msg" where
"VerKey \<equiv> EncKey \<circ> VerK"

abbreviation PriKey :: "key_id \<Rightarrow> msg" where
"PriKey \<equiv> AgrKey \<circ> PriK"

abbreviation PubKey :: "key_id set \<Rightarrow> msg" where
"PubKey \<equiv> AgrKey \<circ> PubK"

primrec InvK :: "enc_key \<Rightarrow> enc_key" where
"InvK (SigK n) = VerK n" |
"InvK (VerK n) = SigK n"

abbreviation InvKey :: "enc_key \<Rightarrow> msg" where
"InvKey \<equiv> EncKey \<circ> InvK"


inductive_set parts :: "msg set \<Rightarrow> msg set"
  for H :: "msg set" where

parts_used [intro]:
  "X \<in> H \<Longrightarrow> X \<in> parts H" |

parts_crypt [intro]:
  "Crypt K X \<in> parts H \<Longrightarrow> X \<in> parts H" |

parts_fst [intro]:
  "\<lbrace>X, Y\<rbrace> \<in> parts H \<Longrightarrow> X \<in> parts H" |

parts_snd [intro]:
  "\<lbrace>X, Y\<rbrace> \<in> parts H \<Longrightarrow> Y \<in> parts H"

definition parts_msg :: "msg \<Rightarrow> msg set" where
"parts_msg X \<equiv> parts {X}"

text \<open>
\null

Constant @{text Rev_PriK} is the numeric identifier of the revocation private key, while functions
@{text Sec_PriK} and @{text Tok_PriK} map the numeric identifiers of sectors and tokens to those of
the respective sector/token private keys. It is assumed that these functions are injective, as well
as that their ranges do not contain @{text Rev_PriK} and are disjoint, and such axioms are proven to
be consistent by showing that there exist three constants satisfying all of them. On the whole,
these axioms just model the assumption that private keys are generated by cryptographically secure
means throughout the PKI, so that the probability for any given private key to occur more than once
within the PKI is negligible.

\null
\<close>

consts Rev_PriK :: key_id

consts Sec_PriK :: "agent_id \<Rightarrow> key_id"

consts Tok_PriK :: "agent_id \<Rightarrow> key_id"

specification (Rev_PriK Sec_PriK Tok_PriK)
  sec_prik_inj: "inj Sec_PriK"
  tok_prik_inj: "inj Tok_PriK"
  sec_prik_rev: "Rev_PriK \<notin> range Sec_PriK"
  tok_prik_rev: "Rev_PriK \<notin> range Tok_PriK"
  sec_prik_tok_prik: "range Sec_PriK \<inter> range Tok_PriK = {}"
by (rule exI [of _ 0], rule exI [of _ "\<lambda>n. n + n + 1"],
 rule exI [of _ "\<lambda>n. n + n + 2"], auto simp: inj_on_def, arith)


abbreviation Gen_PubKey :: msg where
"Gen_PubKey \<equiv> PubKey {}"

abbreviation Rev_PriKey :: msg where
"Rev_PriKey \<equiv> PriKey Rev_PriK"

abbreviation Rev_PubKey :: msg where
"Rev_PubKey \<equiv> PubKey {Rev_PriK}"

abbreviation Tok_PriKey :: "agent_id \<Rightarrow> msg" where
"Tok_PriKey n \<equiv> PriKey (Tok_PriK n)"

abbreviation Tok_PubKey :: "agent_id \<Rightarrow> msg" where
"Tok_PubKey n \<equiv> PubKey {Tok_PriK n}"

abbreviation Sec_PriKey :: "agent_id \<Rightarrow> msg" where
"Sec_PriKey n \<equiv> PriKey (Sec_PriK n)"

abbreviation Sec_PubKey :: "agent_id \<Rightarrow> msg" where
"Sec_PubKey n \<equiv> PubKey {Sec_PriK n, Rev_PriK}"

abbreviation Sign :: "agent_id \<Rightarrow> msg \<Rightarrow> msg" where
"Sign n X \<equiv> Crypt (SigK n) (Hash X)"

abbreviation ID :: "agent_id \<Rightarrow> msg \<Rightarrow> msg" where
"ID n X \<equiv> case X of AgrKey (PubK S) \<Rightarrow> PubKey (insert (Tok_PriK n) S)"

text \<open>
\null

The spy's starting knowledge, as defined by the initial state @{text s\<^sub>0}, consists of the following
messages.

  \<^item> All the public keys used in the PKI (including the group generator).

  \<^item> All token pseudonymous identifiers (in both hashed and non-hashed formats).

  \<^item> Compromised private keys used in the PKI (excluding the revocation one, assumed to be secret).

  \<^item> Mappings of all token public keys, compromised token private keys, and anonymity-compromised
    token pseudonymous identifiers (in both hashed and non-hashed formats) to the respective tokens.

\null
\<close>

consts bad_sigk :: "agent_id set"

consts bad_sec_prik :: "agent_id set"

consts bad_tok_prik :: "agent_id set"

consts bad_id :: "(agent_id \<times> agent_id) set"

type_synonym event = "agent \<times> msg"

type_synonym state = "event set"

abbreviation used :: "state \<Rightarrow> msg set" where
"used s \<equiv> Range s"

abbreviation spied :: "state \<Rightarrow> msg set" where
"spied s \<equiv> s `` {Spy}"

abbreviation s\<^sub>0 :: state where
"s\<^sub>0 \<equiv> {Spy} \<times> ({Gen_PubKey, Rev_PubKey} \<union>
  SigKey ` bad_sigk \<union> Sec_PriKey ` bad_sec_prik \<union> Tok_PriKey ` bad_tok_prik \<union>
  range VerKey \<union> range Sec_PubKey \<union> range Tok_PubKey \<union>
  range (\<lambda>(n, m). ID n (Sec_PubKey m)) \<union>
  range (\<lambda>(n, m). Hash (ID n (Sec_PubKey m))) \<union>
  range (\<lambda>n. \<langle>n, Tok_PubKey n\<rangle>) \<union>
  {\<langle>n, Tok_PriKey n\<rangle> | n. n \<in> bad_tok_prik} \<union>
  {\<langle>n, ID n (Sec_PubKey m)\<rangle> | n m. (n, m) \<in> bad_id} \<union>
  {\<langle>n, Hash (ID n (Sec_PubKey m))\<rangle> | n m. (n, m) \<in> bad_id})"

text \<open>
\null

Protocol rules are defined here below. Particularly, for any public key $[SK_1\times...\times SK_n]
G$ known to the spy, they enable him to generate public key $[SK_1\times...\times SK_n\times
SK_{n+1}]G$ for any additional, compromised private key $SK_{n+1}$, as well as public key
$[SK_1\times...\times SK_{i-1}\times SK_{i+1}\times...\times SK_n]G$ for any compromised private key
$SK_i$, where $1\leq i\leq n$ (which is equivalent to multiplying the original public key by $(SK_i)
^{-1}$). The spy can also map the resulting public keys to the same token, if identified, as the
original public key, in the latter case as long as the related token private key still occurs as a
factor in the resulting modular product. Furthermore, the spy can associate a token with any known
public key whose modular product of private keys contains the corresponding token private key as a
factor, provided that this key is compromised.

\null
\<close>

abbreviation rel_sector :: "(state \<times> state) set" where
"rel_sector \<equiv> {(s, s') | s s' m.
  s' = s \<union> {Sector m, Spy} \<times> {\<lbrace>Sec_PubKey m, Sign m (Sec_PubKey m)\<rbrace>}}"

abbreviation rel_token :: "(state \<times> state) set" where
"rel_token \<equiv> {(s, s') | s s' m n S.
  s' = s \<union> {Token n, Spy} \<times> {Hash (ID n (PubKey S))} \<and>
  \<lbrace>PubKey S, Sign m (PubKey S)\<rbrace> \<in> used s}"


abbreviation rel_pubk_less :: "(state \<times> state) set" where
"rel_pubk_less \<equiv> {(s, s') | s s' A S.
  s' = insert (Spy, PubKey (S - {A})) s \<and>
  {PriKey A, PubKey S} \<subseteq> spied s}"

abbreviation rel_pubk_more :: "(state \<times> state) set" where
"rel_pubk_more \<equiv> {(s, s') | s s' A S.
  s' = insert (Spy, PubKey (insert A S)) s \<and>
  {PriKey A, PubKey S} \<subseteq> spied s}"

abbreviation rel_hash :: "(state \<times> state) set" where
"rel_hash \<equiv> {(s, s') | s s' X.
  s' = insert (Spy, Hash X) s \<and>
  X \<in> spied s}"

abbreviation rel_dec :: "(state \<times> state) set" where
"rel_dec \<equiv> {(s, s') | s s' K X.
  s' = insert (Spy, X) s \<and>
  {Crypt K X, InvKey K} \<subseteq> spied s}"

abbreviation rel_enc :: "(state \<times> state) set" where
"rel_enc \<equiv> {(s, s') | s s' K X.
  s' = insert (Spy, Crypt K X) s \<and>
  {X, EncKey K} \<subseteq> spied s}"

abbreviation rel_sep :: "(state \<times> state) set" where
"rel_sep \<equiv> {(s, s') | s s' X Y.
  s' = s \<union> {Spy} \<times> {X, Y} \<and>
  \<lbrace>X, Y\<rbrace> \<in> spied s}"

abbreviation rel_con :: "(state \<times> state) set" where
"rel_con \<equiv> {(s, s') | s s' X Y.
  s' = insert (Spy, \<lbrace>X, Y\<rbrace>) s \<and>
  {X, Y} \<subseteq> spied s}"


abbreviation rel_id_pubk_less :: "(state \<times> state) set" where
"rel_id_pubk_less \<equiv> {(s, s') | s s' n A S.
  s' = insert (Spy, \<langle>n, PubKey (S - {A})\<rangle>) s \<and>
  {PriKey A, PubKey (S - {A}), \<langle>n, PubKey S\<rangle>} \<subseteq> spied s \<and>
  Tok_PriK n \<in> S - {A}}"

abbreviation rel_id_pubk_more :: "(state \<times> state) set" where
"rel_id_pubk_more \<equiv> {(s, s') | s s' n A S.
  s' = insert (Spy, \<langle>n, PubKey (insert A S)\<rangle>) s \<and>
  {PriKey A, PubKey (insert A S), \<langle>n, PubKey S\<rangle>} \<subseteq> spied s}"

abbreviation rel_id_pubk_prik :: "(state \<times> state) set" where
"rel_id_pubk_prik \<equiv> {(s, s') | s s' n S.
  s' = insert (Spy, \<langle>n, PubKey S\<rangle>) s \<and>
  {Tok_PriKey n, PubKey S} \<subseteq> spied s \<and>
  Tok_PriK n \<in> S}"

abbreviation rel_id_hash :: "(state \<times> state) set" where
"rel_id_hash \<equiv> {(s, s') | s s' n X.
  s' = s \<union> {Spy} \<times> {\<langle>n, X\<rangle>, \<langle>n, Hash X\<rangle>} \<and>
  {X, Hash X} \<subseteq> spied s \<and>
  (\<langle>n, X\<rangle> \<in> spied s \<or> \<langle>n, Hash X\<rangle> \<in> spied s)}"


definition rel :: "(state \<times> state) set" where
"rel \<equiv> rel_sector \<union> rel_token \<union> rel_pubk_less \<union> rel_pubk_more \<union>
  rel_hash \<union> rel_dec \<union> rel_enc \<union> rel_sep \<union> rel_con \<union>
  rel_id_pubk_less \<union> rel_id_pubk_more \<union> rel_id_pubk_prik \<union> rel_id_hash"

abbreviation in_rel :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 60) where
"s \<turnstile> s' \<equiv> (s, s') \<in> rel"

abbreviation in_rel_rtrancl :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>" 60) where
"s \<Turnstile> s' \<equiv> (s, s') \<in> rel\<^sup>*"

end
