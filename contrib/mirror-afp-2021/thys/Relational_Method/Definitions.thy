(*  Title:       The Relational Method with Message Anonymity for the Verification of Cryptographic Protocols
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "The relational method and message anonymity"

theory Definitions
  imports Main
begin

text \<open>
\null

\emph{This paper is dedicated to my mother, my favourite chess opponent -- in addition to being many
other wonderful things!}
\<close>


subsection "Introduction"

text \<open>
As Bertrand Russell says in the last pages of \emph{A History of Western Philosophy}, a distinctive
feature of science is that "we can make successive approximations to the truth, in which each new
stage results from an improvement, not a rejection, of what has gone before". When dealing with a
formal verification method for information processing systems, such as Paulson's inductive method
for the verification of cryptographic protocols (cf. @{cite "Paulson98"}, @{cite "Paulson20"}), a
more modest goal for this iterative improvement process, yet of significant practical importance, is
to streamline the definitions and proofs needed to model such a system and verify its properties.

With this aim, specially when it comes to verifying protocols using public key cryptography, this
paper proposes an enhancement of the inductive method, named \emph{relational method} for reasons
clarified in what follows, and puts it into practice by verifying a sample protocol. This new method
is the result of some changes to the way how events, states, spy's capabilities, and the protocol
itself are formalized in the inductive method. Here below is a description of these changes, along
with a rationale for them.

  \<^descr>[Events.] In the inductive method, the fundamental building blocks of cryptographic protocols are
events of the form @{text "Says A B X"}, where @{text X} is a message being exchanged, @{text A} is
the agent that sends it, and @{text B} is the agent to which it is addressed.
\\However, any exchanged message can be intercepted by the spy and forwarded to any other agent, so
its intended recipient is not relevant for the protocol \emph{security} correctness -- though of
course being relevant for the protocol \emph{functional} correctness. Moreover, a legitimate agent
may also generate messages, e.g. ephemeral private keys, that she will never exchange with any other
agent. To model such an event, a datatype constructor other than @{text Says} should be used. How to
make things simpler?
\\The solution adopted in the relational method is to model events just as ordered pairs of the form
@{text "(A, X)"}, where @{text A} is an agent and @{text X} is a message. If event @{text "(A, X)"}
stands for @{text A}'s sending of @{text X} to another agent, where @{text A} is a legitimate agent,
then this event will be accompanied by event @{text "(Spy, X)"}, representing the spy's interception
of @{text X}. If event @{text "(A, X)"} rather stands for @{text A}'s generation of private message
@{text X}, e.g. an ephemeral private key, for her own exclusive use -- and if the spy has not hacked
@{text A} so as to steal her private messages as well --, then no companion event @{text "(Spy, X)"}
will occur instead.

  \<^descr>[States.] In the inductive method, the possible states of a cryptographic protocol are modeled as
event \emph{traces}, i.e. lists, and the protocol itself is formalized as a set of such traces.
Consequently, the protocol rules and security properties are expressed as formulae satisfied by any
event trace @{text evs} belonging to this set.
\\However, these formulae are such that their truth values depend only on the events contained in
@{text evs}, rather than on the actual order in which they occur -- in fact, robust protocol rules
and security properties cannot depend on the exact sequence of message exchanges in a scenario where
the spy can freely intercept and forward messages, or even generate and send her own ones. Thus, one
library function, @{const set}, and two custom recursive functions, @{text used} and @{text knows},
are needed to convert event traces into event sets and message sets, respectively.
\\In the relational method, protocol states are simply modeled as event sets, so that the occurrence
of event @{text "(A, X)"} in state @{text s} can be expressed as the transition to the augmented
state @{term "insert (A, X) s"}. Hence, states consist of relations between agents and messages. As
a result, function @{const set} need not be used any longer, whereas functions @{text used} and
@{text spied} -- the latter one being a replacement for @{text "knows Spy"} --, which take a state
@{text s} as input, are mere abbreviations for @{term "Range s"} and @{term "s `` {Spy}"}.

  \<^descr>[Spy's capabilities.] In the inductive method, the spy's attack capabilities are formalized via
two inductively defined functions, @{text analz} and @{text synth}, used to construct the sets of
all the messages that the spy can learn -- @{text "analz (knows Spy evs)"} -- and send to legitimate
agents -- @{text "synth (analz (knows Spy evs))"} -- downstream of event trace @{text evs}.
\\Indeed, the introduction of these functions goes in the direction of decoupling the formalization
of the spy's capabilities from that of the protocol itself, consistently with the fact that what the
spy can do is independent of how the protocol works -- which only matters when it comes to verifying
protocol security.
\\In principle, this promises to provide a relevant benefit: these functions need to be defined, and
their properties to be proven, just once, whereupon such definitions and properties can be reused in
the formalization and verification of whatever protocol.
\\In practice, since both functions are of type @{text "msg set \<Rightarrow> msg set"}, where @{text msg} is
the datatype defining all possible message formats, this benefit only applies as long as message
formats remain unchanged. However, when it comes to verifying a protocol making use of public key
cryptography, some new message format, and consequently some new related spy's capability as well,
are likely to be required. An example of this will be provided right away by the protocol considered
in this paper.
\\In the relational method, the representation of events as agent-message pairs offers a simpler way
to model the spy's capabilities, namely as supplementary protocol rules, analogous to the inductive
method's @{text Fake} rule, augmenting a state by one or more events of the form @{text "(Spy, X)"}.
In addition to eliminating the need for functions @{text analz} and @{text synth} -- which, in light
of the above considerations, does not significantly harm reusability --, this choice also abolishes
any distinction between what the spy can learn and what she can send. In fact, a state containing
event @{text "(Spy, X)"} is interpreted as one where the spy both knows message @{text X} and may
have sent it to whatever legitimate agent. Actually, this formalizes the facts that a real-world
attacker is free to send any message she has learned to any other party, and conversely to use any
message she has generated to further augment her knowledge.
\\In the inductive method, the former fact is modeled by property @{term "H \<subseteq> synth H"} of function
@{text synth}, but the latter one has no formal counterpart, as in general @{term "H \<subset> synth H"}.
This limitation on the spy's capabilities is not significant as long as the protocol makes use of
static keys only, but it is if session keys or ephemeral key pairs are generated -- as happens in
key establishment protocols, even in those using symmetric cryptography alone. In any such case, a
realistic spy must also be able to learn from anything she herself has generated, such as a nonce or
an ephemeral private key -- a result achieved without effort in the relational method.
\\An additional, nontrivial problem for the inductive method is that many protocols, including key
establishment ones, require the spy to be able to generate \emph{fresh} ephemeral messages only, as
otherwise the spy could succeed in breaking the protocol by just guessing the ephemeral messages
already generated at random by some legitimate agent -- a quite unrealistic attack pattern, provided
that such messages vary in a sufficiently wide range. At first glance, this need could be addressed
by extending the inductive definition of function @{text synth} with introduction rules of the form
@{term "Nonce n \<notin> H \<Longrightarrow> Nonce n \<in> synth H"} or @{term "PriKey A \<notin> H \<Longrightarrow> PriKey A \<in> synth H"}.
However, private ephemeral messages are not in general included in @{text "analz (knows Spy evs)"},
since nonces may be encrypted with uncompromised keys when exchanged and private keys are usually
not exchanged at all, so this approach would not work. The only satisfactory alternative would be to
change the signature of function @{text synth}, e.g. by adding a second input message set @{text H'}
standing for @{text "used evs"}, or else by replacing @{text H} with event trace @{text evs} itself,
but this would render the function definition much more convoluted -- a problem easily bypassed in
the relational method.

  \<^descr>[Protocol.] In the inductive method, a cryptographic protocol consists of an inductively defined
set of event traces. This enables to prove the protocol security properties by induction using the
induction rule automatically generated as a result of such an inductive definition, i.e. by means of
\emph{rule induction}. Actually, this feature is exactly what gives the method its very name. Hence,
a consistent way to name a protocol verification method using some other form of induction would be
to replace adjective "inductive" with another one referring to that form of induction.
\\The relational method owes its name to this consideration. In this method, the introduction rules
defining \emph{protocol rules}, i.e. the possible transitions between protocol states, are replaced
with \emph{relations} between states, henceforth named \emph{protocol relations}. That is, for any
two states @{text s} and @{text s'}, there exists a transition leading from @{text s} to @{text s'}
just in case the ordered pair @{term "(s, s')"} is contained in at least one protocol relation --
a state of affairs denoted using infix notation @{text "s \<turnstile> s'"}. Then, the inductively defined set
itself is replaced with the \emph{reflexive transitive closure} of the union of protocol relations.
Namely, any state @{text s} may be reached from \emph{initial state} @{text s\<^sub>0}, viz. is a possible
protocol state, just in case pair @{term "(s\<^sub>0, s)"} lies within this reflexive transitive closure --
a state of affairs denoted using infix notation @{text "s\<^sub>0 \<Turnstile> s"}. As a result, rule induction is
replaced with induction over reflexive transitive closures via rule @{thm [source] rtrancl_induct},
which is the circumstance that originates the method name.
\\These changes provide the following important benefits.

    \<^item> Inserting and modifying the formal definition of a protocol is much more comfortable. In fact,
any change even to a single introduction rule within a monolithic inductive set definition entails a
re-evaluation of the whole definition, whereas each protocol relation will have its own stand-alone
definition, which also makes it easier to find errors. This advantage may go almost unnoticed for a
very simple protocol providing for just a few protocol rules, but gets evident in case of a complex
protocol. An example of this will be provided by the protocol considered in this paper: when looking
at the self-contained abbreviations used to define protocol relations, the reader will easily grasp
how much more convoluted an equivalent inductive set definition would have been.

    \<^item> In addition to induction via rule @{thm [source] rtrancl_induct}, a further powerful reasoning
pattern turns out to be available. It is based on the following general rule applying to reflexive
transitive closures (indeed, a rule so general and useful that it could rightfully become part of
the standard library), later on proven and assigned the name @{text rtrancl_start}:
@{prop [display] "\<lbrakk>(x, y) \<in> r\<^sup>*; P y; \<not> P x\<rbrakk> \<Longrightarrow>
\<exists>u v. (x, u) \<in> r\<^sup>* \<and> (u, v) \<in> r \<and> (v, y) \<in> r\<^sup>* \<and> \<not> P u \<and> P v"}
In natural language, this rule states that for any chain of elements linked by a relation, if some
predicate is false for the first element of the chain and true for the last one, there must exist a
link in the chain where the predicate becomes true.
\\This rule can be used to prove propositions of the form @{text "\<lbrakk>s \<Turnstile> s'; P s'[; Q]\<rbrakk> \<Longrightarrow> R s'"} for
any state @{text s} and predicate @{text P} such that @{term "\<not> P s"}, with an optional additional
assumption @{text Q}, without resorting to induction. Notably, \emph{regularity lemmas} have exactly
this form, where @{term "s = s\<^sub>0"}, @{term "P = (\<lambda>s. X \<in> parts (used s))"} for some term @{text X} of
type @{text msg}, and @{text Q}, if present, puts some constraint on @{text X} or its components.
\\Such a proof consists of two steps. First, lemma @{text "\<lbrakk>s \<turnstile> s'; P s'; \<not> P s[; Q]\<rbrakk> \<Longrightarrow> R s'"} is
proven by simplification, using the definitions of protocol relations. Then, the target proposition
is proven by applying rule @{text rtrancl_start} as a destruction rule (cf. @{cite "Paulson20"}) and
proving @{term "P s'"} by assumption, @{term "\<not> P s"} by simplification, and the residual subgoal
by means of the previous lemma.

In addition to the relational method, this paper is aimed at introducing still another enhancement:
besides message confidentiality and authenticity, it takes into consideration a further important
security property, \emph{message anonymity}. Being legitimate agents identified via natural numbers,
the fact that in state @{text s} the spy ignores that message @{text X\<^sub>n} is associated with agent
@{text n}, viz. @{text X\<^sub>n}'s property of being \emph{anonymous} in state @{text s}, can be expressed
as @{text "\<langle>n, X\<^sub>n\<rangle> \<notin> spied s"}, where notation @{text "\<langle>n, X\<^sub>n\<rangle>"} refers to a new constructor added to
datatype @{text msg} precisely for this purpose.

A basic constraint upon any protocol relation augmenting the spy's knowledge with @{text "\<langle>n, X\<rangle>"}
is that the spy must know message @{text X} in the current state, as it is impossible to identify
the agent associated with an unknown message. There is also an additional, more subtle constraint.
Any such protocol relation either augments a state in which the spy knows @{text "\<langle>n, C X\<^sub>1 \<dots> X\<^sub>m\<rangle>"},
i.e. containing event @{text "(Spy, \<langle>n, C X\<^sub>1 \<dots> X\<^sub>m\<rangle>)"}, with event @{text "(Spy, \<langle>n, X\<^sub>i\<rangle>)"}, where
$1 \leq i \leq m$ and @{text C} is some constructor of datatype @{text msg}, or conversely augments
a state containing event @{text "(Spy, \<langle>n, X\<^sub>i\<rangle>)"} with @{text "(Spy, \<langle>n, C X\<^sub>1 \<dots> X\<^sub>m\<rangle>)"}. However, the
latter spy's inference is justified only if the compound message @{text "C X\<^sub>1 \<dots> X\<^sub>m"} is part of a
message generated or accepted by some legitimate agent according to the protocol rules. Otherwise,
that is, if @{text "C X\<^sub>1 \<dots> X\<^sub>m"} were just a message generated at random by the spy, her inference
would be as sound as those of most politicians and all advertisements: even if the conclusion were
true, it would be so by pure chance.

This problem can be solved as follows.

  \<^item> A further constructor @{text Log}, taking a message as input, is added to datatype @{text msg},
and every protocol relation modeling the generation or acceptance of a message @{text X} by some
legitimate agent must augment the current state with event @{term "(Spy, Log X)"}.
\\In this way, the set of all the messages that have been generated or accepted by some legitimate
agent in state @{text s} matches @{term "Log -` spied s"}.

  \<^item> A function @{text crypts} is defined inductively. It takes a message set @{text H} as input, and
returns the least message set @{text H'} such that @{term "H \<subseteq> H'"} and for any (even empty) list
of keys @{text KS}, if the encryption of @{text "\<lbrace>X, Y\<rbrace>"}, @{text "\<lbrace>Y, X\<rbrace>"}, or @{text "Hash X"}
with @{text KS} is contained in @{text H'}, then the encryption of @{text X} with @{text KS} is
contained in @{text H'} as well. 
\\In this way, the set of all the messages that are part of messages exchanged by legitimate agents,
viz. that may be mapped to agents, in state @{text s} matches @{term "crypts (Log -` spied s)"}.

  \<^item> Another function @{text key_sets} is defined, too. It takes two inputs, a message @{text X} and
a message set @{text H}, and returns the set of the sets of @{text KS}' inverse keys for any list of
keys @{text KS} such that the encryption of @{text X} with @{text KS} is included in @{text H}.
\\In this way, the fact that in state @{text s} the spy can map a compound message @{text X} to some
agent, provided that she knows all the keys in set @{text U}, can be expressed through conditions
@{term "U \<in> key_sets X (crypts (Log -` spied s))"} and @{term "U \<subseteq> spied s"}.
\\The choice to define @{text key_sets} so as to collect the inverse keys of encryption keys, viz.
decryption ones, depends on the fact that the sample protocol verified in this paper uses symmetric
keys alone -- which match their own inverse keys -- for encryption, whereas asymmetric key pairs are
used in cryptograms only for signature generation -- so that the inverse keys are public ones. In
case of a protocol (also) using public keys for encryption, encryption keys themselves should (also)
be collected, since the corresponding decryption keys, i.e. private keys, would be unknown to the
spy by default. This would formalize the fact that encrypted messages can be mapped to agents not
only by decrypting them, but also by recomputing the cryptograms (provided that the plaintexts are
known) and checking whether they match the exchanged ones.
\<close>


subsection "A sample protocol"

text \<open>
As previously mentioned, this paper tries the relational method, including message anonymity, by
applying it to the verification of a sample authentication protocol in which Password Authenticated
Connection Establishment (PACE) with Chip Authentication Mapping (cf. @{cite "ICAO15"}) is first
used by an \emph{owner} to establish a secure channel with her own \emph{asset} and authenticate it,
and then the owner sends a password (other than the PACE one) to the asset over that channel so as
to authenticate herself. This enables to achieve a reliable mutual authentication even if the PACE
key is shared by multiple owners or is weak, as happens in electronic passports. Although the PACE
mechanism is specified for use in electronic documents, nothing prevents it in principle from being
used in other kinds of smart cards or even outside of the smart card world, which is the reason why
this paper uses the generic names \emph{asset} and \emph{owner} for the card and the cardholder,
respectively.

In more detail, this protocol provides for the following steps. In this list, messages are specified
using the same syntax that will be adopted in the formal text (for further information about PACE
with Chip Authentication Mapping, cf. @{cite "ICAO15"}).

  \<^enum> \emph{Asset n} $\rightarrow$ \emph{Owner n}:
\\\hspace*{1em}@{text "Crypt (Auth_ShaKey n) (PriKey S)"}

  \<^enum> \emph{Owner n} $\rightarrow$ \emph{Asset n}:
\\\hspace*{1em}@{text "\<lbrace>Num 1, PubKey A\<rbrace>"}

  \<^enum> \emph{Asset n} $\rightarrow$ \emph{Owner n}:
\\\hspace*{1em}@{text "\<lbrace>Num 2, PubKey B\<rbrace>"}

  \<^enum> \emph{Owner n} $\rightarrow$ \emph{Asset n}:
\\\hspace*{1em}@{text "\<lbrace>Num 3, PubKey C\<rbrace>"}

  \<^enum> \emph{Asset n} $\rightarrow$ \emph{Owner n}:
\\\hspace*{1em}@{text "\<lbrace>Num 4, PubKey D\<rbrace>"}

  \<^enum> \emph{Owner n} $\rightarrow$ \emph{Asset n}:
\\\hspace*{1em}@{text "Crypt (SesK SK) (PubKey D)"}

  \<^enum> \emph{Asset n} $\rightarrow$ \emph{Owner n}:
\\\hspace*{1em}@{text "\<lbrace>Crypt (SesK SK) (PubKey C),"}
\\\hspace*{1.5em}@{text "Crypt (SesK SK) (Auth_PriK n \<otimes> B),"}
\\\hspace*{1.5em}@{text "Crypt (SesK SK) (Crypt SigK"}
\\\hspace*{2em}@{text "\<lbrace>Hash (Agent n), Hash (Auth_PubKey n)\<rbrace>)\<rbrace>"}

  \<^enum> \emph{Owner n} $\rightarrow$ \emph{Asset n}:
\\\hspace*{1em}@{text "Crypt (SesK SK) (Pwd n)"}

  \<^enum> \emph{Asset n} $\rightarrow$ \emph{Owner n}:
\\\hspace*{1em}@{text "Crypt (SesK SK) (Num 0)"}

Legitimate agents consist of an infinite population of assets and owners. For each natural number
@{text n}, @{text "Owner n"} is an owner and @{text "Asset n"} is her own asset, and these agents
are assigned the following authentication data.

  \<^item> @{text "Key (Auth_ShaKey n)"}: static symmetric PACE key shared by both agents.

  \<^item> @{text "Auth_PriKey n"}, @{text "Auth_PubKey n"}: static private and public keys stored on
@{text "Asset n"} and used for @{text "Asset n"}'s authentication via Chip Authentication Mapping.

  \<^item> @{text "Pwd n"}: unique password (other than the PACE one) shared by both agents and used for
@{text "Owner n"}'s authentication.

Function @{text Pwd} is defined as a constructor of datatype @{text msg} and then is injective,
which formalizes the assumption that each asset-owner pair has a distinct password, whereas no such
constraint is put on functions @{text Auth_ShaKey}, @{text Auth_PriKey}, and @{text Auth_PubKey},
which allows multiple asset-owner pairs to be assigned the same keys. On the other hand, function
@{text Auth_PriKey} is constrained to be such that the complement of its range is infinite. As each
protocol run requires the generation of fresh ephemeral private keys, this constraint ensures that
an unbounded number of protocol runs can be carried out. All assumptions are formalized by applying
the definitional approach, viz. without introducing any axiom, and so is this constraint, expressed
by defining function @{text Auth_PriKey} using the indefinite description operator @{text SOME}.

The protocol starts with @{text "Asset n"} sending an ephemeral private key encrypted with the PACE
key to @{text "Owner n"}. Actually, if @{text "Asset n"} is a smart card, the protocol should rather
start with @{text "Owner n"} sending a plain request for such encrypted nonce, but this preliminary
step is omitted here as it is irrelevant for protocol security. After that, @{text "Owner n"} and
@{text "Asset n"} generate two ephemeral key pairs each and send the respective public keys to the
other party.

Then, both parties agree on the same session key by deriving it from the ephemeral keys generated
previously (actually, two distinct session keys would be derived, one for encryption and the other
one for MAC computation, but such a level of detail is unnecessary for protocol verification). The
session key is modeled as @{text "Key (SesK SK)"}, where @{text SesK} is an apposite constructor
added to datatype @{text key} and @{term "SK = (Some S, {A, B}, {C, D})"}. The adoption of type
@{typ "nat option"} for the first component enables to represent as @{term "(None, {A, B}, {C, D})"}
the wrong session key derived from @{text "Owner n"} if @{text "PriKey S"} was encrypted using a key
other than @{text "Key (Auth_ShaKey n)"} -- which reflects the fact that the protocol goes on even
without the two parties sharing the same session key. The use of type @{typ "nat set"} for the other
two components enables the spy to compute @{text "Key (SesK SK)"} if she knows \emph{either} private
key and the other public key referenced by each set, as long as she also knows @{text "PriKey S"} --
which reflects the fact that given two key pairs, Diffie-Hellman key agreement generates the same
shared secret independently of which of the respective private keys is used for computation.

This session key is used by both parties to compute their authentication tokens. Both encrypt the
other party's second ephemeral public key, but @{text "Asset n"} appends two further fields: the
Encrypted Chip Authentication Data, as provided for by Chip Authentication Mapping, and an encrypted
signature of the hash values of @{text "Agent n"} and @{text "Auth_PubKey n"}. Infix notation
@{text "Auth_PriK n \<otimes> B"} refers to a constructor of datatype @{text msg} standing for plain Chip
Authentication Data, and @{text Agent} is another such constructor standing for agent identification
data. @{text "Owner n"} is expected to validate this signature by also checking @{text "Agent n"}'s
hash value against reference identification data known by other means -- otherwise, the spy would
not be forced to know @{text "Auth_PriKey n"} to masquerade as @{text "Asset n"}, since she could do
that by just knowing @{text "Auth_PriKey m"} for some other @{text m}, even if @{term "Auth_PriKey m
\<noteq> Auth_PriKey n"}. If @{text "Asset n"} is an electronic passport, the owner, i.e. the inspection
system, could get cardholder's identification data by reading her personal data on the booklet, and
such a signature could be retrieved from the chip (actually through a distinct message, but this is
irrelevant for protocol security as long as the password is sent after the signature's validation)
by reading the Document Security Object -- provided that @{text "Auth_PubKey n"} is included within
Data Group 14.

The protocol ends with @{text "Owner n"} sending her password, encrypted with the session key, to
@{text "Asset n"}, who validates it and replies with an encrypted acknowledgment.

Here below are some concluding remarks about the way how this sample protocol is formalized.

  \<^item> A single signature private key, unknown to the spy, is assumed to be used for all legitimate
agents. Similarly, the spy might have hacked some legitimate agent so as to steal her ephemeral
private keys as soon as they are generated, but here all legitimate agents are assumed to be out of
the spy's reach in this respect. Of course, this is just the choice of one of multiple possible
scenarios, and nothing prevents these assumptions from being dropped.

  \<^item> In the real world, a legitimate agent would use any one of her ephemeral private keys just once,
after which the key would be destroyed. On the contrary, no such constraint is enforced here, since
it turns out to be unnecessary for protocol verification. There is a single exception, required for
the proof of a unicity lemma: after @{text "Asset n"} has used @{text "PriKey B"} to compute her
authentication token, she must discard @{text "PriKey B"} so as not to use this key any longer. The
way how this requirement is expressed emphasizes once more the flexibility of the modeling of events
in the relational method: @{text "Asset n"} may use @{text "PriKey B"} in this computation only if
event @{text "(Asset n, PubKey B)"} is not yet contained in the current state @{text s}, and then
@{text s} is augmented with that event. Namely, events can also be used to model garbage collection!

  \<^item> The sets of the legitimate agents whose authentication data have been identified in advance (or
equivalently, by means other than attacking the protocol, e.g. by social engineering) by the spy are
defined consistently with the constraint that known data alone can be mapped to agents, as well as
with the definition of initial state @{text s\<^sub>0}. For instance, the set @{text bad_id_prikey} of the
agents whose Chip Authentication private keys have been identified is defined as a subset of the set
@{text bad_prikey} of the agents whose Chip Authentication private keys have been stolen. Moreover,
all the signatures included in assets' authentication tokens are assumed to be already known to the
spy in state @{text s\<^sub>0}, so that @{text bad_id_prikey} includes also any agent whose identification
data or Chip Authentication public key have been identified in advance.

  \<^item> The protocol rules augmenting the spy's knowledge with some message of the form @{text "\<langle>n, X\<rangle>"}
generally require the spy to already know some other message of the same form. There is just one
exception: the spy can infer @{text "\<langle>n, Agent n\<rangle>"} from @{text "Agent n"}. This expresses the fact
that the detection of identification data within a message generated or accepted by some legitimate
agent is in itself sufficient to map any known component of that message to the identified agent,
regardless of whether any data were already mapped to that agent in advance.

  \<^item> As opposed to what happens for constructors @{text "(\<otimes>)"} and @{text "MPair"}, there do not
exist two protocol rules enabling the spy to infer @{text "\<langle>n, Crypt K X\<rangle>"} from @{text "\<langle>n, X\<rangle>"} or
@{text "\<langle>n, Key K\<rangle>"} and vice versa. A single protocol rule is rather defined, which enables the spy
to infer @{text "\<langle>n, X\<rangle>"} from @{text "\<langle>n, Key K\<rangle>"} or vice versa, provided that @{text "Crypt K X"}
has been exchanged by some legitimate agent. In fact, the protocol provides for just one compound
message made up of cryptograms, i.e. the asset's authentication token, and all these cryptograms are
generated using the same encryption key @{text "Key (SesK SK)"}. Thus, if two such cryptograms have
plaintexts @{text X\<^sub>1}, @{text X\<^sub>2} and the spy knows @{text "\<langle>n, X\<^sub>1\<rangle>"}, she can infer @{text "\<langle>n, X\<^sub>2\<rangle>"}
by inferring @{text "\<langle>n, Key (SesK SK)\<rangle>"}, viz. she need not know @{text "\<langle>n, Crypt (SesK SK) X\<^sub>1\<rangle>"}
to do that.

The formal content is split into the following sections.

  \<^item> Section \ref{Definitions}, \emph{Definitions}, contains all the definitions needed to formalize
the sample protocol by means of the relational method, including message anonymity.

  \<^item> Section \ref{Authentication}, \emph{Confidentiality and authenticity properties}, proves that
the following theorems hold under appropriate assumptions.

    \<^enum> Theorem @{text sigkey_secret}: the signature private key is secret.

    \<^enum> Theorem @{text auth_shakey_secret}: an asset-owner pair's PACE key is secret.

    \<^enum> Theorem @{text auth_prikey_secret}: an asset's Chip Authentication private key is secret.

    \<^enum> Theorem @{text owner_seskey_unique}: an owner's session key is unknown to other owners.

    \<^enum> Theorem @{text owner_seskey_secret}: an owner's session key is secret.

    \<^enum> Theorem @{text owner_num_genuine}: the encrypted acknowledgment received by an owner has been
sent by the respective asset.

    \<^enum> Theorem @{text owner_token_genuine}: the PACE authentication token received by an owner has
been generated by the respective asset, using her Chip Authentication private key and the same
ephemeral keys used to derive the session key.

    \<^enum> Theorem @{text pwd_secret}: an asset-owner pair's password is secret.

    \<^enum> Theorem @{text asset_seskey_unique}: an asset's session key is unknown to other assets, and
may be used by that asset to compute just one PACE authentication token.

    \<^enum> Theorem @{text asset_seskey_secret}: an asset's session key is secret.

    \<^enum> Theorem @{text asset_pwd_genuine}: the encrypted password received by an asset has been sent
by the respective owner.

    \<^enum> Theorem @{text asset_token_genuine}: the PACE authentication token received by an asset has
been generated by the respective owner, using the same ephemeral key used to derive the session key.

  Particularly, these proofs confirm that the mutual authentication between an owner and her asset
is reliable even if their PACE key is compromised, unless either their Chip Authentication private
key or their password also is -- namely, the protocol succeeds in implementing a two-factor mutual
authentication.

  \<^item> Section \ref{Anonymity}, \emph{Anonymity properties}, proves that the following theorems hold
under appropriate assumptions.

    \<^enum> Theorem @{text pwd_anonymous}: an asset-owner pair's password is anonymous.

    \<^enum> Theorem @{text auth_prikey_anonymous}: an asset's Chip Authentication private key is
anonymous.

    \<^enum> Theorem @{text auth_shakey_anonymous}: an asset-owner pair's PACE key is anonymous.

  \<^item> Section \ref{Possibility}, \emph{Possibility properties}, shows how possibility properties (cf.
@{cite "Paulson98"}) can be proven by constructing sample protocol runs, either ordinary or attack
ones. Two such properties are proven:

    \<^enum> Theorem @{text runs_unbounded}: for any possible protocol state @{text s} and any asset-owner
pair, there exists a state @{text s'} reachable from @{text s} in which a protocol run has been
completed by those agents using an ephemeral private key @{text "PriKey S"} not yet exchanged in
@{text s} -- namely, an unbounded number of protocol runs can be carried out by legitimate agents.

    \<^enum> Theorem @{text pwd_compromised}: in a scenario not satisfying the assumptions of theorem
@{text pwd_anonymous}, the spy can steal an asset-owner pair's password and even identify those
agents.

  The latter is an example of a possibility property aimed at confirming that the assumptions of a
given confidentiality, authenticity, or anonymity property are necessary for it to hold.

For further information about the formal definitions and proofs contained in these sections, see
Isabelle documentation, particularly @{cite "Paulson20"}, @{cite "Nipkow20"}, @{cite "Krauss20"},
and @{cite "Nipkow11"}.

\textbf{Important note.} This sample protocol was already considered in a former paper of mine (cf.
@{cite "Noce17"}). For any purpose, that paper should be regarded as being obsolete and superseded
by the present paper.
\<close>


subsection "Definitions"

text \<open>
\label{Definitions}
\<close>

type_synonym agent_id = nat

type_synonym key_id = nat

type_synonym seskey_in = "key_id option \<times> key_id set \<times> key_id set"

datatype agent =
  Asset agent_id |
  Owner agent_id |
  Spy

datatype key =
  SigK |
  VerK |
  PriK key_id |
  PubK key_id |
  ShaK key_id |
  SesK seskey_in

datatype msg =
  Num nat |
  Agent agent_id |
  Pwd agent_id |
  Key key |
  Mult key_id key_id (infixl "\<otimes>" 70) |
  Hash msg |
  Crypt key msg |
  MPair msg msg |
  IDInfo agent_id msg |
  Log msg

syntax
  "_MPair"  :: "['a, args] \<Rightarrow> 'a * 'b"  ("(2\<lbrace>_,/ _\<rbrace>)")
  "_IDInfo" :: "[agent_id, msg] \<Rightarrow> msg"      ("(2\<langle>_,/ _\<rangle>)")
translations
  "\<lbrace>X, Y, Z\<rbrace>" \<rightleftharpoons> "\<lbrace>X, \<lbrace>Y, Z\<rbrace>\<rbrace>"
  "\<lbrace>X, Y\<rbrace>" \<rightleftharpoons> "CONST MPair X Y"
  "\<langle>n, X\<rangle>" \<rightleftharpoons> "CONST IDInfo n X"


abbreviation SigKey :: "msg" where
"SigKey \<equiv> Key SigK"

abbreviation VerKey :: "msg" where
"VerKey \<equiv> Key VerK"

abbreviation PriKey :: "key_id \<Rightarrow> msg" where
"PriKey \<equiv> Key \<circ> PriK"

abbreviation PubKey :: "key_id \<Rightarrow> msg" where
"PubKey \<equiv> Key \<circ> PubK"

abbreviation ShaKey :: "key_id \<Rightarrow> msg" where
"ShaKey \<equiv> Key \<circ> ShaK"

abbreviation SesKey :: "seskey_in \<Rightarrow> msg" where
"SesKey \<equiv> Key \<circ> SesK"

primrec InvK :: "key \<Rightarrow> key" where
"InvK SigK = VerK" |
"InvK VerK = SigK" |
"InvK (PriK A) = PubK A" |
"InvK (PubK A) = PriK A" |
"InvK (ShaK SK) = ShaK SK" |
"InvK (SesK SK) = SesK SK"

abbreviation InvKey :: "key \<Rightarrow> msg" where
"InvKey \<equiv> Key \<circ> InvK"


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


inductive_set crypts :: "msg set \<Rightarrow> msg set"
  for H :: "msg set" where

crypts_used [intro]:
  "X \<in> H \<Longrightarrow> X \<in> crypts H" |

crypts_hash [intro]:
  "foldr Crypt KS (Hash X) \<in> crypts H \<Longrightarrow> foldr Crypt KS X \<in> crypts H" |

crypts_fst [intro]:
  "foldr Crypt KS \<lbrace>X, Y\<rbrace> \<in> crypts H \<Longrightarrow> foldr Crypt KS X \<in> crypts H" |

crypts_snd [intro]:
  "foldr Crypt KS \<lbrace>X, Y\<rbrace> \<in> crypts H \<Longrightarrow> foldr Crypt KS Y \<in> crypts H"


definition key_sets :: "msg \<Rightarrow> msg set \<Rightarrow> msg set set" where
"key_sets X H \<equiv> {InvKey ` set KS | KS. foldr Crypt KS X \<in> H}"

definition parts_msg :: "msg \<Rightarrow> msg set" where
"parts_msg X \<equiv> parts {X}"

definition crypts_msg :: "msg \<Rightarrow> msg set" where
"crypts_msg X \<equiv> crypts {X}"

definition key_sets_msg :: "msg \<Rightarrow> msg \<Rightarrow> msg set set" where
"key_sets_msg X Y \<equiv> key_sets X {Y}"

fun seskey_set :: "seskey_in \<Rightarrow> key_id set" where
"seskey_set (Some S, U, V) = insert S (U \<union> V)" |
"seskey_set (None, U, V) = U \<union> V"


definition Auth_PriK :: "agent_id \<Rightarrow> key_id" where
"Auth_PriK \<equiv> SOME f. infinite (- range f)"

abbreviation Auth_PriKey :: "agent_id \<Rightarrow> msg" where
"Auth_PriKey \<equiv> PriKey \<circ> Auth_PriK"

abbreviation Auth_PubKey :: "agent_id \<Rightarrow> msg" where
"Auth_PubKey \<equiv> PubKey \<circ> Auth_PriK"

consts Auth_ShaK :: "agent_id \<Rightarrow> key_id"

abbreviation Auth_ShaKey :: "agent_id \<Rightarrow> key" where
"Auth_ShaKey \<equiv> ShaK \<circ> Auth_ShaK"

abbreviation Sign :: "agent_id \<Rightarrow> key_id \<Rightarrow> msg" where
"Sign n A \<equiv> Crypt SigK \<lbrace>Hash (Agent n), Hash (PubKey A)\<rbrace>"

abbreviation Token :: "agent_id \<Rightarrow> key_id \<Rightarrow> key_id \<Rightarrow> key_id \<Rightarrow> seskey_in \<Rightarrow> msg"
where "Token n A B C SK \<equiv> \<lbrace>Crypt (SesK SK) (PubKey C),
  Crypt (SesK SK) (A \<otimes> B), Crypt (SesK SK) (Sign n A)\<rbrace>"


consts bad_agent :: "agent_id set"

consts bad_pwd :: "agent_id set"

consts bad_shak :: "key_id set"

consts bad_id_pwd :: "agent_id set"

consts bad_id_prik :: "agent_id set"

consts bad_id_pubk :: "agent_id set"

consts bad_id_shak :: "agent_id set"

definition bad_prik :: "key_id set" where
"bad_prik \<equiv> SOME U. U \<subseteq> range Auth_PriK"

abbreviation bad_prikey :: "agent_id set" where
"bad_prikey \<equiv> Auth_PriK -` bad_prik"

abbreviation bad_shakey :: "agent_id set" where
"bad_shakey \<equiv> Auth_ShaK -` bad_shak"

abbreviation bad_id_password :: "agent_id set" where
"bad_id_password \<equiv> bad_id_pwd \<inter> bad_pwd"

abbreviation bad_id_prikey :: "agent_id set" where
"bad_id_prikey \<equiv> (bad_agent \<union> bad_id_pubk \<union> bad_id_prik) \<inter> bad_prikey"

abbreviation bad_id_pubkey :: "agent_id set" where
"bad_id_pubkey \<equiv> bad_agent \<union> bad_id_pubk \<union> bad_id_prik \<inter> bad_prikey"

abbreviation bad_id_shakey :: "agent_id set" where
"bad_id_shakey \<equiv> bad_id_shak \<inter> bad_shakey"


type_synonym event = "agent \<times> msg"

type_synonym state = "event set"

abbreviation used :: "state \<Rightarrow> msg set" where
"used s \<equiv> Range s"

abbreviation spied :: "state \<Rightarrow> msg set" where
"spied s \<equiv> s `` {Spy}"

abbreviation s\<^sub>0 :: state where
"s\<^sub>0 \<equiv> range (\<lambda>n. (Asset n, Auth_PriKey n)) \<union> {Spy} \<times> insert VerKey
  (range Num \<union> range Auth_PubKey \<union> range (\<lambda>n. Sign n (Auth_PriK n)) \<union>
   Agent ` bad_agent \<union> Pwd ` bad_pwd \<union> PriKey ` bad_prik \<union> ShaKey ` bad_shak \<union>
   (\<lambda>n. \<langle>n, Pwd n\<rangle>) ` bad_id_password \<union>
   (\<lambda>n. \<langle>n, Auth_PriKey n\<rangle>) ` bad_id_prikey \<union>
   (\<lambda>n. \<langle>n, Auth_PubKey n\<rangle>) ` bad_id_pubkey \<union>
   (\<lambda>n. \<langle>n, Key (Auth_ShaKey n)\<rangle>) ` bad_id_shakey)"


abbreviation rel_asset_i :: "(state \<times> state) set" where
"rel_asset_i \<equiv> {(s, s') | s s' n S.
  s' = insert (Asset n, PriKey S) s \<union>
    {Asset n, Spy} \<times> {Crypt (Auth_ShaKey n) (PriKey S)} \<union>
    {(Spy, Log (Crypt (Auth_ShaKey n) (PriKey S)))} \<and>
  PriKey S \<notin> used s}"

abbreviation rel_owner_ii :: "(state \<times> state) set" where
"rel_owner_ii \<equiv> {(s, s') | s s' n S A K.
  s' = insert (Owner n, PriKey A) s \<union>
    {Owner n, Spy} \<times> {\<lbrace>Num 1, PubKey A\<rbrace>} \<union>
    {Spy} \<times> Log ` {Crypt K (PriKey S), \<lbrace>Num 1, PubKey A\<rbrace>} \<and>
  Crypt K (PriKey S) \<in> used s \<and>
  PriKey A \<notin> used s}"

abbreviation rel_asset_ii :: "(state \<times> state) set" where
"rel_asset_ii \<equiv> {(s, s') | s s' n A B.
  s' = insert (Asset n, PriKey B) s \<union>
    {Asset n, Spy} \<times> {\<lbrace>Num 2, PubKey B\<rbrace>} \<union>
    {Spy} \<times> Log ` {\<lbrace>Num 1, PubKey A\<rbrace>, \<lbrace>Num 2, PubKey B\<rbrace>} \<and>
  \<lbrace>Num 1, PubKey A\<rbrace> \<in> used s \<and>
  PriKey B \<notin> used s}"

abbreviation rel_owner_iii :: "(state \<times> state) set" where
"rel_owner_iii \<equiv> {(s, s') | s s' n B C.
  s' = insert (Owner n, PriKey C) s \<union>
    {Owner n, Spy} \<times> {\<lbrace>Num 3, PubKey C\<rbrace>} \<union>
    {Spy} \<times> Log ` {\<lbrace>Num 2, PubKey B\<rbrace>, \<lbrace>Num 3, PubKey C\<rbrace>} \<and>
  \<lbrace>Num 2, PubKey B\<rbrace> \<in> used s \<and>
  PriKey C \<notin> used s}"

abbreviation rel_asset_iii :: "(state \<times> state) set" where
"rel_asset_iii \<equiv> {(s, s') | s s' n C D.
  s' = insert (Asset n, PriKey D) s \<union>
    {Asset n, Spy} \<times> {\<lbrace>Num 4, PubKey D\<rbrace>} \<union>
    {Spy} \<times> Log ` {\<lbrace>Num 3, PubKey C\<rbrace>, \<lbrace>Num 4, PubKey D\<rbrace>} \<and>
  \<lbrace>Num 3, PubKey C\<rbrace> \<in> used s \<and>
  PriKey D \<notin> used s}"

abbreviation rel_owner_iv :: "(state \<times> state) set" where
"rel_owner_iv \<equiv> {(s, s') | s s' n S A B C D K SK.
  s' = insert (Owner n, SesKey SK) s \<union>
    {Owner n, Spy} \<times> {Crypt (SesK SK) (PubKey D)} \<union>
    {Spy} \<times> Log ` {\<lbrace>Num 4, PubKey D\<rbrace>, Crypt (SesK SK) (PubKey D)} \<and>
  {Crypt K (PriKey S), \<lbrace>Num 2, PubKey B\<rbrace>, \<lbrace>Num 4, PubKey D\<rbrace>} \<subseteq> used s \<and>
  {Owner n} \<times> {\<lbrace>Num 1, PubKey A\<rbrace>, \<lbrace>Num 3, PubKey C\<rbrace>} \<subseteq> s \<and>
  SK = (if K = Auth_ShaKey n then Some S else None, {A, B}, {C, D})}"

abbreviation rel_asset_iv :: "(state \<times> state) set" where
"rel_asset_iv \<equiv> {(s, s') | s s' n S A B C D SK.
  s' = s \<union> {Asset n} \<times> {SesKey SK, PubKey B} \<union>
    {Asset n, Spy} \<times> {Token n (Auth_PriK n) B C SK} \<union>
    {Spy} \<times> Log ` {Crypt (SesK SK) (PubKey D),
      Token n (Auth_PriK n) B C SK} \<and>
  {Asset n} \<times> {Crypt (Auth_ShaKey n) (PriKey S),
    \<lbrace>Num 2, PubKey B\<rbrace>, \<lbrace>Num 4, PubKey D\<rbrace>} \<subseteq> s \<and>
  {\<lbrace>Num 1, PubKey A\<rbrace>, \<lbrace>Num 3, PubKey C\<rbrace>,
    Crypt (SesK SK) (PubKey D)} \<subseteq> used s \<and>
  (Asset n, PubKey B) \<notin> s \<and>
  SK = (Some S, {A, B}, {C, D})}"

abbreviation rel_owner_v :: "(state \<times> state) set" where
"rel_owner_v \<equiv> {(s, s') | s s' n A B C SK.
  s' = s \<union> {Owner n, Spy} \<times> {Crypt (SesK SK) (Pwd n)} \<union>
    {Spy} \<times> Log ` {Token n A B C SK, Crypt (SesK SK) (Pwd n)} \<and>
  Token n A B C SK \<in> used s \<and>
  (Owner n, SesKey SK) \<in> s \<and>
  B \<in> fst (snd SK)}"

abbreviation rel_asset_v :: "(state \<times> state) set" where
"rel_asset_v \<equiv> {(s, s') | s s' n SK.
  s' = s \<union> {Asset n, Spy} \<times> {Crypt (SesK SK) (Num 0)} \<union>
    {Spy} \<times> Log ` {Crypt (SesK SK) (Pwd n), Crypt (SesK SK) (Num 0)} \<and>
  (Asset n, SesKey SK) \<in> s \<and>
  Crypt (SesK SK) (Pwd n) \<in> used s}"


abbreviation rel_prik :: "(state \<times> state) set" where
"rel_prik \<equiv> {(s, s') | s s' A.
  s' = insert (Spy, PriKey A) s \<and>
  PriKey A \<notin> used s}"

abbreviation rel_pubk :: "(state \<times> state) set" where
"rel_pubk \<equiv> {(s, s') | s s' A.
  s' = insert (Spy, PubKey A) s \<and>
  PriKey A \<in> spied s}"

abbreviation rel_sesk :: "(state \<times> state) set" where
"rel_sesk \<equiv> {(s, s') | s s' A B C D S.
  s' = insert (Spy, SesKey (Some S, {A, B}, {C, D})) s \<and>
  {PriKey S, PriKey A, PubKey B, PriKey C, PubKey D} \<subseteq> spied s}"

abbreviation rel_fact :: "(state \<times> state) set" where
"rel_fact \<equiv> {(s, s') | s s' A B.
  s' = s \<union> {Spy} \<times> {PriKey A, PriKey B} \<and>
  A \<otimes> B \<in> spied s \<and>
  (PriKey A \<in> spied s \<or> PriKey B \<in> spied s)}"

abbreviation rel_mult :: "(state \<times> state) set" where
"rel_mult \<equiv> {(s, s') | s s' A B.
  s' = insert (Spy, A \<otimes> B) s \<and>
  {PriKey A, PriKey B} \<subseteq> spied s}"

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
  {X, Key K} \<subseteq> spied s}"

abbreviation rel_sep :: "(state \<times> state) set" where
"rel_sep \<equiv> {(s, s') | s s' X Y.
  s' = s \<union> {Spy} \<times> {X, Y} \<and>
  \<lbrace>X, Y\<rbrace> \<in> spied s}"

abbreviation rel_con :: "(state \<times> state) set" where
"rel_con \<equiv> {(s, s') | s s' X Y.
  s' = insert (Spy, \<lbrace>X, Y\<rbrace>) s \<and>
  {X, Y} \<subseteq> spied s}"


abbreviation rel_id_agent :: "(state \<times> state) set" where
"rel_id_agent \<equiv> {(s, s') | s s' n.
  s' = insert (Spy, \<langle>n, Agent n\<rangle>) s \<and>
  Agent n \<in> spied s}"

abbreviation rel_id_invk :: "(state \<times> state) set" where
"rel_id_invk \<equiv> {(s, s') | s s' n K.
  s' = insert (Spy, \<langle>n, InvKey K\<rangle>) s \<and>
  {InvKey K, \<langle>n, Key K\<rangle>} \<subseteq> spied s}"

abbreviation rel_id_sesk :: "(state \<times> state) set" where
"rel_id_sesk \<equiv> {(s, s') | s s' n A SK X U.
  s' = s \<union> {Spy} \<times> {\<langle>n, PubKey A\<rangle>, \<langle>n, SesKey SK\<rangle>} \<and>
  {PubKey A, SesKey SK} \<subseteq> spied s \<and>
  (\<langle>n, PubKey A\<rangle> \<in> spied s \<or> \<langle>n, SesKey SK\<rangle> \<in> spied s) \<and>
  A \<in> seskey_set SK \<and>
  SesKey SK \<in> U \<and>
  U \<in> key_sets X (crypts (Log -` spied s))}"

abbreviation rel_id_fact :: "(state \<times> state) set" where
"rel_id_fact \<equiv> {(s, s') | s s' n A B.
  s' = s \<union> {Spy} \<times> {\<langle>n, PriKey A\<rangle>, \<langle>n, PriKey B\<rangle>} \<and>
  {PriKey A, PriKey B, \<langle>n, A \<otimes> B\<rangle>} \<subseteq> spied s}"

abbreviation rel_id_mult :: "(state \<times> state) set" where
"rel_id_mult \<equiv> {(s, s') | s s' n A B U.
  s' = insert (Spy, \<langle>n, A \<otimes> B\<rangle>) s \<and>
  U \<union> {PriKey A, PriKey B, A \<otimes> B} \<subseteq> spied s \<and>
  (\<langle>n, PriKey A\<rangle> \<in> spied s \<or> \<langle>n, PriKey B\<rangle> \<in> spied s) \<and>
  U \<in> key_sets (A \<otimes> B) (crypts (Log -` spied s))}"

abbreviation rel_id_hash :: "(state \<times> state) set" where
"rel_id_hash \<equiv> {(s, s') | s s' n X U.
  s' = s \<union> {Spy} \<times> {\<langle>n, X\<rangle>, \<langle>n, Hash X\<rangle>} \<and>
  U \<union> {X, Hash X} \<subseteq> spied s \<and>
  (\<langle>n, X\<rangle> \<in> spied s \<or> \<langle>n, Hash X\<rangle> \<in> spied s) \<and>
  U \<in> key_sets (Hash X) (crypts (Log -` spied s))}"

abbreviation rel_id_crypt :: "(state \<times> state) set" where
"rel_id_crypt \<equiv> {(s, s') | s s' n X U.
  s' = s \<union> {Spy} \<times> IDInfo n ` insert X U \<and>
  insert X U \<subseteq> spied s \<and>
  (\<langle>n, X\<rangle> \<in> spied s \<or> (\<exists>K \<in> U. \<langle>n, K\<rangle> \<in> spied s)) \<and>
  U \<in> key_sets X (crypts (Log -` spied s))}"

abbreviation rel_id_sep :: "(state \<times> state) set" where
"rel_id_sep \<equiv> {(s, s') | s s' n X Y.
  s' = s \<union> {Spy} \<times> {\<langle>n, X\<rangle>, \<langle>n, Y\<rangle>} \<and>
  {X, Y, \<langle>n, \<lbrace>X, Y\<rbrace>\<rangle>} \<subseteq> spied s}"

abbreviation rel_id_con :: "(state \<times> state) set" where
"rel_id_con \<equiv> {(s, s') | s s' n X Y U.
  s' = insert (Spy, \<langle>n, \<lbrace>X, Y\<rbrace>\<rangle>) s \<and>
  U \<union> {X, Y, \<lbrace>X, Y\<rbrace>} \<subseteq> spied s \<and>
  (\<langle>n, X\<rangle> \<in> spied s \<or> \<langle>n, Y\<rangle> \<in> spied s) \<and>
  U \<in> key_sets \<lbrace>X, Y\<rbrace> (crypts (Log -` spied s))}"


definition rel :: "(state \<times> state) set" where
"rel \<equiv> rel_asset_i \<union> rel_owner_ii \<union> rel_asset_ii \<union> rel_owner_iii \<union>
  rel_asset_iii \<union> rel_owner_iv \<union> rel_asset_iv \<union> rel_owner_v \<union> rel_asset_v \<union>
  rel_prik \<union> rel_pubk \<union> rel_sesk \<union> rel_fact \<union> rel_mult \<union> rel_hash \<union> rel_dec \<union>
  rel_enc \<union> rel_sep \<union> rel_con \<union> rel_id_agent \<union> rel_id_invk \<union> rel_id_sesk \<union>
  rel_id_fact \<union> rel_id_mult \<union> rel_id_hash \<union> rel_id_crypt \<union> rel_id_sep \<union> rel_id_con"

abbreviation in_rel :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 60) where
"s \<turnstile> s' \<equiv> (s, s') \<in> rel"

abbreviation in_rel_rtrancl :: "state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Turnstile>" 60) where
"s \<Turnstile> s' \<equiv> (s, s') \<in> rel\<^sup>*"


end