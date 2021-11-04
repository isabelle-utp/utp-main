(*
(C) Copyright Andreas Viktor Hess, DTU, 2020
(C) Copyright Sebastian A. Mödersheim, DTU, 2020
(C) Copyright Achim D. Brucker, University of Exeter, 2020
(C) Copyright Anders Schlichtkrull, DTU, 2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      Keyserver_Composition.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>The Composition of the Two Keyserver Protocols\<close>
theory Keyserver_Composition
  imports "../PSPSP"
begin

declare [[code_timing]]

trac\<open>
Protocol: kscomp

Types:
honest = {a,b,c}
dishonest = {i}
agent = honest ++ dishonest

Sets:
ring/1 valid/1 revoked/1 deleted/1
ring'/1 seen/1 pubkeys/0

Functions:
Public h/1 sign/2 crypt/2 scrypt/2 pair/2 update/3
Private inv/1 pw/1

Analysis:
sign(X,Y) -> Y
crypt(X,Y) ? inv(X) -> Y
scrypt(X,Y) ? X -> Y
pair(X,Y) -> X,Y
update(X,Y,Z) -> X,Y,Z

Transactions:
### The signature-based keyserver protocol
p1_outOfBand(A:honest)
  new PK
  insert PK ring(A)
* insert PK valid(A)
  send PK.

p1_oufOfBandD(A:dishonest)
  new PK
* insert PK valid(A)
  send PK
  send inv(PK).

p1_updateKey(A:honest,PK:value)
  PK in ring(A)
  new NPK
  delete PK ring(A)
  insert PK deleted(A)
  insert NPK ring(A)
  send sign(inv(PK),pair(A,NPK)).

p1_updateKeyServer(A:agent,PK:value,NPK:value)
  receive sign(inv(PK),pair(A,NPK))
* PK in valid(A)
* NPK notin valid(_)
  NPK notin revoked(_)
* delete PK valid(A)
  insert PK revoked(A)
* insert NPK valid(A)
  send inv(PK).

p1_authAttack(A:honest,PK:value)
  receive inv(PK)
* PK in valid(A)
  attack.

### The password-based keyserver protocol
p2_passwordGenD(A:dishonest)
  send pw(A).

p2_pubkeysGen()
  new PK
  insert PK pubkeys
  send PK.

p2_updateKeyPw(A:honest,PK:value)
  PK in pubkeys
  new NPK
# NOTE: The ring' sets are not used elsewhere, but we have to avoid that the fresh keys generated
#       by this rule are abstracted to the empty abstraction, and so we insert them into a ring'
#       set. Otherwise the two protocols would have too many abstractions in common (in particular,
#       the empty abstraction) which leads to false attacks in the composed protocol (probably
#       because the term implication graphs of the two protocols then become 'linked' through the
#       empty abstraction)
  insert NPK ring'(A)
  send NPK
  send crypt(PK,update(A,NPK,pw(A))).

#Transactions of p2:
p2_updateKeyServerPw(A:agent,PK:value,NPK:value)
receive crypt(PK,update(A,NPK,pw(A)))
  PK in pubkeys
  NPK notin pubkeys
  NPK notin seen(_)
* insert NPK valid(A)
  insert NPK seen(A).

p2_authAttack2(A:honest,PK:value)
  receive inv(PK)
* PK in valid(A)
  attack.
\<close> \<open>
sign(inv(val(deleted(A))),pair(A,val(ring(A)))) where A:honest
sign(inv(val(deleted(A),valid(B))),pair(A,val(ring(A)))) where A:honest B:dishonest
sign(inv(val(deleted(A),seen(B),valid(B))),pair(A,val(ring(A)))) where A:honest B:dishonest
sign(inv(val(deleted(A),valid(A))),pair(A,val(ring(A)))) where A:honest B:dishonest
sign(inv(val(deleted(A),seen(B),valid(B),valid(A))),pair(A,val(ring(A)))) where A:honest B:dishonest
pair(A,val(ring(A))) where A:honest
inv(val(deleted(A),revoked(A))) where A:honest
inv(val(valid(A))) where A:dishonest
inv(val(revoked(A))) where A:dishonest
inv(val(revoked(A),seen(A))) where A:dishonest
inv(val(revoked(B),seen(B),revoked(A),deleted(A))) where A:honest B:dishonest
inv(val(revoked(A),deleted(A),seen(B),valid(B))) where A:honest B:dishonest
occurs(val(ring(A))) where A:honest
occurs(val(valid(A))) where A:dishonest
occurs(val(ring'(A))) where A:honest
occurs(val(pubkeys))
occurs(val(valid(A),ring(A))) where A:honest
pw(A) where A:dishonest
crypt(val(pubkeys),update(A,val(ring'(A)),pw(A))) where A:honest
val(ring(A)) where A:honest
val(valid(A)) where A:dishonest
val(ring'(A)) where A:honest
val(pubkeys)
val(valid(A),ring(A)) where A:honest

timplies(val(pubkeys),val(valid(A),pubkeys)) where A:dishonest

timplies(val(ring'(A)),val(ring'(A),valid(B))) where A:honest B:dishonest
timplies(val(ring'(A)),val(ring'(A),valid(A),seen(A))) where A:honest
timplies(val(ring'(A)),val(ring'(A),valid(A),seen(A),valid(B))) where A:honest B:dishonest
timplies(val(ring'(A)),val(seen(B),valid(B),ring'(A))) where A:honest B:dishonest

timplies(val(ring'(A),valid(B)),val(ring'(A),valid(A),seen(A),valid(B))) where A:honest B:dishonest
timplies(val(ring'(A),valid(B)),val(seen(B),valid(B),ring'(A))) where A:honest B:dishonest

timplies(val(ring(A)),val(ring(A),valid(A))) where A:honest
timplies(val(ring(A)),val(ring(A),valid(B))) where A:honest B:dishonest
timplies(val(ring(A)),val(deleted(A))) where A:honest
timplies(val(ring(A)),val(revoked(A),deleted(A),seen(B),valid(B))) where A:honest B:dishonest
timplies(val(ring(A)),val(revoked(A),deleted(A),seen(B),revoked(B))) where A:honest B:dishonest
timplies(val(ring(A)),val(deleted(A),seen(B),valid(B))) where A:honest B:dishonest
timplies(val(ring(A)),val(ring(A),seen(B),valid(B))) where A:honest B:dishonest
timplies(val(ring(A)),val(valid(A),deleted(A),seen(B),valid(B))) where A:honest B:dishonest
timplies(val(ring(A)),val(valid(A),ring(A),seen(B),valid(B))) where A:honest B:dishonest

timplies(val(ring(A),valid(A)),val(deleted(A),valid(A))) where A:honest
timplies(val(ring(A),valid(B)),val(deleted(A),valid(B))) where A:honest B:dishonest
timplies(val(ring(A),valid(A)),val(deleted(A),revoked(A))) where A:honest

timplies(val(deleted(A)),val(deleted(A),valid(A))) where A:honest
timplies(val(deleted(A)),val(deleted(A),valid(B))) where A:honest B:dishonest
timplies(val(deleted(A)),val(revoked(A),seen(B),valid(B),deleted(A))) where A:honest B:dishonest
timplies(val(deleted(A)),val(revoked(B),seen(B),revoked(A),deleted(A))) where A:honest B:dishonest
timplies(val(deleted(A)),val(seen(B),valid(B),deleted(A))) where A:honest B:dishonest
timplies(val(deleted(A)),val(seen(B),valid(B),valid(A),deleted(A))) where A:honest B:dishonest

timplies(val(revoked(A)),val(seen(A),revoked(A))) where A:dishonest
timplies(val(revoked(A)),val(seen(A),revoked(A),valid(A))) where A:dishonest

timplies(val(revoked(A),deleted(A)),val(revoked(B),seen(B),revoked(A),deleted(A))) where A:honest B:dishonest
timplies(val(revoked(A),deleted(A)),val(seen(B),valid(B),revoked(A),deleted(A))) where A:honest B:dishonest

timplies(val(seen(B),valid(B),deleted(A),valid(A)),val(revoked(A),seen(B),valid(B),deleted(A))) where A:honest B:dishonest
timplies(val(seen(B),valid(B),deleted(A),valid(A)),val(revoked(B),seen(B),revoked(A),deleted(A))) where A:honest B:dishonest
timplies(val(seen(B),valid(B),revoked(A),deleted(A)),val(revoked(B),seen(B),revoked(A),deleted(A))) where A:honest B:dishonest
timplies(val(seen(A),valid(A)),val(revoked(A),seen(A))) where A:dishonest
timplies(val(seen(A),valid(A),revoked(A)),val(seen(A),revoked(A))) where A:dishonest
timplies(val(seen(B),valid(B),ring(A)),val(deleted(A),seen(B),valid(B))) where A:honest B:dishonest
timplies(val(seen(B),valid(B),valid(A),ring(A)),val(deleted(A),seen(B),valid(B),valid(A))) where A:honest B:dishonest
timplies(val(seen(B),valid(B),valid(A),ring(A)),val(revoked(A),seen(B),valid(B),deleted(A))) where A:honest B:dishonest
timplies(val(seen(B),valid(B),valid(A),ring(A)),val(revoked(B),seen(B),revoked(A),deleted(A))) where A:honest B:dishonest

timplies(val(valid(A)),val(revoked(A))) where A:dishonest

timplies(val(valid(A),deleted(A)),val(deleted(A),revoked(A))) where A:honest
timplies(val(valid(A),deleted(A)),val(revoked(A),seen(B),valid(B),deleted(A))) where A:honest B:dishonest
timplies(val(valid(A),deleted(A)),val(revoked(B),seen(B),revoked(A),deleted(A))) where A:honest B:dishonest
timplies(val(valid(A),deleted(A)),val(seen(B),valid(B),valid(A),deleted(A))) where A:honest B:dishonest

timplies(val(ring(A),valid(A)),val(deleted(A),seen(B),valid(B),valid(A))) where A:honest B:dishonest
timplies(val(ring(A),valid(A)),val(revoked(B),seen(B),revoked(A),deleted(A))) where A:honest B:dishonest
timplies(val(ring(A),valid(A)),val(seen(B),valid(B),valid(A),ring(A))) where A:honest B:dishonest
timplies(val(valid(B),deleted(A)),val(seen(B),valid(B),deleted(A))) where A:honest B:dishonest
timplies(val(ring(A),valid(B)),val(deleted(A),seen(B),valid(B))) where A:honest B:dishonest
timplies(val(ring(A),valid(B)),val(seen(B),valid(B),ring(A))) where A:honest B:dishonest

timplies(val(valid(A)),val(seen(A),valid(A))) where A:dishonest
\<close>

subsection \<open>Proof: The composition of the two keyserver protocols is secure\<close>
protocol_model_setup spm: kscomp
setup_protocol_checks spm kscomp_protocol
manual_protocol_security_proof ssp: kscomp
  apply check_protocol_intro
  subgoal by code_simp
  subgoal
    apply coverage_check_intro
    subgoal by code_simp
    subgoal by code_simp
    subgoal by eval
    subgoal by eval
    subgoal by eval
    subgoal by code_simp
    subgoal by code_simp
    subgoal by eval
    subgoal by eval
    subgoal by eval
    done
  subgoal by eval
  subgoal by eval
  subgoal
    apply (unfold spm.wellformed_fixpoint_def Let_def case_prod_unfold; intro conjI)
    subgoal by code_simp
    subgoal by code_simp
    subgoal by eval
    subgoal by code_simp
    subgoal by code_simp
    done
  done


subsection \<open>The generated theorems and definitions\<close>
thm ssp.protocol_secure

thm kscomp_enum_consts.nchotomy
thm kscomp_sets.nchotomy
thm kscomp_fun.nchotomy
thm kscomp_atom.nchotomy
thm kscomp_arity.simps
thm kscomp_public.simps
thm kscomp_\<Gamma>.simps
thm kscomp_Ana.simps

thm kscomp_transaction_p1_outOfBand_def
thm kscomp_transaction_p1_oufOfBandD_def
thm kscomp_transaction_p1_updateKey_def
thm kscomp_transaction_p1_updateKeyServer_def
thm kscomp_transaction_p1_authAttack_def
thm kscomp_transaction_p2_passwordGenD_def
thm kscomp_transaction_p2_pubkeysGen_def
thm kscomp_transaction_p2_updateKeyPw_def
thm kscomp_transaction_p2_updateKeyServerPw_def
thm kscomp_transaction_p2_authAttack2_def
thm kscomp_protocol_def

thm kscomp_fixpoint_def

end
