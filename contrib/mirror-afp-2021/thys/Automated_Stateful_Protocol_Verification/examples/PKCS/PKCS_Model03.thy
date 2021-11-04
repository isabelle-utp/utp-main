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

(*  Title:      PKCS_Model03.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>The PKCS Model, Scenario 3\<close>
theory PKCS_Model03
  imports "../../PSPSP"

begin

declare [[code_timing]]

trac\<open>
Protocol: ATTACK_UNSET

Types: 
token   = {token1}

Sets:
extract/1 wrap/1 decrypt/1 sensitive/1

Functions:
Public  senc/2 h/1 
Private inv/1

Analysis:
senc(M,K2) ? K2 -> M  #This analysis rule corresponds to the decrypt2 rule in the AIF-omega specification.
                      #M was type untyped

Transactions:

iik1()
new K1
insert K1 sensitive(token1)
insert K1 extract(token1)
send h(K1).

iik2()
new K2
insert K2 wrap(token1)
send h(K2).

# ======================wrap================
wrap(K1:value,K2:value)
receive h(K1)
receive h(K2)
K1 in extract(token1)
K2 in wrap(token1)
send senc(K1,K2).

# ======================set wrap================
setwrap(K2:value)
receive h(K2)
K2 notin decrypt(token1)
insert K2 wrap(token1).

# ======================set decrypt================
setdecrypt(K2:value)
receive h(K2)
K2 notin wrap(token1)
insert K2 decrypt(token1).

# ======================decrypt================
decrypt1(K2:value,M:value)  #M was untyped in the AIF-omega specification.
receive h(K2)
receive senc(M,K2)
K2 in decrypt(token1)
send M.

# ======================attacks================
attack1(K1:value)
receive K1
K1 in sensitive(token1)
attack.
\<close>

subsection \<open>Protocol model setup\<close>
protocol_model_setup spm: ATTACK_UNSET

subsection \<open>Fixpoint computation\<close>
compute_fixpoint ATTACK_UNSET_protocol ATTACK_UNSET_fixpoint
compute_SMP [optimized] ATTACK_UNSET_protocol ATTACK_UNSET_SMP

subsection \<open>Proof of security\<close>
manual_protocol_security_proof ssp: ATTACK_UNSET
  for ATTACK_UNSET_protocol ATTACK_UNSET_fixpoint ATTACK_UNSET_SMP
  apply check_protocol_intro
  subgoal by code_simp
  subgoal by code_simp
  subgoal by code_simp
  subgoal by code_simp
  subgoal by code_simp
  done


subsection \<open>The generated theorems and definitions\<close>
thm ssp.protocol_secure

thm ATTACK_UNSET_enum_consts.nchotomy
thm ATTACK_UNSET_sets.nchotomy
thm ATTACK_UNSET_fun.nchotomy
thm ATTACK_UNSET_atom.nchotomy
thm ATTACK_UNSET_arity.simps
thm ATTACK_UNSET_public.simps
thm ATTACK_UNSET_\<Gamma>.simps
thm ATTACK_UNSET_Ana.simps

thm ATTACK_UNSET_transaction_iik1_def
thm ATTACK_UNSET_transaction_iik2_def 
thm ATTACK_UNSET_transaction_wrap_def
thm ATTACK_UNSET_transaction_setwrap_def
thm ATTACK_UNSET_transaction_setdecrypt_def
thm ATTACK_UNSET_transaction_decrypt1_def
thm ATTACK_UNSET_transaction_attack1_def

thm ATTACK_UNSET_protocol_def

thm ATTACK_UNSET_fixpoint_def
thm ATTACK_UNSET_SMP_def

end
