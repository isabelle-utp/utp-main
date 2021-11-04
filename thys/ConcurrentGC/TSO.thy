(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory TSO
imports
  Global_Invariants_Lemmas
  Local_Invariants_Lemmas
  Tactics
begin

(*>*)
section\<open> Coarse TSO invariants \<close>

context gc
begin

lemma tso_lock_invL[intro]:
  "\<lbrace> tso_lock_invL \<rbrace> gc"
by vcg_jackhammer

lemma tso_store_inv[intro]:
  "\<lbrace> LSTP tso_store_inv \<rbrace> gc"
unfolding tso_store_inv_def by vcg_jackhammer

lemma mut_tso_lock_invL[intro]:
  "\<lbrace> mut_m.tso_lock_invL m \<rbrace> gc"
by (vcg_chainsaw mut_m.tso_lock_invL_def)

end

context mut_m
begin

lemma tso_store_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP tso_store_inv \<rbrace> mutator m"
unfolding tso_store_inv_def by vcg_jackhammer

lemma gc_tso_lock_invL[intro]:
  "\<lbrace> gc.tso_lock_invL \<rbrace> mutator m"
by (vcg_chainsaw gc.tso_lock_invL_def)

lemma tso_lock_invL[intro]:
  "\<lbrace> tso_lock_invL \<rbrace> mutator m"
by vcg_jackhammer

end

context mut_m'
begin

lemma tso_lock_invL[intro]:
  "\<lbrace> tso_lock_invL \<rbrace> mutator m'"
by (vcg_chainsaw tso_lock_invL)

end

context sys
begin

lemma tso_gc_store_inv[intro]:
  notes fun_upd_apply[simp]
  shows
  "\<lbrace> LSTP tso_store_inv \<rbrace> sys"
apply (vcg_chainsaw tso_store_inv_def)
apply (metis (no_types) list.set_intros(2))
done

lemma gc_tso_lock_invL[intro]:
  "\<lbrace> gc.tso_lock_invL \<rbrace> sys"
by (vcg_chainsaw gc.tso_lock_invL_def)

lemma mut_tso_lock_invL[intro]:
  "\<lbrace> mut_m.tso_lock_invL m \<rbrace> sys"
by (vcg_chainsaw mut_m.tso_lock_invL_def)

end
(*<*)

end
(*>*)
