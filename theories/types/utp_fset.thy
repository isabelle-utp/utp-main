(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_fset.thy                                                         *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* UTP Finite Sets *}

theory utp_fset
imports 
  "../core/utp_value"
  "../core/utp_sorts"
  "../core/utp_event"
  "../tactics/utp_pred_tac"
  "../tactics/utp_expr_tac"
begin

typedef 'a::DEFINED UFSET = "{xs :: 'a fset. \<forall>x\<in>\<^sub>fxs. \<D> x}"
  apply (rule_tac x="\<lbrace>\<rbrace>" in exI)
  apply (auto)
done

instantiation UFSET :: (DEFINED) DEFINED
begin
definition "Defined_UFSET (xs :: 'a UFSET) = True"
instance ..
end

lemma Defined_UFSET [defined]: 
  "\<D> (xs :: ('a::DEFINED UFSET))"
  by (simp add:Defined_UFSET_def)

end