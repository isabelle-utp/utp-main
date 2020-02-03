theory factorial
  imports "UTP.utp"
begin

utp_lit_vars

alphabet sfact = x::nat y::nat

definition pfact :: "nat \<Rightarrow> sfact hrel" where
  "pfact X =
    x := X ;; y := 1 ;;
    while x > 1 invr y * fact(x) = fact(X)
    do y := y * x ;; x := x - 1 od"

lemma "TRY(id\<^sub>s \<Turnstile> pfact 4)"
  unfolding pfact_def
  apply (sym_eval) oops

lemma pfact_correct: "\<lbrace>true\<rbrace>pfact num\<lbrace>y = fact(\<guillemotleft>num\<guillemotright>)\<rbrace>\<^sub>u"
  unfolding pfact_def
  apply (hoare_auto)
  apply (metis diff_Suc_Suc diff_zero fact_diff_Suc less_SucI mult.assoc)
  apply (metis fact_0 fact_Suc_0 less_Suc0 linorder_neqE_nat mult.right_neutral)
  done


end