theory factorial
  imports "UTP.utp"
begin

alphabet fact_st =
  i :: nat
  result :: nat

abbreviation factorial :: "nat \<Rightarrow> fact_st hrel"  where
  "factorial num \<equiv> 
    result := 1 ;;
    i := \<guillemotleft>num\<guillemotright> ;;
    while (1 < i)
    invr result * fact(i) = fact(\<guillemotleft>num\<guillemotright>)
    do
      result := result * i ;;
      i := i - 1
    od"

lemma "\<lbrace>true\<rbrace>factorial num\<lbrace>result = fact(\<guillemotleft>num\<guillemotright>)\<rbrace>\<^sub>u"
  apply (hoare_auto)
  apply (simp add: fact_reduce)
  apply (metis fact_0 fact_Suc_0 less_Suc0 linorder_neqE_nat mult.right_neutral)
  done

end