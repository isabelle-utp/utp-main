theory max_list
  imports "UTP.utp_easy_parser"
begin

alphabet max_st =
  i :: nat
  result :: nat
  xs :: "nat list"

abbreviation maximum :: "nat list \<Rightarrow> max_st hrel"  where
  "maximum list \<equiv>
    xs := \<guillemotleft>list\<guillemotright> ;; 
    if (#xs = 0)
    then 
      result := 0
    else
      result := xs[0] ;;  
      i := 1 ;;
      while i < #xs
      invr xs = \<guillemotleft>list\<guillemotright> \<and> i > 0 \<and> result = Max(set(take(i, xs)))
      do
        if xs[i] > result
          then result := xs[i]  ;; i := i + 1
          else i := i + 1
        fi
      od
    fi"


lemma "TRY(id \<Turnstile> maximum [4,3,7,1,12,8])"
  apply (sym_eval)
  oops

lemma "list \<noteq> [] \<Longrightarrow> {{true}} maximum list {{result = Max(set(\<guillemotleft>list\<guillemotright>))}}"
  apply (hoare_auto)
    apply (auto simp add: take_Suc_conv_app_nth)
  oops

end