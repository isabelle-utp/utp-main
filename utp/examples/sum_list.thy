section \<open> Summing a List \<close>

theory sum_list
  imports "UTP.utp"
begin

text \<open> We first create a state space with the variables the program needs. \<close>

alphabet st_sum_list = 
  i   :: nat
  xs  :: "int list"
  ans :: int

text \<open> Next, we define the program as by a homogeneous relation over the state-space type. \<close>

abbreviation Sum_List :: "st_sum_list hrel" where
  "Sum_List \<equiv>
  i := 0 ;;
  ans := 0 ;;
  while (i < length xs) invr (ans = list_sum(take i xs))
  do
    ans := ans + xs ! i ;;
    i := i + 1
  od"

text \<open> Next, we symbolically evaluate some examples. \<close>

lemma "TRY([&xs \<mapsto>\<^sub>s \<guillemotleft>[4,3,7,1,12,8]\<guillemotright>] \<Turnstile> Sum_List)"
  apply (sym_eval) oops

text \<open> Finally, we verify the program. \<close>

theorem Sum_List_sums:
  "\<lbrace>xs = \<guillemotleft>XS\<guillemotright>\<rbrace> Sum_List \<lbrace>ans = list_sum(xs)\<rbrace>\<^sub>u"
  by (hoare_auto, metis add.foldr_snoc take_Suc_conv_app_nth)

end