subsection \<open>Interface for extending an order pair on lists\<close>

theory List_Order
  imports
    Knuth_Bendix_Order.Order_Pair
begin

type_synonym 'a list_ext = "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a list rel"

locale list_order_extension =
  fixes s_list :: "'a list_ext"
    and ns_list :: "'a list_ext"
  assumes extension: "SN_order_pair S NS \<Longrightarrow> SN_order_pair (s_list S NS) (ns_list S NS)"
    and s_map: "\<lbrakk>\<And> a b. (a,b) \<in> S \<Longrightarrow> (f a,f b) \<in> S; \<And> a b. (a,b) \<in> NS \<Longrightarrow> (f a,f b) \<in> NS\<rbrakk> \<Longrightarrow> (as,bs) \<in> s_list S NS \<Longrightarrow> (map f as, map f bs) \<in> s_list S NS" 
    and ns_map: "\<lbrakk>\<And> a b. (a,b) \<in> S \<Longrightarrow> (f a,f b) \<in> S; \<And> a b. (a,b) \<in> NS \<Longrightarrow> (f a,f b) \<in> NS\<rbrakk> \<Longrightarrow> (as,bs) \<in> ns_list S NS \<Longrightarrow> (map f as, map f bs) \<in> ns_list S NS" 
    and all_ns_imp_ns: "length as = length bs \<Longrightarrow> \<lbrakk>\<And> i. i < length bs \<Longrightarrow>  (as ! i, bs ! i) \<in> NS\<rbrakk> \<Longrightarrow> (as,bs) \<in> ns_list S NS"

type_synonym 'a list_ext_impl = "('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"

locale list_order_extension_impl = list_order_extension s_list ns_list for
  s_list ns_list :: "'a list_ext" +
  fixes list_ext :: "'a list_ext_impl"
  assumes list_ext_s: "\<And> s ns. s_list {(a,b). s a b} {(a,b). ns a b} = {(as,bs). fst (list_ext (\<lambda> a b. (s a b, ns a b)) as bs)}"
     and  list_ext_ns: "\<And> s ns. ns_list {(a,b). s a b} {(a,b). ns a b} = {(as,bs). snd (list_ext (\<lambda> a b. (s a b, ns a b)) as bs)}"
    and s_ext_local_mono: "\<And> s ns s' ns' as bs. (set as \<times> set bs) \<inter> ns \<subseteq> ns' \<Longrightarrow> (set as \<times> set bs) \<inter> s \<subseteq> s' \<Longrightarrow> (as,bs) \<in> s_list ns s \<Longrightarrow> (as,bs) \<in> s_list ns' s'"
    and ns_ext_local_mono: "\<And> s ns s' ns' as bs. (set as \<times> set bs) \<inter> ns \<subseteq> ns' \<Longrightarrow> (set as \<times> set bs) \<inter> s \<subseteq> s' \<Longrightarrow> (as,bs) \<in> ns_list ns s \<Longrightarrow> (as,bs) \<in> ns_list ns' s'"

end
