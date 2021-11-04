section \<open>Executability of the orders\<close>
theory Executable_Orders
  imports 
    WPO
    RPO
    LPO
    Multiset_Extension2_Impl
begin

text \<open>If one loads the implementation of multiset orders (in particular for @{const mul_ext}), 
  then all orders defined in this AFP-entry (WPO, RPO, LPO, multiset extension of order pairs) are executable.\<close>

export_code 
  lpo
  rpo 
  wpo.wpo 
  mul_ext 
  mult2_impl 
  in Haskell 

end