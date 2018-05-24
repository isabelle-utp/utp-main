section \<open> Asynchronous Channels \<close>

theory AsyncChannel
  imports Actions
begin

definition async_channel :: "('a \<Rightarrow> 'e) \<Rightarrow> ('a \<Rightarrow> 'e) \<Rightarrow> 'e Process" ("_ \<midarrow>c\<rightarrow> _" [85,86] 85) where
"async_channel efrom eto =
   (decl (isEmpty :: bool, buf :: 'a) \<bullet>
      isEmpty := true ;
      do &isEmpty \<rightarrow> efrom\<^bold>?(buf) ; isEmpty := false
       | (\<not> &isEmpty) \<rightarrow> efrom\<^bold>?(buf) \<box> (eto\<^bold>!(&buf) ; isEmpty := true)
      od)"

end