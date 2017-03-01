theory utp_library
  imports "../utp/utp"
begin
  
type_synonym book = string
  
alphabet library =
  books :: "book set"
  loans :: "book set"
  
abbreviation "Books \<equiv> {''War and Peace'', ''Pride and Prejudice'', ''Les Miserables''}"
  
definition InitLibrary :: "library hrel_des" where
[upred_defs]: "InitLibrary = true \<turnstile>\<^sub>n ($books\<acute> =\<^sub>u \<guillemotleft>Books\<guillemotright> \<and> $loans\<acute> =\<^sub>u {}\<^sub>u)"

definition InitLibrary' :: "library hrel_des" where
[upred_defs]: "InitLibrary' = true \<turnstile>\<^sub>n (books, loans := \<guillemotleft>Books\<guillemotright>, {}\<^sub>u)"

definition Library_inv :: "library upred" where
"Library_inv = (&loans \<subseteq>\<^sub>u &books)"

definition BorrowBook :: "book \<Rightarrow> library hrel_des" where
[upred_defs]: "BorrowBook(b)  = ((\<guillemotleft>b\<guillemotright> \<notin>\<^sub>u &loans \<and> \<guillemotleft>b\<guillemotright> \<in>\<^sub>u &books) \<turnstile>\<^sub>n ($loans\<acute> =\<^sub>u $loans \<union>\<^sub>u {\<guillemotleft>b\<guillemotright>}\<^sub>u \<and> $books\<acute> =\<^sub>u $books))"

definition ReturnBook :: "book \<Rightarrow> library hrel_des" where
[upred_defs]: "ReturnBook(b)  = ((\<guillemotleft>b\<guillemotright> \<in>\<^sub>u &loans) \<turnstile>\<^sub>n ($loans\<acute> =\<^sub>u $loans - {\<guillemotleft>b\<guillemotright>}\<^sub>u \<and> $books\<acute> =\<^sub>u $books))"

definition BorrowBook' :: "book \<Rightarrow> library hrel_des" where
[upred_defs]: "BorrowBook'(b)  = ((\<guillemotleft>b\<guillemotright> \<notin>\<^sub>u &loans \<and> \<guillemotleft>b\<guillemotright> \<in>\<^sub>u &books) \<turnstile>\<^sub>n loans := &loans \<union>\<^sub>u {\<guillemotleft>b\<guillemotright>}\<^sub>u)"

definition ReturnBook' :: "book \<Rightarrow> library hrel_des" where
[upred_defs]: "ReturnBook'(b)  = ((\<guillemotleft>b\<guillemotright> \<in>\<^sub>u &loans) \<turnstile>\<^sub>n (loans := &loans - {\<guillemotleft>b\<guillemotright>}\<^sub>u))"

lemma "InitLibrary ;; InitLibrary = InitLibrary"
  by (fast_rel_blast)

lemma "BorrowBook(b) = BorrowBook'(b)"
  by (fast_rel_auto)
    
lemma "ReturnBook(b) = ReturnBook'(b)"
  by (fast_rel_auto)

lemma BorrowBook_twice: "(BorrowBook(b) ;; BorrowBook(b)) = \<bottom>\<^sub>D"
  by (fast_rel_auto)
    
lemma [simp]: 
  "{}\<^sub>u \<union>\<^sub>u A = A" "A - A = {}\<^sub>u" "x \<in>\<^sub>u {x}\<^sub>u = true" "x \<notin>\<^sub>u {}\<^sub>u = true"
  by (pred_auto)+
    
lemma BorrowAndReturn: 
  assumes "b \<in> Books"
  shows "(InitLibrary' ;; BorrowBook'(b) ;; ReturnBook'(b)) = InitLibrary'"
  using assms
  apply (fast_rel_auto)
  apply blast
(*
  apply (rule wpd_H3_eq_intro)
  apply (simp_all add: InitLibrary'_def BorrowBook'_def ReturnBook'_def closure)
  apply (simp add: wp closure usubst)
  apply literalise
  apply (metis (full_types) assms true_alt_def utp_pred.inf_top_left)
*)
oops
    
lemma NotInLibrary:
  "(InitLibrary ;; BorrowBook(''Pride and Prejudice and Zombies'')) = \<bottom>\<^sub>D"
  by (fast_rel_auto)
  
end