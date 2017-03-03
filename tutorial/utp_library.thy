section {* A simple library in the UTP theory of designs *}

theory utp_library
  imports "../utp/utp"
begin

subsection {* Preliminaries -- set up some syntax *}
  
notation true_upred ("abort")

definition establishes_inv :: "'a hrel_des \<Rightarrow> 'a upred \<Rightarrow> bool" (infixl "establishes" 85) where
[upred_defs]: "establishes_inv P iv \<equiv> true \<turnstile>\<^sub>r \<lceil>iv\<rceil>\<^sub>> \<sqsubseteq> P"
    
definition maintains_inv :: "'a hrel_des \<Rightarrow> 'a upred \<Rightarrow> bool" (infixl "maintains" 85) where
[upred_defs]: "maintains_inv P iv \<equiv> (pre\<^sub>D(P) \<and> \<lceil>iv\<rceil>\<^sub><) \<turnstile>\<^sub>r \<lceil>iv\<rceil>\<^sub>> \<sqsubseteq> P"
  
type_synonym 'a prog = "'a hrel_des"

subsection {* Library state space *}  

type_synonym book = string

alphabet library =
  books :: "book set"
  loans :: "book set"

abbreviation "Books \<equiv> {''War and Peace''
                       ,''Pride and Prejudice''
                       ,''Les Miserables''}"

subsection {* Library operations *}
  
definition InitLibrary :: "library prog" where
[upred_defs]: "InitLibrary = true \<turnstile>\<^sub>n books, loans := \<guillemotleft>Books\<guillemotright>, {}\<^sub>u"
  
definition InitLibraryAlt :: "library prog" where
[upred_defs]: "InitLibraryAlt = true \<turnstile>\<^sub>n ($books\<acute> =\<^sub>u \<guillemotleft>Books\<guillemotright> \<and> $loans\<acute> =\<^sub>u {}\<^sub>u)"

lemma InitLibrary_alt_same: "InitLibrary = InitLibraryAlt"
  by (rel_auto)

definition LibraryInvariant :: "library upred" where
[upred_defs]: "LibraryInvariant = (&loans \<subseteq>\<^sub>u &books)"

definition BorrowBook :: "book \<Rightarrow> library prog" where
[upred_defs]: "BorrowBook(b) = (\<guillemotleft>b\<guillemotright> \<notin>\<^sub>u &loans \<and> \<guillemotleft>b\<guillemotright> \<in>\<^sub>u &books) \<turnstile>\<^sub>n loans := &loans \<union>\<^sub>u {\<guillemotleft>b\<guillemotright>}\<^sub>u"

definition ReturnBook :: "book \<Rightarrow> library prog" where
[upred_defs]: "ReturnBook(b) = ((\<guillemotleft>b\<guillemotright> \<in>\<^sub>u &loans) \<turnstile>\<^sub>n (loans := &loans - {\<guillemotleft>b\<guillemotright>}\<^sub>u))"

subsection {* Library proofs *}

lemma InitLibrary_Idempotent: "InitLibrary ;; InitLibrary = InitLibrary"
  by (rel_blast)

lemma BorrowBook_Twice: "(BorrowBook(b) ;; BorrowBook(b)) = abort"
  by (rel_auto)

lemma ReturnBook_Twice: "(ReturnBook(b) ;; ReturnBook(b)) = abort"
  by (rel_auto)

lemma NotInLibrary:
  "(InitLibrary ;; BorrowBook(''Pride and Prejudice and Zombies'')) = abort"
  by (rel_auto)

text {*
  Simon, originally this proof went through with @{text "(rel_blast)"} alone
  but it took a lot of time (15 secs). I revised it to go through faster...
  In the future, I think it is good practice \emph{not} to leave proofs that
  take such a long time in the scripts as this causes a long delays when we
  building the system to validate merges, and we frequently have to do this.
  If you know the proof goes through, perhaps comment out the script as TODO
  and add the lemma as a sorry before committing to Github. Cheers, Frank.
*}

theorem BorrowAndReturn: 
  assumes "b \<in> Books"
  shows "(InitLibrary ;; BorrowBook(b) ;; ReturnBook(b)) = InitLibrary"
  using assms
  apply (rel_simp)
-- {* Give blast a little help... *}
  apply (case_tac "ok\<^sub>v")
  apply (simp_all)
  apply (blast)+
done

lemma "InitLibrary establishes LibraryInvariant"
  by (rel_auto)

lemma "BorrowBook(b) maintains LibraryInvariant"
  by (rel_auto)
    
lemma "ReturnBook(b) maintains LibraryInvariant"
  by (rel_auto)
end