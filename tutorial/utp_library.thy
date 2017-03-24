section {* A simple library in the UTP theory of designs *}

theory utp_library
  imports "../theories/utp_theories"
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

subsection {* Library operations *}

definition InitLibrary :: "book set \<Rightarrow> library prog" where
[upred_defs]: "InitLibrary(bs) = true \<turnstile>\<^sub>n books, loans := \<guillemotleft>bs\<guillemotright>, {}\<^sub>u"

definition InitLibraryAlt :: "book set \<Rightarrow> library prog" where
[upred_defs]: "InitLibraryAlt(bs) = true \<turnstile>\<^sub>n ($books\<acute> =\<^sub>u \<guillemotleft>bs\<guillemotright> \<and> $loans\<acute> =\<^sub>u {}\<^sub>u)"

lemma InitLibrary_alt_same: "InitLibrary(bs) = InitLibraryAlt(bs)"
  by (rel_auto)

definition LibraryInvariant :: "library upred" where
[upred_defs]: "LibraryInvariant = (&loans \<subseteq>\<^sub>u &books)"

definition BorrowBook :: "book \<Rightarrow> library prog" where
[upred_defs]: "BorrowBook(b) = (\<guillemotleft>b\<guillemotright> \<notin>\<^sub>u &loans \<and> \<guillemotleft>b\<guillemotright> \<in>\<^sub>u &books) \<turnstile>\<^sub>n loans := &loans \<union>\<^sub>u {\<guillemotleft>b\<guillemotright>}\<^sub>u"

definition ReturnBook :: "book \<Rightarrow> library prog" where
[upred_defs]: "ReturnBook(b) = ((\<guillemotleft>b\<guillemotright> \<in>\<^sub>u &loans) \<turnstile>\<^sub>n (loans := &loans - {\<guillemotleft>b\<guillemotright>}\<^sub>u))"

subsection {* Library proofs *}

lemma InitLibrary_Idempotent: "InitLibrary(bs) ;; InitLibrary(bs) = InitLibrary(bs)"
  by (rel_blast)

lemma BorrowBook_Twice: "(BorrowBook(b) ;; BorrowBook(b)) = abort"
  by (rel_auto)

lemma ReturnBook_Twice: "(ReturnBook(b) ;; ReturnBook(b)) = abort"
  by (rel_auto)

abbreviation "Books \<equiv> {''War and Peace''
                       ,''Pride and Prejudice''
                       ,''Les Miserables''}"

lemma NotInLibrary:
  "(InitLibrary(Books) ;; BorrowBook(''Pride and Prejudice and Zombies'')) = abort"
  by (rel_auto)

theorem BorrowAndReturn:
  assumes "b \<in> bs"
  shows "(InitLibrary(bs) ;; BorrowBook(b) ;; ReturnBook(b)) = InitLibrary(bs)"
  using assms by (rel_blast)

lemma "InitLibrary(bs) establishes LibraryInvariant"
  by (rel_auto)

lemma "BorrowBook(b) maintains LibraryInvariant"
  by (rel_auto)

lemma "ReturnBook(b) maintains LibraryInvariant"
  by (rel_auto)
end