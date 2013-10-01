(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: List_extra.thy                                                       *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* Extra list functions and lemmas *}

theory List_extra
  imports 
    Main 
    Monad_Syntax
    Sublist
begin

subsection {* List functions *}

text {*
The following variant of the standard @{text nth} function returns
@{text "\<bottom>"} if the index is out of range.
*}

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" ("_\<langle>_\<rangle>" [90, 0] 91)
where
  "[]\<langle>i\<rangle> = None"
| "(x # xs)\<langle>i\<rangle> = (case i of 0 \<Rightarrow> Some x | Suc j \<Rightarrow> xs \<langle>j\<rangle>)"

fun sequence :: "'a option list \<Rightarrow> 'a list option" where
"sequence [] = Some []" |
"sequence (f # fs) = do { x \<leftarrow> f; xs \<leftarrow> sequence fs; Some (x # xs) }"

abbreviation "mapM f \<equiv> sequence \<circ> map f"

subsection {* List lemmas *}

lemma nth_el_appendl[simp]: "i < length xs \<Longrightarrow> (xs @ ys)\<langle>i\<rangle> = xs\<langle>i\<rangle>"
  apply (induct xs arbitrary: i)
  apply simp
  apply (case_tac i)
  apply simp_all
done

lemma nth_el_appendr[simp]: "length xs \<le> i \<Longrightarrow> (xs @ ys)\<langle>i\<rangle> = ys\<langle>i - length xs\<rangle>"
  apply (induct xs arbitrary: i)
  apply simp
  apply (case_tac i)
  apply simp_all
done

lemma sorted_last [simp]: "\<lbrakk> x \<in> set xs; sorted xs \<rbrakk> \<Longrightarrow> x \<le> last xs"
  apply (induct xs)
  apply (auto)
  apply (metis last_in_set sorted_Cons)+
done

lemma prefix_length_eq:
  "\<lbrakk> length xs = length ys; prefixeq xs ys \<rbrakk> \<Longrightarrow> xs = ys"
  by (metis not_equal_is_parallel parallel_def)

fun interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
"interleave [] ys = {ys}" |
"interleave (x # xs) (y # ys) = (Cons x) ` (interleave xs (y # ys)) 
                              \<union> (Cons y) ` (interleave (x # xs) ys)" |
"interleave xs [] = {xs}"

lemma interleave_finite [simp]:
  "finite (interleave xs ys)"
  apply (induct xs arbitrary: ys)
  apply (simp)
  apply (induct_tac ys)
  apply (auto)
done

lemma interleave_right_nil [simp]:
  "interleave xs [] = {xs}"
  by (induct xs, auto)

lemma interleave_headE [elim!]:
  "\<lbrakk> z # zs \<in> interleave xs ys
   ; \<And> xs'. xs = z # xs' \<Longrightarrow> P
   ; \<And> ys'. ys = z # ys' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (induct xs)
  apply (auto)
  apply (induct ys)
  apply (auto)
done

lemma interleave_member:
  "\<lbrakk> zs \<in> interleave xs ys; z \<in> set zs \<rbrakk> \<Longrightarrow> z \<in> set xs \<or> z \<in> set ys"
  apply (induct xs arbitrary: zs)
  apply (auto)
  apply (induct ys)
  apply (auto)
oops

(* FIXME: What happens if no progress can be made? *)
fun intersync :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" where
"intersync s (x # xs) (y # ys) 
  = (case (x = y , x \<in> s , y \<in> s) of
          (True  , True   , _      ) \<Rightarrow> Cons x ` intersync s xs ys |
          (True  , False  , _      ) \<Rightarrow> ((Cons x ` intersync s xs (y # ys))
                                         \<union> (Cons y ` intersync s (x # xs) ys)) |
          (False , True   , True   ) \<Rightarrow> {[]} |
          (False , True   , False  ) \<Rightarrow> Cons y ` intersync s (x # xs) ys |
          (False , False  , True   ) \<Rightarrow> Cons x ` intersync s xs (y # ys) |
          (False , False  , False  ) \<Rightarrow> ((Cons x ` intersync s xs (y # ys))
                                         \<union> (Cons y ` intersync s (x # xs) ys)))" |
"intersync s [] (y # ys) = 
   (if (y \<in> s) then {[]} else Cons y ` intersync s [] ys)" |
"intersync s (x # xs) [] = 
   (if (x \<in> s) then {[]} else Cons x ` intersync s xs [])" |
"intersync s [] [] = {[]}"

(* FIXME: We should be able to prove this property... *)
lemma intersync_empty_interleave:
  "intersync {} xs ys = interleave xs ys"
  apply (induct xs)
  apply (simp_all)
  apply (induct ys)
  apply (simp_all)
  apply (induct ys arbitrary: a xs)
  apply (simp_all)
  apply (case_tac "aa = a")
  apply (simp_all)
oops

end
