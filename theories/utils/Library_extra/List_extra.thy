theory List_extra
  imports Main
begin

text {*
The following variant of the standard @{text nth} function returns
@{text "\<bottom>"} if the index is out of range.
*}

primrec
  nth_el :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" ("_\<langle>_\<rangle>" [90, 0] 91)
where
  "[]\<langle>i\<rangle> = None"
| "(x # xs)\<langle>i\<rangle> = (case i of 0 \<Rightarrow> Some x | Suc j \<Rightarrow> xs \<langle>j\<rangle>)"


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

end
