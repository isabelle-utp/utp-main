(*  Title:      JinjaDCI/Common/Auxiliary.thy

    Author:     David von Oheimb, Tobias Nipkow, Susannah Mansky
    Copyright   1999 TU Muenchen, 2019-20 UIUC

    Based on the Jinja theory Common/Auxiliary.thy by David von Oheimb and Tobias Nipkow
*)

chapter \<open> Jinja Source Language \label{cha:j} \<close>

section \<open> Auxiliary Definitions \<close>

theory Auxiliary imports Main begin
(* FIXME move and possibly turn into a general simproc *)
lemma nat_add_max_le[simp]:
  "((n::nat) + max i j \<le> m) = (n + i \<le> m \<and> n + j \<le> m)"
 (*<*)by arith(*>*)

lemma Suc_add_max_le[simp]:
  "(Suc(n + max i j) \<le> m) = (Suc(n + i) \<le> m \<and> Suc(n + j) \<le> m)"
(*<*)by arith(*>*)


notation Some  ("(\<lfloor>_\<rfloor>)")

(*<*)
declare
 option.splits[split]
 Let_def[simp]
 subset_insertI2 [simp]
 Cons_eq_map_conv [iff]
(*>*)


subsection \<open>@{text distinct_fst}\<close>
 
definition distinct_fst  :: "('a \<times> 'b) list \<Rightarrow> bool"
where
  "distinct_fst  \<equiv>  distinct \<circ> map fst"

lemma distinct_fst_Nil [simp]:
  "distinct_fst []"
 (*<*)
by (unfold distinct_fst_def) (simp (no_asm))
(*>*)

lemma distinct_fst_Cons [simp]:
  "distinct_fst ((k,x)#kxs) = (distinct_fst kxs \<and> (\<forall>y. (k,y) \<notin> set kxs))"
(*<*)
by (unfold distinct_fst_def) (auto simp:image_def)
(*>*)

lemma distinct_fst_appendD:
 "distinct_fst(kxs @ kxs') \<Longrightarrow> distinct_fst kxs \<and> distinct_fst kxs'"
(*<*)by(induct kxs, auto)(*>*)

lemma map_of_SomeI:
  "\<lbrakk> distinct_fst kxs; (k,x) \<in> set kxs \<rbrakk> \<Longrightarrow> map_of kxs k = Some x"
(*<*)by (induct kxs) (auto simp:fun_upd_apply)(*>*)


subsection \<open> Using @{term list_all2} for relations \<close>

definition fun_of :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  "fun_of S \<equiv> \<lambda>x y. (x,y) \<in> S"

text \<open> Convenience lemmas \<close>
(*<*)
declare fun_of_def [simp]
(*>*)
lemma rel_list_all2_Cons [iff]:
  "list_all2 (fun_of S) (x#xs) (y#ys) = 
   ((x,y) \<in> S \<and> list_all2 (fun_of S) xs ys)"
  (*<*)by simp(*>*)

lemma rel_list_all2_Cons1:
  "list_all2 (fun_of S) (x#xs) ys = 
  (\<exists>z zs. ys = z#zs \<and> (x,z) \<in> S \<and> list_all2 (fun_of S) xs zs)"
  (*<*)by (cases ys) auto(*>*)

lemma rel_list_all2_Cons2:
  "list_all2 (fun_of S) xs (y#ys) = 
  (\<exists>z zs. xs = z#zs \<and> (z,y) \<in> S \<and> list_all2 (fun_of S) zs ys)"
  (*<*)by (cases xs) auto(*>*)

lemma rel_list_all2_refl:
  "(\<And>x. (x,x) \<in> S) \<Longrightarrow> list_all2 (fun_of S) xs xs"
  (*<*)by (simp add: list_all2_refl)(*>*)

lemma rel_list_all2_antisym:
  "\<lbrakk> (\<And>x y. \<lbrakk>(x,y) \<in> S; (y,x) \<in> T\<rbrakk> \<Longrightarrow> x = y); 
     list_all2 (fun_of S) xs ys; list_all2 (fun_of T) ys xs \<rbrakk> \<Longrightarrow> xs = ys"
  (*<*)by (rule list_all2_antisym) auto(*>*)

lemma rel_list_all2_trans: 
  "\<lbrakk> \<And>a b c. \<lbrakk>(a,b) \<in> R; (b,c) \<in> S\<rbrakk> \<Longrightarrow> (a,c) \<in> T;
    list_all2 (fun_of R) as bs; list_all2 (fun_of S) bs cs\<rbrakk> 
  \<Longrightarrow> list_all2 (fun_of T) as cs"
  (*<*)by (rule list_all2_trans) auto(*>*)

lemma rel_list_all2_update_cong:
  "\<lbrakk> i<size xs; list_all2 (fun_of S) xs ys; (x,y) \<in> S \<rbrakk> 
  \<Longrightarrow> list_all2 (fun_of S) (xs[i:=x]) (ys[i:=y])"
  (*<*)by (simp add: list_all2_update_cong)(*>*)

lemma rel_list_all2_nthD:
  "\<lbrakk> list_all2 (fun_of S) xs ys; p < size xs \<rbrakk> \<Longrightarrow> (xs!p,ys!p) \<in> S"
  (*<*)by (drule list_all2_nthD) auto(*>*)

lemma rel_list_all2I:
  "\<lbrakk> length a = length b; \<And>n. n < length a \<Longrightarrow> (a!n,b!n) \<in> S \<rbrakk> \<Longrightarrow> list_all2 (fun_of S) a b"
  (*<*)by (erule list_all2_all_nthI) simp(*>*)

(*<*)declare fun_of_def [simp del](*>*)

subsection \<open> Auxiliary properties of @{text "map_of"} function \<close>

lemma map_of_set_pcs_notin: "C \<notin> (\<lambda>t. snd (fst t)) ` set FDTs \<Longrightarrow> map_of FDTs (F, C) = None"
(*<*)by (metis image_eqI image_image map_of_eq_None_iff snd_conv)(*>*)

lemma map_of_insertmap_SomeD':
  "map_of fs F = Some y \<Longrightarrow> map_of (map (\<lambda>(F, y). (F, D, y)) fs) F = Some(D,y)"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)

lemma map_of_reinsert_neq_None:
  "Ca \<noteq> D \<Longrightarrow> map_of (map (\<lambda>(F, y). ((F, Ca), y)) fs) (F, D) = None"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)

lemma map_of_remap_insertmap:
  "map_of (map ((\<lambda>((F, D), b, T). (F, D, b, T)) \<circ> (\<lambda>(F, y). ((F, D), y))) fs)
    = map_of (map (\<lambda>(F, y). (F, D, y)) fs)"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)


lemma map_of_reinsert_SomeD:
  "map_of (map (\<lambda>(F, y). ((F, D), y)) fs) (F, D) = Some T \<Longrightarrow> map_of fs F = Some T"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)

lemma map_of_filtered_SomeD:
"map_of fs (F,D) = Some (a, T) \<Longrightarrow> Q ((F,D),a,T) \<Longrightarrow>
       map_of (map (\<lambda>((F,D), b, T). ((F,D), P T)) (filter Q fs))
        (F,D) = Some (P T)"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)


lemma map_of_remove_filtered_SomeD:
"map_of fs (F,C) = Some (a, T) \<Longrightarrow> Q ((F,C),a,T) \<Longrightarrow>
       map_of (map (\<lambda>((F,D), b, T). (F, P T)) [((F, D), b, T)\<leftarrow>fs . Q ((F, D), b, T) \<and> D = C])
        F = Some (P T)"
(*<*)by (induct fs) (auto simp:fun_upd_apply split: if_split_asm)(*>*)


lemma map_of_Some_None_split:
assumes "t = map (\<lambda>(F, y). ((F, C), y)) fs @ t'" "map_of t' (F, C) = None" "map_of t (F, C) = Some y"
shows "map_of (map (\<lambda>((F, D), b, T). (F, D, b, T)) t) F = Some (C, y)"
(*<*)
proof -
  have "map_of (map (\<lambda>(F, y). ((F, C), y)) fs) (F, C) = Some y" using assms by auto
  then have "\<forall>p. map_of fs F = Some p \<or> Some y \<noteq> Some p"
    by (metis map_of_reinsert_SomeD)
  then have "\<forall>f b p pa. ((f ++ map_of (map (\<lambda>(a, p). (a, b::'b, p)) fs)) F = Some p \<or> Some (b, pa) \<noteq> Some p)
     \<or> Some y \<noteq> Some pa"
    by (metis (no_types) map_add_find_right map_of_insertmap_SomeD')
  then have "(map_of (map (\<lambda>((a, b), c, d). (a, b, c, d)) t')
                     ++ map_of (map (\<lambda>(a, p). (a, C, p)) fs)) F = Some (C, y)"
    by blast
  then have "(map_of (map (\<lambda>((a, b), c, d). (a, b, c, d)) t')
      ++ map_of (map ((\<lambda>((a, b), c, d). (a, b, c, d)) \<circ> (\<lambda>(a, y). ((a, C), y))) fs)) F = Some (C, y)"
    by (simp add: map_of_remap_insertmap)
  then show ?thesis using assms by auto
qed
(*>*)

end
