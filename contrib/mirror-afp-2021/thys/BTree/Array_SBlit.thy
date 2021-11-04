theory Array_SBlit
  imports "Separation_Logic_Imperative_HOL.Array_Blit"
begin

section "Same array Blit"

text "The standard framework already provides a function to copy array
      elements."

term blit
thm blit_rule
thm blit.simps
  (* Same array BLIT *)
definition "sblit a s d l \<equiv> blit a s a d l"

text "When copying values within arrays,
      blit only works for moving elements to the left."

lemma sblit_rule[sep_heap_rules]:
  assumes LEN:
    "si+len \<le> length lsrc"
    and DST_SM: "di \<le> si"
  shows
    "< src \<mapsto>\<^sub>a lsrc  >
    sblit src si di len
    <\<lambda>_. src \<mapsto>\<^sub>a (take di lsrc @ take len (drop si lsrc) @ drop (di+len) lsrc)
    >"
  unfolding sblit_def
  using LEN DST_SM
proof (induction len arbitrary: lsrc si di)
  case 0 thus ?case by sep_auto
next
  case (Suc len) 
  note [sep_heap_rules] = Suc.IH      

  have [simp]: "\<And>x. lsrc ! si # take len (drop (Suc si) lsrc) @ x
      = take (Suc len) (drop si lsrc) @ x"
    apply simp
    by (metis Suc.prems(1) add_Suc_right Cons_nth_drop_Suc
        less_Suc_eq_le add.commute not_less_eq take_Suc_Cons 
        Nat.trans_le_add2)

  from Suc.prems show ?case
    by (sep_auto simp: take_update_last drop_upd_irrelevant)
qed

subsection "A reverse blit"

text "The function rblit may be used to copy elements a defined offset to the right"

(* Right BLIT or Reverse BLIT *)
primrec rblit :: "_ array \<Rightarrow> nat \<Rightarrow> _ array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "rblit _ _ _ _ 0 = return ()"
| "rblit src si dst di (Suc l) = do {
      x \<leftarrow> Array.nth src (si+l);
      Array.upd (di+l) x dst;
      rblit src si dst di l
    }"

text "For separated arrays it is equivalent to normal blit.
      The proof follows similarly to the corresponding proof for blit."

lemma rblit_rule[sep_heap_rules]:
  assumes LEN: "si+len \<le> length lsrc" "di+len \<le> length ldst"
  shows
    "< src \<mapsto>\<^sub>a lsrc 
      * dst \<mapsto>\<^sub>a ldst >
    rblit src si dst di len
    <\<lambda>_. src \<mapsto>\<^sub>a lsrc 
      * dst \<mapsto>\<^sub>a (take di ldst @ take len (drop si lsrc) @ drop (di+len) ldst)
    >"
  using LEN
proof (induction len arbitrary: ldst)
  case 0 thus ?case by sep_auto
next
  case (Suc len) 
  note [sep_heap_rules] = Suc.IH

  have [simp]: "drop (di + len) (ldst[di + len := lsrc ! (si + len)])
      = lsrc ! (si + len) #  drop (Suc (di + len)) ldst"
    by (metis Cons_nth_drop_Suc Suc.prems(2) Suc_le_eq add_Suc_right drop_upd_irrelevant length_list_update lessI nth_list_update_eq)

  have "take len (drop si lsrc) @ [lsrc ! (si + len)] = take (Suc len) (drop si lsrc)"
  proof -
    have "len < length (drop si lsrc)"
      using Suc.prems(1) by force
    then show "take len (drop si lsrc) @ [lsrc ! (si + len)] = take (Suc len) (drop si lsrc)"
      by (metis (no_types) Suc.prems(1) add_leD1 nth_drop take_Suc_conv_app_nth)
  qed
  then have [simp]: "\<And>x. take len (drop si lsrc) @
     lsrc ! (si + len) # x = take (Suc len) (drop si lsrc) @ x"
    by simp
  from Suc.prems show ?case
    by (sep_auto simp: take_update_last drop_upd_irrelevant)
qed

definition "srblit a s d l \<equiv> rblit a s a d l"

text "However, within arrays we can now copy to the right."

lemma srblit_rule[sep_heap_rules]:
  assumes LEN:
    "di+len \<le> length lsrc"
    and DST_GR: "di \<ge> si"
  shows
    "< src \<mapsto>\<^sub>a lsrc  >
    srblit src si di len
    <\<lambda>_. src \<mapsto>\<^sub>a (take di lsrc @ take len (drop si lsrc) @ drop (di+len) lsrc)
    >"
  unfolding srblit_def
  using LEN DST_GR
proof (induction len arbitrary: lsrc si di)
  case 0 thus ?case by sep_auto
next
  case (Suc len) 
  note [sep_heap_rules] = Suc.IH

  have[simp]: "take len (drop si (lsrc[di + len := lsrc ! (si + len)]))
        = take len (drop si lsrc)"
    sledgehammer
    by (metis Suc.prems(2) ab_semigroup_add_class.add.commute add_le_cancel_right take_drop take_update_cancel)
  have [simp]: "drop (di + len) (lsrc[di + len := lsrc ! (si + len)])
         = lsrc ! (si+len) # drop (Suc di + len) lsrc"
    by (metis Suc.prems(1) add_Suc_right add_Suc_shift add_less_cancel_left append_take_drop_id le_imp_less_Suc le_refl plus_1_eq_Suc same_append_eq take_update_cancel upd_conv_take_nth_drop)
  have "take len (drop si lsrc) @
     [lsrc ! (si + len)] = take (Suc len) (drop si lsrc)"
  proof -
    have "len < length lsrc - si"
      using Suc.prems(1) Suc.prems(2) by linarith
    then show ?thesis
      by (metis (no_types) Suc.prems(1) Suc.prems(2) add_leD1 le_add_diff_inverse length_drop nth_drop take_Suc_conv_app_nth)
  qed
  then have [simp]: "\<And>x. take len (drop si lsrc) @
     lsrc ! (si + len) # x = take (Suc len) (drop si lsrc) @ x"
    by simp
  from Suc.prems show ?case
    by (sep_auto simp: take_update_last drop_upd_irrelevant)
qed

subsection "Modeling target language blit"

text "For convenience, a function that is oblivious to the direction of the shift
      is defined."
definition "safe_sblit a s d l \<equiv> 
    if s > d then
      sblit a s d l
    else
      srblit a s d l
"

text "We obtain a heap rule similar to the one of blit,
      but for copying within one array."

lemma safe_sblit_rule[sep_heap_rules]:
  assumes LEN:
    "len > 0 \<longrightarrow> di+len \<le> length lsrc \<and> si+len \<le> length lsrc"
  shows
    "< src \<mapsto>\<^sub>a lsrc  >
    safe_sblit src si di len
    <\<lambda>_. src \<mapsto>\<^sub>a (take di lsrc @ take len (drop si lsrc) @ drop (di+len) lsrc)
    >"
  unfolding safe_sblit_def
  using LEN
  apply(cases len)
   apply(sep_auto simp add: sblit_def srblit_def)[]
  apply sep_auto
  done

(* Compare this to blit_rule *)
thm blit_rule
thm safe_sblit_rule

subsection "Code Generator Setup"

text "Note that the requirement for correctness
      is even weaker here than in SML.
      We therefore manually handle the case where length is 0 (in which case nothing happens at all)."

code_printing code_module "array_sblit" \<rightharpoonup> (SML)
  \<open>
   fun array_sblit src si di len = (
      if len > 0 then
        ArraySlice.copy {
          di = IntInf.toInt di,
          src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
          dst = src}
      else ()
    )
\<close>

definition safe_sblit' where
  [code del]: "safe_sblit' src si di len 
      = safe_sblit src (nat_of_integer si) (nat_of_integer di) 
          (nat_of_integer len)"

lemma [code]:
  "safe_sblit src si di len 
      = safe_sblit' src (integer_of_nat si) (integer_of_nat di) 
          (integer_of_nat len)" by (simp add: safe_sblit'_def)

(* TODO: Export to other languages: OCaml, Haskell *)
code_printing constant safe_sblit' \<rightharpoonup>
  (SML) "(fn/ ()/ => /array'_sblit _ _ _ _)"
  and (Scala) "{ ('_: Unit)/=>/
      def safescopy(src: Array['_], srci: Int, dsti: Int, len: Int) = {
       if (len > 0)
          System.arraycopy(src, srci, src, dsti, len)
        else
          ()
      }
      safescopy(_.array,_.toInt,_.toInt,_.toInt)
    }"

export_code safe_sblit checking SML Scala


subsection "Derived operations"

definition array_shr where
  "array_shr a i k \<equiv> do {
  l \<leftarrow> Array.len a;
  safe_sblit a i (i+k) (l-(i+k))
}"

find_theorems "Array.len"

lemma array_shr_rule[sep_heap_rules]:
  "< src \<mapsto>\<^sub>a lsrc  >
    array_shr src i k
    <\<lambda>_. src \<mapsto>\<^sub>a (take (i+k) lsrc @ take (length lsrc - (i+k)) (drop i lsrc))
    >"
  unfolding array_shr_def
  by sep_auto

lemma array_shr_rule_alt:
  "< src \<mapsto>\<^sub>a lsrc  >
    array_shr src i k
    <\<lambda>_. src \<mapsto>\<^sub>a (take (length lsrc) (take (i+k) lsrc @ (drop i lsrc)))
    >"
  by (sep_auto simp add: min_def)

definition array_shl where
  "array_shl a i k \<equiv> do {
  l \<leftarrow> Array.len a;
  safe_sblit a i (i-k) (l-i)
}
"

lemma array_shl_rule[sep_heap_rules]:
  "
    < src \<mapsto>\<^sub>a lsrc  >
    array_shl src i k
    <\<lambda>_. src \<mapsto>\<^sub>a (take (i-k) lsrc @ (drop i lsrc) @ drop (i - k + (length lsrc - i)) lsrc)
    >"
  unfolding array_shl_def
  by sep_auto


lemma array_shl_rule_alt:
  "
    \<lbrakk>i \<le> length lsrc; k \<le> i\<rbrakk> \<Longrightarrow>
    < src \<mapsto>\<^sub>a lsrc  >
    array_shl src i k
    <\<lambda>_. src \<mapsto>\<^sub>a (take (i-k) lsrc @ (drop i lsrc) @ drop (length lsrc - k) lsrc)
    >"
  by sep_auto


end