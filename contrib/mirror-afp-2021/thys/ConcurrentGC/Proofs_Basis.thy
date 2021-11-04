(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Proofs_Basis
imports
  Model
  "HOL-Library.Simps_Case_Conv"
begin

(* From 40e16c534243 by Makarius. Doesn't seem to have a huge impact on run time now (2021-01-07) *)
declare subst_all [simp del] [[simproc del: defined_all]]

(*>*)
section\<open> Proofs Basis \label{sec:proofs-basis}\<close>

text\<open>

Extra HOL.

\<close>

lemma Set_bind_insert[simp]:
  "Set.bind (insert a A) B = B a \<union> (Set.bind A B)"
by (auto simp: Set.bind_def)

lemma option_bind_invE[elim]:
  "\<lbrakk> Option.bind f g = None; \<And>a. \<lbrakk> f = Some a; g a = None \<rbrakk> \<Longrightarrow> Q; f = None \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk> Option.bind f g = Some x; \<And>a. \<lbrakk> f = Some a; g a = Some x \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (case_tac [!] f) simp_all

lemmas conj_explode = conj_imp_eq_imp_imp

text\<open>

Tweak the default simpset:
\<^item> "not in dom" as a premise negates the goal
\<^item> we always want to execute suffix
\<^item> we try to make simplification rules about @{const \<open>fun_upd\<close>} more stable

\<close>

declare dom_def[simp]
declare suffix_to_prefix[simp]
declare map_option.compositionality[simp]
declare o_def[simp]
declare Option.Option.option.set_map[simp]
declare bind_image[simp]

declare fun_upd_apply[simp del]
declare fun_upd_same[simp]
declare fun_upd_other[simp]

declare gc_phase.case_cong[cong]
declare mem_store_action.case_cong[cong]
declare process_name.case_cong[cong]
declare hs_phase.case_cong[cong]
declare hs_type.case_cong[cong]

declare if_split_asm[split]

text\<open>

Collect the component definitions. Inline everything. This is what the proofs work on.
Observe we lean heavily on locales.

\<close>

context gc
begin

lemmas all_com_defs =
  (* gc.com_def *) handshake_done_def handshake_init_def handshake_noop_def handshake_get_roots_def handshake_get_work_def
  mark_object_fn_def

lemmas com_def2 = com_def[simplified all_com_defs append.simps if_True if_False]

intern_com com_def2

end

context mut_m
begin

lemmas all_com_defs =
  (* mut.com_def *) mut_m.handshake_def mut_m.store_def
  mark_object_fn_def

lemmas com_def2 = mut_m.com_def[simplified all_com_defs append.simps if_True if_False]

intern_com com_def2

end

context sys
begin

lemmas all_com_defs =
  (* sys.com_def *) sys.alloc_def sys.free_def sys.mem_TSO_def sys.handshake_def

lemmas com_def2 = com_def[simplified all_com_defs append.simps if_True if_False]

intern_com com_def2

end

lemmas all_com_interned_defs = gc.com_interned mut_m.com_interned sys.com_interned

named_theorems inv "Location-sensitive invariant definitions"
named_theorems nie "Non-interference elimination rules"


subsection\<open> Model-specific functions and predicates \<close>

text\<open>

We define a pile of predicates and accessor functions for the
process's local states. One might hope that a more sophisticated
approach would automate all of this (cf @{cite [cite_macro=citet]
"DBLP:journals/entcs/SchirmerW09"}).

\<close>

abbreviation prefixed :: "location \<Rightarrow> location set" where
  "prefixed p \<equiv> { l . prefix p l }"

abbreviation suffixed :: "location \<Rightarrow> location set" where
  "suffixed p \<equiv> { l . suffix p l }"

abbreviation "is_mw_Mark w \<equiv> \<exists>r fl. w = mw_Mark r fl"
abbreviation "is_mw_Mutate w \<equiv> \<exists>r f r'. w = mw_Mutate r f r'"
abbreviation "is_mw_Mutate_Payload w \<equiv> \<exists>r f pl. w = mw_Mutate_Payload r f pl"
abbreviation "is_mw_fA w \<equiv> \<exists>fl. w = mw_fA fl"
abbreviation "is_mw_fM w \<equiv> \<exists>fl. w = mw_fM fl"
abbreviation "is_mw_Phase w \<equiv> \<exists>ph. w = mw_Phase ph"

abbreviation (input) pred_in_W :: "'ref \<Rightarrow> 'mut process_name \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" (infix "in'_W" 50) where
  "r in_W p \<equiv> \<lambda>s. r \<in> W (s p)"

abbreviation (input) pred_in_ghost_honorary_grey :: "'ref \<Rightarrow> 'mut process_name \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" (infix "in'_ghost'_honorary'_grey" 50) where
  "r in_ghost_honorary_grey p \<equiv> \<lambda>s. r \<in> ghost_honorary_grey (s p)"

abbreviation "gc_cas_mark s \<equiv> cas_mark (s gc)"
abbreviation "gc_fM s \<equiv> fM (s gc)"
abbreviation "gc_field s \<equiv> field (s gc)"
abbreviation "gc_field_set s \<equiv> field_set (s gc)"
abbreviation "gc_mark s \<equiv> mark (s gc)"
abbreviation "gc_mut s \<equiv> mut (s gc)"
abbreviation "gc_muts s \<equiv> muts (s gc)"
abbreviation "gc_phase s \<equiv> phase (s gc)"
abbreviation "gc_tmp_ref s \<equiv> tmp_ref (s gc)"
abbreviation "gc_ghost_honorary_grey s \<equiv> ghost_honorary_grey (s gc)"
abbreviation "gc_ref s \<equiv> ref (s gc)"
abbreviation "gc_refs s \<equiv> refs (s gc)"
abbreviation "gc_the_ref \<equiv> the \<circ> gc_ref"
abbreviation "gc_W s \<equiv> W (s gc)"

abbreviation at_gc :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_pred" where
  "at_gc l P \<equiv> at gc l \<^bold>\<longrightarrow> LSTP P"

abbreviation atS_gc :: "location set \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_pred" where
  "atS_gc ls P \<equiv> atS gc ls \<^bold>\<longrightarrow> LSTP P"

context mut_m
begin

abbreviation at_mut :: "location \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_pred" where
  "at_mut l P \<equiv> at (mutator m) l \<^bold>\<longrightarrow> LSTP P"

abbreviation atS_mut :: "location set \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_pred" where
  "atS_mut ls P \<equiv> atS (mutator m) ls \<^bold>\<longrightarrow> LSTP P"

abbreviation "mut_cas_mark s \<equiv> cas_mark (s (mutator m))"
abbreviation "mut_field s \<equiv> field (s (mutator m))"
abbreviation "mut_fM s \<equiv> fM (s (mutator m))"
abbreviation "mut_ghost_honorary_grey s \<equiv> ghost_honorary_grey (s (mutator m))"
abbreviation "mut_ghost_hs_phase s \<equiv> ghost_hs_phase (s (mutator m))"
abbreviation "mut_ghost_honorary_root s \<equiv> ghost_honorary_root (s (mutator m))"
abbreviation "mut_hs_pending s \<equiv> mutator_hs_pending (s (mutator m))"
abbreviation "mut_hs_type s \<equiv> hs_type (s (mutator m))"
abbreviation "mut_mark s \<equiv> mark (s (mutator m))"
abbreviation "mut_new_ref s \<equiv> new_ref (s (mutator m))"
abbreviation "mut_phase s \<equiv> phase (s (mutator m))"
abbreviation "mut_ref s \<equiv> ref (s (mutator m))"
abbreviation "mut_tmp_ref s \<equiv> tmp_ref (s (mutator m))"
abbreviation "mut_the_new_ref \<equiv> the \<circ> mut_new_ref"
abbreviation "mut_the_ref \<equiv> the \<circ> mut_ref"
abbreviation "mut_refs s \<equiv> refs (s (mutator m))"
abbreviation "mut_roots s \<equiv> roots (s (mutator m))"
abbreviation "mut_W s \<equiv> W (s (mutator m))"

end

abbreviation sys_heap :: "('field, 'mut, 'payload, 'ref) lsts \<Rightarrow> 'ref \<Rightarrow> ('field, 'payload, 'ref) object option" where "sys_heap s \<equiv> heap (s sys)"

abbreviation "sys_fA s \<equiv> fA (s sys)"
abbreviation "sys_fM s \<equiv> fM (s sys)"
abbreviation "sys_ghost_honorary_grey s \<equiv> ghost_honorary_grey (s sys)"
abbreviation "sys_ghost_hs_in_sync m s \<equiv> ghost_hs_in_sync (s sys) m"
abbreviation "sys_ghost_hs_phase s \<equiv> ghost_hs_phase (s sys)"
abbreviation "sys_hs_pending m s \<equiv> hs_pending (s sys) m"
abbreviation "sys_hs_type s \<equiv> hs_type (s sys)"
abbreviation "sys_mem_store_buffers p s \<equiv> mem_store_buffers (s sys) p"
abbreviation "sys_mem_lock s \<equiv> mem_lock (s sys)"
abbreviation "sys_phase s \<equiv> phase (s sys)"
abbreviation "sys_W s \<equiv> W (s sys)"

abbreviation atS_sys :: "location set \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'payload, 'ref) gc_pred" where
  "atS_sys ls P \<equiv> atS sys ls \<^bold>\<longrightarrow> LSTP P"

text\<open>Projections on TSO buffers.\<close>

abbreviation (input) "tso_unlocked s \<equiv> mem_lock (s sys) = None"
abbreviation (input) "tso_locked_by p s \<equiv> mem_lock (s sys) = Some p"

abbreviation (input) "tso_pending p P s \<equiv> filter P (mem_store_buffers (s sys) p)"
abbreviation (input) "tso_pending_store p w s \<equiv> w \<in> set (mem_store_buffers (s sys) p)"

abbreviation (input) "tso_pending_fA p \<equiv> tso_pending p is_mw_fA"
abbreviation (input) "tso_pending_fM p \<equiv> tso_pending p is_mw_fM"
abbreviation (input) "tso_pending_mark p \<equiv> tso_pending p is_mw_Mark"
abbreviation (input) "tso_pending_mw_mutate p \<equiv> tso_pending p is_mw_Mutate"
abbreviation (input) "tso_pending_mutate p \<equiv> tso_pending p (is_mw_Mutate \<^bold>\<or> is_mw_Mutate_Payload)" \<comment>\<open> TSO makes it (mostly) not worth distinguishing these. \<close>
abbreviation (input) "tso_pending_phase p \<equiv> tso_pending p is_mw_Phase"

abbreviation (input) "tso_no_pending_marks \<equiv> \<^bold>\<forall>p. LIST_NULL (tso_pending_mark p)"

text\<open>

A somewhat-useful abstraction of the heap, following l4.verified,
which asserts that there is an object at the given reference with the
given property. In some sense this encodes a three-valued logic.

\<close>

definition obj_at :: "(('field, 'payload, 'ref) object \<Rightarrow> bool) \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "obj_at P r \<equiv> \<lambda>s. case sys_heap s r of None \<Rightarrow> False | Some obj \<Rightarrow> P obj"

abbreviation (input) valid_ref :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "valid_ref r \<equiv> obj_at \<langle>True\<rangle> r"

definition valid_null_ref :: "'ref option \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "valid_null_ref r \<equiv> case r of None \<Rightarrow> \<langle>True\<rangle> | Some r' \<Rightarrow> valid_ref r'"

abbreviation pred_points_to :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" (infix "points'_to" 51) where
  "x points_to y \<equiv> \<lambda>s. obj_at (\<lambda>obj. y \<in> ran (obj_fields obj)) x s"

text\<open>

We use Isabelle's standard transitive-reflexive closure to define
reachability through the heap.

\<close>

definition reaches :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" (infix "reaches" 51) where
  "x reaches y = (\<lambda>s. (\<lambda>x y. (x points_to y) s)\<^sup>*\<^sup>* x y)"

text\<open>

The predicate \<open>obj_at_field_on_heap\<close> asserts that @{term \<open>valid_ref r\<close>}
and if \<open>f\<close> is a field of the object referred to by \<open>r\<close> then it it satisfies \<open>P\<close>.

\<close>

definition obj_at_field_on_heap :: "('ref \<Rightarrow> bool) \<Rightarrow> 'ref \<Rightarrow> 'field \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "obj_at_field_on_heap P r f \<equiv> \<lambda>s.
     case map_option obj_fields (sys_heap s r) of
         None \<Rightarrow> False
       | Some fs \<Rightarrow> (case fs f of None \<Rightarrow> True
                               | Some r' \<Rightarrow> P r')"


subsection\<open>Object colours\<close>

text\<open>

We adopt the classical tricolour scheme for object colours due to
@{cite [cite_macro=citet] "DBLP:journals/cacm/DijkstraLMSS78"}, but
tweak it somewhat in the presence of worklists and TSO. Intuitively:
\begin{description}
\item[White] potential garbage, not yet reached
\item[Grey] reached, presumed live, a source of possible new references (work)
\item[Black] reached, presumed live, not a source of new references
\end{description}

In this particular setting we use the following interpretation:
\begin{description}
\item[White:] not marked
\item[Grey:] on a worklist or @{const \<open>ghost_honorary_grey\<close>}
\item[Black:] marked and not on a worklist
\end{description}

Note that this allows the colours to overlap: an object being marked
may be white (on the heap) and in @{const "ghost_honorary_grey"} for
some process, i.e. grey.

\<close>

abbreviation marked :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "marked r s \<equiv> obj_at (\<lambda>obj. obj_mark obj = sys_fM s) r s"

definition white :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "white r s \<equiv> obj_at (\<lambda>obj. obj_mark obj \<noteq> sys_fM s) r s"

definition WL :: "'mut process_name \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts \<Rightarrow> 'ref set" where
  "WL p = (\<lambda>s. W (s p) \<union> ghost_honorary_grey (s p))"

definition grey :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "grey r = (\<^bold>\<exists>p. \<langle>r\<rangle> \<^bold>\<in> WL p)"

definition black :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "black r \<equiv> marked r \<^bold>\<and> \<^bold>\<not>grey r"

text\<open> These demonstrate the overlap in colours. \<close>

lemma colours_distinct[dest]:
  "black r s \<Longrightarrow> \<not>grey r s"
  "black r s \<Longrightarrow> \<not>white r s"
  "grey r s  \<Longrightarrow> \<not>black r s"
  "white r s \<Longrightarrow> \<not>black r s"
by (auto simp: black_def white_def obj_at_def split: option.splits) (* FIXME invisible *)

lemma marked_imp_black_or_grey:
  "marked r s \<Longrightarrow> black r s \<or> grey r s"
  "\<not> white r s \<Longrightarrow> \<not> valid_ref r s \<or> black r s \<or> grey r s"
by (auto simp: black_def grey_def white_def obj_at_def split: option.splits)  (* FIXME invisible *)

text\<open>

In some phases the heap is monochrome.

\<close>

definition black_heap :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "black_heap = (\<^bold>\<forall>r. valid_ref r \<^bold>\<longrightarrow> black r)"

definition white_heap :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "white_heap = (\<^bold>\<forall>r. valid_ref r \<^bold>\<longrightarrow> white r)"

definition no_black_refs :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "no_black_refs = (\<^bold>\<forall>r. \<^bold>\<not>black r)"

definition no_grey_refs :: "('field, 'mut, 'payload, 'ref) lsts_pred" where
  "no_grey_refs = (\<^bold>\<forall>r. \<^bold>\<not>grey r)"


subsection\<open>Reachability\<close>

text\<open>

We treat pending TSO heap mutations as extra mutator roots.

\<close>

abbreviation store_refs :: "('field, 'payload, 'ref) mem_store_action \<Rightarrow> 'ref set" where
  "store_refs w \<equiv> case w of mw_Mutate r f r' \<Rightarrow> {r} \<union> Option.set_option r' | mw_Mutate_Payload r f pl \<Rightarrow> {r} | _ \<Rightarrow> {}"

definition (in mut_m) tso_store_refs :: "('field, 'mut, 'payload, 'ref) lsts \<Rightarrow> 'ref set" where
  "tso_store_refs = (\<lambda>s. \<Union>w \<in> set (sys_mem_store_buffers (mutator m) s). store_refs w)"

abbreviation (in mut_m) root :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "root x \<equiv> \<langle>x\<rangle> \<^bold>\<in> mut_roots \<^bold>\<union> mut_ghost_honorary_root \<^bold>\<union> tso_store_refs"

definition (in mut_m) reachable :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "reachable y = (\<^bold>\<exists>x. root x \<^bold>\<and> x reaches y)"

definition grey_reachable :: "'ref \<Rightarrow> ('field, 'mut, 'payload, 'ref) lsts_pred" where
  "grey_reachable y = (\<^bold>\<exists>g. grey g \<^bold>\<and> g reaches y)"


subsection\<open> Sundry detritus \<close>

lemmas eq_imp_simps = \<comment>\<open>equations for deriving useful things from @{const \<open>eq_imp\<close>} facts\<close>
  eq_imp_def
  all_conj_distrib
  split_paired_All split_def fst_conv snd_conv prod_eq_iff
  conj_explode
  simp_thms

lemma p_not_sys:
  "p \<noteq> sys \<longleftrightarrow> p = gc \<or> (\<exists>m. p = mutator m)"
by (cases p) simp_all

lemma (in mut_m') m'm[iff]: "m' \<noteq> m"
using mm' by blast

text\<open> obj at \<close>

lemma obj_at_cong[cong]:
  "\<lbrakk>\<And>obj. sys_heap s r = Some obj \<Longrightarrow> P obj = P' obj; r = r'; s = s'\<rbrakk>
   \<Longrightarrow> obj_at P r s \<longleftrightarrow> obj_at P' r' s'"
unfolding obj_at_def by (simp cong: option.case_cong)

lemma obj_at_split:
  "Q (obj_at P r s) = ((sys_heap s r = None \<longrightarrow> Q False) \<and> (\<forall>obj. sys_heap s r = Some obj \<longrightarrow> Q (P obj)))"
by (simp add: obj_at_def split: option.splits)

lemma obj_at_split_asm:
  "Q (obj_at P r s) = (\<not> ((sys_heap s r = None \<and> \<not>Q False) \<or> (\<exists>obj. sys_heap s r = Some obj \<and> \<not> Q (P obj))))"
by (simp add: obj_at_def split: option.splits)

lemmas obj_at_splits = obj_at_split obj_at_split_asm

lemma obj_at_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. map_option P (sys_heap s r))
          (obj_at P r)"
by (simp add: eq_imp_def obj_at_def split: option.splits)

lemmas obj_at_fun_upd[simp] = eq_imp_fun_upd[OF obj_at_eq_imp, simplified eq_imp_simps]

lemma obj_at_simps:
  "obj_at (\<lambda>obj. P obj \<and> Q obj) r s \<longleftrightarrow> obj_at P r s \<and> obj_at Q r s"
(*  "obj_at (\<lambda>obj. R) r s \<longleftrightarrow> valid_ref r s \<and> R" looks good but applies to valid_ref *)
by (simp_all split: obj_at_splits)

text\<open> obj at field on heap \<close>

lemma obj_at_field_on_heap_cong[cong]:
  "\<lbrakk>\<And>r' obj. \<lbrakk>sys_heap s r = Some obj; obj_fields obj f = Some r'\<rbrakk>\<Longrightarrow> P r' = P' r'; r = r'; f = f'; s = s'\<rbrakk>
   \<Longrightarrow> obj_at_field_on_heap P r f s \<longleftrightarrow> obj_at_field_on_heap P' r' f' s'"
unfolding obj_at_field_on_heap_def by (simp cong: option.case_cong)

lemma obj_at_field_on_heap_split:
  "Q (obj_at_field_on_heap P r f s) \<longleftrightarrow> ((sys_heap s r = None \<longrightarrow> Q False)
                                 \<and> (\<forall>obj. sys_heap s r = Some obj \<and> obj_fields obj f = None \<longrightarrow> Q True)
                                 \<and> (\<forall>r' obj. sys_heap s r = Some obj \<and> obj_fields obj f = Some r' \<longrightarrow> Q (P r')))"
by (simp add: obj_at_field_on_heap_def split: option.splits)

lemma obj_at_field_on_heap_split_asm:
  "Q (obj_at_field_on_heap P r f s) \<longleftrightarrow> (\<not> ((sys_heap s r = None \<and> \<not>Q False)
                                    \<or> (\<exists>obj. sys_heap s r = Some obj \<and> obj_fields obj f = None \<and> \<not> Q True)
                                    \<or> (\<exists>r' obj. sys_heap s r = Some obj \<and> obj_fields obj f = Some r' \<and> \<not> Q (P r'))))"
by (simp add: obj_at_field_on_heap_def split: option.splits)

lemmas obj_at_field_on_heap_splits = obj_at_field_on_heap_split obj_at_field_on_heap_split_asm

lemma obj_at_field_on_heap_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. sys_heap s r)
          (obj_at_field_on_heap P r f)"
by (simp add: eq_imp_def obj_at_field_on_heap_def)

lemmas obj_at_field_on_heap_fun_upd[simp] = eq_imp_fun_upd[OF obj_at_field_on_heap_eq_imp, simplified eq_imp_simps]

lemma obj_at_field_on_heap_imp_valid_ref[elim]:
  "obj_at_field_on_heap P r f s \<Longrightarrow> valid_ref r s"
  "obj_at_field_on_heap P r f s \<Longrightarrow> valid_null_ref (Some r) s"
by (auto simp: obj_at_field_on_heap_def valid_null_ref_def split: obj_at_splits option.splits)

lemma obj_at_field_on_heapE[elim]:
  "\<lbrakk> obj_at_field_on_heap P r f s; sys_heap s' r = sys_heap s r; \<And>r'. P r' \<Longrightarrow> P' r' \<rbrakk>
       \<Longrightarrow> obj_at_field_on_heap P' r f s'"
by (simp add: obj_at_field_on_heap_def split: option.splits)

lemma valid_null_ref_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. Option.bind r (map_option \<langle>True\<rangle> \<circ> sys_heap s))
          (valid_null_ref r)"
by (simp add: eq_imp_def obj_at_def valid_null_ref_def split: option.splits)

lemmas valid_null_ref_fun_upd[simp] = eq_imp_fun_upd[OF valid_null_ref_eq_imp, simplified]

lemma valid_null_ref_simps[simp]:
  "valid_null_ref None s"
  "valid_null_ref (Some r) s \<longleftrightarrow> valid_ref r s"
unfolding valid_null_ref_def by simp_all

text\<open>Derive simplification rules from \<open>case\<close> expressions\<close>

simps_of_case hs_step_simps[simp]: hs_step_def (splits: hs_phase.split)
simps_of_case do_load_action_simps[simp]: fun_cong[OF do_load_action_def[simplified atomize_eq]] (splits: mem_load_action.split)
simps_of_case do_store_action_simps[simp]: fun_cong[OF do_store_action_def[simplified atomize_eq]] (splits: mem_store_action.split)

(* This gives some indication of how much we're cheating on the TSO front. *)
lemma do_store_action_prj_simps[simp]:
  "fM (do_store_action w s) = fl \<longleftrightarrow> (fM s = fl \<and> w \<noteq> mw_fM (\<not>fM s)) \<or> w = mw_fM fl"
  "fl = fM (do_store_action w s) \<longleftrightarrow> (fl = fM s \<and> w \<noteq> mw_fM (\<not>fM s)) \<or> w = mw_fM fl"
  "fA (do_store_action w s) = fl \<longleftrightarrow> (fA s = fl \<and> w \<noteq> mw_fA (\<not>fA s)) \<or> w = mw_fA fl"
  "fl = fA (do_store_action w s) \<longleftrightarrow> (fl = fA s \<and> w \<noteq> mw_fA (\<not>fA s)) \<or> w = mw_fA fl"
  "ghost_hs_in_sync (do_store_action w s) = ghost_hs_in_sync s"
  "ghost_hs_phase (do_store_action w s) = ghost_hs_phase s"
  "ghost_honorary_grey (do_store_action w s) = ghost_honorary_grey s"
  "hs_pending (do_store_action w s) = hs_pending s"
  "hs_type (do_store_action w s) = hs_type s"
  "heap (do_store_action w s) r = None \<longleftrightarrow> heap s r = None"
  "mem_lock (do_store_action w s) = mem_lock s"
  "phase (do_store_action w s) = ph \<longleftrightarrow> (phase s = ph \<and> (\<forall>ph'. w \<noteq> mw_Phase ph') \<or> w = mw_Phase ph)"
  "ph = phase (do_store_action w s) \<longleftrightarrow> (ph = phase s \<and> (\<forall>ph'. w \<noteq> mw_Phase ph') \<or> w = mw_Phase ph)"
  "W (do_store_action w s) = W s"
by (auto simp: do_store_action_def fun_upd_apply split: mem_store_action.splits obj_at_splits)


text\<open> reaches \<close>

lemma reaches_refl[iff]:
  "(r reaches r) s"
unfolding reaches_def by blast

lemma reaches_step[intro]:
  "\<lbrakk>(x reaches y) s; (y points_to z) s\<rbrakk> \<Longrightarrow> (x reaches z) s"
  "\<lbrakk>(y reaches z) s; (x points_to y) s\<rbrakk> \<Longrightarrow> (x reaches z) s"
unfolding reaches_def
 apply (simp add: rtranclp.rtrancl_into_rtrancl)
apply (simp add: converse_rtranclp_into_rtranclp)
done

lemma reaches_induct[consumes 1, case_names refl step, induct set: reaches]:
  assumes "(x reaches y) s"
  assumes "\<And>x. P x x"
  assumes "\<And>x y z. \<lbrakk>(x reaches y) s; P x y; (y points_to z) s\<rbrakk> \<Longrightarrow> P x z"
  shows "P x y"
using assms unfolding reaches_def by (rule rtranclp.induct)

lemma converse_reachesE[consumes 1, case_names base step]:
  assumes "(x reaches z) s"
  assumes "x = z \<Longrightarrow> P"
  assumes "\<And>y. \<lbrakk>(x points_to y) s; (y reaches z) s\<rbrakk> \<Longrightarrow> P"
  shows P
using assms unfolding reaches_def by (blast elim: converse_rtranclpE)

lemma reaches_fields: \<comment> \<open>Complicated condition takes care of \<open>alloc\<close>: collapses no object and object with no fields\<close>
  assumes "(x reaches y) s'"
  assumes "\<forall>r'. \<Union>(ran ` obj_fields ` set_option (sys_heap s' r')) = \<Union>(ran ` obj_fields ` set_option (sys_heap s r'))"
  shows "(x reaches y) s"
using assms
proof induct
  case (step x y z)
  then have "(y points_to z) s"
    by (cases "sys_heap s y")
       (auto 10 10 simp: ran_def obj_at_def split: option.splits dest!: spec[where x=y])
  with step show ?case by blast
qed simp

lemma reaches_eq_imp:
  "eq_imp (\<lambda>r' s. \<Union>(ran ` obj_fields ` set_option (sys_heap s r')))
          (x reaches y)"
unfolding eq_imp_def by (metis reaches_fields)

lemmas reaches_fun_upd[simp] = eq_imp_fun_upd[OF reaches_eq_imp, simplified eq_imp_simps, rule_format]

text\<open>

Location-specific facts.

\<close>

lemma obj_at_mark_dequeue[simp]:
  "obj_at P r (s(sys := s sys\<lparr> heap := (sys_heap s)(r' := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r')), mem_store_buffers := wb' \<rparr>))
\<longleftrightarrow> obj_at (\<lambda>obj. (P (if r = r' then obj\<lparr> obj_mark := fl \<rparr> else obj))) r s"
by (clarsimp simp: fun_upd_apply split: obj_at_splits)

lemma obj_at_field_on_heap_mw_simps[simp]:
  "obj_at_field_on_heap P r0 f0
         (s(sys := (s sys)\<lparr> heap := (sys_heap s)(r := map_option (\<lambda>obj :: ('field, 'payload, 'ref) object. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                            mem_store_buffers := (mem_store_buffers (s Sys))(p := ws) \<rparr>))
\<longleftrightarrow> ( (r \<noteq> r0 \<or> f \<noteq> f0) \<and> obj_at_field_on_heap P r0 f0 s )
   \<or> (r = r0 \<and> f = f0 \<and> valid_ref r s \<and> (case opt_r' of Some r'' \<Rightarrow> P r'' | _ \<Rightarrow> True))"
  "obj_at_field_on_heap P r f (s(sys := s sys\<lparr>heap := (sys_heap s)(r' := map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r')), mem_store_buffers := sb'\<rparr>))
\<longleftrightarrow> obj_at_field_on_heap P r f s"
by (auto simp: obj_at_field_on_heap_def fun_upd_apply split: option.splits obj_at_splits)

lemma obj_at_field_on_heap_no_pending_stores:
  "\<lbrakk> sys_load (mutator m) (mr_Ref r f) (s sys) = mv_Ref opt_r'; \<forall>opt_r'. mw_Mutate r f opt_r' \<notin> set (sys_mem_store_buffers (mutator m) s); valid_ref r s \<rbrakk>
     \<Longrightarrow> obj_at_field_on_heap (\<lambda>r. opt_r' = Some r) r f s"
unfolding sys_load_def fold_stores_def
apply clarsimp
apply (rule fold_invariant[where P="\<lambda>fr. obj_at_field_on_heap (\<lambda>r'. Option.bind (heap (fr (s sys)) r) (\<lambda>obj. obj_fields obj f) = Some r') r f s"
                             and Q="\<lambda>w. w \<in> set (sys_mem_store_buffers (mutator m) s)"])
  apply fastforce
 apply (fastforce simp: obj_at_field_on_heap_def split: option.splits obj_at_splits)
apply (auto simp: do_store_action_def map_option_case fun_upd_apply
           split: obj_at_field_on_heap_splits option.splits obj_at_splits mem_store_action.splits)
done
(*<*)

end

(*>*)
