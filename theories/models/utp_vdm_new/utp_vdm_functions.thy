(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_functions.thy                                                *)
(* Authors: Original CML model by Simon Foster, University of York (UK)       *)
(*          Adapted to VDM by Luis Diogo Couto, Aarhus University (DK)        *)
(******************************************************************************)

header {* VDM Function Library *}

theory utp_vdm_functions
imports 
  utp_vdm_types
  utp_vdm_tac
  utp_vdm_expr
  utp_vdm_monad
begin

abbreviation "hol_floor \<equiv> floor"
abbreviation "hol_abs \<equiv> abs"

type_synonym 'a hol_set = "'a set"

text {* Set up the VDM expression parser with API functions *}

text {* List Functions *}

definition seq_comp :: "('a \<Rightarrow> 'b::{vdmv,linorder}) \<Rightarrow> 'a bset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b list" where
"seq_comp f A P = blist (f `\<^sub>b {x \<in>\<^sub>b A. P(x)}\<^sub>b)"

lift_definition inds :: "'a list \<Rightarrow> nat bset" is
"\<lambda> xs. {1..length xs}"
  by (metis countable_member_bset)

declare real_of_nat_Suc [evalp]

lemma inds_nil [simp]:
  "inds [] = {}\<^sub>b"
  by (auto simp add:inds.rep_eq)

lemma inds_cons [simp]:
  "inds (x#xs) = bset_insert 1 (bset_image Suc (inds xs))"
  by (transfer, auto)
  
definition "vinds xs     \<equiv> real `\<^sub>b (inds xs)"
definition "vconc xs     \<equiv> foldr (op @) xs []"

declare vinds_def [eval,evalp]
declare vconc_def [eval,evalp]

definition "vexpr_hd      = Op1DR {x. x \<noteq> []} hd"
definition "vexpr_tl      = Op1DR {x. x \<noteq> []} tl"
definition "vexpr_seqapp  = Op2DR {(xs, i::real). i \<in> Nats \<and> nat (floor i) < length xs} (\<lambda> xs i. nth xs (nat (floor i)))"

definition vexpr_seqcomp :: "('a \<Rightarrow> 'b::{vdmv,linorder} vdme * bool vdme) \<Rightarrow> 'a bset vdme \<Rightarrow> 'b list vdme" where
"vexpr_seqcomp FP eA = do { A <- eA
                          ; PA <- vdme_bset_iter A (\<lambda> x. do { c <- snd(FP(x)); if c then LitD {x}\<^sub>b else LitD {}\<^sub>b })
                          ; LA <- vdme_bset_iter (\<Union>\<^sub>b PA) (fst \<circ> FP)
                          ; LitD (blist LA) }"
                          
definition vexpr_subseq :: "'a list vdme \<Rightarrow> real vdme \<Rightarrow> real vdme \<Rightarrow> 'a list vdme" where
"vexpr_subseq = Op3DR {(xs, m, n). m \<ge> 0 \<and> n \<ge> m} (\<lambda> xs m n. sublist xs {nat (floor m) .. nat (floor n)})"

declare vexpr_seqcomp_def [evalp]
declare vexpr_subseq_def [evalp]

declare vexpr_hd_def [eval,evalp]
declare vexpr_tl_def [eval,evalp]
declare vexpr_seqapp_def [eval,evalp]

abbreviation "vexpr_elems   \<equiv> Op1D' bset_set"
abbreviation "vexpr_concat  \<equiv> Op2D' (op @)"
abbreviation "vexpr_conc    \<equiv> Op1D' vconc"
abbreviation "vexpr_reverse \<equiv> Op1D' rev"
abbreviation "vexpr_inds    \<equiv> Op1D' vinds"
abbreviation "vexpr_len     \<equiv> Op1D' length"

syntax
  "_vexpr_hd"      :: "n_pexpr \<Rightarrow> n_pexpr" ("hd _")
  "_vexpr_tl"      :: "n_pexpr \<Rightarrow> n_pexpr" ("tl _")
  "_vexpr_len"     :: "n_pexpr \<Rightarrow> n_pexpr" ("len _")
  "_vexpr_elems"   :: "n_pexpr \<Rightarrow> n_pexpr" ("elems _")
  "_vexpr_inds"    :: "n_pexpr \<Rightarrow> n_pexpr" ("inds _")
  "_vexpr_reverse" :: "n_pexpr \<Rightarrow> n_pexpr" ("reverse _")
  "_vexpr_concat"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "^" 65)
  "_vexpr_conc"    :: "n_pexpr \<Rightarrow> n_pexpr" ("conc _")
  "_vexpr_seqapp"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_'<_'>")
  "_vexpr_seqcomp" :: "n_pexpr \<Rightarrow> pttrn \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("[_ | _ in @set _ &/ _]")
  "_vexpr_subseq"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_'(_, ..., _')")

translations
  "_vexpr_hd xs"        == "CONST vexpr_hd xs"
  "_vexpr_tl xs"        == "CONST vexpr_tl xs"
  "_vexpr_len xs"       == "CONST vexpr_len xs"
  "_vexpr_elems xs"     == "CONST vexpr_elems xs"
  "_vexpr_inds xs"      == "CONST vexpr_inds xs"
  "_vexpr_reverse xs"   == "CONST vexpr_reverse xs"
  "_vexpr_concat xs ys" == "CONST vexpr_concat xs ys"
  "_vexpr_conc xss"     == "CONST vexpr_conc xss"
  "_vexpr_seqapp xs i"  == "CONST vexpr_seqapp xs i"
  "_vexpr_seqcomp f x A P" == "CONST vexpr_seqcomp (\<lambda> x. (f, P)) A"
  "_vexpr_subseq xs m n"   == "CONST vexpr_subseq xs m n"
  
text {* Set Functions *}

term bPow

abbreviation "vexpr_in_set    \<equiv> Op2D' bset_member"
abbreviation "vexpr_not_in_set\<equiv> Op2D' bset_not_member"
abbreviation "vexpr_dunion    \<equiv> Op1D' BUnion"
abbreviation "vexpr_dinter    \<equiv> Op1D' BInter"
abbreviation "vexpr_subset    \<equiv> Op2D' bset_subset_eq"
abbreviation "vexpr_psubset   \<equiv> Op2D' bset_subset"
abbreviation "vexpr_fpower    \<equiv> Op1D' bPow"
abbreviation "vexpr_card      \<equiv> Op1D' bcard"
abbreviation "vexpr_lookup    \<equiv> Op2D (\<lambda> (x, m). DestBMap m x)"

lift_definition batLeastAtMost :: "int \<Rightarrow> int \<Rightarrow> int bset" is atLeastAtMost
  by (metis countable_member_bset)

definition vexpr_set_range :: "real vdme \<Rightarrow> real vdme \<Rightarrow> real bset vdme" where
"vexpr_set_range = Op2D' (\<lambda> m n. real `\<^sub>b batLeastAtMost (floor m) (floor n))"

definition vexpr_setcomp :: "('a \<Rightarrow> 'b::{vdmv,linorder} vdme * bool vdme) \<Rightarrow> 'a bset vdme \<Rightarrow> 'b bset vdme" where
"vexpr_setcomp FP eA = do { A <- eA
                          ; PA <- vdme_bset_iter A (\<lambda> x. do { c <- snd(FP(x)); if c then LitD {x}\<^sub>b else LitD {}\<^sub>b })
                          ; LA <- vdme_bset_iter (\<Union>\<^sub>b PA) (fst \<circ> FP)
                          ; LitD LA }"

declare vexpr_setcomp_def [evalp]

definition ForallSetD :: "'a bset vdme \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> bool vdme" where
"ForallSetD xs f = MkPExpr (\<lambda> b. (Some (\<forall> x \<in> DestBSet (the (\<lbrakk>xs\<rbrakk>\<^sub>* b)). \<lbrakk>f(x)\<rbrakk>\<^sub>* b = Some True)))"

definition ExistsSetD :: "'a bset vdme \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> bool vdme" where
"ExistsSetD xs f = MkPExpr (\<lambda> b. (Some (\<exists> x \<in> DestBSet (the (\<lbrakk>xs\<rbrakk>\<^sub>* b)). \<lbrakk>f(x)\<rbrakk>\<^sub>* b = Some True)))"

definition BCollect :: "('a \<Rightarrow> bool option) \<Rightarrow> 'a bset option" where
"BCollect p = (if (None \<notin> range p) then Some (bset_Collect (the \<circ> p)) else None)"

definition BCollect_ext :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> bool option) \<Rightarrow> 'b bset option" where
"BCollect_ext f p = do { xs \<leftarrow> BCollect p; bset_option (f `\<^sub>b xs) }"

lemma the_Some_image [simp]:
  "the ` Some ` xs = xs"
  by (auto simp add:image_iff)

lemma map_bset_Some [simp]: 
  "bset_option (Some `\<^sub>b xs) = Some xs"
  by (auto simp add: bset_option_def bset_image.rep_eq)

lemma the_comp_Some [simp]: 
  "the \<circ> (\<lambda>x. \<lfloor>p x\<rfloor>) = p"
  by (auto)

lemma FCollect_ext_Some [simp]: 
  "BCollect_ext Some xs = BCollect xs"
  apply (case_tac "BCollect xs")
  apply (auto simp add:BCollect_ext_def)
done

definition vcollect :: "('a \<Rightarrow> bool vdme) \<Rightarrow> 'a bset vdme" where
"vcollect P = MkPExpr (\<lambda> b. BCollect (\<lambda> x. \<lbrakk>P x\<rbrakk>\<^sub>*b))"

definition vcollect_ext :: "('a \<Rightarrow> 'b vdme) \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> 'b bset vdme" where
"vcollect_ext f P = MkPExpr (\<lambda> b. BCollect_ext (\<lambda> x. \<lbrakk>f(x)\<rbrakk>\<^sub>*b) (\<lambda> x. \<lbrakk>P(x)\<rbrakk>\<^sub>*b))"

abbreviation vcollect_ext_ty :: "('a \<Rightarrow> 'b vdme) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> bool vdme) \<Rightarrow> 'b bset vdme" where
"vcollect_ext_ty f A P \<equiv> vcollect_ext f (\<lambda> x. AndD (P(x)) (LitD (x \<in> A)))"

syntax
  "_vexpr_quotev"  :: "id \<Rightarrow> n_pexpr" ("<_>")
  "_vexpr_in_set"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "in @set" 50)
  "_vexpr_not_in_set"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "not in @set" 50)
  "_vexpr_union"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "union" 65)
  "_vexpr_inter"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "inter" 70)
  "_vexpr_dunion"  :: "n_pexpr \<Rightarrow> n_pexpr" ("dunion _")
  "_vexpr_dinter"  :: "n_pexpr \<Rightarrow> n_pexpr" ("dinter _")
  "_vexpr_sminus"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "setminus" 70)
  "_vexpr_subset"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "subset" 50) 
  "_vexpr_psubset" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "psubset" 50)
  "_vexpr_fpower"  :: "n_pexpr \<Rightarrow> n_pexpr" ("power _")
  "_vexpr_card"    :: "n_pexpr \<Rightarrow> n_pexpr" ("card _")
(*  "_vexpr_all_set" :: "pttrn \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("(3forall _ in @set _ @/ _)" [0, 0, 10] 10) *)
  "_vexpr_collect" :: "n_pexpr \<Rightarrow> pttrn \<Rightarrow> vty \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("{_ | _ : _ &/ _}")
  "_vexpr_setcomp" :: "n_pexpr \<Rightarrow> pttrn \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("{_ | _ in @set _ &/ _}")
  "_vexpr_setrange" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("{_, ..., _}")

translations
  "_vexpr_quotev x"    == "CONST LitD (CONST QuoD IDSTR(x))"
  "_vexpr_in_set x xs" == "CONST vexpr_in_set x xs"
  "_vexpr_not_in_set x xs" == "CONST vexpr_not_in_set x xs"
  "_vexpr_union x y"   == "CONST Op2D' CONST bset_union x y"
  "_vexpr_inter x y"   == "CONST Op2D' CONST bset_inter x y"
  "_vexpr_dunion xs"   == "CONST vexpr_dunion xs"
  "_vexpr_dinter xs"   == "CONST vexpr_dinter xs"
  "_vexpr_sminus x y"  == "CONST Op2D' CONST bset_minus x y"
  "_vexpr_subset x y"  == "CONST vexpr_subset x y"
  "_vexpr_psubset x y" == "CONST vexpr_psubset x y"
  "_vexpr_fpower xs"   == "CONST vexpr_fpower xs"
  "_vexpr_card x"      == "CONST vexpr_card x"

  (* Parse rules for forall set quantifiers *)

  "_vexpr_forall 
    (_vbinds 
      (_vsetbind 
        (_vidts x xs) A) bs) e" => "CONST ForallSetD A (\<lambda>x. _vexpr_forall 
                                                            (_vbinds (_vsetbind xs A) bs) e)"
  "_vexpr_forall 
    (_vbinds 
      (_vsetbind 
        (_vidt x) xs) bs) e" == "CONST ForallSetD xs (\<lambda>x. _vexpr_forall bs e)"
  "_vexpr_forall 
    (_vbind 
      (_vsetbind 
        (_vidts x xs) A)) e" => "CONST ForallSetD A (\<lambda>x. _vexpr_forall (_vbind (_vsetbind xs A)) e)"
  "_vexpr_forall 
    (_vbind 
      (_vsetbind 
        (_vidt x) xs)) e" == "CONST ForallSetD xs (\<lambda>x. e)"

  (* Parse rules for exists set quantifiers *)

  "_vexpr_exists 
    (_vbinds 
      (_vsetbind 
        (_vidts x xs) A) bs) e" => "CONST ExistsSetD A (\<lambda>x. _vexpr_exists 
                                                            (_vbinds (_vsetbind xs A) bs) e)"
  "_vexpr_exists 
    (_vbinds 
      (_vsetbind 
        (_vidt x) xs) bs) e" == "CONST ExistsSetD xs (\<lambda>x. _vexpr_exists bs e)"
  "_vexpr_exists 
    (_vbind 
      (_vsetbind 
        (_vidts x xs) A)) e" => "CONST ExistsSetD A (\<lambda>x. _vexpr_exists (_vbind (_vsetbind xs A)) e)"
  "_vexpr_exists 
    (_vbind 
      (_vsetbind 
        (_vidt x) xs)) e" == "CONST ExistsSetD xs (\<lambda>x. e)"

(*  "_vexpr_all_set x xs p" == "CONST ForallSetD xs (\<lambda>x. p)" *)
  "_vexpr_collect e x t p" => "CONST vcollect_ext_ty (\<lambda> x. e) t (\<lambda> x. p)"
  "_vexpr_setcomp f x A P" == "CONST vexpr_setcomp (\<lambda> x. (f, P)) A"
  "_vexpr_setrange m n"    == "CONST vexpr_set_range m n"

term "|forall x,y in @set {1,...,5} & true|"

term "|exists x,y in @set {1,...,5} & true|"

text {* Map Functions *}

definition "vexpr_mapupd \<equiv> Op3D' (\<lambda> m x v. bmap_upd m x (Some v))"

declare vexpr_mapupd_def [eval,evalp]

nonterminal vmaplets and vmaplet

syntax
  "_vmaplet"  :: "[n_pexpr, n_pexpr] => vmaplet"       ("_ /|->/ _")
  ""          :: "vmaplet => vmaplets"             ("_")
  "_VMaplets" :: "[vmaplet, vmaplets] => vmaplets" ("_,/ _")
  "_VMap"     :: "vmaplets => n_pexpr"               ("(1{_})") 

translations
  "_VMap (_VMaplets (_vmaplet x v) ms2)" == "CONST vexpr_mapupd (_VMap ms2) x v"
  "_VMap (_vmaplet x v)" == "CONST vexpr_mapupd (CONST LitD CONST bmempty) x v"

definition "vmapapp = (\<lambda> (m, k). DestBMap m k)"

definition vexpr_map_collect :: 
  "('a \<Rightarrow> ('b * 'c) vdme) \<Rightarrow> 'a bset vdme \<Rightarrow> ('b, 'c) bmap vdme" where
"vexpr_map_collect f A = do { A' <- A; g <- vdme_bset_iter A' f; LitD (graph_bmap g)}"

declare vmapapp_def [eval,evalp]
declare vexpr_map_collect_def [eval,evalp]

lemma dom_vmapapp [defined]:
  "dom vmapapp = {(m, k). k \<in>\<^sub>b bmdom(m)}"
  by (auto simp add:bmdom.rep_eq vmapapp_def)

abbreviation "fmap_plus f g \<equiv> (f + g :: ('a, 'b) fmap)"
 
abbreviation "vexpr_dom       \<equiv> Op1D' bmdom"
abbreviation "vexpr_rng       \<equiv> Op1D' bmran"
abbreviation "vexpr_mapcomp   \<equiv> Op2D' bmap_comp"
abbreviation "vexpr_mapempty  \<equiv> LitD  bmempty"
abbreviation "vexpr_munion    \<equiv> Op2D' bmap_add"
abbreviation "vexpr_moverride \<equiv> Op2D' bmap_add"
abbreviation "vexpr_domresto  \<equiv> Op2D' bmap_dom_res"
abbreviation "vexpr_domresfr  \<equiv> Op2D' bmap_dom_res_by"
abbreviation "vexpr_ranresto  \<equiv> Op2D' bmap_ran_res"
abbreviation "vexpr_ranresfr  \<equiv> Op2D' bmap_ran_res_by"
abbreviation "vexpr_mapapp    \<equiv> Op2D vmapapp"
abbreviation "vexpr_mapinv    \<equiv> Op1D' bmap_inv"

syntax
  "_vexpr_dom"       :: "n_pexpr \<Rightarrow> n_pexpr" ("dom _")
  "_vexpr_rng"       :: "n_pexpr \<Rightarrow> n_pexpr" ("rng _")
  "_vexpr_moverride" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "++" 65)
  "_vexpr_domresto"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "<:" 110)
  "_vexpr_domresfr"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "<-:" 110)
  "_vexpr_ranresto"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl ":>" 110)
  "_vexpr_ranresfr"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl ":->" 110)
  "_vexpr_mapcomp"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "comp" 55)  
  "_vexpr_mapinv"    :: "n_pexpr \<Rightarrow> n_pexpr" ("inverse _")
  "_vexpr_mapapp"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_[_]" [200,0] 200)
  "_vexpr_mapcomp"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> pttrn \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("{_ |-> _ | _ in @set _}")
  "_vexpr_mapempty"  :: "n_pexpr" ("{|->}")

translations
  "_vexpr_dom x"         == "CONST vexpr_dom x"
  "_vexpr_rng x"         == "CONST vexpr_rng x"
  "_vexpr_moverride f g" == "CONST vexpr_moverride f g"
  "_vexpr_domresto s f"  == "CONST vexpr_domresto s f"
  "_vexpr_domresfr s f"  == "CONST vexpr_domresfr s f"
  "_vexpr_ranresto s f"  == "CONST vexpr_ranresto s f"
  "_vexpr_ranresfr s f"  == "CONST vexpr_ranresfr s f"
  "_vexpr_mapinv m"      == "CONST vexpr_mapinv m"
  "_vexpr_mapapp m k"    == "CONST vexpr_mapapp m k"
  "_vexpr_mapcomp e f x A" == "CONST vexpr_map_collect (\<lambda> x. (CONST vexpr_prod e f)) A"
  "_vexpr_mapempty"      == "CONST vexpr_mapempty"

(*
term "|{x |-> (x * 2) + 5 | x in @set {1,...,5}}|"
*)

text {* Numeric Functions *}

abbreviation idiv :: "real \<Rightarrow> real \<Rightarrow> real" where
"idiv x y \<equiv> (floor x) div (floor y)"

abbreviation imod :: "real \<Rightarrow> real \<Rightarrow> real" where
"imod x y \<equiv> (floor x) mod (floor y)"

abbreviation vpower :: "real \<Rightarrow> real \<Rightarrow> real" where
"vpower x n \<equiv> x ^ (nat (floor n))"

abbreviation "vexpr_uminus    \<equiv> Op1D' (uminus :: real \<Rightarrow> real)"
abbreviation "vexpr_abs       \<equiv> Op1D' (abs :: real \<Rightarrow> real)"
abbreviation "vexpr_floor     \<equiv> Op1D' (floor :: real \<Rightarrow> real)"
abbreviation "vexpr_plus      \<equiv> Op2D' (op + :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_minus     \<equiv> Op2D' (op - :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_mult      \<equiv> Op2D' (op * :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_divide    \<equiv> Op2DR {(x,y). y \<noteq> 0} (op / :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_idiv      \<equiv> Op2DR {(x,y). y \<noteq> 0} idiv"
abbreviation "vexpr_imod      \<equiv> Op2DR {(x,y). y \<noteq> 0} imod"
abbreviation "vexpr_power     \<equiv> Op2D' (vpower :: real \<Rightarrow> real \<Rightarrow> real)"
abbreviation "vexpr_le        \<equiv> Op2D' (op \<le> :: real \<Rightarrow> real \<Rightarrow> bool)"
abbreviation "vexpr_less      \<equiv> Op2D' (op < :: real \<Rightarrow> real \<Rightarrow> bool)"
abbreviation "vexpr_ge        \<equiv> Op2D' (\<lambda> (x::real) y. y \<le> x)"
abbreviation "vexpr_greater   \<equiv> Op2D' (\<lambda> (x::real) y. y < x)"

syntax
  "_vexpr_uminus"  :: "n_pexpr \<Rightarrow> n_pexpr" ("- _" [81] 80)
  "_vexpr_abs"     :: "n_pexpr \<Rightarrow> n_pexpr" ("abs _")
  "_vexpr_floor"   :: "n_pexpr \<Rightarrow> n_pexpr" ("floor _")
  "_vexpr_plus"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "+" 30)
  "_vexpr_minus"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "-" 65)
  "_vexpr_mult"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "*" 70)
  "_vexpr_divide"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "'/" 70)
  "_vexpr_idiv"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "div" 70)
  "_vexpr_imod"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "mod" 70)
  "_vexpr_power"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "**" 70)
  "_vexpr_le"      :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "<=" 50)
  "_vexpr_less"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "<" 50)
  "_vexpr_ge"      :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix ">=" 50)
  "_vexpr_greater" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix ">" 50)

translations
  "_vexpr_uminus x"    == "CONST vexpr_uminus x"
  "_vexpr_abs x"       == "CONST vexpr_abs x"
  "_vexpr_floor x"     == "CONST vexpr_floor x"
  "_vexpr_plus x y"    == "CONST vexpr_plus x y"
  "_vexpr_minus x y"   == "CONST vexpr_minus x y"
  "_vexpr_mult x y"    == "CONST vexpr_mult x y"
  "_vexpr_divide x y"  == "CONST vexpr_divide x y"
  "_vexpr_idiv x y"    == "CONST vexpr_idiv x y"
  "_vexpr_imod x y"    == "CONST vexpr_imod x y"
  "_vexpr_power x y"   == "CONST vexpr_power x y"
  "_vexpr_le x y"      == "CONST vexpr_le x y"
  "_vexpr_less x y"    == "CONST vexpr_less x y"
  "_vexpr_ge x y"      == "CONST vexpr_le y x"
  "_vexpr_greater x y" == "CONST vexpr_less y x"

text {* Other constructs *}

(*
abbreviation "vexpr_and       \<equiv> Op2D' conj"
abbreviation "vexpr_or        \<equiv> Op2D' disj"
abbreviation "vexpr_implies   \<equiv> Op2D' implies"
*)

term "|$x <= $y|"

term "|$x in @set {1}|"

(* term "|^x^|" *)

term "|mk_prod(1, {})|"

term "|forall x:@nat1 & ^x^ > 1|"
term "|forall x in @set {1} & ^x^ > 5|"

lemma "|forall x:@nat1 & ^x^ > 0| = |true|"
  by (vdm_tac)

term "|$x > 0|"
term "\<parallel>@int inv x == ^x^ > 5\<parallel>"

lemma "|2 : (@int inv x == (^x^ < 5))| = |2 : @int|"
  by (vdm_tac)
  
lemma "|card {1,2,3}| = |3|"
  by (vdm_tac)

instantiation bset :: (DEFINED) DEFINED
begin

definition "defined_bset xs = (\<forall>x\<in>\<^sub>bxs. \<D> x)"

instance ..

end

text {* Some test lemmas ... *}

lemma "|{1} : @set of @int| = |{1}|"
  by (vdm_tac)

lemma "|{1,2,3} hasType @set of @nat| = |true|"
  by (vdm_tac)

lemma "|forall x : @int & ^x^ in @set {^x^}| = |true|"
  by (vdm_tac)

lemma "|true => false| = |false|"
  by (vdm_tac)

term "`x := ({1,2,3,4,5,6,7} union {8,9})`"

lemma "|{2} union {3}| = |{2,3}|"
  apply (simp add:evalp)
  oops

lemma "|card {2}| = |1|"
  by (vdm_tac)

lemma "|2 in @set {3,2}| = |true|"
  by (vdm_tac)

lemma "|5 <= 6| = |true|"
  by (vdm_tac)

lemma "|[2,1,5,4]<2>| = |5|"
  by (vdm_tac)

term "|{ &x + 1 | x : @nat & &x > 1}|"

lemma "|{ &x | x : @real & &x in @set &xs}| = |&xs|"
  apply (simp add:vcollect_ext_def evalp)
  apply (case_tac xs)
  apply (auto simp add:BCollect_def)
done

lemma BUnion_insert [simp]: 
  "\<Union>\<^sub>b (bset_insert x xs) = x \<union>\<^sub>b (\<Union>\<^sub>b xs)"
  by (auto)

lemma "|dunion({{1,3},{2},{3}})| = |{1,2,3}|"
  apply (vdm_tac)
  oops

declare defined_pexpr_def [evalp]

lemma Defined_option_bind_1 [dest]:
  "\<D> ((x::'a option) \<guillemotright>= f) \<Longrightarrow> \<D> x"
  by (case_tac x, simp_all)

lemma "|defn(@x union @y)| = |defn(@x) and defn(@y)|"
  apply (utp_poly_auto_tac)
  apply (drule_tac x="b" in spec)
  apply (metis Defined_option_bind_1)
  apply (metis (mono_tags) Defined_option_bind_1 Defined_option_elim bind_lunit)
  apply (metis (mono_tags) Defined_option_elim bind_lunit nDefined_option_elim option.distinct(1))
done

lemma "|defn(@x<@i>)| = |defn(@i) and defn(@x) and (@i < len @x)|"
  apply (vdm_auto_tac)
oops

(*
lemma "|defn(@x[@i])| = |defn(@i) and defn(@x) and (@i in @set (dom @x))|"
  apply (vdm_tac)
  apply (auto simp add:evalp Defined_WF_PEXPRESSION_def fdom.rep_eq)
  apply (case_tac "\<lbrakk>x\<rbrakk>\<^sub>*b = None")
  apply (simp)
  apply (case_tac "\<lbrakk>i\<rbrakk>\<^sub>*b = None")
oops
*)

term "|{1 |-> 2, 2 |-> 3} ++ {2 |-> 3}|"

(*
lemma "|forall x:@nat @ &x > 0 => (floor (5 / &x)) hasType @nat| = |true|"
  by (vdm_auto_tac)
*)

(* FIXME: Should the following really be safe rules? *)

lemma fdom_elim [elim!]:
  "\<lbrakk> k \<in> \<langle>fdom m\<rangle>\<^sub>f; \<And> v. \<lbrakk> \<langle>m\<rangle>\<^sub>m k = Some v; v \<in> \<langle>fran m\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (auto simp add:fdom.rep_eq fran.rep_eq)
  apply (metis ranI)
done

declare mimpliesI_Some [intro!]

declare bmdom.rep_eq [evalp]
declare bmran.rep_eq [evalp]


lemma "|forall m:@map @nat to @nat & forall i:@nat & &i in @set dom(&m) => &m[&i] hasType @nat| = |true|"
  apply (vdm_auto_tac)
  apply (metis contra_subsetD ranI)
done

term "|{5,...,9}|"

(* declare vexpr_set_range_def [evalp] *)

thm vexpr_set_range_def

lemma EvalD_vexpr_set_range [evalp]: 
  "\<lbrakk>vexpr_set_range (NumD m) (NumD n)\<rbrakk>\<^sub>*b = \<lfloor>real `\<^sub>b batLeastAtMost (hol_floor m) (hol_floor n)\<rfloor>"
  by (simp add:vexpr_set_range_def evalp)
  
lemma batLeastAtMost_simp_1 [simp]: 
  "m < n \<Longrightarrow> batLeastAtMost m n = bset_insert m (batLeastAtMost (m + 1) n)"
  by (auto simp add:batLeastAtMost.rep_eq)

lemma batLeastAtMost_simp_2 [simp]: 
  "batLeastAtMost m m = {m}\<^sub>b"
  by (auto simp add:batLeastAtMost.rep_eq)
  
lemma map_bset_option_empty [simp]:
  "bset_option {}\<^sub>b = Some {}\<^sub>b"
  by (simp add:bset_option_def)

lemma map_bset_option_simp [simp]:
  "bset_option (bset_insert x A) = do { v <- x; vs <- bset_option A; Some (bset_insert v vs) }"
  apply (auto simp add:bset_option_def)
  apply (case_tac x, auto simp add:bset_image.rep_eq)
done

lemma bset_image_insert [simp]: 
  "f `\<^sub>b (bset_insert x A) = bset_insert (f x) (f `\<^sub>b A)"
  by (transfer, auto)
  
lemma bset_insert_union [simp]:
  "bset_union (bset_insert x A) B = bset_insert x (bset_union A B)"
  by (transfer, auto)
  
lemma bset_empty_union [simp]:
  "bset_union bset_empty A = A"
  by (transfer, auto)
 
lemma BUnion_empty [simp]:
  "BUnion {}\<^sub>b = {}\<^sub>b"
  by (simp add: BUnion_rep_eq)
  
lemma BUnion_union [simp]:
  "BUnion (A \<union>\<^sub>b B) = BUnion A \<union>\<^sub>b BUnion B"
  by (auto simp add:BUnion_rep_eq)
  
lemma "|{ &x | x in @set {1,...,5} & &x > 0 }| = |{2,1,3,4,5}|"
  by (vdm_auto_tac)
  
declare BUnion_rep_eq [simp del]
  
lemma "|[ &x | x in @set {1,...,5} & true ]| = |[1,2,3,4,5]|"
  by (vdm_tac)

term "|[1,2,3,4,5](2,...,3)|"

lemma "|defn(&x / &n)| = |&n <> 0|"
  by (vdm_tac)

lemma "|<x> hasType <x> | <y> | <z>| = |true|"
  by (vdm_tac)

end
