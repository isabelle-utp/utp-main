(******************************************************************************)
(* Project: CML model for Isabelle/UTP                                        *)
(* File: utp_cml_functions.thy                                                *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* CML Function Library *}

theory utp_cml_functions
imports 
  utp_cml_types
  utp_cml_tac
  utp_cml_laws
  utp_cml_expr
  utp_cml_monad
begin

type_synonym 'a hol_set = "'a set"

text {* Set up the CML expression parser with API functions *}

text {* List Functions *}

definition seq_comp :: "('a \<Rightarrow> 'b::{vbasic,linorder}) \<Rightarrow> 'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'b list" where
"seq_comp f A P = flist (fset_comp f A P)"

lift_definition inds :: "'a list \<Rightarrow> nat fset" is
"\<lambda> xs. {1..length xs}" 
  by (simp add:fsets_def)

declare real_of_nat_Suc [evalp]

lemma inds_nil [simp]:
  "inds [] = \<lbrace>\<rbrace>"
  by (auto simp add:inds.rep_eq)

lemma inds_cons [simp]:
  "inds (x#xs) = finsert 1 (Suc `\<^sub>f (inds xs))"
  by (auto simp add:inds.rep_eq)

definition "vinds xs     \<equiv> real `\<^sub>f (inds xs)"
definition "vconc xs     \<equiv> foldr (op @) xs []"

declare vinds_def [eval,evalp]
declare vconc_def [eval,evalp]

definition "vexpr_hd      = Op1DR {x. x \<noteq> []} hd"
definition "vexpr_tl      = Op1DR {x. x \<noteq> []} tl"
definition "vexpr_seqapp  = Op2DR {(xs, i::real). i \<in> Nats \<and> nat (floor i) < length xs} (\<lambda> xs i. nth xs (nat (floor i)))"

definition vexpr_seqcomp :: "('a option \<Rightarrow> 'b::{vbasic,linorder} cmle * bool cmle) \<Rightarrow> 'a fset cmle \<Rightarrow> 'b list cmle" where
"vexpr_seqcomp FP eA = do { A <- eA
                          ; PA <- cmle_fset_iter A (\<lambda> x. do { c <- snd(FP(Some(x))); if c then LitD \<lbrace>x\<rbrace> else LitD \<lbrace>\<rbrace> })
                          ; LA <- cmle_fset_iter (\<Union>\<^sub>f PA) (fst \<circ> FP \<circ> Some)
                          ; LitD (flist LA) }"

definition vexpr_subseq :: "'a list cmle \<Rightarrow> real cmle \<Rightarrow> real cmle \<Rightarrow> 'a list cmle" where
"vexpr_subseq = Op3DR {(xs, m, n). m \<ge> 0 \<and> n \<ge> m} (\<lambda> xs m n. sublist xs {nat (floor m) .. nat (floor n)})"

declare vexpr_seqcomp_def [evalp]
declare vexpr_subseq_def [evalp]

declare vexpr_hd_def [eval,evalp]
declare vexpr_tl_def [eval,evalp]
declare vexpr_seqapp_def [eval,evalp]

abbreviation "vexpr_elems   \<equiv> Op1D' fset"
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
  "_vexpr_seqcomp" :: "n_pexpr \<Rightarrow> pttrn \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("[_ | _ in @set _ @/ _]")
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

abbreviation "vexpr_in_set    \<equiv> Op2D' (op \<in>\<^sub>f)"
abbreviation "vexpr_dunion    \<equiv> Op1D' FUnion"
abbreviation "vexpr_dinter    \<equiv> Op1D' FInter"
abbreviation "vexpr_subset    \<equiv> Op2D' (op \<subseteq>\<^sub>f)"
abbreviation "vexpr_psubset   \<equiv> Op2D' (op \<subset>\<^sub>f)"
abbreviation "vexpr_fpower    \<equiv> Op1D' FinPow"
abbreviation "vexpr_card      \<equiv> Op1D' fcard"
abbreviation "vexpr_lookup    \<equiv> Op2D (\<lambda> (x, m). \<langle>m\<rangle>\<^sub>m x)"

lift_definition fatLeastAtMost :: "int \<Rightarrow> int \<Rightarrow> int fset" is atLeastAtMost
  by (auto simp add:fsets_def)

definition vexpr_set_range :: "real cmle \<Rightarrow> real cmle \<Rightarrow> real fset cmle" where
"vexpr_set_range = Op2D' (\<lambda> m n. real `\<^sub>f fatLeastAtMost (floor m) (floor n))"

definition vexpr_setcomp :: "('a option \<Rightarrow> 'b::{vbasic,linorder} cmle * bool cmle) \<Rightarrow> 'a fset cmle \<Rightarrow> 'b fset cmle" where
"vexpr_setcomp FP eA = do { A <- eA
                          ; PA <- cmle_fset_iter A (\<lambda> x. do { c <- snd(FP(Some(x))); if c then LitD \<lbrace>x\<rbrace> else LitD \<lbrace>\<rbrace> })
                          ; LA <- cmle_fset_iter (\<Union>\<^sub>f PA) (fst \<circ> FP \<circ> Some)
                          ; LitD LA }"

declare vexpr_setcomp_def [evalp]

definition ForallSetD :: "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"ForallSetD xs f = MkPExpr (\<lambda> b. (Some (\<forall> x \<in> \<langle>the (\<lbrakk>xs\<rbrakk>\<^sub>* b)\<rangle>\<^sub>f. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)))"

definition ExistsSetD :: "'a fset cmle \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> bool cmle" where
"ExistsSetD xs f = MkPExpr (\<lambda> b. (Some (\<exists> x \<in> \<langle>the (\<lbrakk>xs\<rbrakk>\<^sub>* b)\<rangle>\<^sub>f. \<lbrakk>f (Some x)\<rbrakk>\<^sub>* b = Some True)))"

definition FCollect :: "('a \<Rightarrow> bool option) \<Rightarrow> 'a fset option" where
"FCollect p = (if (finite (Collect (the \<circ> p)) \<and> None \<notin> range p) then Some (Abs_fset (Collect (the \<circ> p))) else None)"

definition FCollect_ext :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> bool option) \<Rightarrow> 'b fset option" where
"FCollect_ext f p = do { xs \<leftarrow> FCollect p; map_fset_option (f `\<^sub>f xs) }"

lemma the_Some_image [simp]:
  "the ` Some ` xs = xs"
  by (auto simp add:image_iff)

lemma map_fset_Some [simp]: 
  "map_fset_option (Some `\<^sub>f xs) = Some xs"
  by (auto simp add:map_fset_option_def)

lemma the_comp_Some [simp]: 
  "the \<circ> (\<lambda>x. \<lfloor>p x\<rfloor>) = p"
  by (auto)

lemma FCollect_ext_Some [simp]: 
  "FCollect_ext Some xs = FCollect xs"
  apply (case_tac "FCollect xs")
  apply (auto simp add:FCollect_ext_def)
done

definition vcollect :: "('a \<Rightarrow> bool cmle) \<Rightarrow> 'a fset cmle" where
"vcollect P = MkPExpr (\<lambda> b. FCollect (\<lambda> x. \<lbrakk>P x\<rbrakk>\<^sub>*b))"

definition vcollect_ext :: "('a \<Rightarrow> 'b cmle) \<Rightarrow> ('a \<Rightarrow> bool cmle) \<Rightarrow> 'b fset cmle" where
"vcollect_ext f P = MkPExpr (\<lambda> b. FCollect_ext (\<lambda> x. \<lbrakk>f(x)\<rbrakk>\<^sub>*b) (\<lambda> x. \<lbrakk>P(x)\<rbrakk>\<^sub>*b))"

abbreviation vcollect_ext_ty :: "('a option \<Rightarrow> 'b cmle) \<Rightarrow> 'a set \<Rightarrow> ('a option \<Rightarrow> bool cmle) \<Rightarrow> 'b fset cmle" where
"vcollect_ext_ty f A P \<equiv> vcollect_ext (f \<circ> Some) (\<lambda> x. AndD (P (Some x)) (LitD (x \<in> A)))"

syntax
  "_vexpr_quotev"  :: "string \<Rightarrow> n_pexpr" ("<_>")
  "_vexpr_in_set"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "in @set" 50)
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
  "_vexpr_collect" :: "n_pexpr \<Rightarrow> pttrn \<Rightarrow> vty \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("{_ | _ : _ @/ _}")
  "_vexpr_setcomp" :: "n_pexpr \<Rightarrow> pttrn \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("{_ | _ in @set _ @/ _}")
  "_vexpr_setrange" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("{_, ..., _}")

translations
  "_vexpr_quotev x"    == "CONST LitD (CONST QuoteD x)"
  "_vexpr_in_set x xs" == "CONST vexpr_in_set x xs"
  "_vexpr_union x y"   == "CONST Op2D' CONST funion x y"
  "_vexpr_inter x y"   == "CONST Op2D' CONST finter x y"
  "_vexpr_dunion xs"   == "CONST vexpr_dunion xs"
  "_vexpr_dinter xs"   == "CONST vexpr_dinter xs"
  "_vexpr_sminus x y"  == "CONST Op2D' CONST fminus x y"
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

term "|forall x,y in @set {1,...,5} @ true|"

term "|exists x,y in @set {1,...,5} @ true|"

text {* Map Functions *}

definition "vexpr_mapupd \<equiv> Op3D' (\<lambda> m x v. fmap_upd m x (Some v))"

declare vexpr_mapupd_def [eval,evalp]

nonterminal vmaplets and vmaplet

syntax
  "_vmaplet"  :: "[n_pexpr, n_pexpr] => vmaplet"       ("_ /|->/ _")
  ""          :: "vmaplet => vmaplets"             ("_")
  "_VMaplets" :: "[vmaplet, vmaplets] => vmaplets" ("_,/ _")
  "_VMap"     :: "vmaplets => n_pexpr"               ("(1{_})")

translations
  "_VMap (_VMaplets (_vmaplet x v) ms2)" == "CONST vexpr_mapupd (_VMap ms2) x v"
  "_VMap (_vmaplet x v)" == "CONST vexpr_mapupd (CONST LitD CONST fmempty) x v"

definition
  ranres :: "('a ~=> 'b) => 'b set => ('a ~=> 'b)" where
"ranres m ys = (\<lambda> x. case m x of None \<Rightarrow> None | Some y \<Rightarrow> (if (y \<in> ys) then Some y else None))"

declare ranres_def [eval,evalp]

lemma finite_dom_map_of:
  fixes f :: "('a::linorder ~=> 'b)"
  assumes "finite (dom f)" 
  shows "\<exists> xs. f = map_of xs"
  by (metis Abs_fmap_inv assms fmap_list_inv list_fmap.rep_eq)

lemma map_comp_dom: "dom (g \<circ>\<^sub>m f) \<subseteq> dom f"
  by (metis (lifting, full_types) Collect_mono dom_def map_comp_simps(1))

lift_definition fmap_comp :: "('b, 'c) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'c) fmap"
is "map_comp" 
  apply (auto simp add:fmaps_def)
  apply (metis finite_subset map_comp_dom)
done

lemma finite_dom_graph_map:
  "finite A \<Longrightarrow> finite (dom (graph_map A))"
  by (simp add:graph_map_def dom_def)

lift_definition fgraph_fmap :: "('a * 'b) fset \<Rightarrow> ('a, 'b) fmap" is graph_map
  by (simp add:fmaps_def, metis finite_dom_graph_map fsets_def mem_Collect_eq)

lift_definition fmap_collect :: "('a \<Rightarrow> 'b * 'c) \<Rightarrow> 'a fset \<Rightarrow> ('b, 'c) fmap"
is "\<lambda> f A. graph_map (f ` A)"
  by (auto simp add:fmaps_def, metis finite_dom_graph_map finite_imageI fsets_def mem_Collect_eq)

lift_definition fmap_add :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" 
is "map_add" by (simp add:fmaps_def)

lift_definition fmap_domr :: "'a fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" 
is "\<lambda> s f. restrict_map f s" by (simp add:fmaps_def)

lift_definition fmap_inv :: "('a, 'b) fmap \<Rightarrow> ('b, 'a) fmap" 
is "map_inv" by (simp add:fmaps_def)

definition fmap_domr' :: "'a fset \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" where
"fmap_domr' s f = fmap_domr (fdom f -\<^sub>f s) f"

definition "vmapapp = (\<lambda> (m, k). Rep_fmap m k)"

definition vexpr_map_collect :: 
  "('a \<Rightarrow> ('b * 'c) cmle) \<Rightarrow> 'a fset cmle \<Rightarrow> ('b, 'c) fmap cmle" where
"vexpr_map_collect f A = do { A' <- A; g <- cmle_fset_iter A' f; LitD (fgraph_fmap g)}"

declare vmapapp_def [eval,evalp]
declare vexpr_map_collect_def [eval,evalp]

lemma dom_vmapapp [defined]:
  "dom vmapapp = {(m, k). k \<in>\<^sub>f fdom(m)}"
  by (auto simp add:fdom.rep_eq vmapapp_def)

abbreviation "vexpr_dom       \<equiv> Op1D' fdom"
abbreviation "vexpr_rng       \<equiv> Op1D' fran"
abbreviation "vexpr_mapcomp   \<equiv> Op2D' fmap_comp"
abbreviation "vexpr_munion    \<equiv> Op2D' fmap_add"
abbreviation "vexpr_moverride \<equiv> Op2D' fmap_add"
abbreviation "vexpr_domresto  \<equiv> Op2D' fmap_domr"
abbreviation "vexpr_domresfr  \<equiv> Op2D' fmap_domr'"
abbreviation "vexpr_mapapp    \<equiv> Op2D vmapapp"
abbreviation "vexpr_mapinv    \<equiv> Op1D' fmap_inv"

syntax
  "_vexpr_dom"       :: "n_pexpr \<Rightarrow> n_pexpr" ("dom _")
  "_vexpr_rng"       :: "n_pexpr \<Rightarrow> n_pexpr" ("rng _")
  "_vexpr_moverride" :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixr "++" 65)
  "_vexpr_domresto"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "<:" 110)
  "_vexpr_domresfr"  :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "<-:" 110)
  "_vexpr_mapcomp"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infixl "comp" 55)  
  "_vexpr_mapinv"    :: "n_pexpr \<Rightarrow> n_pexpr" ("inverse _")
  "_vexpr_mapapp"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("_[_]")
  "_vexpr_mapcomp"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> pttrn \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" ("{_ |-> _ | _ in @set _}")

translations
  "_vexpr_dom x"         == "CONST vexpr_dom x"
  "_vexpr_rng x"         == "CONST vexpr_rng x"
  "_vexpr_moverride f g" == "CONST vexpr_moverride f g"
  "_vexpr_domresto s f"  == "CONST vexpr_domresto s f"
  "_vexpr_domresfr s f"  == "CONST vexpr_domresfr s f"
  "_vexpr_mapinv m"      == "CONST vexpr_mapinv m"
  "_vexpr_mapapp m k"    == "CONST vexpr_mapapp m k"
  "_vexpr_mapcomp e f x A" == "CONST vexpr_map_collect (\<lambda> x. (CONST vexpr_prod e f)) A"

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
  "_vexpr_plus"    :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "+" 30)
  "_vexpr_minus"   :: "n_pexpr \<Rightarrow> n_pexpr \<Rightarrow> n_pexpr" (infix "-" 65)
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

term "|$x in @set {<1>}|"

(* term "|^x^|" *)

term "|mk_prod(1, {})|"

term "|forall x:@nat1 @ ^x^ > 1|"
term "|forall x in @set {1} @ ^x^ > 5|"

lemma "|forall x:@nat1 @ ^x^ > 0| = |true|"
  by (cml_tac)

term "|$x > 0|"
term "\<parallel>@int inv x == ^x^ > 5\<parallel>"

lemma "|2 : (@int inv x == (^x^ < 5))| = |2 : @int|"
  by (cml_tac)

lemma "|card {1,2,3}| = |3|"
  by (cml_tac)

instantiation fset :: (DEFINED) DEFINED
begin

definition "Defined_fset xs = (\<forall>x\<in>\<^sub>fxs. \<D> x)"

instance ..

end

text {* Some test lemmas ... *}

lemma "|{1} : @set of @int| = |{1}|"
  by (cml_tac)

lemma "|{1,2,3} hasType @set of @nat| = |true|"
  by (cml_tac)

lemma "|forall x : @int @ ^x^ in @set {^x^}| = |true|"
  by (cml_tac)

lemma "|true => false| = |false|"
  by (cml_tac)

term "`x := ({1,2,3,4,5,6,7} union {8,9})`"

lemma "|{2} union {3}| = |{2,3}|"
  by (simp add:evalp)

lemma "|card {2}| = |1|"
  by (cml_tac)

lemma "|2 in @set {3,2}| = |true|"
  by (cml_tac)

lemma "|5 <= 6| = |true|"
  by (cml_tac)

lemma "|[2,1,5,4]<2>| = |5|"
  by (cml_tac)

term "|{ &x + 1 | x : @nat @ &x > 1}|"

lemma "|{ &x | x : @real @ &x in @set &xs}| = |&xs|"
  apply (simp add:vcollect_ext_def evalp)
  apply (case_tac xs)
  apply (auto simp add:FCollect_def)
done

lemma FUnion_finsert [simp]: 
  "\<Union>\<^sub>f (finsert x xs) = x \<union>\<^sub>f (\<Union>\<^sub>f xs)"
  by (auto)

lemma "|dunion({{1,3},{2},{3}})| = |{1,2,3}|"
  by (cml_tac)


declare Defined_pexpr_def [evalp]

lemma Defined_option_bind_1 [dest]:
  "\<D> ((x::'a option) \<guillemotright>= f) \<Longrightarrow> \<D> x"
  by (case_tac x, simp_all)

lemma "|defn(@x union @y)| = |defn(@x) and defn(@y)|"
  apply (utp_poly_auto_tac)
  apply (drule_tac x="b" in spec)
  apply (metis (mono_tags) Defined_option_bind_1 Defined_option_elim bind_lunit)
  apply (metis Defined_option.simps(2) Defined_option_elim Some_defined bind_lunit)
done


lemma "|defn(@x<@i>)| = |defn(@i) and defn(@x) and (@i < len @x)|"
  apply (cml_auto_tac)
oops

(*
lemma "|defn(@x[@i])| = |defn(@i) and defn(@x) and (@i in @set (dom @x))|"
  apply (cml_tac)
  apply (auto simp add:evalp Defined_WF_PEXPRESSION_def fdom.rep_eq)
  apply (case_tac "\<lbrakk>x\<rbrakk>\<^sub>*b = None")
  apply (simp)
  apply (case_tac "\<lbrakk>i\<rbrakk>\<^sub>*b = None")
oops
*)

term "|{1 |-> 2, 2 |-> 3} ++ {2 |-> 3}|"

lemma "|forall x:@nat @ &x > 0 => (floor (5 / &x)) hasType @nat| = |true|"
  by (cml_auto_tac)

(* FIXME: Should the following really be safe rules? *)

lemma fdom_elim [elim!]:
  "\<lbrakk> k \<in> \<langle>fdom m\<rangle>\<^sub>f; \<And> v. \<lbrakk> \<langle>m\<rangle>\<^sub>m k = Some v; v \<in> \<langle>fran m\<rangle>\<^sub>f \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (auto simp add:fdom.rep_eq fran.rep_eq)
  apply (metis ranI)
done

declare mimpliesI_Some [intro!]

lemma "|forall m:@map @nat to @nat @ forall i:@nat @ &i in @set dom(&m) => &m[&i] hasType @nat| = |true|"
  by (cml_auto_tac)

term "|{5,...,9}|"

declare vexpr_set_range_def [evalp]

thm cmle_fset_iter_def


lemma fatLeastAtMost_simp_1 [simp]: 
  "m < n \<Longrightarrow> fatLeastAtMost m n = finsert m (fatLeastAtMost (m + 1) n)"
  by (auto simp add:fatLeastAtMost.rep_eq)

lemma fatLeastAtMost_simp_2 [simp]: 
  "fatLeastAtMost m m = \<lbrace>m\<rbrace>"
  by (auto simp add:fatLeastAtMost.rep_eq)

lemma map_fset_option_empty [simp]:
  "map_fset_option \<lbrace>\<rbrace> = Some \<lbrace>\<rbrace>"
  by (simp add:map_fset_option_def)

lemma map_fset_option_simp [simp]:
  "map_fset_option (finsert x A) = do { v <- x; vs <- map_fset_option A; Some (finsert v vs) }"
  apply (auto simp add:map_fset_option_def)
  apply (metis bind_lunit not_Some_eq the.simps)
done

lemma "|{ &x | x in @set {1,...,5} @ & x > 0 }| = |{2,1,3,4,5}|"
  by (cml_tac)

lemma "|[ &x | x in @set {1,...,5} @ true ]| = |[1,2,3,4,5]|"
  by (cml_tac)

term "|[1,2,3,4,5](2,...,3)|"

end
