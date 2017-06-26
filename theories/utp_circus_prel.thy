(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_circus_prel.thy                                                  *)
(* Authors: Simon Foster and Frank Zeyda (University of York, UK)             *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)
(* LAST REVIEWED: 23 June 2017 *)

section {* {\Circus} Preliminaries *}

theory utp_circus_prel
imports utp_theories_deep
begin

text {* Hide HOL's @{typ "'a rel"} type again (recall should do that)! *}

hide_type Relation.rel

subsection {* Channel Events *}

text {*
  The @{text "\<epsilon>(c)"} operator defined below yields the possible events for some
  channel @{text c}. It is useful to construct synchronisation sets of parallel
  compositions, for instance.
*}

definition events :: "('a, '\<epsilon>) chan \<Rightarrow> '\<epsilon> set" ("\<epsilon>'(_')") where
"events c = c ` UNIV"

subsection {* Mapper Lenses *}

text {*
  The parse translation below yields a heterogeneous mapping function for any
  record type. This is effectively lifting a function on its extension type to
  an update on the entire record. We note that the \<open>more_update\<close> function does
  something similar, but is not precisely suitable here since it only considers
  homogeneous functions, namely of type \<open>'a \<Rightarrow> 'a\<close> rather than \<open>'a \<Rightarrow> 'b\<close>.
*}

syntax "_map_ext" :: "id \<Rightarrow> logic" ("map'_ext[_]")

ML \<open>
  fun map_ext_tr [Free (name, _)] =
    let
      val extend = Free (name ^ ".extend", dummyT);
      val truncate = Free (name ^ ".truncate", dummyT);
      val more = Free (name ^ ".more", dummyT)
    in
      Abs ("f", dummyT,
      Abs ("r", dummyT,
        extend $ (truncate $ Bound 0) $ (Bound 1 $ (more $ (Bound 0)))))
    end
  | map_ext_tr _ = raise Match;
\<close>

parse_translation \<open>[(@{syntax_const "_map_ext"}, K map_ext_tr)]\<close>

subsubsection {* Mapping Functors *}

definition map_des_ext ::
  "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow>
   ('\<alpha> des \<Rightarrow> '\<beta> des)" where
[lens_defs]: "map_des_ext = map_ext[des_vars]"

definition map_rp_ext ::
  "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow>
   ('\<tau>::trace, '\<alpha>) rp_vars_scheme \<Rightarrow> ('\<tau>::trace, '\<beta>) rp_vars_scheme" where
[lens_defs]: "map_rp_ext = map_ext[rp_vars]"

definition map_rsp_st ::
  "('\<sigma> \<Rightarrow> '\<tau>) \<Rightarrow>
   ('\<sigma>, '\<alpha>) rsp_vars_scheme \<Rightarrow> ('\<tau>, '\<alpha>) rsp_vars_scheme" where
[lens_defs]:
"map_rsp_st f = (\<lambda>r. \<lparr>st\<^sub>v = f (rsp_vars.st\<^sub>v r), \<dots> = rsp_vars.more r\<rparr>)"

definition map_rsp_ext ::
  "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow>
   ('\<sigma>, '\<alpha>) rsp_vars_scheme \<Rightarrow> ('\<sigma>, '\<beta>) rsp_vars_scheme" where
[lens_defs]: "map_rsp_ext = map_ext[rsp_vars]"

definition map_csp_ext ::
  "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow>
   ('c, '\<alpha>) csp_vars_scheme \<Rightarrow> ('c, '\<beta>) csp_vars_scheme" where
[lens_defs]: "map_csp_ext = map_ext[csp_vars]"

subsubsection {* Lens Definitions *}

definition map_des_lens ::
  "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow> ('\<alpha> des \<Longrightarrow> '\<beta> des)" ("map'_des\<^sub>L") where
[lens_defs]:
"map_des_lens l = \<lparr>
  lens_get = map_des_ext (get\<^bsub>l\<^esub>),
  lens_put = map_des_ext o (put\<^bsub>l\<^esub>) o des_vars.more\<rparr>"

definition map_rp_lens ::
  "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow>
   (('\<tau>::trace, '\<alpha>) rp \<Longrightarrow> ('\<tau>::trace, '\<beta>) rp)" ("map'_rp\<^sub>L") where
[lens_defs]:
"map_rp_lens l = map_des\<^sub>L \<lparr>
  lens_get = map_rp_ext (get\<^bsub>l\<^esub>),
  lens_put = map_rp_ext o (put\<^bsub>l\<^esub>) o rp_vars.more\<rparr>"

definition map_rsp_lens ::
  "('\<alpha> \<Longrightarrow> '\<beta>) \<Rightarrow>
   (('\<sigma>, '\<tau>::trace, '\<alpha>) rsp \<Longrightarrow> ('\<sigma>, '\<tau>::trace, '\<beta>) rsp)" ("map'_rsp\<^sub>L") where
[lens_defs]:
"map_rsp_lens l = map_rp\<^sub>L \<lparr>
  lens_get = map_rsp_ext (get\<^bsub>l\<^esub>),
  lens_put = map_rsp_ext o (put\<^bsub>l\<^esub>) o rsp_vars.more\<rparr>"

definition map_rsp_st_lens ::
  "('\<sigma> \<Longrightarrow> '\<psi>) \<Rightarrow>
   (('\<sigma>, '\<tau>::trace, '\<alpha>) rsp \<Longrightarrow> ('\<psi>, '\<tau>::trace, '\<alpha>) rsp)" ("map'_rsp'_st\<^sub>L") where
[lens_defs]:
"map_rsp_st_lens l = map_rp\<^sub>L \<lparr>
  lens_get = map_rsp_st (get\<^bsub>l\<^esub>),
  lens_put = map_rsp_st o (put\<^bsub>l\<^esub>) o rsp_vars.st\<^sub>v\<rparr>"

subsubsection {* Lenses Laws *}

lemma vwb_map_des_lens:
"vwb_lens l \<Longrightarrow> vwb_lens (map_des\<^sub>L l)"
apply (unfold_locales)
apply (unfold map_des_lens_def map_des_ext_def)
apply (unfold des_vars.extend_def des_vars.truncate_def)
apply (auto)
done

lemma map_des_lens_id:
"map_des\<^sub>L 1\<^sub>L = 1\<^sub>L"
apply (unfold map_des_lens_def map_des_ext_def id_lens_def)
apply (unfold des_vars.extend_def des_vars.truncate_def)
apply (auto simp: fun_eq_iff)
done

lemma map_des_lens_comp:
"map_des\<^sub>L (l1 ;\<^sub>L l2) = (map_des\<^sub>L l1) ;\<^sub>L (map_des\<^sub>L l2)"
apply (unfold map_des_lens_def map_des_ext_def lens_comp_def)
apply (unfold des_vars.extend_def des_vars.truncate_def)
apply (auto simp: fun_eq_iff)
done

text {* More laws need to be proved here! [TODO] *}

subsection {* Proof Support *}

declare des_vars.extend_def [lens_defs]
declare des_vars.truncate_def [lens_defs]
declare rp_vars.extend_def [lens_defs]
declare rp_vars.truncate_def [lens_defs]
declare rsp_vars.extend_def [lens_defs]
declare rsp_vars.truncate_def [lens_defs]
declare csp_vars.extend_def [lens_defs]
declare csp_vars.truncate_def [lens_defs]

subsection {* State Hiding *}

text {* Move this to the theory @{theory utp_csp}. [TODO] *}

definition hide_state :: "('\<sigma>, '\<epsilon>) action \<Rightarrow> (unit, '\<epsilon>) action" where
"hide_state A = A \<restriction>\<^sub>p ((map_rsp_st\<^sub>L 0\<^sub>L) \<times>\<^sub>L (map_rsp_st\<^sub>L 0\<^sub>L))"

definition st_rel ::
  "'\<sigma> \<times> '\<sigma> \<Longrightarrow> ('\<sigma>, '\<tau>::trace, '\<alpha>) rsp \<times> ('\<sigma>, '\<tau>::trace, '\<alpha>) rsp" where
[lens_defs]: "st_rel = st \<times>\<^sub>L st"

text {* Note that the following lemma does not hold! *}

lemma hide_state_ex_cancel [simp]:
"hide_state (\<exists> {$st,$st\<acute>} \<bullet> P) = hide_state P"
apply (unfold hide_state_def)
apply (rel_simp)
oops

subsection {* Instantiations *}

text {* Move this to the theory @{theory utp_dvar}. [TODO] *}

instantiation vstore :: vst
begin
definition vstore_lens_vstore :: "vstore \<Longrightarrow> vstore" where
"vstore_lens_vstore = 1\<^sub>L"
instance
apply (intro_classes)
apply (unfold vstore_lens_vstore_def)
apply (rule id_vwb_lens)
done
end
end