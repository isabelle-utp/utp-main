(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Lens_Extra.thy                                                       *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Extra Lens Laws \<close>

theory Lens_Extra
  imports 
    Optics.Lenses 
    "HOL-Eisbach.Eisbach"
begin

lemma list_augment_last [simp]:
  "list_augment (xs @ [y]) (length xs) z = xs @ [z]"
  by (induct xs, simp_all)

lemma lens_get_put_quasi_commute:
  "\<lbrakk> vwb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> s v) = put\<^bsub>X /\<^sub>L Y\<^esub> (get\<^bsub>Y\<^esub> s) v"
proof -
  assume a1: "vwb_lens Y"
  assume a2: "X \<subseteq>\<^sub>L Y"
  have "\<And>l la. put\<^bsub>l ;\<^sub>L la\<^esub> = (\<lambda>b c. put\<^bsub>la\<^esub> (b::'b) (put\<^bsub>l\<^esub> (get\<^bsub>la\<^esub> b::'a) (c::'c)))"
    by (simp add: lens_comp_def)
  then have "\<And>l la b c. get\<^bsub>l\<^esub> (put\<^bsub>la ;\<^sub>L l\<^esub> (b::'b) (c::'c)) = put\<^bsub>la\<^esub> (get\<^bsub>l\<^esub> b::'a) c \<or> \<not> weak_lens l"
    by force
  then show ?thesis
    using a2 a1 by (metis lens_quotient_comp vwb_lens_wb wb_lens_def)
qed
  
lemma lens_put_of_quotient:
  "\<lbrakk> vwb_lens Y; X \<subseteq>\<^sub>L Y \<rbrakk> \<Longrightarrow> put\<^bsub>Y\<^esub> s (put\<^bsub>X /\<^sub>L Y\<^esub> v\<^sub>2 v\<^sub>1) = put\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> s v\<^sub>2) v\<^sub>1"
proof -
  assume a1: "vwb_lens Y"
  assume a2: "X \<subseteq>\<^sub>L Y"
  have f3: "\<And>l b. put\<^bsub>l\<^esub> (b::'b) (get\<^bsub>l\<^esub> b::'a) = b \<or> \<not> vwb_lens l"
    by force
  have f4: "\<And>b c. put\<^bsub>X /\<^sub>L Y\<^esub> (get\<^bsub>Y\<^esub> b) c = get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> b c)"
    using a2 a1 by (simp add: lens_get_put_quasi_commute)
  have "\<And>b c a. put\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> b c) a = put\<^bsub>Y\<^esub> b a"
    using a2 a1 by (simp add: sublens_put_put)
  then show ?thesis
    using f4 f3 a1 by (metis mwb_lens.put_put mwb_lens_def vwb_lens_mwb weak_lens.put_get)
qed

lemma lens_override_idem [simp]:
  "vwb_lens X \<Longrightarrow> S \<oplus>\<^sub>L S on X = S"
  by (simp add: lens_override_def)
        
lemma lens_override_put_right_in:
  "\<lbrakk> vwb_lens A; X \<subseteq>\<^sub>L A \<rbrakk> \<Longrightarrow> S\<^sub>1 \<oplus>\<^sub>L (put\<^bsub>X\<^esub> S\<^sub>2 v) on A = put\<^bsub>X\<^esub> (S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on A) v"
  by (simp add: lens_override_def lens_get_put_quasi_commute lens_put_of_quotient)

lemma lens_override_put_right_out:
  "\<lbrakk> vwb_lens A; X \<bowtie> A \<rbrakk> \<Longrightarrow> S\<^sub>1 \<oplus>\<^sub>L (put\<^bsub>X\<^esub> S\<^sub>2 v) on A = (S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on A)"
  by (simp add: lens_override_def  lens_indep.lens_put_irr2)    

lemma bij_lens_intro: "\<lbrakk> weak_lens L; \<And> \<sigma> \<rho>. put\<^bsub>L\<^esub> \<sigma> (get\<^bsub>L\<^esub> \<rho>) = \<rho> \<rbrakk> \<Longrightarrow> bij_lens L"
  using bij_lens.intro bij_lens_axioms.intro by blast

subsection \<open>Mapper Lenses\<close>

definition lmap_lens :: 
  "(('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> ('\<gamma> \<Rightarrow> '\<delta>)) \<Rightarrow> 
   (('\<beta> \<Rightarrow> '\<alpha>) \<Rightarrow> '\<delta> \<Rightarrow> '\<gamma>) \<Rightarrow> 
   ('\<gamma> \<Rightarrow> '\<alpha>) \<Rightarrow> 
   ('\<beta> \<Longrightarrow> '\<alpha>) \<Rightarrow> 
   ('\<delta> \<Longrightarrow> '\<gamma>)" where
  [lens_defs]:
  "lmap_lens f g h l = \<lparr>
  lens_get = f (get\<^bsub>l\<^esub>),
  lens_put = g o (put\<^bsub>l\<^esub>) o h \<rparr>"
  
text \<open>
  The parse translation below yields a heterogeneous mapping lens for any
  record type. This achieved through the utility function above that
  constructs a functorial lens. This takes as input a heterogeneous mapping
  function that lifts a function on a record's extension type to an update
  on the entire record, and also the record's ``more'' function. The first input
  is given twice as it has different polymorphic types, being effectively
  a type functor construction which are not explicitly supported by HOL. We note 
  that the \<open>more_update\<close> function does something similar to the extension lifting, 
  but is not precisely suitable here since it only considers homogeneous functions, 
  namely of type \<open>'a \<Rightarrow> 'a\<close> rather than \<open>'a \<Rightarrow> 'b\<close>.
\<close>
  
syntax 
  "_lmap" :: "id \<Rightarrow> logic" ("lmap[_]")

ML \<open>
  fun lmap_tr [Free (name, _)] =
    let
      val extend = Free (name ^ ".extend", dummyT);
      val truncate = Free (name ^ ".truncate", dummyT);
      val more = Free (name ^ ".more", dummyT);
      val map_ext = Abs ("f", dummyT,
                    Abs ("r", dummyT,
                      extend $ (truncate $ Bound 0) $ (Bound 1 $ (more $ (Bound 0)))))

    in
      Const (@{const_syntax "lmap_lens"}, dummyT) $ map_ext $ map_ext $ more
    end
  | lmap_tr _ = raise Match;
\<close>

parse_translation \<open>[(@{syntax_const "_lmap"}, K lmap_tr)]\<close>  

subsection \<open> Tactic \<close>

text \<open> A simple tactic for simplifying lens expressions \<close>

declare split_paired_all [alpha_splits]

method lens_simp = (simp add: alpha_splits lens_defs prod.case_eq_if)

end