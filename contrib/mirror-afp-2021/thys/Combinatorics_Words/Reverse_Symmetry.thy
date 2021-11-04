(*  Title:      CoW/Reverse_Symmetry.thy
    Author:     Martin Raška, Charles University
*)

theory Reverse_Symmetry
  imports Main
begin

chapter "Reverse symmetry"

text \<open>This theory deals with a mechanism which produces new facts on lists from already known facts
by the reverse symmetry of lists, induced by the mapping @{term rev}.
It constructs the rule attribute ``reversed'' which produces the symmetrical fact using so-called
reversal rules, which are rewriting rules that may be applied to obtain the symmetrical fact.
An example of such a reversal rule is the already existing @{thm rev_append[symmetric, no_vars]}.
Some additional reversal rules are given in this theory.

The symmetrical fact 'A[reversed]' is constructed from the fact 'A' in the following manner:
  1. each schematic variable @{term "xs::'a list"} of type @{typ "'a list"}
is instantiated by @{term "rev xs"};
  2. constant Nil is substituted by @{term "rev Nil"};
  3. each quantification of @{typ "'a list"} type variable @{term "\<And>(xs::'a list). P xs"}
is substituted by (logically equivalent) quantification @{term "\<And>xs. P (rev xs)"},
similarly for $\forall$, $\exists$ and $\exists!$ quantifiers; each bounded quantification of @{typ "'a list"} type
variable @{term "\<forall>(xs::'a list) \<in> A. P xs"} is substituted by (logically equivalent)
quantification @{term "\<forall>xs\<in>rev ` A. P (rev xs)"}, similarly for bounded $\exists$ quantifier;
  4. simultaneous rewrites according to a the current list of reversal rules are performed;
  5. final correctional rewrites related to reversion of @{const "Cons"} are performed.

List of reversal rules is maintained by declaration attribute ``reversal\_rule'' with standard
``add'' and ``del'' options. 

See examples at the end of the file.
\<close>


section \<open>Quantifications and maps\<close>

lemma all_surj_conv: assumes "surj f" shows "(\<And>x. PROP P (f x)) \<equiv> (\<And>y. PROP P y)"
proof
  fix y assume "\<And>x. PROP P (f x)"
  then have "PROP P (f (inv f y))".
  then show "PROP P y" unfolding surj_f_inv_f[OF assms].
qed

lemma All_surj_conv: assumes "surj f" shows "(\<forall>x. P (f x)) \<longleftrightarrow> (\<forall>y. P y)"
proof (intro iffI allI)
  fix y assume "\<forall>x. P (f x)"
  then have "P (f (inv f y))"..
  then show "P y" unfolding surj_f_inv_f[OF assms].
qed simp

lemma Ex_surj_conv: assumes "surj f" shows "(\<exists>x. P (f x)) \<longleftrightarrow> (\<exists>y. P y)"
proof
  assume "\<exists>x. P (f x)"
  then obtain x where "P (f x)"..
  then show "\<exists>x. P x"..
next 
  assume "\<exists>y. P y"
  then obtain y where "P y"..
  then have "P (f (inv f y))" unfolding surj_f_inv_f[OF assms].
  then show "\<exists>x. P (f x)"..
qed

lemma Ex1_bij_conv: assumes "bij f" shows "(\<exists>!x. P (f x)) \<longleftrightarrow> (\<exists>!y. P y)"
proof
  have imp: "\<exists>!y. Q y" if bij: "bij g" and ex1: "\<exists>!x. Q (g x)" for g Q
  proof -
    from ex1E[OF ex1, rule_format]
    obtain x where ex: "Q (g x)" and uniq: "\<And>x'. Q (g x') \<Longrightarrow> x' = x" by blast
    {
      fix y assume "Q y"
      then have "Q (g (inv g y))" unfolding surj_f_inv_f[OF bij_is_surj[OF bij]].
      from uniq[OF this] have "x = inv g y"..
      then have "y = g x" unfolding bij_inv_eq_iff[OF bij]..
    }
    with ex show "\<exists>!y. Q y"..
  qed
  show "\<exists>!x. P (f x) \<Longrightarrow> \<exists>!y. P y" using imp[OF assms].
  assume "\<exists>!y. P y"
  then have "\<exists>!y. P (f (inv f y))" unfolding surj_f_inv_f[OF bij_is_surj[OF assms]].
  from imp[OF bij_imp_bij_inv[OF assms] this]
  show "\<exists>!x. P (f x)".
qed

lemma Ball_inj_conv: assumes "inj f" shows "(\<forall>y\<in>f ` A. P (inv f y)) \<longleftrightarrow> (\<forall>x\<in>A. P x)"
  using ball_simps(9)[of f A "\<lambda>y. P (inv f y)"] unfolding inv_f_f[OF assms].

lemma Bex_inj_conv: assumes "inj f" shows "(\<exists>y\<in>f ` A. P (inv f y)) \<longleftrightarrow> (\<exists>x\<in>A. P x)"
  using bex_simps(7)[of f A "\<lambda>y. P (inv f y)"] unfolding inv_f_f[OF assms].

subsection \<open>Quantifications and reverse\<close>

lemma rev_involution: "rev \<circ> rev = id"
  by auto

lemma rev_bij: "bij rev" 
  using o_bij[OF rev_involution rev_involution].

lemma rev_inv: "inv rev = rev"
  using inv_unique_comp[OF rev_involution rev_involution].

lemmas all_rev_conv = all_surj_conv[OF bij_is_surj[OF rev_bij]]
   and All_rev_conv = All_surj_conv[OF bij_is_surj[OF rev_bij]]
   and Ex_rev_conv = Ex_surj_conv[OF bij_is_surj[OF rev_bij]]
   and Ex1_rev_conv = Ex1_bij_conv[OF rev_bij]
   and Ball_rev_conv = Ball_inj_conv[OF bij_is_inj[OF rev_bij], unfolded rev_inv]
   and Bex_rev_conv = Bex_inj_conv[OF bij_is_inj[OF rev_bij], unfolded rev_inv]

section \<open>Attributes\<close>

context
begin

subsection \<open>Definitons of reverse wrapers\<close>

private definition rev_Nil_wrap :: "'a list"
  where "rev_Nil_wrap = rev Nil" 

private definition all_rev_wrap :: "('a list \<Rightarrow> prop) \<Rightarrow> prop"
  where "all_rev_wrap P \<equiv> (\<And>x. PROP P (rev x))"

private definition All_rev_wrap :: "('a list \<Rightarrow> bool) \<Rightarrow> bool"
  where "All_rev_wrap P = (\<forall>x. P (rev x))"

private definition Ex_rev_wrap :: "('a list \<Rightarrow> bool) \<Rightarrow> bool"
  where "Ex_rev_wrap P = (\<exists>x. P (rev x))"

private definition Ex1_rev_wrap :: "('a list \<Rightarrow> bool) \<Rightarrow> bool"
  where "Ex1_rev_wrap P = (\<exists>!x. P (rev x))"

private definition Ball_rev_wrap :: "'a list set \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> bool"
  where "Ball_rev_wrap A P = (\<forall>x \<in> rev ` A. P (rev x))"

private definition Bex_rev_wrap :: "'a list set \<Rightarrow> ('a list \<Rightarrow> bool) \<Rightarrow> bool"
  where "Bex_rev_wrap A P = (\<exists>x \<in> rev ` A. P (rev x))"

subsection \<open>Initial reversal rules\<close>

private lemma rev_Nil: "rev Nil = Nil"
  by simp

private lemmas init_rev_wrap =
  eq_reflection[OF trans[OF rev_Nil[symmetric] rev_Nil_wrap_def[symmetric]]]
  transitive[OF all_rev_conv[symmetric] all_rev_wrap_def[symmetric], of P P for P]
  eq_reflection[OF trans[OF All_rev_conv[symmetric] All_rev_wrap_def[symmetric], of P P for P]]
  eq_reflection[OF trans[OF Ex_rev_conv[symmetric] Ex_rev_wrap_def[symmetric], of P P for P]] (* Ex_rev_wrapI *)
  eq_reflection[OF trans[OF Ex1_rev_conv[symmetric] Ex1_rev_wrap_def[symmetric], of P P for P]]
  eq_reflection[OF trans[OF Ball_rev_conv[symmetric] Ball_rev_wrap_def[symmetric], of P P for P]]
  eq_reflection[OF trans[OF Bex_rev_conv[symmetric] Bex_rev_wrap_def[symmetric], of P P for P]]

private lemma all_rev_unwrap: "all_rev_wrap (\<lambda>x. PROP P x) \<equiv> (\<And>x. PROP P (rev x))"
  using all_rev_wrap_def.

private lemma All_rev_unwrap: "All_rev_wrap (\<lambda>x. P x) = (\<forall>x. P (rev x))"
  using All_rev_wrap_def.

private lemma Ex_rev_unwrap: "Ex_rev_wrap (\<lambda>x. P x) = (\<exists>x. P (rev x))"
  using Ex_rev_wrap_def.

private lemma Ex1_rev_unwrap: "Ex1_rev_wrap (\<lambda>x. P x) = (\<exists>!x. P (rev x))"
  using Ex1_rev_wrap_def.

private lemma Ball_rev_unwrap: "Ball_rev_wrap A (\<lambda>x. P x) = (\<forall>x \<in> rev ` A. P (rev x))"
  using Ball_rev_wrap_def.

private lemma Bex_rev_unwrap: "Bex_rev_wrap A (\<lambda>x. P x) = (\<exists>x \<in> rev ` A. P (rev x))"
  using Bex_rev_wrap_def.

private lemmas init_rev_unwrap =
  eq_reflection[OF rev_Nil_wrap_def]
  all_rev_unwrap
  eq_reflection[OF All_rev_unwrap]
  eq_reflection[OF Ex_rev_unwrap]
  eq_reflection[OF Ex1_rev_unwrap]
  eq_reflection[OF Ball_rev_unwrap]
  eq_reflection[OF Bex_rev_unwrap]

subsection \<open>Cons reversion\<close>

definition snocs :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "snocs xs ys  = xs @ ys"

lemma Cons_rev: "a # rev u = rev (snocs u [a])"
  unfolding snocs_def by simp

lemma snocs_snocs: "snocs (snocs xs (y # ys)) zs = snocs xs (y # snocs ys zs)"
  unfolding snocs_def by simp

subsection \<open>Final corrections\<close>

lemma snocs_Nil: "snocs [] xs = xs"
  unfolding snocs_def by simp

lemma snocs_is_append: "snocs xs ys = xs @ ys"
  unfolding snocs_def..

private lemmas final_correct1 =
  snocs_Nil

private lemmas final_correct2 =
  snocs_is_append

subsection \<open>Declaration attribute \<open>reversal_rule\<close>\<close>

ML \<open>
structure Reversal_Rules = 
  Named_Thms(
    val name = @{binding "reversal_rule"}
    val description = "Rules performing reverse-symmetry transformation on theorems on lists"
  )
\<close>

attribute_setup reversal_rule = 
  \<open>Attrib.add_del
    (Thm.declaration_attribute Reversal_Rules.add_thm)
    (Thm.declaration_attribute Reversal_Rules.del_thm)\<close>
  "maintaining a list of reversal rules"

subsection \<open>Rule attribute \<open>reversed\<close>\<close>

ML \<open>
val eq_refl = @{thm eq_reflection}

fun pure_eq_of th =
  case Thm.prop_of th of
    Const (\<^const_name>\<open>Pure.eq\<close>, _) $ _ $ _
      => SOME (th)
  | Const (\<^const_name>\<open>Trueprop\<close>, _) $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ _ )
      => SOME (th RS eq_refl)
  | _ => NONE

val init_rev_wrap = @{thms init_rev_wrap}
val init_unwrap = @{thms init_rev_unwrap}
val final_correct1 = map_filter pure_eq_of @{thms final_correct1}
val final_correct2 = map_filter pure_eq_of @{thms final_correct2}

fun reverse ths context th =
  let
    val ctxt = Context.proof_of context
    val rules = map_filter pure_eq_of (ths @ Reversal_Rules.get ctxt)
    val vars = Term.add_vars (Thm.full_prop_of th) []
    fun add_inst_vars [] inst_vars = inst_vars
      | add_inst_vars ( ((v, i), T) :: vars ) inst_vars =
          case T of
            Type(\<^type_name>\<open>list\<close>, _) =>
              add_inst_vars vars (
                (
                  ((v, i), T),
                  Thm.cterm_of ctxt 
                    ( Const(\<^const_name>\<open>rev\<close>, Type(\<^type_name>\<open>fun\<close>, [T, T])) $ Var((v, i), T) )
                ) :: inst_vars
              )
          | _ => add_inst_vars vars inst_vars
  in
    th
    |> Drule.instantiate_normalize
       ([], add_inst_vars vars [])
    |> Simplifier.rewrite_rule ctxt init_rev_wrap
    |> Simplifier.rewrite_rule ctxt init_unwrap
    |> Simplifier.rewrite_rule ctxt rules
    |> Simplifier.rewrite_rule ctxt final_correct1
    |> Simplifier.rewrite_rule ctxt final_correct2
  end

val reversed = Scan.optional (Scan.lift (Args.add -- Args.colon) |-- Attrib.thms) []
  >> (fn ths => Thm.rule_attribute [] (reverse ths))
\<close>

attribute_setup reversed =
  \<open>reversed\<close>
  "Transforms the theorem on lists to reverse-symmetric version"

end

section \<open>Declaration of basic reversal rules\<close>

lemma hd_last_Nil: "hd [] = last []"
  unfolding hd_def last_def by simp 

lemma last_rev_hd: "last(rev xs) = hd xs"
  by (induct xs, simp add: hd_last_Nil, simp)

lemma hd_rev_last: "hd(rev xs) = last xs"
  by (induct xs, simp add: hd_last_Nil, simp)

lemma tl_rev: "tl (rev xs) = rev (butlast xs)"
  unfolding rev_swap[symmetric] butlast_rev[of "rev xs", symmetric] rev_rev_ident..

lemma if_rev: "(if P then rev u else rev v) = rev (if P then u else v)"
  by simp

lemma rev_in_conv: "rev u \<in> A \<longleftrightarrow> u \<in> rev ` A"
  using image_iff by fastforce

lemma in_lists_rev: "u \<in> lists A \<Longrightarrow> rev u \<in> lists A"
  by auto

lemma rev_in_lists: "rev u \<in> lists A \<Longrightarrow> u \<in> lists A"
  by auto

lemma rev_lists_conv: "rev ` lists A = lists A"
proof (intro equalityI subsetI)
  fix x
  show "x \<in> rev ` lists A \<Longrightarrow> x \<in> lists A"
    unfolding rev_in_conv[symmetric] using rev_in_lists.
  show "x \<in> lists A \<Longrightarrow> x \<in> rev ` lists A"
    unfolding rev_in_conv[symmetric] using in_lists_rev.
qed

lemma coset_rev: "List.coset (rev xs) = List.coset xs"
 by simp

lemmas [reversal_rule] =
  Cons_rev
  snocs_snocs
  rev_append[symmetric]
  last_rev_hd hd_rev_last
  tl_rev butlast_rev
  rev_is_rev_conv
  length_rev
  take_rev
  drop_rev
  rotate_rev
  if_rev
  rev_in_conv
  rev_lists_conv
  set_rev
  coset_rev

section \<open>Examples\<close>

context
begin

subsection \<open>Cons and append\<close>

private lemma example_Cons_append:
  assumes "xs = [a, b]" and "ys = [b, a, b]"
  shows "xs @ xs @ xs = a # b # a # ys"
using assms by simp

thm
  example_Cons_append
  example_Cons_append[reversed]
  example_Cons_append[reversed, reversed]

thm
  not_Cons_self
  not_Cons_self[reversed]

thm
  neq_Nil_conv
  neq_Nil_conv[reversed]

subsection \<open>Induction rules\<close>

thm
  list_nonempty_induct
  list_nonempty_induct[reversed] (* needs work *)
  list_nonempty_induct[reversed, where P="\<lambda>x. P (rev x)" for P, unfolded rev_rev_ident] 

thm
  list_induct2
  list_induct2[reversed] (* needs work *)
  list_induct2[reversed, where P="\<lambda>x y. P (rev x) (rev y)" for P, unfolded rev_rev_ident]

subsection \<open>hd, tl, last, butlast\<close>

thm
  hd_append
  hd_append[reversed]
  last_append

thm
  length_tl
  length_tl[reversed]
  length_butlast

thm
  hd_Cons_tl
  hd_Cons_tl[reversed]
  append_butlast_last_id
  append_butlast_last_id[reversed]

subsection \<open>set\<close>

thm
  hd_in_set
  hd_in_set[reversed]
  last_in_set

thm
  set_ConsD
  set_ConsD[reversed]

thm
  split_list_first
  split_list_first[reversed]

thm
  split_list_first_prop
  split_list_first_prop[reversed]
  split_list_first_prop[reversed, unfolded append_assoc append_Cons append_Nil]
  split_list_last_prop

thm
  split_list_first_propE
  split_list_first_propE[reversed]
  split_list_first_propE[reversed, unfolded append_assoc append_Cons append_Nil]
  split_list_last_propE

subsection \<open>rotate\<close>

private lemma rotate1_hd_tl': "xs \<noteq> [] \<Longrightarrow> rotate 1 xs = tl xs @ [hd xs]"
  by (cases xs) simp_all

thm
  rotate1_hd_tl'
  rotate1_hd_tl'[reversed]

end

end