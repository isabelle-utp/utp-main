(******************************************************************************)
(* Project: Unifying Theories of Programming in HOL                           *)
(* File: utp_alpha_pred.thy                                                   *)
(* Author: Frank Zeyda and Simon Foster, University of York (UK)              *)
(******************************************************************************)

header {* Conversion of alphabetised predicates into map sets *}

theory utp_alpha_map
imports utp_alpha_pred
begin

definition WF_BINDING_MAP :: "('VALUE VAR, 'VALUE) fmap set" where
"WF_BINDING_MAP = {f. \<forall>x. x \<in>\<^sub>f fdom f \<longrightarrow> the (\<langle>f\<rangle>\<^sub>m x) \<rhd> x}"

definition binding_fmap ::
  "'VALUE ALPHABET \<Rightarrow> 'VALUE WF_BINDING \<Rightarrow> ('VALUE VAR, 'VALUE) fmap" where
"binding_fmap a b = list_fmap (map (\<lambda> x. (x, \<langle>b\<rangle>\<^sub>b x)) (flist a))"

lemma binding_fmap_rep_eq: 
  assumes "x \<in>\<^sub>f a"
  shows "\<langle>binding_fmap a b\<rangle>\<^sub>m x = Some (\<langle>b\<rangle>\<^sub>b x)"
proof -
  obtain xs where fset: "a = fset xs" and lprops: "sorted xs" "distinct xs"
    by (metis flist_inv flist_props)

  with assms have "x \<in>\<^sub>f fset xs"
    by simp

  with lprops have "\<langle>binding_fmap (fset xs) b\<rangle>\<^sub>m x = Some (\<langle>b\<rangle>\<^sub>b x)"
    apply (induct xs)
    apply (simp add: binding_fmap_def list_fmap.rep_eq)+
    apply (subgoal_tac "flist (finsert xa (fset xs)) = (xa # flist (fset xs))")
    apply (simp add: sorted_Cons)
    apply (metis)
    apply (metis (lifting) distinct.simps(2) fset_cons fset_inv sorted_Cons)
  done

  with fset show ?thesis
    by (simp)
qed

lemma fdom_binding_map [simp]:
  "fdom (binding_fmap a b) = a"
  by (auto simp add:binding_fmap_def)

lemma binding_fmap [closure]:
  "binding_fmap a b \<in> WF_BINDING_MAP"
  apply (unfold WF_BINDING_MAP_def)
  apply (rule CollectI)
  apply (rule allI)
  apply (simp add:binding_fmap_rep_eq)
done

lemma fmap_list_binding_fmap:
  "fmap_list (binding_fmap a b) = map (\<lambda> x. (x, \<langle>b\<rangle>\<^sub>b x)) (flist a)"
  apply (subgoal_tac "(map fst (map (\<lambda>x. (x, \<langle>b\<rangle>\<^sub>b x)) (flist a))) = flist a")
  apply (simp add: binding_fmap_def)
  apply (simp add: map_map comp_def)
done

definition fmap_binding ::
  "('VALUE VAR, 'VALUE) fmap \<Rightarrow> 'VALUE WF_BINDING" where
"fmap_binding f = Abs_WF_BINDING (\<lambda> x. if (x \<in>\<^sub>f Fmap.fdom f) then the (\<langle>f\<rangle>\<^sub>m x) else default (vtype x))"

lemma fmap_binding_rep_eq:
  "f \<in> WF_BINDING_MAP \<Longrightarrow> 
   \<langle>fmap_binding f\<rangle>\<^sub>b = (\<lambda> x. if (x \<in>\<^sub>f Fmap.fdom f) then the (\<langle>f\<rangle>\<^sub>m x) else default (vtype x))"
  apply (subgoal_tac "(\<lambda> x. if (x \<in>\<^sub>f Fmap.fdom f) then the (\<langle>f\<rangle>\<^sub>m x) else default (vtype x)) \<in> WF_BINDING")
  apply (simp add:fmap_binding_def)
  apply (unfold WF_BINDING_def)
  apply (unfold WF_BINDING_MAP_def)
  apply (rule CollectI)
  apply (rule allI)
  apply (case_tac "v \<in>\<^sub>f fdom f")
  apply (auto intro:typing defined)
done

lemma binding_fmap_inv:
  "fmap_binding (binding_fmap a b) \<cong> b on \<langle>a\<rangle>\<^sub>f"
  by (simp add:binding_equiv_def closure fmap_binding_rep_eq binding_fmap_rep_eq)

definition predicate_maps :: 
  "'VALUE ALPHABET \<Rightarrow>    'VALUE WF_PREDICATE \<Rightarrow> ('VALUE VAR, 'VALUE) fmap set" where
"predicate_maps a p = binding_fmap a ` destPRED p"

definition maps_predicate :: 
  "('VALUE VAR, 'VALUE) fmap set \<Rightarrow> 'VALUE WF_PREDICATE" where
"maps_predicate fs = mkPRED {b. \<exists>f\<in>fs. fmap_binding f \<cong> b on \<langle>fdom f\<rangle>\<^sub>f}"

lemma predicate_maps_inv[simp]:
  "maps_predicate (predicate_maps (\<alpha> p) (\<pi> p)) = \<pi> p"
  apply (simp add:maps_predicate_def predicate_maps_def)
  apply (subgoal_tac "\<And> b f. (fmap_binding (binding_fmap (\<alpha> p) f) \<cong> b on \<langle>\<alpha> p\<rangle>\<^sub>f) = f \<cong> b on \<langle>\<alpha> p\<rangle>\<^sub>f")
  apply (safe)
  apply (smt UNIV_I WF_ALPHA_PREDICATE_binding_equiv mem_Collect_eq mkPRED_inverse)
  apply (simp)
  apply (rule_tac x="x" in bexI)
  apply (metis binding_fmap_inv)
  apply (simp)
  apply (metis (lifting) binding_equiv_comm binding_equiv_trans binding_fmap_inv)
  apply (metis (lifting) binding_equiv_trans binding_fmap_inv)
done

end