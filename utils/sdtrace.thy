section {* Super-dense traces *}

theory sdtrace
  imports ttrace
begin

typedef sdreal = "UNIV :: (real \<times> nat) set" ..

setup_lifting type_definition_sdreal

lift_definition mk_sdreal :: "real \<Rightarrow> nat \<Rightarrow> sdreal" ("<_,_>") is Pair .

lift_definition inst :: "sdreal \<Rightarrow> real" is "fst" .
lift_definition ind  :: "sdreal \<Rightarrow> nat" is "snd" .

lemma inst [simp]: "inst <t,i> = t"
  by (transfer, simp)

lemma ind [simp]: "ind <t,i> = i"
  by (transfer, simp)

instantiation sdreal :: linorder
begin

lift_definition less_eq_sdreal :: "sdreal \<Rightarrow> sdreal \<Rightarrow> bool" is
"\<lambda> (m, i) (n, j). m < n \<or> (m = n \<and> i \<le> j)" .

lift_definition less_sdreal :: "sdreal \<Rightarrow> sdreal \<Rightarrow> bool" is
"\<lambda> (m, i) (n, j). m < n \<or> (m = n \<and> i < j)" .

instance
  by (intro_classes) (transfer, auto)+

end

definition inds where "inds f t = {i. <t,i> \<in> dom(f)}"

typedef 'a sdf =
  "{f :: sdreal \<rightharpoonup> 'a. (\<exists> t\<ge>0. ((\<forall> t'\<in>{0..t}. <t',0> \<in> dom(f)) \<or>
                                (\<forall> t'\<in>{0..<t}. <t',0> \<in> dom(f))))
                     \<and> (\<forall> t\<in>inst`dom(f). \<exists> i. \<forall> i'\<in>inds f t. i' \<le> i)
   }"

  by (rule_tac x="Map.empty" in exI, auto)

setup_lifting type_definition_sdf

(* Final microstep of an instant *)

lift_definition final_ms :: "'a sdf \<Rightarrow> real \<rightharpoonup> nat" is
"\<lambda> f t. if (<t,0> \<in> dom(f)) then Some (Max (inds f t)) else None" .

setup_lifting type_definition_cgf

lift_definition cgf_to_sdf :: "'a cgf \<Rightarrow> 'a sdf" is
"\<lambda> f st. if (inst st \<in> dom(f) \<and> ind st = 0) then f (inst st) else None"
  apply (auto simp add: inds_def)
  apply (rule_tac x="0" in exI)
  apply (auto)
done

text {* There are more super-dense functions than contiguous functions *}

lemma inj_cgf_to_sdf: "inj cgf_to_sdf"
  apply (rule injI)
  apply (transfer)
  apply (auto)
  apply (rule ext)
  apply (drule_tac x="<xa,0>" and y="<xa,0>" in cong)
  apply (auto)
  apply (case_tac "xa < 0")
  apply (simp)
  apply (metis (full_types) atLeastLessThan_empty atLeastLessThan_empty_iff2 atLeastLessThan_iff domIff)
  apply (metis atLeastLessThan_iff domIff inst)
done

lift_definition init_f :: "'a sdf \<Rightarrow> (real \<rightharpoonup> 'a)" is "\<lambda> f t. f <t, 0>" .
lift_definition final_f :: "'a sdf \<Rightarrow> (real \<rightharpoonup> 'a)" is "\<lambda> f t. f <t, Max (inds f t)>" .

text {* The initial value functions and final value functions for a contiguous function are the same *}

lemma cgf_init_f_eq_final_f:
  "init_f (cgf_to_sdf g) = final_f (cgf_to_sdf g)"
  apply (transfer, auto simp add: inds_def dom_if)
  apply (rule ext)
  apply (auto)
  apply (case_tac "<t,0> \<in> dom (\<lambda>st. g (inst st))")
  apply (auto)
  apply (subgoal_tac "{i. i = 0 \<and> <t,i> \<in> dom (\<lambda>st. g (inst st))} = {0}")
  apply (auto)
done
end