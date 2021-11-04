(*  Title:       X86 instruction semantics and basic block symbolic execution
    Authors:     Freek Verbeek, Abhijith Bharadwaj, Joshua Bockenek, Ian Roessle, Timmy Weerwag, Binoy Ravindran
    Year:        2020
    Maintainer:  Freek Verbeek (freek@vt.edu)
*)

section "Removing superfluous memory writes"

theory StateCleanUp
  imports State "HOL-Eisbach.Eisbach"
begin


definition "assumptions \<equiv> id"

text \<open>We are going to make schematic theorems of the form:
      \[
        @{term assumptions} ?A \implies \ldots 
      \]
      The assumptions will be generated on-the-fly. The seemingly weird lemmas below achieves that.\<close>


lemma assumptions_impI:
assumes "assumptions (P \<and> A)"
  shows "P"
  using assms
  by (auto simp add: assumptions_def)

lemma assumptions_conjE:
  shows "assumptions (P \<and> A) \<longleftrightarrow> P \<and> assumptions A"
  by (auto simp add: assumptions_def)

lemma assumptionsI:
  shows "assumptions True"
  by (auto simp add: assumptions_def)



text \<open>Consider two consecutive memory updates. If they write to the same memory locations, only one of these
      need to be kept. We formulate an Eisbach method to that end. \<close>


text \<open>Returns true if two states are equal except for a specific memory region.\<close>
definition eq_except_for_mem :: "state \<Rightarrow> state \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> 256 word \<Rightarrow> bool \<Rightarrow> bool"
  where "eq_except_for_mem \<sigma> \<sigma>' a si v b \<equiv> \<sigma> with [\<lbrakk>a,si\<rbrakk> :=\<^sub>m v] = (if b then \<sigma>' else \<sigma>' with [\<lbrakk>a,si\<rbrakk> :=\<^sub>m v])"


lemma eefm_start:
  assumes "eq_except_for_mem (\<sigma> with updates) (\<sigma> with updates') a si v b"
  shows "(\<sigma> with ((\<lbrakk>a,si\<rbrakk> :=\<^sub>m v)#updates)) = (if b then \<sigma> with updates' else \<sigma> with ((\<lbrakk>a,si\<rbrakk> :=\<^sub>m v)#updates'))"
  using assms
  by (auto simp add: eq_except_for_mem_def region_addresses_def state_with_updates.simps(2) state_update.simps)

lemma eefm_clean_mem:
assumes "si' \<le> si"
    and "eq_except_for_mem (\<sigma> with updates) (\<sigma> with updates') a si v b"
  shows "eq_except_for_mem (\<sigma> with ((\<lbrakk>a,si'\<rbrakk> :=\<^sub>m v')#updates)) (\<sigma> with updates') a si v b"
  using assms
  apply (auto simp add: eq_except_for_mem_def state_with_updates.simps(2) state_update.simps)
  subgoal
    apply (cases "\<sigma> with updates";cases "\<sigma> with updates'";cases "\<sigma>")
    by (auto simp add: override_on_def region_addresses_iff)
  apply (cases "\<sigma> with updates";cases "\<sigma> with updates'")
  apply (auto simp add: override_on_def region_addresses_iff)
  apply (rule ext)
  apply (auto split: if_splits)
  by meson

method eefm_clean_mem = (rule eefm_clean_mem, (simp (no_asm);fail))


lemma eefm_clean_mem_enclosed:
  assumes "si < 32" (* due to 256 words being written to memory *)
      and "enclosed a' si' a si"
      and "eq_except_for_mem (\<sigma> with updates) (\<sigma> with updates') a' si' v' b"
  shows "eq_except_for_mem (\<sigma> with ((\<lbrakk>a,si\<rbrakk> :=\<^sub>m v)#updates)) 
                           (\<sigma> with ((\<lbrakk>a,si\<rbrakk> :=\<^sub>m overwrite (8 * unat (a' - a)) (8 * unat (a' - a) + 8*si') v (v' << unat (a'-a)*8))#updates'))
                           a' si' v' True"
proof(cases b)
  case True
  thus ?thesis
    using assms(3)
    apply (auto simp add: eq_except_for_mem_def state_with_updates.simps(2) state_update.simps)
    apply (cases "\<sigma> with updates";cases "\<sigma> with updates'")
    apply (auto simp add: override_on_def)
    apply (rule ext)
    apply (auto)

    apply (rule word_eqI)
    subgoal premises prems for _ _ _ _ x n
    proof-
      have 1: "unat (x - a) - unat (a' - a) = unat(x - a')"
        using address_in_enclosed_region_as_linarith[OF assms(2),of x]
              address_of_enclosed_region_ge[OF assms(2)]
              word_le_nat_alt prems(4-5)
        by (auto simp add: unat_sub_if_size word_size)
      thus ?thesis
        using prems address_in_enclosed_region[of a' si' a si x,OF assms(2)] assms(1)
        by (auto simp add: word_size take_byte_shiftlr_256 nth_take_byte_overwrite)
    qed

    apply (rule word_eqI)
    subgoal for _ _ _ _ x n
      using notin_region_addresses_sub[of x a' si' a]
      by (auto simp add: word_size nth_take_byte_overwrite)
    done
next
  case False
  thus ?thesis
    using assms(3)
    apply (auto simp add: eq_except_for_mem_def state_with_updates.simps(2) state_update.simps)
    apply (cases "\<sigma> with updates";cases "\<sigma> with updates'")
    apply (auto simp add: override_on_def)
    apply (rule ext)
    using enclosed_spec[OF assms(2)]
    apply (auto)

    subgoal premises prems for _ _ _ _ _ x 
    proof-
      have 1: "unat (x - a) - unat (a' - a) = unat(x - a')"
        using address_in_enclosed_region_as_linarith[OF assms(2),of x]
              address_of_enclosed_region_ge[OF assms(2)]
              word_le_nat_alt prems(6)
        by (auto simp add: unat_sub_if_size word_size)
      show ?thesis
        apply (rule word_eqI)
        using 1 prems address_in_enclosed_region[of a' si' a si x,OF assms(2)] assms(1)
        by (auto simp add: word_size take_byte_shiftlr_256 nth_take_byte_overwrite)
    qed

     subgoal for _ _ _ _ _ x
       apply (rule word_eqI)
       using notin_region_addresses_sub[of x a' si' a]
       by (auto simp add: word_size nth_take_byte_overwrite)
     by meson
qed


lemmas eefm_clean_mem_enclosed_plus  = eefm_clean_mem_enclosed[OF _ enclosed_plus, simplified]
lemmas eefm_clean_mem_enclosed_minus_numeral = eefm_clean_mem_enclosed[OF _ enclosed_minus_minus, of _ "numeral n" "numeral m"] for n m

method eefm_clean_mem_enclosed_plus = 
        (rule eefm_clean_mem_enclosed_plus, (
            (simp (no_asm);fail), (simp (no_asm);fail),
            (
             (simp (no_asm_simp);fail) |
             (rule assumptions_impI[of "_ + _ < 18446744073709551616"],simp (no_asm_simp),subst (asm) assumptions_conjE))
            )
        )

method eefm_clean_mem_enclosed_minus_numeral = 
        (rule eefm_clean_mem_enclosed_minus_numeral, (
            (simp (no_asm);fail), (simp (no_asm);fail), (simp (no_asm);fail), (simp (no_asm);fail), (simp (no_asm);fail),
            (
             (simp (no_asm_simp);fail) |           
             (rule assumptions_impI[of "_ \<le> _"],simp (no_asm_simp),subst (asm) assumptions_conjE))
            ) 
        )

lemma eefm_next_mem:
assumes "separate a si a' si'"
   and "eq_except_for_mem (\<sigma> with updates) (\<sigma> with updates') a si v b"
 shows "eq_except_for_mem (\<sigma> with ((\<lbrakk>a',si'\<rbrakk> :=\<^sub>m v')#updates)) (\<sigma> with ((\<lbrakk>a',si'\<rbrakk> :=\<^sub>m v')#updates')) a si v b"
  using assms
  apply (auto simp add: eq_except_for_mem_def override_on_def separate_def state_with_updates.simps(2) state_update.simps)
  apply (cases "\<sigma> with updates";cases "\<sigma> with updates'")
  apply (auto simp add: override_on_def)
  apply (rule ext)
   apply (auto)
  apply (cases "\<sigma> with updates";cases "\<sigma> with updates'")
  apply (auto simp add: override_on_def)
  apply (rule ext)
  apply (auto)
  by (metis select_convs(2))

method eefm_next_mem =        
        (rule eefm_next_mem,
            (  (simp (no_asm_simp) add: separate_simps state_simps; fail) |
               (rule assumptions_impI[of "separate _ _ _ _ "],simp (no_asm_simp),subst (asm) assumptions_conjE))
        )

lemma eefm_end:
  shows "eq_except_for_mem (\<sigma> with updates) (\<sigma> with updates) a si v False"
  by (auto simp add: eq_except_for_mem_def)


text \<open>We need a tactic exactly like ``subst'' but that applies to the outer most term.\<close>

ML_file \<open>MySubst.ML\<close>


text \<open>The following method takes a goal with state with symbolic state updates.
      It first applies @{thm eefm_start}, considering the outer-most memory update to some region $\llbracket a, si \rrbracket$.
      A list @{term updates'} is generated that produces a similar state except for region $\llbracket a, si \rrbracket$.
      The list thus can have fewer updates since any update to a region that is enclosed in region $\llbracket a, si \rrbracket$ can be removed.
      Consecutively, this method applies rules to determine whether a state update can be kept, merged or removed.
      It may add assumptions to the goal, that assume no overflow.
\<close>

method clean_up_mem = (
    mysubst eefm_start,
    ( eefm_clean_mem | eefm_clean_mem_enclosed_plus | eefm_clean_mem_enclosed_minus_numeral | eefm_next_mem)+,
    rule eefm_end,
    simp (no_asm),
    ((match premises in A[thin]: "assumptions (?A \<and> ?B)" \<Rightarrow> \<open>cut_tac A;subst (asm) assumptions_conjE, erule conjE \<close>)+)?
  )


text \<open>The method above applies to one state update. This method can be repeated as long as modifies
      the goal, as it always makes the goal smaller. The method below repeats a given method until
      the goal is unchanged. In deterministic fashion (a la the REPEAT\_DETERM tactic).\<close>

method_setup repeat_until_unchanged = \<open>
  Method.text_closure >>
    (fn text => fn ctxt => fn using => 
          \<comment> \<open>parse the method supplied as parameter\<close>
      let val ctxt_tac = Method.evaluate_runtime text ctxt using
          fun repeat_until_unchanged (ctxt,st) = 
            case Seq.pull (ctxt_tac (ctxt,st)) of
                SOME (Seq.Result (ctxt',st'), _) => 
                  if Thm.eq_thm (st, st') then 
                    Seq.make_results (Seq.succeed (ctxt',st'))
                  else
                    repeat_until_unchanged (ctxt',st')
              | _ => Seq.make_results (Seq.succeed (ctxt,st))
      in
        repeat_until_unchanged 
      end)
\<close>

method clean_up = repeat_until_unchanged clean_up_mem

end