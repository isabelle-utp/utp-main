(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Connection between @{text "mod_ring"} and @{text "mod_type"}\<close>

text \<open>This file shows that the type @{text "mod_ring"}, which is defined in the 
  Berlekamp--Zassenhaus development, is an instantiation of the type class @{text "mod_type"}.\<close>

theory Finite_Field_Mod_Type_Connection
  imports
  Berlekamp_Zassenhaus.Finite_Field
  Rank_Nullity_Theorem.Mod_Type
begin

instantiation mod_ring :: (finite) ord
begin
definition less_eq_mod_ring :: "'a mod_ring \<Rightarrow> 'a mod_ring \<Rightarrow> bool" 
  where "less_eq_mod_ring x y = (to_int_mod_ring x \<le> to_int_mod_ring y)"

definition less_mod_ring :: "'a mod_ring \<Rightarrow> 'a mod_ring \<Rightarrow> bool" 
  where "less_mod_ring x y = (to_int_mod_ring x < to_int_mod_ring y)"

instance proof qed
end

instantiation mod_ring :: (finite) linorder
begin
instance by (intro_classes, unfold less_eq_mod_ring_def less_mod_ring_def) (transfer, auto)
end


instance mod_ring :: (finite) wellorder
proof -
have "wf {(x :: 'a mod_ring, y). x < y}"
    by (auto simp add: trancl_def tranclp_less intro!: finite_acyclic_wf acyclicI)
  thus "OFCLASS('a mod_ring, wellorder_class)"
    by(rule wf_wellorderI) intro_classes
qed


lemma strict_mono_to_int_mod_ring: "strict_mono to_int_mod_ring"
  unfolding strict_mono_def unfolding less_mod_ring_def by auto


instantiation mod_ring :: (nontriv) mod_type
begin
definition Rep_mod_ring :: "'a mod_ring \<Rightarrow> int"
  where "Rep_mod_ring x = to_int_mod_ring x"

definition Abs_mod_ring :: "int \<Rightarrow> 'a mod_ring"
  where "Abs_mod_ring x = of_int_mod_ring x"

instance 
proof (intro_classes)
  show "type_definition (Rep::'a mod_ring \<Rightarrow> int) Abs {0..<int CARD('a mod_ring)}"
    unfolding Rep_mod_ring_def Abs_mod_ring_def type_definition_def by (transfer, auto) 
  show "1 < int CARD('a mod_ring)" using less_imp_of_nat_less nontriv by fastforce
  show "0 = (Abs::int \<Rightarrow> 'a mod_ring) 0"
    by (simp add: Abs_mod_ring_def)
  show "1 = (Abs::int \<Rightarrow> 'a mod_ring) 1"
    by (metis (mono_tags, hide_lams) Abs_mod_ring_def of_int_hom.hom_one of_int_of_int_mod_ring)
  fix x y::"'a mod_ring"
  show "x + y = Abs ((Rep x + Rep y) mod int CARD('a mod_ring))"
    unfolding Abs_mod_ring_def Rep_mod_ring_def by (transfer, auto)
  show "- x = Abs (- Rep x mod int CARD('a mod_ring))" 
    unfolding Abs_mod_ring_def Rep_mod_ring_def by (transfer, auto simp add: zmod_zminus1_eq_if)
  show "x * y = Abs (Rep x * Rep y mod int CARD('a mod_ring))"
    unfolding Abs_mod_ring_def Rep_mod_ring_def by (transfer, auto)
  show "x - y = Abs ((Rep x - Rep y) mod int CARD('a mod_ring))"
    unfolding Abs_mod_ring_def Rep_mod_ring_def by (transfer, auto)
  show "strict_mono (Rep::'a mod_ring \<Rightarrow> int)" unfolding Rep_mod_ring_def 
    by (rule strict_mono_to_int_mod_ring)
qed
end
end
