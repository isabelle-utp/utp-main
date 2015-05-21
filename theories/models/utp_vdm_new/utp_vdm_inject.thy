(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_inject.thy                                                   *)
(* Authors: Original CML model by Simon Foster, University of York (UK)       *)
(*          Adapted to VDM by Luis Diogo Couto, Aarhus University (DK)        *)
(******************************************************************************)

theory utp_vdm_inject
imports utp_vdm_model
begin

default_sort type

section {* Injecting basic values *}

subsection {* The vbasic class *}

text {* To make injecting values into the domain easy, we introduce a type class
  representing HOL values which can be injected into the domain. It consists of
  an injection, projection and a function which gives a vtype equivalent for the 
  given HOL type. When we introduce subtypes this type will be the most general
  type. It follows that injecting any value gives a vdmv of the correct vtype.

  Perhaps the most important thing this class allows us to do is to inject arbitrary
  HOL functions over basic values into the value space.
*}

class vdmv =
  fixes Inject  :: "'a \<Rightarrow> vdmv"
  and   Type    :: "'a itself \<Rightarrow> vdmt"
  assumes Inject_inj: "Inject x = Inject y \<Longrightarrow> x = y"
  and Inject_range [simp]: 
        "range Inject = {x. x :\<^sub>v Type TYPE('a) \<and> \<D> x}"

syntax
  "_VTYPE" :: "type => logic"  ("(1VTYPE/(1'(_')))")

translations 
  "VTYPE('a)" == "CONST Type TYPE('a)"

text {* InjB and ProjB lift the Inject and Project functions up to domain level. *}

context vdmv
begin

definition Project :: "vdmv \<Rightarrow> 'a option" where
"Project x \<equiv> if (x :\<^sub>v VTYPE('a) \<and> \<D> x) then Some (inv_into UNIV Inject x) else None"

lemma Inject_type[simp]: "Inject x :\<^sub>v VTYPE('a)"
  by (insert Inject_range, auto simp add:image_def)

lemma Inject_Project [simp]: "Project (Inject x) = Some x"
  apply (auto simp add:Project_def)
  apply (metis Inject_inj injI inv_f_f)
  apply (metis (mono_tags) Inject_range mem_Collect_eq rangeI)
done

lemma Inject_simp [simp]: "Inject x = Inject y \<longleftrightarrow> x = y"
  by (metis Inject_inj)

lemma Project_Inject [simp]: 
  "\<And> x. \<lbrakk> x :\<^sub>v VTYPE('a); \<D> x \<rbrakk> \<Longrightarrow> Inject (the (Project x)) = x"
  by (auto intro:f_inv_into_f simp add:Project_def)

lemma Project_ndefined [simp]:
  "\<not> \<D> x \<Longrightarrow> Project x = None"
  by (simp add:Project_def)

lemma Project_dom [simp]: "\<And> x y. Project x = Some y \<Longrightarrow> x :\<^sub>v VTYPE('a)"
  by (case_tac "x :\<^sub>v VTYPE('a)", auto simp add:Project_def)

lemma Project_ndom [simp]: "\<And> x. \<lbrakk> Project x = None \<rbrakk> \<Longrightarrow> \<not> \<D> x \<or> \<not> x :\<^sub>v VTYPE('a)"
  apply (simp only:Project_def)
  apply (case_tac "x :\<^sub>v VTYPE('a)")
  apply (auto)
done

lemma Inject_Project_comp [simp]:
  "Project \<circ> Inject = Some" 
  by (simp add:comp_def)

lemma Inject_defined [simp]:
  "\<D> (Inject x)"
  by (metis Inject_Project Project_def option.simps(2))
  
lemma Project_defined [dest]: 
  "\<lbrakk> x :\<^sub>v VTYPE('a); \<D> x \<rbrakk> \<Longrightarrow> Project x \<noteq> None"
  by (metis Project_def option.simps(3))

lemma Project_Some [dest,simp]: 
  "\<And> x. Project x = Some y \<Longrightarrow> x = Inject y"
  apply (frule Project_dom)
  apply (drule Project_Inject)
  apply (metis Project_def option.simps(3))
  apply (simp)
done

lemma Project_None [elim]:
  "\<lbrakk> (Project x :: 'a option) = None; \<not> x :\<^sub>v VTYPE('a) \<Longrightarrow> P; \<not> \<D> x \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (unfold Project_def)
  apply (case_tac "x :\<^sub>v VTYPE('a) \<and> \<D> x")
  apply (force)+
done

lemma Inject_Project_list [simp]:
  assumes "\<forall>x\<in>set xs. x :\<^sub>v VTYPE('a) \<and> \<D> x"
  shows "xs = map Inject (map (the \<circ> Project) xs)"
using assms by (induct xs, auto)

lemma Project_inj_on:
  "inj_on (the \<circ> (Project :: vdmv \<Rightarrow> 'a option)) (bdcarrier(VTYPE('a)))"
    apply (rule inj_onI)
    apply (auto simp add: bcarrier_def bdcarrier_def)
    apply (metis Project_Inject)
done

end

subsection {* Units are injectable *}

instantiation unit :: vdmv
begin

definition "Inject_unit (x::unit) = UnitD"
definition "Type_unit (t::unit itself) = UnitT"

instance 
  by (intro_classes, auto simp add:Inject_unit_def Type_unit_def)
end

subsection {* Bools are injectable *}

instantiation bool :: vdmv
begin
definition "Inject_bool \<equiv> BoolD"
definition "Type_bool (x::bool itself) \<equiv> BoolT"

declare Type_bool_def [simp]

instance by (intro_classes, auto simp add:Inject_bool_def) 
end

lemma BTYPE_bool: "BoolT = VTYPE(bool)"
  by (simp add:Type_bool_def)

subsection {* Real numbers are injectable *}

instantiation real :: vdmv
begin

definition "Inject_real \<equiv> NumberD"
definition "Type_real (x::real itself) = NumberT"

declare Type_real_def [simp]

instance by (intro_classes, auto simp add:Inject_real_def)
end

lemma VTYPE_real: "NumberT = VTYPE(real)"
  by (simp add:Type_real_def)

subsection {* Tokens are injectable *}

typedef token = "{x::vdmv. \<D> x}"
  by (rule_tac x="BoolD True" in exI, simp)

declare Abs_token_inverse [simp]
declare Rep_token_inverse [simp]
declare Rep_token_inject [simp]

instantiation token :: vdmv
begin

definition "Inject_token = TokenD \<circ> Rep_token"
definition "Type_token (t::token itself) = TokenT"

instance
  apply (intro_classes)
  apply (auto simp add: Inject_token_def Type_token_def)
  apply (metis DEFINED_def DEFINED_member Rep_token TokenD_defn)
  apply (simp add:image_def)
  apply (rule_tac x="Abs_token xa" in exI)
  apply (simp)
done
end

subsection {* Characters are injectable *}

instantiation char :: vdmv
begin

definition "Inject_char \<equiv> CharD"
definition "Type_char (x::char itself) \<equiv> CharT"

instance by (intro_classes, auto simp add:Inject_char_def Type_char_def)
end

lemma VTYPE_char: "CharT = VTYPE(char)"
  by (simp add:Type_char_def)

subsection {* Option types are injectable *}

instantiation option :: (vdmv) vdmv
begin

definition Inject_option :: "'a option \<Rightarrow> vdmv" where
"Inject_option x = OptionD VTYPE('a) (x >>= Some \<circ> Inject)"

definition Type_option :: "'a option itself \<Rightarrow> vdmt" where
"Type_option t = OptionT VTYPE('a)"

instance
  apply (intro_classes)
  apply (case_tac x)
  apply (case_tac y)
  apply (auto simp add:Inject_option_def Type_option_def)
  apply (case_tac y)
  apply (auto simp add:Inject_option_def)
  apply (case_tac xa)
  apply (auto)
  apply (case_tac xa)
  apply (auto simp add:image_def)
  apply (erule OptionT_type_cases)
  apply (auto)
  apply (rule_tac x="None" in exI)
  apply (simp add:Inject_option_def)
  apply (rule_tac x="Project xa" in exI)
  apply (auto simp add:Inject_option_def)
done
end

subsection {* Pairs are injectable *}

instantiation prod :: (vdmv, vdmv) vdmv
begin

definition Inject_prod :: "'a \<times> 'b \<Rightarrow> vdmv" where
"Inject_prod \<equiv> \<lambda> x. PairD (Inject (fst x)) (Inject (snd x))"
                
definition Type_prod :: "('a \<times> 'b) itself \<Rightarrow> vdmt" where
"Type_prod x = PairT VTYPE('a) VTYPE('b)"

instance
  apply (intro_classes)
  apply (force simp add:Inject_prod_def)
  apply (auto simp add:Type_prod_def Inject_prod_def image_def)
  apply (metis Project_Inject fst_conv snd_conv)
done
end

subsection {* Lists are injectable *}

text {* The representation is quite complicated as we have to recursively
  inject/project each element and provide correct output if one value
  doesn't project correctly. *}

definition option_list :: "('a option) list \<Rightarrow> ('a list) option" where
"option_list xs \<equiv> if (None \<in> set xs) then None else Some (map the xs)"

lemma option_list_nil [simp]: "option_list [] = Some []"
  by (simp add:option_list_def)

lemma option_list_cons_none [simp]: 
  "option_list (None # xs) = None"
  by (simp add:option_list_def)

lemma option_list_cons_some [simp]: 
  "option_list (Some x # xs) = do { xs' \<leftarrow> option_list xs; Some (x # xs') }"
  by (simp add:option_list_def)

lemma option_list_map [simp]: "option_list (map Some xs) = Some xs"
  by (auto simp add:option_list_def image_def comp_def)

instantiation list :: (vdmv) vdmv
begin

definition Inject_list :: "'a list \<Rightarrow> vdmv" where
"Inject_list xs = ListD VTYPE('a) (map Inject xs)"

definition Type_list :: "'a list itself \<Rightarrow> vdmt" where
"Type_list xs \<equiv> ListT VTYPE('a)"

instance 
  apply (intro_classes)
  apply (simp add:Inject_list_def)
  apply (metis Inject_Project_comp map_map option.inject option_list_map)
  apply (auto simp add:Type_list_def Inject_list_def)
  apply (auto simp add:image_def Inject_list_def)
  apply (rule_tac x="map (the \<circ> Project :: vdmv \<Rightarrow> 'a) xs" in exI)
  apply (simp)
  apply (metis Inject_Project_list map_map)
done
end

lemma Type_list: "ListT (VTYPE('a)) = VTYPE(('a::vdmv) list)"
  by (simp add:Type_list_def)

subsection {* Finite sets are injectable *}

definition option_set :: "('a option) set \<Rightarrow> ('a set) option" where
"option_set xs \<equiv> if (None \<in> xs) then None else Some (the ` xs)"

lemma option_set_empty [simp]: "option_set {} = Some {}"
  by (simp add:option_set_def)

lemma option_set_insert: 
  "option_set (insert x xs) = do { xs' \<leftarrow> option_set xs; x' \<leftarrow> x; Some (insert x' xs') }"
  by (case_tac x, simp_all add:option_set_def)

lemma option_set_image [simp]: "option_set (Some ` xs) = Some xs"
  by (auto simp add:option_set_def image_def)

instantiation bset :: (vdmv) vdmv
begin

definition Inject_bset :: "'a bset \<Rightarrow> vdmv" where
"Inject_bset xs = SetD VTYPE('a) (bset_image Inject xs)"

definition Type_bset :: "'a bset itself \<Rightarrow> vdmt" where
"Type_bset x = SetT VTYPE('a)"

thm bspec

lemma bbspec [dest?]: 
  "\<forall>x\<in>\<^sub>bA. P x \<Longrightarrow> x \<in>\<^sub>b A \<Longrightarrow> P x"
  by (simp add: bBall_def)

instance
  apply (intro_classes)
  apply (simp add:Inject_bset_def)
  apply (simp only: DestBSet_inject)
  apply (metis Inject_Project_comp bset.map_comp bset.map_id the_Some)
  apply (auto simp add:Inject_bset_def Type_bset_def)
  apply (transfer)
  apply (metis Inject_type image_iff)
  apply (transfer)
  apply (metis Inject_defined image_iff)
  apply (erule SetT_type_cases)
  apply (auto)
  apply (simp add:image_def Inject_bset_def)
  apply (rule_tac x="bset_image (the \<circ> Project) A" in exI)  
  apply (transfer)
  apply (auto)
  apply (metis Project_Inject comp_apply imageI)
done
  
end

subsection {* Bounded partial functions are injectable *}

lemma functional_map_prod_on:
  "\<lbrakk> functional R; inj_on f (Domain R) \<rbrakk> \<Longrightarrow> functional (map_prod f g ` R)"
  apply (auto simp add: functional_def inj_on_def)
  apply (metis Domain.DomainI fst_conv snd_conv)
done

instantiation bmap :: (vdmv, vdmv) vdmv
begin

definition Inject_bmap :: "('a, 'b) bmap \<Rightarrow> vdmv" where
"Inject_bmap f = FuncD VTYPE('a) VTYPE('b) (bset_image (map_prod Inject Inject) (bmap_graph f))" 

definition Type_bmap :: "('a, 'b) bmap itself => vdmt" where
"Type_bmap x = FuncT VTYPE('a) VTYPE('b)"

lemma bset_image_inverse_lemma:
  assumes
    "bfunctional F"
    "DestBSet(F) \<subseteq> bdcarrier(VTYPE('a)) \<times> bdcarrier(VTYPE('b))"
  shows "bset_image 
           (map_prod Inject Inject) 
           (bmap_graph 
              (graph_bmap (bset_image (map_prod (the \<circ> Project :: vdmv \<Rightarrow> 'a) (the \<circ> Project :: vdmv \<Rightarrow> 'b)) F))) = F"
proof -
  from assms have "bfunctional (bset_image (map_prod (the \<circ> Project :: vdmv \<Rightarrow> 'a) (the \<circ> Project :: vdmv \<Rightarrow> 'b)) F)"
    apply (transfer) 
    apply (rule functional_map_prod_on)
    apply (metis)
    apply (rule subset_inj_on[of _ "bdcarrier VTYPE('a)"])
    apply (rule Project_inj_on)
    apply (metis DomainE mem_Sigma_iff subsetCE subsetI)
  done

  with assms(2) show ?thesis
    apply (subst graph_bmap_inv)
    apply (simp_all)
    apply (transfer)
    apply (simp add:image_comp map_prod_compose[THEN sym] bdcarrier_def bcarrier_def)
    apply (auto)
    apply (drule subsetD, auto)
    apply (insert image_iff)
    apply (fastforce)
  done
qed
              
instance proof
  fix x y :: "('a, 'b) bmap"
  assume inj_assm: "Inject x = Inject y"
  thus "x = y"
  proof -
    have "inj (map_prod (Inject :: 'a \<Rightarrow> vdmv) (Inject :: 'b \<Rightarrow> vdmv))"
      by (metis (full_types) Inject_simp injI prod_inj_map)
    
    with inj_assm show ?thesis
      apply (simp add: Inject_bmap_def)
      apply (transfer)
      apply (metis inj_image_eq_iff map_graph_inv)
    done
  qed
next
  let ?IJ = "Inject :: ('a,'b) bmap \<Rightarrow> vdmv"
  show "range ?IJ = {x. x :\<^sub>v VTYPE(('a, 'b) bmap) \<and> \<D> x}"
  proof
    show "range ?IJ \<subseteq> {x. x :\<^sub>v VTYPE(('a, 'b) bmap) \<and> \<D> x}"
      apply (auto simp add: Inject_bmap_def Type_bmap_def)
      apply (transfer)
      apply (metis Inject_type old.prod.inject prod_fun_imageE)
      apply (transfer)
      apply (metis Inject_type old.prod.inject prod_fun_imageE)
      apply (transfer)
      apply (rule functional_map_prod)
      apply (rule map_graph_functional)
      apply (metis Inject_simp injI)
      apply (transfer)
      apply (auto)
      apply (transfer)
      apply (auto)
    done
    
    show "{x. x :\<^sub>v VTYPE(('a, 'b) bmap) \<and> \<D> x} \<subseteq> range ?IJ"
      proof (safe, simp add:Type_bmap_def)
        fix F
        assume fassms: "F :\<^sub>v FuncT VTYPE('a) VTYPE('b)" "\<D> F"
        then obtain f where 
          fF: "F = FuncD VTYPE('a) VTYPE('b) f" and ffunc: "bfunctional f" and 
          ftype: "\<forall> (x, y)\<in>\<^sub>bf. x :\<^sub>v VTYPE('a) \<and> y :\<^sub>v VTYPE('b)" and
          fdefined: "\<forall> (x, y)\<in>\<^sub>bf. \<D> x \<and> \<D> y"
          by (auto simp add:bdcarrier_def bcarrier_def)
       
        from ftype and fdefined have fdt: "DestBSet(f) \<subseteq> bdcarrier(VTYPE('a)) \<times> bdcarrier(VTYPE('b))"
          apply (simp add:bdcarrier_def bcarrier_def bBall_def)
          apply (transfer, auto)
        done
         
        with fF ffunc show "F \<in> range ?IJ"
        proof -
          have "\<exists>v. Inject (v\<Colon>('a, 'b) bmap) = F" 
            by (metis (no_types) Inject_bmap_def fF fdt ffunc utp_vdm_inject.bset_image_inverse_lemma)
          thus "F \<in> range (Inject\<Colon>('a, 'b) bmap \<Rightarrow> vdmv)" by blast
        qed
      qed
    qed
  qed

end

instantiation option :: (type) DEFINED
begin

primrec defined_option :: "'a option \<Rightarrow> bool" where
"defined_option None = False" |
"defined_option (Some x) = True"

instance ..

end

fun InjVDM :: "'a::vdmv option \<Rightarrow> vdmv" where
"InjVDM None = BotD VTYPE('a)" |
"InjVDM (Some x) = Inject x"

definition ProjVDM :: "vdmv \<Rightarrow> 'a::vdmv option" where
"ProjVDM x = (if (\<D> x) then Project x else None)"

lemma InjVDM_inv[simp]: "ProjVDM (InjVDM x) = x"
  by (case_tac x, auto simp add:ProjVDM_def)

lemma InjVDM_type[typing]: 
  "InjVDM (x :: 'a::vdmv option) :\<^sub>v VTYPE('a)"
  by (case_tac x, auto)

lemma InjVDM_defined [defined]: "\<D> x \<Longrightarrow> \<D> (InjVDM x)"
  by (case_tac x, simp_all)
  
lemma InjVDM_nbot [defined]: "\<D> (InjVDM (Some x))"
  by (simp)
  
end
