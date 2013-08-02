(******************************************************************************)
(* Project: VDM model for Isabelle/UTP                                        *)
(* File: utp_vdm_inject.thy                                                   *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

theory utp_vdm_inject
imports utp_vdm_values
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

class vbasic =
  fixes Inject  :: "'a \<Rightarrow> vbasic"
  and   Type    :: "'a itself \<Rightarrow> vbasict"
  assumes Inject_inj: "Inject x = Inject y \<Longrightarrow> x = y"
  and     Inject_range [simp]: "range Inject = {x. x :\<^sub>b Type (TYPE('a)) \<and> \<D> x}"

syntax
  "_BTYPE" :: "type => logic"  ("(1BTYPE/(1'(_')))")
  "_VTYPE" :: "type => logic"  ("(1VTYPE/(1'(_')))")

translations 
  "BTYPE('a)" == "CONST Type TYPE('a)"
  "VTYPE('a)" == "CONST BasicT (CONST Type TYPE('a))"

text {* InjB and ProjB lift the Inject and Project functions up to domain level. *}

context vbasic
begin

definition Project :: "vbasic \<Rightarrow> 'a option" where
"Project x \<equiv> if (x :\<^sub>b BTYPE('a) \<and> \<D> x) then Some (inv Inject x) else None"

lemma Inject_type[simp]: "Inject x :\<^sub>b BTYPE('a)"
  by (insert Inject_range, auto simp add:image_def)

lemma Inject_Project [simp]: "Project (Inject x) = Some x"
  apply (auto simp add:Project_def)
  apply (metis Inject_inj injI inv_f_f)
  apply (metis (mono_tags) Inject_range mem_Collect_eq rangeI)
done

lemma Inject_simp [simp]: "Inject x = Inject y \<longleftrightarrow> x = y"
  by (metis Inject_inj)

lemma Project_Inject [simp]: 
  "\<And> x. \<lbrakk> x :\<^sub>b BTYPE('a); \<D> x \<rbrakk> \<Longrightarrow> Inject (the (Project x)) = x"
  by (auto intro:f_inv_into_f simp add:Project_def)

lemma Project_ndefined [simp]:
  "\<not> \<D> x \<Longrightarrow> Project x = None"
  by (simp add:Project_def)

lemma Project_dom [simp]: "\<And> x y. Project x = Some y \<Longrightarrow> x :\<^sub>b BTYPE('a)"
  by (case_tac "x :\<^sub>b BTYPE('a)", auto simp add:Project_def)

lemma Project_ndom [simp]: "\<And> x. \<lbrakk> Project x = None \<rbrakk> \<Longrightarrow> \<not> \<D> x \<or> \<not> x :\<^sub>b BTYPE('a)"
  apply (simp only:Project_def)
  apply (case_tac "x :\<^sub>b BTYPE('a)")
  apply (auto)
done

lemma Inject_Project_comp [simp]:
  "Project \<circ> Inject = Some" 
  by (simp add:comp_def)

lemma Inject_defined [simp]:
  "\<D> (Inject x)"
  by (metis Inject_Project Project_def option.simps(2))
  
lemma Project_defined [dest]: 
  "\<lbrakk> x :\<^sub>b BTYPE('a); \<D> x \<rbrakk> \<Longrightarrow> Project x \<noteq> None"
  by (metis Project_def option.simps(3))

lemma Project_Some [dest,simp]: 
  "\<And> x. Project x = Some y \<Longrightarrow> x = Inject y"
  apply (frule Project_dom)
  apply (drule Project_Inject)
  apply (metis Project_def option.simps(3))
  apply (simp)
done

lemma Project_None [elim]:
  "\<lbrakk> (Project x :: 'a option) = None; \<not> x :\<^sub>b BTYPE('a) \<Longrightarrow> P; \<not> \<D> x \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (unfold Project_def)
  apply (case_tac "x :\<^sub>b BTYPE('a) \<and> \<D> x")
  apply (force)+
done

lemma Inject_Project_list [simp]:
  assumes "\<forall>x\<in>set xs. x :\<^sub>b BTYPE('a) \<and> \<D> x"
  shows "xs = map Inject (map (the \<circ> Project) xs)"
using assms by (induct xs, auto)

end

subsection {* Units are injectable *}

instantiation unit :: vbasic
begin

definition "Inject_unit (x::unit) = UnitI"
definition "Type_unit (t::unit itself) = UnitBT"

instance 
  by (intro_classes, auto simp add:Inject_unit_def Type_unit_def)
end

(*
subsection {* Naturals are injectable *}

instantiation nat :: vbasic
begin
definition "Inject_nat \<equiv> NatI"
definition Type_nat :: "nat itself \<Rightarrow> vbasict" where
"Type_nat x \<equiv> NatBT"

declare Type_nat_def [simp]

instance
  by (intro_classes, auto simp add:Inject_nat_def) 
end

lemma BTYPE_nat: "NatBT = BTYPE(nat)"
  by (simp add:Type_nat_def)

subsection {* Integers are injectable *}

instantiation int :: vbasic
begin
definition "Inject_int \<equiv> IntI"
definition Type_int :: "int itself \<Rightarrow> vbasict" where
"Type_int x \<equiv> IntBT"

declare Type_int_def [simp]

instance by (intro_classes, auto simp add:Inject_int_def) 
end

lemma BTYPE_int: "IntBT = BTYPE(int)"
  by (simp add:Type_int_def)
*)

subsection {* Bools are injectable *}

instantiation bool :: vbasic
begin
definition "Inject_bool \<equiv> BoolI"
definition "Type_bool (x::bool itself) \<equiv> BoolBT"

declare Type_bool_def [simp]

instance by (intro_classes, auto simp add:Inject_bool_def) 
end

lemma BTYPE_bool: "BoolBT = BTYPE(bool)"
  by (simp add:Type_bool_def)

(*
subsection {* Rationals are injectable *}

instantiation rat :: vbasic
begin

definition "Inject_rat \<equiv> RatI"
definition "Type_rat (x::rat itself) = RatBT"

declare Type_rat_def [simp]

instance by (intro_classes, auto simp add:Inject_rat_def)
end

lemma BTYPE_rat: "RatBT = BTYPE(rat)"
  by (simp add:Type_rat_def)
*)

subsection {* Rationals are injectable *}

instantiation real :: vbasic
begin

definition "Inject_real \<equiv> NumberI"
definition "Type_real (x::real itself) = NumberBT"

declare Type_real_def [simp]

instance by (intro_classes, auto simp add:Inject_real_def)
end

lemma BTYPE_real: "NumberBT = BTYPE(real)"
  by (simp add:Type_real_def)

subsection {* Names are injectable *}

instantiation NAME :: vbasic
begin

definition "Inject_NAME = NameI"
definition "Type_NAME (x::NAME itself) = NameBT"

declare Type_NAME_def [simp]

instance by (intro_classes, auto simp add:Inject_NAME_def)
end

subsection {* Tokens are injectable *}

typedef token = "{x::vbasic. \<D> x}"
  by (rule_tac x="BoolI True" in exI, simp)

declare Abs_token_inverse [simp]
declare Rep_token_inverse [simp]
declare Rep_token_inject [simp]

instantiation token :: vbasic
begin

definition "Inject_token = TokenI \<circ> Rep_token"
definition "Type_token (t::token itself) = TokenBT"

instance
  apply (intro_classes)
  apply (auto simp add: Inject_token_def Type_token_def)
  apply (metis Rep_token mem_Collect_eq)
  apply (simp add:image_def)
  apply (rule_tac x="Abs_token xa" in exI)
  apply (simp)
done
end


(*
subsection {* Channels are injectable *}

typedef chan = "UNIV :: (NAME * vbasict) set"
  by auto

instantiation chan :: vbasic
begin

definition "Inject_chan c = ChanI (fst (Rep_chan c)) (snd (Rep_chan c))"
*)

subsection {* Characters are injectable *}

instantiation char :: vbasic
begin

definition "Inject_char \<equiv> CharI"
definition "Type_char (x::char itself) \<equiv> CharBT"

instance by (intro_classes, auto simp add:Inject_char_def Type_char_def)
end

lemma BTYPE_char: "CharBT = BTYPE(char)"
  by (simp add:Type_char_def)

subsection {* Pairs are injectable *}

instantiation prod :: (vbasic, vbasic) vbasic
begin

definition Inject_prod :: "'a \<times> 'b \<Rightarrow> vbasic" where
"Inject_prod \<equiv> \<lambda> x. PairI (Inject (fst x)) (Inject (snd x))"
                
definition Type_prod :: "('a \<times> 'b) itself \<Rightarrow> vbasict" where
"Type_prod x = PairBT BTYPE('a) BTYPE('b)"

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

instantiation list :: (vbasic) vbasic
begin

definition Inject_list :: "'a list \<Rightarrow> vbasic" where
"Inject_list xs = ListI BTYPE('a) (map Inject xs)"

definition Type_list :: "'a list itself \<Rightarrow> vbasict" where
"Type_list xs \<equiv> ListBT BTYPE('a)"

instance 
  apply (intro_classes)
  apply (simp add:Inject_list_def)
  apply (metis Inject_Project_comp map_map option.inject option_list_map)
  apply (auto simp add:Type_list_def Inject_list_def)
  apply (auto simp add:image_def Inject_list_def)
  apply (rule_tac x="map (the \<circ> Project :: vbasic \<Rightarrow> 'a) xs" in exI)
  apply (simp)
  apply (metis Inject_Project_list map_map)
done
end

(*
*)

(* Unfortunately the injections only work for monomorphically typed function, at the moment
   which is no surprise as we need explicit machinery to build polymorphic versions *)
lemma Type_list: "ListBT (BTYPE('a)) = BTYPE(('a::vbasic) list)"
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

(*
lemma flist_finsert_sorted [simp]:
  "\<lbrakk> sorted (x # xs); distinct (x # xs) \<rbrakk> \<Longrightarrow> flist (finsert x (fset xs)) = x # xs"
  apply (subgoal_tac "\<forall>x'. x'\<in>\<^sub>ffset xs \<longrightarrow> x < x'")
  apply (auto)
  apply (metis fset_inv sorted_Cons)
  apply (metis le_neq_trans sorted_Cons)
done
*)

instantiation fset :: (vbasic) vbasic
begin

definition Inject_fset :: "'a fset \<Rightarrow> vbasic" where
"Inject_fset xs = FSetI BTYPE('a) (Abs_fset (Inject ` Rep_fset xs))"

(*
definition Project_fset :: "vbasic \<Rightarrow> 'a fset option" where 
"Project_fset xs = (ProjFSetI xs >>= (\<lambda> x. option_set (Project ` Rep_fset x))) >>= Some \<circ> Abs_fset"
*)

definition Type_fset :: "'a fset itself \<Rightarrow> vbasict" where
"Type_fset x = FSetBT BTYPE('a)"

instance proof
  fix x y :: "'a fset"
  assume "Inject x = Inject y"
  thus "x = y"
      apply (simp add: Inject_fset_def)
      apply (drule FSetI_inj)
      apply (subgoal_tac "Inject ` \<langle>x\<rangle>\<^sub>f = Inject ` \<langle>y\<rangle>\<^sub>f")
      apply (simp)
      apply (metis Inject_Project_comp Rep_fset_inverse image_compose these_image_Some_eq)
      apply (metis Rep_fset_finite Rep_fset_inv finite_imageI)
  done

next

  show "range (Inject :: 'a fset \<Rightarrow> vbasic) = {x. x :\<^sub>b BTYPE('a fset) \<and> \<D> x}"
  proof (auto)
    fix x :: "'a fset"
    show "Inject x :\<^sub>b BTYPE('a fset)"
      by (force simp add:Type_fset_def Inject_fset_def image_def flist_def)
  next
    fix x :: "'a fset"
    show "\<D> (Inject x)"
      by (auto simp add:Inject_fset_def)
  next
    fix x
    assume "x :\<^sub>b BTYPE('a fset)" "\<D> x"
    thus "x \<in> range (Inject :: 'a fset \<Rightarrow> vbasic)"
      apply (auto simp add:Type_fset_def Inject_fset_def image_def)
      apply (rule_tac x="((the \<circ> Project) `\<^sub>f xs)" in exI)
      apply (simp)
    done
  qed
qed
end

subsection {* Finite maps are injectable *}

definition vbasic_map :: "('a::vbasic \<rightharpoonup> 'b::vbasic) \<Rightarrow> (vbasic \<rightharpoonup> vbasic)" where
"vbasic_map f = (\<lambda> x. ((Project x :: 'a option) >>= f) >>= Some \<circ> Inject)"

definition map_vbasic :: "(vbasic \<rightharpoonup> vbasic) \<Rightarrow> ('a::vbasic \<rightharpoonup> 'b::vbasic)" where
"map_vbasic f \<equiv> (\<lambda> x::'a. f (Inject x) >>= Project)"

lemma vbasic_map_inv:
  "map_vbasic (vbasic_map f) = f"
  by (auto simp add:vbasic_map_def map_vbasic_def)

term "bcarrier"

definition "bdcarrier x \<equiv> bcarrier x \<inter> DEFINED"

lemma map_vbasic_inv:
  assumes 
    "dom f \<subseteq> bdcarrier BTYPE('a::vbasic)"
    "ran f \<subseteq> bdcarrier BTYPE('b::vbasic)"
  shows "vbasic_map (map_vbasic f :: 'a \<rightharpoonup> 'b) = f"
  using assms
  apply (auto simp add:vbasic_map_def map_vbasic_def)
  apply (rule ext)
  apply (case_tac "Project x :: 'a option")
  apply (auto simp add:bdcarrier_def)
  apply (erule Project_None)
  apply (auto simp add:DEFINED_def bcarrier_def)
  apply (metis domIff mem_Collect_eq set_mp)
  apply (metis domIff mem_Collect_eq set_mp)
  apply (drule Project_Some)
  apply (case_tac "f (Inject a)")
  apply (auto)
  apply (case_tac "Project aa :: 'b option")
  apply (auto)
  apply (erule Project_None)
  apply (metis (lifting) mem_Collect_eq ranI set_rev_mp)
  apply (metis mem_Collect_eq ranI set_mp)
done


lemma vbasic_map_inj:
  "inj vbasic_map"
  by (metis injI vbasic_map_inv)

lemma vbasic_map_dom: "dom (vbasic_map f) = Inject ` dom f"
  apply (auto simp add:vbasic_map_def)
  apply (case_tac "Project x :: 'a option", simp_all, case_tac "f a", auto)
done

lemma vbasic_map_ran: "ran (vbasic_map f) = Inject ` ran f"
  apply (auto simp add:vbasic_map_def ran_def)
  apply (case_tac "Project a :: 'a option", simp_all, case_tac "f aa", auto)
  apply (rule_tac x="Inject a" in exI)
  apply (auto)
done


(*
lemma vbasic_map_ran: "ran (vbasic_map f) = Inject ` ran f"
  apply (force simp add:vbasic_map_def ran_def image_def)
*)

lemma map_vbasic_dom: "dom (map_vbasic f) \<subseteq> (the\<circ>Project) ` dom f"
  apply (auto simp add:map_vbasic_def)
  apply (metis Inject_Project bind_lzero domIff image_compose image_iff option.distinct(1) the.simps)
done

lift_definition vbasic_fmap :: "('a::vbasic, 'b::vbasic) fmap \<Rightarrow> (vbasic, vbasic) fmap"
is "vbasic_map"
  by (simp add:fmaps_def vbasic_map_dom)

lift_definition fmap_vbasic :: "(vbasic, vbasic) fmap \<Rightarrow> ('a::vbasic, 'b::vbasic) fmap" 
is "map_vbasic"
  apply (simp add:fmaps_def)
  apply (metis finite_imageI finite_subset map_vbasic_dom)
done

lemma vbasic_fmap_inv:
  "fmap_vbasic (vbasic_fmap x) = x"
  by (auto simp add:fmap_vbasic.rep_eq vbasic_fmap.rep_eq vbasic_map_inv)

lemma vbasic_fmap_inj:
  "inj vbasic_fmap"
  by (metis injI vbasic_fmap_inv)

(*
lemma vbasic_fmap_inv:
  "vbasic_fmap (fmap_vbasic x) = x"
  apply (auto simp add:fmap_vbasic.rep_eq vbasic_fmap.rep_eq vbasic_map_inv)
*)

lemma vbasic_map_dest: "vbasic_map f x = Some y \<Longrightarrow> \<exists> a b. x = Inject a \<and> f a = Some b \<and> Project y = Some b"
  apply (simp add:vbasic_map_def)
  apply (case_tac "Project x :: 'a option", simp_all)
  apply (case_tac "f a", simp_all)
  apply (rule_tac x="a" in exI)
  apply (auto)
done

lemma vbasic_mapE [elim!]: 
  assumes 
    "vbasic_map f x = Some y" 
    "\<And> a b. \<lbrakk>x = Inject a; f a = Some b; Project y = Some b\<rbrakk> \<Longrightarrow> P"
  shows "P"
  by (insert assms, auto dest!:vbasic_map_dest)


(*
definition vbasic_map :: "('a::vbasic, 'b::vbasic) fmap \<Rightarrow> vbasic \<Rightarrow> vbasic option" where
"vbasic_map f \<equiv> (\<lambda> x. ((Project x :: 'a option) >>= Rep_fmap f) >>= Some \<circ> Inject)"

definition map_vbasic :: "(vbasic, vbasic) fmap \<Rightarrow> ('a::vbasic \<Rightarrow> 'b::vbasic option)" where
"map_vbasic f \<equiv> (\<lambda> x::'a. \<langle>f\<rangle>\<^sub>m (Inject x) >>= Project)"

lemma vbasic_map_dest: "vbasic_map f x = Some y \<Longrightarrow> \<exists> a b. x = Inject a \<and> \<langle>f\<rangle>\<^sub>m a = Some b \<and> Project y = Some b"
  apply (simp add:vbasic_map_def)
  apply (case_tac "Project x :: 'a option", simp_all)
  apply (case_tac "Rep_fmap f a", simp_all)
  apply (rule_tac x="a" in exI)
  apply (auto)
done

lemma vbasic_mapE [elim!]: 
  assumes 
    "vbasic_map f x = Some y" 
    "\<And> a b. \<lbrakk>x = Inject a; \<langle>f\<rangle>\<^sub>m a = Some b; Project y = Some b\<rbrakk> \<Longrightarrow> P"
  shows "P"
  by (insert assms, auto dest!:vbasic_map_dest)

lemma vbasic_map_dom: "dom (vbasic_map f) = Inject ` dom (Rep_fmap f)"
  apply (auto simp add:vbasic_map_def)
  apply (case_tac "Project x :: 'a option", simp_all, case_tac "Rep_fmap f a", auto)
done

lemma map_vbasic_dom: "dom (map_vbasic f) \<subseteq> (the \<circ> Project) ` dom (Rep_fmap f)"
  apply (auto)
  apply (case_tac "Rep_fmap f (Inject x)", simp add:map_vbasic_def)
  apply (simp add:dom_def image_def)
  apply (metis Inject_Project the.simps)
done

lemma vbasic_map_inj [simp]: "vbasic_map f = vbasic_map g \<Longrightarrow> f = g"
  apply (rule fmext)
  apply (auto simp add:vbasic_map_def)
  apply (drule_tac x="Inject x" and y="Inject x" in cong, simp)
  apply (simp)
  apply (case_tac "Rep_fmap f x")
  apply (case_tac[!] "Rep_fmap g x")
  apply (simp_all)
done

lemma finite_dom_vbasic_map[simp]: "finite (dom (vbasic_map f))"
  by (simp add:vbasic_map_dom)

lemma finite_dom_map_vbasic[simp]: "finite (dom (map_vbasic f))"
  by (auto intro: finite_subset[OF map_vbasic_dom])
*)
  
instantiation fmap :: (vbasic, vbasic) vbasic
begin

definition Inject_fmap :: "('a, 'b) fmap \<Rightarrow> vbasic" where
"Inject_fmap f = FinMapI BTYPE('a) BTYPE('b) (vbasic_fmap f)"

definition Type_fmap :: "('a, 'b) fmap itself => vbasict" where
"Type_fmap x = MapBT BTYPE('a) BTYPE('b)"

instance proof
  fix x y :: "('a, 'b) fmap"
  assume "Inject x = Inject y"
  thus "x = y"
    by (metis (full_types) FinMapI_inj Inject_fmap_def vbasic_fmap_inv)

next
  
  show "range (Inject :: ('a,'b) fmap \<Rightarrow> vbasic) = {x. x :\<^sub>b BTYPE(('a,'b) fmap) \<and> \<D> x}"
  proof (auto simp add:Inject_fmap_def Type_fmap_def)
    fix x :: "('a,'b) fmap"
    show "FinMapI BTYPE('a) BTYPE('b) (vbasic_fmap x) :\<^sub>b MapBT (BTYPE('a)) (BTYPE('b))"     
      by (force intro!:FinMapI_type simp add:fdom.rep_eq fran.rep_eq vbasic_fmap.rep_eq vbasic_map_dom ran_def)

  next
    fix x :: "('a,'b) fmap"
(*
    obtain xs where "x = list_fmap xs" "distinct (map fst xs)" "sorted (map fst xs)"
      by (metis fmap_list_inv fmap_list_props(1) fmap_list_props(2))
*)

    show "\<D> (FinMapI BTYPE('a) BTYPE('b) (vbasic_fmap x))"
      by (auto simp add:defined fdom.rep_eq fran.rep_eq vbasic_fmap.rep_eq DEFINED_def vbasic_map_dom vbasic_map_ran)
  next
    fix f :: "(vbasic, vbasic) fmap"

    assume tyassm:
      "\<forall>x. x\<in>\<langle>fdom f\<rangle>\<^sub>f \<longrightarrow> x :\<^sub>b BTYPE('a)"
      "\<forall>y. y\<in>\<langle>fran f\<rangle>\<^sub>f \<longrightarrow> y :\<^sub>b BTYPE('b)" 
    and defassm: "\<D> (FinMapI BTYPE('a) BTYPE('b) f)"


    thus "FinMapI BTYPE('a) BTYPE('b) f \<in> range (Inject :: ('a,'b) fmap \<Rightarrow> vbasic)"
      apply (auto simp add:image_def Inject_fmap_def defined)
      apply (rule_tac x="(fmap_vbasic f)" in exI)
      apply (rule_tac f="FinMapI BTYPE('a) BTYPE('b)" in cong)
      apply (auto simp add:vbasic_map_inv vbasic_fmap.rep_eq fmap_vbasic.rep_eq fdom.rep_eq fran.rep_eq)
      apply (rule_tac map_vbasic_inv[THEN sym])
      apply (auto simp add:bdcarrier_def bcarrier_def)
    done
  qed
qed

end
 
subsection {* Injecting functions over basic values *}

definition vfun1 :: "('a::vbasic \<Rightarrow> 'b::vbasic) \<Rightarrow> ('a set) \<Rightarrow> vdmv" where
"vfun1 \<equiv> \<lambda> f P. FuncD BTYPE('a) VTYPE('b) 
                      (\<lambda> x. case (Project x) of 
                              None \<Rightarrow> BotD (VTYPE('b))
                            | Some v \<Rightarrow> if (v \<in> P) then BasicD (Inject (f v)) 
                                                   else BotD (VTYPE('b)))"

definition vfun2 :: 
  "('a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic) \<Rightarrow>
   'a set \<Rightarrow> 'b set \<Rightarrow> vdmv" where
"vfun2 \<equiv> \<lambda> f P Q. FuncD BTYPE('a) (BTYPE('b) \<rightarrow> VTYPE('c))
                        (\<lambda> x. case (Project x) of
                                None \<Rightarrow> BotD (BTYPE('b) \<rightarrow> VTYPE('c))
                              | Some v \<Rightarrow> if (v \<in> P) then vfun1 (f v) Q 
                                                     else BotD (BTYPE('b) \<rightarrow> VTYPE('c)))"

lemma vfun1_type [typing]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "vfun1 f P :\<^sub>v BTYPE('a) \<rightarrow> VTYPE('b)"
  apply (simp add:vfun1_def)
  apply (rule FuncD_type)
  apply (case_tac "Project x :: 'a option")
  apply (auto)
done

lemma vfun2_type [typing]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  shows "vfun2 f P Q :\<^sub>v BTYPE('a) \<rightarrow> BTYPE('b) \<rightarrow> VTYPE('c)"
  apply (simp add:vfun2_def)
  apply (rule FuncD_type)
  apply (case_tac "Project x :: 'a option")
  apply (auto intro:typing)
done

fun InjVB :: "'a::vbasic option \<Rightarrow> vdmv" where
"InjVB None = BotD VTYPE('a)" |
"InjVB (Some x) = BasicD (Inject x)"

definition ProjVB :: "vdmv \<Rightarrow> 'a::vbasic option" where
"ProjVB x = (if (\<D> x \<and> x \<in> range BasicD) then Project (ProjBasicD x) else None)"

lemma InjVB_inv[simp]: "ProjVB (InjVB x) = x"
  by (case_tac x, auto simp add:ProjVB_def)

lemma InjVB_nbot [defined]: "\<D> (InjVB (Some x))"
  by (simp)

lemma InjVB_vbvalues [simp]: "InjVB x \<in> vbvalues"
  apply (case_tac x)
  apply (auto simp add:vbvalues_def)
  apply (metis Inject_type)
done

end
