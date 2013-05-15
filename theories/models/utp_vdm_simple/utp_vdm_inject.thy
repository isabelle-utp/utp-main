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
  and   Type    :: "'a itself \<Rightarrow> vdmt"
  assumes Inject_inj [simp]: "Inject x = Inject y \<Longrightarrow> x = y"
  and     Inject_range [simp]: "range Inject = {x. x :\<^sub>b Type (TYPE('a)) \<and> \<D>\<^sub>b x}"

text {* InjB and ProjB lift the Inject and Project functions up to domain level. *}

context vbasic
begin

definition Project :: "vbasic \<Rightarrow> 'a option" where
"Project x \<equiv> if (x :\<^sub>b Type (TYPE('a)) \<and> \<D>\<^sub>b x) then Some (inv Inject x) else None"

lemma Inject_type[simp]: "Inject x :\<^sub>b Type (TYPE('a))"
  by (insert Inject_range, auto simp add:image_def)

lemma Inject_Project [simp]: "Project (Inject x) = Some x"
  apply (auto simp add:Project_def)
  apply (metis Inject_inj injI inv_f_f)
  apply (metis (mono_tags) Inject_range mem_Collect_eq rangeI)
done

lemma Project_Inject [simp]: 
  "\<And> x. \<lbrakk> x :\<^sub>b Type TYPE('a); \<D>\<^sub>b x \<rbrakk> \<Longrightarrow> Inject (the (Project x)) = x"
  by (auto intro:f_inv_into_f simp add:Project_def)

lemma Project_bot [simp]:
  "Project BotI = None"
  by (simp add:Project_def)

lemma Project_dom [simp]: "\<And> x y. Project x = Some y \<Longrightarrow> x :\<^sub>b Type TYPE('a)"
  by (case_tac "x :\<^sub>b Type TYPE('a)", auto simp add:Project_def)

lemma Inject_Project_comp [simp]:
  "Project \<circ> Inject = Some" 
  by (simp add:comp_def)

lemma Inject_defined [simp]:
  "\<D>\<^sub>b (Inject x)"
  by (metis Inject_Project Project_def option.simps(2))
  
lemma Project_defined [dest]: 
  "\<lbrakk> x :\<^sub>b Type TYPE('a); \<D>\<^sub>b x \<rbrakk> \<Longrightarrow> Project x \<noteq> None"
  by (metis Project_def option.simps(3))

lemma Project_Some [dest,simp]: 
  "\<And> x. Project x = Some y \<Longrightarrow> x = Inject y"
  apply (frule Project_dom)
  apply (drule Project_Inject)
  apply (metis Project_def option.simps(3))
  apply (simp)
done

lemma Inject_Project_list [simp]:
  assumes "foldr (op \<and> \<circ> \<D>\<^sub>b) xs True" "\<forall>x\<in>set xs. x :\<^sub>b Type TYPE('a)"
  shows "xs = map Inject (map (the \<circ> Project) xs)"
using assms by (induct xs, auto)

end

subsection {* Naturals are injectable *}

instantiation nat :: vbasic
begin
definition "Inject_nat \<equiv> NatI"
definition Type_nat :: "nat itself \<Rightarrow> vdmt" where
"Type_nat x \<equiv> NatT"

declare Type_nat_def [simp]

instance
  by (intro_classes, auto simp add:Inject_nat_def) 
end

lemma Type_nat: "NatT = Type TYPE(nat)"
  by (simp add:Type_nat_def)

subsection {* Integers are injectable *}

instantiation int :: vbasic
begin
definition "Inject_int \<equiv> IntI"
definition Type_int :: "int itself \<Rightarrow> vdmt" where
"Type_int x \<equiv> IntT"

declare Type_int_def [simp]

instance by (intro_classes, auto simp add:Inject_int_def) 
end

lemma Type_int: "IntT = Type TYPE(int)"
  by (simp add:Type_int_def)

subsection {* Bools are injectable *}

instantiation bool :: vbasic
begin
definition "Inject_bool \<equiv> BoolI"
definition "Type_bool (x::bool itself) \<equiv> BoolT"

declare Type_bool_def [simp]

instance by (intro_classes, auto simp add:Inject_bool_def) 
end

lemma Type_bool: "BoolT = Type TYPE(bool)"
  by (simp add:Type_bool_def)

subsection {* Rationals are injectable *}

instantiation rat :: vbasic
begin

definition "Inject_rat \<equiv> RatI"
definition "Type_rat (x::rat itself) = RatT"

declare Type_rat_def [simp]

instance by (intro_classes, auto simp add:Inject_rat_def)
end

lemma Type_rat: "RatT = Type TYPE(rat)"
  by (simp add:Type_rat_def)

subsection {* Characters are injectable *}

instantiation char :: vbasic
begin

definition "Inject_char \<equiv> CharI"
definition "Type_char (x::char itself) \<equiv> CharT"

instance by (intro_classes, auto simp add:Inject_char_def Type_char_def)
end

lemma Type_char: "CharT = Type TYPE(char)"
  by (simp add:Type_char_def)

subsection {* Pairs are injectable *}

instantiation prod :: (vbasic, vbasic) vbasic
begin

definition Inject_prod :: "'a \<times> 'b \<Rightarrow> vbasic" where
"Inject_prod \<equiv> \<lambda> x. PairI (Inject (fst x)) (Inject (snd x))"
                
definition Type_prod :: "('a \<times> 'b) itself \<Rightarrow> vdmt" where
"Type_prod x = PairT (Type (TYPE('a))) (Type (TYPE('b)))"

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
"Inject_list xs = ListI (map Inject xs)"

definition Type_list :: "'a list itself \<Rightarrow> vdmt" where
"Type_list xs \<equiv> ListT (Type (TYPE('a)))"

instance 
  apply (intro_classes)
  apply (simp add:Inject_list_def)
  apply (metis Inject_Project_comp map_map option.inject option_list_map)
  apply (auto simp add:Type_list_def Inject_list_def)
  apply (auto simp add:image_def Inject_list_def)
  apply (induct_tac xa, auto)
  apply (rule_tac x="map (the \<circ> Project :: vbasic \<Rightarrow> 'a) xs" in exI)
  apply (simp)
  apply (metis Inject_Project_list map_map)
done
end

(*
*)

(* Unfortunately the injections only work for monomorphically typed function, at the moment
   which is no surprise as we need explicit machinery to build polymorphic versions *)
lemma Type_list: "ListT (Type TYPE('a)) = Type(TYPE(('a::vbasic) list))"
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

lemma FSetI_inj: "FSetI f = FSetI g \<Longrightarrow> f = g"
  apply (simp add:FSetI_def flist_def)
  apply (metis Rep_fset_finite Rep_fset_inject sorted_list_of_set_inj)
done

instantiation fset :: (vbasic) vbasic
begin

definition Inject_fset :: "'a fset \<Rightarrow> vbasic" where
"Inject_fset xs = FSetI (Abs_fset (Inject ` Rep_fset xs))"

(*
definition Project_fset :: "vbasic \<Rightarrow> 'a fset option" where 
"Project_fset xs = (ProjFSetI xs >>= (\<lambda> x. option_set (Project ` Rep_fset x))) >>= Some \<circ> Abs_fset"
*)

definition Type_fset :: "'a fset itself \<Rightarrow> vdmt" where
"Type_fset x = FSetT (Type (TYPE('a)))"

instance 
  apply (intro_classes)
  apply (simp add: Inject_fset_def)
  apply (drule FSetI_inj)
  apply (subgoal_tac "Inject ` Rep_fset x = Inject ` Rep_fset y")
  apply (simp)
  apply (metis Inject_Project_comp Rep_fset_inject inj_Some inj_on_Un_image_eq_iff inj_on_imageI2)
  apply (metis Rep_fset_finite Rep_fset_inv finite_imageI)
  apply (simp add:Type_fset_def Inject_fset_def image_def)
  apply (auto)
  apply (rule FSetI_type)
  apply (auto simp add:flist_def)
  apply (auto simp add:FSetI_def flist_def)

(*
  apply (induct_tac xa)
  apply (rule_tac x="Abs_fset ((the \<circ> Project) ` (set xs))" in exI)
  apply (simp)
  apply (metis finite_set sorted_distinct_set_unique sorted_list_of_set)
done
*)
sorry
end

subsection {* Finite maps are injectable *}

definition vbasic_map :: "('a::{vbasic,linorder}, 'b::{vbasic,linorder}) fmap \<Rightarrow> vbasic \<Rightarrow> vbasic option" where
"vbasic_map f \<equiv> (\<lambda> x. ((Project x :: 'a option) >>= Rep_fmap f) >>= Some \<circ> Inject)"

definition map_vbasic :: "(vbasic, vbasic) fmap \<Rightarrow> ('a::{vbasic,linorder} \<Rightarrow> 'b::{vbasic,linorder} option)" where
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
  
instantiation fmap :: ("{vbasic,linorder}", "{vbasic,linorder}") vbasic
begin

definition Inject_fmap :: "('a::{vbasic,linorder}, 'b::{vbasic,linorder}) fmap \<Rightarrow> vbasic" where
"Inject_fmap f = FinMapI (Abs_fmap (vbasic_map f))"

definition Type_fmap :: "('a, 'b) fmap itself => vdmt" where
"Type_fmap x = MapT (Type (TYPE('a))) (Type (TYPE('b)))"

instance proof
  fix x y :: "('a, 'b) fmap"
  assume "Inject x = Inject y"
  thus "x = y"
    by (auto dest!:FinMapI_inj Abs_fmap_inj vbasic_map_inj simp add:Inject_fmap_def)

next
  
  show "range (Inject :: ('a,'b) fmap \<Rightarrow> vbasic) = {x. x :\<^sub>b Type TYPE(('a,'b) fmap) \<and> \<D>\<^sub>b x}"
  proof (auto simp add:Inject_fmap_def Type_fmap_def)
    fix x :: "('a,'b) fmap"
    show "FinMapI (Abs_fmap (vbasic_map x)) :\<^sub>b MapT (Type TYPE('a)) (Type TYPE('b))"      
      by (auto intro!:FinMapI_type simp add:fdom_def fran_def Rep_fmap_inverse
         ,force simp add:ran_def)


  next
    fix x :: "('a,'b) fmap"
    show "\<D>\<^sub>b (FinMapI (Abs_fmap (vbasic_map x)))"
      sorry

  next
    fix f :: "(vbasic, vbasic) fmap"
    assume tyassm:
      "\<forall>x\<in>Rep_fset (Fmap.fdom f). x :\<^sub>b Type TYPE('a)"
      "\<forall>y\<in>Rep_fset (Fmap.fran f). y :\<^sub>b Type TYPE('b)"

    thus "FinMapI f \<in> range (Inject :: ('a,'b) fmap \<Rightarrow> vbasic)" 
    proof -
      have "Abs_fmap (vbasic_map (Abs_fmap (map_vbasic f :: 'a \<rightharpoonup> 'b))) = f"
        apply (rule fmext)
        apply (simp)
        apply (simp add:vbasic_map_def)
        apply (case_tac "Project x :: 'a option")
        apply (simp)
      sorry

(*
        apply (metis Project_defined domIff fdom.rep_eq tyassm(1))
        apply (simp add:map_vbasic_def)
        apply (auto dest!: Project_Some)
        apply (case_tac "Rep_fmap f (Inject a)", simp_all)
        apply (case_tac "Project aa :: 'b option", simp_all)
        apply (insert tyassm(2))
        apply (simp add:fran_def)
        apply (force simp add:ran_def)
        apply (force dest!: Project_Some)
      done
*)

      thus ?thesis
        apply (simp add:image_def Inject_fmap_def) 
        apply (rule_tac x="(Abs_fmap (map_vbasic f))" in exI)
        apply (rule_tac f="FinMapI" in cong, simp)
        apply (force)
      done
    qed
  qed
qed
end

class vdmv = 
  fixes InjectV  :: "'a \<Rightarrow> vdmv"
  and   TypeV    :: "'a itself \<Rightarrow> vdmt"
  assumes InjectV_inj [simp]: "InjectV x = InjectV y \<Longrightarrow> x = y"
  and     InjectV_range [simp]: "range InjectV = {x. x :\<^sub>v TypeV (TYPE('a)) \<and> \<D>\<^sub>v x}"

context vdmv
begin

definition ProjectV :: "vdmv \<Rightarrow> 'a option" where
"ProjectV x \<equiv> if (x :\<^sub>v TypeV (TYPE('a)) \<and> \<D>\<^sub>v x) then Some (inv InjectV x) else None"

lemma InjectV_type[simp]: "InjectV x :\<^sub>v TypeV (TYPE('a))"
  by (insert InjectV_range, auto simp add:image_def)

lemma InjectV_ProjectV [simp]: "ProjectV (InjectV x) = Some x"
  apply (auto simp add:ProjectV_def)
  apply (metis InjectV_inj injI inv_f_f)
  apply (metis (mono_tags) InjectV_range mem_Collect_eq rangeI)
done

lemma ProjectV_InjectV [simp]: 
  "\<And> x. \<lbrakk> x :\<^sub>v TypeV TYPE('a); \<D>\<^sub>v x \<rbrakk> \<Longrightarrow> InjectV (the (ProjectV x)) = x"
  by (auto intro:f_inv_into_f simp add:ProjectV_def)

lemma ProjectV_dom [simp]: "\<And> x y. ProjectV x = Some y \<Longrightarrow> x :\<^sub>v TypeV TYPE('a)"
  by (case_tac "x :\<^sub>v TypeV TYPE('a)", auto simp add:ProjectV_def)

lemma InjectV_ProjectV_comp [simp]:
  "ProjectV \<circ> InjectV = Some" 
  by (simp add:comp_def)

lemma Inject_defined [simp]:
  "\<D>\<^sub>v (InjectV x)"
  by (metis InjectV_ProjectV ProjectV_def option.simps(2))
  
lemma ProjectV_defined [dest]: 
  "\<lbrakk> x :\<^sub>v TypeV TYPE('a); \<D>\<^sub>v x \<rbrakk> \<Longrightarrow> ProjectV x \<noteq> None"
  by (metis ProjectV_def option.simps(3))

lemma ProjectV_Some [dest,simp]: 
  "\<And> x. ProjectV x = Some y \<Longrightarrow> x = InjectV y"
  apply (frule ProjectV_dom)
  apply (drule ProjectV_InjectV)
  apply (metis ProjectV_def option.simps(3))
  apply (simp)
done

lemma InjectV_ProjectV_list [simp]:
  assumes "foldr (op \<and> \<circ> \<D>\<^sub>v) xs True" "\<forall>x\<in>set xs. x :\<^sub>v TypeV TYPE('a)"
  shows "xs = map InjectV (map (the \<circ> ProjectV) xs)"
using assms by (induct xs, auto)

end

instantiation "fun" :: (vbasic,vdmv) vdmv
begin

definition InjectV_fun :: "('a \<Rightarrow> 'b) \<Rightarrow> vdmv" where
"InjectV_fun f = FuncD (\<lambda> x. case (Project x) of Some v \<Rightarrow> InjectV (f v) | None \<Rightarrow> BotD)"

definition TypeV_fun :: "('a \<Rightarrow> 'b) itself \<Rightarrow> vdmt" where
"TypeV_fun f = (Type (TYPE('a))) \<rightarrow> (TypeV (TYPE('b)))"

instance 
  apply (intro_classes)
  apply (rule_tac ext)
  apply (simp add:InjectV_fun_def fun_eq_iff)
  apply (drule_tac x="Inject xa" in spec)
  apply (force)
  apply (auto)
  apply (simp add:InjectV_fun_def TypeV_fun_def)
  apply (rule)
  apply (case_tac "Project x :: 'a option")
  apply (force)
  apply (simp)
  apply (simp)
  apply (simp add:InjectV_fun_def)
  apply (simp add:InjectV_fun_def TypeV_fun_def)
  apply (erule FuncT_type_cases')
  apply (auto)
  apply (simp add:image_def)
  apply (rule_tac x="the \<circ> ProjectV \<circ> f \<circ> Inject" in exI)
  apply (simp add:InjectV_fun_def)
  apply (rule ext)
  apply (case_tac "Project x :: 'a option")
  apply (simp_all)
sorry
end
  
subsection {* Injecting functions over basic values *}

definition vfun1 :: "('a::vbasic \<Rightarrow> 'b::vbasic) \<Rightarrow> ('a set) \<Rightarrow> vdmv" where
"vfun1 \<equiv> \<lambda> f P. FuncD (\<lambda> x. case (Project x) of 
                              None \<Rightarrow> BotD 
                            | Some v \<Rightarrow> if (v \<in> P) then BasicD (Inject (f v)) else BotD)"

definition vfun2 :: 
  "('a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic) \<Rightarrow>
   'a set \<Rightarrow> 'b set \<Rightarrow> vdmv" where
"vfun2 \<equiv> \<lambda> f P Q. FuncD (\<lambda> x. case (Project x) of
                                None \<Rightarrow> BotD
                              | Some v \<Rightarrow> if (v \<in> P) then vfun1 (f v) Q else BotD)"

lemma vfun1_type [typing]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "vfun1 f P :\<^sub>v Type TYPE('a) \<rightarrow> Type TYPE('b)"
  apply (simp add:vfun1_def)
  apply (rule FuncD_type)
  apply (case_tac "Project x :: 'a option")
  apply (auto)
done

lemma vfun2_type [typing]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  shows "vfun2 f P Q :\<^sub>v Type TYPE('a) \<rightarrow> Type TYPE('b) \<rightarrow> Type TYPE('c)"
  apply (simp add:vfun2_def)
  apply (rule FuncD_type)
  apply (case_tac "Project x :: 'a option")
  apply (auto intro:typing)
done

definition "InjVB  x \<equiv> BasicD (Inject x)"
definition "ProjVB x \<equiv> the (Project (ProjBasicD x))"

lemma InjVB_inv[simp]: "ProjVB (InjVB x) = x"
  by (simp add:ProjVB_def InjVB_def)

lemma InjVB_nbot [simp]: "\<D>\<^sub>v (InjVB x)"
  by (simp add:InjVB_def)

lemma InjVB_vbvalues [simp]: "InjVB x \<in> vbvalues"
  apply (auto simp add:vbvalues_def InjVB_def)
  apply (metis Inject_type)
done

end
