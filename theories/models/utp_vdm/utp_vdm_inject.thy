theory utp_vdm_inject
imports utp_vdm_values "../../utils/HOLCF_extra/Sfun_Extra"
begin

section {* Injecting basic values *}

subsection {* Injecting basic values into vval *}

fixrec ProjBasicV :: "vval \<rightarrow> vbasic lift" where
"x \<noteq> \<bottom> \<Longrightarrow> ProjBasicV\<cdot>(BasicV\<cdot>x) = x"

lemma ProjBasicV_bot [simp]: 
  "ProjBasicV\<cdot>\<bottom> = \<bottom>"
  "\<And> xs. xs \<noteq> \<bottom> \<Longrightarrow> ProjBasicV\<cdot>(SetV\<cdot>xs) = \<bottom>"
  "\<And> f. f \<noteq> \<bottom> \<Longrightarrow> ProjBasicV\<cdot>(FuncV\<cdot>f) = \<bottom>" 
  by (fixrec_simp)+

lemma ProjBasicV_simps [simp]:
  "ProjBasicV\<cdot>(SetV\<cdot>xs) = \<bottom>"
  "ProjBasicV\<cdot>(FuncV\<cdot>f) = \<bottom>"
  apply (case_tac "xs = \<bottom>", simp_all)
  apply (case_tac "f = \<bottom>", simp_all)
done

lemma BasicV_inv [simp]:
  "ProjBasicV\<cdot>(BasicV\<cdot>x) = x"
  by (case_tac x, simp_all)

definition IsBasicV where "IsBasicV v \<longleftrightarrow> ProjBasicV\<cdot>v \<noteq> \<bottom>"

lemma IsBasicV_simps [simp]: 
  "IsBasicV x \<Longrightarrow> x \<noteq> \<bottom>"
  "\<not> IsBasicV \<bottom>"
  "\<And> x. \<not> IsBasicV (SetV\<cdot>x)"
  "\<And> x. \<not> IsBasicV (FuncV\<cdot>x)"
  by (case_tac[!] x, simp_all add:IsBasicV_def)

lemma ProjBasicV_inv [simp] :
  "IsBasicV x \<Longrightarrow> BasicV\<cdot>(ProjBasicV\<cdot>x) = x"
  apply (simp add:IsBasicV_def)
  apply (case_tac x, simp_all)
done

subsection {* The vbasic class *}

text {* To make injecting values into the domain easy, we introduce a type class
  representing HOL values which can be injected into the domain. It consists of
  an injection, projection and a function which gives a vtype equivalent for the 
  given HOL type. When we introduce subtypes this type will be the most general
  type. It follows that injecting any value gives a vval of the correct vtype.

  Perhaps the most important thing this class allows us to do is to inject arbitrary
  HOL functions over basic values into the value space.
*}

class vbasic = discrete_cpo +
  fixes Inject  :: "'a \<Rightarrow> vbasic"
  and   Type    :: "'a itself \<Rightarrow> vbtype"
  assumes Inject_inj [simp]: "Inject x = Inject y \<Longrightarrow> x = y"
  and     Inject_range [simp]: "range Inject = {x. x :\<^sub>b Type (TYPE('a))}"

text {* InjB and ProjB lift the Inject and Project functions up to domain level. *}

lemma cont_Inject [simp,cont2cont]: "cont Inject"
  by (simp)

context vbasic
begin

definition Project :: "vbasic \<Rightarrow> 'a option" where
"Project x \<equiv> if (x :\<^sub>b Type (TYPE('a))) then Some (inv Inject x) else None"

lemma Inject_type[simp]: "Inject x :\<^sub>b Type (TYPE('a))"
  by (insert Inject_range, auto simp add:image_def)

lemma Inject_Project [simp]: "Project (Inject x) = Some x"
  by (auto simp add:Project_def, metis Inject_inj injI inv_f_f)

lemma Project_Inject [simp]: "\<And> x. x :\<^sub>b Type TYPE('a) \<Longrightarrow> Inject (the (Project x)) = x"
  by (auto intro:f_inv_into_f simp add:Project_def)

lemma Project_dom [simp]: "\<And> x y. Project x = Some y \<Longrightarrow> x :\<^sub>b Type TYPE('a)"
  by (case_tac "x :\<^sub>b Type TYPE('a)", auto simp add:Project_def)

definition InjB :: "'a lift \<rightarrow> vbasic lift" where
"InjB \<equiv> \<Lambda> (Def x). Def (Inject x)"

definition ProjB :: "vbasic lift \<rightarrow> 'a lift" where
"ProjB \<equiv> \<Lambda> (Def x). case (Project x) of None \<Rightarrow> \<bottom> | Some (y :: 'a) \<Rightarrow> Def y"

lemma Inject_Project_comp [simp]:
  "Project \<circ> Inject = Some" 
  by (simp add:comp_def)

lemma Project_defined [dest]: "x :\<^sub>b Type TYPE('a) \<Longrightarrow> Project x \<noteq> None"
  by (metis Inject_Project Project_Inject option.simps(3))

lemma Project_Some [dest,simp]: "\<And> x. Project x = Some y \<Longrightarrow> x = Inject y"
  apply (frule Project_dom)
  apply (drule Project_Inject)
  apply (simp)
done


lemma InjB_simps [simp]:
(*  "InjB\<cdot>(Def x) = Def (Inject x)" *)
  "InjB\<cdot>\<bottom> = \<bottom>"
(*  "ProjB\<cdot>(Def (Inject x)) = Def x" *)
  "ProjB\<cdot>\<bottom> = \<bottom>"
  by (simp_all add:InjB_def ProjB_def)

lemma InjB_inv [simp]: "ProjB\<cdot>(InjB\<cdot>x) = x"
  apply (case_tac x)
  apply (simp_all add:InjB_def ProjB_def)
done

lemma InjB_type [intro]: "BasicV\<cdot>(InjB\<cdot>x) : BasicType (Type TYPE('a))"
  by (case_tac x, auto simp add:InjB_def)

lemma ProjB_inv [simp]: "x :\<^sub>b Type TYPE('a) \<Longrightarrow> InjB\<cdot>(ProjB\<cdot>(Def x)) = Def x"
  apply (simp add:InjB_def ProjB_def)
  apply (case_tac "(Project x :: 'a option)")
  apply (auto)
done

end

subsection {* Integers are injectable *}

instantiation int :: vbasic
begin
definition "Inject_int \<equiv> IntI"
definition Type_int :: "int itself \<Rightarrow> vbtype" where
"Type_int x \<equiv> IntT"

instance by (intro_classes, auto simp add:Inject_int_def Type_int_def) 
end

lemma Type_int: "IntT = Type TYPE(int)"
  by (simp add:Type_int_def)

subsection {* Bools are injectable *}

instantiation bool :: vbasic
begin
definition "Inject_bool \<equiv> BoolI"
definition "Type_bool (x::bool itself) \<equiv> BoolT"

instance by (intro_classes, auto simp add:Inject_bool_def Type_bool_def) 
end

lemma Type_bool: "BoolT = Type TYPE(bool)"
  by (simp add:Type_bool_def)

subsection {* Rationals are injectable *}

instantiation rat :: discrete_cpo
begin

definition below_rat_def:
  "(x::rat) \<sqsubseteq> y \<longleftrightarrow> x = y"

instance proof
qed (rule below_rat_def)

end

instantiation rat :: vbasic
begin

definition "Inject_rat \<equiv> RatI"
definition "Type_rat (x::rat itself) = RatT"

instance by (intro_classes, auto simp add:Inject_rat_def Type_rat_def)
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
                
definition Type_prod :: "('a \<times> 'b) itself \<Rightarrow> vbtype" where
"Type_prod x = PairT (Type (TYPE('a))) (Type (TYPE('b)))"

instance
  apply (intro_classes)
  apply (force simp add:Inject_prod_def)
  apply (auto simp add:Type_prod_def Inject_prod_def image_def)
  apply (metis Project_Inject)+
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

definition Type_list :: "'a list itself \<Rightarrow> vbtype" where
"Type_list xs \<equiv> ListT (Type (TYPE('a)))"

instance 
  apply (intro_classes)
  apply (simp add:Inject_list_def)
  apply (metis Inject_Project_comp map_map option.inject option_list_map)
  apply (auto simp add:Inject_list_def Type_list_def)
  apply (rule ListI_type)
  apply (auto simp add:image_def Inject_list_def)
  apply (metis Project_Inject ex_map_conv)
done
end

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

definition Type_fset :: "'a fset itself \<Rightarrow> vbtype" where
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
  apply (rule_tac x="Abs_fset ((the \<circ> Project) ` (set xs))" in exI)
  apply (simp)
  apply (metis finite_set sorted_distinct_set_unique sorted_list_of_set)
done
end

subsection {* Finite maps are injectable *}

definition vbasic_map :: "('a::{vbasic,linorder}, 'b::{vbasic,linorder}) fmap \<Rightarrow> vbasic \<Rightarrow> vbasic option" where
"vbasic_map f \<equiv> (\<lambda> x. ((Project x :: 'a option) >>= Rep_fmap f) >>= Some \<circ> Inject)"

definition map_vbasic :: "(vbasic, vbasic) fmap \<Rightarrow> ('a::{vbasic,linorder} \<Rightarrow> 'b::{vbasic,linorder} option)" where
"map_vbasic f \<equiv> (\<lambda> x::'a. fmlookup (Inject x) f >>= Project)"

lemma vbasic_map_dest: "vbasic_map f x = Some y \<Longrightarrow> \<exists> a b. x = Inject a \<and> fmlookup a f = Some b \<and> Project y = Some b"
  apply (simp add:vbasic_map_def)
  apply (case_tac "Project x :: 'a option", simp_all)
  apply (case_tac "Rep_fmap f a", simp_all)
  apply (rule_tac x="a" in exI)
  apply (auto simp add:fmlookup_def)
done

lemma vbasic_mapE [elim!]: 
  assumes 
    "vbasic_map f x = Some y" 
    "\<And> a b. \<lbrakk>x = Inject a; fmlookup a f = Some b; Project y = Some b\<rbrakk> \<Longrightarrow> P"
  shows "P"
  by (insert assms, auto dest!:vbasic_map_dest)

lemma vbasic_map_dom: "dom (vbasic_map f) = Inject ` dom (Rep_fmap f)"
  apply (auto simp add:vbasic_map_def)
  apply (case_tac "Project x :: 'a option", simp_all, case_tac "Rep_fmap f a", auto)
done

lemma map_vbasic_dom: "dom (map_vbasic f) \<subseteq> (the \<circ> Project) ` dom (Rep_fmap f)"
  apply (auto)
  apply (case_tac "Rep_fmap f (Inject x)", simp add:fmlookup_def map_vbasic_def)
  apply (simp add:dom_def image_def)
  apply (metis Inject_Project the.simps)
done

lemma vbasic_map_inj [simp]: "vbasic_map f = vbasic_map g \<Longrightarrow> f = g"
  apply (rule fmext)
  apply (auto simp add:vbasic_map_def fmlookup_def)
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

definition Type_fmap :: "('a, 'b) fmap itself => vbtype" where
"Type_fmap x = MapT (Type (TYPE('a))) (Type (TYPE('b)))"

instance proof
  fix x y :: "('a, 'b) fmap"
  assume "Inject x = Inject y"
  thus "x = y"
    by (auto dest!:FinMapI_inj Abs_fmap_inj vbasic_map_inj simp add:Inject_fmap_def)

next
  
  show "range (Inject :: ('a,'b) fmap \<Rightarrow> vbasic) = {x. x :\<^sub>b Type TYPE(('a,'b) fmap)}"
  proof (auto simp add:Inject_fmap_def Type_fmap_def)
    fix x :: "('a,'b) fmap"
    show "FinMapI (Abs_fmap (vbasic_map x)) :\<^sub>b MapT (Type TYPE('a)) (Type TYPE('b))"      
      by (auto intro!:FinMapI_type simp add:fdom_def fran_def Rep_fmap_inverse
         ,force simp add:ran_def)

  next
    fix f :: "(vbasic, vbasic) fmap"
    assume tyassm:
      "\<forall>x\<in>Rep_fset (Fmap.fdom f). x :\<^sub>b Type TYPE('a)"
      "\<forall>y\<in>Rep_fset (Fmap.fran f). y :\<^sub>b Type TYPE('b)"

    thus "FinMapI f \<in> range (Inject :: ('a,'b) fmap \<Rightarrow> vbasic)" 
    proof -
      have "Abs_fmap (vbasic_map (Abs_fmap (map_vbasic f :: 'a \<rightharpoonup> 'b))) = f"
        apply (rule fmext)
        apply (simp add:fmlookup_def)
        apply (simp add:vbasic_map_def)
        apply (case_tac "Project x :: 'a option")
        apply (simp_all)
        apply (metis Project_defined domIff fdom.rep_eq tyassm(1))
        apply (simp add:map_vbasic_def fmlookup_def)
        apply (auto dest!: Project_Some)
        apply (case_tac "Rep_fmap f (Inject a)", simp_all)
        apply (case_tac "Project aa :: 'b option", simp_all)
        apply (insert tyassm(2))
        apply (simp add:fran_def)
        apply (force simp add:ran_def)
        apply (force dest!: Project_Some)
      done

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
  
subsection {* Injecting functions over basic values *}

definition vbfun1 :: "('a::vbasic \<Rightarrow> 'b::vbasic) \<Rightarrow> ('a set) \<Rightarrow> (vbasic lift \<rightarrow> vbasic lift)" where
"vbfun1 \<equiv> \<lambda> f P. InjB oo (\<Lambda> (Def x). if (x \<in> P) then Def (f x) else \<bottom>) oo ProjB"

lemma vbfun1_cont [simp,cont2cont]: 
  "cont vbfun1"
  by (simp add:vbfun1_def)

lemma vbfun1_bot [simp]: "(vbfun1 f P)\<cdot>\<bottom> = \<bottom>"
  by (simp add:vbfun1_def InjB_def ProjB_def)

lemma vbfun1_app [simp]: 
  "x \<in> P \<Longrightarrow> vbfun1 f P\<cdot>(InjB\<cdot>(Def x)) = InjB\<cdot>(Def (f x))"
  by (simp add:vbfun1_def)

lemma vbfun1_napp [simp]: 
  "x \<notin> P \<Longrightarrow> vbfun1 f P\<cdot>(InjB\<cdot>(Def x)) = \<bottom>"
  by (simp add:vbfun1_def)

lemma vbfun1_nbot_exists:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  assumes "vbfun1 f P\<cdot>x \<noteq> \<bottom>"
  shows "\<exists> a::'a. x = InjB\<cdot>(Def a) \<and> a \<in> P"
  apply (insert assms)
  apply (case_tac x, simp_all)
  apply (simp add:vbfun1_def ProjB_def)
  apply (case_tac "Project a :: 'a option", simp_all)
  apply (case_tac "aa \<in> P")
  apply (simp add:InjB_def)
  apply (metis Project_Some)
  apply (simp)
done

lemma vbfun1_elim [elim]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  assumes "vbfun1 f P\<cdot>x \<noteq> \<bottom>" "\<And> a::'a. \<lbrakk> x = InjB\<cdot>(Def a); a \<in> P \<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  by (metis assms(1) assms(2) vbfun1_nbot_exists)

definition vbfun2 :: 
  "('a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic) \<Rightarrow>
   'a set \<Rightarrow> 'b set \<Rightarrow>
  (vbasic lift \<rightarrow> vbasic lift \<rightarrow> vbasic lift)" where
"vbfun2 \<equiv> \<lambda> f P Q. \<Lambda> a b. InjB\<cdot>((\<Lambda> (Def x) (Def y). if (x \<in> P \<and> y \<in> Q) then Def (f x y) else \<bottom>)\<cdot>(ProjB\<cdot>a)\<cdot>(ProjB\<cdot>b))"

lemma vbfun2_cont [simp,cont2cont]: 
  "cont vbfun2"
  by (simp add:vbfun2_def InjB_def ProjB_def)

lemma vbfun2_bot [simp]: 
  "(vbfun2 f P Q)\<cdot>\<bottom> = \<bottom>"
  "(vbfun2 f P Q)\<cdot>x\<cdot>\<bottom> = \<bottom>"
  apply (simp_all add:vbfun2_def InjB_def ProjB_def)
  apply (case_tac "x")
  apply (simp_all)
  apply (case_tac "Project a :: 'a option")
  apply (simp_all)
done

lemma vbfun2_app [simp]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  and   x :: "'a" 
  assumes "x \<in> P"
  shows "vbfun2 f P Q\<cdot>(InjB\<cdot>(Def x)) = vbfun1 (f x) Q"
  by (simp add:vbfun2_def vbfun1_def assms oo_def)

lemma vbfun2_napp [simp]: 
  "x \<notin> P \<Longrightarrow> vbfun2 f P Q\<cdot>(InjB\<cdot>(Def x)) = \<bottom>"
  "\<And> x y. y \<notin> Q \<Longrightarrow> (vbfun2 f P Q)\<cdot>x\<cdot>(InjB\<cdot>(Def y)) = \<bottom>"
  apply (simp add:vbfun2_def)
  apply (rule cfun_eqI)
  apply (simp)
  apply (case_tac "ProjB\<cdot>xa :: 'b lift")
  apply (simp_all)
  apply (simp add:vbfun2_def)
  apply (case_tac "ProjB\<cdot>x :: 'a lift")
  apply (simp_all)
done

lemma vbfun2_nbot_exists:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  assumes "vbfun2 f P Q\<cdot>x\<cdot>y \<noteq> \<bottom>"
  shows "\<exists> a::'a. x = InjB\<cdot>(Def a) \<and> a \<in> P" "\<exists> b::'b. y = InjB\<cdot>(Def b) \<and> b \<in> Q"
  apply (insert assms)
  apply (case_tac x, simp_all)
  apply (case_tac y, simp_all)
  apply (simp add:vbfun2_def ProjB_def)
  apply (case_tac "Project a :: 'a option", simp_all)
  apply (case_tac "Project aa :: 'b option", simp_all)
  apply (case_tac "ab \<in> P")
  apply (simp add:InjB_def)
  apply (metis Project_Some)
  apply (simp)
  apply (case_tac x, simp_all)
  apply (case_tac y, simp_all)
  apply (simp add:vbfun2_def ProjB_def)
  apply (case_tac "Project a :: 'a option", simp_all)
  apply (case_tac "Project aa :: 'b option", simp_all)
  apply (case_tac "ac \<in> Q")
  apply (simp add:InjB_def)
  apply (metis Project_Some)
  apply (simp)
done

lemma vbfun2_elim [elim]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  assumes 
    "vbfun2 f P Q\<cdot>x\<cdot>y \<noteq> \<bottom>" 
    "\<And> a::'a. \<And> b::'b. \<lbrakk> x = InjB\<cdot>(Def a); a \<in> P; y = InjB\<cdot>(Def b); b \<in> Q \<rbrakk> \<Longrightarrow> R"
  shows "R"
  by (metis assms vbfun2_nbot_exists)

definition "bplus \<equiv> vbfun2 ((op +) :: int \<Rightarrow> int \<Rightarrow> int) UNIV UNIV"

lemma bplus_test: "bplus\<cdot>(InjB\<cdot>(Def (5::int)))\<cdot>(InjB\<cdot>(Def (6::int))) = InjB\<cdot>(Def (11::int))"
  by (simp add:bplus_def)

fixrec ProjFuncV :: "vval \<rightarrow> (vval \<rightarrow>! vval)" where
"f \<noteq> \<bottom> \<Longrightarrow> ProjFuncV\<cdot>(FuncV\<cdot>f) = f"

lemma ProjFuncV_bot [simp]: 
  "ProjFuncV\<cdot>\<bottom> = \<bottom>" 
  "\<And> x y. \<lbrakk>x \<noteq> \<bottom>\<rbrakk> \<Longrightarrow> ProjFuncV\<cdot>(BasicV\<cdot>x) = \<bottom>" 
  "\<And> xs. xs \<noteq> \<bottom> \<Longrightarrow> ProjFuncV\<cdot>(SetV\<cdot>xs) = \<bottom>" 
  by (fixrec_simp)+

lemma ProjFuncV_simps [simp]:
  "ProjFuncV\<cdot>(BasicV\<cdot>v) = \<bottom>"
  "ProjFuncV\<cdot>(SetV\<cdot>xs) = \<bottom>"
  apply (case_tac v, simp_all)
  apply (case_tac "xs = \<bottom>", simp_all)
done

lemma FuncV_inv [simp]: "ProjFuncV\<cdot>(FuncV\<cdot>f) = f"
  by (case_tac "f = \<bottom>", simp_all)

definition "InjVB  x \<equiv> BasicV\<cdot>(InjB\<cdot>(Def x))"
definition "ProjVB x \<equiv> Undef (ProjB\<cdot>(ProjBasicV\<cdot>x))"

lemma InjVB_inv[simp]: "ProjVB (InjVB x) = x"
  by (simp add:ProjVB_def InjVB_def)

lemma ProjVB_inv[simp]: 
  "\<lbrakk> x : BasicType (Type TYPE('a::vbasic)); x \<noteq> \<bottom> \<rbrakk> \<Longrightarrow> InjVB (ProjVB x :: 'a) = x"
  by (force simp add:InjVB_def ProjVB_def ProjB_def InjB_def)

lemma InjVB_Type[intro]: "InjVB (x::'a::vbasic) : BasicType (Type (TYPE('a)))"
  by (auto simp add:InjVB_def InjB_def)

abbreviation "sfun_abs2 \<equiv> \<Lambda> f. (\<Lambda>! x. sfun_abs\<cdot>(\<Lambda> x. sfun_abs\<cdot>(f\<cdot>x))\<cdot>!x)"

abbreviation "FuncV2 \<equiv> \<Lambda> f. FuncV\<cdot>(\<Lambda>! x. FuncV\<cdot>(f\<cdot>!x))"
abbreviation "SFuncV \<equiv> \<Lambda> f. FuncV\<cdot>(sfun_abs\<cdot>f)"
abbreviation "SFuncV2 \<equiv> \<Lambda> f. FuncV\<cdot>(sfun_abs\<cdot>(\<Lambda> x. FuncV\<cdot>(sfun_abs\<cdot>(f\<cdot>x))))"

definition pfun1 :: "('a::vbasic \<Rightarrow> 'b::vbasic) \<Rightarrow> 'a set \<Rightarrow> vval" where
"pfun1 f P \<equiv> FuncV\<cdot>(sfun_abs\<cdot>(BasicV oo (vbfun1 f P) oo ProjBasicV))"

definition pfun2 :: 
  "('a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> vval" where
"pfun2 f P Q \<equiv> SFuncV2\<cdot>(\<Lambda> x y. BasicV\<cdot>(vbfun2 f P Q\<cdot>(ProjBasicV\<cdot>x)\<cdot>(ProjBasicV\<cdot>y)))"

(*
definition "pfun3 f P Q R \<equiv> InjV\<cdot>(\<Lambda> (Def x) (Def y) (Def z). if (P x \<and> Q y \<and> R z) then Def (f x y z) else \<bottom>)"
*)




abbreviation "bfun1 f \<equiv> pfun1 f UNIV"
abbreviation "bfun2 f \<equiv> pfun2 f UNIV UNIV"
(* abbreviation "bfun3 f \<equiv> pfun3 f (\<lambda> x. True) (\<lambda> x. True) (\<lambda> x. True)" *)


lemma pfun1_type [intro]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "pfun1 f P : (BasicType (Type TYPE('a)) → BasicType (Type TYPE('b)))"
  apply (simp add:pfun1_def oo_def)
  apply (rule FuncV_type)
  apply (auto simp add:cdom_def cran_def)
  apply (case_tac x, auto)
  apply (case_tac x, auto)
  apply (erule vbfun1_elim)
  apply (simp)
  apply (case_tac "a \<in> P")
  apply (auto)
done

lemma pfun1_app [simp]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic" and x :: "'a"
  assumes "x \<in> P"
  shows "(ProjFuncV\<cdot>(pfun1 f P))\<cdot>!(InjVB x) = InjVB (f x)"
  by (simp add:pfun1_def assms InjVB_def)

lemma sfun_bot_intro [intro]: "\<forall> x. f\<cdot>!x = \<bottom> \<Longrightarrow> f = \<bottom>"
  apply (simp add: sfun_eq_iff sfun_rep_def)
  apply (auto intro: cfun_eqI)
done

lemma sfun_nbot_param: "(\<Lambda>! x. f x) \<noteq> \<bottom> \<Longrightarrow> \<exists> x. f x \<noteq> \<bottom>"
  by (rule ccontr, simp)

lemma sfun_nbotE[elim]: "\<lbrakk> (\<Lambda>! x. f x) \<noteq> \<bottom>; \<And> x. f x \<noteq> \<bottom> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis (hide_lams, no_types) sfun_nbot_param)  

lemma pfun2_type [intro]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  shows "pfun2 f P Q : BasicType (Type TYPE('a)) → BasicType (Type TYPE('b)) → BasicType (Type TYPE('c))"
  apply (auto intro!:FuncV_type simp add:cdom_def cran_def pfun2_def)
  apply (case_tac x, auto)
  apply (case_tac lift)
  apply (force)
  apply (force)
  apply (case_tac x, simp_all)
  apply (case_tac lift)
  apply (auto)
  apply (case_tac xa, simp_all)
  apply (force simp add:cran_def)
  apply (force)
done

lemma pfun2_app [simp]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic" and x :: "'a"
  assumes "x \<in> P"
  shows "(ProjFuncV\<cdot>(pfun2 f P Q))\<cdot>!(InjVB x) = pfun1 (f x) Q"
  by (simp add:pfun2_def pfun1_def assms sfun_eq_iff cfun_eq_iff InjVB_def)

end
