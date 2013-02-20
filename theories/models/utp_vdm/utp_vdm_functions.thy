theory utp_vdm_functions
imports utp_vdm_sorts
begin

definition TID :: "vval" where
"TID = vbasic_fun1 id"

definition TCONST :: "vval" where
"TCONST = vbasic_fun2 (\<lambda> x y. x)"

(* vbasic lift \<rightarrow> (vbasic lift \<rightarrow>!vval) *)

definition TEQ :: "vval" where
"TEQ = vbasic_fun2 (\<lambda> x y. BoolI (x = y))"

definition TNEQ :: "vval" where
"TNEQ = vbasic_fun2 (\<lambda> x y. BoolI (x \<noteq> y))"

lemma TID_type [simp]: "TID :\<^sub>v a → a"
  by (force simp add:TID_def vbasic_fun1_def)

lemma TCONST_type [simp]: "TCONST :\<^sub>v a → b → a"
  by (force simp add:TCONST_def vbasic_fun2_def)

lemma TEQ_type: "TEQ :\<^sub>v a → a → \<bool>"
  by (force simp add:TEQ_def vbasic_fun2_def)

lemma TNEQ_type: "TNEQ :\<^sub>v a → a → \<bool>"
  by (force simp add:TNEQ_def vbasic_fun2_def)


text {* We create functions for VDM *}

lemma Defined_pfun1 [simp]: "P \<noteq> {} \<Longrightarrow> \<D> (pfun1 f P)"
  apply (auto simp add:Defined_vval_def InjB_def pfun1_def sfun_eq_iff cfun_eq_iff)
  apply (drule_tac x="InjVB x" in spec)
  apply (simp add:InjVB_def, simp add:InjB_def)
done

lemma Defined_pfun2 [simp]: "\<lbrakk>P \<noteq> {}; Q \<noteq> {}\<rbrakk> \<Longrightarrow> \<D> (pfun2 f P Q)"
  apply (auto simp add:Defined_vval_def InjB_def pfun2_def sfun_eq_iff cfun_eq_iff)
  apply (drule_tac x="InjVB x" in spec)
  apply (drule_tac x="InjVB xa" in spec)
  apply (simp add:InjVB_def, simp add:InjB_def)
done

definition vapp :: "vval \<Rightarrow> vval \<Rightarrow> vval" (infixl "$" 65) where
"vapp f x \<equiv> Rep_cfun (sfun_rep\<cdot>(ProjFuncV\<cdot>f)) x"

definition vcomp :: "vval \<Rightarrow> vval \<Rightarrow> vval" (infixl "comp" 60) where
"vcomp f g \<equiv> FuncV\<cdot>(ProjFuncV\<cdot>f oo! ProjFuncV\<cdot>g)"

definition vovrd :: "vval \<Rightarrow> vtype \<Rightarrow> vval \<Rightarrow> vval" (infixl "\<oplus>\<^bsub>_\<^esub>" 65) where
"f \<oplus>\<^bsub>t\<^esub> g \<equiv> BFuncV\<cdot>(sfun_abs\<cdot>(\<Lambda> (Def x). if (x :\<^sub>b t) then g$BasicV\<cdot>(Def x) else f$BasicV\<cdot>(Def x)))"

lemma FuncV_app[simp]: "FuncV\<cdot>f $ x = sfun_rep\<cdot>f\<cdot>x"
  by (simp add:vapp_def)

(* Note: The vbtypes restriction is necessary whilst we can't deal with HO functions *)
lemma vapp_type [intro]: "\<lbrakk> f :\<^sub>v a → b; x :\<^sub>v a; a \<in> vbtypes \<rbrakk> \<Longrightarrow> f $ x :\<^sub>v b"
  by (force simp add:vapp_def)

lemma vcomp_vapp[simp]: "(f comp g) $ x = f $ (g $ x)"
  by (simp add:vcomp_def vapp_def)

lemma vcomp_type [intro]: "\<lbrakk> g :\<^sub>v a → b; f :\<^sub>v b → c; b \<in> vbtypes \<rbrakk> \<Longrightarrow> f comp g :\<^sub>v a → c"
  apply (auto simp add: vcomp_def cdom_def cran_def soo_def)
  apply (rule FuncV_type)
  apply (auto)
  apply (drule_tac x="x" in spec)
  apply (simp)
  apply (metis FuncV_app FuncV_type vapp_type)
done

lemma app_bot[simp]: "vapp \<bottom> f = \<bottom>" "vapp f \<bottom> = \<bottom>"
  by (simp_all add:vapp_def)

lemma vovrd_simps [simp]: 
  "\<lbrakk> x \<in> vbvalues; t \<in> vbtypes \<rbrakk> \<Longrightarrow> 
   (f \<oplus>\<^bsub>t\<^esub> g)$x = (if (x :\<^sub>v t) then g$x else f$x)"
  by (auto simp add:vovrd_def vapp_def vbvalues_def)

lemma vovrd_type1 [intro]:
  "\<lbrakk> f :\<^sub>v a → b; vcarrier a \<inter> vcarrier t = {\<bottom>} \<rbrakk> \<Longrightarrow> f \<oplus>\<^bsub>t\<^esub> g :\<^sub>v a → b"
  apply (simp add:vovrd_def)
  apply (rule FuncV_type)
  apply (rule allI)
  apply (rule impI)
  apply (simp)
  apply (rule conjI)
  apply (rule impI)
  apply (simp add:set_eq_iff)
  apply (simp add:vcarrier_def)
  apply (drule_tac x="BasicV\<cdot>(Def x)" in spec)
  apply (force)
  apply (force)
done

lemma vovrd_type2 [intro]:
  "\<lbrakk> g :\<^sub>v a → b \<rbrakk> \<Longrightarrow> f \<oplus>\<^bsub>a\<^esub> g :\<^sub>v a → b"
  apply (simp add:vovrd_def)
  apply (rule FuncV_type)
  apply (rule allI)
  apply (rule impI)
  apply (simp add:carrier_def)
  apply (auto)
done

(*
lemma Defined_vapp_type1 [dest]: "\<lbrakk> f : a → b; \<D> (f$x) \<rbrakk> \<Longrightarrow> x : a"
  apply (auto simp add:cdom_def Defined_vval_def vapp_def)
  apply (case_tac x)
  apply (simp_all)
  apply (case_tac lift)
  apply (simp_all)
  apply (rule BasicV_type)
  apply (auto)
*)

lemma Defined_vapp_defined [dest]: "\<lbrakk> f :\<^sub>v a → b; \<D> (f$x) \<rbrakk> \<Longrightarrow> \<D> x"
  by (auto simp add:cdom_def Defined_vval_def vapp_def)

lemma pfun1_vapp [simp]: "x \<in> P \<Longrightarrow> pfun1 f P $ InjVB x = InjVB (f x)"
  by (simp add:pfun1_def InjVB_def)

lemma pfun1_app_simps [simp]:
  "pfun1 f P $ \<bottom> = \<bottom>"
  "pfun1 f P $ (SetV\<cdot>xs) = \<bottom>"
  "pfun1 f P $ (FuncV\<cdot>g) = \<bottom>"
  by (simp_all add:pfun1_def vapp_def)

(*
lemma Defined_app_intro [intro]: 
  "\<lbrakk> f \<noteq> \<bottom>; \<D> x; x \<in> cdom (sfun_rep' f) \<rbrakk> \<Longrightarrow> \<D> (FuncV\<cdot>f $ x)"
  by (case_tac f, simp_all add:Defined_vval_def vapp_def cdom_def cran_def)
  
lemma Defined_pfun1_vapp_InjVB [intro]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "\<D> (pfun1 f P $ InjVB x) \<longleftrightarrow> x \<in> P"
  by (auto simp add:pfun1_def vapp_def Defined_vval_def InjB_def vbfun1_def ProjB_def InjVB_def)
*)

lemma pfun2_vapp [simp]: "\<lbrakk>x \<in> P; y \<in> Q\<rbrakk> \<Longrightarrow> pfun2 f P Q $ InjVB x $ InjVB y = InjVB (f x y)"
  by (simp add:pfun2_def pfun1_def vapp_def InjVB_def)

lemma pfun2_app_simps [simp]:
  "pfun2 f P Q $ \<bottom> = \<bottom>"
  "pfun2 f P Q $ (SetV\<cdot>xs) = \<bottom>"
  "pfun2 f P Q $ (FuncV\<cdot>g) = \<bottom>"
  "(pfun2 f P Q $ x) $ (SetV\<cdot>ys) = \<bottom>"
  "(pfun2 f P Q $ x) $ (FuncV\<cdot>g) = \<bottom>"
  by (simp_all add:pfun2_def vapp_def)

lemma Defined_pfun2_vapp_InjVB [simp]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  shows "\<D> (pfun2 f P Q $ InjVB x $ InjVB y) \<longleftrightarrow> x \<in> P \<and> y \<in> Q"
  apply (auto simp add:vapp_def)
  apply (simp_all add:Defined_vval_def pfun2_def InjVB_def)
  apply (metis Rep_cfun_strict1 vbfun2_napp(1))
  apply (metis vbfun2_napp(2))
done

definition "vplus \<equiv> (bfun2 (op + :: nat \<Rightarrow> nat \<Rightarrow> nat) \<oplus>\<^bsub>\<int>\<^esub>
                     bfun2 (op + :: int \<Rightarrow> int \<Rightarrow> int)) \<oplus>\<^bsub>\<rat>\<^esub>
                     bfun2 (op + :: rat \<Rightarrow> rat \<Rightarrow> rat)"

definition "vleq \<equiv> (bfun2 (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool) \<oplus>\<^bsub>\<int>\<^esub>
                    bfun2 (op \<le> :: int \<Rightarrow> int \<Rightarrow> bool)) \<oplus>\<^bsub>\<rat>\<^esub>
                    bfun2 (op \<le> :: rat \<Rightarrow> rat \<Rightarrow> bool)"

definition "vless \<equiv> (bfun2 (op \<le> :: nat \<Rightarrow> nat \<Rightarrow> bool) \<oplus>\<^bsub>\<int>\<^esub>
                     bfun2 (op \<le> :: int \<Rightarrow> int \<Rightarrow> bool)) \<oplus>\<^bsub>\<rat>\<^esub>
                     bfun2 (op \<le> :: rat \<Rightarrow> rat \<Rightarrow> bool)"

definition "vdiv \<equiv> pfun2 (op / :: rat \<Rightarrow> rat \<Rightarrow> rat) UNIV {x. x > 0}"

lemma vplus_type: "a \<in> {\<nat>,\<int>,\<rat>} \<Longrightarrow> vplus :\<^sub>v a → a → a"
  by (force simp add:vplus_def)

lemma vleq_type: "a \<in> {\<nat>,\<int>,\<rat>} \<Longrightarrow> vleq :\<^sub>v a → a → \<bool>"
  by (force simp add:vleq_def)

lemma distinct_types [dest]: 
  "\<lbrakk> x :\<^sub>v \<nat>; x \<noteq> \<bottom>; x :\<^sub>v t; t \<noteq> \<nat> \<rbrakk> \<Longrightarrow> P"
  "\<lbrakk> x :\<^sub>v \<int>; x \<noteq> \<bottom>; x :\<^sub>v t; t \<noteq> \<int> \<rbrakk> \<Longrightarrow> P"
  "\<lbrakk> x :\<^sub>v \<rat>; x \<noteq> \<bottom>; x :\<^sub>v t; t \<noteq> \<rat> \<rbrakk> \<Longrightarrow> P"
  "\<lbrakk> x :\<^sub>v \<bool>; x \<noteq> \<bottom>; x :\<^sub>v t; t \<noteq> \<bool> \<rbrakk> \<Longrightarrow> P"
  "\<lbrakk> x :\<^sub>v CharT; x \<noteq> \<bottom>; x :\<^sub>v t; t \<noteq> CharT \<rbrakk> \<Longrightarrow> P"
  by (force)+

lemma InjVB_Type[simp]: "Type TYPE('a) = a \<Longrightarrow> InjVB (x :: 'a::vbasic) :\<^sub>v a"
  by (force)

lemma vplus_nat: "vplus $ InjVB (x :: nat) $ InjVB (y :: nat) = InjVB (x + y)"
  by (auto simp add:vplus_def)

lemma vplus_int: "vplus $ InjVB (x :: int) $ InjVB (y :: int) = InjVB (x + y)"
  by (auto simp add:vplus_def)

lemma vplus_rat: "vplus $ InjVB (x :: rat) $ InjVB (y :: rat) = InjVB (x + y)"
  by (auto simp add:vplus_def)

lemma "\<D> (vdiv$InjVB (x::rat)$InjVB y) \<longleftrightarrow> (y::rat) > 0"
  by (simp add:vdiv_def)

definition "vhead \<equiv> BFuncV\<cdot>(sfun_abs\<cdot>(\<Lambda> (Def x). case ProjListI x of Some (x#xs) \<Rightarrow> BasicV\<cdot>(Def x) | x \<Rightarrow> \<bottom>))"
definition "vtail \<equiv> BFuncV\<cdot>(sfun_abs\<cdot>(\<Lambda> (Def x). case ProjListI x of Some (x#xs) \<Rightarrow> BasicV\<cdot>(Def (ListI xs)) | x \<Rightarrow> \<bottom>))"
definition "vlength \<equiv> BFuncV\<cdot>(sfun_abs\<cdot>(\<Lambda> (Def x). case ProjListI x of Some xs \<Rightarrow> BasicV\<cdot>(Def (NatI (length xs))) | x \<Rightarrow> \<bottom>))"

lemma vhead_type: "vhead :\<^sub>v ListT a → a"
  by (auto intro!:FuncV_type simp add:vhead_def, case_tac xs, auto)

lemma vtail_type: "vtail :\<^sub>v ListT a → ListT a"
  by (auto intro!:FuncV_type simp add:vtail_def, case_tac xs, auto)

lemma vlength_type: "vlength :\<^sub>v ListT a → \<nat>"
  by (force intro!:FuncV_type simp add:vlength_def)




(*
lemma Defined_pfun1_vapp:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "\<D> (pfun1 f P $ x) \<longleftrightarrow> \<D> x \<and> x : BasicT (Type TYPE('a)) \<and> ProjVB x \<in> P"
  apply (auto simp add:pfun1_def vapp_def Defined_vval_def)
  apply (erule vbfun1_elim)
  apply (case_tac x, auto simp add:InjB_def)
  apply (erule vbfun1_elim)
  apply (case_tac x, auto simp add:InjB_def ProjVB_def ProjB_def)
  apply (auto dest!:Project_defined simp add:vbfun1_def ProjB_def InjB_def)
done


lemma Defined_bfun1_app:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "\<D> (bfun1 f $ x) \<longleftrightarrow> \<D> x \<and> x : BasicT (Type TYPE('a))"
  apply (auto simp add:pfun1_def vapp_def Defined_vval_def)
  apply (erule vbfun1_elim)
  apply (case_tac x, auto simp add:InjB_def)
  apply (auto dest!:Project_defined simp add:vbfun1_def ProjB_def InjB_def)
done

lemma Defined_bfun2_app:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  shows "\<D> (bfun2 f $ x $ y) \<longleftrightarrow> \<D> x \<and> \<D> y \<and> x : BasicT (Type TYPE('a)) \<and> y : BasicT (Type TYPE('b))"
  apply (auto simp add:pfun2_def vapp_def Defined_vval_def)
  apply (erule vbfun2_elim)
  apply (case_tac x, auto simp add:InjB_def)
  apply (erule vbfun2_elim)
  apply (case_tac y, auto simp add:InjB_def)
  apply (auto dest!:Project_defined simp add:vbfun2_def ProjB_def InjB_def)
done
 
lemma vplus_type [intro]: "vplus : \<int> → \<int> → \<int>"
  by (force simp add:Type_int)

lemma head_type [intro]: "head : ListT \<int> → \<int>"
  by (auto simp add: Type_list Type_int head_def)

lemma tail_type [intro]: "tail : ListT \<int> → ListT \<int>"
  by (force simp add: Type_int Type_list tail_def)

lemma "\<D> (vplus$x$y) \<longleftrightarrow> x : \<int> \<and> \<D> x \<and> y : \<int> \<and> \<D> y"
  by (metis Defined_bfun2_app Type_int_def)

lemma Defined_head [simp]:
  "\<D> (head$xs) \<longleftrightarrow> \<D> xs \<and> xs : ListType \<int> \<and> (vless$InjVB(0::int)$(len$xs)) = InjVB True"
  apply (auto simp add:Defined_vval_def head_def)
  apply (case_tac "xs = \<bottom>")
  apply (auto)
sorry

lemma Defined_tail [simp]:
  "\<D> (tail$xs) \<longleftrightarrow> \<D> xs \<and> xs : ListType \<int> \<and> (vless$InjVB(0::int)$(len$xs)) = InjVB True"
sorry

abbreviation vless_syn :: "vval \<Rightarrow> vval \<Rightarrow> bool" (infix "<v" 65) where
"vless_syn x y \<equiv> (vless $ x $ y) = InjVB True"


definition "thirdItem \<equiv> head comp tail comp tail"

lemma thirdItem_type: "thirdItem : ListType \<int> → \<int>"
  by (auto simp add:thirdItem_def)

lemma "\<D> (thirdItem$xs) \<longleftrightarrow> \<D> xs \<and> xs : ListType \<int> \<and> ((InjVB (3 :: int)) <v (len $ xs))"
  apply (unfold thirdItem_def)
  apply (simp)
  apply (simp add:vless_def tail_def head_def len_def)
sorry
*)

end
