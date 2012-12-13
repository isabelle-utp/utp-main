theory utp_vdm_functions
imports utp_vdm_sorts
begin

text {* We create functions for VDM *}

lemma Defined_pfun1 [simp]: "P \<noteq> {} \<Longrightarrow> \<D> (pfun1 f P)"
  apply (auto simp add:Defined_vval_def InjB_def pfun1_def sfun_eq_iff cfun_eq_iff)
  apply (drule_tac x="BasicV\<cdot>(InjB\<cdot>(Def x))" in spec)
  apply (simp, simp add:InjB_def)
done

lemma Defined_pfun2 [simp]: "\<lbrakk>P \<noteq> {}; Q \<noteq> {}\<rbrakk> \<Longrightarrow> \<D> (pfun2 f P Q)"
  apply (auto simp add:Defined_vval_def InjB_def pfun2_def sfun_eq_iff cfun_eq_iff)
  apply (drule_tac x="BasicV\<cdot>(InjB\<cdot>(Def x))" in spec)
  apply (drule_tac x="BasicV\<cdot>(InjB\<cdot>(Def xa))" in spec)
  apply (simp, simp add:InjB_def)
done

definition vapp :: "vval \<Rightarrow> vval \<Rightarrow> vval" (infixl "$" 65) where
"vapp f \<equiv> Rep_cfun (sfun_rep\<cdot>(ProjFuncV\<cdot>f))"

definition vcomp :: "vval \<Rightarrow> vval \<Rightarrow> vval" (infixl "comp" 60) where
"vcomp f g = FuncV\<cdot>(ProjFuncV\<cdot>f oo! ProjFuncV\<cdot>g)"

lemma FuncV_app[simp]: "FuncV\<cdot>f $ x = sfun_rep\<cdot>f\<cdot>x"
  by (simp add:vapp_def)

lemma vapp_type [intro]: "\<lbrakk> f : a → b; x : a \<rbrakk> \<Longrightarrow> f $ x : b"
  apply (auto simp add: vapp_def cdom_def cran_def)
  apply (metis BotV_type)
done

lemma vcomp_vapp[simp]: "(f comp g) $ x = f $ (g $ x)"
  by (simp add:vcomp_def vapp_def)

lemma vcomp_type [intro]: "\<lbrakk> f : b → c; g : a → b \<rbrakk> \<Longrightarrow> f comp g : a → c"
  apply (auto simp add: vcomp_def cdom_def cran_def soo_def)
  apply (rule FuncV_type)
  apply (force simp add:cdom_def cran_def)
  apply (force simp add:cdom_def cran_def)
done

lemma app_bot[simp]: "vapp \<bottom> f = \<bottom>" "vapp f \<bottom> = \<bottom>"
  by (simp_all add:vapp_def)

lemma Defined_vapp_type1 [dest]: "\<lbrakk> f : a → b; \<D> (f$x) \<rbrakk> \<Longrightarrow> x : a"
  by (auto simp add:cdom_def Defined_vval_def vapp_def)

lemma Defined_vapp_defined [dest]: "\<lbrakk> f : a → b; \<D> (f$x) \<rbrakk> \<Longrightarrow> \<D> x"
  by (auto simp add:cdom_def Defined_vval_def vapp_def)

lemma pfun1_vapp [simp]: "x \<in> P \<Longrightarrow> pfun1 f P $ InjVB x = InjVB (f x)"
  by (simp add:pfun1_def InjVB_def)

lemma pfun1_app_simps [simp]:
  "pfun1 f P $ \<bottom> = \<bottom>"
  "pfun1 f P $ (SetV\<cdot>xs) = \<bottom>"
  "pfun1 f P $ (FuncV\<cdot>g) = \<bottom>"
  by (simp_all add:pfun1_def vapp_def)

lemma Defined_app_intro [intro]: 
  "\<lbrakk> f \<noteq> \<bottom>; \<D> x; x \<in> cdom (sfun_rep' f) \<rbrakk> \<Longrightarrow> \<D> (FuncV\<cdot>f $ x)"
  by (case_tac f, simp_all add:Defined_vval_def vapp_def cdom_def cran_def)
  
lemma Defined_pfun1_vapp_InjVB [intro]:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "\<D> (pfun1 f P $ InjVB x) \<longleftrightarrow> x \<in> P"
  by (auto simp add:pfun1_def vapp_def Defined_vval_def InjB_def vbfun1_def ProjB_def InjVB_def)

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

abbreviation "vplus \<equiv> bfun2 ((op +) :: int \<Rightarrow> int \<Rightarrow> int)"
abbreviation "vless_eq \<equiv> bfun2 ((op \<le>) :: int \<Rightarrow> int \<Rightarrow> bool)"
definition "vless \<equiv> bfun2 ((op <) :: int \<Rightarrow> int \<Rightarrow> bool)"
definition "vdiv \<equiv> pfun2 (op / :: rat \<Rightarrow> rat \<Rightarrow> rat) UNIV {x. x > 0}"

lemma "\<D> (vdiv$InjVB (x::rat)$InjVB y) \<longleftrightarrow> (y::rat) > 0"
  by (simp add:vdiv_def)

definition "head \<equiv> pfun1 (hd :: int list \<Rightarrow> int) {x. length x > 0}"
definition "tail \<equiv> pfun1 (tl :: int list \<Rightarrow> int list) {x. length x > 0}"
definition "len \<equiv> bfun1 (length :: int list \<Rightarrow> int)"

lemma Defined_pfun1_vapp:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "\<D> (pfun1 f P $ x) \<longleftrightarrow> \<D> x \<and> x : BasicType (Type TYPE('a)) \<and> ProjVB x \<in> P"
  apply (auto simp add:pfun1_def vapp_def Defined_vval_def)
  apply (erule vbfun1_elim)
  apply (case_tac x, auto simp add:InjB_def)
  apply (erule vbfun1_elim)
  apply (case_tac x, auto simp add:InjB_def ProjVB_def ProjB_def)
  apply (auto dest!:Project_defined simp add:vbfun1_def ProjB_def InjB_def)
done


lemma Defined_bfun1_app:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic"
  shows "\<D> (bfun1 f $ x) \<longleftrightarrow> \<D> x \<and> x : BasicType (Type TYPE('a))"
  apply (auto simp add:pfun1_def vapp_def Defined_vval_def)
  apply (erule vbfun1_elim)
  apply (case_tac x, auto simp add:InjB_def)
  apply (auto dest!:Project_defined simp add:vbfun1_def ProjB_def InjB_def)
done

lemma Defined_bfun2_app:
  fixes f :: "'a::vbasic \<Rightarrow> 'b::vbasic \<Rightarrow> 'c::vbasic"
  shows "\<D> (bfun2 f $ x $ y) \<longleftrightarrow> \<D> x \<and> \<D> y \<and> x : BasicType (Type TYPE('a)) \<and> y : BasicType (Type TYPE('b))"
  apply (auto simp add:pfun2_def vapp_def Defined_vval_def)
  apply (erule vbfun2_elim)
  apply (case_tac x, auto simp add:InjB_def)
  apply (erule vbfun2_elim)
  apply (case_tac y, auto simp add:InjB_def)
  apply (auto dest!:Project_defined simp add:vbfun2_def ProjB_def InjB_def)
done
 
lemma vplus_type [intro]: "vplus : \<int> → \<int> → \<int>"
  by (force simp add:Type_int)

lemma head_type [intro]: "head : ListType \<int> → \<int>"
  by (auto simp add: Type_list Type_int head_def)

lemma tail_type [intro]: "tail : ListType \<int> → ListType \<int>"
  by (force simp add: Type_int Type_list tail_def)

lemma "\<D> (vplus$x$y) \<longleftrightarrow> x : \<int> \<and> \<D> x \<and> y : \<int> \<and> \<D> y"
  by (metis Defined_bfun2_app Type_int_def)

(*
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
