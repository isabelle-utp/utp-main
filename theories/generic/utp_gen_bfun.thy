theory utp_gen_bfun
imports utp_gen_pred
begin

section {* Binding Functions *}

text {* TODO: Develop a proof tactic for membership to @{text "WF_BINDING_FUN"}. *}

context GEN_PRED
begin

subsection {* Theorems *}

text {* These theorems are useful when reasoning about lifted predicates. *}

theorem binding_fun_non_interfere1 :
"\<lbrakk>x \<in> a\<rbrakk> \<Longrightarrow>
 (\<lambda> b . f (b x)) \<in> WF_BINDING_FUN a"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: BINDING_EQUIV_def)
done

theorem binding_fun_non_interfere2 :
"\<lbrakk>x1 \<in> a; x2 \<in> a\<rbrakk> \<Longrightarrow>
 (\<lambda> b . f (b x1) (b x2)) \<in> WF_BINDING_FUN a"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: BINDING_EQUIV_def)
done

theorem binding_fun_non_interfere3 :
"\<lbrakk>x1 \<in> a; x2 \<in> a; x3 \<in> a\<rbrakk> \<Longrightarrow>
 (\<lambda> b . f (b x1) (b x2) (b x3)) \<in> WF_BINDING_FUN a"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: BINDING_EQUIV_def)
done

theorem binding_fun_non_interfere4 :
"\<lbrakk>x1 \<in> a; x2 \<in> a; x3 \<in> a; x4 \<in> a\<rbrakk> \<Longrightarrow>
 (\<lambda> b . f (b x1) (b x2) (b x3) (b x4)) \<in> WF_BINDING_FUN a"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: BINDING_EQUIV_def)
done

theorem binding_fun_non_interfere5 :
"\<lbrakk>x1 \<in> a; x2 \<in> a; x3 \<in> a; x4 \<in> a; x5 \<in> a\<rbrakk> \<Longrightarrow>
 (\<lambda> b . f (b x1) (b x2) (b x3) (b x4) (b x5)) \<in> WF_BINDING_FUN a"
apply (simp add: WF_BINDING_FUN_def)
apply (simp add: BINDING_EQUIV_def)
done

(* Maybe the following are actually not needed in practice. *)

theorem binding_fun_and :
"\<lbrakk>(\<lambda> b . f b) \<in> WF_BINDING_FUN a;
 (\<lambda> b . g b) \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 (\<lambda> b . (f b) \<and> (g b)) \<in> WF_BINDING_FUN a"
apply (simp add: WF_BINDING_FUN_def)
done

theorem binding_fun_or :
"\<lbrakk>(\<lambda> b . f b) \<in> WF_BINDING_FUN a;
 (\<lambda> b . g b) \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 (\<lambda> b . (f b) \<or> (g b)) \<in> WF_BINDING_FUN a"
apply (simp add: WF_BINDING_FUN_def)
done

theorem binding_fun_not [simp] :
"\<lbrakk>(\<lambda> b . f b) \<in> WF_BINDING_FUN a\<rbrakk> \<Longrightarrow>
 (\<lambda> b . \<not> (f b)) \<in> WF_BINDING_FUN a"
apply (simp add: WF_BINDING_FUN_def)
done
(*
subsection {* Proof Experiments *}

text {* We cannot do the following proof anymore at this level! *}

text {* Maybe we should assume some type constructors for basic types... *}

definition x_var :: "'TYPE VAR" where
"x_var \<equiv> MkPlain ''x'' IntType"

theorem
"({x_var} \<odot> b \<bullet> IntOf (b x_var) = 1 \<and> IntOf (b x_var) = 2) = false {x_var}"
apply (subst LiftP_def)
apply (simp_all)
apply (subst binding_fun_non_interfere1)
apply (simp_all)
apply (subst FalseP_def)
apply (simp_all)
done
*)
end
end
