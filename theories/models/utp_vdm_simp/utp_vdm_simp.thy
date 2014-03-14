(******************************************************************************)
(* Project: A simplified VDM model for Isabelle/UTP                           *)
(* File: utp_vdm_simp.thy                                                     *)
(* Author: Simon Foster, University of York (UK)                              *)
(******************************************************************************)

header {* VDM Value Domain *}

theory utp_vdm_simp
imports 
  Derive
  Char_ord
  Option_ord
  Monad_Syntax
  utp_base
begin

type_synonym tname = string 

datatype vbt =  Bool\<^isub>t | Num\<^isub>t | Unit\<^isub>t | Quo\<^isub>t | Tag\<^isub>t tname vbt
             | Prod\<^isub>t vbt vbt | Fset\<^isub>t vbt | Fmap\<^isub>t vbt vbt
datatype vft = Func\<^isub>t vbt vft | Set\<^isub>t vbt | Basic\<^isub>t vbt

derive countable vbt

datatype vbv = Bot\<^isub>v vbt | Bool\<^isub>v bool | Num\<^isub>v real | Unit\<^isub>v | Quo\<^isub>v string | Tag\<^isub>v string vbv
  | Prod\<^isub>v vbv vbv | Fset\<^isub>v vbt "(vbv list)" | Fmap\<^isub>v vbt vbt "(vbv * vbv) list" 
datatype vfv = Func\<^isub>v vbt vft "(vbv \<Rightarrow> vfv)" | Set\<^isub>v vbt "(vbv set)" | Basic\<^isub>v vbv

inductive vbt_rel :: "vbv \<Rightarrow> vbt \<Rightarrow> bool" (infix ":\<^sub>b" 50) where 
vbt_bottom [intro!]: "Bot\<^isub>v a :\<^sub>b a" | 
vbt_boolt [intro!]: "Bool\<^isub>v x :\<^sub>b Bool\<^isub>t" | 
vbt_numbt [intro!]: "Num\<^isub>v n :\<^sub>b Num\<^isub>t" |
vbt_unitt [intro!]: "Unit\<^isub>v :\<^sub>b Unit\<^isub>t" |
vbt_quot [intro!]: "Quo\<^isub>v n :\<^sub>b Quo\<^isub>t" |
vbt_tagt [intro!]: "x :\<^sub>b a \<Longrightarrow> Tag\<^isub>v i x :\<^sub>b Tag\<^isub>t i a" |
(* vbt_tagbt: "\<lbrakk> i \<in> dom(\<Pi>); x :\<^sub>b the(\<Pi>(i)) \<rbrakk> \<Longrightarrow> Tag\<^isub>v i x :\<^sub>b Tag\<^isub>t \<Pi>" | *)
vbt_prodbt [intro!]: "\<lbrakk> x :\<^sub>b a; y :\<^sub>b b \<rbrakk> \<Longrightarrow> Prod\<^isub>v x y :\<^sub>b Prod\<^isub>t a b" | 
vbt_setbt [intro!]: "\<lbrakk> \<forall> x \<in> set xs. x :\<^sub>b a \<rbrakk> \<Longrightarrow> Fset\<^isub>v a xs :\<^sub>b Fset\<^isub>t a" | 
vbt_mapbt [intro!]: "\<lbrakk> \<forall> (k,v) \<in> set xs. (k :\<^sub>b a \<and> v :\<^sub>b b) \<rbrakk> \<Longrightarrow> Fmap\<^isub>v a b xs :\<^sub>b Fmap\<^isub>t a b" 

inductive_cases 
  Bot\<^isub>v_cases[elim]: "Bot\<^isub>v a :\<^sub>b b" and
  Bool\<^isub>v_cases [elim]: "Bool\<^isub>v x :\<^sub>b a" and
  Bool\<^isub>t_cases [elim!]: "x :\<^sub>b Bool\<^isub>t" and
  Num\<^isub>v_cases [elim]: "Num\<^isub>v x :\<^sub>b a" and
  Num\<^isub>t_cases [elim!]: "x :\<^sub>b Num\<^isub>t" and
  Unit\<^isub>v_cases [elim]: "Unit\<^isub>v :\<^sub>b a" and
  Unit\<^isub>t_cases [elim!]: "x :\<^sub>b Unit\<^isub>t" and
  Quo\<^isub>v_cases [elim]: "Quo\<^isub>v x :\<^sub>b a" and
  Quo\<^isub>t_cases [elim!]: "x :\<^sub>b Quo\<^isub>t" and
  Tag\<^isub>v_cases [elim!]: "Tag\<^isub>v i x :\<^sub>b a" and
  Tag\<^isub>t_cases [elim!]: "x :\<^sub>b Tag\<^isub>t i a" and
  Prod\<^isub>v_cases [elim!]: "Prod\<^isub>v x y :\<^sub>b a" and
  Prod\<^isub>t_cases [elim!]: "x :\<^sub>b Prod\<^isub>t a b" and
  Fset\<^isub>v_cases [elim]: "Fset\<^isub>v a xs :\<^sub>b b" and
  Fset\<^isub>t_cases [elim!]: "x :\<^sub>b Fset\<^isub>t a" and
  Fmap\<^isub>v_cases [elim]: "Fmap\<^isub>v a b xs :\<^sub>b c" and
  Fmap\<^isub>t_cases [elim!]: "x :\<^sub>b Fmap\<^isub>t a b"
  
instantiation vbv :: DEFINED
begin

fun Defined_vbv :: "vbv \<Rightarrow> bool" where
"\<D>(Bot\<^isub>v a)       = False" |
"\<D>(Tag\<^isub>v i x)     = \<D> x" |
"\<D>(Prod\<^isub>v x y)    = (\<D>(x) \<and> \<D>(y))" |
"\<D>(Fset\<^isub>v a xs)   = (\<forall> x \<in> set(xs). \<D>(x))" |
"\<D>(Fmap\<^isub>v a b xs) = (\<forall> (x,y) \<in> set xs. \<D> x \<and> \<D> y)" |
"\<D>(Bool\<^isub>v x)      = True" |
"\<D>(Num\<^isub>v x)       = True" |
"\<D>(Unit\<^isub>v)        = True" |
"\<D>(Quo\<^isub>v x)       = True"

instance ..
end

fun vbt_val :: "vbt \<Rightarrow> vbv" where
"vbt_val Bool\<^isub>t       = Bool\<^isub>v True" |
"vbt_val Num\<^isub>t        = Num\<^isub>v 0" |
"vbt_val Unit\<^isub>t       = Unit\<^isub>v" |
"vbt_val Quo\<^isub>t        = Quo\<^isub>v ''q''" |
"vbt_val (Tag\<^isub>t i t)  = Tag\<^isub>v i (vbt_val t)" |
"vbt_val (Prod\<^isub>t a b) = Prod\<^isub>v (vbt_val a) (vbt_val b)" |
"vbt_val (Fset\<^isub>t a)   = Fset\<^isub>v a []" |
"vbt_val (Fmap\<^isub>t a b) = Fmap\<^isub>v a b []"

theorem vbt_val_well_typed:
  "vbt_val t :\<^sub>b t"
  by (induct t, auto)

theorem vbt_val_well_defined:
  "\<D>(vbt_val t)"
  by (induct t, simp_all)

theorem vbt_rel_nonempty: "\<exists> v. (v :\<^sub>b t \<and> \<D>(v))"
  by (metis vbt_val_well_defined vbt_val_well_typed)

theorem vbt_monomorphic:
  "\<lbrakk> x :\<^sub>b a; x :\<^sub>b b \<rbrakk> \<Longrightarrow> a = b"
  by (induct x arbitrary: a b, auto)


(*

"vbt_val (Tag\<^isub>t \<Pi>)  = (if (dom(\<Pi>) = {}) 
                      then Unit\<^isub>v 
                      else (let i = (SOME x. x \<in> dom(\<Pi>)) in
                           Tag\<^isub>v i (vbt_val(the(\<Pi>(i))))))"
*)

end