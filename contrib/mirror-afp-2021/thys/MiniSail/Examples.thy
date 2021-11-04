(*<*)
theory Examples
imports SubstMethods  fuzzyrule.fuzzyrule
begin
(*>*)

subsection \<open>Examples from thesis\<close>

text \<open>
let x = false in 
let y = 0b11 in 
let z = 42 in 
let w = (true,(z,y)) in ()
\<close>

method fresh_mth_aux uses add = (
       (match conclusion in  "atom z \<sharp> GNil" for z   \<Rightarrow> \<open> simp add: fresh_GNil[of "atom z"] add\<close>)
     |  (match conclusion in  "atom z \<sharp> DNil" for z   \<Rightarrow> \<open> simp add: fresh_DNil[of "atom z" ] add\<close>)
     |  (match conclusion in  "atom z \<sharp> Nil" for z   \<Rightarrow> \<open> simp add: fresh_Nil[of "atom z" ] add\<close>)
     |  (match conclusion in  "atom z \<sharp> {||}" for z   \<Rightarrow> \<open> simp add: fresh_empty_fset[of "atom z" ] add\<close>)
     |  (match conclusion in  "atom (z::x) \<sharp> ((x::x,b::b,c::c)#\<^sub>\<Gamma>G)" for z x b c G   \<Rightarrow> \<open>simp add: fresh_GCons[of "atom z" "(x,b,c)" G] add\<close>)
     |  (match conclusion in  "atom z \<sharp> (b::b)" for z b  \<Rightarrow> \<open> simp add: b.fresh[of "atom z" ] add\<close>)
     |  (match conclusion in  "atom z \<sharp> (c::c)" for z c  \<Rightarrow> \<open> simp add: c.fresh[of "atom z" ] add\<close>)
     |  (match conclusion in  "atom z \<sharp> (i::int)" for z i  \<Rightarrow> \<open> simp add: pure_fresh add\<close>)
(* tbc delta and types
     | (auto simp add: add x_fresh_b pure_fresh) (* Cases where there is no subst and so can most likely get what we want from induction premises *)*)
)

method fresh_mth_basic uses add = (
     (unfold fresh_prodN, intro conjI)?,
     (fresh_mth_aux add: add)+)

method wf_ctx uses add = (
  (rule wfPhi_emptyI | rule wfTh_emptyI| rule wfD_emptyI| rule wfG_nilI | rule wfG_cons2I )+
)

method wfb uses add = (
  (rule wfB_boolI | rule wfB_intI | rule wfB_unitI | rule wfB_pairI  )+
)

method wfc uses add =  (
  (rule wfC_trueI | rule wfC_falseI | rule wfC_notI | rule wfC_eqI  )+
)

method wfv uses add =  (
  (rule wfV_varI | fuzzy_rule wfV_litI | rule wfV_pairI )+
)

method wfce uses add =  (
  (rule wfCE_valI | rule wfCE_fstI | rule wfCE_sndI | rule wfCE_eqI )+
)

method wfe uses add =  (
  (rule wfE_valI | rule wfE_fstI | rule wfE_sndI )+
)

method wfs uses add =  (
  (rule wfS_letI | rule wfS_valI )+
)

method wf_all uses add = (
  (wfb | wfv | wfc | wfce | wfe | wfs | auto simp add: add | wf_ctx | fresh_mth_basic add: add )+
)

method wf_all2 uses add = (
  (wfb | wfv | wfc | wfce | wfe | wfs | wf_ctx )+
)

method wf_let uses add = (
  (rule wfS_letI, rule wfE_valI, wf_ctx add: add ),
  (rule wfV_litI,rule wfG_nilI, rule wfTh_emptyI))

(*
rule wfS_letI, rule wfE_valI, rule wfPhi_emptyI , rule wfTh_emptyI, rule wfD_emptyI, rule wfG_nilI, rule wfTh_emptyI),
  (rule wfV_litI,rule wfG_nilI, rule wfTh_emptyI)
*)

lemma 
  shows "[] ; [] ; {||} ; GNil ; []\<^sub>\<Delta> \<turnstile>\<^sub>w\<^sub>f LET x = [ [ L_false ]\<^sup>v ]\<^sup>e  IN  [[ L_unit ]\<^sup>v]\<^sup>s : B_unit"
  apply wf_let
  apply(rule wfS_valI,wf_ctx)
  by(fuzzy_rule wfV_litI,  wf_all)

lemma 
  assumes " atom z \<sharp> x"
  shows   "[] ; [] ; {||} ; GNil ; []\<^sub>\<Delta> \<turnstile>\<^sub>w\<^sub>f LET x = [ [ L_false ]\<^sup>v ]\<^sup>e IN 
                                   LET z = [ [ L_num 42]\<^sup>v ]\<^sup>e IN  [[ L_unit ]\<^sup>v]\<^sup>s : B_unit"


  apply wf_let
  apply(rule wfS_letI)

  apply(rule wfE_valI, wf_ctx,auto,wf_ctx)
  by(wf_all add: assms)
 

text \<open>
val not_bool : (x : bool [ T ]) -> { z : bool | ~ (z = x) }
function not_bool(x) = if x then F else T

val eq_int : ( x : int x int [ T ]) -> { z : bool | z = (fst x = snd x ) }
function eq_int ( x ) = 
    let x1 = fst x in
    let x2 = snd x in
    let x3 = x1 = x2 in x3
  
val neq_int : ( ( x : int x int [ T ]) -> { z : bool | ~ ( z = (fst x = snd x )) }
function neq_int (x) = not_bool(eq_int(x))
\<close>


lemma 
  assumes "atom z \<sharp> x"
  shows "wfFT [] []  {||}  (AF_fun_typ (x::x) B_bool C_true (\<lbrace> z : B_bool | C_not (C_eq (CE_val (V_var z)) (CE_val (V_var x))) \<rbrace>)
      (AS_if (V_var x)  [[L_false]\<^sup>v]\<^sup>s [[L_true]\<^sup>v]\<^sup>s))"
  apply(rule wfFTI,wf_all) 
  apply (simp add: supp_at_base)+
  apply(rule wfTI)
  by(wf_all add: assms)

lemma 
  assumes "atom z \<sharp> x"
  shows "wfFT [] []  {||}  (AF_fun_typ (x::x) (B_pair B_int B_int) C_true (\<lbrace> z : B_bool | (C_eq (CE_val (V_var z)) (CE_op Eq (CE_fst (CE_val (V_var x))) (CE_fst (CE_val (V_var x))))) \<rbrace>)
      (AS_let x1 (AE_fst ((V_var x))) (
       AS_let x2 (AE_snd ((V_var x))) (
       AS_let x3 (AE_op Eq ((V_var x1)) ((V_var x2))) (AS_val (V_var x3))))))"
     
  apply(rule wfFTI,wf_all2) 
  defer 1
 
 
  apply simp
  apply(rule wfTI)
      apply(fresh_mth_basic )
  defer 1
          apply(wf_all )
  using assms apply simp
          apply(wf_all )
  using assms apply simp
           apply(wf_all )
  using assms apply simp
          apply(wf_all )
  defer 1
            apply(wf_all )
 using assms apply simp
(*,wf_ctx,rule wfC_eqI,rule wfCE_valI,rule wfV_varI, (wf_ctx|auto|wf1)+)*)
     apply(fresh_mth_basic )
    apply((wf_ctx|auto|wf1)+)
   apply(rule wfCE_eqI,rule wfCE_fstI, rule wfCE_valI,rule wfV_varI)
     apply((wf_ctx|auto|wf1)+)
      apply(fresh_mth_basic add: assms)+
     apply((wf_ctx|auto|wf1)+)
  using assms apply simp
   apply(rule wfCE_fstI ,rule wfCE_valI,rule wfV_varI)
  apply((wf_ctx|auto|wf1)+)
     apply(fresh_mth_basic add: assms)+
    apply((wf_ctx|auto|wf1)+)
  using assms apply simp
  by((wf_ctx|auto|wf1)+)


end