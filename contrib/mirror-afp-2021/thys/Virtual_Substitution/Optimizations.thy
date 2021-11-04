section "Optimizations"
theory Optimizations
  imports Debruijn
begin

text "Does negation normal form conversion"
fun nnf :: "atom fm \<Rightarrow> atom fm" where
  "nnf TrueF = TrueF" |
  "nnf FalseF = FalseF " |
  "nnf (Atom a) = Atom a" |
  "nnf (And \<phi>\<^sub>1 \<phi>\<^sub>2) = And (nnf \<phi>\<^sub>1) (nnf \<phi>\<^sub>2)" |
  "nnf (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = Or (nnf \<phi>\<^sub>1) (nnf \<phi>\<^sub>2)" |
  "nnf (ExQ \<phi>) = ExQ (nnf \<phi>)" |
  "nnf (AllQ \<phi>) = AllQ (nnf \<phi>)"|
  "nnf (AllN i \<phi>) = AllN i (nnf \<phi>)"|
  "nnf (ExN i \<phi>) = ExN i (nnf \<phi>)" |
  "nnf (Neg TrueF) = FalseF" |
  "nnf (Neg FalseF) = TrueF" |
  "nnf (Neg (Neg \<phi>)) = (nnf \<phi>)" |
  "nnf (Neg (And \<phi>\<^sub>1 \<phi>\<^sub>2)) = (Or (nnf (Neg \<phi>\<^sub>1)) (nnf (Neg \<phi>\<^sub>2)))" |
  "nnf (Neg (Or \<phi>\<^sub>1 \<phi>\<^sub>2)) = (And (nnf (Neg \<phi>\<^sub>1)) (nnf (Neg \<phi>\<^sub>2)))" |
  "nnf (Neg (Atom a)) = Atom(aNeg a)" |
  "nnf (Neg (ExQ \<phi>)) = AllQ (nnf (Neg \<phi>))" |
  "nnf (Neg (AllQ \<phi>)) = ExQ (nnf (Neg \<phi>))"|
  "nnf (Neg (AllN i \<phi>)) = ExN i (nnf (Neg \<phi>))"|
  "nnf (Neg (ExN i \<phi>)) = AllN i (nnf (Neg \<phi>))"


subsection "Simplify Constants"

fun simp_atom :: "atom \<Rightarrow> atom fm" where
  "simp_atom (Eq p)   = (case get_if_const p of None \<Rightarrow> Atom(Eq   p) | Some(r) \<Rightarrow> (if r=0 then TrueF else FalseF))"|
  "simp_atom (Less p) = (case get_if_const p of None \<Rightarrow> Atom(Less p) | Some(r) \<Rightarrow> (if r<0 then TrueF else FalseF))"|
  "simp_atom (Leq p)  = (case get_if_const p of None \<Rightarrow> Atom(Leq  p) | Some(r) \<Rightarrow> (if r\<le>0 then TrueF else FalseF))"|
  "simp_atom (Neq p)  = (case get_if_const p of None \<Rightarrow> Atom(Neq  p) | Some(r) \<Rightarrow> (if r\<noteq>0 then TrueF else FalseF))"

fun simpfm :: "atom fm \<Rightarrow> atom fm" where
  "simpfm TrueF = TrueF"|
  "simpfm FalseF = FalseF"|
  "simpfm (Atom a) = simp_atom a"|
  "simpfm (And \<phi> \<psi>) = and (simpfm \<phi>) (simpfm \<psi>)"|
  "simpfm (Or \<phi> \<psi>) = or (simpfm \<phi>) (simpfm \<psi>)"|
  "simpfm (ExQ \<phi>) = ExQ (simpfm \<phi>)"|
  "simpfm (Neg \<phi>) = neg (simpfm \<phi>)"|
  "simpfm (AllQ \<phi>) = AllQ(simpfm \<phi>)"|
  "simpfm (AllN i \<phi>) = AllN i (simpfm \<phi>)"|
  "simpfm (ExN i \<phi>) = ExN i (simpfm \<phi>)"


subsection "Group Quantifiers"

fun groupQuantifiers :: "atom fm \<Rightarrow> atom fm" where
  "groupQuantifiers TrueF = TrueF"|
  "groupQuantifiers FalseF = FalseF"|
  "groupQuantifiers (And A B) = And (groupQuantifiers A) (groupQuantifiers B)"|
  "groupQuantifiers (Or A B) = Or (groupQuantifiers A) (groupQuantifiers B)"|
  "groupQuantifiers (Neg A) = Neg (groupQuantifiers A)"|
  "groupQuantifiers (Atom A) = Atom A"|
  "groupQuantifiers (ExQ (ExQ A)) = groupQuantifiers (ExN 2 A)"|
  "groupQuantifiers (ExQ (ExN j A)) = groupQuantifiers (ExN (j+1) A)"|
  "groupQuantifiers (ExN j (ExQ A)) = groupQuantifiers (ExN (j+1) A)"|
  "groupQuantifiers (ExN i (ExN j A)) = groupQuantifiers (ExN (i+j) A)"|
  "groupQuantifiers (ExQ A) = ExQ (groupQuantifiers A)"|
  "groupQuantifiers (AllQ (AllQ A)) = groupQuantifiers (AllN 2 A)"|
  "groupQuantifiers (AllQ (AllN j A)) = groupQuantifiers (AllN (j+1) A)"|
  "groupQuantifiers (AllN j (AllQ A)) = groupQuantifiers (AllN (j+1) A)"|
  "groupQuantifiers (AllN i (AllN j A)) = groupQuantifiers (AllN (i+j) A)"|
  "groupQuantifiers (AllQ A) = AllQ (groupQuantifiers A)"|
  "groupQuantifiers (AllN j A) = AllN j A"|
  "groupQuantifiers (ExN j A) = ExN j A"

subsection "Clear Quantifiers"

text "clearQuantifiers F goes through the formula F and removes all quantifiers who's variables
are not present in the formula. For example, clearQuantifiers (ExQ(TrueF)) evaluates to TrueF. This
preserves the truth value of the formula as shown in the clearQuantifiers\\_eval proof. This is used
within the QE overall procedure to eliminate quantifiers in the cases where QE was successful."
fun depth' :: "'a fm \<Rightarrow> nat"where
  "depth' TrueF = 1"|
  "depth' FalseF = 1"|
  "depth' (Atom _) = 1"|
  "depth' (And \<phi> \<psi>) = max (depth' \<phi>) (depth' \<psi>) + 1"|
  "depth' (Or \<phi> \<psi>) = max (depth' \<phi>) (depth' \<psi>) + 1"|
  "depth' (Neg \<phi>) = depth' \<phi> + 1"|
  "depth' (ExQ \<phi>) = depth' \<phi> + 1"|
  "depth' (AllQ \<phi>) = depth' \<phi> + 1"|
  "depth' (AllN i \<phi>) = depth' \<phi>  + i * 2 + 1"|
  "depth' (ExN i \<phi>) = depth' \<phi>  + i * 2 + 1"

function clearQuantifiers :: "atom fm \<Rightarrow> atom fm" where
  "clearQuantifiers TrueF = TrueF"|
  "clearQuantifiers FalseF = FalseF"|
  "clearQuantifiers (Atom a) = simp_atom a"|
  "clearQuantifiers (And \<phi> \<psi>) = and (clearQuantifiers \<phi>) (clearQuantifiers \<psi>)"|
  "clearQuantifiers (Or \<phi> \<psi>) = or (clearQuantifiers \<phi>) (clearQuantifiers \<psi>)"|
  "clearQuantifiers (Neg \<phi>) = neg (clearQuantifiers \<phi>)"|
  "clearQuantifiers (ExQ \<phi>) = 
  (let \<phi>' = clearQuantifiers \<phi> in
  (if freeIn 0 \<phi>' then lowerFm 0 1 \<phi>' else ExQ \<phi>'))"|
  "clearQuantifiers (AllQ \<phi>) = 
  (let \<phi>' = clearQuantifiers \<phi> in
  (if freeIn 0 \<phi>' then lowerFm 0 1 \<phi>' else AllQ \<phi>'))"|
  "clearQuantifiers (ExN 0 \<phi>) = clearQuantifiers \<phi>"|
  "clearQuantifiers (ExN (Suc i) \<phi>) = clearQuantifiers (ExN i (ExQ \<phi>))"|
  "clearQuantifiers (AllN 0 \<phi>) = clearQuantifiers \<phi>"|
  "clearQuantifiers (AllN (Suc i) \<phi>) = clearQuantifiers (AllN i (AllQ \<phi>))"
  by pat_completeness auto
termination
  apply(relation "measures [\<lambda>A. depth' A]")
  by auto

subsection "Push Forall"

fun push_forall :: "atom fm \<Rightarrow> atom fm" where
  "push_forall TrueF = TrueF"|
  "push_forall FalseF = FalseF"|
  "push_forall (Atom a) = simp_atom a"|
  "push_forall (And \<phi> \<psi>) = and (push_forall \<phi>) (push_forall \<psi>)"|
  "push_forall (Or \<phi> \<psi>) = or (push_forall \<phi>) (push_forall \<psi>)"|
  "push_forall (ExQ \<phi>) = ExQ (push_forall \<phi>)"|
  "push_forall (ExN i \<phi>) = ExN i (push_forall \<phi>)"|
  "push_forall (Neg \<phi>) = neg (push_forall \<phi>)"|
  "push_forall (AllQ TrueF) = TrueF"|
  "push_forall (AllQ FalseF) = FalseF"|
  "push_forall (AllQ (Atom a)) = (if freeIn 0 (Atom a) then Atom(lowerAtom 0 1 a) else AllQ (Atom a))"|
  "push_forall (AllQ (And \<phi> \<psi>)) = and (push_forall (AllQ \<phi>)) (push_forall (AllQ \<psi>))"|
  "push_forall (AllQ (Or \<phi> \<psi>)) = ( 
  if freeIn 0 \<phi>  
  then(
    if freeIn 0 \<psi>
    then or (lowerFm 0 1 \<phi>) (lowerFm 0 1 \<psi>)
    else or (lowerFm 0 1 \<phi>) (AllQ \<psi>))
  else (
    if freeIn 0 \<psi>
    then or (AllQ \<phi>) (lowerFm 0 1 \<psi>)
    else AllQ (or \<phi> \<psi>))
)"|
  "push_forall (AllQ \<phi>) = (if freeIn 0 \<phi> then lowerFm 0 1 \<phi> else AllQ \<phi>)"|
  "push_forall (AllN i \<phi>) = AllN i (push_forall  \<phi>)" (* TODO, several bugs in this *)


subsection "Unpower"

fun to_list :: "nat \<Rightarrow> real mpoly \<Rightarrow> (real mpoly * nat) list" where
  "to_list v p = [(isolate_variable_sparse p v x, x). x \<leftarrow> [0..<(MPoly_Type.degree p v)+1]]"

fun chop :: "(real mpoly * nat) list \<Rightarrow> (real mpoly * nat) list"where
  "chop [] = []"|
  "chop ((p,i)#L) = (if p=0 then chop L else (p,i)#L)"

fun decreasePower :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly * nat"where
  "decreasePower v p = (case chop (to_list v p) of [] \<Rightarrow> (p,0) | ((p,i)#L) \<Rightarrow> (sum_list [term * (Var v) ^ (x-i). (term,x)\<leftarrow>((p,i)#L)],i))"

fun unpower :: "nat \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "unpower v (Atom (Eq p)) = (case decreasePower v p of (_,0) \<Rightarrow> Atom(Eq p)| (p,_) \<Rightarrow> Or(Atom (Eq p))(Atom (Eq (Var v))) )"|
  "unpower v (Atom (Neq p)) = (case decreasePower v p of (_,0) \<Rightarrow> Atom(Neq p)| (p,_) \<Rightarrow> And(Atom (Neq p))(Atom (Neq (Var v))) )"|
  "unpower v (Atom (Less p)) = (case decreasePower v p of (_,0) \<Rightarrow> Atom(Less p)| (p,n) \<Rightarrow>
  if n mod 2 = 0 then 
    And(Atom (Less p))(Atom(Neq (Var v)))
  else
    Or
      (And (Atom (Less ( p))) (Atom (Less (-Var v))))
      (And (Atom (Less (-p))) (Atom (Less (Var v))))
 )"|
  "unpower v (Atom (Leq p)) = (case decreasePower v p of (_,0) \<Rightarrow> Atom(Leq p)| (p,n) \<Rightarrow>
  if n mod 2 = 0 then 
    Or (Atom (Leq p)) (Atom (Eq (Var v)))
  else
    Or (Atom (Eq p))
    (Or
      (And (Atom (Less ( p))) (Atom (Leq (-Var v))))
      (And (Atom (Less (-p))) (Atom (Leq (Var v)))))
 )"|
  "unpower v (And a b) = And (unpower v a) (unpower v b)"|
  "unpower v (Or a b) = Or (unpower v a) (unpower v b)"|
  "unpower v (Neg a) = Neg (unpower v a)"|
  "unpower v (TrueF) = TrueF"|
  "unpower v (FalseF) = FalseF"|
  "unpower v (AllQ F) = AllQ(unpower (v+1) F)"|
  "unpower v (ExQ F) = ExQ (unpower (v+1) F)"|
  "unpower v (AllN x F) = AllN x (unpower (v+x) F)"|
  "unpower v (ExN x F) = ExN x (unpower (v+x) F)"



end