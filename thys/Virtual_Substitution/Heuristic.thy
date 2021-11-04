subsection "Heuristic Algorithms"
theory Heuristic
  imports VSAlgos Reindex Optimizations
begin
fun IdentityHeuristic :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> nat" where
  "IdentityHeuristic n _ _ = n"

fun step_augment :: "(nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm) \<Rightarrow> (nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm" where
  "step_augment step heuristic 0 var L F = list_conj (map fm.Atom L @ F)" |
  "step_augment step heuristic (Suc 0) 0 L F = step 0 L F" |
  "step_augment step heuristic _ 0 L F = list_conj (map fm.Atom L @ F)" |
  "step_augment step heuristic (Suc amount) (Suc i) L F =(
  let var = heuristic (Suc i) L F in
  let swappedL = map (swap_atom (i+1) var) L in
  let swappedF = map (swap_fm (i+1) var) F in
 list_disj[step_augment step heuristic amount i al fl. (al,fl)<-dnf ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(step (i+1) swappedL swappedF))])"


fun the_real_step_augment :: "(nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm) \<Rightarrow> nat \<Rightarrow> (atom list * atom fm list * nat) list \<Rightarrow> atom fm" where
  "the_real_step_augment step 0 F = list_disj (map (\<lambda>(L,F,n). ExN n (list_conj (map fm.Atom L @ F))) F)" |
  "the_real_step_augment step (Suc amount) F =(
 ExQ (the_real_step_augment step amount (dnf_modified ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(list_disj(map (\<lambda>(L,F,n). ExN n (step (n+amount) L F)) F))))))"


fun aquireData :: "nat \<Rightarrow> atom list \<Rightarrow> (nat fset*nat fset*nat fset)"where
  "aquireData n L = fold (\<lambda>A (l,e,g). 
 case A of
  Eq p \<Rightarrow> 
  (
    funion l (fset_of_list(filter (\<lambda>v. let (a,b,c) = get_coeffs v p in
    ((MPoly_Type.degree p v = 1 \<or> MPoly_Type.degree p v = 2) \<and> (check_nonzero_const a \<or> check_nonzero_const b \<or> check_nonzero_const c))) [0..<(n+1)])),
  funion e (fset_of_list(filter (\<lambda>v.(MPoly_Type.degree p v = 1 \<or> MPoly_Type.degree p v = 2)) [0..<(n+1)]))
  ,ffilter (\<lambda>v. MPoly_Type.degree p v \<le> 2) g)
 | Leq p \<Rightarrow> (l,e,ffilter (\<lambda>v. MPoly_Type.degree p v \<le> 2) g)
 | Neq p \<Rightarrow> (l,e,ffilter (\<lambda>v. MPoly_Type.degree p v \<le> 2) g)
 | Less p \<Rightarrow> (l,e,ffilter (\<lambda>v. MPoly_Type.degree p v \<le> 2) g)
) L (fempty,fempty,fset_of_list [0..<(n+1)])"


datatype natpair = Pair "nat*nat"

instantiation natpair :: linorder 
begin
definition [simp]: "less_eq (A::natpair) B = (case A of Pair(a,b) \<Rightarrow> (case B of Pair(c,d) \<Rightarrow> if a=c then b\<le>d else a<c))"
definition [simp]: "less (A::natpair) B = (case A of Pair(a,b) \<Rightarrow> (case B of Pair(c,d) \<Rightarrow> if a=c then b<d else a<c))"
instance proof
  fix x :: natpair
  fix y :: natpair
  fix z :: natpair
  obtain a b where x : "x = Pair (a,b)" apply(cases x) by auto
  obtain c d where y : "y = Pair (c,d)" apply(cases y) by auto
  obtain e f where z : "z = Pair (e,f)" apply(cases z) by auto
  show "(x < y) = strict (\<le>) x y"
    unfolding x y by auto
  show "x\<le>x" unfolding x by auto
  show "x\<le> y \<Longrightarrow> y\<le> z \<Longrightarrow> x\<le> z" unfolding x y z apply auto
    apply (metis dual_order.trans not_less_iff_gr_or_eq)
    by (metis less_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding x y apply auto
    apply (metis not_less_iff_gr_or_eq)
    by (metis antisym_conv not_less_iff_gr_or_eq)
  show "x \<le> y \<or> y \<le> x" unfolding x y by auto
qed
end

fun getBest :: "nat fset \<Rightarrow> atom list \<Rightarrow> nat option" where
  "getBest S L = (let X =  fset_of_list(map (\<lambda>x. Pair(count_list (map (\<lambda>l. case l of
   Eq p   \<Rightarrow> MPoly_Type.degree p x = 0
|  Less p \<Rightarrow> MPoly_Type.degree p x = 0
|  Neq p  \<Rightarrow> MPoly_Type.degree p x = 0
|  Leq p  \<Rightarrow> MPoly_Type.degree p x = 0
) L) False,x)) (sorted_list_of_fset S)) in
(case (sorted_list_of_fset X) of [] \<Rightarrow> None | Cons (Pair(x,v)) _ \<Rightarrow> Some v))
"

fun heuristicPicker :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> (nat*(nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm)) option"where
  "heuristicPicker n L F = (case (let (l,e,g) = aquireData n L in
(case getBest l L of
  None \<Rightarrow> (case F of 
  [] \<Rightarrow> 
    (case getBest g L of 
    None \<Rightarrow> (case getBest e L of None \<Rightarrow> None | Some v \<Rightarrow> Some(v,qe_eq_repeat))
    | Some v \<Rightarrow> Some(v,gen_qe)
    )
  | _ \<Rightarrow> (case getBest e L of None \<Rightarrow> None | Some v \<Rightarrow> Some(v,qe_eq_repeat))
  )
| Some v \<Rightarrow> Some(v,luckyFind')
)) of None => None | Some(var,step) => (if var > n then None else Some(var,step)))"


fun superPicker :: "nat \<Rightarrow> nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm" where
  "superPicker 0 var L F = list_conj (map fm.Atom L @ F)"|
  "superPicker amount 0 L F = (case heuristicPicker 0 L F of Some(0,step) \<Rightarrow> step 0 L F | _ \<Rightarrow> list_conj (map fm.Atom L @ F))" |
  "superPicker (Suc amount) (Suc i) L F =(
  case heuristicPicker (Suc i) L F of
   Some(var,step) \<Rightarrow>
    let swappedL = map (swap_atom (i+1) var) L in
    let swappedF = map (swap_fm (i+1) var) F in
    list_disj[superPicker amount i al fl. (al,fl)<-dnf ((push_forall \<circ> nnf \<circ> unpower 0 o groupQuantifiers o clearQuantifiers)(step (i+1) swappedL swappedF))]
  | None \<Rightarrow> list_conj (map fm.Atom L @ F))"


datatype quadnat = Quad "nat \<times> nat \<times> nat \<times> nat"

instantiation quadnat :: linorder begin
definition [simp]:"A<B =
  (case A of  Quad(a1,b1,c1,d1) \<Rightarrow> (case B of Quad(a2,b2,c2,d2) \<Rightarrow>
  (if a1=a2 then (
    if b1=b2 then (
      if c1=c2 then d1<d2 else c1<c2
    ) else b1<b2
  ) else a1<a2)))"
definition [simp]:"A\<le>B =
  (case A of  Quad(a1,b1,c1,d1) \<Rightarrow> (case B of Quad(a2,b2,c2,d2) \<Rightarrow>
  (if a1=a2 then (
    if b1=b2 then (
      if c1=c2 then d1\<le>d2 else c1<c2
    ) else b1<b2
  ) else a1<a2)))"
instance proof
  fix x y z
  obtain a1 b1 c1 d1 where x : "x = Quad(a1,b1,c1,d1)"
    by (metis prod_cases4 quadnat.exhaust) 
  obtain a2 b2 c2 d2 where y : "y = Quad(a2,b2,c2,d2)"
    by (metis prod_cases4 quadnat.exhaust) 
  obtain a3 b3 c3 d3 where z : "z = Quad(a3,b3,c3,d3)"
    by (metis prod_cases4 quadnat.exhaust) 
  show "(x < y) = strict (\<le>) x y" unfolding x y by auto
  show "x \<le> x" unfolding x by auto
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding x y z apply auto
    apply (metis dual_order.trans not_less_iff_gr_or_eq)
    apply (metis less_trans)
    apply (metis dual_order.strict_trans not_less_iff_gr_or_eq)
    apply (metis less_trans)
    apply (metis dual_order.strict_trans not_less_iff_gr_or_eq)
    apply (metis less_trans)
    apply (metis less_trans not_less_iff_gr_or_eq)
    by (metis less_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding x y apply auto
    apply (metis less_imp_not_less)
    apply (metis not_less_iff_gr_or_eq)
    apply (metis not_less_iff_gr_or_eq)
    by (metis antisym_conv not_less_iff_gr_or_eq)
  show "x \<le> y \<or> y \<le> x" unfolding x y by auto
qed
end

fun brownsHeuristic :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> nat" where
  "brownsHeuristic n L _ = (case sorted_list_of_fset (fset_of_list (map (\<lambda>x.
  case (foldl (\<lambda>(maxdeg,totaldeg,appearancecount) l. 
  let p = case l of Eq p \<Rightarrow> p | Less p \<Rightarrow> p | Leq p \<Rightarrow> p | Neq p \<Rightarrow> p in
  let deg = MPoly_Type.degree p x in
  (max maxdeg deg,totaldeg+deg,appearancecount+(if deg>0 then 1 else 0))) (0,0,0) L) of (a,b,c) \<Rightarrow> Quad(a,b,c,x)
 ) [0..<n])) of [] \<Rightarrow> n | Cons (Quad(_,_,_,x)) _ \<Rightarrow> if x>n then n else x)"


end
