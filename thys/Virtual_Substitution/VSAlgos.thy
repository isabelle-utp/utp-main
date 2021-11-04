section "Algorithms"
subsection "Equality VS Helper Functions"
theory VSAlgos
  imports Debruijn Optimizations
begin


text "This is a subprocess which simply separates out the equality atoms from the other kinds of atoms

Note that we search for equality atoms that are of degree one or two

This is used within the equalityVS algorithm"
fun find_eq :: "nat \<Rightarrow> atom list \<Rightarrow> real mpoly list * atom list" where
  "find_eq var [] = ([],[])"|
  "find_eq var ((Less p)#as) = (let (A,B) = find_eq var as in (A,Less p#B))" |
  "find_eq var ((Eq p)#as) = (let (A,B) = find_eq var as in
   if MPoly_Type.degree p var < 3 \<and> MPoly_Type.degree p var \<noteq> 0
  then (p # A,B) 
  else (A,Eq p # B)
)"|
  "find_eq var ((Leq p)#as) = (let (A,B) = find_eq var as in (A,Leq p#B))" |
  "find_eq var ((Neq p)#as) = (let (A,B) = find_eq var as in (A,Neq p#B))"




(* given ax^2+bx+c returns formula representing a=0 and b=0 and c=0 *)
fun split_p :: "nat \<Rightarrow> real mpoly \<Rightarrow> atom fm" where
  "split_p var p = And (Atom (Eq (isolate_variable_sparse p var 2)))
                (And (Atom (Eq (isolate_variable_sparse p var 1)))
                     (Atom (Eq (isolate_variable_sparse p var 0))))"



text "
The linearsubstitution virtually substitutes in an equation of $b*x+c=0$ into an arbitrary atom

linearsubstitution x b c (Eq p) = F corresponds to removing variable x from polynomial p and replacing
it with an equivalent function F where F doesn't mention variable x

If there exists a way to assign variables that makes p = 0 true,
then that same set of variables will make F true

If there exists a way to assign variables that makes F true and also have b*x+c=0,
then that same set of variables will make p=0 true

Same applies for other kinds of atoms that aren't equality
"
fun linear_substitution :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom \<Rightarrow> atom" where
  "linear_substitution var a b (Eq p) = 
  (let d = MPoly_Type.degree p var in
    (Eq (\<Sum>i\<in>{0..<(d+1)}.  isolate_variable_sparse p var i * (a^i) * (b^(d-i))))
  )" |
  "linear_substitution var a b (Less p) = 
  (let d = MPoly_Type.degree p var in
    let P = (\<Sum>i\<in>{0..<(d+1)}. isolate_variable_sparse p var i * (a^i) * (b^(d-i))) in
      (Less(P * (b ^ (d mod 2))))
    )"|
  "linear_substitution var a b (Leq p) = 
  (let d = MPoly_Type.degree p var in
    let P = (\<Sum>i\<in>{0..<(d+1)}. isolate_variable_sparse p var i * (a^i) * (b^(d-i))) in
      (Leq(P * (b ^ (d mod 2))))
    )"|
  "linear_substitution var a b (Neq p) = 
  (let d = MPoly_Type.degree p var in
    (Neq (\<Sum>i\<in>{0..<(d+1)}.  isolate_variable_sparse p var i * (a^i) * (b^(d-i))))
  )"

fun linear_substitution_fm_helper :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom fm \<Rightarrow> nat \<Rightarrow> atom fm" where
  "linear_substitution_fm_helper var b c F z = liftmap (\<lambda>x.\<lambda>A. Atom(linear_substitution (var+x) (liftPoly 0 x b) (liftPoly 0 x c) A)) F z"

fun linear_substitution_fm :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "linear_substitution_fm var b c F = linear_substitution_fm_helper var b c F 0"


text "
quadraticpart1 var a b A takes in an expression of the form
(a+b * sqrt(c))/d
for an arbitrary c and substitutes it in for the variable var in the atom A
"
fun quadratic_part_1 :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom \<Rightarrow> real mpoly" where
  "quadratic_part_1 var a b d (Eq p) = (
  let deg = MPoly_Type.degree p var in
  \<Sum>i\<in>{0..<(deg+1)}. (isolate_variable_sparse p var i) * ((a+b*(Var var))^i) * (d^(deg - i))
)" |
  "quadratic_part_1 var a b d (Less p) = (
  let deg = MPoly_Type.degree p var in
  let P = \<Sum>i\<in>{0..<(deg+1)}. (isolate_variable_sparse p var i) * ((a+b*(Var var))^i) * (d^(deg - i)) in
  P * (d ^ (deg mod 2))
)"|
  "quadratic_part_1 var a b d (Leq p) = (
  let deg = MPoly_Type.degree p var in
  let P = \<Sum>i\<in>{0..<(deg+1)}. (isolate_variable_sparse p var i) * ((a+b*(Var var))^i) * (d^(deg - i)) in
  P * (d ^ (deg mod 2))
)"|
  "quadratic_part_1 var a b d (Neq p) = (
  let deg = MPoly_Type.degree p var in
  \<Sum>i\<in>{0..<(deg+1)}. (isolate_variable_sparse p var i) * ((a+b*(Var var))^i) * (d^(deg - i))
)"

fun quadratic_part_2 :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly" where
  "quadratic_part_2 var sq p = (
  let deg = MPoly_Type.degree p var in
  \<Sum>i\<in>{0..<deg+1}. 
    (isolate_variable_sparse p var i)*(sq^(i div 2)) * (Const(of_nat(i mod 2))) * (Var var) 
   +(isolate_variable_sparse p var i)*(sq^(i div 2)) * Const(1-of_nat(i mod 2))
)
"

text"
quadraticsub var a b c d A represents virtually substituting an expression of the form
(a+b*sqrt(c))/d into variable var in atom A
"
primrec quadratic_sub :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom \<Rightarrow> atom fm" where
  "quadratic_sub var a b c d (Eq p) = (
    let (p1::real mpoly) = quadratic_part_1 var a b d (Eq p) in
    let (p2::real mpoly) = quadratic_part_2 var c p1 in
    let (A::real mpoly) = isolate_variable_sparse p2 var 0 in
    let (B::real mpoly) = isolate_variable_sparse p2 var 1 in
    And
      (Atom(Leq (A*B)))
      (Atom (Eq (A^2-B^2*c)))
)" | 
  "quadratic_sub var a b c d (Less p) = (
    let (p1::real mpoly) = quadratic_part_1 var a b d (Less p) in
    let (p2::real mpoly) = quadratic_part_2 var c p1 in
    let (A::real mpoly) = isolate_variable_sparse p2 var 0 in
    let (B::real mpoly) = isolate_variable_sparse p2 var 1 in
    Or
      (And
        (Atom(Less(A)))
        (Atom (Less (B^2*c-A^2))))
      (And
        (Atom(Leq B))
        (Or
          (Atom(Less A))
          (Atom(Less (A^2-B^2*c)))))
)" |
  "quadratic_sub var a b c d (Leq p) = (
    let (p1::real mpoly) = quadratic_part_1 var a b d (Leq p) in
    let (p2::real mpoly) = quadratic_part_2 var c p1 in
    let (A::real mpoly) = isolate_variable_sparse p2 var 0 in
    let (B::real mpoly) = isolate_variable_sparse p2 var 1 in
    Or
      (And
        (Atom(Leq(A)))
        (Atom (Leq(B^2*c-A^2))))
      (And
        (Atom(Leq B))
        (Atom(Leq (A^2-B^2*c))))
)" |
  "quadratic_sub var a b c d (Neq p) = (
    let (p1::real mpoly) = quadratic_part_1 var a b d (Neq p) in
    let (p2::real mpoly) = quadratic_part_2 var c p1 in
    let (A::real mpoly) = isolate_variable_sparse p2 var 0 in
    let (B::real mpoly) = isolate_variable_sparse p2 var 1 in
    Or
      (Atom(Less(-A*B)))
      (Atom (Neq(A^2-B^2*c)))
)"


fun quadratic_sub_fm_helper :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom fm \<Rightarrow> nat \<Rightarrow> atom fm" where
  "quadratic_sub_fm_helper var a b c d F z = liftmap (\<lambda>x.\<lambda>A. quadratic_sub (var+x) (liftPoly 0 x a) (liftPoly 0 x b) (liftPoly 0 x c) (liftPoly 0 x d) A) F z"

fun quadratic_sub_fm :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "quadratic_sub_fm var a b c d F = quadratic_sub_fm_helper var a b c d F 0"

subsection "General VS Helper Functions"
  (*
  allZero p var
  takes in a polynomial of the form sum a_i x^i where x is the variable var
  returns the formula where all a_i=0
*)
fun allZero :: "real mpoly \<Rightarrow> nat \<Rightarrow> atom fm" where
  "allZero p var = list_conj [Atom(Eq(isolate_variable_sparse p var i)). i <- [0..<(MPoly_Type.degree p var)+1]]"

fun alternateNegInfinity :: "real mpoly \<Rightarrow> nat \<Rightarrow> atom fm" where
  "alternateNegInfinity p var = foldl (\<lambda>F.\<lambda>i.
let a_n = isolate_variable_sparse p var i in
let exp = (if i mod 2 = 0 then Const(1) else Const(-1)) in
  or (Atom(Less (exp * a_n)))
    (and (Atom (Eq a_n)) F)
) FalseF ([0..<((MPoly_Type.degree p var)+1)])"


(*
  substNegInfity var a
  substitutes negative infinity for the variable var in the atom a
  defined in pages 610-611
*)
fun substNegInfinity :: "nat \<Rightarrow> atom \<Rightarrow> atom fm" where
  "substNegInfinity var (Eq p) = allZero p var " |
  "substNegInfinity var (Less p) = alternateNegInfinity p var"|
  "substNegInfinity var (Leq p) = Or (alternateNegInfinity p var) (allZero p var)"|
  "substNegInfinity var (Neq p) = Neg (allZero p var)"

(*
  convertDerivative var p
  is equivalent to p^+ < 0 defined on page 615 around variable var
*)
function convertDerivative :: "nat \<Rightarrow> real mpoly \<Rightarrow> atom fm" where
  "convertDerivative var p = (if (MPoly_Type.degree p var) = 0 then Atom (Less p) else
  Or (Atom (Less p)) (And (Atom(Eq p)) (convertDerivative var (derivative var p))))"
  by pat_completeness auto
termination
  apply(relation "measures [\<lambda>(var,p). MPoly_Type.degree p var]")
  apply auto
  using degree_derivative
  by (metis less_add_one)

(*
  substInfinitesimalLinear var b c A
  substitutes -c/b+epsilon for variable var in atom A
  assumes b is nonzero
  defined in page 615
*)
fun substInfinitesimalLinear :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom \<Rightarrow> atom fm" where
  "substInfinitesimalLinear var b c (Eq p) = allZero p var"|
  "substInfinitesimalLinear var b c (Less p) = 
  liftmap
    (\<lambda>x. \<lambda>A. Atom(linear_substitution (var+x) (liftPoly 0 x b) (liftPoly 0 x c) A)) 
    (convertDerivative var p)
    0"|
  "substInfinitesimalLinear var b c (Leq p) = 
Or
  (allZero p var)
  (liftmap
    (\<lambda>x. \<lambda>A. Atom(linear_substitution (var+x) (liftPoly 0 x b) (liftPoly 0 x c) A)) 
    (convertDerivative var p)
    0)"|
  "substInfinitesimalLinear var b c (Neq p) = neg (allZero p var)"

(*
  substInfinitesimalQuadratic var a b c A
  substitutes (quadratic equation)+epsilon for variable var in atom A
  assumes a is nonzero and the determinant is positive
  defined in page 615
*)
fun substInfinitesimalQuadratic :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom \<Rightarrow> atom fm" where
  "substInfinitesimalQuadratic var a b c d (Eq p) = allZero p var"|
  "substInfinitesimalQuadratic var a b c d (Less p) = quadratic_sub_fm var a b c d (convertDerivative var p)"|
  "substInfinitesimalQuadratic var a b c d (Leq p) = 
Or
  (allZero p var)
  (quadratic_sub_fm var a b c d (convertDerivative var p))"|
  "substInfinitesimalQuadratic var a b c d (Neq p) = neg (allZero p var)"


fun substInfinitesimalLinear_fm :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "substInfinitesimalLinear_fm var b c F = liftmap (\<lambda>x.\<lambda>A. substInfinitesimalLinear (var+x) (liftPoly 0 x b) (liftPoly 0 x c) A) F 0"


fun substInfinitesimalQuadratic_fm :: "nat \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> real mpoly \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "substInfinitesimalQuadratic_fm var a b c d F = liftmap (\<lambda>x.\<lambda>A. substInfinitesimalQuadratic (var+x) (liftPoly 0 x a) (liftPoly 0 x b) (liftPoly 0 x c) (liftPoly 0 x d) A) F 0"

subsection "VS Algorithms"

text
  "elimVar var L F
  attempts to do quadratic elimination on the variable defined by var.
  L is the list of conjuctive atoms, F is a list of unnecessary garbage"
fun elimVar :: "nat \<Rightarrow> atom list \<Rightarrow> (atom fm) list \<Rightarrow> atom \<Rightarrow> atom fm" where
  "elimVar var L F (Eq p) =  (
  let (a,b,c) = get_coeffs var p in

   (Or 
      
      (And (And (Atom (Eq a)) (Atom (Neq b)))
      (list_conj (
        (map (\<lambda>a. Atom (linear_substitution var (-c) b a)) L)@
        (map (linear_substitution_fm var (-c) b) F)
        )))
      

      (And (Atom (Neq a)) (And (Atom(Leq (-(b^2)+4*a*c)))
        (Or (list_conj (
        (map (quadratic_sub var (-b) 1 (b^2-4*a*c) (2*a)) L)@
        (map (quadratic_sub_fm var (-b) 1 (b^2-4*a*c) (2*a)) F)
        ))
        (list_conj (
        (map (quadratic_sub var (-b) (-1) (b^2-4*a*c) (2*a)) L)@
        (map (quadratic_sub_fm var (-b) (-1) (b^2-4*a*c) (2*a)) F)
        ))
       ))
      ))

)" |
  "elimVar var L F (Less p) =  (
  let (a,b,c) = get_coeffs var p in
    (Or 
      
      (And (And (Atom (Eq a)) (Atom (Neq b)))
      (list_conj (
          (map (substInfinitesimalLinear var (-c) b) L)
          @(map (substInfinitesimalLinear_fm var (-c) b) F)
      )))
      

      (And (Atom (Neq a)) (And (Atom(Leq (-(b^2)+4*a*c)))
        (Or (list_conj (
        (map (substInfinitesimalQuadratic var (-b) 1 (b^2-4*a*c) (2*a)) L)@
        (map (substInfinitesimalQuadratic_fm var (-b) 1 (b^2-4*a*c) (2*a)) F)
        ))
        (list_conj (
        (map (substInfinitesimalQuadratic var (-b) (-1) (b^2-4*a*c) (2*a)) L)@
        (map (substInfinitesimalQuadratic_fm var (-b) (-1) (b^2-4*a*c) (2*a)) F)
        ))
       ))
      ))
)"|
  "elimVar var L F (Neq p) =  (
  let (a,b,c) = get_coeffs var p in
    (Or 
      
      (And (And (Atom (Eq a)) (Atom (Neq b)))
      (list_conj (
          (map (substInfinitesimalLinear var (-c) b) L)
          @(map (substInfinitesimalLinear_fm var (-c) b) F)
      )))
      

      (And (Atom (Neq a)) (And (Atom(Leq (-(b^2)+4*a*c)))
        (Or (list_conj (
        (map (substInfinitesimalQuadratic var (-b) 1 (b^2-4*a*c) (2*a)) L)@
        (map (substInfinitesimalQuadratic_fm var (-b) 1 (b^2-4*a*c) (2*a)) F)
        ))
        (list_conj (
        (map (substInfinitesimalQuadratic var (-b) (-1) (b^2-4*a*c) (2*a)) L)@
        (map (substInfinitesimalQuadratic_fm var (-b) (-1) (b^2-4*a*c) (2*a)) F)
        ))
       ))
      )))
"|
  "elimVar var L F (Leq p) =  (
  let (a,b,c) = get_coeffs var p in

   (Or 
      
      (And (And (Atom (Eq a)) (Atom (Neq b)))
      (list_conj (
        (map (\<lambda>a. Atom (linear_substitution var (-c) b a)) L)@
        (map (linear_substitution_fm var (-c) b) F)
        )))
      

      (And (Atom (Neq a)) (And (Atom(Leq (-(b^2)+4*a*c)))
        (Or (list_conj (
        (map (quadratic_sub var (-b) 1 (b^2-4*a*c) (2*a)) L)@
        (map (quadratic_sub_fm var (-b) 1 (b^2-4*a*c) (2*a)) F)
        ))
        (list_conj (
        (map (quadratic_sub var (-b) (-1) (b^2-4*a*c) (2*a)) L)@
        (map (quadratic_sub_fm var (-b) (-1) (b^2-4*a*c) (2*a)) F)
        ))
       ))
      ))

)"

(* single virtual substitution of equality *)
fun qe_eq_one :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm" where
  "qe_eq_one var L F = 
    (case find_eq var L of 
        (p#A,L') \<Rightarrow> Or (And (Neg (split_p var p))
                      ((elimVar var L F) (Eq p))
                    )
                    (And (split_p var p) 
                      (list_conj (map Atom ((map Eq A)  @ L') @ F))
                    )
      | ([],L') \<Rightarrow> list_conj ((map Atom L) @ F)
)"


fun check_nonzero_const :: "real mpoly \<Rightarrow> bool"where
  "check_nonzero_const p = (case get_if_const p of Some x \<Rightarrow> x \<noteq> 0 | None \<Rightarrow> False)"

fun find_lucky_eq :: "nat \<Rightarrow> atom list \<Rightarrow> real mpoly option"where
  "find_lucky_eq v [] = None"|
  "find_lucky_eq v (Eq p#L) = 
(let (a,b,c) = get_coeffs v p in
(if (MPoly_Type.degree p v = 1 \<or> MPoly_Type.degree p v = 2) \<and> (check_nonzero_const a \<or> check_nonzero_const b \<or> check_nonzero_const c) then Some p else
find_lucky_eq v L
))"|
  "find_lucky_eq v (_#L) = find_lucky_eq v L"


fun luckyFind :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm option" where
  "luckyFind v L F = (case find_lucky_eq v L of Some p \<Rightarrow> Some ((elimVar v L F) (Eq p)) | None \<Rightarrow> None)"

fun luckyFind' :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm" where
  "luckyFind' v L F = (case find_lucky_eq v L of Some p \<Rightarrow> (elimVar v L F) (Eq p) | None \<Rightarrow> And (list_conj (map Atom L)) (list_conj F))"


fun find_luckiest_eq :: "nat \<Rightarrow> atom list \<Rightarrow> real mpoly option"where
  "find_luckiest_eq v [] = None"|
  "find_luckiest_eq v (Eq p#L) = 
(if (MPoly_Type.degree p v = 1 \<or> MPoly_Type.degree p v = 2) then
(let (a,b,c) = get_coeffs v p in
 (case get_if_const a of None \<Rightarrow> find_luckiest_eq v L
 | Some a \<Rightarrow> (case get_if_const b of None \<Rightarrow> find_luckiest_eq v L
 | Some b \<Rightarrow> (case get_if_const c of None \<Rightarrow> find_luckiest_eq v L
 | Some c \<Rightarrow> if a\<noteq>0\<or>b\<noteq>0\<or>c\<noteq>0 then Some p else find_luckiest_eq v L))))
 else
find_luckiest_eq v L
)"|
  "find_luckiest_eq v (_#L) = find_luckiest_eq v L"



fun luckiestFind :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm" where
  "luckiestFind v L F = (case find_luckiest_eq v L of Some p \<Rightarrow> (elimVar v L F) (Eq p) | None \<Rightarrow> And (list_conj (map Atom L)) (list_conj F))"


primrec qe_eq_repeat_helper :: "nat \<Rightarrow> real mpoly list \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm" where
  "qe_eq_repeat_helper var [] L F = list_conj ((map Atom L) @ F)"|
  "qe_eq_repeat_helper var (p#A) L F = 
  Or (And (Neg (split_p var p))
    ((elimVar var ((map Eq (p#A)) @ L) F) (Eq p))
  )
  (And (split_p var p) 
    (qe_eq_repeat_helper var A L F)
  )"

fun qe_eq_repeat :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm" where
  "qe_eq_repeat var L F = 
    (case luckyFind var L F of Some(F) \<Rightarrow> F | None \<Rightarrow> 
    (let (A,L') = find_eq var L in
      qe_eq_repeat_helper var A L' F 
)
)
"

fun all_degree_2 :: "nat \<Rightarrow> atom list \<Rightarrow> bool" where
  "all_degree_2 var [] = True"|
  "all_degree_2 var (Eq p#as) = ((MPoly_Type.degree p var \<le> 2)\<and>(all_degree_2 var as))"|
  "all_degree_2 var (Less p#as) = ((MPoly_Type.degree p var \<le> 2)\<and>(all_degree_2 var as))"|
  "all_degree_2 var (Leq p#as) = ((MPoly_Type.degree p var \<le> 2)\<and>(all_degree_2 var as))"|
  "all_degree_2 var (Neq p#as) = ((MPoly_Type.degree p var \<le> 2)\<and>(all_degree_2 var as))"

fun gen_qe :: "nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm" where
  "gen_qe var L F = (case F of 
[] \<Rightarrow> (case luckyFind var L [] of Some F \<Rightarrow> F | None \<Rightarrow> (
    (if all_degree_2 var L 
      then list_disj (list_conj (map (substNegInfinity var) L) # (map (elimVar var L []) L)) 
  else (qe_eq_repeat var L []))))
| _ \<Rightarrow> qe_eq_repeat var L F
)"

subsection "DNF"

fun dnf :: "atom fm \<Rightarrow> (atom list * atom fm list) list" where
  "dnf TrueF = [([],[])]" |
  "dnf FalseF = []" |
  "dnf (Atom \<phi>) = [([\<phi>],[])]" |
  "dnf (And \<phi>\<^sub>1 \<phi>\<^sub>2) = [(A@B,A'@B').(A,A')\<leftarrow>dnf \<phi>\<^sub>1,(B,B')\<leftarrow>dnf \<phi>\<^sub>2]" |
  "dnf (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = dnf \<phi>\<^sub>1 @ dnf \<phi>\<^sub>2" |
  "dnf (ExQ \<phi>) = [([],[ExQ \<phi>])]" |
  "dnf (Neg \<phi>) = [([],[Neg \<phi>])]"|
  "dnf (AllQ \<phi>) = [([],[AllQ \<phi>])]"|
  "dnf (AllN i \<phi>) = [([],[AllN i \<phi>])]"|
  "dnf (ExN i \<phi>) = [([],[ExN i \<phi>])]"

text "
  dnf F
  returns the \"disjunctive normal form\" of F, but since F can contain quantifiers, we return
  (L,R,n) terms in a list. each term in the list represents a conjunction over the outside disjunctive list
    
  L is all the atoms we are able to reach, we are allowed to go underneath exists binders
  
  R is the remaining formulas (negation exists cannot be simplified) which are also under the same number
      of exist binders.

  n is the total number of binders each conjunct has
"
fun dnf_modified :: "atom fm \<Rightarrow> (atom list * atom fm list * nat) list" where
  "dnf_modified TrueF = [([],[],0)]" |
  "dnf_modified FalseF = []" |
  "dnf_modified (Atom \<phi>) = [([\<phi>],[],0)]" |
  "dnf_modified (And \<phi>\<^sub>1 \<phi>\<^sub>2) = [
  let A = map (liftAtom d1 d2) A in
  let B = map (liftAtom 0 d1) B in
  let A' = map (liftFm d1 d2) A' in
  let B' = map (liftFm 0 d1) B' in
    (A @ B, A' @ B',d1+d2).
  (A,A',d1) \<leftarrow> dnf_modified \<phi>\<^sub>1, (B,B',d2) \<leftarrow> dnf_modified \<phi>\<^sub>2]" |
  "dnf_modified (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = dnf_modified \<phi>\<^sub>1 @ dnf_modified \<phi>\<^sub>2" |
  "dnf_modified (ExQ \<phi>) = [(A,A',d+1). (A,A',d) \<leftarrow> dnf_modified \<phi>]" |
  "dnf_modified (Neg \<phi>) = [([],[Neg \<phi>],0)]"|
  "dnf_modified (AllQ \<phi>) = [([],[AllQ \<phi>],0)]"|
  "dnf_modified (AllN i \<phi>) = [([],[AllN i \<phi>],0)]"|
  "dnf_modified (ExN i \<phi>) = [(A,A',d+i). (A,A',d) \<leftarrow> dnf_modified \<phi>]"


(*
repeatedly applies nnf and dnf on subformulas and then attempts to eliminate the quantifier based
on the qe quantifier elimination method given. Works on innermost variables first and builds out
*)
fun QE_dnf :: "(atom fm \<Rightarrow> atom fm) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> atom list \<Rightarrow> atom fm list \<Rightarrow> atom fm) \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "QE_dnf opt step (And \<phi>\<^sub>1 \<phi>\<^sub>2) = and (QE_dnf opt step \<phi>\<^sub>1) (QE_dnf opt step \<phi>\<^sub>2)" |
  "QE_dnf opt step (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = or (QE_dnf opt step \<phi>\<^sub>1) (QE_dnf opt step \<phi>\<^sub>2)" |
  "QE_dnf opt step (Neg \<phi>) = neg(QE_dnf opt step \<phi>)" |
  "QE_dnf opt step (ExQ \<phi>) = list_disj [ExN (n+1) (step 1 n al fl). (al,fl,n)\<leftarrow>(dnf_modified(opt(QE_dnf opt step \<phi>)))]"|
  "QE_dnf opt step (TrueF) = TrueF"|
  "QE_dnf opt step (FalseF) = FalseF"|
  "QE_dnf opt step (Atom a) = simp_atom a"|
  "QE_dnf opt step (AllQ \<phi>) = Neg(list_disj [ExN (n+1) (step 1 n al fl). (al,fl,n)\<leftarrow>(dnf_modified(opt(neg(QE_dnf opt step \<phi>))))])"|
  "QE_dnf opt step (ExN 0 \<phi>) = QE_dnf opt step \<phi>"|
  "QE_dnf opt step (AllN 0 \<phi>) = QE_dnf opt step \<phi>"|
  "QE_dnf opt step (AllN (Suc i) \<phi>) = Neg(list_disj [ExN (n+i+1) (step (Suc i) (n+i) al fl). (al,fl,n)\<leftarrow>(dnf_modified(opt(neg(QE_dnf opt step \<phi>))))])"|
  "QE_dnf opt step (ExN (Suc i) \<phi>) = list_disj [ExN (n+i+1) (step (Suc i) (n+i) al fl). (al,fl,n)\<leftarrow>(dnf_modified(opt(QE_dnf opt step \<phi>)))]"

fun QE_dnf' :: "(atom fm \<Rightarrow> atom fm) \<Rightarrow> (nat \<Rightarrow> (atom list * atom fm list * nat) list  \<Rightarrow> atom fm) \<Rightarrow> atom fm \<Rightarrow> atom fm" where 
  "QE_dnf' opt step (And \<phi>\<^sub>1 \<phi>\<^sub>2) = and (QE_dnf' opt step \<phi>\<^sub>1) (QE_dnf' opt step \<phi>\<^sub>2)" |
  "QE_dnf' opt step (Or \<phi>\<^sub>1 \<phi>\<^sub>2) = or (QE_dnf' opt step \<phi>\<^sub>1) (QE_dnf' opt step \<phi>\<^sub>2)" |
  "QE_dnf' opt step (Neg \<phi>) = neg(QE_dnf' opt step \<phi>)" |
  "QE_dnf' opt step (ExQ \<phi>) = step 1 (dnf_modified(opt(QE_dnf' opt step \<phi>)))"|
  "QE_dnf' opt step (TrueF) = TrueF"|
  "QE_dnf' opt step (FalseF) = FalseF"|
  "QE_dnf' opt step (Atom a) = simp_atom a"|
  "QE_dnf' opt step (AllQ \<phi>) = Neg(step 1 (dnf_modified(opt(neg(QE_dnf' opt step \<phi>)))))"|
  "QE_dnf' opt step (ExN 0 \<phi>) = QE_dnf' opt step \<phi>"|
  "QE_dnf' opt step (AllN 0 \<phi>) = QE_dnf' opt step \<phi>"|
  "QE_dnf' opt step (AllN (Suc i) \<phi>) = Neg(step  (Suc i) (dnf_modified(opt(neg(QE_dnf' opt step \<phi>)))))"|
  "QE_dnf' opt step (ExN (Suc i) \<phi>) = step (Suc i) (dnf_modified(opt(QE_dnf' opt step \<phi>)))"

subsection "Repeat QE multiple times"

fun countQuantifiers :: "atom fm \<Rightarrow> nat" where
  "countQuantifiers (Atom _) = 0"|
  "countQuantifiers (TrueF) = 0"|
  "countQuantifiers (FalseF) = 0"|
  "countQuantifiers (And a b) = countQuantifiers a + countQuantifiers b"|
  "countQuantifiers (Or a b) = countQuantifiers a + countQuantifiers b"|
  "countQuantifiers (Neg a) = countQuantifiers a"|
  "countQuantifiers (ExQ a) = countQuantifiers a + 1"|
  "countQuantifiers (AllQ a) = countQuantifiers a + 1"|
  "countQuantifiers (ExN n a) = countQuantifiers a + n"|
  "countQuantifiers (AllN n a) = countQuantifiers a + n"

fun repeatAmountOfQuantifiers_helper :: "(atom fm \<Rightarrow> atom fm) \<Rightarrow> nat \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "repeatAmountOfQuantifiers_helper step 0 F = F"|
  "repeatAmountOfQuantifiers_helper step (Suc i) F = repeatAmountOfQuantifiers_helper step i (step F)"

fun repeatAmountOfQuantifiers :: "(atom fm \<Rightarrow> atom fm) \<Rightarrow> atom fm \<Rightarrow> atom fm" where
  "repeatAmountOfQuantifiers step F = (
let F = step F in
let n = countQuantifiers F in
repeatAmountOfQuantifiers_helper step n F
)"

end