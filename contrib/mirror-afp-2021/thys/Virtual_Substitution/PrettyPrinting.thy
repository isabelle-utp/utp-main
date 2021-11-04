theory PrettyPrinting
  imports
    ExecutiblePolyProps
    PolyAtoms
    Polynomials.Show_Polynomials
    Polynomials.Power_Products
begin

global_interpretation drlex_pm: linorder drlex_pm drlex_pm_strict
  defines Min_drlex_pm = "linorder.Min drlex_pm"
    and Max_drlex_pm = "linorder.Max drlex_pm"
    and sorted_drlex_pm = "linorder.sorted drlex_pm"
    and sorted_list_of_set_drlex_pm = "linorder.sorted_list_of_set drlex_pm"
    and sort_key_drlex_pm = "linorder.sort_key drlex_pm"
    and insort_key_drlex_pm = "linorder.insort_key drlex_pm"
    and part_drlex_pm = "drlex_pm.part"
  apply unfold_locales
  subgoal by (simp add: drlex_pm_strict_def)
  subgoal by (simp add: drlex_pm_refl)
  subgoal using drlex_pm_trans by auto
  subgoal by (simp add: drlex_pm_antisym)
  subgoal by (simp add: drlex_pm_lin) 
  done

definition "monomials_list mp = drlex_pm.sorted_list_of_set (monomials mp)"

definition shows_monomial_gen::"((nat \<times> nat) \<Rightarrow> shows) \<Rightarrow> ('a \<Rightarrow> shows) \<Rightarrow> shows \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a option \<Rightarrow> shows" where
  "shows_monomial_gen shows_factor shows_coeff sep mon cff =
    shows_sep (\<lambda>s. case s of
        Inl cff \<Rightarrow> shows_coeff cff
      | Inr factor \<Rightarrow> shows_factor factor
    ) sep ((case cff of None \<Rightarrow> [] | Some cff \<Rightarrow> [Inl cff]) @ map Inr (Poly_Mapping.items mon))"

definition "shows_factor_compact factor =
  (case factor of (k, v) \<Rightarrow> shows_string ''x'' +@+ shows k +@+
    (if v = 1 then shows_string '''' else shows_string ''^'' +@+ shows v))"

definition "shows_factor_Var factor =
  (case factor of (k, v) \<Rightarrow> shows_string ''(Var '' +@+ shows k +@+ shows_string '')'' +@+
    (if v = 1 then shows_string '''' else shows_string ''^'' +@+ shows v))"

definition shows_monomial_compact::"('a \<Rightarrow> shows) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a option \<Rightarrow> shows" where
  "shows_monomial_compact shows_coeff m =
    shows_monomial_gen shows_factor_compact shows_coeff (shows_string '' '') m"

definition shows_monomial_Var::"('a \<Rightarrow> shows) \<Rightarrow> (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a option \<Rightarrow> shows" where
  "shows_monomial_Var shows_coeff m =
    shows_monomial_gen shows_factor_Var shows_coeff (shows_string ''*'') m"

fun shows_mpoly :: "bool \<Rightarrow> ('a \<Rightarrow> shows) \<Rightarrow> 'a::{zero,one} mpoly \<Rightarrow> shows" where
  "shows_mpoly input shows_coeff p = shows_sep (\<lambda>mon.
    (if input then shows_monomial_Var (\<lambda>x. shows_paren (shows_string ''Const '' +@+ shows_paren (shows_coeff x))) else shows_monomial_compact shows_coeff)
      mon
      (let cff = MPoly_Type.coeff p mon in if cff = 1 then None else Some cff)
  )
    (shows_string '' + '')
    (monomials_list p)"


definition "rat_of_real (x::real) =
  (if (\<exists>r::rat. x = of_rat r) then (THE r. x = of_rat r) else 99999999999.99999999999)"

lemma rat_of_real: "rat_of_real x = r" if "x = of_rat r"
  using that
  unfolding rat_of_real_def
  by simp

lemma rat_of_real_code[code]: "rat_of_real (Ratreal r) = r"
  by (simp add: rat_of_real)

definition "shows_real x = shows (rat_of_real x)"

experiment begin
abbreviation "foo \<equiv> ((Var 0::real mpoly) + Const (0.5) * Var 1 + Var 2)^3"
value [code] "shows_mpoly True shows_real foo ''''"
  (* rhs of foo\\_eq is the output of this \<open>value\<close> command *)
lemma foo_eq: "foo = (Var 0)^3 + (Const (3/2))*(Var 0)^2*(Var 1) + (Const (3))*(Var 0)^2*(Var 2) + (Const (3/4))*(Var 0)*(Var 1)^2 + (Const (3))*(Var 0)*(Var 1)*(Var 2) + (Const (3))*(Var 0)*(Var 2)^2 + (Const (1/8))*(Var 1)^3 + (Const (3/4))*(Var 1)^2*(Var 2) + (Const (3/2))*(Var 1)*(Var 2)^2 + (Var 2)^3"
  by code_simp
value [code] "shows_mpoly False shows_real foo ''''"
value [code] "shows_mpoly False (shows_paren o shows_mpoly False shows_real) (extract_var foo 0) ''''"
value [code] "shows_list_gen (shows_mpoly False shows_real)
  ''[]'' ''['' '', '' '']''
   (Polynomial.coeffs (mpoly_to_nested_poly foo 0)) ''''"
end

fun shows_atom :: "bool \<Rightarrow> atom \<Rightarrow> shows" where
  "shows_atom c (Eq p) = (shows_string ''('' +@+ shows_mpoly c shows_real p +@+ shows_string ''=0)'')"|
  "shows_atom c (Less p) = (shows_string ''('' +@+ shows_mpoly c shows_real p +@+ shows_string ''<0)'')"|
  "shows_atom c (Leq p) = (shows_string ''('' +@+ shows_mpoly c shows_real p +@+ shows_string ''<=0)'')"|
  "shows_atom c(Neq p) = (shows_string ''('' +@+ shows_mpoly c shows_real p +@+ shows_string ''~=0)'')"

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


function shows_fm :: "bool \<Rightarrow> atom fm \<Rightarrow> shows" where
  "shows_fm c (Atom a) = shows_atom c a"|
  "shows_fm c (TrueF) = shows_string ''(T)''"|
  "shows_fm c (FalseF) = shows_string ''(F)''"|
  "shows_fm c (And \<phi> \<psi>) = (shows_string ''('' +@+ shows_fm c \<phi> +@+ shows_string '' and '' +@+ shows_fm c \<psi> +@+ shows_string ('')''))"|
  "shows_fm c (Or \<phi> \<psi>) = (shows_string ''('' +@+ shows_fm c \<phi> +@+ shows_string '' or '' +@+ shows_fm c \<psi>  +@+ shows_string '')'')"|
  "shows_fm c (Neg \<phi>) = (shows_string ''(neg '' +@+ shows_fm c \<phi> +@+ shows_string '')'')"|
  "shows_fm c (ExQ \<phi>) = (shows_string ''(exists'' +@+ shows_fm c \<phi> +@+ shows_string '')'')"|
  "shows_fm c (AllQ \<phi>) = (shows_string ''(forall'' +@+ shows_fm c \<phi> +@+ shows_string '')'')"|
  "shows_fm c (ExN 0 \<phi>) = shows_fm c \<phi>"|
  "shows_fm c (ExN (Suc n) \<phi>) = shows_fm c (ExQ(ExN n \<phi>))"|
  "shows_fm c (AllN 0 \<phi>) = shows_fm c \<phi>"|
  "shows_fm c (AllN (Suc n) \<phi>) = shows_fm c (AllQ(AllN n \<phi>))"
  by pat_completeness auto
termination
  apply(relation "measures [\<lambda>(_,A). depth' A]")
  by auto


value "shows_fm False (ExQ (Or (AllQ(And (Neg TrueF) (Neg FalseF))) (Atom(Eq(Const 4))))) []"
value "shows_fm True (ExQ (Or (AllQ(And (Neg TrueF) (Neg FalseF))) (Atom(Eq(Const 4))))) []"

end