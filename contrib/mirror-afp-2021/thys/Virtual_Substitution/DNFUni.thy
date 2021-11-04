subsection "Overall General VS Proofs"
theory DNFUni
  imports QE InfinitesimalsUni
begin

fun DNFUni :: "atomUni fmUni \<Rightarrow> atomUni list list" where
  "DNFUni (AtomUni a) = [[a]]"|
  "DNFUni (TrueFUni) = [[]]" |
  "DNFUni (FalseFUni) = []"|
  "DNFUni (AndUni A B) = [A' @ B'. A' \<leftarrow> DNFUni A, B' \<leftarrow> DNFUni B]"|
  "DNFUni (OrUni A B) = DNFUni A @ DNFUni B"

lemma eval_DNFUni : "evalUni F x = evalUni (list_disj_Uni(map (list_conj_Uni o (map AtomUni)) (DNFUni F))) x"
proof(induction F)
  case TrueFUni
  then show ?case by auto
next
  case FalseFUni
  then show ?case by auto
next
  case (AtomUni x)
  then show ?case by auto
next
  case (AndUni F1 F2)
  show ?case unfolding DNFUni.simps eval_list_disj_Uni evalUni.simps AndUni List.map_concat List.set_concat apply simp
    unfolding eval_list_conj_Uni_append
    by blast
next
  case (OrUni F1 F2)
  then show ?case  unfolding DNFUni.simps List.map_append eval_list_disj_Uni List.set_append evalUni.simps
    by blast
qed

fun elimVarUni_atom :: "atomUni list \<Rightarrow> atomUni \<Rightarrow> atomUni fmUni" where
  "elimVarUni_atom F (EqUni (a,b,c)) =
(OrUni
  (AndUni 
    (AndUni (AtomUni (EqUni (0,0,a))) (AtomUni (NeqUni (0,0,b))))
      (list_conj_Uni (map (linearSubstitutionUni b c) F)))
    (AndUni (AtomUni (NeqUni (0,0,a))) (AndUni (AtomUni(LeqUni (0,0,-(b^2)+4*a*c)))
      (OrUni 
        (list_conj_Uni (map (quadraticSubUni (-b) 1 (b^2-4*a*c) (2*a)) F))
        (list_conj_Uni (map (quadraticSubUni (-b) (-1) (b^2-4*a*c) (2*a)) F))
      )
    )
  )
)
" |
  "elimVarUni_atom F (LeqUni (a,b,c)) =
(OrUni
  (AndUni 
    (AndUni (AtomUni (EqUni (0,0,a))) (AtomUni (NeqUni (0,0,b))))
      (list_conj_Uni (map (linearSubstitutionUni b c) F)))
    (AndUni (AtomUni (NeqUni (0,0,a))) (AndUni (AtomUni(LeqUni (0,0,-(b^2)+4*a*c)))
      (OrUni 
        (list_conj_Uni (map (quadraticSubUni (-b) 1 (b^2-4*a*c) (2*a)) F))
        (list_conj_Uni (map (quadraticSubUni (-b) (-1) (b^2-4*a*c) (2*a)) F))
      )
    )
  )
)
" |
  "elimVarUni_atom F (LessUni (a,b,c)) =
(OrUni
  (AndUni 
    (AndUni (AtomUni (EqUni (0,0,a))) (AtomUni (NeqUni (0,0,b))))
      (list_conj_Uni (map (substInfinitesimalLinearUni b c) F)))
    (AndUni (AtomUni (NeqUni (0,0,a))) (AndUni (AtomUni(LeqUni (0,0,-(b^2)+4*a*c)))
      (OrUni 
        (list_conj_Uni (map(substInfinitesimalQuadraticUni (-b) 1 (b^2-4*a*c) (2*a)) F))
        (list_conj_Uni (map(substInfinitesimalQuadraticUni (-b) (-1) (b^2-4*a*c) (2*a)) F))
      )
    )
  )
)
"|
  "elimVarUni_atom F (NeqUni (a,b,c)) =
(OrUni
  (AndUni 
    (AndUni (AtomUni (EqUni (0,0,a))) (AtomUni (NeqUni (0,0,b))))
      (list_conj_Uni (map (substInfinitesimalLinearUni b c) F)))
    (AndUni (AtomUni (NeqUni (0,0,a))) (AndUni (AtomUni(LeqUni (0,0,-(b^2)+4*a*c)))
      (OrUni 
        (list_conj_Uni (map(substInfinitesimalQuadraticUni (-b) 1 (b^2-4*a*c) (2*a)) F))
        (list_conj_Uni (map(substInfinitesimalQuadraticUni (-b) (-1) (b^2-4*a*c) (2*a)) F))
      )
    )
  )
)
"




fun generalVS_DNF :: "atomUni list \<Rightarrow> atomUni fmUni" where
  "generalVS_DNF L  = list_disj_Uni (list_conj_Uni(map substNegInfinityUni L) # (map (\<lambda>A. elimVarUni_atom L A) L))"



end