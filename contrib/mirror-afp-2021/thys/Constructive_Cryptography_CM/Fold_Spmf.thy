theory Fold_Spmf
  imports
    More_CC
begin

primrec (transfer) 
  foldl_spmf :: "('b \<Rightarrow> 'a \<Rightarrow> 'b spmf) \<Rightarrow> 'b spmf \<Rightarrow> 'a list \<Rightarrow> 'b spmf" 
  where
    foldl_spmf_Nil: "foldl_spmf f p [] = p"
  | foldl_spmf_Cons: "foldl_spmf f p (x # xs) = foldl_spmf f (bind_spmf p (\<lambda>a. f a x)) xs"

lemma foldl_spmf_return_pmf_None [simp]:
  "foldl_spmf f (return_pmf None) xs = return_pmf None"
  by(induction xs) simp_all

lemma foldl_spmf_bind_spmf: "foldl_spmf f (bind_spmf p g) xs = bind_spmf p (\<lambda>a. foldl_spmf f (g a) xs)"
  by(induction xs arbitrary: g) simp_all

lemma bind_foldl_spmf_return:
  "bind_spmf p (\<lambda>x. foldl_spmf f (return_spmf x) xs) = foldl_spmf f p xs"
  by(simp add: foldl_spmf_bind_spmf[symmetric])

lemma foldl_spmf_map [simp]: "foldl_spmf f p (map g xs) = foldl_spmf (map_fun id (map_fun g id) f) p xs"
  by(induction xs arbitrary: p) simp_all


lemma foldl_spmf_identity [simp]: "foldl_spmf (\<lambda>s x. return_spmf s) p xs = p"
  by(induction xs arbitrary: p) simp_all

lemma foldl_spmf_conv_foldl:
  "foldl_spmf (\<lambda>s x. return_spmf (f s x)) p xs = map_spmf (\<lambda>s. foldl f s xs) p"
  by(induction xs arbitrary: p)(simp_all add: map_spmf_conv_bind_spmf[symmetric] spmf.map_comp o_def)

lemma foldl_spmf_Cons':
  "foldl_spmf f (return_spmf a) (x # xs) = bind_spmf (f a x) (\<lambda>a'. foldl_spmf f (return_spmf a') xs)"
  by(simp add: bind_foldl_spmf_return)

lemma foldl_spmf_append: "foldl_spmf f p (xs @ ys) = foldl_spmf f (foldl_spmf f p xs) ys"
  by(induction xs arbitrary: p) simp_all

lemma 
  foldl_spmf_helper:
  assumes "\<And>x. h (f x) = x"
  assumes "\<And>x. f (h x) = x"
  shows "foldl_spmf (\<lambda>a e. map_spmf h (g (f a) e)) acc es = 
    map_spmf h (foldl_spmf g (map_spmf f acc) es)" 
  using assms proof (induction es arbitrary: acc)
  case (Cons a es)
  then show ?case 
    by (simp add: spmf.map_comp map_bind_spmf bind_map_spmf o_def)
qed (simp add: map_spmf_conv_bind_spmf)

lemma 
  foldl_spmf_helper2:
  assumes "\<And>x y. p (f x y) = x"
  assumes "\<And>x y. q (f x y) = y"
  assumes "\<And>x. f (p x) (q x) = x"
  shows "foldl_spmf (\<lambda>a e. map_spmf (f (p a)) (g (q a) e)) acc es = 
    bind_spmf acc (\<lambda>acc'. map_spmf (f (p acc')) (foldl_spmf g (return_spmf (q acc')) es))" 
  proof (induction es arbitrary: acc)
    note [simp] = spmf.map_comp map_bind_spmf bind_map_spmf o_def
  case (Cons e es)
  then show ?case
    apply (simp add: map_spmf_conv_bind_spmf assms)
    apply (subst bind_spmf_assoc[symmetric])
    by (simp add: bind_foldl_spmf_return)
qed (simp add: assms(3))

lemma foldl_pair_constl: "foldl (\<lambda>s e. map_prod (\<lambda>_. c) (\<lambda>r. f r e) s) (c, sr) l = 
    Pair c (foldl (\<lambda>s e. f s e) sr l)"
  by (induction l arbitrary: sr) (auto simp add: map_prod_def split_def)

lemma foldl_spmf_pair_left:
  "foldl_spmf (\<lambda>(l, r) e. map_spmf (\<lambda>l'. (l', r)) (f l e)) (return_spmf (l, r)) es = 
    map_spmf (\<lambda>l'. (l', r)) (foldl_spmf f (return_spmf l) es)"
  apply (induction es arbitrary: l)
   apply simp_all
  apply (subst (2) map_spmf_conv_bind_spmf)
  apply (subst foldl_spmf_bind_spmf)
  apply (subst (2) bind_foldl_spmf_return[symmetric])
  by (simp add: map_spmf_conv_bind_spmf)

lemma foldl_spmf_pair_left2:
  "foldl_spmf (\<lambda>(l, _) e. map_spmf (\<lambda>l'. (l', c')) (f l e)) (return_spmf (l, c)) es = 
    map_spmf (\<lambda>l'. (l', if es = [] then c else c')) (foldl_spmf f (return_spmf l) es)"
  apply (induction es arbitrary: l c c')
   apply simp_all
  apply (subst (2) map_spmf_conv_bind_spmf)
  apply (subst foldl_spmf_bind_spmf)
  apply (subst (2) bind_foldl_spmf_return[symmetric])
  by (simp add: map_spmf_conv_bind_spmf)

lemma foldl_pair_constr: "foldl (\<lambda>s e. map_prod (\<lambda>l. f l e) (\<lambda>_. c) s) (sl, c) l = 
   Pair (foldl (\<lambda>s e. f s e) sl l) c"
  by (induction l arbitrary: sl) (auto simp add: map_prod_def split_def)

lemma foldl_spmf_pair_right:
  "foldl_spmf (\<lambda>(l, r) e. map_spmf (\<lambda>r'. (l, r')) (f r e)) (return_spmf (l, r)) es = 
    map_spmf (\<lambda>r'. (l, r')) (foldl_spmf f (return_spmf r) es)"
  apply (induction es arbitrary: r)
   apply simp_all
  apply (subst (2) map_spmf_conv_bind_spmf)
  apply (subst foldl_spmf_bind_spmf)
  apply (subst (2) bind_foldl_spmf_return[symmetric])
  by (simp add: map_spmf_conv_bind_spmf)

lemma foldl_spmf_pair_right2:
  "foldl_spmf (\<lambda>(_, r) e. map_spmf (\<lambda>r'. (c', r')) (f r e)) (return_spmf (c, r)) es = 
    map_spmf (\<lambda>r'. (if es = [] then c else c', r')) (foldl_spmf f (return_spmf r) es)"
  apply (induction es arbitrary: r c c')
   apply simp_all
  apply (subst (2) map_spmf_conv_bind_spmf)
  apply (subst foldl_spmf_bind_spmf)
  apply (subst (2) bind_foldl_spmf_return[symmetric])
  by (auto simp add: map_spmf_conv_bind_spmf split_def)

lemma foldl_spmf_pair_right3:
  "foldl_spmf (\<lambda>(l, r) e. map_spmf (Pair (g e)) (f r e)) (return_spmf (l, r)) es = 
    map_spmf (Pair (if es = [] then l else g (last es))) (foldl_spmf f (return_spmf r) es)"
  apply (induction es arbitrary: r l)
   apply simp_all
  apply (subst (2) map_spmf_conv_bind_spmf)
  apply (subst foldl_spmf_bind_spmf)
  apply (subst (2) bind_foldl_spmf_return[symmetric])
  by (clarsimp simp add: split_def map_bind_spmf o_def)

lemma foldl_pullout: "bind_spmf f (\<lambda>x. bind_spmf (foldl_spmf g init (events x)) (\<lambda>y. h x y)) = 
    bind_spmf (bind_spmf f (\<lambda>x. foldl_spmf (\<lambda>(l, r) e. map_spmf (Pair l) (g r e)) (map_spmf (Pair x) init) (events x)))
     (\<lambda>(x, y). h x y)" for f g h init events
    apply (simp add: foldl_spmf_helper2[where f=Pair and p=fst and q=snd, simplified] split_def)
    apply (clarsimp simp add: map_spmf_conv_bind_spmf)
  by (subst bind_spmf_assoc[symmetric]) (auto simp add: bind_foldl_spmf_return)
  
lemma bind_foldl_spmf_pair_append: "
  bind_spmf
    (foldl_spmf (\<lambda>(x, y) e. map_spmf (apfst ((@) x)) (f y e)) (return_spmf (a @ c, b)) es)
    (\<lambda>(x, y). g x y) =
  bind_spmf
    (foldl_spmf (\<lambda>(x, y) e. map_spmf (apfst ((@) x)) (f y e)) (return_spmf (c, b)) es)
    (\<lambda>(x, y). g (a @ x) y)"
  apply (induction es arbitrary: c b)
   apply (simp_all add: split_def map_spmf_conv_bind_spmf apfst_def map_prod_def)
  apply (subst (1 2) foldl_spmf_bind_spmf)
  by simp

lemma foldl_spmf_chain: "
(foldl_spmf (\<lambda>(oevents, s_event) event. map_spmf (map_prod ((@) oevents) id) (fff s_event event)) (return_spmf ([], s_event)) ievents) 
  \<bind> (\<lambda>(oevents, s_event'). foldl_spmf ggg (return_spmf s_core) oevents 
        \<bind> (\<lambda>s_core'. return_spmf (f s_core' s_event'))) =
foldl_spmf (\<lambda>(s_event, s_core) event. fff s_event event \<bind>  (\<lambda>(oevents, s_event').
      map_spmf (Pair s_event') (foldl_spmf ggg (return_spmf s_core) oevents))) (return_spmf (s_event, s_core)) ievents
  \<bind> (\<lambda>(s_event', s_core'). return_spmf (f s_core' s_event'))"
proof (induction ievents arbitrary: s_event s_core)
  case Nil
  show ?case by simp
next
  case (Cons e es)

  show ?case 
    apply (subst (1 2) foldl_spmf_Cons')
    apply (simp add: split_def)
    apply (subst map_spmf_conv_bind_spmf)
    apply simp
    apply (rule bind_spmf_cong[OF refl])
    apply (subst (2) map_spmf_conv_bind_spmf)
    apply simp
    apply (subst Cons.IH[symmetric, simplified split_def])
    apply (subst bind_commute_spmf)
    apply (subst (2) map_spmf_conv_bind_spmf[symmetric])
    apply (subst map_bind_spmf[symmetric, simplified o_def])
    apply (subst (1) foldl_spmf_bind_spmf[symmetric])
    apply (subst (3) map_spmf_conv_bind_spmf)
    apply (simp add: foldl_spmf_append[symmetric] map_prod_def split_def)
    subgoal for x
      apply (cases x)
      subgoal for a b
        apply (simp add: split_def)
        apply (subst bind_foldl_spmf_pair_append[where c="[]" and a=a and b=b and es=es, simplified apfst_def map_prod_def append_Nil2 split_def id_def])
        by simp
      done
    done
qed


\<comment> \<open>pauses\<close>
primrec pauses :: "'a list \<Rightarrow> (unit, 'a, 'b) gpv" where
  "pauses [] = Done ()"
| "pauses (x # xs) = Pause x (\<lambda>_. pauses xs)"

lemma WT_gpv_pauses [WT_intro]:
  "\<I> \<turnstile>g pauses xs \<surd>" if "set xs \<subseteq> outs_\<I> \<I>"
  using that by(induction xs) auto

lemma exec_gpv_pauses:
  "exec_gpv callee (pauses xs) s =
   map_spmf (Pair ()) (foldl_spmf (map_fun id (map_fun id (map_spmf snd)) callee) (return_spmf s) xs)"
  by(induction xs arbitrary: s)(simp_all add: split_def foldl_spmf_Cons' map_bind_spmf bind_map_spmf o_def del: foldl_spmf_Cons)


end