section {* Terminated lists *}

theory Terminated_lists
imports
  Main
  Monoid_extra
begin

text {* Finite terminated lists are lists where the Nil element 
        can record some information.*}

subsection {* Generic terminated lists datatype *}

datatype ('\<alpha>,'\<theta>) gtlist = Nil "'\<alpha>" ("[;;(_)]") | Cons "'\<theta>" "('\<alpha>,'\<theta>) gtlist" (infixr "#\<^sub>g\<^sub>t" 65) 
  
syntax
  "_gtlist"     :: "args \<Rightarrow> 'a \<Rightarrow> ('\<alpha>,'\<theta>) gtlist"    ("[(_);;(_)]")

translations
  "[x,xs;;y]" == "(x#\<^sub>g\<^sub>t[xs;;y])"
  "[x;;y]" == "x#\<^sub>g\<^sub>t[;;y]"
  
value "[a,b,c;;e]"
value "[;;e]"
  
text {* If we take '\<alpha> to be the unit type, then we have a traditional
        list where the Nil element does not record anything else. *}

type_synonym '\<theta> unit_ttlist1 = "(unit,'\<theta>) gtlist"
  
primrec ttlist1_list2list :: "'\<theta> unit_ttlist1 \<Rightarrow> '\<theta> list" where
"ttlist1_list2list (Nil s) = []" |
"ttlist1_list2list (Cons x xs) = x#(ttlist1_list2list xs)"

primrec list2ttlist1_list :: "'\<theta> list \<Rightarrow> '\<theta> unit_ttlist1" where
"list2ttlist1_list [] = (Nil ())" |
"list2ttlist1_list (x#xs) = (Cons x (list2ttlist1_list xs))"

lemma "list2ttlist1_list (ttlist1_list2list sl) = sl"
  by (induct sl, auto)
  
lemma "ttlist1_list2list (list2ttlist1_list sl) = sl"
  by (induct sl, auto)
    
text {* If we wanted to show that given a plus operator between
        '\<alpha> => '\<theta> yielding '\<theta>, we would need some kind of locale
        here, and would need a function ('\<alpha> => '\<theta> => '\<theta>) to be
        able to define plus in a generic way. *}

subsection {* Standard terminated lists *}
  
datatype '\<alpha> stlist = Nil "'\<alpha>" ("[;(_)]") | Cons "'\<alpha>" "'\<alpha> stlist" (infixr "#\<^sub>t" 65)  
  
syntax
  "_stlist"     :: "args \<Rightarrow> 'a \<Rightarrow> '\<alpha> stlist"    ("[(_); (_)]")

translations
  "[x,xs;y]" == "(x#\<^sub>t[xs;y])"
  "[x;y]" == "x#\<^sub>t[;y]"

value "[a,b,c;e]"
value "[;e]"
  
text {* We can then show that a list is a special
        case of this structure by defining a pair of functions. *}

primrec stlist2list :: "'\<theta> stlist \<Rightarrow> '\<theta> list" where
"stlist2list [;s] = []" |
"stlist2list (x#\<^sub>txs) = x#(stlist2list xs)"  

primrec list2stlist :: "'\<theta> \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> stlist" where
"list2stlist a [] = [;a]" |
"list2stlist a (x#xs) = (Cons x (list2stlist a xs))"
  
lemma "stlist2list (list2stlist z sl) = sl"
  by (induct sl, auto)

text {* And given a stlist with a predefined zero representation,
        we get the same back. *}
    
lemma "list2stlist z (stlist2list (sl#\<^sub>t[;z])) = (sl#\<^sub>t[;z])"
  by (auto)
  
primrec seq2_Nlist2list :: "'\<theta> stlist \<Rightarrow> '\<theta> list" where
"seq2_Nlist2list [;s] = [s]" |
"seq2_Nlist2list (x#\<^sub>txs) = x#(seq2_Nlist2list xs)"

primrec Nlist2seq2_list :: "'\<theta> list \<Rightarrow> '\<theta> stlist" where
"Nlist2seq2_list [] = [;undefined]" |
"Nlist2seq2_list (x#xs) = (if xs = [] then [;x] else (x#\<^sub>t(Nlist2seq2_list xs)))"

lemma "Nlist2seq2_list (seq2_Nlist2list sl) = sl"
  apply (induct sl)
  by (auto)
  
lemma 
  assumes "length sl > 0" 
  shows "seq2_Nlist2list (Nlist2seq2_list sl) = sl"
  using assms
  apply (induct sl)
  by auto
    
subsection {* Auxiliary induction rules *}
  
lemma stlist_induct_cons: 
  "\<lbrakk>
   \<And>a b.  P [;a] [;b];
   \<And>a x xs. P (x#\<^sub>txs) [;a] ;
   \<And>a y ys. P [;a] (y#\<^sub>tys);
   \<And>x xs y ys. P xs ys  \<Longrightarrow> P (x#\<^sub>txs) (y#\<^sub>tys) \<rbrakk>
 \<Longrightarrow> P xs ys"
  apply (induct xs arbitrary: ys)
  apply auto
  apply (case_tac "xa")
  apply auto
  apply (case_tac "x")
  by auto

subsection {* Operators *}
  
text {* We define a concatenation operator (plus) based on the plus of the
        parametrised type being used. *}  
  
fun concat_stlist :: "('a::plus) stlist \<Rightarrow> ('a::plus) stlist \<Rightarrow> ('a::plus) stlist" (infixl "@\<^sub>t" 66)
where
"[;z] @\<^sub>t [;x] = [;z+x]" |
"[;z] @\<^sub>t (x#\<^sub>txs) = (z+x)#\<^sub>txs" |
"(x#\<^sub>txs) @\<^sub>t zs = x#\<^sub>t(xs@\<^sub>tzs)"

text {* We define a last function *}
  
primrec last :: "'a stlist \<Rightarrow> 'a" where
"last [;x] = x" |
"last (x#\<^sub>txs) = last xs"

subsection {* Classes *}

subsubsection {* Plus *}  
  
text {* We now instantiate the plus operator for the stlist type. *}
  
instantiation stlist :: (plus) plus
begin

  definition plus_stlist :: "'a stlist \<Rightarrow> 'a stlist \<Rightarrow> 'a stlist"
    where "plus_stlist == concat_stlist"
  
  instance by (intro_classes)
end
  
lemma plus_seq_assoc: 
  fixes xs ys zs::"'a::{plus,semigroup_add} stlist"
  shows "(xs + ys) + zs = xs + (ys + zs)"
  unfolding plus_stlist_def
  apply (induct xs)
  apply (induct ys)
  apply (induct zs)
  apply auto
  apply (simp add: add.assoc)
  by (simp add:add.semigroup_axioms semigroup.assoc)  
  
lemma stlist_nil_concat_cons:
  shows "[;a] + (xs#\<^sub>tys) = (a + xs)#\<^sub>tys" 
  by (simp add:plus_stlist_def)

lemma stlist_not_cons: "d \<noteq> x#\<^sub>td"
  by (metis add_cancel_left_right lessI less_imp_not_eq2 stlist.size(4))
    
lemma stlist_concat_not_eq: "(b#\<^sub>t[;d])+a \<noteq> [;c]+a"
  unfolding plus_stlist_def
  apply (induct a rule:stlist.induct)
  apply simp_all
  by (metis stlist_not_cons)
    
lemma stlist_concat_not_eq2: "(b#\<^sub>t[d;e])+a \<noteq> [;c]+a"
  unfolding plus_stlist_def
  apply (induct a rule:stlist.induct)
  apply simp_all
  by (metis add_le_same_cancel1 lessI not_less stlist.size(4) trace_class.le_add)
    
lemma stlist_concat_noteq: "x1a #\<^sub>t x2 \<noteq> x2"
  apply (induct x2)
  by auto
    
lemma stlist_concat_noteq2: "(b #\<^sub>t x2) + a \<noteq> (b #\<^sub>t x1a #\<^sub>t x2) + a"
  by (simp add: plus_stlist_def stlist_not_cons)
    
lemma stlist_last_concat:
  fixes s z :: "'a::plus stlist"
  shows "last (s + (x#\<^sub>tz)) = last z"
  unfolding plus_stlist_def
  apply (induct s)
  by auto
    
lemma stlist_last_concat2:
  fixes s :: "'a::plus stlist"
  shows "last (x#\<^sub>t(s + [;z])) = last s + z"
  unfolding plus_stlist_def
  apply (induct s)
  by auto
    
lemma stlist_last_concat3:
  fixes s :: "'a::plus stlist"
  shows "last ((x#\<^sub>ts) + [;z]) = last s + z"
  unfolding plus_stlist_def
  apply (induct s)
  by auto    
    
lemma stlist_eq_nil_pluses_imp0:
  shows "[;a] = [;c] + e \<Longrightarrow> \<exists>z. e = [;z]"
  apply (induct e)
  apply auto
  by (simp add: stlist_nil_concat_cons)
    
lemma stlist_eq_nil:
  shows "a = b \<longleftrightarrow> [;a] = [;b]"
  by simp
    
lemma stlist_plus_nils:
  fixes a b :: "'a::plus"
  shows "a + b = c \<longleftrightarrow> [;a] + [;b] = [;c]"
  by (simp add: plus_stlist_def)
     
lemma stlist_eqnils_plus_zero_cons_imp:
  fixes a :: "'a::monoid_add"
  shows "[;a] + (0 #\<^sub>t xs) = [;c] + (0 #\<^sub>t ys) \<Longrightarrow> [;a] + xs = [;c] + ys"
  by (simp add: stlist_nil_concat_cons)
    
lemma stlist_eq_nil_iff_cons_eq1:
  assumes "xs = ys"
  shows "[;a] = [;b] \<longleftrightarrow> (a#xs) = (b#ys)"
  using assms by blast
    
lemma stlist_eq_nil_iff_cons_eq2:
  assumes "xs = ys"
  shows "a = b \<longleftrightarrow> (a#xs) = (b#ys)"
  using assms by blast
    
subsubsection {* Additive monoid *}
  
text {* Given a monoid_add class we also have a monoid_add. On top of
        plus we define the zero as the parametrised type zero. *}
  
instantiation stlist :: (zero) zero
begin
  definition zero_stlist :: "'a stlist" where "zero_stlist = [;0]" 
  
  lemma stlist_zero_is_zero:
  shows "[;0] = 0"
  by (simp add:zero_stlist_def)

  instance by intro_classes
end
  
instantiation stlist :: (monoid_add) monoid_add
begin
  
subsubsection {* Lemmas on monoid_add with stlist *}
    
lemma stlist_concat_zero_left[simp]: 
  fixes y::"'a stlist"
  shows "[;0] + y = y"
  unfolding plus_stlist_def
  by (induct y, auto)

   
lemma stlist_concat_zero_right[simp]: 
  fixes y::"'a stlist"
  shows "y + [;0] = y"
  unfolding plus_stlist_def
  by (induct y, auto)
    
instance
  apply (intro_classes)
  by (auto simp:plus_seq_assoc zero_stlist_def)
end

text {* Given an additive monoid type, we can define a front function
        that yields front(s) + last(s) for a given stlist s *}
    
primrec front :: "'a::fzero_add_zero stlist \<Rightarrow> 'a stlist" where
"front [;x] = [;fzero x]" |
"front (x#\<^sub>txs) = (x#\<^sub>tfront xs)"

primrec tail :: "'a::fzero_add_zero stlist \<Rightarrow> 'a stlist" where
"tail [;x] = [;fzero x]" |
"tail (x#\<^sub>txs) = (fzero x#\<^sub>txs)"

primrec head :: "'a::fzero_add_zero stlist \<Rightarrow> 'a" where
"head [;x] = x" |
"head (x#\<^sub>txs) = x"

value "front [a;b]"

lemma stlist_front_concat_last: "s = front(s) + [;last(s)]"
  unfolding plus_stlist_def
  apply (induct s)
  by auto

lemma 
  assumes "x \<noteq> []"
  shows "x = [hd x] + (tl x)"
  using assms
  by (simp add: plus_list_def)

lemma stlist_head_concat_tail: 
  "s = [;head(s)] + tail(s)"
  apply (induct s)
   apply auto
   apply (simp add: plus_stlist_def)
  by (simp add: stlist_nil_concat_cons)
    
lemma stlist_cons_plus_nil_front_last:
  shows "(x #\<^sub>t xs) + [;b] = (x #\<^sub>t front(xs)) + [;last(xs) + b]"
  by (metis (no_types, lifting) concat_stlist.simps(3) plus_seq_assoc plus_stlist_def stlist_front_concat_last stlist_plus_nils)
  
lemma stlist_cons_plus_nils:
  shows "(x #\<^sub>t xs) + [;b] = (y #\<^sub>t ys) + [;d] \<longleftrightarrow> x = y \<and> (xs + [;b] = ys + [;d])"
  by (simp add: plus_stlist_def)
    
lemma stlist_cons_plus_nils_eq_cons:
  shows "[;e] + (x #\<^sub>t xs) = (y #\<^sub>t ys) \<longleftrightarrow> e + x = y \<and> xs = ys"
  by (simp add: stlist_nil_concat_cons)
    
lemma stlist_plus_cons_eq_front_plus:
  shows "e + (x #\<^sub>t xs) = front(e) + ((last(e) + x) #\<^sub>t xs)"
  by (metis plus_seq_assoc stlist_cons_plus_nils_eq_cons stlist_front_concat_last)
    
subsubsection {* Orders *}
  

text {* We now instantiate the ord class for the stlist type. *}

instance stlist :: (semigroup_add) semigroup_add
  apply intro_classes
  by (metis (no_types, lifting) plus_seq_assoc)
  
instantiation stlist :: (semigroup_add) ord
begin
  definition less_eq_stlist :: "'a stlist \<Rightarrow> 'a stlist \<Rightarrow> bool" where "less_eq_stlist == fzero_le"
  definition less_stlist :: "'a stlist \<Rightarrow> 'a stlist \<Rightarrow> bool" where "less_stlist x y == x \<le> y \<and> \<not> (y \<le> x)"
(*
  lemma stlist_plus_follow_concat:
  fixes a c :: "'a stlist"
  shows "a + (b #\<^sub>t c) = a + [b;0] + c"
  by (metis concat_stlist.simps(3) plus_seq_assoc plus_stlist_def stlist_concat_zero_left)  
 *)   
  instance by (intro_classes)
end
  (*
lemma monoid_le_stlist2:
  "(xs :: 'a::monoid_add stlist) \<le>\<^sub>m ys \<longleftrightarrow> xs \<le> ys"
  by (simp add: less_eq_stlist_def)

  *)
lemma stlist_right_cancel_monoid2:
  "(b#\<^sub>ta) = (c#\<^sub>ta) \<longleftrightarrow> b = c"  
  by auto
    
subsubsection {* Left Cancelative Semigroup *}
  
text {* We now instantiate the left_cancel_monoid class for the stlist type. *}

instantiation stlist :: (left_cancel_semigroup) left_cancel_semigroup
begin
  
lemma stlist_left_zero_cancel:
  fixes a :: "'a stlist"
  shows "a + [;b] = a + [;c] \<Longrightarrow> [;b] = [;c]"
  unfolding plus_stlist_def
  apply (induct a)
  apply auto
  using left_cancel_semigroup_class.add_left_imp_eq by blast
   
lemma stlist_left_cancel_monoid0:
  fixes b c :: "'a stlist"
  shows "[;a] + b = [;a] + c \<Longrightarrow> b = c"
  unfolding plus_stlist_def
  apply (induct rule:stlist_induct_cons)
  apply auto
  using left_cancel_semigroup_class.add_left_imp_eq by blast+
    
lemma stlist_left_cancel_monoid:
  fixes a b c :: "'a stlist"
  shows "a + b = a + c \<Longrightarrow> b = c"
  apply (induct a rule:stlist.induct)
  using Terminated_lists.stlist_left_cancel_monoid0 apply blast
  by (simp add: plus_stlist_def)

instance apply (intro_classes)
  using stlist_left_cancel_monoid by blast+
end
  
instantiation stlist :: (left_cancel_monoid) left_cancel_monoid
begin
  instance by (intro_classes)
end
  
subsubsection {* Right Cancelative Monoid *}
  
text {* We now instantiate the right_cancel_monoid class for the stlist type. *}  
  
instantiation stlist :: (right_cancel_monoid) right_cancel_monoid
begin

lemma stlist_right_cancel_monoid0:
  fixes b c :: "'a stlist"
  shows "(b + [;a] = c + [;a]) \<Longrightarrow> b = c"
  unfolding plus_stlist_def
  apply (induct b c rule:stlist_induct_cons, auto)
  using right_cancel_semigroup_class.add_right_imp_eq by blast
    
lemma stlist_right_cancel_monoid1:
  fixes b c :: "'a stlist"
  shows "(b + [a;d] = c + [a;d]) \<Longrightarrow> b = c"
  unfolding plus_stlist_def
  apply (induct b c rule:stlist_induct_cons, auto)
  using right_cancel_semigroup_class.add_right_imp_eq apply blast
  apply (case_tac "xs", simp+)
  by (case_tac "ys", simp+)
    
lemma eqs: "x = y \<longleftrightarrow> (x #\<^sub>t xs) = (y #\<^sub>t xs)"
  by auto
    
lemma stlist_right_cancel_monoid:
  fixes b c :: "'a stlist"
  shows "b+a = c+a \<Longrightarrow> b = c"
  apply (induct a arbitrary: b c rule:stlist.induct)
  using stlist_right_cancel_monoid0 apply blast
  by (metis (no_types, lifting) add.assoc concat_stlist.simps(3) plus_stlist_def stlist_concat_zero_left stlist_right_cancel_monoid1 zero_stlist_def)

instance by (intro_classes, simp add:stlist_right_cancel_monoid)
end
  
subsubsection {* Monoid Sum *}    
  
instantiation stlist :: (monoid_sum_0) monoid_sum_0
begin
    
lemma stlist_zero_monoid_sum:
  fixes a :: "'a stlist"
  shows "a + b = 0 \<Longrightarrow> a = 0"
  apply (induct a b rule:stlist_induct_cons)
  by (simp add: plus_stlist_def zero_stlist_def zero_sum_left)+ 
    
instance
  apply (intro_classes)
  using  stlist_zero_monoid_sum  by blast+
end

subsubsection {* Difference *}
 
instance stlist :: (semigroup_add) semigroup_add_fzero
  by intro_classes
    
instantiation stlist :: (semigroup_add) minus
begin
  definition minus_stlist :: "'a stlist \<Rightarrow> 'a stlist \<Rightarrow> 'a stlist" where "minus_stlist == fzero_subtract"
  
  instance by intro_classes
end
  
subsubsection {* Pre trace *}

instantiation stlist :: (pre_trace) pre_trace
begin
  
lemma stlist_eq_sum_conv_nils:
  fixes a :: "'a::pre_trace"
  assumes "[;a] + [;b] = [;c] + [;d]"
  shows "\<exists> e . [;a] = [;c] + e \<and> e + [;b] = [;d] \<or> [;a] + e = [;c] \<and> [;b] = e + [;d]"
proof -
 
  have a: "([;a] + [;b] = [;c] + [;d]) = (a + b = c + d)"
    by (metis stlist_plus_nils)
      
  have b: "(a + b = c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"
    by (simp add: pre_trace_class.sum_eq_sum_conv)
  
  then have "(a + b = c + d) \<Longrightarrow> \<exists> e . [;a] = [;c] + e \<and> e + [;b] = [;d] \<or> [;a] + e = [;c] \<and> [;b] = e + [;d]"   
    by (metis stlist_plus_nils)
    
  with a b show ?thesis using assms by simp
qed
  
lemma stlist_eq_sum_conv_nils1:
  fixes a :: "'a::pre_trace stlist"
  assumes "a + [;b] = c + [;d]"
  shows "\<exists> e . a = c + e \<and> e + [;b] = [;d] \<or> a + e = c \<and> [;b] = e + [;d]"
  using assms
  apply (induct a c rule:stlist_induct_cons)
  apply (simp add: stlist_eq_sum_conv_nils)
  by (simp_all add: plus_stlist_def)
    
text {* The next lemma is key to prove the required induction
        in the following lemma stlist_sum_eq_sum_conv. *}
    
lemma stlist_eq_sum_conv_nils2:
  fixes a :: "'a::pre_trace"
  assumes "[;a] + b = [;c] + d"
  shows "\<exists> e . [;a] = [;c] + e \<and> e + b = d \<or> [;a] + e = [;c] \<and> b = e + d"
  using assms
  proof (induct b d arbitrary: a c rule:stlist_induct_cons)
    case (1 a b)
    then show ?case by (simp add: stlist_eq_sum_conv_nils)
  next
    case (2 a x xs)
    then show ?case by (simp add: plus_stlist_def)
  next
    case (3 a y ys)
    then show ?case by (simp add: plus_stlist_def)
  next
    case (4 x xs y ys)
    have a:"([;a] + (x #\<^sub>t xs) = [;c] + (y #\<^sub>t ys))
         =
         (((a + x) #\<^sub>t xs) = ((c + y) #\<^sub>t ys))"
      by (simp add: stlist_nil_concat_cons)
    
    hence eq1:"a + x = c + y"
      using "4.prems" by blast
      
    hence eq2:"xs=ys"
      using "4.prems" a by blast
    
    from eq1 have "\<exists>e. a = c + e \<and> e + x = y \<or> a + e = c \<and> x = e + y"
      by (simp add: pre_trace_class.sum_eq_sum_conv)
        
    then have "\<exists>e. [;a] = [;c] + e \<and> e + [;x] = [;y] \<or> [;a] + e = [;c] \<and> [;x] = e + [;y]"
      by (metis stlist_plus_nils)
        
    hence "\<exists>e z. [;z] = e \<and> ([;a] = [;c] + e \<and> e + [;x] = [;y] \<or> [;a] + e = [;c] \<and> [;x] = e + [;y])"
      by (metis stlist_eq_nil_pluses_imp0)
    
    hence "\<exists>e z. [;z] = e \<and> ([;a] = [;c] + e \<and> [;z] + (x#\<^sub>txs) = (y#\<^sub>tys) \<or> [;a] + e = [;c] \<and> [;x] = [;z + y])"    
      using eq2 by (metis (no_types, lifting) "4.prems" concat_stlist.simps(1) plus_seq_assoc plus_stlist_def stlist_left_cancel_monoid0) 
    
    hence "\<exists>e z. [;z] = e \<and> ([;a] = [;c] + e \<and> [;z] + (x#\<^sub>txs) = (y#\<^sub>tys) \<or> [;a] + e = [;c] \<and> (x#\<^sub>txs) = [;z] + (y#\<^sub>tys))"
      using eq2 by (metis (no_types, lifting) "4.prems" concat_stlist.simps(1) plus_seq_assoc plus_stlist_def stlist_left_cancel_monoid0) 
    
    hence eq3:"\<exists>e. [;a] = [;c] + e \<and> e + (x#\<^sub>txs) = (y#\<^sub>tys) \<or> [;a] + e = [;c] \<and> (x#\<^sub>txs) = e + (y#\<^sub>tys)"
      by auto
        
    then show ?case by auto   
qed
  
lemma stlist_sum_eq_sum_conv:
  fixes a :: "'a stlist"
  shows "(a + b) = (c + d) \<Longrightarrow> \<exists> e . a = c + e \<and> e + b = d \<or> a + e = c \<and> b = e + d"  
  apply (induct a c rule:stlist_induct_cons)
  apply (simp add:stlist_eq_sum_conv_nils2)+ 
  apply (case_tac d)
  apply (simp add: plus_stlist_def)
  apply (metis concat_stlist.simps(3) plus_stlist_def stlist_cons_plus_nils_eq_cons)
  apply (case_tac b)
  apply (simp add: plus_stlist_def)
  apply (metis concat_stlist.simps(3) plus_stlist_def stlist_cons_plus_nils_eq_cons)
  by (simp add: plus_stlist_def)  
  
instance by (intro_classes, simp add:stlist_sum_eq_sum_conv)
end

subsubsection {* Trace *} 
  
text {* Given a type of class pre_trace we get a trace. This means that
        for a given type, as long as we define an appropriate zero, and
        plus operator, and it obeys the required monoid laws in addition
        to sum_eq_sum_conv, then the resulting stlist is a trace. *}

  class fzero_add_zero_0 = fzero_add_zero + fzero_is_0
  
class fzero_sum_zero_0 = fzero_sum_zero + fzero_is_0
  
class fzero_almost_pre_trace_0 = left_cancel_semigroup + fzero_sum_zero + fzero_is_0  
  
class fzero_pre_trace_0 = fzero_pre_trace + fzero_is_0 (*left_cancel_semigroup + fzero_sum_zero_0*) 

class fzero_trace_0 = fzero_trace + fzero_is_0
 
instance fzero_add_zero_0 \<subseteq> monoid_add
  apply intro_classes
  using fzero_is_0 apply (metis add_fzero_left)
  using fzero_is_0 by (metis add_fzero_right)
    
instance fzero_almost_pre_trace_0 \<subseteq> left_cancel_semigroup
  by intro_classes
    
instance fzero_almost_pre_trace_0 \<subseteq> fzero_sum_zero_0
  by intro_classes
  
instance fzero_sum_zero_0 \<subseteq> monoid_sum_0
  apply intro_classes
  using fzero_is_0 apply (metis add_fzero_left)
  using fzero_is_0 apply (metis add_fzero_right)
  using fzero_is_0 by (metis fzero_sum)
    
instance fzero_pre_trace_0 \<subseteq> fzero_sum_zero_0
  by intro_classes
    
instance fzero_trace_0 \<subseteq> fzero_pre_trace_0
  by intro_classes
    
instance fzero_pre_trace_0 \<subseteq> pre_trace
  apply intro_classes
  using fzero_is_0 by (simp add: fzero_pre_trace_class.sum_eq_sum_conv)
  
instance fzero_trace_0 \<subseteq> trace
  apply intro_classes
  using fzero_is_0 apply (simp add: fzero_trace_class.le_iff_add monoid_le_def)
  using fzero_is_0 apply (simp add: less_le_not_le)
  using fzero_is_0 apply (simp add: minus_def fzero_is_0 monoid_subtract_def fzero_subtract_def, auto)
    by (simp_all add:fzero_is_0 fzero_le_def monoid_le_def)
    
instance fzero_trace_0 \<subseteq> monoid_add
  by intro_classes
    
instance fzero_trace_0 \<subseteq> fzero_trace
  by intro_classes
    
instance fzero_pre_trace_0 \<subseteq> fzero_pre_trace
  by intro_classes
    
lemma subtract_monoid_fzero_eq:
  fixes a :: "'a::fzero_pre_trace_0"
  shows "a -\<^sub>d b = a -\<^sub>m b"
  apply (simp add: minus_def fzero_is_0 monoid_subtract_def fzero_subtract_def, auto)
  by (simp_all add:fzero_is_0 fzero_le_def monoid_le_def)

lemma stlist_subtract_monoid_fzero_eq:
  fixes a :: "'a::monoid_add stlist"
  assumes "\<forall>x::'a::monoid_add stlist. fzero x = 0"
  shows "a -\<^sub>d b = a -\<^sub>m b"
  apply (simp add: minus_def fzero_is_0 monoid_subtract_def fzero_subtract_def, auto)
  apply (simp_all add:fzero_is_0 fzero_le_def monoid_le_def)
  using assms by simp
    
 (*
instantiation stlist :: (pre_trace) trace
begin
declare [[show_sorts]]
instance 
  apply (intro_classes, simp_all add:less_eq_stlist_def less_stlist_def minus_stlist_def)
  
   apply (simp add: fzero_le_def monoid_le_def)
   
    apply (simp add: monoid_subtract_def fzero_subtract_def, auto)
    
    apply (simp add: fzero_le_def monoid_le_def)
    
   apply (simp add: fzero_le_def monoid_le_def)
  sledgehammer
    nitpick
end*)
 
lemma monoid_plus_prefix_iff_zero:
  fixes a b :: "'a::trace"
  shows "a + x \<le> a \<longleftrightarrow> x = 0"
  by (metis add.right_neutral antisym left_cancel_semigroup_class.add_left_imp_eq trace_class.le_add)
    
lemma stlist_le_nil_imp_le_elements:
  fixes a b :: "'a::fzero_trace"
  shows "[;a] \<le> [;b] \<Longrightarrow> a \<le> b"
  apply (simp add: less_eq_stlist_def fzero_le_def)
  apply auto
  apply (case_tac c)
  apply auto
  apply (simp add: plus_stlist_def)
  by (simp add: stlist_nil_concat_cons)
    
lemma stlist_le_elements_imp_stlist_le_nil:
  fixes a b :: "'a::fzero_trace"
  shows "a \<le> b \<Longrightarrow> [;a] \<le> [;b]"
  apply (simp add: less_eq_stlist_def fzero_le_def le_is_fzero_le)
  by (metis stlist_plus_nils)
    
lemma stlist_le_nil_iff_le_elements:
  fixes a b :: "'a::fzero_trace"
  shows "[;a] \<le> [;b] \<longleftrightarrow> a \<le> b"
  apply auto
  apply (simp add: stlist_le_nil_imp_le_elements)
  by (simp add:stlist_le_elements_imp_stlist_le_nil)
    
lemma stlist_nil_le_cons_imp_le:
  fixes xs :: "'a::fzero_trace stlist"
  shows "[;a] \<le> (x#\<^sub>txs) \<Longrightarrow> a \<le> x"
  apply (simp add:less_eq_stlist_def le_is_fzero_le fzero_le_def)
  apply auto
  apply (case_tac c)
   apply (simp add: plus_stlist_def)
  by (metis stlist_cons_plus_nils_eq_cons)
    
lemma monoid_le_stlist:
  fixes a :: "'a::semigroup_add stlist"
  shows "a \<le> b \<longleftrightarrow> a \<le>\<^sub>d b"
  by (simp add:le_is_fzero_le less_eq_stlist_def)

lemma monoid_subtract_stlist: 
  fixes a :: "'a::semigroup_add stlist"
  shows "(a - b) = (a -\<^sub>d b)"
  by (simp add:minus_def minus_stlist_def) 
    
lemma stlist_minus_nils_imp_minus:
  fixes a b :: "'a::fzero_trace"
  (*assumes "\<forall>x::'a::trace stlist. fzero x = 0"*)
  shows "[;a] - [;b] = [;c] \<Longrightarrow> a - b = c"
  apply (simp add:minus_stlist_def minus_def) 
  using subtract_monoid_fzero_eq add.left_neutral pre_trace_class.add_monoid_diff_cancel_left stlist_plus_nils stlist_zero_is_zero fzero_trace_class.le_iff_add fzero_trace_class.minus_def fzero_trace_class.not_le_minus
  

 
lemma stlist_minus_imp_minus_nils:
  fixes a b :: "'a::fzero_trace"
  shows "a - b = c \<Longrightarrow> [;a] - [;b] = [;c]"
  unfolding minus_stlist_def minus_def
    nitpick
proof - (* massaged from an smt Isar proof *)
  assume a1: "a - b = c"
  have f2: "[;a] - [;b] = 0 \<longrightarrow> [;a] -\<^sub>m [;b] = [;0]"
    
    by (simp add: minus_stlist_def stlist_zero_is_zero)
  obtain aas :: "'a stlist \<Rightarrow> 'a stlist \<Rightarrow> 'a stlist" where
    "\<forall>x0 x1. (\<exists>v2. x0 = x1 + v2) = (x0 = x1 + aas x0 x1)"
    by moura
  then have f3: "\<forall>as asa. (\<not> as \<le> asa \<or> asa = as + aas asa as) \<and> (as \<le> asa \<or> (\<forall>asb. asa \<noteq> as + asb))"
    by (meson trace_class.le_iff_add)
  obtain aa :: "'a stlist \<Rightarrow> 'a" where
    "\<forall>x0. (\<exists>v3. x0 = [;v3]) = (x0 = [;aa x0])"
    by moura
  then have "\<forall>a ab as. [;a] \<noteq> [;ab] + as \<or> as = [;aa as]"
    by (meson stlist_eq_nil_pluses_imp0)
  then show "[;a] -\<^sub>m [;b] = [;c]"
    using f3 f2 a1 by (metis (no_types) minus_stlist_def pre_trace_class.add_monoid_diff_cancel_left stlist_minus_nils_imp_minus trace_class.not_le_minus)
qed
*)
    
lemma stlist_minus_eq_minus_nils:
  fixes a b :: "'a::trace"
  assumes "\<forall>x::'a::trace stlist. fzero x = 0"
  shows "a - b = c \<longleftrightarrow> [;a] - [;b] = [;c]"  
  using assms
  by (smt concat_stlist.simps(1) minus_stlist_def monoid_le_def monoid_subtract_def plus_stlist_def pre_trace_class.add_monoid_diff_cancel_left stlist_eq_nil_pluses_imp0 stlist_plus_nils stlist_subtract_monoid_fzero_eq stlist_zero_is_zero trace_class.minus_def)
 (* by (metis stlist_minus_nils_imp_minus stlist_minus_imp_minus_nils)
   *) 
lemma
  fixes a :: "'a::{trace,right_cancel_monoid}"
  shows "a = e + a \<longleftrightarrow> e = 0"
  by (metis add.assoc add.right_neutral left_cancel_semigroup_class.add_left_imp_eq right_cancel_semigroup_class.add_right_imp_eq)

lemma stlist_cons_minus_nil_eq:
  fixes xs :: "'a::fzero_trace stlist"
  assumes "[;a] \<le> (x#\<^sub>txs)"
  shows "(x#\<^sub>txs) - [;a] = (x-a)#\<^sub>txs"
proof -
  have a:"(x#\<^sub>txs) - [;a] = (THE c. x #\<^sub>t xs = [;a] + c)"
    using assms by (simp add:minus_stlist_def fzero_subtract_def le_is_fzero_le less_eq_stlist_def)
  
  have b:"(x-a)#\<^sub>txs = (THE c. x = a + c) #\<^sub>t xs"
    using assms
    apply (simp add:minus_def fzero_subtract_def)
    using minus_def fzero_subtract_def stlist_nil_le_cons_imp_le le_is_fzero_le
    by fastforce
  
  then have "(THE c. x #\<^sub>t xs = [;a] + c) = (THE c. x = a + c) #\<^sub>t xs"
    apply (auto)
    apply (rule the_equality)
     apply (simp add:plus_stlist_def)
    using assms minus_def stlist_nil_le_cons_imp_le 
     apply (metis fzero_trace_class.diff_add_cancel_left')
    by (metis assms fzero_trace_class.diff_add_cancel_left' stlist_cons_plus_nils_eq_cons stlist_left_cancel_monoid stlist_nil_le_cons_imp_le)
      
  then show ?thesis using a b by auto
qed

lemma stlist_zero_minus:
  fixes a :: "'a::fzero_trace"
  assumes "b \<le> a"
  shows "[;a] - [;b] = [;a - b]"
  using assms
  apply (simp add:minus_stlist_def fzero_subtract_def)
  apply auto
   apply (rule the_equality)
    apply (simp add: plus_stlist_def)
    apply (metis fzero_trace_class.add_diff_cancel_left fzero_trace_class.le_iff_add)
  apply (metis concat_stlist.simps(1) fzero_trace_class.diff_add_cancel_left' left_cancel_semigroup_class.add_left_imp_eq plus_stlist_def)
  by (metis less_eq_stlist_def stlist_le_nil_iff_le_elements)
  
(* a - (b + c) = a - b - c *)
    (*
lemma
  fixes a :: "'a::trace"
  shows "[;a] - [;b] = [;a - b]"
  using stlist_minus_eq_minus_nils by blast
    *)

lemma stlist_le_sum_cases:
fixes a :: "'a::pre_trace stlist"
shows "a \<le> b + c \<Longrightarrow> a \<le> b \<or> b \<le> a"
by (metis less_eq_stlist_def fzero_le_def stlist_sum_eq_sum_conv)
    
lemma stlist_nil_minus:
  fixes a b :: "'a::trace"
  assumes "\<forall>x::'a::trace stlist. fzero x = 0"
  shows "[;b] - [;a] = [;b-a]"
  apply (case_tac "a \<le> b")
  apply auto
  apply (simp add:minus_stlist_def)
   apply (metis assms minus_stlist_def stlist_minus_eq_minus_nils)
   using assms apply (simp add:zero_stlist_def)
  using assms stlist_minus_eq_minus_nils trace_class.not_le_minus by blast
  (*apply (metis assms stlist_le_nil_iff_le_elements zero_stlist_def)
  by (simp add:zero_stlist_def)
*)
(* assorted lemmas below *)
(*
lemma stlist_cons_right_prefix:
  fixes a :: "'a::pre_trace"
  assumes "\<forall>x::'a::pre_trace stlist. fzero x = 0"
  shows "[;a] \<le> [a;c]"
  using assms sledgehammer
proof -
  obtain aas :: "'a stlist \<Rightarrow> 'a stlist \<Rightarrow> 'a stlist" where
    "\<forall>x0 x1. (\<exists>v2. x0 = x1 + v2) = (x0 = x1 + aas x0 x1)"
    by moura
  then have f1: "\<forall>as asa. (\<not> as \<le> asa \<or> asa = as + aas asa as) \<and> (as \<le> asa \<or> (\<forall>asb. asa \<noteq> as + asb))"
    using assms fzero_trace_class.le_iff_add
    by (meson assms trace_class.le_iff_add)
  have f2: "[;a] + [;0] \<le> [;a]"
    by (simp add: monoid_plus_prefix_iff_zero zero_stlist_def)
  have "aas ([;a] + [;0] + aas [;a] ([;a] + [;0])) ([;a] + [;0] + aas [;a] ([;a] + [;0])) = 0"
    using f1 by (metis (no_types) monoid_plus_prefix_iff_zero order_refl)
  then have "a + 0 = a"
    using f2 f1 by (metis Terminated_lists.last.simps(1) concat_stlist.simps(1) order_refl plus_stlist_def zero_stlist_def)
  then show ?thesis
    using f1 by (metis (no_types) stlist_cons_plus_nils_eq_cons)
qed
    
lemma stlist_cons_minus_zero_left:
  fixes a :: "'a::trace"
  shows "[a;c] - [;a] = [0;c]"
  by (simp add: stlist_cons_minus_nil_eq stlist_cons_right_prefix)
  *)
end