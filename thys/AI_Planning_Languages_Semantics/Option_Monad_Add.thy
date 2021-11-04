theory Option_Monad_Add
imports "HOL-Library.Monad_Syntax"
begin
  definition "oassert \<Phi> \<equiv> if \<Phi> then Some () else None"

  fun omap :: "('a\<rightharpoonup>'b) \<Rightarrow> 'a list \<rightharpoonup> 'b list" where
    "omap f [] = Some []" 
  | "omap f (x#xs) = do { y \<leftarrow> f x; ys \<leftarrow> omap f xs; Some (y#ys) }"  
    
  lemma omap_cong[fundef_cong]:
    assumes "\<And>x. x\<in>set l' \<Longrightarrow> f x = f' x"
    assumes "l=l'"
    shows "omap f l = omap f' l'"
    unfolding assms(2) using assms(1) by (induction l') (auto)

  lemma assert_eq_iff[simp]: 
    "oassert \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"  
    "oassert \<Phi> = Some u \<longleftrightarrow> \<Phi>"  
    unfolding oassert_def by auto

  lemma omap_length[simp]: "omap f l = Some l' \<Longrightarrow> length l' = length l" 
    apply (induction l arbitrary: l') 
    apply (auto split: Option.bind_splits)
    done 

  lemma omap_append[simp]: "omap f (xs@ys) = do {xs \<leftarrow> omap f xs; ys \<leftarrow> omap f ys; Some (xs@ys)}"
    by (induction xs) (auto)
    
        
  lemma omap_alt: "omap f l = Some l' \<longleftrightarrow> (l' = map (the o f) l \<and> (\<forall>x\<in>set l. f x \<noteq> None))"  
    apply (induction l arbitrary: l')
    apply (auto split: Option.bind_splits)
    done
    
  lemma omap_alt_None: "omap f l = None \<longleftrightarrow> (\<exists>x\<in>set l. f x = None)"
    apply (induction l)
    apply (auto split: Option.bind_splits)
    done
    
  lemma omap_nth: "\<lbrakk>omap f l = Some l'; i<length l\<rbrakk> \<Longrightarrow> f (l!i) = Some (l'!i)"
    apply (induction l arbitrary: l' i)
    apply (auto split: Option.bind_splits simp: nth_Cons split: nat.splits)
    done

  lemma omap_eq_Nil_conv[simp]: "omap f xs = Some [] \<longleftrightarrow> xs=[]"
    apply (cases xs) 
    apply (auto split: Option.bind_splits)
    done

  lemma omap_eq_Cons_conv[simp]: "omap f xs = Some (y#ys') \<longleftrightarrow> (\<exists>x xs'. xs=x#xs' \<and> f x = Some y \<and> omap f xs' = Some ys')"  
    apply (cases xs) 
    apply (auto split: Option.bind_splits)
    done
        
  lemma omap_eq_append_conv[simp]: "omap f xs = Some (ys\<^sub>1@ys\<^sub>2) \<longleftrightarrow> (\<exists>xs\<^sub>1 xs\<^sub>2. xs=xs\<^sub>1@xs\<^sub>2 \<and> omap f xs\<^sub>1 = Some ys\<^sub>1 \<and> omap f xs\<^sub>2 = Some ys\<^sub>2)"
    apply (induction ys\<^sub>1 arbitrary: xs)
    apply (auto 0 3 split: Option.bind_splits)
    apply (metis append_Cons)
    done
  
  lemma omap_list_all2_conv: "omap f xs = Some ys \<longleftrightarrow> (list_all2 (\<lambda>x y. f x = Some y)) xs ys"  
    apply (induction xs arbitrary: ys)
    apply (auto split: Option.bind_splits simp: )
    apply (simp add: list_all2_Cons1)
    apply (simp add: list_all2_Cons1)
    apply (simp add: list_all2_Cons1)
    apply clarsimp
    by (metis option.inject)
    
    
    
    
  fun omap_option where
    "omap_option f None = Some None"    
  | "omap_option f (Some x) = do { x \<leftarrow> f x; Some (Some x) }"
  
  lemma omap_option_conv:
    "omap_option f xx = None \<longleftrightarrow> (\<exists>x. xx=Some x \<and> f x = None)" 
    "omap_option f xx = (Some (Some x')) \<longleftrightarrow> (\<exists>x. xx=Some x \<and> f x = Some x')"
    "omap_option f xx = (Some None) \<longleftrightarrow> xx=None"
    by (cases xx;auto split: Option.bind_splits)+
  
  lemma omap_option_eq: "omap_option f x = (case x of None \<Rightarrow> Some None | Some x \<Rightarrow> do { x \<leftarrow> f x; Some (Some x) })"  
    by (auto split: option.split)
      
  fun omap_prod where
    "omap_prod f\<^sub>1 f\<^sub>2 (a,b) = do { a\<leftarrow>f\<^sub>1 a; b\<leftarrow>f\<^sub>2 b; Some (a,b) }"
    
      
  (* Extend map function for datatype to option monad.
    TODO: Show reasonable lemmas, like parametricity, etc. 
    Hopefully only depending on BNF-property of datatype
   *)
  definition "omap_dt setf mapf f obj \<equiv> do {
    oassert (\<forall>x\<in>setf obj. f x \<noteq> None);
    Some (mapf (the o f) obj)
  }"
    
    
    
end
