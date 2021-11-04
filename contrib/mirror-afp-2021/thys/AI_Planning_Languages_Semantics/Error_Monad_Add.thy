theory Error_Monad_Add
imports
  "Certification_Monads.Check_Monad"
  "Show.Show_Instances"
begin
  (* TODO: Move *)  
  abbreviation "assert_opt \<Phi> \<equiv> if \<Phi> then Some () else None"  

  definition "lift_opt m e \<equiv> case m of Some x \<Rightarrow> Error_Monad.return x | None \<Rightarrow> Error_Monad.error e"
    
  lemma lift_opt_simps[simp]: 
    "lift_opt None e = error e"
    "lift_opt (Some v) e = return v"
    by (auto simp: lift_opt_def)
  
  (* TODO: Move *)  
  lemma reflcl_image_iff[simp]: "R\<^sup>=``S = S\<union>R``S" by blast 
    
  named_theorems return_iff
      
  lemma bind_return_iff[return_iff]: "Error_Monad.bind m f = Inr y \<longleftrightarrow> (\<exists>x. m = Inr x \<and> f x = Inr y)"
    by auto
    
  lemma lift_opt_return_iff[return_iff]: "lift_opt m e = Inr x \<longleftrightarrow> m=Some x"
    unfolding lift_opt_def by (auto split: option.split)
      
  lemma check_return_iff[return_iff]: "check \<Phi> e = Inr uu \<longleftrightarrow> \<Phi>"    
    by (auto simp: check_def)
  
  
  lemma check_simps[simp]:  
    "check True e = succeed"
    "check False e = error e"
    by (auto simp: check_def)
        
  lemma Let_return_iff[return_iff]: "(let x=v in f x) = Inr w \<longleftrightarrow> f v = Inr w" by simp

  
  abbreviation ERR :: "shows \<Rightarrow> (unit \<Rightarrow> shows)" where "ERR s \<equiv> \<lambda>_. s"
  abbreviation ERRS :: "String.literal \<Rightarrow> (unit \<Rightarrow> shows)" where "ERRS s \<equiv> ERR (shows s)"
  
  
  lemma error_monad_bind_split: "P (bind m f) \<longleftrightarrow> (\<forall>v. m = Inl v \<longrightarrow> P (Inl v)) \<and> (\<forall>v. m = Inr v \<longrightarrow> P (f v))"
    by (cases m) auto
  
  lemma error_monad_bind_split_asm: "P (bind m f) \<longleftrightarrow> \<not> (\<exists>x. m = Inl x \<and> \<not> P (Inl x) \<or> (\<exists>x. m = Inr x \<and> \<not> P (f x)))"
    by (cases m) auto
  
  lemmas error_monad_bind_splits =error_monad_bind_split error_monad_bind_split_asm
  
  
end
