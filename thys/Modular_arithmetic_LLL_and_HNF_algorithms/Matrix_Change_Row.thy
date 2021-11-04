section \<open>Missing Matrix Operations\<close>

text \<open>In this theory we provide an operation that can change a single
  row in a matrix efficiently, and all other rows in the matrix implementation
  will be reused.\<close>

(* TODO: move this part into JNF-AFP-entry *)

theory Matrix_Change_Row
  imports 
    Jordan_Normal_Form.Matrix_IArray_Impl
    Polynomial_Interpolation.Missing_Unsorted
begin

definition change_row :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "change_row k f A = mat (dim_row A) (dim_col A) (\<lambda> (i,j). 
     if i = k then f j (A $$ (k,j)) else A $$ (i,j))"

lemma change_row_carrier[simp]: 
  "(change_row k f A \<in> carrier_mat nr nc) = (A \<in> carrier_mat nr nc)" 
  "dim_row (change_row k f A) = dim_row A" 
  "dim_col (change_row k f A) = dim_col A" 
  unfolding change_row_def carrier_mat_def by auto

lemma change_row_index[simp]: "A \<in> carrier_mat nr nc \<Longrightarrow> i < nr \<Longrightarrow> j < nc \<Longrightarrow>
  change_row k f A $$ (i,j) = (if i = k then f j (A $$ (k,j)) else A $$ (i,j))" 
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> change_row k f A $$ (i,j) = (if i = k then f j (A $$ (k,j)) else A $$ (i,j))" 
  unfolding change_row_def by auto

lift_definition change_row_impl :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a mat_impl \<Rightarrow> 'a mat_impl" is
  "\<lambda> k f (nr,nc,A). let Ak = IArray.sub A k; Arows = IArray.list_of A;
     Ak' = IArray.IArray (map (\<lambda> (i,c). f i c) (zip [0 ..< nc] (IArray.list_of Ak)));
     A' = IArray.IArray (Arows [k := Ak'])
     in (nr,nc,A')" 
proof (auto, goal_cases)
  case (1 k f nc b row)
  show ?case 
  proof (cases b)
    case (IArray rows)
    with 1 have "row \<in> set rows \<or> k < length rows 
       \<and> row = IArray (map (\<lambda> (i,c). f i c) (zip [0 ..< nc] (IArray.list_of (rows ! k))))"
      by (cases "k < length rows", auto simp: set_list_update dest: in_set_takeD in_set_dropD)
    with 1 IArray show ?thesis by (cases, auto)
  qed
qed

lemma change_row_code[code]: "change_row k f (mat_impl A) = (if k < dim_row_impl A 
  then mat_impl (change_row_impl k f A) 
  else Code.abort (STR ''index out of bounds in change_row'') (\<lambda> _. change_row k f (mat_impl A)))"
  (is "?l = ?r")
proof (cases "k < dim_row_impl A")
  case True
  hence id: "?r = mat_impl (change_row_impl k f A)" by simp
  show ?thesis unfolding id unfolding change_row_def
  proof (rule eq_matI, goal_cases)
    case (1 i j)
    thus ?case using True
      by (transfer, auto simp: mk_mat_def)
  qed (transfer, auto)+
qed simp

end
