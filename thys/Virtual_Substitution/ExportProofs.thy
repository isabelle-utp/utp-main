subsection "Top-Level Algorithm Proofs"
theory ExportProofs
  imports HeuristicProofs Exports
    (*"HOL-Library.Code_Real_Approx_By_Float"*)
    HOL.String "HOL-Library.Code_Target_Int" "HOL-Library.Code_Target_Nat" PrettyPrinting Show.Show_Real
begin


theorem "eval (Unpower f) L = eval f L" unfolding unpower_eval Unpower_def by auto


theorem VSLuckiest: "\<forall>xs. eval (VSLuckiest \<phi>) xs = eval \<phi> xs"
  unfolding VSLuckiest_def Unpower_def opt_def
  using QE_dnf_eval[OF luckiestFind_eval' opt_no_group] opt_no_group
  by fastforce

theorem VSLuckiestBlocks : "\<forall>xs. eval (VSLuckiestBlocks \<phi>) xs = eval \<phi> xs"
  unfolding VSLuckiestBlocks_def Unpower_def opt_group_def
  using QE_dnf'_eval[OF the_real_step_augment[OF luckiestFind_eval, of "\<lambda>x _ _. x"] opt]
  using opt
  by fastforce

theorem VSEquality : "\<forall>xs. eval (VSEquality \<phi>) xs = eval \<phi> xs"
  unfolding VSEquality_def Unpower_def opt_def
  using QE_dnf_eval[OF qe_eq_repeat_eval' opt_no_group]
  using  opt_no_group VSLuckiest
  by fastforce


theorem VSEqualityBlocks : "\<forall>xs. eval (VSEqualityBlocks \<phi>) xs = eval \<phi> xs"
  unfolding VSEqualityBlocks_def Unpower_def opt_group_def
  using QE_dnf'_eval[OF the_real_step_augment[OF qe_eq_repeat_eval, of "\<lambda>x _ _. x"] opt]
  using opt VSLuckiestBlocks
  by fastforce

theorem VSGeneralBlocks : "\<forall>xs. eval (VSGeneralBlocks \<phi>) xs = eval \<phi> xs"
  unfolding VSGeneralBlocks_def Unpower_def opt_group_def
  using QE_dnf'_eval[OF the_real_step_augment[OF gen_qe_eval, of "\<lambda>x _ _. x"] opt]
  using opt VSLuckiestBlocks
  by fastforce

theorem VSLuckyBlocks : "\<forall>xs. eval (VSLuckyBlocks \<phi>) xs = eval \<phi> xs"
  unfolding VSLuckyBlocks_def Unpower_def opt_group_def
  using QE_dnf'_eval[OF the_real_step_augment[OF luckyFind'_eval, of "\<lambda>x _ _. x"] opt]
  using opt VSLuckiestBlocks
  by fastforce

theorem VSLEGBlocks : "\<forall>xs. eval (VSLEGBlocks \<phi>) xs = eval \<phi> xs"
  unfolding VSLEGBlocks_def opt_group_def
  using VSEqualityBlocks VSGeneralBlocks VSLuckyBlocks
  by fastforce

theorem VSEqualityBlocksLimited : "\<forall>xs. eval (VSEqualityBlocksLimited \<phi>) xs = eval \<phi> xs"
  unfolding VSEqualityBlocksLimited_def Unpower_def opt_group_def
  using QE_dnf_eval[OF qe_eq_repeat_eval_augment opt] opt VSLuckiestBlocks
  by fastforce


theorem VSEquality_3_times : "\<forall>xs. eval (VSEquality_3_times \<phi>) xs = eval \<phi> xs"
  using VSEquality unfolding VSEquality_3_times_def by auto

theorem VSGeneral:  "\<forall>xs. eval (VSGeneral \<phi>) xs = eval \<phi> xs"
  unfolding VSGeneral_def Unpower_def Unpower_def opt_def
  using QE_dnf_eval[OF gen_qe_eval' opt_no_group]
  using  opt_no_group VSLuckiest
  by fastforce

theorem VSGeneralBlocksLimited:  "\<forall>xs. eval (VSGeneralBlocksLimited \<phi>) xs = eval \<phi> xs"
  unfolding VSGeneralBlocksLimited_def Unpower_def opt_group_def
  using QE_dnf_eval[OF gen_qe_eval_augment opt] opt VSLuckiestBlocks
  by fastforce

theorem VSBrowns:  "\<forall>xs. eval (VSBrowns \<phi>) xs = eval \<phi> xs"
  unfolding VSBrowns_def Unpower_def opt_group_def
  using QE_dnf_eval[OF step_augmenter_eval[of gen_qe brownsHeuristic, OF gen_qe_eval brownHueristic_less_than] opt] opt VSLuckiestBlocks
  by fastforce


theorem VSGeneral_3_times : "\<forall>xs. eval (VSGeneral_3_times \<phi>) xs = eval \<phi> xs"
  unfolding  VSGeneral_3_times_def  using VSGeneral
  by auto

theorem VSLucky: "\<forall>xs. eval (VSLucky \<phi>) xs = eval \<phi> xs"
  unfolding VSLucky_def Unpower_def opt_def
  using QE_dnf_eval[OF luckyFind_eval' opt_no_group] opt_no_group VSLuckiest
  by fastforce

theorem VSLuckyBlocksLimited: "\<forall>xs. eval (VSLuckyBlocksLimited \<phi>) xs = eval \<phi> xs"
  unfolding VSLuckyBlocksLimited_def Unpower_def opt_group_def
  using QE_dnf_eval[OF luckyFind_eval_augment opt] opt VSLuckiestBlocks
  by fastforce

theorem VSLEG: "\<forall>xs. eval (VSLEG \<phi>) xs = eval \<phi> xs"
  unfolding VSLEG_def
  using VSLucky VSEquality VSGeneral by auto

theorem VSHeuristic : "\<forall>xs. eval(VSHeuristic \<phi>) xs = eval \<phi> xs"
  unfolding VSHeuristic_def Unpower_def opt_group_def
  using QE_dnf_eval[OF superPicker_eval opt] opt VSLuckiestBlocks
  by fastforce


theorem VSLuckiestRepeat : "\<forall>xs. eval (VSLuckiestRepeat \<phi>) xs = eval \<phi> xs"
  unfolding VSLuckiestRepeat_def using repeatAmountOfQuantifiers_eval[OF] using VSLuckiest
  by blast 


export_code
  print_mpoly
  VSGeneral VSEquality VSLucky VSLEG VSLuckiest
  VSGeneralBlocksLimited VSEqualityBlocksLimited VSLuckyBlocksLimited 
  VSGeneralBlocks VSEqualityBlocks VSLuckyBlocks VSLEGBlocks VSLuckiestBlocks
  QE_dnf
  gen_qe qe_eq_repeat
  simpfm push_forall nnf Unpower
  is_quantifier_free is_solved
  add mult C V pow minus
  Eq Or is_quantifier_free 

real_of_int real_mult real_div real_plus real_minus

VSGeneral_3_times VSEquality_3_times VSHeuristic VSLuckiestRepeat VSBrowns
in SML module_name VS




end