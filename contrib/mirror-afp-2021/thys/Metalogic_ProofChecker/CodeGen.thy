  
section "Code Generation"

theory CodeGen
  imports ProofTerm TheoryExe CheckerExe Instances
    "HOL-Library.Code_Target_Int"
    "HOL-Library.Code_Target_Nat"
begin

declare typ_of_def[code]

export_code exe_check_proof exereplay exe_wf_theory
  Bv PBound Tv Free ExeTheory ExeSignature (* To have acces to type constructors in interace*)
  in SML module_name ExportCheck file_prefix export

(*
  Need to change the following yourself, to open the interface

  datatype int = Int_of_integer of IntInf.int;
  datatype nat = Nat of IntInf.int;
  datatype 'a set = Set of 'a list | Coset of 'a list;
*)

end
