(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: Abstract_Pacemaker.thy                                               *)
(* Authors: Casper Thule                                                      *)
(* Emails: casper.thule@eng.au.dk                                             *)
(******************************************************************************)
(* LAST REVIEWED: 30 Oct 2017 *)

section {* Abstract_Pacemaker case study *}

text {* 
  This theory contains the VDM-SL case study Abstract Pacemaker expressed using
  LPF and Isabelle/UTP.
*}

theory Abstract_Pacemaker
imports
  "./LPF"
  "./LPF_Operators"
begin
datatype Event = A | V | nil
type_synonym Trace = "Event list lpf"

(* Turn this into state *)
definition aperiod :: "nat" where
  "aperiod = 5"

(* Turn this into state *)
definition vdelay :: "nat" where
  "vdelay = 2"

definition wrongTR :: "Trace" where
  "wrongTR = lpf_Some([A,nil,V,nil,nil,A,nil,nil,nil,nil])"

definition innerFunction :: "real \<Rightarrow> Event lpf" where
"innerFunction x = lpf_Some(A)"

definition IdealHeart :: "Trace" where 
"IdealHeart = 
  seq_comprehension_lpf  (\<lambda>x . 
    if (x mod aperiod) = 1
    then lpf_Some(A)
    else if (x mod aperiod) = (vdelay + 1)
    then lpf_Some(V)
    else lpf_Some(nil)) 
  (lpf_Some(List.coset([1..100])))"
 
definition Pace :: "Trace \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Trace" where
"Pace tr aperi vdl = IdealHeart"

end