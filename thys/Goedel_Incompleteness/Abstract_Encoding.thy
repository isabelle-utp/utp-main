chapter \<open>Abstract Encoding\<close>

(*<*)
theory Abstract_Encoding imports Deduction2
begin
(*>*)

text \<open>Here we simply fix some unspecified encoding functions: encoding formulas
and proofs as numerals.\<close>

locale Encode =
Syntax_with_Numerals
  var trm fmla Var FvarsT substT Fvars subst
  num
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
+
fixes enc :: "'fmla \<Rightarrow> 'trm" ("\<langle>_\<rangle>")
assumes
enc[simp,intro!]: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> enc \<phi> \<in> num"
begin

end \<comment> \<open>context @{locale Encode}\<close>

text \<open>Explicit proofs (encoded as numbers), needed only for the harder half of
Goedel's first, and for both half's of Rosser's version; not needed in Goedel's
second.\<close>

locale Encode_Proofs =
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  enc
+
Deduct2_with_Proofs
  var trm fmla Var FvarsT substT Fvars subst
  eql cnj imp all exi
  fls
  dsj
  num
  prv bprv
  "proof" prfOf
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
and eql cnj imp all exi
and prv bprv
and enc ("\<langle>_\<rangle>")
and fls dsj
and "proof" :: "'proof set" and prfOf
+
fixes encPf :: "'proof \<Rightarrow> 'trm"
assumes
encPf[simp,intro!]: "\<And> pf. pf \<in> proof \<Longrightarrow> encPf pf \<in> num"


(*<*)
end
(*>*)