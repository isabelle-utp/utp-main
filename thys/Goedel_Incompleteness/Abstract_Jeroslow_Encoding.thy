chapter \<open>Jeroslow's Variant of G\"odel's Second Incompleteness Theorem\<close>

(*<*)
theory Abstract_Jeroslow_Encoding imports
"Syntax_Independent_Logic.Deduction"
begin
(*>*)

section \<open>Encodings and Derivability\<close>

text \<open>Here we formalize some of the assumptions of Jeroslow's theorem:
encoding, term-encoding and the First Derivability Condition.\<close>


subsection \<open>Encoding of formulas\<close>

locale Encode =
Syntax_with_Numerals
  var trm fmla Var FvarsT substT Fvars subst
  num
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
+
fixes
(*************************************)
(* Numeric formulas are assumed to be encoded as numerals: *)
enc :: "'fmla \<Rightarrow> 'trm" ("\<langle>_\<rangle>")
assumes
enc[simp,intro!]: "\<And> \<phi>. \<phi> \<in> fmla \<Longrightarrow> enc \<phi> \<in> num"
begin

end \<comment> \<open>context @{locale Encode}\<close>


subsection \<open>Encoding of computable functions\<close>

text \<open>Jeroslow assumes the encodability of an abstract (unspecified) class of
computable functions and the assumption that a particular function, @{term "sub \<phi>"} for each formula
@{term \<phi>}, is in this collection. This is used to prove a different flavor of the diagonalization
lemma (Jeroslow 1973). It turns out that only an encoding of unary computable functions
is needed, so we only assume that.\<close>

locale Encode_UComput =
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  enc
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
and enc ("\<langle>_\<rangle>")
+
\<comment> \<open>Abstract (unspeficied) notion of unary "computable" function
between numerals, which are encoded as numerals. They
contain a special substitution-like function @{term "sub \<phi>"} for each formula @{term "\<phi>"}.\<close>
fixes ucfunc :: "('trm \<Rightarrow> 'trm) set"
  and encF :: "('trm \<Rightarrow> 'trm) \<Rightarrow> 'trm"
  and sub :: "'fmla \<Rightarrow> 'trm \<Rightarrow> 'trm"
assumes
\<comment> \<open>NB: Due to the limitations of the type system, we define @{term "ufunc"} as a set of functions
between terms, but we only care about their actions on numerals ...
so we assume they send numerals to numerals:\<close>
ucfunc[simp,intro!]: "\<And> f n. f \<in> ucfunc \<Longrightarrow> n \<in> num \<Longrightarrow> f n \<in> num"
and
encF[simp,intro!]: "\<And> f. f \<in> ucfunc \<Longrightarrow> encF f \<in> num"
and
sub[simp]: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> sub \<phi> \<in> ucfunc"
and
\<comment> \<open>The function @{term "sub \<phi>"} takes any encoding of a function @{term "f"} and returns the encoding of
the formula obtained by substituting for @{term "xx"} the value of @{term "f"} applied to its own encoding:\<close>
sub_enc:
"\<And> \<phi> f. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {xx} \<Longrightarrow> f \<in> ucfunc \<Longrightarrow>
    sub \<phi> (encF f) = enc (inst \<phi> (f (encF f)))"


subsection \<open>Term-encoding of computable functons\<close>

text \<open>For handling the notion of term-representation (which we introduce later),
we assume we are given a set @{term "Ops"} of term operators and their encodings as numerals.
We additionally assume that the term operators behave well w.r.t. free variables and
substitution.\<close>

locale TermEncode =
Syntax_with_Numerals
  var trm fmla Var FvarsT substT Fvars subst
  num
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
+
fixes
Ops ::  "('trm \<Rightarrow> 'trm) set"
and
enc :: "('trm \<Rightarrow> 'trm) \<Rightarrow> 'trm" ("\<langle>_\<rangle>")
assumes
Ops[simp,intro!]: "\<And>f t. f \<in> Ops \<Longrightarrow> t \<in> trm \<Longrightarrow> f t \<in> trm"
and
enc[simp,intro!]: "\<And> f. f \<in> Ops \<Longrightarrow> enc f \<in> num"
and
Ops_FvarsT[simp]: "\<And> f t. f \<in> Ops \<Longrightarrow> t \<in> trm \<Longrightarrow> FvarsT (f t) = FvarsT t"
and
Ops_substT[simp]: "\<And> f t. f \<in> Ops \<Longrightarrow> t \<in> trm \<Longrightarrow> t1 \<in> trm \<Longrightarrow> x \<in> var \<Longrightarrow>
  substT (f t) t1 x = f (substT t t1 x)"
begin

end \<comment> \<open>context @{locale TermEncode}\<close>


subsection \<open>The first Hilbert-Bernays-Löb derivability condition\<close>

locale HBL1 =
Encode
  var trm fmla Var FvarsT substT Fvars subst
  num
  enc
+
Deduct
  var trm fmla Var FvarsT substT Fvars subst
  num
  eql cnj imp all exi
  prv
for
var :: "'var set" and trm :: "'trm set" and fmla :: "'fmla set"
and Var FvarsT substT Fvars subst
and num
and eql cnj imp all exi
and prv bprv
and enc ("\<langle>_\<rangle>")
+
fixes P :: 'fmla
assumes
P[intro!,simp]: "P \<in> fmla"
and
Fvars_P[simp]: "Fvars P = {xx}"
and
HBL1: "\<And>\<phi>. \<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> prv (subst P \<langle>\<phi>\<rangle> xx)"
begin

text \<open>Predicate version of the provability formula\<close>
definition PP where "PP \<equiv> \<lambda>t. subst P t xx"

lemma PP[simp]: "\<And>t. t \<in> trm \<Longrightarrow> PP t \<in> fmla"
  unfolding PP_def by auto

lemma Fvars_PP[simp]: "\<And>t. t \<in> trm \<Longrightarrow> Fvars (PP t) = FvarsT t"
  unfolding PP_def by auto

lemma [simp]:
"n \<in> num \<Longrightarrow> subst (PP (Var yy)) n yy = PP n"
"n \<in> num \<Longrightarrow> subst (PP (Var xx)) n xx = PP n"
  unfolding PP_def by auto

lemma HBL1_PP:
"\<phi> \<in> fmla \<Longrightarrow> Fvars \<phi> = {} \<Longrightarrow> prv \<phi> \<Longrightarrow> prv (PP \<langle>\<phi>\<rangle>)"
  using HBL1 unfolding PP_def by auto

end \<comment> \<open>context @{locale HBL1}\<close>

(*<*)
end
(*>*)