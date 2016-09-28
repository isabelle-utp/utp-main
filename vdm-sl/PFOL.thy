section {* Partial First Order Logic *}

theory PFOL
  imports "../utp/utp_var"
begin

subsection {* Truth values *}

text {* We obtain three valued logic by simply using the option type *}

type_synonym tvl = "bool option"

notation
  Some ("\<lfloor>_\<rfloor>")

text {* Definedness of a given tvl value *}

definition tvl_defined :: "tvl \<Rightarrow> bool" ("\<D>\<^sub>3") where
"\<D>\<^sub>3(p) \<equiv> p \<noteq> None"

syntax
  "_true_tvl"  :: "tvl" ("true\<^sub>3")
  "_false_tvl" :: "tvl" ("false\<^sub>3")
  "_bot_tvl"   :: "tvl" ("\<bottom>\<^sub>3")

translations
  "_true_tvl"  => "CONST Some CONST True"
  "_false_tvl" => "CONST Some CONST False"
  "_bot_tvl"   => "CONST None"

lemma tvl_defined [intro, simp]: "\<D>\<^sub>3(\<lfloor>x\<rfloor>)"
  by (simp add: tvl_defined_def)

lemma tvl_cases:
  "\<lbrakk> p = true\<^sub>3 \<Longrightarrow> P; p = false\<^sub>3 \<Longrightarrow> P; p = \<bottom>\<^sub>3 \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto)

text {* Tautologies *}

definition tvl_taut :: "tvl \<Rightarrow> bool" ("[_]\<^sub>3") where
"tvl_taut p = (p = true\<^sub>3)"

lemma tvl_taut_Some [simp]: "[\<lfloor>x\<rfloor>]\<^sub>3 = x"
  by (simp add: tvl_taut_def)

lemma tvlI [intro]: "p \<Longrightarrow> [\<lfloor>p\<rfloor>]\<^sub>3"
  by (simp add: tvl_taut_def)

lemma tvlD [dest!]: "[\<lfloor>p\<rfloor>]\<^sub>3 \<Longrightarrow> p"
  by (simp add: tvl_taut_def)

lemma tvl_bot [simp]: "[\<bottom>\<^sub>3]\<^sub>3 = False"
  by (simp add: tvl_taut_def)

subsection {* Logical operators *}

text {* The operators in this section are taken from a paper by Gavilanes-Franco and Lucio-Carrasco
        called "A first order logic for partial functions". Rather than defining them in terms
        of conjunction and disjunction, we define them all separately and then prove the laws 
        about the relationships. *}

definition knot :: "tvl \<Rightarrow> tvl" ("\<not>\<^sub>k _" [40] 40) where
"knot p = (case p of
             None \<Rightarrow> None |
             Some v \<Rightarrow> Some (\<not> v))"

definition kand :: "tvl \<Rightarrow> tvl \<Rightarrow> tvl" (infixr "\<and>\<^sub>k" 35) where
"kand p q =
  (if (p = true\<^sub>3 \<and> q = true\<^sub>3)
      then true\<^sub>3
   else if (p = false\<^sub>3 \<or> q = false\<^sub>3)
      then false\<^sub>3
   else \<bottom>\<^sub>3)"

definition kor :: "tvl \<Rightarrow> tvl \<Rightarrow> tvl" (infixr "\<or>\<^sub>k" 35) where
"(p \<or>\<^sub>k q) =
  (if (p = true\<^sub>3 \<or> q = true\<^sub>3)
      then true\<^sub>3
   else if (p = false\<^sub>3 \<and> q = false\<^sub>3)
      then false\<^sub>3
   else \<bottom>\<^sub>3)"

definition kimpl :: "tvl \<Rightarrow> tvl \<Rightarrow> tvl" (infixr "\<Rightarrow>\<^sub>k" 25) where
"(p \<Rightarrow>\<^sub>k q) =
    (if (p = false\<^sub>3 \<or> q = true\<^sub>3)
        then true\<^sub>3
     else if (p = true\<^sub>3 \<and> q = false\<^sub>3)
        then false\<^sub>3
     else \<bottom>\<^sub>3)"

definition kEx :: "('a \<Rightarrow> tvl) \<Rightarrow> tvl" (binder "\<exists>\<^sub>k" 10) where
"kEx P = 
  (if (\<exists> x. P(x) = true\<^sub>3)
      then true\<^sub>3
   else if (\<forall> x. P(x) = false\<^sub>3)
      then false\<^sub>3
   else \<bottom>\<^sub>3)"

definition kAll :: "('a \<Rightarrow> tvl) \<Rightarrow> tvl" (binder "\<forall>\<^sub>k" 10) where
"kAll P = 
  (if (\<forall> x. P(x) = true\<^sub>3)
      then true\<^sub>3
   else if (\<exists> x. P(x) = false\<^sub>3)
      then false\<^sub>3
   else \<bottom>\<^sub>3)"

definition kBall :: "'a set \<Rightarrow> ('a \<Rightarrow> tvl) \<Rightarrow> tvl" where
"kBall A P = (\<forall>\<^sub>k x. \<lfloor>x \<in> A\<rfloor> \<Rightarrow>\<^sub>k P x)" -- {* bounded universal quantification *}

definition kBex :: "'a set \<Rightarrow> ('a \<Rightarrow> tvl) \<Rightarrow> tvl" where
"kBex A P = (\<exists>\<^sub>k x. \<lfloor>x \<in> A\<rfloor> \<Rightarrow>\<^sub>k P x)" -- {* bounded existential quantification *}

syntax
  "_kBall" :: "pttrn => 'a set => bool => bool"      ("(3\<forall>\<^sub>k_\<in>_./ _)" [0, 0, 10] 10)
  "_kBex"  :: "pttrn => 'a set => bool => bool"      ("(3\<exists>\<^sub>k_\<in>_./ _)" [0, 0, 10] 10)

translations
  "\<forall>\<^sub>k x \<in> A. P" == "CONST kBall A (\<lambda> x. P)"
  "\<exists>\<^sub>k x \<in> A. P" == "CONST kBex A (\<lambda> x. P)"

subsection {* Definedness rules *}

text {* The first task in setting up proof automation is automate definedness checking. We
        first prove some laws about the definedness of the logical connectives. We need
        to do this first, as these laws will be necessary for the proof calculus. There
        are probably weakened forms of each of these rules, but I haven't the time to
        figure them out right now. *}

lemma tvl_defined_alt_def: "\<D>\<^sub>3(p) = [p]\<^sub>3 \<or> [\<not>\<^sub>k p]\<^sub>3"
  by (auto simp add: tvl_defined_def knot_def tvl_taut_def)

lemma knot_defined [simp]: "\<D>\<^sub>3 (\<not>\<^sub>k p) = \<D>\<^sub>3 p"
  by (cases p rule: tvl_cases, simp_all add: knot_def tvl_defined_def)

lemma knot_defI [intro]: "\<D>\<^sub>3 p \<Longrightarrow> \<D>\<^sub>3 (\<not>\<^sub>k p)"
  by simp

lemma kand_defI1 [intro]: "\<lbrakk> \<D>\<^sub>3(p); \<D>\<^sub>3(q) \<rbrakk> \<Longrightarrow> \<D>\<^sub>3(p \<and>\<^sub>k q)"
  by (auto simp add: kand_def tvl_defined_def)

lemma kor_defI1 [intro]: "\<lbrakk> \<D>\<^sub>3(p); \<D>\<^sub>3(q) \<rbrakk> \<Longrightarrow> \<D>\<^sub>3(p \<or>\<^sub>k q)"
  by (auto simp add: kor_def tvl_defined_def)

lemma kimpl_defI1 [intro]: "\<lbrakk> \<D>\<^sub>3(p); \<D>\<^sub>3(q) \<rbrakk> \<Longrightarrow> \<D>\<^sub>3(p \<Rightarrow>\<^sub>k q)"
  by (auto simp add: kimpl_def tvl_defined_def)

lemma kAll_defI1 [intro]: "\<lbrakk> \<And> x. \<D>\<^sub>3(P x) \<rbrakk> \<Longrightarrow> \<D>\<^sub>3 (\<forall>\<^sub>kx. P x)"
  by (auto simp add: tvl_defined_def kAll_def, metis (full_types))

lemma kEx_defI1 [intro]: "\<lbrakk> \<And> x. \<D>\<^sub>3(P x) \<rbrakk> \<Longrightarrow> \<D>\<^sub>3 (\<exists>\<^sub>kx. P x)"
  by (auto simp add: tvl_defined_def kEx_def, metis (full_types))

subsection {* Proof rules *}

text {* Many of these rules take a similar form to their HOL equivalents, but additionally
        have definedness provisos. These provisos much be discharged by the laws above.
        Again, there's a lot of work still to do to make proof automation effective. *}

lemma keqI [intro]: "\<lbrakk> [P \<Rightarrow>\<^sub>k Q]\<^sub>3; [Q \<Rightarrow>\<^sub>k P]\<^sub>3 \<rbrakk> \<Longrightarrow> P = Q"
  by (cases P rule: tvl_cases; cases Q rule:tvl_cases, simp_all add: tvl_taut_def kimpl_def)

lemma kNotI [intro]: "\<lbrakk> [P]\<^sub>3 \<Longrightarrow> False; \<D>\<^sub>3(P) \<rbrakk> \<Longrightarrow> [\<not>\<^sub>k P]\<^sub>3"
  by (cases P rule: tvl_cases, auto simp add: knot_def tvl_taut_def tvl_defined_def)

lemma kNotE [elim?]: "\<lbrakk> [\<not>\<^sub>k P]\<^sub>3; [\<not>\<^sub>k P]\<^sub>3 \<Longrightarrow> [P]\<^sub>3 \<rbrakk> \<Longrightarrow> R"
  by (simp add: knot_def tvl_taut_def)

lemma kAndI [intro]: "\<lbrakk> [P]\<^sub>3; [Q]\<^sub>3 \<rbrakk> \<Longrightarrow> [P \<and>\<^sub>k Q]\<^sub>3"
  by (simp add: kand_def tvl_taut_def)

lemma kAndE [elim]: "\<lbrakk> [P \<and>\<^sub>k Q]\<^sub>3; [P]\<^sub>3 \<Longrightarrow> [Q]\<^sub>3 \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (cases P rule: tvl_cases; cases Q rule: tvl_cases, simp_all add: kand_def tvl_taut_def)

lemma kOrI1 [intro]: "[P]\<^sub>3 \<Longrightarrow> [P \<or>\<^sub>k Q]\<^sub>3"
  by (simp add: kor_def tvl_taut_def)

lemma kOrI2 [intro]: "[Q]\<^sub>3 \<Longrightarrow> [P \<or>\<^sub>k Q]\<^sub>3"
  by (simp add: kor_def tvl_taut_def)

lemma kOrE [elim]: "\<lbrakk> [P \<or>\<^sub>k Q]\<^sub>3; [P]\<^sub>3 \<Longrightarrow> R; [Q]\<^sub>3 \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (cases P rule: tvl_cases; cases Q rule: tvl_cases, simp_all add: kor_def tvl_taut_def)

lemma kAllI [intro]: "\<lbrakk> \<And> x. [P x]\<^sub>3 \<rbrakk> \<Longrightarrow> [\<forall>\<^sub>k x. P x]\<^sub>3"
  by (auto simp add: kAll_def tvl_taut_def)

lemma kAllE [elim]: "\<lbrakk> [\<forall>\<^sub>k x. P x]\<^sub>3; [P x]\<^sub>3 \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (auto simp add: kAll_def tvl_taut_def, metis option.distinct(1) option.inject)

lemma kimpI [intro]: "\<lbrakk> [P]\<^sub>3 \<Longrightarrow> [Q]\<^sub>3 ; \<D>\<^sub>3(P) \<rbrakk> \<Longrightarrow> [P \<Rightarrow>\<^sub>k Q]\<^sub>3"
  by (cases P rule: tvl_cases; cases Q rule: tvl_cases , auto simp add: kimpl_def tvl_defined_def)

lemma kBallI [intro]: "\<lbrakk> \<And> x. x \<in> A \<Longrightarrow> [P x]\<^sub>3 \<rbrakk> \<Longrightarrow> [\<forall>\<^sub>k x \<in> A. P x]\<^sub>3"
  by (force simp add: kBall_def)

lemma kExI [intro]: "[P x]\<^sub>3 \<Longrightarrow> [\<exists>\<^sub>k x. P x]\<^sub>3"
  using option.inject by (auto simp add: kEx_def tvl_taut_def, fastforce)

lemma kBexI [intro]: "\<lbrakk> x \<in> A; [P x]\<^sub>3 \<rbrakk> \<Longrightarrow> [\<exists>\<^sub>k x \<in> A. P x]\<^sub>3"
  by (auto simp add: kBex_def)

subsection {* Algebraic laws *}

text {* Again, this set of laws is largely incomplete. *}

lemma knot_false [simp]: "(\<not>\<^sub>k false\<^sub>3) = true\<^sub>3"
  by blast

lemma knot_true [simp]: "(\<not>\<^sub>k true\<^sub>3) = false\<^sub>3"
  by (simp add: knot_def)

lemma knot_bot [simp]: "(\<not>\<^sub>k \<bottom>\<^sub>3) = \<bottom>\<^sub>3"
  by (simp add: knot_def)

lemma kand_assoc: "((p \<and>\<^sub>k q) \<and>\<^sub>k r) = (p \<and>\<^sub>k q \<and>\<^sub>k r)"
   by (cases p, simp_all add: kand_def)

lemma kand_comm: "(p \<and>\<^sub>k q) = (q \<and>\<^sub>k p)"
  by (cases p, simp_all add: kand_def)

lemma kand_idem: "(p \<and>\<^sub>k p) = p"
  by (cases p rule: tvl_cases, simp_all add: kand_def)

lemma kand_left_unit [simp]: "(true\<^sub>3  \<and>\<^sub>k p) = p"
  by (cases p rule: tvl_cases, simp_all add: kand_def)

lemma kand_right_unit [simp]: "(p \<and>\<^sub>k true\<^sub>3) = p"
  by (cases p rule: tvl_cases, simp_all add: kand_def)

lemma kand_left_anhil [simp]: "(false\<^sub>3  \<and>\<^sub>k p) = false\<^sub>3"
  by (cases p rule: tvl_cases, simp_all add: kand_def)

lemma kand_right_anhil [simp]: "(p \<and>\<^sub>k false\<^sub>3) = false\<^sub>3"
  by (cases p rule: tvl_cases, simp_all add: kand_def)

lemma kimpl_false [simp]: "(false\<^sub>3 \<Rightarrow>\<^sub>k p) = true\<^sub>3"
  by (simp add: kimpl_def)

lemma kimpl_kor: "(p \<Rightarrow>\<^sub>k q) = (\<not>\<^sub>k p \<or>\<^sub>k q)"
  by (cases p rule: tvl_cases, simp_all add: kimpl_def kor_def)

lemma kor_demorgan:
  "(p \<or>\<^sub>k q) = (\<not>\<^sub>k ((\<not>\<^sub>k p) \<and>\<^sub>k (\<not>\<^sub>k q)))"
  apply (cases p rule: tvl_cases; cases q rule: tvl_cases)
  apply (simp_all add: kor_def kand_def knot_def)
done  

lemma kand_demorgan:
  "(p \<and>\<^sub>k q) = (\<not>\<^sub>k ((\<not>\<^sub>k p) \<or>\<^sub>k (\<not>\<^sub>k q)))"
  apply (cases p rule: tvl_cases; cases q rule: tvl_cases)
  apply (simp_all add: kor_def kand_def knot_def)
done

lemma kand_Some [simp]: "(\<lfloor>x\<rfloor> \<and>\<^sub>k \<lfloor>y\<rfloor>) = \<lfloor>x \<and> y\<rfloor>"
  by (simp add: kand_def)

lemma kor_Some [simp]: "(\<lfloor>x\<rfloor> \<or>\<^sub>k \<lfloor>y\<rfloor>) = \<lfloor>x \<or> y\<rfloor>"
  by (simp add: kor_def)

lemma kAll_kEx: "(\<forall>\<^sub>k x. P x) = (\<not>\<^sub>k (\<exists>\<^sub>k x. \<not>\<^sub>k P x))"
  by (simp add: kAll_def kEx_def knot_def, metis knot_bot knot_def knot_false knot_true tvl_cases)

lemma kAll_true [simp]: "(\<forall>\<^sub>k x. true\<^sub>3) = true\<^sub>3"
  by (simp add: kAll_def)

lemma kAll_kand: "(\<forall>\<^sub>k x. P x \<and>\<^sub>k Q x) = ((\<forall>\<^sub>k x. P x) \<and>\<^sub>k (\<forall>\<^sub>k x. Q x))"
  by (auto simp add: kAll_def kand_def)

lemma kAll_false [simp]: "(\<exists>\<^sub>k x. true\<^sub>3) = true\<^sub>3"
  by (simp add: kEx_def)

end