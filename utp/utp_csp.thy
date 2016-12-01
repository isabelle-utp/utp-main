section {* Theory of CSP *}

theory utp_csp
  imports utp_rea_designs utp_procedure
begin

subsection {* Preliminaries *} 

record '\<phi> alpha_csp' = 
  csp_ref :: "'\<phi> set"

type_synonym ('\<phi>, '\<alpha>) alpha_csp_scheme = "('\<phi> list, ('\<phi>, '\<alpha>) alpha_csp'_scheme) alpha_rp_scheme"

type_synonym ('\<phi>,'\<alpha>) alphabet_csp  = "('\<phi>,'\<alpha>) alpha_csp_scheme alphabet"
type_synonym ('\<phi>,'\<alpha>,'\<beta>) relation_csp  = "(('\<phi>,'\<alpha>) alphabet_csp, ('\<phi>,'\<beta>) alphabet_csp) relation"
type_synonym ('\<phi>,'\<alpha>) hrelation_csp  = "(('\<phi>,'\<alpha>) alphabet_csp, ('\<phi>,'\<alpha>) alphabet_csp) relation"
type_synonym ('\<phi>,'\<sigma>) predicate_csp  = "('\<phi>,'\<sigma>) alphabet_csp upred"

definition [uvar_defs]: "ref\<^sub>c = VAR csp_ref"
definition [uvar_defs]: "\<Sigma>\<^sub>c    = VAR more"

declare alpha_csp'.splits [alpha_splits]

lemma ref\<^sub>c_vwb_lens [simp]: "vwb_lens ref\<^sub>c"
  by (unfold_locales, simp_all add: ref\<^sub>c_def)

lemma csp_vwb_lens [simp]: "vwb_lens \<Sigma>\<^sub>c"
  by (unfold_locales, simp_all add: \<Sigma>\<^sub>c_def)
  
definition [uvar_defs]: "ref = (ref\<^sub>c ;\<^sub>L \<Sigma>\<^sub>R)"
definition [uvar_defs]: "\<Sigma>\<^sub>C   = (\<Sigma>\<^sub>c ;\<^sub>L \<Sigma>\<^sub>R)"

lemma ref_vwb_lens [simp]: "vwb_lens ref"
  by (simp add: ref_def)

lemma csp_lens_vwb_lens [simp]: "vwb_lens \<Sigma>\<^sub>C"
  by (simp add: \<Sigma>\<^sub>C_def)

lemma csp_lens_indep_ok [simp]: "\<Sigma>\<^sub>C \<bowtie> ok" "ok \<bowtie> \<Sigma>\<^sub>C"
  by (simp_all add: \<Sigma>\<^sub>C_def)

lemma csp_lens_indep_wait [simp]: "\<Sigma>\<^sub>C \<bowtie> wait" "wait \<bowtie> \<Sigma>\<^sub>C"
  by (simp_all add: \<Sigma>\<^sub>C_def)

abbreviation lift_csp :: "_ \<Rightarrow> _" ("\<lceil>_\<rceil>\<^sub>C") where
"\<lceil>P\<rceil>\<^sub>C \<equiv> P \<oplus>\<^sub>p (\<Sigma>\<^sub>C \<times>\<^sub>L \<Sigma>\<^sub>C)"

text {* The following function defines the parallel composition of two CSP event traces *}

fun trpar :: "'\<theta> event set \<Rightarrow> '\<theta> event list \<Rightarrow> '\<theta> event list \<Rightarrow> '\<theta> event list set" where
"trpar cs [] [] = {[]}" |
"trpar cs (e # t) [] = (if e \<in> cs then {[]} else {x. hd(x) = e \<and> tl(x) \<in> (trpar cs t [])})" |
"trpar cs [] (e # t) = (if e \<in> cs then {[]} else {x. hd(x) = e \<and> tl(x) \<in> (trpar cs [] t)})" |
"trpar cs (e\<^sub>1 # t\<^sub>1) (e\<^sub>2 # t\<^sub>2) =
    (if (e\<^sub>1 = e\<^sub>2)
       then 
         if e\<^sub>1 \<in> cs
         then {e\<^sub>1 # t | t. t \<in> (trpar cs t\<^sub>1 t\<^sub>2)}
         else {e\<^sub>1 # t | t. t \<in> (trpar cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))} \<union> {e\<^sub>1 # t | t. t \<in> (trpar cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2)}
       else
         if e\<^sub>1 \<in> cs
           then
             if e\<^sub>2 \<in> cs
               then {[]}
               else {e\<^sub>2 # t | t. t \<in> trpar cs (e\<^sub>1 # t\<^sub>1) (t\<^sub>2)}
           else
             if e\<^sub>2 \<in> cs
               then {e\<^sub>1 # t | t. t \<in> trpar cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)}
               else {e\<^sub>1 # t | t. t \<in> trpar cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)} \<union> {e\<^sub>2 # t | t. t \<in> trpar cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2})"

syntax
  "_utrpar" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("trpar\<^sub>u'(_,_,_')")

translations
  "trpar\<^sub>u(cs,t1,t2)" == "CONST trop CONST trpar cs t1 t2"

subsection {* Extra healthiness conditions and dependencies *}

definition [upred_defs]: "STOP = CSP1($ok\<acute> \<and> R3c($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition [upred_defs]: "SKIP = RH(\<exists> $ref \<bullet> CSP1(II))"

definition [upred_defs]: "CSP3(P) = (SKIP ;; P)"

definition [upred_defs]: "CSP4(P) = (P ;; SKIP)"

subsection {* Process constructs *}

definition [upred_defs]: "Stop = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition [upred_defs]: "Skip = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> (\<not> $wait\<acute>) \<and> \<lceil>II\<rceil>\<^sub>R))"

definition Guard :: "('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp" (infix "&\<^sub>u" 65)
where "g &\<^sub>u A = RH((g \<Rightarrow> \<not> A\<^sup>f\<^sub>f) \<turnstile> ((g \<and> A\<^sup>t\<^sub>f) \<or> ((\<not> g) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"

definition ExtChoice :: "('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp" (infixl "\<box>" 65)
where "A\<^sub>1 \<box> A\<^sub>2 = RH(\<not> A\<^sub>1\<^sup>f\<^sub>f \<and> \<not> A\<^sub>2\<^sup>f\<^sub>f \<turnstile> (A\<^sub>1\<^sup>t\<^sub>f \<and> A\<^sub>2\<^sup>t\<^sub>f) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (A\<^sub>1\<^sup>t\<^sub>f \<or> A\<^sub>2\<^sup>t\<^sub>f))"

definition do\<^sub>u :: "('\<theta> event, ('\<theta>,'\<alpha>) alphabet_csp \<times> ('\<theta>,'\<alpha>) alphabet_csp) uexpr \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp" where
"do\<^sub>u(e) = ($tr\<acute> =\<^sub>u $tr \<and> e \<notin>\<^sub>u $ref\<acute> \<triangleleft> $wait\<acute> \<triangleright> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>e\<rangle>)"

definition OutputCSP ::
  "('a, '\<theta>) chan \<Rightarrow> 
    ('a, ('\<theta>,'\<alpha>) alphabet_csp \<times> ('\<theta>,'\<alpha>) alphabet_csp) uexpr \<Rightarrow> 
    ('\<theta>, '\<alpha>) hrelation_csp \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_csp" where
"OutputCSP c v A = (RH(true \<turnstile> do\<^sub>u (c, v)\<^sub>e) ;; A)"

definition do\<^sub>I :: 
  "('a, '\<theta>) chan \<Rightarrow> 
    ('a, ('\<theta>,'\<alpha>) alphabet_csp) uvar \<Rightarrow>
    ('a \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_csp"
where "do\<^sub>I c x P = (($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c,\<guillemotleft>e\<guillemotright>)\<^sub>e}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
                   \<triangleleft> $wait\<acute> \<triangleright>
                   (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c,\<guillemotleft>e\<guillemotright>)\<^sub>e\<rangle>}\<^sub>u \<and> (c, $x\<acute>)\<^sub>e =\<^sub>u last\<^sub>u($tr\<acute>)))"

definition InputCSP :: 
  "('a::two, '\<theta>) chan \<Rightarrow> _ \<Rightarrow>
    ('a \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow> 
    (_ \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_csp) \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_csp"
where "InputCSP c x P A = (var\<^bsub>RDES\<^esub> x \<bullet> RH(true \<turnstile> do\<^sub>I c x P \<and> \<lceil>II\<rceil>\<^sub>R) ;; A(x))"

syntax
  "_csp_event"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>u _" [80,79] 80)
  "_csp_output" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!\<^sub>u'(_') \<rightarrow> _" [80,0,79] 80)
  "_csp_input"  :: "('a, '\<theta>) chan \<Rightarrow> id \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" ("_?\<^sub>u'(_ :/ _') \<rightarrow> _" [80,0,0,79] 80)

translations
  "c!\<^sub>u(v) \<rightarrow> A"     == "CONST OutputCSP c v A"
  "c \<rightarrow>\<^sub>u A"         == "CONST OutputCSP c ()\<^sub>u A"
  "c?\<^sub>u(x : P) \<rightarrow> A" => "CONST InputCSP c \<lceil>IDSTR(x)\<rceil>\<^sub>d (\<lambda> x. P) (\<lambda> x. A)"

text {* Merge predicate for CSP *}

(*
definition
  "CSPMerge(cs) =
    ((true \<turnstile>\<^sub>r (($wait\<^sub>r\<acute> =\<^sub>u ($0-wait\<^sub>r \<or> $1-wait\<^sub>r) \<and>
      $ref\<^sub>r\<acute> =\<^sub>u ($0-ref\<^sub>r \<union>\<^sub>u $1-ref\<^sub>r) \<and>
      ($tr\<^sub>r\<acute> - $tr\<^sub>r\<^sub><) \<in>\<^sub>u (trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, $0-tr\<^sub>r - $tr\<^sub>r\<^sub><, $1-tr\<^sub>r - $tr\<^sub>r\<^sub><)) \<and> 
      $0-tr\<^sub>r \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u $1-tr\<^sub>r \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>))) ;; SKIP)"

definition ParCSP :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> '\<theta> event set \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infixl "\<parallel>[_]\<^sub>C\<^sub>S\<^sub>P" 85)
where "P \<parallel>[cs]\<^sub>C\<^sub>S\<^sub>P Q = P \<parallel>\<^bsub>CSPMerge(cs)\<^esub> Q"
*)

subsection {* CSP laws *}

theorem STOP_is_Stop: "STOP = Stop"
  apply (rel_tac) 
  using minus_zero_eq apply blast+
done

lemma Skip_is_rea_skip: "Skip = II\<^sub>r"
  apply (rel_tac) using minus_zero_eq by blast+
  
(*
(* TODO : Circus merge predicate: *)

finition "MSt = undefined"

definition "M(cs) = ((($tr\<acute> - $\<^sub><tr) \<in>\<^sub>u (trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, $0.tr - $\<^sub><tr, $1.tr - $\<^sub><tr)) \<and> $0.tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u $1.tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<and> 
                    (  (($0.wait \<or> $1.wait) \<and> $ref\<acute> \<subseteq>\<^sub>u (($0.ref \<union>\<^sub>u $1.ref) \<inter>\<^sub>u \<guillemotleft>cs\<guillemotright>) \<union>\<^sub>u (($0.ref \<inter>\<^sub>u $1.ref) - \<guillemotleft>cs\<guillemotright>))
                       \<triangleleft> $wait\<acute> \<triangleright>
                       (\<not> $1.wait \<and> \<not> $2.wait \<and> MSt)
                    ))"
*)

end