section {* Theory of CSP *}

theory utp_csp
  imports utp_reactive utp_procedure
begin

subsection {* Preliminaries *}

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

subsection {* Healthiness conditions *}

definition "CSP1(P) = (P \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

text {* CSP2 is just H2 since the type system will automatically have J identifying the reactive
        variables as required. *}

definition "CSP2(P) = H2(P)"

definition "SKIP = RH(\<exists> $ref \<bullet> II)"

definition "CSP3(P) = (SKIP ;; P)"

definition "CSP4(P) = (P ;; SKIP)"

subsection {* Process constructs *}

abbreviation wait_f::"('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("_\<^sub>f" [1000] 1000)
where "wait_f R \<equiv> R\<lbrakk>false/$wait\<acute>\<rbrakk>"

abbreviation wait_t::"('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("_\<^sub>t" [1000] 1000)
where "wait_t R \<equiv> R\<lbrakk>true/$wait\<acute>\<rbrakk>"

definition "Stop = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>))"

definition "Skip = RH(true \<turnstile> ($tr\<acute> =\<^sub>u $tr \<and> (\<not> $wait\<acute>) \<and> \<lceil>II\<rceil>\<^sub>R))"

definition "Chaos = RH(false \<turnstile> true)"

definition Guard :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infix "&\<^sub>u" 65)
where "g &\<^sub>u A = RH((g \<Rightarrow> \<not> A\<^sup>f\<^sub>f) \<turnstile> ((g \<and> A\<^sup>t\<^sub>f) \<or> ((\<not> g) \<and> $tr\<acute> =\<^sub>u $tr \<and> $wait\<acute>)))"

definition ExtChoice :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infixl "\<box>" 65)
where "A\<^sub>1 \<box> A\<^sub>2 = RH(\<not> A\<^sub>1\<^sup>f\<^sub>f \<and> \<not> A\<^sub>2\<^sup>f\<^sub>f \<turnstile> (A\<^sub>1\<^sup>t\<^sub>f \<and> A\<^sub>2\<^sup>t\<^sub>f) \<triangleleft> $tr =\<^sub>u $tr\<acute> \<and> $wait\<acute> \<triangleright> (A\<^sub>1\<^sup>t\<^sub>f \<or> A\<^sub>2\<^sup>t\<^sub>f))"

definition do\<^sub>u :: "('\<theta> event, ('\<theta>,'\<alpha>) alphabet_rp \<times> ('\<theta>,'\<alpha>) alphabet_rp) uexpr \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" where
"do\<^sub>u(e) = ($tr\<acute> =\<^sub>u $tr \<and> e \<notin>\<^sub>u $ref\<acute> \<triangleleft> $wait\<acute> \<triangleright> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<langle>e\<rangle>)"

definition OutputCSP ::
  "('a, '\<theta>) chan \<Rightarrow> 
    ('a, ('\<theta>,'\<alpha>) alphabet_rp \<times> ('\<theta>,'\<alpha>) alphabet_rp) uexpr \<Rightarrow> 
    ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_rp" where
"OutputCSP c v A = (RH(true \<turnstile> do\<^sub>u (c, v)\<^sub>e) ;; A)"

definition do\<^sub>I :: 
  "('a, '\<theta>) chan \<Rightarrow> 
    ('a, ('\<theta>,'\<alpha>) alphabet_rp) uvar \<Rightarrow>
    ('a \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp) \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_rp"
where "do\<^sub>I c x P = (($tr\<acute> =\<^sub>u $tr \<and> {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> (c,\<guillemotleft>e\<guillemotright>)\<^sub>e}\<^sub>u \<inter>\<^sub>u $ref\<acute> =\<^sub>u {}\<^sub>u)
                   \<triangleleft> $wait\<acute> \<triangleright>
                   (($tr\<acute> - $tr) \<in>\<^sub>u {e : \<guillemotleft>\<delta>\<^sub>u(c)\<guillemotright> | P(e) \<bullet> \<langle>(c,\<guillemotleft>e\<guillemotright>)\<^sub>e\<rangle>}\<^sub>u \<and> (c, $x\<acute>)\<^sub>e =\<^sub>u last\<^sub>u($tr\<acute>)))"

definition InputCSP :: 
  "('a::continuum, '\<theta>) chan \<Rightarrow> string \<Rightarrow>
    ('a \<Rightarrow> ('\<theta>, '\<alpha>::vst) hrelation_rp) \<Rightarrow> 
    ('a dvar \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp) \<Rightarrow>
    ('\<theta>, '\<alpha>) hrelation_rp"
where "InputCSP c x P A = (var_block x (\<lambda> x. RH(true \<turnstile> do\<^sub>I c (x\<up>) P \<and> \<lceil>II\<rceil>\<^sub>R) ;; A(x)))"

syntax
  "_csp_event"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow>\<^sub>u _" [80,79] 80)
  "_csp_output" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_!\<^sub>u'(_') \<rightarrow> _" [80,0,79] 80)
  "_csp_input"  :: "('a, '\<theta>) chan \<Rightarrow> id \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" ("_?\<^sub>u'(_ :/ _') \<rightarrow> _" [80,0,0,79] 80)

translations
  "c!\<^sub>u(v) \<rightarrow> A"     == "CONST OutputCSP c v A"
  "c \<rightarrow>\<^sub>u A"         == "CONST OutputCSP c ()\<^sub>u A"
  "c?\<^sub>u(x : P) \<rightarrow> A" => "CONST InputCSP c IDSTR(x) (\<lambda> x. P) (\<lambda> x. A)"

text {* Merge predicate for CSP *}

definition
  "CSPMerge(cs) =
    (($ok\<acute> =\<^sub>u ($0.ok \<and> $1.ok) \<and>
      $wait\<acute> =\<^sub>u ($0.wait \<or> $1.wait) \<and>
      $ref\<acute> =\<^sub>u ($0.ref \<union>\<^sub>u $1.ref) \<and>
      ($tr\<acute> - $\<^sub><tr) \<in>\<^sub>u (trpar\<^sub>u(\<guillemotleft>cs\<guillemotright>, $0.tr - $\<^sub><tr, $1.tr - $\<^sub><tr)) \<and> 
      $0.tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright> =\<^sub>u $1.tr \<restriction>\<^sub>u \<guillemotleft>cs\<guillemotright>) ;; SKIP)"

definition ParCSP :: "('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> '\<theta> event set \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp \<Rightarrow> ('\<theta>, '\<alpha>) hrelation_rp" (infixl "\<parallel>[_]\<^sub>C\<^sub>S\<^sub>P" 85)
where "P \<parallel>[cs]\<^sub>C\<^sub>S\<^sub>P Q = P \<parallel>\<^bsub>CSPMerge(cs)\<^esub> Q"

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