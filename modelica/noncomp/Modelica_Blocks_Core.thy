theory Modelica_Blocks_Core
  imports "../Modelica_Core"
begin
  
consts
  eps\<^sub>m :: real
  
type_synonym ('a, 'l, 'c) mcon = "('a \<Longrightarrow> ('l, 'c) mst_scheme)"
  
translations
  (type) "('a, 'l, 'c) mcon" <= (type) "('a \<Longrightarrow> ('l, 'c) mst_scheme)"
  
datatype ('l, 'c) mevgrd =
  TimeEvent (ofTimeEvent: "real \<Rightarrow> bool") | StateEvent (ofStateEvent: "(real, 'l, 'c) mexpr")
  
record (overloaded) ('l, 'c) mblock = 
  mieqs :: "('l, 'c) mst_scheme upred"               -- {* Initial Equations *}
  mdeqs :: "('l, 'c) mrel"                           -- {* Differential Equations *}
  maeqs :: "('l, 'c) mst_scheme upred"               -- {* Algebraic Equations *}
  mqeqs :: "('l, 'c) mst_scheme upred"               -- {* Discrete Equations *}
  mreqs :: "('l, 'c) mst_scheme hrel set"            -- {* Reset Equations *}
  mzcfs :: "(real, ('l, 'c) mst_scheme) uexpr set"   -- {* Zero Crossing Expressions *}
  mtevs :: "real \<Rightarrow> bool"                            -- {* Time Event Expressions *}
  
definition "EvInv eps z  = (\<lceil>z\<rceil>\<^sub>< >\<^sub>u -eps \<Rightarrow> \<lceil>z\<rceil>\<^sub>> >\<^sub>u -eps)"
definition "EvExit eps z = (\<lceil>z\<rceil>\<^sub>< >\<^sub>u 0 \<and> \<lceil>z\<rceil>\<^sub>> \<le>\<^sub>u 0)"
  
definition interleave_r :: "'a hrel set \<Rightarrow> 'a hrel" ("|||\<^sub>r _") where
"interleave_r A = (\<Sqinter> xs\<in>{xs. set(xs) = A} \<bullet> (;; p : xs \<bullet> p))" 
  
definition svid_fst :: "'a \<Longrightarrow> 'a \<times> 'b" ("\<^bold>v\<^sub>0") where
[lens_defs]: "svid_fst = fst\<^sub>L"

definition svid_snd :: "'b \<Longrightarrow> 'a \<times> 'b" ("\<^bold>v\<^sub>1") where
[lens_defs]: "svid_snd = snd\<^sub>L"

syntax
  "_svid_fst" :: "svid" ("\<^bold>v\<^sub>0")
  "_svid_snd" :: "svid" ("\<^bold>v\<^sub>1")  
  
translations
  "_svid_fst" == "CONST svid_fst"
  "_svid_snd" == "CONST svid_snd"
  
lemma skip_lens_ext_fst:
  "II \<oplus>\<^sub>p (\<^bold>v\<^sub>0 \<times>\<^sub>L \<^bold>v\<^sub>0) = ($\<^bold>v\<^sub>0\<acute> =\<^sub>u $\<^bold>v\<^sub>0)"
  by (rel_auto)
  
lemma fst_snd_eq_skip: 
  "($\<^bold>v\<^sub>0\<acute> =\<^sub>u $\<^bold>v\<^sub>0 \<and> $\<^bold>v\<^sub>1\<acute> =\<^sub>u $\<^bold>v\<^sub>1) = II"
  by (rel_auto)
    
lemma iterate_skip_lemma_1: 
  "($\<^bold>v\<^sub>0\<acute> =\<^sub>u $\<^bold>v\<^sub>0 \<and> $\<^bold>v\<^sub>1\<acute> =\<^sub>u $\<^bold>v\<^sub>0) ;; (II \<triangleleft> &\<^bold>v\<^sub>0 =\<^sub>u &\<^bold>v\<^sub>1 \<triangleright>\<^sub>r X) = \<^bold>v\<^sub>1 := &\<^bold>v\<^sub>0"
  by (rel_auto)
    
definition iterate :: "'a hrel \<Rightarrow> 'a hrel" where
"iterate P = (\<exists> $\<^bold>v\<^sub>1;$\<^bold>v\<^sub>1\<acute> \<bullet> (\<nu> X \<bullet> (P \<oplus>\<^sub>p (\<^bold>v\<^sub>0 \<times>\<^sub>L \<^bold>v\<^sub>0) \<and> $\<^bold>v\<^sub>1\<acute> =\<^sub>u $\<^bold>v\<^sub>0) ;; (II \<triangleleft> &\<^bold>v\<^sub>0 =\<^sub>u &\<^bold>v\<^sub>1 \<triangleright>\<^sub>r X))) \<restriction>\<^sub>e (\<^bold>v\<^sub>0 \<times>\<^sub>L \<^bold>v\<^sub>0)"
  
lemma iterate_II: "iterate II = II"
  by (simp add: iterate_def skip_lens_ext_fst iterate_skip_lemma_1 lfp_const, rel_auto)

definition mblock_comp :: "('l,'c) mblock \<Rightarrow> ('l,'c) mblock \<Rightarrow> ('l,'c) mblock" (infixr "\<oplus>\<^sub>m" 85) where
[upred_defs, mo_defs]:
"A \<oplus>\<^sub>m B = \<lparr> mieqs = (mieqs A \<and> mieqs B)
          , mdeqs = (mdeqs A \<and> mdeqs B)
          , maeqs = (maeqs A \<and> maeqs B)
          , mqeqs = (mqeqs A \<and> mqeqs B)
          , mreqs = (mreqs A \<union> mreqs B)
          , mzcfs = (mzcfs A \<union> mzcfs B)
          , mtevs = (\<lambda> t. mtevs A t \<or> mtevs B t) \<rparr>"
    
(* FIXME: Take account of time events here too. *)
    
definition mblock_sem :: 
  "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('l::t2_space,'c::t2_space) mblock \<Rightarrow> ('l,'c) mrel" ("'(_,_,_') \<Turnstile> \<lbrakk>_\<rbrakk>\<^sub>m") where
[upred_defs, mo_defs]:
"(\<epsilon>, s, q) \<Turnstile> \<lbrakk>M\<rbrakk>\<^sub>m =  
  (let I = mieqs M; D = mdeqs M; A = maeqs M; Q = mqeqs M; R = mreqs M; Z = mzcfs M; T = mtevs M in
   \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> [I \<and> Q \<and> A]\<^sub>C\<^sub>>) ;;
   (\<mu>\<^sub>R X \<bullet> ([D \<and> \<lceil>\<lceil>A\<rceil>\<^sub>>\<rceil>\<^sub>h \<and> q \<leftarrow>\<^sub>h $q]\<^sub>H 
                 inv (\<not> \<guillemotleft>T\<guillemotright>($mtime\<acute>)\<^sub>a) \<and> (\<And> z\<in>Z \<bullet> EvInv \<epsilon> z) 
                 until\<^sub>H ((\<guillemotleft>T\<guillemotright>($mtime\<acute>)\<^sub>a) \<or> (\<Or> z\<in>Z \<bullet> EvExit \<epsilon> z))) ;;
            \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> [iterate($s\<acute> =\<^sub>u $s \<and> \<lceil>Q\<rceil>\<^sub>> \<and> \<lceil>A\<rceil>\<^sub>>) ;; |||\<^sub>r R]\<^sub>C) ;; X))"

(*
definition timeGuards :: "('l, 'c) mblock \<Rightarrow> ((real \<Rightarrow> bool) \<times> ('l, 'c) mrel) list" where
[upred_defs, mo_defs]:
"timeGuards M = map (\<lambda> (g, e). (ofTimeEvent g, e)) (filter (is_TimeEvent \<circ> fst) (mgrds M))"

definition stateGuards :: "('l, 'c) mblock \<Rightarrow> ((real, 'l, 'c) mexpr \<times> ('l, 'c) mrel) list" where
[upred_defs, mo_defs]:
"stateGuards M = map (\<lambda> (g, e). (ofStateEvent g, e)) (filter (Not \<circ> is_TimeEvent \<circ> fst) (mgrds M))"

text {* A time event is triggered whenever the internal clock hits one of the instants in
  the given set of real number. *}
  
definition ti_event :: "(real \<Rightarrow> bool) \<Rightarrow> ('l, 'c) mst_scheme hrel" where
[upred_defs, mo_defs]: "ti_event P = (\<guillemotleft>P\<guillemotright>($time\<acute>)\<^sub>a)"
  
text {* State events are recorded whenever the given function crosses zero. A zero crossing event 
  is registered at some non-deterministically chosen instant when the function $zcf$ was previously 
  $\ge eps$ and it becomes less than $eps$. There is not one point which satisifies this specification 
  and then event can occur at any $t$ when $zcf(t) \in [0,eps)$ *}
  
definition zc_event :: "(real, ('l, 'c) mst_scheme) uexpr \<Rightarrow> ('l, 'c) mst_scheme hrel \<times> ('l, 'c) mst_scheme hrel" where
[upred_defs, mo_defs]: "zc_event zcf = (\<lceil>zcf\<rceil>\<^sub>> \<ge>\<^sub>u 0, (\<lceil>zcf \<ge>\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>\<rceil>\<^sub>< \<and> \<lceil>zcf <\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>\<rceil>\<^sub>>))"
  
text {* When the zero-crossing function was previously close to 0, but now it is sufficiently far
  away ($> eps$), a "phantom" event iteration executes which simply resets the previous value
  of the zero crossing function to that point so that any correspondonding when statement is
  re-enabled. *}

definition zc_restore :: "(real, ('l, 'c) mst_scheme) uexpr \<Rightarrow> ('l, 'c) mst_scheme hrel" where
[upred_defs, mo_defs]: "zc_restore zcf = (\<lceil>zcf <\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>\<rceil>\<^sub><  \<and> \<lceil>zcf \<ge>\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>\<rceil>\<^sub>>)"

definition minvs :: "('l, 'c) mblock \<Rightarrow> ('l, 'c) mst_scheme hrel" where
[upred_defs, mo_defs]: 
  "minvs M = foldr (op \<and>) (map (fst \<circ> zc_event \<circ> fst) (stateGuards M)) true"

definition mconds :: "('l, 'c) mblock \<Rightarrow> ('l, 'c) mst_scheme hrel" where
[upred_defs, mo_defs]: 
  "mconds M = (foldr (op \<or>) (map (snd \<circ> zc_event \<circ> fst) (stateGuards M)) false \<or>
               foldr (op \<or>) (map (zc_restore \<circ> fst) (stateGuards M)) false \<or> 
               foldr (op \<or>) (map (ti_event \<circ> fst) (timeGuards M)) false)"
  
text {* For discrete events, we first execute each time event up to once, and then enter iteration
  for the state events. *}
  
definition mdeqs :: "('l::t2_space,'c::t2_space) mblock \<Rightarrow> ('l,'c) mrel" where
[upred_defs, mo_defs]: "mdeqs M = 
   (foldr (op ;;) (map (\<lambda> (R, dq). dq \<triangleleft> \<guillemotleft>R\<guillemotright>(&\<^bold>c:time)\<^sub>a \<triangleright>\<^sub>R II\<^sub>R) (timeGuards M)) II\<^sub>R) ;;
   (\<mu>\<^sub>R X \<bullet> foldr 
           (\<lambda> (zcf, dq) q. 
           (dq ;; X) \<triangleleft> (\<lceil>zcf\<rceil>\<^sub>< \<ge>\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>)\<lbrakk>&\<^bold>d/&\<^bold>c\<rbrakk> \<and> (\<lceil>zcf\<rceil>\<^sub>< <\<^sub>u \<guillemotleft>eps\<^sub>m\<guillemotright>) \<triangleright>\<^sub>R q) (stateGuards M) II\<^sub>R)"
 (* zcf  previously not satisfied ---^               ^--- now it is *)

definition CoreTime :: "('l::t2_space,'c::t2_space) mblock" where
[upred_defs, mo_defs]:
  "CoreTime = \<lparr> minit = (&time =\<^sub>u 0), mceqs = &time \<leftarrow>\<^sub>h ($time + \<guillemotleft>ti\<guillemotright>), mgrds = [] \<rparr>"

definition mblock_comp :: "('l,'c) mblock \<Rightarrow> ('l,'c) mblock \<Rightarrow> ('l,'c) mblock" (infixr "\<oplus>\<^sub>m" 85) where
[upred_defs, mo_defs]:
"A \<oplus>\<^sub>m B = \<lparr> minit = (minit A \<and> minit B)
          , mceqs = (mceqs A \<and> mceqs B)
          , mgrds = (mgrds A @ mgrds B) \<rparr>"
  
definition mblock_sem :: "('l::t2_space,'c::t2_space) mblock \<Rightarrow> ('l,'c) mrel" ("\<lbrakk>_\<rbrakk>\<^sub>m") where
[upred_defs, mo_defs]:
"\<lbrakk>M\<rbrakk>\<^sub>m = (let M' = CoreTime \<oplus>\<^sub>m M in
        \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> [minit M']\<^sub>C\<^sub>>) ;; 
        (\<mu>\<^sub>R X \<bullet> \<^bold>d :=\<^sub>R &\<^bold>c ;; ([mceqs M']\<^sub>H [minvs M' | mconds M']\<^sub>H\<^sup>+ (mdeqs M')) ;; X))"
*)
  
default_sort t2_space

end
