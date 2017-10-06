theory Modelica_Discrete
  imports "../Modelica_Core"
begin
    
definition sample :: "real \<Rightarrow> real \<Rightarrow> _" where
[upred_defs]: "sample s p = (\<^bold>\<exists> n::nat \<bullet> &time =\<^sub>u \<guillemotleft>s\<guillemotright> + \<guillemotleft>of_nat n\<guillemotright>*\<guillemotleft>p\<guillemotright>)"
      
text {* The following function construct the overall event iteration guard by extracting the condition
  of each "when" construct in the model and taking their disjunction. In order words, if ever
  the condition of a "when" is satisfied then event iteration will begin. For us, event iteration
  begins whenever one of the guards changes state, either from false to true to true to false. 
  The latter will not actually yield any behaviour though as the discrete equations are only
  executed when their condition was false and is now true.*}
  
definition mevs :: "'c mblock \<Rightarrow> 'c mst_scheme hrel" where
[upred_defs]: "mevs M = foldr (\<lambda> g p. (\<lceil>g\<rceil>\<^sub>< \<noteq>\<^sub>u \<lceil>g\<rceil>\<^sub>>) \<or> p) (map fst (mgrds M)) false"
  
text {* The next construct describes the behaviour of event iteration. At each step, "when" guards
  which are satisfied giving rise to execution of the associated discrete equations. Once no
  more conditions are true, the iteration terminates. 

  This behaviour is constructed by folding the conditional construct over the list of guards.
  If a condition $p$ is satisfied, and it wasn't satisfied at the beginning of the interval,
  then the corresponding discrete equation $dq$ will be executed
  and the iteration will recurse. If no more events are possible then the else branch is reached
  and the iteration terminates. *}
  
definition mdeqs :: "('c::t2_space) mblock \<Rightarrow> 'c mrel" where
"mdeqs M = (\<mu>\<^sub>R X \<bullet> foldr (\<lambda> (p, dq) q. (dq ;; X) \<triangleleft> (\<lceil>p\<rceil>\<^sub>> \<and> \<lceil>\<not> p\<rceil>\<^sub>>\<lbrakk>&\<^bold>d/&\<^bold>c\<rbrakk>) \<triangleright>\<^sub>R q) (mgrds M) II\<^sub>R)" 
(*                      p is currently satisfied ---^     ^--- p wasn't satisfied previously *)

text {* The overall behaviour of a Modelica model is then given below. The initialisation is first
  executed. Then the main body of the model's behaviour is given. The continuous equation system
  is first activated, with the "when" guards attached. Once one of the guards changes its value
  from $false$ to $true -- that is when the guard was false in the initial state but is true in the final
  state -- the event iteration is activated. *}

definition mblock_sem :: "('c::t2_space) mblock \<Rightarrow> 'c mrel" ("\<lbrakk>_\<rbrakk>\<^sub>m") where
"\<lbrakk>M\<rbrakk>\<^sub>m = minit M ;; 
       (\<mu>\<^sub>R X \<bullet> \<^bold>d :=\<^sub>R &\<^bold>c ;; ((mceqs M) [mevs M]\<^sub>H (mdeqs M)) ;; X)"
  
definition mblock_sum :: "'c mblock \<Rightarrow> 'c mblock \<Rightarrow> 'c mblock" (infixl "\<oplus>\<^sub>m" 85) where
[upred_defs]:
"A \<oplus>\<^sub>m B = \<lparr> minit = (minit A \<and> minit B)
          , mceqs = (mceqs A \<and> mceqs B)
          , mgrds = (mgrds A @ mgrds B) \<rparr>"
  
lemma hEvolve_conj: "(&x \<leftarrow>\<^sub>H f(ti) \<and> &y \<leftarrow>\<^sub>H g(ti)) = ({&x,&y} \<leftarrow>\<^sub>H (f(ti), g(ti))\<^sub>u)"
  by (rel_auto)

definition Block :: "('c::t2_space) mblock" where
[upred_defs]:
  "Block = \<lparr> minit = ($st:\<^bold>c:time =\<^sub>u 0), mceqs = &time \<leftarrow>\<^sub>H (&time + \<guillemotleft>ti\<guillemotright>), mgrds = [] \<rparr>"
    
definition DiscreteBlock :: "real \<Rightarrow> real \<Rightarrow> (bool \<Longrightarrow> 'c mst_ext) \<Rightarrow> (bool \<Longrightarrow> 'c mst_ext) \<Rightarrow> ('d,'c::t2_space) mblock" where
[upred_defs]:
  "DiscreteBlock samplePeriod startTime sampleTrigger firstTrigger 
  = Block \<oplus>\<^sub>m 
    \<lparr> minit = true
    , mceqs = {&sampleTrigger, &firstTrigger} \<leftarrow>\<^sub>H (&sampleTrigger, &firstTrigger)\<^sub>u
    , mevs = sample startTime samplePeriod
    , mdeqs = undefined \<rparr>"

definition ZeroOrderHold :: 
  "real \<Rightarrow> real \<Rightarrow> 
  (real \<Longrightarrow> 'c mst_ext) \<Rightarrow> (real \<Longrightarrow> 'c mst_ext) \<Rightarrow> (real \<Longrightarrow> 'c mst_ext) \<Rightarrow> 
  ('d, 'c::t2_space) mblock" where
[upred_defs]:
  "ZeroOrderHold samplePeriod startTime u y ySample
  = Block \<oplus>\<^sub>m
    \<lparr> minit = \<lceil>$ySample =\<^sub>u $u \<and> $y =\<^sub>u $ySample\<rceil>\<^sub>C
    , mceqs = ({&y,&ySample} \<leftarrow>\<^sub>H (&ySample, &ySample)\<^sub>u)
    , mevs  = sample startTime samplePeriod
    , mdeqs = \<lceil>$ySample\<acute> =\<^sub>u $u\<rceil>\<^sub>C \<rparr>"
  
  
end