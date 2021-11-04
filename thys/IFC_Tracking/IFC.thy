section \<open>Definitions\<close>

text \<open>
This section contains all necessary definitions of this development. Section~\ref{sec:pm} contains 
the structural definition of our program model which includes the security specification as well 
as abstractions of control flow and data.  Executions of our program model are defined in 
section~\ref{sec:ex}.  Additional well-formedness properties are defined in section~\ref{sec:wf}. 
Our security property is defined in section~\ref{sec:sec}.  Our characterisation of how information
is propagated by executions of our program model is defined in section~\ref{sec:char-cp}, for which
the correctness result can be found in section~\ref{sec:cor-cp}.  Section~\ref{sec:char-scp} contains
an additional approximation of this characterisation whose correctness result can be found in 
section~\ref{sec:cor-scp}.
\<close>


theory IFC
imports Main
begin

subsection \<open>Program Model\<close>
text_raw \<open>\label{sec:pm}\<close>

text \<open>Our program model contains all necessary components for the remaining development and consists of:\<close>

record ('n, 'var, 'val, 'obs) ifc_problem =  
\<comment> \<open>A set of nodes representing program locations:\<close>
  nodes :: \<open>'n set\<close>
\<comment> \<open>An initial node where all executions start:\<close>
  entry :: \<open>'n\<close>
\<comment> \<open>A final node where executions can terminate:\<close>
  return :: \<open>'n\<close>
\<comment> \<open>An abstraction of control flow in the form of an edge relation:\<close>
  edges :: \<open>('n \<times> 'n) set\<close>
\<comment> \<open>An abstraction of variables written at program locations:\<close>
  writes :: \<open>'n \<Rightarrow> 'var set\<close>
\<comment> \<open>An abstraction of variables read at program locations:\<close>
  reads :: \<open>'n \<Rightarrow> 'var set\<close>
\<comment> \<open>A set of variables containing the confidential information in the initial state:\<close>
  hvars :: \<open>'var set\<close>
\<comment> \<open>A step function on location state pairs:\<close>
  step :: \<open>('n \<times> ('var \<Rightarrow> 'val)) \<Rightarrow> ('n \<times> ('var \<Rightarrow> 'val))\<close>
\<comment> \<open>An attacker model producing observations based on the reached state at certain locations:\<close>
  att :: \<open>'n \<rightharpoonup> (('var \<Rightarrow> 'val) \<Rightarrow> 'obs)\<close>

text \<open>We fix a program in the following in order to define the central concepts.  
The necessary well-formedness assumptions will be made in section~\ref{sec:wf}.\<close>
locale IFC_def =
fixes prob :: \<open>('n, 'var, 'val, 'obs) ifc_problem\<close>
begin  

text \<open>Some short hands to the components of the program which we will utilise exclusively in the following.\<close>
definition nodes where \<open>nodes = ifc_problem.nodes prob\<close>
definition entry where \<open>entry = ifc_problem.entry prob\<close>
definition return where \<open>return = ifc_problem.return prob\<close>
definition edges where \<open>edges = ifc_problem.edges prob\<close>
definition writes where \<open>writes = ifc_problem.writes prob\<close>
definition reads where \<open>reads = ifc_problem.reads prob\<close>
definition hvars where \<open>hvars = ifc_problem.hvars prob\<close>
definition step where \<open>step = ifc_problem.step prob\<close>
definition att where \<open>att = ifc_problem.att prob\<close>

text \<open>The components of the step function for convenience.\<close>
definition suc where \<open>suc n \<sigma> = fst (step (n, \<sigma>))\<close>
definition sem where \<open>sem n \<sigma> = snd (step (n, \<sigma>))\<close>

lemma step_suc_sem: \<open>step (n,\<sigma>) = (suc n \<sigma>, sem n \<sigma>)\<close> unfolding suc_def sem_def by auto


subsubsection \<open>Executions\<close>
text \<open>\label{sec:ex}\<close>
text \<open>In order to define what it means for a program to be well-formed, we first require concepts 
of executions and program paths.\<close>

text \<open>The sequence of nodes visited by the execution corresponding to an input state.\<close>
definition path where
\<open>path \<sigma> k= fst ((step^^k) (entry,\<sigma>))\<close>

text \<open>The sequence of states visited by the execution corresponding to an input state.\<close>
definition kth_state ( \<open>_\<^bsup>_\<^esup>\<close> [111,111] 110) where 
\<open>\<sigma>\<^bsup>k\<^esup> = snd ((step^^k) (entry,\<sigma>))\<close>

text \<open>A predicate asserting that a sequence of nodes is a valid program path according to the
control flow graph.\<close>

definition is_path where
\<open>is_path \<pi> = (\<forall> n. (\<pi> n, \<pi> (Suc n)) \<in> edges)\<close> 
end

subsubsection \<open>Well-formed Programs\<close>
text_raw \<open>\label{sec:wf}\<close>

text \<open>The following assumptions define our notion of valid programs.\<close>
locale IFC = IFC_def \<open>prob\<close> for prob:: \<open>('n, 'var, 'val, 'out) ifc_problem\<close> +
assumes ret_is_node[simp,intro]: \<open>return \<in> nodes\<close>
and entry_is_node[simp,intro]: \<open>entry \<in> nodes\<close>
and writes: \<open>\<And> v n. (\<exists>\<sigma>. \<sigma> v \<noteq> sem n \<sigma> v) \<Longrightarrow> v \<in> writes n\<close>
and writes_return: \<open>writes return = {}\<close>
and uses_writes: \<open>\<And> n \<sigma> \<sigma>'. (\<forall> v \<in> reads n. \<sigma> v = \<sigma>' v) \<Longrightarrow> \<forall> v \<in> writes n. sem n \<sigma> v = sem n \<sigma>' v\<close>
and uses_suc: \<open>\<And> n \<sigma> \<sigma>'. (\<forall> v \<in> reads n. \<sigma> v = \<sigma>' v) \<Longrightarrow> suc n \<sigma> = suc n \<sigma>'\<close>
and uses_att: \<open>\<And> n f \<sigma> \<sigma>'. att n = Some f \<Longrightarrow> (\<forall> v \<in> reads n. \<sigma> v = \<sigma>' v) \<Longrightarrow> f \<sigma> = f \<sigma>'\<close>
and edges_complete[intro,simp]: \<open>\<And>m \<sigma>. m \<in> nodes \<Longrightarrow> (m,suc m \<sigma>) \<in> edges\<close>
and edges_return : \<open>\<And>x. (return,x) \<in> edges \<Longrightarrow> x = return \<close>
and edges_nodes: \<open>edges \<subseteq> nodes \<times> nodes\<close>    
and reaching_ret: \<open>\<And> x. x \<in> nodes \<Longrightarrow> \<exists> \<pi> n. is_path \<pi> \<and> \<pi> 0 = x \<and> \<pi> n = return\<close>


subsection \<open>Security\<close>
text_raw \<open>\label{sec:sec}\<close>

text \<open>We define our notion of security, which corresponds to what Bohannon et al.~\cite{Bohannon:2009:RN:1653662.1653673} 
refer to as indistinguishable security.  In order to do so we require notions of observations made
by the attacker, termination and equivalence of input states.\<close>

context IFC_def
begin

subsubsection \<open>Observations\<close>
text_raw \<open>\label{sec:obs}\<close>

text \<open>The observation made at a given index within an execution.\<close>
definition obsp where
\<open>obsp \<sigma> k = (case att(path \<sigma> k) of Some f \<Rightarrow> Some (f (\<sigma>\<^bsup>k\<^esup>)) | None \<Rightarrow> None)\<close>

text \<open>The indices within a path where an observation is made.\<close>
definition obs_ids :: \<open>(nat \<Rightarrow> 'n) \<Rightarrow> nat set\<close> where
\<open>obs_ids \<pi> = {k. att (\<pi> k) \<noteq> None}\<close>

text \<open>A predicate relating an observable index to the number of observations made before.\<close>
definition is_kth_obs :: \<open>(nat \<Rightarrow> 'n) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close>where
\<open>is_kth_obs \<pi> k i = (card (obs_ids \<pi> \<inter> {..<i}) = k \<and> att (\<pi> i) \<noteq>  None)\<close>

text \<open>The final sequence of observations made for an execution.\<close>
definition obs where
\<open>obs \<sigma> k = (if (\<exists>i. is_kth_obs (path \<sigma>) k i) then obsp \<sigma> (THE i. is_kth_obs (path \<sigma>) k i) else None)\<close>

text \<open>Comparability of observations.\<close>
definition obs_prefix :: \<open>(nat \<Rightarrow> 'obs option) \<Rightarrow> (nat \<Rightarrow> 'obs option) \<Rightarrow> bool\<close> (infix \<open>\<lesssim>\<close> 50) where
\<open>a \<lesssim> b \<equiv> \<forall> i. a i \<noteq> None \<longrightarrow> a i = b i\<close>

definition obs_comp (infix \<open>\<approx>\<close> 50) where
\<open>a \<approx> b \<equiv> a \<lesssim> b \<or> b \<lesssim> a\<close>

subsubsection \<open>Low equivalence of input states\<close>

definition restrict (infix \<open>\<restriction>\<close> 100 ) where
\<open>f\<restriction>U = (\<lambda> n. if n \<in> U then f n else undefined)\<close>

text \<open>Two input states are low equivalent if they coincide on the non high variables.\<close>
definition loweq (infix \<open>=\<^sub>L\<close> 50) 
where \<open>\<sigma> =\<^sub>L \<sigma>' = (\<sigma>\<restriction>(-hvars) = \<sigma>'\<restriction>(-hvars))\<close>

subsubsection \<open>Termination\<close>

text \<open>An execution terminates iff it reaches the terminal node at any point.\<close>
definition terminates where
\<open>terminates \<sigma> \<equiv> \<exists> i. path \<sigma> i = return\<close>


subsubsection \<open>Security Property\<close>
text \<open>The fixed program is secure if and only if for all pairs of low equivalent inputs the observation
sequences are comparable and if the execution for an input state terminates then the observation sequence 
is not missing any observations.\<close>

definition secure where
\<open>secure \<equiv> \<forall> \<sigma> \<sigma>'. \<sigma> =\<^sub>L \<sigma>' \<longrightarrow> (obs \<sigma> \<approx> obs \<sigma>' \<and> (terminates \<sigma> \<longrightarrow> obs \<sigma>' \<lesssim> obs \<sigma>))\<close>



subsection \<open>Characterisation of Information Flows\<close>
text \<open>We now define our characterisation of information flows which tracks data and control dependencies 
within executions. To do so we first require some additional concepts.\<close>

subsubsection \<open>Post Dominance\<close>
text \<open>We utilise the post dominance relation in order to define control dependence.\<close>

text \<open>The basic post dominance relation.\<close>
definition is_pd (infix \<open>pd\<rightarrow>\<close> 50) where 
\<open>y pd\<rightarrow> x \<longleftrightarrow> x \<in> nodes \<and> (\<forall> \<pi> n. is_path \<pi> \<and> \<pi> (0::nat) = x \<and> \<pi> n = return \<longrightarrow> (\<exists>k\<le>n. \<pi> k = y))\<close>

text \<open>The immediate post dominance relation.\<close>
definition is_ipd (infix \<open>ipd\<rightarrow>\<close> 50)where
\<open>y ipd\<rightarrow> x \<longleftrightarrow> x \<noteq> y \<and> y pd\<rightarrow> x \<and> (\<forall> z. z\<noteq>x \<and> z pd\<rightarrow> x \<longrightarrow> z pd\<rightarrow> y)\<close>

definition ipd where 
\<open>ipd x = (THE y. y ipd\<rightarrow> x)\<close>

text \<open>The post dominance tree.\<close>
definition pdt where
\<open>pdt = {(x,y). x\<noteq>y \<and> y pd\<rightarrow> x}\<close>


subsubsection \<open>Control Dependence\<close>

text \<open>An index on an execution path is control dependent upon another if the path does not visit
the immediate post domiator of the node reached by the smaller index.\<close>
definition is_cdi (\<open>_ cd\<^bsup>_\<^esup>\<rightarrow> _\<close> [51,51,51]50) where
\<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k \<longleftrightarrow> is_path \<pi> \<and> k < i \<and> \<pi> i \<noteq> return \<and> (\<forall> j \<in> {k..i}. \<pi> j \<noteq> ipd (\<pi> k))\<close> 

text \<open>The largest control dependency of an index is the immediate control dependency.\<close>
definition is_icdi (\<open>_ icd\<^bsup>_\<^esup>\<rightarrow> _\<close> [51,51,51]50) where
\<open>n icd\<^bsup>\<pi>\<^esup>\<rightarrow> n' \<longleftrightarrow> is_path \<pi> \<and> n cd\<^bsup>\<pi>\<^esup>\<rightarrow> n' \<and> (\<forall> m \<in> {n'<..<n}.\<not> n cd\<^bsup>\<pi>\<^esup>\<rightarrow> m)\<close>

text \<open>For the definition of the control slice, which we will define next, we require the uniqueness 
of the immediate control dependency.\<close>

lemma icd_uniq: assumes  \<open>m icd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> \<open> m icd\<^bsup>\<pi>\<^esup>\<rightarrow> n'\<close> shows \<open>n = n'\<close>
proof - 
  {
    fix n n' assume *: \<open>m icd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> \<open> m icd\<^bsup>\<pi>\<^esup>\<rightarrow> n'\<close> \<open>n < n'\<close>
    have \<open>n'<m\<close> using * unfolding is_icdi_def is_cdi_def by auto    
    hence \<open>\<not> m cd\<^bsup>\<pi>\<^esup>\<rightarrow> n'\<close> using * unfolding is_icdi_def by auto
    with *(2) have \<open>False\<close> unfolding is_icdi_def by auto
  }
  thus ?thesis using assms by (metis linorder_neqE_nat)
qed


subsubsection \<open>Control Slice\<close>
text \<open>We utilise the control slice, that is the sequence of nodes visited by the control dependencies 
of an index, to match indices between executions.\<close>

function cs:: \<open>(nat \<Rightarrow> 'n) \<Rightarrow> nat \<Rightarrow> 'n list\<close> (\<open>cs\<^bsup>_\<^esup> _\<close> [51,70] 71) where
\<open>cs\<^bsup>\<pi>\<^esup> n = (if (\<exists> m. n icd\<^bsup>\<pi>\<^esup>\<rightarrow> m) then (cs \<pi> (THE m. n icd\<^bsup>\<pi>\<^esup>\<rightarrow> m))@[\<pi> n] else [\<pi> n])\<close> 
by pat_completeness auto  
termination \<open>cs\<close> proof
  show \<open>wf (measure snd)\<close> by simp
  fix \<pi> n  
  define m where \<open>m == (The (is_icdi n \<pi>))\<close>
  assume \<open>Ex (is_icdi n \<pi>)\<close> 
  hence \<open>n icd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> unfolding m_def by (metis (full_types) icd_uniq theI')
  hence \<open>m < n\<close> unfolding is_icdi_def is_cdi_def by simp
  thus \<open>((\<pi>, The (is_icdi n \<pi>)), \<pi>, n) \<in> measure snd\<close> by (metis in_measure m_def snd_conv)
qed

inductive cs_less (infix \<open>\<prec>\<close> 50) where
\<open>length xs < length ys \<Longrightarrow> take (length xs) ys = xs  \<Longrightarrow> xs \<prec> ys\<close>     

definition cs_select (infix \<open>\<exclamdown>\<close> 50) where
\<open>\<pi>\<exclamdown>xs = (THE k. cs\<^bsup>\<pi>\<^esup> k = xs)\<close>


subsubsection \<open>Data Dependence\<close>

text \<open>Data dependence is defined straight forward. An index is data dependent upon another, 
if the index reads a variable written by the earlier index and the variable in question has not 
been written by any index in between.\<close>
definition is_ddi (\<open>_ dd\<^bsup>_,_\<^esup>\<rightarrow> _\<close> [51,51,51,51] 50) where
\<open>n dd\<^bsup>\<pi>,v\<^esup>\<rightarrow> m \<longleftrightarrow> is_path \<pi> \<and> m < n \<and> v \<in> reads (\<pi> n) \<inter> (writes (\<pi> m)) \<and> (\<forall> l \<in> {m<..<n}. v \<notin> writes (\<pi> l))\<close>



subsubsection \<open>Characterisation via Critical Paths\<close>
text_raw \<open>\label{sec:char-cp}\<close>
text \<open>With the above we define the set of critical paths which as we will prove characterise the matching
points in executions where diverging data is read.\<close>

inductive_set cp where

\<comment> \<open>Any pair of low equivalent input states and indices where a diverging high variable is first
read is critical.\<close>

\<open>\<lbrakk>\<sigma> =\<^sub>L \<sigma>'; 
  cs\<^bsup>path \<sigma>\<^esup> n = cs\<^bsup>path \<sigma>'\<^esup> n'; 
  h \<in> reads(path \<sigma> n); 
  (\<sigma>\<^bsup>n\<^esup>) h \<noteq> (\<sigma>'\<^bsup>n'\<^esup>) h; 
  \<forall> k<n. h\<notin>writes(path \<sigma> k); 
  \<forall> k'<n'. h\<notin>writes(path \<sigma>' k')
 \<rbrakk> \<Longrightarrow> ((\<sigma>,n),(\<sigma>',n')) \<in> cp\<close> |

\<comment> \<open>If from a pair of critical indices in two executions there exist data dependencies from both
indices to a pair of matching indices where the variable diverges, the later pair of indices is critical.\<close>

\<open>\<lbrakk>((\<sigma>,k),(\<sigma>',k')) \<in> cp; 
  n dd\<^bsup>path \<sigma>,v\<^esup>\<rightarrow> k;
  n' dd\<^bsup>path \<sigma>',v\<^esup>\<rightarrow> k'; 
  cs\<^bsup>path \<sigma>\<^esup> n = cs\<^bsup>path \<sigma>'\<^esup> n'; 
  (\<sigma>\<^bsup>n\<^esup>) v \<noteq> (\<sigma>'\<^bsup>n'\<^esup>) v
 \<rbrakk> \<Longrightarrow> ((\<sigma>,n),(\<sigma>',n')) \<in> cp\<close> |

\<comment> \<open>If from a pair of critical indices the executions take different branches and one of the critical 
indices is a control dependency of an index that is data dependency of a matched index where diverging 
data is read and the variable in question is not written by the other execution after the executions
first reached matching indices again, then the later matching pair of indices is critical.\<close>

\<open>\<lbrakk>((\<sigma>,k),(\<sigma>',k')) \<in> cp; 
  n dd\<^bsup>path \<sigma>,v\<^esup>\<rightarrow> l; 
  l cd\<^bsup>path \<sigma>\<^esup>\<rightarrow> k; 
  cs\<^bsup>path \<sigma>\<^esup> n = cs\<^bsup>path \<sigma>'\<^esup> n'; 
  path \<sigma> (Suc k) \<noteq> path \<sigma>' (Suc k'); 
  (\<sigma>\<^bsup>n\<^esup>) v \<noteq> (\<sigma>'\<^bsup>n'\<^esup>) v; 
  \<forall>j'\<in>{(LEAST i'. k' < i' \<and> (\<exists>i. cs\<^bsup>path \<sigma>\<^esup> i = cs\<^bsup>path \<sigma>'\<^esup> i'))..<n'}. v\<notin>writes (path \<sigma>' j')
 \<rbrakk> \<Longrightarrow> ((\<sigma>,n),(\<sigma>',n')) \<in> cp\<close> | 

\<comment> \<open>The relation is symmetric.\<close>

\<open>\<lbrakk>((\<sigma>,k),(\<sigma>',k')) \<in> cp\<rbrakk> \<Longrightarrow> ((\<sigma>',k'),(\<sigma>,k)) \<in> cp\<close>


text \<open>Based on the set of critical paths, the critical observable paths are those that either directly 
reach observable nodes or are diverging control dependencies of an observable index.\<close>

inductive_set cop where
\<open>\<lbrakk>((\<sigma>,n),(\<sigma>',n')) \<in> cp;
  path \<sigma> n \<in> dom att
 \<rbrakk> \<Longrightarrow> ((\<sigma>,n),(\<sigma>',n')) \<in> cop\<close> |

\<open>\<lbrakk>((\<sigma>,k),(\<sigma>',k')) \<in> cp; 
  n cd\<^bsup>path \<sigma>\<^esup>\<rightarrow> k; 
  path \<sigma> (Suc k) \<noteq> path \<sigma>' (Suc k'); 
  path \<sigma> n \<in> dom att
 \<rbrakk> \<Longrightarrow> ((\<sigma>,n),(\<sigma>',k')) \<in> cop\<close>



subsubsection \<open>Approximation via Single Critical Paths\<close>
text_raw \<open>\label{sec:char-scp}\<close>

text \<open>For applications we also define a single execution approximation.\<close>

definition is_dcdi_via (\<open>_ dcd\<^bsup>_,_\<^esup>\<rightarrow> _ via _ _\<close> [51,51,51,51,51,51] 50) where
\<open>n dcd\<^bsup>\<pi>,v\<^esup>\<rightarrow> m via \<pi>' m' = (is_path \<pi> \<and> m < n \<and> (\<exists> l' n'. cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m' \<and> cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n' \<and> n' dd\<^bsup>\<pi>',v\<^esup>\<rightarrow> l' \<and> l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> m') \<and> (\<forall> l \<in> {m..<n}. v\<notin> writes(\<pi> l)))\<close>

inductive_set scp where
\<open>\<lbrakk>h \<in> hvars; h \<in> reads (path \<sigma> n); (\<forall> k<n. h\<notin> writes(path \<sigma> k))\<rbrakk> \<Longrightarrow> (path \<sigma>,n) \<in> scp\<close> |
\<open>\<lbrakk>(\<pi>,m) \<in> scp; n cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<rbrakk> \<Longrightarrow> (\<pi>,n) \<in> scp\<close>|
\<open>\<lbrakk>(\<pi>,m) \<in> scp; n dd\<^bsup>\<pi>,v\<^esup>\<rightarrow> m\<rbrakk> \<Longrightarrow> (\<pi>,n) \<in> scp\<close>|
\<open>\<lbrakk>(\<pi>,m) \<in> scp; (\<pi>',m') \<in> scp; n dcd\<^bsup>\<pi>,v\<^esup>\<rightarrow> m via \<pi>' m'\<rbrakk> \<Longrightarrow> (\<pi>,n) \<in> scp\<close>

inductive_set scop where
\<open>\<lbrakk>(\<pi>,n) \<in> scp; \<pi> n \<in> dom att\<rbrakk> \<Longrightarrow> (\<pi>,n) \<in> scop\<close>



subsubsection \<open>Further Definitions\<close>
text \<open>The following concepts are utilised by the proofs.\<close>

inductive contradicts (infix \<open>\<cc>\<close> 50) where
\<open>\<lbrakk>cs\<^bsup>\<pi>'\<^esup> k' \<prec> cs\<^bsup>\<pi>\<^esup> k ; \<pi> = path \<sigma>;  \<pi>' = path \<sigma>' ; \<pi> (Suc (\<pi>\<exclamdown>cs\<^bsup>\<pi>'\<^esup> k')) \<noteq> \<pi>' (Suc k')\<rbrakk> \<Longrightarrow> (\<sigma>', k') \<cc> (\<sigma>, k)\<close>|
\<open>\<lbrakk>cs\<^bsup>\<pi>'\<^esup> k' = cs\<^bsup>\<pi>\<^esup> k ; \<pi> = path \<sigma>;  \<pi>' = path \<sigma>' ; \<sigma>\<^bsup>k\<^esup> \<restriction> (reads (\<pi> k)) \<noteq> \<sigma>'\<^bsup>k'\<^esup> \<restriction> (reads (\<pi> k))\<rbrakk> \<Longrightarrow> (\<sigma>',k') \<cc> (\<sigma>,k)\<close>

definition path_shift (infixl \<open>\<guillemotleft>\<close> 51) where 
[simp]: \<open>\<pi>\<guillemotleft>m = (\<lambda> n. \<pi> (m+n))\<close> 

definition path_append :: \<open>(nat \<Rightarrow> 'n) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'n) \<Rightarrow> (nat \<Rightarrow> 'n)\<close> (\<open>_ @\<^bsup>_\<^esup> _\<close> [0,0,999] 51) where
[simp]: \<open>\<pi> @\<^bsup>m\<^esup> \<pi>' = (\<lambda>n.(if n \<le> m then \<pi> n else \<pi>' (n-m)))\<close> 

definition eq_up_to :: \<open>(nat \<Rightarrow> 'n) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'n) \<Rightarrow> bool\<close> (\<open>_ =\<^bsub>_\<^esub> _\<close> [55,55,55] 50) where
\<open>\<pi> =\<^bsub>k\<^esub> \<pi>' = (\<forall> i \<le> k. \<pi> i = \<pi>' i)\<close>

end (* End of locale IFC_def *)




section \<open>Proofs\<close>
text_raw \<open>\label{sec:proofs}\<close>

subsection \<open>Miscellaneous Facts\<close>

lemma option_neq_cases: assumes \<open>x \<noteq> y\<close> obtains (none1) a where \<open>x = None\<close> \<open>y = Some a\<close> | (none2) a where \<open>x = Some a\<close> \<open>y = None\<close> | (some) a b where \<open>x = Some a\<close> \<open>y = Some b\<close> \<open>a \<noteq> b\<close> using assms by fastforce

lemmas nat_sym_cases[case_names less sym eq] = linorder_less_wlog

lemma mod_bound_instance: assumes \<open>j < (i::nat)\<close> obtains j' where \<open>k < j'\<close> and \<open>j' mod i = j\<close>  proof -
  have \<open>k < Suc k * i + j\<close> using assms less_imp_Suc_add by fastforce
  moreover
  have \<open>(Suc k * i + j) mod i = j\<close> by (metis assms mod_less mod_mult_self3) 
  ultimately show \<open>thesis\<close> using that by auto
qed

lemma list_neq_prefix_cases: assumes \<open>ls \<noteq> ls'\<close> and \<open>ls \<noteq> Nil\<close> and \<open>ls' \<noteq> Nil\<close>
  obtains (diverge) xs x x' ys ys' where \<open>ls = xs@[x]@ys\<close> \<open>ls' = xs@[x']@ys'\<close> \<open>x \<noteq> x'\<close> |
   (prefix1) xs where \<open>ls = ls'@xs\<close> and \<open>xs \<noteq> Nil\<close> |
   (prefix2) xs where \<open>ls@xs = ls'\<close> and \<open>xs \<noteq> Nil\<close> 
using assms proof (induct \<open>length ls\<close> arbitrary: \<open>ls\<close> \<open>ls'\<close> rule: less_induct)
  case (less ls ls')
  obtain z zs z' zs' where
  lz: \<open>ls = z#zs\<close> \<open>ls' = z'#zs'\<close> by (metis list.exhaust less(6,7))
  show \<open>?case\<close> proof cases
    assume zz: \<open>z = z'\<close>
    hence zsz: \<open>zs \<noteq> zs'\<close> using less(5) lz by auto
    have lenz: \<open>length zs < length ls\<close> using lz by auto    
    show \<open>?case\<close> proof(cases \<open>zs = Nil\<close>)
      assume zs: \<open>zs = Nil\<close>
      hence \<open>zs' \<noteq> Nil\<close> using zsz by auto
      moreover
      have \<open>ls@zs' = ls'\<close> using zs lz zz by auto
      ultimately
      show \<open>thesis\<close> using less(4) by blast
    next
      assume zs: \<open>zs \<noteq> Nil\<close>
      show \<open>thesis\<close> proof (cases \<open>zs' = Nil\<close>)
        assume \<open>zs' = Nil\<close>
        hence \<open>ls = ls'@zs\<close> using lz zz by auto
        thus \<open>thesis\<close> using zs less(3) by blast
      next
        assume zs': \<open>zs' \<noteq> Nil\<close>
        { fix xs x ys x' ys' 
          assume \<open>zs = xs @ [x] @ ys\<close> \<open>zs' = xs @ [x'] @ ys'\<close> and xx: \<open>x \<noteq> x'\<close>
          hence \<open>ls = (z#xs) @ [x] @ ys\<close> \<open>ls' = (z#xs) @ [x'] @ ys'\<close> using lz zz by auto
          hence \<open>thesis\<close> using less(2) xx by blast
        } note * = this
        { fix xs 
          assume \<open>zs = zs' @ xs\<close> and xs: \<open>xs \<noteq> []\<close>
          hence \<open>ls = ls' @ xs\<close> using lz zz by auto
          hence \<open>thesis\<close> using xs less(3) by blast
        } note ** = this
        { fix xs 
          assume \<open>zs@xs = zs'\<close> and xs: \<open>xs \<noteq> []\<close>
          hence \<open>ls@xs = ls'\<close> using lz zz by auto
          hence \<open>thesis\<close> using xs less(4) by blast
        } note *** = this
        have \<open>(\<And>xs x ys x' ys'. zs = xs @ [x] @ ys \<Longrightarrow> zs' = xs @ [x'] @ ys' \<Longrightarrow> x \<noteq> x' \<Longrightarrow> thesis) \<Longrightarrow> 
              (\<And>xs. zs = zs' @ xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> thesis) \<Longrightarrow> 
              (\<And>xs. zs @ xs = zs' \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
        using less(1)[OF lenz _ _ _ zsz zs zs' ] .
        thus \<open>thesis\<close> using * ** *** by blast
      qed
    qed 
  next
    assume \<open>z \<noteq> z'\<close>
    moreover
    have \<open>ls = []@[z]@zs\<close> \<open>ls' = []@[z']@zs'\<close> using lz by auto
    ultimately show \<open>thesis\<close> using less(2) by blast
  qed
qed

lemma three_cases: assumes \<open>A \<or> B \<or> C\<close> obtains \<open>A\<close> | \<open>B\<close> | \<open>C\<close> using assms by auto

lemma insort_greater: \<open>\<forall> x \<in> set ls. x < y \<Longrightarrow> insort y ls = ls@[y]\<close> by (induction \<open>ls\<close>,auto) 

lemma insort_append_first: assumes \<open>\<forall> y \<in> set ys. x \<le> y\<close> shows \<open>insort x (xs@ys) = insort x xs @ ys\<close> using assms by (induction \<open>xs\<close>,auto,metis insort_is_Cons)

lemma sorted_list_of_set_append: assumes \<open>finite xs\<close> \<open>finite ys\<close> \<open>\<forall> x \<in> xs. \<forall> y \<in> ys. x < y\<close> shows \<open>sorted_list_of_set (xs \<union> ys) = sorted_list_of_set xs @ (sorted_list_of_set ys)\<close>
using assms(1,3) proof (induction \<open>xs\<close>)
  case empty thus \<open>?case\<close> by simp
next
  case (insert x xs)
  hence iv: \<open>sorted_list_of_set (xs \<union> ys) = sorted_list_of_set xs @ sorted_list_of_set ys\<close> by blast
  have le: \<open>\<forall> y \<in> set (sorted_list_of_set ys). x < y\<close> using insert(4) assms(2) sorted_list_of_set by auto
  have \<open>sorted_list_of_set (insert x xs \<union> ys) = sorted_list_of_set (insert x (xs \<union> ys))\<close> by auto
  also 
  have \<open>\<dots> = insort x (sorted_list_of_set (xs \<union> ys))\<close> by (metis Un_iff assms(2) finite_Un insert.hyps(1) insert.hyps(2) insert.prems insertI1 less_irrefl sorted_list_of_set.insert)
  also 
  have \<open>\<dots> = insort x (sorted_list_of_set xs @ sorted_list_of_set ys)\<close> using iv by simp
  also
  have \<open>\<dots> = insort x (sorted_list_of_set xs) @ sorted_list_of_set ys\<close>  by (metis le insort_append_first less_le_not_le)
  also 
  have \<open>\<dots> = sorted_list_of_set (insert x xs) @ sorted_list_of_set ys\<close> using sorted_list_of_set_insert[OF insert(1),of \<open>x\<close>] insert(2) by auto
  finally  
  show \<open>?case\<close> .
qed

lemma filter_insort: \<open>sorted xs \<Longrightarrow> filter P (insort x xs) = (if P x then insort x (filter P xs) else filter P xs)\<close> by (induction \<open>xs\<close>, simp) (metis filter_insort filter_insort_triv map_ident) 

lemma filter_sorted_list_of_set: assumes \<open>finite xs\<close> shows \<open>filter P (sorted_list_of_set xs) = sorted_list_of_set {x \<in> xs. P x}\<close> using assms proof(induction \<open>xs\<close>)
  case empty thus \<open>?case\<close> by simp
next  
  case (insert x xs)
  have *: \<open>set (sorted_list_of_set xs) = xs\<close> \<open>sorted (sorted_list_of_set xs)\<close> \<open>distinct (sorted_list_of_set xs)\<close> by (auto simp add: insert.hyps(1))
  have **: \<open>P x \<Longrightarrow> {y \<in> insert x xs. P y} = insert x {y \<in> xs. P y}\<close> by auto
  have ***: \<open>\<not> P x \<Longrightarrow> {y \<in> insert x xs. P y} = {y \<in> xs. P y}\<close> by auto
  note filter_insort[OF *(2),of \<open>P\<close> \<open>x\<close>] sorted_list_of_set_insert[OF insert(1), of \<open>x\<close>] insert(2,3) ** ***  
  thus \<open>?case\<close> by (metis (mono_tags) "*"(1) List.finite_set distinct_filter distinct_insort distinct_sorted_list_of_set set_filter sorted_list_of_set.insert)
qed

lemma unbounded_nat_set_infinite: assumes \<open>\<forall> (i::nat). \<exists> j\<ge>i. j \<in> A\<close> shows \<open>\<not> finite A\<close> using assms
by (metis finite_nat_set_iff_bounded_le not_less_eq_eq)

lemma infinite_ascending: assumes nf: \<open>\<not> finite (A::nat set)\<close> obtains f where \<open>range f = A\<close> \<open>\<forall> i. f i < f (Suc i)\<close> proof 
  let \<open>?f\<close> = \<open>\<lambda> i. (LEAST a. a \<in> A \<and> card (A \<inter> {..<a}) = i)\<close>
  { fix i 
    obtain a where \<open>a \<in> A\<close> \<open>card (A \<inter> {..<a}) = i\<close> 
    proof (induction \<open>i\<close> arbitrary: \<open>thesis\<close>)
      case 0
      let \<open>?a0\<close> = \<open>(LEAST a. a \<in> A)\<close>
      have \<open>?a0 \<in> A\<close> by (metis LeastI empty_iff finite.emptyI nf set_eq_iff)      
      moreover
      have \<open>\<And>b. b \<in> A \<Longrightarrow> ?a0 \<le> b\<close> by (metis Least_le)
      hence \<open>card (A \<inter> {..<?a}) = 0\<close> by force
      ultimately
      show \<open>?case\<close> using 0 by blast
    next
      case (Suc i)
      obtain a where aa: \<open>a \<in> A\<close> and card: \<open>card (A \<inter> {..<a}) = i\<close> using Suc.IH by metis
      have nf': \<open>~ finite (A - {..a})\<close> using nf by auto
      let \<open>?b\<close> = \<open>LEAST b. b \<in> A - {..a}\<close>
      have bin: \<open>?b \<in> A-{..a}\<close> by (metis LeastI empty_iff finite.emptyI nf' set_eq_iff)
      have le: \<open>\<And>c. c \<in> A-{..a} \<Longrightarrow> ?b \<le> c\<close> by (metis Least_le)
      have ab: \<open>a < ?b\<close> using bin by auto
      have \<open>\<And> c. c \<in> A \<Longrightarrow> c < ?b \<Longrightarrow> c \<le> a\<close> using le by force
      hence \<open>A \<inter> {..<?b} = insert a (A \<inter> {..<a})\<close> using bin ab aa by force 
      hence \<open>card (A \<inter>{..<?b}) = Suc i\<close> using card by auto
      thus \<open>?case\<close> using Suc.prems bin by auto
    qed
    note \<open>\<And> thesis. ((\<And>a. a \<in> A \<Longrightarrow> card (A \<inter> {..<a}) = i \<Longrightarrow> thesis) \<Longrightarrow> thesis)\<close>
  }
  note ex = this
    
  {
    fix i
    obtain a where a: \<open>a \<in> A \<and> card (A \<inter>{..<a}) = i\<close>  using ex by blast
    have ina: \<open>?f i \<in> A\<close> and card: \<open>card (A \<inter>{..<?f i}) = i\<close> using LeastI[of \<open>\<lambda> a. a \<in> A \<and> card (A \<inter>{..<a}) = i\<close> \<open>a\<close>, OF a] by auto    
    obtain b where b: \<open>b \<in> A \<and> card (A \<inter>{..<b}) = Suc i\<close>  using ex by blast
    have inab: \<open>?f (Suc i) \<in> A\<close> and cardb: \<open>card (A \<inter>{..<?f (Suc i)}) = Suc i\<close> using LeastI[of \<open>\<lambda> a. a \<in> A \<and> card (A \<inter>{..<a}) = Suc i\<close> \<open>b\<close>, OF b] by auto
    have \<open>?f i < ?f (Suc i)\<close> proof (rule ccontr)
      assume \<open>\<not> ?f i < ?f (Suc i)\<close>
      hence \<open>A \<inter>{..<?f (Suc i)} \<subseteq> A \<inter>{..<?f i}\<close> by auto
      moreover have \<open>finite (A \<inter>{..<?f i})\<close> by auto
      ultimately have \<open>card(A \<inter>{..<?f (Suc i)}) \<le> card (A \<inter>{..<?f i})\<close> by (metis (erased, lifting) card_mono)
      thus \<open>False\<close> using card cardb by auto 
    qed
    note this ina
  }
  note b = this
  thus \<open>\<forall> i. ?f i < ?f (Suc i)\<close> by auto
  have *: \<open>range ?f \<subseteq> A\<close> using b by auto
  moreover
  { 
    fix a assume ina: \<open>a \<in> A\<close>
    let \<open>?i\<close> = \<open>card (A \<inter> {..<a})\<close>
    obtain b where b: \<open>b \<in> A \<and> card (A \<inter>{..<b}) = ?i\<close>  using ex by blast
    have inab: \<open>?f ?i \<in> A\<close> and cardb: \<open>card (A \<inter>{..<?f ?i}) = ?i\<close> using LeastI[of \<open>\<lambda> a. a \<in> A \<and> card (A \<inter>{..<a}) = ?i\<close> \<open>b\<close>, OF b] by auto
    have le: \<open>?f ?i \<le> a\<close> using Least_le[of \<open>\<lambda> a. a \<in> A \<and> card (A \<inter>{..<a}) = ?i\<close> \<open>a\<close>] ina by auto    
    have \<open>a = ?f ?i\<close> proof (rule ccontr)
      have fin: \<open>finite (A \<inter> {..<a})\<close> by auto
      assume \<open>a \<noteq> ?f ?i\<close>
      hence \<open>?f ?i < a\<close> using le by simp
      hence \<open>?f ?i \<in> A \<inter> {..<a}\<close> using inab by auto
      moreover
      have \<open>A \<inter> {..<?f ?i} \<subseteq> A \<inter> {..<a}\<close> using le by auto
      hence \<open>A \<inter> {..<?f ?i} = A \<inter> {..<a}\<close> using cardb card_subset_eq[OF fin] by auto
      ultimately      
      show \<open>False\<close> by auto
    qed
    hence \<open>a \<in> range ?f\<close> by auto
  }
  hence \<open>A \<subseteq> range ?f\<close> by auto 
  ultimately show \<open>range ?f = A\<close> by auto
qed

lemma mono_ge_id: \<open>\<forall> i. f i < f (Suc i) \<Longrightarrow> i \<le> f i\<close> 
  apply (induction \<open>i\<close>,auto) 
  by (metis not_le not_less_eq_eq order_trans)

lemma insort_map_mono: assumes mono: \<open>\<forall> n m. n < m \<longrightarrow> f n < f m\<close> shows \<open>map f (insort n ns) = insort (f n) (map f ns)\<close>
  apply (induction \<open>ns\<close>)
   apply auto
     apply (metis not_less not_less_iff_gr_or_eq mono)
    apply (metis antisym_conv1 less_imp_le mono)
   apply (metis mono not_less)
  by (metis mono not_less)  

lemma sorted_list_of_set_map_mono: assumes mono: \<open>\<forall> n m. n < m \<longrightarrow> f n < f m\<close> and fin: \<open>finite A\<close>
shows \<open>map f (sorted_list_of_set A) = sorted_list_of_set (f`A)\<close>
using fin proof (induction)
  case empty thus \<open>?case\<close> by simp
next
  case (insert x A)
  have [simp]:\<open>sorted_list_of_set (insert x A) = insort x (sorted_list_of_set A)\<close> using insert sorted_list_of_set.insert by simp
  have \<open>f ` insert x A = insert (f x) (f ` A)\<close> by auto
  moreover
  have \<open>f x \<notin> f`A\<close> apply (rule ccontr) using insert(2) mono apply auto by (metis insert.hyps(2) mono neq_iff)
  ultimately
  have \<open>sorted_list_of_set (f ` insert x A) = insort (f x) (sorted_list_of_set (f`A))\<close> using insert(1) sorted_list_of_set.insert by simp
  also
  have \<open>\<dots> = insort (f x) (map f (sorted_list_of_set A))\<close> using insert.IH by auto
  also have \<open>\<dots> = map f (insort x (sorted_list_of_set A))\<close> using insort_map_mono[OF mono] by auto
  finally  
  show \<open>map f (sorted_list_of_set (insert x A)) = sorted_list_of_set (f ` insert x A)\<close> by simp
qed

lemma GreatestIB:
fixes n :: \<open>nat\<close> and P
assumes a:\<open>\<exists>k\<le>n. P k\<close>
shows GreatestBI: \<open>P (GREATEST k. k\<le>n \<and> P k)\<close> and GreatestB: \<open>(GREATEST k. k\<le>n \<and> P k) \<le> n\<close> 
proof -
  show \<open>P (GREATEST k. k\<le>n \<and> P k)\<close> using GreatestI_ex_nat[OF assms] by auto  
  show \<open>(GREATEST k. k\<le>n \<and> P k) \<le> n\<close> using GreatestI_ex_nat[OF assms] by auto
qed

lemma GreatestB_le:
fixes n :: \<open>nat\<close>
assumes \<open>x\<le>n\<close> and \<open>P x\<close>
shows \<open>x \<le> (GREATEST k. k\<le>n \<and> P k)\<close> 
proof -
  have *: \<open>\<forall> y. y\<le>n \<and> P y \<longrightarrow> y<Suc n\<close> by auto
  then show \<open>x \<le> (GREATEST k. k\<le>n \<and> P k)\<close> using assms by (blast intro: Greatest_le_nat)
qed

lemma LeastBI_ex: assumes \<open>\<exists>k \<le> n. P k\<close> shows \<open>P (LEAST k::'c::wellorder. P k)\<close> and \<open>(LEAST k. P k) \<le> n\<close> 
proof -
  from assms guess k .. 
  hence k: \<open>k \<le> n\<close> \<open>P k\<close> by auto     
  thus \<open>P (LEAST k. P k)\<close> using LeastI[of \<open>P\<close> \<open>k\<close>] by simp
  show \<open>(LEAST k. P k) \<le> n\<close> using Least_le[of \<open>P\<close> \<open>k\<close>] k by auto
qed

lemma allB_atLeastLessThan_lower:  assumes \<open>(i::nat) \<le> j\<close> \<open>\<forall> x\<in>{i..<n}. P x\<close> shows \<open>\<forall> x\<in>{j..<n}. P x\<close> proof 
  fix x assume \<open>x\<in>{j..<n}\<close> hence \<open>x\<in>{i..<n}\<close> using assms(1) by simp
  thus \<open>P x\<close> using assms(2) by auto
qed


subsection \<open>Facts about Paths\<close>

context IFC
begin

lemma path0: \<open>path \<sigma> 0 = entry\<close> unfolding path_def by auto

lemma path_in_nodes[intro]: \<open>path \<sigma> k \<in> nodes\<close> proof (induction \<open>k\<close>)
  case (Suc k)
  hence \<open>\<And> \<sigma>'. (path \<sigma> k, suc (path \<sigma> k) \<sigma>') \<in> edges\<close> by auto
  hence \<open>(path \<sigma> k, path \<sigma> (Suc k)) \<in> edges\<close> unfolding path_def 
    by (metis suc_def comp_apply funpow.simps(2) prod.collapse) 
  thus \<open>?case\<close> using edges_nodes by force
qed (auto simp add: path_def)

lemma path_is_path[simp]: \<open>is_path (path \<sigma>)\<close> unfolding is_path_def path_def using step_suc_sem apply auto
by (metis path_def suc_def edges_complete path_in_nodes prod.collapse)

lemma term_path_stable: assumes \<open>is_path \<pi>\<close> \<open>\<pi> i = return\<close> and le: \<open>i \<le> j\<close> shows \<open>\<pi> j = return\<close> 
using le proof (induction \<open>j\<close>)
  case (Suc j) 
  show \<open>?case\<close> proof cases
    assume \<open>i\<le>j\<close>
    hence \<open>\<pi> j = return\<close> using Suc by simp
    hence \<open>(return, \<pi> (Suc j)) \<in> edges\<close> using assms(1) unfolding is_path_def by metis
    thus \<open>\<pi> (Suc j) = return\<close> using edges_return by auto
  next
    assume \<open>\<not> i \<le> j\<close>
    hence \<open>Suc j = i\<close> using Suc by auto
    thus \<open>?thesis\<close> using assms(2) by auto
  qed
next
  case 0 thus \<open>?case\<close> using assms by simp
qed 

lemma path_path_shift: assumes \<open>is_path \<pi>\<close> shows \<open>is_path (\<pi>\<guillemotleft>m)\<close> 
using assms unfolding is_path_def by simp

lemma path_cons: assumes \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> \<open>\<pi> m = \<pi>' 0\<close> shows \<open>is_path (\<pi> @\<^bsup>m\<^esup> \<pi>')\<close> 
unfolding is_path_def proof(rule,cases)
  fix n assume \<open>m < n\<close> thus \<open>((\<pi> @\<^bsup>m\<^esup> \<pi>') n, (\<pi> @\<^bsup>m\<^esup>  \<pi>') (Suc n)) \<in> edges\<close> 
    using assms(2) unfolding is_path_def path_append_def
    by (auto,metis Suc_diff_Suc diff_Suc_Suc less_SucI) 
next
  fix n assume *: \<open>\<not> m < n\<close>  thus \<open>((\<pi> @\<^bsup>m\<^esup>  \<pi>') n, (\<pi> @\<^bsup>m\<^esup>  \<pi>') (Suc n)) \<in> edges\<close> proof cases
    assume [simp]: \<open>n = m\<close>
    thus \<open>?thesis\<close> using assms unfolding is_path_def path_append_def by force
  next
    assume \<open>n \<noteq> m\<close>
    hence \<open>Suc n \<le> m\<close> \<open>n\<le> m\<close> using * by auto
    with assms(1) show \<open>?thesis\<close> unfolding is_path_def by auto
  qed
qed

lemma is_path_loop: assumes \<open>is_path \<pi>\<close> \<open>0 < i\<close> \<open>\<pi> i = \<pi> 0\<close> shows \<open>is_path (\<lambda> n. \<pi> (n mod i))\<close> unfolding is_path_def proof (rule,cases)
  fix n
  assume \<open>0 < Suc n mod i\<close>
  hence \<open>Suc n mod i = Suc (n mod i)\<close> by (metis mod_Suc neq0_conv)
  moreover 
  have \<open>(\<pi> (n mod i), \<pi> (Suc (n mod i))) \<in> edges\<close> using assms(1) unfolding is_path_def by auto
  ultimately
  show \<open>(\<pi> (n mod i), \<pi> (Suc n mod i)) \<in> edges\<close> by simp
  next
  fix n
  assume \<open>\<not> 0 < Suc n mod i\<close>
  hence \<open>Suc n mod i = 0\<close> by auto
  moreover 
  hence \<open>n mod i = i - 1\<close> using assms(2) by (metis Zero_neq_Suc diff_Suc_1 mod_Suc)
  ultimately
  show \<open>(\<pi>(n mod i), \<pi> (Suc n mod i)) \<in> edges\<close> using assms(1) unfolding is_path_def by (metis assms(3) mod_Suc)
qed

lemma path_nodes: \<open>is_path \<pi> \<Longrightarrow> \<pi> k \<in> nodes\<close> unfolding is_path_def using edges_nodes by force 

lemma direct_path_return': assumes \<open>is_path \<pi> \<close> \<open>\<pi> 0 = x\<close> \<open>x \<noteq> return\<close> \<open>\<pi> n = return\<close>
obtains \<pi>' n' where \<open>is_path \<pi>'\<close> \<open>\<pi>' 0 = x\<close> \<open>\<pi>' n' = return\<close> \<open>\<forall> i> 0. \<pi>' i \<noteq> x\<close>
using assms proof (induction \<open>n\<close> arbitrary: \<open>\<pi>\<close>  rule: less_induct)
  case (less n \<pi>) 
  hence ih: \<open>\<And> n' \<pi>'. n' < n \<Longrightarrow> is_path \<pi>' \<Longrightarrow> \<pi>' 0 = x \<Longrightarrow> \<pi>' n' = return \<Longrightarrow> thesis\<close> using assms by auto
  show \<open>thesis\<close> proof cases
    assume \<open>\<forall> i>0. \<pi> i \<noteq> x\<close> thus \<open>thesis\<close> using less by auto
  next
    assume \<open>\<not> (\<forall> i>0. \<pi> i \<noteq> x)\<close>
    then obtain i where \<open>0<i\<close> \<open>\<pi> i = x\<close> by auto
    hence \<open>(\<pi>\<guillemotleft>i) 0 = x\<close> by auto
    moreover
    have \<open>i < n\<close> using less(3,5,6) \<open>\<pi> i = x\<close> by (metis linorder_neqE_nat term_path_stable less_imp_le)    
    hence \<open>(\<pi>\<guillemotleft>i) (n-i) = return\<close> using less(6) by auto
    moreover
    have \<open>is_path (\<pi>\<guillemotleft>i)\<close> using less(3) by (metis path_path_shift)
    moreover
    have \<open>n - i < n\<close> using \<open>0<i\<close> \<open>i < n\<close> by auto    
    ultimately show \<open>thesis\<close> using ih by auto
  qed
qed

lemma direct_path_return: assumes  \<open>x \<in> nodes\<close> \<open>x \<noteq> return\<close>
obtains \<pi> n where \<open>is_path \<pi>\<close> \<open>\<pi> 0 = x\<close> \<open>\<pi> n = return\<close> \<open>\<forall> i> 0. \<pi> i \<noteq> x\<close>
using direct_path_return'[of _ \<open>x\<close>] reaching_ret[OF assms(1)] assms(2) by blast

lemma path_append_eq_up_to: \<open>(\<pi> @\<^bsup>k\<^esup> \<pi>') =\<^bsub>k\<^esub> \<pi>\<close>  unfolding eq_up_to_def by auto

lemma eq_up_to_le: assumes \<open>k \<le> n\<close> \<open>\<pi> =\<^bsub>n\<^esub>  \<pi>'\<close> shows \<open>\<pi> =\<^bsub>k\<^esub> \<pi>'\<close> using assms unfolding eq_up_to_def by auto 

lemma eq_up_to_refl: shows \<open>\<pi> =\<^bsub>k\<^esub> \<pi>\<close> unfolding eq_up_to_def by auto 

lemma eq_up_to_sym: assumes \<open>\<pi> =\<^bsub>k\<^esub> \<pi>'\<close> shows \<open>\<pi>' =\<^bsub>k\<^esub> \<pi>\<close> using assms unfolding eq_up_to_def by auto

lemma eq_up_to_apply: assumes \<open>\<pi> =\<^bsub>k\<^esub> \<pi>'\<close> \<open>j \<le> k\<close> shows \<open>\<pi> j = \<pi>' j\<close> using assms unfolding eq_up_to_def by auto

lemma path_swap_ret: assumes \<open>is_path \<pi>\<close> obtains \<pi>' n where \<open>is_path \<pi>'\<close> \<open>\<pi> =\<^bsub>k\<^esub> \<pi>'\<close> \<open>\<pi>' n = return\<close>
proof -
  have nd: \<open>\<pi> k \<in> nodes\<close> using assms path_nodes by simp
  obtain \<pi>' n where *: \<open>is_path \<pi>'\<close> \<open>\<pi>' 0 = \<pi> k\<close> \<open>\<pi>' n = return\<close> using reaching_ret[OF nd] by blast
  have \<open>\<pi> =\<^bsub>k\<^esub> (\<pi>@\<^bsup>k\<^esup> \<pi>')\<close> by (metis eq_up_to_sym path_append_eq_up_to)
  moreover
  have \<open>is_path (\<pi>@\<^bsup>k\<^esup> \<pi>')\<close> using assms * path_cons by metis
  moreover
  have \<open>(\<pi>@\<^bsup>k\<^esup> \<pi>') (k + n) = return\<close> using * by auto
  ultimately
  show \<open>thesis\<close> using that by blast
qed

lemma path_suc: \<open>path \<sigma> (Suc k) = fst (step (path \<sigma> k, \<sigma>\<^bsup>k\<^esup>))\<close> by (induction \<open>k\<close>, auto simp: path_def kth_state_def)

lemma kth_state_suc: \<open>\<sigma>\<^bsup>Suc k\<^esup>  = snd (step (path \<sigma> k, \<sigma>\<^bsup>k\<^esup>))\<close> by (induction \<open>k\<close>, auto simp: path_def kth_state_def)


subsection \<open>Facts about Post Dominators\<close>

lemma pd_trans: assumes 1: \<open>y pd\<rightarrow> x\<close> and 2: \<open>z pd\<rightarrow>y\<close> shows \<open>z pd\<rightarrow>x\<close> 
proof -
  {
    fix \<pi> n
    assume 3[simp]: \<open>is_path \<pi>\<close> \<open>\<pi> 0 = x\<close> \<open>\<pi> n = return\<close>
    then obtain k where \<open>\<pi> k = y\<close> and 7: \<open>k \<le> n\<close> using 1 unfolding is_pd_def by blast
    then have \<open>(\<pi>\<guillemotleft>k) 0 = y\<close> and \<open>(\<pi>\<guillemotleft>k) (n-k) = return\<close> by auto
    moreover have \<open>is_path (\<pi>\<guillemotleft>k)\<close> by(metis 3(1) path_path_shift)
    ultimately obtain k' where 8: \<open>(\<pi>\<guillemotleft>k) k' = z\<close> and \<open>k' \<le> n-k\<close> using 2 unfolding is_pd_def by blast
    hence \<open>k+k'\<le>n\<close> and \<open>\<pi> (k+ k') = z\<close> using 7 by auto
    hence \<open>\<exists>k\<le>n. \<pi> k = z\<close> using path_nodes by auto    
  }
  thus \<open>?thesis\<close> using 1 unfolding is_pd_def by blast
qed

lemma pd_path: assumes \<open>y pd\<rightarrow> x\<close>
obtains \<pi> n k where \<open>is_path \<pi>\<close> and \<open>\<pi> 0 = x\<close> and \<open>\<pi> n = return\<close> and \<open>\<pi> k = y\<close> and \<open>k \<le> n\<close>   
using assms unfolding is_pd_def using reaching_ret[of \<open>x\<close>] by blast

lemma pd_antisym: assumes xpdy: \<open>x pd\<rightarrow> y\<close> and ypdx: \<open>y pd\<rightarrow> x\<close> shows \<open>x = y\<close>
proof -
  obtain \<pi> n where path: \<open>is_path \<pi>\<close> and \<pi>0: \<open>\<pi> 0 = x\<close> and \<pi>n: \<open>\<pi> n = return\<close> using pd_path[OF ypdx] by metis
  hence kex: \<open>\<exists>k\<le>n. \<pi> k = y\<close> using ypdx unfolding is_pd_def by auto
  obtain k where k: \<open>k = (GREATEST k. k\<le>n \<and> \<pi> k = y)\<close> by simp
  have \<pi>k: \<open>\<pi> k = y\<close> and kn: \<open>k \<le> n\<close> using k kex by (auto intro: GreatestIB)
  
  have kpath: \<open>is_path (\<pi>\<guillemotleft>k)\<close> by (metis path_path_shift path)
  moreover have k0: \<open>(\<pi>\<guillemotleft>k) 0 = y\<close> using \<pi>k by simp
  moreover have kreturn: \<open>(\<pi>\<guillemotleft>k) (n-k) = return\<close> using kn \<pi>n by simp
  ultimately have ky': \<open>\<exists>k'\<le>(n-k).(\<pi>\<guillemotleft>k) k' = x\<close> using xpdy unfolding is_pd_def by simp      

  obtain k' where k': \<open>k' = (GREATEST k'. k'\<le>(n-k) \<and> (\<pi>\<guillemotleft>k) k' = x)\<close> by simp

  with ky' have \<pi>k': \<open>(\<pi>\<guillemotleft>k) k' = x\<close> and kn': \<open>k' \<le> (n-k)\<close>  by (auto intro: GreatestIB)
  have k'path: \<open>is_path (\<pi>\<guillemotleft>k\<guillemotleft>k')\<close> using kpath by(metis path_path_shift)
  moreover have k'0: \<open>(\<pi>\<guillemotleft>k\<guillemotleft>k') 0 = x\<close> using \<pi>k' by simp
  moreover have k'return: \<open>(\<pi>\<guillemotleft>k\<guillemotleft>k') (n-k-k') = return\<close> using kn' kreturn by (metis path_shift_def le_add_diff_inverse)
  ultimately have ky'': \<open>\<exists>k''\<le>(n-k-k').(\<pi>\<guillemotleft>k\<guillemotleft>k') k'' = y\<close> using ypdx unfolding is_pd_def by blast

  obtain k'' where k'': \<open>k''= (GREATEST k''. k''\<le>(n-k-k') \<and> (\<pi>\<guillemotleft>k\<guillemotleft>k') k'' = y)\<close> by simp
  with ky'' have \<pi>k'': \<open>(\<pi>\<guillemotleft>k\<guillemotleft>k') k'' = y\<close> and kn'': \<open>k'' \<le> (n-k-k')\<close>  by (auto intro: GreatestIB)

  from this(1) have  \<open>\<pi> (k + k' + k'') = y\<close> by (metis path_shift_def add.commute add.left_commute)
  moreover
  have \<open>k + k' +k'' \<le> n\<close> using kn'' kn' kn by simp
  ultimately have \<open>k + k' + k''\<le> k\<close> using k by(auto simp: GreatestB_le)
  hence \<open>k' = 0\<close> by simp
  with k0 \<pi>k' show \<open>x = y\<close> by simp
qed

lemma pd_refl[simp]: \<open>x \<in> nodes \<Longrightarrow> x pd\<rightarrow> x\<close> unfolding is_pd_def by blast

lemma pdt_trans_in_pdt: \<open>(x,y) \<in> pdt\<^sup>+ \<Longrightarrow> (x,y) \<in> pdt\<close> 
proof (induction rule: trancl_induct)
  case base thus \<open>?case\<close> by simp
next
  case (step y z) show \<open>?case\<close> unfolding pdt_def proof (simp)
    have *: \<open>y pd\<rightarrow> x\<close> \<open>z pd\<rightarrow> y\<close> using step unfolding pdt_def by auto
    hence [simp]: \<open>z pd\<rightarrow> x\<close> using pd_trans[where x=\<open>x\<close> and y=\<open>y\<close> and z=\<open>z\<close>] by simp
    have \<open>x\<noteq>z\<close> proof 
      assume \<open>x = z\<close>
      hence \<open>z pd\<rightarrow> y\<close> \<open>y pd\<rightarrow> z\<close> using * by auto
      hence \<open>z = y\<close> using pd_antisym by auto
      thus \<open>False\<close> using step(2) unfolding pdt_def by simp
    qed
    thus \<open>x \<noteq> z \<and> z pd\<rightarrow> x\<close> by auto
  qed
qed

lemma pdt_trancl_pdt: \<open>pdt\<^sup>+ = pdt\<close> using pdt_trans_in_pdt by fast

lemma trans_pdt: \<open>trans pdt\<close> by (metis pdt_trancl_pdt trans_trancl)

definition [simp]: \<open>pdt_inv = pdt\<inverse>\<close>

lemma wf_pdt_inv: \<open>wf (pdt_inv)\<close> proof (rule ccontr)
  assume \<open>\<not> wf (pdt_inv)\<close>
  then obtain f where  \<open>\<forall>i. (f (Suc i), f i) \<in> pdt\<inverse>\<close> using wf_iff_no_infinite_down_chain by force
  hence *: \<open>\<forall> i. (f i, f (Suc i)) \<in> pdt\<close> by simp
  have **:\<open>\<forall> i. \<forall> j>i. (f i, f j) \<in> pdt\<close> proof(rule,rule,rule)
    fix i j assume  \<open>i < (j::nat)\<close> thus \<open>(f i, f j) \<in> pdt\<close> proof (induction \<open>j\<close> rule: less_induct)
      case (less k)
      show \<open>?case\<close> proof (cases \<open>Suc i < k\<close>)
        case True
        hence k:\<open>k-1 < k\<close> \<open>i < k-1\<close> and sk: \<open>Suc (k-1) = k\<close> by auto
        show \<open>?thesis\<close> using less(1)[OF k] *[rule_format,of \<open>k-1\<close>,unfolded sk] trans_pdt[unfolded trans_def] by blast
      next
        case False
        hence \<open>Suc i = k\<close> using less(2) by auto
        then show \<open>?thesis\<close> using * by auto
      qed
    qed
  qed
  hence ***:\<open>\<forall> i. \<forall> j > i. f j pd\<rightarrow> f i\<close> \<open>\<forall> i. \<forall> j > i. f i \<noteq>  f j\<close> unfolding pdt_def by auto
  hence ****:\<open>\<forall> i>0. f i pd\<rightarrow> f 0\<close> by simp
  hence \<open>f 0 \<in> nodes\<close>  using * is_pd_def by fastforce
  then obtain \<pi> n where \<pi>:\<open>is_path \<pi>\<close> \<open>\<pi> 0 = f 0\<close> \<open>\<pi> n = return\<close> using reaching_ret by blast  
  hence \<open>\<forall> i>0. \<exists> k\<le>n. \<pi> k = f i\<close> using ***(1) \<open>f 0 \<in> nodes\<close> unfolding is_pd_def by blast
  hence \<pi>f:\<open>\<forall> i. \<exists> k\<le>n. \<pi> k = f i\<close> using \<pi>(2) by (metis le0 not_gr_zero)
  have \<open>range f \<subseteq> \<pi> ` {..n}\<close> proof(rule subsetI)
    fix x assume \<open>x \<in> range f\<close>
    then obtain i where \<open>x = f i\<close> by auto
    then obtain k where \<open>x = \<pi> k\<close> \<open>k \<le> n\<close> using \<pi>f by metis
    thus \<open>x \<in> \<pi> ` {..n}\<close> by simp
  qed
  hence f:\<open>finite (range f)\<close> using finite_surj by auto
  hence fi:\<open>\<exists> i. infinite {j. f j = f i}\<close>  using pigeonhole_infinite[OF _ f] by auto
  obtain i where \<open>infinite {j. f j = f i}\<close> using fi ..    
  thus \<open>False\<close> 
    by (metis (mono_tags, lifting) "***"(2) bounded_nat_set_is_finite gt_ex mem_Collect_eq nat_neq_iff)
qed

lemma return_pd: assumes \<open>x \<in> nodes\<close> shows \<open>return pd\<rightarrow> x\<close> unfolding is_pd_def using assms by blast

lemma pd_total: assumes xz: \<open>x pd\<rightarrow> z\<close> and yz: \<open>y pd\<rightarrow> z\<close> shows \<open>x pd\<rightarrow> y \<or> y pd\<rightarrow>x\<close> 
proof -
  obtain \<pi> n where path: \<open>is_path \<pi>\<close> and \<pi>0: \<open>\<pi> 0 = z\<close> and \<pi>n: \<open>\<pi> n = return\<close> using xz reaching_ret unfolding is_pd_def by force
  have *: \<open>\<exists> k\<le>n. (\<pi> k = x \<or> \<pi> k = y)\<close> (is \<open>\<exists> k\<le>n. ?P k\<close>) using path \<pi>0 \<pi>n xz yz unfolding is_pd_def by auto
  obtain k where k: \<open>k = (LEAST k. \<pi> k = x \<or> \<pi> k = y)\<close> by simp
  hence kn: \<open>k\<le>n\<close> and \<pi>k: \<open>\<pi> k = x \<or> \<pi> k = y\<close> using LeastBI_ex[OF *] by auto 
  note k_le = Least_le[where P = \<open>?P\<close>] 
  show \<open>?thesis\<close> proof (cases)
    assume kx: \<open>\<pi> k = x\<close>
    have k_min: \<open>\<And> k'. \<pi> k' = y \<Longrightarrow> k \<le> k'\<close> using k_le unfolding k by auto
    {
      fix \<pi>' 
      and n' :: \<open>nat\<close>
      assume path': \<open>is_path \<pi>'\<close> and \<pi>'0: \<open>\<pi>' 0 = x\<close> and \<pi>'n': \<open>\<pi>' n' = return\<close>
      have path'': \<open>is_path (\<pi> @\<^bsup>k\<^esup> \<pi>')\<close> using path_cons[OF path path'] kx \<pi>'0 by auto
      have \<pi>''0: \<open>(\<pi> @\<^bsup>k\<^esup> \<pi>') 0 = z\<close> using \<pi>0 by simp
      have \<pi>''n: \<open>(\<pi> @\<^bsup>k\<^esup> \<pi>') (k+n') = return\<close> using \<pi>'n' kx \<pi>'0 by auto
      obtain k' where k': \<open>k' \<le> k + n'\<close> \<open>(\<pi> @\<^bsup>k\<^esup> \<pi>') k' = y\<close> using yz path'' \<pi>''0 \<pi>''n unfolding is_pd_def by blast
      have **: \<open>k \<le> k'\<close> proof (rule ccontr)
        assume \<open>\<not> k \<le> k'\<close>
        hence \<open>k' < k\<close> by simp
        moreover 
        hence \<open>\<pi> k' = y\<close> using k' by auto
        ultimately
        show \<open>False\<close> using k_min by force
     qed
     hence \<open>\<pi>' (k' - k) = y\<close> using k' \<pi>'0 kx  by auto
     moreover
     have \<open>(k' - k) \<le> n'\<close> using k' by auto
     ultimately 
     have \<open>\<exists> k\<le> n'. \<pi>' k = y\<close> by auto
   }
   hence \<open>y pd\<rightarrow> x\<close> using kx path_nodes path unfolding is_pd_def by auto
   thus \<open>?thesis\<close> ..
 next \<comment> \<open>This is analogous argument\<close>
   assume kx: \<open>\<pi> k \<noteq> x\<close>
   hence ky: \<open>\<pi> k = y\<close> using \<pi>k by auto
   have k_min: \<open>\<And> k'. \<pi> k' = x \<Longrightarrow> k \<le> k'\<close> using k_le unfolding k by auto
    {
      fix \<pi>' 
      and n' :: \<open>nat\<close>
      assume path': \<open>is_path \<pi>'\<close> and \<pi>'0: \<open>\<pi>' 0 = y\<close> and \<pi>'n': \<open>\<pi>' n' = return\<close>
      have path'': \<open>is_path (\<pi> @\<^bsup>k\<^esup> \<pi>')\<close> using path_cons[OF path path'] ky \<pi>'0 by auto
      have \<pi>''0: \<open>(\<pi> @\<^bsup>k\<^esup> \<pi>') 0 = z\<close> using \<pi>0 by simp
      have \<pi>''n: \<open>(\<pi> @\<^bsup>k\<^esup> \<pi>') (k+n') = return\<close> using \<pi>'n' ky \<pi>'0 by auto
      obtain k' where k': \<open>k' \<le> k + n'\<close> \<open>(\<pi> @\<^bsup>k\<^esup> \<pi>') k' = x\<close> using xz path'' \<pi>''0 \<pi>''n unfolding is_pd_def by blast
      have **: \<open>k \<le> k'\<close> proof (rule ccontr)
        assume \<open>\<not> k \<le> k'\<close>
        hence \<open>k' < k\<close> by simp
        moreover 
        hence \<open>\<pi> k' = x\<close> using k' by auto
        ultimately
        show \<open>False\<close> using k_min by force
     qed
     hence \<open>\<pi>' (k' - k) = x\<close> using k' \<pi>'0 ky  by auto
     moreover
     have \<open>(k' - k) \<le> n'\<close> using k' by auto
     ultimately 
     have \<open>\<exists> k\<le> n'. \<pi>' k = x\<close> by auto
   }
   hence \<open>x pd\<rightarrow> y\<close> using ky path_nodes path unfolding is_pd_def by auto
   thus \<open>?thesis\<close> ..
  qed
qed    

lemma pds_finite: \<open>finite {y . (x,y) \<in> pdt}\<close> proof cases 
  assume \<open>x \<in> nodes\<close>
  then obtain \<pi> n where \<pi>:\<open>is_path \<pi>\<close> \<open>\<pi> 0 = x\<close> \<open>\<pi> n = return\<close> using reaching_ret by blast
  have *: \<open>\<forall> y \<in> {y. (x,y)\<in> pdt}. y pd\<rightarrow> x\<close> using pdt_def by auto
  have \<open>\<forall> y \<in> {y. (x,y)\<in> pdt}. \<exists> k \<le> n. \<pi> k = y\<close>  using * \<pi> is_pd_def by blast
  hence \<open>{y. (x,y)\<in> pdt} \<subseteq> \<pi> ` {..n}\<close>  by auto
  then show \<open>?thesis\<close> using finite_surj by blast
next
  assume \<open>\<not> x\<in> nodes\<close>
  hence \<open>{y. (x,y)\<in>pdt} = {}\<close> unfolding pdt_def is_pd_def using path_nodes reaching_ret by fastforce
  then show \<open>?thesis\<close> by simp
qed

lemma ipd_exists: assumes node: \<open>x \<in> nodes\<close> and not_ret: \<open>x\<noteq>return\<close> shows \<open>\<exists>y. y ipd\<rightarrow> x\<close> 
proof -
  let \<open>?Q\<close> = \<open>{y. x\<noteq>y \<and> y pd\<rightarrow> x}\<close>
  have *: \<open>return \<in> ?Q\<close> using assms return_pd by simp    
  hence **: \<open>\<exists> x. x\<in> ?Q\<close> by auto
  have fin: \<open>finite ?Q\<close> using pds_finite unfolding pdt_def by auto
  have tot: \<open>\<forall> y z. y\<in>?Q \<and> z \<in> ?Q \<longrightarrow> z pd\<rightarrow> y \<or> y pd\<rightarrow> z\<close> using pd_total by auto
  obtain y where ymax: \<open>y\<in> ?Q\<close> \<open>\<forall> z\<in>?Q. z = y \<or> z pd\<rightarrow> y\<close> using fin ** tot proof (induct)
    case empty
    then show \<open>?case\<close> by auto
  next
    case (insert x F) show \<open>thesis\<close> proof (cases \<open>F = {}\<close>)
      assume \<open>F = {}\<close>
      thus \<open>thesis\<close> using insert(4)[of \<open>x\<close>] by auto
    next  
      assume \<open>F \<noteq> {}\<close>
      hence \<open>\<exists> x. x\<in> F\<close> by auto
      have \<open>\<And>y. y \<in> F \<Longrightarrow> \<forall>z\<in>F. z = y \<or> z pd\<rightarrow> y \<Longrightarrow> thesis\<close> proof -
        fix y assume a: \<open>y \<in> F\<close> \<open>\<forall>z\<in>F. z = y \<or> z pd\<rightarrow> y\<close>
        have \<open>x \<noteq> y\<close> using insert a by auto
        have \<open>x pd\<rightarrow> y \<or> y pd\<rightarrow> x\<close> using insert(6) a(1) by auto
        thus \<open>thesis\<close> proof 
          assume \<open>x pd\<rightarrow> y\<close>
          hence \<open>\<forall>z\<in>insert x F. z = y \<or> z pd\<rightarrow> y\<close> using a(2) by blast
          thus \<open>thesis\<close> using a(1) insert(4) by blast
        next
          assume \<open>y pd\<rightarrow> x\<close>
          have \<open>\<forall>z\<in>insert x F. z = x \<or> z pd\<rightarrow> x\<close> proof
            fix z assume \<open>z\<in> insert x F\<close> thus \<open>z = x \<or> z pd\<rightarrow> x\<close> proof(rule,simp)
              assume \<open>z\<in>F\<close>
              hence \<open>z = y \<or> z pd\<rightarrow> y\<close> using a(2) by auto
              thus \<open>z = x \<or> z pd\<rightarrow> x\<close> proof(rule,simp add: \<open>y pd\<rightarrow> x\<close>)
                assume \<open>z pd\<rightarrow> y\<close>
                show \<open>z = x \<or> z pd\<rightarrow> x\<close> using \<open>y pd\<rightarrow> x\<close> \<open>z pd\<rightarrow> y\<close> pd_trans by blast
              qed 
            qed
          qed 
          then show \<open>thesis\<close> using insert by blast
        qed
      qed
      then show \<open>thesis\<close> using insert by blast
    qed
  qed    
  hence ***: \<open>y pd\<rightarrow> x\<close> \<open>x\<noteq>y\<close> by auto
  have \<open>\<forall> z. z \<noteq> x \<and> z pd\<rightarrow> x \<longrightarrow> z pd\<rightarrow> y\<close> proof (rule,rule)
    fix z 
    assume a: \<open> z \<noteq> x \<and> z pd\<rightarrow> x\<close>
    hence b: \<open>z \<in> ?Q\<close> by auto
    have \<open>y pd\<rightarrow> z \<or> z pd\<rightarrow> y\<close> using pd_total ***(1) a by auto
    thus \<open>z pd\<rightarrow> y\<close> proof
      assume c: \<open>y pd\<rightarrow> z\<close>
      hence \<open>y = z\<close> using b ymax pdt_def pd_antisym by auto
      thus \<open>z pd\<rightarrow> y\<close> using c by simp
    qed simp
  qed
  with *** have  \<open>y ipd\<rightarrow> x\<close> unfolding is_ipd_def by simp
  thus \<open>?thesis\<close> by blast
qed

lemma ipd_unique: assumes yipd: \<open>y ipd\<rightarrow> x\<close> and y'ipd: \<open>y' ipd\<rightarrow> x\<close> shows \<open>y = y'\<close> 
proof -  
  have 1: \<open>y pd\<rightarrow> y'\<close> and  2: \<open>y' pd\<rightarrow> y\<close> using yipd y'ipd unfolding is_ipd_def by auto
  show \<open>?thesis\<close> using pd_antisym[OF 1 2] .
qed

lemma ipd_is_ipd: assumes \<open>x \<in> nodes\<close> and \<open>x\<noteq>return\<close> shows \<open>ipd x ipd\<rightarrow> x\<close> proof -
  from assms obtain y where \<open>y ipd\<rightarrow> x\<close> using ipd_exists by auto
  moreover
  hence \<open>\<And> z. z ipd\<rightarrow>x \<Longrightarrow> z = y\<close> using ipd_unique by simp
  ultimately show \<open>?thesis\<close> unfolding ipd_def by (auto intro: theI2)
qed

lemma is_ipd_in_pdt: \<open>y ipd\<rightarrow> x \<Longrightarrow> (x,y) \<in> pdt\<close> unfolding is_ipd_def pdt_def by auto

lemma ipd_in_pdt: \<open>x \<in> nodes \<Longrightarrow> x\<noteq>return \<Longrightarrow> (x,ipd x) \<in> pdt\<close> by (metis ipd_is_ipd is_ipd_in_pdt)

lemma no_pd_path: assumes \<open>x \<in> nodes\<close> and \<open>\<not> y pd\<rightarrow> x\<close>
obtains \<pi> n where \<open>is_path \<pi>\<close> and \<open>\<pi> 0 = x\<close> and \<open>\<pi> n = return\<close> and \<open>\<forall> k \<le> n. \<pi> k \<noteq> y\<close>
proof (rule ccontr)
  assume \<open>\<not> thesis\<close>
  hence \<open>\<forall> \<pi> n.  is_path \<pi> \<and> \<pi> 0 = x \<and> \<pi> n = return \<longrightarrow> (\<exists> k\<le>n . \<pi> k = y)\<close> using that by force
  thus \<open>False\<close> using assms unfolding is_pd_def by auto
qed

lemma pd_pd_ipd: assumes \<open>x \<in> nodes\<close> \<open>x\<noteq>return\<close> \<open>y\<noteq>x\<close> \<open>y pd\<rightarrow> x\<close> shows \<open>y pd\<rightarrow> ipd x\<close> 
proof -
  have \<open>ipd x pd\<rightarrow> x\<close> by (metis assms(1,2) ipd_is_ipd is_ipd_def)
  hence \<open>y pd\<rightarrow> ipd x \<or> ipd x pd\<rightarrow> y\<close> by (metis assms(4) pd_total)
  thus \<open>?thesis\<close> proof
    have 1: \<open>ipd x ipd\<rightarrow> x\<close> by (metis assms(1,2) ipd_is_ipd)
    moreover
    assume \<open>ipd x pd\<rightarrow> y\<close>
    ultimately
    show \<open>y pd\<rightarrow> ipd x\<close> unfolding is_ipd_def using assms(3,4) by auto
  qed auto
qed

lemma pd_nodes: assumes \<open>y pd\<rightarrow> x\<close> shows pd_node1: \<open>y \<in> nodes\<close> and pd_node2: \<open>x \<in> nodes\<close>
proof -
  obtain \<pi> k where \<open>is_path \<pi>\<close> \<open>\<pi> k = y\<close> using assms unfolding is_pd_def using reaching_ret by force
  thus \<open>y \<in> nodes\<close> using path_nodes by auto
  show \<open>x \<in> nodes\<close> using assms unfolding is_pd_def by simp
qed

lemma pd_ret_is_ret: \<open>x pd\<rightarrow> return \<Longrightarrow> x = return\<close> by (metis pd_antisym pd_node1 return_pd)

lemma ret_path_none_pd: assumes \<open>x \<in> nodes\<close> \<open>x\<noteq>return\<close> 
obtains \<pi> n where \<open>is_path \<pi>\<close>  \<open>\<pi> 0 = x\<close> \<open>\<pi> n = return\<close>  \<open>\<forall> i>0. \<not> x pd\<rightarrow> \<pi> i\<close>
proof(rule ccontr)
  assume \<open>\<not>thesis\<close>
  hence *: \<open>\<And> \<pi> n. \<lbrakk>is_path \<pi>; \<pi> 0 = x; \<pi> n = return\<rbrakk> \<Longrightarrow> \<exists>i>0. x pd\<rightarrow> \<pi> i\<close> using that by blast
  obtain \<pi> n where **: \<open>is_path \<pi>\<close>  \<open>\<pi> 0 = x\<close> \<open>\<pi> n = return\<close> \<open>\<forall> i>0. \<pi> i \<noteq> x\<close> using direct_path_return[OF assms] by metis
  then obtain i where ***: \<open>i>0\<close> \<open>x pd\<rightarrow> \<pi> i\<close> using * by blast
  hence \<open>\<pi> i \<noteq> return\<close> using pd_ret_is_ret assms(2) by auto
  hence \<open>i < n\<close> using assms(2) term_path_stable ** by (metis linorder_neqE_nat less_imp_le)
  hence \<open>(\<pi>\<guillemotleft>i)(n-i) = return\<close> using **(3) by auto
  moreover
  have \<open>(\<pi>\<guillemotleft>i) (0) = \<pi> i\<close> by simp
  moreover 
  have \<open>is_path (\<pi>\<guillemotleft>i)\<close> using **(1) path_path_shift by metis
  ultimately
  obtain k where \<open>(\<pi>\<guillemotleft>i) k = x\<close> using ***(2) unfolding is_pd_def by metis
  hence \<open>\<pi> (i + k) = x\<close> by auto
  thus \<open>False\<close> using **(4) \<open>i>0\<close> by auto
qed

lemma path_pd_ipd0': assumes \<open>is_path \<pi>\<close> and \<open>\<pi> n \<noteq> return\<close> \<open>\<pi> n \<noteq> \<pi> 0\<close> and \<open>\<pi> n pd\<rightarrow> \<pi> 0\<close> 
obtains k where \<open>k \<le> n\<close> and \<open>\<pi> k = ipd(\<pi> 0)\<close> 
proof(rule ccontr)  
  have *: \<open>\<pi> n pd\<rightarrow> ipd (\<pi> 0)\<close> by (metis is_pd_def assms(3,4) pd_pd_ipd pd_ret_is_ret)  
  obtain \<pi>' n' where **: \<open>is_path \<pi>'\<close> \<open>\<pi>' 0 = \<pi> n\<close> \<open>\<pi>' n' = return\<close> \<open>\<forall> i>0. \<not> \<pi> n pd\<rightarrow> \<pi>' i\<close>  by (metis assms(2) assms(4) pd_node1 ret_path_none_pd)
  hence \<open>\<forall> i>0. \<pi>' i \<noteq> ipd (\<pi> 0)\<close> using * by metis
  moreover
  assume \<open>\<not> thesis\<close>
  hence \<open>\<forall> k\<le>n. \<pi> k \<noteq> ipd (\<pi> 0)\<close> using that by blast
  ultimately
  have \<open>\<forall> i. (\<pi>@\<^bsup>n\<^esup>  \<pi>') i \<noteq> ipd (\<pi> 0)\<close> by (metis diff_is_0_eq neq0_conv path_append_def)
  moreover
  have \<open>(\<pi>@\<^bsup>n\<^esup>  \<pi>') (n + n') = return\<close> 
    by (metis \<open>\<pi>' 0 = \<pi> n\<close> \<open>\<pi>' n' = return\<close> add_diff_cancel_left' assms(2) diff_is_0_eq path_append_def)
  moreover
  have \<open>(\<pi>@\<^bsup>n\<^esup>  \<pi>') 0 = \<pi> 0\<close> by (metis le0 path_append_def)
  moreover
  have \<open>is_path (\<pi>@\<^bsup>n\<^esup>  \<pi>')\<close> by (metis \<open>\<pi>' 0 = \<pi> n\<close> \<open>is_path \<pi>'\<close> assms(1) path_cons)
  moreover  
  have \<open>ipd (\<pi> 0) pd\<rightarrow> \<pi> 0\<close> by (metis **(2,3,4) assms(2) assms(4) ipd_is_ipd is_ipd_def neq0_conv pd_node2)
  moreover
  have \<open>\<pi> 0 \<in> nodes\<close> by (metis assms(1) path_nodes)
  ultimately
  show \<open>False\<close> unfolding is_pd_def by blast
qed

lemma path_pd_ipd0: assumes \<open>is_path \<pi>\<close> and \<open>\<pi> 0 \<noteq> return\<close> \<open>\<pi> n \<noteq> \<pi> 0\<close> and \<open>\<pi> n pd\<rightarrow> \<pi> 0\<close> 
obtains k where \<open>k \<le> n\<close> and \<open>\<pi> k = ipd(\<pi> 0)\<close> 
proof cases 
  assume *: \<open>\<pi> n = return\<close>
  have \<open>ipd (\<pi> 0) pd\<rightarrow> (\<pi> 0)\<close> by (metis is_ipd_def is_pd_def assms(2,4) ipd_is_ipd)
  with assms(1,2,3) * show \<open>thesis\<close> unfolding is_pd_def by (metis that)
next
  assume \<open>\<pi> n \<noteq> return\<close> 
  from path_pd_ipd0' [OF assms(1) this assms(3,4)] that show \<open>thesis\<close> by auto
qed

lemma path_pd_ipd: assumes \<open>is_path \<pi>\<close> and \<open>\<pi> k \<noteq> return\<close> \<open>\<pi> n \<noteq> \<pi> k\<close> and \<open>\<pi> n pd\<rightarrow> \<pi> k\<close> and kn: \<open>k < n\<close> 
obtains l where \<open>k < l\<close> and \<open>l \<le> n\<close> and \<open>\<pi> l = ipd(\<pi> k)\<close> 
proof -
  have \<open>is_path (\<pi> \<guillemotleft> k)\<close> \<open>(\<pi> \<guillemotleft> k) 0 \<noteq> return\<close> \<open>(\<pi> \<guillemotleft> k) (n - k) \<noteq> (\<pi> \<guillemotleft> k) 0\<close> \<open>(\<pi> \<guillemotleft> k) (n - k) pd\<rightarrow> (\<pi> \<guillemotleft> k) 0\<close> 
  using assms path_path_shift by auto 
  with path_pd_ipd0[of \<open>\<pi>\<guillemotleft>k\<close> \<open>n-k\<close>]
  obtain ka where \<open>ka \<le> n - k\<close> \<open>(\<pi> \<guillemotleft> k) ka = ipd ((\<pi> \<guillemotleft> k) 0)\<close> .
  hence \<open>k + ka \<le> n\<close> \<open>\<pi> (k + ka) = ipd (\<pi> k)\<close> using kn by auto
  moreover 
  hence \<open>\<pi> (k + ka) ipd\<rightarrow> \<pi> k\<close> by (metis assms(1) assms(2) ipd_is_ipd path_nodes)
  hence \<open>k < k + ka\<close> unfolding is_ipd_def by (metis nat_neq_iff not_add_less1)
  ultimately
  show \<open>thesis\<close> using that[of \<open>k+ka\<close>] by auto
qed

lemma path_ret_ipd: assumes \<open>is_path \<pi>\<close> and \<open>\<pi> k \<noteq> return\<close> \<open>\<pi> n = return\<close> 
obtains l where \<open>k < l\<close> and \<open>l \<le> n\<close> and \<open>\<pi> l = ipd(\<pi> k)\<close> 
proof -
  have \<open>\<pi> n \<noteq> \<pi> k\<close> using assms by auto
  moreover
  have \<open>k \<le> n\<close> apply (rule ccontr) using term_path_stable assms by auto
  hence \<open>k < n\<close> by (metis assms(2,3) dual_order.order_iff_strict)
  moreover
  have \<open>\<pi> n pd\<rightarrow> \<pi> k\<close> by (metis assms(1,3) path_nodes return_pd)
  ultimately
  obtain l where \<open>k < l\<close> \<open>l \<le> n\<close> \<open>\<pi> l = ipd (\<pi> k)\<close> using assms path_pd_ipd by blast
  thus \<open>thesis\<close> using that by auto
qed

lemma pd_intro: assumes \<open>l pd\<rightarrow> k\<close> \<open>is_path \<pi>\<close> \<open>\<pi> 0 = k\<close> \<open>\<pi> n = return\<close> 
obtains i where \<open>i \<le> n\<close> \<open>\<pi> i = l\<close> using assms unfolding is_pd_def by metis

lemma path_pd_pd0: assumes path:  \<open>is_path \<pi>\<close> and lpdn: \<open>\<pi> l pd\<rightarrow> n\<close> and npd0: \<open>n pd\<rightarrow> \<pi> 0\<close> 
obtains k where \<open>k \<le> l\<close> \<open>\<pi> k = n\<close>
proof (rule ccontr)
  assume \<open>\<not> thesis\<close>
  hence notn: \<open>\<And> k. k \<le> l \<Longrightarrow> \<pi> k \<noteq> n\<close> using that by blast
  have nret: \<open>\<pi> l \<noteq> return\<close> by (metis is_pd_def assms(1,3) notn)
  
  obtain \<pi>' n' where path': \<open>is_path \<pi>'\<close> and \<pi>0': \<open>\<pi>' 0 = \<pi> l\<close> and \<pi>n': \<open>\<pi>' n' = return\<close> and nonepd: \<open>\<forall> i>0. \<not> \<pi> l pd\<rightarrow> \<pi>' i\<close>
  using nret path path_nodes ret_path_none_pd by metis
  
  have \<open>\<pi> l \<noteq> n\<close> using notn by simp
  hence \<open>\<forall> i. \<pi>' i \<noteq> n\<close> using nonepd \<pi>0' lpdn by (metis neq0_conv)
  
  hence notn': \<open>\<forall> i. (\<pi>@\<^bsup>l\<^esup> \<pi>') i \<noteq> n\<close> using notn \<pi>0' by auto

  have \<open>is_path (\<pi>@\<^bsup>l\<^esup> \<pi>')\<close> using path path' by (metis \<pi>0' path_cons)
  moreover
  have \<open>(\<pi>@\<^bsup>l\<^esup> \<pi>') 0 = \<pi> 0\<close> by simp
  moreover
  have \<open>(\<pi>@\<^bsup>l\<^esup> \<pi>') (n' + l) = return\<close> using \<pi>0' \<pi>n' by auto
  ultimately
  show \<open>False\<close> using notn' npd0 unfolding is_pd_def by blast
qed


subsection \<open>Facts about Control Dependencies\<close>

lemma icd_imp_cd: \<open>n icd\<^bsup>\<pi>\<^esup>\<rightarrow> k \<Longrightarrow> n cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> by (metis is_icdi_def)

lemma ipd_impl_not_cd:  assumes \<open>j \<in> {k..i}\<close> and \<open>\<pi> j = ipd (\<pi> k)\<close> shows \<open>\<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> 
  by (metis assms(1) assms(2) is_cdi_def)

lemma cd_not_ret: assumes \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k \<close> shows \<open>\<pi> k \<noteq> return\<close> by (metis is_cdi_def assms nat_less_le term_path_stable)

lemma cd_path_shift: assumes \<open>j \<le> k\<close> \<open>is_path \<pi> \<close> shows \<open>(i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k) = (i - j cd\<^bsup>\<pi>\<guillemotleft>j\<^esup>\<rightarrow> k-j)\<close> proof 
  assume a: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>
  hence b: \<open>k < i\<close> by (metis is_cdi_def)
  hence \<open>is_path (\<pi> \<guillemotleft> j)\<close> \<open>k - j < i - j\<close> using assms apply (metis path_path_shift) 
  by (metis assms(1) b diff_less_mono)  
  moreover 
  have c: \<open>\<forall> j \<in> {k..i}. \<pi> j \<noteq> ipd (\<pi> k)\<close> by (metis a ipd_impl_not_cd)
  hence \<open>\<forall> ja \<in> {k - j..i - j}. (\<pi> \<guillemotleft> j) ja \<noteq> ipd ((\<pi> \<guillemotleft> j) (k - j))\<close> using b assms by auto fastforce
  moreover 
  have \<open>j < i\<close> using assms(1) b by auto
  hence \<open>(\<pi>\<guillemotleft>j) (i - j) \<noteq> return\<close> using a unfolding is_cdi_def by auto 
  ultimately
  show \<open>i - j cd\<^bsup>\<pi>\<guillemotleft>j\<^esup>\<rightarrow> k-j\<close> unfolding is_cdi_def by simp
next
  assume a: \<open>i - j cd\<^bsup>\<pi>\<guillemotleft>j\<^esup>\<rightarrow> k-j\<close>
  hence b: \<open>k - j < i-j\<close> by (metis is_cdi_def)
  moreover
  have c: \<open>\<forall> ja \<in> {k - j..i - j}. (\<pi> \<guillemotleft> j) ja \<noteq> ipd ((\<pi> \<guillemotleft> j) (k - j))\<close> by (metis a ipd_impl_not_cd)
  have \<open>\<forall> j \<in> {k..i}. \<pi> j \<noteq> ipd (\<pi> k)\<close> proof (rule,goal_cases) case (1 n)
    hence \<open>n-j \<in> {k-j..i-j}\<close> using assms by auto
    hence \<open>\<pi> (j + (n-j)) \<noteq> ipd(\<pi> (j + (k-j)))\<close> by (metis c path_shift_def)
    thus \<open>?case\<close> using 1 assms(1) by auto
  qed
  moreover
  have \<open>j < i\<close> using assms(1) b by auto
  hence \<open>\<pi> i \<noteq> return\<close> using a unfolding is_cdi_def by auto
  ultimately
  show \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> unfolding is_cdi_def by (metis assms(1) assms(2) diff_is_0_eq' le_diff_iff nat_le_linear nat_less_le)
qed 

lemma cd_path_shift0: assumes \<open>is_path \<pi>\<close> shows \<open>(i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k) = (i-k cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow>0)\<close>
  using cd_path_shift[OF _ assms] by (metis diff_self_eq_0 le_refl)

lemma icd_path_shift: assumes \<open>l \<le> k\<close> \<open>is_path \<pi>\<close> shows \<open>(i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k) = (i - l icd\<^bsup>\<pi>\<guillemotleft>l\<^esup>\<rightarrow> k - l)\<close> 
proof -
  have \<open>is_path (\<pi>\<guillemotleft>l)\<close> using path_path_shift assms(2) by auto
  moreover
  have \<open>(i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k) = (i - l cd\<^bsup>\<pi>\<guillemotleft>l\<^esup>\<rightarrow> k - l)\<close> using assms cd_path_shift by auto
  moreover 
  have \<open>(\<forall> m \<in> {k<..<i}. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m) = (\<forall> m \<in> {k - l<..<i - l}. \<not> i - l cd\<^bsup>\<pi> \<guillemotleft> l\<^esup>\<rightarrow> m)\<close> 
  proof -
    {fix m assume *: \<open>\<forall> m \<in> {k - l<..<i - l}. \<not> i - l cd\<^bsup>\<pi> \<guillemotleft> l\<^esup>\<rightarrow> m\<close> \<open>m \<in> {k<..<i}\<close> 
      hence \<open>m-l \<in> {k-l<..<i-l}\<close> using assms(1) by auto
      hence \<open>\<not> i - l cd\<^bsup>\<pi>\<guillemotleft>l\<^esup>\<rightarrow>(m-l)\<close> using * by blast
      moreover
      have \<open>l \<le> m\<close> using * assms by auto
      ultimately have \<open>\<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow>m\<close> using assms(2) cd_path_shift by blast
    }
    moreover
    {fix m assume *: \<open>\<forall> m \<in> {k<..<i}. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> \<open>m-l \<in> {k-l<..<i-l}\<close> 
      hence \<open>m \<in> {k<..<i}\<close> using assms(1) by auto
      hence \<open>\<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow>m\<close> using * by blast
      moreover
      have \<open>l \<le> m\<close> using * assms by auto
      ultimately have \<open>\<not> i - l cd\<^bsup>\<pi>\<guillemotleft>l\<^esup>\<rightarrow>(m-l)\<close> using assms(2) cd_path_shift by blast
    }
    ultimately show \<open>?thesis\<close> by auto (metis diff_add_inverse)
  qed
  ultimately
  show \<open>?thesis\<close> unfolding is_icdi_def using assms by blast
qed

lemma icd_path_shift0: assumes \<open>is_path \<pi>\<close> shows \<open>(i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k) = (i-k icd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow>0)\<close>
  using icd_path_shift[OF _ assms] by (metis diff_self_eq_0 le_refl)

lemma cdi_path_swap: assumes \<open>is_path \<pi>'\<close> \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> \<open>\<pi> =\<^bsub>j\<^esub>  \<pi>'\<close> shows \<open>j cd\<^bsup>\<pi>'\<^esup>\<rightarrow>k\<close> using assms unfolding eq_up_to_def is_cdi_def by auto

lemma cdi_path_swap_le: assumes \<open>is_path \<pi>'\<close> \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> \<open>\<pi> =\<^bsub>n\<^esub>  \<pi>'\<close> \<open>j \<le> n\<close> shows \<open>j cd\<^bsup>\<pi>'\<^esup>\<rightarrow>k\<close> by (metis assms cdi_path_swap eq_up_to_le)

lemma not_cd_impl_ipd:  assumes \<open>is_path \<pi>\<close> and \<open>k < i\<close> and \<open>\<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> and \<open>\<pi> i \<noteq> return\<close> obtains j where \<open>j \<in> {k..i}\<close> and \<open>\<pi> j = ipd (\<pi> k)\<close>
by (metis assms(1) assms(2) assms(3) assms(4) is_cdi_def)

lemma icd_is_the_icd: assumes \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> shows \<open>k = (THE k. i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close> using assms icd_uniq 
  by (metis the1_equality)

lemma all_ipd_imp_ret: assumes \<open>is_path \<pi>\<close> and \<open>\<forall> i. \<pi> i \<noteq> return \<longrightarrow> (\<exists> j>i. \<pi> j = ipd (\<pi> i))\<close> shows \<open>\<exists>j. \<pi> j = return\<close>
proof - 
  { fix x assume *: \<open>\<pi> 0 = x\<close>
    have \<open>?thesis\<close> using wf_pdt_inv * assms  
    proof(induction \<open>x\<close> arbitrary: \<open>\<pi>\<close> rule: wf_induct_rule )
    case (less x \<pi>) show \<open>?case\<close> proof (cases \<open>x = return\<close>)
      case True thus \<open>?thesis\<close> using less(2) by auto
    next
      assume not_ret: \<open>x \<noteq> return\<close>
      moreover
      then obtain k where k_ipd: \<open>\<pi> k = ipd x\<close> using less(2,4) by auto
      moreover  
      have \<open>x \<in> nodes\<close> using less(2,3) by (metis path_nodes)
      ultimately 
      have \<open>(x, \<pi> k) \<in> pdt\<close> by (metis ipd_in_pdt)
      hence a: \<open>(\<pi> k, x) \<in> pdt_inv\<close> unfolding pdt_inv_def by simp     
      have b: \<open>is_path (\<pi> \<guillemotleft> k)\<close> by (metis less.prems(2) path_path_shift)    
      have c: \<open>\<forall> i. (\<pi>\<guillemotleft>k) i \<noteq> return \<longrightarrow> (\<exists>j>i. (\<pi>\<guillemotleft>k) j = ipd ((\<pi>\<guillemotleft>k) i))\<close> using less(4) apply auto
        by (metis (full_types) ab_semigroup_add_class.add_ac(1) less_add_same_cancel1 less_imp_add_positive)
      from less(1)[OF a _ b c]
      have \<open>\<exists>j. (\<pi>\<guillemotleft>k) j = return\<close> by auto    
      thus \<open>\<exists>j. \<pi> j = return\<close> by auto
    qed
    qed
  }
  thus \<open>?thesis\<close> by simp
qed

lemma loop_has_cd: assumes \<open>is_path \<pi>\<close> \<open>0 < i\<close> \<open>\<pi> i = \<pi> 0\<close> \<open>\<pi> 0 \<noteq> return\<close> shows \<open>\<exists> k < i. i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> proof (rule ccontr)
  let \<open>?\<pi>\<close> = \<open>(\<lambda> n. \<pi> (n mod i))\<close>  
  assume \<open>\<not> (\<exists>k<i. i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close>
  hence \<open>\<forall> k <i. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> by blast
  hence *: \<open>\<forall> k<i. (\<exists>j \<in> {k..i}. \<pi> j = ipd (\<pi> k))\<close> using assms(1,3,4) not_cd_impl_ipd by metis
  have \<open>\<forall> k. (\<exists> j > k. ?\<pi> j = ipd (?\<pi> k))\<close> proof 
    fix k
    have \<open>k mod i < i\<close> using assms(2) by auto
    with * obtain j where \<open>j \<in> {(k mod i)..i}\<close> \<open>\<pi> j = ipd (\<pi> (k mod i))\<close> by auto
    then obtain j' where 1: \<open>j' < i\<close> \<open>\<pi> j' = ipd (\<pi> (k mod i))\<close> 
      by (cases \<open>j = i\<close>, auto ,metis assms(2) assms(3),metis le_neq_implies_less)
    then obtain j'' where 2: \<open>j'' > k\<close> \<open>j'' mod i = j'\<close> by (metis mod_bound_instance)
    hence \<open>?\<pi> j'' = ipd (?\<pi> k)\<close> using 1 by auto
    with 2(1)
    show \<open>\<exists> j > k. ?\<pi> j = ipd (?\<pi> k)\<close> by auto
  qed
  moreover 
  have \<open>is_path ?\<pi>\<close> by (metis assms(1) assms(2) assms(3) is_path_loop)
  ultimately 
  obtain k where \<open>?\<pi> k = return\<close> by (metis (lifting) all_ipd_imp_ret)
  moreover 
  have \<open>k mod i < i\<close> by (simp add: assms(2)) 
  ultimately
  have \<open>\<pi> i = return\<close> by (metis assms(1) term_path_stable less_imp_le)
  thus \<open>False\<close> by (metis assms(3) assms(4))
qed

lemma loop_has_cd': assumes \<open>is_path \<pi>\<close> \<open>j < i\<close> \<open>\<pi> i = \<pi> j\<close> \<open>\<pi> j \<noteq> return\<close> shows \<open>\<exists> k \<in> {j..<i}. i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> 
proof -
  have \<open>\<exists> k'< i-j. i-j cd\<^bsup>\<pi>\<guillemotleft>j\<^esup>\<rightarrow>k'\<close> 
    apply(rule loop_has_cd) 
    apply (metis assms(1) path_path_shift)
    apply (auto simp add: assms less_imp_le)
    done
  then obtain k where k: \<open>k<i-j\<close> \<open>i-j cd\<^bsup>\<pi>\<guillemotleft>j\<^esup>\<rightarrow>k\<close> by auto
  hence k': \<open>(k+j) < i\<close>  \<open>i-j cd\<^bsup>\<pi>\<guillemotleft>j\<^esup>\<rightarrow> (k+j)-j\<close>  by auto
  note cd_path_shift[OF _ assms(1)]
  hence \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k+j\<close> using k'(2) by (metis le_add1 add.commute)
  with k'(1) show \<open>?thesis\<close> by force
qed  

lemma claim'': assumes path\<pi>: \<open>is_path \<pi>\<close> and path\<pi>': \<open>is_path \<pi>'\<close> 
and \<pi>i: \<open>\<pi> i = \<pi>' i'\<close> and \<pi>j: \<open>\<pi> j = \<pi>' j'\<close> 
and not_cd:  \<open>\<forall> k. \<not> j cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>  \<open>\<forall> k. \<not> i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k\<close> 
and nret: \<open>\<pi> i \<noteq> return\<close>
and ilj: \<open>i < j\<close>
shows \<open>i' < j'\<close> proof (rule ccontr)
  assume \<open>\<not> i' < j'\<close>  
  hence jlei: \<open>j' \<le> i'\<close> by auto
  show \<open>False\<close> proof (cases)
  assume j'li': \<open>j' < i'\<close> 
  define \<pi>'' where \<open>\<pi>'' \<equiv> (\<pi>@\<^bsup>j\<^esup>(\<pi>'\<guillemotleft>j'))\<guillemotleft>i\<close>
  note \<pi>''_def[simp]
  have \<open>\<pi> j = (\<pi>' \<guillemotleft> j') 0\<close> by (metis path_shift_def Nat.add_0_right \<pi>j)
  hence \<open>is_path \<pi>''\<close> using path\<pi> path\<pi>' \<pi>''_def path_path_shift path_cons by presburger
  moreover 
  have \<open>\<pi>'' (j-i+(i'-j')) = \<pi>'' 0\<close>  using ilj jlei \<pi>i \<pi>j 
    by (auto, metis add_diff_cancel_left' le_antisym le_diff_conv le_eq_less_or_eq)
  moreover
  have \<open>\<pi>'' 0 \<noteq> return\<close> by (simp add: ilj less_or_eq_imp_le nret)
  moreover
  have \<open>0 < j-i+(i'-j')\<close> by (metis add_is_0 ilj neq0_conv zero_less_diff)
  ultimately obtain k where k: \<open>k < j-i+(i'-j')\<close> \<open>j-i+(i'-j') cd\<^bsup>\<pi>''\<^esup>\<rightarrow> k\<close>   by (metis loop_has_cd)
  hence *: \<open>\<forall> l \<in> {k..j-i+(i'-j')}. \<pi>'' l \<noteq> ipd (\<pi>'' k)\<close> by (metis is_cdi_def)
  show \<open>False\<close> proof (cases \<open>k < j-i\<close>)
    assume a: \<open>k < j - i\<close>
    hence b: \<open>\<pi>'' k = \<pi> (i + k)\<close> by auto
    have \<open>\<forall> l \<in> {i+k..j}. \<pi> l \<noteq> ipd (\<pi> (i+k))\<close> proof
      fix l assume l: \<open>l \<in> {i + k..j}\<close>
      hence \<open>\<pi> l = \<pi>'' (l - i)\<close> by auto
      moreover 
      from a l have \<open>l-i \<in> {k .. j-i + (i'-j')}\<close> by force
      ultimately show \<open>\<pi> l \<noteq> ipd (\<pi> (i + k))\<close> using * b by auto
    qed
    moreover 
    have \<open>i + k < j\<close> using a by simp
    moreover
    have \<open>\<pi> j \<noteq> return\<close> by (metis \<pi>i \<pi>j j'li' nret path\<pi>' term_path_stable less_imp_le) 
    ultimately
    have \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i+k\<close>  by (metis not_cd_impl_ipd path\<pi>)
    thus \<open>False\<close> by (metis not_cd(1))
  next
    assume \<open>\<not> k < j - i\<close>
    hence a: \<open>j - i \<le> k\<close> by simp
    hence b: \<open>\<pi>'' k = \<pi>' (j' + (i + k) - j)\<close> unfolding \<pi>''_def path_shift_def path_append_def using ilj 
      by(auto,metis \<pi>j add_diff_cancel_left' le_antisym le_diff_conv add.commute)
    have \<open>\<forall> l \<in> {j' + (i+k) - j..i'}. \<pi>' l \<noteq> ipd (\<pi>' (j' + (i+k) - j))\<close> proof
      fix l assume l: \<open>l \<in> {j' + (i+k) - j..i'}\<close>
      hence \<open>\<pi>' l = \<pi>'' (j + l - i - j')\<close> unfolding \<pi>''_def path_shift_def path_append_def using ilj
        by (auto, metis Nat.diff_add_assoc \<pi>j a add.commute add_diff_cancel_left' add_leD1 le_antisym le_diff_conv)
      moreover 
      from a l have \<open>j + l - i - j' \<in> {k .. j-i + (i'-j')}\<close> by force
      ultimately show \<open>\<pi>' l \<noteq> ipd (\<pi>' (j' + (i + k) - j))\<close> using * b by auto
    qed
    moreover 
    have \<open>j' + (i+k) - j < i'\<close> using a  j'li' ilj k(1) by linarith      
    moreover 
    have \<open>\<pi>' i' \<noteq> return\<close> by (metis \<pi>i nret)
    ultimately    
    have \<open>i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j' + (i+k) - j\<close> by (metis not_cd_impl_ipd path\<pi>')
    thus \<open>False\<close> by (metis not_cd(2))
  qed
  next
  assume \<open>\<not> j' < i'\<close>
  hence \<open>j' = i'\<close> by (metis \<open>\<not> i' < j'\<close> linorder_cases)
  hence \<open>\<pi> i = \<pi> j\<close> by (metis \<pi>i \<pi>j)
  thus \<open>False\<close> by (metis ilj loop_has_cd' not_cd(1) nret path\<pi>)
qed
qed

lemma other_claim': assumes path: \<open>is_path \<pi>\<close> and eq: \<open>\<pi> i = \<pi> j\<close> and \<open>\<pi> i \<noteq> return\<close> 
and icd: \<open>\<forall> k. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> and \<open>\<forall> k. \<not> j cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> shows \<open>i = j\<close>  
proof (rule ccontr,cases)
  assume \<open>i < j\<close> thus \<open>False\<close> using assms claim'' by blast
next
  assume \<open>\<not> i < j\<close> \<open>i \<noteq> j\<close> 
  hence \<open>j < i\<close> by auto
  thus \<open>False\<close> using assms claim'' by (metis loop_has_cd')
qed  

lemma icd_no_cd_path_shift: assumes \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close> shows \<open>(\<forall> k. \<not> i - 1 cd\<^bsup>\<pi>\<guillemotleft>1\<^esup>\<rightarrow> k)\<close> 
proof (rule,rule ccontr,goal_cases)
  case (1 k)
  hence *: \<open>i - 1 cd\<^bsup>\<pi> \<guillemotleft> 1\<^esup>\<rightarrow> k\<close> by simp
  have **: \<open>1 \<le> k + 1\<close> by simp
  have ***: \<open>is_path \<pi>\<close> by (metis assms is_icdi_def)
  hence \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k+1\<close> using cd_path_shift[OF ** ***] * by auto
  moreover 
  hence \<open>k+1 < i\<close> unfolding is_cdi_def by simp
  moreover
  have \<open>0 < k + 1\<close> by simp
  ultimately show \<open>False\<close> using assms[unfolded is_icdi_def] by auto
qed

lemma claim': assumes path\<pi>: \<open>is_path \<pi>\<close> and path\<pi>': \<open>is_path \<pi>'\<close> and
  \<pi>i: \<open>\<pi> i = \<pi>' i'\<close> and \<pi>j: \<open>\<pi> j = \<pi>' j'\<close> and not_cd:
  \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close> \<open>j icd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close>
  \<open>i' icd\<^bsup>\<pi>'\<^esup>\<rightarrow> 0\<close> \<open>j' icd\<^bsup>\<pi>'\<^esup>\<rightarrow> 0\<close>
   and ilj: \<open>i < j\<close>
   and nret: \<open>\<pi> i \<noteq> return\<close>
  shows \<open>i' < j'\<close> 
proof -
  have g0: \<open>0 < i\<close> \<open>0 < j\<close> \<open>0 < i'\<close> \<open>0 < j'\<close>using not_cd[unfolded is_icdi_def is_cdi_def] by auto
  have  \<open>(\<pi> \<guillemotleft> 1) (i - 1) = (\<pi>' \<guillemotleft> 1) (i' - 1)\<close> \<open>(\<pi> \<guillemotleft> 1) (j - 1) = (\<pi>' \<guillemotleft> 1) (j' - 1)\<close> using \<pi>i \<pi>j g0 by auto
  moreover
  have \<open>\<forall> k. \<not> (j - 1) cd\<^bsup>\<pi>\<guillemotleft>1\<^esup>\<rightarrow> k\<close> \<open>\<forall> k. \<not> (i' - 1) cd\<^bsup>\<pi>'\<guillemotleft>1\<^esup>\<rightarrow> k\<close> 
    by (metis icd_no_cd_path_shift not_cd(2)) (metis icd_no_cd_path_shift not_cd(3))
  moreover
  have \<open>is_path (\<pi>\<guillemotleft>1)\<close> \<open>is_path (\<pi>'\<guillemotleft>1)\<close> using path\<pi> path\<pi>' path_path_shift by blast+
  moreover 
  have \<open>(\<pi>\<guillemotleft>1) (i - 1) \<noteq> return\<close> using g0 nret by auto
  moreover 
  have \<open>i - 1 < j - 1\<close> using g0 ilj by auto
  ultimately have \<open>i' - 1 < j' - 1\<close> using claim'' by blast
  thus \<open>i'<j'\<close> by auto
qed

lemma other_claim: assumes path: \<open>is_path \<pi>\<close> and eq: \<open>\<pi> i = \<pi> j\<close> and \<open>\<pi> i \<noteq> return\<close> 
and icd: \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close> and \<open>j icd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close> shows \<open>i = j\<close>  proof (rule ccontr,cases)
  assume \<open>i < j\<close> thus \<open>False\<close> using assms claim' by blast
next
  assume \<open>\<not> i < j\<close> \<open>i \<noteq> j\<close> 
  hence \<open>j < i\<close> by auto
  thus \<open>False\<close> using assms claim' by (metis less_not_refl)
qed

lemma cd_trans0: assumes \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close> and \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow>j\<close> shows \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close> proof (rule ccontr)    
  have path: \<open>is_path \<pi>\<close> and ij: \<open>0 < j\<close> and jk: \<open>j < k\<close> 
  and nret: \<open>\<pi> j \<noteq> return\<close> \<open>\<pi> k \<noteq> return\<close>
  and noipdi: \<open>\<forall> l \<in> {0..j}. \<pi> l \<noteq> ipd (\<pi> 0)\<close>
  and noipdj: \<open>\<forall> l \<in> {j..k}. \<pi> l \<noteq> ipd (\<pi> j)\<close>
  using assms unfolding is_cdi_def by auto
  assume \<open>\<not> k cd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close>
  hence \<open>\<exists>l \<in> {0..k}. \<pi> l = ipd (\<pi> 0)\<close> unfolding is_cdi_def using path ij jk nret by force
  then obtain l where \<open>l \<in> {0..k}\<close> and l: \<open>\<pi> l = ipd (\<pi> 0)\<close> by auto
  hence jl: \<open>j<l\<close> and lk: \<open>l\<le>k\<close> using noipdi ij by auto
  have pdj: \<open>ipd (\<pi> 0) pd\<rightarrow> \<pi> j\<close> proof (rule ccontr)    
    have \<open>\<pi> j \<in> nodes\<close> using path by (metis path_nodes)
    moreover 
    assume \<open>\<not> ipd (\<pi> 0) pd\<rightarrow> \<pi> j\<close>
    ultimately
    obtain \<pi>' n where *: \<open>is_path \<pi>'\<close> \<open>\<pi>' 0 = \<pi> j\<close> \<open>\<pi>' n = return\<close> \<open>\<forall> k\<le>n. \<pi>' k \<noteq> ipd(\<pi> 0)\<close> using no_pd_path by metis
    hence path': \<open>is_path (\<pi> @\<^bsup>j\<^esup>  \<pi>')\<close> by (metis path path_cons) 
    moreover
    have \<open>\<forall> k \<le> j + n. (\<pi>@\<^bsup>j\<^esup>  \<pi>') k \<noteq> ipd (\<pi> 0)\<close> using noipdi *(4) by auto
    moreover 
    have \<open>(\<pi>@\<^bsup>j\<^esup>  \<pi>') 0 = \<pi> 0\<close> by auto
    moreover
    have \<open>(\<pi>@\<^bsup>j\<^esup>  \<pi>') (j + n) = return\<close> using *(2,3) by auto
    ultimately
    have \<open>\<not> ipd (\<pi> 0) pd\<rightarrow> \<pi> 0\<close> unfolding is_pd_def by metis
    thus \<open>False\<close> by (metis is_ipd_def ij ipd_is_ipd nret(1) path path_nodes term_path_stable less_imp_le)
  qed
  hence \<open>(\<pi>\<guillemotleft>j) (l-j) pd\<rightarrow> (\<pi>\<guillemotleft>j) 0\<close> using jl l by auto
  moreover
  have \<open>is_path (\<pi>\<guillemotleft>j)\<close> by (metis path path_path_shift)
  moreover
  have \<open>\<pi> l \<noteq> return\<close> by (metis lk nret(2) path term_path_stable)
  hence \<open>(\<pi>\<guillemotleft>j) (l-j) \<noteq> return\<close> using jl by auto
  moreover 
  have \<open>\<pi> j \<noteq> ipd (\<pi> 0)\<close> using noipdi by force
  hence \<open>(\<pi>\<guillemotleft>j) (l-j) \<noteq> (\<pi>\<guillemotleft>j) 0\<close> using jl l by auto
  ultimately
  obtain k' where \<open>k' \<le> l-j\<close> and \<open>(\<pi>\<guillemotleft>j) k' = ipd ((\<pi>\<guillemotleft>j) 0)\<close> using path_pd_ipd0' by blast
  hence \<open>j + k' \<in> {j..k}\<close> \<open>\<pi> (j+k') = ipd (\<pi> j)\<close> using jl lk by auto
  thus \<open>False\<close> using noipdj by auto
qed

lemma cd_trans: assumes \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> and \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow>j\<close> shows \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> proof -
  have path: \<open>is_path \<pi>\<close> using assms is_cdi_def by auto
  have ij: \<open>i<j\<close> using assms is_cdi_def by auto
  let \<open>?\<pi>\<close> = \<open>\<pi>\<guillemotleft>i\<close>
  have \<open>j-i cd\<^bsup>?\<pi>\<^esup>\<rightarrow> 0\<close> using assms(1) cd_path_shift0 path by auto
  moreover
  have \<open>k-i cd\<^bsup>?\<pi>\<^esup>\<rightarrow>j-i\<close> by (metis assms(2) cd_path_shift is_cdi_def ij less_imp_le_nat)
  ultimately
  have \<open>k-i cd\<^bsup>?\<pi>\<^esup>\<rightarrow> 0\<close> using cd_trans0 by auto
  thus \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> using path cd_path_shift0 by auto
qed

lemma excd_impl_exicd: assumes \<open>\<exists> k. i cd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> shows \<open>\<exists> k. i icd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> 
using assms proof(induction \<open>i\<close> arbitrary: \<open>\<pi>\<close> rule: less_induct)
  case (less i) 
  then obtain k where k: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> by auto
  hence ip: \<open>is_path \<pi>\<close> unfolding is_cdi_def by auto
  show \<open>?case\<close> proof (cases)
    assume *: \<open>\<forall> m \<in> {k<..<i}. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close>
    hence \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> using k ip unfolding is_icdi_def by auto
    thus \<open>?case\<close> by auto
  next
    assume \<open>\<not> (\<forall> m \<in> {k<..<i}. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m)\<close>
    then obtain m where m: \<open>m \<in> {k<..<i}\<close> \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> by blast
    hence \<open>i - m cd\<^bsup>\<pi>\<guillemotleft>m\<^esup>\<rightarrow> 0\<close> by (metis cd_path_shift0 is_cdi_def)
    moreover 
    have \<open>i - m < i\<close> using m by auto
    ultimately
    obtain k' where k': \<open>i - m icd\<^bsup>\<pi>\<guillemotleft>m\<^esup>\<rightarrow> k'\<close> using less(1) by blast
    hence \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k' + m\<close> using ip 
    by (metis add.commute add_diff_cancel_right' icd_path_shift le_add1)
    thus \<open>?case\<close> by auto
  qed
qed

lemma cd_split: assumes \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> and \<open>\<not> i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> obtains m where \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> and \<open>m cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> 
proof -
  have ki: \<open>k < i\<close> using assms is_cdi_def by auto
  obtain m where m: \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using assms(1) by (metis excd_impl_exicd)
  hence \<open>k \<le> m\<close> unfolding is_icdi_def using ki assms(1) by force
  hence km: \<open>k < m\<close>using m assms(2) by (metis le_eq_less_or_eq)
  moreover have \<open>\<pi> m \<noteq> return\<close> using m unfolding is_icdi_def is_cdi_def by (simp, metis term_path_stable less_imp_le)
  moreover have \<open>m<i\<close> using m unfolding is_cdi_def is_icdi_def by auto
  ultimately 
  have \<open>m cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> using assms(1) unfolding is_cdi_def by auto
  with m that show \<open>thesis\<close> by auto
qed

lemma cd_induct[consumes 1, case_names base IS]: assumes prem: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> and base: \<open>\<And> i. i icd\<^bsup>\<pi>\<^esup>\<rightarrow>k \<Longrightarrow> P i\<close> 
and IH: \<open>\<And> k' i'. k' cd\<^bsup>\<pi>\<^esup>\<rightarrow> k \<Longrightarrow> P k' \<Longrightarrow> i' icd\<^bsup>\<pi>\<^esup>\<rightarrow> k' \<Longrightarrow> P i'\<close> shows \<open>P i\<close> 
using prem IH proof (induction \<open>i\<close> rule: less_induct,cases)
  case (less i) 
  assume \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>
  thus \<open>P i\<close> using base by simp
next
  case (less i')
  assume \<open>\<not> i' icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>
  then obtain k' where k': \<open> i' icd\<^bsup>\<pi>\<^esup>\<rightarrow> k'\<close> \<open>k' cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> using less cd_split by blast
  hence icdk: \<open>i' cd\<^bsup>\<pi>\<^esup>\<rightarrow> k'\<close> using is_icdi_def by auto
  note ih=less(3)[OF k'(2)  _ k'(1)]
  have ki: \<open>k' < i'\<close> using k' is_icdi_def is_cdi_def by auto
  have \<open>P k'\<close> using less(1)[OF ki k'(2) ] less(3) by auto
  thus \<open>P i'\<close> using ih by simp
qed

lemma cdi_prefix: \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> m \<Longrightarrow> m < n' \<Longrightarrow> n' \<le> n \<Longrightarrow> n' cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close>  unfolding is_cdi_def 
  by (simp, metis term_path_stable)

lemma cr_wn': assumes 1: \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> and nc: \<open>\<not> m' cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> and 3: \<open>m < m'\<close> shows \<open>n < m'\<close>
proof (rule ccontr)
  assume \<open>\<not> n < m'\<close>
  hence \<open>m' \<le> n\<close> by simp  
  hence \<open>m' cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> by (metis 1 3 cdi_prefix)
  thus \<open>False\<close> using nc by simp
qed

lemma cr_wn'': assumes \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> and \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> and \<open>\<not> m cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> and  \<open>i \<le> j\<close> shows \<open>m \<le> n\<close> proof (rule ccontr) 
  assume \<open>\<not>m\<le>n\<close>
  hence nm: \<open>n < m\<close> by auto
  moreover 
  have \<open>m<j\<close> using assms(1) assms(4) unfolding is_cdi_def by auto
  ultimately 
  have \<open>m cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> using assms(2) cdi_prefix by auto
  thus \<open>False\<close> using assms(3) by auto
qed

lemma ret_no_cd: assumes \<open>\<pi> n = return\<close> shows \<open>\<not> n cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> by (metis assms is_cdi_def)

lemma ipd_not_self: assumes \<open>x \<in> nodes\<close> \<open>x\<noteq> return\<close> shows \<open>x \<noteq> ipd x\<close> by (metis is_ipd_def assms ipd_is_ipd)

lemma icd_cs: assumes \<open>l icd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>\<^esup> k @ [\<pi> l]\<close>
proof -
  from assms have \<open>k = (THE k. l icd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close> by (metis icd_is_the_icd)
  with assms show \<open>?thesis\<close> by auto
qed

lemma cd_not_pd: assumes \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> \<open>\<pi> l \<noteq> \<pi> k\<close> shows \<open>\<not> \<pi> l pd\<rightarrow> \<pi> k\<close> proof
  assume pd: \<open>\<pi> l pd\<rightarrow> \<pi> k\<close>
  have nret: \<open>\<pi> k \<noteq> return\<close> by (metis assms(1) pd pd_ret_is_ret ret_no_cd)
  have kl: \<open>k < l\<close> by (metis is_cdi_def assms(1))
  have path: \<open>is_path \<pi>\<close> by (metis is_cdi_def assms(1))
  from path_pd_ipd[OF path nret assms(2) pd kl]
  obtain n where \<open>k < n\<close> \<open>n \<le> l\<close> \<open>\<pi> n = ipd (\<pi> k)\<close> .
  thus \<open>False\<close> using assms(1) unfolding is_cdi_def by auto
qed

lemma cd_ipd_is_cd: assumes \<open>k<m\<close> \<open>\<pi> m = ipd (\<pi> k)\<close> \<open>\<forall> n \<in> {k..<m}. \<pi> n \<noteq> ipd (\<pi> k)\<close> and mcdj: \<open>m cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> shows \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> proof cases
  assume \<open>j < k\<close> thus \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> by (metis mcdj assms(1) cdi_prefix less_imp_le_nat)
next
  assume \<open>\<not> j < k\<close>
  hence kj: \<open>k \<le> j\<close> by simp 
  have \<open>k < j\<close> apply (rule ccontr) using kj assms mcdj by (auto, metis is_cdi_def is_ipd_def cd_not_pd ipd_is_ipd path_nodes term_path_stable less_imp_le)
  moreover 
  have \<open>j < m\<close> using mcdj is_cdi_def by auto
  hence \<open>\<forall> n \<in> {k..j}. \<pi> n \<noteq> ipd(\<pi> k)\<close> using assms(3) by force
  ultimately
  have \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> by (metis mcdj is_cdi_def term_path_stable less_imp_le)
  hence \<open>m cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> by (metis mcdj cd_trans)
  hence \<open>False\<close> by (metis is_cdi_def is_ipd_def assms(2) cd_not_pd ipd_is_ipd path_nodes term_path_stable less_imp_le)
  thus \<open>?thesis\<close> by simp
qed

lemma ipd_pd_cd0: assumes lcd: \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close> shows \<open>ipd (\<pi> 0) pd\<rightarrow> (\<pi> n)\<close> 
proof -
  obtain k l where \<pi>0: \<open>\<pi> 0 = k\<close> and \<pi>n: \<open>\<pi> n = l\<close> and cdi: \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> 0\<close> using lcd unfolding is_cdi_def by blast
  have nret: \<open>k \<noteq> return\<close> by (metis is_cdi_def \<pi>0 cdi term_path_stable less_imp_le)
  have  path: \<open>is_path \<pi>\<close> and ipd: \<open>\<forall> i\<le>n. \<pi> i \<noteq> ipd k\<close> using cdi unfolding is_cdi_def \<pi>0 by auto
  {
    fix \<pi>' n'
    assume path': \<open>is_path \<pi>'\<close>
    and \<pi>'0: \<open>\<pi>' 0 = l\<close>
    and ret: \<open>\<pi>' n' = return\<close>
    have \<open>is_path (\<pi> @\<^bsup>n\<^esup>  \<pi>')\<close> using path path' \<pi>n \<pi>'0 by (metis path_cons)
    moreover
    have \<open>(\<pi> @\<^bsup>n\<^esup>  \<pi>') (n+n') = return\<close> using ret \<pi>n \<pi>'0 by auto
    moreover
    have \<open>(\<pi> @\<^bsup>n\<^esup>  \<pi>') 0 = k\<close> using \<pi>0 by auto
    moreover    
    have \<open>ipd k pd\<rightarrow> k\<close> by (metis is_ipd_def path \<pi>0 ipd_is_ipd nret path_nodes)
    ultimately
    obtain k' where k': \<open>k' \<le> n+n'\<close> \<open>(\<pi> @\<^bsup>n\<^esup>  \<pi>') k' = ipd k\<close> by (metis pd_intro)
    have \<open>\<not> k'\<le> n\<close> proof 
      assume \<open>k' \<le> n\<close> 
      hence \<open>(\<pi> @\<^bsup>n\<^esup>  \<pi>') k' = \<pi> k'\<close> by auto
      thus \<open>False\<close> using k'(2) ipd by (metis \<open>k' \<le> n\<close>)
    qed
    hence \<open>(\<pi> @\<^bsup>n\<^esup>  \<pi>') k' = \<pi>' (k' - n)\<close> by auto
    moreover 
    have \<open>(k' - n) \<le> n'\<close> using k' by simp
    ultimately
    have \<open>\<exists> k'\<le>n'. \<pi>' k' = ipd k\<close> unfolding k' by auto
  }
  moreover
  have \<open>l \<in> nodes\<close> by (metis \<pi>n path path_nodes)
  ultimately show \<open>ipd (\<pi> 0) pd\<rightarrow> (\<pi> n)\<close> unfolding is_pd_def  by (simp add: \<pi>0 \<pi>n) 
qed

lemma ipd_pd_cd: assumes lcd: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> shows \<open>ipd (\<pi> k) pd\<rightarrow> (\<pi> l)\<close> 
proof - 
  have \<open>l-k cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow>0\<close> using lcd cd_path_shift0 is_cdi_def by blast 
  moreover
  note ipd_pd_cd0[OF this]
  moreover 
  have \<open>(\<pi> \<guillemotleft> k) 0 = \<pi> k\<close> by auto
  moreover
  have \<open>k < l\<close> using lcd unfolding is_cdi_def by simp
  then have \<open>(\<pi> \<guillemotleft> k) (l - k) = \<pi> l\<close> by simp 
  ultimately show \<open>?thesis\<close> by simp
qed

lemma cd_is_cd_ipd: assumes km: \<open>k<m\<close> and ipd: \<open>\<pi> m = ipd (\<pi> k)\<close> \<open>\<forall> n \<in> {k..<m}. \<pi> n \<noteq> ipd (\<pi> k)\<close> and cdj: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> and nipdj: \<open>ipd (\<pi> j) \<noteq> \<pi> m\<close> shows \<open>m cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> proof -
  have path: \<open>is_path \<pi>\<close> 
  and jk: \<open>j < k\<close> 
  and nretj: \<open>\<pi> k \<noteq> return\<close> 
  and nipd: \<open>\<forall> l \<in> {j..k}. \<pi> l \<noteq> ipd (\<pi> j)\<close> using  cdj is_cdi_def by auto
  have pd: \<open>ipd (\<pi> j) pd\<rightarrow> \<pi> m\<close> by (metis atLeastAtMost_iff cdj ipd(1) ipd_pd_cd jk le_refl less_imp_le nipd nretj path path_nodes pd_pd_ipd)  
  have nretm: \<open>\<pi> m \<noteq> return\<close> by (metis nipdj pd pd_ret_is_ret)
  have jm: \<open>j < m\<close> using jk km by simp
  show \<open>m cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> proof (rule ccontr)
    assume ncdj: \<open>\<not> m cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close>     
    hence \<open>\<exists> l \<in> {j..m}. \<pi> l = ipd (\<pi> j)\<close> unfolding is_cdi_def by (metis jm nretm path)
    then obtain l 
    where jl: \<open>j \<le> l\<close> and \<open>l \<le> m\<close> 
    and lipd: \<open>\<pi> l = ipd (\<pi> j)\<close> by force
    hence lm: \<open>l < m\<close> using nipdj by (metis le_eq_less_or_eq)
    have npd: \<open>\<not> ipd (\<pi> k) pd\<rightarrow> \<pi> l\<close> by (metis ipd(1) lipd nipdj pd pd_antisym)
    have nd: \<open>\<pi> l \<in> nodes\<close> using path path_nodes by simp
    from no_pd_path[OF nd npd]
    obtain \<pi>' n where path': \<open>is_path \<pi>'\<close> and \<pi>'0: \<open>\<pi>' 0 = \<pi> l\<close> and \<pi>'n: \<open>\<pi>' n = return\<close> and nipd: \<open>\<forall> ka\<le>n. \<pi>' ka \<noteq> ipd (\<pi> k)\<close> .
    let \<open>?\<pi>\<close> = \<open>(\<pi>@\<^bsup>l\<^esup> \<pi>') \<guillemotleft> k\<close>
    have path'': \<open>is_path ?\<pi>\<close> by (metis \<pi>'0 path path' path_cons path_path_shift)
    moreover
    have kl: \<open>k < l\<close> using lipd cdj jl unfolding is_cdi_def by fastforce    
    have \<open>?\<pi> 0 = \<pi> k\<close> using kl by auto
    moreover
    have \<open>?\<pi> (l + n - k) = return\<close> using \<pi>'n \<pi>'0 kl by auto
    moreover
    have \<open>ipd (\<pi> k) pd\<rightarrow> \<pi> k\<close> by (metis is_ipd_def ipd_is_ipd nretj path path_nodes)
    ultimately
    obtain l' where l': \<open>l' \<le> (l + n - k)\<close> \<open>?\<pi> l' = ipd (\<pi> k)\<close> unfolding is_pd_def by blast
    show \<open>False\<close> proof (cases )
      assume *: \<open>k + l' \<le> l\<close>
      hence \<open>\<pi> (k + l') = ipd (\<pi> k)\<close> using l' by auto
      moreover 
      have \<open>k + l' < m\<close> by (metis "*" dual_order.strict_trans2 lm)
      ultimately
      show \<open>False\<close> using ipd(2) by simp
    next
      assume \<open>\<not> k + l' \<le> l\<close>
      hence \<open>\<pi>' (k + l' - l) = ipd (\<pi> k)\<close> using l' by auto
      moreover
      have \<open>k + l' - l \<le> n\<close> using l' kl by linarith  
      ultimately 
      show \<open>False\<close> using nipd by auto
    qed
  qed
qed

lemma ipd_icd_greatest_cd_not_ipd: assumes ipd: \<open>\<pi> m = ipd (\<pi> k)\<close> \<open>\<forall> n \<in> {k..<m}. \<pi> n \<noteq> ipd (\<pi> k)\<close>
and km: \<open>k < m\<close> and icdj: \<open>m icd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> shows \<open>j = (GREATEST j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> ipd (\<pi> j) \<noteq> \<pi> m)\<close>
proof -
  let \<open>?j\<close> = \<open>GREATEST j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> ipd (\<pi> j) \<noteq> \<pi> m\<close>
  have kcdj: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using assms cd_ipd_is_cd is_icdi_def by blast   
  have nipd: \<open>ipd (\<pi> j) \<noteq> \<pi> m\<close> using icdj unfolding is_icdi_def is_cdi_def by auto
  have bound: \<open>\<And> j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> ipd (\<pi> j) \<noteq> \<pi> m \<Longrightarrow> j \<le> k\<close> unfolding is_cdi_def by simp
  have exists: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> ipd (\<pi> j) \<noteq> \<pi> m\<close> (is \<open>?P j\<close>) using kcdj nipd by auto
  note GreatestI_nat[of \<open>?P\<close> _ \<open>k\<close>, OF exists] Greatest_le_nat[of \<open>?P\<close> \<open>j\<close> \<open>k\<close>, OF exists]
  hence kcdj': \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> ?j\<close> and ipd': \<open>ipd (\<pi> ?j) \<noteq> \<pi> m\<close> and jj: \<open>j \<le> ?j\<close> using bound by auto
  hence mcdj': \<open>m cd\<^bsup>\<pi>\<^esup>\<rightarrow> ?j\<close> using ipd km cd_is_cd_ipd by auto
  show \<open>j = ?j\<close> proof (rule ccontr)
    assume \<open>j \<noteq> ?j\<close>
    hence jlj: \<open>j < ?j\<close> using jj by simp
    moreover 
    have \<open>?j < m\<close> using kcdj' km unfolding is_cdi_def by auto
    ultimately
    show \<open>False\<close> using icdj mcdj' unfolding is_icdi_def by auto
  qed
qed

lemma cd_impl_icd_cd: assumes \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> and \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> and \<open>\<not> i icd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> shows \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close>
  using assms cd_split icd_uniq by metis

lemma cdi_is_cd_icdi: assumes \<open>k icd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> shows \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<longleftrightarrow> j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<or> i = j\<close> 
  by (metis assms cd_impl_icd_cd cd_trans icd_imp_cd icd_uniq)

lemma same_ipd_stable: assumes \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> \<open>i<j\<close> \<open>ipd (\<pi> i) = ipd (\<pi> k)\<close> shows \<open>ipd (\<pi> j) = ipd (\<pi> k)\<close>
proof -
  have jcdi: \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> by (metis is_cdi_def assms(1,2,3) cr_wn' le_antisym less_imp_le_nat)
  have 1: \<open>ipd (\<pi> j) pd\<rightarrow> \<pi> k \<close> by (metis assms(2) ipd_pd_cd)
  have 2: \<open>ipd (\<pi> k) pd\<rightarrow> \<pi> j \<close> by (metis assms(4) ipd_pd_cd jcdi)
  have 3: \<open>ipd (\<pi> k) pd\<rightarrow> (ipd (\<pi> j))\<close>  by (metis 2 IFC_def.is_cdi_def assms(1,2,4) atLeastAtMost_iff jcdi less_imp_le pd_node2 pd_pd_ipd) 
  have 4: \<open>ipd (\<pi> j) pd\<rightarrow> (ipd (\<pi> k))\<close> by (metis 1 2 IFC_def.is_ipd_def assms(2) cd_not_pd ipd_is_ipd jcdi pd_node2 ret_no_cd) 
  show \<open>?thesis\<close> using 3 4 pd_antisym by simp
qed

lemma icd_pd_intermediate': assumes icd: \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>  and j: \<open>k < j\<close> \<open>j < i\<close> shows \<open>\<pi> i pd\<rightarrow> (\<pi> j)\<close>
using j proof (induction \<open>i - j\<close> arbitrary: \<open>j\<close> rule: less_induct)
  case (less j)
  have \<open>\<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using less.prems icd unfolding is_icdi_def by force
  moreover 
  have \<open>is_path \<pi>\<close> using icd by (metis is_icdi_def)
  moreover 
  have \<open>\<pi> i \<noteq> return\<close> using icd by (metis is_icdi_def ret_no_cd)
  ultimately
  have \<open>\<exists> l. j \<le> l \<and> l \<le> i \<and> \<pi> l = ipd (\<pi> j)\<close> unfolding is_cdi_def using less.prems by auto
  then obtain l where l: \<open>j \<le> l\<close> \<open>l \<le> i\<close> \<open>\<pi> l = ipd (\<pi> j)\<close> by blast
  hence lpd: \<open>\<pi> l pd\<rightarrow> (\<pi> j)\<close> by (metis is_ipd_def \<open>\<pi> i \<noteq> return\<close> \<open>is_path \<pi>\<close> ipd_is_ipd path_nodes term_path_stable)
  show \<open>?case\<close> proof (cases)
    assume \<open>l = i\<close>
    thus \<open>?case\<close> using lpd by auto
  next
    assume \<open>l \<noteq> i\<close>
    hence \<open>l < i\<close> using l by simp
    moreover
    have \<open>j \<noteq> l\<close> using l by (metis is_ipd_def \<open>\<pi> i \<noteq> return\<close> \<open>is_path \<pi>\<close> ipd_is_ipd path_nodes term_path_stable)
    hence \<open>j < l\<close> using l by simp
    moreover 
    hence \<open>i - l < i - j\<close> by (metis diff_less_mono2 less.prems(2))
    moreover
    have \<open>k < l\<close> by (metis l(1) less.prems(1) linorder_neqE_nat not_le order.strict_trans)
    ultimately
    have \<open>\<pi> i pd\<rightarrow> (\<pi> l)\<close> using less.hyps by auto
    thus \<open>?case\<close> using lpd by (metis pd_trans)
  qed
qed

lemma icd_pd_intermediate: assumes icd: \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>  and j: \<open>k < j\<close> \<open>j \<le> i\<close> shows \<open>\<pi> i pd\<rightarrow> (\<pi> j)\<close> 
using assms icd_pd_intermediate'[OF assms(1,2)] apply (cases \<open>j < i\<close>,metis) by (metis is_icdi_def le_neq_trans path_nodes pd_refl)

lemma no_icd_pd: assumes path: \<open>is_path \<pi>\<close> and noicd: \<open>\<forall> l\<ge>n. \<not> k icd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> and nk: \<open>n \<le> k\<close> shows \<open>\<pi> k pd\<rightarrow> \<pi> n\<close>
proof cases
  assume \<open>\<pi> k = return\<close> thus \<open>?thesis\<close> by (metis path path_nodes return_pd)  
next
  assume nret: \<open>\<pi> k \<noteq> return\<close>
  have nocd: \<open>\<And> l. n\<le>l \<Longrightarrow> \<not> k cd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> proof 
    fix l assume kcd: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> and nl: \<open>n \<le> l\<close>
    hence \<open>(k - n) cd\<^bsup>\<pi>\<guillemotleft>n\<^esup>\<rightarrow> (l - n)\<close> using cd_path_shift[OF nl path] by simp
    hence \<open>\<exists> l. (k - n) icd\<^bsup>\<pi>\<guillemotleft>n\<^esup>\<rightarrow> l\<close> using excd_impl_exicd by blast
    then guess l' ..
    hence \<open>k icd\<^bsup>\<pi>\<^esup>\<rightarrow> (l' + n)\<close> using icd_path_shift[of \<open>n\<close> \<open>l' + n\<close> \<open>\<pi>\<close> \<open>k\<close>] path by auto
    thus \<open>False\<close> using noicd by auto
  qed    
  hence \<open>\<And>l. n \<le> l \<Longrightarrow> l<k \<Longrightarrow> \<exists> j \<in> {l..k}. \<pi> j = ipd (\<pi> l)\<close> using path nret unfolding is_cdi_def by auto 
  thus \<open>?thesis\<close> using nk proof (induction \<open>k - n\<close> arbitrary: \<open>n\<close> rule: less_induct,cases)
    case (less n) 
    assume \<open>n = k\<close>
    thus \<open>?case\<close> using pd_refl path path_nodes by auto
  next
    case (less n)
    assume \<open>n \<noteq> k\<close>
    hence nk: \<open>n < k\<close> using less(3) by auto
    with less(2) obtain j where jnk: \<open>j \<in> {n..k}\<close> and ipdj: \<open>\<pi> j = ipd (\<pi> n)\<close> by blast
    have nretn: \<open>\<pi> n \<noteq> return\<close> using nk nret term_path_stable path by auto
    with ipd_is_ipd path path_nodes is_ipd_def ipdj
    have jpdn: \<open>\<pi> j pd\<rightarrow> \<pi> n\<close> by auto
    show \<open>?case\<close> proof cases
      assume \<open>j = k\<close> thus \<open>?case\<close> using jpdn by simp
    next
      assume \<open>j \<noteq> k\<close>
      hence jk: \<open>j < k\<close> using jnk by auto
      have \<open>j \<noteq> n\<close> using ipdj by (metis ipd_not_self nretn path path_nodes)
      hence nj: \<open>n < j\<close> using jnk by auto
      have *: \<open>k - j < k - n\<close> using jk nj by auto
      
      with less(1)[OF *] less(2) jk nj
      have \<open>\<pi> k pd\<rightarrow> \<pi> j\<close> by auto

      thus \<open>?thesis\<close> using jpdn pd_trans by metis
    qed
  qed
qed


lemma first_pd_no_cd: assumes path: \<open>is_path \<pi>\<close> and pd: \<open>\<pi> n pd\<rightarrow> \<pi> 0\<close> and first: \<open>\<forall> l < n. \<pi> l \<noteq> \<pi> n\<close> shows \<open>\<forall> l. \<not> n cd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> 
proof (rule ccontr, goal_cases)
  case 1
  then obtain l where ncdl: \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> by blast
  hence ln: \<open>l < n\<close> using is_cdi_def by auto
  have \<open>\<not> \<pi> n pd\<rightarrow> \<pi> l\<close> using ncdl cd_not_pd by (metis ln first)
  then obtain \<pi>' n' where path': \<open>is_path \<pi>'\<close> and \<pi>0: \<open>\<pi>' 0 = \<pi> l\<close> and \<pi>n: \<open>\<pi>' n' = return\<close> and not\<pi>n: \<open>\<forall> j\<le> n'. \<pi>' j \<noteq> \<pi> n\<close> unfolding is_pd_def using path path_nodes by auto
  let \<open>?\<pi>\<close> = \<open>\<pi>@\<^bsup>l\<^esup> \<pi>'\<close>
  
  have \<open>is_path ?\<pi>\<close> by (metis \<pi>0 path path' path_cons)
  moreover
  have \<open>?\<pi> 0 = \<pi> 0\<close> by auto
  moreover
  have \<open>?\<pi> (n' + l) = return\<close> using \<pi>0 \<pi>n by auto
  ultimately
  obtain j where j: \<open>j \<le> n' + l\<close> and jn: \<open>?\<pi> j = \<pi> n\<close> using pd unfolding is_pd_def by blast
  show \<open>False\<close> proof cases
    assume \<open>j \<le> l\<close> thus \<open>False\<close> using jn first ln by auto
  next
    assume \<open>\<not> j \<le> l\<close> thus \<open>False\<close> using j jn not\<pi>n by auto
  qed
qed

lemma first_pd_no_icd: assumes path: \<open>is_path \<pi>\<close> and pd: \<open>\<pi> n pd\<rightarrow> \<pi> 0\<close> and first: \<open>\<forall> l < n. \<pi> l \<noteq> \<pi> n\<close> shows \<open>\<forall> l. \<not> n icd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close>
  by (metis first first_pd_no_cd icd_imp_cd path pd)

lemma path_nret_ex_nipd: assumes \<open>is_path \<pi>\<close> \<open>\<forall> i. \<pi> i \<noteq> return\<close> shows \<open>\<forall> i. (\<exists> j\<ge>i. (\<forall> k>j. \<pi> k \<noteq> ipd (\<pi> j)))\<close> proof(rule, rule ccontr)
  fix i
  assume \<open>\<not> (\<exists>j\<ge>i. \<forall> k>j. \<pi> k \<noteq> ipd (\<pi> j))\<close>
  hence *: \<open>\<forall> j\<ge>i. (\<exists>k>j. \<pi> k = ipd (\<pi> j))\<close> by blast
  have \<open>\<forall> j. (\<exists>k>j. (\<pi>\<guillemotleft>i) k = ipd ((\<pi>\<guillemotleft>i) j))\<close> proof
    fix j
    have \<open>i + j \<ge> i\<close> by auto
    then obtain k where k: \<open>k>i+j\<close> \<open>\<pi> k = ipd (\<pi> (i+j))\<close> using * by blast
    hence \<open>(\<pi>\<guillemotleft>i) (k - i) = ipd ((\<pi>\<guillemotleft>i) j)\<close> by auto
    moreover  
    have \<open>k - i > j\<close> using k by auto
    ultimately
    show \<open>\<exists>k>j. (\<pi>\<guillemotleft>i) k = ipd ((\<pi>\<guillemotleft>i) j)\<close> by auto
  qed
  moreover
  have \<open>is_path (\<pi>\<guillemotleft>i)\<close> using assms(1) path_path_shift by simp
  ultimately
  obtain k where \<open>(\<pi>\<guillemotleft>i) k = return\<close> using all_ipd_imp_ret by blast
  thus \<open>False\<close> using assms(2) by auto
qed

lemma path_nret_ex_all_cd: assumes \<open>is_path \<pi>\<close> \<open>\<forall> i. \<pi> i \<noteq> return\<close> shows \<open>\<forall> i. (\<exists> j\<ge>i. (\<forall> k>j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j))\<close>
unfolding is_cdi_def using assms path_nret_ex_nipd[OF assms] by (metis atLeastAtMost_iff ipd_not_self linorder_neqE_nat not_le path_nodes)


lemma path_nret_inf_all_cd: assumes \<open>is_path \<pi>\<close> \<open>\<forall> i. \<pi> i \<noteq> return\<close> shows \<open>\<not> finite {j. \<forall> k>j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j}\<close> 
using unbounded_nat_set_infinite path_nret_ex_all_cd[OF assms] by auto

lemma path_nret_inf_icd_seq: assumes path: \<open>is_path \<pi>\<close> and nret: \<open>\<forall> i. \<pi> i \<noteq> return\<close> 
obtains f where \<open>\<forall> i. f (Suc i) icd\<^bsup>\<pi>\<^esup>\<rightarrow> f i\<close> \<open>range f = {i. \<forall> j>i. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}\<close> \<open>\<not> (\<exists>i. f 0 cd\<^bsup>\<pi>\<^esup>\<rightarrow> i)\<close>
proof -
  note path_nret_inf_all_cd[OF assms]
  then obtain f where ran: \<open>range f = {j. \<forall> k>j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j}\<close> and asc: \<open>\<forall> i. f i < f (Suc i)\<close> using infinite_ascending by blast
  have mono: \<open>\<forall> i j. i < j \<longrightarrow> f i < f j\<close> using asc by (metis lift_Suc_mono_less)
  {
    fix i
    have cd: \<open>f (Suc i) cd\<^bsup>\<pi>\<^esup>\<rightarrow> f i\<close> using ran asc by auto
    have \<open>f (Suc i) icd\<^bsup>\<pi>\<^esup>\<rightarrow> f i\<close> proof (rule ccontr)
      assume \<open>\<not> f (Suc i) icd\<^bsup>\<pi>\<^esup>\<rightarrow> f i\<close>
      then obtain m where  im: \<open>f i < m\<close> and mi: \<open> m < f (Suc i)\<close> and cdm: \<open>f (Suc i) cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> unfolding is_icdi_def using assms(1) cd by auto
      have \<open>\<forall> k>m. k cd\<^bsup>\<pi>\<^esup>\<rightarrow>m\<close> proof (rule,rule,cases)
        fix k assume \<open>f (Suc i) < k\<close>
        hence \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> f (Suc i)\<close> using ran by auto
        thus \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using cdm cd_trans by metis
      next
        fix k assume mk: \<open>m < k\<close> and \<open>\<not> f (Suc i) < k\<close>
        hence ik: \<open>k \<le> f (Suc i)\<close> by simp
        thus \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using cdm by (metis cdi_prefix mk)
      qed
      hence \<open>m \<in> range f\<close> using ran by blast
      then obtain j where m: \<open>m = f j\<close> by blast
      show \<open>False\<close> using im mi mono unfolding m by (metis Suc_lessI le_less not_le)
    qed
  }
  moreover  
  {
    fix m
    assume cdm: \<open>f 0 cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close>
    have \<open>\<forall> k>m. k cd\<^bsup>\<pi>\<^esup>\<rightarrow>m\<close> proof (rule,rule,cases)
      fix k assume \<open>f 0 < k\<close>
      hence \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> f 0\<close> using ran by auto
      thus \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using cdm cd_trans by metis
    next
      fix k assume mk: \<open>m < k\<close> and \<open>\<not> f 0 < k\<close>
      hence ik: \<open>k \<le> f 0\<close> by simp
      thus \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using cdm by (metis cdi_prefix mk)
    qed
    hence \<open>m \<in> range f\<close> using ran by blast
    then obtain j where m: \<open>m = f j\<close> by blast
    hence fj0: \<open>f j < f 0\<close>  using cdm m is_cdi_def by auto
    hence \<open>0 < j\<close> by (metis less_irrefl neq0_conv)
    hence \<open>False\<close> using fj0 mono by fastforce
  }
  ultimately show \<open>thesis\<close> using that ran by blast
qed

lemma cdi_iff_no_strict_pd: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k \<longleftrightarrow> is_path \<pi> \<and> k < i \<and> \<pi> i \<noteq> return \<and> (\<forall> j \<in> {k..i}. \<not> (\<pi> k, \<pi> j) \<in> pdt)\<close>
proof
  assume cd:\<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>
  have 1: \<open>is_path \<pi> \<and> k < i \<and> \<pi> i \<noteq> return\<close> using cd unfolding is_cdi_def by auto
  have 2: \<open>\<forall> j \<in> {k..i}. \<not> (\<pi> k, \<pi> j) \<in> pdt\<close> proof (rule ccontr)
    assume \<open> \<not> (\<forall>j\<in>{k..i}. (\<pi> k, \<pi> j) \<notin> pdt)\<close>
    then obtain j where \<open>j \<in> {k..i}\<close> and \<open>(\<pi> k, \<pi> j) \<in> pdt\<close> by auto
    hence \<open>\<pi> j \<noteq> \<pi> k\<close> and \<open>\<pi> j pd\<rightarrow> \<pi> k\<close> unfolding pdt_def by auto
    thus \<open>False\<close> using path_pd_ipd by (metis \<open>j \<in> {k..i}\<close> atLeastAtMost_iff cd cd_not_pd cdi_prefix le_eq_less_or_eq) 
  qed
  show \<open>is_path \<pi> \<and> k < i \<and> \<pi> i \<noteq> return \<and> (\<forall> j \<in> {k..i}. \<not> (\<pi> k, \<pi> j) \<in> pdt)\<close> using 1 2 by simp
next
  assume \<open>is_path \<pi> \<and> k < i \<and> \<pi> i \<noteq> return \<and> (\<forall> j \<in> {k..i}. \<not> (\<pi> k, \<pi> j) \<in> pdt)\<close>
  thus \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> by (metis ipd_in_pdt term_path_stable less_or_eq_imp_le not_cd_impl_ipd path_nodes)
qed


subsection \<open>Facts about Control Slices\<close>

lemma last_cs: \<open>last (cs\<^bsup>\<pi>\<^esup> i) = \<pi> i\<close> by auto

lemma cs_not_nil: \<open>cs\<^bsup>\<pi>\<^esup> n \<noteq> []\<close> by (auto)

lemma cs_return: assumes \<open>\<pi> n = return\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> n = [\<pi> n]\<close> by (metis assms cs.elims icd_imp_cd ret_no_cd)

lemma cs_0[simp]: \<open>cs\<^bsup>\<pi>\<^esup> 0 = [\<pi> 0]\<close> using is_icdi_def is_cdi_def by auto

lemma cs_inj: assumes \<open>is_path \<pi>\<close> \<open>\<pi> n \<noteq> return\<close> \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>\<^esup> n'\<close> shows \<open>n = n'\<close> 
using assms proof (induction \<open>cs\<^bsup>\<pi>\<^esup> n\<close> arbitrary: \<open>\<pi>\<close> \<open>n\<close> \<open>n'\<close> rule:rev_induct)
  case Nil hence \<open>False\<close> using cs_not_nil by metis thus \<open>?case\<close> by simp
next
  case (snoc x xs \<pi> n n') show \<open>?case\<close> proof (cases \<open>xs\<close>)
  case Nil 
  hence *: \<open>\<not> (\<exists> k. n icd\<^bsup>\<pi>\<^esup>\<rightarrow>k)\<close> using snoc(2) cs_not_nil 
    by (auto,metis append1_eq_conv append_Nil cs_not_nil)
  moreover
  have \<open>[x] = cs\<^bsup>\<pi>\<^esup> n'\<close> using Nil snoc by auto
  hence **: \<open>\<not> (\<exists> k. n' icd\<^bsup>\<pi>\<^esup>\<rightarrow>k)\<close> using cs_not_nil
    by (auto,metis append1_eq_conv append_Nil cs_not_nil)
  ultimately
  have \<open>\<forall> k. \<not> n cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> \<open>\<forall> k. \<not> n' cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> using excd_impl_exicd by auto blast+
  moreover 
  hence  \<open>\<pi> n = \<pi> n'\<close> using snoc(5,2) by auto (metis * ** list.inject)
  ultimately
  show \<open>n = n'\<close> using other_claim' snoc by blast
next
  case (Cons y ys)
  hence *: \<open>\<exists> k. n icd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> using snoc(2) by auto (metis append_is_Nil_conv list.distinct(1) list.inject)
  then obtain k where k: \<open>n icd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> by auto
  have \<open>k = (THE k . n icd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close> using k by (metis icd_is_the_icd)
  hence xsk: \<open>xs = cs\<^bsup>\<pi>\<^esup> k\<close> using * k snoc(2) unfolding cs.simps[of \<open>\<pi>\<close> \<open>n\<close>] by auto
  have **: \<open>\<exists> k. n' icd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> using snoc(2)[unfolded snoc(5)] by auto (metis Cons append1_eq_conv append_Nil list.distinct(1))
  then obtain k' where k': \<open>n' icd\<^bsup>\<pi>\<^esup>\<rightarrow> k'\<close> by auto
  hence \<open>k' = (THE k . n' icd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close> using k' by (metis icd_is_the_icd)
  hence xsk': \<open>xs = cs\<^bsup>\<pi>\<^esup> k'\<close> using ** k' snoc(5,2) unfolding cs.simps[of \<open>\<pi>\<close> \<open>n'\<close>] by auto
  hence \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>\<^esup> k'\<close> using xsk by simp
  moreover
  have kn: \<open>k < n\<close> using k by (metis is_icdi_def is_cdi_def)
  hence \<open>\<pi> k \<noteq> return\<close> using snoc by (metis term_path_stable less_imp_le)
  ultimately
  have kk'[simp]: \<open>k' = k\<close> using snoc(1) xsk snoc(3) by metis
  have nk0: \<open>n - k icd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> 0\<close> \<open>n' - k icd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> 0\<close> using k k' icd_path_shift0 snoc(3) by auto
  moreover 
  have nkr: \<open>(\<pi>\<guillemotleft>k)(n-k) \<noteq> return\<close> using snoc(4) kn by auto
  moreover 
  have \<open>is_path (\<pi>\<guillemotleft>k)\<close> by (metis path_path_shift snoc.prems(1))
  moreover 
  have kn': \<open>k < n'\<close> using k' kk' by (metis is_icdi_def is_cdi_def)
  have \<open>\<pi> n = \<pi> n'\<close> using snoc(5) * ** by auto
  hence \<open>(\<pi>\<guillemotleft>k)(n-k) = (\<pi>\<guillemotleft>k)(n'-k)\<close> using kn kn' by auto 
  ultimately  
  have \<open>n - k = n' - k\<close> using other_claim  by auto
  thus \<open>n = n'\<close> using kn kn' by auto
qed
qed

lemma cs_cases: fixes \<pi> i 
obtains (base) \<open>cs\<^bsup>\<pi>\<^esup> i = [\<pi> i]\<close> and \<open>\<forall> k. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> | 
(depend) k where  \<open>cs\<^bsup>\<pi>\<^esup> i = (cs\<^bsup>\<pi>\<^esup> k)@[\<pi> i]\<close> and \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> 
proof cases
  assume *: \<open>\<exists> k. i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>
  then obtain k where k: \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> ..
  hence \<open>k = (THE k. i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close>  by (metis icd_is_the_icd)
  hence \<open>cs\<^bsup>\<pi>\<^esup> i = (cs\<^bsup>\<pi>\<^esup> k)@[\<pi> i]\<close> using * by auto
  with k that show \<open>thesis\<close> by simp
next
  assume *: \<open>\<not> (\<exists> k. i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close>
  hence \<open>\<forall> k. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> by (metis excd_impl_exicd)
  moreover 
  have \<open>cs\<^bsup>\<pi>\<^esup> i = [\<pi> i]\<close> using * by auto
  ultimately
  show \<open>thesis\<close> using that by simp
qed

lemma cs_length_one: assumes \<open>length (cs\<^bsup>\<pi>\<^esup> i) = 1\<close> shows  \<open>cs\<^bsup>\<pi>\<^esup> i = [\<pi> i]\<close> and \<open>\<forall> k. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>
  apply (cases \<open>i\<close> \<open>\<pi>\<close> rule: cs_cases)
  using assms cs_not_nil 
    apply auto 
  apply (cases \<open>i\<close> \<open>\<pi>\<close> rule: cs_cases) 
  using assms cs_not_nil 
  by auto

lemma cs_length_g_one: assumes \<open>length (cs\<^bsup>\<pi>\<^esup> i) \<noteq> 1\<close> obtains k where  \<open>cs\<^bsup>\<pi>\<^esup> i = (cs\<^bsup>\<pi>\<^esup> k)@[\<pi> i]\<close> and \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> 
  apply (cases \<open>i\<close> \<open>\<pi>\<close> rule: cs_cases) 
  using assms cs_not_nil by auto

lemma claim: assumes  path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and  ii: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> and jj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> 
and bl: \<open>butlast (cs\<^bsup>\<pi>\<^esup> i) = butlast (cs\<^bsup>\<pi>\<^esup> j)\<close> and nret: \<open>\<pi> i \<noteq> return\<close> and ilj: \<open>i < j\<close> 
shows \<open>i' < j'\<close>
proof (cases )
  assume *: \<open>length (cs\<^bsup>\<pi>\<^esup> i) = 1\<close>
  hence **: \<open>length (cs\<^bsup>\<pi>\<^esup> i) = 1\<close> \<open>length (cs\<^bsup>\<pi>\<^esup> j) = 1\<close> \<open>length (cs\<^bsup>\<pi>'\<^esup> i') = 1\<close> \<open>length (cs\<^bsup>\<pi>'\<^esup> j') = 1\<close>  
    apply metis
    apply (metis "*" bl butlast.simps(2) butlast_snoc cs_length_g_one cs_length_one(1) cs_not_nil) 
    apply (metis "*" ii)
    by (metis "*" bl butlast.simps(2) butlast_snoc cs_length_g_one cs_length_one(1) cs_not_nil jj)
  then obtain \<open>cs\<^bsup>\<pi>\<^esup> i = [\<pi> i]\<close> \<open>cs\<^bsup>\<pi>\<^esup> j = [\<pi> j]\<close> \<open>cs\<^bsup>\<pi>'\<^esup> j' = [\<pi>' j']\<close> \<open>cs\<^bsup>\<pi>'\<^esup> i'= [\<pi>' i']\<close> 
    \<open>\<forall> k. \<not> j cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> \<open>\<forall> k. \<not> i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k\<close> \<open>\<forall> k. \<not> j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k\<close>
  by (metis cs_length_one ** )
  moreover 
  hence \<open>\<pi> i = \<pi>' i'\<close> \<open>\<pi> j = \<pi>' j'\<close> using  assms by auto
  ultimately
  show \<open>i' < j'\<close> using nret ilj path claim'' by blast
next
  assume *: \<open>length (cs\<^bsup>\<pi>\<^esup> i) \<noteq> 1\<close>
  hence **: \<open>length (cs\<^bsup>\<pi>\<^esup> i) \<noteq> 1\<close> \<open>length (cs\<^bsup>\<pi>\<^esup> j) \<noteq> 1\<close> \<open>length (cs\<^bsup>\<pi>'\<^esup> i') \<noteq> 1\<close> \<open>length (cs\<^bsup>\<pi>'\<^esup> j') \<noteq> 1\<close>  
    apply metis
    apply (metis "*" bl butlast.simps(2) butlast_snoc cs_length_g_one cs_length_one(1) cs_not_nil)
    apply (metis "*" ii)
    by (metis "*" bl butlast.simps(2) butlast_snoc cs_length_g_one cs_length_one(1) cs_not_nil jj)
  obtain k l k' l' where ***:
    \<open>cs\<^bsup>\<pi>\<^esup> i = (cs\<^bsup>\<pi>\<^esup> k)@[\<pi> i]\<close> \<open>cs\<^bsup>\<pi>\<^esup> j = (cs\<^bsup>\<pi>\<^esup> l)@[\<pi> j]\<close>  \<open>cs\<^bsup>\<pi>'\<^esup> i' = (cs\<^bsup>\<pi>'\<^esup> k')@[\<pi>' i']\<close> \<open>cs\<^bsup>\<pi>'\<^esup> j' = (cs\<^bsup>\<pi>'\<^esup> l')@[\<pi>' j']\<close> and
    icds: \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> \<open>j icd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> \<open>i' icd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> \<open>j' icd\<^bsup>\<pi>'\<^esup>\<rightarrow> l'\<close>
    by (metis ** cs_length_g_one)
  hence \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>\<^esup> l\<close> \<open>cs\<^bsup>\<pi>'\<^esup> k' = cs\<^bsup>\<pi>'\<^esup> l'\<close> using assms by auto
  moreover
  have \<open>\<pi> k \<noteq> return\<close> \<open>\<pi>' k' \<noteq> return\<close> using nret 
    apply (metis is_icdi_def icds(1) is_cdi_def term_path_stable less_imp_le) 
    by (metis is_cdi_def is_icdi_def icds(3) term_path_stable less_imp_le)
  ultimately  
  have lk[simp]: \<open>l = k\<close> \<open>l' = k'\<close> using path cs_inj by auto
  let \<open>?\<pi>\<close> = \<open>\<pi> \<guillemotleft> k\<close> 
  let \<open>?\<pi>'\<close> = \<open>\<pi>'\<guillemotleft>k'\<close>
  have \<open>i-k icd\<^bsup>?\<pi>\<^esup>\<rightarrow> 0\<close> \<open>j-k icd\<^bsup>?\<pi>\<^esup>\<rightarrow> 0\<close> \<open>i'-k' icd\<^bsup>?\<pi>'\<^esup>\<rightarrow> 0\<close> \<open>j'-k' icd\<^bsup>?\<pi>'\<^esup>\<rightarrow> 0\<close> using icd_path_shift0 path icds by auto
  moreover
  have ki: \<open>k < i\<close> using icds by (metis is_icdi_def is_cdi_def)
  hence \<open>i-k < j-k\<close> by (metis diff_is_0_eq diff_less_mono ilj nat_le_linear order.strict_trans)
  moreover
  have \<pi>i: \<open>\<pi> i = \<pi>' i'\<close> \<open>\<pi> j = \<pi>' j'\<close> using assms *** by auto
  have \<open>k' < i'\<close> \<open>k' < j'\<close> using icds unfolding lk by (metis is_cdi_def is_icdi_def)+ 
  hence \<open>?\<pi> (i-k) = ?\<pi>' (i'-k')\<close> \<open>?\<pi> (j-k) = ?\<pi>' (j'-k')\<close> using \<pi>i ki ilj by auto
  moreover 
  have \<open>?\<pi> (i-k) \<noteq> return\<close> using nret ki by auto
  moreover
  have \<open>is_path ?\<pi>\<close> \<open>is_path ?\<pi>'\<close> using path path_path_shift by auto
  ultimately
  have \<open>i'-k' < j' - k'\<close> using claim' by blast
  thus \<open>i' < j'\<close> by (metis diff_is_0_eq diff_less_mono less_nat_zero_code linorder_neqE_nat nat_le_linear)
qed

lemma cs_split': assumes \<open>cs\<^bsup>\<pi>\<^esup> i = xs@[x,x']@ys\<close>  shows \<open>\<exists> m. cs\<^bsup>\<pi>\<^esup> m = xs@[x] \<and> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> 
using assms proof (induction \<open>ys\<close> arbitrary: \<open>i\<close> rule:rev_induct ) 
  case (snoc y ys)
  hence \<open>length (cs\<^bsup>\<pi>\<^esup> i) \<noteq> 1\<close> by auto
  then obtain i' where \<open>cs\<^bsup>\<pi>\<^esup> i = (cs\<^bsup>\<pi>\<^esup> i') @ [\<pi> i]\<close> and *: \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> i'\<close> using cs_length_g_one[of \<open>\<pi>\<close> \<open>i\<close>] by metis
  hence \<open>cs\<^bsup>\<pi>\<^esup> i' = xs@[x,x']@ys\<close> using snoc(2) by (metis append1_eq_conv append_assoc)
  then obtain m where **: \<open>cs\<^bsup>\<pi>\<^esup> m = xs @ [x]\<close> and \<open>i' cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using snoc(1) by blast
  hence \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using * cd_trans by (metis is_icdi_def)
  with ** show \<open>?case\<close> by blast
next
  case Nil
  hence \<open>length (cs\<^bsup>\<pi>\<^esup> i) \<noteq> 1\<close> by auto
  then obtain i' where a: \<open>cs\<^bsup>\<pi>\<^esup> i = (cs\<^bsup>\<pi>\<^esup> i') @ [\<pi> i]\<close> and *: \<open>i icd\<^bsup>\<pi>\<^esup>\<rightarrow> i'\<close> using cs_length_g_one[of \<open>\<pi>\<close> \<open>i\<close>] by metis
  have \<open>cs\<^bsup>\<pi>\<^esup> i = (xs@[x])@[x']\<close> using Nil by auto
  hence \<open>cs\<^bsup>\<pi>\<^esup> i' = xs@[x]\<close> using append1_eq_conv a by metis  
  thus \<open>?case\<close> using * unfolding is_icdi_def by blast
qed

lemma cs_split: assumes \<open>cs\<^bsup>\<pi>\<^esup> i = xs@[x]@ys@[\<pi> i]\<close>  shows \<open>\<exists> m. cs\<^bsup>\<pi>\<^esup> m = xs@[x] \<and> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> proof -
  obtain x' ys' where \<open>ys@[\<pi> i] = [x']@ys'\<close> by (metis append_Cons append_Nil neq_Nil_conv)
  thus \<open>?thesis\<close> using cs_split'[of \<open>\<pi>\<close> \<open>i\<close> \<open>xs\<close> \<open>x\<close> \<open>x'\<close> \<open>ys'\<close>] assms by auto
qed

lemma cs_less_split: assumes \<open>xs \<prec> ys\<close> obtains a as where \<open>ys = xs@a#as\<close>
  using assms unfolding cs_less.simps apply auto
by (metis Cons_nth_drop_Suc append_take_drop_id)

lemma cs_select_is_cs: assumes \<open>is_path \<pi>\<close> \<open>xs \<noteq> Nil\<close> \<open>xs \<prec> cs\<^bsup>\<pi>\<^esup> k\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> (\<pi>\<exclamdown>xs) = xs\<close> \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> (\<pi>\<exclamdown>xs)\<close>proof -
  obtain b bs where b: \<open>cs\<^bsup>\<pi>\<^esup> k = xs@b#bs\<close> using assms cs_less_split by blast
  obtain a as where a: \<open>xs = as@[a]\<close> using assms by (metis rev_exhaust)
  have \<open>cs\<^bsup>\<pi>\<^esup> k = as@[a,b]@bs\<close> using a b by auto
  then obtain k' where csk: \<open>cs\<^bsup>\<pi>\<^esup> k' = xs\<close> and is_cd: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> k'\<close> using cs_split' a by blast
  hence nret: \<open>\<pi> k' \<noteq> return\<close> by (metis is_cdi_def term_path_stable less_imp_le)
  show a: \<open>cs\<^bsup>\<pi>\<^esup> (\<pi>\<exclamdown>xs) = xs\<close> unfolding cs_select_def using cs_inj[OF assms(1) nret] csk the_equality[of _ \<open>k'\<close>]
    by (metis (mono_tags))
  show \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> (\<pi>\<exclamdown>xs)\<close> unfolding cs_select_def by (metis a assms(1) cs_inj cs_select_def csk is_cd nret)
qed

lemma cd_in_cs: assumes \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> shows \<open>\<exists> ns. cs\<^bsup>\<pi>\<^esup> n = (cs\<^bsup>\<pi>\<^esup> m) @ ns @[\<pi> n]\<close> 
using assms proof (induction rule: cd_induct)
  case (base  n) thus \<open>?case\<close> by (metis append_Nil cs.simps icd_is_the_icd)
next
  case (IS k n)
  hence \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>\<^esup> k @ [\<pi> n]\<close> by (metis cs.simps icd_is_the_icd)  
  thus \<open>?case\<close> using IS by force
qed

lemma butlast_cs_not_cd: assumes \<open>butlast (cs\<^bsup>\<pi>\<^esup> m) = butlast (cs\<^bsup>\<pi>\<^esup> n)\<close> shows \<open>\<not> m cd\<^bsup>\<pi>\<^esup>\<rightarrow>n\<close>
by (metis append_Cons append_Nil append_assoc assms cd_in_cs cs_not_nil list.distinct(1) self_append_conv snoc_eq_iff_butlast)

lemma wn_cs_butlast: assumes \<open>butlast (cs\<^bsup>\<pi>\<^esup> m) = butlast (cs\<^bsup>\<pi>\<^esup> n)\<close> \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> \<open>m<n\<close> shows \<open>i<j\<close>
proof (rule ccontr)
  assume \<open>\<not> i < j\<close>
  moreover
  have \<open>\<not> n cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> by (metis assms(1) butlast_cs_not_cd)
  ultimately
  have \<open>n \<le> m\<close> using assms(2,3) cr_wn'' by auto
  thus \<open>False\<close> using assms(4) by auto
qed


text \<open>This is the central theorem making the control slice suitable for matching indices between executions.\<close>

theorem cs_order: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and csi: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> 
and csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> and nret: \<open>\<pi> i \<noteq> return\<close> and ilj: \<open>i < j\<close>   
shows \<open>i'<j'\<close>
proof -
  have \<open>cs\<^bsup>\<pi>\<^esup> i \<noteq> cs\<^bsup>\<pi>\<^esup> j\<close> using cs_inj[OF path(1) nret] ilj by blast
  moreover 
  have \<open>cs\<^bsup>\<pi>\<^esup> i \<noteq> Nil\<close> \<open>cs\<^bsup>\<pi>\<^esup> j \<noteq> Nil\<close> by (metis cs_not_nil)+
  ultimately show \<open>?thesis\<close> proof (cases rule: list_neq_prefix_cases)
    case (diverge xs x x' ys ys')
    note csx = \<open>cs\<^bsup>\<pi>\<^esup> i = xs @ [x] @ ys\<close>
    note csx' = \<open>cs\<^bsup>\<pi>\<^esup> j = xs @ [x'] @ ys'\<close>
    note xx = \<open>x \<noteq> x'\<close>
    show \<open>i' < j'\<close> proof (cases \<open>ys\<close>) 
      assume ys: \<open>ys = Nil\<close>
      show \<open>?thesis\<close> proof (cases \<open>ys'\<close>)
        assume ys': \<open>ys' = Nil\<close>
        have cs: \<open>cs\<^bsup>\<pi>\<^esup> i = xs @ [x]\<close> \<open>cs\<^bsup>\<pi>\<^esup> j = xs @ [x']\<close> by (metis append_Nil2 csx ys, metis append_Nil2 csx' ys')
        hence bl: \<open>butlast (cs\<^bsup>\<pi>\<^esup> i) = butlast (cs\<^bsup>\<pi>\<^esup> j)\<close> by auto        
        show \<open>i' < j'\<close> using claim[OF path csi csj bl nret ilj] .
      next
        fix y' zs'
        assume ys': \<open>ys' = y'#zs'\<close>
        have cs: \<open>cs\<^bsup>\<pi>\<^esup> i = xs @ [x]\<close> \<open>cs\<^bsup>\<pi>\<^esup> j = xs @ [x',y']@ zs'\<close> by (metis append_Nil2 csx ys, metis append_Cons append_Nil csx' ys')         
        obtain n where n: \<open>cs\<^bsup>\<pi>\<^esup> n = xs@[x']\<close> and jn: \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> using cs cs_split' by blast
        obtain n' where n': \<open>cs\<^bsup>\<pi>'\<^esup> n' = xs@[x']\<close> and jn': \<open>j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> using cs cs_split' unfolding csj by blast
        have csn : \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and bl: \<open>butlast (cs\<^bsup>\<pi>\<^esup> i) = butlast (cs\<^bsup>\<pi>\<^esup> n)\<close> using n n' cs by auto
        hence bl': \<open>butlast (cs\<^bsup>\<pi>'\<^esup> i') = butlast (cs\<^bsup>\<pi>'\<^esup> n')\<close> using csi by auto
        have notcd: \<open>\<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> by (metis butlast_cs_not_cd bl)
        have nin: \<open>i \<noteq> n\<close> using cs n xx by auto
        have iln: \<open>i < n\<close> apply (rule ccontr) using cr_wn'[OF jn notcd] nin ilj by auto
        note claim[OF path csi csn bl nret iln]
        hence \<open>i' < n'\<close> .
        thus \<open>i' < j'\<close> using jn' unfolding is_cdi_def by auto
      qed
    next
      fix y zs
      assume ys: \<open>ys = y#zs\<close>
      show \<open>?thesis\<close> proof (cases \<open>ys'\<close>)
        assume ys' : \<open>ys' = Nil\<close>
        have cs: \<open>cs\<^bsup>\<pi>\<^esup> i = xs @ [x,y]@zs\<close> \<open>cs\<^bsup>\<pi>\<^esup> j = xs @ [x']\<close> by (metis append_Cons append_Nil csx ys, metis append_Nil2 csx' ys')
        obtain n where n: \<open>cs\<^bsup>\<pi>\<^esup> n = xs@[x]\<close> and jn: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> using cs cs_split' by blast
        obtain n' where n': \<open>cs\<^bsup>\<pi>'\<^esup> n' = xs@[x]\<close> and jn': \<open>i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> using cs cs_split' unfolding csi by blast
        have csn : \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and bl: \<open>butlast (cs\<^bsup>\<pi>\<^esup> n) = butlast (cs\<^bsup>\<pi>\<^esup> j)\<close> using n n' cs by auto
        hence bl': \<open>butlast (cs\<^bsup>\<pi>'\<^esup> j') = butlast (cs\<^bsup>\<pi>'\<^esup> n')\<close> using csj by auto
        have notcd: \<open>\<not> j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> by (metis butlast_cs_not_cd bl')
        have nin: \<open>n < i\<close> using jn unfolding is_cdi_def by auto
        have nlj: \<open>n < j\<close> using nin ilj by auto
        note claim[OF path csn csj bl _ nlj]
        hence nj': \<open>n' < j'\<close> using term_path_stable[OF path(1) _] less_imp_le nin nret by auto
        show \<open>i' < j'\<close> apply(rule ccontr) using cdi_prefix[OF jn' nj'] notcd by auto
      next
        fix y' zs'
        assume ys' : \<open>ys' = y'#zs'\<close>
        have cs: \<open>cs\<^bsup>\<pi>\<^esup> i = xs@[x,y]@zs\<close> \<open>cs\<^bsup>\<pi>\<^esup> j = xs@[x',y']@zs'\<close> by (metis append_Cons append_Nil csx ys,metis append_Cons append_Nil csx' ys')
        have neq: \<open>cs\<^bsup>\<pi>\<^esup> i \<noteq> cs\<^bsup>\<pi>\<^esup> j\<close> using cs_inj path nret ilj by blast
        obtain m where m: \<open>cs\<^bsup>\<pi>\<^esup> m = xs@[x]\<close> and im: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using cs cs_split' by blast
        obtain n where n: \<open>cs\<^bsup>\<pi>\<^esup> n = xs@[x']\<close> and jn: \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> using cs cs_split' by blast
        obtain m' where m': \<open>cs\<^bsup>\<pi>'\<^esup> m' = xs@[x]\<close> and im': \<open>i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> m'\<close> using cs cs_split' unfolding csi by blast
        obtain n' where n': \<open>cs\<^bsup>\<pi>'\<^esup> n' = xs@[x']\<close> and jn': \<open>j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> using cs cs_split' unfolding csj by blast
        have \<open>m \<le> n\<close> using ilj m n wn_cs_butlast[OF _ jn im] by force
        moreover
        have \<open>m \<noteq> n\<close> using m n xx by (metis last_snoc)
        ultimately 
        have mn: \<open>m < n\<close> by auto
        moreover 
        have \<open>\<pi> m \<noteq> return\<close> by (metis last_cs last_snoc m mn n path(1) term_path_stable xx less_imp_le)
        moreover  
        have \<open>butlast (cs\<^bsup>\<pi>\<^esup> m) = butlast (cs\<^bsup>\<pi>\<^esup> n)\<close> \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close> \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> using m n n' m' by auto
        ultimately
        have \<open>m' < n'\<close> using claim path by blast
        thus \<open>i' < j'\<close> using m' n' im' jn' wn_cs_butlast by (metis butlast_snoc)        
      qed
    qed
  next
    case (prefix1 xs)
    note pfx = \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>\<^esup> j @ xs\<close>
    note xs = \<open>xs \<noteq> []\<close>
    obtain a as where \<open>xs = a#as\<close> using xs by (metis list.exhaust)
    moreover
    obtain bs b where bj: \<open>cs\<^bsup>\<pi>\<^esup> j = bs@[b]\<close> using cs_not_nil by (metis rev_exhaust)
    ultimately
    have \<open>cs\<^bsup>\<pi>\<^esup> i = bs@[b,a]@as\<close> using pfx by auto
    then obtain m where \<open>cs\<^bsup>\<pi>\<^esup> m = bs@[b]\<close> and cdep:  \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> m\<close> using cs_split' by blast
    hence mi: \<open>m = j\<close> using bj cs_inj by (metis is_cdi_def term_path_stable less_imp_le)
    hence \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using cdep by auto
    hence \<open>False\<close> using ilj unfolding is_cdi_def by auto
    thus \<open>i' < j'\<close> ..
  next
    case (prefix2 xs)
    have pfx : \<open>cs\<^bsup>\<pi>'\<^esup> i' @ xs = cs\<^bsup>\<pi>'\<^esup> j'\<close> using prefix2 csi csj by auto
    note xs = \<open>xs \<noteq> []\<close>
     obtain a as where \<open>xs = a#as\<close> using xs by (metis list.exhaust)
    moreover
    obtain bs b where bj: \<open>cs\<^bsup>\<pi>'\<^esup> i'  = bs@[b]\<close> using cs_not_nil by (metis rev_exhaust)
    ultimately
    have \<open>cs\<^bsup>\<pi>'\<^esup> j' = bs@[b,a]@as\<close> using pfx by auto
    then obtain m where \<open>cs\<^bsup>\<pi>'\<^esup> m = bs@[b]\<close> and cdep:  \<open>j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> m\<close> using cs_split' by blast
    hence mi: \<open>m = i'\<close> using bj cs_inj by (metis is_cdi_def term_path_stable less_imp_le)
    hence \<open>j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i'\<close> using cdep by auto
    thus \<open>i' < j'\<close> unfolding is_cdi_def by auto  
  qed
qed

lemma cs_order_le: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and csi: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> 
and csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> and nret: \<open>\<pi> i \<noteq> return\<close> and ilj: \<open>i \<le> j\<close>   
shows \<open>i'\<le>j'\<close> proof cases
  assume \<open>i < j\<close> with cs_order[OF assms(1,2,3,4,5)] show \<open>?thesis\<close> by simp
next
  assume \<open>\<not> i < j\<close>
  hence \<open>i = j\<close> using ilj by simp
  hence csij: \<open>cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>'\<^esup> j'\<close> using csi csj by simp  
  have nret': \<open>\<pi>' i' \<noteq> return\<close> using nret last_cs csi by metis
  show \<open>?thesis\<close> using cs_inj[OF path(2) nret' csij] by simp
qed

lemmas cs_induct[case_names cs] = cs.induct

lemma icdi_path_swap: assumes \<open>is_path \<pi>'\<close> \<open>j icd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> \<open>\<pi> =\<^bsub>j\<^esub>  \<pi>'\<close> shows \<open>j icd\<^bsup>\<pi>'\<^esup>\<rightarrow>k\<close> using assms unfolding eq_up_to_def is_icdi_def is_cdi_def by auto

lemma icdi_path_swap_le: assumes \<open>is_path \<pi>'\<close> \<open>j icd\<^bsup>\<pi>\<^esup>\<rightarrow>k\<close> \<open>\<pi> =\<^bsub>n\<^esub>  \<pi>'\<close> \<open>j \<le> n\<close> shows \<open>j icd\<^bsup>\<pi>'\<^esup>\<rightarrow>k\<close> by (metis assms icdi_path_swap eq_up_to_le)

lemma cs_path_swap: assumes \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> \<open>\<pi> =\<^bsub>k\<^esub> \<pi>'\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k\<close> using assms(1,3) proof (induction \<open>\<pi>\<close> \<open>k\<close> rule:cs_induct,cases)
  case (cs \<pi> k)     
  let \<open>?l\<close> = \<open>(THE l. k icd\<^bsup>\<pi>\<^esup>\<rightarrow> l)\<close>
  assume *: \<open>\<exists>l. k icd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close>
  have kicd: \<open>k icd\<^bsup>\<pi>\<^esup>\<rightarrow> ?l\<close> by (metis "*" icd_is_the_icd)
  hence \<open>?l < k\<close> unfolding is_cdi_def[of \<open>k\<close> \<open>\<pi>\<close> \<open>?l\<close>] is_icdi_def[of \<open>k\<close> \<open>\<pi>\<close> \<open>?l\<close>] by auto
  hence \<open>\<forall> i\<le>?l. \<pi> i = \<pi>' i\<close> using cs(2,3) unfolding eq_up_to_def by auto
  hence csl: \<open>cs\<^bsup>\<pi>\<^esup> ?l = cs\<^bsup>\<pi>'\<^esup> ?l\<close> using cs(1,2) * unfolding eq_up_to_def by auto 
  have kicd: \<open>k icd\<^bsup>\<pi>\<^esup>\<rightarrow> ?l\<close> by (metis "*" icd_is_the_icd)
  hence csk: \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>\<^esup> ?l @ [\<pi> k]\<close> using kicd by auto
  have kicd': \<open>k icd\<^bsup>\<pi>'\<^esup>\<rightarrow> ?l\<close> using kicd icdi_path_swap[OF assms(2) _ cs(3)] by simp
  hence \<open>?l = (THE l. k icd\<^bsup>\<pi>'\<^esup>\<rightarrow> l)\<close> by (metis icd_is_the_icd)
  hence csk': \<open>cs\<^bsup>\<pi>'\<^esup> k = cs\<^bsup>\<pi>'\<^esup> ?l @ [\<pi>' k]\<close> using kicd' by auto
  have \<open>\<pi>' k = \<pi> k\<close> using cs(3) unfolding eq_up_to_def by auto
  with csl csk csk'  
  show \<open>?case\<close> by auto
next
  case (cs \<pi> k)
  assume *: \<open>\<not> (\<exists>l. k icd\<^bsup>\<pi>\<^esup>\<rightarrow> l)\<close>
  hence csk: \<open>cs\<^bsup>\<pi>\<^esup> k = [\<pi> k]\<close> by auto
  have \<open>\<not> (\<exists>l. k icd\<^bsup>\<pi>'\<^esup>\<rightarrow> l)\<close> apply (rule ccontr) using * icdi_path_swap_le[OF cs(2) _, of \<open>k\<close> \<open>\<pi>'\<close>] cs(3) by (metis eq_up_to_sym le_refl)
  hence csk': \<open>cs\<^bsup>\<pi>'\<^esup> k = [\<pi>' k]\<close> by auto
  with csk show \<open>?case\<close> using cs(3) eq_up_to_apply by auto
qed

lemma cs_path_swap_le: assumes \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> \<open>\<pi> =\<^bsub>n\<^esub>  \<pi>'\<close> \<open>k \<le> n\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k\<close> by (metis assms cs_path_swap eq_up_to_le)

lemma cs_path_swap_cd: assumes \<open>is_path \<pi>\<close> and \<open>is_path \<pi>'\<close> and \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> 
obtains k' where \<open>n' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> and \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close>
proof -
  from cd_in_cs[OF assms(4)]
  obtain ns where *: \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>\<^esup> k @ ns @ [\<pi> n]\<close> by blast
  obtain xs x where csk: \<open>cs\<^bsup>\<pi>\<^esup> k = xs @ [x]\<close> by (metis cs_not_nil rev_exhaust)
  have \<open>\<pi> n = \<pi>' n'\<close> using assms(3) last_cs by metis
  hence **: \<open>cs\<^bsup>\<pi>'\<^esup> n' = xs@[x]@ns@[\<pi>' n']\<close> using * assms(3) csk by auto
  from cs_split[OF **]
  obtain k' where \<open>cs\<^bsup>\<pi>'\<^esup> k' = xs @ [x]\<close> \<open>n' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> by blast
  thus \<open>thesis\<close> using that csk by auto
qed

lemma path_ipd_swap: assumes \<open>is_path \<pi>\<close> \<open>\<pi> k \<noteq> return\<close> \<open>k < n\<close> 
obtains \<pi>' m where \<open>is_path \<pi>'\<close> \<open>\<pi> =\<^bsub>n\<^esub>  \<pi>'\<close> \<open>k < m\<close> \<open>\<pi>' m = ipd (\<pi>' k)\<close> \<open>\<forall> l \<in> {k..<m}. \<pi>' l \<noteq> ipd (\<pi>' k)\<close>
proof -
  obtain \<pi>' r where *: \<open>\<pi>' 0 = \<pi> n\<close> \<open>is_path \<pi>'\<close> \<open>\<pi>' r = return\<close> by (metis assms(1) path_nodes reaching_ret)
  let \<open>?\<pi>\<close> = \<open>\<pi>@\<^bsup>n\<^esup>  \<pi>'\<close>
  have path: \<open>is_path ?\<pi>\<close> and ret: \<open>?\<pi> (n + r) = return\<close> and equpto:  \<open>?\<pi> =\<^bsub>n\<^esub>  \<pi>\<close> using assms path_cons * path_append_eq_up_to by auto
  have \<pi>k: \<open>?\<pi> k = \<pi> k\<close> by (metis assms(3) less_imp_le_nat path_append_def)
  obtain j where j: \<open>k < j \<and> j \<le> (n + r) \<and> ?\<pi> j = ipd (\<pi> k)\<close> (is \<open>?P j\<close> )by (metis \<pi>k assms(2) path path_ret_ipd ret)
  define m where m: \<open>m \<equiv> LEAST m . ?P m\<close>
  have Pm: \<open>?P m\<close> using LeastI[of \<open>?P\<close> \<open>j\<close>] j m by auto
  hence km: \<open>k < m\<close> \<open>m \<le> (n + r)\<close> \<open>?\<pi> m = ipd (\<pi> k)\<close> by auto
  have le: \<open>\<And>l. ?P l \<Longrightarrow> m \<le> l\<close> using Least_le[of \<open>?P\<close>] m by blast
  have \<pi>knipd: \<open>?\<pi> k \<noteq> ipd (\<pi> k)\<close> by (metis \<pi>k assms(1) assms(2) ipd_not_self path_nodes)
  have nipd': \<open>\<And>l. k < l \<Longrightarrow> l < m \<Longrightarrow> ?\<pi> l \<noteq> ipd (\<pi> k)\<close> apply (rule ccontr) using le km(2) by force
  have \<open>\<forall> l \<in> {k..<m}. ?\<pi> l \<noteq> ipd(\<pi> k)\<close> using \<pi>knipd nipd' by(auto, metis le_eq_less_or_eq,metis le_eq_less_or_eq)
  thus \<open>thesis\<close> using that by (metis \<pi>k eq_up_to_sym km(1) km(3) path path_append_eq_up_to)
qed

lemma cs_sorted_list_of_cd': \<open>cs\<^bsup>\<pi>\<^esup> k = map \<pi> (sorted_list_of_set { i . k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}) @ [\<pi> k]\<close> 
proof (induction \<open>\<pi>\<close> \<open>k\<close> rule: cs.induct, cases)
  case (1 \<pi> k)
  assume \<open>\<exists> j. k icd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close>
  then guess j ..
  note j = this
  hence csj: \<open>cs\<^bsup>\<pi>\<^esup> j = map \<pi> (sorted_list_of_set {i. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}) @ [\<pi> j]\<close> by (metis "1.IH" icd_is_the_icd)
  have \<open>{i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} = insert j {i. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}\<close> using cdi_is_cd_icdi[OF j] by auto
  moreover
  have f: \<open>finite {i. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}\<close> unfolding is_cdi_def by auto
  moreover
  have \<open>j \<notin> {i. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}\<close> unfolding is_cdi_def by auto
  ultimately
  have \<open>sorted_list_of_set { i . k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} = insort j (sorted_list_of_set { i . j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i})\<close> using sorted_list_of_set_insert by auto
  moreover
  have \<open>\<forall> x \<in>  {i. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}. x < j\<close> unfolding is_cdi_def by auto
  hence \<open>\<forall> x \<in> set (sorted_list_of_set {i. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}). x < j\<close> by (simp add: f) 
  ultimately
  have \<open>sorted_list_of_set { i . k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} = (sorted_list_of_set { i . j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i})@[j]\<close>  using insort_greater by auto
  hence \<open>cs\<^bsup>\<pi>\<^esup> j = map \<pi> (sorted_list_of_set { i . k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i})\<close> using csj by auto
  thus \<open>?case\<close> by (metis icd_cs j)
next
  case (1 \<pi> k)
  assume *: \<open>\<not> (\<exists> j. k icd\<^bsup>\<pi>\<^esup>\<rightarrow> j)\<close>
  hence \<open>cs\<^bsup>\<pi>\<^esup> k = [\<pi> k]\<close> by (metis cs_cases)
  moreover 
  have \<open>{ i . k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} = {}\<close> by (auto, metis * excd_impl_exicd)
  ultimately 
  show \<open>?case\<close> by (metis append_Nil list.simps(8) sorted_list_of_set_empty)
qed

lemma cs_sorted_list_of_cd: \<open>cs\<^bsup>\<pi>\<^esup> k = map \<pi> (sorted_list_of_set ({ i . k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {k}))\<close> proof -
  have le: \<open>\<forall> x \<in> {i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow>i}.\<forall> y \<in> {k}. x < y\<close> unfolding is_cdi_def by auto
  have fin: \<open>finite {i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow>i}\<close> \<open>finite {k}\<close> unfolding is_cdi_def by auto  
  show \<open>?thesis\<close> unfolding cs_sorted_list_of_cd'[of \<open>\<pi>\<close> \<open>k\<close>] sorted_list_of_set_append[OF fin le] by auto
qed

lemma cs_not_ipd: assumes \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> ipd (\<pi> j) \<noteq> ipd (\<pi> k)\<close> (is \<open>?Q j\<close>)
shows \<open>cs\<^bsup>\<pi>\<^esup> (GREATEST j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> ipd (\<pi> j) \<noteq> ipd (\<pi> k)) = [n\<leftarrow>cs\<^bsup>\<pi>\<^esup> k . ipd n \<noteq> ipd (\<pi> k)]\<close>
(is \<open>cs\<^bsup>\<pi>\<^esup> ?j = filter ?P _\<close>) 
proof -  
  have csk: \<open>cs\<^bsup>\<pi>\<^esup> k = map \<pi> (sorted_list_of_set ({ i . k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i } \<union> {k}))\<close> by (metis cs_sorted_list_of_cd)
  have csj: \<open>cs\<^bsup>\<pi>\<^esup> ?j = map \<pi> (sorted_list_of_set ({i. ?j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i } \<union> {?j}))\<close> by (metis cs_sorted_list_of_cd)
  
  have bound: \<open>\<forall> j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> ipd (\<pi> j) \<noteq> ipd(\<pi> k) \<longrightarrow> j \<le> k\<close> unfolding is_cdi_def by simp
    
  have kcdj: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> ?j\<close> and ipd': \<open>ipd (\<pi> ?j) \<noteq> ipd(\<pi> k)\<close> using GreatestI_nat[of \<open>?Q\<close> \<open>j\<close> \<open>k\<close>, OF assms] bound by auto
   
  have greatest: \<open>\<And> j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<Longrightarrow> ipd (\<pi> j) \<noteq> ipd (\<pi> k) \<Longrightarrow> j \<le> ?j\<close> using Greatest_le_nat[of \<open>?Q\<close>  _ \<open>k\<close>] bound by auto
  have less_not_ipdk: \<open>\<And> j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<Longrightarrow> j < ?j \<Longrightarrow> ipd (\<pi> j) \<noteq> ipd (\<pi> k)\<close>   by (metis (lifting) ipd' kcdj same_ipd_stable)
  hence le_not_ipdk: \<open>\<And> j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<Longrightarrow> j \<le> ?j \<Longrightarrow> ipd (\<pi> j) \<noteq> ipd (\<pi> k)\<close> using kcdj ipd' by (case_tac \<open>j = ?j\<close>,auto)
  have *: \<open>{j \<in> {i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow>i} \<union> {k}. ?P (\<pi> j)} = insert ?j { i . ?j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<close> 
    apply auto  
    apply (metis (lifting, no_types) greatest cr_wn'' kcdj le_antisym le_refl)
    apply (metis kcdj)
    apply (metis ipd')
    apply (metis (full_types) cd_trans kcdj)
    apply (subgoal_tac \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> x\<close>)
    apply (metis (lifting, no_types) is_cdi_def less_not_ipdk)
    by (metis (full_types) cd_trans kcdj)
  have \<open>finite ({i . k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {k})\<close> unfolding is_cdi_def by auto
  note filter_sorted_list_of_set[OF this, of \<open>?P o \<pi>\<close>]
  hence \<open>[n\<leftarrow>cs\<^bsup>\<pi>\<^esup> k . ipd n \<noteq> ipd(\<pi> k)] = map \<pi> (sorted_list_of_set {j \<in> {i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow>i} \<union> {k}. ?P (\<pi> j)})\<close> unfolding csk filter_map by auto 
  also 
  have \<open>\<dots> =  map \<pi> (sorted_list_of_set (insert ?j { i . ?j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}))\<close> unfolding * by auto
  also 
  have \<open>\<dots> = cs\<^bsup>\<pi>\<^esup> ?j\<close> using csj by auto
  finally 
  show \<open>?thesis\<close> by metis
qed

lemma cs_ipd: assumes ipd: \<open>\<pi> m = ipd (\<pi> k)\<close> \<open>\<forall> n \<in> {k..<m}. \<pi> n \<noteq> ipd (\<pi> k)\<close>
and km: \<open>k < m\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> m = [n\<leftarrow>cs\<^bsup>\<pi>\<^esup> k . ipd n \<noteq> \<pi> m] @ [\<pi> m]\<close>
proof cases
  assume \<open>\<exists> j. m icd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close>  
  then obtain j where jicd: \<open>m icd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> by blast
  hence *: \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>\<^esup> j @ [\<pi> m]\<close> by (metis icd_cs)
  have j: \<open>j = (GREATEST j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> ipd (\<pi> j) \<noteq> \<pi> m)\<close> using jicd assms ipd_icd_greatest_cd_not_ipd by blast
  moreover
  have \<open>ipd (\<pi> j) \<noteq> ipd (\<pi> k)\<close> by (metis is_cdi_def is_icdi_def is_ipd_def cd_not_pd ipd(1) ipd_is_ipd jicd path_nodes less_imp_le term_path_stable)
  moreover
  have \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> unfolding j by (metis (lifting, no_types) assms(3) cd_ipd_is_cd icd_imp_cd ipd(1) ipd(2) j jicd)
  ultimately
  have \<open>cs\<^bsup>\<pi>\<^esup> j = [n\<leftarrow>cs\<^bsup>\<pi>\<^esup> k . ipd n \<noteq> \<pi> m]\<close> using cs_not_ipd[of \<open>k\<close> \<open>\<pi>\<close> \<open>j\<close>] ipd(1) by metis
  thus \<open>?thesis\<close> using * by metis
next
  assume noicd: \<open>\<not> (\<exists> j. m icd\<^bsup>\<pi>\<^esup>\<rightarrow> j)\<close>  
  hence csm: \<open>cs\<^bsup>\<pi>\<^esup> m = [\<pi> m]\<close> by auto
  have \<open>\<And>j. k cd\<^bsup>\<pi>\<^esup>\<rightarrow>j \<Longrightarrow> ipd(\<pi> j) = \<pi> m\<close> using cd_is_cd_ipd[OF km ipd] by (metis excd_impl_exicd noicd)
  hence *: \<open>{j \<in> {i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {k}. ipd (\<pi> j) \<noteq> \<pi> m} = {}\<close> using ipd(1) by auto
  have **: \<open>((\<lambda>n. ipd n \<noteq> \<pi> m) o \<pi>) = (\<lambda>n. ipd (\<pi> n) \<noteq> \<pi> m)\<close> by auto
  have fin: \<open>finite ({i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {k})\<close> unfolding is_cdi_def by auto
  note csk = cs_sorted_list_of_cd[of \<open>\<pi>\<close> \<open>k\<close>]
  hence \<open>[n\<leftarrow>cs\<^bsup>\<pi>\<^esup> k . ipd n \<noteq> \<pi> m] = [n\<leftarrow> (map \<pi> (sorted_list_of_set ({i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {k}))) . ipd n \<noteq> \<pi> m]\<close> by simp
  also
  have \<open>\<dots> = map \<pi> [n <- sorted_list_of_set ({i. k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {k}). ipd (\<pi> n) \<noteq> \<pi> m]\<close>  by (auto simp add: filter_map **) 
  also 
  have \<open>\<dots> = []\<close> unfolding * filter_sorted_list_of_set[OF fin, of \<open>\<lambda>n. ipd (\<pi> n) \<noteq> \<pi> m\<close>] by auto
  finally
  show \<open>?thesis\<close> using csm by (metis append_Nil)
qed

lemma converged_ipd_same_icd: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and  converge: \<open>l < m\<close> \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close> 
and csk: \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> and icd: \<open>l icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> and suc: \<open>\<pi> (Suc k) = \<pi>' (Suc k')\<close>
and ipd: \<open>\<pi>' m' = ipd (\<pi> k)\<close> \<open>\<forall> n \<in> {k'..<m'}. \<pi>' n \<noteq> ipd (\<pi> k)\<close>
shows \<open>\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close>
proof cases
  assume l: \<open>l = Suc k\<close>
  hence \<open>Suc k cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> using icd by (metis is_icdi_def)
  hence \<open>\<pi> (Suc k) \<noteq> ipd (\<pi> k)\<close> unfolding is_cdi_def by auto
  hence \<open>\<pi>' (Suc k') \<noteq> ipd (\<pi>' k')\<close> by (metis csk last_cs suc)
  moreover 
  have \<open>\<pi>' (Suc k') \<noteq> return\<close> by (metis \<open>Suc k cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> ret_no_cd suc)
  ultimately
  have \<open>Suc k' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> unfolding is_cdi_def using path(2) apply auto 
  by (metis ipd_not_self le_Suc_eq le_antisym path_nodes term_path_stable)
  hence \<open>Suc k' icd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> unfolding is_icdi_def using path(2) by fastforce  
  hence \<open>cs\<^bsup>\<pi>'\<^esup> (Suc k') = cs\<^bsup>\<pi>'\<^esup> k' @[\<pi>' (Suc k')]\<close> using icd_cs by auto 
  moreover
  have \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>\<^esup> k @ [\<pi> l]\<close> using icd icd_cs by auto
  ultimately 
  have \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> (Suc k')\<close> by (metis csk l suc)
  thus \<open>?thesis\<close> by blast
next
  assume nsuck: \<open>l \<noteq> Suc k\<close>
  have kk'[simp]: \<open>\<pi>' k' = \<pi> k\<close> by (metis csk last_cs)
  have kl: \<open>k < l\<close> using icd unfolding is_icdi_def is_cdi_def by auto
  hence skl: \<open>Suc k < l\<close> by (metis Suc_lessI nsuck)
  hence lpd: \<open>\<pi> l pd\<rightarrow> \<pi> (Suc k)\<close> using icd icd_pd_intermediate by auto
  have km: \<open>k < m\<close> by (metis converge(1) kl order.strict_trans)  
  have lcd: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> using icd is_icdi_def by auto
  hence ipdk_pdl: \<open>ipd (\<pi> k) pd\<rightarrow> (\<pi> l)\<close> by (metis ipd_pd_cd)
  have *: \<open>ipd (\<pi> k) \<in> nodes\<close> by (metis ipdk_pdl pd_node1)
  have nretk: \<open>\<pi> k \<noteq> return\<close> by (metis kl lcd path(1) ret_no_cd term_path_stable less_imp_le)
  have **: \<open>\<not> (\<pi> l) pd\<rightarrow> ipd (\<pi> k)\<close> proof 
    assume a: \<open>\<pi> l pd\<rightarrow> ipd (\<pi> k)\<close>
    hence \<open>\<pi> l pd\<rightarrow> (\<pi> k)\<close> by (metis is_ipd_def \<open>k < l\<close> ipd_is_ipd ipdk_pdl path(1) path_nodes pd_antisym term_path_stable less_imp_le)
    moreover 
    have \<open>\<pi> l \<noteq> (\<pi> k)\<close> by (metis "*" a ipd_not_self ipdk_pdl lcd pd_antisym ret_no_cd)
    ultimately
    show \<open>False\<close> using lcd cd_not_pd by auto
  qed

  have km': \<open>k' < m'\<close> using cs_order[OF path csk converge(2) nretk km] . 

  obtain \<pi>'' n'' where path'': \<open>is_path \<pi>''\<close>  and \<pi>''0: \<open>\<pi>'' 0 = ipd (\<pi> k)\<close> and \<pi>''n: \<open>\<pi>'' n'' = return\<close> and not\<pi>l: \<open>\<forall> i\<le>n''. \<pi>'' i \<noteq> \<pi> l\<close> using no_pd_path[OF * **] .
  let \<open>?\<pi>'\<close> = \<open>(\<pi>' @\<^bsup>m'\<^esup> \<pi>'') \<guillemotleft> Suc k'\<close>
  have \<open>is_path ?\<pi>'\<close> by (metis \<pi>''0 ipd(1) path'' path(2) path_cons path_path_shift)
  moreover 
  have \<open>?\<pi>' 0 = \<pi> (Suc k)\<close> using km' suc by auto
  moreover
  have \<open>?\<pi>' (m' - Suc k' + n'') = return\<close> using \<pi>''n km' \<pi>''0 ipd(1) by auto  
  ultimately
  obtain l'' where l'': \<open>l'' \<le> m' - Suc k' + n''\<close> \<open>?\<pi>' l'' = \<pi> l\<close> using lpd unfolding is_pd_def by blast
  have l''m: \<open>l'' \<le> m' - Suc k'\<close> apply (rule ccontr) using l'' not\<pi>l km' by (cases \<open>Suc (k' + l'') \<le> m'\<close>, auto)
  let \<open>?l'\<close> = \<open>Suc ( k' + l'')\<close>
  have lm': \<open>?l' \<le> m'\<close> using l''m km' by auto
  
  \<comment> \<open>Now we have found our desired l'\<close>
  have 1: \<open>\<pi>' ?l' = \<pi> l\<close> using  l'' l''m lm' by auto
  have 2: \<open>k' < ?l'\<close> by simp  
  have 3: \<open>?l' < m'\<close> apply (rule ccontr) using lm' by (simp, metis "**" 1 ipd(1) ipdk_pdl)  
  
  \<comment> \<open>Need the least such l'\<close>

  let \<open>?P\<close> = \<open>\<lambda> l'. \<pi>' l' = \<pi> l \<and> k' < l' \<and> l' < m'\<close>

  have *: \<open>?P ?l'\<close> using 1 2 3 by blast

  define l' where l': \<open>l' == LEAST l'. ?P l'\<close>
  
  have \<pi>l': \<open>\<pi>' l' = \<pi> l\<close> using l' 1 2 3 LeastI[of \<open>?P\<close>] by blast  
  have kl': \<open>k' < l'\<close> using l' 1 2 3 LeastI[of \<open>?P\<close>] by blast
  have lm': \<open>l' < m'\<close> using l' 1 2 3 LeastI[of \<open>?P\<close>] by blast  

  have nretl': \<open>\<pi>' l' \<noteq> return\<close> by (metis \<pi>''n \<pi>l' le_refl not\<pi>l)
 
  have nipd': \<open>\<forall> j \<in> {k'..l'}. \<pi>' j \<noteq> ipd (\<pi>' k')\<close> using lm' kk' ipd(2) kl' by force
 
  have lcd': \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> by (metis is_cdi_def kl' nipd' nretl' path(2))

  have licd: \<open>l' icd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> proof -
    have \<open>\<forall> m \<in> {k'<..<l'}. \<not> l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> m\<close> proof (rule ccontr)
      assume \<open>\<not> (\<forall> m \<in> {k'<..<l'}. \<not> l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> m)\<close>
      then obtain j' where kj': \<open>k' < j'\<close> and jl': \<open>j' < l'\<close> and lcdj': \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> by force
      have jm': \<open>j'<m'\<close> by (metis jl' lm' order.strict_trans)
      have \<open>\<pi>' j' \<noteq> \<pi> l\<close> apply (rule ccontr) using l' kj' jm' jl' Least_le[of \<open>?P\<close> \<open>j'\<close>] by auto       
      hence \<open>\<not> \<pi>' l' pd\<rightarrow> \<pi>' j'\<close> using cd_not_pd lcdj' \<pi>l' by metis
      moreover have \<open>\<pi>' j' \<in> nodes\<close> using path(2) path_nodes by auto
      ultimately
      obtain \<pi>\<^sub>1 n\<^sub>1 where path\<^sub>1: \<open>is_path \<pi>\<^sub>1\<close> and \<pi>0\<^sub>1: \<open>\<pi>\<^sub>1 0 = \<pi>' j'\<close> and \<pi>n\<^sub>1: \<open>\<pi>\<^sub>1 n\<^sub>1 = return\<close> and nl': \<open>\<forall> l \<le>n\<^sub>1. \<pi>\<^sub>1 l \<noteq> \<pi>' l'\<close> unfolding is_pd_def by blast
      let \<open>?\<pi>''\<close> = \<open>(\<pi>'@\<^bsup>j'\<^esup> \<pi>\<^sub>1) \<guillemotleft> Suc k'\<close>
      have \<open>is_path ?\<pi>''\<close> by (metis \<pi>0\<^sub>1 path(2) path\<^sub>1 path_cons path_path_shift)
      moreover
      have \<open>?\<pi>'' 0 = \<pi> (Suc k)\<close> by (simp, metis kj' less_eq_Suc_le suc)
      moreover
      have kj': \<open>Suc k' \<le> j'\<close> by (metis kj' less_eq_Suc_le)
      hence \<open>?\<pi>'' (j' - Suc k' + n\<^sub>1) = return\<close> by (simp, metis \<pi>0\<^sub>1 \<pi>n\<^sub>1)
      ultimately
      obtain l'' where *: \<open>?\<pi>'' l'' = \<pi> l\<close> and **: \<open>l'' \<le>j' - Suc k' + n\<^sub>1\<close> using lpd is_pd_def by blast      
      show \<open>False\<close> proof (cases)
        assume a: \<open>l'' \<le> j' - Suc k'\<close>        
        hence \<open>\<pi>' (l'' + Suc k') = \<pi> l\<close> using * kj' by(simp, metis Nat.le_diff_conv2 add_Suc diff_add_inverse le_add1 le_add_diff_inverse2)
        moreover 
        have \<open>l'' + Suc k' < l'\<close> by (metis a jl' add_diff_cancel_right' kj' le_add_diff_inverse less_imp_diff_less ordered_cancel_comm_monoid_diff_class.le_diff_conv2)
        moreover
        have \<open>l'' + Suc k' < m'\<close> by (metis Suc_lessD calculation(2) less_trans_Suc lm')
        moreover 
        have \<open>k' < l'' + Suc k'\<close> by simp
        ultimately
        show \<open>False\<close> using Least_le[of \<open>?P\<close> \<open>l'' + Suc k'\<close>] l' by auto
      next
        assume a: \<open>\<not> l'' \<le> j' - Suc k'\<close>
        hence \<open>\<not> Suc (k' + l'') \<le> j'\<close> by simp
        hence \<open>\<pi>\<^sub>1 (Suc (k' + l'') - j') = \<pi> l\<close> using * kj' by simp 
        moreover 
        have \<open>Suc (k' + l'') - j' \<le> n\<^sub>1\<close> using ** kj' by simp
        ultimately
        show \<open>False\<close> using nl' by (metis \<pi>l')
      qed
    qed
    thus \<open>?thesis\<close> unfolding is_icdi_def using lcd' path(2) by simp
  qed
  hence \<open>cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<pi>'\<^esup> k' @ [\<pi>' l']\<close> by (metis icd_cs)
  hence \<open>cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<pi>\<^esup> l\<close> by (metis \<pi>l' csk icd icd_cs)
  thus \<open>?thesis\<close> by metis
qed

lemma converged_same_icd: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and converge: \<open>l < n\<close> \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> 
and csk: \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> and icd: \<open>l icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> and suc: \<open>\<pi> (Suc k) = \<pi>' (Suc k')\<close>
shows \<open>\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close> proof -
  
  have nret: \<open>\<pi> k \<noteq> return\<close> using icd unfolding is_icdi_def is_cdi_def using term_path_stable less_imp_le by metis 
  have kl: \<open>k < l\<close> using icd unfolding is_icdi_def is_cdi_def by auto
  have kn: \<open>k < n\<close> using converge kl by simp
  from path_ipd_swap[OF path(1) nret kn]
  obtain \<rho> m where path\<rho>: \<open>is_path \<rho>\<close> and \<pi>\<rho>: \<open>\<pi> =\<^bsub>n\<^esub>  \<rho>\<close> and km: \<open>k < m\<close> and ipd: \<open>\<rho> m = ipd (\<rho> k)\<close> \<open>\<forall> l \<in> {k..<m}. \<rho> l \<noteq> ipd (\<rho> k)\<close> .
  have csk1: \<open>cs\<^bsup>\<rho>\<^esup> k = cs\<^bsup>\<pi>\<^esup> k\<close> using cs_path_swap_le path path\<rho> \<pi>\<rho> kn by auto
  have suc\<rho>: \<open>\<rho> (Suc k) = \<pi> (Suc k)\<close> by (metis \<pi>\<rho> eq_up_to_def kn less_eq_Suc_le)

  have nret': \<open>\<pi>' k' \<noteq> return\<close> by (metis csk last_cs nret)
  have kn': \<open>k' < n'\<close> using cs_order[OF path csk converge(2) nret kn] .
  from path_ipd_swap[OF path(2) nret' kn']
  obtain \<rho>' m' where path\<rho>': \<open>is_path \<rho>'\<close> and \<pi>\<rho>': \<open>\<pi>' =\<^bsub>n'\<^esub> \<rho>'\<close> and km': \<open>k' < m'\<close> and ipd': \<open>\<rho>' m' = ipd (\<rho>' k')\<close> \<open>\<forall> l \<in> {k'..<m'}. \<rho>' l \<noteq> ipd (\<rho>' k')\<close> .
  have csk1': \<open>cs\<^bsup>\<rho>'\<^esup> k' = cs\<^bsup>\<pi>'\<^esup> k'\<close> using cs_path_swap_le path path\<rho>' \<pi>\<rho>' kn' by auto
  have suc\<rho>': \<open>\<rho>' (Suc k') = \<pi>' (Suc k')\<close> by (metis \<pi>\<rho>' eq_up_to_def kn' less_eq_Suc_le)
  
  have icd\<rho>: \<open>l icd\<^bsup>\<rho>\<^esup>\<rightarrow> k\<close> using icdi_path_swap_le[OF path\<rho> icd \<pi>\<rho>] converge by simp

  have lm: \<open>l < m\<close> using ipd(1) icd\<rho> km unfolding is_icdi_def is_cdi_def by auto

  have csk': \<open>cs\<^bsup>\<rho>\<^esup> k = cs\<^bsup>\<rho>'\<^esup> k'\<close> using csk1 csk1' csk by auto

  hence kk': \<open>\<rho>' k' = \<rho> k\<close> using last_cs by metis

  have suc': \<open>\<rho> (Suc k) = \<rho>' (Suc k')\<close> using suc suc\<rho> suc\<rho>' by auto

  have mm': \<open>\<rho>' m' = \<rho> m\<close> using ipd(1) ipd'(1) kk' by auto

  from cs_ipd[OF ipd km] cs_ipd[OF ipd' km',unfolded mm', folded csk']  
  have csm: \<open>cs\<^bsup>\<rho>\<^esup> m = cs\<^bsup>\<rho>'\<^esup> m'\<close> by metis

  from converged_ipd_same_icd[OF path\<rho> path\<rho>' lm  csm csk' icd\<rho> suc' ipd'[unfolded kk']]
  obtain l' where csl: \<open>cs\<^bsup>\<rho>\<^esup> l = cs\<^bsup>\<rho>'\<^esup> l'\<close> by blast
  
  have csl\<rho>: \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<rho>\<^esup> l\<close> using \<pi>\<rho> converge(1) cs_path_swap_le less_imp_le_nat path(1) path\<rho> by blast 

  have nretl: \<open>\<rho> l \<noteq> return\<close> by (metis icd\<rho> icd_imp_cd ret_no_cd)

  have csn': \<open>cs\<^bsup>\<rho>\<^esup> n = cs\<^bsup>\<rho>'\<^esup> n'\<close> using converge(2) cs_path_swap path path\<rho> path\<rho>' \<pi>\<rho> \<pi>\<rho>' by auto
  
  have ln': \<open>l' < n'\<close> using cs_order[OF path\<rho> path\<rho>' csl csn' nretl converge(1)] .
    
  have csl\<rho>': \<open>cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<rho>'\<^esup> l'\<close> using cs_path_swap_le[OF path(2) path\<rho>' \<pi>\<rho>'] ln' by auto

  have csl': \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close> using csl\<rho> csl\<rho>' csl by auto
  thus \<open>?thesis\<close> by blast
qed

lemma cd_is_cs_less: assumes \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> k \<prec> cs\<^bsup>\<pi>\<^esup> l\<close> proof -
  obtain xs where csl: \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>\<^esup> k @ xs @[\<pi> l]\<close> using cd_in_cs[OF assms] by blast
  hence len: \<open>length(cs\<^bsup>\<pi>\<^esup> k) < length (cs\<^bsup>\<pi>\<^esup> l)\<close> by auto
  have take: \<open>take (length (cs\<^bsup>\<pi>\<^esup> k)) (cs\<^bsup>\<pi>\<^esup> l) = cs\<^bsup>\<pi>\<^esup> k\<close> using csl by auto
  show \<open>?thesis\<close> using cs_less.intros[OF len take] . 
qed

lemma cs_select_id: assumes \<open>is_path \<pi>\<close> \<open>\<pi> k \<noteq> return\<close> shows \<open>\<pi>\<exclamdown>cs\<^bsup>\<pi>\<^esup> k = k\<close> (is \<open>?k = k\<close>) proof -
  have *: \<open>\<And> i . cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>\<^esup> k  \<Longrightarrow> i = k\<close> using cs_inj[OF assms] by metis  
  hence \<open>cs\<^bsup>\<pi>\<^esup> ?k = cs\<^bsup>\<pi>\<^esup> k\<close> unfolding cs_select_def using theI[of \<open>\<lambda> i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>\<^esup> k\<close> \<open>k\<close>] by auto
  thus \<open>?k = k\<close> using * by auto
qed

lemma cs_single_nocd: assumes \<open>cs\<^bsup>\<pi>\<^esup> i = [x]\<close> shows \<open>\<forall> k. \<not> i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> proof -
  have \<open>\<not> (\<exists> k. i icd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close> apply (rule ccontr) using assms cs_not_nil by auto
  hence \<open>\<not> (\<exists> k. i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close> by (metis excd_impl_exicd)
  thus \<open>?thesis\<close> by blast
qed

lemma cs_single_pd_intermed: assumes \<open>is_path \<pi>\<close> \<open>cs\<^bsup>\<pi>\<^esup> n = [\<pi> n]\<close> \<open>k \<le> n\<close> shows \<open>\<pi> n pd\<rightarrow> \<pi> k\<close> proof -
  have \<open>\<forall> l. \<not> n icd\<^bsup>\<pi>\<^esup>\<rightarrow> l\<close> by (metis assms(2) cs_single_nocd icd_imp_cd)
  thus \<open>?thesis\<close> by (metis assms(1) assms(3) no_icd_pd)
qed


lemma cs_first_pd:  assumes path: \<open>is_path \<pi>\<close> and pd: \<open>\<pi> n pd\<rightarrow> \<pi> 0\<close> and first: \<open>\<forall> l < n. \<pi> l \<noteq> \<pi> n\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> n = [\<pi> n]\<close> 
by (metis cs_cases first first_pd_no_cd icd_imp_cd path pd)

lemma converged_pd_cs_single: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and  converge: \<open>l < m\<close> \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close> 
and \<pi>0: \<open>\<pi> 0 = \<pi>' 0\<close> and mpdl: \<open>\<pi> m pd\<rightarrow> \<pi> l\<close> and csl: \<open>cs\<^bsup>\<pi>\<^esup> l = [\<pi> l]\<close>
shows \<open>\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close> proof -
  have *: \<open>\<pi> l pd\<rightarrow> \<pi>' 0\<close> using cs_single_pd_intermed[OF path(1) csl] \<pi>0[symmetric] by auto
  have \<pi>m: \<open>\<pi> m = \<pi>' m'\<close> by (metis converge(2) last_cs)
  hence **: \<open>\<pi>' m' pd\<rightarrow> \<pi> l\<close> using mpdl by metis
  
  obtain l' where lm': \<open>l' \<le> m'\<close> and \<pi>l:  \<open>\<pi>' l' = \<pi> l\<close> (is \<open>?P l'\<close>) using path_pd_pd0[OF path(2) ** *] .
  
  let \<open>?l\<close> = \<open>(LEAST l'. \<pi>' l' = \<pi> l)\<close>
  
  have \<pi>l': \<open>\<pi>' ?l = \<pi> l\<close> using LeastI[of \<open>?P\<close>,OF \<pi>l] .
  moreover
  have \<open>\<forall> i <?l. \<pi>' i \<noteq> \<pi> l\<close> using Least_le[of \<open>?P\<close>] by (metis not_less)
  hence \<open>\<forall> i <?l. \<pi>' i \<noteq> \<pi>' ?l\<close> using \<pi>l' by metis
  moreover
  have \<open>\<pi>' ?l pd\<rightarrow> \<pi>' 0\<close> using * \<pi>l' by metis
  ultimately
  have \<open>cs\<^bsup>\<pi>'\<^esup> ?l = [\<pi>' ?l]\<close> using cs_first_pd[OF path(2)] by metis
  thus \<open>?thesis\<close> using csl \<pi>l' by metis
qed

lemma converged_cs_single: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and  converge: \<open>l < m\<close> \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close> 
and \<pi>0: \<open>\<pi> 0 = \<pi>' 0\<close> and csl: \<open>cs\<^bsup>\<pi>\<^esup> l = [\<pi> l]\<close>
shows \<open>\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close> proof cases
  assume *: \<open>\<pi> l = return\<close>  
  hence \<open>\<pi> m = return\<close> by (metis converge(1) path(1) term_path_stable less_imp_le)
  hence \<open>cs\<^bsup>\<pi>\<^esup> m = [return]\<close> using cs_return by auto
  hence \<open>cs\<^bsup>\<pi>'\<^esup> m' = [return]\<close> using converge by simp
  moreover
  have \<open>cs\<^bsup>\<pi>\<^esup> l = [return]\<close> using * cs_return by auto
  ultimately show \<open>?thesis\<close> by metis
next
  assume nret: \<open>\<pi> l \<noteq> return\<close>
  have \<pi>m: \<open>\<pi> m = \<pi>' m'\<close> by (metis converge(2) last_cs)
  
  obtain \<pi>\<^sub>1 n where path1: \<open>is_path \<pi>\<^sub>1\<close> and upto: \<open>\<pi> =\<^bsub>m\<^esub> \<pi>\<^sub>1\<close> and \<pi>n: \<open>\<pi>\<^sub>1 n = return\<close> using path(1) path_swap_ret by blast

  obtain \<pi>\<^sub>1' n' where path1': \<open>is_path \<pi>\<^sub>1'\<close> and upto': \<open>\<pi>' =\<^bsub>m'\<^esub>  \<pi>\<^sub>1'\<close> and \<pi>n': \<open>\<pi>\<^sub>1' n' = return\<close> using path(2) path_swap_ret by blast

  have \<pi>1l: \<open>\<pi>\<^sub>1 l = \<pi> l\<close> using upto converge(1) by (metis eq_up_to_def nat_less_le)

  have cs1l: \<open>cs\<^bsup>\<pi>\<^sub>1\<^esup> l = cs\<^bsup>\<pi>\<^esup> l\<close> using cs_path_swap_le upto path1 path(1) converge(1) by auto

  have csl1: \<open>cs\<^bsup>\<pi>\<^sub>1\<^esup> l = [\<pi>\<^sub>1 l]\<close> by (metis \<pi>1l cs1l csl)
  
  have converge1: \<open>cs\<^bsup>\<pi>\<^sub>1\<^esup> n = cs\<^bsup>\<pi>\<^sub>1'\<^esup> n'\<close> using \<pi>n \<pi>n' cs_return by auto
  
  have ln: \<open>l < n\<close> using nret \<pi>n \<pi>1l term_path_stable[OF path1 \<pi>n] by (auto, metis linorder_neqE_nat less_imp_le)

  have \<pi>01: \<open>\<pi>\<^sub>1 0 = \<pi>\<^sub>1' 0\<close> using \<pi>0 eq_up_to_apply[OF upto] eq_up_to_apply[OF upto'] by auto

  have pd: \<open>\<pi>\<^sub>1 n pd\<rightarrow> \<pi>\<^sub>1 l\<close> using \<pi>n by (metis path1 path_nodes return_pd)
  
  obtain l' where csl: \<open>cs\<^bsup>\<pi>\<^sub>1\<^esup> l = cs\<^bsup>\<pi>\<^sub>1'\<^esup> l'\<close> using converged_pd_cs_single[OF path1 path1' ln converge1 \<pi>01 pd csl1] by blast

  have cs1m: \<open>cs\<^bsup>\<pi>\<^sub>1\<^esup> m = cs\<^bsup>\<pi>\<^esup> m\<close> using cs_path_swap upto path1 path(1) by auto
  have cs1m': \<open>cs\<^bsup>\<pi>\<^sub>1'\<^esup> m' = cs\<^bsup>\<pi>'\<^esup> m'\<close> using cs_path_swap upto' path1' path(2) by auto
  hence converge1: \<open>cs\<^bsup>\<pi>\<^sub>1\<^esup> m = cs\<^bsup>\<pi>\<^sub>1'\<^esup> m'\<close> using converge(2) cs1m by metis
  
  have nret1: \<open>\<pi>\<^sub>1 l \<noteq> return\<close> using nret \<pi>1l by auto
  
  have lm': \<open>l' < m'\<close> using cs_order[OF path1 path1' csl converge1 nret1 converge(1)] .
  
  have \<open>cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<pi>\<^sub>1'\<^esup> l'\<close> using cs_path_swap_le[OF path(2) path1' upto'] lm' by auto
  moreover
  have \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>\<^sub>1\<^esup> l\<close> using cs_path_swap_le[OF path(1) path1 upto] converge(1) by auto
  ultimately
  have \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close> using csl by auto
  thus \<open>?thesis\<close> by blast
qed

lemma converged_cd_same_suc: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and init: \<open>\<pi> 0 = \<pi>' 0\<close> 
and cd_suc: \<open>\<forall> k k'. cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k' \<and> l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k \<longrightarrow> \<pi> (Suc k) = \<pi>' (Suc k')\<close> and converge: \<open>l < m\<close> \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close> 
shows  \<open>\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close>
using path init cd_suc converge proof (induction \<open>\<pi>\<close> \<open>l\<close> rule: cs_induct,cases)
  case (cs \<pi> l)
  assume *: \<open>\<exists>k. l icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>
  let \<open>?k\<close> = \<open>THE k. l icd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close>
  have icd: \<open>l icd\<^bsup>\<pi>\<^esup>\<rightarrow> ?k\<close> by (metis "*" icd_is_the_icd)
  hence lcdk: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> ?k\<close> by (metis is_icdi_def)
  hence kl: \<open>?k<l\<close> using is_cdi_def by metis
  
  have \<open>\<And> j. ?k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<Longrightarrow> l cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using icd cd_trans is_icdi_def by fast
  hence suc': \<open>\<forall> j j'. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j' \<and> ?k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<longrightarrow> \<pi> (Suc j) = \<pi>' (Suc j')\<close> using cs.prems(4) by blast

  from cs.IH[OF * cs(2) path(2) cs(4) suc'] cs.prems kl 
  have \<open>\<exists>k'. cs\<^bsup>\<pi>\<^esup> (THE k. l icd\<^bsup>\<pi>\<^esup>\<rightarrow> k) = cs\<^bsup>\<pi>'\<^esup> k'\<close> by (metis Suc_lessD less_trans_Suc)
  then obtain k' where csk: \<open>cs\<^bsup>\<pi>\<^esup> ?k = cs\<^bsup>\<pi>'\<^esup> k'\<close> by blast
  
  have suc2: \<open>\<pi> (Suc ?k) = \<pi>' (Suc k')\<close> using cs.prems(4) lcdk csk by auto

  have km: \<open>?k < m\<close> using kl cs.prems(5) by simp
  
  from converged_same_icd[OF cs(2) path(2) cs.prems(5) cs.prems(6) csk icd suc2]  
  show \<open>?case\<close> .
next
  case (cs \<pi> l)
  assume \<open>\<not> (\<exists>k. l icd\<^bsup>\<pi>\<^esup>\<rightarrow> k)\<close>
  hence \<open>cs\<^bsup>\<pi>\<^esup> l = [\<pi> l]\<close> by auto
  with cs converged_cs_single
  show \<open>?case\<close> by metis
qed

lemma converged_cd_diverge: 
assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and init: \<open>\<pi> 0 = \<pi>' 0\<close> and notin: \<open>\<not> (\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l')\<close> and converge: \<open>l < m\<close> \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close> 
obtains k k' where \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> \<open>\<pi> (Suc k) \<noteq> \<pi>' (Suc k')\<close>
using assms converged_cd_same_suc by blast



lemma converged_cd_same_suc_return: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and \<pi>0: \<open>\<pi> 0 = \<pi>' 0\<close> 
and cd_suc: \<open>\<forall> k k'. cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k' \<and> l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k \<longrightarrow> \<pi> (Suc k) = \<pi>' (Suc k')\<close> and ret: \<open>\<pi>' n' = return\<close> 
shows  \<open>\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close>proof cases
  assume \<open>\<pi> l = return\<close>
  hence \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> n'\<close> using ret cs_return by presburger
  thus \<open>?thesis\<close> by blast
next
  assume nretl: \<open>\<pi> l \<noteq> return\<close>
  have \<open>\<pi> l \<in> nodes\<close> using path path_nodes by auto
  then obtain \<pi>l n where ipl: \<open>is_path \<pi>l\<close> and \<pi>l:  \<open>\<pi> l = \<pi>l 0\<close> and retn: \<open>\<pi>l n = return\<close> and notl: \<open>\<forall> i>0. \<pi>l i \<noteq> \<pi> l\<close> by (metis direct_path_return nretl)
  hence ip: \<open>is_path (\<pi>@\<^bsup>l\<^esup> \<pi>l)\<close> and l: \<open>(\<pi>@\<^bsup>l\<^esup> \<pi>l) l = \<pi> l\<close> and retl: \<open>(\<pi>@\<^bsup>l\<^esup> \<pi>l) (l + n) = return\<close> and nl: \<open>\<forall> i>l. (\<pi>@\<^bsup>l\<^esup> \<pi>l) i \<noteq> \<pi> l\<close> using path_cons[OF path(1) ipl \<pi>l] by auto
  
  have \<pi>0': \<open>(\<pi>@\<^bsup>l\<^esup> \<pi>l) 0 = \<pi>' 0\<close>  unfolding cs_0 using  \<pi>l \<pi>0  by auto

  have csn: \<open>cs\<^bsup>\<pi>@\<^bsup>l\<^esup> \<pi>l\<^esup>  (l+n) = cs\<^bsup>\<pi>'\<^esup> n'\<close> using ret retl cs_return by metis

  have eql: \<open>(\<pi>@\<^bsup>l\<^esup> \<pi>l) =\<^bsub>l\<^esub> \<pi>\<close> by (metis path_append_eq_up_to)    

  have csl': \<open>cs\<^bsup>\<pi>@\<^bsup>l\<^esup> \<pi>l\<^esup>  l = cs\<^bsup>\<pi>\<^esup> l\<close> using eql cs_path_swap ip path(1) by metis
  
  have \<open>0 < n\<close> using nretl[unfolded \<pi>l] retn by (metis neq0_conv)
  hence ln: \<open>l < l + n\<close> by simp

  have *: \<open>\<forall> k k'. cs\<^bsup>\<pi> @\<^bsup>l\<^esup> \<pi>l\<^esup>  k = cs\<^bsup>\<pi>'\<^esup> k' \<and> l cd\<^bsup>\<pi> @\<^bsup>l\<^esup> \<pi>l\<^esup>\<rightarrow> k \<longrightarrow> (\<pi> @\<^bsup>l\<^esup> \<pi>l) (Suc k) = \<pi>' (Suc k')\<close> proof (rule,rule,rule)  
    fix k k' assume *: \<open>cs\<^bsup>\<pi> @\<^bsup>l\<^esup> \<pi>l\<^esup>  k = cs\<^bsup>\<pi>'\<^esup> k' \<and> l cd\<^bsup>\<pi> @\<^bsup>l\<^esup> \<pi>l\<^esup>\<rightarrow> k\<close>
    hence kl: \<open>k < l\<close> using is_cdi_def by auto
    hence \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k' \<and> l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> using eql * cs_path_swap_le[OF ip path(1) eql,of \<open>k\<close>] cdi_path_swap_le[OF path(1) _ eql,of \<open>l\<close> \<open>k\<close>] by auto
    hence \<open>\<pi> (Suc k) = \<pi>' (Suc k')\<close> using cd_suc by blast
    then show \<open>(\<pi> @\<^bsup>l\<^esup> \<pi>l) (Suc k) = \<pi>' (Suc k')\<close> using cs_path_swap_le[OF ip path(1) eql,of \<open>Suc k\<close>] kl by auto
  qed 
  obtain l' where \<open>cs\<^bsup>\<pi> @\<^bsup>l\<^esup> \<pi>l\<^esup>  l = cs\<^bsup>\<pi>'\<^esup> l'\<close> using converged_cd_same_suc[OF ip path(2) \<pi>0' * ln csn]  by blast
  moreover
  have \<open>cs\<^bsup>\<pi>@\<^bsup>l\<^esup> \<pi>l\<^esup>  l = cs\<^bsup>\<pi>\<^esup> l\<close> using eql by (metis cs_path_swap ip path(1))
  ultimately
  show \<open>?thesis\<close> by metis
qed

lemma converged_cd_diverge_return: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and init: \<open>\<pi> 0 = \<pi>' 0\<close> 
and notin: \<open>\<not> (\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l')\<close> and ret: \<open>\<pi>' m' = return\<close> 
obtains k k' where \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> \<open>\<pi> (Suc k) \<noteq> \<pi>' (Suc k')\<close> using converged_cd_same_suc_return[OF path init _ ret, of \<open>l\<close>] notin by blast

lemma returned_missing_cd_or_loop: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and \<pi>0: \<open>\<pi> 0 = \<pi>' 0\<close> 
and notin': \<open>\<not>(\<exists> k'. cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k')\<close> and nret: \<open>\<forall> n'. \<pi>' n' \<noteq> return\<close> and ret: \<open>\<pi> n = return\<close> 
obtains i i' where \<open>i<k\<close> \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> \<open>\<pi> (Suc i) \<noteq> \<pi>' (Suc i')\<close> \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<or> (\<forall> j'> i'. j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i')\<close>
proof -  
  obtain f where icdf: \<open>\<forall> i'. f (Suc i') icd\<^bsup>\<pi>'\<^esup>\<rightarrow> f i'\<close> and ran: \<open>range f = {i'. \<forall> j'>i'. j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i'}\<close> and icdf0: \<open>\<not> (\<exists>i'. f 0 cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i')\<close> using path(2) path_nret_inf_icd_seq nret by blast
  show \<open>thesis\<close> proof cases
    assume \<open>\<exists> j. \<not> (\<exists> i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> (f j))\<close>
    then obtain j where ni\<pi>: \<open>\<not> (\<exists> i. cs\<^bsup>\<pi>'\<^esup> (f j) = cs\<^bsup>\<pi>\<^esup> i)\<close> by metis
    note converged_cd_diverge_return[OF path(2,1) \<pi>0[symmetric] ni\<pi> ret] that
    then obtain i k' where csk: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> k'\<close> and cdj: \<open>f j cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> and div:  \<open>\<pi> (Suc i) \<noteq> \<pi>' (Suc k')\<close> by metis
    have \<open>k' \<in> range f\<close> using cdj proof (induction \<open>j\<close>)
      case 0 thus \<open>?case\<close> using icdf0 by blast
    next
      case (Suc j)
      have icdfj: \<open>f (Suc j) icd\<^bsup>\<pi>'\<^esup>\<rightarrow> f j\<close> using icdf by auto
      show \<open>?case\<close> proof cases
        assume \<open>f (Suc j) icd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close>
        hence \<open>k' = f j\<close> using icdfj  by (metis icd_uniq)
        thus \<open>?case\<close> by auto
      next
        assume \<open>\<not> f (Suc j) icd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close>
        hence \<open>f j cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> using cd_impl_icd_cd[OF Suc.prems icdfj] by auto
        thus \<open>?case\<close> using Suc.IH by auto
      qed
    qed
    hence alldep: \<open>\<forall> i'>k'. i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> using ran by auto
    show \<open>thesis\<close> proof cases
      assume \<open>i < k\<close> with alldep that[OF _ csk div] show \<open>thesis\<close> by blast
    next
      assume \<open>\<not> i < k\<close>
      hence ki: \<open>k\<le>i\<close> by auto
      have \<open>k \<noteq> i\<close> using notin' csk by auto
      hence ki': \<open>k<i\<close> using ki by auto
      obtain ka k' where \<open>cs\<^bsup>\<pi>\<^esup> ka = cs\<^bsup>\<pi>'\<^esup> k'\<close> \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> ka\<close> \<open>\<pi> (Suc ka) \<noteq> \<pi>' (Suc k')\<close>
      using converged_cd_diverge[OF path \<pi>0 notin' ki' csk] by blast
      moreover
      hence \<open>ka < k\<close> unfolding is_cdi_def by auto
      ultimately
      show \<open>?thesis\<close> using that by blast
    qed
  next
    assume \<open>\<not>(\<exists> j. \<not> (\<exists> i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> (f j)))\<close>
    hence allin: \<open>\<forall> j. (\<exists> i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> (f j))\<close> by blast
    define f' where f': \<open>f' \<equiv> \<lambda> j. (SOME i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> (f j))\<close>
    have \<open>\<forall> i. f' i < f' (Suc i)\<close> proof
      fix i
      have csi: \<open>cs\<^bsup>\<pi>'\<^esup> (f i) = cs\<^bsup>\<pi>\<^esup> (f' i)\<close> unfolding f' using allin by (metis (mono_tags) someI_ex)
      have cssuci: \<open>cs\<^bsup>\<pi>'\<^esup> (f (Suc i)) = cs\<^bsup>\<pi>\<^esup> (f' (Suc i))\<close> unfolding f' using allin by (metis (mono_tags) someI_ex)
      have fi: \<open>f i < f (Suc i)\<close> using icdf unfolding is_icdi_def is_cdi_def by auto
      have \<open>f (Suc i) cd\<^bsup>\<pi>'\<^esup>\<rightarrow> f i\<close> using icdf unfolding is_icdi_def by blast
      hence nreti: \<open>\<pi>' (f i) \<noteq> return\<close> by (metis cd_not_ret)
      show \<open>f' i < f' (Suc i)\<close> using cs_order[OF path(2,1) csi cssuci nreti fi] .
    qed
    hence kle: \<open>k < f' (Suc k)\<close> using mono_ge_id[of \<open>f'\<close> \<open>Suc k\<close>] by auto
    have cssk: \<open>cs\<^bsup>\<pi>\<^esup> (f' (Suc k)) = cs\<^bsup>\<pi>'\<^esup> (f (Suc k))\<close> unfolding f' using allin by (metis (mono_tags) someI_ex)
    obtain ka k' where \<open>cs\<^bsup>\<pi>\<^esup> ka = cs\<^bsup>\<pi>'\<^esup> k'\<close> \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> ka\<close> \<open>\<pi> (Suc ka) \<noteq> \<pi>' (Suc k')\<close>
    using converged_cd_diverge[OF path \<pi>0 notin' kle cssk] by blast
    moreover
    hence \<open>ka < k\<close> unfolding is_cdi_def by auto
    ultimately
    show \<open>?thesis\<close> using that by blast
  qed
qed

lemma missing_cd_or_loop: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and \<pi>0: \<open>\<pi> 0 = \<pi>' 0\<close> and notin': \<open>\<not>(\<exists> k'. cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k')\<close>  
obtains i i' where \<open>i < k\<close> \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> \<open>\<pi> (Suc i) \<noteq> \<pi>' (Suc i')\<close> \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<or> (\<forall> j'> i'. j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i')\<close>
proof cases
  assume \<open>\<exists> n'. \<pi>' n' = return\<close>
  then obtain n' where retn: \<open>\<pi>' n' = return\<close> by blast
  note converged_cd_diverge_return[OF path \<pi>0 notin' retn]
  then obtain ka k' where \<open>cs\<^bsup>\<pi>\<^esup> ka = cs\<^bsup>\<pi>'\<^esup> k'\<close> \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> ka\<close> \<open>\<pi> (Suc ka) \<noteq> \<pi>' (Suc k')\<close> by blast
  moreover
  hence \<open>ka < k\<close> unfolding is_cdi_def by auto
  ultimately show \<open>thesis\<close> using that by simp
next
  assume \<open>\<not> (\<exists> n'. \<pi>' n' = return)\<close>
  hence notret: \<open>\<forall> n'. \<pi>' n' \<noteq> return\<close> by auto
  then obtain \<pi>l n where ipl: \<open>is_path \<pi>l\<close> and \<pi>l:  \<open>\<pi> k = \<pi>l 0\<close> and retn: \<open>\<pi>l n = return\<close> using reaching_ret path(1) path_nodes by metis
  hence ip: \<open>is_path (\<pi>@\<^bsup>k\<^esup>\<pi>l)\<close> and l: \<open>(\<pi>@\<^bsup>k\<^esup>\<pi>l) k = \<pi> k\<close> and retl: \<open>(\<pi>@\<^bsup>k\<^esup>\<pi>l) (k + n) = return\<close> using path_cons[OF path(1) ipl \<pi>l] by auto
  
  have \<pi>0': \<open>(\<pi>@\<^bsup>k\<^esup>\<pi>l) 0 = \<pi>' 0\<close>  unfolding cs_0 using  \<pi>l \<pi>0  by auto

  have eql: \<open>(\<pi>@\<^bsup>k\<^esup>\<pi>l) =\<^bsub>k\<^esub> \<pi>\<close> by (metis path_append_eq_up_to)    

  have csl': \<open>cs\<^bsup>\<pi>@\<^bsup>k\<^esup>\<pi>l\<^esup>  k = cs\<^bsup>\<pi>\<^esup> k\<close> using eql cs_path_swap ip path(1) by metis
  
  hence notin: \<open>\<not>(\<exists> k'. cs\<^bsup>\<pi>@\<^bsup>k\<^esup>\<pi>l\<^esup>  k = cs\<^bsup>\<pi>'\<^esup> k')\<close> using notin' by auto

  obtain i i' where *: \<open>i < k\<close> and csi: \<open>cs\<^bsup>\<pi>@\<^bsup>k\<^esup>\<pi>l\<^esup>  i = cs\<^bsup>\<pi>'\<^esup> i'\<close> and suci: \<open>(\<pi> @\<^bsup>k\<^esup> \<pi>l) (Suc i) \<noteq> \<pi>' (Suc i')\<close>  and cdloop: \<open>k cd\<^bsup>\<pi>@\<^bsup>k\<^esup>\<pi>l\<^esup>\<rightarrow> i \<or> (\<forall> j'>i'. j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i')\<close>
  using returned_missing_cd_or_loop[OF ip path(2) \<pi>0' notin notret retl] by blast

  have \<open>i \<noteq> k\<close> using notin csi by auto
  hence ik: \<open>i < k\<close> using * by auto
  hence \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> using csi cs_path_swap_le[OF ip path(1) eql] by auto
  moreover
  have \<open>\<pi> (Suc i) \<noteq> \<pi>' (Suc i')\<close> using ik eq_up_to_apply[OF eql, of \<open>Suc i\<close>] suci by auto
  moreover
  have \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<or> (\<forall> j'>i'. j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i')\<close> using cdloop cdi_path_swap_le[OF path(1) _ eql, of \<open>k\<close> \<open>i\<close>] by auto
  ultimately
  show \<open>thesis\<close> using that[OF *] by blast
qed


lemma path_shift_set_cd: assumes \<open>is_path \<pi>\<close> shows \<open>{k + j| j . n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> j } = {i. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i }\<close>
proof -
  { fix i
    assume \<open>i\<in>{k+j | j . n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> j }\<close>
    then obtain j where \<open>i = k+j\<close> \<open>n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> j\<close> by auto
    hence \<open>k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i\<close> using cd_path_shift[OF _ assms, of \<open>k\<close> \<open>k+j\<close> \<open>k+n\<close>] by simp
    hence \<open>i\<in>{ i. k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i }\<close> by blast
  }
  moreover
  { fix i
    assume \<open>i\<in>{ i. k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i }\<close>
    hence *: \<open>k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i\<close> by blast
    then obtain j where i: \<open>i = k+j\<close> by (metis le_Suc_ex)
    hence \<open>k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> k+j\<close> using * by auto
    hence \<open>n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> j\<close> using cd_path_shift[OF _ assms, of \<open>k\<close> \<open>k+j\<close> \<open>k+n\<close>] by simp
    hence \<open>i\<in>{k+j | j . n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> j }\<close> using i by simp
  }
  ultimately show \<open>?thesis\<close> by blast
qed

lemma cs_path_shift_set_cd: assumes path: \<open>is_path \<pi>\<close> shows \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n = map \<pi> (sorted_list_of_set {i. k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i }) @ [\<pi> (k+n)]\<close>
proof -
  have mono:\<open>\<forall>n m. n < m \<longrightarrow> k + n < k + m\<close> by auto
  have fin: \<open>finite {i. n cd\<^bsup>\<pi> \<guillemotleft> k\<^esup>\<rightarrow> i}\<close> unfolding is_cdi_def by auto
  have *: \<open>(\<lambda> x. k+x)`{i. n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> i} = {k + i | i. n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> i}\<close> by auto
  have \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n = map (\<pi>\<guillemotleft>k) (sorted_list_of_set {i. n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> i}) @ [(\<pi>\<guillemotleft>k) n]\<close> using cs_sorted_list_of_cd' by blast
  also 
  have \<open>\<dots> = map \<pi> (map (\<lambda> x. k+x) (sorted_list_of_set{i. n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> i})) @ [\<pi> (k+n)]\<close> by auto
  also 
  have \<open>\<dots> = map \<pi> (sorted_list_of_set ((\<lambda> x. k+x)`{i. n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> i})) @ [\<pi> (k+n)]\<close> using sorted_list_of_set_map_mono[OF mono fin] by auto
  also 
  have \<open>\<dots> = map \<pi> (sorted_list_of_set ({k + i | i. n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> i})) @ [\<pi> (k+n)]\<close> using * by auto
  also 
  have \<open>\<dots> = map \<pi> (sorted_list_of_set ({i. k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i})) @ [\<pi> (k+n)]\<close> using path_shift_set_cd[OF path] by auto
  finally
  show \<open>?thesis\<close> .
qed

lemma cs_split_shift_cd: assumes \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> and \<open>j < k\<close> and \<open>k < n\<close> and \<open>\<forall>j'<k. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> j' \<longrightarrow> j' \<le> j\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>\<^esup> j @ cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> (n-k)\<close>
proof -
  have path: \<open>is_path \<pi>\<close> using assms unfolding is_cdi_def by auto
  have 1: \<open>{i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} = {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k} \<union> {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i}\<close> by auto
  have le: \<open>\<forall> i\<in> {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k}. \<forall> j\<in> {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i}. i < j\<close> by auto
  
  have 2: \<open>{i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k} = {i . j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {j}\<close> proof - 
    { fix i assume \<open>i\<in>{i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k}\<close> 
      hence cd: \<open>n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> and ik:\<open>i < k\<close> by auto
      have \<open>i\<in>{i . j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {j}\<close> proof cases
        assume \<open>i < j\<close> hence \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> by (metis is_cdi_def assms(1) cd cdi_prefix nat_less_le)
        thus \<open>?thesis\<close> by simp
      next
        assume \<open>\<not> i < j\<close>
        moreover
        have \<open>i \<le> j\<close> using assms(4) ik cd by auto
        ultimately
        show \<open>?thesis\<close> by auto
      qed
    }
    moreover
    { fix i assume \<open>i\<in>{i . j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} \<union> {j}\<close>
      hence \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<or> i = j\<close> by auto
      hence \<open>i\<in>{i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k}\<close> using assms(1,2) cd_trans[OF _ assms(1)] apply auto unfolding is_cdi_def 
      by (metis (poly_guards_query) diff_diff_cancel diff_is_0_eq le_refl le_trans nat_less_le)
    }
    ultimately show \<open>?thesis\<close> by blast
  qed
  
  have \<open>cs\<^bsup>\<pi>\<^esup> n = map \<pi> (sorted_list_of_set {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}) @ [\<pi> n]\<close> using cs_sorted_list_of_cd' by simp
  also 
  have \<open>\<dots> = map \<pi> (sorted_list_of_set ({i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k} \<union> {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i})) @ [\<pi> n]\<close> using 1 by metis
  also 
  have \<open>\<dots> = map \<pi> ((sorted_list_of_set {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k}) @ (sorted_list_of_set {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i})) @ [\<pi> n]\<close>
    using sorted_list_of_set_append[OF _ _ le] is_cdi_def by auto
  also 
  have \<open>\<dots> = (map \<pi> (sorted_list_of_set {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k})) @ (map \<pi> (sorted_list_of_set {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i})) @ [\<pi> n]\<close> by auto
  also
  have \<open>\<dots> = cs\<^bsup>\<pi>\<^esup> j @ (map \<pi> (sorted_list_of_set {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i})) @ [\<pi> n]\<close> unfolding 2 using cs_sorted_list_of_cd by auto
  also 
  have \<open>\<dots> = cs\<^bsup>\<pi>\<^esup> j @ cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> (n-k)\<close> using cs_path_shift_set_cd[OF path, of \<open>k\<close> \<open>n-k\<close>] assms(3) by auto
  finally
  show \<open>?thesis\<close> .
qed

lemma cs_split_shift_nocd: assumes \<open>is_path \<pi>\<close> and \<open>k < n\<close> and \<open>\<forall>j. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<longrightarrow> k \<le> j\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> (n-k)\<close>
proof -
  have path: \<open>is_path \<pi>\<close> using assms by auto
  have 1: \<open>{i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i} = {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k} \<union> {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i}\<close> by auto
  have le: \<open>\<forall> i\<in> {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k}. \<forall> j\<in> {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i}. i < j\<close> by auto
  have 2: \<open>{i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k} = {}\<close> using assms by auto
  
  have \<open>cs\<^bsup>\<pi>\<^esup> n = map \<pi> (sorted_list_of_set {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i}) @ [\<pi> n]\<close> using cs_sorted_list_of_cd' by simp
  also 
  have \<open>\<dots> = map \<pi> (sorted_list_of_set ({i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> i < k} \<union> {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i})) @ [\<pi> n]\<close> using 1 by metis
  also 
  have \<open>\<dots> = map \<pi> (sorted_list_of_set {i. n cd\<^bsup>\<pi>\<^esup>\<rightarrow> i \<and> k \<le> i}) @ [\<pi> n]\<close>
    unfolding 2 by auto
  also 
  have \<open>\<dots> = cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> (n-k)\<close> using cs_path_shift_set_cd[OF path, of \<open>k\<close> \<open>n-k\<close>] assms(2)  by auto
  finally show \<open>?thesis\<close> .
qed

lemma shifted_cs_eq_is_eq: assumes \<open>is_path \<pi>\<close> and \<open>is_path \<pi>'\<close> and \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> and \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> n'\<close> shows \<open>cs\<^bsup>\<pi>\<^esup> (k+n) = cs\<^bsup>\<pi>'\<^esup> (k'+n')\<close>
proof (rule ccontr)
  note path = assms(1,2)
  note csk = assms(3)
  note csn = assms(4)
  assume ne: \<open>cs\<^bsup>\<pi>\<^esup> (k+n) \<noteq> cs\<^bsup>\<pi>'\<^esup> (k'+n')\<close>
  have nretkn:\<open>\<pi> (k+n) \<noteq> return\<close> proof 
    assume 1:\<open>\<pi> (k+n) = return\<close>
    hence \<open>(\<pi>\<guillemotleft>k) n = return\<close> by auto
    hence \<open>(\<pi>'\<guillemotleft>k') n' = return\<close> using last_cs assms(4) by metis
    hence \<open>\<pi>' (k' + n') = return\<close> by auto
    thus \<open>False\<close> using ne 1 cs_return by auto
  qed
  hence nretk: \<open>\<pi> k \<noteq> return\<close> using term_path_stable[OF assms(1), of \<open>k\<close> \<open>k +n\<close>] by auto
  have nretkn': \<open>\<pi>' (k'+n') \<noteq> return\<close> proof 
    assume 1:\<open>\<pi>' (k'+n') = return\<close>
    hence \<open>(\<pi>'\<guillemotleft>k') n' = return\<close> by auto
    hence \<open>(\<pi>\<guillemotleft>k) n = return\<close> using last_cs assms(4) by metis
    hence \<open>\<pi> (k + n) = return\<close> by auto
    thus \<open>False\<close> using ne 1 cs_return by auto
  qed
  hence nretk': \<open>\<pi>' k' \<noteq> return\<close> using term_path_stable[OF assms(2), of \<open>k'\<close> \<open>k' +n'\<close>] by auto
  have n0:\<open>n > 0\<close> proof (rule ccontr)
    assume *: \<open>\<not> 0 < n\<close>    
    hence 1:\<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> 0 = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> n'\<close> using assms(3,4) by auto
    have \<open>(\<pi>\<guillemotleft>k) 0 = (\<pi>'\<guillemotleft>k') 0\<close> using assms(3) last_cs path_shift_def by (metis monoid_add_class.add.right_neutral)
    hence \<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> 0 = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> n'\<close> using 1 cs_0 by metis
    hence n0': \<open>n' = 0\<close> using cs_inj[of \<open>\<pi>'\<guillemotleft>k'\<close> \<open>0\<close> \<open>n'\<close> ] * assms(2) by (metis path_shift_def assms(4) last_cs nretkn path_path_shift)
    thus \<open>False\<close> using ne * assms(3) by fastforce
  qed
  have n0':\<open>n' > 0\<close> proof (rule ccontr)
    assume *: \<open>\<not> 0 < n'\<close>    
    hence 1:\<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> 0 = cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n\<close> using assms(3,4) by auto
    have \<open>(\<pi>'\<guillemotleft>k') 0 = (\<pi>\<guillemotleft>k) 0\<close> using assms(3) last_cs path_shift_def by (metis monoid_add_class.add.right_neutral)
    hence \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> 0 = cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n\<close> using 1 cs_0 by metis
    hence n0: \<open>n = 0\<close> using cs_inj[of \<open>\<pi>\<guillemotleft>k\<close> \<open>0\<close> \<open>n\<close> ] * assms(1) by (metis path_shift_def assms(4) last_cs nretkn path_path_shift)
    thus \<open>False\<close> using ne * assms(3) by fastforce
  qed
  have cdleswap': \<open>\<forall> j'<k'. (k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j' \<longrightarrow> (\<exists>j<k. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close> proof (rule,rule,rule, rule ccontr)
    fix j' assume jk': \<open>j'<k'\<close> and ncdj': \<open>(k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> and ne: \<open>\<not> (\<exists>j<k. k + n cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close>
    hence kcdj': \<open>k' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> using cr_wn' by blast 
      
      then obtain j where kcdj: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> and csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> using csk cs_path_swap_cd path by metis
      hence jk: \<open>j < k\<close> unfolding is_cdi_def by auto
      
      have ncdn: \<open>\<not> (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using ne csj jk by blast 
      
      obtain l' where lnocd': \<open>l' = n' \<or> n' cd\<^bsup>\<pi>'\<guillemotleft>k'\<^esup>\<rightarrow> l'\<close> and cslsing': \<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> l' = [(\<pi>'\<guillemotleft>k') l']\<close>        
        proof cases
          assume \<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> n' = [(\<pi>'\<guillemotleft>k') n']\<close> thus \<open>thesis\<close> using that[of \<open>n'\<close>] by auto
        next
          assume *: \<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> n' \<noteq> [(\<pi>'\<guillemotleft>k') n']\<close>
          then obtain x ys where \<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> n' = [x]@ys@[(\<pi>'\<guillemotleft>k') n']\<close> by (metis append_Cons append_Nil cs_length_g_one cs_length_one(1) neq_Nil_conv) 
          then obtain l' where \<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> l' = [x]\<close> and cdl': \<open>n' cd\<^bsup>\<pi>'\<guillemotleft>k'\<^esup>\<rightarrow> l'\<close> using cs_split[of \<open>\<pi>'\<guillemotleft>k'\<close> \<open>n'\<close> \<open>Nil\<close> \<open>x\<close> \<open>ys\<close>] by auto
          hence \<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> l' = [(\<pi>'\<guillemotleft>k') l']\<close> using last_cs by (metis last.simps) 
          thus \<open>thesis\<close> using that cdl' by auto
      qed
      hence ln': \<open>l'\<le>n'\<close> unfolding is_cdi_def by auto
      hence lcdj': \<open>k'+l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> using jk' ncdj'  by (metis add_le_cancel_left cdi_prefix trans_less_add1)
            
      obtain l where lnocd: \<open>l = n \<or> n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> l\<close> and csl: \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> l = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> l'\<close> using lnocd' proof
        assume \<open>l' = n'\<close> thus \<open>thesis\<close> using csn that[of \<open>n\<close>] by auto
        next
        assume \<open>n' cd\<^bsup>\<pi>'\<guillemotleft>k'\<^esup>\<rightarrow> l'\<close>
        then obtain l where \<open>n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> l\<close> \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> l = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> l'\<close> using cs_path_swap_cd path csn by (metis path_path_shift)
        thus \<open>thesis\<close> using that by auto
      qed
      
      have cslsing: \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> l = [(\<pi>\<guillemotleft>k) l]\<close> using cslsing' last_cs csl last.simps by metis
      
      have ln: \<open>l\<le>n\<close> using lnocd unfolding is_cdi_def by auto
      hence nretkl: \<open>\<pi> (k + l) \<noteq> return\<close> using term_path_stable[of \<open>\<pi>\<close> \<open>k+l\<close> \<open>k+n\<close>] nretkn path(1) by auto  
      
      have *: \<open>n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> l \<Longrightarrow> k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> k+l\<close> using cd_path_shift[of \<open>k\<close> \<open>k+l\<close> \<open>\<pi>\<close> \<open>k+n\<close>] path(1) by auto
      
      have ncdl: \<open>\<not> (k+l) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> apply rule using lnocd apply rule using ncdn apply blast using cd_trans ncdn * by blast      
      
      hence \<open>\<exists> i\<in> {j..k+l}. \<pi> i = ipd (\<pi> j)\<close> unfolding is_cdi_def using path(1) jk nretkl by auto
      hence \<open>\<exists> i\<in> {k<..k+l}. \<pi> i = ipd (\<pi> j)\<close> using kcdj unfolding is_cdi_def by force
      
      then obtain i where ki: \<open>k < i\<close> and il: \<open>i \<le> k+l\<close> and ipdi: \<open>\<pi> i = ipd (\<pi> j)\<close> by force
      
      hence \<open>(\<pi>\<guillemotleft>k) (i-k) = ipd (\<pi> j)\<close> \<open>i-k \<le> l\<close> by auto
      hence pd: \<open>(\<pi>\<guillemotleft>k) l pd\<rightarrow> ipd (\<pi> j)\<close> using cs_single_pd_intermed[OF _ cslsing] path(1) path_path_shift by metis
      moreover
      have \<open>(\<pi>\<guillemotleft>k) l = \<pi>' (k' + l')\<close> using csl last_cs by (metis path_shift_def)
      moreover
      have \<open>\<pi> j = \<pi>' j'\<close> using csj last_cs by metis
      ultimately
      have \<open>\<pi>' (k'+l') pd\<rightarrow> ipd (\<pi>' j')\<close> by simp
      moreover
      have \<open>ipd (\<pi>' j') pd\<rightarrow> \<pi>' (k'+l')\<close> using ipd_pd_cd[OF lcdj'] .
      ultimately
      have \<open>\<pi>' (k'+l') = ipd (\<pi>' j')\<close> using pd_antisym by auto
      thus \<open>False\<close> using lcdj' unfolding is_cdi_def by force
  qed
  
  \<comment> \<open>Symmetric version of the above statement\<close>
  have cdleswap: \<open>\<forall> j<k. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<longrightarrow> (\<exists>j'<k'. (k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j' \<and> cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close> proof (rule,rule,rule, rule ccontr)
    fix j assume jk: \<open>j<k\<close> and ncdj: \<open>(k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> and ne: \<open>\<not> (\<exists>j'<k'. k' + n' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j' \<and> cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close>
    hence kcdj: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using cr_wn' by blast
      
      then obtain j' where kcdj': \<open>k' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> and csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> using csk cs_path_swap_cd path by metis
      hence jk': \<open>j' < k'\<close> unfolding is_cdi_def by auto
      
      have ncdn': \<open>\<not> (k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> using ne csj jk' by blast 
      
      obtain l where lnocd: \<open>l = n \<or> n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> l\<close> and cslsing: \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> l = [(\<pi>\<guillemotleft>k) l]\<close>        
        proof cases
          assume \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n = [(\<pi>\<guillemotleft>k) n]\<close> thus \<open>thesis\<close> using that[of \<open>n\<close>] by auto
        next
          assume *: \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n \<noteq> [(\<pi>\<guillemotleft>k) n]\<close>
          then obtain x ys where \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n = [x]@ys@[(\<pi>\<guillemotleft>k) n]\<close> by (metis append_Cons append_Nil cs_length_g_one cs_length_one(1) neq_Nil_conv) 
          then obtain l where \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> l = [x]\<close> and cdl: \<open>n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> l\<close> using cs_split[of \<open>\<pi>\<guillemotleft>k\<close> \<open>n\<close> \<open>Nil\<close> \<open>x\<close> \<open>ys\<close>] by auto
          hence \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> l = [(\<pi>\<guillemotleft>k) l]\<close> using last_cs by (metis last.simps) 
          thus \<open>thesis\<close> using that cdl by auto
      qed
      hence ln: \<open>l\<le>n\<close> unfolding is_cdi_def by auto
      hence lcdj: \<open>k+l cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using jk ncdj  by (metis add_le_cancel_left cdi_prefix trans_less_add1)
            
      obtain l' where lnocd': \<open>l' = n' \<or> n' cd\<^bsup>\<pi>'\<guillemotleft>k'\<^esup>\<rightarrow> l'\<close> and csl: \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> l = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> l'\<close> using lnocd proof
        assume \<open>l = n\<close> thus \<open>thesis\<close> using csn that[of \<open>n'\<close>] by auto
        next
        assume \<open>n cd\<^bsup>\<pi>\<guillemotleft>k\<^esup>\<rightarrow> l\<close>
        then obtain l' where \<open>n' cd\<^bsup>\<pi>'\<guillemotleft>k'\<^esup>\<rightarrow> l'\<close> \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> l = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> l'\<close> using cs_path_swap_cd path csn by (metis path_path_shift)
        thus \<open>thesis\<close> using that by auto
      qed
      
      have cslsing': \<open>cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> l' = [(\<pi>'\<guillemotleft>k') l']\<close> using cslsing last_cs csl last.simps by metis
      
      have ln': \<open>l'\<le>n'\<close> using lnocd' unfolding is_cdi_def by auto
      hence nretkl': \<open>\<pi>' (k' + l') \<noteq> return\<close> using term_path_stable[of \<open>\<pi>'\<close> \<open>k'+l'\<close> \<open>k'+n'\<close>] nretkn' path(2) by auto  
      
      have *: \<open>n' cd\<^bsup>\<pi>'\<guillemotleft>k'\<^esup>\<rightarrow> l' \<Longrightarrow> k'+n' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'+l'\<close> using cd_path_shift[of \<open>k'\<close> \<open>k'+l'\<close> \<open>\<pi>'\<close> \<open>k'+n'\<close>] path(2) by auto
      
      have ncdl': \<open>\<not> (k'+l') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> apply rule using lnocd' apply rule using ncdn' apply blast using cd_trans ncdn' * by blast      
      
      hence \<open>\<exists> i'\<in> {j'..k'+l'}. \<pi>' i' = ipd (\<pi>' j')\<close> unfolding is_cdi_def using path(2) jk' nretkl' by auto
      hence \<open>\<exists> i'\<in> {k'<..k'+l'}. \<pi>' i' = ipd (\<pi>' j')\<close> using kcdj' unfolding is_cdi_def by force
      
      then obtain i' where ki': \<open>k' < i'\<close> and il': \<open>i' \<le> k'+l'\<close> and ipdi: \<open>\<pi>' i' = ipd (\<pi>' j')\<close> by force
      
      hence \<open>(\<pi>'\<guillemotleft>k') (i'-k') = ipd (\<pi>' j')\<close> \<open>i'-k' \<le> l'\<close> by auto
      hence pd: \<open>(\<pi>'\<guillemotleft>k') l' pd\<rightarrow> ipd (\<pi>' j')\<close> using cs_single_pd_intermed[OF _ cslsing'] path(2) path_path_shift by metis
      moreover
      have \<open>(\<pi>'\<guillemotleft>k') l' = \<pi> (k + l)\<close> using csl last_cs by (metis path_shift_def)
      moreover
      have \<open>\<pi>' j' = \<pi> j\<close> using csj last_cs by metis
      ultimately
      have \<open>\<pi> (k+l) pd\<rightarrow> ipd (\<pi> j)\<close> by simp
      moreover
      have \<open>ipd (\<pi> j) pd\<rightarrow> \<pi> (k+l)\<close> using ipd_pd_cd[OF lcdj] .
      ultimately
      have \<open>\<pi> (k+l) = ipd (\<pi> j)\<close> using pd_antisym by auto
      thus \<open>False\<close> using lcdj unfolding is_cdi_def by force
  qed
  
  have cdle: \<open>\<exists>j. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> j < k\<close> (is \<open>\<exists> j. ?P j\<close>) proof (rule ccontr)
    assume \<open>\<not> (\<exists>j. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> j < k)\<close>
    hence allge: \<open>\<forall>j. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<longrightarrow> k \<le> j\<close> by auto
    have allge': \<open>\<forall>j'. (k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j' \<longrightarrow> k' \<le> j'\<close> proof (rule, rule, rule ccontr)
      fix j' 
      assume *: \<open>k' + n' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> and \<open>\<not> k' \<le> j'\<close>
      then obtain j where \<open>j<k\<close> \<open>(k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using cdleswap' by (metis le_neq_implies_less nat_le_linear)
      thus \<open>False\<close> using allge by auto
    qed
    have \<open>cs\<^bsup>\<pi>\<^esup> (k + n) = cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n\<close> using cs_split_shift_nocd[OF assms(1) _ allge] n0 by auto
    moreover
    have \<open>cs\<^bsup>\<pi>'\<^esup> (k' + n') = cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close> using cs_split_shift_nocd[OF assms(2) _ allge'] n0' by auto
    ultimately
    show \<open>False\<close> using ne assms(4) by auto
  qed
  
  define j where  \<open>j == GREATEST j. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> j < k\<close>  
  have cdj:\<open>(k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> and jk: \<open>j < k\<close> and jge:\<open>\<forall> j'< k. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j' \<longrightarrow> j' \<le> j\<close> proof -
    have bound: \<open>\<forall> y. ?P y \<longrightarrow> y \<le> k\<close> by auto
    show \<open>(k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using GreatestI_nat[of \<open>?P\<close>] j_def bound cdle by blast
    show \<open>j < k\<close> using GreatestI_nat[of \<open>?P\<close>] bound j_def cdle by blast
    show \<open>\<forall> j'< k. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j' \<longrightarrow> j' \<le> j\<close> using Greatest_le_nat[of \<open>?P\<close>] bound j_def by blast
  qed
    
  obtain j' where cdj':\<open>(k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> and csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close>  and jk': \<open>j' < k'\<close> using cdleswap cdj jk by blast
  have jge':\<open>\<forall> i'< k'. (k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i' \<longrightarrow> i' \<le> j'\<close> proof(rule,rule,rule)
    fix i'
    assume ik': \<open>i' < k'\<close> and cdi': \<open>k' + n' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i'\<close>
    then obtain i where cdi:\<open>(k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> and csi: \<open> cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i\<close> and ik: \<open>i<k\<close> using cdleswap' by force 
    have ij: \<open>i \<le> j\<close> using jge cdi ik by auto
    show \<open>i' \<le> j'\<close> using cs_order_le[OF assms(1,2) csi[symmetric] csj _ ij] cd_not_ret[OF cdi] by simp
  qed
  have \<open>cs\<^bsup>\<pi>\<^esup> (k + n) = cs\<^bsup>\<pi>\<^esup> j @ cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n\<close> using  cs_split_shift_cd[OF cdj jk _ jge] n0 by auto
  moreover
  have \<open>cs\<^bsup>\<pi>'\<^esup> (k' + n') = cs\<^bsup>\<pi>'\<^esup> j' @ cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close> using  cs_split_shift_cd[OF cdj' jk' _ jge'] n0' by auto
  ultimately
  have \<open>cs\<^bsup>\<pi>\<^esup> (k+n) = cs\<^bsup>\<pi>'\<^esup> (k'+n')\<close> using csj assms(4) by auto
  thus \<open>False\<close> using ne by simp
qed

lemma cs_eq_is_eq_shifted: assumes \<open>is_path \<pi>\<close> and \<open>is_path \<pi>'\<close> and \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> and \<open>cs\<^bsup>\<pi>\<^esup> (k+n) = cs\<^bsup>\<pi>'\<^esup> (k'+n')\<close> shows \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> n'\<close>
proof (rule ccontr)
  assume ne: \<open>cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n \<noteq> cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close>
  have nretkn:\<open>\<pi> (k+n) \<noteq> return\<close> proof 
    assume 1:\<open>\<pi> (k+n) = return\<close>
    hence 2:\<open>\<pi>' (k'+n') = return\<close> using assms(4) last_cs by metis
    hence \<open>(\<pi>\<guillemotleft>k) n = return\<close> \<open>(\<pi>'\<guillemotleft>k') n' = return\<close> using 1 by auto
    hence \<open>cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n = cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close> using cs_return by metis 
    thus \<open>False\<close> using ne by simp
  qed
  hence nretk: \<open>\<pi> k \<noteq> return\<close> using term_path_stable[OF assms(1), of \<open>k\<close> \<open>k +n\<close>] by auto
  have nretkn': \<open>\<pi>' (k'+n') \<noteq> return\<close> proof 
    assume 1:\<open>\<pi>' (k'+n') = return\<close>
    hence 2:\<open>\<pi> (k+n) = return\<close> using assms(4) last_cs by metis
    hence \<open>(\<pi>\<guillemotleft>k) n = return\<close> \<open>(\<pi>'\<guillemotleft>k') n' = return\<close> using 1 by auto
    hence \<open>cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n = cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close> using cs_return by metis 
    thus \<open>False\<close> using ne by simp
  qed
  hence nretk': \<open>\<pi>' k' \<noteq> return\<close> using term_path_stable[OF assms(2), of \<open>k'\<close> \<open>k' +n'\<close>] by auto
  have n0:\<open>n > 0\<close> proof (rule ccontr)
    assume *: \<open>\<not> 0 < n\<close>    
    hence \<open>cs\<^bsup>\<pi>'\<^esup> k' = cs\<^bsup>\<pi>'\<^esup> (k'+ n')\<close> using assms(3,4) by auto
    hence n0: \<open>n = 0\<close> \<open>n' = 0\<close> using cs_inj[OF assms(2) nretkn', of \<open>k'\<close>] * by auto
    have \<open>cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n = cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close> unfolding n0 cs_0 by (auto , metis last_cs assms(3))
    thus \<open>False\<close> using ne by simp
  qed
  have n0':\<open>n' > 0\<close> proof (rule ccontr)
    assume *: \<open>\<not> 0 < n'\<close>    
    hence \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>\<^esup> (k+ n)\<close> using assms(3,4) by auto
    hence n0: \<open>n = 0\<close> \<open>n' = 0\<close> using cs_inj[OF assms(1) nretkn, of \<open>k\<close>] * by auto
    have \<open>cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n = cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close> unfolding n0 cs_0 by (auto , metis last_cs assms(3))
    thus \<open>False\<close> using ne by simp
  qed
  have cdle: \<open>\<exists>j. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> j < k\<close> (is \<open>\<exists> j. ?P j\<close>) proof (rule ccontr)
    assume \<open>\<not> (\<exists>j. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> j < k)\<close>
    hence allge: \<open>\<forall>j. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<longrightarrow> k \<le> j\<close> by auto
    have allge': \<open>\<forall>j'. (k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j' \<longrightarrow> k' \<le> j'\<close> proof (rule, rule)
      fix j' 
      assume *: \<open>k' + n' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close>
      obtain j where cdj: \<open>k+n cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> and csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> using cs_path_swap_cd[OF assms(2,1) assms(4)[symmetric] *] by metis
      hence kj:\<open>k \<le> j\<close> using allge by auto
      thus kj': \<open>k' \<le> j'\<close> using cs_order_le[OF assms(1,2,3) csj nretk] by simp
    qed
    have \<open>cs\<^bsup>\<pi>\<^esup> (k + n) = cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n\<close> using cs_split_shift_nocd[OF assms(1) _ allge] n0 by auto
    moreover
    have \<open>cs\<^bsup>\<pi>'\<^esup> (k' + n') = cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close> using cs_split_shift_nocd[OF assms(2) _ allge'] n0' by auto
    ultimately
    show \<open>False\<close> using ne assms(4) by auto
  qed
  define j where  \<open>j == GREATEST j. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j \<and> j < k\<close>  
  have cdj:\<open>(k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> and jk: \<open>j < k\<close> and jge:\<open>\<forall> j'< k. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j' \<longrightarrow> j' \<le> j\<close> proof -
    have bound: \<open>\<forall> y. ?P y \<longrightarrow> y \<le> k\<close> by auto
    show \<open>(k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> using GreatestI_nat[of \<open>?P\<close>] bound j_def cdle by blast
    show \<open>j < k\<close> using GreatestI_nat[of \<open>?P\<close>] bound j_def cdle by blast
    show \<open>\<forall> j'< k. (k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> j' \<longrightarrow> j' \<le> j\<close> using Greatest_le_nat[of \<open>?P\<close>] bound j_def by blast
  qed
  obtain j' where cdj':\<open>(k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> j'\<close> and csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> using cs_path_swap_cd assms cdj by blast
  have jge':\<open>\<forall> i'< k'. (k'+n') cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i' \<longrightarrow> i' \<le> j'\<close> proof(rule,rule,rule)
    fix i'
    assume ik': \<open>i' < k'\<close> and cdi': \<open>k' + n' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i'\<close>
    then obtain i where cdi:\<open>(k+n) cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> and csi: \<open> cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i\<close> using cs_path_swap_cd[OF assms(2,1) assms(4)[symmetric]] by blast
    have nreti': \<open>\<pi>' i' \<noteq> return\<close> by (metis cd_not_ret cdi')
    have ik: \<open>i < k\<close> using cs_order[OF assms(2,1) csi _ nreti' ik'] assms(3) by auto
    have ij: \<open>i \<le> j\<close> using jge cdi ik by auto
    show \<open>i' \<le> j'\<close> using cs_order_le[OF assms(1,2) csi[symmetric] csj _ ij] cd_not_ret[OF cdi] by simp
  qed
  have jk': \<open>j' < k'\<close> using cs_order[OF assms(1,2) csj assms(3) cd_not_ret[OF cdj] jk] .
  have \<open>cs\<^bsup>\<pi>\<^esup> (k + n) = cs\<^bsup>\<pi>\<^esup> j @ cs\<^bsup>\<pi> \<guillemotleft> k\<^esup> n\<close> using  cs_split_shift_cd[OF cdj jk _ jge] n0 by auto
  moreover
  have \<open>cs\<^bsup>\<pi>'\<^esup> (k' + n') = cs\<^bsup>\<pi>'\<^esup> j' @ cs\<^bsup>\<pi>' \<guillemotleft> k'\<^esup> n'\<close> using  cs_split_shift_cd[OF cdj' jk' _ jge'] n0' by auto
  ultimately
  have \<open>cs\<^bsup>\<pi>\<guillemotleft>k\<^esup> n = cs\<^bsup>\<pi>'\<guillemotleft>k'\<^esup> n'\<close> using csj assms(4) by auto
  thus \<open>False\<close> using ne by simp
qed

lemma converged_cd_diverge_cs: assumes \<open>is_path \<pi>\<close> and \<open>is_path \<pi>'\<close> and \<open>cs\<^bsup>\<pi>\<^esup> j  = cs\<^bsup>\<pi>'\<^esup> j'\<close> and \<open>j<l\<close> and \<open>\<not> (\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l')\<close> and \<open>l < m\<close> and \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close>
obtains k k' where \<open>j\<le>k\<close> \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> and \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> and \<open>\<pi> (Suc k) \<noteq> \<pi>' (Suc k')\<close>
  proof -  
  have \<open>is_path (\<pi>\<guillemotleft>j)\<close> \<open>is_path (\<pi>'\<guillemotleft>j')\<close> using assms(1,2) path_path_shift by auto
  moreover
  have \<open>(\<pi>\<guillemotleft>j) 0 = (\<pi>'\<guillemotleft>j') 0\<close> using assms(3) last_cs by (metis path_shift_def add.right_neutral)
  moreover
  have \<open>\<not>(\<exists>l'. cs\<^bsup>\<pi>\<guillemotleft>j\<^esup> (l-j) = cs\<^bsup>\<pi>'\<guillemotleft>j'\<^esup> l')\<close> proof 
    assume \<open>\<exists>l'. cs\<^bsup>\<pi> \<guillemotleft> j\<^esup> (l - j) = cs\<^bsup>\<pi>' \<guillemotleft> j'\<^esup> l'\<close>
    then obtain l' where csl: \<open>cs\<^bsup>\<pi>\<guillemotleft>j\<^esup> (l - j) = cs\<^bsup>\<pi>'\<guillemotleft>j'\<^esup> l'\<close> by blast
      
    have \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> (j' + l')\<close> using shifted_cs_eq_is_eq[OF assms(1,2,3) csl] assms(4) by auto
    thus \<open>False\<close> using assms(5) by blast
  qed
  moreover
  have \<open>l-j < m-j\<close> using assms by auto
  moreover
  have \<open>\<pi> j \<noteq> return\<close> using cs_return assms(1-5) term_path_stable by (metis nat_less_le) 
  hence \<open>j'<m'\<close> using cs_order[OF assms(1,2,3,7)] assms by auto
  hence \<open>cs\<^bsup>\<pi>\<guillemotleft>j\<^esup> (m-j) = cs\<^bsup>\<pi>'\<guillemotleft>j'\<^esup> (m'-j')\<close> using cs_eq_is_eq_shifted[OF assms(1,2,3),of \<open>m-j\<close> \<open>m'-j'\<close>] assms(4,6,7) by auto
  ultimately
  obtain k k' where csk: \<open>cs\<^bsup>\<pi>\<guillemotleft>j\<^esup> k = cs\<^bsup>\<pi>'\<guillemotleft>j'\<^esup> k'\<close> and lcdk: \<open>l-j cd\<^bsup>\<pi>\<guillemotleft>j\<^esup>\<rightarrow> k\<close> and suc:\<open>(\<pi>\<guillemotleft>j) (Suc k) \<noteq> (\<pi>'\<guillemotleft>j') (Suc k')\<close> using converged_cd_diverge by blast
  
  have \<open>cs\<^bsup>\<pi>\<^esup> (j+k) = cs\<^bsup>\<pi>'\<^esup> (j'+k')\<close> using shifted_cs_eq_is_eq[OF assms(1-3) csk] .
  moreover
  have \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> j+k\<close> using lcdk assms(1,2,4) by (metis add.commute add_diff_cancel_right' cd_path_shift le_add1)
  moreover
  have \<open>\<pi> (Suc (j+k)) \<noteq> \<pi>' (Suc (j'+ k'))\<close> using suc by auto
  moreover
  have \<open>j \<le> j+k\<close> by auto
  ultimately
  show \<open>thesis\<close> using that[of \<open>j+k\<close> \<open>j'+k'\<close>] by auto
qed


lemma cs_ipd_conv: assumes csk: \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> and ipd: \<open>\<pi> l = ipd (\<pi> k)\<close> \<open>\<pi>' l' = ipd(\<pi>' k')\<close> 
  and nipd: \<open>\<forall>n\<in>{k..<l}. \<pi> n \<noteq> ipd (\<pi> k)\<close> \<open>\<forall>n'\<in>{k'..<l'}. \<pi>' n' \<noteq> ipd (\<pi>' k')\<close> and kl: \<open>k < l\<close> \<open>k' < l'\<close> 
shows \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close> using cs_ipd[OF ipd(1) nipd(1) kl(1)] cs_ipd[OF ipd(2) nipd(2) kl(2)] csk ipd by (metis (no_types) last_cs)

lemma cp_eq_cs: assumes \<open>((\<sigma>,k),(\<sigma>',k'))\<in>cp\<close> shows \<open>cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k'\<close> 
  using assms 
  apply(induction rule: cp.induct) 
     apply blast+ 
  apply simp 
  done 

lemma cd_cs_swap: assumes \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<close> \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close> \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> shows \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> k'\<close> proof -
  have \<open>\<exists> i. l icd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close> using assms(1) excd_impl_exicd by blast
  hence \<open>cs\<^bsup>\<pi>\<^esup> l \<noteq> [\<pi> l]\<close> by auto
  hence \<open>cs\<^bsup>\<pi>'\<^esup> l' \<noteq> [\<pi>' l']\<close> using assms last_cs by metis
  hence \<open>\<exists> i'. l' icd\<^bsup>\<pi>'\<^esup>\<rightarrow> i'\<close> by (metis cs_cases)
  hence path': \<open>is_path \<pi>'\<close> unfolding is_icdi_def is_cdi_def by auto
  from cd_in_cs[OF assms(1)]
  obtain ys where csl: \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>\<^esup> k @ ys @ [\<pi> l]\<close> by blast
  obtain xs where csk: \<open>cs\<^bsup>\<pi>\<^esup> k = xs@[\<pi> k]\<close> by (metis append_butlast_last_id cs_not_nil last_cs)
  have \<pi>l: \<open>\<pi> l = \<pi>' l'\<close> using assms last_cs by metis
  have csl': \<open>cs\<^bsup>\<pi>'\<^esup> l' = xs@[\<pi> k]@ys@[\<pi>' l']\<close> by (metis \<pi>l append_eq_appendI assms(2) csk csl)
  from cs_split[of \<open>\<pi>'\<close> \<open>l'\<close> \<open>xs\<close> \<open>\<pi> k\<close> \<open>ys\<close>]
  obtain m where csm: \<open>cs\<^bsup>\<pi>'\<^esup> m = xs @ [\<pi> k]\<close> and lcdm: \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> m\<close> using csl' by metis 
  have csm': \<open>cs\<^bsup>\<pi>'\<^esup> m = cs\<^bsup>\<pi>'\<^esup> k'\<close> by (metis assms(3) csk csm)
  have \<open>\<pi>' m \<noteq> return\<close> using lcdm unfolding is_cdi_def using term_path_stable by (metis nat_less_le)
  hence \<open>m = k'\<close> using cs_inj path' csm' by auto
  thus \<open>?thesis\<close> using lcdm by auto
qed


subsection \<open>Facts about Observations\<close>
lemma kth_obs_not_none: assumes \<open>is_kth_obs (path \<sigma>) k i\<close> obtains a where \<open>obsp \<sigma> i = Some a\<close> using assms unfolding is_kth_obs_def obsp_def by auto

lemma kth_obs_unique: \<open>is_kth_obs \<pi> k i \<Longrightarrow> is_kth_obs \<pi> k j \<Longrightarrow> i = j\<close> proof (induction \<open>i\<close> \<open>j\<close> rule: nat_sym_cases)
  case sym thus \<open>?case\<close> by simp
next
  case eq thus \<open>?case\<close> by simp
next
  case (less i j) 
  have \<open>obs_ids \<pi> \<inter> {..<i} \<subseteq> obs_ids \<pi> \<inter> {..<j}\<close> using less(1) by auto
  moreover
  have \<open>i \<in> obs_ids \<pi> \<inter> {..<j}\<close> using less unfolding is_kth_obs_def obs_ids_def by auto
  moreover  
  have \<open>i \<notin> obs_ids \<pi> \<inter> {..<i}\<close> by auto
  moreover 
  have \<open>card (obs_ids \<pi> \<inter> {..<i}) = card (obs_ids \<pi> \<inter> {..<j})\<close> using less.prems unfolding is_kth_obs_def by auto
  moreover
  have \<open>finite (obs_ids \<pi> \<inter> {..<i})\<close> \<open>finite (obs_ids \<pi> \<inter> {..<j})\<close> by auto
  ultimately 
  have \<open>False\<close> by (metis card_subset_eq)
  thus \<open>?case\<close> ..
qed

lemma obs_none_no_kth_obs: assumes \<open>obs \<sigma> k = None\<close> shows \<open>\<not> (\<exists> i. is_kth_obs (path \<sigma>) k i)\<close> 
  apply rule
  using assms 
  unfolding obs_def obsp_def 
  apply (auto split: option.split_asm)  
  by (metis assms kth_obs_not_none kth_obs_unique obs_def option.distinct(2) the_equality)

lemma obs_some_kth_obs : assumes \<open>obs \<sigma> k \<noteq> None\<close> obtains i where \<open>is_kth_obs (path \<sigma>) k i\<close> by (metis obs_def assms)

lemma not_none_is_obs: assumes \<open>att(\<pi> i) \<noteq> None\<close> shows \<open>is_kth_obs \<pi> (card (obs_ids \<pi> \<inter> {..<i})) i\<close>  unfolding is_kth_obs_def using assms by auto

lemma in_obs_ids_is_kth_obs: assumes \<open>i \<in> obs_ids \<pi>\<close> obtains k where \<open>is_kth_obs \<pi> k i\<close> proof 
  have \<open>att (\<pi> i) \<noteq> None\<close> using assms obs_ids_def by auto 
  thus \<open>is_kth_obs \<pi> (card (obs_ids \<pi> \<inter> {..<i})) i\<close> using not_none_is_obs by auto
qed

lemma kth_obs_stable: assumes \<open>is_kth_obs \<pi> l j\<close> \<open>k < l\<close> shows \<open>\<exists> i. is_kth_obs \<pi> k i\<close> using assms proof (induction \<open>l\<close> arbitrary: \<open>j\<close> rule: less_induct )
  case (less l j)
  have cardl: \<open>card (obs_ids \<pi> \<inter> {..<j}) = l\<close> using less is_kth_obs_def by auto
  then obtain i where  ex: \<open>i \<in> obs_ids \<pi> \<inter> {..<j}\<close> (is \<open>?P i\<close>) using less(3) by (metis card.empty empty_iff less_irrefl subsetI subset_antisym zero_diff zero_less_diff)
  have bound: \<open>\<forall> i. i \<in> obs_ids \<pi> \<inter> {..<j} \<longrightarrow> i \<le> j\<close> by auto
  let \<open>?i\<close> = \<open>GREATEST i. i \<in> obs_ids \<pi> \<inter> {..<j}\<close>
  have *: \<open>?i < j\<close> \<open>?i \<in> obs_ids \<pi>\<close> using GreatestI_nat[of \<open>?P\<close> \<open>i\<close> \<open>j\<close>] ex bound by auto
  have **: \<open>\<forall> i. i \<in> obs_ids \<pi> \<and> i<j \<longrightarrow> i \<le> ?i\<close> using Greatest_le_nat[of \<open>?P\<close> _ \<open>j\<close>] ex bound by auto
  have \<open>(obs_ids \<pi> \<inter> {..<?i}) \<union> {?i} = obs_ids \<pi> \<inter> {..<j}\<close> apply rule apply auto using *[simplified] apply simp+ using **[simplified] by auto
  moreover
  have \<open>?i \<notin> (obs_ids \<pi> \<inter> {..<?i})\<close> by auto
  ultimately
  have \<open>Suc (card (obs_ids \<pi> \<inter> {..<?i})) = l\<close> using cardl by (metis Un_empty_right Un_insert_right card_insert_disjoint finite_Int finite_lessThan)
  hence \<open>card (obs_ids \<pi> \<inter> {..<?i}) = l - 1\<close> by auto
  hence iko: \<open>is_kth_obs \<pi> (l - 1) ?i\<close> using *(2) unfolding is_kth_obs_def obs_ids_def by auto
  have ll: \<open>l - 1 < l\<close> by (metis One_nat_def diff_Suc_less less.prems(2) not_gr0 not_less0)
  note IV=less(1)[OF ll iko]
  show \<open>?thesis\<close> proof cases
    assume \<open>k < l - 1\<close> thus \<open>?thesis\<close> using IV by simp
  next
    assume \<open>\<not> k < l - 1\<close>
    hence \<open>k = l - 1\<close> using less by auto
    thus \<open>?thesis\<close> using iko by blast
  qed
qed

lemma kth_obs_mono: assumes \<open>is_kth_obs \<pi> k i\<close> \<open>is_kth_obs \<pi> l j\<close> \<open>k < l\<close> shows \<open>i < j\<close> proof (rule ccontr)
  assume \<open>\<not> i < j\<close>
  hence \<open>{..<j} \<subseteq> {..<i}\<close> by auto
  hence \<open>obs_ids \<pi> \<inter> {..<j} \<subseteq> obs_ids \<pi> \<inter> {..<i}\<close> by auto
  moreover 
  have \<open>finite (obs_ids \<pi> \<inter> {..<i})\<close> by auto
  ultimately
  have \<open>card (obs_ids \<pi> \<inter> {..<j}) \<le> card (obs_ids \<pi> \<inter> {..<i})\<close> by (metis card_mono)
  thus \<open>False\<close> using assms unfolding is_kth_obs_def by auto
qed

lemma kth_obs_le_iff: assumes \<open>is_kth_obs \<pi> k i\<close> \<open>is_kth_obs \<pi> l j\<close>  shows \<open>k < l \<longleftrightarrow> i < j\<close> by (metis assms kth_obs_unique kth_obs_mono not_less_iff_gr_or_eq)

lemma ret_obs_all_obs: assumes path: \<open>is_path \<pi>\<close> and iki: \<open>is_kth_obs \<pi> k i\<close> and ret: \<open>\<pi> i = return\<close> and kl: \<open>k < l\<close> obtains j where \<open>is_kth_obs \<pi> l j\<close>
proof-
  show \<open>thesis\<close>
  using kl iki ret proof (induction \<open>l - k\<close> arbitrary: \<open>k\<close> \<open>i\<close> rule: less_induct)
    case (less k i)
    note kl = \<open>k < l\<close>
    note iki = \<open>is_kth_obs \<pi> k i\<close>
    note ret = \<open>\<pi> i = return\<close>  
    have card: \<open>card (obs_ids \<pi> \<inter> {..<i}) = k\<close> and att_ret: \<open>att return \<noteq> None\<close>using iki ret unfolding is_kth_obs_def by auto
    have rets: \<open>\<pi> (Suc i) = return\<close> using path ret term_path_stable by auto
    hence attsuc: \<open>att (\<pi> (Suc i)) \<noteq> None\<close> using att_ret by auto
    hence *: \<open>i \<in> obs_ids \<pi>\<close> using att_ret ret unfolding obs_ids_def by auto
    have \<open>{..< Suc i} = insert i {..<i}\<close> by auto
    hence a: \<open>obs_ids \<pi> \<inter> {..< Suc i} = insert i (obs_ids \<pi> \<inter> {..<i})\<close> using * by auto
    have b: \<open>i \<notin> obs_ids \<pi> \<inter> {..<i}\<close> by auto
    have \<open>finite (obs_ids \<pi> \<inter> {..<i})\<close> by auto
    hence \<open>card (obs_ids \<pi> \<inter> {..<Suc i}) = Suc k\<close> by (metis card card_insert_disjoint a b)
    hence iksuc: \<open>is_kth_obs \<pi> (Suc k) (Suc i)\<close> using attsuc unfolding is_kth_obs_def by auto
    have suckl: \<open>Suc k \<le> l\<close> using kl by auto
    note less
    thus \<open>thesis\<close> proof (cases \<open>Suc k < l\<close>) 
      assume skl: \<open>Suc k < l\<close> 
      from less(1)[OF _ skl iksuc rets] skl
      show \<open>thesis\<close> by auto
    next
      assume \<open>\<not> Suc k < l\<close>
      hence \<open>Suc k = l\<close> using suckl by auto
      thus \<open>thesis\<close> using iksuc that by auto
    qed
  qed
qed

lemma no_kth_obs_missing_cs: assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and iki: \<open>is_kth_obs \<pi> k i\<close> and not_in_\<pi>': \<open>\<not>(\<exists>i'. is_kth_obs \<pi>' k i')\<close>  obtains  l j where \<open>is_kth_obs \<pi> l j\<close> \<open>\<not> (\<exists> j'. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close>
proof (rule ccontr)
  assume \<open>\<not> thesis\<close>
  hence all_in_\<pi>': \<open>\<forall> l j. is_kth_obs \<pi> l j \<longrightarrow> (\<exists> j' . cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close> using that by blast
  then obtain i' where csi: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> using assms by blast    
  hence \<open>att(\<pi>' i') \<noteq> None\<close> using iki by (metis is_kth_obs_def last_cs)
  then obtain k' where ik': \<open>is_kth_obs \<pi>' k' i'\<close> by (metis not_none_is_obs)
  hence kk': \<open>k' < k\<close> using not_in_\<pi>' kth_obs_stable by (auto, metis not_less_iff_gr_or_eq)
  show \<open>False\<close> proof (cases \<open>\<pi> i = return\<close>)
    assume \<open>\<pi> i \<noteq> return\<close>
    thus \<open>False\<close> using kk' ik' csi iki proof (induction \<open>k\<close> arbitrary: \<open>i\<close> \<open>i'\<close> \<open>k'\<close> )
      case 0 thus \<open>?case\<close> by simp
    next
      case (Suc k i i' k')      
      then obtain j where ikj: \<open>is_kth_obs \<pi> k j\<close> by (metis kth_obs_stable lessI)
      then obtain j' where csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> using all_in_\<pi>' by blast    
      hence \<open>att(\<pi>' j') \<noteq> None\<close> using ikj by (metis is_kth_obs_def last_cs)
      then obtain k2 where ik2: \<open>is_kth_obs \<pi>' k2 j'\<close> by (metis not_none_is_obs)
      have ji: \<open>j < i\<close> using kth_obs_mono [OF ikj \<open>is_kth_obs \<pi> (Suc k) i\<close>] by auto
      hence nretj: \<open>\<pi> j \<noteq> return\<close> using Suc(2) term_path_stable less_imp_le path(1) by metis    
      have ji': \<open>j' < i'\<close> using cs_order[OF path _ _ nretj, of \<open>j'\<close> \<open>i\<close> \<open>i'\<close>] csj \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close>  ji by auto
      have \<open>k2 \<noteq> k'\<close> using ik2 Suc(4) ji' kth_obs_unique[of \<open>\<pi>'\<close> \<open>k'\<close> \<open>i'\<close> \<open>j'\<close>] by (metis less_irrefl)
      hence k2k': \<open>k2 < k'\<close> using kth_obs_mono[OF \<open>is_kth_obs \<pi>' k' i'\<close> ik2] ji' by (metis not_less_iff_gr_or_eq)
      hence k2k: \<open>k2 < k\<close> using Suc by auto
      from Suc.IH[OF nretj k2k ik2 csj ikj] show \<open>False\<close> .
    qed
  next
    assume \<open>\<pi> i = return\<close>
    hence reti': \<open>\<pi>' i' = return\<close> by (metis csi last_cs)
    from ret_obs_all_obs[OF path(2) ik' reti' kk', of \<open>False\<close>] not_in_\<pi>'
    show \<open>False\<close> by blast
  qed
qed

lemma kth_obs_cs_missing_cs:  assumes path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> and iki: \<open>is_kth_obs \<pi> k i\<close> and iki': \<open>is_kth_obs \<pi>' k i'\<close> and csi: \<open>cs\<^bsup>\<pi>\<^esup> i \<noteq> cs\<^bsup>\<pi>'\<^esup> i'\<close> 
obtains l j where \<open>j \<le> i\<close> \<open>is_kth_obs \<pi> l j\<close> \<open>\<not> (\<exists> j'. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close> | l' j' where \<open>j' \<le> i'\<close> \<open>is_kth_obs \<pi>' l' j'\<close> \<open>\<not> (\<exists> j. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close>
proof (rule ccontr)
  assume nt: \<open>\<not> thesis\<close> 
  show \<open>False\<close> using iki iki' csi that proof (induction \<open>k\<close> arbitrary: \<open>i\<close> \<open>i'\<close> rule: less_induct)
    case (less k i i')
    hence all_in_\<pi>': \<open>\<forall> l j. j\<le>i \<and> is_kth_obs \<pi> l j \<longrightarrow> (\<exists> j' . cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close> 
    and all_in_\<pi>: \<open>\<forall> l' j'. j' \<le> i' \<and> is_kth_obs \<pi>' l' j' \<longrightarrow> (\<exists> j . cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close> by (metis nt) (metis nt less(6))
    obtain j j' where csji: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> i'\<close> and csij: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> j'\<close> using all_in_\<pi> all_in_\<pi>' less by blast 
    then obtain l l' where ilj: \<open>is_kth_obs \<pi> l j\<close> and ilj': \<open>is_kth_obs \<pi>' l' j'\<close> by (metis is_kth_obs_def last_cs less.prems(1,2))
    have lnk: \<open>l \<noteq> k\<close> using ilj csji less(2) less(4) kth_obs_unique by auto
    have lnk': \<open>l' \<noteq> k\<close> using ilj' csij less(3) less(4) kth_obs_unique by auto
    have cseq: \<open>\<forall> l j j'. l < k \<and>  is_kth_obs \<pi> l j \<and> is_kth_obs \<pi>' l j' \<longrightarrow> cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> proof - 
      { fix t p p' assume tk: \<open>t < k\<close> and ikp: \<open>is_kth_obs \<pi> t p\<close> and ikp': \<open>is_kth_obs \<pi>' t p'\<close> 
        hence pi: \<open>p < i\<close> and pi': \<open>p' < i'\<close> by (metis kth_obs_mono less.prems(1)) (metis kth_obs_mono less.prems(2) tk ikp') 
        have *: \<open>\<And>j l. j \<le> p \<Longrightarrow> is_kth_obs \<pi> l j \<Longrightarrow> \<exists>j'. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> using pi all_in_\<pi>' by auto
        have **: \<open>\<And>j' l'. j' \<le> p' \<Longrightarrow> is_kth_obs \<pi>' l' j' \<Longrightarrow> \<exists>j. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> using pi' all_in_\<pi> by auto
        have \<open>cs\<^bsup>\<pi>\<^esup> p = cs\<^bsup>\<pi>'\<^esup> p'\<close> apply(rule ccontr) using less(1)[OF tk ikp ikp'] * ** by blast
      }
      thus \<open>?thesis\<close> by blast
    qed
    have ii'nret: \<open>\<pi> i \<noteq> return \<or> \<pi>' i' \<noteq> return\<close> using less cs_return by auto
    have a: \<open>k < l \<or> k < l'\<close> proof (rule ccontr)
      assume \<open>\<not>(k < l \<or> k < l')\<close> 
      hence *: \<open>l < k\<close> \<open>l' < k\<close> using lnk lnk' by auto
      hence ji: \<open>j < i\<close> and ji': \<open>j' < i'\<close> using ilj ilj' less(2,3) kth_obs_mono by auto      
      show \<open>False\<close> using ii'nret proof
        assume nreti: \<open>\<pi> i \<noteq> return\<close>
        hence nretj': \<open>\<pi>' j' \<noteq> return\<close> using last_cs csij by metis
        show \<open>False\<close> using cs_order[OF path(2,1) csij[symmetric] csji[symmetric] nretj' ji'] ji by simp
      next
        assume nreti': \<open>\<pi>' i' \<noteq> return\<close>
        hence nretj': \<open>\<pi> j \<noteq> return\<close> using last_cs csji by metis
        show \<open>False\<close> using cs_order[OF path csji csij nretj' ji] ji' by simp
      qed
    qed
    have \<open>l < k \<or> l' < k\<close> proof (rule ccontr)
      assume \<open>\<not> (l< k \<or> l' < k)\<close>
      hence \<open>k < l\<close> \<open>k < l'\<close> using lnk lnk' by auto
      hence ji: \<open>i < j\<close> and ji': \<open>i' < j'\<close> using ilj ilj' less(2,3) kth_obs_mono by auto
      show \<open>False\<close> using ii'nret proof
        assume nreti: \<open>\<pi> i \<noteq> return\<close>
        show \<open>False\<close> using cs_order[OF path csij csji nreti ji]  ji' by simp
      next
        assume nreti': \<open>\<pi>' i' \<noteq> return\<close>
        show \<open>False\<close> using cs_order[OF path(2,1) csji[symmetric] csij[symmetric] nreti' ji'] ji by simp
      qed
    qed    
    hence \<open>k < l \<and> l' < k \<or> k < l' \<and> l < k\<close> using a by auto
    thus \<open>False\<close> proof
      assume \<open>k < l \<and> l' < k\<close>
      hence kl: \<open>k < l\<close> and lk': \<open>l' < k\<close> by auto    
      hence ij: \<open>i < j\<close> and ji': \<open>j' < i'\<close> using less(2,3) ilj ilj' kth_obs_mono by auto      
      have nreti: \<open>\<pi> i \<noteq> return\<close> by (metis csji ii'nret ij last_cs path(1) term_path_stable less_imp_le)
      obtain h where ilh: \<open>is_kth_obs \<pi> l' h\<close> using ji' all_in_\<pi> ilj' no_kth_obs_missing_cs path(1) path(2) by (metis kl lk' ilj kth_obs_stable)
      hence \<open>cs\<^bsup>\<pi>\<^esup> h = cs\<^bsup>\<pi>'\<^esup> j'\<close> using cseq lk' ilj' by blast
      hence \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>\<^esup> h\<close> using csij by auto
      hence hi: \<open>h = i\<close> using cs_inj nreti path(1) by metis      
      have \<open>l' = k\<close> using less(2) ilh unfolding hi by (metis is_kth_obs_def)      
      thus \<open>False\<close> using lk' by simp
    next
      assume \<open>k < l' \<and> l < k\<close>
      hence kl': \<open>k < l'\<close> and lk: \<open>l < k\<close> by auto    
      hence ij': \<open>i' < j'\<close> and ji: \<open>j < i\<close> using less(2,3) ilj ilj' kth_obs_mono by auto      
      have nreti': \<open>\<pi>' i' \<noteq> return\<close> by (metis csij ii'nret ij' last_cs path(2) term_path_stable less_imp_le)
      obtain h' where ilh': \<open>is_kth_obs \<pi>' l h'\<close> using all_in_\<pi>' ilj no_kth_obs_missing_cs path(1) path(2) kl' lk ilj' kth_obs_stable by metis
      hence \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> h'\<close> using cseq lk ilj by blast
      hence \<open>cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>'\<^esup> h'\<close> using csji by auto
      hence hi: \<open>h' = i'\<close> using cs_inj nreti' path(2) by metis      
      have \<open>l = k\<close> using less(3) ilh' unfolding hi by (metis is_kth_obs_def)      
      thus \<open>False\<close> using lk by simp
    qed
  qed
qed


subsection \<open>Facts about Data\<close>

lemma reads_restrict1: \<open>\<sigma> \<restriction> (reads n) = \<sigma>' \<restriction> (reads n) \<Longrightarrow> \<forall> x \<in> reads n. \<sigma> x = \<sigma>' x\<close> by (metis restrict_def)

lemma reads_restrict2: \<open>\<forall> x \<in> reads n. \<sigma> x = \<sigma>' x \<Longrightarrow> \<sigma> \<restriction> (reads n) = \<sigma>' \<restriction> (reads n)\<close>  unfolding restrict_def by auto

lemma reads_restrict: \<open>(\<sigma> \<restriction> (reads n) = \<sigma>' \<restriction> (reads n)) = (\<forall> x \<in> reads n. \<sigma> x = \<sigma>' x)\<close> using reads_restrict1 reads_restrict2 by metis

lemma reads_restr_suc: \<open>\<sigma> \<restriction> (reads n) = \<sigma>' \<restriction> (reads n) \<Longrightarrow> suc n \<sigma> = suc n \<sigma>'\<close> by (metis reads_restrict uses_suc)

lemma reads_restr_sem: \<open>\<sigma> \<restriction> (reads n) = \<sigma>' \<restriction> (reads n) \<Longrightarrow> \<forall> v \<in> writes n. sem n \<sigma> v = sem n \<sigma>' v\<close> by (metis reads_restrict1 uses_writes)

lemma reads_obsp: assumes \<open>path \<sigma> k = path \<sigma>' k'\<close> \<open>\<sigma>\<^bsup>k\<^esup> \<restriction> (reads (path \<sigma> k)) = \<sigma>'\<^bsup>k'\<^esup> \<restriction> (reads (path \<sigma> k))\<close> shows \<open>obsp \<sigma> k = obsp \<sigma>' k'\<close> 
  using assms(2) uses_att 
  unfolding obsp_def assms(1) reads_restrict 
  apply (cases \<open>att (path \<sigma>' k')\<close>)  
  by auto

lemma no_writes_unchanged0: assumes \<open>\<forall> l<k. v\<notin> writes(path \<sigma> l)\<close> shows \<open>(\<sigma>\<^bsup>k\<^esup>) v = \<sigma> v\<close> using assms 
proof (induction \<open>k\<close>)
  case 0 thus \<open>?case\<close> by(auto simp add: kth_state_def) 
next
  case (Suc k)
  hence \<open>(\<sigma>\<^bsup>k\<^esup>) v = \<sigma> v\<close> by auto
  moreover 
  have \<open>\<sigma>\<^bsup>Suc k\<^esup>  = snd ( step (path \<sigma> k,\<sigma>\<^bsup>k\<^esup>))\<close> by (metis kth_state_suc)
  hence \<open>\<sigma>\<^bsup>Suc k\<^esup>  = sem (path \<sigma> k) (\<sigma>\<^bsup>k\<^esup>)\<close> by (metis step_suc_sem snd_conv)
  moreover
  have \<open>v \<notin> writes (path \<sigma> k)\<close> using Suc.prems by blast
  ultimately 
  show \<open>?case\<close> using writes by metis
qed

lemma written_read_dd: assumes \<open>is_path \<pi>\<close> \<open>v \<in> reads (\<pi> k) \<close> \<open>v \<in> writes (\<pi> j)\<close> \<open>j<k\<close> obtains l where \<open>k dd\<^bsup>\<pi>,v\<^esup>\<rightarrow> l\<close> 
proof -
  let \<open>?l\<close> = \<open>GREATEST l. l < k \<and> v \<in> writes (\<pi> l)\<close>
  have \<open>?l < k\<close> by (metis (no_types, lifting) GreatestI_ex_nat assms(3) assms(4) less_or_eq_imp_le)
  moreover
  have \<open>v \<in> writes (\<pi> ?l)\<close> by (metis (no_types, lifting) GreatestI_nat assms(3) assms(4) less_or_eq_imp_le) 
  hence \<open>v \<in> reads (\<pi> k) \<inter> writes (\<pi> ?l)\<close> using assms(2) by auto
  moreover
  note is_ddi_def
  have \<open>\<forall> l \<in> {?l<..<k}. v \<notin> writes (\<pi> l)\<close> by (auto, metis (lifting, no_types) Greatest_le_nat le_antisym nat_less_le)
  ultimately 
  have \<open>k dd\<^bsup>\<pi>,v\<^esup>\<rightarrow> ?l\<close> using assms(1) unfolding is_ddi_def by blast
  thus \<open>thesis\<close> using that by simp
qed

lemma no_writes_unchanged: assumes \<open>k \<le> l\<close> \<open>\<forall> j \<in> {k..<l}. v\<notin> writes(path \<sigma> j)\<close> shows \<open>(\<sigma>\<^bsup>l\<^esup>) v = (\<sigma>\<^bsup>k\<^esup>) v\<close> using assms
proof (induction \<open>l - k\<close> arbitrary: \<open>l\<close>)
  case 0 thus \<open>?case\<close> by(auto) 
next
  case (Suc lk l)
  hence kl: \<open>k < l\<close> by auto
  then obtain l' where lsuc: \<open>l = Suc l'\<close> using lessE by blast
  hence \<open>lk = l' - k\<close> using Suc by auto
  moreover 
  have \<open>\<forall> j \<in> {k..<l'}. v \<notin> writes (path \<sigma> j)\<close> using Suc(4) lsuc by auto
  ultimately  
  have \<open>(\<sigma>\<^bsup>l'\<^esup>) v = (\<sigma>\<^bsup>k\<^esup>) v\<close> using Suc(1)[of \<open>l'\<close>] lsuc kl by fastforce
  moreover 
  have \<open>\<sigma>\<^bsup>l\<^esup> = snd ( step (path \<sigma> l',\<sigma>\<^bsup>l'\<^esup>))\<close> by (metis kth_state_suc lsuc)
  hence \<open>\<sigma>\<^bsup>l\<^esup> = sem (path \<sigma> l') (\<sigma>\<^bsup>l'\<^esup>)\<close> by (metis step_suc_sem snd_conv)
  moreover
  have \<open>l' < l\<close> \<open>k \<le> l'\<close> using kl lsuc by auto
  hence \<open>v \<notin> writes (path \<sigma> l')\<close> using Suc.prems(2) by auto
  ultimately 
  show \<open>?case\<close> using writes by metis
qed

lemma ddi_value: assumes \<open>l dd\<^bsup>(path \<sigma>),v\<^esup>\<rightarrow> k\<close> shows \<open>(\<sigma>\<^bsup>l\<^esup>) v = (\<sigma>\<^bsup>Suc k\<^esup> ) v\<close>
using assms no_writes_unchanged[of \<open>Suc k\<close> \<open>l\<close> \<open>v\<close> \<open>\<sigma>\<close>] unfolding is_ddi_def by auto

lemma written_value: assumes \<open>path \<sigma> l = path \<sigma>' l'\<close> \<open>\<sigma>\<^bsup>l\<^esup> \<restriction> reads (path \<sigma> l) = \<sigma>'\<^bsup>l'\<^esup> \<restriction> reads (path \<sigma> l)\<close> \<open>v \<in> writes (path \<sigma> l)\<close> 
shows \<open>(\<sigma>\<^bsup>Suc l\<^esup> ) v = (\<sigma>'\<^bsup>Suc l'\<^esup> ) v\<close> 
by (metis assms reads_restr_sem snd_conv step_suc_sem kth_state_suc) 


subsection \<open>Facts about Contradicting Paths\<close>

lemma obsp_contradict: assumes csk: \<open>cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k'\<close> and obs: \<open>obsp \<sigma> k \<noteq> obsp \<sigma>' k'\<close> shows \<open>(\<sigma>', k') \<cc> (\<sigma>, k)\<close>
proof -
  have pk: \<open>path \<sigma> k = path \<sigma>' k'\<close> using assms last_cs by metis
  hence \<open>\<sigma>\<^bsup>k\<^esup>\<restriction>(reads (path \<sigma> k)) \<noteq> \<sigma>'\<^bsup>k'\<^esup>\<restriction>(reads (path \<sigma> k))\<close> using obs reads_obsp[OF pk] by auto
  thus \<open>(\<sigma>',k') \<cc> (\<sigma>,k)\<close> using contradicts.intros(2)[OF csk[symmetric]] by auto
qed

lemma missing_cs_contradicts: assumes notin: \<open>\<not>(\<exists> k'. cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k')\<close> and converge: \<open>k<n\<close> \<open>cs\<^bsup>path \<sigma>\<^esup> n = cs\<^bsup>path \<sigma>'\<^esup> n'\<close> shows \<open>\<exists> j'. (\<sigma>', j') \<cc> (\<sigma>, k)\<close>
proof -
  let \<open>?\<pi>\<close> = \<open>path \<sigma>\<close>
  let \<open>?\<pi>'\<close> = \<open>path \<sigma>'\<close>
  have init: \<open>?\<pi> 0 = ?\<pi>' 0\<close> unfolding path_def by auto
  have path: \<open>is_path ?\<pi>\<close> \<open>is_path ?\<pi>'\<close> using path_is_path by auto
  obtain j j' where csj: \<open>cs\<^bsup>?\<pi>\<^esup> j = cs\<^bsup>?\<pi>'\<^esup> j'\<close> and cd: \<open>k cd\<^bsup>?\<pi>\<^esup>\<rightarrow>j\<close> and suc: \<open>?\<pi> (Suc j) \<noteq> ?\<pi>' (Suc j')\<close> using converged_cd_diverge[OF path init notin converge] .
  have less: \<open>cs\<^bsup>?\<pi>\<^esup> j \<prec> cs\<^bsup>?\<pi>\<^esup> k\<close> using cd cd_is_cs_less by auto
  have nretj: \<open>?\<pi> j \<noteq> return\<close> by (metis cd is_cdi_def term_path_stable less_imp_le)
  have cs: \<open>?\<pi> \<exclamdown> cs\<^bsup>?\<pi>'\<^esup> j' = j\<close> using csj cs_select_id nretj path_is_path by metis
  have \<open>(\<sigma>',j') \<cc> (\<sigma>,k)\<close> using contradicts.intros(1)[of \<open>?\<pi>'\<close> \<open>j'\<close> \<open>?\<pi>\<close> \<open>k\<close> \<open>\<sigma>\<close> \<open>\<sigma>'\<close>,unfolded cs] less suc csj by metis
  thus \<open>?thesis\<close> by blast
qed

theorem obs_neq_contradicts_term: fixes \<sigma> \<sigma>' defines \<pi>: \<open>\<pi> \<equiv> path \<sigma>\<close> and \<pi>': \<open>\<pi>' \<equiv> path \<sigma>'\<close> assumes ret: \<open>\<pi> n = return\<close> \<open>\<pi>' n' = return\<close> and obsne: \<open>obs \<sigma> \<noteq> obs \<sigma>'\<close> 
shows \<open>\<exists> k k'. ((\<sigma>', k') \<cc> (\<sigma> ,k) \<and> \<pi> k \<in> dom (att)) \<or> ((\<sigma>, k) \<cc> (\<sigma>' ,k') \<and> \<pi>' k' \<in> dom (att))\<close>
proof - 
  have path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> using \<pi> \<pi>' path_is_path by auto
  obtain k1 where neq: \<open>obs \<sigma> k1 \<noteq> obs \<sigma>' k1\<close> using obsne ext[of \<open>obs \<sigma>\<close> \<open>obs \<sigma>'\<close>] by blast  
  hence \<open>(\<exists>k i i'. is_kth_obs \<pi> k i \<and> is_kth_obs \<pi>' k i' \<and> obsp \<sigma> i \<noteq> obsp \<sigma>' i' \<and> cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i') 
  \<or> (\<exists> k i. is_kth_obs \<pi> k i \<and> \<not> (\<exists> i'. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i')) 
  \<or> (\<exists> k i'. is_kth_obs \<pi>' k i' \<and> \<not> (\<exists> i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))\<close>
  proof(cases rule: option_neq_cases)
    case (none2 x)
    have notin\<pi>': \<open>\<not> (\<exists> l. is_kth_obs \<pi>' k1 l)\<close> using none2(2) \<pi>' obs_none_no_kth_obs by auto
    obtain i where in\<pi>: \<open>is_kth_obs \<pi> k1 i\<close> using obs_some_kth_obs[of \<open>\<sigma>\<close> \<open>k1\<close>] none2(1) \<pi> by auto            
    obtain l j where \<open>is_kth_obs \<pi> l j\<close> \<open>\<not> (\<exists> j'. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close> using path in\<pi> notin\<pi>' by (metis no_kth_obs_missing_cs)
    thus \<open>?thesis\<close> by blast
  next
    case (none1 x)
    have notin\<pi>: \<open>\<not> (\<exists> l. is_kth_obs \<pi> k1 l)\<close> using none1(1) \<pi> obs_none_no_kth_obs by auto
    obtain i' where in\<pi>': \<open>is_kth_obs \<pi>' k1 i'\<close> using obs_some_kth_obs[of \<open>\<sigma>'\<close> \<open>k1\<close>] none1(2) \<pi>' by auto            
    obtain l j where \<open>is_kth_obs \<pi>' l j\<close> \<open>\<not> (\<exists> j'. cs\<^bsup>\<pi>\<^esup> j' = cs\<^bsup>\<pi>'\<^esup> j)\<close> using path in\<pi>' notin\<pi> by (metis no_kth_obs_missing_cs)
    thus \<open>?thesis\<close> by blast
  next  
    case (some x y)
    obtain i where in\<pi>: \<open>is_kth_obs \<pi> k1 i\<close> using obs_some_kth_obs[of \<open>\<sigma>\<close> \<open>k1\<close>] some \<pi> by auto
    obtain i' where in\<pi>': \<open>is_kth_obs \<pi>' k1 i'\<close> using obs_some_kth_obs[of \<open>\<sigma>'\<close> \<open>k1\<close>] some \<pi>' by auto
    show \<open>?thesis\<close> proof (cases)
      assume *: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close>
      have \<open>obsp \<sigma> i = obs \<sigma> k1\<close> by (metis obs_def \<pi> in\<pi> kth_obs_unique the_equality)
      moreover
      have \<open>obsp \<sigma>' i' = obs \<sigma>' k1\<close> by (metis obs_def \<pi>' in\<pi>' kth_obs_unique the_equality)
      ultimately
      have \<open>obsp \<sigma> i \<noteq> obsp \<sigma>' i'\<close> using neq by auto
      thus \<open>?thesis\<close> using * in\<pi> in\<pi>' by blast
    next
      assume *: \<open>cs\<^bsup>\<pi>\<^esup> i \<noteq> cs\<^bsup>\<pi>'\<^esup> i'\<close>
      note kth_obs_cs_missing_cs[OF path in\<pi> in\<pi>' *]
      thus \<open>?thesis\<close> by metis
    qed
  qed
  thus \<open>?thesis\<close> proof (cases rule: three_cases)
    case 1
    then obtain k i i' where iki: \<open>is_kth_obs \<pi> k i\<close> \<open>is_kth_obs \<pi>' k i'\<close> and obsne: \<open>obsp \<sigma> i \<noteq> obsp \<sigma>' i'\<close> and csi: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> by auto
    note obsp_contradict[OF csi[unfolded \<pi> \<pi>'] obsne]
    moreover
    have \<open>\<pi> i \<in> dom att\<close> using iki unfolding is_kth_obs_def by auto
    ultimately
    show \<open>?thesis\<close> by blast
  next
    case 2
    then obtain k i where iki: \<open>is_kth_obs \<pi> k i\<close> and notin\<pi>': \<open>\<not> (\<exists>i'. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i')\<close> by auto
    let \<open>?n\<close> = \<open>Suc (max n i)\<close>
    have nn: \<open>n < ?n\<close> by auto
    have iln: \<open>i < ?n\<close> by auto
    have retn: \<open>\<pi> ?n = return\<close> using ret term_path_stable path by auto
    hence \<open>cs\<^bsup>\<pi>\<^esup> ?n = cs\<^bsup>\<pi>'\<^esup> n'\<close> using ret(2) cs_return by auto
    then obtain i' where \<open>(\<sigma>',i') \<cc> (\<sigma>,i)\<close> using missing_cs_contradicts[OF notin\<pi>'[unfolded \<pi> \<pi>'] iln] \<pi> \<pi>' by auto
    moreover
    have \<open>\<pi> i \<in> dom att\<close> using iki is_kth_obs_def by auto
    ultimately
    show \<open>?thesis\<close> by blast
  next
    case 3
    then obtain k i' where iki: \<open>is_kth_obs \<pi>' k i'\<close> and notin\<pi>': \<open>\<not> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i')\<close> by auto
    let \<open>?n\<close> = \<open>Suc (max n' i')\<close>
    have nn: \<open>n' < ?n\<close> by auto
    have iln: \<open>i' < ?n\<close> by auto
    have retn: \<open>\<pi>' ?n = return\<close> using ret term_path_stable path by auto
    hence \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> ?n\<close> using ret(1) cs_return by auto
    then obtain i where \<open>(\<sigma>,i) \<cc> (\<sigma>',i')\<close> using missing_cs_contradicts notin\<pi>' iln \<pi> \<pi>' by metis
    moreover
    have \<open>\<pi>' i' \<in> dom att\<close> using iki is_kth_obs_def by auto
    ultimately
    show \<open>?thesis\<close> by blast
  qed
qed

lemma obs_neq_some_contradicts': fixes \<sigma> \<sigma>' defines \<pi>: \<open>\<pi> \<equiv> path \<sigma>\<close> and \<pi>': \<open>\<pi>' \<equiv> path \<sigma>'\<close> 
assumes obsnecs: \<open>obsp \<sigma> i \<noteq> obsp \<sigma>' i' \<or> cs\<^bsup>\<pi>\<^esup> i \<noteq> cs\<^bsup>\<pi>'\<^esup> i'\<close>
and iki: \<open>is_kth_obs \<pi> k i\<close> and iki': \<open>is_kth_obs \<pi>' k i'\<close>
shows \<open>\<exists> k k'. ((\<sigma>', k') \<cc> (\<sigma> ,k) \<and> \<pi> k \<in> dom att) \<or> ((\<sigma>, k) \<cc> (\<sigma>' ,k') \<and> \<pi>' k' \<in> dom att)\<close>
using obsnecs iki iki' proof (induction \<open>k\<close> arbitrary: \<open>i\<close> \<open>i'\<close> rule: less_induct )
  case (less k i i')  
  note iki = \<open>is_kth_obs \<pi> k i\<close>
  and iki' = \<open>is_kth_obs \<pi>' k i'\<close>
  have domi: \<open>\<pi> i \<in> dom att\<close> by (metis is_kth_obs_def domIff iki)
  have domi': \<open>\<pi>' i' \<in> dom att\<close> by (metis is_kth_obs_def domIff iki')
  note obsnecs = \<open>obsp \<sigma> i \<noteq> obsp \<sigma>' i' \<or> cs\<^bsup>\<pi>\<^esup> i \<noteq> cs\<^bsup>\<pi>'\<^esup> i'\<close>  
  show \<open>?thesis\<close> proof cases
    assume csi: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close>
    hence *: \<open>obsp \<sigma> i \<noteq> obsp \<sigma>' i'\<close> using obsnecs by auto
    note obsp_contradict[OF _ *] csi domi \<pi> \<pi>'
    thus \<open>?thesis\<close> by blast    
  next      
    assume ncsi: \<open>cs\<^bsup>\<pi>\<^esup> i \<noteq> cs\<^bsup>\<pi>'\<^esup> i'\<close>  
    have path: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> using \<pi> \<pi>' path_is_path by auto
    have \<pi>0: \<open>\<pi> 0 = \<pi>' 0\<close> unfolding \<pi> \<pi>' path_def by auto
    note kth_obs_cs_missing_cs[of \<open>\<pi>\<close> \<open>\<pi>'\<close> \<open>k\<close> \<open>i\<close> \<open>i'\<close>] \<pi> \<pi>' path_is_path iki iki' ncsi 
    hence \<open>(\<exists> l j .j \<le> i \<and> is_kth_obs \<pi> l j \<and> \<not> (\<exists> j'. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')) \<or> (\<exists> l' j'. j' \<le> i' \<and> is_kth_obs \<pi>' l' j' \<and> \<not> (\<exists> j. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'))\<close> by metis
    thus \<open>?thesis\<close> proof
      assume \<open>\<exists>l j. j \<le> i \<and> is_kth_obs \<pi> l j \<and> \<not> (\<exists>j'. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close>
      then obtain l j where ji: \<open>j\<le>i\<close> and iobs: \<open>is_kth_obs \<pi> l j\<close> and notin: \<open>\<not> (\<exists>j'. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close> by blast
      have dom: \<open>\<pi> j \<in> dom att\<close> using iobs is_kth_obs_def by auto
      obtain n n' where nj: \<open>n < j\<close> and csn: \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and sucn:  \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close> and cdloop: \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> n \<or> (\<forall> j'> n'. j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n')\<close>
      using missing_cd_or_loop[OF path \<pi>0 notin] by blast
      show \<open>?thesis\<close> using cdloop proof
        assume cdjn: \<open>j cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close>
        hence csnj: \<open>cs\<^bsup>\<pi>'\<^esup> n' \<prec> cs\<^bsup>\<pi>\<^esup> j\<close> using csn by (metis cd_is_cs_less)
        have cssel: \<open>\<pi> (Suc (\<pi> \<exclamdown> cs\<^bsup>\<pi>'\<^esup> n')) = \<pi> (Suc n)\<close> using csn by (metis cdjn cd_not_ret cs_select_id path(1))
        have \<open>(\<sigma>',n') \<cc> (\<sigma>,j)\<close> using csnj apply(rule contradicts.intros(1)) using cssel \<pi> \<pi>' sucn by auto 
        thus \<open>?thesis\<close> using dom by auto
      next
        assume loop: \<open>\<forall> j'>n'. j' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close>
        show \<open>?thesis\<close> proof cases
          assume in': \<open>i' \<le> n'\<close>
          have nreti': \<open>\<pi>' i' \<noteq> return\<close> by( metis le_eq_less_or_eq lessI loop not_le path(2) ret_no_cd term_path_stable)
          show \<open>?thesis\<close> proof cases
            assume \<open>\<exists> \<iota>. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> \<iota>\<close>
            then obtain \<iota> where cs\<iota>: \<open>cs\<^bsup>\<pi>\<^esup> \<iota> = cs\<^bsup>\<pi>'\<^esup> i'\<close> by metis            
            have \<iota>n: \<open>\<iota> \<le> n\<close> using cs_order_le[OF path(2,1) cs\<iota>[symmetric] csn[symmetric] nreti' in'] .
            hence \<iota>i: \<open>\<iota> < i\<close> using nj ji by auto 
            have dom\<iota>: \<open>\<pi> \<iota> \<in> dom att\<close> using domi' cs\<iota> last_cs by metis
            obtain \<kappa> where i\<kappa>\<iota>: \<open>is_kth_obs \<pi> \<kappa> \<iota>\<close> using dom\<iota> by (metis is_kth_obs_def domIff)
            hence \<kappa>k: \<open>\<kappa> < k\<close> using \<iota>i iki by (metis kth_obs_le_iff)
            obtain \<iota>' where i\<kappa>\<iota>': \<open>is_kth_obs \<pi>' \<kappa> \<iota>'\<close> using \<kappa>k iki' by (metis kth_obs_stable)
            have \<open>\<iota>' < i'\<close> using \<kappa>k iki' i\<kappa>\<iota>' by (metis kth_obs_le_iff)
            hence cs\<iota>': \<open>cs\<^bsup>\<pi>\<^esup> \<iota> \<noteq> cs\<^bsup>\<pi>'\<^esup> \<iota>'\<close> unfolding cs\<iota> using cs_inj[OF path(2) nreti', of \<open>\<iota>'\<close>] by blast           
            thus \<open>?thesis\<close> using less(1)[OF \<kappa>k _ i\<kappa>\<iota> i\<kappa>\<iota>'] by auto
          next
            assume notin'': \<open>\<not>(\<exists> \<iota>. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> \<iota>)\<close>
            obtain \<iota> \<iota>' where \<iota>i': \<open>\<iota>' < i'\<close> and cs\<iota>: \<open>cs\<^bsup>\<pi>\<^esup> \<iota> = cs\<^bsup>\<pi>'\<^esup> \<iota>'\<close> and suc\<iota>: \<open>\<pi> (Suc \<iota>) \<noteq> \<pi>' (Suc \<iota>')\<close> and cdloop': \<open>i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> \<iota>' \<or> (\<forall> j>\<iota>. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> \<iota>)\<close>
            using missing_cd_or_loop[OF path(2,1) \<pi>0[symmetric] notin''] by metis
            show \<open>?thesis\<close> using cdloop' proof
              assume cdjn: \<open>i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> \<iota>'\<close>
              hence csnj: \<open>cs\<^bsup>\<pi>\<^esup> \<iota> \<prec> cs\<^bsup>\<pi>'\<^esup> i'\<close> using cs\<iota> by (metis cd_is_cs_less)
              have cssel: \<open>\<pi>' (Suc (\<pi>' \<exclamdown> cs\<^bsup>\<pi>\<^esup> \<iota>)) = \<pi>' (Suc \<iota>')\<close> using cs\<iota> by (metis cdjn cd_not_ret cs_select_id path(2))
              have \<open>(\<sigma>,\<iota>) \<cc> (\<sigma>',i')\<close> using csnj apply(rule contradicts.intros(1)) using cssel \<pi> \<pi>' suc\<iota> by auto 
              thus \<open>?thesis\<close> using domi' by auto
            next
              assume loop': \<open>\<forall> j>\<iota>. j cd\<^bsup>\<pi>\<^esup>\<rightarrow> \<iota>\<close>
              have \<iota>n': \<open>\<iota>' < n'\<close> using in' \<iota>i' by auto
              have nret\<iota>': \<open>\<pi>' \<iota>' \<noteq> return\<close> by (metis cs\<iota> last_cs le_eq_less_or_eq lessI path(1) path(2) suc\<iota> term_path_stable)
              have \<open>\<iota> < n\<close> using cs_order[OF path(2,1) cs\<iota>[symmetric] csn[symmetric] nret\<iota>' \<iota>n'] .
              hence \<open>\<iota> < i\<close> using nj ji by auto
              hence cdi\<iota>: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> \<iota>\<close> using loop' by auto
              hence cs\<iota>i: \<open>cs\<^bsup>\<pi>'\<^esup> \<iota>' \<prec> cs\<^bsup>\<pi>\<^esup> i\<close> using cs\<iota> by (metis cd_is_cs_less)
              have cssel: \<open>\<pi> (Suc (\<pi> \<exclamdown> cs\<^bsup>\<pi>'\<^esup> \<iota>')) = \<pi> (Suc \<iota>)\<close> using cs\<iota> by (metis cdi\<iota> cd_not_ret cs_select_id path(1))
              have \<open>(\<sigma>',\<iota>') \<cc> (\<sigma>,i)\<close> using cs\<iota>i apply(rule contradicts.intros(1)) using cssel \<pi> \<pi>' suc\<iota> by auto 
              thus \<open>?thesis\<close> using domi by auto
            qed
          qed
        next
          assume \<open>\<not> i' \<le> n'\<close>
          hence ni': \<open>n'< i'\<close> by simp
          hence cdin: \<open>i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> using loop by auto
          hence csni: \<open>cs\<^bsup>\<pi>\<^esup> n \<prec> cs\<^bsup>\<pi>'\<^esup> i'\<close> using csn by (metis cd_is_cs_less)
          have cssel: \<open>\<pi>' (Suc (\<pi>' \<exclamdown> cs\<^bsup>\<pi>\<^esup> n)) = \<pi>' (Suc n')\<close> using csn by (metis cdin cd_not_ret cs_select_id path(2))
          have \<open>(\<sigma>,n) \<cc> (\<sigma>',i')\<close> using csni apply(rule contradicts.intros(1)) using cssel \<pi> \<pi>' sucn by auto 
          thus \<open>?thesis\<close> using domi' by auto
        qed
      qed
    next
      \<comment> \<open>Symmetric case as above, indices might be messy.\<close>
      assume \<open>\<exists>l j. j \<le> i' \<and> is_kth_obs \<pi>' l j \<and> \<not> (\<exists>j'. cs\<^bsup>\<pi>\<^esup> j' = cs\<^bsup>\<pi>'\<^esup> j)\<close>
      then obtain l j where ji': \<open>j\<le>i'\<close> and iobs: \<open>is_kth_obs \<pi>' l j\<close> and notin: \<open>\<not> (\<exists>j'. cs\<^bsup>\<pi>'\<^esup> j = cs\<^bsup>\<pi>\<^esup> j')\<close> by metis
      have dom: \<open>\<pi>' j \<in> dom att\<close> using iobs is_kth_obs_def by auto
      obtain n n' where nj: \<open>n < j\<close> and csn: \<open>cs\<^bsup>\<pi>'\<^esup> n = cs\<^bsup>\<pi>\<^esup> n'\<close> and sucn:  \<open>\<pi>' (Suc n) \<noteq> \<pi> (Suc n')\<close> and cdloop: \<open>j cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n \<or> (\<forall> j'> n'. j' cd\<^bsup>\<pi>\<^esup>\<rightarrow> n')\<close>
      using missing_cd_or_loop[OF path(2,1) \<pi>0[symmetric] ] notin by metis
      show \<open>?thesis\<close> using cdloop proof
        assume cdjn: \<open>j cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n\<close>
        hence csnj: \<open>cs\<^bsup>\<pi>\<^esup> n' \<prec> cs\<^bsup>\<pi>'\<^esup> j\<close> using csn by (metis cd_is_cs_less)
        have cssel: \<open>\<pi>' (Suc (\<pi>' \<exclamdown> cs\<^bsup>\<pi>\<^esup> n')) = \<pi>' (Suc n)\<close> using csn by (metis cdjn cd_not_ret cs_select_id path(2))
        have \<open>(\<sigma>,n') \<cc> (\<sigma>',j)\<close> using csnj apply(rule contradicts.intros(1)) using cssel \<pi>' \<pi> sucn by auto 
        thus \<open>?thesis\<close> using dom by auto
      next
        assume loop: \<open>\<forall> j'>n'. j' cd\<^bsup>\<pi>\<^esup>\<rightarrow> n'\<close>
        show \<open>?thesis\<close> proof cases
          assume in': \<open>i \<le> n'\<close>
          have nreti: \<open>\<pi> i \<noteq> return\<close> by (metis le_eq_less_or_eq lessI loop not_le path(1) ret_no_cd term_path_stable)
          show \<open>?thesis\<close> proof cases
            assume \<open>\<exists> \<iota>. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> \<iota>\<close>
            then obtain \<iota> where cs\<iota>: \<open>cs\<^bsup>\<pi>'\<^esup> \<iota> = cs\<^bsup>\<pi>\<^esup> i\<close> by metis            
            have \<iota>n: \<open>\<iota> \<le> n\<close> using cs_order_le[OF path cs\<iota>[symmetric] csn[symmetric] nreti in'] .
            hence \<iota>i': \<open>\<iota> < i'\<close> using nj ji' by auto 
            have dom\<iota>: \<open>\<pi>' \<iota> \<in> dom att\<close> using domi cs\<iota> last_cs by metis
            obtain \<kappa> where i\<kappa>\<iota>: \<open>is_kth_obs \<pi>' \<kappa> \<iota>\<close> using dom\<iota> by (metis is_kth_obs_def domIff)
            hence \<kappa>k: \<open>\<kappa> < k\<close> using \<iota>i' iki' by (metis kth_obs_le_iff)
            obtain \<iota>' where i\<kappa>\<iota>': \<open>is_kth_obs \<pi> \<kappa> \<iota>'\<close> using \<kappa>k iki by (metis kth_obs_stable)
            have \<open>\<iota>' < i\<close> using \<kappa>k iki i\<kappa>\<iota>' by (metis kth_obs_le_iff)
            hence cs\<iota>': \<open>cs\<^bsup>\<pi>'\<^esup> \<iota> \<noteq> cs\<^bsup>\<pi>\<^esup> \<iota>'\<close> unfolding cs\<iota> using cs_inj[OF path(1) nreti, of \<open>\<iota>'\<close>] by blast           
            thus \<open>?thesis\<close> using less(1)[OF \<kappa>k _ i\<kappa>\<iota>' i\<kappa>\<iota>] by auto
          next
            assume notin'': \<open>\<not>(\<exists> \<iota>. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> \<iota>)\<close>
            obtain \<iota> \<iota>' where \<iota>i: \<open>\<iota>' < i\<close> and cs\<iota>: \<open>cs\<^bsup>\<pi>'\<^esup> \<iota> = cs\<^bsup>\<pi>\<^esup> \<iota>'\<close> and suc\<iota>: \<open>\<pi>' (Suc \<iota>) \<noteq> \<pi> (Suc \<iota>')\<close> and cdloop': \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> \<iota>' \<or> (\<forall> j>\<iota>. j cd\<^bsup>\<pi>'\<^esup>\<rightarrow> \<iota>)\<close>
            using missing_cd_or_loop[OF path \<pi>0 notin''] by metis
            show \<open>?thesis\<close> using cdloop' proof
              assume cdjn: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> \<iota>'\<close>
              hence csnj: \<open>cs\<^bsup>\<pi>'\<^esup> \<iota> \<prec> cs\<^bsup>\<pi>\<^esup> i\<close> using cs\<iota> by (metis cd_is_cs_less)
              have cssel: \<open>\<pi> (Suc (\<pi> \<exclamdown> cs\<^bsup>\<pi>'\<^esup> \<iota>)) = \<pi> (Suc \<iota>')\<close> using cs\<iota> by (metis cdjn cd_not_ret cs_select_id path(1))
              have \<open>(\<sigma>',\<iota>) \<cc> (\<sigma>,i)\<close> using csnj apply(rule contradicts.intros(1)) using cssel \<pi>' \<pi> suc\<iota> by auto 
              thus \<open>?thesis\<close> using domi by auto
            next
              assume loop': \<open>\<forall> j>\<iota>. j cd\<^bsup>\<pi>'\<^esup>\<rightarrow> \<iota>\<close>
              have \<iota>n': \<open>\<iota>' < n'\<close> using in' \<iota>i by auto
              have nret\<iota>': \<open>\<pi> \<iota>' \<noteq> return\<close> by (metis cs\<iota> last_cs le_eq_less_or_eq lessI path(1) path(2) suc\<iota> term_path_stable)
              have \<open>\<iota> < n\<close> using cs_order[OF path cs\<iota>[symmetric] csn[symmetric] nret\<iota>' \<iota>n'] .
              hence \<open>\<iota> < i'\<close> using nj ji' by auto
              hence cdi\<iota>: \<open>i' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> \<iota>\<close> using loop' by auto
              hence cs\<iota>i': \<open>cs\<^bsup>\<pi>\<^esup> \<iota>' \<prec> cs\<^bsup>\<pi>'\<^esup> i'\<close> using cs\<iota> by (metis cd_is_cs_less)
              have cssel: \<open>\<pi>' (Suc (\<pi>' \<exclamdown> cs\<^bsup>\<pi>\<^esup> \<iota>')) = \<pi>' (Suc \<iota>)\<close> using cs\<iota> by (metis cdi\<iota> cd_not_ret cs_select_id path(2))
              have \<open>(\<sigma>,\<iota>') \<cc> (\<sigma>',i')\<close> using cs\<iota>i' apply(rule contradicts.intros(1)) using cssel \<pi>' \<pi> suc\<iota> by auto 
              thus \<open>?thesis\<close> using domi' by auto
            qed
          qed
        next
          assume \<open>\<not> i \<le> n'\<close>
          hence ni: \<open>n'< i\<close> by simp
          hence cdin: \<open>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> n'\<close> using loop by auto
          hence csni': \<open>cs\<^bsup>\<pi>'\<^esup> n \<prec> cs\<^bsup>\<pi>\<^esup> i\<close> using csn by (metis cd_is_cs_less)
          have cssel: \<open>\<pi> (Suc (\<pi> \<exclamdown> cs\<^bsup>\<pi>'\<^esup> n)) = \<pi> (Suc n')\<close> using csn by (metis cdin cd_not_ret cs_select_id path(1))
          have \<open>(\<sigma>',n) \<cc> (\<sigma>,i)\<close> using csni' apply(rule contradicts.intros(1)) using cssel \<pi>' \<pi> sucn by auto 
          thus \<open>?thesis\<close> using domi by auto
        qed
      qed
    qed
  qed
qed

theorem obs_neq_some_contradicts: fixes \<sigma> \<sigma>' defines \<pi>: \<open>\<pi> \<equiv> path \<sigma>\<close> and \<pi>': \<open>\<pi>' \<equiv> path \<sigma>'\<close> 
assumes obsne: \<open>obs \<sigma> k \<noteq> obs \<sigma>' k\<close> and not_none: \<open>obs \<sigma> k \<noteq> None\<close> \<open>obs \<sigma>' k \<noteq> None\<close> 
shows \<open>\<exists> k k'. ((\<sigma>', k') \<cc> (\<sigma> ,k) \<and> \<pi> k \<in> dom att) \<or> ((\<sigma>, k) \<cc> (\<sigma>' ,k') \<and> \<pi>' k' \<in> dom att)\<close>
proof -
  obtain i where iki: \<open>is_kth_obs \<pi> k i\<close> using not_none(1) by (metis \<pi> obs_some_kth_obs)
  obtain i' where iki': \<open>is_kth_obs \<pi>' k i'\<close> using not_none(2) by (metis \<pi>' obs_some_kth_obs)
  have \<open>obsp \<sigma> i = obs \<sigma> k\<close> by (metis \<pi> iki kth_obs_unique obs_def the_equality)
  moreover
  have \<open>obsp \<sigma>' i' = obs \<sigma>' k\<close> by (metis \<pi>' iki' kth_obs_unique obs_def the_equality)
  ultimately
  have obspne: \<open>obsp \<sigma> i \<noteq> obsp \<sigma>' i'\<close> using obsne by auto
  show \<open>?thesis\<close> using obs_neq_some_contradicts'[OF _ iki[unfolded \<pi>] iki'[unfolded \<pi>']] using obspne \<pi> \<pi>' by metis
qed

theorem obs_neq_ret_contradicts: fixes \<sigma> \<sigma>' defines \<pi>: \<open>\<pi> \<equiv> path \<sigma>\<close> and \<pi>': \<open>\<pi>' \<equiv> path \<sigma>'\<close> 
assumes ret: \<open>\<pi> n = return\<close> and obsne: \<open>obs \<sigma>' i \<noteq> obs \<sigma> i\<close> and obs:\<open>obs \<sigma>' i \<noteq> None\<close>
shows \<open>\<exists> k k'. ((\<sigma>', k') \<cc> (\<sigma> ,k) \<and> \<pi> k \<in> dom (att)) \<or> ((\<sigma>, k) \<cc> (\<sigma>' ,k') \<and> \<pi>' k' \<in> dom (att))\<close>
proof (cases \<open>\<exists> j k'. is_kth_obs \<pi>' j k' \<and> (\<nexists> k. cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k')\<close>)
  case True
  obtain l k' where jk': \<open>is_kth_obs \<pi>' l k'\<close> and unmatched: \<open>(\<nexists> k. cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k')\<close> using True by blast
  have \<pi>0: \<open>\<pi> 0 = \<pi>' 0\<close> using \<pi> \<pi>' path0 by auto
  obtain j j' where csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j'\<close> and cd: \<open>k' cd\<^bsup>\<pi>'\<^esup>\<rightarrow>j'\<close> and suc: \<open>\<pi> (Suc j) \<noteq> \<pi>' (Suc j')\<close>
    using converged_cd_diverge_return[of \<open>\<pi>'\<close> \<open>\<pi>\<close> \<open>k'\<close> \<open>n\<close>] ret unmatched path_is_path \<pi> \<pi>' \<pi>0 by metis 
  hence *: \<open>(\<sigma>, j) \<cc> (\<sigma>' ,k')\<close> using contradicts.intros(1)[of \<open>\<pi>\<close> \<open>j\<close> \<open>\<pi>'\<close> \<open>k'\<close> \<open>\<sigma>'\<close> \<open>\<sigma>\<close>, unfolded csj] \<pi> \<pi>'
    using cd_is_cs_less cd_not_ret cs_select_id by auto 
  have \<open>\<pi>' k' \<in> dom(att)\<close> using jk' by (meson domIff is_kth_obs_def) 
  thus \<open>?thesis\<close> using * by blast
next
  case False
  hence *: \<open>\<And> j k'. is_kth_obs \<pi>' j k' \<Longrightarrow> \<exists> k. cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> by auto
  obtain k' where k': \<open>is_kth_obs \<pi>' i k'\<close> using obs \<pi>' obs_some_kth_obs by blast
  obtain l where \<open>is_kth_obs \<pi> i l\<close> using * \<pi> \<pi>' k' no_kth_obs_missing_cs path_is_path by metis
  thus \<open>?thesis\<close> using \<pi> \<pi>' obs obs_neq_some_contradicts obs_none_no_kth_obs obsne by metis
qed


subsection \<open>Facts about Critical Observable Paths\<close>

lemma contradicting_in_cp: assumes leq:\<open>\<sigma> =\<^sub>L \<sigma>'\<close> and cseq: \<open>cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k'\<close> 
and readv: \<open>v\<in>reads(path \<sigma> k)\<close> and vneq: \<open>(\<sigma>\<^bsup>k\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'\<^esup>) v\<close> shows \<open>((\<sigma>,k),(\<sigma>',k')) \<in> cp\<close>
  using cseq readv vneq proof(induction \<open>k+k'\<close> arbitrary: \<open>k\<close> \<open>k'\<close> \<open>v\<close> rule: less_induct)
  fix k k' v     
  assume csk: \<open>cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k'\<close>
  assume vread: \<open>v \<in> reads (path \<sigma> k)\<close>
  assume vneq: \<open>(\<sigma>\<^bsup>k\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'\<^esup>) v\<close>
  assume IH: \<open>\<And>ka k'a v. ka + k'a < k + k' \<Longrightarrow> cs\<^bsup>path \<sigma>\<^esup> ka = cs\<^bsup>path \<sigma>'\<^esup> k'a \<Longrightarrow> v \<in> reads (path \<sigma> ka) \<Longrightarrow> (\<sigma>\<^bsup>ka\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'a\<^esup>) v \<Longrightarrow> ((\<sigma>, ka), \<sigma>', k'a) \<in> cp\<close> 
  
  define \<pi> where  \<open>\<pi> \<equiv> path \<sigma>\<close> 
  define \<pi>' where \<open>\<pi>' \<equiv> path \<sigma>'\<close> 
  have path: \<open>\<pi> = path \<sigma>\<close> \<open>\<pi>' = path \<sigma>'\<close> using \<pi>_def \<pi>'_def path_is_path by auto  
  have ip: \<open>is_path \<pi>\<close> \<open>is_path \<pi>'\<close> using path path_is_path by auto
            
  have \<pi>0: \<open>\<pi>' 0 = \<pi> 0\<close> unfolding path path_def by auto
  have vread': \<open>v \<in> reads (path \<sigma>' k')\<close> using csk vread by (metis last_cs)
  have cseq: \<open>cs\<^bsup>\<pi>'\<^esup> k' = cs\<^bsup>\<pi>\<^esup> k\<close> using csk path by simp
  
  show \<open>((\<sigma>, k), \<sigma>', k') \<in> cp\<close> proof cases
    assume vnw: \<open>\<forall> l < k. v\<notin>writes (\<pi> l)\<close>
    hence \<sigma>v: \<open>(\<sigma>\<^bsup>k\<^esup>) v = \<sigma> v\<close> by (metis no_writes_unchanged0 path(1))
    show \<open>?thesis\<close> proof cases
      assume vnw': \<open>\<forall> l < k'. v\<notin>writes (\<pi>' l)\<close>
      hence \<sigma>v': \<open>(\<sigma>'\<^bsup>k'\<^esup>) v = \<sigma>' v\<close> by (metis no_writes_unchanged0 path(2))
      with \<sigma>v vneq have \<open>\<sigma> v \<noteq> \<sigma>' v\<close> by auto
      hence vhigh: \<open>v \<in> hvars\<close> using leq unfolding loweq_def restrict_def by (auto,metis)
      thus \<open>?thesis\<close> using cp.intros(1)[OF leq csk vread vneq] vnw vnw' path by simp
    next
      assume \<open>\<not>(\<forall> l < k'. v\<notin>writes (\<pi>' l))\<close>
      then obtain l' where kddl': \<open>k' dd\<^bsup>\<pi>',v\<^esup>\<rightarrow> l'\<close> using path(2) path_is_path written_read_dd vread' by blast
      hence lv': \<open>v \<in> writes (\<pi>' l')\<close> unfolding is_ddi_def by auto
      have lk': \<open>l' < k'\<close> by (metis is_ddi_def kddl')
      have nret: \<open>\<pi>' l' \<noteq> return\<close> using lv' writes_return by auto
      
      have notin\<pi>: \<open>\<not> (\<exists>l. cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<pi>\<^esup> l)\<close> proof
        assume \<open>\<exists>l. cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<pi>\<^esup> l\<close>
        then guess l ..
        note csl = \<open>cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<pi>\<^esup> l\<close>
        have lk: \<open>l < k\<close> using lk' cseq ip cs_order[of \<open>\<pi>'\<close> \<open>\<pi>\<close> \<open>l'\<close> \<open>l\<close> \<open>k'\<close> \<open>k\<close>] csl nret path by force
                  
        have \<open>v \<in> writes (\<pi> l)\<close> using csl lv' last_cs by metis
        thus \<open>False\<close> using lk vnw by blast
      qed

      from converged_cd_diverge[OF ip(2,1) \<pi>0 notin\<pi> lk' cseq]
      obtain i i' where  csi: \<open>cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i\<close> and lcdi: \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> i'\<close>  and div: \<open>\<pi>' (Suc i') \<noteq> \<pi> (Suc i)\<close> .
      
      have 1: \<open>\<pi> (Suc i) = suc (\<pi> i) (\<sigma>\<^bsup>i\<^esup>)\<close> by (metis step_suc_sem fst_conv path(1) path_suc)
      have 2: \<open>\<pi>' (Suc i') = suc (\<pi>' i') (\<sigma>'\<^bsup>i'\<^esup>)\<close> by (metis step_suc_sem fst_conv path(2) path_suc)
      have 3: \<open>\<pi>' i' = \<pi> i\<close> using csi last_cs by metis
      have nreads: \<open>\<sigma>\<^bsup>i\<^esup> \<restriction> reads (\<pi> i) \<noteq> \<sigma>'\<^bsup>i'\<^esup> \<restriction> reads (\<pi> i)\<close> by (metis 1 2 3 div reads_restr_suc)
      then obtain v' where v'read: \<open>v'\<in> reads(path \<sigma> i)\<close> \<open>(\<sigma>\<^bsup>i\<^esup>) v' \<noteq> (\<sigma>'\<^bsup>i'\<^esup>) v'\<close> unfolding path by (metis reads_restrict)
      
      have nreti: \<open>\<pi>' i' \<noteq> return\<close> by (metis csi div ip(1) ip(2) last_cs lessI term_path_stable less_imp_le)
      have ik': \<open>i' < k'\<close> using lcdi lk' is_cdi_def by auto            
      have ik: \<open>i < k\<close> using cs_order[OF ip(2,1) csi cseq nreti ik'] .
      
      have cpi: \<open>((\<sigma>, i), (\<sigma>', i')) \<in> cp\<close> using IH[of \<open>i\<close> \<open>i'\<close>] v'read csi ik ik' path by auto 
      hence cpi': \<open>((\<sigma>', i'), (\<sigma>, i)) \<in> cp\<close> using cp.intros(4) by blast
      
      have nwvi: \<open>\<forall>j'\<in>{LEAST i'. i < i' \<and> (\<exists>i. cs\<^bsup>path \<sigma>'\<^esup> i = cs\<^bsup>path \<sigma>\<^esup> i')..<k}. v \<notin> writes (path \<sigma> j')\<close> using vnw[unfolded path] 
        by (metis (poly_guards_query) atLeastLessThan_iff)
      
      from cp.intros(3)[OF cpi' kddl'[unfolded path] lcdi[unfolded path] csk[symmetric] div[unfolded path] vneq[symmetric] nwvi] 
      
      show \<open>?thesis\<close> using cp.intros(4) by simp 
    qed
  next
    assume wv: \<open>\<not> (\<forall> l<k. v \<notin> writes (\<pi> l))\<close> 
    then obtain l where kddl: \<open>k dd\<^bsup>\<pi>,v\<^esup>\<rightarrow> l\<close> using path(1) path_is_path written_read_dd vread by blast
    hence lv: \<open>v \<in> writes (\<pi> l)\<close> unfolding is_ddi_def by auto
    have lk: \<open>l < k\<close> by (metis is_ddi_def kddl)
    have nret: \<open>\<pi> l \<noteq> return\<close> using lv writes_return by auto
    have nwb: \<open>\<forall> i \<in> {Suc l..< k}. v\<notin>writes(\<pi> i)\<close> using kddl unfolding is_ddi_def by auto
    have \<sigma>vk: \<open>(\<sigma>\<^bsup>k\<^esup>) v = (\<sigma>\<^bsup>Suc l\<^esup> ) v\<close> using kddl ddi_value path(1) by auto

    show \<open>?thesis\<close> proof cases
      assume vnw': \<open>\<forall> l < k'. v\<notin>writes (\<pi>' l)\<close>
      hence \<sigma>v': \<open>(\<sigma>'\<^bsup>k'\<^esup>) v = \<sigma>' v\<close> by (metis no_writes_unchanged0 path(2))

      have notin\<pi>': \<open>\<not> (\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l')\<close> proof
        assume \<open>\<exists>l'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close>
        then guess l' ..
        note csl = \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close>
        have lk: \<open>l' < k'\<close> using lk cseq ip cs_order[of \<open>\<pi>\<close> \<open>\<pi>'\<close> \<open>l\<close> \<open>l'\<close> \<open>k\<close> \<open>k'\<close>] csl nret by metis
                  
        have \<open>v \<in> writes (\<pi>' l')\<close> using csl lv last_cs by metis
        thus \<open>False\<close> using lk vnw' by blast
      qed

      from converged_cd_diverge[OF ip(1,2) \<pi>0[symmetric] notin\<pi>' lk cseq[symmetric]]
      obtain i i' where  csi: \<open>cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i\<close> and lcdi: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> i\<close>  and div: \<open>\<pi> (Suc i) \<noteq> \<pi>' (Suc i')\<close> by metis
      
      have 1: \<open>\<pi> (Suc i) = suc (\<pi> i) (\<sigma>\<^bsup>i\<^esup>)\<close> by (metis step_suc_sem fst_conv path(1) path_suc)
      have 2: \<open>\<pi>' (Suc i') = suc (\<pi>' i') (\<sigma>'\<^bsup>i'\<^esup>)\<close> by (metis step_suc_sem fst_conv path(2) path_suc)
      have 3: \<open>\<pi>' i' = \<pi> i\<close> using csi last_cs by metis
      have nreads: \<open>\<sigma>\<^bsup>i\<^esup> \<restriction> reads (\<pi> i) \<noteq> \<sigma>'\<^bsup>i'\<^esup> \<restriction> reads (\<pi> i)\<close> by (metis 1 2 3 div reads_restr_suc)
      have contri: \<open>(\<sigma>',i') \<cc> (\<sigma>,i)\<close> using contradicts.intros(2)[OF csi path nreads] .
      
      have nreti: \<open>\<pi> i \<noteq> return\<close> by (metis csi div ip(1) ip(2) last_cs lessI term_path_stable less_imp_le)
      have ik: \<open>i < k\<close> using lcdi lk is_cdi_def by auto            
      have ik': \<open>i' < k'\<close> using cs_order[OF ip(1,2) csi[symmetric] cseq[symmetric] nreti ik] .
      have nreads: \<open>\<sigma>\<^bsup>i\<^esup> \<restriction> reads (\<pi> i) \<noteq> \<sigma>'\<^bsup>i'\<^esup> \<restriction> reads (\<pi> i)\<close> by (metis 1 2 3 div reads_restr_suc)
      then obtain v' where v'read: \<open>v'\<in> reads(path \<sigma> i)\<close> \<open>(\<sigma>\<^bsup>i\<^esup>) v' \<noteq> (\<sigma>'\<^bsup>i'\<^esup>) v'\<close> unfolding path by (metis reads_restrict)
      
      
      have cpi: \<open>((\<sigma>, i), (\<sigma>', i')) \<in> cp\<close> using IH[of \<open>i\<close> \<open>i'\<close>] v'read csi ik ik' path by auto 
      hence cpi': \<open>((\<sigma>', i'), (\<sigma>, i)) \<in> cp\<close> using cp.intros(4) by blast
      
      have vnwi: \<open>\<forall>j'\<in>{LEAST i'a. i' < i'a \<and> (\<exists>i. cs\<^bsup>path \<sigma>\<^esup> i = cs\<^bsup>path \<sigma>'\<^esup> i'a)..<k'}. v \<notin> writes (path \<sigma>' j')\<close> using vnw'[unfolded path]
        by (metis (poly_guards_query) atLeastLessThan_iff)
        
      from cp.intros(3)[OF cpi kddl[unfolded path] lcdi[unfolded path] csk div[unfolded path] vneq vnwi]   
      
      show \<open>?thesis\<close> using cp.intros(4) by simp
    next
      assume \<open>\<not> (\<forall> l<k'. v \<notin> writes (\<pi>' l))\<close>
      then obtain l' where kddl': \<open>k' dd\<^bsup>\<pi>',v\<^esup>\<rightarrow> l'\<close> using path(2) path_is_path written_read_dd vread' by blast
      hence lv': \<open>v \<in> writes (\<pi>' l')\<close> unfolding is_ddi_def by auto
      have lk': \<open>l' < k'\<close> by (metis is_ddi_def kddl')            
      have nretl': \<open>\<pi>' l' \<noteq> return\<close> using lv' writes_return by auto
      have nwb': \<open>\<forall> i' \<in> {Suc l'..< k'}. v\<notin>writes(\<pi>' i')\<close> using kddl' unfolding is_ddi_def by auto
      have \<sigma>vk': \<open>(\<sigma>'\<^bsup>k'\<^esup>) v = (\<sigma>'\<^bsup>Suc l'\<^esup> ) v\<close> using kddl' ddi_value path(2) by auto

      show \<open>?thesis\<close> proof cases 
        assume csl: \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> l'\<close>
        hence \<pi>l: \<open>\<pi> l = \<pi>' l'\<close> by (metis last_cs)
        have \<sigma>vls: \<open>(\<sigma>\<^bsup>Suc l\<^esup> ) v \<noteq> (\<sigma>'\<^bsup>Suc l'\<^esup> ) v\<close> by (metis \<sigma>vk \<sigma>vk' vneq)
        have r\<sigma>: \<open>\<sigma>\<^bsup>l\<^esup> \<restriction> reads (\<pi> l) \<noteq> \<sigma>'\<^bsup>l'\<^esup> \<restriction> reads (\<pi> l)\<close> using path \<pi>l \<sigma>vls written_value lv by blast
        then obtain v' where v'read: \<open>v'\<in> reads(path \<sigma> l)\<close> \<open>(\<sigma>\<^bsup>l\<^esup>) v' \<noteq> (\<sigma>'\<^bsup>l'\<^esup>) v'\<close> unfolding path by (metis reads_restrict)
      
      
        have cpl: \<open>((\<sigma>, l), (\<sigma>', l')) \<in> cp\<close> using IH[of \<open>l\<close> \<open>l'\<close>] v'read csl lk lk' path by auto 
        show \<open>((\<sigma>, k), (\<sigma>', k')) \<in> cp\<close> using cp.intros(2)[OF cpl kddl[unfolded path] kddl'[unfolded path] csk vneq] .        
      next
        assume csl: \<open>cs\<^bsup>\<pi>\<^esup> l \<noteq> cs\<^bsup>\<pi>'\<^esup> l'\<close>
        show \<open>?thesis\<close> proof cases
          assume \<open>\<exists> i'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> i'\<close>
          then obtain i' where csli': \<open>cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> i'\<close> by blast
          have ilne': \<open>i' \<noteq> l'\<close> using csl csli' by auto
          have ij': \<open>i' < k'\<close> using cs_order[OF ip csli' cseq[symmetric] nret lk] .
          have iv': \<open>v \<in> writes(\<pi>' i')\<close> using lv csli' last_cs by metis
          have il': \<open>i' < l'\<close> using kddl' ilne' ij' iv' unfolding is_ddi_def by auto
          have nreti': \<open>\<pi>' i' \<noteq> return\<close> using csli' nret last_cs by metis

          have l'notin\<pi>: \<open>\<not>(\<exists>i. cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<pi>\<^esup> i )\<close> proof
            assume \<open>\<exists>i. cs\<^bsup>\<pi>'\<^esup> l' = cs\<^bsup>\<pi>\<^esup> i\<close>
            then obtain i where csil: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> l'\<close> by metis
            have ik: \<open>i < k\<close> using cs_order[OF ip(2,1) csil[symmetric] cseq nretl' lk'] .
            have li: \<open>l < i\<close> using cs_order[OF ip(2,1) csli'[symmetric] csil[symmetric] nreti' il'] .
            have iv: \<open>v \<in> writes(\<pi> i)\<close> using lv' csil last_cs by metis
            show \<open>False\<close> using kddl ik li iv is_ddi_def by auto
          qed
          
          obtain n n' where csn: \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and lcdn': \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close>  and sucn: \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close> and in': \<open>i' \<le> n'\<close>
          using converged_cd_diverge_cs [OF ip(2,1) csli'[symmetric] il' l'notin\<pi> lk' cseq] by metis 
          
          \<comment> \<open>Can apply the IH to n and n'\<close>
          
          have 1: \<open>\<pi> (Suc n) = suc (\<pi> n) (\<sigma>\<^bsup>n\<^esup>)\<close> by (metis step_suc_sem fst_conv path(1) path_suc)
          have 2: \<open>\<pi>' (Suc n') = suc (\<pi>' n') (\<sigma>'\<^bsup>n'\<^esup>)\<close> by (metis step_suc_sem fst_conv path(2) path_suc)
          have 3: \<open>\<pi>' n' = \<pi> n\<close> using csn last_cs by metis
          have nreads: \<open>\<sigma>\<^bsup>n\<^esup> \<restriction> reads (\<pi> n) \<noteq> \<sigma>'\<^bsup>n'\<^esup> \<restriction> reads (\<pi> n)\<close> by (metis 1 2 3 sucn reads_restr_suc)
          then obtain v' where v'read: \<open>v'\<in>reads (path \<sigma> n)\<close> \<open>(\<sigma>\<^bsup>n\<^esup>) v' \<noteq> (\<sigma>'\<^bsup>n'\<^esup>) v'\<close> by (metis path(1) reads_restrict)
          moreover
          have nl': \<open>n' < l'\<close> using lcdn' is_cdi_def by auto
          have nk': \<open>n' < k'\<close> using nl' lk' by simp
          have nretn': \<open>\<pi>' n' \<noteq> return\<close> by (metis ip(2) nl' nretl' term_path_stable less_imp_le)
          have nk: \<open>n < k\<close> using cs_order[OF ip(2,1) csn[symmetric] cseq nretn' nk'] .
          hence lenn: \<open>n+n' < k+k'\<close> using nk' by auto
          ultimately  
          have \<open>((\<sigma>, n), (\<sigma>', n')) \<in> cp\<close> using IH csn path by auto
          hence ncp: \<open>((\<sigma>', n'), (\<sigma>, n)) \<in> cp\<close> using cp.intros(4) by auto
          
          have nles: \<open>n < (LEAST i'. n < i' \<and> (\<exists>i. cs\<^bsup>\<pi>'\<^esup> i = cs\<^bsup>\<pi>\<^esup> i'))\<close> (is \<open>_ < (LEAST i. ?P i)\<close>) using nk cseq LeastI[of \<open>?P\<close> \<open>k\<close>] by metis
          moreover
          have ln: \<open>l \<le> n\<close> using cs_order_le[OF ip(2,1) csli'[symmetric] csn[symmetric] nreti' in'] .
          ultimately 
          have lles: \<open>Suc l \<le> (LEAST i'. n < i' \<and> (\<exists>i. cs\<^bsup>\<pi>'\<^esup> i = cs\<^bsup>\<pi>\<^esup> i'))\<close> by auto
          
          have nwcseq: \<open>\<forall>j'\<in>{LEAST i'. n < i' \<and> (\<exists>i. cs\<^bsup>\<pi>'\<^esup> i = cs\<^bsup>\<pi>\<^esup> i')..<k}. v \<notin> writes (\<pi> j')\<close> proof 
            fix j' assume *: \<open>j' \<in> {LEAST i'. n < i' \<and> (\<exists>i. cs\<^bsup>\<pi>'\<^esup> i = cs\<^bsup>\<pi>\<^esup> i')..<k}\<close>
            hence \<open>(LEAST i'. n < i' \<and> (\<exists>i. cs\<^bsup>\<pi>'\<^esup> i = cs\<^bsup>\<pi>\<^esup> i')) \<le> j'\<close> by (metis (poly_guards_query) atLeastLessThan_iff)
            hence \<open>Suc l \<le> j'\<close> using lles by auto
            moreover
            have \<open>j' < k\<close> using * by (metis (poly_guards_query) atLeastLessThan_iff) 
            ultimately have \<open>j'\<in> {Suc l..<k}\<close> by (metis (poly_guards_query) atLeastLessThan_iff)
            thus \<open>v\<notin>writes (\<pi> j')\<close> using nwb by auto
          qed
          
          from cp.intros(3)[OF ncp,folded path,OF kddl' lcdn' cseq sucn[symmetric] vneq[symmetric] nwcseq]
          have \<open>((\<sigma>', k'), \<sigma>, k) \<in> cp\<close> .
          thus \<open>((\<sigma>, k), (\<sigma>', k')) \<in> cp\<close> using cp.intros(4) by auto
        next
          assume lnotin\<pi>': \<open>\<not> (\<exists>i'. cs\<^bsup>\<pi>\<^esup> l = cs\<^bsup>\<pi>'\<^esup> i')\<close>
          show \<open>?thesis\<close> proof cases
            assume \<open>\<exists> i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> l'\<close>
            then obtain i where csli: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> l'\<close> by blast
            have ilne: \<open>i \<noteq> l\<close> using csl csli by auto
            have ij: \<open>i < k\<close> using cs_order[OF ip(2,1) csli[symmetric] cseq nretl' lk'] .
            have iv: \<open>v \<in> writes(\<pi> i)\<close> using lv' csli last_cs by metis
            have il: \<open>i < l\<close> using kddl ilne ij iv unfolding is_ddi_def by auto
            have nreti: \<open>\<pi> i \<noteq> return\<close> using csli nretl' last_cs by metis

            obtain n n' where csn: \<open>cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and lcdn: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close>  and sucn: \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close> and ilen: \<open>i \<le> n\<close>
            using converged_cd_diverge_cs [OF ip csli il lnotin\<pi>' lk cseq[symmetric]] by metis 
          
            \<comment> \<open>Can apply the IH to n and n'\<close>
          
            have 1: \<open>\<pi> (Suc n) = suc (\<pi> n) (\<sigma>\<^bsup>n\<^esup>)\<close> by (metis step_suc_sem fst_conv path(1) path_suc)
            have 2: \<open>\<pi>' (Suc n') = suc (\<pi>' n') (\<sigma>'\<^bsup>n'\<^esup>)\<close> by (metis step_suc_sem fst_conv path(2) path_suc)
            have 3: \<open>\<pi>' n' = \<pi> n\<close> using csn last_cs by metis
            have nreads: \<open>\<sigma>\<^bsup>n\<^esup> \<restriction> reads (\<pi> n) \<noteq> \<sigma>'\<^bsup>n'\<^esup> \<restriction> reads (\<pi> n)\<close> by (metis 1 2 3 sucn reads_restr_suc)
            then obtain v' where v'read: \<open>v'\<in>reads (path \<sigma> n)\<close> \<open>(\<sigma>\<^bsup>n\<^esup>) v' \<noteq> (\<sigma>'\<^bsup>n'\<^esup>) v'\<close> by (metis path(1) reads_restrict)
            moreover  
            have nl: \<open>n < l\<close> using lcdn is_cdi_def by auto
            have nk: \<open>n < k\<close> using nl lk by simp
            have nretn: \<open>\<pi> n \<noteq> return\<close> by (metis ip(1) nl nret term_path_stable less_imp_le)
            have nk': \<open>n' < k'\<close> using cs_order[OF ip csn cseq[symmetric] nretn nk] .
            hence lenn: \<open>n+n' < k+k'\<close> using nk by auto
            ultimately  
            have ncp: \<open>((\<sigma>, n), (\<sigma>', n')) \<in> cp\<close> using IH csn path by auto
            
            have nles': \<open>n' < (LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))\<close> (is \<open>_ < (LEAST i. ?P i)\<close>) using nk' cseq LeastI[of \<open>?P\<close> \<open>k'\<close>] by metis
            moreover
            have ln': \<open>l' \<le> n'\<close> using cs_order_le[OF ip csli csn nreti ilen] .
            ultimately 
            have lles': \<open>Suc l' \<le> (LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))\<close> by auto
          
            have nwcseq': \<open>\<forall>j'\<in>{(LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))..<k'}. v \<notin> writes (\<pi>' j')\<close> proof 
              fix j' assume *: \<open>j' \<in> {(LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))..<k'}\<close>
              hence \<open>(LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i')) \<le> j'\<close> by (metis (poly_guards_query) atLeastLessThan_iff)
              hence \<open>Suc l' \<le> j'\<close> using lles' by auto
              moreover
              have \<open>j' < k'\<close> using * by (metis (poly_guards_query) atLeastLessThan_iff) 
              ultimately have \<open>j'\<in> {Suc l'..<k'}\<close> by (metis (poly_guards_query) atLeastLessThan_iff)
              thus \<open>v\<notin>writes (\<pi>' j')\<close> using nwb' by auto
              qed
            
            from cp.intros(3)[OF ncp,folded path, OF kddl lcdn cseq[symmetric] sucn vneq nwcseq']
            
            show \<open>((\<sigma>, k), (\<sigma>', k')) \<in> cp\<close> .
          next
            assume l'notin\<pi>: \<open>\<not> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> l')\<close>
            define m where \<open>m \<equiv> 0::nat\<close>
            define m' where \<open>m' \<equiv> 0::nat\<close>
            have csm: \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close> unfolding m_def m'_def cs_0 by (metis \<pi>0)
            have ml: \<open>m<l \<or> m'<l'\<close> using csm csl unfolding m_def m'_def by (metis neq0_conv)
            have \<open>\<exists> n n'. cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n' \<and> \<pi> (Suc n) \<noteq> \<pi>' (Suc n') \<and> 
            (l cd\<^bsup>\<pi>\<^esup>\<rightarrow> n \<and> (\<forall>j'\<in>{(LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))..<k'}. v\<notin>writes (\<pi>' j'))
            \<or> l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n' \<and> (\<forall>j\<in>{(LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i))..<k}. v\<notin>writes (\<pi> j)))\<close>
            using csm ml proof (induction \<open>k+k'-(m+m')\<close> arbitrary: \<open>m\<close> \<open>m'\<close> rule: less_induct)
              case (less m m')
              note csm = \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m'\<close>
              note lm = \<open>m < l \<or> m' < l'\<close>
              note IH = \<open>\<And> n n'. 
                k + k' - (n + n') < k + k' - (m + m') \<Longrightarrow>
                cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n' \<Longrightarrow>
                n < l \<or> n' < l' \<Longrightarrow> ?thesis\<close>
              show \<open>?thesis\<close> using lm proof
                assume ml: \<open>m < l\<close>
                obtain n n' where mn: \<open>m \<le> n\<close> and csn: \<open> cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and lcdn: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> and suc: \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close>
                  using  converged_cd_diverge_cs[OF ip csm ml lnotin\<pi>' lk cseq[symmetric]] .
                have nl: \<open>n < l\<close> using lcdn is_cdi_def by auto
                hence nk: \<open>n<k\<close> using lk by auto
                have nretn: \<open>\<pi> n \<noteq> return\<close> using lcdn by (metis cd_not_ret)
                have nk': \<open>n'<k'\<close> using cs_order[OF ip csn cseq[symmetric] nretn nk] .
                show \<open>?thesis\<close> proof cases
                  assume \<open>\<forall>j'\<in>{(LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))..<k'}. v\<notin>writes (\<pi>' j')\<close>
                  thus \<open>?thesis\<close> using lcdn csn suc by blast
                next
                  assume \<open>\<not>(\<forall>j'\<in>{(LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))..<k'}. v\<notin>writes (\<pi>' j'))\<close>
                  then obtain j' where jin': \<open>j'\<in>{(LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))..<k'}\<close> and vwrite: \<open>v\<in>writes (\<pi>' j')\<close> by blast
                  define i' where \<open>i' \<equiv> LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i')\<close>
                  have Pk': \<open>n' < k' \<and> (\<exists> k. cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k')\<close> (is \<open>?P k'\<close>) using nk' cseq[symmetric] by blast
                  have ni': \<open>n' < i'\<close> using LeastI[of \<open>?P\<close>, OF Pk'] i'_def by auto
                  obtain i where csi: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> using LeastI[of \<open>?P\<close>, OF Pk'] i'_def by blast
                  have ij': \<open>i'\<le>j'\<close> using jin'[folded i'_def] by auto
                  have jk': \<open>j'<k'\<close> using jin'[folded i'_def] by auto
                  have jl': \<open>j' \<le> l'\<close> using kddl' jk' vwrite unfolding is_ddi_def by auto
                  have nretn': \<open>\<pi>' n' \<noteq> return\<close> using nretn csn last_cs by metis
                  have iln: \<open>n<i\<close> using cs_order[OF ip(2,1) csn[symmetric] csi[symmetric] nretn' ni'] .
                  hence mi: \<open>m < i\<close> using mn by auto
                  have nretm: \<open>\<pi> m \<noteq> return\<close> by (metis ip(1) mn nretn term_path_stable)
                  have mi': \<open>m'<i'\<close> using cs_order[OF ip csm csi nretm mi] .
                  have ik': \<open>i' < k'\<close> using ij' jk' by auto
                  have nreti': \<open>\<pi>' i' \<noteq> return\<close> by (metis ij' jl' nretl' ip(2) term_path_stable)
                  have ik: \<open>i < k\<close> using cs_order[OF ip(2,1) csi[symmetric] cseq nreti' ik'] .
                  show \<open>?thesis\<close> proof cases
                    assume il:\<open>i < l\<close>
                    have le: \<open>k + k' - (i +i') < k+k' - (m+m')\<close> using mi mi' ik ik' by auto
                    show \<open>?thesis\<close> using IH[OF le] using csi il by blast
                  next
                    assume \<open>\<not> i < l\<close>
                    hence li: \<open>l \<le> i\<close> by auto
                    have \<open>i' \<le> l'\<close> using ij' jl' by auto
                    hence il': \<open>i' < l'\<close> using  csi l'notin\<pi> by fastforce 
                    obtain n n' where in': \<open>i' \<le> n'\<close> and csn: \<open> cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and lcdn': \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> and suc: \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close>
                      using  converged_cd_diverge_cs[OF ip(2,1) csi[symmetric] il' _ lk' cseq] l'notin\<pi> by metis
                    have nk': \<open>n' < k'\<close> using lcdn' is_cdi_def lk' by auto
                    have nretn': \<open>\<pi>' n' \<noteq> return\<close> by (metis cd_not_ret lcdn')
                    have nk: \<open>n < k\<close> using cs_order[OF ip(2,1) csn[symmetric] cseq nretn' nk'] . 
                    define j where \<open>j \<equiv> LEAST j. n < j \<and> (\<exists>j'. cs\<^bsup>\<pi>'\<^esup> j' = cs\<^bsup>\<pi>\<^esup> j)\<close>
                    have Pk: \<open>n < k \<and> (\<exists>j'. cs\<^bsup>\<pi>'\<^esup> j' = cs\<^bsup>\<pi>\<^esup> k)\<close> (is \<open>?P k\<close>) using nk cseq by blast
                    have nj: \<open>n<j\<close> using LeastI[of \<open>?P\<close>, OF Pk] j_def by auto
                    have ilen: \<open>i \<le> n\<close> using cs_order_le[OF ip(2,1) csi[symmetric] csn[symmetric] nreti' in'] . 
                    hence lj: \<open>l<j\<close> using li nj by simp
                    have \<open>\<forall>l\<in>{l<..<k}. v \<notin> writes (\<pi> l)\<close> using  kddl unfolding is_ddi_def by simp
                    hence nw: \<open>\<forall>l\<in>{j..<k}. v \<notin> writes (\<pi> l)\<close> using lj by auto
                    show \<open>?thesis\<close> using csn lcdn' suc nw[unfolded j_def] by blast
                  qed
                qed
              next
                assume ml': \<open>m' < l'\<close>
                obtain n n' where mn': \<open>m' \<le> n'\<close> and csn: \<open> cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and lcdn': \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> and suc: \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close>
                  using  converged_cd_diverge_cs[OF ip(2,1) csm[symmetric] ml' _ lk' cseq] l'notin\<pi> by metis
                have nl': \<open>n' < l'\<close> using lcdn' is_cdi_def by auto
                hence nk': \<open>n'<k'\<close> using lk' by auto
                have nretn': \<open>\<pi>' n' \<noteq> return\<close> using lcdn' by (metis cd_not_ret)
                have nk: \<open>n<k\<close> using cs_order[OF ip(2,1) csn[symmetric] cseq nretn' nk'] .
                show \<open>?thesis\<close> proof cases
                  assume \<open>\<forall>j\<in>{(LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i))..<k}. v\<notin>writes (\<pi> j)\<close>
                  thus \<open>?thesis\<close> using lcdn' csn suc by blast
                next
                  assume \<open>\<not>(\<forall>j\<in>{(LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i))..<k}. v\<notin>writes (\<pi> j))\<close>
                  then obtain j where jin: \<open>j\<in>{(LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i))..<k}\<close> and vwrite: \<open>v\<in>writes (\<pi> j)\<close> by blast
                  define i where \<open>i \<equiv> LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i)\<close>
                  have Pk: \<open>n < k \<and> (\<exists> k'. cs\<^bsup>\<pi>'\<^esup> k' = cs\<^bsup>\<pi>\<^esup> k)\<close> (is \<open>?P k\<close>) using nk cseq by blast
                  have ni: \<open>n < i\<close> using LeastI[of \<open>?P\<close>, OF Pk] i_def by auto
                  obtain i' where csi: \<open>cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'\<close> using LeastI[of \<open>?P\<close>, OF Pk] i_def by metis
                  have ij: \<open>i\<le>j\<close> using jin[folded i_def] by auto
                  have jk: \<open>j<k\<close> using jin[folded i_def] by auto
                  have jl: \<open>j \<le> l\<close> using kddl jk vwrite unfolding is_ddi_def by auto
                  have nretn: \<open>\<pi> n \<noteq> return\<close> using nretn' csn last_cs by metis
                  have iln': \<open>n'<i'\<close> using cs_order[OF ip csn csi nretn ni] .
                  hence mi': \<open>m' < i'\<close> using mn' by auto
                  have nretm': \<open>\<pi>' m' \<noteq> return\<close> by (metis ip(2) mn' nretn' term_path_stable)
                  have mi: \<open>m<i\<close> using cs_order[OF ip(2,1) csm[symmetric] csi[symmetric] nretm' mi'] .
                  have ik: \<open>i < k\<close> using ij jk by auto
                  have nreti: \<open>\<pi> i \<noteq> return\<close> by (metis ij ip(1) jl nret term_path_stable)
                  have ik': \<open>i' < k'\<close> using cs_order[OF ip csi cseq[symmetric] nreti ik] .
                  show \<open>?thesis\<close> proof cases
                    assume il':\<open>i' < l'\<close>
                    have le: \<open>k + k' - (i +i') < k+k' - (m+m')\<close> using mi mi' ik ik' by auto
                    show \<open>?thesis\<close> using IH[OF le] using csi il' by blast
                  next
                    assume \<open>\<not> i' < l'\<close>
                    hence li': \<open>l' \<le> i'\<close> by auto
                    have \<open>i \<le> l\<close> using ij jl by auto
                    hence il: \<open>i < l\<close> using  csi lnotin\<pi>' by fastforce 
                    obtain n n' where ilen: \<open>i \<le> n\<close> and csn: \<open> cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and lcdn: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> and suc: \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close>
                      using  converged_cd_diverge_cs[OF ip csi il _ lk cseq[symmetric]] lnotin\<pi>' by metis
                    have nk: \<open>n < k\<close> using lcdn is_cdi_def lk by auto
                    have nretn: \<open>\<pi> n \<noteq> return\<close> by (metis cd_not_ret lcdn)
                    have nk': \<open>n' < k'\<close> using cs_order[OF ip csn cseq[symmetric] nretn nk] . 
                    define j' where \<open>j' \<equiv> LEAST j'. n' < j' \<and> (\<exists>j. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> j')\<close>
                    have Pk': \<open>n' < k' \<and> (\<exists>j. cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> k')\<close> (is \<open>?P k'\<close>) using nk' cseq[symmetric] by blast
                    have nj': \<open>n'<j'\<close> using LeastI[of \<open>?P\<close>, OF Pk'] j'_def by auto
                    have in': \<open>i' \<le> n'\<close> using cs_order_le[OF ip csi csn nreti ilen] . 
                    hence lj': \<open>l'<j'\<close> using li' nj' by simp
                    have \<open>\<forall>l\<in>{l'<..<k'}. v \<notin> writes (\<pi>' l)\<close> using  kddl' unfolding is_ddi_def by simp
                    hence nw': \<open>\<forall>l\<in>{j'..<k'}. v \<notin> writes (\<pi>' l)\<close> using lj' by auto
                    show \<open>?thesis\<close> using csn lcdn suc nw'[unfolded j'_def] by blast
                  qed
                qed
              qed
            qed
            then obtain n n' where csn: \<open> cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n'\<close> and suc: \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close>
            and cdor: 
            \<open>(l cd\<^bsup>\<pi>\<^esup>\<rightarrow> n \<and> (\<forall>j'\<in>{(LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i'))..<k'}. v\<notin>writes (\<pi>' j'))
            \<or> l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n' \<and> (\<forall>j\<in>{(LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i))..<k}. v\<notin>writes (\<pi> j)))\<close> 
            by blast
            show \<open>?thesis\<close> using cdor proof
              assume *: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> n \<and> (\<forall>j'\<in>{LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i')..<k'}. v \<notin> local.writes (\<pi>' j'))\<close>
              hence lcdn: \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> by blast 
              have nowrite: \<open>\<forall>j'\<in>{LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i')..<k'}. v \<notin> local.writes (\<pi>' j')\<close> using * by blast
              show \<open>?thesis\<close> proof (rule cp.intros(3)[of \<open>\<sigma>\<close> \<open>n\<close> \<open>\<sigma>'\<close> \<open>n'\<close>,folded path])
                show \<open>l cd\<^bsup>\<pi>\<^esup>\<rightarrow> n\<close> using lcdn .
                show \<open>k dd\<^bsup>\<pi>,v\<^esup>\<rightarrow> l\<close> using kddl .
                show \<open>cs\<^bsup>\<pi>\<^esup> k = cs\<^bsup>\<pi>'\<^esup> k'\<close> using cseq by simp
                show \<open>\<pi> (Suc n) \<noteq> \<pi>' (Suc n')\<close> using suc by simp
                show \<open>\<forall>j'\<in>{LEAST i'. n' < i' \<and> (\<exists>i. cs\<^bsup>\<pi>\<^esup> i = cs\<^bsup>\<pi>'\<^esup> i')..<k'}. v \<notin> local.writes (\<pi>' j')\<close> using nowrite .
                show \<open>(\<sigma>\<^bsup>k\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'\<^esup>) v\<close> using vneq .
                have nk: \<open>n < k\<close> using lcdn lk is_cdi_def by auto
                have nretn: \<open>\<pi> n \<noteq> return\<close> using cd_not_ret lcdn by metis
                have nk': \<open>n' < k'\<close> using cs_order[OF ip csn cseq[symmetric] nretn nk] .
                hence le: \<open>n + n' < k + k'\<close> using nk by auto
                moreover
                have 1: \<open>\<pi> (Suc n) = suc (\<pi> n) (\<sigma>\<^bsup>n\<^esup>)\<close> by (metis step_suc_sem fst_conv path(1) path_suc)
                have 2: \<open>\<pi>' (Suc n') = suc (\<pi>' n') (\<sigma>'\<^bsup>n'\<^esup>)\<close> by (metis step_suc_sem fst_conv path(2) path_suc)
                have 3: \<open>\<pi>' n' = \<pi> n\<close> using csn last_cs by metis
                have nreads: \<open>\<sigma>\<^bsup>n\<^esup> \<restriction> reads (\<pi> n) \<noteq> \<sigma>'\<^bsup>n'\<^esup> \<restriction> reads (\<pi> n)\<close> by (metis 1 2 3 suc reads_restr_suc)
                then obtain v' where v'read: \<open>v'\<in>reads (path \<sigma> n)\<close> \<open>(\<sigma>\<^bsup>n\<^esup>) v' \<noteq> (\<sigma>'\<^bsup>n'\<^esup>) v'\<close> by (metis path(1) reads_restrict)
                ultimately  
                show \<open>((\<sigma>, n), (\<sigma>', n')) \<in> cp\<close> using IH csn path by auto
              qed
            next
              assume *: \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n' \<and> (\<forall>j\<in>{(LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i))..<k}. v\<notin>writes (\<pi> j))\<close>
              hence lcdn': \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> by blast 
              have nowrite: \<open>\<forall>j\<in>{(LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i))..<k}. v\<notin>writes (\<pi> j)\<close> using * by blast
              show \<open>?thesis\<close> proof (rule cp.intros(4), rule cp.intros(3)[of \<open>\<sigma>'\<close> \<open>n'\<close> \<open>\<sigma>\<close> \<open>n\<close>,folded path])
                show \<open>l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> n'\<close> using lcdn' .
                show \<open>k' dd\<^bsup>\<pi>',v\<^esup>\<rightarrow> l'\<close> using kddl' .
                show \<open>cs\<^bsup>\<pi>'\<^esup> k' = cs\<^bsup>\<pi>\<^esup> k\<close> using cseq .
                show \<open>\<pi>' (Suc n') \<noteq> \<pi> (Suc n)\<close> using suc by simp
                show \<open>\<forall>j\<in>{(LEAST i. n < i \<and> (\<exists>i'. cs\<^bsup>\<pi>'\<^esup> i' = cs\<^bsup>\<pi>\<^esup> i))..<k}. v\<notin>writes (\<pi> j)\<close> using nowrite .
                show \<open>(\<sigma>'\<^bsup>k'\<^esup>) v \<noteq> (\<sigma>\<^bsup>k\<^esup>) v\<close> using vneq by simp
                have nk': \<open>n' < k'\<close> using lcdn' lk' is_cdi_def by auto
                have nretn': \<open>\<pi>' n' \<noteq> return\<close> using cd_not_ret lcdn' by metis
                have nk: \<open>n < k\<close> using cs_order[OF ip(2,1) csn[symmetric] cseq nretn' nk'] .
                hence le: \<open>n + n' < k + k'\<close> using nk' by auto
                moreover
                have 1: \<open>\<pi> (Suc n) = suc (\<pi> n) (\<sigma>\<^bsup>n\<^esup>)\<close> by (metis step_suc_sem fst_conv path(1) path_suc)
                have 2: \<open>\<pi>' (Suc n') = suc (\<pi>' n') (\<sigma>'\<^bsup>n'\<^esup>)\<close> by (metis step_suc_sem fst_conv path(2) path_suc)
                have 3: \<open>\<pi>' n' = \<pi> n\<close> using csn last_cs by metis
                have nreads: \<open>\<sigma>\<^bsup>n\<^esup> \<restriction> reads (\<pi> n) \<noteq> \<sigma>'\<^bsup>n'\<^esup> \<restriction> reads (\<pi> n)\<close> by (metis 1 2 3 suc reads_restr_suc)
                then obtain v' where v'read: \<open>v'\<in>reads (path \<sigma> n)\<close> \<open>(\<sigma>\<^bsup>n\<^esup>) v' \<noteq> (\<sigma>'\<^bsup>n'\<^esup>) v'\<close> by (metis path(1) reads_restrict)
                ultimately  
                have \<open>((\<sigma>, n), (\<sigma>', n')) \<in> cp\<close> using IH csn path by auto
                thus \<open>((\<sigma>', n'), \<sigma>, n) \<in> cp\<close> using cp.intros(4) by simp                
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed


theorem contradicting_in_cop: assumes \<open>\<sigma> =\<^sub>L \<sigma>'\<close> and \<open>(\<sigma>',k') \<cc> (\<sigma>,k)\<close> and \<open>path \<sigma> k \<in> dom att\<close> 
shows \<open>((\<sigma>,k),\<sigma>',k') \<in> cop\<close> using assms(2) proof(cases) 
  case (1 \<pi>' \<pi>) 
  define j where \<open>j \<equiv> \<pi> \<exclamdown> cs\<^bsup>\<pi>'\<^esup> k'\<close>
  have csj: \<open>cs\<^bsup>\<pi>\<^esup> j = cs\<^bsup>\<pi>'\<^esup> k'\<close> unfolding j_def using 1 by (metis cs_not_nil cs_select_is_cs(1) path_is_path)
  have suc: \<open>\<pi> (Suc j) \<noteq> \<pi>' (Suc k')\<close> using 1 j_def by simp
  have kcdj: \<open>k cd\<^bsup>\<pi>\<^esup>\<rightarrow> j\<close> by (metis cs_not_nil cs_select_is_cs(2) 1(1,2) j_def path_is_path)
  obtain v where readv: \<open>v\<in>reads(path \<sigma> j)\<close> and vneq: \<open>(\<sigma>\<^bsup>j\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'\<^esup>) v\<close> using suc csj unfolding 1 by (metis IFC_def.suc_def 1(2) 1(3) last_cs path_suc reads_restr_suc reads_restrict)
  have \<open>((\<sigma>,j),\<sigma>',k') \<in> cp\<close> apply (rule contradicting_in_cp[OF assms(1)]) using readv vneq csj 1 by auto
  thus \<open>((\<sigma>,k),\<sigma>',k') \<in> cop\<close> using kcdj suc assms(3) cop.intros(2) unfolding 1 by auto
  next
  case (2 \<pi>' \<pi>)
  obtain v where readv: \<open>v\<in>reads(path \<sigma> k)\<close> and vneq: \<open>(\<sigma>\<^bsup>k\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'\<^esup>) v\<close> using 2(2-4) by (metis reads_restrict)
  have \<open>((\<sigma>,k),\<sigma>',k') \<in> cp\<close> apply (rule contradicting_in_cp[OF assms(1)]) using readv vneq 2 by auto
  thus \<open>((\<sigma>,k),\<sigma>',k') \<in> cop\<close> using assms(3) cop.intros(1) unfolding 2 by auto
qed


theorem cop_correct_term: fixes \<sigma> \<sigma>' defines \<pi>: \<open>\<pi> \<equiv> path \<sigma>\<close> and \<pi>': \<open>\<pi>' \<equiv> path \<sigma>'\<close> 
assumes ret: \<open>\<pi> n = return\<close> \<open>\<pi>' n' = return\<close> and obsne: \<open>obs \<sigma> \<noteq> obs \<sigma>'\<close> and leq: \<open>\<sigma> =\<^sub>L \<sigma>'\<close>
shows \<open>\<exists> k k'. ((\<sigma>,k),\<sigma>',k')\<in> cop \<or> ((\<sigma>',k'),\<sigma>,k)\<in> cop\<close>
proof -
  have *: \<open>\<exists> k k'. ((\<sigma>', k') \<cc> (\<sigma> ,k) \<and> \<pi> k \<in> dom (att)) \<or> ((\<sigma>, k) \<cc> (\<sigma>' ,k') \<and> \<pi>' k' \<in> dom (att))\<close> using  obs_neq_contradicts_term ret obsne \<pi> \<pi>' by auto
  have leq' :\<open>\<sigma>' =\<^sub>L \<sigma>\<close> using leq unfolding loweq_def by auto
  from * contradicting_in_cop[OF leq] contradicting_in_cop[OF leq'] show \<open>?thesis\<close> unfolding \<pi> \<pi>' by metis
qed


theorem cop_correct_ret: fixes \<sigma> \<sigma>' defines \<pi>: \<open>\<pi> \<equiv> path \<sigma>\<close> and \<pi>': \<open>\<pi>' \<equiv> path \<sigma>'\<close> 
assumes ret: \<open>\<pi> n = return\<close> and obsne: \<open>obs \<sigma> i \<noteq> obs \<sigma>' i\<close> and obs: \<open>obs \<sigma>' i \<noteq> None\<close> and leq: \<open>\<sigma> =\<^sub>L \<sigma>'\<close>
shows \<open>\<exists> k k'. ((\<sigma>,k),\<sigma>',k')\<in> cop \<or> ((\<sigma>',k'),\<sigma>,k)\<in> cop\<close>
proof -
  have *: \<open>\<exists> k k'. ((\<sigma>', k') \<cc> (\<sigma> ,k) \<and> \<pi> k \<in> dom (att)) \<or> ((\<sigma>, k) \<cc> (\<sigma>' ,k') \<and> \<pi>' k' \<in> dom (att))\<close>
    by (metis (no_types, lifting) \<pi> \<pi>' obs obs_neq_ret_contradicts obsne ret) 
  have leq' :\<open>\<sigma>' =\<^sub>L \<sigma>\<close> using leq unfolding loweq_def by auto
  from * contradicting_in_cop[OF leq] contradicting_in_cop[OF leq'] show \<open>?thesis\<close> unfolding \<pi> \<pi>' by metis
qed


theorem cop_correct_nterm: assumes obsne: \<open>obs \<sigma> k \<noteq> obs \<sigma>' k\<close> \<open>obs \<sigma> k \<noteq> None\<close> \<open>obs \<sigma>' k \<noteq> None\<close> 
and leq: \<open>\<sigma> =\<^sub>L \<sigma>'\<close>
shows \<open>\<exists> k k'. ((\<sigma>,k),\<sigma>',k')\<in> cop \<or> ((\<sigma>',k'),\<sigma>,k)\<in> cop\<close>
proof -
  obtain k k' where \<open>((\<sigma>', k') \<cc> (\<sigma> ,k) \<and> path \<sigma> k \<in> dom att) \<or> ((\<sigma>, k) \<cc> (\<sigma>' ,k') \<and> path \<sigma>' k' \<in> dom att)\<close> 
  using obs_neq_some_contradicts[OF obsne] by metis
  thus \<open>?thesis\<close> proof
    assume *: \<open>(\<sigma>', k') \<cc> (\<sigma> ,k) \<and> path \<sigma> k \<in> dom att\<close>
    hence \<open>((\<sigma>,k),\<sigma>',k') \<in> cop\<close> using leq by (metis contradicting_in_cop)
    thus \<open>?thesis\<close> using * by blast
  next 
    assume *: \<open>(\<sigma>, k) \<cc> (\<sigma>' ,k') \<and> path \<sigma>' k' \<in> dom att\<close>
    hence \<open>((\<sigma>',k'),\<sigma>,k) \<in> cop\<close> using leq by (metis contradicting_in_cop loweq_def)
    thus \<open>?thesis\<close> using * by blast
  qed
qed


subsection \<open>Correctness of the Characterisation\<close>
text_raw \<open>\label{sec:cor-cp}\<close>

text \<open>The following is our main correctness result. If there exist no critical observable paths,
then the program is secure.\<close>

theorem cop_correct: assumes \<open>cop = empty\<close> shows \<open>secure\<close> proof (rule ccontr)
  assume \<open>\<not> secure\<close>
  then obtain \<sigma> \<sigma>' where leq: \<open> \<sigma> =\<^sub>L \<sigma>'\<close> 
    and **: \<open>\<not> obs \<sigma> \<approx> obs \<sigma>' \<or> (terminates \<sigma> \<and> \<not> obs \<sigma>' \<lesssim> obs \<sigma>)\<close>
    unfolding secure_def by blast
  show \<open>False\<close> using ** proof
    assume \<open>\<not> obs \<sigma> \<approx> obs \<sigma>'\<close>
    then obtain k where \<open>obs \<sigma> k \<noteq> obs \<sigma>' k \<and> obs \<sigma> k \<noteq> None \<and> obs \<sigma>' k \<noteq> None\<close> 
      unfolding obs_comp_def obs_prefix_def
      by (metis kth_obs_stable linorder_neqE_nat obs_none_no_kth_obs obs_some_kth_obs) 
    thus \<open>False\<close> using cop_correct_nterm leq assms by auto
  next
    assume *: \<open>terminates \<sigma> \<and> \<not> obs \<sigma>' \<lesssim> obs \<sigma>\<close>
    then obtain n where ret: \<open>path \<sigma> n = return\<close>  
      unfolding terminates_def by auto
    obtain k where \<open>obs \<sigma> k \<noteq> obs \<sigma>' k \<and> obs \<sigma>' k \<noteq> None\<close> using * unfolding obs_prefix_def by metis 
    thus \<open>False\<close> using cop_correct_ret ret leq assms by (metis empty_iff) 
  qed
qed


text \<open>Our characterisation is not only correct, it is also precise in the way that \<open>cp\<close> characterises 
exactly the matching indices in executions for low equivalent input states where diverging data is read. 
This follows easily as the inverse implication to lemma \<open>contradicting_in_cp\<close> can be shown by simple induction.\<close>

theorem cp_iff_reads_contradict: \<open>((\<sigma>,k),(\<sigma>',k')) \<in> cp \<longleftrightarrow> \<sigma> =\<^sub>L \<sigma>' \<and> cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k' \<and> (\<exists> v\<in>reads(path \<sigma> k). (\<sigma>\<^bsup>k\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'\<^esup>) v)\<close> 
proof
  assume \<open>\<sigma> =\<^sub>L \<sigma>' \<and> cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k' \<and> (\<exists>v\<in>reads (path \<sigma> k). (\<sigma>\<^bsup>k\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'\<^esup>) v)\<close>
  thus \<open>((\<sigma>, k), \<sigma>', k') \<in> cp\<close> using contradicting_in_cp by blast 
next
  assume \<open>((\<sigma>, k), \<sigma>', k') \<in> cp\<close> 
  thus \<open>\<sigma> =\<^sub>L \<sigma>' \<and> cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k' \<and> (\<exists>v\<in>reads (path \<sigma> k). (\<sigma>\<^bsup>k\<^esup>) v \<noteq> (\<sigma>'\<^bsup>k'\<^esup>) v)\<close>
  proof (induction)
    case (1 \<sigma> \<sigma>' n n' h)
    then show \<open>?case\<close> by blast 
  next
    case (2 \<sigma> k \<sigma>' k' n v n')
    have \<open>v\<in>reads (path \<sigma> n)\<close> using 2(2) unfolding is_ddi_def by auto
    then show \<open>?case\<close> using 2 by auto
  next
    case (3 \<sigma> k \<sigma>' k' n v l n')
    have \<open>v\<in>reads (path \<sigma> n)\<close> using 3(2) unfolding is_ddi_def by auto
    then show \<open>?case\<close> using 3(4,6,8) by auto
  next
    case (4 \<sigma> k \<sigma>' k')
    hence \<open>cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k'\<close> by simp
    hence \<open>path \<sigma>' k' = path \<sigma> k\<close> by (metis last_cs) 
    moreover have \<open>\<sigma>' =\<^sub>L \<sigma>\<close> using 4(2) unfolding loweq_def by simp
    ultimately show \<open>?case\<close> using 4 by metis
  qed
qed


text \<open>In the same way the inverse implication to \<open>contradicting_in_cop\<close> follows easily 
such that we obtain the following characterisation of \<open>cop\<close>.\<close>

theorem cop_iff_contradicting: \<open>((\<sigma>,k),(\<sigma>',k')) \<in> cop \<longleftrightarrow> \<sigma> =\<^sub>L \<sigma>' \<and> (\<sigma>',k') \<cc> (\<sigma>,k) \<and> path \<sigma> k \<in> dom att\<close> 
proof
  assume \<open>\<sigma> =\<^sub>L \<sigma>' \<and> (\<sigma>', k') \<cc> (\<sigma>, k) \<and> path \<sigma> k \<in> dom att\<close> thus \<open>((\<sigma>,k),(\<sigma>',k')) \<in> cop\<close> using contradicting_in_cop by simp
next
  assume \<open>((\<sigma>,k),(\<sigma>',k')) \<in> cop\<close> 
  thus \<open> \<sigma> =\<^sub>L \<sigma>' \<and> (\<sigma>',k') \<cc> (\<sigma>,k) \<and> path \<sigma> k \<in> dom att\<close> proof (cases rule: cop.cases)
    case 1
    then show \<open>?thesis\<close> using cp_iff_reads_contradict contradicts.simps by (metis (full_types) reads_restrict1)
  next
    case (2 k)
    then show \<open>?thesis\<close> using cp_iff_reads_contradict contradicts.simps
      by (metis cd_is_cs_less cd_not_ret contradicts.intros(1) cs_select_id path_is_path) 
  qed
qed


subsection \<open>Correctness of the Single Path Approximation\<close>
text_raw \<open>\label{sec:cor-scp}\<close>

theorem cp_in_scp: assumes \<open>((\<sigma>,k),(\<sigma>',k'))\<in>cp\<close> shows \<open>(path \<sigma>,k)\<in>scp \<and> (path \<sigma>',k')\<in>scp\<close> 
using assms proof(induction \<open>\<sigma>\<close> \<open>k\<close> \<open>\<sigma>'\<close> \<open>k'\<close> rule:cp.induct[case_names read_high dd dcd sym])
  case (read_high \<sigma> \<sigma>' k k' h) 
  have \<open>\<sigma> h = (\<sigma>\<^bsup>k\<^esup>) h\<close> using read_high(5) by (simp add: no_writes_unchanged0)
  moreover have \<open>\<sigma>' h = (\<sigma>'\<^bsup>k'\<^esup>) h\<close> using read_high(6) by (simp add: no_writes_unchanged0)
  ultimately have \<open>\<sigma> h \<noteq> \<sigma>' h\<close> using read_high(4) by simp 
  hence *: \<open>h\<in>hvars\<close> using read_high(1) unfolding loweq_def by (metis Compl_iff IFC_def.restrict_def)
  have 1: \<open>(path \<sigma>,k)\<in>scp\<close> using scp.intros(1) read_high(3,5) * by auto
  have \<open>path \<sigma> k = path \<sigma>' k'\<close> using read_high(2) by (metis last_cs)
  hence \<open>(path \<sigma>',k')\<in>scp\<close> using scp.intros(1) read_high(3,6) * by auto
  thus \<open>?case\<close> using 1 by auto
next
  case dd show \<open>?case\<close> using scp.intros(3) dd by auto  
next 
  case sym thus \<open>?case\<close> by blast
next
  case (dcd \<sigma> k \<sigma>' k' n v l n')   
  note scp.intros(4) is_dcdi_via_def cd_cs_swap cs_ipd
  have 1: \<open>(path \<sigma>, n)\<in>scp\<close> using dcd.IH dcd.hyps(2) dcd.hyps(3) scp.intros(2) scp.intros(3) by blast 
  have csk: \<open>cs\<^bsup>path \<sigma>\<^esup> k = cs\<^bsup>path \<sigma>'\<^esup> k'\<close> using cp_eq_cs[OF dcd(1)] .
  have kn: \<open>k<n\<close> and kl: \<open>k<l\<close> and ln: \<open>l<n\<close> using dcd(2,3) unfolding is_ddi_def is_cdi_def by auto
  have nret: \<open>path \<sigma> k \<noteq> return\<close> using cd_not_ret dcd.hyps(3) by auto
  have \<open>k' < n'\<close> using kn csk dcd(4) cs_order nret path_is_path last_cs by blast
  have 2: \<open>(path \<sigma>', n')\<in>scp\<close> proof cases    
    assume j'ex: \<open>\<exists>j'\<in>{k'..<n'}. v \<in> writes (path \<sigma>' j')\<close>
    hence \<open>\<exists>j'. j'\<in>{k'..<n'} \<and> v \<in> writes (path \<sigma>' j')\<close> by auto
    note * = GreatestI_ex_nat[OF this]
    define j' where \<open>j' == GREATEST j'. j'\<in>{k'..<n'} \<and> v \<in> writes (path \<sigma>' j')\<close>
    note ** = *[of \<open>j'\<close>,folded j'_def]  
    have \<open>k' \<le> j'\<close> \<open>j'<n'\<close> and j'write: \<open>v \<in> writes (path \<sigma>' j')\<close>
      using "*" atLeastLessThan_iff j'_def nat_less_le by auto
    have nowrite: \<open>\<forall> i'\<in>{j'<..<n'}. v \<notin> writes(path \<sigma>' i')\<close> proof (rule, rule ccontr)
      fix i' assume \<open>i' \<in> {j'<..<n'}\<close> \<open>\<not> v \<notin> local.writes (path \<sigma>' i')\<close>
      hence \<open>i' \<in> {k'..<n'} \<and> v \<in> local.writes (path \<sigma>' i')\<close> using \<open>k' \<le> j'\<close> by auto
      hence \<open>i' \<le> j'\<close> using Greatest_le_nat
        by (metis (no_types, lifting) atLeastLessThan_iff j'_def nat_less_le)
      thus \<open>False\<close> using \<open>i' \<in> {j'<..<n'}\<close> by auto
    qed
    have \<open>path \<sigma>' n' = path \<sigma> n\<close> using dcd(4) last_cs by metis
    hence \<open>v\<in>reads(path \<sigma>' n')\<close> using dcd(2) unfolding is_ddi_def by auto    
    hence nddj': \<open>n' dd\<^bsup>path \<sigma>',v\<^esup>\<rightarrow> j'\<close> using dcd(2) unfolding is_ddi_def using nowrite \<open>j'<n'\<close> j'write by auto 
    show \<open>?thesis\<close> proof cases
      assume \<open>j' cd\<^bsup>path \<sigma>'\<^esup>\<rightarrow> k'\<close>
      thus \<open>(path \<sigma>',n') \<in> scp\<close> using scp.intros(2) scp.intros(3) dcd.IH nddj' by fast
    next
      assume jcdk': \<open>\<not> j' cd\<^bsup>path \<sigma>'\<^esup>\<rightarrow> k'\<close>
      show \<open>?thesis\<close> proof cases
        assume \<open>j' = k'\<close>
        thus \<open>?thesis\<close> using scp.intros(3) dcd.IH nddj' by fastforce 
      next
        assume \<open>j' \<noteq> k'\<close> hence \<open>k' < j'\<close> using \<open>k' \<le> j'\<close> by auto
        have \<open>path \<sigma>' j' \<noteq> return\<close> using j'write writes_return by auto
        hence ipdex':\<open>\<exists>j. j \<in>{k'..j'} \<and> path \<sigma>' j = ipd (path \<sigma>' k') \<close> using path_is_path \<open>k' < j'\<close> jcdk' is_cdi_def by blast
        define i' where \<open>i' == LEAST j. j\<in> {k'..j'} \<and> path \<sigma>' j = ipd (path \<sigma>' k')\<close>        
        have iipd': \<open>i'\<in> {k'..j'}\<close> \<open>path \<sigma>' i' = ipd (path \<sigma>' k')\<close> unfolding i'_def using LeastI_ex[OF ipdex'] by simp_all
        have *:\<open>\<forall> i \<in> {k'..<i'}. path \<sigma>' i \<noteq> ipd (path \<sigma>' k')\<close> proof (rule, rule ccontr)
          fix i assume  *: \<open>i \<in> {k'..<i'}\<close> \<open>\<not> path \<sigma>' i \<noteq> ipd (path \<sigma>' k')\<close>
          hence **: \<open>i \<in>{k'..j'} \<and> path \<sigma>' i = ipd (path \<sigma>' k')\<close> (is \<open>?P i\<close>) using iipd'(1) by auto
          thus \<open>False\<close> using Least_le[of \<open>?P\<close> \<open>i\<close>] i'_def * by auto
        qed
        have \<open>i' \<noteq> k'\<close> using iipd'(2) by (metis csk last_cs nret path_in_nodes ipd_not_self)
        hence \<open>k'<i'\<close> using iipd'(1) by simp
        hence csi': \<open>cs\<^bsup>path \<sigma>'\<^esup> i' = [n\<leftarrow>cs\<^bsup>path \<sigma>'\<^esup> k' . ipd n \<noteq> path \<sigma>' i'] @ [path \<sigma>' i']\<close>using cs_ipd[OF iipd'(2) *] by fast 
        
        have ncdk': \<open>\<not> n' cd\<^bsup>path \<sigma>'\<^esup>\<rightarrow> k'\<close> using \<open>j' < n'\<close> \<open>k' < j'\<close> cdi_prefix jcdk' less_imp_le_nat by blast
        hence ncdk: \<open>\<not> n cd\<^bsup>path \<sigma>\<^esup>\<rightarrow> k\<close> using cd_cs_swap csk dcd(4) by blast        
        have ipdex: \<open>\<exists>i. i\<in>{k..n} \<and> path \<sigma> i = ipd (path \<sigma> k)\<close> (is \<open>\<exists>i. ?P i\<close>) proof cases
          assume *:\<open>path \<sigma> n = return\<close> 
          from path_ret_ipd[of \<open>path \<sigma>\<close> \<open>k\<close> \<open>n\<close>,OF path_is_path nret *]          
          obtain i where \<open>?P i\<close> by fastforce thus \<open>?thesis\<close> by auto
        next
          assume *:\<open>path \<sigma> n \<noteq> return\<close>           
          show \<open>?thesis\<close> using not_cd_impl_ipd [of \<open>path \<sigma>\<close> \<open>k\<close> \<open>n\<close>, OF path_is_path \<open>k<n\<close> ncdk *] by auto
        qed
        
        define i where  \<open>i == LEAST j. j\<in> {k..n} \<and> path \<sigma> j = ipd (path \<sigma> k)\<close>        
        have iipd: \<open>i\<in> {k..n}\<close> \<open>path \<sigma> i = ipd (path \<sigma> k)\<close> unfolding i_def using LeastI_ex[OF ipdex] by simp_all
        have **:\<open>\<forall> i' \<in> {k..<i}. path \<sigma> i' \<noteq> ipd (path \<sigma> k)\<close> proof (rule, rule ccontr)
          fix i' assume  *: \<open>i' \<in> {k..<i}\<close> \<open>\<not> path \<sigma> i' \<noteq> ipd (path \<sigma> k)\<close>
          hence **: \<open>i' \<in>{k..n} \<and> path \<sigma> i' = ipd (path \<sigma> k)\<close> (is \<open>?P i'\<close>) using iipd(1) by auto
          thus \<open>False\<close> using Least_le[of \<open>?P\<close> \<open>i'\<close>] i_def * by auto
        qed
        have \<open>i \<noteq> k\<close> using iipd(2) by (metis nret path_in_nodes ipd_not_self)
        hence \<open>k<i\<close> using iipd(1) by simp
        hence \<open>cs\<^bsup>path \<sigma>\<^esup> i = [n\<leftarrow>cs\<^bsup>path \<sigma>\<^esup> k . ipd n \<noteq> path \<sigma> i] @ [path \<sigma> i]\<close>using cs_ipd[OF iipd(2) **] by fast 
        hence csi: \<open>cs\<^bsup>path \<sigma>\<^esup> i = cs\<^bsup>path \<sigma>'\<^esup> i'\<close> using csi' csk unfolding iipd'(2) iipd(2) by (metis last_cs)
        hence \<open>(LEAST i'. k' < i' \<and> (\<exists>i. cs\<^bsup>path \<sigma>\<^esup> i = cs\<^bsup>path \<sigma>'\<^esup> i')) \<le> i'\<close> (is \<open>(LEAST x. ?P x) \<le> _\<close>) 
          using \<open>k' < i'\<close> Least_le[of \<open>?P\<close> \<open>i'\<close>] by blast
        hence nw: \<open>\<forall>j'\<in>{i'..<n'}. v \<notin> writes (path \<sigma>' j')\<close> using dcd(7) allB_atLeastLessThan_lower by blast  
        moreover have \<open>v \<in> writes (path \<sigma>' j')\<close> using nddj' unfolding is_ddi_def by auto
        moreover have \<open>i' \<le> j'\<close> using iipd'(1) by auto
        ultimately have \<open>False\<close>  using \<open>j' < n'\<close> by auto
        thus \<open>?thesis\<close> ..
      qed
    qed
  next
    assume \<open>\<not> (\<exists>j'\<in>{k'..<n'}. v \<in> writes (path \<sigma>' j'))\<close>
    
    hence \<open>n' dcd\<^bsup>path \<sigma>',v\<^esup>\<rightarrow> k' via (path \<sigma>) k\<close> unfolding is_dcdi_via_def using dcd(2-4) csk \<open>k'<n'\<close> path_is_path by metis    
    thus \<open>?thesis\<close> using dcd.IH scp.intros(4) by blast 
  qed
  with 1 show \<open>?case\<close> ..
qed   


theorem cop_in_scop: assumes \<open>((\<sigma>,k),(\<sigma>',k'))\<in>cop\<close> shows \<open>(path \<sigma>,k)\<in>scop \<and> (path \<sigma>',k')\<in>scp\<close>
  using assms 
  apply (induct rule: cop.induct)
   apply (simp add: cp_in_scp)
  using cp_in_scp scop.intros scp.intros(2)
   apply blast
  using cp_in_scp scop.intros scp.intros(2)
  apply blast
  done

text \<open>The main correctness result for out single execution approximation follows directly.\<close>

theorem scop_correct: assumes \<open>scop = empty\<close> shows \<open>secure\<close> 
  using cop_correct assms cop_in_scop by fast 

end

end