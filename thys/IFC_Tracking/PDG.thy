section \<open>Example: Program Dependence Graphs\<close>
text_raw \<open>\label{sec:pdg}\<close>

text \<open>Program dependence graph (PDG) based slicing provides a very crude but direct approximation of 
our characterisation. As such we can easily derive a corresponding correctness result.\<close>

theory PDG imports IFC
begin

context IFC 
begin

text \<open>We utilise our established dependencies on program paths to define the PDG. Note that PDGs 
usually only contain immediate control dependencies instead of the transitive ones we use here.
However as slicing is considering reachability questions this does not affect the result.\<close>
inductive_set pdg where 
\<open>\<lbrakk>i cd\<^bsup>\<pi>\<^esup>\<rightarrow> k\<rbrakk> \<Longrightarrow> (\<pi> k, \<pi> i) \<in> pdg\<close> |
\<open>\<lbrakk>i dd\<^bsup>\<pi>,v\<^esup>\<rightarrow> k\<rbrakk> \<Longrightarrow> (\<pi> k, \<pi> i) \<in> pdg\<close> 

text \<open>The set of sources is the set of nodes reading high variables.\<close>
inductive_set sources where
\<open>n \<in> nodes \<Longrightarrow> h \<in> hvars \<Longrightarrow> h \<in> reads n \<Longrightarrow> n\<in> sources\<close>

text \<open>The forward slice is the set of nodes reachable in the PDG from the set of sources.  To ensure 
security slicing aims to prove that no observable node is contained in the \<close>
inductive_set slice where
\<open>n\<in> sources \<Longrightarrow> n \<in> slice\<close> |
\<open>m \<in> slice \<Longrightarrow> (m,n)\<in>pdg \<Longrightarrow> n \<in> slice\<close>


text \<open>As the PDG does not contain data control dependencies themselves we have to decompose these.\<close>
lemma dcd_pdg: assumes \<open>n dcd\<^bsup>\<pi>,v\<^esup>\<rightarrow> m via \<pi>' m'\<close> obtains l where \<open>(\<pi> m,l)\<in> pdg\<close> and \<open>(l,\<pi> n)\<in>pdg\<close>
proof -
  assume r: \<open>(\<And>l. (\<pi> m, l) \<in> pdg \<Longrightarrow> (l, \<pi> n) \<in> pdg \<Longrightarrow> thesis)\<close>
  obtain l' n' where ln: \<open>cs\<^bsup>\<pi>\<^esup> m = cs\<^bsup>\<pi>'\<^esup> m' \<and> cs\<^bsup>\<pi>\<^esup> n = cs\<^bsup>\<pi>'\<^esup> n' \<and> n' dd\<^bsup>\<pi>',v\<^esup>\<rightarrow> l' \<and> l' cd\<^bsup>\<pi>'\<^esup>\<rightarrow> m'\<close> using assms unfolding is_dcdi_via_def by metis
  hence  mn: \<open>\<pi>' m' = \<pi> m \<and> \<pi>' n' = \<pi> n\<close> by (metis last_cs ln) 
  have 1: \<open>(\<pi> m, \<pi>' l') \<in> pdg\<close> by (metis ln mn pdg.intros(1)) 
  have 2: \<open>(\<pi>' l', \<pi> n) \<in> pdg\<close> by (metis ln mn pdg.intros(2)) 
  show thesis using 1 2 r by auto
qed

text \<open>By induction it directly follows that the slice is an approximation of the single critical paths.\<close>
lemma scp_slice: \<open>(\<pi>, i)\<in> scp \<Longrightarrow> \<pi> i \<in> slice\<close> 
  apply (induction rule: scp.induct)
     apply (simp add: path_in_nodes slice.intros(1) sources.intros)
    using pdg.intros(1) slice.intros(2) apply blast
  using pdg.intros(2) slice.intros(2) apply blast
  by (metis dcd_pdg slice.intros(2))

lemma scop_slice: \<open>(\<pi>, i) \<in> scop \<Longrightarrow> \<pi> i \<in> slice \<inter> dom(att)\<close>  by (metis IntI scop.cases scp_slice) 

text \<open>The requirement targeted by slicing, that no observable node is contained in the slice, 
is thereby a sound criteria for security.\<close>
lemma pdg_correct: assumes \<open>slice \<inter> dom(att) = {}\<close> shows \<open>secure\<close>
proof (rule ccontr)
  assume \<open>\<not> secure\<close> 
  then obtain \<pi> i where \<open>(\<pi>, i) \<in> scop\<close> using scop_correct by force 
  thus \<open>False\<close> using scop_slice assms by auto 
qed

end

end