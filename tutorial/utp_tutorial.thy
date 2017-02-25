section {* Isabelle/UTP Primer *}

(*<*)
theory utp_tutorial
  imports "../utp/utp"
begin
(*>*)
  
text {* In this section we will introduce Hoare and He's \emph{Unifying Theories of Programming} through
  a tutorial about our mechanisation, in Isabelle, called Isabelle/UTP. The UTP is a framework for building and reasoning
  about heterogeneous semantics of programming and modelling languages. One of the core ideas of the UTP
  is that any program (or model) can be represented as a logical predicate over the program's state
  variables. The UTP thus begins from a higher-order logical core, and constructs a semantics for
  imperative relational programs, which can then be refined and extended with more complex language
  paradigms and theories. Isabelle/UTP mechanises this language of predicates and relations, and provides
  proof tactics for solving conjectures. For example, we can prove the following simple conjecture: *}

lemma "(true \<and> false) = false"
  by pred_auto
  
text {* We discharge this using our predicate calculus tactic, \emph{pred-auto}. It should be noted 
  that @{term true}, @{term false}, and the conjunction operator are not simply the HOL operators; 
  rather they act on on our UTP predicate type. *}
    
subsection {* State-spaces and lenses *}

text {* Predicates in the UTP are alphabetised, meaning they specify beheaviours
  in terms of a collection of variables, the alphabet, which effectively gives a state-space for
  a particular program. Thus the type of UTP predicates @{typ "'\<alpha> upred"} is parametric in the alphabet
  @{typ "'\<alpha>"}. In Isabelle/UTP we can create a particular state-space with the alphabet command: *}
  
alphabet myst =
  x :: "int"
  y :: "int"
  z :: "int set"
  
text {* This command creates an alphabet with three variables, $x$, $y$, and $z$, each of which
  has a defined type. A new Isabelle type is created, @{typ myst}, which can be then used
  as the parameter for our predicate model, e.g. @{typ "myst upred"}. 
  In the context of our mechanisation, such variables are 
  represented using \emph{lenses}. A lens, $X : V \Longrightarrow S$, is a pair of functions, 
  $get :: V \to S$ and $put : S \to V \to S$, where $S$ is the source type, and $V$ is the view type. 
  The source type represents a larger type, and view type a particular region of the source that 
  can be observed and manipulated independently of
  the rest of the source. In Isabelle/UTP, the source type is the state space, and the view type is
  the variable type. For instance, we here have that @{term "x"} has type @{typ "int \<Longrightarrow> myst"}
  and @{term "z"} has type @{typ "int set \<Longrightarrow> myst"}. Since the different variable characterise
  different regions of the state space we can distinguish them using the independence predicate
  @{term "x \<bowtie> z"}. In this case we can prove that the two variables are different using the simplifier: *}

lemma "x \<bowtie> z"
  by simp

text {* However, we cannot prove, for example, that @{term "x \<bowtie> x"} of course since the same region
  of the state-space is characterised by both. *}

subsection {* Predicate calculus *}

  text {* We can now use these variables to define predicates
  in Isabelle/UTP, for example @{term "&x >\<^sub>u &y"}, which corresponds to all valuations of the state-space
  in which $x$ is greater than $y$. Often we have to annotate our variable to help Isabelle understand
  that we are referring to UTP variables, and not, for example, HOL logical variables. In this case we
  have to decorate with an ampersand. Moreover, we often have to annotate operators with $u$ subscripts
  to denote that they refer to the UTP version of the operator, and not the HOL version. We can now
  write down and prove a simple proof goal: *}
  
lemma "`(&x =\<^sub>u 8 \<and> &y =\<^sub>u 5) \<Rightarrow> &x >\<^sub>u &y`"
  by (pred_auto)

text {* The backticks denote that we are writing an tautology. Effectively this goal tells us that
  $x = 8$ and $y = 5$ are valid valuations for the predicate. Conversely the following goal is not
  provable. *}
  
lemma "`(&x =\<^sub>u 5 \<and> &y =\<^sub>u 5) \<Rightarrow> &x >\<^sub>u &y`"
  apply (pred_auto) -- {* Results in @{term False} *}
oops 
    
text {* We can similarly quantify over UTP variables as the following two examples illustrate. *}
  
lemma "(\<exists> x \<bullet> &x >\<^sub>u &y) = true"
  by (pred_auto, presburger)

lemma "(\<forall> x \<bullet> &x >\<^sub>u &y) = false"
  by (pred_auto)

text {* The first goal states that for any given valuation of $y$ there is a valuation of $x$ which
  is greater. Predicate calculus alone is insufficient to prove this and so we can also use Isabelle's
  \emph{sledgehammer} tool which attempts to solve the goal using an array of automated theorem provers
  and SMT solvers. In this case it finds that Isabelle's tactic for Presburger arithmetic can solve the 
  goal. In this second case we have a goal which states that every valuation of $x$ is greater than
  a given valuation of $y$. Of course, this isn't the case and so we can prove the goal is equivalent
  to @{term false}. *}
  
subsection {* Meta-logical operators *}
  
text {* In addition to predicate calculus operators, we also often need to assert meta-logical
  properties about a predicate, such as ``variable $x$ is not present in predicate $P$''. In Isabelle/UTP
  we assert this property using the unrestriction operator, e.g. @{term "x \<sharp> true"}. Here are some
  examples of its use, including discharge using our tactic \emph{unrest-tac}. *}

lemma "x \<sharp> true"
  by (unrest_tac)

lemma "x \<sharp> (&y >\<^sub>u 6)"
  by (unrest_tac)
  
lemma "x \<sharp> (\<forall> x \<bullet> &x =\<^sub>u &y)"
  by (unrest_tac)
    
text {* The tactic attempts to prove the unrestriction using a set of built-in unrestriction laws
  that exist for every operator of the calculus. The final example is interesting, because it shows we are not dealing with a syntactic 
  property but rather a semantic one. Typically one would describe the (non-)presence of variables 
  syntactically, by checking if the syntax tree of $P$ refers to $x$. In this case we are actually
  checking whether the valuation of $P$ depends on $x$ or not not. In other words, if we can rewrite
  $P$ to a form where $x$ is not present, but $P$ is otherwise equivalent, then $x$ is unrestricted -- 
  it can take any value. The following example illustrates this: *}
    
lemma "x \<sharp> (&x <\<^sub>u 5 \<or> &x =\<^sub>u 5 \<or> &x >\<^sub>u 5)"
  by (pred_auto)
    
text {* Of course, if $x$ is either less than $5$, equal to $5$, or greater than $5$ then $x$ can
  take any value and the predicate will still be satisfied. Indeed this predicate is actually
  equal to @{term true} and thus @{term x} is unrestricted. We will often use unrestriction to
  encode necessary side conditions on algebraic laws of programming.

  In addition to presence of variables, we will often want to substitute a variable for an expression.
  We write this using the familiar syntax @{term "P\<lbrakk>v/x\<rbrakk>"}, and also @{term "P\<lbrakk>v\<^sub>1,v\<^sub>2,v\<^sub>3/x\<^sub>1,x\<^sub>2,x\<^sub>3\<rbrakk>"} for
  an arbitrary number of expressions and variables. We can evaluate substitutions using the tactic
  \emph{subst-tac} as the following examples show:
 *}

lemma "(&y =\<^sub>u &x)\<lbrakk>2/x\<rbrakk> = (&y =\<^sub>u 2)"
  by (subst_tac)
    
lemma "(&y =\<^sub>u &x \<and> &y \<in>\<^sub>u &z)\<lbrakk>2/y\<rbrakk> = (2 =\<^sub>u &x \<and> 2 \<in>\<^sub>u &z)"
  by (subst_tac)
    
lemma "(\<exists> &x \<bullet> &x \<in>\<^sub>u &z)\<lbrakk>76/&x\<rbrakk> = (\<exists> &x \<bullet> &x \<in>\<^sub>u &z)"
  by (subst_tac)
    
lemma "true\<lbrakk>1,2/&x,&y\<rbrakk> = true"
  by (subst_tac)

text {* We can also, of course, combine substitution and predicate calculus to prove conjectures
  containing substitutions. *}
    
lemma "(&x =\<^sub>u 1 \<and> &y =\<^sub>u &x)\<lbrakk>2/x\<rbrakk> = false"
  apply (subst_tac)
  apply (pred_auto)
done
    
text {* So far, we have considered UTP predicates which contain only UTP variables. However it is
  possible to have another kind of variable -- a logical HOL variable which is sometimes known
  as a ``logical constant''. Such variables are not program or model variables, but they simply
  exist to assert logical properties of a predicate. The next two examples compare UTP and HOL
  variables in a quantification. *}

lemma "(\<forall> x \<bullet> &x =\<^sub>u &x) = true"
  by (pred_auto)

lemma "(\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> =\<^sub>u \<guillemotleft>x\<guillemotright>) = true"
  by (pred_auto)
  
text {* The first quantification is a quantification of a UTP variable, which we've already encountered.
  The second is a quantifier over a HOL variable, denoted by the quantifier being bold. In addition
  we refer to HOL variables, not using the ampersand, but the quotes @{term "\<guillemotleft>k\<guillemotright>"}. These quotes
  allow us to insert an arbitrary HOL term into a UTP expression, such as a logical variable. *}
    
subsection {* Relations *}
  
text {* Relations, @{typ "('\<alpha>, '\<beta>) rel"}, are a class of predicate in which the state space is a product 
  -- i.e. @{typ "('\<alpha> \<times> '\<beta>) upred"} -- and divides the variables into input or ``before'' variables
  and output or ``after'' variables. In Isabelle/UTP we can write down a relational variable using
  the dollar notation, as illustrated below: *}
  
term "($x\<acute> =\<^sub>u 1 \<and> $y\<acute> =\<^sub>u $y \<and> $z\<acute> =\<^sub>u $z) :: myst hrel"
  
text {* Type @{typ "'\<alpha> hrel"} is the type of homogeneous relations, which have the same before and
  after state. This example relation can be intuitively thought of as the relation which sets
  $x$ to $1$ and leaves the other two variables unchanged. We would normally refer to this as
  an assignment of course, and for convenience we can write such a predicate using a more
  convenient syntax, @{term "x := 1"}, which is equivalent: *}
  
lemma "(x := 1) = (($x\<acute> =\<^sub>u 1 \<and> $y\<acute> =\<^sub>u $y \<and> $z\<acute> =\<^sub>u $z) :: myst hrel)"
  by (rel_auto)
  
text {* Since we are now in the world of relations, we have an additional tactic called \emph{rel-auto}
  that solves conjectures in relational calculus. We can use relational variables to write to
  loose specifications for programs, and then prove that a given program is a refinement. For example: *}
  
lemma "($x\<acute> >\<^sub>u $y) \<sqsubseteq> (x, y := &y + 3, 5)"
  by (rel_auto)
   
text {* This tells us that the specification that the after value of $x$ must be greater than the initial
  value of $y$, is refined by the program which adds $3$ to $y$ and assigns this to $x$, and 
  simultaneously assigns $5$ to $y$. Of course this is not the only refinement, but an interesting
  one. In addition to assignments, we can also construct relational specifications and programs using 
  sequential (or relational) composition: *}
    
lemma "(x := 1 ;; x := &x + 1) = (x := 2)"
  by (rel_auto)

text {* Internally what is happening here is quite subtle, so we can also prove this laws in the Isar
  proof scripting language which allows us to further expose the details of the argument. In this
  proof we will make use of both the tactic and already proven laws of programming from Isabelle/UTP. *}
    
lemma "(x := 1 ;; x := &x + 1) = (x := 2)"
proof -
  -- {* We first show that a relational composition of an assignment and some program $P$ corresponds
        to substitution of the assignment into $P$, which is proved using the law 
        @{thm [source] "assigns_r_comp"}. *}
  have "(x := 1 ;; x := &x + 1) = (x := &x + 1)\<lbrakk>1/$x\<rbrakk>"
    by (simp add: assigns_r_comp alpha)
  -- {* Next we execute the substitution using the relational calculus tactic. *}
  also have "... = x := 1 + 1" 
    by (rel_auto)
  -- {* Finally by evaluation of the expression, we obtain the desired result of $2$. *}
  also have "... = x := 2"
    by (simp)
  finally show ?thesis .
qed

text {* UTP also gives us an if-then-else conditional construct, written @{term "P \<triangleleft> b \<triangleright> Q"}, which
  is a more concise way of writing $\textbf{if}~b~\textbf{then}~P~\textbf{else}~Q$. *}

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y := 1,7)"
  by (rel_auto)

(*<*)
end
(*>*)
