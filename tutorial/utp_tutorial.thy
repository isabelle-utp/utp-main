section \<open> Isabelle/UTP Primer \<close>

(*<*)
theory utp_tutorial
imports "UTP-Theories.utp_theories"
begin
(*>*)

text \<open> In this section, we will introduce Hoare and He's \emph{Unifying Theories of Programming}~\cite{Hoare&98} through
  a tutorial about our mechanisation, in Isabelle, called Isabelle/UTP~\cite{Foster16a,Feliachi2010,Zeyda16}. The UTP
  is a framework for building and reasoning about heterogeneous semantics of programming and modelling languages. One of the core ideas of the UTP
  is that any program (or model) can be represented as a logical predicate over the program's state
  variables. The UTP thus begins from a higher-order logical core, and constructs a semantics for
  imperative relational programs, which can then be refined and extended with more complex language
  paradigms and theories. Isabelle/UTP mechanises this language of predicates and relations, and provides
  proof tactics for solving conjectures. For example, we can prove the following simple conjectures: \<close>

lemma "(true \<and> false) = false"
  by pred_auto

lemma "(true \<Rightarrow> P \<and> P) = P"
  by (pred_auto)

text \<open> We discharge these using our predicate calculus tactic, \emph{pred-auto}. It should be noted
  that @{term true}, @{term false}, and the conjunction operator are not simply the HOL operators;
  rather they act on on our UTP predicate type (@{typ "'\<alpha> upred"}). \<close>

subsection \<open> State-spaces and Lenses \<close>

text \<open> Predicates in the UTP are alphabetised, meaning they specify beheaviours
  in terms of a collection of variables, the alphabet, which effectively gives a state-space for
  a particular program. Thus the type of UTP predicates @{typ "'\<alpha> upred"} is parametric in the alphabet
  @{typ "'\<alpha>"}. In Isabelle/UTP we can create a particular state-space with the \textbf{alphabet} command: \<close>

alphabet myst =
  x :: "int"
  y :: "int"
  z :: "int set"

text \<open> This command creates an alphabet with three variables, $x$, $y$, and $z$, each of which
  has a defined type. A new Isabelle type is created, @{typ myst}, which can be then used
  as the parameter for our predicate model, e.g. @{typ "myst upred"}.
  In the context of our mechanisation, such variables are
  represented using \emph{lenses}~\cite{Foster16a,Foster09}. A lens, $X : V \Longrightarrow S$,
  is a pair of functions, $get :: V \to S$ and $put : S \to V \to S$, where $S$ is the source type,
  and $V$ is the view type. The source type represents a ``larger'' type that can in some sense be
  subdivided, and the view type a particular region of the source that can be observed and
  manipulated independently of the rest of the source.

  In Isabelle/UTP, the source type is the state space, and the view type is
  the variable type. For instance, we here have that @{term "x"} has type @{typ "int \<Longrightarrow> myst"}
  and @{term "z"} has type @{typ "int set \<Longrightarrow> myst"}. Thus, performing an assignment to $x$ equates
  to application of the $put$ function, and looking up the present valuation is application of the
  $get$ function.

  Since the different variable characterise different regions of the state space we can distinguish
  them using the independence predicate @{term "x \<bowtie> z"}. Two lenses are independent if they characterise
  disjoint regions of the source type. In this case we can prove that the two variables are different
  using the simplifier: \<close>

lemma "x \<bowtie> z"
  by simp

text \<open> However, we cannot prove, for example, that @{term "x \<bowtie> x"} of course since the same region
  of the state-space is characterised by both. Lenses thus provide us with a semantic characterisation
  of variables, rather than a syntactic notion. For more background on this use of lenses please see
  our recent paper~\cite{Foster16a}. \<close>

subsection \<open> Predicate Calculus \<close>

text \<open> We can now use this characterisation of variables to define predicates
  in Isabelle/UTP, for example @{term "&x >\<^sub>u &y"}, which corresponds to all valuations of the state-space
  in which $x$ is greater than $y$. Often we have to annotate our variables to help Isabelle understand
  that we are referring to UTP variables, and not, for example, HOL logical variables. In this case we
  have to decorate the names with an ampersand. Moreover, we often have to annotate operators with
  $u$ subscripts to denote that they refer to the UTP version of the operator, and not the HOL version.
  We can now write down and prove a simple proof goal: \<close>

lemma "`(&x =\<^sub>u 8 \<and> &y =\<^sub>u 5) \<Rightarrow> &x >\<^sub>u &y`"
  by (pred_auto)

text \<open> The backticks denote that we are writing an tautology. Effectively this goal tells us that
  $x = 8$ and $y = 5$ are valid valuations for the predicate. Conversely the following goal is not
  provable. \<close>

lemma "`(&x =\<^sub>u 5 \<and> &y =\<^sub>u 5) \<Rightarrow> &x >\<^sub>u &y`"
  apply (pred_simp) \<comment> \<open> Results in @{term False} \<close>
oops

text \<open> We can similarly quantify over UTP variables as the following two examples illustrate. \<close>

lemma "(\<exists> x \<bullet> &x >\<^sub>u &y) = true"
  by (pred_simp, presburger)

lemma "(\<forall> x \<bullet> &x >\<^sub>u &y) = false"
  by (pred_auto)

text \<open> The first goal states that for any given valuation of $y$ there is a valuation of $x$ which
  is greater. Predicate calculus alone is insufficient to prove this and so we can also use Isabelle's
  \emph{sledgehammer} tool~\cite{Blanchette2011} which attempts to solve the goal using an array of automated theorem provers
  and SMT solvers. In this case it finds that Isabelle's tactic for Presburger arithmetic can solve the
  goal. In this second case we have a goal which states that every valuation of $x$ is greater than
  a given valuation of $y$. Of course, this isn't the case and so we can prove the goal is equivalent
  to @{term false}. \<close>

subsection \<open> Meta-logical Operators \<close>

text \<open> In addition to predicate calculus operators, we also often need to assert meta-logical
  properties about a predicate, such as ``variable $x$ is not present in predicate $P$''. In Isabelle/UTP
  we assert this property using the \emph{unrestriction} operator, e.g. @{term "x \<sharp> true"}. Here are some
  examples of its use, including discharge using our tactic \emph{unrest-tac}. \<close>

lemma "x \<sharp> true"
  by (unrest_tac)

lemma "x \<sharp> (&y >\<^sub>u 6)"
  by (unrest_tac)

lemma "x \<sharp> (\<forall> x \<bullet> &x =\<^sub>u &y)"
  by (unrest_tac)

text \<open> The tactic attempts to prove the unrestriction using a set of built-in unrestriction laws
  that exist for every operator of the calculus. The final example is interesting, because it shows we are
  not dealing with a syntactic
  property but rather a semantic one. Typically, one would describe the (non-)presence of variables
  syntactically, by checking if the syntax tree of $P$ refers to $x$. In this case we are actually
  checking whether the valuation of $P$ depends on $x$ or not. In other words, if we can rewrite
  $P$ to a form where $x$ is not present, but $P$ is otherwise equivalent, then $x$ is unrestricted --
  it can take any value. The following example illustrates this: \<close>

lemma "x \<sharp> (&x <\<^sub>u 5 \<or> &x =\<^sub>u 5 \<or> &x >\<^sub>u 5)"
  by (pred_auto)

text \<open> Of course, if $x$ is either less than $5$, equal to $5$, or greater than $5$ then $x$ can
  take any value and the predicate will still be satisfied. Indeed this predicate is actually
  equal to @{term true} and thus @{term x} is unrestricted. We will often use unrestriction to
  encode necessary side conditions on algebraic laws of programming.

  In addition to presence of variables, we will often want to substitute a variable for an expression.
  We write this using the familiar syntax @{term "P\<lbrakk>v/x\<rbrakk>"}, and also @{term [source] "P\<lbrakk>v\<^sub>1,v\<^sub>2,v\<^sub>3/x\<^sub>1,x\<^sub>2,x\<^sub>3\<rbrakk>"} for
  an arbitrary number of expressions and variables. We can evaluate substitutions using the tactic
  \emph{subst-tac} as the following examples show:
 \<close>

lemma "(&y =\<^sub>u &x)\<lbrakk>2/x\<rbrakk> = (&y =\<^sub>u 2)"
  by (subst_tac)

lemma "(&y =\<^sub>u &x \<and> &y \<in>\<^sub>u &z)\<lbrakk>2/y\<rbrakk> = (2 =\<^sub>u &x \<and> 2 \<in>\<^sub>u &z)"
  by (subst_tac)
    
lemma "(\<exists> &x \<bullet> &x \<in>\<^sub>u &z)\<lbrakk>76/&x\<rbrakk> = (\<exists> &x \<bullet> &x \<in>\<^sub>u &z)"
  by (subst_tac)

lemma "true\<lbrakk>1,2/&x,&y\<rbrakk> = true"
  by (subst_tac)

text \<open> We can also, of course, combine substitution and predicate calculus to prove conjectures
  containing substitutions. Below, we prove a theorem in two steps, first applying the substitution,
  and then secondly utilising predicate calculus. Note the need to add the type coercion: 
  @{term "1 :\<^sub>u int"} -- this is because both 1 and 2 are polymorphic (e.g. they can also have type 
  @{typ real}), and thus explicit types must be added.  \<close>

lemma "(&x =\<^sub>u 1 \<and> &y =\<^sub>u &x)\<lbrakk>2/x\<rbrakk> = false" (is "?lhs = ?rhs")
proof -
  have "?lhs = (2 =\<^sub>u (1 :\<^sub>u int) \<and> &y =\<^sub>u 2)"
    by (subst_tac)
  also have "... = ?rhs"
    by (pred_auto)
  finally show ?thesis .
qed

text \<open> Isabelle/UTP also supports a more general notation for substitutions, where-by variable
  maplets can be considered as explicit objects that correspond to functions on the state-space. 
  For example, @{term "[&x \<mapsto>\<^sub>s 1, &y \<mapsto>\<^sub>s 2]"} is a substitution that replaces $x$ with 1 and $y$
  with 2. Such substitution functions ($\sigma$) can be applied to an expression or predicate using 
  the dagger operator: @{term "\<sigma> \<dagger> P"}. Thus, we can perform the following simplification: \<close>
  
lemma "[&x \<mapsto>\<^sub>s 1, &y \<mapsto>\<^sub>s 2] \<dagger> (&x <\<^sub>u &y) = ((1 :\<^sub>u int) <\<^sub>u 2)"
  by (subst_tac)
  
text \<open> This notation thus allows us to deal with state space much more flexibly. The more standard 
  notation @{term "P\<lbrakk>v/x\<rbrakk>"} is in fact syntactic sugar to application of the singleton substitution
  function @{term "[x \<mapsto>\<^sub>s v]"}.
    
  So far, we have considered UTP predicates which contain only UTP variables. However it is
  possible to have another kind of variable -- a logical HOL variable which is sometimes known
  as a ``logical constant''~\cite{Morgan90}. Such variables are not program or model variables,
  but they simply exist to assert logical properties of a predicate. The next two examples compare UTP and HOL
  variables in a quantification. \<close>

lemma "(\<forall> x \<bullet> &x =\<^sub>u &x) = true"
  by (pred_auto)

lemma "(\<^bold>\<forall> x \<bullet> \<guillemotleft>x\<guillemotright> =\<^sub>u \<guillemotleft>x\<guillemotright>) = true"
  by (pred_auto)

text \<open> The first quantification is a quantification of a UTP variable, which we've already encountered.
  The second is a quantifier over a HOL variable, denoted by the quantifier being bold. In addition
  we refer to HOL variables, not using the ampersand, but the quotes @{term "\<guillemotleft>k\<guillemotright>"}. These quotes
  allow us to insert an arbitrary HOL term into a UTP expression, such as a logical variable. \<close>

subsection \<open> Relations \<close>

text \<open> Relations, @{typ "('\<alpha>, '\<beta>) urel"}, are a class of predicate in which the state space is a product
  -- i.e. @{typ "('\<alpha> \<times> '\<beta>) upred"} -- and divides the variables into input or ``before'' variables
  and output or ``after'' variables. In Isabelle/UTP we can write down a relational variable using
  the dollar notation, as illustrated below: \<close>

term "($x\<acute> =\<^sub>u 1 \<and> $y\<acute> =\<^sub>u $y \<and> $z\<acute> =\<^sub>u $z) :: myst hrel"

text \<open> Type @{typ "'\<alpha> hrel"} is the type of homogeneous relations, which have the same before and
  after state. This example relation can be intuitively thought of as the relation which sets
  $x$ to $1$ and leaves the other two variables unchanged. We would normally refer to this as
  an assignment of course, and for convenience we can write such a predicate using a more
  convenient syntax, @{term "x := 1"}, which is equivalent: \<close>

lemma "(x := 1) = (($x\<acute> =\<^sub>u 1 \<and> $y\<acute> =\<^sub>u $y \<and> $z\<acute> =\<^sub>u $z) :: myst hrel)"
  by (rel_auto)

text \<open> Since we are now in the world of relations, we have an additional tactic called \emph{rel-auto}
  that solves conjectures in relational calculus. We can use relational variables to write to
  loose specifications for programs, and then prove that a given program is a refinement. Refinement
  is an order on programs that allows us to assert that a program refines a given specification,
  for example: \<close>

lemma "($x\<acute> >\<^sub>u $y) \<sqsubseteq> (x, y := &y + 3, 5)"
  by (rel_auto)

text \<open> This tells us that the specification that the after value of $x$ must be greater than the initial
  value of $y$, is refined by the program which adds $3$ to $y$ and assigns this to $x$, and
  simultaneously assigns $5$ to $y$. Of course, this is not the only refinement, but an interesting
  one. A refinement conjecture @{term "P \<sqsubseteq> Q"} in general asserts that @{term "Q"} is more deterministic
  than @{term "P"}. In addition to assignments, we can also construct relational specifications and programs
  using sequential (or relational) composition: \<close>

lemma "x := 1 ;; x := (&x + 1) = x := 2"
  by (rel_auto)

text \<open> Internally, what is happening here is quite subtle, so we can also prove this law in the Isar
  proof scripting language which allows us to further expose the details of the argument. In this
  proof we will make use of both the tactic and already proven laws of programming from Isabelle/UTP. \<close>

lemma "x := 1 ;; x := (&x + 1) = x := 2"
proof -
  \<comment> \<open> We first show that a relational composition of an assignment and some program $P$ corresponds
        to substitution of the assignment into $P$, which is proved using the law
        @{thm [source] "assigns_r_comp"}. \<close>
  have "x := 1 ;; x := (&x + 1) = (x := (&x + 1))\<lbrakk>1/$x\<rbrakk>"
    by (simp add: assigns_r_comp alpha usubst)
  \<comment> \<open> Next we execute the substitution using the relational calculus tactic. \<close>
  also have "... = x := (1 + 1)"
    by (rel_auto)
  \<comment> \<open> Finally by evaluation of the expression, we obtain the desired result of $2$. \<close>
  also have "... = x := 2"
    by (simp)
  finally show ?thesis .
qed

text \<open> UTP also gives us an if-then-else conditional construct, written @{term "P \<triangleleft> b \<triangleright> Q"}, which
  is a more concise way of writing $\textbf{if}~b~\textbf{then}~P~\textbf{else}~Q$. It also allows
  the expression of while loops, which gives us a simple imperative programming language. \<close>

lemma "(x := 1 ;; (y := 7 \<triangleleft> $x >\<^sub>u 0 \<triangleright> y := 8)) = (x,y) := (1,7)"
  by (rel_auto)

text \<open> Below is an illustration of how we can express a simple while loop in Isabelle/UTP. \<close>

term "(x,y) := (3,1);; while &x >\<^sub>u 0 do x := (&x - 1);; y := (&y * 2) od"

subsection \<open> Non-determinism and Complete Lattices \<close>

text \<open> So far we have considered only deterministic programming operators. However, one of the
  key feature of the UTP is that it allows non-deterministic specifications. Determinism is
  ordered by the refinement order @{term "P \<sqsubseteq> Q"}, which states that $P$ is more deterministic
  that $Q$, or alternatively that $Q$ makes fewer commitments than $P$. The refinement order
  @{term "P \<sqsubseteq> Q"} corresponds to a universally closed implication @{term "Q \<Rightarrow> P"}. The most
  deterministic specification is @{term "false"}, which also corresponds to a miraculous program,
  and the least is @{term "true"}, as the following theorems demonstrate. \<close>

theorem false_greatest: "P \<sqsubseteq> false"
  by (rel_auto)

theorem true_least: "true \<sqsubseteq> P"
  by (rel_auto)

text \<open> In this context @{term true} corresponds to a programmer error, such as an aborting or
  non-terminating program (the theory of relations does not distinguish these). We can similarly
  specify a non-deterministic choice between $P$ and $Q$ with
  @{term "P \<sqinter> Q"}, or alternatively @{term "\<Sqinter> A"} where $A$ is a set of possible behaviours.
  Predicate @{term "P \<sqinter> Q"} encapsulates the behaviours of both $P$ and $Q$, and is thus
  refined by both. We can also prove a variety of theorems about non-deterministic choice. \<close>

theorem Choice_equiv:
  fixes P Q :: "'\<alpha> upred"
  shows "\<Sqinter> {P, Q} = P \<sqinter> Q"
  by simp

text \<open> Theorem @{thm [source] Choice_equiv} shows the relationship between the big choice operator
  and its binary equivalent. The latter is simply a choice over a set with two elements. \<close>

theorem Choice_refine:
  fixes A B :: "'\<alpha> upred set"
  assumes "B \<subseteq> A"
  shows "\<Sqinter> A \<sqsubseteq> \<Sqinter> B"
  by (simp add: Sup_subset_mono assms)

text \<open> The intuition of theorem @{thm [source] Choice_refine} is that a specification with more
  options is refined by one with less options. We can also prove a number of theorems about
  the binary version of the operator. \<close>

theorem choice_thms:
  fixes P Q :: "'\<alpha> upred"
  shows
    "P \<sqinter> P = P"
    "P \<sqinter> Q = Q \<sqinter> P"
    "(P \<sqinter> Q) \<sqinter> R = P \<sqinter> (Q \<sqinter> R)"
    "P \<sqinter> true = true"
    "P \<sqinter> false = P"
    "P \<sqinter> Q \<sqsubseteq> P"
  by (simp_all add: lattice_class.inf_sup_aci true_upred_def false_upred_def)

text \<open> Non-deterministic choice is idempotent, meaning that a choice between $P$ and $P$ is no choice. It
  is also commutative and associative. If we make a choice between @{term "P"} and @{term "true"} then
  the erroneous behaviour signified by the latter is always chosen. Thus our operator is a so-called
  ``demonic choice'' since the worst possibility is always picked. Similarly, if a choice is made between
  @{term "P"} and a miracle (@{term "false"}) then @{term "P"} is always chosen in order to avoid miracles.
  Finally, the choice between @{term "P"} and @{term "Q"} can always be refined by removing one of the
  possibilities.

  Since predicates form a complete lattice, then by the Knaster-Tarski theorem the set of fixed points
  of a monotone function @{term "F"} is also a complete lattice. In particular, this complete lattice
  has a weakest and strongest element which can be calculated using the notations @{term "\<mu> X \<bullet> F(X)"}
  and @{term "\<nu> X \<bullet> F(X)"}, respectively. Such fixed point constructions are of particular use for
  expressing recursive and iterative constructions. Isabelle/HOL provides a number of laws for reasoning
  about fixed points, a few of which are detailed below.
\<close>

theorem mu_id: "(\<mu> X \<bullet> X) = true"
  by (simp add: mu_id)

theorem nu_id: "(\<nu> X \<bullet> X) = false"
  by (simp add: nu_id)

theorem mu_unfold: "mono F \<Longrightarrow> (\<mu> X \<bullet> F(X)) = F(\<mu> X \<bullet> F(X))"
  by (simp add: def_gfp_unfold)

theorem nu_unfold: "mono F \<Longrightarrow> (\<nu> X \<bullet> F(X)) = F(\<nu> X \<bullet> F(X))"
  by (simp add: def_lfp_unfold)

text \<open> Perhaps of most interest are the unfold laws, also known as the ``copy rule'', that allows
  the function body $F$ of the fixed point equation to be expanded once. These state that, provided
  that the body of the fixed point is a monotone function, then the body can be copied to the outside.
  These can be used to prove equivalent laws for operators like the while loop. \<close>

subsection \<open> Laws of Programming \<close>

text \<open> Although we have some primitive tactics for proving conjectures in the predicate and relational
  calculi, in order to build verification tools for programs we need a set of algebraic ``laws of
  programming''~\cite{Hoare87} that describe important theoretical properties of the operators.
  Isabelle/UTP contains several hundred examples of such laws, and we here outline a few of them. \<close>

theorem seq_assoc: "(P ;; Q) ;; R = P ;; (Q ;; R)"
  by (rel_auto)

theorem seq_unit:
  "P ;; II = P"
  "II ;; P = P"
  by (rel_auto)+

theorem seq_zero:
  "P ;; false = false"
  "false ;; P = false"
  by (rel_auto)+

text \<open> Sequential composition is associative, has the operator @{term "II"} as its left and
  right unit, and @{term "false"} as its left and right zeros. The @{term "II"} operator is a form
  of assignment which simply identifies all the variables between the before and after state,
  as the following example demonstrates. \<close>

lemma "x := &x = II"
  by (rel_auto)

text \<open> In the context of relations, @{term "false"} denotes the empty relation, and is usually
  used to represent a miraculous program. This is intuition of it being a left and right zero:
  if a miracle occurred then the whole of the program collapses. The conditional @{term "P \<triangleleft> b \<triangleright> Q"}
  also has a number of algebraic laws that we can prove. \<close>

theorem cond_true: "P \<triangleleft> true \<triangleright> Q = P"
  by (rel_auto)

theorem cond_false: "P \<triangleleft> false \<triangleright> Q = Q"
  by (rel_auto)

theorem cond_commute: "(P \<triangleleft> \<not> b \<triangleright> Q) = (Q \<triangleleft> b \<triangleright> P)"
  by (rel_auto)

theorem cond_shadow: "(P \<triangleleft> b \<triangleright> Q) \<triangleleft> b \<triangleright> R = P \<triangleleft> b \<triangleright> R"
  by (rel_auto)

text \<open> A conditional with @{term true} or @{term false} as its condition presents no choice.
  A conditional can also be commuted by negating the condition. Finally, a conditional within
  a conditional over the same condition, @{term b}, presents and unreachable branch. Thus the
  inner branch can be pruned away. We next prove some useful laws about assignment: \<close>

theorem assign_commute:
  assumes "x \<bowtie> y" "y \<sharp> e" "x \<sharp> f"
  shows "x := e;; y := f = y := f ;; x := e"
  using assms by (rel_auto)

theorem assign_twice:
  shows "x := \<guillemotleft>e\<guillemotright>;; x := \<guillemotleft>f\<guillemotright> = x := \<guillemotleft>f\<guillemotright>"
  by (rel_auto)

theorem assign_null:
  assumes "x \<bowtie> y"
  shows "(x, y) := (e, &y) = x := e"
  using assms by (rel_auto)

text \<open> Assignments can commute provided that the two variables are independent, and the expressions
  being assigned do not depend on the variable of the other assignment. A sequence of assignments
  to the same variable is equal to the second assignment, provided that the two expressions are
  both literals, i.e. @{term "\<guillemotleft>e\<guillemotright>"}. Finally, in a multiple assignment, if one of the variables
  is assigned to itself then this can be hidden, provided the two variables are independent. \<close>


text \<open>
  Since alphabetised relations form a complete lattice, we can denote iterative constructions like
  the while loop which is defined as @{term "while\<^sub>\<bottom> b do P od = (\<mu> X \<bullet> (P ;; X) \<triangleleft> b \<triangleright>\<^sub>r II)"}. We can
  then prove some common laws about iteration. \<close>

theorem while_false: "while\<^sub>\<bottom> false do P od = II"
  by (simp add: while_bot_false)

theorem while_unfold: "while\<^sub>\<bottom> b do P od = (P ;; while\<^sub>\<bottom> b do P od) \<triangleleft> b \<triangleright>\<^sub>r II"
  using while_bot_unfold by blast

text \<open> As we have seen, the predicate @{term "true"} represents the erroneous program. For loops, we
  have it that a non-terminating program equates to @{term true}, as the following example demonstrates. \<close>

lemma "while\<^sub>\<bottom> true do x := (&x + 1) od = true"
  by (simp add: assigns_r_feasible while_infinite)

text \<open> A program should not be able to recover from non-termination, of course, and therefore it
  ought to be the case that @{term true} is a left zero for sequential composition:
  @{term "true ;; P = true"}. However this is not the case as the following examples illustrate: \<close>

lemma "true ;; P = true"
  apply (rel_simp)
  nitpick \<comment> \<open> Counterexample found \<close>
oops

lemma "true ;; (x,y,z) := (\<guillemotleft>c\<^sub>1\<guillemotright>,\<guillemotleft>c\<^sub>2\<guillemotright>,\<guillemotleft>c\<^sub>3\<guillemotright>) = ((x,y,z) := (\<guillemotleft>c\<^sub>1\<guillemotright>,\<guillemotleft>c\<^sub>2\<guillemotright>,\<guillemotleft>c\<^sub>3\<guillemotright>) :: myst hrel)"
  by (rel_auto)

text \<open> The latter gives an example of a relation for which @{term true} is actually a left unit
  rather than a left zero. The assignment @{term "x,y,z := \<guillemotleft>c\<^sub>1\<guillemotright>,\<guillemotleft>c\<^sub>2\<guillemotright>,\<guillemotleft>c\<^sub>3\<guillemotright>"} does not depend
  on any before variables, and thus it is insensitive to a non-terminating program preceding it.
  Thus we can see that the theory of relations alone is insufficient to handle non-termination. \<close>

subsection \<open> Designs \<close>

text \<open> Though we now have a theory of UTP relations with which can form simple programs, as we have seen
  this theory experiences some problems. A UTP design, @{term "P \<turnstile>\<^sub>r Q"}, is a relational specification
  in terms of assumption $P$ and commitment $Q$. Such a construction states that, if $P$ holds and
  the program is allowed to execute, then the program will terminate and satisfy its commitment $Q$. If
  $P$ is not satisfied then the program will abort yielding the predicate @{term true}. For example the design
  @{term "($x \<noteq>\<^sub>u 0) \<turnstile>\<^sub>r (y := (&y div &x))"} represents a program which, assuming that $x \neq 0$ assigns
  $y$ divided by $x$ to $y$.
\<close>

lemma dex1: "(true \<turnstile>\<^sub>r (x,y) := (2,6)) ;; (($x \<noteq>\<^sub>u 0) \<turnstile>\<^sub>r (y := (&y div &x))) = true \<turnstile>\<^sub>r x,y := 2,3"
  by (rel_auto, fastforce+)

lemma dex2: "(true \<turnstile>\<^sub>r (x,y) := (0,4)) ;; (($x \<noteq>\<^sub>u 0) \<turnstile>\<^sub>r y := (&y div &x)) = true"
  by (rel_blast)

text \<open> The first example shows the result of pre-composing this design with another design that
  has a @{term true} assumption, and assigns 2 and 6 to $x$ and $y$ respectively. Since $x$ satisfies
  $x \neq 0$, then the design executes and changes $y$ to $3$. In the second example 0 is assigned to $x$,
  which leads to the design aborting. Unlike with relations, designs do have @{term true} as a left zero: \<close>

theorem design_left_zero: "true ;; (P \<turnstile>\<^sub>r Q) = true"
  by (simp add: H1_left_zero H1_rdesign Healthy_def)

text \<open> Thus designs allow us to properly handle programmer error, such as non-termination.

  The design turnstile is defined using two observational variables $ok, ok' : \mathbb{B}$,
  which are used to represent whether a program has been  ($ok$) and whether it has
  terminated ($ok'$). Specifically, a design @{term "P \<turnstile> Q"} is defined as
  $(ok \wedge P) \Rightarrow (ok' \wedge Q)$. This means that if the program was started ($ok$) and
  satisfied its assumption ($P$), then it will terminate ($ok'$) and satisfy its commitment ($Q$).
  For more on the theory of designs please see the associated tutorial~\cite{Cavalcanti&06}. \<close>

subsection \<open> Reactive Designs \<close>

text \<open> A reactive design, @{term "\<^bold>R\<^sub>s(P \<turnstile> Q)"}, is a specialised form of design which is reactive
  in nature. Whereas designs represents programs that start and terminate, reactive designs also
  have intermediate ``waiting'' states. In such a state the reactive design is waiting for something
  external to occur before it can continue, such as receiving a message or waiting for sufficient time
  to pass as measured by a clock. When waiting, a reactive design has not terminated, but neither is
  it an infinite loop or some other error state.

  Reactive designs have two additional pair of observational variables:

  \begin{itemize}
    \item $wait, wait' : \mathbb{B}$ -- denote whether the predecessor is in a waiting state, and
      whether the current program is a waiting state;
    \item $tr, tr' : \mathcal{T}$ -- denotes the interaction history using a suitable trace type
      $\mathcal{T}$.
  \end{itemize}

 For more details on reactive designs please see the associated tutorial~\cite{Cavalcanti&06}. \<close>
(*<*)
end
(*>*)