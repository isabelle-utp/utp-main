section \<open> Refusal Tests \<close>

theory Refusal_Tests
  imports Main
  "../../toolkit/Terminated_lists"
  "Failures"
begin

subsection \<open> Refusal Sets \<close>

datatype 'e refusal = rfnil ("\<bullet>") | rfset "'e set" ("[_]\<^sub>\<R>")

instantiation refusal :: (type) order
begin
  fun less_eq_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" where
  "\<bullet> \<le> S = True" |
  "R \<le> \<bullet> = (R = \<bullet>)" |
  "[X]\<^sub>\<R> \<le> [Y]\<^sub>\<R> = (X \<subseteq> Y)"
  definition less_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" where
  "less_refusal S R = (S \<le> R \<and> \<not> R \<le> S)"
instance proof
  fix x y z :: "'a refusal"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_refusal_def)
  show "x \<le> x"
    by (cases x, simp_all)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis Refusal_Tests.less_eq_refusal.elims(2) dual_order.antisym less_eq_refusal.simps(2) refusal.inject)
qed

end

abbreviation rsubseteq :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> bool" ("(_/ \<subseteq>\<^sub>\<R> _)" [51, 51] 50) where 
"S \<subseteq>\<^sub>\<R> R \<equiv> S \<le> R"

fun rmember :: "'a \<Rightarrow> 'a refusal \<Rightarrow> bool" ("(_/ \<in>\<^sub>\<R> _)" [51, 51] 50) where
"x \<in>\<^sub>\<R> \<bullet> = False" | "x \<in>\<^sub>\<R> [R]\<^sub>\<R> = (x \<in> R)"

abbreviation rnot_member ("(_/ \<notin>\<^sub>\<R> _)" [51, 51] 50)
  where "rnot_member x A \<equiv> \<not> (x \<in>\<^sub>\<R>  A)"

instantiation refusal :: (type) lattice
begin
  fun sup_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal"  where
  "sup \<bullet> R = R" |
  "sup S \<bullet> = S" |
  "sup [S]\<^sub>\<R> [R]\<^sub>\<R> = [S \<union> R]\<^sub>\<R>"

  fun inf_refusal :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal"  where
  "inf \<bullet> R = \<bullet>" |
  "inf S \<bullet> = \<bullet>" |
  "inf [S]\<^sub>\<R> [R]\<^sub>\<R> = [S \<inter> R]\<^sub>\<R>"
instance proof
  fix x y z :: "'a refusal"
  show "inf x y \<subseteq>\<^sub>\<R> x"
    by (cases x, simp_all, cases y, simp_all)
  show "inf x y \<subseteq>\<^sub>\<R> y"
    by (cases x, simp_all, cases y, simp_all)
  show "x \<subseteq>\<^sub>\<R> y \<Longrightarrow> x \<subseteq>\<^sub>\<R> z \<Longrightarrow> x \<subseteq>\<^sub>\<R> inf y z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
  show "x \<subseteq>\<^sub>\<R> sup x y"
    by (cases x, simp_all, cases y, simp_all)
  show "y \<subseteq>\<^sub>\<R> sup x y"
    by (cases x, simp_all, cases y, simp_all)
  show "y \<subseteq>\<^sub>\<R> x \<Longrightarrow> z \<subseteq>\<^sub>\<R> x \<Longrightarrow> sup y z \<subseteq>\<^sub>\<R> x"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all, cases y, simp_all, cases y, simp_all)
qed
end

abbreviation runion :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal"  (infixl "\<union>\<^sub>\<R>" 65)
  where "runion \<equiv> Lattices.sup"

abbreviation rinter :: "'a refusal \<Rightarrow> 'a refusal \<Rightarrow> 'a refusal"  (infixl "\<inter>\<^sub>\<R>" 70)
  where "rinter \<equiv> Lattices.inf"

subsection \<open> Refusal Events \<close>

text \<open> The following type embodies the notion of Cavalcanti et al.'s RT model 
       where an event @{term a} cannot follow a set which refuses @{term a}. 
       Observe that in RT-model presented in UCS this is not enforced. \<close>

typedef 'e revent = "{(X :: 'e refusal, a :: 'e). a \<notin>\<^sub>\<R> X}"
  by (rule_tac x="(\<bullet>, undefined)" in exI, simp)

syntax
  "_revent"     :: "args \<Rightarrow> 'e \<Rightarrow> 'e revent"    ("'(_,_')\<^sub>\<R>")

translations
  "(x,y)\<^sub>\<R>" == "CONST Abs_revent (x,y)"

setup_lifting type_definition_revent

lift_definition rrefusal :: "'e revent \<Rightarrow> 'e refusal" is fst .
lift_definition revent   :: "'e revent \<Rightarrow> 'e" is snd .

lemma revent_notin_refusal [simp]:
  "revent a \<notin>\<^sub>\<R> rrefusal a"
  by (metis Rep_revent mem_Collect_eq prod.case_eq_if revent.rep_eq rrefusal.rep_eq)

lemma rrefusal_revent [simp]: "b \<notin>\<^sub>\<R> a \<Longrightarrow> rrefusal (a,b)\<^sub>\<R> = a"
  by (auto simp add:rrefusal_def Abs_revent_inverse)

lemma revent_revent [simp]: "b \<notin>\<^sub>\<R> a \<Longrightarrow> revent (a,b)\<^sub>\<R> = b"
  by (auto simp add:revent_def Abs_revent_inverse)

lemma rrefusal_revent_pair [simp]: "rrefusal (rrefusal a, revent a)\<^sub>\<R> = rrefusal a"
  apply (auto simp add:rrefusal_def Abs_revent_inverse)
  by (simp add: Rep_revent_inverse revent.rep_eq)

lemma revent_revent_pair [simp]: "revent (rrefusal a, revent a)\<^sub>\<R> = revent a"
  apply (auto simp add:rrefusal_def Abs_revent_inverse)
  by (simp add: Rep_revent_inverse revent.rep_eq)

lemma revent_pair_eq:
  assumes "b \<notin>\<^sub>\<R> a" "d \<notin>\<^sub>\<R> c"
  shows "(a, b)\<^sub>\<R> = (c, d)\<^sub>\<R> \<longleftrightarrow> a = c \<and> b = d"
  using assms
  by (metis revent_revent rrefusal_revent)

instantiation revent :: (type) preorder
begin
  definition less_eq_revent :: "'e revent \<Rightarrow> 'e revent \<Rightarrow> bool" where "less_eq_revent a b \<equiv> rrefusal a \<le> rrefusal b \<and> revent a = revent b"
  definition less_revent :: "'e revent \<Rightarrow> 'e revent \<Rightarrow> bool" where "less_revent a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)"

instance apply intro_classes
  by (auto simp add:less_revent_def less_eq_revent_def)
end

subsection \<open> Refusal Traces \<close>

text \<open> A standard refusal trace is either a refusal or a refusal event 
       followed by a refusal trace. In other words, it is a generalised 
       terminated list whose nil element is of type @{type revent}. \<close>

datatype 'e rtrace = Refusal "'e refusal" ("\<langle>_\<rangle>\<^sub>\<R>") | REvent "'e revent" "'e rtrace" (infix "#\<^sub>\<R>" 65)

syntax
  "_rtrace"     :: "args \<Rightarrow> 'e \<Rightarrow> 'e rtrace"    ("\<langle>(_),(_)\<rangle>\<^sub>\<R>")

translations
  "\<langle>x,xs,y\<rangle>\<^sub>\<R>" == "(x#\<^sub>\<R>\<langle>xs,y\<rangle>\<^sub>\<R>)"
  "\<langle>x,y\<rangle>\<^sub>\<R>" == "x#\<^sub>\<R>\<langle>y\<rangle>\<^sub>\<R>"

text \<open> The set of refusal traces is rtraces. \<close>

type_synonym 'e rtraces = "('e rtrace) set"

value "\<langle>a,b,c,e\<rangle>\<^sub>\<R>"
value "\<langle>e\<rangle>\<^sub>\<R>"

instantiation refusal :: (type) plus
begin
lift_definition plus_refusal :: "'e refusal \<Rightarrow> 'e refusal \<Rightarrow> 'e refusal" is sup .

instance
  by intro_classes
end

instantiation rtrace :: (plus) plus
begin

fun plus_rtrace :: "'e rtrace \<Rightarrow> 'e rtrace \<Rightarrow> 'e rtrace" where
"plus_rtrace \<langle>x\<rangle>\<^sub>\<R> \<langle>y\<rangle>\<^sub>\<R> = \<langle>x+y\<rangle>\<^sub>\<R>" |
"plus_rtrace \<langle>x\<rangle>\<^sub>\<R> (y#\<^sub>\<R>ys) = (x+rrefusal(y),revent(y))\<^sub>\<R>#\<^sub>\<R> ys" |
"plus_rtrace (x#\<^sub>\<R>xs) ys = x#\<^sub>\<R>(plus_rtrace xs ys)"

instance by intro_classes
end

instantiation rtrace :: (type) preorder
begin

fun less_eq_rtrace :: "'a rtrace \<Rightarrow> 'a rtrace \<Rightarrow> bool" where
"less_eq_rtrace \<langle>x\<rangle>\<^sub>\<R> \<langle>y\<rangle>\<^sub>\<R> = (x \<le> y)" |
"less_eq_rtrace \<langle>x\<rangle>\<^sub>\<R> (y#\<^sub>\<R>ys) = (x \<le> rrefusal y)" |
"less_eq_rtrace (x#\<^sub>\<R>xs) (y#\<^sub>\<R>ys) = (x \<le> y \<and> less_eq_rtrace xs ys)" |
"less_eq_rtrace (x#\<^sub>\<R>xs) \<langle>y\<rangle>\<^sub>\<R> = False"

definition less_rtrace :: "'a rtrace \<Rightarrow> 'a rtrace \<Rightarrow> bool" where 
    "less_rtrace a b \<equiv> a \<le> b \<and> \<not>(b \<le> a)"

lemma rtrace_refl:
  fixes x :: "'a rtrace"
  shows "x \<le> x"
  apply (induct x rule:rtrace.induct)
  by auto

lemma rtrace_trans:
  fixes x y z :: "'a rtrace"
  shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  apply (induct x z arbitrary:y rule:less_eq_rtrace.induct)
  apply (case_tac ya)
      apply auto
     apply (metis Refusal_Tests.less_eq_rtrace.simps(2) Refusal_Tests.less_eq_rtrace.simps(3) less_eq_revent_def less_eq_rtrace.simps(1) order_trans rtrace.exhaust)
  by (metis Refusal_Tests.less_eq_rtrace.simps(3) less_eq_rtrace.simps(4) order_trans rtrace.exhaust)+
 
instance apply intro_classes
    apply (auto simp add:less_rtrace_def)
   apply (simp add: rtrace_refl)
  using rtrace_trans by blast
end  

subsubsection \<open> Healthiness Conditions \<close>

definition MRT0 :: "'e rtraces \<Rightarrow> bool" where
"MRT0 RT \<equiv> \<langle>\<bullet>\<rangle>\<^sub>\<R> \<in> RT"

definition MRT1 :: "'e::plus rtraces \<Rightarrow> bool" where
"MRT1 RT \<equiv> \<forall>\<Phi>\<^sub>1 \<Phi>\<^sub>2. \<Phi>\<^sub>1 + \<langle>[{}]\<^sub>\<R>\<rangle>\<^sub>\<R> + \<Phi>\<^sub>2 \<in> RT \<longrightarrow> \<Phi>\<^sub>1 + \<langle>\<bullet>\<rangle>\<^sub>\<R> + \<Phi>\<^sub>2 \<in> RT"

definition MRT2 :: "'e::plus rtraces \<Rightarrow> bool" where
"MRT2 RT \<equiv> \<forall>\<Phi>. \<Phi> + \<langle>\<bullet>\<rangle>\<^sub>\<R> \<in> RT \<longrightarrow> \<Phi> + \<langle>[{}]\<^sub>\<R>\<rangle>\<^sub>\<R> \<in> RT"

definition MRT3 :: "'e::plus rtraces \<Rightarrow> bool" where
"MRT3 RT \<equiv> \<forall>\<rho> e X. \<rho> + \<langle>e,[X]\<^sub>\<R>\<rangle>\<^sub>\<R> \<in> RT \<longrightarrow> \<rho> \<in> RT"

definition MRT4 :: "'e::plus rtraces \<Rightarrow> bool" where
"MRT4 RT \<equiv> \<forall>\<Phi>\<^sub>1 \<Phi>\<^sub>2 X\<^sub>1 X\<^sub>2. \<Phi>\<^sub>1 + \<langle>[X\<^sub>1]\<^sub>\<R>\<rangle>\<^sub>\<R> + \<Phi>\<^sub>2 \<in> RT \<and> X\<^sub>2 \<subseteq> X\<^sub>1 \<longrightarrow> \<Phi>\<^sub>1 + \<langle>[X\<^sub>2]\<^sub>\<R>\<rangle>\<^sub>\<R> + \<Phi>\<^sub>2 \<in> RT"

definition MRT5 :: "'e::plus rtraces \<Rightarrow> bool" where
"MRT5 RT \<equiv> \<forall>X X\<^sub>1 \<Phi>\<^sub>1 \<Phi>\<^sub>2 e. \<Phi>\<^sub>1 + \<langle>[X\<^sub>1]\<^sub>\<R>\<rangle>\<^sub>\<R> + \<Phi>\<^sub>2 \<in> RT \<and> \<Phi>\<^sub>1 + \<langle>([X]\<^sub>\<R>,e)\<^sub>\<R>,\<bullet>\<rangle>\<^sub>\<R> \<notin> RT \<longrightarrow> \<Phi>\<^sub>1 + \<langle>[X + {e}]\<^sub>\<R>\<rangle>\<^sub>\<R> + \<Phi>\<^sub>2 \<in> RT"

definition RT1 :: "'e rtraces \<Rightarrow> bool" where
"RT1 RT \<equiv> \<forall>\<rho>\<^sub>1 \<rho>\<^sub>2. (\<rho>\<^sub>2 \<in> RT \<and> \<rho>\<^sub>1 \<le> \<rho>\<^sub>2) \<longrightarrow> \<rho>\<^sub>1 \<in> RT"

definition RT2 :: "'e::plus rtraces \<Rightarrow> bool" where
"RT2 RT \<equiv> \<forall>\<Phi>\<^sub>1 \<Phi>\<^sub>2 X Y. \<Phi>\<^sub>1 + \<langle>[X]\<^sub>\<R>\<rangle>\<^sub>\<R> + \<Phi>\<^sub>2 \<in> RT \<and> (\<forall>e. e \<in> Y \<and> \<Phi>\<^sub>1 + \<langle>([X]\<^sub>\<R>,e)\<^sub>\<R>,\<bullet>\<rangle>\<^sub>\<R> \<notin> RT) \<longrightarrow> \<Phi>\<^sub>1 + \<langle>[X + Y]\<^sub>\<R>\<rangle>\<^sub>\<R> + \<Phi>\<^sub>2 \<in> RT"

subsubsection \<open> Refinement \<close>

abbreviation refine_rtraces :: "'e rtraces \<Rightarrow> 'e rtraces \<Rightarrow> bool"  (infixl "\<sqsubseteq>\<^sub>\<R>" 70)
  where "refine_rtraces P Q \<equiv> Q \<subseteq> P"

subsubsection \<open> Traces and failures projections \<close>

primrec trace :: "'e rtrace \<Rightarrow> 'e trace" where
"trace \<langle>x\<rangle>\<^sub>\<R> = []" |
"trace (x#\<^sub>\<R>xs) = (revent x)#(trace xs)"

primrec last :: "'e rtrace \<Rightarrow> 'e refusal" where
"last \<langle>x\<rangle>\<^sub>\<R> = x" |
"last (x#\<^sub>\<R>xs) = (last xs)"

primrec firstRefusal :: "'e rtrace \<Rightarrow> 'e refusal" where
"firstRefusal \<langle>x\<rangle>\<^sub>\<R> = x" |
"firstRefusal (x#\<^sub>\<R>xs) = rrefusal x"

fun lastRefusalSet :: "'e rtrace \<Rightarrow> 'e set" where
"lastRefusalSet \<langle>\<bullet>\<rangle>\<^sub>\<R> = {}" |
"lastRefusalSet \<langle>[X]\<^sub>\<R>\<rangle>\<^sub>\<R> = X" |
"lastRefusalSet (x#\<^sub>\<R>xs) = (lastRefusalSet xs)"

definition failures :: "'e rtrace \<Rightarrow> 'e failure set" where
"failures \<rho> = {f. f = (trace \<rho>,lastRefusalSet \<rho>) \<and> last \<rho> \<noteq> \<bullet>}"

definition RTtoFailures :: "'e rtrace set \<Rightarrow> 'e failure set" where
"RTtoFailures RT = (\<Union>\<rho>\<in>RT. failures(\<rho>))"

definition RTtoTraces :: "'e rtrace set \<Rightarrow> 'e trace set" where
"RTtoTraces RT = (\<Union>\<rho>\<in>RT. {trace(\<rho>)})"

definition RT2F :: "'e rtrace set \<Rightarrow> 'e fprocess" where
"RT2F RT = (RTtoFailures RT, RTtoTraces RT)"

subsubsection \<open> Operators \<close>

definition Div :: "'e rtraces" where
"Div = {\<langle>\<bullet>\<rangle>\<^sub>\<R>}"

definition Stop :: "'e rtraces" where
"Stop = {rt. \<exists>X. rt = \<langle>X\<rangle>\<^sub>\<R>}"

definition Prefix :: "'e \<Rightarrow> 'e rtraces \<Rightarrow> 'e rtraces" (infixl "\<rightarrow>\<^sub>\<R>" 65) where
"a \<rightarrow>\<^sub>\<R> P = {rt. \<exists>X. a \<notin>\<^sub>\<R> X \<and> rt = \<langle>X\<rangle>\<^sub>\<R>} \<union> {rt. \<exists>X \<rho>. \<rho> \<in> P \<and> a \<notin>\<^sub>\<R> X \<and> rt = (X,a)\<^sub>\<R>#\<^sub>\<R>\<rho>}"

definition IntChoice :: "'e rtraces \<Rightarrow> 'e rtraces \<Rightarrow> 'e rtraces" (infixl "\<sqinter>\<^sub>\<R>" 65) where
"P \<sqinter>\<^sub>\<R> Q = P \<union> Q"

definition ExtChoice :: "'e rtraces \<Rightarrow> 'e rtraces \<Rightarrow> 'e rtraces" (infix "\<box>\<^sub>\<R>" 65) where
"P \<box>\<^sub>\<R> Q = {rt. rt \<in> (P \<union> Q) \<and> \<langle>firstRefusal rt\<rangle>\<^sub>\<R> \<in> (P \<inter> Q)}"

definition PriRevent :: "'e::order revent \<Rightarrow> bool" where
"PriRevent \<rho> == \<forall>b. \<rho> \<noteq> b \<longrightarrow> \<not> revent \<rho> \<le> revent b"

definition PriHigher :: "'e::order revent \<Rightarrow> 'e refusal" where
"PriHigher X = [{b. revent X < b}]\<^sub>\<R>"

primrec PriRtrace :: "'e::order rtrace \<Rightarrow> 'e rtrace" where
"PriRtrace \<langle>X\<rangle>\<^sub>\<R> = \<langle>X\<rangle>\<^sub>\<R>" |
"PriRtrace (X #\<^sub>\<R> ys) = (if PriRevent X then X #\<^sub>\<R> PriRtrace ys else (rrefusal X \<union>\<^sub>\<R> PriHigher X,revent X)\<^sub>\<R> #\<^sub>\<R> PriRtrace ys)"

definition Pri :: "'e::order rtraces \<Rightarrow> 'e rtraces" where
"Pri P = {rt. \<exists>\<rho>. \<rho> \<in> P \<and> rt = PriRtrace \<rho>}"

subsubsection \<open> Results with Pri \<close>

lemma 
  assumes "RT1 P" "RT1 Q" "RT1 R"
  shows "P \<box>\<^sub>\<R> (Q \<sqinter>\<^sub>\<R> R) = (P \<box>\<^sub>\<R> Q) \<sqinter>\<^sub>\<R> (P \<box>\<^sub>\<R> R)"
  using assms unfolding ExtChoice_def IntChoice_def apply auto
  by (metis RT1_def distrib_sup_le firstRefusal.simps(1) firstRefusal.simps(2) inf_refusal.simps(1) less_eq_rtrace.simps(2) refusal.exhaust rtrace.exhaust rtrace_refl sup.cobounded1 sup_refusal.simps(1) sup_refusal.simps(2))+

lemma Pri_Stop: "Pri(Stop) = Stop"
  unfolding Pri_def PriRtrace_def PriRevent_def Stop_def
  by auto

lemma Pri_Div: "Pri(Div) = Div"
  unfolding Pri_def PriRtrace_def PriRevent_def Div_def
  by auto
  
lemma Pri_IntChoice: "Pri(P \<sqinter>\<^sub>\<R> Q) = Pri(P) \<sqinter>\<^sub>\<R> Pri(Q)"
  unfolding Pri_def PriRtrace_def PriRevent_def IntChoice_def
  by auto

lemma Pri_ExtChoice: "Pri(P \<box>\<^sub>\<R> Q) = Pri(P) \<box>\<^sub>\<R> Pri(Q)"
  unfolding Pri_def PriRtrace_def PriRevent_def ExtChoice_def
  nitpick
  oops

lemma a_b_Stop:
  "(a \<rightarrow>\<^sub>\<R> Stop) \<box>\<^sub>\<R> (b \<rightarrow>\<^sub>\<R> Stop) = {rt. (\<exists>X. a \<notin>\<^sub>\<R> X \<and> b \<notin>\<^sub>\<R> X \<and> (rt = \<langle>X\<rangle>\<^sub>\<R> \<or> (\<exists>Y. rt = \<langle>(X,a)\<^sub>\<R>,Y\<rangle>\<^sub>\<R> \<or> rt = \<langle>(X,b)\<^sub>\<R>,Y\<rangle>\<^sub>\<R>)))}"
  unfolding ExtChoice_def Prefix_def Stop_def by auto

lemma Pri_ExtChoice_eg1:
  assumes "b \<le> a"
  shows "Pri((a \<rightarrow>\<^sub>\<R> Stop) \<box>\<^sub>\<R> (b \<rightarrow>\<^sub>\<R> Stop)) = a \<rightarrow>\<^sub>\<R> Stop"
  apply (simp add:a_b_Stop)
  using assms unfolding Prefix_def Stop_def Pri_def
  unfolding PriRtrace_def
  apply auto
  unfolding PriHigher_def
  apply auto
       apply metis
  apply (metis Un_iff mem_Collect_eq order_less_irrefl revent_revent rmember.simps(2) rrefusal_revent sup_refusal.elims)
  

lemma "Pri(a \<rightarrow>\<^sub>\<R> Stop) = a \<rightarrow>\<^sub>\<R> Stop"
  unfolding Pri_def PriRtrace_def PriRevent_def Stop_def Prefix_def
  apply auto

nitpick
lemma "Pri(a \<rightarrow>\<^sub>\<R> P) = a \<rightarrow>\<^sub>\<R> Pri(P)"
  unfolding Pri_def PriRtrace_def PriRevent_def
  apply auto
  

subsubsection \<open> Results with mapping \<close>

lemma Stop_traces: "snd Failures.Stop = RTtoTraces(Stop)"
  unfolding Failures.Stop_def Stop_def
  unfolding RTtoTraces_def
  by auto

lemma Stop_failures: "fst Failures.Stop = RTtoFailures(Stop)"
  unfolding Failures.Stop_def Stop_def
  unfolding RTtoFailures_def failures_def
  apply auto
  by force

lemma Div_traces: "snd Failures.Div = RTtoTraces(Div)"
  unfolding Failures.Div_def Div_def
  unfolding RTtoTraces_def
  by auto

lemma Div_failures: "fst Failures.Div = RTtoFailures(Div)"
  unfolding Failures.Div_def Div_def
  unfolding RTtoFailures_def failures_def
  by auto

lemma Prefix_traces: "snd(a \<rightarrow> RT2F P) = RTtoTraces(a \<rightarrow>\<^sub>\<R> P)"
  unfolding Failures.prefix_def Prefix_def
  unfolding RTtoTraces_def RT2F_def
  apply auto
  using rmember.simps(1) apply fastforce
  by (metis revent_revent rmember.simps(1) trace.simps(2))+

lemma Prefix_failures: "fst(a \<rightarrow> RT2F P) = RTtoFailures(a \<rightarrow>\<^sub>\<R> P)"
  unfolding Failures.prefix_def Prefix_def
  unfolding RTtoFailures_def RT2F_def failures_def
  apply auto
  apply (metis Refusal_Tests.last.simps(1) lastRefusalSet.simps(2) refusal.distinct(1) rmember.simps(2) trace.simps(1))
     apply (metis Refusal_Tests.last.simps(2) lastRefusalSet.simps(3) revent_revent rmember.simps(1) trace.simps(2))
    apply (metis lastRefusalSet.simps(2) rmember.elims(3))
  by (simp add: revent_revent)+

lemma IntChoice_traces: "snd(RT2F(P) \<sqinter> RT2F(Q)) = RTtoTraces(P \<sqinter>\<^sub>\<R> Q)"
  unfolding Failures.intChoice_def IntChoice_def
  unfolding RTtoTraces_def RT2F_def
  by auto

lemma IntChoice_failures: "fst(RT2F(P) \<sqinter> RT2F(Q)) = RTtoFailures(P \<sqinter>\<^sub>\<R> Q)"
  unfolding Failures.intChoice_def IntChoice_def
  unfolding RTtoFailures_def RT2F_def
  by auto

(* TODO: Proof for external choice is rather more complicated *)

lemma 
  assumes "MRT0 P" "MRT0 Q" "RT1 P" "RT1 Q"
  shows ExtChoice_traces: "snd(RT2F(P) \<box> RT2F(Q)) = RTtoTraces(P \<box>\<^sub>\<R> Q)"
  using assms unfolding Failures.extChoice_def ExtChoice_def
  unfolding RTtoTraces_def RT2F_def
  apply auto
  oops

lemma 
  assumes "MRT0 P" "MRT0 Q" "RT1 P" "RT1 Q"
  shows ExtChoice_failures: "fst(RT2F(P) \<box> RT2F(Q)) = RTtoFailures(P \<box>\<^sub>\<R> Q)"
  using assms unfolding Failures.extChoice_def ExtChoice_def
  unfolding RTtoFailures_def RTtoTraces_def RT2F_def
  unfolding firstRefusal_def
  apply auto
  apply (smt Refusal_Tests.last.simps(1) failures_def lastRefusalSet.elims list.simps(3) mem_Collect_eq prod.sel(1) prod.sel(2) rtrace.simps(7) trace.simps(2))
  oops

text \<open> Observe that termination is not treated explicitly here, but could
       be achieved by parametrising 'e with an option type (tick). \<close>

(* TO BE REVIEWED BELOW *)

instantiation refusal :: (type) disjoint_rel
begin
  primrec fzero_refusal :: "'e refusal \<Rightarrow> 'e refusal" where 
    "fzero_refusal \<bullet> = \<bullet>" | "fzero_refusal [_]\<^sub>\<R> = [{}]\<^sub>\<R>"
  definition disjoint_rel_refusal :: "'e refusal \<Rightarrow> 'e refusal \<Rightarrow> bool" where "disjoint_rel_refusal a b = ((a = \<bullet> \<and> b = \<bullet>) \<or> a \<inter>\<^sub>\<R> b = [{}]\<^sub>\<R>)"

  lemma refusal_inf_eq_bullet: "[S]\<^sub>\<R> \<inter>\<^sub>\<R> d = \<bullet> \<longleftrightarrow> d = \<bullet>"
    using inf_refusal.elims by blast

  lemma refusal_inf_eq_emptyset:  "[S]\<^sub>\<R> \<inter>\<^sub>\<R> d = [{}]\<^sub>\<R> \<longleftrightarrow> (\<exists>Z. d = [Z]\<^sub>\<R> \<and> S \<inter> Z = {})"
    apply auto
    by (metis inf_refusal.elims refusal.distinct(1) refusal.inject)
  
  lemma refusal_rel_refusal:
     "a \<inter>\<^sub>\<R> b \<noteq> \<bullet> \<and> a \<inter>\<^sub>\<R> b \<noteq> [{}]\<^sub>\<R> \<Longrightarrow> \<exists>d. a \<union>\<^sub>\<R> b = a \<union>\<^sub>\<R> d \<and> (a \<inter>\<^sub>\<R> d = \<bullet> \<or> a \<inter>\<^sub>\<R> d = [{}]\<^sub>\<R>)"
  proof (induct a b rule:sup_refusal.induct)
    case (1 R)
    then show ?case by auto
  next
    case (2 v)
    then show ?case by simp
  next
    case (3 S R)
    then have "(\<exists>d. [S]\<^sub>\<R> \<union>\<^sub>\<R> [R]\<^sub>\<R> = [S]\<^sub>\<R> \<union>\<^sub>\<R> d \<and> ([S]\<^sub>\<R> \<inter>\<^sub>\<R> d = \<bullet> \<or> [S]\<^sub>\<R> \<inter>\<^sub>\<R> d = [{}]\<^sub>\<R>))
              =
              ((\<exists>d. [S]\<^sub>\<R> \<union>\<^sub>\<R> [R]\<^sub>\<R> = [S]\<^sub>\<R> \<union>\<^sub>\<R> d \<and> [S]\<^sub>\<R> \<inter>\<^sub>\<R> d = \<bullet>)
                \<or>
               (\<exists>d. [S]\<^sub>\<R> \<union>\<^sub>\<R> [R]\<^sub>\<R> = [S]\<^sub>\<R> \<union>\<^sub>\<R> d \<and> [S]\<^sub>\<R> \<inter>\<^sub>\<R> d = [{}]\<^sub>\<R>))"
      by auto
    also have "... = 
              ((\<exists>d. [S]\<^sub>\<R> \<union>\<^sub>\<R> [R]\<^sub>\<R> = [S]\<^sub>\<R> \<union>\<^sub>\<R> d \<and> d = \<bullet>)
                \<or>
               (\<exists>d. [S]\<^sub>\<R> \<union>\<^sub>\<R> [R]\<^sub>\<R> = [S]\<^sub>\<R> \<union>\<^sub>\<R> d \<and> (\<exists>Z. d = [Z]\<^sub>\<R> \<and> S \<inter> Z = {})))"
      by (auto simp add:refusal_inf_eq_bullet refusal_inf_eq_emptyset)
    also have "... = 
              (([S]\<^sub>\<R> \<union>\<^sub>\<R> [R]\<^sub>\<R> = [S]\<^sub>\<R> \<union>\<^sub>\<R> \<bullet>)
                \<or>
               (\<exists>Z. [S]\<^sub>\<R> \<union>\<^sub>\<R> [R]\<^sub>\<R> = [S]\<^sub>\<R> \<union>\<^sub>\<R> [Z]\<^sub>\<R> \<and>  S \<inter> Z = {}))"
      by blast
    also have "... = 
              (([S]\<^sub>\<R> \<union>\<^sub>\<R> [R]\<^sub>\<R> = [S]\<^sub>\<R> \<union>\<^sub>\<R> \<bullet>)
                \<or>
               (\<exists>Z. S \<union> R = S \<union> Z \<and> S \<inter> Z = {}))"
      by auto
    also have "... = True"
      by (simp add: disjoint_rel_set_sum)
    finally show ?case by auto 
  qed

  lemma refusal_rel_refusal2:
    "a \<inter>\<^sub>\<R> b \<noteq> \<bullet> \<and> a \<inter>\<^sub>\<R> b \<noteq> [{}]\<^sub>\<R> \<Longrightarrow> \<exists>d. a + b = a + d \<and> (a \<inter>\<^sub>\<R> d = \<bullet> \<or> a \<inter>\<^sub>\<R> d = [{}]\<^sub>\<R>)"
  proof (induct a b rule:sup_refusal.induct)
    case (1 R)
    then show ?case by auto
  next
    case (2 v)
    then show ?case by auto
  next
    case (3 S R)
    then show ?case apply auto
      by (metis Diff_disjoint Un_Diff_cancel inf_refusal.simps(3) plus_refusal.simps(3))
  qed

  lemma refusal_rel_dist: "((a \<union>\<^sub>\<R> b) \<inter>\<^sub>\<R> c = \<bullet> \<or> (a \<union>\<^sub>\<R> b) \<inter>\<^sub>\<R> c = [{}]\<^sub>\<R>) = ((a \<inter>\<^sub>\<R> c = \<bullet> \<or> a \<inter>\<^sub>\<R> c = [{}]\<^sub>\<R>) \<and> (b \<inter>\<^sub>\<R> c = \<bullet> \<or> b \<inter>\<^sub>\<R> c = [{}]\<^sub>\<R>))"
  proof (induct a b rule:inf_refusal.induct)
    case (1 R)
    then show ?case by auto
  next
    case (2 v)
    then show ?case by auto
  next
    case (3 S R)
    then show ?case apply (case_tac c) 
      using refusal_inf_eq_bullet by auto
  qed

instance apply intro_classes
     apply (simp_all add:disjoint_rel_refusal_def fzero_refusal_def)

     apply (simp add: abel_semigroup.commute inf.abel_semigroup_axioms)
    apply (smt abel_semigroup.commute inf.abel_semigroup_axioms inf_idem inf_le2 less_eq_refusal.elims(2) refusal.simps(7) refusal_rel_dist sup_inf_absorb)
  
  apply (smt abel_semigroup.commute inf.abel_semigroup_axioms inf_idem inf_sup_ord(2) less_eq_refusal.elims(2) refusal.simps(6) refusal.simps(7) refusal_inf_eq_bullet refusal_rel_dist sup_inf_absorb)
  
  apply (metis inf_refusal.elims refusal_inf_eq_bullet refusal_rel_refusal2)
nitpick
  apply (smt inf_idem inf_le2 inf_refusal.elims inf_right_idem le_iff_sup refusal.simps(6) refusal.simps(7) refusal_rel_dist)
    apply ( simp add:refusal_rel_refusal2)
  
    apply (smt inf_bot_right inf_commute inf_refusal.elims inf_refusal.simps(3) plus_refusal.simps(3) refusal_inf_eq_bullet refusal_rel_refusal sup_inf_absorb sup_refusal.elims sup_refusal.simps(3))
     apply (simp add: inf_commute)+
(*  using inf_refusal.elims apply blast
  apply (metis inf_bot_right refusal.exhaust refusal.simps(6) refusal.simps(7) refusal_inf_eq_emptyset)
  
    sledgehammer[debug=true]
    apply (smt inf_bot_right inf_refusal.elims inf_refusal.simps(3) plus_refusal.simps(3) refusal.distinct(1) refusal_inf_eq_bullet refusal_rel_refusal sup_inf_absorb sup_refusal.elims sup_refusal.simps(3))
(*  apply (metis inf_refusal.elims refusal_inf_eq_bullet refusal_rel_refusal) *)

  by (metis (no_types, lifting) inf_refusal.elims refusal.distinct(1) refusal_rel_dist)
 *)
end

lemma
  fixes a b :: "'e refusal"
  shows "a \<bar> b \<and> a \<bar> c \<and> a + b = a + c \<longrightarrow> b = c"
  nitpick

instantiation refusal :: (type) fzero_weak_add_zero
begin

instance apply intro_classes
     apply (auto simp add:fzero_refusal_def plus_refusal_def)
   apply (simp add: inf_sup_aci(6))
  by (metis abel_semigroup.commute sup.abel_semigroup_axioms sup_refusal.simps(1))
end

instantiation refusal :: (type) fzero_add_fzero_ord
begin

instance apply intro_classes
  apply (auto simp add:fzero_weak_le_def fzero_le_def)
   apply (metis le_iff_sup plus_refusal.transfer)
  by (metis inf_sup_ord(3) plus_refusal.transfer)
end

(* NOTE: not possible to have left_cancellation for bullet. No trace algebra unless bullet is
         inserted within the refusal type itself! *)

instantiation revent :: (type) plus
begin

 (* If we do not fix the resulting set addition then + is not closed under the type. *)
definition plus_revent :: "'a revent \<Rightarrow> 'a revent \<Rightarrow> 'a revent" where
"plus_revent r\<^sub>0 r\<^sub>1 = ((rrefusal r\<^sub>0 + rrefusal r\<^sub>1) - {revent r\<^sub>1},revent r\<^sub>1)\<^sub>\<R>"

instance by intro_classes
end

instantiation revent :: (type) disjoint_rel
begin
 
definition fzero_revent :: "'a revent \<Rightarrow> 'a revent" where
"fzero_revent r = (fzero (rrefusal r), revent r)\<^sub>\<R>"
definition disjoint_rel_revent :: "'a revent \<Rightarrow> 'a revent \<Rightarrow> bool" where
"disjoint_rel_revent r\<^sub>0 r\<^sub>1 = (rrefusal r\<^sub>0 \<bar> rrefusal r\<^sub>1)"

lemma 
  fixes a :: "'a revent"
  assumes "(\<not> a \<bar> b)"
  shows "\<exists>d. a + b = a + d \<and> a \<bar> d"
proof -
  have "(\<exists>d. a + b = a + d \<and> a \<bar> d)
        =
        (\<exists>d. (rrefusal a, revent a)\<^sub>\<R> + (rrefusal b, revent b)\<^sub>\<R> = (rrefusal a, revent a)\<^sub>\<R> + (rrefusal d, revent d)\<^sub>\<R> \<and> rrefusal a \<bar> rrefusal d)"
    by (simp add:plus_revent_def disjoint_rel_revent_def)
  also have "... =
        (\<exists>d. (rrefusal a + rrefusal b, revent b)\<^sub>\<R> = (rrefusal a + rrefusal d, revent d)\<^sub>\<R> \<and> revent d \<notin>\<^sub>\<R> rrefusal a + rrefusal d \<and> rrefusal a \<bar> rrefusal d)"
    apply (simp add:plus_revent_def)
    nitpick
  also have "... =
        (\<exists>d. (rrefusal a + rrefusal b, revent b)\<^sub>\<R> = (rrefusal a + rrefusal d, revent d)\<^sub>\<R> \<and> rrefusal a \<bar> rrefusal d)
        \<or>
        (\<exists>d. rrefusal a + rrefusal b = rrefusal a + rrefusal d \<and> rrefusal a \<bar> rrefusal d)"
    by auto
  assume "\<not> rrefusal a \<bar> rrefusal b"
  then have "(\<exists>d e. rrefusal a + rrefusal b = rrefusal a + rrefusal (rrefusal d, revent e)\<^sub>\<R> \<and> rrefusal a \<bar> rrefusal (rrefusal d, revent e)\<^sub>\<R>)"
    using assms
    using disjoint_rel_sum 
    

  have "(\<exists>d. a + b = a + d \<and> a \<bar> d)
        =
        (\<exists>d. rrefusal a + rrefusal b = rrefusal a + rrefusal d \<and> rrefusal a \<bar> rrefusal d)"
    apply (simp add:plus_revent_def disjoint_rel_revent_def )
  
proof -
  from assms have "\<not> rrefusal a \<bar> rrefusal b"
    by (simp add:disjoint_rel_revent_def)
  then have "\<exists>d. rrefusal a + rrefusal b = rrefusal a + d \<and> rrefusal a \<bar> d"
    using disjoint_rel_sum by blast
  then have "\<exists>d e. rrefusal a + rrefusal b = rrefusal a + d \<and> rrefusal a \<bar> d \<and> rrefusal e = d"
    apply auto
    

instance apply intro_classes
     apply (simp add: disjoint_rel_revent_def disjoint_rel_sym)
  apply (metis (mono_tags, lifting) Abs_revent_inverse disjoint_rel_revent_def disjoint_rel_zero fzero_refusal_def fzero_revent_def mem_Collect_eq prod.sel(1) rmember.simps(1) rrefusal.rep_eq split_beta)
  




instantiation rtrace :: (type) fzero
begin
  definition fzero_rtrace :: "'e rtrace \<Rightarrow> 'e rtrace" where "fzero_rtrace a = \<langle>\<bullet>\<rangle>\<^sub>\<R>"

instance by intro_classes
end

instantiation rtrace :: (type) disjoint_rel
begin

primrec rtrace2refusals :: "'e rtrace \<Rightarrow> ('e refusal) list" where
"rtrace2refusals \<langle>x\<rangle>\<^sub>\<R> = [x]" |
"rtrace2refusals (x#\<^sub>\<R>xs) = (rrefusal x)#(rtrace2refusals xs)"

fun disjoint_rel_rtrace :: "'e rtrace \<Rightarrow> 'e rtrace \<Rightarrow> bool" where
"disjoint_rel_rtrace \<langle>x\<rangle>\<^sub>\<R>    \<langle>y\<rangle>\<^sub>\<R>     = x \<bar> y" |
"disjoint_rel_rtrace \<langle>x\<rangle>\<^sub>\<R>    (y#\<^sub>\<R>s)  = x \<bar> rrefusal y" |
"disjoint_rel_rtrace (x#\<^sub>\<R>xs) (y#\<^sub>\<R>ys) = ((rrefusal x \<bar> rrefusal y) \<and> disjoint_rel_rtrace xs ys)" |
"disjoint_rel_rtrace (x#\<^sub>\<R>xs) \<langle>y\<rangle>\<^sub>\<R>    = rrefusal x \<bar> y"

lemma disjoint_rel_rtrace_sym:
  fixes a :: "'a rtrace"
  shows "(a \<bar> b) = b \<bar> a"
  proof (induct a b rule:disjoint_rel_rtrace.induct)
    case (1 x y)
    then show ?case by (simp add: disjoint_rel_sym)
  next
    case (2 x y s)
    then show ?case by (simp add: disjoint_rel_sym)
  next
    case (3 x xs y ys)
    then show ?case by (simp add: disjoint_rel_sym)
  next
    case (4 x xs y)
    then show ?case by (simp add: disjoint_rel_sym)
qed

lemma disjoint_rel_rtrace_fzero:
  fixes a :: "'a rtrace"
  shows "a \<bar> f\<^sub>0(a)"
  apply (case_tac a, auto)
   apply (metis disjoint_rel_rtrace.simps(1) disjoint_rel_zero fzero_refusal_def fzero_rtrace_def)
  by (metis disjoint_rel_refusal_def disjoint_rel_rtrace.simps(4) disjoint_rel_sym fzero_rtrace_def inf_refusal.simps(1))

lemma
  fixes a :: "'a rtrace"
  shows "(\<not> a \<bar> b) \<Longrightarrow> \<exists>d. a + b = a + d \<and> a \<bar> d"
  proof (induct a b rule:disjoint_rel_rtrace.induct)
  case (1 x y)
    then show ?case
      by (metis disjoint_rel_rtrace.simps(1) disjoint_rel_sum plus_rtrace.simps(1))
  next
    case (2 x y s)
    have "\<langle>x\<rangle>\<^sub>\<R> \<bar> (y #\<^sub>\<R> s) \<longleftrightarrow> (x \<bar> rrefusal y)"
      by simp

    have "\<langle>x\<rangle>\<^sub>\<R> + (y #\<^sub>\<R> s) = (x+rrefusal(y),revent(y))\<^sub>\<R> #\<^sub>\<R>s"
      by simp

    have "(\<not> (x \<bar> rrefusal y)) \<longrightarrow> (\<exists>d. x + rrefusal(y) = x + rrefusal(d) \<and> x \<bar> rrefusal d)"
      apply auto
      sledgehammer[debug=true]


    have "(\<not> \<langle>x\<rangle>\<^sub>\<R> \<bar> (y #\<^sub>\<R> s)) \<longrightarrow> (\<exists>d. (x+rrefusal(y),revent(y))\<^sub>\<R> #\<^sub>\<R>s = (x+rrefusal(d),revent(d))\<^sub>\<R> #\<^sub>\<R>s \<and> revent(y) = revent(d) \<and> x \<bar> rrefusal d)"
      
    then have "(\<not> \<langle>x\<rangle>\<^sub>\<R> \<bar> (y #\<^sub>\<R> s)) \<longrightarrow> 

    have "(\<exists>d. \<langle>x\<rangle>\<^sub>\<R> + (y #\<^sub>\<R> s) = \<langle>x\<rangle>\<^sub>\<R> + d \<and> \<langle>x\<rangle>\<^sub>\<R> \<bar> d)
          =
          (\<exists>d. (x+rrefusal(y),revent(y))\<^sub>\<R> #\<^sub>\<R>s = \<langle>x\<rangle>\<^sub>\<R> + d \<and> \<langle>x\<rangle>\<^sub>\<R> \<bar> d)"
      by simp
    (*
      by (smt disjoint_rel_rtrace.elims(2) plus_rtrace.simps(1) plus_rtrace.simps(2) rtrace.simps(2) rtrace.simps(4))
      by (smt disjoint_rel_rtrace.elims(2) plus_rtrace.simps(1) plus_rtrace.simps(2) rtrace.distinct(1) rtrace.inject(2)) *)
  next
    case (3 x xs y ys)
    then show ?case sorry
  next
  case (4 x xs y)
  then show ?case sorry
  qed *)

instance apply intro_classes
  using disjoint_rel_rtrace_sym  apply simp
  using disjoint_rel_rtrace_fzero apply simp
end





text \<open> Is 'e refusal a boolean algebra? No because of complement. \<close>

(*
instantiation refusal :: (type) bounded_lattice
begin
(*
fun minus_refusal :: "'e refusal \<Rightarrow> 'e refusal \<Rightarrow> 'e refusal" where
"minus_refusal \<bullet> R = R" |
"minus_refusal S \<bullet> = S" |
"minus_refusal [S]\<^sub>\<R> [R]\<^sub>\<R> = [S - R]\<^sub>\<R>"

primrec uminus_refusal :: "'e refusal \<Rightarrow> 'e refusal" where
"uminus_refusal \<bullet> = [- {}]\<^sub>\<R>" |
"uminus_refusal [x]\<^sub>\<R> = [- x]\<^sub>\<R>"*)

definition bot_refusal :: "'e refusal" where "bot_refusal = \<bullet>"
definition top_refusal :: "'e refusal" where "top_refusal = [UNIV]\<^sub>\<R>"

  lemma inf_sup_dist: "x \<union>\<^sub>\<R> y \<inter>\<^sub>\<R> z = (x \<union>\<^sub>\<R> y) \<inter>\<^sub>\<R> (x \<union>\<^sub>\<R> z)"
  proof (induct x y rule:sup_refusal.induct)
    case (1 R)
    then show ?case by simp
  next
    case (2 v)
    then show ?case by simp
  next
    case (3 S R)
    then show ?case by (case_tac z, auto)
  qed

instance
  apply intro_classes
       apply (auto simp add:bot_refusal_def top_refusal_def inf_refusal.elims sup_refusal.elims)
  using less_eq_refusal.elims(3) by auto[1]
end  *)




instantiation rtrace :: (type) plus
begin

fun plus_rtrace :: "'e rtrace \<Rightarrow> 'e rtrace \<Rightarrow> 'e rtrace" where
"plus_rtrace {x}\<^sub>\<R> {y}\<^sub>\<R> = {x+y}\<^sub>\<R>" |
"plus_rtrace {x}\<^sub>\<R> (y#\<^sub>\<R>s) = (x+rrefusal(y),revent(y))\<^sub>\<R> #\<^sub>\<R> s" |
"plus_rtrace (x#\<^sub>\<R>xs) ys = x#\<^sub>\<R>(plus_rtrace xs ys)"

instance by intro_classes
end



(*
instantiation list :: (disjoint_rel) disjoint_rel
begin

function disjoint_rel_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"disjoint_rel_list xs ys = ((hd xs) \<bar> (hd ys) \<and> (disjoint_rel_list (tl xs) (tl ys)))"
  by auto

instance apply intro_classes
  sledgehammer[debug=true]
  apply (auto simp add:disjoint_rel_list.cases)
  

end*)





instantiation rtrace :: (type) disjoint_rel
begin


  

instance apply intro_classes
(*
instantiation rtrace :: (type) fzero_is_0
begin
definition fzero_rtrace :: "'e rtrace \<Rightarrow> 'e rtrace" where "fzero_rtrace a = {\<bullet>}\<^sub>\<R>"

instance apply intro_classes
  apply (auto simp add:fzero_rtrace_def)
*)
type_synonym 'e rtracex = "('e refusal,'e revent) gtlist" 

definition plus_revent_refusal :: "'e refusal \<Rightarrow> 'e revent \<Rightarrow> 'e revent" where
"plus_revent_refusal r e = Abs_revent (r \<union>\<^sub>\<R> rrefusal(e),revent(e))"

interpretation rtracex: gtlist "plus_revent_refusal" .

notation rtracex.plus_gtlist_def (infixl "+" 65)

thm rtracex.plus_gtlist_def.cases

print_locale! gtlist


lemma "rtracex.last(x + x) = y"

  apply (simp add:rtracex.concat_gtlist.simps)
print_interps gtlist

sublocale gtlist_fzero \<subseteq> fzero_add_zero "\<lambda>x. fzero x" "concat_gtlist" *)

end