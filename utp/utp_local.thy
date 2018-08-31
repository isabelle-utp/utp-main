section \<open> Local Variables \<close>

theory utp_local
imports 
  utp_rel_laws 
  utp_meta_subst 
  utp_theory
begin
      
subsection \<open> Preliminaries \<close>
  
text \<open> The following type is used to augment that state-space with a stack of local variables
  represented as a list in the special variable $store$. Local variables will be represented
  by pushing variables onto the stack, and popping them off after use. The element type of
  the stack is @{typ "'u"} which corresponds to a suitable injection universe. \<close>
  
alphabet 'u local =
  store :: "'u list"

text \<open> State-space with a countable universe for local variables. \<close>
  
type_synonym 'a clocal = "(nat, 'a) local_scheme"
  
text \<open> The following predicate wraps the relation with assumptions that the stack has a particular 
  size before and after execution. \<close>
  
definition local_num where
"local_num n P = [#\<^sub>u(&store) =\<^sub>u \<guillemotleft>n\<guillemotright>]\<^sup>\<top> ;; P ;; [#\<^sub>u(&store) =\<^sub>u \<guillemotleft>n\<guillemotright>]\<^sup>\<top>"
  
declare inj_univ.from_univ_def [upred_defs]
declare inj_univ.to_univ_lens_def [upred_defs]
declare nat_inj_univ_def [upred_defs]
    
subsection \<open> State Primitives \<close>
  
text \<open> The following record is used to characterise the UTP theory specific operators we require
  in order to create the local variable operators. \<close>
  
record ('\<alpha>, 's) state_prim =
  
  \<comment> \<open> The first field states where in the alphabet @{typ "'\<alpha>"} the user state-space type is 
        @{typ "'s"} is located with the form of a lens. \<close>

  sstate   :: "'s \<Longrightarrow> '\<alpha>" ("\<^bold>s\<index>") 

  \<comment> \<open> The second field is the theory's substitution operator. It takes a substitution over the
        state-space type and constructs a homogeneous assignment relation. \<close>

  sassigns :: "'s usubst \<Rightarrow> '\<alpha> hrel" ("\<^bold>\<langle>_\<^bold>\<rangle>\<index>")
  
syntax
  "_sstate" :: "logic \<Rightarrow> svid" ("\<^bold>s\<index>")

translations
  "_sstate T" => "CONST sstate T"

text \<open> The following record type adds an injection universe @{typ "'u"} to the above operators.
  This is needed because the stack has a homogeneous type into which we must inject type variable
  bindings. The universe can be any Isabelle type, but must satisfy the axioms of the locale
  @{term inj_univ}, which broadly shows the injectable values permitted. \<close>
  
record ('\<alpha>, 's, 'u, 'a) local_prim = "('\<alpha>, ('u, 's) local_scheme) state_prim" +
  inj_local :: "('a, 'u) inj_univ"
  
text \<open> The following locales give the assumptions required of the above signature types. The first
  gives the definining axioms for state-spaces. State-space lens @{text "\<^bold>s"} must be a very well-behaved
  lens, and sequential composition of assignments corresponds to functional composition of the
  underlying substitutions. TODO: We might also need operators to properly handle framing in the
  future. \<close>
  
locale utp_state =
  fixes S (structure)
  assumes "vwb_lens \<^bold>s"
  and passigns_comp: "(\<^bold>\<langle>\<sigma>\<^bold>\<rangle> ;; \<^bold>\<langle>\<rho>\<^bold>\<rangle>) = \<^bold>\<langle>\<rho> \<circ> \<sigma>\<^bold>\<rangle>"
      
text \<open> The next locale combines the axioms of a state-space and an injection universe structure. It
  then uses the required constructs to create the local variable operators. \<close>
  
locale utp_local_state = utp_state S + inj_univ "inj_local S" for S :: "('\<alpha>, 's, 'u::two, 'a) local_prim" (structure)
begin

  text \<open> The following two operators represent opening and closing a variable scope, which is
   implemented by pushing an arbitrary initial value onto the stack, and popping it off, respectively. \<close>
  
  definition var_open :: "'\<alpha> hrel" ("open\<^sub>v") where
  "var_open = (\<Sqinter> v \<bullet> \<^bold>\<langle>[store \<mapsto>\<^sub>s (&store ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>)]\<^bold>\<rangle>)"
  
  definition var_close :: "'\<alpha> hrel" ("close\<^sub>v") where
  "var_close = \<^bold>\<langle>[store \<mapsto>\<^sub>s front\<^sub>u(&store) \<triangleleft> #\<^sub>u(&store) >\<^sub>u 0 \<triangleright> &store]\<^bold>\<rangle>"
  
  text \<open> The next operator is an expression that returns a lens pointing to the top of the stack.
    This is effectively a dynamic lens, since where it points to depends on the initial number
    of variables on the stack. \<close>
  
  definition top_var :: "('a \<Longrightarrow> ('u, 'b) local_scheme, '\<alpha>) uexpr" ("top\<^sub>v") where
  "top_var = \<guillemotleft>\<lambda> l. to_univ_lens ;\<^sub>L list_lens l ;\<^sub>L store\<guillemotright>(#\<^sub>u(&\<^bold>s:store) - 1)\<^sub>a"
  
  text \<open> Finally, we combine the above operators to represent variable scope. This is a kind of
    binder which takes a homogeneous relation, parametric over a lens, and returns a relation. It
    simply opens the variable scope, substitutes the top variable into the body, and then closes
    the scope afterwards. \<close>
  
  definition var_scope :: "(('a \<Longrightarrow> ('u, 's) local_scheme) \<Rightarrow> '\<alpha> hrel) \<Rightarrow> '\<alpha> hrel" where
  "var_scope f = open\<^sub>v ;; f(x)\<lbrakk>x\<rightarrow>\<lceil>top\<^sub>v\<rceil>\<^sub><\<rbrakk> ;; close\<^sub>v" 
end

notation utp_local_state.var_open ("open[_]")
notation utp_local_state.var_close ("close[_]")  
notation utp_local_state.var_scope ("\<V>[_,/ _]")
notation utp_local_state.top_var ("top[_]")
  
syntax       
  "_var_scope"      :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic" ("var[_] _ \<bullet> _" [0, 0, 10] 10)
  "_var_scope_type" :: "logic \<Rightarrow> id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var[_] _ :: _ \<bullet> _" [0, 0, 0, 10] 10)

translations
  "_var_scope T x P" == "CONST utp_local_state.var_scope T (\<lambda> x. P)"
  "_var_scope_type T x t P" => "CONST utp_local_state.var_scope T (_abs (_constrain x (_uvar_ty t)) P)"
    
text \<open> Next, we prove a collection of important generci laws about variable scopes using the axioms
  defined above. \<close>
  
context utp_local_state
begin
  
  lemma var_open_commute:
    "\<lbrakk> x \<bowtie> store; store \<sharp> v \<rbrakk> \<Longrightarrow> \<^bold>\<langle>[x \<mapsto>\<^sub>s v]\<^bold>\<rangle> ;; open\<^sub>v = open\<^sub>v ;; \<^bold>\<langle>[x \<mapsto>\<^sub>s v]\<^bold>\<rangle>"
    by (simp add: var_open_def passigns_comp seq_UINF_distl' seq_UINF_distr' usubst unrest lens_indep_sym)

  lemma var_close_commute:
    "\<lbrakk> x \<bowtie> store; store \<sharp> v \<rbrakk> \<Longrightarrow> \<^bold>\<langle>[x \<mapsto>\<^sub>s v]\<^bold>\<rangle> ;; close\<^sub>v = close\<^sub>v ;; \<^bold>\<langle>[x \<mapsto>\<^sub>s v]\<^bold>\<rangle>"
    by (simp add: var_close_def passigns_comp seq_UINF_distl' seq_UINF_distr' usubst unrest lens_indep_sym)

  lemma var_open_close_lemma: 
    "[store \<mapsto>\<^sub>s front\<^sub>u(&store ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>) \<triangleleft> 0 <\<^sub>u #\<^sub>u(&store ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>) \<triangleright> &store ^\<^sub>u \<langle>\<guillemotleft>v\<guillemotright>\<rangle>] = id"
    by (rel_auto)
  
  lemma var_open_close: "open\<^sub>v ;; close\<^sub>v = \<^bold>\<langle>id\<^bold>\<rangle>"
    by (simp add: var_open_def var_close_def seq_UINF_distr' passigns_comp usubst var_open_close_lemma)
      
  lemma var_scope_skip: "(var[S] x \<bullet> \<^bold>\<langle>id\<^bold>\<rangle>) = \<^bold>\<langle>id\<^bold>\<rangle>"
    by (simp add: var_scope_def var_open_def var_close_def seq_UINF_distr' passigns_comp var_open_close_lemma usubst)  

  (* A property we'd like to prove globally, but requires additional laws for assignment that may
     not be possible generically. *)
      
  lemma var_scope_nonlocal_left: 
    "\<lbrakk> x \<bowtie> store ; store \<sharp> v \<rbrakk> \<Longrightarrow> \<^bold>\<langle>[x \<mapsto>\<^sub>s v]\<^bold>\<rangle> ;; (var[S] y \<bullet> P(y)) = (var[S] y \<bullet> \<^bold>\<langle>[x \<mapsto>\<^sub>s v]\<^bold>\<rangle> ;; P(y))"
  oops
      
end
                   
declare utp_local_state.var_open_def [upred_defs]
declare utp_local_state.var_close_def [upred_defs]  
declare utp_local_state.top_var_def [upred_defs]
declare utp_local_state.var_scope_def [upred_defs]  
    
subsection \<open> Relational State Spaces \<close>
  
text \<open> To illustrate the above technique, we instantiate it for relations with a @{typ nat} as
  the universe type. The following definition defines the state-space location, assignment operator,
  and injection universe for this. \<close>
  
definition rel_local_state :: 
  "'a::countable itself \<Rightarrow> ((nat, 's) local_scheme, 's, nat, 'a::countable) local_prim" where
  "rel_local_state t = \<lparr> sstate = 1\<^sub>L, sassigns = assigns_r, inj_local = nat_inj_univ \<rparr>"
  
abbreviation rel_local ("R\<^sub>l") where
"rel_local \<equiv> rel_local_state TYPE('a::countable)"
  
syntax
  "_rel_local_state_type" :: "type \<Rightarrow> logic" ("R\<^sub>l[_]")
  
translations
  "_rel_local_state_type a" => "CONST rel_local_state (_TYPE a)"
  
lemma get_rel_local [lens_defs]:
  "get\<^bsub>\<^bold>s\<^bsub>R\<^sub>l\<^esub>\<^esub> = id"
  by (simp add: rel_local_state_def lens_defs)
  
lemma rel_local_state [simp]: "utp_local_state R\<^sub>l"
  by (unfold_locales, simp_all add: upred_defs assigns_comp rel_local_state_def)

lemma sassigns_rel_state [simp]: "\<^bold>\<langle>\<sigma>\<^bold>\<rangle>\<^bsub>R\<^sub>l\<^esub> = \<langle>\<sigma>\<rangle>\<^sub>a"
  by (simp add: rel_local_state_def)

syntax
  "_rel_var_scope"      :: "id \<Rightarrow> logic \<Rightarrow> logic" ("var _ \<bullet> _" [0, 10] 10)
  "_rel_var_scope_type" :: "id \<Rightarrow> type \<Rightarrow> logic \<Rightarrow> logic" ("var _ :: _ \<bullet> _" [0, 0, 10] 10)

translations
  "_rel_var_scope x P" => "_var_scope R\<^sub>l x P"
  "_rel_var_scope_type x t P" => "_var_scope_type (_rel_local_state_type t) x t P"
 
text \<open> Next we prove some examples laws. \<close>
  
lemma rel_var_ex_1: "(var x :: string \<bullet> II) = II"
  by (rel_auto')

lemma rel_var_ex_2: "(var x \<bullet> x := 1) = II"
  by (rel_auto')
   
lemma rel_var_ex_3: "x \<bowtie> store \<Longrightarrow> x := 1 ;; open[R\<^sub>l['a::countable]] = open[R\<^sub>l['a]] ;; x := 1"
  by (metis pr_var_def rel_local_state sassigns_rel_state unrest_one utp_local_state.var_open_commute)

lemma rel_var_ex_4: "\<lbrakk> x \<bowtie> store; store \<sharp> v \<rbrakk> \<Longrightarrow> x := v ;; open[R\<^sub>l['a::countable]] = open[R\<^sub>l['a]] ;; x := v"
  by (metis pr_var_def rel_local_state sassigns_rel_state utp_local_state.var_open_commute)
 
lemma rel_var_ex_5: "\<lbrakk> x \<bowtie> store; store \<sharp> v \<rbrakk> \<Longrightarrow> x := v ;; (var y :: int \<bullet> P) = (var y :: int \<bullet> x := v ;; P)"
  by (simp add: utp_local_state.var_scope_def seqr_assoc[THEN sym] rel_var_ex_4, rel_auto', force+)

end