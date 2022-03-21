section \<open> Overloaded Expression Constructs \<close>

theory utp_expr_ovld
  imports "Z_Toolkit.Z_Toolkit" utp
begin recall_syntax

hide_const (open) Map.dom
hide_const (open) Map.ran

subsection \<open> Overloadable Constants \<close>

text \<open> For convenience, we often want to utilise the same expression syntax for multiple constructs.
  This can be achieved using ad-hoc overloading. We create a number of polymorphic constants and then
  overload their definitions using appropriate implementations. In order for this to work,
  each collection must have its own unique type. Thus we do not use the HOL map type directly,
  but rather our own partial function type, for example. \<close>

\<comment> \<open> Empty elements, for example empty set, nil list, 0... \<close> 
abbreviation (input) "uempty \<equiv> 0"

class ovrd = plus
begin

definition [upred_defs]: "ovrd = plus"

end

consts
  \<comment> \<open> Function application, map application, list application... \<close>
  uapply     :: "'f \<Rightarrow> 'k \<Rightarrow> 'v"
  \<comment> \<open> Function update, map update, list update... \<close>
  uupd       :: "'f \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 'f"
  \<comment> \<open> Collection summation \<close>
  usums      :: "'f \<Rightarrow> 'a"
  \<comment> \<open> Construct a collection from a list of entries \<close>
  uentries   :: "'k set \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> 'f"
  
text \<open> We need a function corresponding to function application in order to overload. \<close>
  
definition fun_apply :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
where "fun_apply f x = f x"

declare fun_apply_def [simp]

definition ffun_entries :: "'k set \<Rightarrow> ('k \<Rightarrow> bool) \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) ffun" where
"ffun_entries d P f = graph_ffun {(k, f k) | k. k \<in> d \<and> P k}"

text \<open> We then set up the overloading for a number of useful constructs for various collections. \<close>

definition [upred_defs]: "list_apply = nth"
definition [upred_defs]: "list_upd = list_augment"
definition [upred_defs]: "list_card = length"
definition [upred_defs]: "list_ran = set"


adhoc_overloading
  uapply rel_apply and uapply fun_apply and uapply list_apply and 
  uapply pfun_app and uapply ffun_app and
  uupd rel_update and uupd pfun_upd and uupd ffun_upd and uupd list_upd and
(*  udom Domain and udom pdom and udom fdom and udom seq_dom and *)
(*  uran Range and uran pran and uran fran and uran list_ran and *)
  usums list_sum and usums Sum and usums pfun_sum and
  uentries pfun_entries and uentries ffun_entries

subsection \<open> Syntax Translations \<close>

syntax
  "_uundef"     :: "logic" ("\<bottom>\<^sub>u")
  "_umap_empty" :: "logic" ("[]\<^sub>u")
  "_uapply"     :: "('a \<Rightarrow> 'b, '\<alpha>) uexpr \<Rightarrow> utuple_args \<Rightarrow> ('b, '\<alpha>) uexpr" ("_'(_')\<^sub>a" [999,0] 999)
  "_uovrd"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<oplus>" 65)
  "_umaplet"    :: "[logic, logic] => umaplet" ("_ /\<mapsto>/ _")
  ""            :: "umaplet => umaplets"             ("_")
  "_UMaplets"   :: "[umaplet, umaplets] => umaplets" ("_,/ _")
  "_UMapUpd"    :: "[logic, umaplets] => logic" ("_/'(_')\<^sub>u" [900,0] 900)
  "_UMap"       :: "umaplets => logic" ("(1[_]\<^sub>u)")
  "_udom"       :: "logic \<Rightarrow> logic" ("dom\<^sub>u'(_')")
  "_uran"       :: "logic \<Rightarrow> logic" ("ran\<^sub>u'(_')")
  "_usum"       :: "logic \<Rightarrow> logic" ("sum\<^sub>u'(_')")
  "_uentries"   :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("entr\<^sub>u'(_,_,_')")

translations
  \<comment> \<open> Pretty printing for adhoc-overloaded constructs \<close>
  "f(x)\<^sub>a"    <= "CONST uapply f x"
  "dom\<^sub>u(f)" <= "CONST dom f"
  "ran\<^sub>u(f)" <= "CONST ran f"  

  "f(k \<mapsto> v)\<^sub>u" <= "CONST uupd f k v"

  \<comment> \<open> Overloaded construct translations \<close>
  "f(x,y,z,u)\<^sub>a" == "CONST bop CONST uapply f (x,y,z,u)\<^sub>u"
  "f(x,y,z)\<^sub>a" == "CONST bop CONST uapply f (x,y,z)\<^sub>u"
  "f(x,y)\<^sub>a"  == "CONST bop CONST uapply f (x,y)\<^sub>u"  
  "f(x)\<^sub>a"    == "CONST bop CONST uapply f x"
  "sum\<^sub>u(A)" == "CONST uop CONST usums A"
  "dom\<^sub>u(f)" == "CONST uop CONST Relation_Toolkit.dom f"
  "ran\<^sub>u(f)" == "CONST uop CONST Relation_Toolkit.ran f"
  "[]\<^sub>u"     => "\<guillemotleft>CONST uempty\<guillemotright>"
  "\<bottom>\<^sub>u"     == "\<guillemotleft>CONST undefined\<guillemotright>"
  "entr\<^sub>u(d,P,f)" == "CONST trop CONST uentries d P \<guillemotleft>f\<guillemotright>"
  "_UMapUpd m (_UMaplets xy ms)" == "_UMapUpd (_UMapUpd m xy) ms"
  "_UMapUpd m (_umaplet  x y)"   == "CONST trop CONST uupd m x y"
  "_UMap ms"                      == "_UMapUpd []\<^sub>u ms"
  "_UMap (_UMaplets ms1 ms2)"     <= "_UMapUpd (_UMap ms1) ms2"
  "_UMaplets ms1 (_UMaplets ms2 ms3)" <= "_UMaplets (_UMaplets ms1 ms2) ms3"

subsection \<open> Simplifications \<close>

lemma ufun_apply_lit [simp]: 
  "\<guillemotleft>f\<guillemotright>(\<guillemotleft>x\<guillemotright>)\<^sub>a = \<guillemotleft>f(x)\<guillemotright>"
  by (transfer, simp)

lemma lit_plus_appl [lit_norm]: "\<guillemotleft>(+)\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x + y" by (simp add: uexpr_defs, transfer, simp)
lemma lit_minus_appl [lit_norm]: "\<guillemotleft>(-)\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x - y" by (simp add: uexpr_defs, transfer, simp)
lemma lit_mult_appl [lit_norm]: "\<guillemotleft>times\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x * y" by (simp add: uexpr_defs, transfer, simp)
lemma lit_divide_apply [lit_norm]: "\<guillemotleft>(/)\<guillemotright>(x)\<^sub>a(y)\<^sub>a = x / y" by (simp add: uexpr_defs, transfer, simp)

(*
lemma pfun_entries_apply [simp]:
  "(entr\<^sub>u(d,P,f) :: (('k, 'v) pfun, '\<alpha>) uexpr)(i)\<^sub>a = ((\<guillemotleft>f\<guillemotright>(i)\<^sub>a) \<triangleleft> i \<in>\<^sub>u d \<and> P(i)\<^sub>a \<triangleright> \<bottom>\<^sub>u)"
  by (pred_auto)
*)

lemma udom_uupdate_pfun [simp]:
  fixes m :: "(('k, 'v) pfun, '\<alpha>) uexpr"
  shows "dom\<^sub>u(m(k \<mapsto> v)\<^sub>u) = {k}\<^sub>u \<union>\<^sub>u dom\<^sub>u(m)"
  by (rel_auto)

lemma uapply_uupdate_pfun [simp]:
  fixes m :: "(('k, 'v) pfun, '\<alpha>) uexpr"
  shows "(m(k \<mapsto> v)\<^sub>u)(i)\<^sub>a = v \<triangleleft> i =\<^sub>u k \<triangleright> m(i)\<^sub>a"
  by (rel_auto)

subsection \<open> Indexed Assignment \<close>

syntax
  \<comment> \<open> Indexed assignment \<close>
  "_assignment_upd" :: "svid \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("(_[_] :=/ _)" [63, 0, 0] 62)

translations
  \<comment> \<open> Indexed assignment uses the overloaded collection update function \emph{uupd}. \<close>
  "_assignment_upd x k v" => "x := &x(k \<mapsto> v)\<^sub>u"

end