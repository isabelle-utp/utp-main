section {* VDM-SL in UTP *}

theory VDM
  imports
    PFOL
    "../deep/utp_deep"
begin

subsection {* Core operator definitions *}

typedef ('a, '\<alpha>) vexpr = "UNIV :: ('\<alpha> \<Rightarrow> 'a option) set" ..

type_synonym '\<alpha> vpred = "(bool, '\<alpha>) vexpr"

type_synonym 'a vtype = "'a set"

setup_lifting type_definition_vexpr

lift_definition vdefined :: "('a, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" ("\<D>\<^sub>v'(_')") is
"\<lambda> e b. Some (b \<in> dom e)" .

lift_definition visdefined :: "('a, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" ("!\<D>\<^sub>v'(_')") is
"\<lambda> e b. if b \<in> dom e then Some True else None" .

lift_definition vexpr :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) uexpr" ("\<lfloor>_\<rfloor>\<^sub>v") is
"\<lambda> e b. the(e b)" .

lift_definition vlift :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) vexpr" ("\<lceil>_\<rceil>\<^sub>v") is
"\<lambda> e b. Some (e b)" .

consts
  veuvar :: "'v \<Rightarrow> 'p" ("&\<^sub>v_" [999] 999)
  viuvar :: "'v \<Rightarrow> 'p" ("$\<^sub>v_" [999] 999)
  vouvar :: "'v \<Rightarrow> 'p" ("$\<^sub>v_\<acute>" [999] 999)

lift_definition vvar :: "('a, '\<alpha>) uvar \<Rightarrow> ('a, '\<alpha>) vexpr"
  is "\<lambda> x b. Some (get\<^bsub>x\<^esub> b)" .

definition vvar_dvar :: "'a::continuum dvar \<Rightarrow> ('a, '\<alpha>::vst) vexpr"
where "vvar_dvar x = vvar (x\<up>)"

declare vvar_dvar_def [upred_defs]

definition vivar :: "('a, '\<alpha>) uvar \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) vexpr"  where
"vivar x = vvar (in_var x)"

definition vivar_dvar :: "'a::continuum dvar \<Rightarrow> ('a, '\<alpha>::vst \<times> '\<beta>) vexpr"
where "vivar_dvar x = vivar (x\<up>)"

declare vivar_def [upred_defs]
declare vivar_dvar_def [upred_defs]

definition vovar :: "('a, '\<beta>) uvar \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>) vexpr"  where
"vovar x = vvar (out_var x)"

definition vovar_dvar :: "'a::continuum dvar \<Rightarrow> ('a, '\<alpha> \<times> '\<beta>::vst) vexpr"
where "vovar_dvar x = vovar (x\<up>)"

declare vovar_def [upred_defs]
declare vovar_dvar_def [upred_defs]

adhoc_overloading
  veuvar vvar and
  veuvar vvar_dvar and
  viuvar vivar and
  viuvar vivar_dvar and
  vouvar vovar and
  vouvar vovar_dvar

lift_definition vsubst :: "'\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr"
is "\<lambda> \<sigma> e b. e (\<sigma> b)" .

adhoc_overloading
  usubst vsubst

lift_definition vsubst_lookup :: "'\<alpha> usubst \<Rightarrow> ('a, '\<alpha>) uvar \<Rightarrow> ('a, '\<alpha>) vexpr" ("\<langle>_\<rangle>\<^sub>v")
is "\<lambda> \<sigma> x b. Some (get\<^bsub>x\<^esub> (\<sigma> b))" .

lift_definition unrest_vexpr :: "('a, '\<alpha>) uvar \<Rightarrow> ('b, '\<alpha>) vexpr \<Rightarrow> bool"
is "\<lambda> x e. (\<forall>b v. e(put\<^bsub>x\<^esub> b v) = e b)" .

adhoc_overloading
  unrest unrest_vexpr

lift_definition vlit :: "'a \<Rightarrow> ('a, '\<alpha>) vexpr" ("\<guillemotleft>_\<guillemotright>\<^sub>v") is "\<lambda> v b. Some v"  .

lift_definition vundef :: "('a, '\<alpha>) vexpr" ("\<bottom>\<^sub>v") is "\<lambda> b. None" .

lift_definition vuop :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> ('b, '\<alpha>) vexpr"
is "\<lambda> f v b. Option.bind (v b) f" .

lift_definition vbop :: "('a \<times> 'b \<rightharpoonup> 'c) \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> ('b, '\<alpha>) vexpr \<Rightarrow> ('c, '\<alpha>) vexpr"
is "\<lambda> (f :: 'a \<times> 'b \<rightharpoonup> 'c) u v b. (do { x <- u b; y <- v b; f (x, y) })" .

lift_definition vtop :: "('a \<times> 'b \<times> 'c \<rightharpoonup> 'd) \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> ('b, '\<alpha>) vexpr \<Rightarrow> ('c, '\<alpha>) vexpr \<Rightarrow> ('d, '\<alpha>) vexpr"
is "\<lambda> (f :: 'a \<times> 'b \<times> 'c \<rightharpoonup> 'd) u v w b. (do { x <- u b; y <- v b; z <- w b; f (x, y, z) })" .

lift_definition vconj :: "(bool, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr"
is "\<lambda> x y b. (x b \<and>\<^sub>k y b)" .

lift_definition vdisj :: "(bool, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr"
is "\<lambda> x y b. (x b \<or>\<^sub>k y b)" .

lift_definition vimpl :: "(bool, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr"
is "\<lambda> x y b. (x b \<Rightarrow>\<^sub>k y b)" .

lift_definition vnot :: "(bool, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr"
is "\<lambda> x b. \<not>\<^sub>k x b" .

lift_definition vtaut :: "(bool, '\<alpha>) vexpr \<Rightarrow> bool" ("[_]\<^sub>V")
is "\<lambda> p. \<forall> b. [p b]\<^sub>3" .

declare [[coercion vtaut]]

definition upfun :: "'a::type set \<Rightarrow> ('a \<Rightarrow> 'b::type) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
[upred_defs]: "upfun A f = ((\<lambda> v. Some (f v)) |` A)"

abbreviation "upfun' \<equiv> upfun UNIV"

abbreviation (input) "vuop' f \<equiv> vuop (upfun' f)"

definition bpfun :: "('a::type * 'b::type) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c::type) \<Rightarrow> ('a * 'b \<rightharpoonup> 'c)" where
[upred_defs]: "bpfun AB f = (\<lambda> (v1, v2). Some (f v1 v2)) |` AB"

abbreviation "bpfun' \<equiv> bpfun UNIV"

abbreviation (input) "vbop' f \<equiv> vbop (bpfun' f)"

definition tpfun :: "('a::type * 'b::type * 'c::type) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd::type) \<Rightarrow> ('a * 'b * 'c \<rightharpoonup> 'd)" where
[upred_defs]: "tpfun ABC f = (\<lambda> (v1, v2, v3). Some (f v1 v2 v3)) |` ABC"

abbreviation "tpfun' \<equiv> tpfun UNIV"

abbreviation (input) "vtop' f \<equiv> vtop (tpfun' f)"

abbreviation "true\<^sub>v  \<equiv> \<guillemotleft>True\<guillemotright>\<^sub>v"
abbreviation "false\<^sub>v \<equiv> \<guillemotleft>False\<guillemotright>\<^sub>v"

lift_definition vexists :: "'a vtype \<Rightarrow> ('a \<Rightarrow> (bool, '\<alpha>) vexpr) \<Rightarrow> (bool, '\<alpha>) vexpr"
is "\<lambda> A P b. (\<exists>\<^sub>k x. P x b)" .

lift_definition vforall :: "'a vtype \<Rightarrow> ('a \<Rightarrow> (bool, '\<alpha>) vexpr) \<Rightarrow> (bool, '\<alpha>) vexpr"
is "\<lambda> A P b. (\<forall>\<^sub>k x. P x b)" .

instantiation vexpr :: (zero, type) zero
begin
  definition zero_vexpr :: "('a, 'b) vexpr" where [upred_defs]: "zero_vexpr = vlit 0"
  instance ..
end

instantiation vexpr :: (one, type) one
begin
  definition one_vexpr :: "('a, 'b) vexpr" where [upred_defs]: "one_vexpr = vlit 1"
  instance ..
end

instantiation vexpr :: (plus, type) plus
begin

  definition plus_vexpr :: "('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr"
  where [upred_defs]: "plus_vexpr x y = vbop (bpfun' (op +)) x y"

instance ..
end

instantiation vexpr :: (minus, type) minus
begin

  definition minus_vexpr :: "('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr"
  where [upred_defs]: "minus_vexpr x y = vbop (bpfun' (op -)) x y"

instance ..
end

instantiation vexpr :: (times, type) times
begin

  definition times_vexpr :: "('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr"
  where [upred_defs]: "times_vexpr x y = vbop (bpfun' (op *)) x y"

instance ..
end

text {* We augment inverse and divide so that it is undefined when the divisor is 0 *}

instantiation vexpr :: ("{zero,inverse}", type) inverse
begin
  definition inverse_vexpr :: "('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr"
  where [upred_defs]: "inverse_vexpr n = vuop (upfun {x. x \<noteq> 0} inverse) n"

  definition divide_vexpr :: "('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr \<Rightarrow> ('a, 'b) vexpr"
  where [upred_defs]: "divide_vexpr m n = vbop (bpfun {(x,y). y \<noteq> 0} divide) m n"

instance ..
end

instance vexpr :: (semigroup_add, type) semigroup_add
  apply (intro_classes)
  apply (auto simp add: plus_vexpr_def times_vexpr_def, transfer, simp add: fun_eq_iff add.commute semiring_class.distrib_right semiring_class.distrib_left)+
  apply (rename_tac a b c x)
  apply (case_tac "a x")
  apply (simp_all)
  apply (case_tac "b x")
  apply (simp_all)
  apply (case_tac "c x")
  apply (simp_all add: bpfun_def add.assoc)
done

instance vexpr :: (numeral, type) numeral
  by (intro_classes)

definition vmap_apply :: "('a \<rightharpoonup> 'b) \<times> 'a \<Rightarrow> 'b option" where
"vmap_apply = (\<lambda> (f, x). f(x))"

definition vmap_update :: "('a \<rightharpoonup> 'b) \<times> 'a \<times> 'b \<rightharpoonup> ('a \<rightharpoonup> 'b)"
where "vmap_update = (\<lambda> (f, k, v). Some (fun_upd f k (Some v)))"

definition vseq_apply :: "'a list \<times> nat \<rightharpoonup> 'a" where
"vseq_apply = bpfun {(xs, i). length xs > i} nth"

definition vseq_update :: "'a list \<times> nat \<times> 'a \<rightharpoonup> 'a list" where
"vseq_update = tpfun {(xs, i, k). length xs > i} list_update"

consts
  vapply :: "'a \<times> 'b \<rightharpoonup> 'c"
  vupdate :: "'m \<times> 'a \<times> 'b \<rightharpoonup> 'm"

subsection {* VDM expression parser *}

adhoc_overloading
  vapply vmap_apply and
  vapply vseq_apply and
  vupdate vmap_update and
  vupdate vseq_update

nonterminal vtuple_args and vmaplet and vmaplets

text {* Tuples might need to be terminated with unit -- not totally sure at the moment *}

syntax
  "_vshEx"         :: "id \<Rightarrow> 'a vtype \<Rightarrow> logic \<Rightarrow> logic"   ("\<exists>\<^sub>v _ : _ \<bullet> _" [0, 0, 10] 10)
  "_vshAll"        :: "id \<Rightarrow> 'a vtype \<Rightarrow> logic \<Rightarrow> logic"   ("\<forall>\<^sub>v _ : _ \<bullet> _" [0, 0, 10] 10)
  "_vshbEx"        :: "id \<Rightarrow> ('a set, '\<alpha>) vexpr \<Rightarrow> logic \<Rightarrow> logic"   ("\<exists>\<^sub>v _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_vshbAll"       :: "id \<Rightarrow> ('a set, '\<alpha>) vexpr \<Rightarrow> logic \<Rightarrow> logic"   ("\<forall>\<^sub>v _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_vlength"       :: "('a list, '\<alpha>) vexpr \<Rightarrow> (nat, '\<alpha>) vexpr" ("len\<^sub>v'(_')")
  "_vnil"          :: "('a list, '\<alpha>) vexpr" ("[]\<^sub>v")
  "_vlist"         :: "args => ('a list, '\<alpha>) vexpr" ("[(_)]\<^sub>v")
  "_vhd"           :: "('a list, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr" ("hd\<^sub>v'(_')")
  "_vtl"           :: "('a list, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr" ("tl\<^sub>v'(_')")
  "_veq"           :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "=\<^sub>v" 50)
  "_vneq"          :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "<>\<^sub>v" 50)
  "_vless"         :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "<\<^sub>v" 50)
  "_vleq"          :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "\<le>\<^sub>v" 50)
  "_vgreat"        :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix ">\<^sub>v" 50)
  "_vgeq"          :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "\<ge>\<^sub>v" 50)
  "_vconj"         :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<and>\<^sub>v" 35)
  "_vdisj"         :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<or>\<^sub>v" 30)
  "_vimpl"         :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<Rightarrow>\<^sub>v" 25)
  "_vnot"          :: "'a \<Rightarrow> 'a" ("\<not>\<^sub>v _" [40] 40)
  "_vempset"       :: "('a set, '\<alpha>) vexpr" ("{}\<^sub>v")
  "_vset"          :: "args => ('a set, '\<alpha>) vexpr" ("{(_)}\<^sub>v")
  "_vunion"        :: "('a set, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr" (infixl "\<union>\<^sub>v" 65)
  "_vinter"        :: "('a set, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr" (infixl "\<inter>\<^sub>v" 70)
  "_vUnion"        :: "('a set set, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr" ("\<Union>\<^sub>v")
  "_vInter"        :: "('a set set, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr" ("\<Inter>\<^sub>v")
  "_vmem"          :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "\<in>\<^sub>v" 50)
  "_vnmem"         :: "('a, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "\<notin>\<^sub>v" 50)
  "_vsubset"       :: "('a set, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "\<subset>\<^sub>v" 50)
  "_vsubseteq"     :: "('a set, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha>) vexpr" (infix "\<subseteq>\<^sub>v" 50)
  "_vtuple"        :: "('a, '\<alpha>) vexpr \<Rightarrow> vtuple_args \<Rightarrow> ('a * 'b, '\<alpha>) vexpr" ("(1'(_,/ _')\<^sub>v)")
  "_vtuple_arg"    :: "('a, '\<alpha>) vexpr \<Rightarrow> vtuple_args" ("_")
  "_vtuple_args"   :: "('a, '\<alpha>) vexpr => vtuple_args \<Rightarrow> vtuple_args"     ("_,/ _")
  "_vapply"        :: "('a, '\<alpha>) vexpr \<Rightarrow> ('b, '\<alpha>) vexpr \<Rightarrow> ('c, '\<alpha>) vexpr" ("_'(_')\<^sub>v" [950,0] 950)
  "_vdom"          :: "('a \<rightharpoonup> 'b, '\<alpha>) vexpr \<Rightarrow> ('a set, '\<alpha>) vexpr" ("dom\<^sub>v'(_')")
  "_vrng"          :: "('a \<rightharpoonup> 'b, '\<alpha>) vexpr \<Rightarrow> ('b set, '\<alpha>) vexpr" ("rng\<^sub>v'(_')")
  "_vcard"         :: "('a set, '\<alpha>) vexpr \<Rightarrow> (nat, '\<alpha>) vexpr" ("card\<^sub>v'(_')")
  "_vmapempty"     :: "('a \<rightharpoonup> 'b, '\<alpha>) vexpr" ("\<lbrace>\<mapsto>\<rbrace>\<^sub>v")
  "_vmaplet"       :: "('a, '\<alpha>) vexpr \<Rightarrow> ('b, '\<alpha>) vexpr \<Rightarrow> vmaplet" ("_ /\<mapsto>/ _")
  "_vmaplets_unit" :: "vmaplet \<Rightarrow> vmaplets" ("_")
  "_vmaplets"      :: "vmaplet \<Rightarrow> vmaplets \<Rightarrow> vmaplets" ("_,/ _")
  "_vmap_enum"     :: "vmaplets \<Rightarrow> ('a \<rightharpoonup> 'b, '\<alpha>) vexpr" ("\<lbrace>_\<rbrace>\<^sub>v")
  "_vdot" :: "('a, '\<alpha>) vexpr \<Rightarrow> id \<Rightarrow> ('b, '\<alpha>) vexpr" ("_.\<^sub>v_" [998,998] 998)

definition [upred_defs]: "hd_pre = {x. length x > 0}"

abbreviation "map_upd f k v \<equiv> fun_upd f k (Some v)"

definition vneq_def [upred_defs]:
  "vneq x y = vbop (bpfun' op \<noteq>) x y"

translations
  "\<forall>\<^sub>v x : A \<bullet> P" == "CONST vforall A (\<lambda> x. P)"
  "\<exists>\<^sub>v x : A \<bullet> P" == "CONST vexists A (\<lambda> x. P)"
  "[]\<^sub>v" == "\<guillemotleft>[]\<guillemotright>\<^sub>v"
  "[x, xs]\<^sub>v" == "CONST vbop (CONST bpfun' op #) x [xs]\<^sub>v"
  "[x]\<^sub>v"     == "CONST vbop (CONST bpfun' op #) x \<guillemotleft>[]\<guillemotright>\<^sub>v"
  "len\<^sub>v(xs)" == "CONST vuop (CONST upfun' CONST length) xs"
  "hd\<^sub>v(xs)"  == "CONST vuop (CONST upfun CONST hd_pre CONST hd) xs"
  "tl\<^sub>v(xs)"  == "CONST vuop (CONST upfun CONST hd_pre CONST tl) xs"
  "x =\<^sub>v y"   == "CONST vbop (CONST bpfun' op =) x y"
  "x <>\<^sub>v y"   == "CONST vneq x y"
  "x <\<^sub>v y"   == "CONST vbop (CONST bpfun' (op <)) x y"
  "x \<le>\<^sub>v y"   == "CONST vbop (CONST bpfun' (op \<le>)) x y"
  "x >\<^sub>v y"   == "y <\<^sub>v x"
  "x \<ge>\<^sub>v y"   == "y \<le>\<^sub>v x"
  "p \<and>\<^sub>v q" == "CONST vconj p q"
  "p \<or>\<^sub>v q" == "CONST vdisj p q"
  "p \<Rightarrow>\<^sub>v q" == "CONST vimpl p q"
  "\<not>\<^sub>v p"   == "CONST vnot p"
  "{}\<^sub>v"      == "\<guillemotleft>{}\<guillemotright>\<^sub>v"
  "{x, xs}\<^sub>v" == "CONST vbop (CONST bpfun' CONST insert) x {xs}\<^sub>v"
  "{x}\<^sub>v"     == "CONST vbop (CONST bpfun' CONST insert) x \<guillemotleft>{}\<guillemotright>\<^sub>v"
  "A \<union>\<^sub>v B"   == "CONST vbop (CONST bpfun' CONST Set.union) A B"
  "A \<inter>\<^sub>v B"   == "CONST vbop (CONST bpfun' CONST Set.inter) A B"
  "\<Union>\<^sub>v A"     == "CONST vuop (CONST upfun' CONST Union) A"
  "\<Inter>\<^sub>v A"     == "CONST vuop (CONST upfun' CONST Inter) A"
  "x \<in>\<^sub>v A" == "CONST vbop (CONST bpfun' (op \<in>)) x A"
  "x \<notin>\<^sub>v A" => "\<not>\<^sub>v (x \<in>\<^sub>v A)"
  "A \<subset>\<^sub>v B" == "CONST vbop (CONST bpfun' (op \<subset>)) A B"
  "A \<subseteq>\<^sub>v B" == "CONST vbop (CONST bpfun' (op \<subseteq>)) A B"
  "(x, y)\<^sub>v" == "CONST vbop (CONST bpfun' CONST Pair) x y"
  "_vtuple x (_vtuple_args y z)" == "_vtuple x (_vtuple_arg (_vtuple y z))"
  "f(x)\<^sub>v"  == "CONST vbop CONST vapply f x"
  "dom\<^sub>v(f)" == "CONST vuop (CONST upfun' CONST dom) f"
  "rng\<^sub>v(f)" == "CONST vuop (CONST upfun' CONST ran) f"
  "card\<^sub>v(f)" == "CONST vuop (CONST upfun' CONST card) f"
  "\<lbrace>\<mapsto>\<rbrace>\<^sub>v"   == "\<guillemotleft>Map.empty\<guillemotright>\<^sub>v"
  (* For some reason I can't get maps to show correctly -- seems something is wrong with these rules *)
  "_vmap_enum (_vmaplets_unit (_vmaplet k v))" == "CONST vbop (CONST bpfun' (CONST map_upd Map.empty)) k v"
  "_vmap_enum (_vmaplets (_vmaplet k v) m)" == "CONST vtop (CONST tpfun' CONST map_upd) (_vmap_enum m) k v"
  "_vdot e k" => "CONST vuop (CONST upfun' k) e"
  "\<lbrace>\<mapsto>\<rbrace>\<^sub>v"     <=   "CONST vlit CONST Map.empty"

abbreviation "vforallSet A P \<equiv> vforall UNIV (\<lambda> x. \<guillemotleft>x\<guillemotright>\<^sub>v \<in>\<^sub>v A \<Rightarrow>\<^sub>v P x)"
abbreviation "vexistsSet A P \<equiv> vexists UNIV (\<lambda> x. \<guillemotleft>x\<guillemotright>\<^sub>v \<in>\<^sub>v A \<Rightarrow>\<^sub>v P x)"

translations
  "\<forall>\<^sub>v x \<in> A \<bullet> P" == "CONST vforallSet A (\<lambda> x. P)"
  "\<exists>\<^sub>v x \<in> A \<bullet> P" == "CONST vexistsSet A (\<lambda> x. P)"

subsection {* Proof Support *}

text {* t may be better to define a designated transfer tactic for VDM. *}

theorem vexpr_eq_iff [uexpr_transfer_laws]:
"e\<^sub>1 = e\<^sub>2 \<longleftrightarrow> Rep_vexpr e\<^sub>1 = Rep_vexpr e\<^sub>2"
apply (transfer)
apply (rule refl)
done

update_uexpr_rep_eq_thms -- {* Re-reads @[thm [source] uexpr_rep_eq_thms}. *}

declare Abs_vexpr_inverse [uexpr_transfer_extra]
declare Rep_vexpr_inverse [uexpr_transfer_extra]

lemmas vexpr_rep_eq_thms [uexpr_transfer_extra] =
  VDM.vundef.rep_eq
  VDM.vlit.rep_eq
  (* VDM.vexpr.rep_eq *)
  VDM.vlift.rep_eq
  VDM.vvar.rep_eq
  VDM.vnot.rep_eq
  VDM.vtaut.rep_eq
  VDM.vsubst.rep_eq
  VDM.vsubst_lookup.rep_eq
  VDM.vuop.rep_eq
  VDM.vdefined.rep_eq
  VDM.vexists.rep_eq
  VDM.vforall.rep_eq
  VDM.vconj.rep_eq
  VDM.vdisj.rep_eq
  VDM.vimpl.rep_eq
  VDM.visdefined.rep_eq
  VDM.unrest_vexpr.rep_eq
  VDM.vbop.rep_eq
  VDM.vtop.rep_eq

subsection {* VDM Unrestriction Laws *}

text {* Unrestriction is effectively semantic freshness; an expression is unrestricted by a
        variable if the value of that variable has no effect on the value of the expresssion. *}

lemma vexpr_unrest [unrest]:
  "x \<sharp> v \<Longrightarrow> x \<sharp> \<lfloor>v\<rfloor>\<^sub>v"
  by (transfer; clarsimp)

lemma vvar_unrest [unrest]:
  "x \<bowtie> y \<Longrightarrow> y \<sharp> &\<^sub>vx"
  by (transfer; clarsimp)

lemma vlit_unrest [unrest]:
  "x \<sharp> \<guillemotleft>v\<guillemotright>\<^sub>v"
  by (transfer; clarsimp)

lemma vuop_unrest [unrest]:
  "x \<sharp> v \<Longrightarrow> x \<sharp> vuop f v"
  by (transfer; clarsimp)

lemma vbop_unrest [unrest]:
  "\<lbrakk> x \<sharp> u; x \<sharp> v \<rbrakk> \<Longrightarrow> x \<sharp> vbop f u v"
  by (transfer; clarsimp)

lemma vtop_unrest [unrest]:
  "\<lbrakk> x \<sharp> u; x \<sharp> v; x \<sharp> w \<rbrakk> \<Longrightarrow> x \<sharp> vtop f u v w"
  by (transfer; clarsimp)

subsection {* VDM Substitution *}

lemma vsubst_lookup_upd [usubst]:
  assumes "vwb_lens x" "\<D>\<^sub>v(v) = true\<^sub>v"
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s \<lfloor>v\<rfloor>\<^sub>v)\<rangle>\<^sub>v x = v"
  using assms
  apply (simp add: subst_upd_uvar_def, transfer)
  apply (rule ext, auto simp add: dom_def fun_eq_iff)
done

lemma vsubst_lookup_upd_indep [usubst]:
  assumes "vwb_lens x" "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<mapsto>\<^sub>s v)\<rangle>\<^sub>v x = \<langle>\<sigma>\<rangle>\<^sub>v x"
  using assms
  by (simp add: subst_upd_uvar_def, transfer, simp)

lemma vvar_subst [usubst]: "\<sigma> \<dagger> &\<^sub>vx = \<langle>\<sigma>\<rangle>\<^sub>v x"
  by (transfer; clarsimp)

lemma vsubst_vnot [usubst]:
  "\<sigma> \<dagger> (\<not>\<^sub>v p ) = (\<not>\<^sub>v (\<sigma> \<dagger> p))"
  by (transfer; clarsimp)

lemma vsubst_vconj [usubst]:
  "\<sigma> \<dagger> (p \<and>\<^sub>v q) = (\<sigma> \<dagger> p \<and>\<^sub>v \<sigma> \<dagger> q)"
  by (transfer; clarsimp)

lemma vsubst_vdisj [usubst]:
  "\<sigma> \<dagger> (p \<or>\<^sub>v q) = (\<sigma> \<dagger> p \<or>\<^sub>v \<sigma> \<dagger> q)"
  by (transfer; clarsimp)

lemma vsubst_vlit [usubst]:
  "\<sigma> \<dagger> \<guillemotleft>v\<guillemotright>\<^sub>v = \<guillemotleft>v\<guillemotright>\<^sub>v"
  by (transfer; clarsimp)

lemma vsubst_vuop [usubst]:
  "\<sigma> \<dagger> (vuop f x) = vuop f (\<sigma> \<dagger> x)"
  by (transfer; clarsimp)

lemma vsubst_vbop [usubst]:
  "\<sigma> \<dagger> (vbop f x y) = vbop f (\<sigma> \<dagger> x) (\<sigma> \<dagger> y)"
  by (transfer; clarsimp)

lemma vsubst_vtop [usubst]:
  "\<sigma> \<dagger> (vtop f x y z) = vtop f (\<sigma> \<dagger> x) (\<sigma> \<dagger> y) (\<sigma> \<dagger> z)"
  by (transfer; clarsimp)

lemma vsubst_vexpr [usubst]:
  "\<sigma> \<dagger> \<lfloor>v\<rfloor>\<^sub>v = \<lfloor>\<sigma> \<dagger> v\<rfloor>\<^sub>v"
  by (transfer; clarsimp)

subsection {* Proof setup *}

text {* We here extend the set of intro-elim rules to allow discharging lifted HOL operators. These
        rule show how tautologies expressed in terms of lifted HOL functions can be directly
        dropped to the HOL operators, which makes proof support direct. *}

lemma upfun'_tvl [simp]: "[upfun' f x]\<^sub>3 = f x"
  by (auto simp add: upfun_def tvl_taut_def)

lemma upfun'_tvlE [elim]: "\<lbrakk> [upfun' f x]\<^sub>3; f x \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp)

lemma upfun'_tvlI [intro]: "f x \<Longrightarrow> [upfun' f x]\<^sub>3"
  by (simp)

lemma bpfun'_tvl [simp]: "[bpfun' f (x, y)]\<^sub>3 = f x y"
  by (auto simp add: bpfun_def tvl_taut_def)

lemma bpfun'_tvlE [elim]: "\<lbrakk> [bpfun' f (x, y)]\<^sub>3; f x y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (simp)

lemma bpfun'_tvlI [intro]: "f x y \<Longrightarrow> [bpfun' f (x, y)]\<^sub>3"
  by (simp)

lemma bpfun'_defined [intro,simp]:
  "\<D>\<^sub>3 (bpfun' f x)"
  by (auto simp add: tvl_defined_def bpfun_def split_beta)

text {* We also set up some useful default simplifications. *}

lemma true_vdm [simp]: "\<lfloor>true\<^sub>v\<rfloor>\<^sub>v = true"
  by (pred_auto)

lemma false_vdm [simp]: "\<lfloor>false\<^sub>v\<rfloor>\<^sub>v = false"
  by (pred_auto)

lemma vconj_left_unit [simp]: "(true\<^sub>v \<and>\<^sub>v p) = p"
  by (pred_auto)

lemma vconj_right_unit [simp]: "(p \<and>\<^sub>v true\<^sub>v) = p"
  by (pred_auto)

lemma vmem_UNIV [simp]: "(x \<in>\<^sub>v \<guillemotleft>UNIV\<guillemotright>\<^sub>v) = !\<D>\<^sub>v(x)"
  by (pred_auto)

lemma restrict_map_UNIV [simp]: "f |` UNIV = f"
  by (simp add: restrict_map_def)

lemma vmem_Collect_1 [simp]: "(x \<in>\<^sub>v \<guillemotleft>{x. P x}\<guillemotright>\<^sub>v) = vuop (upfun' P) x"
  by (pred_auto)

lemma vmem_Collect_2 [simp]: "((x, y)\<^sub>v \<in>\<^sub>v \<guillemotleft>{x. P x}\<guillemotright>\<^sub>v) = vbop (upfun' P) x y"
  by (pred_auto)

lemma upfun'_simp [simp]: "upfun' f x = Some (f x)"
  by (pred_auto)

lemma bpfun'_simp [simp]: "bpfun' f (x, y) = Some (f x y)"
  by (pred_auto)

text {* Here we are using introduction / elimination to prove some simple properties *}

lemma example1: "(\<forall>\<^sub>v x : Nats \<bullet> \<guillemotleft>x\<guillemotright>\<^sub>v >\<^sub>v \<guillemotleft>1 :: nat\<guillemotright>\<^sub>v) = false\<^sub>v"
  by (pred_auto)

lemma example2: "(\<exists>\<^sub>v x : Nats \<bullet> \<guillemotleft>x\<guillemotright>\<^sub>v >\<^sub>v \<guillemotleft>1 :: nat\<guillemotright>\<^sub>v) = true\<^sub>v"
  by (pred_auto)

subsection {* Definedness laws *}

text {* The proof support also relies on a decision regarding definedness of various operators. Here
        we prove some key laws. *}

lemma vdefined_visdefined [simp]: "(\<D>\<^sub>v(x) \<and>\<^sub>v !\<D>\<^sub>v(x)) = \<D>\<^sub>v(x)"
  by (pred_auto)

lemma vdefined_vdefined [simp]: "\<D>\<^sub>v(\<D>\<^sub>v(v)) = true\<^sub>v"
  by (pred_auto)

lemma vdefined_vlit [simp]: "\<D>\<^sub>v(\<guillemotleft>v\<guillemotright>\<^sub>v) = true\<^sub>v"
  by (pred_auto)

lemma vdefined_zero [simp]: "\<D>\<^sub>v(0) = true\<^sub>v"
  by (pred_auto)

lemma vdefined_one [simp]: "\<D>\<^sub>v(1) = true\<^sub>v"
  by (pred_auto)

lemma vdefined_upfun: "\<D>\<^sub>v(vuop (upfun A f) x) = (\<D>\<^sub>v(x) \<and>\<^sub>v x \<in>\<^sub>v \<guillemotleft>A\<guillemotright>\<^sub>v)"
  apply (transfer)
  apply (rule ext)
  apply (auto simp add: upfun_def bpfun_def dom_def)
  apply (rename_tac A f x b)
  apply (case_tac "x b")
  apply (auto)
  apply (meson domI domIff restrict_out)
done

lemma vdefined_upfun' [simp]: "\<D>\<^sub>v(vuop (upfun' f) x) = \<D>\<^sub>v(x)"
  by (simp add: vdefined_upfun)

lemma vdefined_bpfun: "\<D>\<^sub>v(vbop (bpfun A f) x y) = (\<D>\<^sub>v(x) \<and>\<^sub>v \<D>\<^sub>v(y) \<and>\<^sub>v (x, y)\<^sub>v \<in>\<^sub>v \<guillemotleft>A\<guillemotright>\<^sub>v)"
  apply (transfer)
  apply (rule ext)
  apply (rename_tac A f x y b)
  apply (auto simp add: bpfun_def dom_def)
  apply (case_tac "x b")
  apply (auto)
  apply (case_tac "y b")
  apply (auto)
  apply (metis option.distinct(2) restrict_out)
done

(* FIXME: Do this proof properly! *)

lemma vdefined_bpfun' [simp]: "\<D>\<^sub>v(vbop (bpfun' f) x y) = (\<D>\<^sub>v(x) \<and>\<^sub>v \<D>\<^sub>v(y))"
  by (pred_auto)

lemma vdefined_tpfun: "\<D>\<^sub>v(vtop (tpfun A f) x y z) = (\<D>\<^sub>v(x) \<and>\<^sub>v \<D>\<^sub>v(y) \<and>\<^sub>v \<D>\<^sub>v(z) \<and>\<^sub>v (x, y, z)\<^sub>v \<in>\<^sub>v \<guillemotleft>A\<guillemotright>\<^sub>v)"
  apply (transfer)
  apply (rule ext)
  apply (rename_tac A f x y z b)
  apply (auto simp add: tpfun_def dom_def)
  apply (case_tac "x b")
  apply (auto)
  apply (case_tac "y b")
  apply (auto)
  apply (case_tac "z b")
  apply (auto)
  apply (metis option.distinct(2) restrict_out)
done

lemma vdefined_upfunI:
  assumes "(x \<in>\<^sub>v \<guillemotleft>A\<guillemotright>\<^sub>v) = P(x)"
  shows "\<D>\<^sub>v(vuop (upfun A f) x) = (\<D>\<^sub>v(x) \<and>\<^sub>v P(x))"
  using assms by (simp add: vdefined_upfun hd_pre_def)

lemma vdefined_vmap_update [simp]:
  "\<D>\<^sub>v(vtop vmap_update m k v) = (\<D>\<^sub>v(m) \<and>\<^sub>v \<D>\<^sub>v(k) \<and>\<^sub>v \<D>\<^sub>v(v))"
  apply (transfer)
  apply (rule ext)
  apply (auto)
  apply (simp add: vdefined_tpfun vmap_update_def)
done

lemma vdefined_undef [simp]:
  "\<D>\<^sub>v(\<bottom>\<^sub>v) = false\<^sub>v"
  by (pred_auto)

lemma vdefined_vvar [simp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "\<D>\<^sub>v(&\<^sub>vx) = true\<^sub>v"
  by (transfer, simp)

lemma vdefined_vmap_apply [simp]:
  "\<D>\<^sub>v(m(x)\<^sub>v) = (\<D>\<^sub>v(x) \<and>\<^sub>v \<D>\<^sub>v(m) \<and>\<^sub>v x \<in>\<^sub>v dom\<^sub>v(m))"
  apply (transfer, simp add:upfun_def bpfun_def vmap_apply_def)
  apply (rule ext)
  apply (rename_tac m x b)
  apply (case_tac "x b")
  apply (auto simp add: dom_def)
  apply (simp add: bind_eq_None_conv)
  apply (case_tac "m b")
  apply (auto simp add: dom_def)
done

lemma vdefined_divide [simp]: "\<D>\<^sub>v(x / y) = (\<D>\<^sub>v(x) \<and>\<^sub>v \<D>\<^sub>v(y) \<and>\<^sub>v y <>\<^sub>v 0)"
  apply (simp add: upred_defs divide_vexpr_def zero_vexpr_def vdefined_bpfun)
  apply (transfer, rule ext, auto)
  apply (case_tac "y b", auto simp add: domIff)
done

lemma vdefined_vhd [simp]: "\<D>\<^sub>v(hd\<^sub>v(xs)) = (\<D>\<^sub>v(xs) \<and>\<^sub>v len\<^sub>v(xs) >\<^sub>v \<guillemotleft>0\<guillemotright>\<^sub>v)"
  by (rule vdefined_upfunI, transfer, simp add: vdefined_upfun upfun_def bpfun_def hd_pre_def)

lemma vdefined_vtl [simp]: "\<D>\<^sub>v(tl\<^sub>v(xs)) = (\<D>\<^sub>v(xs) \<and>\<^sub>v len\<^sub>v(xs) >\<^sub>v \<guillemotleft>0\<guillemotright>\<^sub>v)"
  by (rule vdefined_upfunI, transfer, simp add: vdefined_upfun upfun_def bpfun_def hd_pre_def)
subsection {* Deduction rules *}

lemma vdm_bind_on_dom_1 [intro]:
  "\<D>\<^sub>3 (\<lfloor>b \<in> dom p\<rfloor> \<and>\<^sub>k p b)"
  by (auto simp add: kand_def)

subsection {* VDM-SL programs *}

text {* Assignment requires that the expression assigned to the
        expression be defined, otherwise an abort will result. *}

definition vassign_uvar :: "('a, '\<alpha>) uvar \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> '\<alpha> hrel_des" where
[urel_defs]: "vassign_uvar x v = (\<lfloor> \<D>\<^sub>v(v) \<rfloor>\<^sub>v \<turnstile>\<^sub>n (x := \<lfloor>v\<rfloor>\<^sub>v))"

definition vassign_dvar :: "'a::continuum dvar \<Rightarrow> ('a, '\<alpha>::vst) vexpr \<Rightarrow> '\<alpha> hrel_des" where
[urel_defs]: "vassign_dvar x v = vassign_uvar (x\<up>) v"

consts
  vassign :: "'v \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> '\<alpha> hrel_des"

adhoc_overloading
  vassign vassign_uvar and vassign vassign_dvar

text {* We define a variant of assignment that updates a particular field in a record *}

abbreviation "vassign_upd x f v \<equiv> vassign_uvar x (vbop (bpfun' (\<lambda> k. f (\<lambda>_. k))) v (&\<^sub>vx))"
(* abbreviation "vassign_map m k v \<equiv> vassign m (vtop vupdate (&\<^sub>vm) k v)" *)

(* TODO: Implement pretty print rules for record update assignment *)

syntax
  "_vassign"     :: "id \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> '\<alpha> hrel_des" (infix ":=\<^sub>v" 40)
  "_vassign_rec" :: "id \<Rightarrow> id \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> '\<alpha> hrel" ("_.\<^sub>v_/ :=\<^sub>v/ _" [999,999,40] 40)
  "_vassign_map" :: "id \<Rightarrow> ('a, '\<alpha>) vexpr \<Rightarrow> ('b, '\<alpha>) vexpr \<Rightarrow> '\<alpha> hrel" ("_'(_')/ :=\<^sub>v/ _" [999,999,40] 40)

translations
  "x :=\<^sub>v v" == "CONST vassign x v"
  "x.\<^sub>vf :=\<^sub>v v" == "CONST vassign_upd x (_update_name f) v"
  "m(k) :=\<^sub>v v" => "CONST vassign m (CONST vtop CONST vupdate (&\<^sub>vm) k v)"

lemma vassign_undef:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x :=\<^sub>v \<bottom>\<^sub>v) = \<bottom>\<^sub>D"
  by (rel_auto robust)

lemma H1_H3_vdm_assign [simp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x :=\<^sub>v v) is H1_H3"
  by (metis H1_rdesign H3_ndesign Healthy_def ndesign_def vassign_uvar_def)

lemma hd_nil_abort:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x :=\<^sub>v hd\<^sub>v([]\<^sub>v)) = true"
  by (rel_auto)

definition wp_vdm :: "('\<alpha>, '\<beta>) rel_des \<Rightarrow> '\<beta> vpred \<Rightarrow> '\<alpha> vpred" (infix "wp\<^sub>v" 60)
where "Q wp\<^sub>v r = \<lceil>Q wp\<^sub>D \<lfloor>r\<rfloor>\<^sub>v\<rceil>\<^sub>v"

text {* Here we augment the set of design weakest precondition laws
        with the VDM assignment operator *}

theorem wpd_vdm_assign [wp]:
  fixes x :: "('a, '\<alpha>) uvar"
  shows "(x :=\<^sub>v v) wp\<^sub>D r = (\<lfloor>\<D>\<^sub>v(v)\<rfloor>\<^sub>v \<and> r\<lbrakk>\<lfloor>v\<rfloor>\<^sub>v/x\<rbrakk>)"
  by (simp add: vassign_uvar_def wp)

lemma wp_calc_test_1:
  "\<lbrakk> vwb_lens x; vwb_lens y \<rbrakk> \<Longrightarrow> (y :=\<^sub>v hd\<^sub>v(&\<^sub>vx)) wp\<^sub>D true
                                  = \<lfloor>len\<^sub>v(&\<^sub>vx) >\<^sub>v \<guillemotleft>0\<guillemotright>\<^sub>v\<rfloor>\<^sub>v"
  by (simp add: wp usubst)

lemma wp_calc_test_2:
  "\<lbrakk> vwb_lens x; vwb_lens y \<rbrakk> \<Longrightarrow> (y :=\<^sub>v 1 / hd\<^sub>v(&\<^sub>vx)) wp\<^sub>D true
                                  = \<lfloor>len\<^sub>v(&\<^sub>vx) >\<^sub>v \<guillemotleft>0\<guillemotright>\<^sub>v \<and>\<^sub>v hd\<^sub>v(&\<^sub>vx) <>\<^sub>v 0\<rfloor>\<^sub>v"
  by (simp add: wp usubst)

subsection {* VDM-SL operations *}

definition vdm_sl_op :: "(bool, '\<alpha>) vexpr \<Rightarrow> (bool, '\<alpha> \<times> '\<alpha>) vexpr \<Rightarrow> '\<alpha> hrel_des \<Rightarrow> '\<alpha> hrel_des"
  ("[pre _ post _ body _]\<^sub>v")
where [upred_defs]: "[pre pr post po body bd]\<^sub>v = (\<lfloor>\<D>\<^sub>v(pr)\<rfloor>\<^sub>v \<and> \<lfloor>pr\<rfloor>\<^sub>v) \<turnstile>\<^sub>n (\<lfloor>\<D>\<^sub>v(po)\<rfloor>\<^sub>v \<and> \<lfloor>po\<rfloor>\<^sub>v \<and> post\<^sub>D(bd))"

lemma vdm_sl_op_H1_H3 [closure]:
  "[pre p post Q body R]\<^sub>v is \<^bold>N"
  by (simp add: vdm_sl_op_def, metis H1_rdesign H3_ndesign Healthy_def ndesign_def)

lemma wp_vdm_sl_op [wp]: "[pre p post Q body R]\<^sub>v wp\<^sub>D r = ((\<lfloor>\<D>\<^sub>v(p)\<rfloor>\<^sub>v \<and> \<lfloor>p\<rfloor>\<^sub>v) \<and> (\<lfloor>\<D>\<^sub>v(Q)\<rfloor>\<^sub>v \<and> \<lfloor>Q\<rfloor>\<^sub>v \<and> post\<^sub>D(R)) wp r)"
  by (simp add: vdm_sl_op_def wp)

(*
lemma vdm_sl_op_true_pre_post [simp]:
  "[pre true\<^sub>v post true\<^sub>v body p \<turnstile>\<^sub>r q]\<^sub>v = true \<turnstile>\<^sub>r q"
  by (simp add: vdm_sl_op_def, pred_auto)

lemma vdm_sl_op_false_pre [simp]:
  "[pre false\<^sub>v post p body b]\<^sub>v = true"
  by (simp add: vdm_sl_op_def, pred_auto)
*)

subsection {* Support for local variables *}

alphabet vlocal =
  vlocals :: "vstore"

instantiation vlocal_ext :: (type) vst
begin
  definition [simp]: "vstore_lens_vlocal_ext = vlocals"
instance
  by (intro_classes, unfold_locales, simp_all)
end
end