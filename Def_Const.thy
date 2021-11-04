section \<open> Defining Declared Constants \<close>

theory Def_Const
  imports Main
  keywords "def_consts" :: "thy_defn"
begin

text \<open> Add a simple command to define previously declared polymorphic constants. This is 
  particularly useful for handling given sets in Z. \<close>

ML \<open>
let fun def_const (n, v) thy = 
  let val Const (pn, typ) = Proof_Context.read_const {proper = false, strict = false} (Named_Target.theory_init thy) n
      val ctx = Overloading.overloading [(n, (pn, dummyT), false)] thy
      val pt = Syntax.check_term ctx (Type.constraint typ (Syntax.parse_term ctx v))
  in (Local_Theory.exit_global o snd o Local_Theory.define (((Binding.name n), NoSyn), ((Binding.name (n ^ "_def"), [Attrib.check_src @{context} (Token.make_src ("code", Position.none) [])]), pt))) ctx 
  end 
  val def_consts = fold def_const
in

Outer_Syntax.command @{command_keyword def_consts} "define a declared constant"
    (Scan.repeat1 ((Parse.name --| @{keyword "="}) -- Parse.term) >> (Toplevel.theory o def_consts))
  end
\<close>

end