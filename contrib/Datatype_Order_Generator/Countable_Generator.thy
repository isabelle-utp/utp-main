(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Countable datatypes *}

theory Countable_Generator
imports "~~/src/HOL/Library/Countable"
  Derive_Manager
begin

subsection "Introduction"

text {*
Brian Huffman and Alexander Krauss have developed a tactic
which automatically can prove that a datatype is countable.
We just make this tactic available in the derive-manager so that
one can conveniently write \texttt{derive countable some-datatype}.
*}

subsection "Features and Limitations"

text {*
We get similar limitation as for the order generator. 
For mutual recursive datatypes, only
for the first mentioned datatype the instantiations of the @{class countable}-class are
derived. 
*}

subsection "Installing the tactic"

text {*
There is nothing more to do, then to write some boiler-plate ML-code
for class-instantiation.
*}

setup {*
  let 
    fun derive dtyp_name _ thy = 
      let
        val base_name = Long_Name.base_name dtyp_name
        val _ = writeln ("proving that datatype " ^ base_name ^ " is countable")
        val sort = @{sort countable}
        val vs = 
          let val i = Datatype.the_spec thy dtyp_name |> #1 
          in map (fn (n,_) => (n, sort)) i end
        val thy' = Class.instantiation ([dtyp_name],vs,sort) thy
          |> Class.prove_instantiation_exit (fn ctxt => countable_tac ctxt 1)
        val _ = writeln ("registered " ^ base_name ^ " in class countable")
      in thy' end
  in 
    Derive_Manager.register_derive "countable" "proves that a datatype is countable" derive
  end
*}

end
