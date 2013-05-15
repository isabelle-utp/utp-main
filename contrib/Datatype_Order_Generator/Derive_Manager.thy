(*  Title:       Deriving class instances for datatypes
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2012 René Thiemann

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

header {* Derive manager *}

theory Derive_Manager
imports Main
keywords "print_derives" :: diag
   and   "derive" :: thy_decl
begin

ML_file "derive_aux.ML" 
ML_file "derive_manager.ML"

text {*
The derive manager allows to install various deriving-commands, e.g., to derive 
orders, pretty-printer, hash-functions, \ldots. -functions. All of the registered commands
are then accessible via the \texttt{derive}-command, e.g., \texttt{derive hashable list}
would automatically derive a hash-function for the datatype \texttt{list}.

There is also the diagnostic command \texttt{print-derives} which shows a list of options
what can currently be derived.
*}

(*
setup {*
  Derive_Manager.register_derive "dummy" "just a test of the deriving setup" (fn dtname => 
  let val _ = Output.writeln ("testing deriving dummy on datatype " ^ dtname) in I end)
*}

print_derives
derive dummy "term"
*)
end
