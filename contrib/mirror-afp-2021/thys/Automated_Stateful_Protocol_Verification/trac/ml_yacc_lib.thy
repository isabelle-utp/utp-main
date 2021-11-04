(*
(C) Copyright Andreas Viktor Hess, DTU, 2020
(C) Copyright Sebastian A. Mödersheim, DTU, 2020
(C) Copyright Achim D. Brucker, University of Exeter, 2020
(C) Copyright Anders Schlichtkrull, DTU, 2020

All Rights Reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are
met:

- Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

- Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

- Neither the name of the copyright holder nor the names of its
  contributors may be used to endorse or promote products
  derived from this software without specific prior written
  permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(*  Title:      ml_yacc_lib.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
*)

section\<open>ML Yacc Library\<close>
theory
  "ml_yacc_lib"
  imports
  Main
begin
ML_file "ml-yacc-lib/base.sig"
ML_file "ml-yacc-lib/join.sml"
ML_file "ml-yacc-lib/lrtable.sml"
ML_file "ml-yacc-lib/stream.sml"
ML_file "ml-yacc-lib/parser2.sml"

(*

The files in the directory "ml-yacc-lib" are part of the sml/NJ language 
processing tools. It was modified to work with Isabelle/ML by Achim D. Brucker.

It was downloaded from http://smlnj.cs.uchicago.edu/dist/working

Upstream Authors: The SML/NJ Team <smlnj-dev-list@lists.sourceforge.net>

Copyright:	2003-2008	The SML/NJ Fellowship
		1989-2002	Lucent Technologies
		1991-2003	John Reppy
		1996-1998,2000	YALE FLINT PROJECT
		1992		Vrije Universiteit, The Netherlands
		1989-1992	Andrew W. Appel, James S. Mattson, David R. Tarditi
		1988		Evans & Sutherland Computer Corporation, Salt Lake City, Utah

STANDARD ML OF NEW JERSEY COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.

Copyright (c) 1989-2002 by Lucent Technologies

Permission to use, copy, modify, and distribute this software and its
documentation for any purpose and without fee is hereby granted,
provided that the above copyright notice appear in all copies and that
both the copyright notice and this permission notice and warranty
disclaimer appear in supporting documentation, and that the name of
Lucent Technologies, Bell Labs or any Lucent entity not be used in
advertising or publicity pertaining to distribution of the software
without specific, written prior permission.

Lucent disclaims all warranties with regard to this software,
including all implied warranties of merchantability and fitness. In no
event shall Lucent be liable for any special, indirect or
consequential damages or any damages whatsoever resulting from loss of
use, data or profits, whether in an action of contract, negligence or
other tortious action, arising out of or in connection with the use
or performance of this software.


The SML/NJ distribution also includes code licensed under the same
terms as above, but with "David R. Tarditi Jr. and Andrew W. Appel",
"Vrije Universiteit" or "Evans & Sutherland" instead of "Lucent".

*)
end
