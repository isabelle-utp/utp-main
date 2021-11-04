(******************************************************************************
 * STANDARD ML OF NEW JERSEY COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.
 * 
 * Copyright (c) 1989-2002 by Lucent Technologies
 * 
 * Permission to use, copy, modify, and distribute this software and its
 * documentation for any purpose and without fee is hereby granted,
 * provided that the above copyright notice appear in all copies and that
 * both the copyright notice and this permission notice and warranty
 * disclaimer appear in supporting documentation, and that the name of
 * Lucent Technologies, Bell Labs or any Lucent entity not be used in
 * advertising or publicity pertaining to distribution of the software
 * without specific, written prior permission.
 * 
 * Lucent disclaims all warranties with regard to this software,
 * including all implied warranties of merchantability and fitness. In no
 * event shall Lucent be liable for any special, indirect or
 * consequential damages or any damages whatsoever resulting from loss of
 * use, data or profits, whether in an action of contract, negligence or
 * other tortious action, arising out of or in connection with the use
 * or performance of this software.
 ******************************************************************************)
(* $Id$ *)

(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* Stream: a structure implementing a lazy stream.  The signature STREAM
   is found in base.sig *)

structure Stream :> STREAM =
struct
   datatype 'a str = EVAL of 'a * 'a str Unsynchronized.ref | UNEVAL of (unit->'a)

   type 'a stream = 'a str Unsynchronized.ref

   fun get(Unsynchronized.ref(EVAL t)) = t
     | get(s as Unsynchronized.ref(UNEVAL f)) = 
	    let val t = (f(), Unsynchronized.ref(UNEVAL f)) in s := EVAL t; t end

   fun streamify f = Unsynchronized.ref(UNEVAL f)
   fun cons(a,s) = Unsynchronized.ref(EVAL(a,s))

end;
