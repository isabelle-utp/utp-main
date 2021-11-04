(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

chapter \<open>Example: Lexer Stress Test\<close>

theory C0
  imports "../C_Main"
begin

declare[[C_lexer_trace]]

section \<open>Regular C Code\<close>

subsection \<open>Comments, Keywords and Pragmas\<close>

C \<comment> \<open>Nesting of comments following the example suite of
      \<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>\<close> \<open>
/* inside /* inside */ int a = "outside";
// inside // inside until end of line
int a = "outside";
/* inside
  // inside
inside
*/ int a = "outside";
// inside /* inside until end of line
int a = "outside";
\<close>

C \<comment> \<open>Backslash newline\<close> \<open>
i\    
n\                
t a = "/* //  /\ 
*\
fff */\
";
\<close>

C \<comment> \<open>Backslash newline, Directive \<^url>\<open>https://gcc.gnu.org/onlinedocs/cpp/Initial-processing.html\<close>\<close> \<open>
/\
*
*/ # /*
*/ defi\
ne FO\
O 10\
20\<close>

C \<comment> \<open>Directive: conditional\<close> \<open>
#ifdef a
#elif
#else
#if
#endif
#endif
\<close>
(*
C \<comment> \<open>Directive: pragma\<close> \<open># f # "/**/"
/**/
#     /**/ //  #

_Pragma /\
**/("a")
\<close>
*)
C \<comment> \<open>Directive: macro\<close> \<open>
#define a zz
#define a(x1,x2) z erz(( zz
#define a (x1,x2) z erz(( zz
#undef z
#if
#define a zz
#define a(x1,x2) z erz(( zz
#define a (x1,x2) z erz(( zz
#endif
\<close>

subsection \<open>Scala/jEdit Latency on Multiple Bindings\<close>

C \<comment> \<open>Example of obfuscated code \<^url>\<open>https://en.wikipedia.org/wiki/International_Obfuscated_C_Code_Contest\<close>\<close> \<open>
#define _ -F<00||--F-OO--;
int F=00,OO=00;main(){F_OO();printf("%1.3f\n",4.*-F/OO/OO);}F_OO()
{
            _-_-_-_
       _-_-_-_-_-_-_-_-_
    _-_-_-_-_-_-_-_-_-_-_-_
  _-_-_-_-_-_-_-_-_-_-_-_-_-_
 _-_-_-_-_-_-_-_-_-_-_-_-_-_-_
 _-_-_-_-_-_-_-_-_-_-_-_-_-_-_
_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_
_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_
_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_
_-_-_-_-_-_-_-_-_-_-_-_-_-_-_-_
 _-_-_-_-_-_-_-_-_-_-_-_-_-_-_
 _-_-_-_-_-_-_-_-_-_-_-_-_-_-_
  _-_-_-_-_-_-_-_-_-_-_-_-_-_
    _-_-_-_-_-_-_-_-_-_-_-_
        _-_-_-_-_-_-_-_
            _-_-_-_
}
\<close>

text \<open> Select inside the ball, experience the latency.
A special keyboard combination ``Ctrl-like key\<^footnote>\<open>on Apple: Cmd\<close> + Shift +
Enter'' lets Isabelle/Scala/jEdit enter in a mode where the selected bound occurrences can be all
simultaneously replaced by new input characters typed on the keyboard. (The ``select-entity'' action
exists since Isabelle2016-1, see the respective section ``Prover IDE -- Isabelle/Scala/jEdit'' in
the NEWS.)\<close>

subsection \<open>Lexing and Parsing Obfuscated Sources\<close>

text \<open>Another lexer/parser - stress test: parsing an obfuscated C source.\<close>

C \<comment> \<open>Example of obfuscated code \<^url>\<open>https://www.ioccc.org/2018/endoh1/prog.c\<close>\<close> \<open>
        #define/*__Int3rn^ti[]n/l_()I3fusc^t3|]_C_C<>I7E_C[]nt3st__*/L/*__MMXVIII__*/for
    #include/*!"'()*+,-./12357:;<=>?CEFGHIJKLMNSTUVWXYZ[]^_`cfhijklmnrstuvwxyz{|}*/<stdio.h>
  char*r,F[1<<21]="~T/}3(|+G{>/zUhy;Jx+5wG<v>>u55t.?sIZrC]n.;m+:l+Hk]WjNJi/Sh+2f1>c2H`)(_2(^L\
 -]=([1/Z<2Y7/X12W:.VFFU1,T77S+;N?;M/>L..K1+JCCI<<H:(G*5F--E11C=5?.(>+(=3)Z-;*(:*.Y/5(-=)2*-U,\
/+-?5'(,+++***''EE>T,215IEUF:N`2`:?GK;+^`+?>)5?>U>_)5GxG).2K.2};}_235(]:5,S7E1(vTSS,-SSTvU(<-HG\
-2E2/2L2/EE->E:?EE,2XMMMM1Hy`)5rHK;+.T+?[n2/_2{LKN2/_|cK2+.2`;}:?{KL57?|cK:2{NrHKtMMMK2nrH;rH[n"
"CkM_E21-E,-1->E(_:mSE/LhLE/mm:2Ul;2M>,2KW-+.-u).5Lm?fM`2`2nZXjj?[n<YcK?2}yC}H[^7N7LX^7N7UN</:-\
ZWXI<^I2K?>T+?KH~-?f<;G_x2;;2XT7LXIuuVF2X(G(GVV-:-:KjJ]HKLyN7UjJ3.WXjNI2KN<l|cKt2~[IsHfI2w{[<VV"
"GIfZG>x#&#&&$#$;ZXIc###$&$$#>7[LMv{&&&&#&##L,l2TY.&$#$#&&$,(iiii,#&&&#$#$?TY2.$#$1(x###;2EE[t,\
SSEz.SW-k,T&&jC?E-.$##      &#&57+$$#      &&&W1-&$$7W  -J$#$kEN&#&      $##C^+$##W,h###n/+L2YE"
"2nJk/H;YNs#$[,:TU(#$   ,:   &&~H>&#   Y;   &&G_x&#2;   ,mT&$YE-#&   5G   $#VVF$#&zNs$$&Ej]HELy\
CN/U^Jk71<(#&:G7E+^&#  l|?1  $$Y.2$$  7lzs  WzZw>&$E    -<V-wE(2$$  G>x;  2zsW/$$#HKt&$$v>+t1(>"
"7>S7S,;TT,&$;S7S>7&#>E_::U  $$'",op  ,*G=  F,*I=957+F  ;int*t,k,O,  i,   j,T[+060<<+020];int M(
int m,int nop){;;;return+   m%(0+nop  );;}  int*tOo,w,  h,z,W;void(C)  (int n){n=putchar(n);}int
f,c,H=11,Y=64<<2,Z,pq,X   ;void(E/*d  */)(  int/*RP*/n  ){L(Z=k+00;  Z;  Z/=+2+000)G[000]=*G*!!f
|M(n,2)<<f,pq=2,f=+06   <f?++pq,++pq  ,G++  ,z:f+001,n  /=2;;}void  (V)(  int/*opqrstabd*/n){C(n
%Y);;C(n/Y+00);;}void  J(){L(pq--,pq   =j   =O=-1+0;++  j<240;I[6+   (h   +6+j/12/2*2+M(j/2,2))*
W+M(j/2/2,+06)*2+w*014      +00+M(00+      000+j,002      +00)]=000      +00+k)k=M(G[j/2/2+(*r-+
32)**"<nopqabdeg"],/*4649&96#*/3);/*&oaogoqo*/;}/*xD%P$Q#Rq*/int/*dbqpdbqpxyzzyboo3570OQ*/main()
{L(X=Y-1;i<21*3;i++,I++)L(r=G,G+=2;*G++;)*G>=13*3?*G-*r?*I++=*G:(*I++=r[1],*I++=r[2]):1;L(j=12,r
=I;(*I=i=getchar())>-1;I++)i-7-3?I-=i<32||127<=i,j+=12:(H+=17+3,W=W<j?j:W,j=12);L(;*r>-1;r++)*r-
7-3?J(),w++:(w=z,h+=17+3);C(71);C(73);V('*'*'1'*7);C(57);C(32*3+1);V(W);V(H);C(122*2);L(V(i=z);i
<32*3;)C(i++/3*X/31);C(33);C(X);C(11);L(G="SJYXHFUJ735";*G;)C(*G++-5);C(3);V(1);L(V(j=z);j<21*3;
 j++){k=257;V(63777);V(k<<2);V(M(j,32)?11:511);V(z);C(22*2);V(i=f=z);V(z);V(W);V(H);V(1<<11);r=
  G=I+W*H;L(t=T;i<1<<21;i++)T[i]=i<Y?i:-1;E(Y);L(i=-1;++i<W*H;t=T+Z*Y+Y)c=I[i]?I[i]*31-31:(31<
    j?j-31:31-j),Z=c[t[c]<z?E(Z),k<(1<<12)-2?t[c]=++k,T:T:t];E(Z);E(257);L(G++;k=G-r>X?X:G-r
        ,C(k),k;)L(;k--;C(*r++/*---#$%&04689@ABDOPQRabdegopq---*/));}C(53+6);return(z);}
\<close>

section \<open>Experiments with \<^dir>\<open>../../src_ext/parser_menhir\<close>\<close>

declare[[C_lexer_trace = false]]

subsection \<open>Expecting to succeed\<close>

\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/aligned_struct_c18.c\<close>\<close>
C_file \<open>../../src_ext/parser_menhir/tests/argument_scope.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/atomic.c\<close>\<close>
C_file \<open>../../src_ext/parser_menhir/tests/atomic_parenthesis.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/bitfield_declaration_ambiguity.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/bitfield_declaration_ambiguity.ok.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/block_scope.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/c11-noreturn.c\<close>\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/c1x-alignas.c\<close>\<close>
C_file \<open>../../src_ext/parser_menhir/tests/char-literal-printing.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/c-namespace.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/control-scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/dangling_else.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/dangling_else_lookahead.c\<close>\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/dangling_else_lookahead.if.c\<close>\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/declaration_ambiguity.c\<close>\<close>
C_file \<open>../../src_ext/parser_menhir/tests/declarators.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/declarator_visibility.c\<close>\<close>
C_file \<open>../../src_ext/parser_menhir/tests/designator.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/enum.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/enum_constant_visibility.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/enum_shadows_typedef.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/enum-trick.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/expressions.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/function-decls.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/function_parameter_scope.c\<close>\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/function_parameter_scope_extends.c\<close>\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/if_scopes.c\<close>\<close>
C_file \<open>../../src_ext/parser_menhir/tests/local_scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/local_typedef.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/long-long-struct.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/loop_scopes.c\<close>\<close>
C_file \<open>../../src_ext/parser_menhir/tests/namespaces.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/no_local_scope.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/parameter_declaration_ambiguity.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/parameter_declaration_ambiguity.test.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/statements.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/struct-recursion.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/typedef_star.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/types.c\<close>
C_file \<open>../../src_ext/parser_menhir/tests/variable_star.c\<close>

subsection \<open>Expecting to fail\<close>

C_file \<open>../../src_ext/parser_menhir/tests/bitfield_declaration_ambiguity.fail.c\<close>
\<^cancel>\<open>C_file \<open>../../src_ext/parser_menhir/tests/dangling_else_misleading.fail.c\<close>\<close>

end
