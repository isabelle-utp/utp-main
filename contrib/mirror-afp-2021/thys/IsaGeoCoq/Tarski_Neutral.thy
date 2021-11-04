(* IsageoCoq

Port part of GeoCoq 3.4.0 (https://geocoq.github.io/GeoCoq/) in Isabelle/Hol (Isabelle2021)

Copyright (C) 2021  Roland Coghetto roland_coghetto (at) hotmail.com

License: LGPL

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 2.1 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
*)

theory Tarski_Neutral

imports
  Main

begin

section "Tarski's axiom system for neutral geometry"

subsection "Tarski's axiom system for neutral geometry: dimensionless"

locale Tarski_neutral_dimensionless =
  fixes Bet  :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  fixes Cong :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  assumes cong_pseudo_reflexivity: "\<forall> a b.
                                   Cong a b b a"
    and   cong_inner_transitivity: "\<forall> a b p q r s.
                                    Cong a b p q \<and>
                                    Cong a b r s
                                      \<longrightarrow>
                                    Cong p q r s"
    and   cong_identity: "\<forall> a b c.
                          Cong a b c c
                            \<longrightarrow>
                          a = b"
    and   segment_construction: "\<forall> a b c q.
                                 \<exists>x. (Bet q a x \<and> Cong a x b c)"
    and   five_segment: "\<forall> a b c a' b' c'.
                         a \<noteq> b \<and>
                         Bet a b c \<and>
                         Bet a' b' c'\<and>
                         Cong a b a' b' \<and>
                         Cong b c b' c' \<and>
                         Cong a d a' d' \<and>
                         Cong b d b' d'
                           \<longrightarrow>
                         Cong c d c' d'"
    and   between_identity: "\<forall> a b.
                             Bet a b a
                               \<longrightarrow>
                             a = b"
    and   inner_pasch: "\<forall> a b c p q.
                        Bet a p c \<and>
                        Bet b q c
                          \<longrightarrow>
                        (\<exists> x. Bet p x b \<and> Bet q x a)"
    and   lower_dim:  "\<exists> a b c. (\<not> Bet a b c \<and> \<not> Bet b c a \<and> \<not> Bet c a b)"

subsection "Tarski's axiom system for neutral geometry: 2D"

locale Tarski_2D = Tarski_neutral_dimensionless +
  assumes upper_dim: "\<forall> a b c p q.
                      p \<noteq> q \<and>
                      Cong a p a q \<and>
                      Cong b p b q \<and>
                      Cong c p c q
                      \<longrightarrow>
                      (Bet a b c \<or> Bet b c a \<or> Bet c a b)"

section "Definitions"
subsection "Tarski's axiom system for neutral geometry: dimensionless"
context Tarski_neutral_dimensionless
begin

subsubsection "Congruence"
definition OFSC ::
  "['p,'p,'p,'p,'p,'p,'p,'p] \<Rightarrow> bool"
  ("_ _ _ _ OFSC _ _ _ _" [99,99,99,99,99,99,99,99] 50)
  where
    "A B C D OFSC A' B' C' D' \<equiv>

  Bet A B C \<and>
  Bet A' B' C' \<and>
  Cong A B A' B' \<and>
  Cong B C B' C' \<and>
  Cong A D A' D' \<and>
  Cong B D B' D'"

definition Cong3 ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool"
  ("_ _ _ Cong3 _ _ _" [99,99,99,99,99,99] 50)
  where
    "A B C Cong3 A' B' C' \<equiv>

  Cong A B A' B' \<and>
  Cong A C A' C' \<and>
  Cong B C B' C'"

subsubsection "Betweenness"

definition Col ::
  "['p,'p,'p] \<Rightarrow> bool"
  ("Col _ _ _" [99,99,99] 50)
  where
    "Col A B C \<equiv>

  Bet A B C \<or> Bet B C A \<or> Bet C A B"

definition Bet4 ::
  "['p,'p,'p,'p] \<Rightarrow> bool"
  ("Bet4 _ _ _ _" [99,99,99,99] 50)
  where
    "Bet4 A1 A2 A3 A4 \<equiv>

  Bet A1 A2 A3 \<and>
  Bet A2 A3 A4 \<and>
  Bet A1 A3 A4 \<and>
  Bet A1 A2 A4"

definition BetS ::
  "['p,'p,'p] \<Rightarrow> bool" ("BetS _ _ _" [99,99,99] 50)
  where
    "BetS A B C \<equiv>

  Bet A B C \<and>
  A \<noteq> B \<and>
  B \<noteq> C"

subsubsection "Collinearity"

definition FSC ::
  "['p,'p,'p,'p,'p,'p,'p,'p] \<Rightarrow> bool"
  ("_ _ _ _ FSC _ _ _ _" [99,99,99,99,99,99,99,99] 50)
  where
    "A B C D FSC A' B' C' D' \<equiv>

  Col A B C \<and>
  A B C Cong3 A' B' C' \<and>
  Cong A D A' D' \<and>
  Cong B D B' D'"

subsubsection "Congruence and Betweenness"
definition IFSC ::
  "['p,'p,'p,'p,'p,'p,'p,'p] \<Rightarrow> bool"
  ("_ _ _ _ IFSC _ _ _ _" [99,99,99,99,99,99,99,99] 50)
  where
    "A B C D IFSC A' B' C' D' \<equiv>

  Bet A B C \<and>
  Bet A' B' C' \<and>
  Cong A C A' C' \<and>
  Cong B C B' C' \<and>
  Cong A D A' D' \<and>
  Cong C D C' D'"

subsubsection "Between transivitity  LE"

definition Le ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ Le _ _" [99,99,99,99] 50)
  where "A B Le C D \<equiv>

  \<exists> E. (Bet C E D \<and> Cong A B C E)"


definition Lt ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ Lt _ _" [99,99,99,99] 50)
  where "A B Lt C D \<equiv>

  A B Le C D \<and> \<not> Cong A B C D"

definition Ge ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _Ge _ _" [99,99,99,99] 50)
  where "A B Ge C D \<equiv>

  C D Le A B"

definition Gt ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ Gt _ _" [99,99,99,99] 50)
  where "A B Gt C D \<equiv>

  C D Lt A B"

subsubsection "Out lines"

definition Out ::
  "['p,'p,'p] \<Rightarrow> bool" ("_ Out _ _" [99,99,99] 50)
  where "P Out A B \<equiv>

  A \<noteq> P \<and>
  B \<noteq> P \<and>
  (Bet P A B \<or> Bet P B A)"

subsubsection "Midpoint"

definition Midpoint ::
  "['p,'p,'p] \<Rightarrow> bool" ("_ Midpoint _ _" [99,99,99] 50)
  where "M Midpoint A B \<equiv>

  Bet A M B \<and>
  Cong A M M B"

subsubsection "Orthogonality"

definition Per ::
  "['p,'p,'p] \<Rightarrow> bool" ("Per _ _ _" [99,99,99] 50)
  where "Per A B C \<equiv>

  \<exists> C'::'p. (B Midpoint C C' \<and> Cong A C A C')"

definition PerpAt ::
  "['p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ PerpAt _ _ _ _ " [99,99,99,99,99] 50)
  where "X PerpAt A B C D \<equiv>

  A \<noteq> B \<and>
  C \<noteq> D \<and>
  Col X A B \<and>
  Col X C D \<and>
  (\<forall> U V. ((Col U A B \<and> Col V C D) \<longrightarrow> Per U X V))"

definition Perp ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ Perp _ _" [99,99,99,99] 50)
  where "A B Perp C D \<equiv>

  \<exists> X::'p. X PerpAt A B C D"

subsubsection "Coplanar"

definition Coplanar ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("Coplanar _ _ _ _" [99,99,99,99] 50)
  where "Coplanar A B C D \<equiv>
  \<exists> X. (Col A B X \<and> Col C D X) \<or>
            (Col A C X \<and> Col B D X) \<or>
            (Col A D X \<and> Col B C X)"

definition TS ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ TS _ _" [99,99,99,99] 50)
  where "A B TS P Q \<equiv>
  \<not> Col P A B \<and> \<not> Col Q A B \<and> (\<exists> T::'p. Col T A B \<and> Bet P T Q)"

definition ReflectL ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ ReflectL _ _" [99,99,99,99] 50)
  where "P' P ReflectL A B \<equiv>
  (\<exists> X. X Midpoint P P' \<and> Col A B X) \<and> (A B Perp P P' \<or> P = P')"

definition Reflect ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ Reflect _ _" [99,99,99,99] 50)
  where "P' P Reflect A B \<equiv>
 (A \<noteq> B \<and> P' P ReflectL A B) \<or> (A = B \<and> A Midpoint P P')"

definition InAngle ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ InAngle _ _ _" [99,99,99,99] 50)
  where "P InAngle A B C \<equiv>
  A \<noteq> B \<and> C \<noteq> B \<and> P \<noteq> B \<and>
(\<exists> X. Bet A X C \<and> (X = B \<or> B Out X P))"

definition ParStrict::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ ParStrict _ _" [99,99,99,99] 50)
  where "A B ParStrict C D \<equiv>  Coplanar A B C D \<and> \<not> (\<exists> X. Col X A B \<and> Col X C D)"

definition Par::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ Par _ _" [99,99,99,99] 50)
  where "A B Par C D \<equiv>
  A B ParStrict C D \<or> (A \<noteq> B \<and> C \<noteq> D \<and> Col A C D \<and> Col B C D)"

definition Plg::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("Plg _ _ _ _" [99,99,99,99] 50)
  where "Plg  A B C D \<equiv>
  (A \<noteq> C \<or> B \<noteq> D) \<and> (\<exists> M. M Midpoint A C \<and> M Midpoint B D)"

definition ParallelogramStrict::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("ParallelogramStrict _ _ _ _" [99,99,99,99] 50)
  where "ParallelogramStrict A B A' B' \<equiv>
  A A' TS B B' \<and> A B Par A' B' \<and> Cong A B A' B'"

definition ParallelogramFlat::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("ParallelogramFlat _ _ _ _" [99,99,99,99] 50)
  where "ParallelogramFlat A B A' B' \<equiv>
  Col A B A' \<and> Col A B B' \<and>
  Cong A B A' B' \<and> Cong A B' A' B \<and>
  (A \<noteq> A' \<or> B \<noteq> B')"

definition Parallelogram::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("Parallelogram _ _ _ _" [99,99,99,99] 50)
  where "Parallelogram A B A' B' \<equiv>
  ParallelogramStrict A B A' B' \<or> ParallelogramFlat A B A' B'"

definition Rhombus::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("Rhombus _ _ _ _" [99,99,99,99] 50)
  where "Rhombus A B C D \<equiv> Plg A B C D \<and> Cong A B B C"

definition Rectangle::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("Rectangle _ _ _ _" [99,99,99,99] 50)
  where "Rectangle A B C D \<equiv> Plg A B C D \<and> Cong A C B D"

definition Square::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("Square _ _ _ _" [99,99,99,99] 50)
  where "Square A B C D \<equiv> Rectangle A B C D \<and> Cong A B B C"

definition Lambert::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("Lambert _ _ _ _" [99,99,99,99] 50)
  where "Lambert A B C D \<equiv>
  A \<noteq> B \<and> B \<noteq> C \<and> C \<noteq> D \<and>
 A \<noteq> D \<and> Per B A D \<and> Per A D C \<and> Per A B C \<and> Coplanar A B C D"

subsubsection "Plane"

definition OS ::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("_ _ OS _ _" [99,99,99,99] 50)
  where "A B OS P Q \<equiv>
\<exists> R::'p. A B TS P R \<and> A B TS Q R"

definition TSP ::
  "['p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _TSP _ _" [99,99,99,99,99] 50)
  where "A B C TSP P Q \<equiv>
  (\<not> Coplanar A B C P) \<and> (\<not> Coplanar A B C Q) \<and>
(\<exists> T. Coplanar A B C T \<and> Bet P T Q)"

definition OSP ::
  "['p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _ OSP _ _" [99,99,99,99,99] 50)
  where "A B C OSP P Q \<equiv>
\<exists> R. ((A B C TSP P R) \<and> (A B C TSP Q R))"

definition Saccheri::
  "['p,'p,'p,'p] \<Rightarrow> bool" ("Saccheri _ _ _ _" [99,99,99,99] 50)
  where "Saccheri A B C D \<equiv>
  Per B A D \<and> Per A D C \<and> Cong A B C D \<and> A D OS B C"

subsubsection "Line reflexivity 2D"

definition ReflectLAt ::
  "['p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ ReflectLAt _ _ _ _" [99,99,99,99,99] 50)
  where "M ReflectLAt P' P A B \<equiv>
  (M Midpoint P P' \<and> Col A B M) \<and> (A B Perp P P' \<or> P = P')"

definition ReflectAt ::
  "['p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ ReflectAt _ _ _ _" [99,99,99,99,99] 50)
  where "M ReflectAt P' P A B \<equiv>
(A \<noteq> B \<and> M ReflectLAt P' P A B) \<or> (A = B \<and> A = M \<and> M Midpoint P P')"

subsubsection "Line reflexivity"

definition upper_dim_axiom ::
  "bool" ("UpperDimAxiom" [] 50)
  where
    "upper_dim_axiom \<equiv>

  \<forall> A B C P Q.
  P \<noteq> Q \<and>
  Cong A P A Q \<and>
  Cong B P B Q \<and>
  Cong C P C Q
    \<longrightarrow>
  (Bet A B C \<or> Bet B C A \<or> Bet C A B)"

definition all_coplanar_axiom ::
  "bool" ("AllCoplanarAxiom" [] 50)
  where
    "AllCoplanarAxiom \<equiv>

  \<forall> A B C P Q.
  P \<noteq> Q \<and>
  Cong A P A Q \<and>
  Cong B P B Q \<and>
  Cong C P C Q
    \<longrightarrow>
  (Bet A B C \<or> Bet B C A \<or> Bet C A B)"

subsubsection "Angles"

definition CongA ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _ CongA _ _ _" [99,99,99,99,99,99] 50)
  where "A B C CongA D E F \<equiv>
  A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E \<and>
(\<exists> A' C' D' F'. Bet B A A' \<and> Cong A A' E D \<and>
  Bet B C C' \<and> Cong C C' E F \<and>
  Bet E D D' \<and> Cong D D' B A \<and>
  Bet E F F' \<and> Cong F F' B C \<and>
  Cong A' C' D' F')"

definition LeA ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _ LeA _ _ _" [99,99,99,99,99,99] 50)
  where "A B C LeA D E F \<equiv>
\<exists> P. (P InAngle D E F \<and> A B C CongA D E P)"

definition LtA ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _ LtA _ _ _" [99,99,99,99,99,99] 50)
  where "A B C LtA D E F \<equiv> A B C LeA D E F \<and> \<not> A B C CongA D E F"

definition GtA ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _ GtA _ _ _" [99,99,99,99,99,99] 50)
  where "A B C GtA D E F \<equiv> D E F LtA A B C"

definition Acute ::
  "['p,'p,'p] \<Rightarrow> bool" ("Acute _ _ _" [99,99,99] 50)
  where "Acute A B C \<equiv>
\<exists> A' B' C'. (Per A' B' C' \<and> A B C LtA A' B' C')"

definition Obtuse ::
  "['p,'p,'p] \<Rightarrow> bool" ("Obtuse _ _ _" [99,99,99] 50)
  where "Obtuse A B C \<equiv>
\<exists> A' B' C'. (Per A' B' C' \<and> A' B' C' LtA A B C)"

definition OrthAt ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ OrthAt _ _ _ _ _" [99,99,99,99,99,99] 50)
  where "X OrthAt A B C U V \<equiv>
  \<not> Col A B C \<and> U \<noteq> V \<and> Coplanar A B C X \<and> Col U V X \<and>
  (\<forall> P Q. (Coplanar A B C P \<and> Col U V Q) \<longrightarrow> Per P X Q)"

definition Orth ::
  "['p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _ Orth _ _" [99,99,99,99,99] 50)
  where "A B C Orth U V \<equiv> \<exists> X. X OrthAt A B C U V"

definition SuppA ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool"
  ("_ _ _ SuppA _ _ _ " [99,99,99,99,99,99] 50)
  where
    "A B C SuppA D E F \<equiv>
  A \<noteq> B \<and> (\<exists> A'. Bet A B A' \<and>  D E F CongA C B A')"

subsubsection "Sum of angles"

definition SumA ::
  "['p,'p,'p,'p,'p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _ _ _ _ SumA _ _ _" [99,99,99,99,99,99,99,99,99] 50)
  where
    "A B C D E F SumA G H I \<equiv>

  \<exists> J. (C B J CongA D E F \<and> \<not> B C OS A J \<and> Coplanar A B C J \<and> A B J CongA G H I)"

definition TriSumA ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ _ _ TriSumA _ _ _" [99,99,99,99,99,99] 50)
  where
    "A B C TriSumA D E F \<equiv>

  \<exists> G H I. (A B C B C A SumA G H I \<and> G H I C A B SumA D E F)"

definition SAMS ::
  "['p,'p,'p,'p,'p,'p] \<Rightarrow> bool" ("SAMS _ _ _ _ _ _" [99,99,99,99,99,99] 50)
  where
    "SAMS A B C D E F \<equiv>

  (A \<noteq> B \<and>
  (E Out D F \<or> \<not> Bet A B C)) \<and>
  (\<exists> J. (C B J CongA D E F \<and> \<not> (B C OS A J) \<and> \<not> (A B TS C J) \<and> Coplanar A B C J))"

subsubsection "Parallelism"

definition Inter ::
  "['p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ Inter _ _ _ _" [99,99,99,99,99] 50)
  where "X Inter A1 A2 B1 B2 \<equiv>

  B1 \<noteq> B2 \<and>
  (\<exists> P::'p. (Col P B1 B2 \<and> \<not> Col P A1 A2)) \<and>
  Col A1 A2 X \<and> Col B1 B2 X"

subsubsection "Perpendicularity"

definition Perp2 ::
  "['p,'p,'p,'p,'p] \<Rightarrow> bool" ("_ Perp2 _ _ _ _" [99,99,99,99,99] 50)
  where
    "P Perp2 A B C D \<equiv>

  \<exists> X Y. (Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D)"

subsubsection "Lentgh"

definition QCong::
  "(['p,'p] \<Rightarrow> bool) \<Rightarrow> bool" ("QCong _" [99] 50)
  where
    "QCong l \<equiv>

  \<exists> A B. (\<forall> X Y. (Cong A B X Y \<longleftrightarrow> l X Y))"

definition TarskiLen::
  "['p,'p,(['p,'p] \<Rightarrow> bool)] \<Rightarrow> bool" ("TarskiLen _ _ _" [99,99,99] 50)
  where
    "TarskiLen A B l \<equiv>

  QCong l \<and> l A B"

definition QCongNull ::
  "(['p,'p] \<Rightarrow> bool) \<Rightarrow> bool" ("QCongNull _" [99] 50)
  where
    "QCongNull l \<equiv>

  QCong l \<and> (\<exists> A. l A A)"

subsubsection "Equivalence Class of Angles"

definition QCongA ::
  "(['p, 'p, 'p] \<Rightarrow> bool) \<Rightarrow> bool" ("QCongA _" [99] 50)
  where
    "QCongA a \<equiv>

  \<exists> A B C. (A \<noteq> B \<and> C \<noteq> B \<and> (\<forall> X Y Z. A B C CongA X Y Z \<longleftrightarrow> a X Y Z))"

definition Ang ::
  "['p,'p,'p, (['p, 'p, 'p] \<Rightarrow> bool) ] \<Rightarrow> bool" ("_ _ _ Ang _" [99,99,99,99] 50)
  where
    "A B C Ang a \<equiv>

  QCongA a \<and>
  a A B C"

definition QCongAAcute ::
  "(['p, 'p, 'p] \<Rightarrow> bool) \<Rightarrow> bool" ("QCongAACute _" [99] 50)
  where
    "QCongAAcute a \<equiv>

  \<exists> A B C. (Acute A B C \<and> (\<forall> X Y Z. (A B C CongA X Y Z \<longleftrightarrow> a X Y Z)))"

definition AngAcute ::
  "['p,'p,'p, (['p,'p,'p] \<Rightarrow> bool)] \<Rightarrow> bool" ("_ _ _ AngAcute _" [99,99,99,99] 50)
  where
    "A B C AngAcute a \<equiv>

  ((QCongAAcute a) \<and> (a A B C))"

definition QCongANullAcute ::
  "(['p,'p,'p] \<Rightarrow> bool) \<Rightarrow> bool" ("QCongANullAcute _" [99] 50)
  where
    "QCongANullAcute a \<equiv>

   QCongAAcute a \<and>
   (\<forall> A B C. (a A B C \<longrightarrow> B Out A C))"

definition QCongAnNull ::
  "(['p,'p,'p] \<Rightarrow> bool) \<Rightarrow> bool" ("QCongAnNull _" [99] 50)
  where
    "QCongAnNull a \<equiv>

  QCongA a \<and>
  (\<forall> A B C. (a A B C \<longrightarrow> \<not> B Out A C))"

definition QCongAnFlat ::
  "(['p,'p,'p] \<Rightarrow> bool) \<Rightarrow> bool" ("QCongAnFlat _" [99] 50)
  where
    "QCongAnFlat a \<equiv>

  QCongA a \<and>
  (\<forall> A B C. (a A B C \<longrightarrow> \<not> Bet A B C))"

definition IsNullAngaP ::
  "(['p,'p,'p] \<Rightarrow> bool) \<Rightarrow> bool" ("IsNullAngaP _" [99] 50)
  where
    "IsNullAngaP a\<equiv>

  QCongAAcute a \<and>
  (\<exists> A B C. (a A B C \<and> B Out A C))"

definition QCongANull ::
  "(['p,'p,'p] \<Rightarrow> bool) \<Rightarrow> bool" ("QCongANull _" [99] 50)
  where
    "QCongANull a \<equiv>

  QCongA a \<and>
  (\<forall> A B C. (a A B C \<longrightarrow> B Out A C))"

definition AngFlat ::
  "(['p, 'p, 'p] \<Rightarrow> bool) \<Rightarrow> bool" ("AngFlat _" [99] 50)
  where
    "AngFlat a \<equiv>

  QCongA a \<and>
  (\<forall> A B C. (a A B C \<longrightarrow> Bet A B C))"

subsection "Parallel's definition Postulate"

definition tarski_s_parallel_postulate ::
  "bool"
  ("TarskiSParallelPostulate")
  where
    "tarski_s_parallel_postulate \<equiv>
\<forall> A B C D T. (Bet A D T \<and> Bet B D C \<and> A \<noteq> D) \<longrightarrow>
(\<exists> X Y. Bet A B X \<and> Bet A C Y \<and> Bet X T Y)"

definition euclid_5 ::
  "bool" ("Euclid5")
  where
    "euclid_5 \<equiv>

  \<forall> P Q R S T U.
  (BetS P T Q \<and>
  BetS R T S \<and>
  BetS Q U R \<and>
  \<not> Col P Q S \<and>
  Cong P T Q T \<and>
  Cong R T S T)
    \<longrightarrow>
  (\<exists> I. BetS S Q I \<and> BetS P U I)"

definition euclid_s_parallel_postulate ::
  "bool" ("EuclidSParallelPostulate")
  where
    "euclid_s_parallel_postulate \<equiv>

  \<forall> A B C D P Q R.
  (B C OS A D \<and>
   SAMS A B C B C D \<and>
   A B C B C D SumA P Q R \<and>
   \<not> Bet P Q R)
    \<longrightarrow>
  (\<exists> Y. B Out A Y \<and> C Out D Y)"

definition playfair_s_postulate ::
  "bool"
  ("PlayfairSPostulate")
  where
    "playfair_s_postulate \<equiv>

  \<forall> A1 A2 B1 B2 C1 C2 P.
  (A1 A2 Par B1 B2 \<and>
  Col P B1 B2 \<and>
  A1 A2 Par C1 C2 \<and>
  Col P C1 C2)
    \<longrightarrow>
  (Col C1 B1 B2 \<and> Col C2 B1 B2)"

section "Propositions"

subsection "Congruence properties"

lemma cong_reflexivity:
  shows "Cong A B A B"
  using cong_inner_transitivity cong_pseudo_reflexivity by blast

lemma cong_symmetry:
  assumes "Cong A B C D"
  shows "Cong C D A B"
  using assms cong_inner_transitivity cong_reflexivity by blast

lemma cong_transitivity:
  assumes "Cong A B C D" and "Cong C D E F"
  shows "Cong A B E F"
  by (meson assms(1) assms(2) cong_inner_transitivity cong_pseudo_reflexivity)

lemma cong_left_commutativity:
  assumes "Cong A B C D"
  shows "Cong B A C D"
  using assms cong_inner_transitivity cong_pseudo_reflexivity by blast

lemma cong_right_commutativity:
  assumes "Cong A B C D"
  shows "Cong A B D C"
  using assms cong_left_commutativity cong_symmetry by blast

lemma cong_3421:
  assumes "Cong A B C D"
  shows "Cong C D B A"
  using assms cong_left_commutativity cong_symmetry by blast

lemma cong_4312:
  assumes "Cong A B C D"
  shows "Cong D C A B"
  using assms cong_left_commutativity cong_symmetry by blast

lemma cong_4321:
  assumes "Cong A B C D"
  shows "Cong D C B A"
  using assms cong_3421 cong_left_commutativity by blast

lemma cong_trivial_identity:
  shows "Cong A A B B"
  using cong_identity segment_construction by blast

lemma cong_reverse_identity:
  assumes "Cong A A C D"
  shows "C = D"
  using assms cong_3421 cong_identity by blast

lemma cong_commutativity:
  assumes "Cong A B C D"
  shows "Cong B A D C"
  using assms cong_3421 by blast

lemma not_cong_2134:
  assumes " \<not> Cong A B C D"
  shows "\<not> Cong B A C D"
  using assms cong_left_commutativity by blast

lemma not_cong_1243:
  assumes "\<not> Cong A B C D"
  shows "\<not> Cong A B D C"
  using assms cong_right_commutativity by blast

lemma not_cong_2143:
  assumes "\<not> Cong A B C D"
  shows "\<not> Cong B A D C"
  using assms cong_commutativity by blast

lemma not_cong_3412:
  assumes "\<not> Cong A B C D"
  shows "\<not> Cong C D A B"
  using assms cong_symmetry by blast

lemma not_cong_4312:
  assumes "\<not> Cong A B C D"
  shows "\<not> Cong D C A B"
  using assms cong_3421 by blast

lemma not_cong_3421:
  assumes "\<not> Cong A B C D"
  shows "\<not> Cong C D B A"
  using assms cong_4312 by blast

lemma not_cong_4321:
  assumes "\<not> Cong A B C D"
  shows "\<not> Cong D C B A"
  using assms cong_4321 by blast

lemma five_segment_with_def:
  assumes "A B C D OFSC A' B' C' D'" and "A \<noteq> B"
  shows "Cong C D C' D'"
  using assms(1) assms(2) OFSC_def five_segment by blast

lemma cong_diff:
  assumes "A \<noteq> B" and "Cong A B C D"
  shows "C \<noteq> D"
  using assms(1) assms(2) cong_identity by blast

lemma cong_diff_2:
  assumes "B \<noteq> A" and "Cong A B C D"
  shows "C \<noteq> D"
  using assms(1) assms(2) cong_identity by blast

lemma cong_diff_3:
  assumes "C \<noteq> D" and "Cong A B C D"
  shows "A \<noteq> B"
  using assms(1) assms(2) cong_reverse_identity by blast

lemma cong_diff_4:
  assumes "D \<noteq> C" and "Cong A B C D"
  shows "A \<noteq> B"
  using assms(1) assms(2) cong_reverse_identity by blast

lemma cong_3_sym:
  assumes "A B C Cong3 A' B' C'"
  shows "A' B' C' Cong3 A B C"
  using assms Cong3_def not_cong_3412 by blast

lemma cong_3_swap:
  assumes "A B C Cong3 A' B' C'"
  shows "B A C Cong3 B' A' C'"
  using assms Cong3_def cong_commutativity by blast

lemma cong_3_swap_2:
  assumes "A B C Cong3 A' B' C'"
  shows "A C B Cong3 A' C' B'"
  using assms Cong3_def cong_commutativity by blast

lemma cong3_transitivity:
  assumes "A0 B0 C0 Cong3 A1 B1 C1" and
    "A1 B1 C1 Cong3 A2 B2 C2"
  shows "A0 B0 C0 Cong3 A2 B2 C2"
  by (meson assms(1) assms(2) Cong3_def cong_inner_transitivity not_cong_3412)

lemma eq_dec_points:
  shows "A = B \<or> \<not> A = B"
  by simp

lemma distinct:
  assumes "P \<noteq> Q"
  shows "R \<noteq> P \<or> R \<noteq> Q"
  using assms by simp

lemma l2_11:
  assumes "Bet A B C" and
    "Bet A' B' C'" and
    "Cong A B A' B'" and
    "Cong B C B' C'"
  shows "Cong A C A' C'"
  by (smt assms(1) assms(2) assms(3) assms(4) cong_right_commutativity cong_symmetry cong_trivial_identity five_segment)

lemma bet_cong3:
  assumes "Bet A B C" and
    "Cong A B A' B'"
  shows "\<exists> C'. A B C Cong3 A' B' C'"
  by (meson assms(1) assms(2) Cong3_def l2_11 not_cong_3412 segment_construction)

lemma construction_uniqueness:
  assumes "Q \<noteq> A" and
    "Bet Q A X" and
    "Cong A X B C" and
    "Bet Q A Y" and
    "Cong A Y B C"
  shows "X = Y"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) cong_identity cong_inner_transitivity cong_reflexivity five_segment)

lemma Cong_cases:
  assumes "Cong A B C D \<or> Cong A B D C \<or> Cong B A C D \<or> Cong B A D C \<or> Cong C D A B \<or> Cong C D B A \<or> Cong D C A B \<or> Cong D C B A"
  shows "Cong A B C D"
  using assms not_cong_3421 not_cong_4321 by blast

lemma Cong_perm :
  assumes "Cong A B C D"
  shows "Cong A B C D \<and> Cong A B D C \<and> Cong B A C D \<and> Cong B A D C \<and> Cong C D A B \<and> Cong C D B A \<and> Cong D C A B \<and> Cong D C B A"
  using assms not_cong_1243 not_cong_3412 by blast

subsection "Betweeness properties"

lemma bet_col:
  assumes "Bet A B C"
  shows "Col A B C"
  by (simp add: assms Col_def)

lemma between_trivial:
  shows "Bet A B B"
  using cong_identity segment_construction by blast

lemma between_symmetry:
  assumes "Bet A B C"
  shows "Bet C B A"
  using assms between_identity between_trivial inner_pasch by blast

lemma Bet_cases:
  assumes "Bet A B C \<or> Bet C B A"
  shows "Bet A B C"
  using assms between_symmetry by blast

lemma Bet_perm:
  assumes "Bet A B C"
  shows "Bet A B C \<and> Bet C B A"
  using assms Bet_cases by blast

lemma between_trivial2:
  shows "Bet A A B"
  using Bet_perm between_trivial by blast

lemma between_equality:
  assumes "Bet A B C" and "Bet B A C"
  shows "A = B"
  using assms(1) assms(2) between_identity inner_pasch by blast

lemma between_equality_2:
  assumes "Bet A B C" and
    "Bet A C B"
  shows "B = C"
  using assms(1) assms(2) between_equality between_symmetry by blast

lemma between_exchange3:
  assumes "Bet A B C" and
    "Bet A C D"
  shows "Bet B C D"
  by (metis Bet_perm assms(1) assms(2) between_identity inner_pasch)

lemma bet_neq12__neq:
  assumes "Bet A B C" and
    "A \<noteq> B"
  shows "A \<noteq> C"
  using assms(1) assms(2) between_identity by blast

lemma bet_neq21__neq:
  assumes "Bet A B C" and
    "B \<noteq> A"
  shows "A \<noteq> C"
  using assms(1) assms(2) between_identity by blast

lemma bet_neq23__neq:
  assumes "Bet A B C" and
    "B \<noteq> C"
  shows "A \<noteq> C"
  using assms(1) assms(2) between_identity by blast

lemma bet_neq32__neq:
  assumes "Bet A B C" and
    "C \<noteq> B"
  shows "A \<noteq> C"
  using assms(1) assms(2) between_identity by blast

lemma not_bet_distincts:
  assumes "\<not> Bet A B C"
  shows "A \<noteq> B \<and> B \<noteq> C"
  using assms between_trivial between_trivial2 by blast

lemma between_inner_transitivity:
  assumes "Bet A B D" and
    "Bet B C D"
  shows "Bet A B C"
  using assms(1) assms(2) Bet_perm between_exchange3 by blast

lemma outer_transitivity_between2:
  assumes "Bet A B C" and
    "Bet B C D" and
    "B \<noteq> C"
  shows "Bet A C D"
proof -
  obtain X where "Bet A C X \<and> Cong C X C D"
    using segment_construction by blast
  thus ?thesis
    using assms(1) assms(2) assms(3) between_exchange3 cong_inner_transitivity construction_uniqueness by blast
qed

lemma between_exchange2:
  assumes "Bet A B D" and
    "Bet B C D"
  shows "Bet A C D"
  using assms(1) assms(2) between_inner_transitivity outer_transitivity_between2 by blast

lemma outer_transitivity_between:
  assumes "Bet A B C" and
    "Bet B C D" and
    "B \<noteq> C"
  shows "Bet A B D"
  using assms(1) assms(2) assms(3) between_symmetry outer_transitivity_between2 by blast

lemma between_exchange4:
  assumes "Bet A B C" and
    "Bet A C D"
  shows "Bet A B D"
  using assms(1) assms(2) between_exchange2 between_symmetry by blast

lemma l3_9_4:
  assumes "Bet4 A1 A2 A3 A4"
  shows "Bet4 A4 A3 A2 A1"
  using assms Bet4_def Bet_cases by blast

lemma l3_17:
  assumes "Bet A B C" and
    "Bet A' B' C" and
    "Bet A P A'"
  shows "(\<exists> Q. Bet P Q C \<and> Bet B Q B')"
proof -
  obtain X where "Bet B' X A \<and> Bet P X C"
    using Bet_perm assms(2) assms(3) inner_pasch by blast
  moreover
  then obtain Y where "Bet X Y C \<and> Bet B Y B'"
    using Bet_perm assms(1) inner_pasch by blast
  ultimately show ?thesis
    using between_exchange2 by blast
qed

lemma lower_dim_ex:
  "\<exists> A B C. \<not> (Bet A B C \<or> Bet B C A \<or> Bet C A B)"
  using lower_dim by auto

lemma two_distinct_points:
  "\<exists> X::'p. \<exists> Y::'p. X \<noteq> Y"
  using lower_dim_ex not_bet_distincts by blast

lemma point_construction_different:
  "\<exists> C. Bet A B C \<and> B \<noteq> C"
  using Tarski_neutral_dimensionless.two_distinct_points Tarski_neutral_dimensionless_axioms cong_reverse_identity segment_construction by blast

lemma another_point:
  "\<exists> B::'p. A \<noteq> B"
  using point_construction_different by blast

lemma Cong_stability:
  assumes "\<not> \<not> Cong A B C D"
  shows "Cong A B C D"
  using assms by simp

lemma l2_11_b:
  assumes "Bet A B C" and
    "Bet A' B' C'" and
    "Cong A B A' B'" and
    "Cong B C B' C'"
  shows "Cong A C A' C'"
  using assms(1) assms(2) assms(3) assms(4) l2_11 by auto

lemma cong_dec_eq_dec_b:
  assumes "\<not> A \<noteq> B"
  shows "A = B"
  using assms(1) by simp

lemma BetSEq:
  assumes "BetS A B C"
  shows "Bet A B C \<and> A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C"
  using assms BetS_def between_identity by auto

subsection "Collinearity"

subsubsection "Collinearity and betweenness"

lemma l4_2:
  assumes "A B C D IFSC A' B' C' D'"
  shows "Cong B D B' D'"
proof cases
  assume "A = C"
  thus ?thesis
    by (metis IFSC_def Tarski_neutral_dimensionless.between_identity Tarski_neutral_dimensionless_axioms assms cong_diff_3)
next
  assume H1: "A \<noteq> C"
  have H2: "Bet A B C \<and> Bet A' B' C' \<and>
            Cong A C A' C' \<and> Cong B C B' C' \<and>
            Cong A D A' D' \<and> Cong C D C' D'"
    using IFSC_def assms by auto
  obtain E where P1: "Bet A C E \<and> Cong C E A C"
    using segment_construction by blast
  have P1A: "Bet A C E"
    using P1 by simp
  have P1B: "Cong C E A C"
    using P1 by simp
  obtain E' where P2: "Bet A' C' E' \<and> Cong C' E' C E"
    using segment_construction by blast
  have P2A: "Bet A' C' E'"
    using P2 by simp
  have P2B: "Cong C' E' C E"
    using P2 by simp
  then have "Cong C E C' E'"
    using not_cong_3412 by blast
  then have "Cong E D E' D'"
    using H1 H2 P1 P2 five_segment by blast
  thus ?thesis
    by (smt H1 H2 P1A P1B P2A P2B Tarski_neutral_dimensionless.cong_commutativity Tarski_neutral_dimensionless.cong_diff_3 Tarski_neutral_dimensionless.cong_symmetry Tarski_neutral_dimensionless_axioms between_inner_transitivity between_symmetry five_segment)
qed

lemma l4_3:
  assumes "Bet A B C" and
    "Bet A' B' C'" and
    "Cong A C A' C'"
    and "Cong B C B' C'"
  shows "Cong A B A' B'"
proof -
  have "A B C A IFSC A' B' C' A'"
    using IFSC_def assms(1) assms(2) assms(3) assms(4) cong_trivial_identity not_cong_2143 by blast
  thus ?thesis
    using l4_2 not_cong_2143 by blast
qed


lemma l4_3_1:
  assumes "Bet A B C" and
    "Bet A' B' C'" and
    "Cong A B A' B'" and
    "Cong A C A' C'"
  shows "Cong B C B' C'"
  by (meson assms(1) assms(2) assms(3) assms(4) between_symmetry cong_4321 l4_3)

lemma l4_5:
  assumes "Bet A B C" and
    "Cong A C A' C'"
  shows  "\<exists> B'. (Bet A' B' C' \<and> A B C Cong3 A' B' C')"
proof -
  obtain X' where P1: "Bet C' A' X' \<and> A' \<noteq> X'"
    using point_construction_different by auto
  obtain B' where P2: "Bet  X' A' B' \<and> Cong A' B' A B"
    using segment_construction by blast
  obtain C'' where P3: "Bet X' B' C'' \<and> Cong B' C'' B C"
    using segment_construction by blast
  then have P4: "Bet A' B' C''"
    using P2 between_exchange3 by blast
  then have "C'' = C'"
    by (smt P1 P2 P3 assms(1) assms(2) between_exchange4 between_symmetry cong_symmetry construction_uniqueness l2_11_b)
  then show ?thesis
    by (smt Cong3_def P1 P2 P3 Tarski_neutral_dimensionless.construction_uniqueness Tarski_neutral_dimensionless_axioms P4 assms(1) assms(2) between_exchange4 between_symmetry cong_commutativity cong_symmetry cong_trivial_identity five_segment not_bet_distincts)
qed

lemma l4_6:
  assumes "Bet A B C" and
    "A B C Cong3 A' B' C'"
  shows "Bet A' B' C'"
proof -
  obtain x where P1: "Bet A' x C' \<and> A B C Cong3 A' x C'"
    using Cong3_def assms(1) assms(2) l4_5 by blast
  then have "A' x C' Cong3 A' B' C'"
    using assms(2) cong3_transitivity cong_3_sym by blast
  then have "A' x C' x IFSC A' x C' B'"
    by (meson Cong3_def Cong_perm IFSC_def P1 cong_reflexivity)
  then have "Cong x x x B'"
    using l4_2 by auto
  then show ?thesis
    using P1 cong_reverse_identity by blast
qed

lemma cong3_bet_eq:
  assumes "Bet A B C" and
    "A B C Cong3 A X C"
  shows "X = B"
proof -
  have "A B C B IFSC A B C X"
    by (meson Cong3_def Cong_perm IFSC_def assms(1) assms(2) cong_reflexivity)
  then show ?thesis
    using cong_reverse_identity l4_2 by blast
qed

subsubsection "Collinearity"

lemma col_permutation_1:
  assumes "Col A B C"
  shows "Col B C A"
  using assms(1) Col_def by blast

lemma col_permutation_2:
  assumes "Col A B C"
  shows "Col C A B"
  using assms(1) col_permutation_1 by blast

lemma col_permutation_3:
  assumes "Col A B C"
  shows "Col C B A"
  using assms(1) Bet_cases Col_def by auto

lemma col_permutation_4:
  assumes "Col A B C"
  shows "Col B A C"
  using assms(1) Bet_perm Col_def by blast

lemma col_permutation_5:
  assumes "Col A B C"
  shows "Col A C B"
  using assms(1) col_permutation_1 col_permutation_3 by blast

lemma not_col_permutation_1:
  assumes "\<not> Col A B C"
  shows "\<not> Col B C A"
  using assms col_permutation_2 by blast

lemma not_col_permutation_2:
  assumes "~ Col A B C"
  shows  "~ Col C A B"
  using assms col_permutation_1 by blast

lemma not_col_permutation_3:
  assumes "\<not> Col A B C"
  shows "\<not> Col C B A"
  using assms col_permutation_3 by blast

lemma not_col_permutation_4:
  assumes "\<not> Col A B C"
  shows "\<not> Col B A C"
  using assms col_permutation_4 by blast

lemma not_col_permutation_5:
  assumes "\<not> Col A B C"
  shows "\<not> Col A C B"
  using assms col_permutation_5 by blast

lemma Col_cases:
  assumes "Col A B C \<or> Col A C B \<or> Col B A C \<or> Col B C A \<or> Col C A B \<or> Col C B A"
  shows "Col A B C"
  using assms not_col_permutation_4 not_col_permutation_5 by blast

lemma Col_perm:
  assumes "Col A B C"
  shows "Col A B C \<and> Col A C B \<and> Col B A C \<and> Col B C A \<and> Col C A B \<and> Col C B A"
  using Col_cases assms by blast

lemma col_trivial_1:
  "Col A A B"
  using bet_col not_bet_distincts by blast

lemma col_trivial_2:
  "Col A B B"
  by (simp add: Col_def between_trivial2)

lemma col_trivial_3:
  "Col A B A"
  by (simp add: Col_def between_trivial2)

lemma l4_13:
  assumes "Col A B C" and
    "A B C Cong3 A' B' C'"
  shows "Col A' B' C'"
  by (metis Tarski_neutral_dimensionless.Col_def Tarski_neutral_dimensionless.cong_3_swap Tarski_neutral_dimensionless.cong_3_swap_2 Tarski_neutral_dimensionless_axioms assms(1) assms(2) l4_6)

lemma l4_14R1:
  assumes "Bet A B C" and
    "Cong A B A' B'"
  shows "\<exists> C'. A B C Cong3 A' B' C'"
  by (simp add: assms(1) assms(2) bet_cong3)

lemma l4_14R2:
  assumes "Bet B C A" and
    "Cong A B A' B'"
  shows "\<exists> C'. A B C Cong3 A' B' C'"
  by (meson assms(1) assms(2) between_symmetry cong_3_swap_2 l4_5)

lemma l4_14R3:
  assumes "Bet C A B" and
    "Cong A B A' B'"
  shows "\<exists> C'. A B C Cong3 A' B' C'"
  by (meson assms(1) assms(2) between_symmetry cong_3_swap l4_14R1 not_cong_2143)

lemma l4_14:
  assumes "Col A B C" and
    "Cong A B A' B'"
  shows "\<exists> C'. A B C Cong3 A' B' C'"
  using Col_def assms(1) assms(2) l4_14R1 l4_14R2 l4_14R3 by blast

lemma l4_16R1:
  assumes "A B C D FSC A' B' C' D'" and
    "A \<noteq> B" and
    "Bet A B C"
  shows "Cong C D C' D'"
proof -
  have "A B C Cong3 A' B' C'"
    using FSC_def assms(1) by blast
  then have "Bet A' B' C'"
    using assms(3) l4_6 by blast
  then have "A B C D OFSC A' B' C' D'"
    by (meson Cong3_def FSC_def OFSC_def assms(1) cong_3_sym l4_6)
  thus ?thesis
    using assms(2) five_segment_with_def by blast
qed

lemma l4_16R2:
  assumes "A B C D FSC A' B' C' D'"
    and "Bet B C A"
  shows "Cong C D C' D'"
proof -
  have "A B C Cong3 A' B' C'"
    using FSC_def assms(1) by blast
  then have "Bet B' C' A'"
    using Bet_perm assms(2) cong_3_swap_2 l4_6 by blast
  then have "B C A D IFSC B' C' A' D'"
    by (meson Cong3_def FSC_def IFSC_def assms(1) assms(2) not_cong_2143)
  then show ?thesis
    using l4_2 by auto
qed

lemma l4_16R3:
  assumes "A B C D FSC A' B' C' D'" and "A \<noteq> B"
    and "Bet C A B"
  shows "Cong C D C' D'"
proof -
  have "A B C Cong3 A' B' C'"
    using FSC_def assms(1) by blast
  then have "Bet C' A' B'"
    using assms(3) between_symmetry cong_3_swap l4_6 by blast
  thus ?thesis
    by (smt Cong3_def FSC_def assms(1) assms(2) assms(3) between_symmetry cong_commutativity five_segment)
qed

lemma l4_16:
  assumes "A B C D FSC A' B' C' D'" and
    "A \<noteq> B"
  shows "Cong C D C' D'"
  by (meson Col_def FSC_def assms(1) assms(2) l4_16R1 l4_16R2 l4_16R3)

lemma l4_17:
  assumes "A \<noteq> B" and
    "Col A B C" and
    "Cong A P A Q" and
    "Cong B P B Q"
  shows "Cong C P C Q"
proof -
  {
    assume "\<not> Bet B C A"
    then have "\<exists>p pa. Bet p pa C \<and> Cong pa P pa Q \<and> Cong p P p Q \<and> p \<noteq> pa"
      using Col_def assms(1) assms(2) assms(3) assms(4) between_symmetry by blast
    then have ?thesis
      using cong_reflexivity five_segment by blast
  }
  then show ?thesis
    by (meson IFSC_def assms(3) assms(4) cong_reflexivity l4_2)
qed


lemma l4_18:
  assumes "A \<noteq> B" and
    "Col A B C" and
    "Cong A C A C'" and
    "Cong B C B C'"
  shows "C = C'"
  using assms(1) assms(2) assms(3) assms(4) cong_diff_3 l4_17 by blast

lemma l4_19:
  assumes "Bet A C B" and
    "Cong A C A C'" and
    "Cong B C B C'"
  shows "C = C'"
  by (metis Col_def assms(1) assms(2) assms(3) between_equality between_trivial cong_identity l4_18 not_cong_3421)

lemma not_col_distincts:
  assumes "\<not> Col A B C"
  shows "\<not> Col A B C \<and> A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C"
  using Col_def assms between_trivial by blast

lemma NCol_cases:
  assumes "\<not> Col A B C \<or> \<not> Col A C B \<or> \<not> Col B A C \<or> \<not> Col B C A \<or> \<not> Col C A B \<or> \<not> Col C B A"
  shows  "\<not> Col A B C"
  using assms not_col_permutation_2 not_col_permutation_3 by blast

lemma NCol_perm:
  assumes "\<not> Col A B C"
  shows "\<not> Col A B C \<and> ~ Col A C B \<and> ~ Col B A C \<and> ~ Col B C A \<and> ~ Col C A B \<and> ~ Col C B A"
  using NCol_cases assms by blast

lemma col_cong_3_cong_3_eq:
  assumes "A \<noteq> B"
    and "Col A B C"
    and "A B C Cong3 A' B' C1"
    and  "A B C Cong3 A' B' C2"
  shows  "C1 = C2"
  by (metis Tarski_neutral_dimensionless.Cong3_def Tarski_neutral_dimensionless.cong_diff Tarski_neutral_dimensionless.l4_18 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) cong_inner_transitivity l4_13)

subsection "Between transitivity le"

lemma l5_1:
  assumes "A \<noteq> B" and
    "Bet A B C" and
    "Bet A B D"
  shows "Bet A C D \<or> Bet A D C"
proof -
  obtain C' where P1: "Bet A D C' \<and> Cong D C' C D"
    using segment_construction by blast
  obtain D' where P2: "Bet A C D' \<and> Cong C D' C D"
    using segment_construction by blast
  obtain B' where P3: "Bet A C' B' \<and> Cong C' B' C B"
    using segment_construction by blast
  obtain B'' where P4: "Bet A D' B'' \<and> Cong D' B'' D B"
    using segment_construction by blast
  then have P5: "Cong B C' B'' C"
    by (smt P1 P2 assms(3) between_exchange3 between_symmetry cong_4312 cong_inner_transitivity l2_11_b)
  then have "Cong B B' B'' B"
    by (meson Bet_cases P1 P2 P3 P4 assms(2) assms(3) between_exchange4 between_inner_transitivity l2_11_b)
  then have P6: "B'' = B'"
    by (meson P1 P2 P3 P4 assms(1) assms(2) assms(3) between_exchange4 cong_inner_transitivity construction_uniqueness not_cong_2134)
  have "Bet B C D'"
    using P2 assms(2) between_exchange3 by blast
  then have "B C D' C' FSC B' C' D C"
    by (smt Cong3_def FSC_def P1 P2 P3 P5 P6 bet_col between_exchange3 between_symmetry cong_3421 cong_pseudo_reflexivity cong_transitivity l2_11_b)
  then have P8: "Cong D' C' D C"
    using P3 P4 P6 cong_identity l4_16 by blast
  obtain E where P9: "Bet C E C' \<and> Bet D E D'"
    using P1 P2 between_trivial2 l3_17 by blast
  then have P10: "D E D' C IFSC D E D' C'"
    by (smt IFSC_def P1 P2 P8 Tarski_neutral_dimensionless.cong_reflexivity Tarski_neutral_dimensionless_axioms cong_3421 cong_inner_transitivity)
  then have "Cong E C E C'"
    using l4_2 by auto
  have P11: "C E C' D IFSC C E C' D'"
    by (smt IFSC_def P1 P2 Tarski_neutral_dimensionless.cong_reflexivity Tarski_neutral_dimensionless_axioms P8 P9 cong_3421 cong_inner_transitivity)
  then have "Cong E D E D'"
    using l4_2 by auto
  obtain P where "Bet C' C P \<and> Cong C P C D'"
    using segment_construction by blast
  obtain R where "Bet D' C R \<and> Cong C R C E"
    using segment_construction by blast
  obtain Q where "Bet P R Q \<and> Cong R Q R P"
    using segment_construction by blast
  have "D' C R P FSC P C E D'"
    by (meson Bet_perm Cong3_def FSC_def \<open>Bet C E C' \<and> Bet D E D'\<close> \<open>Bet C' C P \<and> Cong C P C D'\<close> \<open>Bet D' C R \<and> Cong C R C E\<close> bet_col between_exchange3 cong_pseudo_reflexivity l2_11_b not_cong_4321)
  have "Cong R P E D'"
    by (metis Cong_cases \<open>D' C R P FSC P C E D'\<close> \<open>Bet C' C P \<and> Cong C P C D'\<close> \<open>Bet D' C R \<and> Cong C R C E\<close> cong_diff_2 l4_16)
  have "Cong R Q E D"
    by (metis Cong_cases \<open>Cong E D E D'\<close> \<open>Cong R P E D'\<close> \<open>Bet P R Q \<and> Cong R Q R P\<close> cong_transitivity)
  have "D' E D C FSC P R Q C"
    by (meson Bet_perm Cong3_def FSC_def \<open>Cong R P E D'\<close> \<open>Cong R Q E D\<close> \<open>Bet C E C' \<and> Bet D E D'\<close> \<open>Bet C' C P \<and> Cong C P C D'\<close> \<open>Bet D' C R \<and> Cong C R C E\<close> \<open>Bet P R Q \<and> Cong R Q R P\<close> bet_col l2_11_b not_cong_2143 not_cong_4321)
  have "Cong D C Q C"
    using \<open>D' E D C FSC P R Q C\<close> \<open>Cong E D E D'\<close> \<open>Bet C E C' \<and> Bet D E D'\<close> cong_identity l4_16 l4_16R2 by blast
  have "Cong C P C Q"
    using P2 \<open>Cong D C Q C\<close> \<open>Bet C' C P \<and> Cong C P C D'\<close> cong_right_commutativity cong_transitivity by blast
  have "Bet A C D \<or> Bet A D C"
  proof cases
    assume "R = C"
    then show ?thesis
      by (metis P1 \<open>Cong E C E C'\<close> \<open>Bet D' C R \<and> Cong C R C E\<close> cong_diff_4)
  next
    assume "R \<noteq> C"
    {
      have "Cong D' P D' Q"
      proof -

        have "Col R C D'"
          by (simp add: \<open>Bet D' C R \<and> Cong C R C E\<close> bet_col between_symmetry)
        have "Cong R P R Q"
          by (metis Tarski_neutral_dimensionless.Cong_cases Tarski_neutral_dimensionless_axioms \<open>Bet P R Q \<and> Cong R Q R P\<close>)
        have "Cong C P C Q"
          by (simp add: \<open>Cong C P C Q\<close>)
        then show ?thesis
          using \<open>Col R C D'\<close> \<open>Cong R P R Q\<close> \<open>R \<noteq> C\<close> l4_17 by blast
      qed
      then have "Cong B P B Q" using  \<open>Cong C P C Q\<close> \<open>Bet B C D'\<close> cong_diff_4
        by (metis Col_def \<open>Bet C' C P \<and> Cong C P C D'\<close> cong_reflexivity l4_17 not_cong_3412)
      have "Cong B' P B' Q"
        by (metis P2 P4 \<open>B'' = B'\<close> \<open>Cong C P C Q\<close> \<open>Cong D' P D' Q\<close> \<open>Bet C' C P \<and> Cong C P C D'\<close> between_exchange3 cong_diff_4 cong_identity cong_reflexivity five_segment)
      have "Cong C' P C' Q"
      proof -
        have "Bet B C' B'"
          using P1 P3 assms(3) between_exchange3 between_exchange4 by blast
        then show ?thesis
          by (metis Col_def \<open>Cong B P B Q\<close> \<open>Cong B' P B' Q\<close> between_equality l4_17 not_bet_distincts)
      qed
      have "Cong P P P Q"
        by (metis Tarski_neutral_dimensionless.cong_diff_2 Tarski_neutral_dimensionless_axioms \<open>Cong C P C Q\<close> \<open>Cong C' P C' Q\<close> \<open>R \<noteq> C\<close> \<open>Bet C E C' \<and> Bet D E D'\<close> \<open>Bet C' C P \<and> Cong C P C D'\<close> \<open>Bet D' C R \<and> Cong C R C E\<close> bet_col bet_neq12__neq l4_17)
      thus ?thesis
        by (metis P2 \<open>Cong R P E D'\<close> \<open>Cong R Q E D\<close> \<open>Bet P R Q \<and> Cong R Q R P\<close> bet_neq12__neq cong_diff_4)
    }
    then have "R \<noteq> C \<longrightarrow> Bet A C D \<or> Bet A D C" by blast
  qed
  thus ?thesis
    by simp
qed

lemma l5_2:
  assumes "A \<noteq> B" and
    "Bet A B C" and
    "Bet A B D"
  shows  "Bet B C D \<or> Bet B D C"
  using assms(1) assms(2) assms(3) between_exchange3 l5_1 by blast

lemma segment_construction_2:
  assumes  "A \<noteq> Q"
  shows "\<exists> X. ((Bet Q A X \<or> Bet Q X A) \<and> Cong Q X B C)"
proof -
  obtain A' where P1: "Bet A Q A' \<and> Cong Q A' A Q"
    using segment_construction by blast
  obtain X where P2: "Bet A' Q X \<and> Cong Q X B C"
    using segment_construction by blast
  then show ?thesis
    by (metis P1 Tarski_neutral_dimensionless.cong_diff_4 Tarski_neutral_dimensionless_axioms between_symmetry l5_2)
qed

lemma l5_3:
  assumes "Bet A B D" and
    "Bet A C D"
  shows "Bet A B C \<or> Bet A C B"
  by (metis Bet_perm assms(1) assms(2) between_inner_transitivity l5_2 point_construction_different)

lemma bet3__bet:
  assumes "Bet A B E" and
    "Bet A D E" and
    "Bet B C D"
  shows "Bet A C E"
  by (meson assms(1) assms(2) assms(3) between_exchange2 between_symmetry l5_3)

lemma le_bet:
  assumes "C D Le A B"
  shows "\<exists> X. (Bet A X B \<and> Cong A X C D)"
  by (meson Le_def assms cong_symmetry)

lemma l5_5_1:
  assumes "A B Le C D"
  shows "\<exists> X. (Bet A B X \<and> Cong A X C D)"
proof -
  obtain P where P1: "Bet C P D \<and> Cong A B C P"
    using Le_def assms by blast
  obtain X where P2: "Bet A B X \<and> Cong B X P D"
    using segment_construction by blast
  then have "Cong A X C D"
    using P1 l2_11_b by blast
  then show ?thesis
    using P2 by blast
qed

lemma l5_5_2:
  assumes "\<exists> X. (Bet A B X \<and> Cong A X C D)"
  shows "A B Le C D"
proof -
  obtain P where P1: "Bet A B P \<and> Cong A P C D"
    using assms by blast
  obtain B' where P2: "Bet C B' D \<and> A B P Cong3 C B' D"
    using P1 l4_5 by blast
  then show ?thesis
    using Cong3_def Le_def by blast
qed

lemma l5_6:
  assumes "A B Le C D" and
    "Cong A B A' B'" and
    "Cong C D C' D'"
  shows "A' B' Le C' D'"
  by (meson Cong3_def Le_def assms(1) assms(2) assms(3) cong_inner_transitivity l4_5)

lemma le_reflexivity:
  shows "A B Le A B"
  using between_trivial cong_reflexivity l5_5_2 by blast

lemma le_transitivity:
  assumes "A B Le C D" and
    "C D Le E F"
  shows "A B Le E F"
  by (meson assms(1) assms(2) between_exchange4 cong_reflexivity l5_5_1 l5_5_2 l5_6 le_bet)

lemma between_cong:
  assumes "Bet A C B" and
    "Cong A C A B"
  shows "C = B"
  by (smt assms(1) assms(2) between_trivial cong_inner_transitivity five_segment l4_19 l4_3_1)

lemma cong3_symmetry:
  assumes "A B C Cong3 A' B' C'"
  shows "A' B' C' Cong3 A B C"
  by (simp add: assms cong_3_sym)

lemma between_cong_2:
  assumes "Bet A D B" and
    "Bet A E B"
    and "Cong A D A E"
  shows "D = E" using l5_3
  by (smt Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) cong_diff cong_inner_transitivity l4_3_1)

lemma between_cong_3:
  assumes "A \<noteq> B"
    and "Bet A B D"
    and "Bet A B E"
    and "Cong B D B E"
  shows "D = E"
  by (meson assms(1) assms(2) assms(3) assms(4) cong_reflexivity construction_uniqueness)

lemma le_anti_symmetry:
  assumes "A B Le C D" and
    "C D Le A B"
  shows "Cong A B C D"
  by (smt Le_def Tarski_neutral_dimensionless.between_exchange4 Tarski_neutral_dimensionless_axioms assms(1) assms(2) bet_neq21__neq between_cong between_exchange3 cong_transitivity l5_5_1 not_cong_3421)

lemma cong_dec:
  shows "Cong A B C D \<or> \<not> Cong A B C D"
  by simp

lemma bet_dec:
  shows "Bet A B C  \<or> \<not> Bet A B C"
  by simp

lemma col_dec:
  shows "Col A B C \<or> \<not> Col A B C"
  by simp

lemma le_trivial:
  shows "A A Le C D"
  using Le_def between_trivial2 cong_trivial_identity by blast

lemma le_cases:
  shows "A B Le C D \<or> C D Le A B"
  by (metis (full_types) cong_reflexivity l5_5_2 l5_6 not_bet_distincts segment_construction_2)

lemma le_zero:
  assumes "A B Le C C"
  shows "A = B"
  by (metis assms cong_diff_4 le_anti_symmetry le_trivial)

lemma le_diff:
  assumes "A \<noteq> B" and "A B Le C D"
  shows "C \<noteq> D"
  using assms(1) assms(2) le_zero by blast

lemma lt_diff:
  assumes "A B Lt C D"
  shows "C \<noteq> D"
  using Lt_def assms cong_trivial_identity le_zero by blast

lemma bet_cong_eq:
  assumes "Bet A B C" and
    "Bet A C D" and
    "Cong B C A D"
  shows "C = D \<and> A = B"
proof -
  have "Bet C B A"
    using Bet_perm assms(1) by blast
  then show ?thesis
    by (metis (no_types) Cong_perm Le_def assms(2) assms(3) between_cong cong_pseudo_reflexivity le_anti_symmetry)
qed

lemma cong__le:
  assumes "Cong A B C D"
  shows "A B Le C D"
  using Le_def assms between_trivial by blast

lemma cong__le3412:
  assumes "Cong A B C D"
  shows "C D Le A B"
  using assms cong__le cong_symmetry by blast

lemma le1221:
  shows "A B Le B A"
  by (simp add: cong__le cong_pseudo_reflexivity)

lemma le_left_comm:
  assumes "A B Le C D"
  shows "B A Le C D"
  using assms le1221 le_transitivity by blast

lemma le_right_comm:
  assumes "A B Le C D"
  shows "A B Le D C"
  by (meson assms cong_right_commutativity l5_5_1 l5_5_2)

lemma le_comm:
  assumes "A B Le C D"
  shows "B A Le D C"
  using assms le_left_comm le_right_comm by blast

lemma ge_left_comm:
  assumes "A B Ge C D"
  shows "B A Ge C D"
  by (meson Ge_def assms le_right_comm)

lemma ge_right_comm:
  assumes "A B Ge C D"
  shows "A B Ge D C"
  using Ge_def assms le_left_comm by presburger

lemma ge_comm0:
  assumes "A B Ge C D"
  shows "B A Ge D C"
  by (meson assms ge_left_comm ge_right_comm)

lemma lt_right_comm:
  assumes "A B Lt C D"
  shows "A B Lt D C"
  using Lt_def assms le_right_comm not_cong_1243 by blast

lemma lt_left_comm:
  assumes "A B Lt C D"
  shows "B A Lt C D"
  using Lt_def assms le_comm lt_right_comm not_cong_2143 by blast

lemma lt_comm:
  assumes "A B Lt C D"
  shows "B A Lt D C"
  using assms lt_left_comm lt_right_comm by blast

lemma gt_left_comm0:
  assumes "A B Gt C D"
  shows "B A Gt C D"
  by (meson Gt_def assms lt_right_comm)

lemma gt_right_comm:
  assumes "A B Gt C D"
  shows "A B Gt D C"
  using Gt_def assms lt_left_comm by presburger

lemma gt_comm:
  assumes "A B Gt C D"
  shows "B A Gt D C"
  by (meson assms gt_left_comm0 gt_right_comm)

lemma cong2_lt__lt:
  assumes "A B Lt C D" and
    "Cong A B A' B'" and
    "Cong C D C' D'"
  shows "A' B' Lt C' D'"
  by (meson Lt_def assms(1) assms(2) assms(3) l5_6 le_anti_symmetry not_cong_3412)

lemma fourth_point:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Col A B P" and
    "Bet A B C"
  shows "Bet P A B \<or> Bet A P B \<or> Bet B P C \<or> Bet B C P"
  by (metis Col_def Tarski_neutral_dimensionless.l5_2 Tarski_neutral_dimensionless_axioms assms(3) assms(4) between_symmetry)

lemma third_point:
  assumes "Col A B P"
  shows "Bet P A B \<or> Bet A P B \<or> Bet A B P"
  using Col_def assms between_symmetry by blast

lemma l5_12_a:
  assumes "Bet A B C"
  shows "A B Le A C \<and> B C Le A C"
  using assms between_symmetry cong_left_commutativity cong_reflexivity l5_5_2 le_left_comm by blast

lemma bet__le1213:
  assumes "Bet A B C"
  shows "A B Le A C"
  using assms l5_12_a by blast

lemma bet__le2313:
  assumes "Bet A B C"
  shows "B C Le A C"
  by (simp add: assms l5_12_a)

lemma bet__lt1213:
  assumes "B \<noteq> C" and
    "Bet A B C"
  shows "A B Lt A C"
  using Lt_def assms(1) assms(2) bet__le1213 between_cong by blast

lemma bet__lt2313:
  assumes "A \<noteq> B" and
    "Bet A B C"
  shows "B C Lt A C"
  using Lt_def assms(1) assms(2) bet__le2313 bet_cong_eq l5_1 by blast

lemma l5_12_b:
  assumes "Col A B C" and
    "A B Le A C" and
    "B C Le A C"
  shows "Bet A B C"
  by (metis assms(1) assms(2) assms(3) between_cong col_permutation_5 l5_12_a le_anti_symmetry not_cong_2143 third_point)

lemma bet_le_eq:
  assumes "Bet A B C"
    and "A C Le B C"
  shows "A = B"
  by (meson assms(1) assms(2) bet__le2313 bet_cong_eq l5_1 le_anti_symmetry)

lemma or_lt_cong_gt:
  "A B Lt C D \<or> A B Gt C D \<or> Cong A B C D"
  by (meson Gt_def Lt_def cong_symmetry local.le_cases)

lemma lt__le:
  assumes "A B Lt C D"
  shows "A B Le C D"
  using Lt_def assms by blast

lemma le1234_lt__lt:
  assumes "A B Le C D" and
    "C D Lt E F"
  shows "A B Lt E F"
  by (meson Lt_def assms(1) assms(2) cong__le3412 le_anti_symmetry le_transitivity)

lemma le3456_lt__lt:
  assumes "A B Lt C D" and
    "C D Le E F"
  shows "A B Lt E F"
  by (meson Lt_def assms(1) assms(2) cong2_lt__lt cong_reflexivity le1234_lt__lt)

lemma lt_transitivity:
  assumes "A B Lt C D" and
    "C D Lt E F"
  shows "A B Lt E F"
  using Lt_def assms(1) assms(2) le1234_lt__lt by blast

lemma not_and_lt:
  "\<not> (A B Lt C D \<and> C D Lt A B)"
  by (simp add: Lt_def le_anti_symmetry)

lemma nlt:
  "\<not> A B Lt A B"
  using not_and_lt by blast

lemma le__nlt:
  assumes "A B Le C D"
  shows "\<not> C D Lt A B"
  using assms le3456_lt__lt nlt by blast

lemma cong__nlt:
  assumes "Cong A B C D"
  shows "\<not> A B Lt C D"
  by (simp add: Lt_def assms)

lemma nlt__le:
  assumes "\<not> A B Lt C D"
  shows "C D Le A B"
  using Lt_def assms cong__le3412 local.le_cases by blast

lemma lt__nle:
  assumes "A B Lt C D"
  shows "\<not> C D Le A B"
  using assms le__nlt by blast

lemma nle__lt:
  assumes "\<not> A B Le C D"
  shows "C D Lt A B"
  using assms nlt__le by blast

lemma lt1123:
  assumes "B \<noteq> C"
  shows "A A Lt B C"
  using assms le_diff nle__lt by blast

lemma bet2_le2__le_R1:
  assumes "Bet a P b" and
    "Bet A Q B" and
    "P a Le Q A" and
    "P b Le Q B" and
    "B = Q"
  shows "a b Le A B"
  by (metis assms(3) assms(4) assms(5) le_comm le_diff)

lemma bet2_le2__le_R2:
  assumes "Bet a Po b" and
    "Bet A PO B" and
    "Po a Le PO A" and
    "Po b Le PO B" and
    "A \<noteq> PO" and
    "B \<noteq> PO"
  shows "a b Le A B"
proof -
  obtain b' where P1: "Bet A PO b' \<and> Cong PO b' b Po"
    using segment_construction by blast
  obtain a' where P2: "Bet B PO a' \<and> Cong PO a' a Po"
    using segment_construction by blast
  obtain a'' where P3: "Bet PO a'' A \<and> Cong Po a PO a''"
    using Le_def assms(3) by blast
  have P4: "a' = a''"
    by (meson Bet_cases P2 P3 assms(2) assms(6) between_inner_transitivity cong_right_commutativity construction_uniqueness not_cong_3412)
  have P5: "B a' Le B A"
    using Bet_cases P3 P4 assms(2) bet__le1213 between_exchange2 by blast
  obtain b'' where P6: "Bet PO b'' B \<and> Cong Po b PO b''"
    using Le_def assms(4) by blast
  then have "b' = b''"
    using P1 assms(2) assms(5) between_inner_transitivity cong_right_commutativity construction_uniqueness not_cong_3412 by blast
  then have "a' b' Le a' B"
    using Bet_cases P2 P6 bet__le1213 between_exchange2 by blast
  then have "a' b' Le A B"
    using P5 le_comm le_transitivity by blast
  thus ?thesis
    by (smt Cong_cases P1 P3 P4 Tarski_neutral_dimensionless.l5_6 Tarski_neutral_dimensionless_axioms assms(1) between_exchange3 between_symmetry cong_reflexivity l2_11_b)
qed

lemma bet2_le2__le:
  assumes "Bet a P b" and
    "Bet A Q B" and
    "P a Le Q A" and
    "P b Le Q B"
  shows "a b Le A B"
proof cases
  assume "A = Q"
  thus ?thesis
    using assms(3) assms(4) le_diff by force
next
  assume "\<not> A = Q"
  thus ?thesis
    using assms(1) assms(2) assms(3) assms(4) bet2_le2__le_R1 bet2_le2__le_R2 by blast
qed

lemma Le_cases:
  assumes "A B Le C D \<or> B A Le C D \<or> A B Le D C \<or> B A Le D C"
  shows "A B Le C D"
  using assms le_left_comm le_right_comm by blast

lemma Lt_cases:
  assumes "A B Lt C D \<or> B A Lt C D \<or> A B Lt D C \<or> B A Lt D C"
  shows "A B Lt C D"
  using assms lt_comm lt_left_comm by blast

subsection "Out lines"

lemma bet_out:
  assumes "B \<noteq> A" and
    "Bet A B C"
  shows  "A Out B C"
  using Out_def assms(1) assms(2) bet_neq12__neq by fastforce

lemma bet_out_1:
  assumes "B \<noteq> A" and
    "Bet C B A"
  shows "A Out B C"
  by (simp add: assms(1) assms(2) bet_out between_symmetry)

lemma out_dec:
  shows "P Out A B \<or> \<not> P Out A B"
  by simp

lemma out_diff1:
  assumes "A Out B C"
  shows "B \<noteq> A"
  using Out_def assms by auto

lemma out_diff2:
  assumes "A Out B C"
  shows "C \<noteq> A"
  using Out_def assms by auto

lemma out_distinct:
  assumes "A Out B C"
  shows  "B \<noteq> A \<and> C \<noteq> A"
  using assms out_diff1 out_diff2 by auto

lemma out_col:
  assumes "A Out B C"
  shows "Col A B C"
  using Col_def Out_def assms between_symmetry by auto

lemma l6_2:
  assumes "A \<noteq> P" and
    "B \<noteq> P" and
    "C \<noteq> P" and
    "Bet A P C"
  shows "Bet B P C \<longleftrightarrow> P Out A B"
  by (smt Bet_cases Out_def assms(1) assms(2) assms(3) assms(4) between_inner_transitivity l5_2 outer_transitivity_between)

lemma bet_out__bet:
  assumes "Bet A P C" and
    "P Out A B"
  shows "Bet B P C"
  by (metis Tarski_neutral_dimensionless.l6_2 Tarski_neutral_dimensionless_axioms assms(1) assms(2) not_bet_distincts out_diff1)

lemma l6_3_1:
  assumes "P Out A B"
  shows "A \<noteq> P \<and> B \<noteq> P \<and> (\<exists> C. (C \<noteq> P \<and> Bet A P C \<and> Bet B P C))"
  using assms bet_out__bet out_diff1 out_diff2 point_construction_different by fastforce

lemma l6_3_2:
  assumes "A \<noteq> P" and
    "B \<noteq> P" and
    "\<exists> C. (C \<noteq> P \<and> Bet A P C \<and> Bet B P C)"
  shows "P Out A B"
  using assms(1) assms(2) assms(3) l6_2 by blast

lemma l6_4_1:
  assumes "P Out A B" and
    "Col A P B"
  shows "\<not> Bet A P B"
  using Out_def assms(1) between_equality between_symmetry by fastforce

lemma l6_4_2:
  assumes "Col A P B"
    and "\<not> Bet A P B"
  shows "P Out A B"
  by (metis Out_def assms(1) assms(2) bet_out col_permutation_1 third_point)

lemma out_trivial:
  assumes "A \<noteq> P"
  shows "P Out A A"
  by (simp add: assms bet_out_1 between_trivial2)

lemma l6_6:
  assumes "P Out A B"
  shows "P Out B A"
  using Out_def assms by auto

lemma l6_7:
  assumes "P Out A B" and
    "P Out B C"
  shows "P Out A C"
  by (smt Out_def assms(1) assms(2) between_exchange4 l5_1 l5_3)

lemma bet_out_out_bet:
  assumes "Bet A B C" and
    "B Out A A'" and
    "B Out C C'"
  shows "Bet A' B C'"
  by (metis Out_def assms(1) assms(2) assms(3) bet_out__bet between_inner_transitivity outer_transitivity_between)

lemma out2_bet_out:
  assumes "B Out A C" and
    "B Out X P" and
    "Bet A X C"
  shows "B Out A P \<and> B Out C P"
  by (smt Out_def Tarski_neutral_dimensionless.l6_7 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) between_exchange2 between_symmetry)

lemma l6_11_uniqueness:
  assumes "A Out X R" and
    "Cong A X B C" and
    "A Out Y R" and
    "Cong A Y B C"
  shows "X = Y"
  by (metis Out_def assms(1) assms(2) assms(3) assms(4) between_cong cong_symmetry cong_transitivity l6_6 l6_7)

lemma l6_11_existence:
  assumes "R \<noteq> A" and
    "B \<noteq> C"
  shows "\<exists> X. (A Out X R \<and> Cong A X B C)"
  by (metis Out_def assms(1) assms(2) cong_reverse_identity segment_construction_2)


lemma segment_construction_3:
  assumes "A \<noteq> B" and
    "X \<noteq> Y"
  shows "\<exists> C. (A Out B C \<and> Cong A C X Y)"
  by (metis assms(1) assms(2) l6_11_existence l6_6)

lemma l6_13_1:
  assumes "P Out A B" and
    "P A Le P B"
  shows "Bet P A B"
  by (metis Out_def assms(1) assms(2) bet__lt1213 le__nlt)

lemma l6_13_2:
  assumes "P Out A B" and
    "Bet P A B"
  shows "P A Le P B"
  by (simp add: assms(2) bet__le1213)

lemma l6_16_1:
  assumes "P \<noteq> Q" and
    "Col S P Q" and
    "Col X P Q"
  shows "Col X P S"
  by (smt Col_def assms(1) assms(2) assms(3) bet3__bet col_permutation_4 l5_1 l5_3 outer_transitivity_between third_point)

lemma col_transitivity_1:
  assumes "P \<noteq> Q" and
    "Col P Q A" and
    "Col P Q B"
  shows "Col P A B"
  by (meson Tarski_neutral_dimensionless.l6_16_1 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) not_col_permutation_2)

lemma col_transitivity_2:
  assumes "P \<noteq> Q" and
    "Col P Q A" and
    "Col P Q B"
  shows "Col Q A B"
  by (metis Tarski_neutral_dimensionless.col_transitivity_1 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) not_col_permutation_4)

lemma l6_21:
  assumes "\<not> Col A B C" and
    "C \<noteq> D" and
    "Col A B P" and
    "Col A B Q" and
    "Col C D P" and
    "Col C D Q"
  shows "P = Q"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) col_transitivity_1 l6_16_1 not_col_distincts)

lemma col2__eq:
  assumes "Col A X Y" and
    "Col B X Y" and
    "\<not> Col A X B"
  shows  "X = Y"
  using assms(1) assms(2) assms(3) l6_16_1 by blast

lemma not_col_exists:
  assumes  "A \<noteq> B"
  shows "\<exists> C. \<not> Col A B C"
  by (metis Col_def assms col_transitivity_2 lower_dim_ex)

lemma col3:
  assumes "X \<noteq> Y" and
    "Col X Y A" and
    "Col X Y B" and
    "Col X Y C"
  shows "Col A B C"
  by (metis assms(1) assms(2) assms(3) assms(4) col_transitivity_2)

lemma colx:
  assumes "A \<noteq> B" and
    "Col X Y A" and
    "Col X Y B" and
    "Col A B C"
  shows "Col X Y C"
  by (metis assms(1) assms(2) assms(3) assms(4) l6_21 not_col_distincts)

lemma out2__bet:
  assumes "A Out B C" and
    "C Out A B"
  shows "Bet A B C"
  by (metis Out_def assms(1) assms(2) between_equality between_symmetry)

lemma bet2_le2__le1346:
  assumes "Bet A B C" and
    "Bet A' B' C'" and
    "A B Le A' B'" and
    "B C Le B' C'"
  shows "A C Le A' C'"
  using Le_cases assms(1) assms(2) assms(3) assms(4) bet2_le2__le by blast

lemma bet2_le2__le2356_R1:
  assumes "Bet A A C" and
    "Bet A' B' C'" and
    "A A Le A' B'" and
    "A' C' Le A C"
  shows "B' C' Le A C"
  using assms(2) assms(4) bet__le2313 le3456_lt__lt lt__nle nlt__le by blast

lemma bet2_le2__le2356_R2:
  assumes "A \<noteq> B" and
    "Bet A B C" and
    "Bet A' B' C'" and
    "A B Le A' B'" and
    "A' C' Le A C"
  shows "B' C' Le B C"
proof -
  have "A \<noteq> C"
    using assms(1) assms(2) bet_neq12__neq by blast
  obtain B0 where P1: "Bet A B B0 \<and> Cong A B0 A' B'"
    using assms(4) l5_5_1 by blast
  then have P2: "A \<noteq> B0"
    using assms(1) bet_neq12__neq by blast
  obtain C0 where P3: "Bet A C0 C \<and> Cong A' C' A C0"
    using Le_def assms(5) by blast
  then have "A \<noteq> C0"
    using assms(1) assms(3) assms(4) bet_neq12__neq cong_diff le_diff by blast
  then have P4: "Bet A B0 C0"
    by (smt Out_def P1 P2 P3 assms(1) assms(2) assms(3) bet__le1213 between_exchange2 between_symmetry l5_1 l5_3 l5_6 l6_13_1 not_cong_3412)
  have K1: "B0 C0 Le B C0"
    using P1 P4 between_exchange3 l5_12_a by blast
  have K2: "B C0 Le B C"
    using P1 P3 P4 bet__le1213 between_exchange3 between_exchange4 by blast
  then have "Cong B0 C0 B' C'"
    using P1 P3 P4 assms(3) l4_3_1 not_cong_3412 by blast
  then show ?thesis
    by (meson K1 K2 cong__nlt le_transitivity nlt__le)
qed

lemma bet2_le2__le2356:
  assumes "Bet A B C" and
    "Bet A' B' C'" and
    "A B Le A' B'" and
    "A' C' Le A C"
  shows "B' C' Le B C"
proof (cases)
  assume "A = B"
  then show ?thesis
    using assms(1) assms(2) assms(3) assms(4) bet2_le2__le2356_R1 by blast
next
  assume "\<not> A = B"
  then show ?thesis
    using assms(1) assms(2) assms(3) assms(4) bet2_le2__le2356_R2 by blast
qed

lemma bet2_le2__le1245:
  assumes "Bet A B C" and
    "Bet A' B' C'" and
    "B C Le B' C'" and
    "A' C' Le A C"
  shows "A' B' Le A B"
  using assms(1) assms(2) assms(3) assms(4) bet2_le2__le2356 between_symmetry le_comm by blast

lemma cong_preserves_bet:
  assumes "Bet B A' A0" and
    "Cong B A' E D'" and
    "Cong B A0 E D0" and
    "E Out D' D0"
  shows "Bet E D' D0"
  using Tarski_neutral_dimensionless.l6_13_1 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) bet__le1213 l5_6 by fastforce

lemma out_cong_cong:
  assumes "B Out A A0" and
    "E Out D D0" and
    "Cong B A E D" and
    "Cong B A0 E D0"
  shows "Cong A A0 D D0"
  by (meson Out_def assms(1) assms(2) assms(3) assms(4) cong_4321 cong_symmetry l4_3_1 l5_6 l6_13_1 l6_13_2)

lemma not_out_bet:
  assumes "Col A B C" and
    "\<not> B Out A C"
  shows "Bet A B C"
  using assms(1) assms(2) l6_4_2 by blast

lemma or_bet_out:
  shows "Bet A B C \<or> B Out A C \<or> \<not> Col A B C"
  using not_out_bet by blast

lemma not_bet_out:
  assumes "Col A B C" and
    "\<not> Bet A B C"
  shows "B Out A C"
  by (simp add: assms(1) assms(2) l6_4_2)

lemma not_bet_and_out:
  shows  "\<not> (Bet A B C \<and> B Out A C)"
  using bet_col l6_4_1 by blast

lemma out_to_bet:
  assumes "Col A' B' C'" and
    "B Out A C \<longleftrightarrow> B' Out A' C'" and
    "Bet A B C"
  shows "Bet A' B' C'"
  using assms(1) assms(2) assms(3) not_bet_and_out or_bet_out by blast

lemma col_out2_col:
  assumes "Col A B C" and
    "B Out A AA" and
    "B Out C CC"
  shows "Col AA B CC" using l6_21
  by (smt Tarski_neutral_dimensionless.out_col Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) col_trivial_2 not_col_permutation_1 out_diff1)

lemma bet2_out_out:
  assumes "B \<noteq> A" and
    "B' \<noteq> A" and
    "A Out C C'" and
    "Bet A B C" and
    "Bet A B' C'"
  shows "A Out B B'"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) bet_out l6_6 l6_7)

lemma bet2__out:
  assumes "A \<noteq> B" and
    "A \<noteq> B'" and
    "Bet A B C"
    and "Bet A B' C"
  shows "A Out B B'"
  using Out_def assms(1) assms(2) assms(3) assms(4) l5_3 by auto

lemma out_bet_out_1:
  assumes "P Out A C" and
    "Bet A B C"
  shows "P Out A B"
  by (metis assms(1) assms(2) not_bet_and_out out2_bet_out out_trivial)

lemma out_bet_out_2:
  assumes "P Out A C" and
    "Bet A B C"
  shows "P Out B C"
  using assms(1) assms(2) l6_6 l6_7 out_bet_out_1 by blast

lemma out_bet__out:
  assumes "Bet P Q A" and
    "Q Out A B"
  shows "P Out A B"
  by (smt Out_def assms(1) assms(2) bet_out_1 bet_out__bet)

lemma segment_reverse:
  assumes "Bet A B C "
  shows "\<exists> B'. Bet A B' C \<and> Cong C B' A B"
  by (metis Bet_perm Cong_perm assms bet_cong_eq cong_reflexivity segment_construction_2)

lemma diff_col_ex:
  shows "\<exists> C. A \<noteq> C \<and> B \<noteq> C \<and> Col A B C"
  by (metis bet_col bet_neq12__neq point_construction_different)

lemma diff_bet_ex3:
  assumes "Bet A B C"
  shows "\<exists> D. A \<noteq> D \<and> B \<noteq> D \<and> C \<noteq> D \<and> Col A B D"
  by (metis (mono_tags, hide_lams) Col_def bet_out_1 between_trivial2 col_transitivity_1 l6_4_1 point_construction_different)

lemma diff_col_ex3:
  assumes "Col A B C"
  shows "\<exists> D. A \<noteq> D \<and> B \<noteq> D \<and> C \<noteq> D \<and> Col A B D"
  by (metis Bet_perm Col_def between_equality between_trivial2 point_construction_different)

lemma Out_cases:
  assumes "A Out B C \<or> A Out C B"
  shows "A Out B C"
  using assms l6_6 by blast

subsection "Midpoint"

lemma midpoint_dec:
  "I Midpoint A B \<or> \<not> I Midpoint A B"
  by simp

lemma is_midpoint_id:
  assumes "A Midpoint A B"
  shows "A = B"
  using Midpoint_def assms between_cong by blast

lemma is_midpoint_id_2:
  assumes "A Midpoint B A"
  shows "A = B"
  using Midpoint_def assms cong_diff_2 by blast

lemma l7_2:
  assumes "M Midpoint A B"
  shows "M Midpoint B A"
  using Bet_perm Cong_perm Midpoint_def assms by blast

lemma l7_3:
  assumes "M Midpoint A A"
  shows "M = A"
  using Midpoint_def assms bet_neq23__neq by blast

lemma l7_3_2:
  "A Midpoint A A"
  by (simp add: Midpoint_def between_trivial2 cong_reflexivity)

lemma symmetric_point_construction:
  "\<exists> P'. A Midpoint P P'"
  by (meson Midpoint_def cong__le cong__le3412 le_anti_symmetry segment_construction)

lemma symmetric_point_uniqueness:
  assumes "P Midpoint A P1" and
    "P Midpoint A P2"
  shows "P1 = P2"
  by (metis Midpoint_def assms(1) assms(2) between_cong_3 cong_diff_4 cong_inner_transitivity)

lemma l7_9:
  assumes "A Midpoint P X" and
    "A Midpoint Q X"
  shows "P = Q"
  using assms(1) assms(2) l7_2 symmetric_point_uniqueness by blast

lemma l7_9_bis:
  assumes "A Midpoint P X" and
    "A Midpoint X Q"
  shows "P = Q"
  using assms(1) assms(2) l7_2 symmetric_point_uniqueness by blast

lemma l7_13_R1:
  assumes "A \<noteq> P" and
    "A Midpoint P' P" and
    "A Midpoint Q' Q"
  shows "Cong P Q P' Q'"
proof -
  obtain X where P1: "Bet P' P X \<and> Cong P X Q A"
    using segment_construction by blast
  obtain X' where P2: "Bet X P' X' \<and> Cong P' X' Q A"
    using segment_construction by blast
  obtain Y where P3: "Bet Q' Q Y \<and> Cong Q Y P A"
    using segment_construction by blast
  obtain Y' where P4: "Bet Y Q' Y' \<and> Cong Q' Y' P A"
    using segment_construction by blast
  have P5: "Bet Y A Q'"
    by (meson Midpoint_def P3 P4 assms(3) bet3__bet between_symmetry l5_3)
  have P6: "Bet P' A X"
    using Midpoint_def P1 assms(2) between_exchange4 by blast
  have P7: "Bet A P X"
    using Midpoint_def P1 assms(2) between_exchange3 by blast
  have P8: "Bet Y Q A"
    using Midpoint_def P3 assms(3) between_exchange3 between_symmetry by blast
  have P9: "Bet A Q' Y'"
    using P4 P5 between_exchange3 by blast
  have P10: "Bet X' P' A"
    using P2 P6 between_exchange3 between_symmetry by blast
  have P11: "Bet X A X'"
    using P10 P2 P6 between_symmetry outer_transitivity_between2 by blast
  have P12: "Bet Y A Y'"
    using P4 P5 between_exchange4 by blast
  have P13: "Cong A X Y A"
    using P1 P3 P7 P8 l2_11_b not_cong_4321 by blast
  have P14: "Cong A Y' X' A"
  proof -
    have Q1: "Cong Q' Y' P' A"
      using Midpoint_def P4 assms(2) cong_transitivity not_cong_3421 by blast
    have "Cong A Q' X' P'"
      by (meson Midpoint_def P2 assms(3) cong_transitivity not_cong_3421)
    then show ?thesis
      using P10 P9 Q1 l2_11_b by blast
  qed
  have P15: "Cong A Y A Y'"
  proof -
    have "Cong Q Y Q' Y'"
      using P3 P4 cong_transitivity not_cong_3412 by blast
    then show ?thesis
      using Bet_perm Cong_perm Midpoint_def P8 P9 assms(3) l2_11_b by blast
  qed
  have P16: "Cong X A Y' A"
    using Cong_cases P13 P15 cong_transitivity by blast
  have P17: "Cong A X' A Y"
    using P14 P15 cong_transitivity not_cong_3421 by blast
  have P18: "X A X' Y' FSC Y' A Y X"
  proof -
    have Q3: "Col X A X'"
      by (simp add: Col_def P11)
    have "Cong X X' Y' Y"
      using Bet_cases P11 P12 P16 P17 l2_11_b by blast
    then show ?thesis
      by (simp add: Cong3_def FSC_def P16 P17 Q3 cong_4321 cong_pseudo_reflexivity)
  qed
  then have "Y Q A X IFSC Y' Q' A X'"
    by (smt IFSC_def Midpoint_def P14 P15 P16 P7 P8 P9 assms(1) assms(3) bet_neq12__neq between_symmetry cong_4321 cong_inner_transitivity cong_right_commutativity l4_16)
  then have "X P A Q IFSC X' P' A Q'"
    by (meson IFSC_def Midpoint_def P10 P7 assms(2) between_symmetry cong_4312 l4_2)
  then show ?thesis
    using l4_2 by auto
qed

lemma l7_13:
  assumes "A Midpoint P' P" and
    "A Midpoint Q' Q"
  shows "Cong P Q P' Q'"
proof (cases)
  assume "A = P"
  then show ?thesis
    using Midpoint_def assms(1) assms(2) cong_3421 is_midpoint_id_2 by blast
next
  show ?thesis
    by (metis Tarski_neutral_dimensionless.l7_13_R1 Tarski_neutral_dimensionless_axioms assms(1) assms(2) cong_trivial_identity is_midpoint_id_2 not_cong_2143)
qed

lemma l7_15:
  assumes "A Midpoint P P'" and
    "A Midpoint Q Q'" and
    "A Midpoint R R'" and
    "Bet P Q R"
  shows "Bet P' Q' R'"
proof -
  have "P Q R Cong3 P' Q' R'"
    using Cong3_def assms(1) assms(2) assms(3) l7_13 l7_2 by blast
  then show ?thesis
    using assms(4) l4_6 by blast
qed

lemma l7_16:
  assumes "A Midpoint P P'" and
    "A Midpoint Q Q'" and
    "A Midpoint R R'" and
    "A Midpoint S S'" and
    "Cong P Q R S"
  shows "Cong P' Q' R' S'"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) cong_transitivity l7_13 not_cong_3412)

lemma symmetry_preserves_midpoint:
  assumes "Z Midpoint A D" and
    "Z Midpoint B E" and
    "Z Midpoint C F" and
    "B Midpoint A C"
  shows "E Midpoint D F"
  by (meson Midpoint_def assms(1) assms(2) assms(3) assms(4) l7_15 l7_16)

lemma Mid_cases:
  assumes "A Midpoint B C \<or> A Midpoint C B"
  shows "A Midpoint B C"
  using assms l7_2 by blast

lemma Mid_perm:
  assumes "A Midpoint B C"
  shows "A Midpoint B C \<and> A Midpoint C B"
  by (simp add: assms l7_2)

lemma l7_17:
  assumes "A Midpoint P P'" and
    "B Midpoint P P'"
  shows "A = B"
proof -
  obtain pp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
    f1: "\<forall>p pa. p Midpoint pa (pp p pa)"
    by (meson symmetric_point_construction)
  then have "\<forall>p pa. Bet pa p (pp p pa)"
    by (meson Midpoint_def)
  then have f2: "\<forall>p. Bet p p p"
    by (meson between_inner_transitivity)
  have f3: "\<forall>p pa. Bet (pp pa p) pa p"
    using f1 Mid_perm Midpoint_def by blast
  have f4: "\<forall>p. pp p p = p"
    using f2 f1 by (metis Midpoint_def bet_cong_eq)
  have f5: "Bet (pp P P') P B"
    using f3 by (meson Midpoint_def assms(2) between_inner_transitivity)
  have f6: "A Midpoint P' P"
    using Mid_perm assms(1) by blast
  have f7: "Bet (pp P P') P A"
    using f3 Midpoint_def assms(1) between_inner_transitivity by blast
  have f8: "Bet P' A P"
    using f6 by (simp add: Midpoint_def)
  have "Cong P' A A P"
    using f6 Midpoint_def by blast
  then have "P' = P \<longrightarrow> A = B"
    using f8 by (metis (no_types) Midpoint_def assms(2) bet_cong_eq between_inner_transitivity l5_2)
  then show ?thesis
    using f7 f6 f5 f4 f1 by (metis (no_types) Col_perm Mid_perm assms(2) bet_col l4_18 l5_2 l7_13)
qed

lemma l7_17_bis:
  assumes "A Midpoint P P'" and
    "B Midpoint P' P"
  shows "A = B"
  by (meson Tarski_neutral_dimensionless.l7_17 Tarski_neutral_dimensionless.l7_2 Tarski_neutral_dimensionless_axioms assms(1) assms(2))

lemma l7_20:
  assumes "Col A M B" and
    "Cong M A M B"
  shows "A = B \<or> M Midpoint A B"
  by (metis Bet_cases Col_def Midpoint_def assms(1) assms(2) between_cong cong_left_commutativity not_cong_3412)

lemma l7_20_bis:
  assumes "A \<noteq> B" and
    "Col A M B" and
    "Cong M A M B"
  shows "M Midpoint A B"
  using assms(1) assms(2) assms(3) l7_20 by blast

lemma cong_col_mid:
  assumes "A \<noteq> C" and
    "Col A B C" and
    "Cong A B B C"
  shows "B Midpoint A C"
  using assms(1) assms(2) assms(3) cong_left_commutativity l7_20 by blast

lemma l7_21_R1:
  assumes "\<not> Col A B C" and
    "B \<noteq> D" and
    "Cong A B C D" and
    "Cong B C D A" and
    "Col A P C" and
    "Col B P D"
  shows "P Midpoint A C"
proof -
  obtain X where P1: "B D P Cong3 D B X"
    using Col_perm assms(6) cong_pseudo_reflexivity l4_14 by blast
  have P2: "Col D B X"
    using P1 assms(6) l4_13 not_col_permutation_5 by blast
  have P3: "B D P A FSC D B X C"
    using FSC_def P1 assms(3) assms(4) assms(6) not_col_permutation_5 not_cong_2143 not_cong_3412 by blast
  have P4: "B D P C FSC D B X A"
    by (simp add: FSC_def P1 assms(3) assms(4) assms(6) col_permutation_5 cong_4321)
  have "A P C Cong3 C X A"
    using Cong3_def Cong_perm P3 P4 assms(2) cong_pseudo_reflexivity l4_16 by blast
  then show ?thesis
    by (smt Cong3_def NCol_cases P2 assms(1) assms(2) assms(5) assms(6) colx cong_col_mid l4_13 not_col_distincts not_col_permutation_1 not_cong_1243)
qed

lemma l7_21:
  assumes "\<not> Col A B C" and
    "B \<noteq> D" and
    "Cong A B C D" and
    "Cong B C D A" and
    "Col A P C" and
    "Col B P D"
  shows "P Midpoint A C \<and> P Midpoint B D"
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) col_transitivity_2 is_midpoint_id_2 l7_21_R1 not_col_distincts not_cong_3412)

lemma l7_22_aux_R1:
  assumes "Bet A1 C C" and
    "Bet B1 C B2" and
    "Cong C A1 C B1" and
    "Cong C C C B2" and
    "M1 Midpoint A1 B1" and
    "M2 Midpoint A2 B2"and
    "C A1 Le C C"
  shows "Bet M1 C M2"
  by (metis assms(3) assms(5) assms(7) cong_diff_3 l7_3 le_diff not_bet_distincts)

lemma l7_22_aux_R2:
  assumes "A2 \<noteq> C" and
    "Bet A1 C A2" and
    "Bet B1 C B2" and
    "Cong C A1 C B1" and
    "Cong C A2 C B2" and
    "M1 Midpoint A1 B1" and
    "M2 Midpoint A2 B2" and
    "C A1 Le C A2"
  shows "Bet M1 C M2"
proof -
  obtain X where P1: "C Midpoint A2 X"
    using symmetric_point_construction by blast
  obtain X0 where P2: "C Midpoint B2 X0"
    using symmetric_point_construction by blast
  obtain X1 where P3: "C Midpoint M2 X1"
    using symmetric_point_construction by blast
  have P4: "X1 Midpoint X X0"
    using P1 P2 P3 assms(7) symmetry_preserves_midpoint by blast
  have P5: "C A1 Le C X"
    using Cong_perm Midpoint_def P1 assms(8) cong_reflexivity l5_6 by blast
  have P6: "Bet C A1 X"
    by (smt Midpoint_def P1 P5 assms(1) assms(2) bet2__out between_symmetry is_midpoint_id_2 l5_2 l6_13_1)
  have P7: "C B1 Le C X0"
  proof -
    have Q1: "Cong C A1 C B1"
      by (simp add: assms(4))
    have "Cong C X C X0"
      using P1 P2 assms(5) l7_16 l7_3_2 by blast
    then show ?thesis
      using P5 Q1 l5_6 by blast
  qed
  have P8: "Bet C B1 X0"
    by (smt Midpoint_def P2 P7 assms(1) assms(3) assms(5) bet2__out between_symmetry cong_identity l5_2 l6_13_1)
  obtain Q where P9: "Bet X1 Q C \<and> Bet A1 Q B1"
    by (meson Bet_perm Midpoint_def P4 P6 P8 l3_17)
  have P10: "X A1 C X1 IFSC X0 B1 C X1"
    by (smt Cong_perm IFSC_def Midpoint_def P1 P2 P4 P6 P8 assms(4) assms(5) between_symmetry cong_reflexivity l7_16 l7_3_2)
  have P11: "Cong A1 X1 B1 X1"
    using P10 l4_2 by blast
  have P12: "Cong Q A1 Q B1"
  proof (cases)
    assume "C = X1"
    then show ?thesis
      using P9 assms(4) bet_neq12__neq by blast
  next
    assume Q1: "\<not> C = X1"
    have Q2: "Col C X1 Q"
      using Col_def P9 by blast
    have Q3: "Cong C A1 C B1"
      by (simp add: assms(4))
    have "Cong X1 A1 X1 B1"
      using P11 not_cong_2143 by blast
    then show ?thesis
      using Q1 Q2 Q3 l4_17 by blast
  qed
  have P13: "Q Midpoint A1 B1"
    by (simp add: Midpoint_def P12 P9 cong_left_commutativity)
  then show ?thesis
    using Midpoint_def P3 P9 assms(6) between_inner_transitivity between_symmetry l7_17 by blast
qed

lemma l7_22_aux:
  assumes "Bet A1 C A2" and
    "Bet B1 C B2" and
    "Cong C A1 C B1" and
    "Cong C A2 C B2" and
    "M1 Midpoint A1 B1" and
    "M2 Midpoint A2 B2" and
    "C A1 Le C A2"
  shows "Bet M1 C M2"
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) l7_22_aux_R1 l7_22_aux_R2)

lemma l7_22:
  assumes "Bet A1 C A2" and
    "Bet B1 C B2" and
    "Cong C A1 C B1" and
    "Cong C A2 C B2" and
    "M1 Midpoint A1 B1" and
    "M2 Midpoint A2 B2"
  shows "Bet M1 C M2"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) between_symmetry l7_22_aux local.le_cases)

lemma bet_col1:
  assumes "Bet A B D" and
    "Bet A C D"
  shows "Col A B C"
  using Bet_perm Col_def assms(1) assms(2) l5_3 by blast

lemma l7_25_R1:
  assumes "Cong C A C B" and
    "Col A B C"
  shows "\<exists> X. X Midpoint A B"
  using assms(1) assms(2) l7_20 l7_3_2 not_col_permutation_5 by blast

lemma l7_25_R2:
  assumes "Cong C A C B" and
    "\<not> Col A B C"
  shows "\<exists> X. X Midpoint A B"
proof -
  obtain P where P1: "Bet C A P \<and> A \<noteq> P"
    using point_construction_different by auto
  obtain Q where P2: "Bet C B Q \<and> Cong B Q A P"
    using segment_construction by blast
  obtain R where P3: "Bet A R Q \<and> Bet B R P"
    using P1 P2 between_symmetry inner_pasch by blast
  obtain X where P4: "Bet A X B \<and> Bet R X C"
    using P1 P3 inner_pasch by blast
  have "Cong X A X B"
  proof -
    have Q1: "Cong R A R B \<longrightarrow> Cong X A X B"
    proof (cases)
      assume "R = C"
      then show ?thesis
        using P4 bet_neq12__neq by blast
    next
      assume Q2: "\<not> R = C"
      have "Col R C X"
        using Col_perm P4 bet_col by blast
      then show ?thesis
        using Q2 assms(1) l4_17 by blast
    qed
    have "Cong R A R B"
    proof -
      have Q3: "C A P B OFSC C B Q A"
        by (simp add: OFSC_def P1 P2 assms(1) cong_pseudo_reflexivity cong_symmetry)
      have Q4: "Cong P B Q A"
        using Q3 assms(2) five_segment_with_def not_col_distincts by blast
      obtain R' where Q5: "Bet A R' Q \<and> B R P Cong3 A R' Q"
        using Cong_perm P3 Q4 l4_5 by blast
      have Q6: "B R P A IFSC A R' Q B"
        by (meson Cong3_def IFSC_def OFSC_def P3 Q3 Q5 not_cong_2143)
      have Q7: "B R P Q IFSC A R' Q P"
        using IFSC_def P2 Q6 cong_pseudo_reflexivity by auto
      have Q8: "Cong R A R' B"
        using Q6 l4_2 by auto
      have Q9: "Cong R Q R' P"
        using Q7 l4_2 by auto
      have Q10: "A R Q Cong3 B R' P"
        using Cong3_def Q4 Q8 Q9 cong_commutativity not_cong_4321 by blast
      have Q11: "Col B R' P"
        using P3 Q10 bet_col l4_13 by blast
      have "R = R'"
      proof -
        have R1: "B \<noteq> P"
          using P1 assms(1) between_cong by blast
        then have R2: "A \<noteq> Q"
          using Q4 cong_diff_2 by blast
        have R3: "B \<noteq> Q"
          using P1 P2 cong_diff_3 by blast
        then have R4: "B \<noteq> R"
          by (metis Cong3_def P1 Q11 Q5 assms(2) bet_col cong_diff_3 l6_21 not_col_distincts)
        have R5: "\<not> Col A Q B"
          by (metis P2 R3 assms(2) bet_col col_permutation_3 col_trivial_2 l6_21)
        have R6: "B \<noteq> P"
          by (simp add: R1)
        have R7: "Col A Q R"
          using NCol_cases P3 bet_col by blast
        have R8: "Col A Q R'"
          using Q5 bet_col col_permutation_5 by blast
        have R9: "Col B P R"
          using NCol_cases P3 bet_col by blast
        have  "Col B P R'"
          using Col_perm Q11 by blast
        then show ?thesis
          using R5 R6 R7 R8 R9 l6_21 by blast
      qed
      then show ?thesis
        using Q8 by blast
    qed
    then show ?thesis
      using Q1 by blast
  qed
  then show ?thesis
    using P4 assms(2) bet_col l7_20_bis not_col_distincts by blast
qed

lemma l7_25:
  assumes "Cong C A C B"
  shows "\<exists> X. X Midpoint A B"
  using assms l7_25_R1 l7_25_R2 by blast

lemma midpoint_distinct_1:
  assumes "A \<noteq> B" and
    "I Midpoint A B"
  shows "I \<noteq> A \<and> I \<noteq> B"
  using assms(1) assms(2) is_midpoint_id is_midpoint_id_2 by blast

lemma midpoint_distinct_2:
  assumes "I \<noteq> A" and
    "I Midpoint A B"
  shows "A \<noteq> B \<and> I \<noteq> B"
  using assms(1) assms(2) is_midpoint_id_2 l7_3 by blast

lemma midpoint_distinct_3:
  assumes "I \<noteq> B" and
    "I Midpoint A B"
  shows "A \<noteq> B \<and> I \<noteq> A"
  using assms(1) assms(2) is_midpoint_id l7_3 by blast

lemma midpoint_def:
  assumes "Bet A B C" and
    "Cong A B B C"
  shows "B Midpoint A C"
  using Midpoint_def assms(1) assms(2) by blast

lemma midpoint_bet:
  assumes "B Midpoint A C"
  shows "Bet A B C"
  using Midpoint_def assms by blast

lemma midpoint_col:
  assumes "M Midpoint A B"
  shows "Col M A B"
  using assms bet_col col_permutation_4 midpoint_bet by blast

lemma midpoint_cong:
  assumes "B Midpoint A C"
  shows "Cong A B B C"
  using Midpoint_def assms by blast

lemma midpoint_out:
  assumes "A \<noteq> C" and
    "B Midpoint A C"
  shows "A Out B C"
  using assms(1) assms(2) bet_out midpoint_bet midpoint_distinct_1 by blast

lemma midpoint_out_1:
  assumes "A \<noteq> C" and
    "B Midpoint A C"
  shows "C Out A B"
  by (metis Tarski_neutral_dimensionless.midpoint_bet Tarski_neutral_dimensionless.midpoint_distinct_1 Tarski_neutral_dimensionless_axioms assms(1) assms(2) bet_out_1 l6_6)

lemma midpoint_not_midpoint:
  assumes "A \<noteq> B" and
    "I Midpoint A B"
  shows "\<not> B Midpoint A I"
  using assms(1) assms(2) between_equality_2 midpoint_bet midpoint_distinct_1 by blast

lemma swap_diff:
  assumes "A \<noteq> B"
  shows "B \<noteq> A"
  using assms by auto

lemma cong_cong_half_1:
  assumes "M Midpoint A B" and
    "M' Midpoint A' B'" and
    "Cong A B A' B'"
  shows "Cong A M A' M'"
proof -
  obtain M'' where P1: "Bet A' M'' B' \<and> A M B Cong3 A' M'' B'"
    using assms(1) assms(3) l4_5 midpoint_bet by blast
  have P2: "M'' Midpoint A' B'"
    by (meson Cong3_def P1 assms(1) cong_inner_transitivity midpoint_cong midpoint_def)
  have P3: "M' = M''"
    using P2 assms(2) l7_17 by auto
  then show ?thesis
    using Cong3_def P1 by blast
qed

lemma cong_cong_half_2:
  assumes "M Midpoint A B" and
    "M' Midpoint A' B'" and
    "Cong A B A' B'"
  shows "Cong B M B' M'"
  using assms(1) assms(2) assms(3) cong_cong_half_1 l7_2 not_cong_2143 by blast

lemma cong_mid2__cong:
  assumes "M Midpoint A B" and
    "M' Midpoint A' B'" and
    "Cong A M A' M'"
  shows "Cong A B A' B'"
  by (meson assms(1) assms(2) assms(3) cong_inner_transitivity l2_11_b midpoint_bet midpoint_cong)

lemma mid__lt:
  assumes "A \<noteq> B" and
    "M Midpoint A B"
  shows "A M Lt A B"
  using assms(1) assms(2) bet__lt1213 midpoint_bet midpoint_distinct_1 by blast

lemma le_mid2__le13:
  assumes "M Midpoint A B" and
    "M' Midpoint A' B'" and
    "A M Le A' M'"
  shows "A B Le A' B'"
  by (smt Tarski_neutral_dimensionless.cong_mid2__cong Tarski_neutral_dimensionless.l7_13 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) bet2_le2__le2356 l5_6 l7_3_2 le_anti_symmetry le_comm local.le_cases midpoint_bet)

lemma le_mid2__le12:
  assumes "M Midpoint A B" and
    "M' Midpoint A' B'"
    and "A B Le A' B'"
  shows "A M Le A' M'"
  by (meson assms(1) assms(2) assms(3) cong__le3412 cong_cong_half_1 le_anti_symmetry le_mid2__le13 local.le_cases)

lemma lt_mid2__lt13:
  assumes "M Midpoint A B" and
    "M' Midpoint A' B'" and
    "A M Lt A' M'"
  shows "A B Lt A' B'"
  by (meson Tarski_neutral_dimensionless.le_mid2__le12 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) lt__nle nlt__le)

lemma lt_mid2__lt12:
  assumes "M Midpoint A B" and
    "M' Midpoint A' B'" and
    "A B Lt A' B'"
  shows "A M Lt A' M'"
  by (meson Tarski_neutral_dimensionless.le_mid2__le13 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) le__nlt nle__lt)

lemma midpoint_preserves_out:
  assumes "A Out B C" and
    "M Midpoint A A'" and
    "M Midpoint B B'" and
    "M Midpoint C C'"
  shows "A' Out B' C'"
  by (smt Out_def assms(1) assms(2) assms(3) assms(4) l6_4_2 l7_15 l7_2 not_bet_and_out not_col_distincts)

lemma col_cong_bet:
  assumes "Col A B D" and
    "Cong A B C D" and
    "Bet A C B"
  shows "Bet C A D \<or> Bet C B D"
  by (smt Col_def assms(1) assms(2) assms(3) bet_cong_eq between_inner_transitivity col_transitivity_2 cong_4321 l6_2 not_bet_and_out not_cong_4312 third_point)

lemma col_cong2_bet1:
  assumes "Col A B D" and
    "Bet A C B" and
    "Cong A B C D" and
    "Cong A C B D"
  shows "Bet C B D"
  by (metis assms(1) assms(2) assms(3) assms(4) bet__le1213 bet_cong_eq between_symmetry col_cong_bet cong__le cong_left_commutativity l5_12_b l5_6 outer_transitivity_between2)

lemma col_cong2_bet2:
  assumes "Col A B D" and
    "Bet A C B" and
    "Cong A B C D" and
    "Cong A D B C"
  shows "Bet C A D"
  by (metis assms(1) assms(2) assms(3) assms(4) bet_cong_eq col_cong_bet cong_identity not_bet_distincts not_cong_3421 outer_transitivity_between2)

lemma col_cong2_bet3:
  assumes "Col A B D" and
    "Bet A B C" and
    "Cong A B C D" and
    "Cong A C B D"
  shows "Bet B C D"
  by (metis assms(1) assms(2) assms(3) assms(4) bet__le1213 bet__le2313 bet_col col_transitivity_2 cong_diff_3 cong_reflexivity l5_12_b l5_6 not_bet_distincts)

lemma col_cong2_bet4:
  assumes "Col A B C" and
    "Bet A B D" and
    "Cong A B C D" and
    "Cong A D B C"
  shows "Bet B D C"
  using assms(1) assms(2) assms(3) assms(4) col_cong2_bet3 cong_right_commutativity by blast

lemma col_bet2_cong1:
  assumes "Col A B D" and
    "Bet A C B" and
    "Cong A B C D" and
    "Bet C B D"
  shows "Cong A C D B"
  by (meson assms(2) assms(3) assms(4) between_symmetry cong_pseudo_reflexivity cong_right_commutativity l4_3)

lemma col_bet2_cong2:
  assumes "Col A B D" and
    "Bet A C B" and
    "Cong A B C D" and
    "Bet C A D"
  shows "Cong D A B C"
  by (meson assms(2) assms(3) assms(4) between_symmetry cong_commutativity cong_pseudo_reflexivity cong_symmetry l4_3)

lemma bet2_lt2__lt:
  assumes "Bet a Po b" and
    "Bet A PO B" and
    "Po a Lt PO A" and
    "Po b Lt PO B"
  shows "a b Lt A B"
  by (metis Lt_cases Tarski_neutral_dimensionless.nle__lt Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) bet2_le2__le1245 le__nlt lt__le)

lemma bet2_lt_le__lt:
  assumes "Bet a Po b" and
    "Bet A PO B" and
    "Cong Po a PO A" and
    "Po b Lt PO B"
  shows "a b Lt A B"
  by (smt Lt_def Tarski_neutral_dimensionless.l4_3_1 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) bet2_le2__le cong__le not_cong_2143)

subsection "Orthogonality"

lemma per_dec:
  "Per A B C \<or> \<not> Per A B C"
  by simp

lemma l8_2:
  assumes "Per A B C"
  shows "Per C B A"
proof -
  obtain C' where P1: "B Midpoint C C' \<and> Cong A C A C'"
    using Per_def assms by blast
  obtain A' where P2: "B Midpoint A A'"
    using symmetric_point_construction by blast
  have "Cong C' A C A'"
    using Mid_perm P1 P2 l7_13 by blast
  thus ?thesis
    using P1 P2 Per_def cong_4321 cong_inner_transitivity by blast
qed

lemma Per_cases:
  assumes "Per A B C \<or> Per C B A"
  shows "Per A B C"
  using assms l8_2 by blast

lemma Per_perm :
  assumes "Per A B C"
  shows "Per A B C \<and> Per C B A"
  by (simp add: assms l8_2)

lemma l8_3 :
  assumes "Per A B C" and
    "A \<noteq> B" and
    "Col B A A'"
  shows "Per A' B C"
  by (smt Per_def assms(1) assms(2) assms(3) l4_17 l7_13 l7_2 l7_3_2)

lemma l8_4:
  assumes "Per A B C" and
    "B Midpoint C C'"
  shows "Per A B C'"
  by (metis Tarski_neutral_dimensionless.l8_2 Tarski_neutral_dimensionless_axioms assms(1) assms(2) l8_3 midpoint_col midpoint_distinct_1)

lemma l8_5:
  "Per A B B"
  using Per_def cong_reflexivity l7_3_2 by blast

lemma l8_6:
  assumes "Per A B C" and
    "Per A' B C" and
    "Bet A C A'"
  shows "B = C"
  by (metis Per_def assms(1) assms(2) assms(3) l4_19 midpoint_distinct_3 symmetric_point_uniqueness)

lemma l8_7:
  assumes "Per A B C" and
    "Per A C B"
  shows "B = C"
proof -
  obtain C' where P1: "B Midpoint C C' \<and> Cong A C A C'"
    using Per_def assms(1) by blast
  obtain A' where P2: "C Midpoint A A'"
    using Per_def assms(2) l8_2 by blast
  have "Per C' C A"
    by (metis P1 Tarski_neutral_dimensionless.l8_3 Tarski_neutral_dimensionless_axioms assms(2) bet_col l8_2 midpoint_bet midpoint_distinct_3)
  then have "Cong A C' A' C'"
    using Cong_perm P2 Per_def symmetric_point_uniqueness by blast
  then have "Cong A' C A' C'"
    using P1 P2 cong_inner_transitivity midpoint_cong not_cong_2134 by blast
  then have Q4: "Per A' B C"
    using P1 Per_def by blast
  have "Bet A' C A"
    using Mid_perm P2 midpoint_bet by blast
  thus ?thesis
    using Q4 assms(1) l8_6 by blast
qed

lemma l8_8:
  assumes "Per A B A"
  shows "A = B"
  using Tarski_neutral_dimensionless.l8_6 Tarski_neutral_dimensionless_axioms assms between_trivial2 by fastforce

lemma per_distinct:
  assumes "Per A B C" and
    "A \<noteq> B"
  shows "A \<noteq> C"
  using assms(1) assms(2) l8_8 by blast

lemma per_distinct_1:
  assumes "Per A B C" and
    "B \<noteq> C"
  shows "A \<noteq> C"
  using assms(1) assms(2) l8_8 by blast

lemma l8_9:
  assumes "Per A B C" and
    "Col A B C"
  shows "A = B \<or> C = B"
  using Col_cases assms(1) assms(2) l8_3 l8_8 by blast

lemma l8_10:
  assumes "Per A B C" and
    "A B C Cong3 A' B' C'"
  shows "Per A' B' C'"
proof -
  obtain D where P1: "B Midpoint C D \<and> Cong A C A D"
    using Per_def assms(1) by blast
  obtain D' where P2: "Bet C' B' D' \<and> Cong B' D' B' C'"
    using segment_construction by blast
  have P3: "B' Midpoint C' D'"
    by (simp add: Midpoint_def P2 cong_4312)
  have "Cong A' C' A' D'"
  proof (cases)
    assume "C = B"
    thus ?thesis
      by (metis Cong3_def P3 assms(2) cong_diff_4 cong_reflexivity is_midpoint_id)
  next
    assume Q1: "\<not> C = B"
    have "C B D A OFSC C' B' D' A'"
      by (metis Cong3_def OFSC_def P1 P3 Tarski_neutral_dimensionless.cong_mid2__cong Tarski_neutral_dimensionless_axioms assms(2) cong_commutativity l4_3_1 midpoint_bet)
    thus ?thesis
      by (meson OFSC_def P1 Q1 cong_4321 cong_inner_transitivity five_segment_with_def)
  qed
  thus ?thesis
    using Per_def P3 by blast
qed

lemma col_col_per_per:
  assumes "A \<noteq> X" and
    "C \<noteq> X" and
    "Col U A X" and
    "Col V C X" and
    "Per A X C"
  shows "Per U X V"
  by (meson Tarski_neutral_dimensionless.l8_2 Tarski_neutral_dimensionless.l8_3 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) assms(5) not_col_permutation_3)

lemma perp_in_dec:
  "X PerpAt A B C D \<or> \<not> X PerpAt A B C D"
  by simp

lemma perp_distinct:
  assumes "A B Perp C D"
  shows "A \<noteq> B \<and> C \<noteq> D"
  using PerpAt_def Perp_def assms by auto

lemma l8_12:
  assumes "X PerpAt A B C D"
  shows "X PerpAt C D A B"
  using Per_perm PerpAt_def assms by auto

lemma per_col:
  assumes "B \<noteq> C" and
    "Per A B C" and
    "Col B C D"
  shows "Per A B D"
  by (metis Tarski_neutral_dimensionless.l8_3 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) l8_2)

lemma l8_13_2:
  assumes "A \<noteq> B" and
    "C \<noteq> D" and
    "Col X A B" and
    "Col X C D" and
    "\<exists> U. \<exists> V. Col U A B \<and> Col V C D \<and> U \<noteq> X \<and> V \<noteq> X \<and> Per U X V"
  shows "X PerpAt A B C D"
proof -
  obtain pp :: 'p and ppa :: 'p where
    f1: "Col pp A B \<and> Col ppa C D \<and> pp \<noteq> X \<and> ppa \<noteq> X \<and> Per pp X ppa"
    using assms(5) by blast
  obtain ppb :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p" and ppc :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p" where
    "\<forall>x0 x1 x2 x3 x4. (\<exists>v5 v6. (Col v5 x3 x2 \<and> Col v6 x1 x0) \<and> \<not> Per v5 x4 v6) = ((Col (ppb x0 x1 x2 x3 x4) x3 x2 \<and> Col (ppc x0 x1 x2 x3 x4) x1 x0) \<and> \<not> Per (ppb x0 x1 x2 x3 x4) x4 (ppc x0 x1 x2 x3 x4))"
    by moura
  then have f2: "\<forall>p pa pb pc pd. (\<not> p PerpAt pa pb pc pd \<or> pa \<noteq> pb \<and> pc \<noteq> pd \<and> Col p pa pb \<and> Col p pc pd \<and> (\<forall>pe pf. (\<not> Col pe pa pb \<or> \<not> Col pf pc pd) \<or> Per pe p pf)) \<and> (p PerpAt pa pb pc pd \<or> pa = pb \<or> pc = pd \<or> \<not> Col p pa pb \<or> \<not> Col p pc pd \<or> (Col (ppb pd pc pb pa p) pa pb \<and> Col (ppc pd pc pb pa p) pc pd) \<and> \<not> Per (ppb pd pc pb pa p) p (ppc pd pc pb pa p))"
    using PerpAt_def by fastforce
  { assume "\<not> Col (ppb D C B A X) pp X"
    then have "\<not> Col (ppb D C B A X) A B \<or> \<not> Col (ppc D C B A X) C D \<or> Per (ppb D C B A X) X (ppc D C B A X)"
      using f1 by (meson assms(1) assms(3) col3 not_col_permutation_2) }
  moreover
  { assume "\<not> Col (ppc D C B A X) ppa X"
    then have "\<not> Col (ppb D C B A X) A B \<or> \<not> Col (ppc D C B A X) C D \<or> Per (ppb D C B A X) X (ppc D C B A X)"
      using f1 by (meson assms(2) assms(4) col3 not_col_permutation_2) }
  ultimately have "\<not> Col (ppb D C B A X) A B \<or> \<not> Col (ppc D C B A X) C D \<or> Per (ppb D C B A X) X (ppc D C B A X)"
    using f1 by (meson Tarski_neutral_dimensionless.col_col_per_per Tarski_neutral_dimensionless_axioms)
  then have "(X PerpAt A B C D \<or> A = B \<or> C = D \<or> \<not> Col X A B \<or> \<not> Col X C D \<or> Col (ppb D C B A X) A B \<and> Col (ppc D C B A X) C D \<and> \<not> Per (ppb D C B A X) X (ppc D C B A X)) \<and> (\<not> Col (ppb D C B A X) A B \<or> \<not> Col (ppc D C B A X) C D \<or> Per (ppb D C B A X) X (ppc D C B A X))"
    using f2 by presburger
  thus ?thesis
    using assms(1) assms(2) assms(3) assms(4) by blast
qed

lemma l8_14_1:
  "\<not> A B Perp A B"
  by (metis PerpAt_def Perp_def Tarski_neutral_dimensionless.col_trivial_1 Tarski_neutral_dimensionless.col_trivial_3 Tarski_neutral_dimensionless_axioms l8_8)

lemma l8_14_2_1a:
  assumes "X PerpAt A B C D"
  shows "A B Perp C D"
  using Perp_def assms by blast

lemma perp_in_distinct:
  assumes "X PerpAt A B C D"
  shows "A \<noteq> B \<and> C \<noteq> D"
  using PerpAt_def assms by blast

lemma l8_14_2_1b:
  assumes "X PerpAt A B C D" and
    "Col Y A B" and
    "Col Y C D"
  shows "X = Y"
  by (metis PerpAt_def assms(1) assms(2) assms(3) l8_13_2 l8_14_1 l8_14_2_1a)

lemma l8_14_2_1b_bis:
  assumes "A B Perp C D" and
    "Col X A B" and
    "Col X C D"
  shows "X PerpAt A B C D"
  using Perp_def assms(1) assms(2) assms(3) l8_14_2_1b by blast

lemma l8_14_2_2:
  assumes "A B Perp C D" and
    "\<forall> Y. (Col Y A B \<and> Col Y C D) \<longrightarrow> X = Y"
  shows "X PerpAt A B C D"
  by (metis Tarski_neutral_dimensionless.PerpAt_def Tarski_neutral_dimensionless.Perp_def Tarski_neutral_dimensionless_axioms assms(1) assms(2))

lemma l8_14_3:
  assumes "X PerpAt A B C D" and
    "Y PerpAt A B C D"
  shows "X = Y"
  by (meson PerpAt_def assms(1) assms(2) l8_14_2_1b)

lemma l8_15_1:
  assumes "Col A B X" and
    "A B Perp C X"
  shows "X PerpAt A B C X"
  using NCol_perm assms(1) assms(2) col_trivial_3 l8_14_2_1b_bis by blast

lemma l8_15_2:
  assumes "Col A B X" and
    "X PerpAt A B C X"
  shows "A B Perp C X"
  using assms(2) l8_14_2_1a by blast

lemma perp_in_per:
  assumes "B PerpAt A B B C"
  shows "Per A B C"
  by (meson NCol_cases PerpAt_def assms col_trivial_3)

lemma perp_sym:
  assumes "A B Perp A B"
  shows "C D Perp C D"
  using assms l8_14_1 by auto

lemma perp_col0:
  assumes "A B Perp C D" and
    "X \<noteq> Y" and
    "Col A B X" and
    "Col A B Y"
  shows "C D Perp X Y"
proof -
  obtain X0 where P1: "X0 PerpAt A B C D"
    using Perp_def assms(1) by blast
  then have P2: " A \<noteq> B \<and> C \<noteq> D \<and> Col X0 A B \<and> Col X0 C D \<and>
  ((Col U A B \<and> Col V C D) \<longrightarrow> Per U X0 V)" using PerpAt_def by blast
  have Q1: "C \<noteq> D" using P2 by blast
  have Q2: "X \<noteq> Y" using assms(2) by blast
  have Q3: "Col X0 C D" using P2 by blast
  have Q4: "Col X0 X Y"
  proof -
    have "\<exists>p pa. Col p pa Y \<and> Col p pa X \<and> Col p pa X0 \<and> p \<noteq> pa"
      by (metis (no_types) Col_cases P2 assms(3) assms(4))
    thus ?thesis
      using col3 by blast
  qed
  have "X0 PerpAt C D X Y"
  proof -
    have "\<forall> U V. (Col U C D \<and> Col V X Y) \<longrightarrow> Per U X0 V"
      by (metis Col_perm P1 Per_perm Q2 Tarski_neutral_dimensionless.PerpAt_def Tarski_neutral_dimensionless_axioms assms(3) assms(4) colx)
    thus ?thesis using Q1 Q2 Q3 Q4 PerpAt_def by blast
  qed
  thus ?thesis
    using Perp_def by auto
qed

lemma per_perp_in:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per A B C"
  shows "B PerpAt A B B C"
  by (metis Col_def assms(1) assms(2) assms(3) between_trivial2 l8_13_2)

lemma per_perp:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per A B C"
  shows "A B Perp B C"
  using Perp_def assms(1) assms(2) assms(3) per_perp_in by blast

lemma perp_left_comm:
  assumes "A B Perp C D"
  shows "B A Perp C D"
proof -
  obtain X where "X PerpAt A B C D"
    using Perp_def assms by blast
  then have "X PerpAt B A C D"
    using PerpAt_def col_permutation_5 by auto
  thus ?thesis
    using Perp_def by blast
qed

lemma perp_right_comm:
  assumes "A B Perp C D"
  shows "A B Perp D C"
  by (meson Perp_def assms l8_12 perp_left_comm)

lemma perp_comm:
  assumes "A B Perp C D"
  shows "B A Perp D C"
  by (simp add: assms perp_left_comm perp_right_comm)

lemma perp_in_sym:
  assumes  "X PerpAt A B C D"
  shows "X PerpAt C D A B"
  by (simp add: assms l8_12)

lemma perp_in_left_comm:
  assumes "X PerpAt A B C D"
  shows "X PerpAt B A C D"
  by (metis Col_cases PerpAt_def assms)

lemma perp_in_right_comm:
  assumes "X PerpAt A B C D"
  shows "X PerpAt A B D C"
  using assms perp_in_left_comm perp_in_sym by blast

lemma perp_in_comm:
  assumes "X PerpAt A B C D"
  shows "X PerpAt B A D C"
  by (simp add: assms perp_in_left_comm perp_in_right_comm)

lemma Perp_cases:
  assumes "A B Perp C D \<or> B A Perp C D \<or> A B Perp D C \<or> B A Perp D C \<or> C D Perp A B \<or> C D Perp B A \<or> D C Perp A B \<or> D C Perp B A"
  shows "A B Perp C D"
  by (meson Perp_def assms perp_in_sym perp_left_comm)

lemma Perp_perm :
  assumes "A B Perp C D"
  shows "A B Perp C D \<and> B A Perp C D \<and> A B Perp D C \<and> B A Perp D C \<and> C D Perp A B \<and> C D Perp B A \<and> D C Perp A B \<and> D C Perp B A"
  by (meson Perp_def assms perp_in_sym perp_left_comm)

lemma Perp_in_cases:
  assumes "X PerpAt A B C D \<or> X PerpAt B A C D \<or> X PerpAt A B D C \<or> X PerpAt B A D C \<or> X PerpAt C D A B \<or> X PerpAt C D B A \<or> X PerpAt D C A B \<or> X PerpAt D C B A"
  shows "X PerpAt A B C D"
  using assms perp_in_left_comm perp_in_sym by blast

lemma Perp_in_perm:
  assumes "X PerpAt A B C D"
  shows "X PerpAt A B C D \<and> X PerpAt B A C D \<and> X PerpAt A B D C \<and> X PerpAt B A D C \<and> X PerpAt C D A B \<and> X PerpAt C D B A \<and> X PerpAt D C A B \<and> X PerpAt D C B A"
  using Perp_in_cases assms by blast

lemma perp_in_col:
  assumes "X PerpAt A B C D"
  shows "Col A B X \<and> Col C D X"
  using PerpAt_def assms col_permutation_2 by presburger

lemma perp_perp_in:
  assumes "A B Perp C A"
  shows "A PerpAt A B C A"
  using assms l8_15_1 not_col_distincts by blast

lemma perp_per_1:
  assumes "A B Perp C A"
  shows "Per B A C"
  using Perp_in_cases assms perp_in_per perp_perp_in by blast

lemma perp_per_2:
  assumes "A B Perp A C"
  shows "Per B A C"
  by (simp add: Perp_perm assms perp_per_1)

lemma perp_col:
  assumes "A \<noteq> E" and
    "A B Perp C D" and
    "Col A B E"
  shows "A E Perp C D"
  using Perp_perm assms(1) assms(2) assms(3) col_trivial_3 perp_col0 by blast

lemma perp_col2:
  assumes "A B Perp X Y" and
    "C \<noteq> D" and
    "Col A B C" and
    "Col A B D"
  shows "C D Perp X Y"
  using Perp_perm assms(1) assms(2) assms(3) assms(4) perp_col0 by blast

lemma perp_col4:
  assumes "P \<noteq> Q" and
    "R \<noteq> S" and
    "Col A B P" and
    "Col A B Q" and
    "Col C D R" and
    "Col C D S" and
    "A B Perp C D"
  shows "P Q Perp R S"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) perp_col0 by blast

lemma perp_not_eq_1:
  assumes "A B Perp C D"
  shows "A \<noteq> B"
  using assms perp_distinct by auto

lemma perp_not_eq_2:
  assumes "A B Perp C D"
  shows "C \<noteq> D"
  using assms perp_distinct by auto

lemma diff_per_diff:
  assumes "A \<noteq> B" and
    "Cong A P B R" and
    "Per B A P"
    and "Per A B R"
  shows "P \<noteq> R"
  using assms(1) assms(3) assms(4) l8_2 l8_7 by blast

lemma per_not_colp:
  assumes "A \<noteq> B" and
    "A \<noteq> P" and
    "B \<noteq> R" and
    "Per B A P"
    and "Per A B R"
  shows "\<not> Col P A R"
  by (metis Per_cases Tarski_neutral_dimensionless.col_permutation_4 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(4) assms(5) l8_3 l8_7)

lemma per_not_col:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per A B C"
  shows "\<not> Col A B C"
  using assms(1) assms(2) assms(3) l8_9 by auto

lemma perp_not_col2:
  assumes "A B Perp C D"
  shows "\<not> Col A B C \<or> \<not> Col A B D"
  using assms l8_14_1 perp_col2 perp_distinct by blast

lemma perp_not_col:
  assumes "A B Perp P A"
  shows "\<not> Col A B P"
proof -
  have "A PerpAt A B P A"
    using assms perp_perp_in by auto
  then have "Per P A B"
    by (simp add: perp_in_per perp_in_sym)
  then have "\<not> Col B A P"
    by (metis NCol_perm Tarski_neutral_dimensionless.perp_not_eq_1 Tarski_neutral_dimensionless.perp_not_eq_2 Tarski_neutral_dimensionless_axioms assms per_not_col)
  thus ?thesis
    using Col_perm by blast
qed

lemma perp_in_col_perp_in:
  assumes "C \<noteq> E" and
    "Col C D E" and
    "P PerpAt A B C D"
  shows  "P PerpAt A B C E"
proof -
  have P2: "C \<noteq> D"
    using assms(3) perp_in_distinct by blast
  have P3: "Col P A B"
    using PerpAt_def assms(3) by auto
  have "Col P C D"
    using PerpAt_def assms(3) by blast
  then have "Col P C E"
    using P2 assms(2) col_trivial_2 colx by blast
  thus ?thesis
    by (smt P3 Perp_perm Tarski_neutral_dimensionless.l8_14_2_1b_bis Tarski_neutral_dimensionless.perp_col Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) l8_14_2_1a)
qed

lemma perp_col2_bis:
  assumes "A B Perp C D" and
    "Col C D P" and
    "Col C D Q" and
    "P \<noteq> Q"
  shows "A B Perp P Q"
  using Perp_cases assms(1) assms(2) assms(3) assms(4) perp_col0 by blast

lemma perp_in_perp_bis_R1:
  assumes "X \<noteq> A" and
    "X PerpAt A B C D"
  shows "X B Perp C D \<or> A X Perp C D"
  by (metis assms(2) l8_14_2_1a perp_col perp_in_col)

lemma perp_in_perp_bis:
  assumes "X PerpAt A B C D"
  shows "X B Perp C D \<or> A X Perp C D"
  by (metis assms l8_14_2_1a perp_in_perp_bis_R1)

lemma col_per_perp:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    (*   "D \<noteq> B" and  *)
    "D \<noteq> C" and
    "Col B C D" and
    "Per A B C"
  shows "C D Perp A B"
  by (metis Perp_cases assms(1) assms(2) assms(3) assms(4) assms(5) col_trivial_2 per_perp perp_col2_bis)

lemma per_cong_mid_R1:
  assumes "B = H" and
    (*  "B \<noteq> C" and *)
    "Bet A B C" and
    "Cong A H C H" and
    "Per H B C"
  shows "B Midpoint A C"
  using assms(1) assms(2) assms(3) midpoint_def not_cong_1243 by blast

lemma per_cong_mid_R2:
  assumes (*"B \<noteq> H" and *)
    "B \<noteq> C" and
    "Bet A B C" and
    "Cong A H C H" and
    "Per H B C"
  shows "B Midpoint A C"
proof -
  have P1: "Per C B H"
    using Per_cases assms(4) by blast
  have P2: "Per H B A"
    using assms(1) assms(2) assms(4) bet_col col_permutation_1 per_col by blast
  then have P3: "Per A B H"
    using Per_cases by blast
  obtain C' where P4: "B Midpoint C C' \<and> Cong H C H C'"
    using Per_def assms(4) by blast
  obtain H' where P5: "B Midpoint H H' \<and> Cong C H C H'"
    using P1 Per_def by blast
  obtain A' where P6: "B Midpoint A A' \<and> Cong H A H A'"
    using P2 Per_def by blast
  obtain H'' where P7: "B Midpoint H H'' \<and> Cong A H A H'"
    using P3 P5 Tarski_neutral_dimensionless.Per_def Tarski_neutral_dimensionless_axioms symmetric_point_uniqueness by fastforce
  then have P8: "H' = H''"
    using P5 symmetric_point_uniqueness by blast
  have "H B H' A IFSC H B H' C"
  proof -
    have Q1: "Bet H B H'"
      by (simp add: P7 P8 midpoint_bet)
    have Q2: "Cong H H' H H'"
      by (simp add: cong_reflexivity)
    have Q3: "Cong B H' B H'"
      by (simp add: cong_reflexivity)
    have Q4: "Cong H A H C"
      using assms(3) not_cong_2143 by blast
    have "Cong H' A H' C"
      using P5 P7 assms(3) cong_commutativity cong_inner_transitivity by blast
    thus ?thesis
      by (simp add: IFSC_def Q1 Q2 Q3 Q4)
  qed
  thus ?thesis
    using assms(1) assms(2) bet_col bet_neq23__neq l4_2 l7_20_bis by auto
qed

lemma per_cong_mid:
  assumes "B \<noteq> C" and
    "Bet A B C" and
    "Cong A H C H" and
    "Per H B C"
  shows "B Midpoint A C"
  using assms(1) assms(2) assms(3) assms(4) per_cong_mid_R1 per_cong_mid_R2 by blast

lemma per_double_cong:
  assumes "Per A B C" and
    "B Midpoint C C'"
  shows "Cong A C A C'"
  using Mid_cases Per_def assms(1) assms(2) l7_9_bis by blast

lemma cong_perp_or_mid_R1:
  assumes "Col A B X" and
    "A \<noteq> B" and
    "M Midpoint A B" and
    "Cong A X B X"
  shows "X = M \<or> \<not> Col A B X \<and> M PerpAt X M A B"
  using assms(1) assms(2) assms(3) assms(4) col_permutation_5 cong_commutativity l7_17_bis l7_2 l7_20 by blast

lemma cong_perp_or_mid_R2:
  assumes "\<not> Col A B X" and
    "A \<noteq> B" and
    "M Midpoint A B" and
    "Cong A X B X"
  shows "X = M \<or> \<not> Col A B X \<and> M PerpAt X M A B"
proof -
  have P1: "Col M A B"
    by (simp add: assms(3) midpoint_col)
  have "Per X M A"
    using Per_def assms(3) assms(4) cong_commutativity by blast
  thus ?thesis
    by (metis P1 assms(1) assms(2) assms(3) midpoint_distinct_1 not_col_permutation_4 per_perp_in perp_in_col_perp_in perp_in_right_comm)
qed

lemma cong_perp_or_mid:
  assumes "A \<noteq> B" and
    "M Midpoint A B" and
    "Cong A X B X"
  shows "X = M \<or> \<not> Col A B X \<and> M PerpAt X M A B"
  using assms(1) assms(2) assms(3) cong_perp_or_mid_R1 cong_perp_or_mid_R2 by blast

lemma col_per2_cases:
  assumes "B \<noteq> C" and
    "B' \<noteq> C" and
    "C \<noteq> D" and
    "Col B C D" and
    "Per A B C" and
    "Per A B' C"
  shows  "B = B' \<or> \<not> Col B' C D"
  by (meson Tarski_neutral_dimensionless.l8_7 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l6_16_1 per_col)

lemma l8_16_1:
  assumes "Col A B X" and
    "Col A B U" and
    "A B Perp C X"
  shows "\<not> Col A B C \<and> Per C X U"
  by (metis assms(1) assms(2) assms(3) l8_5 perp_col0 perp_left_comm perp_not_col2 perp_per_2)

lemma l8_16_2:
  assumes "Col A B X" and
    "Col A B U"
    and "U \<noteq> X" and
    "\<not> Col A B C" and
    "Per C X U"
  shows "A B Perp C X"
proof -
  obtain X where "X PerpAt A B C X"
    by (metis (no_types) NCol_perm assms(1) assms(2) assms(3) assms(4) assms(5) l8_13_2 l8_2 not_col_distincts)
  thus ?thesis
    by (smt Perp_perm assms(1) assms(2) assms(3) assms(4) assms(5) col3 col_per_perp not_col_distincts per_col per_perp)
qed

lemma l8_18_uniqueness:
  assumes (*"\<not> Col A B C" and *)
    "Col A B X" and
    "A B Perp C X" and
    "Col A B Y" and
    "A B Perp C Y"
  shows "X = Y"
  using assms(1) assms(2) assms(3) assms(4) l8_16_1 l8_7 by blast

lemma midpoint_distinct:
  assumes "\<not> Col A B C" and
    "Col A B X" and
    "X Midpoint C C'"
  shows "C \<noteq> C'"
  using assms(1) assms(2) assms(3) l7_3 by auto

lemma l8_20_1_R1:
  assumes "A = B"
  shows "Per B A P"
  by (simp add: assms l8_2 l8_5)

lemma l8_20_1_R2:
  assumes "A \<noteq> B" and
    "Per A B C" and
    "P Midpoint C' D" and
    "A Midpoint C' C" and
    "B Midpoint D C"
  shows "Per B A P"
proof -
  obtain B' where P1: "A Midpoint B B'"
    using symmetric_point_construction by blast
  obtain D' where P2: "A Midpoint D D'"
    using symmetric_point_construction by blast
  obtain P' where P3: "A Midpoint P P'"
    using symmetric_point_construction by blast
  have P4: "Per B' B C"
    by (metis P1 Tarski_neutral_dimensionless.Per_cases Tarski_neutral_dimensionless.per_col Tarski_neutral_dimensionless_axioms assms(1) assms(2) midpoint_col not_col_permutation_4)
  have P5: "Per B B' C'"
  proof -
    have "Per B' B C"
      by (simp add: P4)
    have "B' B C Cong3 B B' C'"
      by (meson Cong3_def P1 assms(4) l7_13 l7_2)
    thus ?thesis
      using P4 l8_10 by blast
  qed
  have P6: "B' Midpoint D' C'"
    by (meson P1 P2 assms(4) assms(5) l7_15 l7_16 l7_2 midpoint_bet midpoint_cong midpoint_def)
  have P7: "P' Midpoint C D'"
    using P2 P3 assms(3) assms(4) symmetry_preserves_midpoint by blast
  have P8: "A Midpoint P P'"
    by (simp add: P3)
  obtain D'' where P9: "B Midpoint C D'' \<and> Cong B' C B' D"
    using P4 assms(5) l7_2 per_double_cong by blast
  have P10: "D'' = D"
    using P9 assms(5) l7_9_bis by blast
  obtain D'' where P11: "B' Midpoint C' D'' \<and> Cong B C' B D''"
    using P5 Per_def by blast
  have P12: "D' = D''"
    by (meson P11 P6 Tarski_neutral_dimensionless.l7_9_bis Tarski_neutral_dimensionless_axioms)
  have P13: "P Midpoint C' D"
    using assms(3) by blast
  have P14: "Cong C D C' D'"
    using P2 assms(4) l7_13 l7_2 by blast
  have P15: "Cong C' D C D'"
    using P2 assms(4) cong_4321 l7_13 by blast
  have P16: "Cong P D P' D'"
    using P2 P8 cong_symmetry l7_13 by blast
  have P17: "Cong P D P' C"
    using P16 P7 cong_3421 cong_transitivity midpoint_cong by blast
  have P18: "C' P D B IFSC D' P' C B"
    by (metis Bet_cases IFSC_def P10 P11 P12 P13 P15 P17 P7 P9 cong_commutativity cong_right_commutativity l7_13 l7_3_2 midpoint_bet)
  then have "Cong B P B P'"
    using Tarski_neutral_dimensionless.l4_2 Tarski_neutral_dimensionless_axioms not_cong_2143 by fastforce
  thus ?thesis
    using P8 Per_def by blast
qed

lemma l8_20_1:
  assumes "Per A B C" and
    "P Midpoint C' D" and
    "A Midpoint C' C" and
    "B Midpoint D C"
  shows "Per B A P"
  using assms(1) assms(2) assms(3) assms(4) l8_20_1_R1 l8_20_1_R2 by fastforce

lemma l8_20_2:
  assumes "P Midpoint C' D" and
    "A Midpoint C' C" and
    "B Midpoint D C" and
    "B \<noteq> C"
  shows "A \<noteq> P"
  using assms(1) assms(2) assms(3) assms(4) l7_3 symmetric_point_uniqueness by blast

lemma perp_col1:
  assumes "C \<noteq> X" and
    "A B Perp C D" and
    "Col C D X"
  shows "A B Perp C X"
  using assms(1) assms(2) assms(3) col_trivial_3 perp_col2_bis by blast

lemma l8_18_existence:
  assumes "\<not> Col A B C"
  shows "\<exists> X. Col A B X \<and> A B Perp C X"
proof -
  obtain Y where P1: "Bet B A Y \<and> Cong A Y A C"
    using segment_construction by blast
  then obtain P where P2: "P Midpoint C Y"
    using Mid_cases l7_25 by blast
  then have P3: "Per A P Y"
    using P1 Per_def l7_2 by blast
  obtain Z where P3: "Bet A Y Z \<and> Cong Y Z Y P"
    using segment_construction by blast
  obtain Q where P4: "Bet P Y Q \<and> Cong Y Q Y A"
    using segment_construction by blast
  obtain Q' where P5: "Bet Q Z Q' \<and> Cong Z Q' Q Z"
    using segment_construction by blast
  then have P6: "Z Midpoint Q Q'"
    using midpoint_def not_cong_3412 by blast
  obtain C' where P7: "Bet Q' Y C' \<and> Cong Y C' Y C"
    using segment_construction by blast
  obtain X where P8: "X Midpoint C C'"
    using Mid_cases P7 l7_25 by blast
  have P9: "A Y Z Q OFSC Q Y P A"
    by (simp add: OFSC_def P3 P4 between_symmetry cong_4321 cong_pseudo_reflexivity)
  have P10: "A \<noteq> Y"
    using P1 assms cong_reverse_identity not_col_distincts by blast
  then have P11: "Cong Z Q P A"
    using P9 five_segment_with_def by blast
  then have P12: "A P Y Cong3 Q Z Y"
    using Cong3_def P3 P4 not_cong_4321 by blast
  have P13: "Per Q Z Y"
    using Cong_perm P1 P12 P2 Per_def l8_10 l8_4 by blast
  then have P14: "Per Y Z Q"
    by (simp add: l8_2)
  have P15: "P \<noteq> Y"
    using NCol_cases P1 P2 assms bet_col l7_3_2 l7_9_bis by blast
  obtain Q'' where P16:"Z Midpoint Q Q'' \<and> Cong Y Q Y Q'"
    using P14 P6 per_double_cong by blast
  then have P17: "Q' = Q''"
    using P6 symmetric_point_uniqueness by blast
  have P18: "Bet Z Y X"
  proof -
    have "Bet Q Y C"
      using P15 P2 P4 between_symmetry midpoint_bet outer_transitivity_between2 by blast
    thus ?thesis
      using P16 P6 P7 P8 l7_22 not_cong_3412 by blast
  qed
  have P19: "Q \<noteq> Y"
    using P10 P4 cong_reverse_identity by blast
  have P20: "Per Y X C"
  proof -
    have "Bet C P Y"
      by (simp add: P2 midpoint_bet)
    thus ?thesis
      using P7 P8 Per_def not_cong_3412 by blast
  qed
  have P21: "Col P Y Q"
    by (simp add: Col_def P4)
  have P22: "Col P Y C"
    using P2 midpoint_col not_col_permutation_5 by blast
  have P23: "Col P Q C"
    using P15 P21 P22 col_transitivity_1 by blast
  have P24: "Col Y Q C"
    using P15 P21 P22 col_transitivity_2 by auto
  have P25: "Col A Y B"
    by (simp add: Col_def P1)
  have P26: "Col A Y Z"
    using P3 bet_col by blast
  have P27: "Col A B Z"
    using P10 P25 P26 col_transitivity_1 by blast
  have P28: "Col Y B Z"
    using P10 P25 P26 col_transitivity_2 by blast
  have P29: "Col Q Y P"
    using P21 not_col_permutation_3 by blast
  have P30: "Q \<noteq> C"
    using P15 P2 P4 between_equality_2 between_symmetry midpoint_bet by blast
  have P31: "Col Y B Z"
    using P28 by auto
  have P32: "Col Y Q' C'"
    by (simp add: P7 bet_col col_permutation_4)
  have P33: "Q \<noteq> Q'"
    using P11 P15 P22 P25 P5 assms bet_neq12__neq col_transitivity_1 cong_reverse_identity by blast
  have P34: "C \<noteq> C'"
    by (smt P15 P18 P3 P31 P8 assms bet_col col3 col_permutation_2 col_permutation_3 cong_3421 cong_diff midpoint_distinct_3)
  have P35: "Q Y C Z OFSC Q' Y C' Z"
    by (meson OFSC_def P15 P16 P2 P4 P5 P7 between_symmetry cong_3421 cong_reflexivity midpoint_bet not_cong_3412 outer_transitivity_between2)
  then have P36: "Cong C Z C' Z"
    using P19 five_segment_with_def by blast
  have P37: "Col Z Y X"
    by (simp add: P18 bet_col)
  have P38: "Y \<noteq> Z"
    using P15 P3 cong_reverse_identity by blast
  then have P40: "X \<noteq> Y"
    by (metis (mono_tags, hide_lams) Col_perm Cong_perm P14 P24 P25 P27 P36 P8 Per_def assms colx per_not_colp)
  have "Col A B X"
    using Col_perm P26 P31 P37 P38 col3 by blast
  thus ?thesis
    by (metis P18 P20 P27 P37 P40 Tarski_neutral_dimensionless.per_col Tarski_neutral_dimensionless_axioms assms between_equality col_permutation_3 l5_2 l8_16_2 l8_2)
qed

lemma l8_21_aux:
  assumes "\<not> Col A B C"
  shows "\<exists> P. \<exists> T. (A B Perp P A \<and> Col A B T \<and> Bet C T P)"
proof -
  obtain X where P1: "Col A B X \<and> A B Perp C X"
    using assms l8_18_existence by blast
  have P2: "X PerpAt A B C X"
    by (simp add: P1 l8_15_1)
  have P3: "Per A X C"
    by (meson P1 Per_perm Tarski_neutral_dimensionless.l8_16_1 Tarski_neutral_dimensionless_axioms col_trivial_3)
  obtain C' where P4: "X Midpoint C C' \<and> Cong A C A C'"
    using P3 Per_def by blast
  obtain C'' where P5: "A Midpoint C C''"
    using symmetric_point_construction by blast
  obtain P where P6: "P Midpoint C' C''"
    by (metis Cong_perm P4 P5 Tarski_neutral_dimensionless.Midpoint_def Tarski_neutral_dimensionless_axioms cong_inner_transitivity l7_25)
  have P7: "Per X A P"
    by (smt P3 P4 P5 P6 l7_2 l8_20_1_R2 l8_4 midpoint_distinct_3 symmetric_point_uniqueness)
  have P8: "X \<noteq> C"
    using P1 assms by auto
  have P9: "A \<noteq> P"
    using P4 P5 P6 P8 l7_9 midpoint_distinct_2 by blast
  obtain T where P10: "Bet P T C \<and> Bet A T X"
    by (meson Mid_perm Midpoint_def P4 P5 P6 l3_17)
  have "A B Perp P A \<and> Col A B T \<and> Bet C T P"
  proof cases
    assume "A = X"
    thus ?thesis
      by (metis Bet_perm Col_def P1 P10 P9 between_identity col_trivial_3 perp_col2_bis)
  next
    assume "A \<noteq> X"
    thus ?thesis
      by (metis Bet_perm Col_def P1 P10 P7 P9 Perp_perm col_transitivity_2 col_trivial_1 l8_3 per_perp perp_not_col2)
  qed
  thus ?thesis
    by blast
qed

lemma l8_21:
  assumes "A \<noteq> B"
  shows "\<exists> P T. A B Perp P A \<and> Col A B T \<and> Bet C T P"
  by (meson assms between_trivial2 l8_21_aux not_col_exists)

lemma per_cong:
  assumes "A \<noteq> B" and
    "A \<noteq> P" and
    "Per B A P" and
    "Per A B R" and
    "Cong A P B R" and
    "Col A B X" and
    "Bet P X R"
  shows "Cong A R P B"
proof -
  have P1: "Per P A B"
    using Per_cases assms(3) by blast
  obtain Q where P2: "R Midpoint B Q"
    using symmetric_point_construction by auto
  have P3: "B \<noteq> R"
    using assms(2) assms(5) cong_identity by blast
  have P4: "Per A B Q"
    by (metis P2 P3 assms(1) assms(4) bet_neq23__neq col_permutation_4 midpoint_bet midpoint_col per_perp_in perp_in_col_perp_in perp_in_per)
  have P5: "Per P A X"
    using P1 assms(1) assms(6) per_col by blast
  have P6: "B \<noteq> Q"
    using P2 P3 l7_3 by blast
  have P7: "Per R B X"
    by (metis assms(1) assms(4) assms(6) l8_2 not_col_permutation_4 per_col)
  have P8: "X \<noteq> A"
    using P3 assms(1) assms(2) assms(3) assms(4) assms(7) bet_col per_not_colp by blast
  obtain P' where P9: "A Midpoint P P'"
    using Per_def assms(3) by blast
  obtain R' where P10: "Bet P' X R' \<and> Cong X R' X R"
    using segment_construction by blast
  obtain M where P11: "M Midpoint R R'"
    by (meson P10 Tarski_neutral_dimensionless.l7_2 Tarski_neutral_dimensionless_axioms l7_25)
  have P12: "Per X M R"
    using P10 P11 Per_def cong_symmetry by blast
  have P13: "Cong X P X P'"
    using P9 assms(1) assms(3) assms(6) cong_left_commutativity l4_17 midpoint_cong per_double_cong by blast
  have P14: "X \<noteq> P'"
    using P13 P8 P9 cong_identity l7_3 by blast
  have P15: "P \<noteq> P'"
    using P9 assms(2) midpoint_distinct_2 by blast
  have P16: "\<not> Col X P P'"
    using P13 P15 P8 P9 l7_17 l7_20 not_col_permutation_4 by blast
  have P17: "Bet A X M"
    using P10 P11 P13 P9 assms(7) cong_symmetry l7_22 by blast
  have P18: "X \<noteq> R"
    using P3 P7 per_distinct_1 by blast
  have P19: "X \<noteq> R'"
    using P10 P18 cong_diff_3 by blast
  have P20: "X \<noteq> M"
    by (metis Col_def P10 P11 P16 P18 P19 assms(7) col_transitivity_1 midpoint_col)
  have P21: "M = B"
    by (smt Col_def P12 P17 P20 P8 Per_perm assms(1) assms(4) assms(6) col_transitivity_2 l8_3 l8_7)
  have "P X R P' OFSC P' X R' P"
    by (simp add: OFSC_def P10 P13 assms(7) cong_commutativity cong_pseudo_reflexivity cong_symmetry)
  then have "Cong R P' R' P"
    using P13 P14 cong_diff_3 five_segment_with_def by blast
  then have "P' A P R IFSC R' B R P"
    by (metis Bet_perm Cong_perm Midpoint_def P11 P21 P9 Tarski_neutral_dimensionless.IFSC_def Tarski_neutral_dimensionless_axioms assms(5) cong_mid2__cong cong_pseudo_reflexivity)
  thus ?thesis
    using l4_2 not_cong_1243 by blast
qed

lemma perp_cong:
  assumes "A \<noteq> B" and
    "A \<noteq> P" and
    "A B Perp P A" and
    "A B Perp R B" and
    "Cong A P B R" and
    "Col A B X" and
    "Bet P X R"
  shows "Cong A R P B"
  using Perp_cases assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) per_cong perp_per_1 by blast

lemma perp_exists:
  assumes "A \<noteq> B"
  shows "\<exists> X. PO X Perp A B"
proof cases
  assume "Col A B PO"
  then obtain C where P1: "A \<noteq> C \<and> B \<noteq> C \<and> PO \<noteq> C \<and> Col A B C"
    using diff_col_ex3 by blast
  then obtain P T where P2: "PO C Perp P PO \<and> Col PO C T \<and> Bet PO T P" using l8_21
    by blast
  then have "PO P Perp A B"
    by (metis P1 Perp_perm \<open>Col A B PO\<close> assms col3 col_trivial_2 col_trivial_3 perp_col2)
  thus ?thesis
    by blast
next
  assume "\<not> Col A B PO"
  thus ?thesis using l8_18_existence
    using assms col_trivial_2 col_trivial_3 l8_18_existence perp_col0 by blast
qed

lemma perp_vector:
  assumes "A \<noteq> B"
  shows "\<exists> X Y. A B Perp X Y"
  using assms l8_21 by blast

lemma midpoint_existence_aux:
  assumes "A \<noteq> B" and
    "A B Perp Q B" and
    "A B Perp P A" and
    "Col A B T" and
    "Bet Q T P" and
    "A P Le B Q"
  shows "\<exists> X. X Midpoint A B"
proof -
  obtain R where P1: "Bet B R Q \<and> Cong A P B R"
    using Le_def assms(6) by blast
  obtain X where P2: "Bet T X B \<and> Bet R X P"
    using P1 assms(5) between_symmetry inner_pasch by blast
  have P3: "Col A B X"
    by (metis Col_def Out_cases P2 assms(4) between_equality l6_16_1 not_out_bet out_diff1)
  have P4: "B \<noteq> R"
    using P1 assms(3) cong_identity perp_not_eq_2 by blast
  have P5: "\<not> Col A B Q"
    using assms(2) col_trivial_2 l8_16_1 by blast
  have P6: "\<not> Col A B R"
    using Col_def P1 P4 P5 l6_16_1 by blast
  have P7: "P \<noteq> R"
    using P2 P3 P6 between_identity by blast
  have "\<exists> X. X Midpoint A B"
  proof cases
    assume "A = P"
    thus ?thesis
      using assms(3) col_trivial_3 perp_not_col2 by blast
  next
    assume Q1: "\<not> A = P"
    have Q2: "A B Perp R B"
      by (metis P1 P4 Perp_perm Tarski_neutral_dimensionless.bet_col1 Tarski_neutral_dimensionless_axioms assms(2) l5_1 perp_col1)
    then have Q3: "Cong A R P B"
      using P1 P2 P3 Q1 assms(1) assms(3) between_symmetry perp_cong by blast
    then have "X Midpoint A B \<and> X Midpoint P R"
      by (smt P1 P2 P3 P6 P7 bet_col cong_left_commutativity cong_symmetry l7_2 l7_21 not_col_permutation_1)
    thus ?thesis
      by blast
  qed
  thus ?thesis by blast
qed

lemma midpoint_existence:
  "\<exists> X. X Midpoint A B"
proof cases
  assume "A = B"
  thus ?thesis
    using l7_3_2 by blast
next
  assume P1: "\<not> A = B"
  obtain Q where P2: "A B Perp B Q"
    by (metis P1 l8_21 perp_comm)
  obtain P T where P3: "A B Perp P A \<and> Col A B T \<and> Bet Q T P"
    using P2 l8_21_aux not_col_distincts perp_not_col2 by blast
  have P4: "A P Le B Q \<or> B Q Le A P"
    by (simp add: local.le_cases)
  have P5: "A P Le B Q \<longrightarrow> (\<exists> X. X Midpoint A B)"
    by (meson P1 P2 P3 Tarski_neutral_dimensionless.Perp_cases Tarski_neutral_dimensionless.midpoint_existence_aux Tarski_neutral_dimensionless_axioms)
  have P6: "B Q Le A P \<longrightarrow> (\<exists> X. X Midpoint A B)"
  proof -
    {
      assume H1: "B Q Le A P"
      have Q6: "B \<noteq> A"
        using P1 by auto
      have Q2: "B A Perp P A"
        by (simp add: P3 perp_left_comm)
      have Q3: "B A Perp Q B"
        using P2 Perp_perm by blast
      have Q4: "Col B A T"
        using Col_perm P3 by blast
      have Q5: "Bet P T Q"
        using Bet_perm P3 by blast
      obtain X where "X Midpoint B A"
        using H1 Q2 Q3 Q4 Q5 Q6 midpoint_existence_aux by blast
      then have "\<exists> X. X Midpoint A B"
        using l7_2 by blast
    }
    thus ?thesis
      by simp
  qed
  thus ?thesis
    using P4 P5 by blast
qed

lemma perp_in_id:
  assumes "X PerpAt A B C A"
  shows "X = A"
  by (meson Col_cases assms col_trivial_3 l8_14_2_1b)

lemma l8_22:
  assumes "A \<noteq> B" and
    "A \<noteq> P" and
    "Per B A P" and
    "Per A B R" and
    "Cong A P B R" and
    "Col A B X" and
    "Bet P X R" and
    "Cong A R P B"
  shows "X Midpoint A B \<and> X Midpoint P R"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) bet_col cong_commutativity cong_diff cong_right_commutativity l7_21 not_col_permutation_5 per_not_colp)

lemma l8_22_bis:
  assumes "A \<noteq> B" and
    "A \<noteq> P" and
    "A B Perp P A" and
    "A B Perp R B" and
    "Cong A P B R" and
    "Col A B X" and
    "Bet P X R"
  shows "Cong A R P B \<and> X Midpoint A B \<and> X Midpoint P R"
  by (metis l8_22 Perp_cases assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) perp_cong perp_per_2)

lemma perp_in_perp:
  assumes "X PerpAt A B C D"
  shows "A B Perp C D"
  using assms l8_14_2_1a by auto

lemma perp_proj:
  assumes "A B Perp C D" and
    "\<not> Col A C D"
  shows "\<exists> X. Col A B X \<and> A X Perp C D"
  using assms(1) not_col_distincts by auto

lemma l8_24 :
  assumes "P A Perp A B" and
    "Q B Perp A B" and
    "Col A B T" and
    "Bet P T Q" and
    "Bet B R Q" and
    "Cong A P B R"
  shows "\<exists> X. X Midpoint A B \<and> X Midpoint P R"
proof -
  obtain X where P1: "Bet T X B \<and> Bet R X P"
    using assms(4) assms(5) inner_pasch by blast
  have P2: "Col A B X"
    by (metis Out_cases P1 assms(3) bet_out_1 col_out2_col not_col_distincts out_trivial)
  have P3: "A \<noteq> B"
    using assms(1) col_trivial_2 l8_16_1 by blast
  have P4: "A \<noteq> P"
    using assms(1) col_trivial_1 l8_16_1 by blast
  have "\<exists> X. X Midpoint A B \<and> X Midpoint P R"
  proof cases
    assume "Col A B P"
    thus ?thesis
      using Perp_perm assms(1) perp_not_col by blast
  next
    assume Q1: "\<not> Col A B P"
    have Q2: "B \<noteq> R"
      using P4 assms(6) cong_diff by blast
    have Q3: "Q \<noteq> B"
      using Q2 assms(5) between_identity by blast
    have Q4: "\<not> Col A B Q"
      by (metis assms(2) col_permutation_3 l8_14_1 perp_col1 perp_not_col)
    have Q5: "\<not> Col A B R"
      by (meson Q2 Q4 assms(5) bet_col col_transitivity_1 not_col_permutation_2)
    have Q6: "P \<noteq> R"
      using P1 P2 Q5 between_identity by blast
    have "\<exists> X. X Midpoint A B \<and> X Midpoint P R"
    proof cases
      assume "A = P"
      thus ?thesis
        using P4 by blast
    next
      assume R0: "\<not> A = P"
      have R1: "A B Perp R B"
        by (metis Perp_cases Q2 Tarski_neutral_dimensionless.bet_col1 Tarski_neutral_dimensionless_axioms assms(2) assms(5) bet_col col_transitivity_1 perp_col1)
      have R2: "Cong A R P B"
        using P1 P2 P3 Perp_perm R0 R1 assms(1) assms(6) between_symmetry perp_cong by blast
      have R3: "\<not> Col A P B"
        using Col_perm Q1 by blast
      have R4: "P \<noteq> R"
        by (simp add: Q6)
      have R5: "Cong A P B R"
        by (simp add: assms(6))
      have R6: "Cong P B R A"
        using R2 not_cong_4312 by blast
      have R7: "Col A X B"
        using Col_perm P2 by blast
      have R8: "Col P X R"
        by (simp add: P1 bet_col between_symmetry)
      thus ?thesis using l7_21
        using R3 R4 R5 R6 R7 by blast
    qed
    thus ?thesis by simp
  qed
  thus ?thesis
    by simp
qed

lemma col_per2__per:
  assumes "A \<noteq> B" and
    "Col A B C" and
    "Per A X P" and
    "Per B X P"
  shows "Per C X P"
  by (meson Per_def assms(1) assms(2) assms(3) assms(4) l4_17 per_double_cong)

lemma perp_in_per_1:
  assumes "X PerpAt A B C D"
  shows "Per A X C"
  using PerpAt_def assms col_trivial_1 by auto

lemma perp_in_per_2:
  assumes "X PerpAt A B C D"
  shows "Per A X D"
  using assms perp_in_per_1 perp_in_right_comm by blast

lemma perp_in_per_3:
  assumes "X PerpAt A B C D"
  shows "Per B X C"
  using assms perp_in_comm perp_in_per_2 by blast

lemma perp_in_per_4:
  assumes "X PerpAt A B C D"
  shows "Per B X D"
  using assms perp_in_per_3 perp_in_right_comm by blast

subsection "Planes"

subsubsection "Coplanar"

lemma coplanar_perm_1:
  assumes "Coplanar A B C D"
  shows "Coplanar A B D C"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_2:
  assumes "Coplanar A B C D"
  shows "Coplanar A C B D"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_3:
  assumes "Coplanar A B C D"
  shows "Coplanar A C D B"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_4:
  assumes "Coplanar A B C D"
  shows "Coplanar A D B C"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_5:
  assumes "Coplanar A B C D"
  shows "Coplanar A D C B"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_6:
  assumes "Coplanar A B C D"
  shows "Coplanar B A C D"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_7:
  assumes "Coplanar A B C D"
  shows "Coplanar B A D C"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_8:
  assumes "Coplanar A B C D"
  shows "Coplanar B C A D"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_9:
  assumes "Coplanar A B C D"
  shows "Coplanar B C D A"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_10:
  assumes "Coplanar A B C D"
  shows "Coplanar B D A C"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_11:
  assumes "Coplanar A B C D"
  shows "Coplanar B D C A"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_12:
  assumes "Coplanar A B C D"
  shows "Coplanar C A B D"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_13:
  assumes "Coplanar A B C D"
  shows "Coplanar C A D B"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_14:
  assumes "Coplanar A B C D"
  shows "Coplanar C B A D"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_15:
  assumes "Coplanar A B C D"
  shows "Coplanar C B D A"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_16:
  assumes "Coplanar A B C D"
  shows "Coplanar C D A B"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_17:
  assumes "Coplanar A B C D"
  shows "Coplanar C D B A"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_18:
  assumes "Coplanar A B C D"
  shows "Coplanar D A B C"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_19:
  assumes "Coplanar A B C D"
  shows "Coplanar D A C B"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_20:
  assumes "Coplanar A B C D"
  shows "Coplanar D B A C"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_21:
  assumes "Coplanar A B C D"
  shows "Coplanar D B C A"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_22:
  assumes "Coplanar A B C D"
  shows "Coplanar D C A B"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma coplanar_perm_23:
  assumes "Coplanar A B C D"
  shows "Coplanar D C B A"
proof -
  obtain X where P1: "(Col A B X \<and> Col C D X) \<or> (Col A C X \<and> Col B D X) \<or> (Col A D X \<and> Col B C X)"
    using Coplanar_def assms by blast
  then show ?thesis
    using Coplanar_def col_permutation_4 by blast
qed

lemma ncoplanar_perm_1:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar A B D C"
  using assms coplanar_perm_1 by blast

lemma ncoplanar_perm_2:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar A C B D"
  using assms coplanar_perm_2 by blast

lemma ncoplanar_perm_3:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar A C D B"
  using assms coplanar_perm_4 by blast

lemma ncoplanar_perm_4:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar A D B C"
  using assms coplanar_perm_3 by blast

lemma ncoplanar_perm_5:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar A D C B"
  using assms coplanar_perm_5 by blast

lemma ncoplanar_perm_6:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar B A C D"
  using assms coplanar_perm_6 by blast

lemma ncoplanar_perm_7:
  assumes "\<not>  Coplanar A B C D"
  shows "\<not> Coplanar B A D C"
  using assms coplanar_perm_7 by blast

lemma ncoplanar_perm_8:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar B C A D"
  using assms coplanar_perm_12 by blast

lemma ncoplanar_perm_9:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar B C D A"
  using assms coplanar_perm_18 by blast

lemma ncoplanar_perm_10:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar B D A C"
  using assms coplanar_perm_13 by blast

lemma ncoplanar_perm_11:
  assumes "\<not> Coplanar A B C D"
  shows "\<not>  Coplanar B D C A"
  using assms coplanar_perm_19 by blast

lemma ncoplanar_perm_12:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar C A B D"
  using assms coplanar_perm_8 by blast

lemma ncoplanar_perm_13:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar C A D B"
  using assms coplanar_perm_10 by blast

lemma ncoplanar_perm_14:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar C B A D"
  using assms coplanar_perm_14 by blast

lemma ncoplanar_perm_15:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar C B D A"
  using assms coplanar_perm_20 by blast

lemma ncoplanar_perm_16:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar C D A B"
  using assms coplanar_perm_16 by blast

lemma ncoplanar_perm_17:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar C D B A"
  using assms coplanar_perm_22 by blast

lemma ncoplanar_perm_18:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar D A B C"
  using assms coplanar_perm_9 by blast

lemma ncoplanar_perm_19:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar D A C B"
  using assms coplanar_perm_11 by blast

lemma ncoplanar_perm_20:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar D B A C"
  using assms coplanar_perm_15 by blast

lemma ncoplanar_perm_21:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar D B C A"
  using assms coplanar_perm_21 by blast

lemma ncoplanar_perm_22:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Coplanar D C A B"
  using assms coplanar_perm_17 by blast

lemma ncoplanar_perm_23:
  assumes "\<not>  Coplanar A B C D"
  shows "\<not> Coplanar D C B A"
  using assms coplanar_perm_23 by blast

lemma coplanar_trivial:
  shows "Coplanar A A B C"
  using Coplanar_def NCol_cases col_trivial_1 by blast

lemma col__coplanar:
  assumes "Col A B C"
  shows "Coplanar A B C D"
  using Coplanar_def assms not_col_distincts by blast

lemma ncop__ncol:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Col A B C"
  using assms col__coplanar by blast

lemma ncop__ncols:
  assumes "\<not> Coplanar A B C D"
  shows "\<not> Col A B C \<and> \<not> Col A B D \<and> \<not> Col A C D \<and> \<not> Col B C D"
  by (meson assms col__coplanar coplanar_perm_4 ncoplanar_perm_9)

lemma bet__coplanar:
  assumes "Bet A B C"
  shows "Coplanar A B C D"
  using assms bet_col ncop__ncol by blast

lemma out__coplanar:
  assumes "A Out B C"
  shows "Coplanar A B C D"
  using assms col__coplanar out_col by blast

lemma midpoint__coplanar:
  assumes "A Midpoint B C"
  shows "Coplanar A B C D"
  using assms midpoint_col ncop__ncol by blast

lemma perp__coplanar:
  assumes "A B Perp C D"
  shows "Coplanar A B C D"
proof -
  obtain P where "P PerpAt A B C D"
    using Perp_def assms by blast
  then show ?thesis
    using Coplanar_def perp_in_col by blast
qed

lemma ts__coplanar:
  assumes "A B TS C D"
  shows "Coplanar A B C D"
  by (metis (full_types) Coplanar_def TS_def assms bet_col col_permutation_2 col_permutation_3)

lemma reflectl__coplanar:
  assumes "A B ReflectL C D"
  shows "Coplanar A B C D"
  by (metis (no_types) ReflectL_def Tarski_neutral_dimensionless.perp__coplanar Tarski_neutral_dimensionless_axioms assms col__coplanar col_trivial_1 ncoplanar_perm_17)

lemma reflect__coplanar:
  assumes "A B Reflect C D"
  shows "Coplanar A B C D"
  by (metis (no_types) Reflect_def Tarski_neutral_dimensionless.reflectl__coplanar Tarski_neutral_dimensionless_axioms assms col_trivial_2 ncop__ncols)

lemma inangle__coplanar:
  assumes "A InAngle B C D"
  shows "Coplanar A B C D"
proof -
  obtain X where P1: "Bet B X D \<and> (X = C \<or> C Out X A)"
    using InAngle_def assms by auto
  then show ?thesis
    by (meson Col_cases Coplanar_def bet_col ncop__ncols out_col)
qed

lemma pars__coplanar:
  assumes "A B ParStrict C D"
  shows "Coplanar A B C D"
  using ParStrict_def assms by auto

lemma par__coplanar:
  assumes "A B Par C D"
  shows "Coplanar A B C D"
  using Par_def assms ncop__ncols pars__coplanar by blast

lemma plg__coplanar:
  assumes "Plg A B C D"
  shows "Coplanar A B C D"
proof -
  obtain M where "Bet A M C \<and> Bet B M D"
    by (meson Plg_def assms midpoint_bet)
  then show ?thesis
    by (metis InAngle_def bet_out_1 inangle__coplanar ncop__ncols not_col_distincts)
qed

lemma plgs__coplanar:
  assumes "ParallelogramStrict A B C D"
  shows "Coplanar A B C D"
  using ParallelogramStrict_def assms par__coplanar by blast

lemma plgf__coplanar:
  assumes "ParallelogramFlat A B C D"
  shows "Coplanar A B C D"
  using ParallelogramFlat_def assms col__coplanar by auto

lemma parallelogram__coplanar:
  assumes "Parallelogram A B C D"
  shows "Coplanar A B C D"
  using Parallelogram_def assms plgf__coplanar plgs__coplanar by auto

lemma rhombus__coplanar:
  assumes "Rhombus A B C D"
  shows "Coplanar A B C D"
  using Rhombus_def assms plg__coplanar by blast

lemma rectangle__coplanar:
  assumes "Rectangle A B C D"
  shows "Coplanar A B C D"
  using Rectangle_def assms plg__coplanar by blast

lemma square__coplanar:
  assumes "Square A B C D"
  shows "Coplanar A B C D"
  using Square_def assms rectangle__coplanar by blast

lemma lambert__coplanar:
  assumes "Lambert A B C D"
  shows "Coplanar A B C D"
  using Lambert_def assms by presburger

subsubsection "Planes"

lemma ts_distincts:
  assumes "A B TS P Q"
  shows "A \<noteq> B \<and> A \<noteq> P \<and> A \<noteq> Q \<and> B \<noteq> P \<and> B \<noteq> Q \<and> P \<noteq> Q"
  using TS_def assms bet_neq12__neq not_col_distincts by blast

lemma l9_2:
  assumes "A B TS P Q"
  shows "A B TS Q P"
  using TS_def assms between_symmetry by blast

lemma invert_two_sides:
  assumes "A B TS P Q"
  shows "B A TS P Q"
  using TS_def assms not_col_permutation_5 by blast

lemma l9_3:
  assumes "P Q TS A C" and
    "Col M P Q" and
    "M Midpoint A C" and
    "Col R P Q" and
    "R Out A B"
  shows "P Q TS B C"
proof -
  have P1: "\<not> Col A P Q"
    using TS_def assms(1) by blast
  have P2: "P \<noteq> Q"
    using P1 not_col_distincts by auto
  obtain T where P3: "Col T P Q \<and> Bet A T C"
    using assms(2) assms(3) midpoint_bet by blast
  have P4: "A \<noteq> C"
    using assms(1) ts_distincts by blast
  have P5: "T = M"
    by (smt P1 P3 Tarski_neutral_dimensionless.bet_col1 Tarski_neutral_dimensionless_axioms assms(2) assms(3) col_permutation_2 l6_21 midpoint_bet)
  have "P Q TS B C"
  proof cases
    assume "C = M"
    then show ?thesis
      using P4 assms(3) midpoint_distinct_1 by blast
  next
    assume P6: "\<not> C = M"
    have P7: "\<not> Col B P Q"
      by (metis P1 assms(4) assms(5) col_permutation_1 colx l6_3_1 out_col)
    have P97: "Bet R A B \<or> Bet R B A"
      using Out_def assms(5) by auto
    {
      assume Q1: "Bet R A B"
      obtain B' where Q2: "M Midpoint B B'"
        using symmetric_point_construction by blast
      obtain R' where Q3: "M Midpoint R R'"
        using symmetric_point_construction by blast
      have Q4: "Bet B' C R'"
        using Q1 Q2 Q3 assms(3) between_symmetry l7_15 by blast
      obtain X where Q5: "Bet M X R' \<and> Bet C X B"
        using Bet_perm Midpoint_def Q2 Q4 between_trivial2 l3_17 by blast
      have Q6: "Col X P Q"
      proof -
        have R1: "Col P M R"
          using P2 assms(2) assms(4) col_permutation_4 l6_16_1 by blast
        have R2: "Col Q M R"
          by (metis R1 assms(2) assms(4) col_permutation_5 l6_16_1 not_col_permutation_3)
        {
          assume "M = X"
          then have "Col X P Q"
            using assms(2) by blast
        }
        then have R3: "M = X \<longrightarrow> Col X P Q" by simp
        {
          assume "M \<noteq> X"
          then have S1: "M \<noteq> R'"
            using Q5 bet_neq12__neq by blast
          have "M \<noteq> R"
            using Q3 S1 midpoint_distinct_1 by blast
          then have "Col X P Q"
            by (smt Col_perm Q3 Q5 R1 R2 S1 bet_out col_transitivity_2 midpoint_col out_col)
        }
        then have "M \<noteq> X \<longrightarrow> Col X P Q" by simp
        then show ?thesis using R3 by blast
      qed
      have "Bet B X C"
        using Q5 between_symmetry by blast
      then have "P Q TS B C" using Q6
        using P7 TS_def assms(1) by blast
    }
    then have P98: "Bet R A B \<longrightarrow> P Q TS B C" by simp
    {
      assume S2: "Bet R B A"
      have S3: "Bet C M A"
        using Bet_perm P3 P5 by blast
      then obtain X where "Bet B X C \<and> Bet M X R"
        using S2 inner_pasch by blast
      then have "P Q TS B C"
        by (metis Col_def P7 TS_def assms(1) assms(2) assms(4) between_inner_transitivity between_trivial l6_16_1 not_col_permutation_5)
    }
    then have "Bet R B A \<longrightarrow> P Q TS B C" by simp
    then show ?thesis using P97 P98
      by blast
  qed
  then show ?thesis by blast
qed

lemma mid_preserves_col:
  assumes "Col A B C" and
    "M Midpoint A A'" and
    "M Midpoint B B'" and
    "M Midpoint C C'"
  shows "Col A' B' C'"
  using Col_def assms(1) assms(2) assms(3) assms(4) l7_15 by auto

lemma per_mid_per:
  assumes (*"A \<noteq> B" and*)
    "Per X A B" and
    "M Midpoint A B" and
    "M Midpoint X Y"
  shows "Cong A X B Y \<and> Per Y B A"
  by (meson Cong3_def Mid_perm assms(1) assms(2) assms(3) l7_13 l8_10)

lemma sym_preserve_diff:
  assumes "A \<noteq> B" and
    "M Midpoint A A'" and
    "M Midpoint B B'"
  shows "A'\<noteq> B'"
  using assms(1) assms(2) assms(3) l7_9 by blast

lemma l9_4_1_aux_R1:
  assumes "R = S" and
    "S C Le R A" and
    "P Q TS A C" and
    "Col R P Q" and
    "P Q Perp A R" and
    "Col S P Q" and
    "P Q Perp C S" and
    "M Midpoint R S"
  shows "\<forall> U C'. M Midpoint U C' \<longrightarrow> (R Out U A \<longleftrightarrow> S Out C C')"
proof -
  have P1: "M = R"
    using assms(1) assms(8) l7_3 by blast
  have P2: "\<not> Col A P Q"
    using TS_def assms(3) by auto
  then have P3: "P \<noteq> Q"
    using not_col_distincts by blast
  obtain T where P4: "Col T P Q \<and> Bet A T C"
    using TS_def assms(3) by blast
  {
    assume "\<not> M = T"
    then have "M PerpAt M T A M" using perp_col2
      by (metis P1 P4 assms(4) assms(5) not_col_permutation_3 perp_left_comm perp_perp_in)
    then have "M T Perp C M"
      using P1 P4 \<open>M \<noteq> T\<close> assms(1) assms(4) assms(7) col_permutation_1 perp_col2 by blast
    then have "Per T M A"
      using \<open>M PerpAt M T A M\<close> perp_in_per_3 by blast
    have "Per T M C"
      by (simp add: \<open>M T Perp C M\<close> perp_per_1)
    have "M = T"
    proof -
      have "Per C M T"
        by (simp add: \<open>Per T M C\<close> l8_2)
      then show ?thesis using l8_6 l8_2
        using P4 \<open>Per T M A\<close> by blast
    qed
    then have "False"
      using \<open>M \<noteq> T\<close> by blast
  }
  then have Q0: "M = T" by blast
  have R1: "\<forall> U C'. ((M Midpoint U C' \<and> M Out U A) \<longrightarrow> M Out C C')"
  proof -
    {
      fix U C'
      assume Q1: "M Midpoint U C' \<and> M Out U A"
      have Q2: "C \<noteq> M"
        using P1 assms(1) assms(7) perp_not_eq_2 by blast
      have Q3: "C' \<noteq> M"
        using Q1 midpoint_not_midpoint out_diff1 by blast
      have Q4: "Bet U M C"
        using P4 Q0 Q1 bet_out__bet l6_6 by blast
      then have "M Out C C'"
        by (metis (full_types) Out_def Q1 Q2 Q3 l5_2 midpoint_bet)
    }
    then show ?thesis by blast
  qed
  have R2: "\<forall> U C'. ((M Midpoint U C' \<and> M Out C C') \<longrightarrow> M Out U A)"
  proof -
    {
      fix U C'
      assume Q1: "M Midpoint U C' \<and> M Out C C'"
      have Q2: "C \<noteq> M"
        using P1 assms(1) assms(7) perp_not_eq_2 by blast
      have Q3: "C' \<noteq> M"
        using Q1 l6_3_1 by blast
      have Q4: "Bet U M C"
        by (metis Out_def Q1 between_inner_transitivity midpoint_bet outer_transitivity_between)
      then have "M Out U A"
        by (metis P2 P4 Q0 Q1 Q2 Q3 l6_2 midpoint_distinct_1)
    }
    then show ?thesis by blast
  qed
  then show ?thesis
    using R1 P1 P2 assms by blast
qed

lemma l9_4_1_aux_R21:
  assumes "R \<noteq> S" and
    "S C Le R A" and
    "P Q TS A C" and
    "Col R P Q" and
    "P Q Perp A R" and
    "Col S P Q" and
    "P Q Perp C S" and
    "M Midpoint R S"
  shows "\<forall> U C'. M Midpoint U C' \<longrightarrow>  (R Out U A \<longleftrightarrow> S Out C C')"
proof -
  obtain D where P1: "Bet R D A \<and> Cong S C R D"
    using Le_def assms(2) by blast
  have P2: "C \<noteq> S"
    using assms(7) perp_not_eq_2 by auto
  have P3: "R \<noteq> D"
    using P1 P2 cong_identity by blast
  have P4: "R S Perp A R"
    using assms(1) assms(4) assms(5) assms(6) not_col_permutation_2 perp_col2 by blast
  have "\<exists> M. (M Midpoint S R \<and> M Midpoint C D)"
  proof -
    have Q1: "\<not> Col A P Q"
      using TS_def assms(3) by blast
    have Q2: "P \<noteq> Q"
      using Q1 not_col_distincts by blast
    obtain T where Q3: "Col T P Q \<and> Bet A T C"
      using TS_def assms(3) by blast
    have Q4: "C S Perp S R"
      by (metis NCol_perm assms(1) assms(4) assms(6) assms(7) perp_col0)
    have Q5: "A R Perp S R"
      using P4 Perp_perm by blast
    have Q6: "Col S R T"
      using Col_cases Q2 Q3 assms(4) assms(6) col3 by blast
    have Q7: "Bet C T A"
      using Bet_perm Q3 by blast
    have Q8: "Bet R D A"
      by (simp add: P1)
    have "Cong S C R D"
      by (simp add: P1)
    then show ?thesis using P1 Q4 Q5 Q6 Q7 l8_24 by blast
  qed
  then obtain M' where P5: "M' Midpoint S R \<and> M' Midpoint C D" by blast
  have P6: "M = M'"
    by (meson P5 assms(8) l7_17_bis)
  have L1: "\<forall> U C'. (M Midpoint U C' \<and> R Out U A) \<longrightarrow> S Out C C'"
  proof -
    {
      fix U C'
      assume R1: "M Midpoint U C' \<and> R Out U A"
      have R2: "C \<noteq> S"
        using P2 by auto
      have R3: "C' \<noteq> S"
        using P5 R1 P6 l7_9_bis out_diff1 by blast
      have R4: "Bet S C C' \<or> Bet S C' C"
      proof -
        have R5: "Bet R U A \<or> Bet R A U"
          using Out_def R1 by auto
        {
          assume "Bet R U A"
          then have "Bet R U D \<or> Bet R D U"
            using P1 l5_3 by blast
          then have "Bet S C C' \<or> Bet S C' C"
            using P5 P6 R1 l7_15 l7_2 by blast
        }
        then have R6: "Bet R U A \<longrightarrow> Bet S C C' \<or> Bet S C' C" by simp
        have "Bet R A U \<longrightarrow> Bet S C C' \<or> Bet S C' C"
          using P1 P5 P6 R1 between_exchange4 l7_15 l7_2 by blast
        then show ?thesis using R5 R6 by blast
      qed
      then have "S Out C C'"
        by (simp add: Out_def R2 R3)
    }
    then show ?thesis by simp
  qed
  have "\<forall> U C'. (M Midpoint U C' \<and> S Out C C') \<longrightarrow> R Out U A"
  proof -
    {
      fix U C'
      assume Q1: "M Midpoint U C' \<and> S Out C C'"
      then have Q2: "U \<noteq> R"
        using P5 P6 l7_9_bis out_diff2 by blast
      have Q3: "A \<noteq> R"
        using assms(5) perp_not_eq_2 by auto
      have Q4: "Bet S C C' \<or> Bet S C' C"
        using Out_def Q1 by auto
      {
        assume V0: "Bet S C C'"
        have V1: "R \<noteq> D"
          by (simp add: P3)
        then have V2: "Bet R D U"
        proof -
          have W1: "M Midpoint S R"
            using P5 P6 by blast
          have W2: "M Midpoint C D"
            by (simp add: P5 P6)
          have "M Midpoint C' U"
            by (simp add: Q1 l7_2)
          then show ?thesis
            using V0 P5 P6 l7_15 by blast
        qed
        have "Bet R D A"
          using P1 by auto
        then have "Bet R U A \<or> Bet R A U"
          using V1 V2 l5_1 by blast
      }
      then have Q5: "Bet S C C' \<longrightarrow> Bet R U A \<or> Bet R A U" by simp
      {
        assume R1: "Bet S C' C"
        have "Bet R U A"
          using P1 P5 P6 Q1 R1 between_exchange4 l7_15 l7_2 by blast
      }
      then have "Bet S C' C \<longrightarrow> Bet R U A \<or> Bet R A U" by simp
      then have "Bet R U A \<or> Bet R A U"
        using Q4 Q5 by blast
      then have "R Out U A"
        by (simp add: Out_def Q2 Q3)
    }
    then show ?thesis by simp
  qed
  then show ?thesis
    using L1 by blast
qed

lemma l9_4_1_aux:
  assumes "S C Le R A" and
    "P Q TS A C" and
    "Col R P Q" and
    "P Q Perp A R" and
    "Col S P Q" and
    "P Q Perp C S" and
    "M Midpoint R S"
  shows "\<forall> U C'. (M Midpoint U C' \<longrightarrow> (R Out U A \<longleftrightarrow> S Out C C'))"
  using l9_4_1_aux_R1 l9_4_1_aux_R21 assms by smt

lemma per_col_eq:
  assumes "Per A B C" and
    "Col A B C" and
    "B \<noteq> C"
  shows "A = B"
  using assms(1) assms(2) assms(3) l8_9 by blast

lemma l9_4_1:
  assumes "P Q TS A C" and
    "Col R P Q" and
    "P Q Perp A R" and
    "Col S P Q" and
    "P Q Perp C S" and
    "M Midpoint R S"
  shows "\<forall> U C'. M Midpoint U C' \<longrightarrow> (R Out U A \<longleftrightarrow> S Out C C')"
proof -
  have P1: "S C Le R A \<or> R A  Le S C"
    using local.le_cases by blast
  {
    assume Q1: "S C Le R A"
    {
      fix U C'
      assume "M Midpoint U C'"
      then have "(R Out U A \<longleftrightarrow> S Out C C')"
        using Q1 assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l9_4_1_aux by blast
    }
    then have "\<forall> U C'. M Midpoint U C' \<longrightarrow> (R Out U A \<longleftrightarrow> S Out C C')" by simp
  }
  then have P2: "S C Le R A \<longrightarrow> (\<forall> U C'. M Midpoint U C' \<longrightarrow> (R Out U A \<longleftrightarrow> S Out C C'))" by simp
  {
    assume Q2: " R A Le S C"
    {
      fix U C'
      assume "M Midpoint U C'"
      then have "(R Out A U \<longleftrightarrow> S Out C' C)"
        using Q2 assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l7_2 l9_2 l9_4_1_aux by blast
      then have "(R Out U A \<longleftrightarrow> S Out C C')"
        using l6_6 by blast
    }
    then have "\<forall> U C'. M Midpoint U C' \<longrightarrow> (R Out U A \<longleftrightarrow> S Out C C')" by simp
  }
  then have P3: "R A Le S C \<longrightarrow> (\<forall> U C'. M Midpoint U C' \<longrightarrow> (R Out U A \<longleftrightarrow> S Out C C'))" by simp

  then show ?thesis
    using P1 P2 by blast
qed

lemma mid_two_sides:
  assumes "M Midpoint A B" and
    "\<not> Col A B X" and
    "M Midpoint X Y"
  shows "A B TS X Y"
proof -
  have f1: "\<not> Col Y A B"
    by (meson Mid_cases Tarski_neutral_dimensionless.mid_preserves_col Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) col_permutation_3)
  have "Bet X M Y"
    using assms(3) midpoint_bet by blast
  then show ?thesis
    using f1 by (metis (no_types) TS_def assms(1) assms(2) col_permutation_1 midpoint_col)
qed


lemma col_preserves_two_sides:
  assumes "C \<noteq> D" and
    "Col A B C" and
    "Col A B D" and
    "A B TS X Y"
  shows "C D TS X Y"
proof -
  have P1: "\<not> Col X A B"
    using TS_def assms(4) by blast
  then have P2: "A \<noteq> B"
    using not_col_distincts by blast
  have P3: "\<not> Col X C D"
    by (metis Col_cases P1 Tarski_neutral_dimensionless.colx Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3))
  have P4: "\<not> Col Y C D"
    by (metis Col_cases TS_def Tarski_neutral_dimensionless.colx Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4))
  then show ?thesis
  proof -
    obtain pp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p" where
      "\<forall>x0 x1 x2 x3. (\<exists>v4. Col v4 x3 x2 \<and> Bet x1 v4 x0) = (Col (pp x0 x1 x2 x3) x3 x2 \<and> Bet x1 (pp x0 x1 x2 x3) x0)"
      by moura
    then have f1: "\<not> Col X A B \<and> \<not> Col Y A B \<and> Col (pp Y X B A) A B \<and> Bet X (pp Y X B A) Y"
      using TS_def assms(4) by presburger
    then have "Col (pp Y X B A) C D"
      by (meson P2 assms(2) assms(3) col3 not_col_permutation_3 not_col_permutation_4)
    then show ?thesis
      using f1 TS_def P3 P4 by blast
  qed
qed

lemma out_out_two_sides:
  assumes "A \<noteq> B" and
    "A B TS X Y" and
    "Col I A B" and
    "Col I X Y" and
    "I Out X U" and
    "I Out Y V"
  shows "A B TS U V"
proof -
  have P0: "\<not> Col X A B"
    using TS_def assms(2) by blast
  then have P1: "\<not> Col V A B"
    by (smt assms(2) assms(3) assms(4) assms(6) col_out2_col col_transitivity_1 not_col_permutation_3 not_col_permutation_4 out_diff2 out_trivial ts_distincts)
  have P2: "\<not> Col U A B"
    by (metis P0 assms(3) assms(5) col_permutation_2 colx out_col out_distinct)
  obtain T where P3: "Col T A B \<and> Bet X T Y"
    using TS_def assms(2) by blast
  have "I = T"
  proof -
    have f1: "\<forall>p pa pb. \<not> Col p pa pb \<and> \<not> Col p pb pa \<and> \<not> Col pa p pb \<and> \<not> Col pa pb p \<and> \<not> Col pb p pa \<and> \<not> Col pb pa p \<or> Col p pa pb"
      using Col_cases by blast
    then have f2: "Col X Y I"
      using assms(4) by blast
    have f3: "Col B A I"
      using f1 assms(3) by blast
    have f4: "Col B A T"
      using f1 P3 by blast
    have f5: "\<not> Col X A B \<and> \<not> Col X B A \<and> \<not> Col A X B \<and> \<not> Col A B X \<and> \<not> Col B X A \<and> \<not> Col B A X"
      using f1 \<open>\<not> Col X A B\<close> by blast
    have f6: "A \<noteq> B \<and> A \<noteq> X \<and> A \<noteq> Y \<and> B \<noteq> X \<and> B \<noteq> Y \<and> X \<noteq> Y"
      using assms(2) ts_distincts by presburger
    have "Col X Y T"
      using f1 by (meson P3 bet_col)
    then show ?thesis
      using f6 f5 f4 f3 f2 by (meson Tarski_neutral_dimensionless.l6_21 Tarski_neutral_dimensionless_axioms)
  qed
  then have "Bet U T V"
    using P3 assms(5) assms(6) bet_out_out_bet by blast
  then show ?thesis
    using P1 P2 P3 TS_def by blast
qed

lemma l9_4_2_aux_R1:
  assumes "R = S " and
    "S C Le R A" and
    "P Q TS A C" and
    "Col R P Q" and
    "P Q Perp A R" and
    "Col S P Q" and
    "P Q Perp C S" and
    "R Out U A" and
    "S Out V C"
  shows "P Q TS U V"
proof -
  have "\<not> Col A P Q"
    using TS_def assms(3) by auto
  then have P2: "P \<noteq> Q"
    using not_col_distincts by blast
  obtain T where P3: "Col T P Q \<and> Bet A T C"
    using TS_def assms(3) by blast
  have "R = T" using assms(1) assms(5) assms(6) assms(7) col_permutation_1 l8_16_1 l8_6
    by (meson P3)
  then show ?thesis
    by (smt P2 P3 assms(1) assms(3) assms(8) assms(9) bet_col col_transitivity_2 l6_6 not_col_distincts out_out_two_sides)
qed

lemma l9_4_2_aux_R2:
  assumes "R \<noteq> S" and
    "S C Le R A" and
    "P Q TS A C" and
    "Col R P Q" and
    "P Q Perp A R" and
    "Col S P Q" and
    "P Q Perp C S" and
    "R Out U A" and
    "S Out V C"
  shows "P Q TS U V"
proof -
  have P1: "P \<noteq> Q"
    using assms(7) perp_distinct by auto
  have P2: "R S TS A C"
    using assms(1) assms(3) assms(4) assms(6) col_permutation_1 col_preserves_two_sides by blast
  have P3: "Col R S P"
    using P1 assms(4) assms(6) col2__eq not_col_permutation_1 by blast
  have P4: "Col R S Q"
    by (metis P3 Tarski_neutral_dimensionless.colx Tarski_neutral_dimensionless_axioms assms(4) assms(6) col_trivial_2)
  have P5: "R S Perp A R"
    using NCol_perm assms(1) assms(4) assms(5) assms(6) perp_col2 by blast
  have P6: "R S Perp C S"
    using assms(1) assms(4) assms(6) assms(7) col_permutation_1 perp_col2 by blast
  have P7: "\<not> Col A R S"
    using P2 TS_def by blast
  obtain T where P8: "Col T R S \<and> Bet A T C"
    using P2 TS_def by blast
  obtain C' where P9: "Bet R C' A \<and> Cong S C R C'"
    using Le_def assms(2) by blast
  have "\<exists> X. X Midpoint S R \<and> X Midpoint C C'"
  proof -
    have Q1: "C S Perp S R"
      using P6 Perp_perm by blast
    have Q2: "A R Perp S R"
      using P5 Perp_perm by blast
    have Q3: "Col S R T"
      using Col_cases P8 by blast
    have Q4: "Bet C T A"
      using Bet_perm P8 by blast
    have Q5: "Bet R C' A"
      by (simp add: P9)
    have "Cong S C R C'"
      by (simp add: P9)
    then show ?thesis using Q1 Q2 Q3 Q4 Q5 l8_24
      by blast
  qed
  then obtain M where P10: "M Midpoint S R \<and> M Midpoint C C'" by blast
  obtain U' where P11: "M Midpoint U U'"
    using symmetric_point_construction by blast
  have P12: "R \<noteq> U"
    using assms(8) out_diff1 by blast
  have P13: "R S TS U U'"
    by (smt P10 P11 P12 P7 assms(8) col_transitivity_2 invert_two_sides mid_two_sides not_col_permutation_3 not_col_permutation_4 out_col)
  have P14: "R S TS V U"
  proof -
    have Q1: "Col M R S"
      using P10 midpoint_col not_col_permutation_5 by blast
    have Q2: "M Midpoint U' U"
      by (meson P11 Tarski_neutral_dimensionless.Mid_cases Tarski_neutral_dimensionless_axioms)
    have "S Out U' V"
      by (meson P10 P11 P2 P5 P6 Tarski_neutral_dimensionless.l7_2 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(8) assms(9) l6_6 l6_7 l9_4_1_aux_R21 not_col_distincts)
    then show ?thesis
      using P13 Q1 Q2 col_trivial_3 l9_2 l9_3 by blast
  qed
  then show ?thesis
    using P1 P3 P4 col_preserves_two_sides l9_2 by blast
qed

lemma l9_4_2_aux:
  assumes "S C Le R A" and
    "P Q TS A C" and
    "Col R P Q" and
    "P Q Perp A R" and
    "Col S P Q" and
    "P Q Perp C S" and
    "R Out U A" and
    "S Out V C"
  shows "P Q TS U V"
  using l9_4_2_aux_R1 l9_4_2_aux_R2
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8))

lemma l9_4_2:
  assumes "P Q TS A C" and
    "Col R P Q" and
    "P Q Perp A R" and
    "Col S P Q" and
    "P Q Perp C S" and
    "R Out U A" and
    "S Out V C"
  shows "P Q TS U V"
proof -
  have P1: "S C Le R A \<or> R A Le S C"
    by (simp add: local.le_cases)
  have P2: "S C Le R A \<longrightarrow> P Q TS U V"
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) l9_4_2_aux)
  have "R A Le S C \<longrightarrow> P Q TS U V"
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) l9_2 l9_4_2_aux)
  then show ?thesis
    using P1 P2 by blast
qed

lemma l9_5:
  assumes "P Q TS A C" and
    "Col R P Q" and
    "R Out A B"
  shows "P Q TS B C"
proof -
  have P1: "P \<noteq> Q"
    using assms(1) ts_distincts by blast
  obtain A' where P2: "Col P Q A' \<and> P Q Perp A A'"
    by (metis NCol_perm Tarski_neutral_dimensionless.TS_def Tarski_neutral_dimensionless_axioms assms(1) l8_18_existence)
  obtain C' where P3: "Col P Q C' \<and> P Q Perp C C'"
    using Col_perm TS_def assms(1) l8_18_existence by blast
  obtain M where P5: "M Midpoint A' C'"
    using midpoint_existence by blast
  obtain D where S2: "M Midpoint A D"
    using symmetric_point_construction by auto
  have "\<exists> B0. Col P Q B0 \<and> P Q Perp B B0"
  proof -
    have S1: "\<not> Col P Q B"
      by (metis P2 Tarski_neutral_dimensionless.colx Tarski_neutral_dimensionless.perp_not_col2 Tarski_neutral_dimensionless_axioms assms(2) assms(3) col_permutation_1 l6_3_1 out_col)
    then show ?thesis
      by (simp add: l8_18_existence)
  qed
  then obtain B' where P99: "Col P Q B' \<and> P Q Perp B B'" by blast
  have "P Q TS B C"
  proof -
    have S3: "C' Out D C \<longleftrightarrow> A' Out A A"
      using Out_cases P2 P3 P5 S2 assms(1) l9_4_1 not_col_permutation_1 by blast
    then have S4: "C' Out D C"
      using P2 Tarski_neutral_dimensionless.perp_not_eq_2 Tarski_neutral_dimensionless_axioms out_trivial by fastforce
    have S5: "P Q TS A D"
      using P2 P3 S3 S4 assms(1) col_permutation_2 l9_4_2 by blast
    {
      assume "A' \<noteq> C'"
      then have "Col M P Q"
        by (smt P2 P3 P5 col_trivial_2 l6_21 midpoint_col not_col_permutation_1)
      then have "P Q TS B D"
        using S2 S5 assms(2) assms(3) l9_3 by blast
    }
    then have "A' \<noteq> C' \<longrightarrow> P Q TS B D" by simp
    then have S6: "P Q TS B D"
      by (metis P3 P5 S2 S5 assms(2) assms(3) l9_3 midpoint_distinct_2 not_col_permutation_1)
    have S7: "Col B' P Q"
      using Col_perm P99 by blast
    have S8: "P Q Perp B B'"
      using P99 by blast
    have S9: "Col C' P Q"
      using Col_cases P3 by auto
    have S10: "P Q Perp D C'"
      by (metis Col_perm P3 S4 l6_3_1 out_col perp_col1 perp_right_comm)
    have S11: "B' Out B B"
      by (metis (no_types) P99 out_trivial perp_not_eq_2)
    have "C' Out C D"
      by (simp add: S4 l6_6)
    then show ?thesis using S6 S7 S8 S9 S10 S11 l9_4_2 by blast
  qed
  then show ?thesis using l8_18_existence by blast
qed

lemma outer_pasch_R1:
  assumes "Col P Q C" and
    "Bet A C P" and
    "Bet B Q C"
  shows "\<exists> X. Bet A X B \<and> Bet P Q X"
  by (smt Bet_perm Col_def assms(1) assms(2) assms(3) between_exchange3 between_trivial outer_transitivity_between2)

lemma outer_pasch_R2:
  assumes "\<not> Col P Q C" and
    "Bet A C P" and
    "Bet B Q C"
  shows "\<exists> X. Bet A X B \<and> Bet P Q X"
proof cases
  assume "B = Q"
  then show ?thesis
    using between_trivial by blast
next
  assume P1: "B \<noteq> Q"
  have P2: "A \<noteq> P"
    using assms(1) assms(2) between_identity col_trivial_3 by blast
  have P3: "P \<noteq> Q"
    using assms(1) col_trivial_1 by blast
  have P4: "P \<noteq> B"
    using assms(1) assms(3) bet_col by blast
  have P5: "P Q TS C B"
  proof -
    have Q1: "\<not> Col C P Q"
      using Col_cases assms(1) by blast
    have Q2: "\<not> Col B P Q"
      by (metis Col_cases P1 Tarski_neutral_dimensionless.colx Tarski_neutral_dimensionless_axioms assms(1) assms(3) bet_col col_trivial_2)
    have "\<exists> T. Col T P Q \<and> Bet C T B"
      using Col_cases assms(3) between_symmetry col_trivial_2 by blast
    then show ?thesis
      by (simp add: Q1 Q2 TS_def)
  qed
  have P6: "P Q TS A B"
    by (metis P5 assms(1) assms(2) bet_out_1 l9_5 not_col_distincts)
  obtain X where P7: "Col X P Q \<and> Bet A X B"
    using P6 TS_def by blast
  have "Bet P Q X"
  proof -
    obtain T where P8: "Bet X T P \<and> Bet C T B"
      using P7 assms(2) between_symmetry inner_pasch by blast
    have P9: "B \<noteq> C"
      using P1 assms(3) bet_neq12__neq by blast
    have P10: "T = Q"
    proof -
      have f1: "\<forall>p pa pb. Col pb pa p \<or> \<not> Bet pb pa p"
        by (meson bet_col1 between_trivial)
      then have f2: "Col Q C B"
        using NCol_cases assms(3) by blast
      have "Col T C B"
        using f1 NCol_cases P8 by blast
      then show ?thesis
        using f2 f1 by (metis (no_types) NCol_cases P7 P8 assms(1) between_trivial l6_16_1 l6_2 not_bet_and_out)
    qed
    then show ?thesis
      using P8 between_symmetry by blast
  qed
  then show ?thesis using P7 by blast
qed

lemma outer_pasch:
  assumes "Bet A C P" and
    "Bet B Q C"
  shows "\<exists> X. Bet A X B \<and> Bet P Q X"
  using assms(1) assms(2) outer_pasch_R1 outer_pasch_R2 by blast

lemma os_distincts:
  assumes "A B OS X Y"
  shows "A \<noteq> B \<and> A \<noteq> X \<and> A \<noteq> Y \<and> B \<noteq> X \<and> B \<noteq> Y"
  using OS_def assms ts_distincts by blast

lemma invert_one_side:
  assumes "A B OS P Q"
  shows "B A OS P Q"
proof -
  obtain T where "A B TS P T \<and> A B TS Q T"
    using OS_def assms by blast
  then have "B A TS P T \<and> B A TS Q T"
    using invert_two_sides by blast
  thus ?thesis
    using OS_def by blast
qed

lemma l9_8_1:
  assumes "P Q TS A C" and
    "P Q TS B C"
  shows "P Q OS A B"
proof -
  have "\<exists> R::'p. (P Q TS A R \<and> P Q TS B R)"
    using assms(1) assms(2) by blast
  then show ?thesis
    using OS_def by blast
qed

lemma not_two_sides_id:
  shows "\<not> P Q TS A A"
  using ts_distincts by blast

lemma l9_8_2:
  assumes "P Q TS A C" and
    "P Q OS A B"
  shows "P Q TS B C"
proof -
  obtain D where P1: "P Q TS A D \<and> P Q TS B D"
    using assms(2) OS_def by blast
  then have "P \<noteq> Q"
    using ts_distincts by blast
  obtain T where P2: "Col T P Q \<and> Bet A T C"
    using TS_def assms(1) by blast
  obtain X where P3: "Col X P Q \<and> Bet A X D"
    using TS_def P1 by blast
  obtain Y where P4: "Col Y P Q \<and> Bet B Y D"
    using TS_def P1 by blast
  then obtain M where P5: "Bet Y M A \<and> Bet X M B" using P3 inner_pasch by blast
  have P6: "A \<noteq> D"
    using P1 ts_distincts by blast
  have P7: "B \<noteq> D"
    using P1 not_two_sides_id by blast
  {
    assume Q0: "Col A B D"
    have "P Q TS B C"
    proof cases
      assume Q1: "M = Y"
      have "X = Y"
      proof -
        have S1: "\<not> Col P Q A"
          using TS_def assms(1) not_col_permutation_1 by blast
        have S3: "Col P Q X"
          using Col_perm P3 by blast
        have S4: "Col P Q Y"
          using Col_perm P4 by blast
        have S5: "Col A D X"
          by (simp add: P3 bet_col col_permutation_5)
        have "Col A D Y"
          by (metis Col_def P5 Q1 S5 Q0 between_equality between_trivial l6_16_1)
        then show ?thesis using S1 S3 S4 S5 P6 l6_21
          by blast
      qed
      then have "X Out A B"
        by (metis P1 P3 P4 TS_def l6_2)
      then show ?thesis using assms(1) P3 l9_5 by blast
    next
      assume Z1: "\<not> M = Y"
      have "X = Y"
      proof -
        have S1: "\<not> Col P Q A"
          using TS_def assms(1) not_col_permutation_1 by blast
        have S3: "Col P Q X"
          using Col_perm P3 by blast
        have S4: "Col P Q Y"
          using Col_perm P4 by blast
        have S5: "Col A D X"
          by (simp add: P3 bet_col col_permutation_5)
        have "Col A D Y"
          by (metis Col_def P4 Q0 P7 l6_16_1)
        then show ?thesis using S1 S3 S4 S5 P6 l6_21
          by blast
      qed
      then have Z3: "M \<noteq> X" using Z1 by blast
      have Z4: "P Q TS M C"
        by (meson Out_cases P4 P5 Tarski_neutral_dimensionless.l9_5 Tarski_neutral_dimensionless_axioms Z1 assms(1) bet_out)
      have "X Out M B"
        using P5 Z3 bet_out by auto
      then show ?thesis using Z4 P3 l9_5 by blast
    qed
  }
  then have Z99: "Col A B D \<longrightarrow> P Q TS B C" by blast
  {
    assume Q0: "\<not> Col A B D"
    have Q1: "P Q TS M C"
    proof -
      have S3: "Y Out A M"
      proof -
        have T1: "A \<noteq> Y"
          using Col_def P4 Q0 col_permutation_4 by blast
        have T2: "M \<noteq> Y"
        proof -
          {
            assume T3: "M = Y"
            have "Col B D X"
            proof -
              have U1: "B \<noteq> M"
                using P1 P4 T3 TS_def by blast
              have U2: "Col B M D"
                by (simp add: P4 T3 bet_col)
              have "Col B M X"
                by (simp add: P5 bet_col between_symmetry)
              then show ?thesis using U1 U2
                using col_transitivity_1 by blast
            qed
            have "False"
              by (metis NCol_cases P1 P3 TS_def \<open>Col B D X\<close> Q0 bet_col col_trivial_2 l6_21)
          }
          then show ?thesis by blast
        qed
        have "Bet Y A M \<or> Bet Y M A" using P5 by blast
        then show ?thesis using T1 T2
          by (simp add: Out_def)
      qed
      then have "X Out M B"
        by (metis P1 P3 P4 P5 TS_def bet_out l9_5)
      then show ?thesis using assms(1) S3 l9_5 P3 P4 by blast
    qed
    have "X Out M B"
      by (metis P3 P5 Q1 TS_def bet_out)
    then have "P Q TS B C" using Q1 P3 l9_5 by blast
  }
  then have "\<not> Col A B D \<longrightarrow> P Q TS B C" by blast
  then show ?thesis using Z99 by blast
qed

lemma l9_9:
  assumes "P Q TS A B"
  shows "\<not> P Q OS A B"
  using assms l9_8_2 not_two_sides_id by blast

lemma l9_9_bis:
  assumes "P Q OS A B"
  shows "\<not> P Q TS A B"
  using assms l9_9 by blast

lemma one_side_chara:
  assumes "P Q OS A B"
  shows "\<forall> X. Col X P Q \<longrightarrow> \<not> Bet A X B"
proof -
  have "\<not> Col A P Q \<and> \<not> Col B P Q"
    using OS_def TS_def assms by auto
  then show ?thesis
    using l9_9_bis TS_def assms by blast
qed

lemma l9_10:
  assumes "\<not> Col A P Q"
  shows "\<exists> C. P Q TS A C"
  by (meson Col_perm assms mid_two_sides midpoint_existence symmetric_point_construction)

lemma one_side_reflexivity:
  assumes "\<not> Col A P Q"
  shows "P Q OS A A"
  using assms l9_10 l9_8_1 by blast

lemma one_side_symmetry:
  assumes "P Q OS A B"
  shows "P Q OS B A"
  by (meson Tarski_neutral_dimensionless.OS_def Tarski_neutral_dimensionless_axioms assms invert_two_sides)

lemma one_side_transitivity:
  assumes "P Q OS A B" and
    "P Q OS B C"
  shows "P Q OS A C"
  by (meson Tarski_neutral_dimensionless.OS_def Tarski_neutral_dimensionless.l9_8_2 Tarski_neutral_dimensionless_axioms assms(1) assms(2))

lemma l9_17:
  assumes "P Q OS A C" and
    "Bet A B C"
  shows "P Q OS A B"
proof cases
  assume "A = C"
  then show ?thesis
    using assms(1) assms(2) between_identity by blast
next
  assume P1: "\<not> A = C"
  obtain D where P2: "P Q TS A D \<and> P Q TS C D"
    using OS_def assms(1) by blast
  then have P3: "P \<noteq> Q"
    using ts_distincts by blast
  obtain X where P4: "Col X P Q \<and> Bet A X D"
    using P2 TS_def by blast
  obtain Y where P5: "Col Y P Q \<and> Bet C Y D"
    using P2 TS_def by blast
  obtain T where P6: "Bet B T D \<and> Bet X T Y"
    using P4 P5 assms(2) l3_17 by blast
  have P7: "P Q TS A D"
    by (simp add: P2)
  have "P Q TS B D"
  proof -
    have Q1: "\<not> Col B P Q"
      using assms(1) assms(2) one_side_chara by blast
    have Q2: "\<not> Col D P Q"
      using P2 TS_def by blast
    obtain T0 where "Col T0 P Q \<and> Bet B T0 D"
    proof -
      assume a1: "\<And>T0. Col T0 P Q \<and> Bet B T0 D \<Longrightarrow> thesis"
      obtain pp :: 'p where
        f2: "Bet B pp D \<and> Bet X pp Y"
        using \<open>\<And>thesis. (\<And>T. Bet B T D \<and> Bet X T Y \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
      have "Col P Q Y"
        using Col_def P5 by blast
      then have "Y = X \<or> Col P Q pp"
        using f2 Col_def P4 colx by blast
      then show ?thesis
        using f2 a1 by (metis BetSEq BetS_def Col_def P4)
    qed
    then show ?thesis using Q1 Q2
      using TS_def by blast
  qed
  then show ?thesis using P7
    using OS_def by blast
qed

lemma l9_18_R1:
  assumes "Col X Y P" and
    "Col A B P"
    and "X Y TS A B"
  shows "Bet A P B \<and> \<not> Col X Y A \<and> \<not> Col X Y B"
  by (meson TS_def assms(1) assms(2) assms(3) col_permutation_5 l9_5 not_col_permutation_1 not_out_bet not_two_sides_id)

lemma l9_18_R2:
  assumes "Col X Y P" and
    "Col A B P" and
    "Bet A P B" and
    "\<not> Col X Y A" and
    "\<not> Col X Y B"
  shows "X Y TS A B"
  using Col_perm TS_def assms(1) assms(3) assms(4) assms(5) by blast

lemma l9_18:
  assumes "Col X Y P" and
    "Col A B P"
  shows "X Y TS A B \<longleftrightarrow> (Bet A P B \<and> \<not> Col X Y A \<and> \<not> Col X Y B)"
  using l9_18_R1 l9_18_R2 assms(1) assms(2) by blast

lemma l9_19_R1:
  assumes "Col X Y P" and
    "Col A B P" and
    "X Y OS A B"
  shows "P Out A B \<and> \<not> Col X Y A"
  by (meson OS_def TS_def assms(1) assms(2) assms(3) col_permutation_5 not_col_permutation_1 not_out_bet one_side_chara)

lemma l9_19_R2:
  assumes "Col X Y P" and
    (*    "Col A B P" and *)
    "P Out A B" and
    "\<not> Col X Y A"
  shows "X Y OS A B"
proof -
  obtain D where "X Y TS A D"
    using Col_perm assms(3) l9_10 by blast
  then show ?thesis
    using OS_def assms(1) assms(2) l9_5 not_col_permutation_1 by blast
qed

lemma l9_19:
  assumes "Col X Y P" and
    "Col A B P"
  shows "X Y OS A B \<longleftrightarrow> (P Out A B \<and> \<not> Col X Y A)"
  using l9_19_R1 l9_19_R2 assms(1) assms(2) by blast

lemma one_side_not_col123:
  assumes "A B OS X Y"
  shows "\<not> Col A B X"
  using assms col_trivial_3 l9_19 by blast

lemma one_side_not_col124:
  assumes "A B OS X Y"
  shows "\<not> Col A B Y"
  using assms one_side_not_col123 one_side_symmetry by blast

lemma col_two_sides:
  assumes "Col A B C" and
    "A \<noteq> C" and
    "A B TS P Q"
  shows "A C TS P Q"
  using assms(1) assms(2) assms(3) col_preserves_two_sides col_trivial_3 by blast

lemma col_one_side:
  assumes "Col A B C" and
    "A \<noteq> C" and
    "A B OS P Q"
  shows "A C OS P Q"
proof -
  obtain T where "A B TS P T \<and> A B TS Q T" using assms(1) assms(2) assms(3) OS_def by blast
  then show ?thesis
    using col_two_sides OS_def assms(1) assms(2) by blast
qed


lemma out_out_one_side:
  assumes "A B OS X Y" and
    "A Out Y Z"
  shows "A B OS X Z"
  by (meson Col_cases Tarski_neutral_dimensionless.OS_def Tarski_neutral_dimensionless_axioms assms(1) assms(2) col_trivial_3 l9_5)

lemma out_one_side:
  assumes "\<not> Col A B X \<or> \<not> Col A B Y" and
    "A Out X Y"
  shows "A B OS X Y"
  using assms(1) assms(2) l6_6 not_col_permutation_2 one_side_reflexivity one_side_symmetry out_out_one_side by blast

lemma bet__ts:
  assumes "A \<noteq> Y" and
    "\<not> Col A B X" and
    "Bet X A Y"
  shows "A B TS X Y"
proof -
  have "\<not> Col Y A B"
    using NCol_cases assms(1) assms(2) assms(3) bet_col col2__eq by blast
  then show ?thesis
    by (meson TS_def assms(2) assms(3) col_permutation_3 col_permutation_5 col_trivial_3)
qed

lemma bet_ts__ts:
  assumes "A B TS X Y" and
    "Bet X Y Z"
  shows "A B TS X Z"
proof -
  have "\<not> Col Z A B"
    using assms(1) assms(2) bet_col between_equality_2 col_permutation_1 l9_18 by blast
  then show ?thesis
    using TS_def assms(1) assms(2) between_exchange4 by blast
qed

lemma bet_ts__os:
  assumes "A B TS X Y" and
    "Bet X Y Z"
  shows "A B OS Y Z"
  using OS_def assms(1) assms(2) bet_ts__ts l9_2 by blast

lemma l9_31 :
  assumes "A X OS Y Z" and
    "A Z OS Y X"
  shows "A Y TS X Z"
proof -
  have P1: "A \<noteq> X \<and> A \<noteq> Z \<and> \<not> Col Y A X \<and> \<not> Col Z A X \<and> \<not> Col Y A Z"
    using assms(1) assms(2) col_permutation_1 one_side_not_col123 one_side_not_col124 os_distincts by blast
  obtain Z' where P2: "Bet Z A Z' \<and> Cong A Z' Z A"
    using segment_construction by blast
  have P3: "Z' \<noteq> A"
    using P1 P2 cong_diff_4 by blast
  have P4: "A X TS Y Z'"
    by (metis (no_types) P2 P3 assms(1) bet__ts l9_8_2 one_side_not_col124 one_side_symmetry)
  have P5: "\<not> Col Y A X"
    using P1 by blast
  obtain T where P6: "Col A T X \<and> Bet Y T Z'"
    using P4 TS_def not_col_permutation_4 by blast
  then have P7: "T \<noteq> A"
  proof -
    have "\<not> Col A Z Y"
      by (simp add: P1 not_col_permutation_1)
    then have f1: "\<not> A Out Z Y"
      using out_col by blast
    have "A \<noteq> Z'"
      using P1 P2 cong_diff_4 by blast
    then show ?thesis
      using f1 by (metis (no_types) P1 P2 P6 l6_2)
  qed
  have P8: "Y A OS Z' T"
    by (smt P1 P2 P3 P6 Tarski_neutral_dimensionless.l6_6 Tarski_neutral_dimensionless_axioms bet_col bet_out col_trivial_2 l6_21 not_col_permutation_1 out_one_side)
  have P9: "A Y TS Z' Z"
    using Col_perm P1 P2 P8 bet__ts between_symmetry one_side_not_col123 by blast
  {
    assume Q0: "Bet T A X"
    have Q1: "Z' Z OS Y T"
      by (metis BetSEq BetS_def P1 P2 P4 P6 TS_def Tarski_neutral_dimensionless.l6_6 Tarski_neutral_dimensionless_axioms bet_col bet_out_1 col_trivial_3 colx not_col_permutation_3 not_col_permutation_4 out_one_side)
    then have Q2: "Z' Out T Y"
      by (metis P6 bet_out_1 os_distincts)
    then have Q3: "A Z OS Y T"
      by (meson Out_cases P1 P2 P6 bet_col col_permutation_3 invert_one_side l9_19_R2)
    have "A Z TS X T"
    proof -
      have R1: "\<not> Col X A Z"
        using P1 col_permutation_3 by blast
      have R2: "\<not> Col T A Z"
        using Q3 between_trivial one_side_chara by blast
      have "\<exists> T0. Col T0 A Z \<and> Bet X T0 T"
      proof -
        have S1: "Col A A Z"
          by (simp add: col_trivial_1)
        have "Bet X A T"
          by (simp add: Q0 between_symmetry)
        then show ?thesis using S1 by blast
      qed
      then show ?thesis using R1 R2
        using TS_def by auto
    qed
    have "A Y TS X Z"
      by (meson Q3 Tarski_neutral_dimensionless.l9_8_2 Tarski_neutral_dimensionless.one_side_symmetry Tarski_neutral_dimensionless_axioms \<open>A Z TS X T\<close> assms(2) l9_9_bis)
  }
  then have P10: "Bet T A X \<longrightarrow> A Y TS X Z" by blast
  {
    assume R1: "Bet A X T"
    then have R3: "A Y OS Z' X"
      by (meson Bet_cases P1 P6 P8 R1 between_equality invert_one_side not_col_permutation_4 not_out_bet out_out_one_side)
    have "A Y TS X Z"
      using R3 P9 l9_8_2 by blast
  }
  then have P11: "Bet A X T \<longrightarrow> A Y TS X Z" by blast
  {
    assume R1: "Bet X T A"
    then have R3: "A Y OS T X"
      by (simp add: P5 P7 R1 bet_out_1 not_col_permutation_4 out_one_side)
    then have "A Y TS X Z"
      using P8 P9 invert_two_sides l9_8_2 by blast
  }
  then have "Bet X T A \<longrightarrow> A Y TS X Z" by blast
  then show ?thesis using P10 P11
    using P6 between_symmetry third_point by blast
qed

lemma col123__nos:
  assumes "Col P Q A"
  shows "\<not> P Q OS A B"
  using assms one_side_not_col123 by blast

lemma col124__nos:
  assumes "Col P Q B"
  shows "\<not> P Q OS A B"
  using assms one_side_not_col124 by blast

lemma col2_os__os:
  assumes "C \<noteq> D" and
    "Col A B C" and
    "Col A B D" and
    "A B OS X Y"
  shows "C D OS X Y"
  by (metis assms(1) assms(2) assms(3) assms(4) col3 col_one_side col_trivial_3 invert_one_side os_distincts)

lemma os_out_os:
  assumes "Col A B P" and
    "A B OS C D" and
    "P Out C C'"
  shows "A B OS C' D"
  using OS_def assms(1) assms(2) assms(3) l9_5 not_col_permutation_1 by blast

lemma ts_ts_os:
  assumes "A B TS C D" and
    "C D TS A B"
  shows "A C OS B D"
proof -
  obtain T1 where P1: "Col T1 A B \<and> Bet C T1 D"
    using TS_def assms(1) by blast
  obtain T where P2: "Col T C D \<and> Bet A T B"
    using TS_def assms(2) by blast
  have P3: "T1 = T"
  proof -
    have "A \<noteq> B"
      using assms(2) ts_distincts by blast
    then show ?thesis
    proof -
      have "Col T1 D C"
        using Col_def P1 by blast
      then have f1: "\<forall>p. (C = T1 \<or> Col C p T1) \<or> \<not> Col C T1 p"
        by (metis assms(1) col_transitivity_1 l6_16_1 ts_distincts)
      have f2: "\<not> Col C A B"
        using TS_def assms(1) by presburger
      have f3: "(Bet B T1 A \<or> Bet T1 A B) \<or> Bet A B T1"
        using Col_def P1 by blast
      {
        assume "T1 \<noteq> B"
        then have "C \<noteq> T1 \<and> \<not> Col C T1 B \<or> (\<exists>p. \<not> Col p T1 B \<and> Col p T1 T) \<or> T \<noteq> A \<and> T \<noteq> B"
          using f3 f2 by (metis (no_types) Col_def col_transitivity_1 l6_16_1)
        then have "T \<noteq> A \<and> T \<noteq> B \<or> C \<noteq> T1 \<and> \<not> Col C T1 T \<or> T1 = T"
          using f3 by (meson Col_def l6_16_1)
      }
      moreover
      {
        assume "T \<noteq> A \<and> T \<noteq> B"
        then have "C \<noteq> T1 \<and> \<not> Col C T1 T \<or> T1 = T"
          using f2 by (metis (no_types) Col_def P1 P2 \<open>A \<noteq> B\<close> col_transitivity_1 l6_16_1)
      }
      ultimately have "C \<noteq> T1 \<and> \<not> Col C T1 T \<or> T1 = T"
        using f2 f1 assms(1) ts_distincts by blast
      then show ?thesis
        by (metis (no_types) Col_def P1 P2 assms(1) l6_16_1 ts_distincts)
    qed
  qed
  have P4: "A C OS T B"
    by (metis Col_cases P2 TS_def assms(1) assms(2) bet_out out_one_side)
  then have "C A OS T D"
    by (metis Col_cases P1 TS_def P3 assms(2) bet_out os_distincts out_one_side)
  then show ?thesis
    by (meson P4 Tarski_neutral_dimensionless.invert_one_side Tarski_neutral_dimensionless.one_side_symmetry Tarski_neutral_dimensionless_axioms one_side_transitivity)
qed

lemma col_one_side_out:
  assumes "Col A X Y" and
    "A B OS X Y"
  shows "A Out X Y"
  by (meson assms(1) assms(2) l6_4_2 not_col_distincts not_col_permutation_4 one_side_chara)

lemma col_two_sides_bet:
  assumes "Col A X Y" and
    "A B TS X Y"
  shows "Bet X A Y"
  using Col_cases assms(1) assms(2) l9_8_1 l9_9 or_bet_out out_out_one_side by blast

lemma os_ts1324__os:
  assumes "A X OS Y Z" and
    "A Y TS X Z"
  shows "A Z OS X Y"
proof -
  obtain P where P1: "Col P A Y \<and> Bet X P Z"
    using TS_def assms(2) by blast
  have P2: "A Z OS X P"
    by (metis Col_cases P1 TS_def assms(1) assms(2) bet_col bet_out_1 col124__nos col_trivial_2 l6_6 l9_19)
  have "A Z OS P Y"
  proof -
    have "\<not> Col A Z P \<or> \<not> Col A Z Y"
      using P2 col124__nos by blast
    moreover have "A Out P Y"
    proof -
      have "X A OS P Z"
        by (metis Col_cases P1 P2 assms(1) bet_out col123__nos out_one_side)
      then have "A X OS P Y"
        by (meson Tarski_neutral_dimensionless.invert_one_side Tarski_neutral_dimensionless.one_side_symmetry Tarski_neutral_dimensionless_axioms assms(1) one_side_transitivity)
      then show ?thesis
        using P1 col_one_side_out not_col_permutation_4 by blast
    qed
    ultimately show ?thesis
      by (simp add: out_one_side)
  qed
  then show ?thesis
    using P2 one_side_transitivity by blast
qed

lemma ts2__ex_bet2:
  assumes "A C TS B D" and
    "B D TS A C"
  shows "\<exists> X. Bet A X C \<and> Bet B X D"
  by (metis TS_def assms(1) assms(2) bet_col col_permutation_5 l9_18_R1 not_col_permutation_2)

lemma out_one_side_1:
  assumes "\<not> Col A B C" and
    "Col A B X" and
    "X Out C D"
  shows "A B OS C D"
  using assms(1) assms(2) assms(3) not_col_permutation_2 one_side_reflexivity one_side_symmetry os_out_os by blast

lemma out_two_sides_two_sides:
  assumes (*"A \<noteq> PX" and *)
    "Col A B PX" and
    "PX Out X P" and
    "A B TS P Y"
  shows "A B TS X Y"
  using assms(1) assms(2) assms(3) l6_6 l9_5 not_col_permutation_1 by blast

lemma l8_21_bis:
  assumes "X \<noteq> Y" and
    "\<not> Col C A B"
  shows "\<exists> P. Cong A P X Y \<and> A B Perp P A \<and> A B TS C P"
proof -
  have P1: "A \<noteq> B"
    using assms(2) not_col_distincts by blast
  then have "\<exists> P T. A B Perp P A \<and> Col A B T \<and> Bet C T P"
    using l8_21 by auto
  then obtain P T where P2: "A B Perp P A \<and> Col A B T \<and> Bet C T P" by blast
  have P3: "A B TS C P"
  proof -
    have "\<not> Col P A B"
      using P2 col_permutation_1 perp_not_col by blast
    then show ?thesis
      using P2 TS_def assms(2) not_col_permutation_1 by blast
  qed
  have P4: "P \<noteq> A"
    using P3 ts_distincts by blast
  obtain P' where P5: "(Bet A P P' \<or> Bet A P' P) \<and> Cong A P' X Y"
    using segment_construction_2 P4 by blast
  have P6: "A B Perp P' A"
    by (smt P2 P5 Perp_perm assms(1) bet_col cong_identity cong_symmetry not_bet_distincts not_col_permutation_2 perp_col2)
  have P7: "\<not> Col P' A B"
    using NCol_perm P6 col_trivial_3 l8_16_1 by blast
  then have P8: "A B OS P P'"
    by (metis Out_def P4 P5 P6 col_permutation_2 out_one_side perp_not_eq_2)
  then have P9: "A B TS C P'"
    using P3 l9_2 l9_8_2 by blast
  then show ?thesis
    using P5 P6 by blast
qed

lemma ts__ncol:
  assumes "A B TS X Y"
  shows  "\<not> Col A X Y \<or> \<not> Col B X Y"
  by (metis TS_def assms col_permutation_1 col_transitivity_2 ts_distincts)

lemma one_or_two_sides_aux:
  assumes "\<not> Col C A B" and
    "\<not> Col D A B" and
    "Col A C X"
    and "Col B D X"
  shows "A B TS C D \<or> A B OS C D"
proof -
  have P1: "A \<noteq> X"
    using assms(2) assms(4) col_permutation_2 by blast
  have P2: "B \<noteq> X"
    using assms(1) assms(3) col_permutation_4 by blast
  have P3: "\<not> Col X A B"
    using P1 assms(1) assms(3) col_permutation_5 col_transitivity_1 not_col_permutation_4 by blast
  {
    assume Q0: "Bet A C X \<and> Bet B D X"
    then have Q1: "A B OS C X"
      using assms(1) bet_out not_col_distincts not_col_permutation_1 out_one_side by blast
    then have "A B OS X D"
      by (metis Q0 assms(2) assms(4) bet_out_1 col_permutation_2 col_permutation_3 invert_one_side l6_4_2 not_bet_and_out not_col_distincts out_one_side)
    then have "A B OS C D"
      using Q1 one_side_transitivity by blast
  }
  then have P4: "Bet A C X \<and> Bet B D X \<longrightarrow> A B OS C D" by blast
  {
    assume "Bet A C X \<and> Bet D X B"
    then have "A B OS C D"
      by (smt P2 assms(1) assms(4) bet_out between_equality_2 l9_10 l9_5 l9_8_1 not_bet_and_out not_col_distincts not_col_permutation_4 out_to_bet out_two_sides_two_sides)
  }
  then have P5: "Bet A C X \<and> Bet D X B \<longrightarrow> A B OS C D " by blast
  {
    assume Q0: "Bet A C X \<and> Bet X B D"
    have Q1: "A B TS X D"
      using P3 Q0 TS_def assms(2) col_trivial_3 by blast
    have "A B OS X C"
      using Q0 assms(1) bet_out not_col_distincts one_side_reflexivity one_side_symmetry out_out_one_side by blast
    then have "A B TS C D"
      using Q1 l9_8_2 by blast
  }
  then have P6: "Bet A C X \<and> Bet X B D \<longrightarrow> A B TS C D" by blast
  {
    assume Q1: "Bet C X A \<and> Bet B D X"
    then have Q2: "A B OS C X"
      using P1 assms(1) assms(3) between_equality_2 l6_4_2 not_col_permutation_1 not_col_permutation_4 out_one_side by blast
    have "A B OS X D"
      using Q1 assms(2) bet_out not_col_distincts one_side_reflexivity os_out_os by blast
    then have "A B OS C D" using Q2
      using one_side_transitivity by blast
  }
  then have P7: "Bet C X A \<and> Bet B D X \<longrightarrow> A B OS C D" by blast
  {
    assume "Bet C X A \<and> Bet D X B"
    then have "A B OS C D"
      by (smt \<open>Bet A C X \<and> Bet D X B \<Longrightarrow> A B OS C D\<close> \<open>Bet C X A \<and> Bet B D X \<Longrightarrow> A B OS C D\<close> assms(1) assms(2) assms(3) assms(4) between_symmetry l6_21 l9_18_R2 not_col_distincts ts_ts_os)
  }
  then have P8: "Bet C X A \<and> Bet D X B \<longrightarrow> A B OS C D" by blast
  {
    assume Q1: "Bet C X A \<and> Bet X B D"
    have Q2: "A B TS X D"
      by (metis P3 Q1 assms(2) bet__ts invert_two_sides not_col_distincts not_col_permutation_3)
    have Q3: "A B OS X C"
      using P1 Q1 assms(1) bet_out_1 not_col_permutation_1 out_one_side by auto
    then have "A B TS C D"
      using Q2 l9_8_2 by blast
  }
  then have P9: "Bet C X A \<and> Bet X B D \<longrightarrow> A B TS C D" by blast
  {
    assume Q0: "Bet X A C \<and> Bet B D X"
    have Q1: "A B TS X C"
      by (metis P3 Q0 assms(1) bet__ts col_permutation_2 not_col_distincts)
    have "A B OS X D"
      by (metis NCol_cases Q0 Tarski_neutral_dimensionless.out_one_side Tarski_neutral_dimensionless_axioms assms(2) assms(4) bet_out_1 invert_one_side l6_4_1 not_col_distincts not_out_bet)
    then have "A B TS C D"
      using Q1 l9_2 l9_8_2 by blast
  }
  then have P10: "Bet X A C \<and> Bet B D X \<longrightarrow> A B TS C D" by blast
  {
    assume Q0: "Bet X A C \<and> Bet D X B"
    have Q1: "A B TS X C"
      by (metis NCol_cases P3 Q0 assms(1) bet__ts not_col_distincts)
    have "A B OS X D"
      by (metis P2 P3 Q0 bet_out_1 col_permutation_3 invert_one_side out_one_side)
    then have "A B TS C D"
      using Q1 l9_2 l9_8_2 by blast
  }
  then have P11: "Bet X A C \<and> Bet D X B \<longrightarrow> A B TS C D"
    by blast
  {
    assume Q0: "Bet X A C \<and> Bet X B D"
    then have Q1: "A B TS C X"
      by (simp add: P1 Q0 assms(1) bet__ts between_symmetry not_col_permutation_1)
    have "A B TS D X"
      by (simp add: P2 Q0 assms(2) bet__ts between_symmetry invert_two_sides not_col_permutation_3)
    then have "A B OS C D"
      using Q1 l9_8_1 by blast
  }
  then have P12: "Bet X A C \<and> Bet X B D \<longrightarrow> A B OS C D" by blast
  then show ?thesis using P4 P5 P6 P7 P8 P9 P10 P11
    using Col_def assms(3) assms(4) by auto
qed

lemma cop__one_or_two_sides:
  assumes "Coplanar A B C D" and
    "\<not> Col C A B" and
    "\<not> Col D A B"
  shows "A B TS C D \<or> A B OS C D"
proof -
  obtain X where P1: "Col A B X \<and> Col C D X \<or> Col A C X \<and> Col B D X \<or> Col A D X \<and> Col B C X"
    using Coplanar_def assms(1) by auto
  have P2: "Col A B X \<and> Col C D X \<longrightarrow> A B TS C D \<or> A B OS C D"
    by (metis TS_def Tarski_neutral_dimensionless.l9_19_R2 Tarski_neutral_dimensionless_axioms assms(2) assms(3) not_col_permutation_3 not_col_permutation_5 not_out_bet)
  have P3: "Col A C X \<and> Col B D X \<longrightarrow>  A B TS C D \<or> A B OS C D"
    using assms(2) assms(3) one_or_two_sides_aux by blast
  have "Col A D X \<and> Col B C X \<longrightarrow>  A B TS C D \<or> A B OS C D"
    using assms(2) assms(3) l9_2 one_or_two_sides_aux one_side_symmetry by blast
  then show ?thesis
    using P1 P2 P3 by blast
qed

lemma os__coplanar:
  assumes "A B OS C D"
  shows "Coplanar A B C D"
proof -
  have P1: "\<not> Col A B C"
    using assms one_side_not_col123 by blast
  obtain C' where P2: "Bet C B C' \<and> Cong B C' B C"
    using segment_construction by presburger
  have P3: "A B TS D C'"
    by (metis (no_types) Cong_perm OS_def P2 TS_def assms bet__ts bet_cong_eq invert_one_side l9_10 l9_8_2 one_side_not_col123 ts_distincts)
  obtain T where P4: "Col T A B \<and> Bet D T C'"
    using P3 TS_def by blast
  have P5: "C' \<noteq> T"
    using P3 P4 TS_def by blast
  have P6: "Col T B C \<longrightarrow> Coplanar A B C D"
    by (metis Col_def Coplanar_def P2 P4 P5 col_trivial_2 l6_16_1)
  {
    assume Q0: "\<not> Col T B C"
    {
      assume R0: "Bet T B A"
      have S1: "B C TS T A"
        by (metis P1 Q0 R0 bet__ts col_permutation_2 not_col_distincts)
      have "C' Out T D"
        using P4 P5 bet_out_1 by auto
      then have "B C OS T D"
        using P2 Q0 bet_col invert_one_side not_col_permutation_3 out_one_side_1 by blast
      then have R1: "B C TS D A"
        using S1 l9_8_2 by blast
      then have "Coplanar A B C D"
        using ncoplanar_perm_9 ts__coplanar by blast
    }
    then have Q1: "Bet T B A \<longrightarrow> Coplanar A B C D" by blast
    {
      assume R0: "\<not> Bet T B A"
      {
        have R2: "B C OS D T"
        proof -
          have S1: "\<not> Col B C D"
            by (metis Col_perm P2 P3 P4 Q0 bet_col colx ts_distincts)
          have S2: "Col B C C'"
            by (simp add: P2 bet_col col_permutation_4)
          have S3: "C' Out D T"
            using P4 P5 bet_out_1 l6_6 by auto
          then show ?thesis
            using S1 S2 out_one_side_1 by blast
        qed

        have R3: "B C OS T A"
          using P4 Q0 R0 col_permutation_2 col_permutation_5 not_bet_out out_one_side by blast
      }
      then have R1: "B C OS D A"
        by (metis P2 P4 Q0 bet_col bet_out_1 col_permutation_2 col_permutation_5 os_out_os)
      then have "Coplanar A B C D"
        by (simp add: R1 assms coplanar_perm_19 invert_one_side l9_31 one_side_symmetry ts__coplanar)
    }
    then have "\<not> Bet T B A \<longrightarrow> Coplanar A B C D" by blast
    then have "Coplanar A B C D" using Q1 by blast
  }
  then have "\<not> Col T B C \<longrightarrow> Coplanar A B C D" by blast
  then show ?thesis using P6 by blast
qed

lemma coplanar_trans_1:
  assumes "\<not> Col P Q R" and
    "Coplanar P Q R A" and
    "Coplanar P Q R B"
  shows "Coplanar Q R A B"
proof -
  have P1: "Col Q R A \<longrightarrow> Coplanar Q R A B"
    by (simp add: col__coplanar)
  {
    assume T1: "\<not> Col Q R A"
    {
      assume T2: "\<not> Col Q R B"
      {
        have "Col Q A B \<longrightarrow> Coplanar Q R A B"
          using ncop__ncols by blast
        {
          assume S1: "\<not> Col Q A B"
          have U1: "Q R TS P A \<or> Q R OS P A"
            by (simp add: T1 assms(1) assms(2) cop__one_or_two_sides coplanar_perm_8 not_col_permutation_2)
          have U2: "Q R TS P B \<or> Q R OS P B"
            using T2 assms(1) assms(3) col_permutation_1 cop__one_or_two_sides coplanar_perm_8 by blast
          have W1: "Q R TS P A \<and> Q R OS P A \<longrightarrow> Q R TS A B \<or> Q R OS A B"
            using l9_9 by blast
          have W2: "Q R TS P A \<and> Q R OS P B \<longrightarrow> Q R TS A B \<or> Q R OS A B"
            using l9_2 l9_8_2 by blast
          have W3: "Q R TS P B \<and> Q R OS P A \<longrightarrow> Q R TS A B \<or> Q R OS A B"
            using l9_8_2 by blast
          have "Q R TS P B \<and> Q R OS P B \<longrightarrow> Q R TS A B \<or> Q R OS A B"
            using l9_9 by blast
          then have S2: "Q R TS A B \<or> Q R OS A B" using U1 U2 W1 W2 W3
            using OS_def l9_2 one_side_transitivity by blast
          have "Coplanar Q R A B"
            using S2 os__coplanar ts__coplanar by blast
        }
        then have "\<not> Col Q A B \<longrightarrow> Coplanar Q R A B" by blast
      }
      then have "Coplanar Q R A B"
        using ncop__ncols by blast
    }
    then have "\<not> Col Q R B \<longrightarrow> Coplanar Q R A B"
      by blast
  }
  then have "\<not> Col Q R A \<longrightarrow> Coplanar Q R A B"
    using ncop__ncols by blast
  then show ?thesis using P1 by blast
qed

lemma col_cop__cop:
  assumes "Coplanar A B C D" and
    "C \<noteq> D" and
    "Col C D E"
  shows "Coplanar A B C E"
proof -
  have "Col D A C \<longrightarrow> Coplanar A B C E"
    by (meson assms(2) assms(3) col_permutation_1 l6_16_1 ncop__ncols)
  moreover
  {
    assume "\<not> Col D A C"
    then have "Coplanar A C B E"
      by (meson assms(1) assms(3) col__coplanar coplanar_trans_1 ncoplanar_perm_11 ncoplanar_perm_13)
    then have "Coplanar A B C E"
      using ncoplanar_perm_2 by blast
  }
  ultimately show ?thesis
    by blast
qed

lemma bet_cop__cop:
  assumes "Coplanar A B C E" and
    "Bet C D E"
  shows "Coplanar A B C D"
  by (metis NCol_perm Tarski_neutral_dimensionless.col_cop__cop Tarski_neutral_dimensionless_axioms assms(1) assms(2) bet_col bet_neq12__neq)

lemma col2_cop__cop:
  assumes "Coplanar A B C D" and
    "C \<noteq> D" and
    "Col C D E" and
    "Col C D F"
  shows "Coplanar A B E F"
proof cases
  assume "C = E"
  then show ?thesis
    using assms(1) assms(2) assms(4) col_cop__cop by blast
next
  assume "C \<noteq> E"
  then show ?thesis
    by (metis assms(1) assms(2) assms(3) assms(4) col_cop__cop col_transitivity_1 ncoplanar_perm_1 not_col_permutation_4)
qed

lemma col_cop2__cop:
  assumes "U \<noteq> V" and
    "Coplanar A B C U" and
    "Coplanar A B C V" and
    "Col U V P"
  shows "Coplanar A B C P"
proof cases
  assume "Col A B C"
  then show ?thesis
    using ncop__ncol by blast
next
  assume "\<not> Col A B C"
  then show ?thesis
    by (smt Col_perm assms(1) assms(2) assms(3) assms(4) col_cop__cop coplanar_trans_1 ncoplanar_perm_1 ncoplanar_perm_14 ncoplanar_perm_15 ncoplanar_perm_23)
qed

lemma bet_cop2__cop:
  assumes "Coplanar A B C U" and
    "Coplanar A B C W" and
    "Bet U V W"
  shows "Coplanar A B C V"
proof -
  have "Col U V W"
    using assms(3) bet_col by blast
  then have "Col U W V"
    by (meson not_col_permutation_5)
  then show ?thesis
    using assms(1) assms(2) assms(3) bet_neq23__neq col_cop2__cop by blast
qed

lemma coplanar_pseudo_trans:
  assumes "\<not> Col P Q R" and
    "Coplanar P Q R A" and
    "Coplanar P Q R B" and
    "Coplanar P Q R C" and
    "Coplanar P Q R D"
  shows "Coplanar A B C D"
proof cases
  have LEM1: "(\<not> Col P Q R \<and> Coplanar P Q R A \<and> Coplanar P Q R B \<and> Coplanar P Q R C) \<longrightarrow> Coplanar A B C R"
    by (smt col_transitivity_2 coplanar_trans_1 ncop__ncols ncoplanar_perm_19 ncoplanar_perm_21)
  assume P2: "Col P Q D"
  have P3: "P \<noteq> Q"
    using assms(1) col_trivial_1 by blast
  have P4: "Coplanar A B C Q"
    by (smt assms(1) assms(2) assms(3) assms(4) col2_cop__cop coplanar_trans_1 ncoplanar_perm_9 not_col_distincts)
  have P5: "\<not> Col Q R P"
    using Col_cases assms(1) by blast
  have P6: "Coplanar Q R P A"
    using assms(2) ncoplanar_perm_12 by blast
  have P7: "Coplanar Q R P B"
    using assms(3) ncoplanar_perm_12 by blast
  have P8: "Coplanar Q R P C"
    using assms(4) ncoplanar_perm_12 by blast
  then have "Coplanar A B C P" using LEM1 P5 P6 P7
    by (smt col_transitivity_2 coplanar_trans_1 ncop__ncols ncoplanar_perm_19)
  then show ?thesis
    using LEM1 P2 P3 P4 col_cop2__cop by blast
next
  assume P9: "\<not> Col P Q D"
  have P10: "Coplanar P Q D A"
    using NCol_cases assms(1) assms(2) assms(5) coplanar_trans_1 ncoplanar_perm_8 by blast
  have P11: "Coplanar P Q D B"
    using assms(1) assms(3) assms(5) col_permutation_1 coplanar_perm_12 coplanar_trans_1 by blast
  have "Coplanar P Q D C"
    by (meson assms(1) assms(4) assms(5) coplanar_perm_7 coplanar_trans_1 ncoplanar_perm_14 not_col_permutation_3)
  then show ?thesis using P9 P10 P11
    by (smt P10 P11 P9 col3 coplanar_trans_1 ncop__ncol ncoplanar_perm_20 ncoplanar_perm_23 not_col_distincts)
qed

lemma l9_30:
  assumes "\<not> Coplanar A B C P" and
    "\<not> Col D E F" and
    "Coplanar D E F P" and
    "Coplanar A B C X" and
    "Coplanar A B C Y" and
    "Coplanar A B C Z" and
    "Coplanar D E F X" and
    "Coplanar D E F Y" and
    "Coplanar D E F Z"
  shows "Col X Y Z"
proof -
  {
    assume P1: "\<not> Col X Y Z"
    have P2: "\<not> Col A B C"
      using assms(1) col__coplanar by blast
    have "Coplanar A B C P"
    proof -
      have Q2: "Coplanar X Y Z A"
        by (smt P2 assms(4) assms(5) assms(6) col2_cop__cop coplanar_trans_1 ncoplanar_perm_18 not_col_distincts)
      have Q3: "Coplanar X Y Z B"
        using P2 assms(4) assms(5) assms(6) col_trivial_3 coplanar_pseudo_trans ncop__ncols by blast
      have Q4: "Coplanar X Y Z C"
        using P2 assms(4) assms(5) assms(6) col_trivial_2 coplanar_pseudo_trans ncop__ncols by blast
      have "Coplanar X Y Z P"
        using assms(2) assms(3) assms(7) assms(8) assms(9) coplanar_pseudo_trans by blast
      then show ?thesis using P1 Q2 Q3 Q4
        using assms(2) assms(3) assms(7) assms(8) assms(9) coplanar_pseudo_trans by blast
    qed
    then have "False" using assms(1) by blast
  }
  then show ?thesis by blast
qed

lemma cop_per2__col:
  assumes "Coplanar A X Y Z" and
    "A \<noteq> Z" and
    "Per X Z A" and
    "Per Y Z A"
  shows "Col X Y Z"
proof cases
  assume "X = Y \<or> X = Z \<or> Y = Z"
  then show ?thesis
    using not_col_distincts by blast
next
  assume H1:"\<not> (X = Y \<or> X = Z \<or> Y = Z)"
  obtain B where P1: "Cong X A X B \<and> Z Midpoint A B \<and> Cong Y A Y B"
    using Per_def assms(3) assms(4) per_double_cong by blast
  have P2: "X \<noteq> Y"
    using H1 by blast
  have P3: "X \<noteq> Z"
    using H1 by blast
  have P4: "Y \<noteq> Z"
    using H1 by blast
  obtain I where P5: " Col A X I \<and> Col Y Z I \<or>
     Col A Y I \<and> Col X Z I \<or> Col A Z I \<and> Col X Y I"
    using Coplanar_def assms(1) by auto
  have P6: "Col A X I \<and> Col Y Z I \<longrightarrow> Col X Y Z"
    by (smt P1 P4 assms(2) l4_17 l4_18 l7_13 l7_2 l7_3_2 midpoint_distinct_2 not_col_permutation_1)
  have P7: "Col A Y I \<and> Col X Z I \<longrightarrow> Col X Y Z"
    by (smt P1 P3 assms(2) col_permutation_1 col_permutation_5 l4_17 l4_18 l7_13 l7_2 l7_3_2 midpoint_distinct_2)
  have "Col A Z I \<and> Col X Y I \<longrightarrow> Col X Y Z"
    by (metis P1 P2 assms(2) col_permutation_1 l4_17 l4_18 l7_13 l7_2 l7_3_2 midpoint_distinct_2)
  then show ?thesis
    using P5 P6 P7 by blast
qed

lemma cop_perp2__col:
  assumes "Coplanar A B Y Z" and
    "X Y Perp A B" and
    "X Z Perp A B"
  shows "Col X Y Z"
proof cases
  assume P1: "Col A B X"
  {
    assume Q0: "X = A"
    then have Q1: "X \<noteq> B"
      using assms(3) perp_not_eq_2 by blast
    have Q2: "Coplanar B Y Z X"
      by (simp add: Q0 assms(1) coplanar_perm_9)
    have Q3: "Per Y X B"
      using Q0 assms(2) perp_per_2 by blast
    have "Per Z X B"
      using Q0 assms(3) perp_per_2 by blast
    then have "Col X Y Z"
      using Q1 Q2 Q3 cop_per2__col not_col_permutation_1 by blast
  }
  then have P2: "X = A \<longrightarrow> Col X Y Z" by blast
  {
    assume Q0: "X \<noteq> A"
    have Q1: "A X Perp X Y"
      by (metis P1 Perp_perm Q0 assms(2) perp_col1)
    have Q2: "A X Perp X Z"
      by (metis P1 Perp_perm Q0 assms(3) perp_col1)
    have Q3: "Coplanar A Y Z X"
      by (smt P1 assms(1) assms(2) col2_cop__cop col_trivial_3 coplanar_perm_12 coplanar_perm_16 perp_distinct)
    have Q4: "Per Y X A"
      using Perp_perm Q1 perp_per_2 by blast
    have "Per Z X A"
      using P1 Q0 assms(3) perp_col1 perp_per_1 by auto
    then have "Col X Y Z"
      using Q0 Q3 Q4 cop_per2__col not_col_permutation_1 by blast
  }
  then have "X \<noteq> A \<longrightarrow> Col X Y Z" by blast
  then show ?thesis
    using P2 by blast
next
  assume P1: "\<not> Col A B X"
  obtain Y0 where P2: "Y0 PerpAt X Y A B"
    using Perp_def assms(2) by blast
  obtain Z0 where P3: "Z0 PerpAt X Z A B"
    using Perp_def assms(3) by auto
  have P4: "X Y0 Perp A B"
    by (metis P1 P2 assms(2) perp_col perp_in_col)
  have P5: "X Z0 Perp A B"
    by (metis P1 P3 assms(3) perp_col perp_in_col)
  have P6: "Y0 = Z0"
    by (meson P1 P2 P3 P4 P5 Perp_perm l8_18_uniqueness perp_in_col)
  have P7: "X \<noteq> Y0"
    using P4 perp_not_eq_1 by blast
  have P8: "Col X Y0 Y"
    using P2 col_permutation_5 perp_in_col by blast
  have "Col X Y0 Z"
    using P3 P6 col_permutation_5 perp_in_col by blast
  then show ?thesis
    using P7 P8 col_transitivity_1 by blast
qed

lemma two_sides_dec:
  shows "A B TS C D \<or> \<not> A B TS C D"
  by simp

lemma cop_nts__os:
  assumes "Coplanar A B C D" and
    "\<not> Col C A B" and
    "\<not> Col D A B" and
    "\<not> A B TS C D"
  shows "A B OS C D"
  using assms(1) assms(2) assms(3) assms(4) cop__one_or_two_sides by blast

lemma cop_nos__ts:
  assumes "Coplanar A B C D" and
    "\<not> Col C A B" and
    "\<not> Col D A B" and
    "\<not> A B OS C D"
  shows "A B TS C D"
  using assms(1) assms(2) assms(3) assms(4) cop_nts__os by blast

lemma one_side_dec:
  "A B OS C D \<or> \<not> A B OS C D"
  by simp

lemma cop_dec:
  "Coplanar A B C D \<or> \<not> Coplanar A B C D"
  by simp

lemma ex_diff_cop:
  "\<exists> E. Coplanar A B C E \<and> D \<noteq> E"
  by (metis col_trivial_2 diff_col_ex ncop__ncols)

lemma ex_ncol_cop:
  assumes "D \<noteq> E"
  shows "\<exists> F. Coplanar A B C F \<and> \<not> Col D E F"
proof cases
  assume "Col A B C"
  then show ?thesis
    using assms ncop__ncols not_col_exists by blast
next
  assume P1: "\<not> Col A B C"
  then show ?thesis
  proof -
    have P2: "(Col D E A \<and> Col D E B) \<longrightarrow> (\<exists> F. Coplanar A B C F \<and> \<not> Col D E F)"
      by (meson P1 assms col3 col_trivial_2 ncop__ncols)
    have P3: "(\<not>Col D E A \<and> Col D E B) \<longrightarrow> (\<exists> F. Coplanar A B C F \<and> \<not> Col D E F)"
      using col_trivial_3 ncop__ncols by blast
    have P4: "(Col D E A \<and> \<not>Col D E B) \<longrightarrow> (\<exists> F. Coplanar A B C F \<and> \<not> Col D E F)"
      using col_trivial_2 ncop__ncols by blast
    have "(\<not>Col D E A \<and> \<not>Col D E B) \<longrightarrow> (\<exists> F. Coplanar A B C F \<and> \<not> Col D E F)"
      using col_trivial_3 ncop__ncols by blast
    then show ?thesis using P2 P3 P4 by blast
  qed
qed

lemma ex_ncol_cop2:
  "\<exists> E F. (Coplanar A B C E \<and> Coplanar A B C F \<and> \<not> Col D E F)"
proof -
  have f1: "\<forall>p pa pb. Coplanar pb pa p pb"
    by (meson col_trivial_3 ncop__ncols)
  have f2: "\<forall>p pa pb. Coplanar pb pa p p"
    by (meson Col_perm col_trivial_3 ncop__ncols)
  obtain pp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
    f3: "\<forall>p pa. p = pa \<or> \<not> Col p pa (pp p pa)"
    using not_col_exists by moura
  have f4: "\<forall>p pa pb. Coplanar pb pb pa p"
    by (meson Col_perm col_trivial_3 ncop__ncols)
  have "\<exists>p. A \<noteq> p"
    by (meson col_trivial_3 diff_col_ex3)
  moreover
  { assume "B \<noteq> A"
    then have "D = B \<longrightarrow> (\<exists>p. \<not> Col D p A \<and> Coplanar A B C p)"
      using f3 f2 by (metis (no_types) Col_perm ncop__ncols)
    then have "D = B \<longrightarrow> (\<exists>p pa. Coplanar A B C p \<and> Coplanar A B C pa \<and> \<not> Col D p pa)"
      using f1 by blast }
  moreover
  { assume "D \<noteq> B"
    moreover
    { assume "\<exists>p. D \<noteq> B \<and> \<not> Coplanar A B C p"
      then have "D \<noteq> B \<and> \<not> Col A B C"
        using ncop__ncols by blast
      then have "\<exists>p. \<not> Col D p B \<and> Coplanar A B C p"
        using f2 f1 by (metis (no_types) Col_perm col_transitivity_1) }
    ultimately have ?thesis
      using f3 by (metis (no_types) col_trivial_3 ncop__ncols) }
  ultimately show ?thesis
    using f4 f3 by blast
qed

lemma col2_cop2__eq:
  assumes "\<not> Coplanar A B C U" and
    "U \<noteq> V" and
    "Coplanar A B C P" and
    "Coplanar A B C Q" and
    "Col U V P" and
    "Col U V Q"
  shows "P = Q"
proof -
  have "Col U Q P"
    by (meson assms(2) assms(5) assms(6) col_transitivity_1)
  then have "Col P Q U"
    using not_col_permutation_3 by blast
  then show ?thesis
    using assms(1) assms(3) assms(4) col_cop2__cop by blast
qed

lemma cong3_cop2__col:
  assumes "Coplanar A B C P" and
    "Coplanar A B C Q" and
    "P \<noteq> Q" and
    "Cong A P A Q" and
    "Cong B P B Q" and
    "Cong C P C Q"
  shows "Col A B C"
proof cases
  assume "Col A B C"
  then show ?thesis by blast
next
  assume P1: "\<not> Col A B C"
  obtain M where P2: "M Midpoint P Q"
    using assms(6) l7_25 by blast
  have P3: "Per A M P"
    using P2 Per_def assms(4) by blast
  have P4: "Per B M P"
    using P2 Per_def assms(5) by blast
  have P5: "Per C M P"
    using P2 Per_def assms(6) by blast
  have "False"
  proof cases
    assume Q1: "A = M"
    have Q2: "Coplanar P B C A"
      using assms(1) ncoplanar_perm_21 by blast
    have Q3: "P \<noteq> A"
      by (metis assms(3) assms(4) cong_diff_4)
    have Q4: "Per B A P"
      by (simp add: P4 Q1)
    have Q5: "Per C A P"
      by (simp add: P5 Q1)
    then show ?thesis using Q1 Q2 Q3 Q4 cop_per2__col
      using P1 not_col_permutation_1 by blast
  next
    assume Q0: "A \<noteq> M"
    have Q1: "Col A B M"
    proof -
      have R1: "Coplanar A B P Q"
        using P1 assms(1) assms(2) coplanar_trans_1 ncoplanar_perm_8 not_col_permutation_2 by blast
      then have R2: "Coplanar P A B M"
        using P2 bet_cop__cop coplanar_perm_14 midpoint_bet ncoplanar_perm_6 by blast
      have R3: "P \<noteq> M"
        using P2 assms(3) l7_3_2 l7_9_bis by blast
      have R4: "Per A M P"
        by (simp add: P3)
      have R5: "Per B M P"
        by (simp add: P4)
      then show ?thesis
        using R2 R3 R4 cop_per2__col by blast
    qed
    have "Col A C M"
    proof -
      have R1: "Coplanar P A C M"
        using P1 Q1 assms(1) col2_cop__cop coplanar_perm_22 ncoplanar_perm_3 not_col_distincts by blast
      have R2: "P \<noteq> M"
        using P2 assms(3) l7_3_2 symmetric_point_uniqueness by blast
      have R3: "Per A M P"
        by (simp add: P3)
      have "Per C M P"
        by (simp add: P5)
      then show ?thesis
        using R1 R2 R3 cop_per2__col by blast
    qed
    then show ?thesis
      using NCol_perm P1 Q0 Q1 col_trivial_3 colx by blast
  qed
  then show ?thesis by blast
qed

lemma l9_38:
  assumes "A B C TSP P Q"
  shows "A B C TSP Q P"
  using Bet_perm TSP_def assms by blast

lemma l9_39:
  assumes "A B C TSP P R" and
    "Coplanar A B C D" and
    "D Out P Q"
  shows "A B C TSP Q R"
proof -
  have P1: "\<not> Col A B C"
    using TSP_def assms(1) ncop__ncol by blast
  have P2: "\<not> Coplanar A B C Q"
    by (metis TSP_def assms(1) assms(2) assms(3) col_cop2__cop l6_6 out_col out_diff2)
  have P3: "\<not> Coplanar A B C R"
    using TSP_def assms(1) by blast
  obtain T where P3A: "Coplanar A B C T \<and> Bet P T R"
    using TSP_def assms(1) by blast
  have W1: "D = T \<longrightarrow> A B C TSP Q R"
    using P2 P3 P3A TSP_def assms(3) bet_out__bet by blast
  {
    assume V1: "D \<noteq> T"
    have V1A: "\<not> Col P D T" using P3A col_cop2__cop
      by (metis TSP_def V1 assms(1) assms(2) col2_cop2__eq col_trivial_2)
    have V1B: "D T TS P R"
      by (metis P3 P3A V1A bet__ts invert_two_sides not_col_permutation_3)
    have "D T OS P Q"
      using V1A assms(3) not_col_permutation_1 out_one_side by blast
    then have V2: "D T TS Q R"
      using V1B l9_8_2 by blast
    then obtain T' where V3: "Col T' D T \<and> Bet Q T' R"
      using TS_def by blast
    have V4: "Coplanar A B C T'"
      using Col_cases P3A V1 V3 assms(2) col_cop2__cop by blast
    then have "A B C TSP Q R"
      using P2 P3 TSP_def V3 by blast
  }
  then have "D \<noteq> T \<longrightarrow> A B C TSP Q R" by blast
  then show ?thesis using W1 by blast
qed

lemma l9_41_1:
  assumes "A B C TSP P R" and
    "A B C TSP Q R"
  shows "A B C OSP P Q"
  using OSP_def assms(1) assms(2) by blast

lemma l9_41_2:
  assumes "A B C TSP P R" and
    "A B C OSP P Q"
  shows "A B C TSP Q R"
proof -
  have P1: "\<not> Coplanar A B C P"
    using TSP_def assms(1) by blast
  obtain S where P2: " A B C TSP P S \<and> A B C TSP Q S"
    using OSP_def assms(2) by blast
  obtain X where P3: "Coplanar A B C X \<and> Bet P X S"
    using P2 TSP_def by blast
  have P4: "\<not> Coplanar A B C P \<and> \<not> Coplanar A B C S"
    using P2 TSP_def by blast
  obtain Y where P5: "Coplanar A B C Y \<and> Bet Q Y S"
    using P2 TSP_def by blast
  have P6: "\<not> Coplanar A B C Q \<and> \<not> Coplanar A B C S"
    using P2 TSP_def by blast
  have P7: "X \<noteq> P \<and> S \<noteq> X \<and> Q \<noteq> Y \<and> S \<noteq> Y"
    using P3 P4 P5 P6 by blast
  {
    assume Q1: "Col P Q S"
    have Q2: "X = Y"
    proof -
      have R2: "Q \<noteq> S"
        using P5 P6 bet_neq12__neq by blast
      have R5: "Col Q S X"
        by (smt Col_def P3 Q1 between_inner_transitivity between_symmetry col_transitivity_2)
      have "Col Q S Y"
        by (simp add: P5 bet_col col_permutation_5)
      then show ?thesis
        using P2 P3 P5 R2 R5 TSP_def col2_cop2__eq by blast
    qed
    then have "X Out P Q"
      by (metis P3 P5 P7 l6_2)
    then have "A B C TSP Q R"
      using P3 assms(1) l9_39 by blast
  }
  then have P7: "Col P Q S \<longrightarrow> A B C TSP Q R" by blast
  {
    assume Q1: "\<not> Col P Q S"
    obtain Z where Q2: "Bet X Z Q \<and> Bet Y Z P"
      using P3 P5 inner_pasch by blast
    {
      assume "X = Z"
      then have "False"
        by (metis P2 P3 P5 Q1 Q2 TSP_def bet_col col_cop2__cop l6_16_1 not_col_permutation_5)
    }
    then have Q3: "X \<noteq> Z" by blast
    have "Y \<noteq> Z"
    proof -
      have "X \<noteq> Z"
        by (meson \<open>X = Z \<Longrightarrow> False\<close>)
      then have "Z \<noteq> Y"
        by (metis (no_types) P2 P3 P5 Q2 TSP_def bet_col col_cop2__cop)
      then show ?thesis
        by meson
    qed
    then have "Y Out P Z"
      using Q2 bet_out l6_6 by auto
    then have Q4: "A B C TSP Z R"
      using assms(1) P5 l9_39 by blast
    have "X Out Z Q"
      using Q2 Q3 bet_out by auto
    then have "A B C TSP Q R"
      using Q4 P3 l9_39 by blast
  }
  then have "\<not> Col P Q S \<longrightarrow> A B C TSP Q R" by blast
  then show ?thesis using P7 by blast
qed

lemma tsp_exists:
  assumes "\<not> Coplanar A B C P"
  shows "\<exists> Q. A B C TSP P Q"
proof -
  obtain Q where P1: "Bet P A Q \<and> Cong A Q A P"
    using segment_construction by blast
  have P2: "Coplanar A B C A"
    using coplanar_trivial ncoplanar_perm_5 by blast
  have P3: "\<not> Coplanar A B C P"
    by (simp add: assms)
  have P4: "\<not> Coplanar A B C Q"
    by (metis P1 P2 Tarski_neutral_dimensionless.col_cop2__cop Tarski_neutral_dimensionless_axioms assms bet_col cong_diff_4 not_col_permutation_2)
  then show ?thesis
    using P1 P2 TSP_def assms by blast
qed


lemma osp_reflexivity:
  assumes "\<not> Coplanar A B C P"
  shows "A B C OSP P P"
  by (meson assms l9_41_1 tsp_exists)

lemma osp_symmetry:
  assumes "A B C OSP P Q"
  shows "A B C OSP Q P"
  using OSP_def assms by auto

lemma osp_transitivity:
  assumes "A B C OSP P Q" and
    "A B C OSP Q R"
  shows "A B C OSP P R"
  using OSP_def assms(1) assms(2) l9_41_2 by blast

lemma cop3_tsp__tsp:
  assumes "\<not> Col D E F" and
    "Coplanar A B C D" and
    "Coplanar A B C E" and
    "Coplanar A B C F" and
    "A B C TSP P Q"
  shows "D E F TSP P Q"
proof -
  obtain T where P1: "Coplanar A B C T \<and> Bet P T Q"
    using TSP_def assms(5) by blast
  have P2: "\<not> Col A B C"
    using TSP_def assms(5) ncop__ncols by blast
  have P3: "Coplanar D E F A \<and> Coplanar D E F B \<and> Coplanar D E F C \<and> Coplanar D E F T"
  proof -
    have P3A: "Coplanar D E F A"
      using P2 assms(2) assms(3) assms(4) col_trivial_3 coplanar_pseudo_trans ncop__ncols by blast
    have P3B: "Coplanar D E F B"
      using P2 assms(2) assms(3) assms(4) col_trivial_2 coplanar_pseudo_trans ncop__ncols by blast
    have P3C: "Coplanar D E F C"
      by (meson P2 assms(2) assms(3) assms(4) coplanar_perm_16 coplanar_pseudo_trans coplanar_trivial)
    have "Coplanar D E F T"
      using P1 P2 assms(2) assms(3) assms(4) coplanar_pseudo_trans by blast
    then show ?thesis using P3A P3B P3C by simp
  qed
  have P4: "\<not> Coplanar D E F P"
    using P3 TSP_def assms(1) assms(5) coplanar_pseudo_trans by auto
  have P5: "\<not> Coplanar D E F Q"
    by (metis P1 P3 P4 TSP_def assms(5) bet_col bet_col1 col2_cop2__eq)
  have P6: "Coplanar D E F T"
    by (simp add: P3)
  have "Bet P T Q"
    by (simp add: P1)
  then show ?thesis
    using P4 P5 P6 TSP_def by blast
qed

lemma cop3_osp__osp:
  assumes "\<not> Col D E F" and
    "Coplanar A B C D" and
    "Coplanar A B C E" and
    "Coplanar A B C F" and
    "A B C OSP P Q"
  shows "D E F OSP P Q"
proof -
  obtain R where P1: "A B C TSP P R \<and> A B C TSP Q R"
    using OSP_def assms(5) by blast
  then show ?thesis
    using OSP_def assms(1) assms(2) assms(3) assms(4) cop3_tsp__tsp by blast
qed

lemma ncop_distincts:
  assumes "\<not> Coplanar A B C D"
  shows "A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> D \<and> B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D"
  using Coplanar_def assms col_trivial_1 col_trivial_2 by blast

lemma tsp_distincts:
  assumes "A B C TSP P Q"
  shows "A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> A \<noteq> P \<and> B \<noteq> P \<and> C \<noteq> P \<and> A \<noteq> Q \<and> B \<noteq> Q \<and> C \<noteq> Q \<and> P \<noteq> Q"
proof -
  obtain pp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p" where
    "\<forall>x0 x1 x2 x3 x4. (\<exists>v5. Coplanar x4 x3 x2 v5 \<and> Bet x1 v5 x0) = (Coplanar x4 x3 x2 (pp x0 x1 x2 x3 x4) \<and> Bet x1 (pp x0 x1 x2 x3 x4) x0)"
    by moura
  then have f1: "\<not> Coplanar A B C P \<and> \<not> Coplanar A B C Q \<and> Coplanar A B C (pp Q P C B A) \<and> Bet P (pp Q P C B A) Q"
    using TSP_def assms by presburger
  then have "Q \<noteq> pp Q P C B A"
    by force
  then show ?thesis
    using f1 by (meson bet_neq32__neq ncop_distincts)
qed

lemma osp_distincts:
  assumes "A B C OSP P Q"
  shows "A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C \<and> A \<noteq> P \<and> B \<noteq> P \<and> C \<noteq> P \<and> A \<noteq> Q \<and> B \<noteq> Q \<and> C \<noteq> Q"
  using OSP_def assms tsp_distincts by blast

lemma tsp__ncop1:
  assumes "A B C TSP P Q"
  shows "\<not> Coplanar A B C P"
  using TSP_def assms by blast

lemma tsp__ncop2:
  assumes "A B C TSP P Q"
  shows "\<not> Coplanar A B C Q"
  using TSP_def assms by auto

lemma osp__ncop1:
  assumes "A B C OSP P Q"
  shows "\<not> Coplanar A B C P"
  using OSP_def TSP_def assms by blast

lemma osp__ncop2:
  assumes "A B C OSP P Q"
  shows "\<not> Coplanar A B C Q"
  using assms osp__ncop1 osp_symmetry by blast

lemma tsp__nosp:
  assumes "A B C TSP P Q"
  shows "\<not> A B C OSP P Q"
  using assms l9_41_2 tsp_distincts by blast

lemma osp__ntsp:
  assumes "A B C OSP P Q"
  shows "\<not> A B C TSP P Q"
  using assms tsp__nosp by blast

lemma osp_bet__osp:
  assumes "A B C OSP P R" and
    "Bet P Q R"
  shows "A B C OSP P Q"
proof -
  obtain S where P1: "A B C TSP P S"
    using OSP_def assms(1) by blast
  then obtain Y where P2: "Coplanar A B C Y \<and> Bet R Y S"
    using TSP_def assms(1) l9_41_2 by blast
  obtain X where Q1: "Coplanar A B C X \<and> Bet P X S"
    using P1 TSP_def by blast
  have Q2: "P \<noteq> X \<and> S \<noteq> X \<and> R \<noteq> Y"
    using P1 P2 Q1 TSP_def assms(1) osp__ncop2 by auto
  {
    assume P3: "Col P R S"
    have P5: "A B C TSP Q S"
    proof -
      have Q3: "X = Y"
      proof -
        have R1: "\<not> Coplanar A B C R"
          using assms(1) osp__ncop2 by blast
        have R2: "R \<noteq> S"
          using P1 assms(1) osp__ntsp by blast
        have R5: "Col R S X"
          by (smt Col_def P3 Q1 bet_col1 between_exchange4 between_symmetry)
        have "Col R S Y"
          using P2 bet_col col_permutation_5 by blast
        then show ?thesis
          using R1 R2 Q1 P2 R5 col2_cop2__eq by blast
      qed
      then have "Y Out P Q"
        by (smt P2 P3 Q1 Q2 assms(2) bet_col1 between_exchange4 between_symmetry l6_3_2 l6_4_2 not_bet_and_out third_point)
      then show ?thesis
        using P1 P2 l9_39 by blast
    qed
    then have "A B C OSP P Q"
      using OSP_def P1 P2 l9_39 by blast
  }
  then have H1: "Col P R S \<longrightarrow> A B C OSP P Q" by blast
  {
    assume T1: "\<not> Col P R S"
    have T2: "X Y OS P R"
    proof -
      have T3: "P \<noteq> X \<and> S \<noteq> X \<and> R \<noteq> Y \<and> S \<noteq> Y"
        using P1 P2 Q2 TSP_def by auto
      have T4: "\<not> Col S X Y"
        by (metis P2 Q1 T1 T3 bet_out_1 col_out2_col col_permutation_5 not_col_permutation_4)
      have T5: "X Y TS P S"
        by (metis Col_perm Q1 Q2 T4 bet__ts bet_col col_transitivity_2)
      have T6: "X Y TS R S"
        by (metis P2 Q1 T4 assms(1) bet__ts col_cop2__cop invert_two_sides not_col_distincts osp__ncop2)
      then show ?thesis
        using T5 l9_8_1 by auto
    qed
    then have T7: "X Y OS P Q"
      using assms(2) l9_17 by blast
    then obtain S' where T7A: "X Y TS P S' \<and> X Y TS Q S'"
      using OS_def by blast
    have T7B: "\<not> Col P X Y \<and> \<not> Col S' X Y \<and> (\<exists> T::'p. Col T X Y \<and> Bet P T S')"
      using T7A TS_def by auto
    have T7C: "\<not> Col Q X Y \<and> \<not> Col S' X Y \<and> (\<exists> T::'p. Col T X Y \<and> Bet Q T S')"
      using T7A TS_def by blast
    obtain X' where T9: "Col X' X Y \<and> Bet P X' S' \<and> X Y TS Q S'"
      using T7A T7B by blast
    obtain Y' where T10: "Col Y' X Y \<and> Bet Q Y' S'"
      using T7C by blast
    have T11: "Coplanar A B C X'"
      using Col_cases P2 Q1 T9 col_cop2__cop ts_distincts by blast
    have T12: "Coplanar A B C Y'"
      using Col_cases P2 Q1 T10 T9 col_cop2__cop ts_distincts by blast
    have T13: "\<not> Coplanar A B C S'"
      using T11 T7C T9 assms(1) bet_col bet_col1 col2_cop2__eq osp__ncop1 by fastforce
    then have "A B C OSP P Q"
    proof -
      have R1: "A B C TSP P S'"
        using P1 T11 T13 T9 TSP_def by blast
      have "A B C TSP Q S'"
        by (metis T10 T12 T13 T7C TSP_def bet_col col_cop2__cop)
      then show ?thesis using R1 by (smt l9_41_1)
    qed
  }
  then show ?thesis using H1 by blast
qed

lemma l9_18_3:
  assumes "Coplanar A B C P" and
    "Col X Y P"
  shows "A B C TSP X Y \<longleftrightarrow> (Bet X P Y \<and> \<not> Coplanar A B C X \<and> \<not> Coplanar A B C Y)"
  by (meson TSP_def assms(1) assms(2) l9_39 not_bet_out not_col_permutation_5 tsp_distincts)

lemma bet_cop__tsp:
  assumes "\<not> Coplanar A B C X" and
    "P \<noteq> Y" and
    "Coplanar A B C P" and
    "Bet X P Y"
  shows "A B C TSP X Y"
  using TSP_def assms(1) assms(2) assms(3) assms(4) bet_col bet_col1 col2_cop2__eq by fastforce

lemma cop_out__osp:
  assumes "\<not> Coplanar A B C X" and
    "Coplanar A B C P" and
    "P Out X Y"
  shows "A B C OSP X Y"
  by (meson OSP_def assms(1) assms(2) assms(3) l9_39 tsp_exists)

lemma l9_19_3:
  assumes "Coplanar A B C P" and
    "Col X Y P"
  shows "A B C OSP X Y \<longleftrightarrow> (P Out X Y \<and> \<not> Coplanar A B C X)"
  by (meson assms(1) assms(2) cop_out__osp l6_4_2 l9_18_3 not_col_permutation_5 osp__ncop1 osp__ncop2 tsp__nosp)

lemma cop2_ts__tsp:
  assumes "\<not> Coplanar A B C X" and "Coplanar A B C D" and
    "Coplanar A B C E" and "D E TS X Y"
  shows "A B C TSP X Y"
proof -
  obtain T where P1: "Col T D E \<and> Bet X T Y"
    using TS_def assms(4) by blast
  have P2: "Coplanar A B C T"
    using P1 assms(2) assms(3) assms(4) col_cop2__cop not_col_permutation_2 ts_distincts by blast
  then show ?thesis
    by (metis P1 TS_def assms(1) assms(4) bet_cop__tsp)
qed

lemma cop2_os__osp:
  assumes "\<not> Coplanar A B C X" and
    "Coplanar A B C D" and
    "Coplanar A B C E" and
    "D E OS X Y"
  shows "A B C OSP X Y"
proof -
  obtain Z where P1: "D E TS X Z \<and> D E TS Y Z"
    using OS_def assms(4) by blast
  then have P2: "A B C TSP X Z"
    using assms(1) assms(2) assms(3) cop2_ts__tsp by blast
  then have P3: "A B C TSP Y Z"
    by (meson P1 assms(2) assms(3) cop2_ts__tsp l9_2 tsp__ncop2)
  then show ?thesis
    using P2 l9_41_1 by blast
qed

lemma cop3_tsp__ts:
  assumes "D \<noteq> E" and
    "Coplanar A B C D" and
    "Coplanar A B C E" and
    "Coplanar D E X Y" and
    "A B C TSP X Y"
  shows "D E TS X Y"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) col_cop2__cop cop2_os__osp cop_nts__os not_col_permutation_2 tsp__ncop1 tsp__ncop2 tsp__nosp)

lemma cop3_osp__os:
  assumes "D \<noteq> E" and
    "Coplanar A B C D" and
    "Coplanar A B C E" and
    "Coplanar D E X Y" and
    "A B C OSP X Y"
  shows "D E OS X Y"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) col_cop2__cop cop2_ts__tsp cop_nts__os not_col_permutation_2 osp__ncop1 osp__ncop2 tsp__nosp)

lemma cop_tsp__ex_cop2:
  assumes (*"Coplanar A B C P" and*)
    "A B C TSP D E"
  shows "\<exists> Q. (Coplanar A B C Q \<and> Coplanar D E P Q \<and> P \<noteq> Q)"
proof cases
  assume "Col D E P"
  then show ?thesis
    by (meson ex_diff_cop ncop__ncols)
next
  assume "\<not> Col D E P"
  then obtain Q where "Coplanar A B C Q \<and> Bet D Q E \<and> \<not> Col D E P"
    using TSP_def assms(1) by blast
  then show ?thesis
    using Col_perm bet_col ncop__ncols by blast
qed

lemma cop_osp__ex_cop2:
  assumes "Coplanar A B C P" and
    "A B C OSP D E"
  shows "\<exists> Q. Coplanar A B C Q \<and> Coplanar D E P Q \<and> P \<noteq> Q"
proof cases
  assume "Col D E P"
  then show ?thesis
    by (metis col_trivial_3 diff_col_ex ncop__ncols)
next
  assume P1: "\<not> Col D E P"
  obtain E' where P2: "Bet E P E' \<and> Cong P E' P E"
    using segment_construction by blast
  have P3: "\<not> Col D E' P"
    by (metis P1 P2 bet_col bet_cong_eq between_symmetry col_permutation_5 l5_2 l6_16_1)
  have P4: "A B C TSP D E'"
    by (metis P2 P3 assms(1) assms(2) bet_cop__tsp l9_41_2 not_col_distincts osp__ncop2 osp_symmetry)
  then have "\<not> Coplanar A B C D \<and> \<not> Coplanar A B C E' \<and> (\<exists> T. Coplanar A B C T \<and> Bet D T E')"
    by (simp add: TSP_def)
  then obtain Q where P7: "Coplanar A B C Q \<and> Bet D Q E'"
    by blast
  then have "Coplanar D E' P Q"
    using bet_col ncop__ncols ncoplanar_perm_5 by blast
  then have "Coplanar D E P Q"
    using Col_perm P2 P3 bet_col col_cop__cop ncoplanar_perm_5 not_col_distincts by blast
  then show ?thesis
    using P3 P7 bet_col col_permutation_5 by blast
qed

lemma sac__coplanar:
  assumes "Saccheri A B C D"
  shows "Coplanar A B C D"
  using Saccheri_def assms ncoplanar_perm_4 os__coplanar by blast

subsection "Line reflexivity"

subsubsection "Dimensionless"

lemma Ch10_Goal1:
  assumes "\<not> Coplanar D C B A"
  shows "\<not> Coplanar A B C D"
  by (simp add: assms ncoplanar_perm_23)

lemma ex_sym:
  "\<exists> Y. (A B Perp X Y \<or> X = Y) \<and> (\<exists> M. Col A B M \<and> M Midpoint X Y)"
proof cases
  assume "Col A B X"
  thus ?thesis
    using l7_3_2 by blast
next
  assume "\<not> Col A B X"
  then obtain M0 where P1: "Col A B M0 \<and> A B Perp X M0"
    using l8_18_existence by blast
  obtain Z where P2: "M0 Midpoint X Z"
    using symmetric_point_construction by blast
  thus ?thesis
    by (metis (full_types) P1 Perp_cases bet_col midpoint_bet perp_col)
qed

lemma is_image_is_image_spec:
  assumes "A \<noteq> B"
  shows "P' P Reflect A B \<longleftrightarrow> P' P ReflectL A B"
  by (simp add: Reflect_def assms)

lemma ex_sym1:
  assumes "A \<noteq> B"
  shows "\<exists> Y. (A B Perp X Y \<or> X = Y) \<and> (\<exists> M. Col A B M \<and> M Midpoint X Y \<and> X Y Reflect A B)"
proof cases
  assume "Col A B X"
  thus ?thesis
    by (meson ReflectL_def Reflect_def assms l7_3_2)
next
  assume P0: "\<not> Col A B X"
  then obtain M0 where P1: "Col A B M0 \<and> A B Perp X M0"
    using l8_18_existence by blast
  obtain Z where P2: "M0 Midpoint X Z"
    using symmetric_point_construction by blast
  have P3: "A B Perp X Z"
  proof cases
    assume "X = Z"
    thus ?thesis
      using P1 P2 P0 midpoint_distinct by blast
  next
    assume "X \<noteq> Z"
    then have P2: "X Z Perp A B"
      using P1 P2 Perp_cases bet_col midpoint_bet perp_col by blast
    show ?thesis
      by (simp add: Tarski_neutral_dimensionless.Perp_perm Tarski_neutral_dimensionless_axioms P2)
  qed
  have P10: "(A B Perp X Z \<or> X = Z)"
    by (simp add: P3)
  have "\<exists> M. Col A B M \<and> M Midpoint X Z \<and> X Z Reflect A B"
    using P1 P2 P3 ReflectL_def assms is_image_is_image_spec l7_2 perp_right_comm by blast
  thus ?thesis
    using P3 by blast
qed

lemma l10_2_uniqueness:
  assumes "P1 P Reflect A B" and
    "P2 P Reflect A B"
  shows "P1 = P2"
proof cases
  assume "A = B"
  thus ?thesis
    using Reflect_def assms(1) assms(2) symmetric_point_uniqueness by auto
next
  assume P1: "A \<noteq> B"
  have P1A: "P1 P ReflectL A B"
    using P1 assms(1) is_image_is_image_spec by auto
  then have P1B: "A B Perp P P1 \<or> P = P1"
    using ReflectL_def by blast
  have P2A: "P2 P ReflectL A B"
    using P1 assms(2) is_image_is_image_spec by auto
  then have P2B: "A B Perp P P2 \<or> P = P2"
    using ReflectL_def by blast
  obtain X where R1: "X Midpoint P P1 \<and> Col A B X"
    by (metis ReflectL_def assms(1) col_trivial_1 is_image_is_image_spec midpoint_existence)
  obtain Y where R2: "Y Midpoint P P2 \<and> Col A B Y"
    by (metis ReflectL_def assms(2) col_trivial_1 is_image_is_image_spec midpoint_existence)
  {
    assume Q1:"(A B Perp P P1 \<and> A B Perp P P2)"
    have S1: "P \<noteq> X"
    proof -
      {
        assume "P = X"
        then have "P = P1"
          using R1 is_midpoint_id by blast
        then have "A B Perp P P"
          using Q1 by blast
        then have "False"
          using perp_distinct by blast
      }
      thus ?thesis by blast
    qed
    then have "P1 = P2"
      by (smt Perp_cases Q1 \<open>\<And>thesis. (\<And>X. X Midpoint P P1 \<and> Col A B X \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>\<And>thesis. (\<And>Y. Y Midpoint P P2 \<and> Col A B Y \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> col_permutation_1 l7_2 l7_9 l8_18_uniqueness midpoint_col perp_col perp_not_col2)
  }
  then have T1: "(A B Perp P P1 \<and> A B Perp P P2) \<longrightarrow> P1 = P2" by blast
  have T2: "(P = P1 \<and> A B Perp P P2) \<longrightarrow> P1 = P2"
    by (metis R1 R2 col3 col_trivial_2 col_trivial_3 midpoint_col midpoint_distinct_1 midpoint_distinct_2 perp_not_col2)
  have T3: "(P = P2 \<and> A B Perp P P1) \<longrightarrow> P1 = P2"
    by (metis R1 R2 col_trivial_2 midpoint_col midpoint_distinct_3 perp_col2 perp_not_col2)
  thus ?thesis
    using T1 T2 T3 P1B P2B by blast
qed

lemma l10_2_uniqueness_spec:
  assumes "P1 P ReflectL A B" and
    "P2 P ReflectL A B"
  shows "P1 = P2"
proof -
  have "A B Perp P P1 \<or> P = P1"
    using ReflectL_def assms(1) by blast
  moreover obtain X1 where "X1 Midpoint P P1 \<and> Col A B X1"
    using ReflectL_def assms(1) by blast
  moreover have "A B Perp P P2 \<or> P = P2"
    using ReflectL_def assms(2) by blast
  moreover obtain X2 where "X2 Midpoint P P2 \<and> Col A B X2"
    using ReflectL_def assms(2) by blast
  ultimately show ?thesis
    by (smt col_permutation_1 l8_16_1 l8_18_uniqueness midpoint_col midpoint_distinct_3 perp_col1 symmetric_point_uniqueness)
qed

lemma l10_2_existence_spec:
  "\<exists> P'. P' P ReflectL A B"
proof cases
  assume "Col A B P"
  thus ?thesis
    using ReflectL_def l7_3_2 by blast
next
  assume "\<not> Col A B P"
  then obtain X where "Col A B X \<and> A B Perp P X"
    using l8_18_existence by blast
  moreover obtain P' where "X Midpoint P P'"
    using symmetric_point_construction by blast
  ultimately show ?thesis
    using ReflectL_def bet_col midpoint_bet perp_col1 by blast
qed

lemma l10_2_existence:
  "\<exists> P'. P' P Reflect A B"
  by (metis Reflect_def l10_2_existence_spec symmetric_point_construction)

lemma l10_4_spec:
  assumes "P P' ReflectL A B"
  shows "P' P ReflectL A B"
proof -
  obtain X where "X Midpoint P P' \<and> Col A B X"
    using ReflectL_def assms l7_2 by blast
  thus ?thesis
    using Perp_cases ReflectL_def assms by auto
qed

lemma l10_4:
  assumes "P P' Reflect A B"
  shows "P' P Reflect A B"
  using Reflect_def Tarski_neutral_dimensionless.l7_2 Tarski_neutral_dimensionless_axioms assms l10_4_spec by fastforce

lemma l10_5:
  assumes "P' P Reflect A B" and
    "P'' P' Reflect A B"
  shows "P = P''"
  by (meson assms(1) assms(2) l10_2_uniqueness l10_4)

lemma l10_6_uniqueness:
  assumes "P P1 Reflect A B" and
    "P P2 Reflect A B"
  shows "P1 = P2"
  using assms(1) assms(2) l10_4 l10_5 by blast

lemma l10_6_uniqueness_spec:
  assumes "P P1 ReflectL A B" and
    "P P2 ReflectL A B"
  shows "P1 = P2"
  using assms(1) assms(2) l10_2_uniqueness_spec l10_4_spec by blast

lemma l10_6_existence_spec:
  assumes "A \<noteq> B"
  shows "\<exists> P. P' P ReflectL A B"
  using l10_2_existence_spec l10_4_spec by blast

lemma l10_6_existence:
  "\<exists> P. P' P Reflect A B"
  using l10_2_existence l10_4 by blast

lemma l10_7:
  assumes "P' P Reflect A B" and
    "Q' Q Reflect A B" and
    "P' = Q'"
  shows "P = Q"
  using assms(1) assms(2) assms(3) l10_6_uniqueness by blast

lemma l10_8:
  assumes "P P Reflect A B"
  shows "Col P A B"
  by (metis Col_perm assms col_trivial_2 ex_sym1 l10_6_uniqueness l7_3)

lemma col__refl:
  assumes "Col P A B"
  shows "P P ReflectL A B"
  using ReflectL_def assms col_permutation_1 l7_3_2 by blast

lemma is_image_col_cong:
  assumes "A \<noteq> B" and
    "P P' Reflect A B" and
    "Col A B X"
  shows "Cong P X P' X"
proof -
  have P1: "P P' ReflectL A B"
    using assms(1) assms(2) is_image_is_image_spec by blast
  obtain M0 where P2: "M0 Midpoint P' P \<and> Col A B M0"
    using P1 ReflectL_def by blast
  have "A B Perp P' P \<or> P' = P"
    using P1 ReflectL_def by auto
  moreover
  {
    assume S1: "A B Perp P' P"
    then have "A \<noteq> B \<and> P' \<noteq> P"
      using perp_distinct by blast
    have S2: "M0 = X \<longrightarrow> Cong P X P' X"
      using P2 cong_4312 midpoint_cong by blast
    {
      assume "M0 \<noteq> X"
      then have "M0 X Perp P' P"
        using P2 S1 assms(3) perp_col2 by blast
      then have "\<not> Col A B P \<and> Per P M0 X"
        by (metis Col_perm P2 S1 colx l8_2 midpoint_col midpoint_distinct_1 per_col perp_col1 perp_not_col2 perp_per_1)
      then have "Cong P X P' X"
        using P2 cong_commutativity l7_2 l8_2 per_double_cong by blast
    }
    then have "Cong P X P' X"
      using S2 by blast
  }
  then have "A B Perp P' P \<longrightarrow> Cong P X P' X" by blast
  moreover
  {
    assume "P = P'"
    then have "Cong P X P' X"
      by (simp add: cong_reflexivity)
  }
  ultimately show ?thesis by blast
qed

lemma is_image_spec_col_cong:
  assumes "P P' ReflectL A B" and
    "Col A B X"
  shows "Cong P X P' X"
  by (metis Col_def Reflect_def assms(1) assms(2) between_trivial col__refl cong_reflexivity is_image_col_cong l10_6_uniqueness_spec)

lemma image_id:
  assumes "A \<noteq> B" and
    "Col A B T" and
    "T T' Reflect A B"
  shows "T = T'"
  using assms(1) assms(2) assms(3) cong_diff_4 is_image_col_cong by blast

lemma osym_not_col:
  assumes "P P' Reflect A B" and
    "\<not> Col A B P"
  shows "\<not> Col A B P'"
  using assms(1) assms(2) l10_4 local.image_id not_col_distincts by blast

lemma midpoint_preserves_image:
  assumes "A \<noteq> B" and
    "Col A B M" and
    "P P' Reflect A B" and
    "M Midpoint P Q" and
    "M Midpoint P' Q'"
  shows "Q Q' Reflect A B"
proof -
  obtain X where P1: "X Midpoint P' P \<and> Col A B X"
    using ReflectL_def assms(1) assms(3) is_image_is_image_spec by blast
  {
    assume S1: "A B Perp P' P"
    obtain Y where S2: "M Midpoint X Y"
      using symmetric_point_construction by blast
    have S3: "Y Midpoint Q Q'"
    proof -
      have R4: "X Midpoint P P'"
        by (simp add: P1 l7_2)
      thus ?thesis
        using assms(4) assms(5) S2 symmetry_preserves_midpoint by blast
    qed
    have S4: "P \<noteq> P'"
      using S1 perp_not_eq_2 by blast
    then have S5: "Q \<noteq> Q'"
      using Tarski_neutral_dimensionless.l7_9 Tarski_neutral_dimensionless_axioms assms(4) assms(5) by fastforce
    have S6: "Y Midpoint Q' Q \<and> Col A B Y"
      by (metis P1 S2 S3 assms(2) colx l7_2 midpoint_col midpoint_distinct_1)
    have S7: "A B Perp Q' Q \<or> Q = Q'"
    proof -
      have R3: "Per M Y Q"
      proof -
        have S1: "Y Midpoint Q Q'"
          using S3 by auto
        have "Cong M Q M Q'"
          using assms(1) assms(2) assms(3) assms(4) assms(5) cong_commutativity is_image_col_cong l7_16 l7_3_2 by blast
        thus ?thesis
          using Per_def S1 by blast
      qed
      {
        have "X = Y \<longrightarrow> (A B Perp Q' Q \<or> Q = Q')"
          by (metis P1 Perp_cases S1 S2 S6 assms(5) l7_3 l7_9_bis)
        {
          assume "X \<noteq> Y"
          then have "Y PerpAt M Y Y Q"
            using R3 S2 S3 S5 midpoint_distinct_1 per_perp_in by blast
          then have V1: "Y Y Perp Y Q \<or> M Y Perp Y Q"
            by (simp add: perp_in_perp_bis)
          {
            have "Y Y Perp Y Q \<longrightarrow> A B Perp Q' Q \<or> Q = Q'"
              using perp_not_eq_1 by blast
            {
              assume T1: "M Y Perp Y Q"
              have T2: "Y Q Perp A B"
              proof cases
                assume "A = M"
                thus ?thesis
                  using Perp_cases S6 T1 assms(1) col_permutation_5 perp_col by blast
              next
                assume "A \<noteq> M"
                thus ?thesis
                  by (smt S6 T1 assms(1) assms(2) col2__eq col_transitivity_2 perp_col0 perp_not_eq_1)
              qed
              have "A B Perp Q' Q \<or> Q = Q'"
                by (metis S3 T2 midpoint_col not_col_distincts perp_col0)
            }
            then have "M Y Perp Y Q \<longrightarrow> A B Perp Q' Q \<or> Q = Q'" by blast
          }
          then have "A B Perp Q' Q \<or> Q = Q'"
            using V1 perp_distinct by blast
        }
        then have "X \<noteq> Y \<longrightarrow> (A B Perp Q' Q \<or> Q = Q')" by blast
      }
      thus ?thesis
        by (metis P1 Perp_cases S1 S2 S6 assms(5) l7_3 l7_9_bis)
    qed
    then have "Q Q' ReflectL A B"
      using ReflectL_def S6 by blast
  }
  then have "A B Perp P' P \<longrightarrow> Q Q' ReflectL A B" by blast
  moreover
  {
    assume "P = P'"
    then have "Q Q' ReflectL A B"
      by (metis P1 assms(2) assms(4) assms(5) col__refl col_permutation_2 colx midpoint_col midpoint_distinct_3 symmetric_point_uniqueness)
  }
  ultimately show ?thesis
    using ReflectL_def assms(1) assms(3) is_image_is_image_spec by auto
qed

lemma image_in_is_image_spec:
  assumes "M ReflectLAt P P' A B"
  shows "P P' ReflectL A B"
proof -
  have P1: "M Midpoint P' P"
    using ReflectLAt_def assms by blast
  have P2: "Col A B M"
    using ReflectLAt_def assms by blast
  have "A B Perp P' P \<or> P' = P"
    using ReflectLAt_def assms by blast
  thus ?thesis using P1 P2
    using ReflectL_def by blast
qed

lemma image_in_gen_is_image:
  assumes "M ReflectAt P P' A B"
  shows "P P' Reflect A B"
  using ReflectAt_def Reflect_def assms image_in_is_image_spec by auto

lemma image_image_in:
  assumes "P \<noteq> P'" and
    "P P' ReflectL A B" and
    "Col A B M" and
    "Col P M P'"
  shows "M ReflectLAt P P' A B"
proof -
  obtain M' where P1: "M' Midpoint P' P \<and> Col A B M'"
    using ReflectL_def assms(2) by blast
  have Q1: "P M' Perp A B"
    by (metis Col_cases P1 Perp_perm ReflectL_def assms(1) assms(2) bet_col cong_diff_3 midpoint_bet midpoint_cong not_cong_4321 perp_col1)
  {
    assume R1: "A B Perp P' P"
    have R3: "P \<noteq> M'"
      using Q1 perp_not_eq_1 by auto
    have R4: "A B Perp P' P"
      by (simp add: R1)
    have R5: "Col P P' M'"
      using P1 midpoint_col not_col_permutation_3 by blast
    have R6: "M' Midpoint P' P"
      by (simp add: P1)
    have R7: "\<not> Col A B P"
      using assms(1) assms(2) col__refl col_permutation_2 l10_2_uniqueness_spec l10_4_spec by blast
    have R8: "P \<noteq> P'"
      by (simp add: assms(1))
    have R9: "Col A B M'"
      by (simp add: P1)
    have R10: "Col A B M"
      by (simp add: assms(3))
    have R11: "Col P P' M'"
      by (simp add: R5)
    have R12: "Col P P' M"
      using Col_perm assms(4) by blast
    have "M = M'"
    proof cases
      assume S1: "A = M'"
      have "Per P M' A"
        by (simp add: S1 l8_5)
      thus ?thesis using l6_21 R8 R9 R10 R11 R12
        using R7 by blast
    next
      assume "A \<noteq> M'"
      thus ?thesis
        using R10 R12 R5 R7 R8 R9 l6_21 by blast
    qed
    then have "M Midpoint P' P"
      using R6 by blast
  }
  then have Q2: "A B Perp P' P \<longrightarrow> M Midpoint P' P" by blast
  have Q3: "P' = P \<longrightarrow> M Midpoint P' P"
    using assms(1) by auto
  have Q4: "A B Perp P' P \<or> P' = P"
    using ReflectL_def assms(2) by auto
  then have "M Midpoint P' P"
    using Q2 Q3 by blast
  thus ?thesis
    by (simp add: ReflectLAt_def Q4 assms(3))
qed

lemma image_in_col:
  assumes "Y ReflectLAt P P' A B"
  shows "Col P P' Y"
  using Col_perm ReflectLAt_def assms midpoint_col by blast

lemma is_image_spec_rev:
  assumes "P P' ReflectL A B"
  shows "P P' ReflectL B A"
proof -
  obtain M0 where P1: "M0 Midpoint P' P \<and> Col A B M0"
    using ReflectL_def assms by blast
  have P2: "Col B A M0"
    using Col_cases P1 by blast
  have "A B Perp P' P \<or> P' = P"
    using ReflectL_def assms by blast
  thus ?thesis
    using P1 P2 Perp_cases ReflectL_def by auto
qed

lemma is_image_rev:
  assumes "P P' Reflect A B"
  shows "P P' Reflect B A"
  using Reflect_def assms is_image_spec_rev by auto

lemma midpoint_preserves_per:
  assumes "Per A B C" and
    "M Midpoint A A1" and
    "M Midpoint B B1" and
    "M Midpoint C C1"
  shows "Per A1 B1 C1"
proof -
  obtain C' where P1: "B Midpoint C C' \<and> Cong A C A C'"
    using Per_def assms(1) by blast
  obtain C1' where P2: "M Midpoint C' C1'"
    using symmetric_point_construction by blast
  thus ?thesis
    by (meson P1 Per_def assms(2) assms(3) assms(4) l7_16 symmetry_preserves_midpoint)
qed

lemma col__image_spec:
  assumes "Col A B X"
  shows "X X ReflectL A B"
  by (simp add: assms col__refl col_permutation_2)

lemma image_triv:
  "A A Reflect A B"
  by (simp add: Reflect_def col__refl col_trivial_1 l7_3_2)

lemma cong_midpoint__image:
  assumes "Cong A X A Y" and
    "B Midpoint X Y"
  shows "Y X Reflect A B"
proof cases
  assume "A = B"
  thus ?thesis
    by (simp add: Reflect_def assms(2))
next
  assume S0: "A \<noteq> B"
  {
    assume S1: "X \<noteq> Y"
    then have "X Y Perp A B"
    proof -
      have T1: "B \<noteq> X"
        using S1 assms(2) midpoint_distinct_1 by blast
      have T2: "B \<noteq> Y"
        using S1 assms(2) midpoint_not_midpoint by blast
      have "Per A B X"
        using Per_def assms(1) assms(2) by auto
      thus ?thesis
        using S0 S1 T1 T2 assms(2) col_per_perp midpoint_col by auto
    qed
    then have "A B Perp X Y \<or> X = Y"
      using Perp_perm by blast
    then have "Y X Reflect A B"
      using ReflectL_def S0 assms(2) col_trivial_2 is_image_is_image_spec by blast
  }
  then have "X \<noteq> Y \<longrightarrow> Y X Reflect A B" by blast
  thus ?thesis
    using assms(2) image_triv is_image_rev l7_3 by blast
qed


lemma col_image_spec__eq:
  assumes "Col A B P" and
    "P P' ReflectL A B"
  shows "P = P'"
  using assms(1) assms(2) col__image_spec l10_2_uniqueness_spec l10_4_spec by blast

lemma image_spec_triv:
  "A A ReflectL B B"
  using col__image_spec not_col_distincts by blast

lemma image_spec__eq:
  assumes "P P' ReflectL A A"
  shows "P = P'"
  using assms col_image_spec__eq not_col_distincts by blast

lemma image__midpoint:
  assumes "P P' Reflect A A"
  shows "A Midpoint P' P"
  using Reflect_def assms by auto

lemma is_image_spec_dec:
  "A B ReflectL C D \<or> \<not> A B ReflectL C D"
  by simp

lemma l10_14:
  assumes "P \<noteq> P'" and
    "A \<noteq> B" and
    "P P' Reflect A B"
  shows "A B TS P P'"
proof -
  have P1: "P P' ReflectL A B"
    using assms(2) assms(3) is_image_is_image_spec by blast
  then obtain M0 where "M0 Midpoint P' P \<and> Col A B M0"
    using ReflectL_def by blast
  then have "A B Perp P' P \<longrightarrow> A B TS P P'"
    by (meson TS_def assms(1) assms(2) assms(3) between_symmetry col_permutation_2 local.image_id midpoint_bet osym_not_col)
  thus ?thesis
    using assms(1) P1 ReflectL_def by blast
qed

lemma l10_15:
  assumes "Col A B C" and
    "\<not> Col A B P"
  shows "\<exists> Q. A B Perp Q C \<and> A B OS P Q"
proof -
  have P1: "A \<noteq> B"
    using assms(2) col_trivial_1 by auto
  obtain X where P2: "A B TS P X"
    using assms(2) col_permutation_1 l9_10 by blast
  {
    assume Q1: "A = C"
    obtain Q where Q2: "\<exists> T. A B Perp Q A \<and> Col A B T \<and> Bet X T Q"
      using P1 l8_21 by blast
    then obtain T where "A B Perp Q A \<and> Col A B T \<and> Bet X T Q" by blast
    then have "A B TS Q X"
      by (meson P2 TS_def between_symmetry col_permutation_2 perp_not_col)
    then have Q5: "A B OS P Q"
      using P2 l9_8_1 by blast
    then have "\<exists> Q. A B Perp Q C \<and> A B OS P Q"
      using Q1 Q2 by blast
  }
  then have P3: "A = C \<longrightarrow> (\<exists> Q. A B Perp Q C \<and> A B OS P Q)" by blast
  {
    assume Q1: "A \<noteq> C"
    then obtain Q where Q2: "\<exists> T. C A Perp Q C \<and> Col C A T \<and> Bet X T Q"
      using l8_21 by presburger
    then obtain T where Q3: "C A Perp Q C \<and> Col C A T \<and> Bet X T Q" by blast
    have Q4: "A B Perp Q C"
      using NCol_perm P1 Q2 assms(1) col_trivial_2 perp_col2 by blast
    have "A B TS Q X"
    proof -
      have R1: "\<not> Col Q A B"
        using Col_perm P1 Q2 assms(1) col_trivial_2 colx perp_not_col by blast
      have R2: "\<not> Col X A B"
        using P2 TS_def by auto
      have R3: "Col T A B"
        by (metis Q1 Q3 assms(1) col_trivial_2 colx not_col_permutation_1)
      have "Bet Q T X"
        using Bet_cases Q3 by blast
      then have "\<exists> T. Col T A B \<and> Bet Q T X"
        using R3 by blast
      thus ?thesis using R1 R2
        by (simp add: TS_def)
    qed
    then have "A B OS P Q"
      using P2 l9_8_1 by blast
    then have "\<exists> Q. A B Perp Q C \<and> A B OS P Q"
      using Q4 by blast
  }
  thus ?thesis using P3 by blast
qed

lemma ex_per_cong:
  assumes "A \<noteq> B" and
    "X \<noteq> Y" and
    "Col A B C" and
    "\<not> Col A B D"
  shows "\<exists> P. Per P C A \<and> Cong P C X Y \<and> A B OS P D"
proof -
  obtain Q where P1: "A B Perp Q C \<and> A B OS D Q"
    using assms(3) assms(4) l10_15 by blast
  obtain P where P2: "C Out Q P \<and> Cong C P X Y"
    by (metis P1 assms(2) perp_not_eq_2 segment_construction_3)
  have P3: "Per P C A"
    using P1 P2 assms(3) col_trivial_3 l8_16_1 l8_3 out_col by blast
  have "A B OS P D"
    using P1 P2 assms(3) one_side_symmetry os_out_os by blast
  thus ?thesis
    using P2 P3 cong_left_commutativity by blast
qed

lemma exists_cong_per:
  "\<exists> C. Per A B C \<and> Cong B C X Y"
proof cases
  assume "A = B"
  thus ?thesis
    by (meson Tarski_neutral_dimensionless.l8_5 Tarski_neutral_dimensionless_axioms l8_2 segment_construction)
next
  assume "A \<noteq> B"
  thus ?thesis
    by (metis Perp_perm bet_col between_trivial l8_16_1 l8_21 segment_construction)
qed

subsubsection "Upper dim 2"

lemma upper_dim_implies_per2__col:
  assumes "upper_dim_axiom"
  shows "\<forall> A B C X. (Per A X C \<and> X \<noteq> C \<and> Per B X C) \<longrightarrow> Col A B X"
proof -
  {
    fix A B C X
    assume "Per A X C \<and> X \<noteq> C \<and> Per B X C"
    moreover then obtain C' where "X Midpoint C C' \<and> Cong A C A C'"
      using Per_def by blast
    ultimately have "Col A B X"
      by (smt Col_def assms midpoint_cong midpoint_distinct_2 not_cong_2134 per_double_cong upper_dim_axiom_def)
  }
  then show ?thesis by blast
qed

lemma upper_dim_implies_col_perp2__col:
  assumes "upper_dim_axiom"
  shows "\<forall> A B X Y P. (Col A B P \<and> A B Perp X P \<and> P A Perp Y P) \<longrightarrow> Col Y X P"
proof -
  {
    fix A B X Y P
    assume H1: "Col A B P \<and> A B Perp X P \<and> P A Perp Y P"
    then have H2: "P \<noteq> A"
      using perp_not_eq_1 by blast
    have "Col Y X P"
    proof -
      have T1: "Per Y P A"
        using H1 l8_2 perp_per_1 by blast
      moreover have "Per X P A"
        using H1 col_trivial_3 l8_16_1 by blast
      then show ?thesis using T1 H2
        using assms upper_dim_implies_per2__col by blast
    qed
  }
  then show ?thesis by blast
qed

lemma upper_dim_implies_perp2__col:
  assumes "upper_dim_axiom"
  shows "\<forall> X Y Z A B. (X Y Perp A B \<and> X Z Perp A B) \<longrightarrow> Col X Y Z"
proof -
  {
    fix X Y Z A B
    assume H1: "X Y Perp A B \<and> X Z Perp A B"
    then have H1A: "X Y Perp A B" by blast
    have H1B: "X Z Perp A B" using H1 by blast
    obtain C where H2: "C PerpAt X Y A B"
      using H1 Perp_def by blast
    obtain C' where H3: "C' PerpAt X Z A B"
      using H1 Perp_def by blast
    have "Col X Y Z"
    proof cases
      assume H2: "Col A B X"
      {
        assume "X = A"
        then have "Col X Y Z" using upper_dim_implies_col_perp2__col
          by (metis H1 H2 Perp_cases assms col_permutation_1)
      }
      then have P1: "X = A \<longrightarrow> Col X Y Z" by blast
      {
        assume P2: "X \<noteq> A"
        then have P3: "A B Perp X Y" using perp_sym
          using H1 Perp_perm by blast
        have "Col A B X"
          by (simp add: H2)
        then have P4: "A X Perp X Y" using perp_col
          using P2 P3 by auto
        have P5: "A X Perp X Z"
          by (metis H1 H2 P2 Perp_perm col_trivial_3 perp_col0)
        have P6: "Col Y Z X"
        proof -
          have Q1: "upper_dim_axiom"
            by (simp add: assms)
          have Q2: "Per Y X A"
            using P4 Perp_cases perp_per_2 by blast
          have "Per Z X A"
            by (meson P5 Tarski_neutral_dimensionless.Perp_cases Tarski_neutral_dimensionless_axioms perp_per_2)
          then show ?thesis using Q1 Q2 P2
            using upper_dim_implies_per2__col by blast
        qed
        then have "Col X Y Z"
          using Col_perm by blast
      }
      then show ?thesis
        using P1 by blast
    next
      assume T1: "\<not> Col A B X"
      obtain Y0 where Q3: "Y0 PerpAt X Y A B"
        using H1 Perp_def by blast
      obtain Z0 where Q4: "Z0 PerpAt X Z A B"
        using Perp_def H1 by blast
      have Q5: "X Y0 Perp A B"
      proof -
        have R1: "X \<noteq> Y0"
          using Q3 T1 perp_in_col by blast
        have R2: "X Y Perp A B"
          by (simp add: H1A)
        then show ?thesis using R1
          using Q3 perp_col perp_in_col by blast
      qed
      have "X Z0 Perp A B"
        by (metis H1B Q4 T1 perp_col perp_in_col)
      then have Q7: "Y0 = Z0"
        by (meson Q3 Q4 Q5 T1 Tarski_neutral_dimensionless.Perp_perm Tarski_neutral_dimensionless_axioms l8_18_uniqueness perp_in_col)
      have "Col X Y Z"
      proof -
        have "X \<noteq> Y0"
          using Q5 perp_distinct by auto
        moreover have "Col X Y0 Y"
          using Q3 not_col_permutation_5 perp_in_col by blast
        moreover have "Col X Y0 Z"
          using Q4 Q7 col_permutation_5 perp_in_col by blast
        ultimately show ?thesis
          using col_transitivity_1 by blast
      qed
      then show ?thesis using l8_18_uniqueness
        by (smt H1 H2 Perp_cases T1 col_trivial_3 perp_col1 perp_in_col perp_not_col)
    qed
  }
  then show ?thesis by blast
qed

lemma upper_dim_implies_not_two_sides_one_side_aux:
  assumes "upper_dim_axiom"
  shows "\<forall> A B X Y PX. (A \<noteq> B \<and> PX \<noteq> A \<and> A B Perp X PX \<and> Col A B PX \<and> \<not> Col X A B \<and> \<not> Col Y A B \<and> \<not> A B TS X Y) \<longrightarrow> A B OS X Y"
proof -
  {
    fix A B X Y PX
    assume H1: "A \<noteq> B \<and> PX \<noteq> A \<and> A B Perp X PX \<and> Col A B PX \<and> \<not> Col X A B \<and> \<not> Col Y A B \<and> \<not> A B TS X Y"
    have H1A: "A \<noteq> B" using H1 by simp
    have H1B: "PX \<noteq> A" using H1 by simp
    have H1C: "A B Perp X PX" using H1 by simp
    have H1D: "Col A B PX" using H1 by simp
    have H1E: "\<not> Col X A B" using H1 by simp
    have H1F: "\<not> Col Y A B" using H1 by simp
    have H1G: "\<not> A B TS X Y" using H1 by simp
    have "\<exists> P T. PX A Perp P PX \<and> Col PX A T \<and> Bet Y T P"
      using H1B l8_21 by blast
    then obtain P T where T1: "PX A Perp P PX \<and> Col PX A T \<and> Bet Y T P"
      by blast
    have J1: "PX A Perp P PX" using T1 by blast
    have J2: "Col PX A T" using T1 by blast
    have J3: "Bet Y T P" using T1 by blast
    have P9: "Col P X PX" using upper_dim_implies_col_perp2__col
      using H1C H1D J1 assms by blast
    have J4: "\<not> Col P A B"
      using H1A H1D T1 col_trivial_2 colx not_col_permutation_3 perp_not_col by blast
    have J5: "PX A TS P Y"
    proof -
      have f1: "Col PX A B"
        using H1D not_col_permutation_1 by blast
      then have f2: "Col B PX A"
        using not_col_permutation_1 by blast
      have f3: "\<forall>p. (T = A \<or> Col p A PX) \<or> \<not> Col p A T"
        by (metis J2 l6_16_1)
      have f4: "Col T PX A"
        using J2 not_col_permutation_1 by blast
      have f5: "\<forall>p. Col p PX B \<or> \<not> Col p PX A"
        using f2 by (meson H1B l6_16_1)
      have f6: "\<forall>p. (B = PX \<or> Col p B A) \<or> \<not> Col p B PX"
        using H1D l6_16_1 by blast
      have f7: "\<forall>p pa. ((B = PX \<or> Col p PX pa) \<or> \<not> Col p PX B) \<or> \<not> Col pa PX A"
        using f5 by (metis l6_16_1)
      have f8: "\<forall>p. ((T = A \<or> B = PX) \<or> Col p A B) \<or> \<not> Col p A PX"
        using f2 by (metis H1B l6_16_1 not_col_permutation_1)
      have "Col B T PX"
        using f5 f4 not_col_permutation_1 by blast
      then have f9: "\<forall>p. (T = PX \<or> Col p T B) \<or> \<not> Col p T PX"
        using l6_16_1 by blast
      have "B = PX \<longrightarrow> \<not> Col Y PX A \<and> \<not> Col P PX A"
        using f1 by (metis (no_types) H1B H1F J4 l6_16_1 not_col_permutation_1)
      then show ?thesis
        using f9 f8 f7 f6 f5 f4 f3 by (metis (no_types) H1B H1F J3 J4 TS_def l9_2 not_col_permutation_1)
    qed
    have J6: "X \<noteq> PX"
      using H1 perp_not_eq_2 by blast
    have J7: "P \<noteq> X"
      using H1A H1D H1G J5 col_preserves_two_sides col_trivial_2 not_col_permutation_1 by blast
    have J8: "Bet X PX P \<or> PX Out X P \<or> \<not> Col X PX P"
      using l6_4_2 by blast
    have J9: "PX A TS P X"
      by (metis H1A H1D H1G J5 J6 J8 Out_cases P9 TS_def bet__ts between_symmetry col_permutation_1 col_preserves_two_sides col_trivial_2 l9_5)
    then have "A B OS X Y"
      by (meson H1A H1D J5 col2_os__os col_trivial_2 l9_2 l9_8_1 not_col_permutation_1)
  }
  then show ?thesis by blast
qed

lemma upper_dim_implies_not_two_sides_one_side:
  assumes "upper_dim_axiom"
  shows "\<forall> A B X Y. (\<not> Col X A B \<and> \<not> Col Y A B \<and> \<not> A B TS X Y) \<longrightarrow> A B OS X Y"
proof -
  {
    fix A B X Y
    assume H1: "\<not> Col X A B \<and> \<not> Col Y A B \<and> \<not> A B TS X Y"
    have H1A: "\<not> Col X A B" using H1 by simp
    have H1B: "\<not> Col Y A B" using H1 by simp
    have H1C: "\<not> A B TS X Y" using H1 by simp
    have P1: "A \<noteq> B"
      using H1A col_trivial_2 by blast
    obtain PX where P2: "Col A B PX \<and> A B Perp X PX"
      using Col_cases H1 l8_18_existence by blast
    have "A B OS X Y"
    proof cases
      assume H5: "PX = A"
      have "B A OS X Y"
      proof -
        have F1: "B A Perp X A"
          using P2 Perp_perm H5 by blast
        have F2: "Col B A A"
          using not_col_distincts by blast
        have F3: "\<not> Col X B A"
          using Col_cases H1A by blast
        have F4: "\<not> Col Y B A"
          using Col_cases H1B by blast
        have "\<not> B A TS X Y"
          using H1C invert_two_sides by blast
        then show ?thesis
          by (metis F1 F3 F4 assms col_trivial_2 upper_dim_implies_not_two_sides_one_side_aux)
      qed
      then show ?thesis
        by (simp add: invert_one_side)
    next
      assume "PX \<noteq> A"
      then show ?thesis
        using H1 P1 P2 assms upper_dim_implies_not_two_sides_one_side_aux by blast
    qed
  }
  then show ?thesis by blast
qed

lemma upper_dim_implies_not_one_side_two_sides:
  assumes "upper_dim_axiom"
  shows "\<forall> A B X Y. (\<not> Col X A B \<and> \<not> Col Y A B \<and> \<not> A B OS X Y) \<longrightarrow> A B TS X Y"
  using assms upper_dim_implies_not_two_sides_one_side by blast

lemma upper_dim_implies_one_or_two_sides:
  assumes "upper_dim_axiom"
  shows "\<forall> A B X Y. (\<not> Col X A B \<and> \<not> Col Y A B) \<longrightarrow> (A B TS X Y \<or> A B OS X Y)"
  using assms upper_dim_implies_not_two_sides_one_side by blast

lemma upper_dim_implies_all_coplanar:
  assumes "upper_dim_axiom"
  shows "all_coplanar_axiom"
  using all_coplanar_axiom_def assms upper_dim_axiom_def by auto

lemma all_coplanar_implies_upper_dim:
  assumes "all_coplanar_axiom"
  shows "upper_dim_axiom"
  using all_coplanar_axiom_def assms upper_dim_axiom_def by auto

lemma all_coplanar_upper_dim:
  shows "all_coplanar_axiom \<longleftrightarrow> upper_dim_axiom"
  using all_coplanar_implies_upper_dim upper_dim_implies_all_coplanar by auto

lemma upper_dim_stab:
  shows "\<not> \<not> upper_dim_axiom \<longrightarrow> upper_dim_axiom" by blast

lemma cop__cong_on_bissect:
  assumes "Coplanar A B X P" and
    "M Midpoint A B" and
    "M PerpAt A B P M" and
    "Cong X A X B"
  shows "Col M P X"
proof -
  have P1: "X = M \<or> \<not> Col A B X \<and> M PerpAt X M A B"
    using assms(2) assms(3) assms(4) cong_commutativity cong_perp_or_mid perp_in_distinct by blast
  {
    assume H1: "\<not> Col A B X \<and> M PerpAt X M A B"
    then have Q1: "X M Perp A B"
      using perp_in_perp by blast
    have Q2: "A B Perp P M"
      using assms(3) perp_in_perp by blast
    have P2: "Col M A B"
      by (simp add: assms(2) midpoint_col)
    then have "Col M P X" using cop_perp2__col
      by (meson Perp_perm Q1 Q2 assms(1) coplanar_perm_1)
  }
  then show ?thesis
    using P1 not_col_distincts by blast
qed

lemma cong_cop_mid_perp__col:
  assumes "Coplanar A B X P" and
    "Cong A X B X" and
    "M Midpoint A B" and
    "A B Perp P M"
  shows "Col M P X"
proof -
  have "M PerpAt A B P M"
    using Col_perm assms(3) assms(4) bet_col l8_15_1 midpoint_bet by blast
  then show ?thesis
    using assms(1) assms(2) assms(3) cop__cong_on_bissect not_cong_2143 by blast
qed

lemma cop_image_in2__col:
  assumes "Coplanar A B P Q" and
    "M ReflectLAt P P' A B" and
    "M ReflectLAt Q Q' A B"
  shows "Col M P Q"
proof -
  have P1: "P P' ReflectL A B"
    using assms(2) image_in_is_image_spec by auto
  then have P2: "A B Perp P' P \<or> P' = P"
    using ReflectL_def by auto
  have P3: "Q Q' ReflectL A B"
    using assms(3) image_in_is_image_spec by blast
  then have P4: "A B Perp Q' Q \<or> Q' = Q"
    using ReflectL_def by auto
  {
    assume S1: "A B Perp P' P \<and> A B Perp Q' Q"
    {
      assume T1: "A = M"
      have T2: "Per B A P"
        by (metis P1 Perp_perm S1 T1 assms(2) image_in_col is_image_is_image_spec l10_14 perp_col1 perp_distinct perp_per_1 ts_distincts)
      have T3: "Per B A Q"
        by (metis S1 T1 assms(3) image_in_col l8_5 perp_col1 perp_per_1 perp_right_comm)
      have T4: "Coplanar B P Q A"
        using assms(1) ncoplanar_perm_18 by blast
      have T5: "B \<noteq> A"
        using S1 perp_distinct by blast
      have T6: "Per P A B"
        by (simp add: T2 l8_2)
      have T7: "Per Q A B"
        using Per_cases T3 by blast
      then have "Col P Q A" using T4 T5 T6
        using cop_per2__col by blast
      then have "Col A P Q"
        using not_col_permutation_1 by blast
      then have "Col M P Q"
        using T1 by blast
    }
    then have S2: "A = M \<longrightarrow> Col M P Q" by blast
    {
      assume D0: "A \<noteq> M"
      have D1: "Per A M P"
      proof -
        have E1: "M Midpoint P P'"
          using ReflectLAt_def assms(2) l7_2 by blast
        have "Cong P A P' A"
          using P1 col_trivial_3 is_image_spec_col_cong by blast
        then have "Cong A P A P'"
          using Cong_perm by blast
        then show ?thesis
          using E1 Per_def by blast
      qed
      have D2: "Per A M Q"
      proof -
        have E2: "M Midpoint Q Q'"
          using ReflectLAt_def assms(3) l7_2 by blast
        have "Cong A Q A Q'"
          using P3 col_trivial_3 cong_commutativity is_image_spec_col_cong by blast
        then show ?thesis
          using E2 Per_def by blast
      qed
      have "Col P Q M"
      proof -
        have W1: "Coplanar P Q A B"
          using assms(1) ncoplanar_perm_16 by blast
        have W2: "A \<noteq> B"
          using S1 perp_distinct by blast
        have "Col A B M"
          using ReflectLAt_def assms(2) by blast
        then have "Coplanar P Q A M"
          using W1 W2 col2_cop__cop col_trivial_3 by blast
        then have V1: "Coplanar A P Q M"
          using ncoplanar_perm_8 by blast
        have V3: "Per P M A"
          by (simp add: D1 l8_2)
        have "Per Q M A"
          using D2 Per_perm by blast
        then show ?thesis
          using V1 D0 V3 cop_per2__col by blast
      qed
      then have "Col M P Q"
        using Col_perm by blast
    }
    then have "A \<noteq> M \<longrightarrow> Col M P Q" by blast
    then have "Col M P Q"
      using S2 by blast
  }
  then have P5: "(A B Perp P' P \<and> A B Perp Q' Q) \<longrightarrow> Col M P Q" by blast
  have P6: "(A B Perp P' P \<and> (Q' = Q)) \<longrightarrow> Col M P Q"
    using ReflectLAt_def assms(3) l7_3 not_col_distincts by blast
  have P7: "(P' = P \<and> A B Perp Q' Q) \<longrightarrow> Col M P Q"
    using ReflectLAt_def assms(2) l7_3 not_col_distincts by blast
  have "(P' = P \<and> Q' = Q) \<longrightarrow> Col M P Q"
    using ReflectLAt_def assms(3) col_trivial_3 l7_3 by blast
  then show ?thesis
    using P2 P4 P5 P6 P7 by blast
qed

lemma l10_10_spec:
  assumes "P' P ReflectL A B" and
    "Q' Q ReflectL A B"
  shows "Cong P Q P' Q'"
proof cases
  assume "A = B"
  then show ?thesis
    using assms(1) assms(2) cong_reflexivity image_spec__eq by blast
next
  assume H1: "A \<noteq> B"
  obtain X where P1: "X Midpoint P P' \<and> Col A B X"
    using ReflectL_def assms(1) by blast
  obtain Y where P2: "Y Midpoint Q Q' \<and> Col A B Y"
    using ReflectL_def assms(2) by blast
  obtain Z where P3: "Z Midpoint X Y"
    using midpoint_existence by blast
  have P4: "Col A B Z"
  proof cases
    assume "X = Y"
    then show ?thesis
      by (metis P2 P3 midpoint_distinct_3)
  next
    assume "X \<noteq> Y"
    then show ?thesis
      by (metis P1 P2 P3 l6_21 midpoint_col not_col_distincts)
  qed
  obtain R where P5: "Z Midpoint P R"
    using symmetric_point_construction by blast
  obtain R' where P6: "Z Midpoint P' R'"
    using symmetric_point_construction by blast
  have P7: "A B Perp P P' \<or> P = P'"
    using ReflectL_def assms(1) by auto
  have P8: "A B Perp Q Q' \<or> Q = Q'"
    using ReflectL_def assms(2) by blast
  {
    assume Q1: "A B Perp P P' \<and> A B Perp Q Q'"
    have Q2: "R R' ReflectL A B"
    proof -
      have "P P' Reflect A B"
        by (simp add: H1 assms(1) is_image_is_image_spec l10_4_spec)
      then have "R R' Reflect A B"
        using H1 P4 P5 P6 midpoint_preserves_image by blast
      then show ?thesis
        using H1 is_image_is_image_spec by blast
    qed
    have Q3: "R \<noteq> R'"
      using P5 P6 Q1 l7_9 perp_not_eq_2 by blast
    have Q4: "Y Midpoint R R'"
      using P1 P3 P5 P6 symmetry_preserves_midpoint by blast
    have Q5: "Cong Q' R' Q R"
      using P2 Q4 l7_13 by blast
    have Q6: "Cong P' Z P Z"
      using P4 assms(1) is_image_spec_col_cong by auto
    have Q7: "Cong Q' Z Q Z"
      using P4 assms(2) is_image_spec_col_cong by blast
    then have "Cong P Q P' Q'"
    proof -
      have S1: "Cong R Z R' Z"
        using P5 P6 Q6 cong_symmetry l7_16 l7_3_2 by blast
      have "R \<noteq> Z"
        using Q3 S1 cong_reverse_identity by blast
      then show ?thesis
        by (meson P5 P6 Q5 Q6 Q7 S1 between_symmetry five_segment midpoint_bet not_cong_2143 not_cong_3412)
    qed
  }
  then have P9: "(A B Perp P P' \<and> A B Perp Q Q') \<longrightarrow> Cong P Q P' Q'" by blast
  have P10: "(A B Perp P P' \<and> Q = Q') \<longrightarrow> Cong P Q P' Q'"
    using P2 Tarski_neutral_dimensionless.l7_3 Tarski_neutral_dimensionless_axioms assms(1) cong_symmetry is_image_spec_col_cong by fastforce
  have P11: "(P = P' \<and> A B Perp Q Q') \<longrightarrow> Cong P Q P' Q'"
    using P1 Tarski_neutral_dimensionless.l7_3 Tarski_neutral_dimensionless.not_cong_4321 Tarski_neutral_dimensionless_axioms assms(2) is_image_spec_col_cong by fastforce
  have "(P = P' \<and> Q = Q') \<longrightarrow> Cong P Q P' Q'"
    using cong_reflexivity by blast
  then show ?thesis
    using P10 P11 P7 P8 P9 by blast
qed

lemma l10_10:
  assumes "P' P Reflect A B" and
    "Q' Q Reflect A B"
  shows "Cong P Q P' Q'"
  using Reflect_def assms(1) assms(2) cong_4321 l10_10_spec l7_13 by auto

lemma image_preserves_bet:
  assumes "A A' ReflectL X Y" and
    "B B' ReflectL X Y" and
    "C C' ReflectL X Y" and
    "Bet A B C"
  shows "Bet A' B' C'"
proof -
  have P3: "A B C Cong3 A' B' C'"
    using Cong3_def assms(1) assms(2) assms(3) l10_10_spec l10_4_spec by blast
  then show ?thesis
    using assms(4) l4_6 by blast
qed

lemma image_gen_preserves_bet:
  assumes "A A' Reflect X Y" and
    "B B' Reflect X Y" and
    "C C' Reflect X Y" and
    "Bet A B C"
  shows "Bet A' B' C'"
proof cases
  assume "X = Y"
  then show ?thesis
    by (metis (full_types) assms(1) assms(2) assms(3) assms(4) image__midpoint l7_15 l7_2)
next
  assume P1: "X \<noteq> Y"
  then have P2: "A A' ReflectL X Y"
    using assms(1) is_image_is_image_spec by blast
  have P3: "B B' ReflectL X Y"
    using P1 assms(2) is_image_is_image_spec by auto
  have "C C' ReflectL X Y"
    using P1 assms(3) is_image_is_image_spec by blast
  then show ?thesis using image_preserves_bet
    using assms(4) P2 P3 by blast
qed

lemma image_preserves_col:
  assumes "A A' ReflectL X Y" and
    "B B' ReflectL X Y" and
    "C C' ReflectL X Y" and
    "Col A B C"
  shows "Col A' B' C'" using image_preserves_bet
  using Col_def assms(1) assms(2) assms(3) assms(4) by auto

lemma image_gen_preserves_col:
  assumes "A A' Reflect X Y" and
    "B B' Reflect X Y" and
    "C C' Reflect X Y" and
    "Col A B C"
  shows "Col A' B' C'"
  using Col_def assms(1) assms(2) assms(3) assms(4) image_gen_preserves_bet by auto

lemma image_gen_preserves_ncol:
  assumes "A A' Reflect X Y" and
    "B B' Reflect X Y" and
    "C C' Reflect X Y" and
    "\<not> Col A B C"
  shows "\<not> Col A' B' C'"
  using assms(1) assms(2) assms(3) assms(4)image_gen_preserves_col l10_4 by blast

lemma image_gen_preserves_inter:
  assumes "A A' Reflect X Y" and
    "B B' Reflect X Y" and
    "C C' Reflect X Y" and
    "D D' Reflect X Y" and
    "\<not> Col A B C" and
    "C \<noteq> D" and
    "Col A B I" and
    "Col C D I" and
    "Col A' B' I'" and
    "Col C' D' I'"
  shows "I I' Reflect X Y"
proof -
  obtain I0 where P1: "I I0 Reflect X Y"
    using l10_6_existence by blast
  then show ?thesis
    by (smt Tarski_neutral_dimensionless.image_gen_preserves_col Tarski_neutral_dimensionless_axioms assms(1) assms(10) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) l10_4 l10_7 l6_21)
qed

lemma intersection_with_image_gen:
  assumes "A A' Reflect X Y" and
    "B B' Reflect X Y" and
    "\<not> Col A B A'" and
    "Col A B C" and
    "Col A' B' C"
  shows "Col C X Y"
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) image_gen_preserves_inter l10_2_uniqueness l10_4 l10_8 not_col_distincts)

lemma image_preserves_midpoint :
  assumes "A A' ReflectL X Y" and
    "B B' ReflectL X Y" and
    "C C' ReflectL X Y" and
    "A Midpoint B C"
  shows "A' Midpoint B' C'"
proof -
  have P1: "Bet B' A' C'" using image_preserves_bet
    using assms(1) assms(2) assms(3) assms(4) midpoint_bet by auto
  have "Cong B' A' A' C'"
    by (metis Cong_perm Tarski_neutral_dimensionless.l10_10_spec Tarski_neutral_dimensionless.l7_13 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) cong_transitivity l7_3_2)
  then show ?thesis
    by (simp add: Midpoint_def P1)
qed

lemma image_spec_preserves_per:
  assumes "A A' ReflectL X Y" and
    "B B' ReflectL X Y" and
    "C C' ReflectL X Y" and
    "Per A B C"
  shows "Per A' B' C'"
proof cases
  assume "X = Y"
  then show ?thesis
    using assms(1) assms(2) assms(3) assms(4) image_spec__eq by blast
next
  assume P1: "X \<noteq> Y"
  obtain C1 where P2: "B Midpoint C C1"
    using symmetric_point_construction by blast
  obtain C1' where P3: "C1 C1' ReflectL X Y"
    by (meson P1 l10_6_existence_spec)
  then have P4: "B' Midpoint C' C1'"
    using P2 assms(2) assms(3) image_preserves_midpoint by blast
  have "Cong A' C' A' C1'"
  proof -
    have Q1: "Cong A' C' A C"
      using assms(1) assms(3) l10_10_spec by auto
    have "Cong A C A' C1'"
      by (metis P2 P3 Tarski_neutral_dimensionless.l10_10_spec Tarski_neutral_dimensionless_axioms assms(1) assms(4) cong_inner_transitivity cong_symmetry per_double_cong)
    then show ?thesis
      using Q1 cong_transitivity by blast
  qed
  then show ?thesis
    using P4 Per_def by blast
qed

lemma image_preserves_per:
  assumes "A A' Reflect X Y" and
    "B B' Reflect X Y"and
    "C C' Reflect X Y" and
    "Per A B C"
  shows "Per A' B' C'"
proof cases
  assume "X = Y"
  then show ?thesis using midpoint_preserves_per
    using assms(1) assms(2) assms(3) assms(4) image__midpoint l7_2  by blast
next
  assume P1: "X \<noteq> Y"
  have P2: "X \<noteq> Y \<and> A A' ReflectL X Y"
    using P1 assms(1) is_image_is_image_spec by blast
  have P3: "X \<noteq> Y \<and> B B' ReflectL X Y"
    using P1 assms(2) is_image_is_image_spec by blast
  have P4: "X \<noteq> Y \<and> C C' ReflectL X Y"
    using P1 assms(3) is_image_is_image_spec by blast
  then show ?thesis using image_spec_preserves_per
    using P2 P3 assms(4) by blast
qed

lemma l10_12:
  assumes "Per A B C" and
    "Per A' B' C'" and
    "Cong A B A' B'" and
    "Cong B C B' C'"
  shows "Cong A C A' C'"
proof cases
  assume P1: "B = C"
  then have "B' = C'"
    using assms(4) cong_reverse_identity by blast
  then show ?thesis
    using P1 assms(3) by blast
next
  assume P2: "B \<noteq> C"
  have "Cong A C A' C'"
  proof cases
    assume "A = B"
    then show ?thesis
      using assms(3) assms(4) cong_diff_3 by force
  next
    assume P3: "A \<noteq> B"
    obtain X where P4: "X Midpoint B B'"
      using midpoint_existence by blast
    obtain A1 where P5: "X Midpoint A' A1"
      using Mid_perm symmetric_point_construction by blast
    obtain C1 where P6: "X Midpoint C' C1"
      using Mid_perm symmetric_point_construction by blast
    have Q1: "A' B' C' Cong3 A1 B C1"
      using Cong3_def P4 P5 P6 l7_13 l7_2 by blast
    have Q2: "Per A1 B C1"
      using assms(2)Q1 l8_10  by blast
    have Q3: "Cong A B A1 B"
      by (metis Cong3_def Q1 Tarski_neutral_dimensionless.cong_symmetry Tarski_neutral_dimensionless_axioms assms(3) cong_inner_transitivity)
    have Q4: "Cong B C B C1"
      by (metis Cong3_def Q1 Tarski_neutral_dimensionless.cong_symmetry Tarski_neutral_dimensionless_axioms assms(4) cong_inner_transitivity)
    obtain Y where P7: "Y Midpoint C C1"
      using midpoint_existence by auto
    then have R1: "C1 C Reflect B Y" using cong_midpoint__image
      using Q4 by blast
    obtain A2 where R2: "A1 A2 Reflect B Y"
      using l10_6_existence by blast
    have R3: "Cong C A2 C1 A1"
      using R1 R2 l10_10 by blast
    have R5: "B B Reflect B Y"
      using image_triv by blast
    have R6: "Per A2 B C" using image_preserves_per
      using Q2 R1 R2 image_triv by blast
    have R7: "Cong A B A2 B"
      using l10_10 Cong_perm Q3 R2 cong_transitivity image_triv by blast
    obtain Z where R7A: "Z Midpoint A A2"
      using midpoint_existence by blast
    have "Cong B A B A2"
      using Cong_perm R7 by blast
    then have T1: "A2 A Reflect B Z" using  R7A cong_midpoint__image
      by blast
    obtain C0 where T2: "B Midpoint C C0"
      using symmetric_point_construction by blast
    have T3: "Cong A C A C0"
      using T2 assms(1) per_double_cong by blast
    have T4: "Cong A2 C A2 C0"
      using R6 T2 per_double_cong by blast
    have T5: "C0 C Reflect B Z"
    proof -
      have "C0 C Reflect Z B"
      proof cases
        assume "A = A2"
        then show ?thesis
          by (metis R7A T2 T3 cong_midpoint__image midpoint_distinct_3)
      next
        assume "A \<noteq> A2"
        then show ?thesis using l4_17 cong_midpoint__image
          by (metis R7A T2 T3 T4 midpoint_col not_col_permutation_3)
      qed
      then show ?thesis
        using is_image_rev by blast
    qed
    have T6: "Cong A C A2 C0"
      using T1 T5 l10_10 by auto
    have R4: "Cong A C A2 C"
      by (metis T4 T6 Tarski_neutral_dimensionless.cong_symmetry Tarski_neutral_dimensionless_axioms cong_inner_transitivity)
    then have Q5: "Cong A C A1 C1"
      by (meson R3 cong_inner_transitivity not_cong_3421)
    then show ?thesis
      using Cong3_def Q1 Q5 cong_symmetry cong_transitivity by blast
  qed
  then show ?thesis by blast
qed

lemma l10_16:
  assumes "\<not> Col A B C" and
    "\<not> Col A' B' P" and
    "Cong A B A' B'"
  shows "\<exists> C'. A B C Cong3 A' B' C' \<and> A' B' OS P C'"
proof cases
  assume "A = B"
  then show ?thesis
    using assms(1) not_col_distincts by auto
next
  assume P1: "A \<noteq> B"
  obtain X where P2: "Col A B X \<and> A B Perp C X"
    using assms(1) l8_18_existence by blast
  obtain X' where P3: "A B X Cong3 A' B' X'"
    using P2 assms(3) l4_14 by blast
  obtain Q where P4: "A' B' Perp Q X' \<and> A' B' OS P Q"
    using P2 P3 assms(2) l10_15 l4_13 by blast
  obtain C' where P5: "X' Out C' Q \<and> Cong X' C' X C"
    by (metis P2 P4 l6_11_existence perp_distinct)
  have P6: "Cong A C A' C'"
  proof cases
    assume "A = X"
    then show ?thesis
      by (metis Cong3_def P3 P5 cong_4321 cong_commutativity cong_diff_3)
  next
    assume "A \<noteq> X"
    have P7: "Per A X C"
      using P2 col_trivial_3 l8_16_1 l8_2 by blast
    have P8: "Per A' X' C'"
    proof -
      have "X' PerpAt A' X' X' C'"
      proof -
        have Z1: "A' X' Perp X' C'"
        proof -
          have W1: "X' \<noteq> C'"
            using P5 out_distinct by blast
          have W2: "X' Q Perp A' B'"
            using P4 Perp_perm by blast
          then have "X' C' Perp A' B'"
            by (metis P5 Perp_perm W1 col_trivial_3 not_col_permutation_5 out_col perp_col2_bis)
          then show ?thesis
            by (metis Cong3_def P2 P3 Perp_perm \<open>A \<noteq> X\<close> col_trivial_3 cong_identity l4_13 perp_col2_bis)
        qed
        have Z2: "Col X' A' X'"
          using not_col_distincts by blast
        have "Col X' X' C'"
          by (simp add: col_trivial_1)
        then show ?thesis
          by (simp add: Z1 Z2 l8_14_2_1b_bis)
      qed
      then show ?thesis
        by (simp add: perp_in_per)
    qed
    have P9: "Cong A X A' X'"
      using Cong3_def P3 by auto
    have "Cong X C X' C'"
      using Cong_perm P5 by blast
    then show ?thesis using l10_12
      using P7 P8 P9 by blast
  qed
  have P10: "Cong B C B' C'"
  proof cases
    assume "B = X"
    then show ?thesis
      by (metis Cong3_def P3 P5 cong_4321 cong_commutativity cong_diff_3)
  next
    assume "B \<noteq> X"
    have Q1: "Per B X C"
      using P2 col_trivial_2 l8_16_1 l8_2 by blast
    have "X' PerpAt B' X' X' C'"
    proof -
      have Q2: "B' X' Perp X' C'"
      proof -
        have R1: "B' \<noteq> X'"
          using Cong3_def P3 \<open>B \<noteq> X\<close> cong_identity by blast
        have "X' C' Perp B' A'"
        proof -
          have S1: "X' \<noteq> C'"
            using Out_def P5 by blast
          have S2: "X' Q Perp B' A'"
            using P4 Perp_perm by blast
          have "Col X' Q C'"
            using Col_perm P5 out_col by blast
          then show ?thesis
            using S1 S2 perp_col by blast
        qed
        then have R2: "B' A' Perp X' C'"
          using Perp_perm by blast
        have R3: "Col B' A' X'"
          using Col_perm P2 P3 l4_13 by blast
        then show ?thesis
          using R1 R2 perp_col by blast
      qed
      have Q3: "Col X' B' X'"
        by (simp add: col_trivial_3)
      have "Col X' X' C'"
        by (simp add: col_trivial_1)
      then show ?thesis using l8_14_2_1b_bis
        using Q2 Q3 by blast
    qed
    then have Q2: "Per B' X' C'"
      by (simp add: perp_in_per)
    have Q3: "Cong B X B' X'"
      using Cong3_def P3 by blast
    have Q4: "Cong X C X' C'"
      using P5 not_cong_3412 by blast
    then show ?thesis
      using Q1 Q2 Q3 l10_12 by blast
  qed
  have P12: "A' B' OS C' Q \<longleftrightarrow> X' Out C' Q \<and> \<not> Col A' B' C'" using l9_19 l4_13
    by (meson P2 P3 P5 one_side_not_col123 out_one_side_1)
  then have P13: "A' B' OS C' Q" using l4_13
    by (meson P2 P3 P4 P5 l6_6 one_side_not_col124 out_one_side_1)
  then show ?thesis
    using Cong3_def P10 P4 P6 assms(3) one_side_symmetry one_side_transitivity by blast
qed

lemma cong_cop_image__col:
  assumes "P \<noteq> P'" and
    "P P' Reflect A B" and
    "Cong P X P' X" and
    "Coplanar A B P X"
  shows "Col A B X"
proof -
  have P1: "(A \<noteq> B \<and> P P' ReflectL A B) \<or> (A = B \<and> A Midpoint P' P)"
    by (metis assms(2) image__midpoint is_image_is_image_spec)
  {
    assume Q1: "A \<noteq> B \<and> P P' ReflectL A B"
    then obtain M where Q2: "M Midpoint P' P \<and> Col A B M"
      using ReflectL_def by blast
    have "Col A B X"
    proof cases
      assume R1: "A = M"
      have R2: "P A Perp A B"
      proof -
        have S1: "P \<noteq> A"
          using Q2 R1 assms(1) midpoint_distinct_2 by blast
        have S2: "P P' Perp A B"
          using Perp_perm Q1 ReflectL_def assms(1) by blast
        have "Col P P' A"
          using Q2 R1 midpoint_col not_col_permutation_3 by blast
        then show ?thesis using perp_col
          using S1 S2 by blast
      qed
      have R3: "Per P A B"
        by (simp add: R2 perp_comm perp_per_1)
      then have R3A: "Per B A P" using l8_2
        by blast
      have "A Midpoint P P' \<and> Cong X P X P'"
        using Cong_cases Q2 R1 assms(3) l7_2 by blast
      then have R4: "Per X A P"
        using Per_def by blast
      have R5: "Coplanar P B X A"
        using assms(4) ncoplanar_perm_20 by blast
      have "P \<noteq> A"
        using R2 perp_not_eq_1 by auto
      then show ?thesis using R4 R5 R3A
        using cop_per2__col not_col_permutation_1 by blast
    next
      assume T1: "A \<noteq> M"
      have T3: "P \<noteq> M"
        using Q2 assms(1) l7_3_2 sym_preserve_diff by blast
      have T2: "P M Perp M A"
      proof -
        have T4: "P P' Perp M A"
          using Perp_perm Q1 Q2 ReflectL_def T1 assms(1) col_trivial_3 perp_col0 by blast
        have "Col P P' M"
          by (simp add: Col_perm Q2 midpoint_col)
        then show ?thesis using T3 T4 perp_col by blast
      qed
      then have "M P Perp A M"
        using perp_comm by blast
      then have "M PerpAt M P A M"
        using perp_perp_in by blast
      then have "M PerpAt P M M A"
        by (simp add: perp_in_comm)
      then have U1: "Per P M A"
        by (simp add: perp_in_per)
      have U2: "Per X M P" using l7_2 cong_commutativity
        using Per_def Q2 assms(3) by blast
      have "Col A X M"
      proof -
        have W2: "Coplanar P A X M"
          by (meson Q1 Q2 assms(4) col_cop2__cop coplanar_perm_13 ncop_distincts)
        have "Per A M P"
          by (simp add: U1 l8_2)
        then show ?thesis using cop_per2__col
          using U2 T3 W2 by blast
      qed
      then show ?thesis
        using Q2 T1 col2__eq not_col_permutation_4 by blast
    qed
  }
  then have P2: "(A \<noteq> B \<and> P P' ReflectL A B) \<longrightarrow> Col A B X" by blast
  have "(A = B \<and> A Midpoint P' P) \<longrightarrow> Col A B X"
    using col_trivial_1 by blast
  then show ?thesis using P1 P2 by blast
qed

lemma cong_cop_per2_1:
  assumes "A \<noteq> B" and
    "Per A B X" and
    "Per A B Y" and
    "Cong B X B Y" and
    "Coplanar A B X Y"
  shows "X = Y \<or> B Midpoint X Y"
  by (meson Per_cases assms(1) assms(2) assms(3) assms(4) assms(5) cop_per2__col coplanar_perm_3 l7_20_bis not_col_permutation_5)

lemma cong_cop_per2:
  assumes "A \<noteq> B" and
    "Per A B X" and
    "Per A B Y" and
    "Cong B X B Y" and
    "Coplanar A B X Y"
  shows "X = Y \<or> X Y ReflectL A B"
proof -
  have "X = Y \<or> B Midpoint X Y"
    using assms(1) assms(2) assms(3) assms(4) assms(5) cong_cop_per2_1 by blast
  then show ?thesis
    by (metis Mid_perm Per_def Reflect_def assms(1) assms(3) cong_midpoint__image symmetric_point_uniqueness)
qed

lemma cong_cop_per2_gen:
  assumes "A \<noteq> B" and
    "Per A B X" and
    "Per A B Y" and
    "Cong B X B Y" and
    "Coplanar A B X Y"
  shows "X = Y \<or> X Y Reflect A B"
proof -
  have "X = Y \<or> B Midpoint X Y"
    using assms(1) assms(2) assms(3) assms(4) assms(5) cong_cop_per2_1 by blast
  then show ?thesis
    using assms(2) cong_midpoint__image l10_4 per_double_cong by blast
qed

lemma ex_perp_cop:
  assumes "A \<noteq> B"
  shows "\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q"
proof -
  {
    assume "Col A B C \<and> Col A B P"
    then have "\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q"
      using assms ex_ncol_cop l10_15 ncop__ncols by blast
  }
  then have T1: "(Col A B C \<and> Col A B P) \<longrightarrow>
    (\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q)" by blast
  {
    assume "\<not>Col A B C \<and> Col A B P"
    then have "\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q"
      by (metis Perp_cases ncop__ncols not_col_distincts perp_exists)
  }
  then have T2: "(\<not>Col A B C \<and> Col A B P) \<longrightarrow>
    (\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q)" by blast

  {
    assume "Col A B C \<and> \<not>Col A B P"
    then have "\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q"
      using l10_15 os__coplanar by blast
  }
  then have T3: "(Col A B C \<and> \<not>Col A B P) \<longrightarrow>
    (\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q)" by blast
  {
    assume "\<not>Col A B C \<and> \<not>Col A B P"
    then have "\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q"
      using l8_18_existence ncop__ncols perp_right_comm by blast
  }
  then have "(\<not>Col A B C \<and> \<not>Col A B P) \<longrightarrow>
    (\<exists> Q. A B Perp Q C \<and> Coplanar A B P Q)" by blast
  then show ?thesis using T1 T2 T3 by blast
qed

lemma hilbert_s_version_of_pasch_aux:
  assumes "Coplanar A B C P" and
    "\<not> Col A I P" and
    "\<not> Col B C P" and
    "Bet B I C" and
    "B \<noteq> I" and
    "I \<noteq> C" and
    "B \<noteq> C"
  shows "\<exists> X. Col I P X \<and> ((Bet A X B \<and> A \<noteq> X \<and> X \<noteq> B \<and> A \<noteq> B) \<or> (Bet A X C \<and> A \<noteq> X \<and> X \<noteq> C \<and> A \<noteq> C))"
proof -
  have T1: "I P TS B C"
    using Col_perm assms(3) assms(4) assms(5) assms(6) bet__ts bet_col col_transitivity_1 by blast
  have T2: "Coplanar A P B I"
    using assms(1) assms(4) bet_cop__cop coplanar_perm_6 ncoplanar_perm_9 by blast
  have T3: "I P TS A B \<or> I P TS A C"
    by (meson T1 T2 TS_def assms(2) cop_nos__ts coplanar_perm_21 l9_2 l9_8_2)
  have T4: "I P TS A B \<longrightarrow>
(\<exists> X. Col I P X \<and>
            ((Bet A X B \<and> A \<noteq> X \<and> X \<noteq> B \<and> A \<noteq> B) \<or>
             (Bet A X C \<and> A \<noteq> X \<and> X \<noteq> C \<and> A \<noteq> C)))"
    by (metis TS_def not_col_permutation_2 ts_distincts)
  have "I P TS A C \<longrightarrow>
(\<exists> X. Col I P X \<and>
            ((Bet A X B \<and> A \<noteq> X \<and> X \<noteq> B \<and> A \<noteq> B) \<or>
             (Bet A X C \<and> A \<noteq> X \<and> X \<noteq> C \<and> A \<noteq> C)))"
    by (metis TS_def not_col_permutation_2 ts_distincts)

  then show ?thesis using T3 T4 by blast
qed

lemma hilbert_s_version_of_pasch:
  assumes "Coplanar A B C P" and
    "\<not> Col C Q P" and
    "\<not> Col A B P" and
    "BetS A Q B"
  shows "\<exists> X. Col P Q X \<and> (BetS A X C \<or> BetS B X C)"
proof -
  obtain X where "Col Q P X \<and>
(Bet C X A \<and> C \<noteq> X \<and> X \<noteq> A \<and> C \<noteq> A \<or>
        Bet C X B \<and> C \<noteq> X \<and> X \<noteq> B \<and> C \<noteq> B)"
    using BetSEq assms(1) assms(2) assms(3) assms(4) coplanar_perm_12 hilbert_s_version_of_pasch_aux by fastforce
  then show ?thesis
    by (metis BetS_def Bet_cases Col_perm)
qed

lemma two_sides_cases:
  assumes "\<not> Col PO A B" and
    "PO P OS A B"
  shows  "PO A TS P B \<or> PO B TS P A"
  by (meson assms(1) assms(2) cop_nts__os l9_31 ncoplanar_perm_3 not_col_permutation_4 one_side_not_col124 one_side_symmetry os__coplanar)

lemma not_par_two_sides:
  assumes "C \<noteq> D" and
    "Col A B I" and
    "Col C D I" and
    "\<not> Col A B C"
  shows "\<exists> X Y. Col C D X \<and> Col C D Y \<and> A B TS X Y"
proof -
  obtain pp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
    f1: "\<forall>p pa. Bet p pa (pp p pa) \<and> pa \<noteq> (pp p pa)"
    by (meson point_construction_different)
  then have f2: "\<forall>p pa pb pc. (Col pc pb p \<or> \<not> Col pc pb (pp p pa)) \<or> \<not> Col pc pb pa"
    by (meson Col_def colx)
  have f3: "\<forall>p pa. Col pa p pa"
    by (meson Col_def between_trivial)
  have f4: "\<forall>p pa. Col pa p p"
    by (meson Col_def between_trivial)
  have f5: "Col I D C"
    by (meson Col_perm assms(3))
  have f6: "\<forall>p pa. Col (pp pa p) p pa"
    using f4 f3 f2 by blast
  then have f7: "\<forall>p pa. Col pa (pp pa p) p"
    by (meson Col_perm)
  then have f8: "\<forall>p pa pb pc. (pc pb TS p (pp p pa) \<or> Col pc pb p) \<or> \<not> Col pc pb pa"
    using f2 f1 by (meson l9_18)
  have "I = D \<or> Col D (pp D I) C"
    using f7 f5 f3 colx by blast
  then have "I = D \<or> Col C D (pp D I)"
    using Col_perm by blast
  then show ?thesis
    using f8 f6 f3 by (metis Col_perm assms(2) assms(4))
qed

lemma cop_not_par_other_side:
  assumes "C \<noteq> D" and
    "Col A B I" and
    "Col C D I" and
    "\<not> Col A B C" and
    "\<not> Col A B P" and
    "Coplanar A B C P"
  shows "\<exists> Q. Col C D Q \<and> A B TS P Q"
proof -
  obtain X Y where P1:"Col C D X \<and> Col C D Y \<and> A B TS X Y"
    using assms(1) assms(2) assms(3) assms(4) not_par_two_sides by blast
  then have "Coplanar C A B X"
    using Coplanar_def assms(1) assms(2) assms(3) col_transitivity_1 by blast
  then have "Coplanar A B P X"
    using assms(4) assms(6) col_permutation_3 coplanar_trans_1 ncoplanar_perm_2 ncoplanar_perm_6 by blast
  then show ?thesis
    by (meson P1 l9_8_2 TS_def assms(5) cop_nts__os not_col_permutation_2 one_side_symmetry)
qed


lemma cop_not_par_same_side:
  assumes "C \<noteq> D" and
    "Col A B I" and
    "Col C D I" and
    "\<not> Col A B C" and
    "\<not> Col A B P" and
    "Coplanar A B C P"
  shows "\<exists> Q. Col C D Q \<and> A B OS P Q"
proof -
  obtain X Y where P1: "Col C D X \<and> Col C D Y \<and> A B TS X Y"
    using assms(1) assms(2) assms(3) assms(4) not_par_two_sides by blast
  then have "Coplanar C A B X"
    using Coplanar_def assms(1) assms(2) assms(3) col_transitivity_1 by blast
  then have "Coplanar A B P X"
    using assms(4) assms(6) col_permutation_1 coplanar_perm_2 coplanar_trans_1 ncoplanar_perm_14 by blast
  then show ?thesis
    by (meson P1 TS_def assms(5) cop_nts__os l9_2 l9_8_1 not_col_permutation_2)
qed

end

subsubsection "Line reflexivity: 2D"

context Tarski_2D

begin

lemma all_coplanar:
  "Coplanar A B C D"
proof -
  have "\<forall> A B C P Q. P \<noteq> Q \<longrightarrow> Cong A P A Q \<longrightarrow> Cong B P B Q\<longrightarrow> Cong C P C Q \<longrightarrow>
(Bet A B C \<or> Bet B C A \<or> Bet C A B)"
    using upper_dim by blast
  then show ?thesis using upper_dim_implies_all_coplanar
    by (smt Tarski_neutral_dimensionless.not_col_permutation_2 Tarski_neutral_dimensionless_axioms all_coplanar_axiom_def all_coplanar_implies_upper_dim coplanar_perm_9 ncop__ncol os__coplanar ts__coplanar upper_dim_implies_not_one_side_two_sides)
qed

lemma per2__col:
  assumes "Per A X C" and
    "X \<noteq> C" and
    "Per B X C"
  shows "Col A B X"
  using all_coplanar_axiom_def all_coplanar_upper_dim assms(1) assms(2) assms(3) upper_dim upper_dim_implies_per2__col by blast

lemma perp2__col:
  assumes "X Y Perp A B" and
    "X Z Perp A B"
  shows "Col X Y Z"
  by (meson Tarski_neutral_dimensionless.cop_perp2__col Tarski_neutral_dimensionless_axioms all_coplanar assms(1) assms(2))
end

subsection "Angles"

subsubsection "Some generalites"

context Tarski_neutral_dimensionless

begin

lemma l11_3:
  assumes "A B C CongA D E F"
  shows "\<exists> A' C' D' F'. B Out A' A \<and> B Out C C' \<and> E Out D' D \<and> E Out F F' \<and> A' B C' Cong3 D' E F'"
proof -
  obtain A' C' D' F' where P1: "Bet B A A' \<and> Cong A A' E D \<and> Bet B C C' \<and> Cong C C' E F \<and> Bet E D D' \<and> Cong D D' B A \<and> Bet E F F' \<and> Cong F F' B C \<and> Cong A' C' D' F'" using CongA_def
    using assms by auto
  then have "A' B C' Cong3 D' E F'"
    by (meson Cong3_def between_symmetry l2_11_b not_cong_1243 not_cong_4312)
  thus ?thesis
    by (metis CongA_def P1 assms bet_out l6_6)
qed

lemma l11_aux:
  assumes "B Out A A'" and
    "E Out D D'" and
    "Cong B A' E D'" and
    "Bet B A A0" and
    "Bet E D D0" and
    "Cong A A0 E D" and
    "Cong D D0 B A"
  shows "Cong B A0 E D0 \<and> Cong A' A0 D' D0"
proof -
  have P2: "Cong B A0 E D0"
    by (meson Bet_cases assms(4) assms(5) assms(6) assms(7) l2_11_b not_cong_1243 not_cong_4312)
  have P3: "Bet B A A' \<or> Bet B A' A"
    using Out_def assms(1) by auto
  have P4: "Bet E D D' \<or> Bet E D' D"
    using Out_def assms(2) by auto
  have P5: "Bet B A A' \<longrightarrow> Cong A' A0 D' D0"
    by (smt P2 assms(1) assms(2) assms(3) assms(4) assms(5) bet_out l6_6 l6_7 out_cong_cong out_diff1)
  have P6: "Bet B A' A \<longrightarrow> Cong A' A0 D' D0"
  proof -
    have "E Out D D0"
      using assms(2) assms(5) bet_out out_diff1 by blast
    thus ?thesis
      by (meson P2 assms(2) assms(3) assms(4) between_exchange4 cong_preserves_bet l4_3_1 l6_6 l6_7)
  qed
  have P7: "Bet E D D' \<longrightarrow> Cong A' A0 D' D0"
    using P3 P5 P6 by blast
  have "Bet E D' D \<longrightarrow> Cong A' A0 D' D0"
    using P3 P5 P6 by blast
  thus ?thesis
    using P2 P3 P4 P5 P6 P7 by blast
qed

lemma l11_3_bis:
  assumes "\<exists> A' C' D' F'. (B Out A' A \<and> B Out C' C \<and> E Out D' D \<and> E Out F' F \<and> A' B C' Cong3 D' E F')"
  shows "A B C CongA D E F"
proof -
  obtain A' C' D' F' where P1:
    "B Out A' A \<and> B Out C' C \<and> E Out D' D \<and> E Out F' F \<and> A' B C' Cong3 D' E F'"
    using assms by blast
  obtain A0 where P2: "Bet B A A0 \<and> Cong A A0 E D"
    using segment_construction by presburger
  obtain C0 where P3: "Bet B C C0 \<and> Cong C C0 E F"
    using segment_construction by presburger
  obtain D0 where P4: "Bet E D D0 \<and> Cong D D0 B A"
    using segment_construction by presburger
  obtain F0 where P5: "Bet E F F0 \<and> Cong F F0 B C"
    using segment_construction by presburger
  have P6: "A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E"
    using P1 out_diff2 by blast
  have "Cong A0 C0 D0 F0"
  proof -
    have Q1: "Cong B A0 E D0 \<and> Cong A' A0 D' D0"
    proof -
      have R1: "B Out A A'"
        by (simp add: P1 l6_6)
      have R2: "E Out D D'"
        by (simp add: P1 l6_6)
      have "Cong B A' E D'"
        using Cong3_def P1 cong_commutativity by blast
      thus ?thesis using l11_aux
        using P2 P4 R1 R2 by blast
    qed
    have Q2: "Cong B C0 E F0 \<and> Cong C' C0 F' F0"
      by (smt Cong3_def Out_cases P1 P3 P5 Tarski_neutral_dimensionless.l11_aux Tarski_neutral_dimensionless_axioms)
    have Q3: "B A' A0 Cong3 E D' D0"
      by (meson Cong3_def P1 Q1 cong_3_swap)
    have Q4: "B C' C0 Cong3 E F' F0"
      using Cong3_def P1 Q2 by blast
    have "Cong C0 A' F0 D'"
    proof -
      have R1: "B C' C0 A' FSC E F' F0 D'"
      proof -
        have S1: "Col B C' C0"
          by (metis (no_types) Col_perm P1 P3 P6 bet_col col_transitivity_1 out_col)
        have S3: "Cong B A' E D'"
          using Cong3_def Q3 by blast
        have "Cong C' A' F' D'"
          using Cong3_def P1 cong_commutativity by blast
        thus ?thesis
          by (simp add: FSC_def S1 Q4 S3)
      qed
      have "B \<noteq> C'"
        using P1 out_distinct by blast
      thus ?thesis
        using R1 l4_16 by blast
    qed
    then have Q6: "B A' A0 C0 FSC E D' D0 F0"
      by (meson FSC_def P1 P2 P6 Q2 Q3 bet_out l6_7 not_cong_2143 out_col)
    have "B \<noteq> A'"
      using Out_def P1 by blast
    thus ?thesis
      using Q6 l4_16 by blast
  qed
  thus ?thesis using P6 P2 P3 P4 P5 CongA_def by auto
qed

lemma l11_4_1:
  assumes "A B C CongA D E F" and
    (*"A \<noteq> B" and "C \<noteq> B" and "D \<noteq> E" and "F \<noteq> E" and*)
    "B Out A' A" and
    "B Out C' C" and
    "E Out D' D" and
    "E Out F' F" and
    "Cong B A' E D'" and "Cong B C' E F'"
  shows "Cong A' C' D' F'"
proof -
  obtain A0 C0 D0 F0 where P1: "B Out A0 A \<and> B Out C C0 \<and> E Out D0 D \<and> E Out F F0 \<and> A0 B C0 Cong3 D0 E F0"
    using assms(1) l11_3 by blast
  have P2: "B Out A' A0"
    using P1 assms(2) l6_6 l6_7 by blast
  have P3: "E Out D' D0"
    by (meson P1 assms(4) l6_6 l6_7)
  have P4: "Cong A' A0 D' D0"
  proof -
    have "Cong B A0 E D0"
      using Cong3_def P1 cong_3_swap by blast
    thus ?thesis using P2 P3
      using assms(6) out_cong_cong by blast
  qed
  have P5: "Cong A' C0 D' F0"
  proof -
    have P6: "B A0 A' C0 FSC E D0 D' F0"
      by (meson Cong3_def Cong_perm FSC_def P1 P2 P4 assms(6) not_col_permutation_5 out_col)
    thus ?thesis
      using P2 Tarski_neutral_dimensionless.l4_16 Tarski_neutral_dimensionless_axioms out_diff2 by fastforce
  qed
  have P6: "B Out C' C0"
    using P1 assms(3) l6_7 by blast
  have "E Out F' F0"
    using P1 assms(5) l6_7 by blast
  then have "Cong C' C0 F' F0"
    using Cong3_def P1 P6 assms(7) out_cong_cong by auto
  then have P9: "B C0 C' A' FSC E F0 F' D'"
    by (smt Cong3_def Cong_perm FSC_def P1 P5 P6 assms(6) assms(7) not_col_permutation_5 out_col)
  then have "Cong C' A' F' D'"
    using P6 Tarski_neutral_dimensionless.l4_16 Tarski_neutral_dimensionless_axioms out_diff2 by fastforce
  thus ?thesis
    using Tarski_neutral_dimensionless.not_cong_2143 Tarski_neutral_dimensionless_axioms by fastforce
qed

lemma l11_4_2:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "D \<noteq> E" and
    "F \<noteq> E" and
    "\<forall> A' C' D' F'. (B Out A' A \<and> B Out C' C \<and> E Out D' D \<and> E Out F' F \<and> Cong B A' E D' \<and> Cong B C' E F' \<longrightarrow> Cong A' C' D' F')"
  shows "A B C CongA D E F"
proof -
  obtain A' where P1: "Bet B A A' \<and> Cong A A' E D"
    using segment_construction by fastforce
  obtain C' where P2: "Bet B C C' \<and> Cong C C' E F"
    using segment_construction by fastforce
  obtain D' where P3: "Bet E D D' \<and> Cong D D' B A"
    using segment_construction by fastforce
  obtain F' where P4: "Bet E F F' \<and> Cong F F' B C"
    using segment_construction by fastforce
  have P5: "Cong A' B D' E"
    by (meson Bet_cases P1 P3 l2_11_b not_cong_1243 not_cong_4312)
  have P6: "Cong B C' E F'"
    by (meson P2 P4 between_symmetry cong_3421 cong_right_commutativity l2_11_b)
  have "B Out A' A \<and> B Out C' C \<and> E Out D' D \<and> E Out F' F \<and> A' B C' Cong3 D' E F'"
    by (metis (no_types, lifting) Cong3_def P1 P2 P3 P4 P5 P6 Tarski_neutral_dimensionless.Out_def Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) assms(5) bet_neq12__neq cong_commutativity)
  thus ?thesis
    using l11_3_bis by blast
qed

lemma conga_refl:
  assumes "A \<noteq> B" and
    "C \<noteq> B"
  shows "A B C CongA A B C"
  by (meson CongA_def assms(1) assms(2) cong_reflexivity segment_construction)

lemma conga_sym:
  assumes "A B C CongA A' B' C'"
  shows "A' B' C' CongA A B C"
proof -
  obtain A0 C0 D0 F0 where
    P1: "Bet B A A0 \<and> Cong A A0 B' A' \<and> Bet B C C0 \<and> Cong C C0 B' C' \<and> Bet B' A' D0 \<and> Cong A' D0 B A \<and> Bet B' C' F0 \<and> Cong C' F0 B C \<and> Cong A0 C0 D0 F0"
    using CongA_def assms by auto
  thus ?thesis
  proof -
    have "\<exists>p pa pb pc. Bet B' A' p \<and> Cong A' p B A \<and> Bet B' C' pa \<and> Cong C' pa B C \<and>Bet B A pb \<and> Cong A pb B' A' \<and>Bet B C pc \<and> Cong C pc B' C' \<and> Cong p pa pb pc"
      by (metis (no_types) Tarski_neutral_dimensionless.cong_symmetry Tarski_neutral_dimensionless_axioms P1)
    thus ?thesis
      using CongA_def assms by auto
  qed
qed

lemma l11_10:
  assumes "A B C CongA D E F" and
    "B Out A' A" and
    "B Out C' C" and
    "E Out D' D" and
    "E Out F' F"
  shows "A' B C' CongA D' E F'"
proof -
  have P1: "A' \<noteq> B"
    using assms(2) out_distinct by auto
  have P2: "C' \<noteq> B"
    using Out_def assms(3) by force
  have P3: "D' \<noteq> E"
    using Out_def assms(4) by blast
  have P4: "F' \<noteq> E"
    using assms(5) out_diff1 by auto
  have P5: "\<forall> A'0 C'0 D'0 F'0. (B Out A'0 A' \<and> B Out C'0 C' \<and> E Out D'0 D' \<and> E Out F'0 F' \<and> Cong B A'0 E D'0 \<and> Cong B C'0 E F'0) \<longrightarrow> Cong A'0 C'0 D'0 F'0"
    by (meson assms(1) assms(2) assms(3) assms(4) assms(5) l11_4_1 l6_7)
  thus ?thesis using P1 P2 P3 P4 P5 l11_4_2 by blast
qed

lemma out2__conga:
  assumes "B Out A' A" and
    "B Out C' C"
  shows "A B C CongA A' B C'"
  by (smt assms(1) assms(2) between_trivial2 conga_refl l11_10 out2_bet_out out_distinct)

lemma cong3_diff:
  assumes "A \<noteq> B" and
    "A B C Cong3 A' B' C'"
  shows "A' \<noteq> B'"
  using Cong3_def assms(1) assms(2) cong_diff by blast

lemma cong3_diff2:
  assumes "B \<noteq> C" and
    "A B C Cong3 A' B' C'"
  shows "B' \<noteq> C'"
  using Cong3_def assms(1) assms(2) cong_diff by blast

lemma cong3_conga:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "A B C Cong3 A' B' C'"
  shows "A B C CongA A' B' C'"
  by (metis assms(1) assms(2) assms(3) cong3_diff cong3_diff2 l11_3_bis out_trivial)

lemma cong3_conga2:
  assumes "A B C Cong3 A' B' C'" and
    "A B C CongA A'' B'' C''"
  shows "A' B' C' CongA A'' B'' C''"
proof -
  obtain A0 C0 A2 C2 where P1: "Bet B A A0 \<and> Cong A A0 B'' A'' \<and> Bet B C C0 \<and> Cong C C0 B'' C''\<and> Bet B'' A'' A2 \<and> Cong A'' A2 B A \<and> Bet B'' C'' C2 \<and> Cong C'' C2 B C \<and> Cong A0 C0 A2 C2"
    using CongA_def assms(2) by auto
  obtain A1 where P5: "Bet B' A' A1 \<and> Cong A' A1 B'' A''"
    using segment_construction by blast
  obtain C1 where P6: "Bet B' C' C1 \<and> Cong C' C1 B'' C''"
    using segment_construction by blast
  have P7: "Cong A A0 A' A1"
  proof -
    have "Cong B'' A'' A' A1" using P5
      using Cong_perm by blast
    thus ?thesis
      using Cong_perm P1 cong_inner_transitivity by blast
  qed
  have P8: "Cong B A0 B' A1"
    using Cong3_def P1 P5 P7 assms(1) cong_commutativity l2_11_b by blast
  have P9: "Cong C C0 C' C1"
    using P1 P6 cong_inner_transitivity cong_symmetry by blast
  have P10: "Cong B C0 B' C1"
    using Cong3_def P1 P6 P9 assms(1) l2_11_b by blast
  have "B A A0 C FSC B' A' A1 C'"
    using FSC_def P1 P5 P7 P8 Tarski_neutral_dimensionless.Cong3_def Tarski_neutral_dimensionless_axioms assms(1) bet_col l4_3 by fastforce
  then have P12: "Cong A0 C A1 C'"
    using CongA_def assms(2) l4_16 by auto
  then have "B C C0 A0 FSC B' C' C1 A1"
    using Cong3_def FSC_def P1 P10 P8 P9 assms(1) bet_col cong_commutativity by auto
  then have P13: "Cong C0 A0 C1 A1"
    using l4_16 CongA_def assms(2) by blast
  have Q2: "Cong A' A1 B'' A''"
    using P1 P7 cong_inner_transitivity by blast
  have Q5: "Bet B'' A'' A2" using P1 by blast
  have Q6: "Cong A'' A2 B' A'"
  proof -
    have "Cong B A B' A'"
      using P1 P7 P8 P5 l4_3 by blast
    thus ?thesis
      using P1 cong_transitivity by blast
  qed
  have Q7: "Bet B'' C'' C2"
    using P1 by blast
  have Q8: "Cong C'' C2 B' C'"
  proof -
    have "Cong B C B' C'"
      using Cong3_def assms(1) by blast
    thus ?thesis
      using P1 cong_transitivity by blast
  qed
  have R2: "Cong C0 A0 C2 A2"
    using Cong_cases P1 by blast
  have "Cong C1 A1 A0 C0"
    using Cong_cases P13 by blast
  then have Q9: "Cong A1 C1 A2 C2"
    using R2 P13 cong_inner_transitivity not_cong_4321 by blast
  thus ?thesis
    using CongA_def P5 Q2 P6 Q5 Q6 Q7 Q8
    by (metis assms(1) assms(2) cong3_diff cong3_diff2)
qed

lemma conga_diff1:
  assumes "A B C CongA A' B' C'"
  shows "A \<noteq> B"
  using CongA_def assms by blast

lemma conga_diff2:
  assumes "A B C CongA A' B' C'"
  shows "C \<noteq> B"
  using CongA_def assms by blast

lemma conga_diff45:
  assumes "A B C CongA A' B' C'"
  shows "A' \<noteq> B'"
  using CongA_def assms by blast

lemma conga_diff56:
  assumes "A B C CongA A' B' C'"
  shows "C' \<noteq> B'"
  using CongA_def assms by blast

lemma conga_trans:
  assumes "A B C CongA A' B' C'" and
    "A' B' C' CongA A'' B'' C''"
  shows "A B C CongA A'' B'' C''"
proof -
  obtain A0 C0 A1 C1 where P1: "Bet B A A0 \<and> Cong A A0 B' A' \<and>
Bet B C C0 \<and> Cong C C0 B' C'\<and> Bet B' A' A1 \<and> Cong A' A1 B A \<and>
Bet B' C' C1 \<and> Cong C' C1 B C \<and> Cong A0 C0 A1 C1"
    using CongA_def assms(1) by auto
  have P2: "A''\<noteq> B'' \<and> C'' \<noteq> B''"
    using CongA_def assms(2) by auto
  have P3: "A1 B' C1 CongA A'' B'' C''"
  proof -
    have L2: "B' Out A1 A'" using P1
      by (metis Out_def assms(2) bet_neq12__neq conga_diff1)
    have L3: "B' Out C1 C'" using P1
      by (metis Out_def assms(1) bet_neq12__neq conga_diff56)
    have L4: "B'' Out A'' A''"
      using P2 out_trivial by auto
    have "B'' Out C'' C''"
      by (simp add: P2 out_trivial)
    thus ?thesis
      using assms(2) L2 L3 L4 l11_10 by blast
  qed
  have L6: "A0 B C0 CongA A' B' C'"
    by (smt Out_cases P1 Tarski_neutral_dimensionless.conga_diff1 Tarski_neutral_dimensionless.conga_diff2 Tarski_neutral_dimensionless.conga_diff45 Tarski_neutral_dimensionless_axioms assms(1) bet_out conga_diff56 l11_10 l5_3)
  have L7: "Cong B A0 B' A1"
    by (meson P1 between_symmetry cong_3421 l2_11_b not_cong_1243)
  have L8: "Cong B C0 B' C1"
    using P1 between_symmetry cong_3421 l2_11_b not_cong_1243 by blast
  have L10: "A0 B C0 Cong3 A1 B' C1"
    by (simp add: Cong3_def L7 L8 P1 cong_commutativity)
  then have L11: "A0 B C0 CongA A'' B'' C''"
    by (meson Tarski_neutral_dimensionless.cong3_conga2 Tarski_neutral_dimensionless_axioms P3 cong_3_sym)
  thus ?thesis using l11_10
  proof -
    have D2: "B Out A A0" using P1
      using CongA_def assms(1) bet_out by auto
    have D3: "B Out C C0" using P1
      using CongA_def assms(1) bet_out by auto
    have D4: "B'' Out A'' A''"
      using P2 out_trivial by blast
    have "B'' Out C'' C''"
      using P2 out_trivial by auto
    thus ?thesis using l11_10 L11 D2 D3 D4
      by blast
  qed
qed

lemma conga_pseudo_refl:
  assumes "A \<noteq> B" and
    "C \<noteq> B"
  shows "A B C CongA C B A"
  by (meson CongA_def assms(1) assms(2) between_trivial cong_pseudo_reflexivity segment_construction)

lemma conga_trivial_1:
  assumes "A \<noteq> B" and
    "C \<noteq> D"
  shows "A B A CongA C D C"
  by (meson CongA_def assms(1) assms(2) cong_trivial_identity segment_construction)

lemma l11_13:
  assumes "A B C CongA D E F" and
    "Bet A B A'" and
    "A'\<noteq> B" and
    "Bet D E D'" and
    "D'\<noteq> E"
  shows "A' B C CongA D' E F"
proof -
  obtain A'' C'' D'' F'' where P1:
    "Bet B A A'' \<and> Cong A A'' E D \<and>
Bet B C C'' \<and> Cong C C'' E F \<and> Bet E D D'' \<and>
Cong D D'' B A \<and>
Bet E F F'' \<and> Cong F F'' B C \<and> Cong A'' C'' D'' F''"
    using CongA_def assms(1) by auto
  obtain A0 where P2:"Bet B A' A0 \<and> Cong A' A0 E D'"
    using segment_construction by blast
  obtain D0 where P3: "Bet E D' D0 \<and> Cong D' D0 B A'"
    using segment_construction by blast
  have "Cong A0 C'' D0 F''"
  proof -
    have L1: "A'' B A0 C'' OFSC D'' E D0 F''"
    proof -
      have L2: "Bet A'' B A0"
      proof -
        have M1: "Bet A'' A B"
          using Bet_perm P1 by blast
        have M2: "Bet A B A0"
          using P2 assms(2) assms(3) outer_transitivity_between by blast
        have "A \<noteq> B"
          using CongA_def assms(1) by blast
        thus ?thesis
          using M1 M2 outer_transitivity_between2 by blast
      qed
      have L3: "Bet D'' E D0" using Bet_perm P1 P2 outer_transitivity_between CongA_def
        by (metis P3 assms(1) assms(4) assms(5))
      have L4: "Cong A'' B D'' E"
        by (meson P1 between_symmetry cong_3421 cong_left_commutativity l2_11_b)
      have L5: "Cong B A0 E D0"
        by (meson P2 P3 between_symmetry cong_3421 cong_right_commutativity l2_11_b)
      have "Cong B C'' E F''"
        by (meson P1 between_symmetry cong_3421 cong_right_commutativity l2_11_b)
      thus ?thesis using P1 L2 L3 L4 L5
        by (simp add: OFSC_def)
    qed
    have "A'' \<noteq> B"
      using CongA_def P1 assms(1) bet_neq12__neq by fastforce
    thus ?thesis
      using L1 five_segment_with_def by auto
  qed
  thus ?thesis
    using CongA_def P1 P2 P3 assms(1) assms(3) assms(5) by auto
qed

lemma conga_right_comm:
  assumes "A B C CongA D E F"
  shows "A B C CongA F E D"
  by (metis Tarski_neutral_dimensionless.conga_diff45 Tarski_neutral_dimensionless.conga_sym Tarski_neutral_dimensionless.conga_trans Tarski_neutral_dimensionless_axioms assms conga_diff56 conga_pseudo_refl)

lemma conga_left_comm:
  assumes "A B C CongA D E F"
  shows "C B A CongA D E F"
  by (meson assms conga_right_comm conga_sym)

lemma conga_comm:
  assumes "A B C CongA D E F"
  shows "C B A CongA F E D"
  by (meson Tarski_neutral_dimensionless.conga_left_comm Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless_axioms assms)

lemma conga_line:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "A' \<noteq> B'" and
    "B' \<noteq> C'"
    and "Bet A B C" and
    "Bet A' B' C'"
  shows "A B C CongA A' B' C'"
  by (metis Bet_cases assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) conga_trivial_1 l11_13)

lemma l11_14:
  assumes "Bet A B A'" and
    "A \<noteq> B" and
    "A' \<noteq> B" and
    "Bet C B C'" and
    "B \<noteq> C" and
    "B \<noteq> C'"
  shows "A B C CongA A' B C'"
  by (metis Bet_perm assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) conga_pseudo_refl conga_right_comm l11_13)

lemma l11_16:
  assumes "Per A B C" and
    "A \<noteq> B" and
    "C \<noteq> B" and
    "Per A' B' C'" and
    "A'\<noteq> B'" and
    "C'\<noteq> B'"
  shows "A B C CongA A' B' C'"
proof -
  obtain C0 where P1: "Bet B C C0 \<and> Cong C C0 B' C'"
    using segment_construction by blast
  obtain C1 where P2: "Bet B' C' C1 \<and> Cong C' C1 B C"
    using segment_construction by blast
  obtain A0 where P3: "Bet B A A0 \<and> Cong A A0 B' A'"
    using segment_construction by blast
  obtain A1 where P4: "Bet B' A' A1 \<and> Cong A' A1 B A"
    using segment_construction by blast
  have "Cong A0 C0 A1 C1"
  proof -
    have Q1: "Per A0 B C0"
      by (metis P1 P3 Tarski_neutral_dimensionless.l8_3 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) bet_col per_col)
    have Q2: "Per A1 B' C1"
      by (metis P2 P4 Tarski_neutral_dimensionless.l8_3 Tarski_neutral_dimensionless_axioms assms(4) assms(5) assms(6) bet_col per_col)
    have Q3: "Cong A0 B A1 B'"
      by (meson P3 P4 between_symmetry cong_3421 cong_left_commutativity l2_11_b)
    have "Cong B C0 B' C1"
      using P1 P2 between_symmetry cong_3421 l2_11_b not_cong_1243 by blast
    thus ?thesis
      using Q1 Q2 Q3 l10_12 by blast
  qed
  thus ?thesis
    using CongA_def P1 P2 P3 P4 assms(2) assms(3) assms(5) assms(6) by auto
qed

lemma l11_17:
  assumes "Per A B C" and
    "A B C CongA A' B' C'"
  shows "Per A' B' C'"
proof -
  obtain A0 C0 A1 C1 where P1: "Bet B A A0 \<and> Cong A A0 B' A' \<and> Bet B C C0 \<and> Cong C C0 B' C' \<and> Bet B' A' A1 \<and> Cong A' A1 B A \<and> Bet B' C' C1 \<and> Cong C' C1 B C \<and> Cong A0 C0 A1 C1"
    using CongA_def assms(2) by auto
  have P2: "Per A0 B C0"
  proof -
    have Q1: "B \<noteq> C"
      using assms(2) conga_diff2 by blast
    have Q2: "Per A0 B C"
      by (metis P1 Tarski_neutral_dimensionless.l8_2 Tarski_neutral_dimensionless_axioms assms(1) assms(2) bet_col conga_diff1 per_col)
    have "Col B C C0"
      using P1 bet_col by blast
    thus ?thesis
      using Q1 Q2 per_col by blast
  qed
  have P3: "Per A1 B' C1"
  proof -
    have "A0 B C0 Cong3 A1 B' C1"
      by (meson Bet_cases Cong3_def P1 l2_11_b not_cong_2134 not_cong_3421)
    thus ?thesis
      using P2 l8_10 by blast
  qed
  have P4: "B' \<noteq> C1"
    using P1 assms(2) between_identity conga_diff56 by blast
  have P5: "Per A' B' C1"
  proof -
    have P6: "B' \<noteq> A1"
      using P1 assms(2) between_identity conga_diff45 by blast
    have P7: "Per C1 B' A1"
      by (simp add: P3 l8_2)
    have "Col B' A1 A'"
      using P1 NCol_cases bet_col by blast
    thus ?thesis
      using P3 P6 Tarski_neutral_dimensionless.l8_3 Tarski_neutral_dimensionless_axioms by fastforce
  qed
  have "Col B' C1 C'"
    using P1 bet_col col_permutation_5 by blast
  thus ?thesis
    using P4 P5 per_col by blast
qed

lemma l11_18_1:
  assumes "Bet C B D" and
    "B \<noteq> C" and
    "B \<noteq> D" and
    "A \<noteq> B" and
    "Per A B C"
  shows "A B C CongA A B D"
  by (smt Tarski_neutral_dimensionless.l8_2 Tarski_neutral_dimensionless.l8_5 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) assms(5) bet_col col_per2__per l11_16)

lemma l11_18_2:
  assumes "Bet C B D" and
    "A B C CongA A B D"
  shows "Per A B C"
proof -
  obtain A0 C0 A1 D0 where P1: "Bet B A A0 \<and> Cong A A0 B A \<and> Bet B C C0 \<and>
Cong C C0 B D \<and> Bet B A A1 \<and> Cong A A1 B A \<and>
Bet B D D0 \<and> Cong D D0 B C \<and> Cong A0 C0 A1 D0"
    using CongA_def assms(2) by auto
  have P2: "A0 = A1"
    by (metis P1 assms(2) conga_diff45 construction_uniqueness)
  have P3: "Per A0 B C0"
  proof -
    have Q1: "Bet C0 B D0"
    proof -
      have R1: "Bet C0 C B"
        using P1 between_symmetry by blast
      have R2: "Bet C B D0"
      proof -
        have S1: "Bet C B D"
          by (simp add: assms(1))
        have S2: "Bet B D D0"
          using P1 by blast
        have "B \<noteq> D"
          using assms(2) conga_diff56 by blast
        thus ?thesis
          using S1 S2 outer_transitivity_between by blast
      qed
      have "C \<noteq> B"
        using assms(2) conga_diff2 by auto
      thus ?thesis
        using R1 R2 outer_transitivity_between2 by blast
    qed
    have Q2: "Cong C0 B B D0"
      by (meson P1 between_symmetry cong_3421 l2_11_b not_cong_1243)
    have "Cong A0 C0 A0 D0"
      using P1 P2 by blast
    thus ?thesis
      using Per_def Q1 Q2 midpoint_def by blast
  qed
  have P4: "B \<noteq> C0"
    using P1 assms(2) bet_neq12__neq conga_diff2 by blast
  have P5: "Per A B C0"
    by (metis P1 P3 Tarski_neutral_dimensionless.l8_3 Tarski_neutral_dimensionless_axioms assms(2) bet_col bet_col1 bet_neq21__neq col_transitivity_1 conga_diff45)
  have "Col B C0 C" using P1
    using NCol_cases bet_col by blast
  thus ?thesis
    using P4 P5 per_col by blast
qed

lemma cong3_preserves_out:
  assumes "A Out B C" and
    "A B C Cong3 A' B' C'"
  shows "A' Out B' C'"
  by (meson assms(1) assms(2) col_permutation_4 cong3_symmetry cong_3_swap l4_13 l4_6 not_bet_and_out or_bet_out out_col)

lemma l11_21_a:
  assumes "B Out A C" and
    "A B C CongA A' B' C'"
  shows "B' Out A' C'"
proof -
  obtain A0 C0 A1 C1 where P1: "Bet B A A0 \<and>
Cong A A0 B' A' \<and> Bet B C C0 \<and>
Cong C C0 B' C' \<and> Bet B' A' A1 \<and>
Cong A' A1 B A \<and> Bet B' C' C1 \<and>
Cong C' C1 B C \<and> Cong A0 C0 A1 C1"
    using CongA_def assms(2) by auto
  have P2: "B Out A0 C0"
    by (metis P1 assms(1) bet_out l6_6 l6_7 out_diff1)
  have P3: "B' Out A1 C1"
  proof -
    have "B A0 C0 Cong3 B' A1 C1"
      by (meson Cong3_def P1 between_symmetry cong_right_commutativity l2_11_b not_cong_4312)
    thus ?thesis
      using P2 cong3_preserves_out by blast
  qed
  thus ?thesis
    by (metis P1 assms(2) bet_out conga_diff45 conga_diff56 l6_6 l6_7)
qed

lemma l11_21_b:
  assumes "B Out A C" and
    "B' Out A' C'"
  shows "A B C CongA A' B' C'"
  by (smt assms(1) assms(2) between_trivial2 conga_trivial_1 l11_10 out2_bet_out out_distinct)

lemma conga_cop__or_out_ts:
  assumes "Coplanar A B C C'" and
    "A B C CongA A B C'"
  shows "B Out C C' \<or> A B TS C C'"
proof -
  obtain A0 C0 A1 C1 where P1: "Bet B A A0 \<and>
Cong A A0 B A \<and>Bet B C C0 \<and>
Cong C C0 B C' \<and>Bet B A A1 \<and>
Cong A A1 B A \<and>Bet B C' C1 \<and>
Cong C' C1 B C \<and> Cong A0 C0 A1 C1"
    using CongA_def assms(2) by auto
  have P2: "A0 = A1" using P1
    by (metis assms(2) conga_diff1 construction_uniqueness)
  have "B Out C C' \<or> A B TS C C'"
  proof cases
    assume "C0 = C1"
    thus ?thesis
      by (metis P1 assms(2) bet2__out conga_diff2 conga_diff56)
  next
    assume R1: "C0 \<noteq> C1"
    obtain M where R2: "M Midpoint C0 C1"
      using midpoint_existence by blast
    have R3: "Cong B C0 B C1"
      by (meson Bet_cases P1 l2_11_b not_cong_2134 not_cong_3421)
    have R3A: "Cong A0 C0 A0 C1"
      using P1 P2 by blast
    then have R4: "Per A0 M C0" using R2
      using Per_def by blast
    have R5: "Per B M C0"
      using Per_def R2 R3 by auto
    then have R6: "Per B M C1"
      using R2 l8_4 by blast
    have R7: "B \<noteq> A0"
      using P1 assms(2) bet_neq12__neq conga_diff45 by blast
    then have "Cong A C0 A C1"
      by (meson Col_perm P1 R3 R3A bet_col l4_17)
    then have R9: "Per A M C0"
      using Per_def R2 by blast
    then have R10: "Per A M C1"
      by (meson R2 Tarski_neutral_dimensionless.l8_4 Tarski_neutral_dimensionless_axioms)
    have R11: "Col B A M"
    proof -
      have S1: "Coplanar C0 B A M"
      proof -
        have "Coplanar B A C0 M"
        proof -
          have T1: "Coplanar B A C0 C1"
          proof -
            have "Coplanar A C0 B C'"
            proof -
              have "Coplanar A C' B C0"
              proof -
                have U1: "Coplanar A C' B C"
                  by (simp add: assms(1) coplanar_perm_4)
                have U2: "B \<noteq> C"
                  using assms(2) conga_diff2 by blast
                have "Col B C C0"
                  by (simp add: P1 bet_col)
                thus ?thesis
                  by (meson Tarski_neutral_dimensionless.col_cop__cop Tarski_neutral_dimensionless_axioms U1 U2)
              qed
              thus ?thesis
                using ncoplanar_perm_5 by blast
            qed

            thus ?thesis
              by (metis P1 Tarski_neutral_dimensionless.col_cop__cop Tarski_neutral_dimensionless_axioms assms(2) bet_col conga_diff56 coplanar_perm_12)
          qed
          have "Col C0 C1 M"
            using Col_perm R2 midpoint_col by blast
          thus ?thesis
            using T1 R1 col_cop__cop by blast
        qed
        thus ?thesis
          using ncoplanar_perm_8 by blast
      qed
      have "C0 \<noteq> M"
        using R1 R2 midpoint_distinct_1 by blast
      thus ?thesis
        using R5 R9 S1 cop_per2__col by blast
    qed
    have "B Out C C' \<or> A B TS C C'"
    proof cases
      assume Q1: "B = M"
      have Q2: "\<not> Col A B C"
        by (metis Col_def P1 Q1 R9 assms(2) conga_diff1 conga_diff2 l6_16_1 l8_9 not_bet_and_out out_trivial)
      have Q3: "\<not> Col A B C'"
        by (metis Col_def P1 Q1 R10 assms(2) conga_diff1 conga_diff56 l6_16_1 l8_9 not_bet_and_out out_trivial)
      have Q4: "Col B A B"
        by (simp add: col_trivial_3)
      have "Bet C B C'"
      proof -
        have S1: "Bet C1 C' B"
          using Bet_cases P1 by blast
        have "Bet C1 B C"
        proof -
          have T1: "Bet C0 C B"
            using Bet_cases P1 by blast
          have "Bet C0 B C1"
            by (simp add: Q1 R2 midpoint_bet)
          thus ?thesis
            using T1 between_exchange3 between_symmetry by blast
        qed
        thus ?thesis
          using S1 between_exchange3 between_symmetry by blast
      qed
      thus ?thesis
        by (metis Q2 Q3 Q4 bet__ts col_permutation_4 invert_two_sides)
    next
      assume L1: "B \<noteq> M"
      have L2: "B M TS C0 C1"
      proof -
        have M1: "\<not> Col C0 B M"
          by (metis (no_types) Col_perm L1 R1 R2 R5 is_midpoint_id l8_9)
        have M2: "\<not> Col C1 B M"
          using Col_perm L1 R1 R2 R6 l8_9 midpoint_not_midpoint by blast
        have M3: "Col M B M"
          using col_trivial_3 by auto
        have "Bet C0 M C1"
          by (simp add: R2 midpoint_bet)
        thus ?thesis
          using M1 M2 M3 TS_def by blast
      qed
      have "A B TS C C'"
      proof -
        have W2: "A B TS C C1"
        proof -
          have V1: "A B TS C0 C1"
            using L2 P1 R11 R7 col_two_sides cong_diff invert_two_sides not_col_permutation_5 by blast
          have "B Out C0 C"
            using L2 Out_def P1 TS_def assms(2) col_trivial_1 conga_diff2 by auto
          thus ?thesis
            using V1 col_trivial_3 l9_5 by blast
        qed
        then have W1: "A B TS C' C"
        proof -
          have Z1: "A B TS C1 C"
            by (simp add: W2 l9_2)
          have Z2: "Col B A B"
            using not_col_distincts by blast
          have "B Out C1 C'"
            using L2 Out_def P1 TS_def assms(2) col_trivial_1 conga_diff56 by auto
          thus ?thesis
            using Z1 Z2 l9_5 by blast
        qed
        thus ?thesis
          by (simp add: l9_2)
      qed
      thus ?thesis by blast
    qed
    thus ?thesis by blast
  qed
  thus ?thesis by blast
qed

lemma conga_os__out:
  assumes "A B C CongA A B C'" and
    "A B OS C C'"
  shows "B Out C C'"
  using assms(1) assms(2) conga_cop__or_out_ts l9_9 os__coplanar by blast

lemma cong2_conga_cong:
  assumes "A B C CongA A' B' C'" and
    "Cong A B A' B'" and
    "Cong B C B' C'"
  shows "Cong A C A' C'"
  by (smt assms(1) assms(2) assms(3) cong_4321 l11_3 l11_4_1 not_cong_3412 out_distinct out_trivial)

lemma angle_construction_1:
  assumes "\<not> Col A B C" and
    "\<not> Col A' B' P"
  shows "\<exists> C'. (A B C CongA A' B' C' \<and> A' B' OS C' P)"
proof -
  obtain C0 where P1: "Col B A C0 \<and> B A Perp C C0"
    using assms(1) col_permutation_4 l8_18_existence by blast
  have "\<exists> C'. (A B C CongA A' B' C' \<and> A' B' OS C' P)"
  proof cases
    assume P1A: "B = C0"
    obtain C' where P2: "Per C' B' A' \<and> Cong C' B' C B \<and> A' B' OS C' P"
      by (metis assms(1) assms(2) col_trivial_1 col_trivial_2 ex_per_cong)
    have P3: "A B C CongA A' B' C'"
      by (metis P1 P2 Tarski_neutral_dimensionless.l8_2 Tarski_neutral_dimensionless.os_distincts Tarski_neutral_dimensionless_axioms P1A assms(1) l11_16 not_col_distincts perp_per_1)
    thus ?thesis using P2 by blast
  next
    assume P4: "B \<noteq> C0"
    have "\<exists> C'. (A B C CongA A' B' C' \<and> A' B' OS C' P)"
    proof cases
      assume R1: "B Out A C0"
      obtain C0' where R2: "B' Out A' C0' \<and> Cong B' C0' B C0"
        by (metis P4 assms(2) col_trivial_1 segment_construction_3)
      have "\<exists> C'. Per C' C0' B' \<and> Cong C' C0' C C0 \<and> B' C0' OS C' P"
      proof -
        have R4: "B' \<noteq> C0'"
          using Out_def R2 by auto
        have R5: "C \<noteq> C0"
          using P1 perp_distinct by blast
        have R6: "Col B' C0' C0'"
          by (simp add: col_trivial_2)
        have "\<not> Col B' C0' P"
          using NCol_cases R2 R4 assms(2) col_transitivity_1 out_col by blast
        then have "\<exists> C'. Per C' C0' B' \<and>
Cong C' C0' C C0 \<and> B' C0' OS C' P" using R4 R5 R6 ex_per_cong by blast
        thus ?thesis by auto
      qed
      then obtain C' where R7: "Per C' C0' B' \<and>
Cong C' C0' C C0 \<and> B' C0' OS C' P" by auto
      then have R8: "C0 B C Cong3 C0' B' C'"
        by (meson Cong3_def P1 R2 col_trivial_2 l10_12 l8_16_1 not_col_permutation_2 not_cong_2143 not_cong_4321)
      have R9: "A B C CongA A' B' C'"
      proof -
        have S1: "C0 B C CongA C0' B' C'"
          by (metis P4 R8 assms(1) cong3_conga not_col_distincts)
        have S3: "B Out C C"
          using assms(1) not_col_distincts out_trivial by force
        have "B' \<noteq> C'"
          using R8 assms(1) cong3_diff2 not_col_distincts by blast
        then have "B' Out C' C'"
          using out_trivial by auto
        thus ?thesis
          using S1 R1 S3 R2 l11_10 by blast
      qed
      have "B' A' OS C' P"
      proof -
        have T1: "Col B' C0' A'"
          by (meson NCol_cases R2 Tarski_neutral_dimensionless.out_col Tarski_neutral_dimensionless_axioms)
        have "B' \<noteq> A'"
          using assms(2) col_trivial_1 by auto
        thus ?thesis
          using T1 R7 col_one_side by blast
      qed
      then have "A' B' OS C' P"
        by (simp add: invert_one_side)
      thus ?thesis
        using R9 by blast
    next
      assume U1: "\<not> B Out A C0"
      then have U2: "Bet A B C0"
        using NCol_perm P1 or_bet_out by blast
      obtain C0' where U3: "Bet A' B' C0' \<and> Cong B' C0' B C0"
        using segment_construction by blast
      have U4: "\<exists> C'. Per C' C0' B' \<and> Cong C' C0' C C0 \<and> B' C0' OS C' P"
      proof -
        have V2: "C \<noteq> C0"
          using Col_cases P1 assms(1) by blast
        have "B' \<noteq> C0'"
          using P4 U3 cong_diff_3 by blast
        then have "\<not> Col B' C0' P"
          using Col_def U3 assms(2) col_transitivity_1 by blast
        thus ?thesis using ex_per_cong
          using V2 not_col_distincts by blast
      qed
      then obtain C' where U5: "Per C' C0' B' \<and> Cong C' C0' C C0 \<and> B' C0' OS C' P"
        by blast
      have U98: "A B C CongA A' B' C'"
      proof -
        have X1: "C0 B C Cong3 C0' B' C'"
        proof -
          have X2: "Cong C0 B C0' B'"
            using Cong_cases U3 by blast
          have X3: "Cong C0 C C0' C'"
            using U5 not_cong_4321 by blast
          have "Cong B C B' C'"
          proof -
            have Y1: "Per C C0 B"
              using P1 col_trivial_3 l8_16_1 by blast
            have "Cong C C0 C' C0'"
              using U5 not_cong_3412 by blast
            thus ?thesis
              using Cong_perm Y1 U5 X2 l10_12 by blast
          qed
          thus ?thesis
            by (simp add: Cong3_def X2 X3)
        qed
        have X22: "Bet C0 B A"
          using U2 between_symmetry by blast
        have X24: "Bet C0' B' A'"
          using Bet_cases U3 by blast
        have "A' \<noteq> B'"
          using assms(2) not_col_distincts by blast
        thus ?thesis
          by (metis P4 X1 X22 X24 assms(1) cong3_conga l11_13 not_col_distincts)
      qed
      have "A' B' OS C' P"
      proof -
        have "B' A' OS C' P"
        proof -
          have W1: "Col B' C0' A'"
            by (simp add: Col_def U3)
          have "B' \<noteq> A'"
            using assms(2) not_col_distincts by blast
          thus ?thesis
            using W1 U5 col_one_side by blast
        qed
        thus ?thesis
          by (simp add: invert_one_side)
      qed
      thus ?thesis
        using U98 by blast
    qed
    thus ?thesis by auto
  qed
  thus ?thesis by auto
qed

lemma angle_construction_2:
  assumes "A \<noteq> B" (*and
    "A \<noteq> C"*) and
    "B \<noteq> C" (*and
    "A' \<noteq> B'"*) and
    "\<not> Col A' B' P"
  shows "\<exists> C'. (A B C CongA A' B' C' \<and> (A' B' OS C' P \<or> Col A' B' C'))"
  by (metis Col_def angle_construction_1 assms(1) assms(2) assms(3) col_trivial_3 conga_line l11_21_b or_bet_out out_trivial point_construction_different)

lemma ex_conga_ts:
  assumes "\<not> Col A B C" and
    "\<not> Col A' B' P"
  shows "\<exists> C'. A B C CongA A' B' C' \<and> A' B' TS C' P"
proof -
  obtain P' where P1: "A' Midpoint P P'"
    using symmetric_point_construction by blast
  have P2: "\<not> Col A' B' P'"
    by (metis P1 assms(2) col_transitivity_1 midpoint_col midpoint_distinct_2 not_col_distincts)
  obtain C' where P3:
    "A B C CongA A' B' C' \<and> A' B' OS C' P'"
    using P2 angle_construction_1 assms(1) by blast
  have "A' B' TS P' P"
    using P1 P2 assms(2) bet__ts l9_2 midpoint_bet not_col_distincts by auto
  thus ?thesis
    using P3 l9_8_2 one_side_symmetry by blast
qed

lemma l11_15:
  assumes "\<not> Col A B C" and
    "\<not> Col D E P"
  shows
    "\<exists> F. (A B C CongA D E F \<and> E D OS F P) \<and>
          (\<forall> F1 F2. ((A B C CongA D E F1 \<and> E D OS F1 P) \<and>
                          (A B C CongA D E F2 \<and> E D OS F2 P))
    \<longrightarrow> E Out F1 F2)"
proof -
  obtain F where P1: "A B C CongA D E F \<and>  D E OS F P"
    using angle_construction_1 assms(1) assms(2) by blast
  then have P2: "A B C CongA D E F \<and> E D OS F P"
    using invert_one_side by blast
  have "(\<forall> F1 F2. ((A B C CongA D E F1 \<and> E D OS F1 P) \<and>
                          (A B C CongA D E F2 \<and> E D OS F2 P)) \<longrightarrow> E Out F1 F2)"
  proof -
    {
      fix F1 F2
      assume P3: "((A B C CongA D E F1 \<and> E D OS F1 P) \<and>
                          (A B C CongA D E F2 \<and> E D OS F2 P))"
      then have P4: "A B C CongA D E F1" by simp
      have P5: "E D OS F1 P" using P3 by simp
      have P6: "A B C CongA D E F2" using P3 by simp
      have P7: "E D OS F2 P" using P3 by simp
      have P8: "D E F1 CongA D E F2"
        using P4 conga_sym P6 conga_trans by blast
      have "D E OS F1 F2"
        using P5 P7 invert_one_side one_side_symmetry one_side_transitivity by blast
      then have "E Out F1 F2" using P8 conga_os__out
        by (meson P3 conga_sym conga_trans)
    }
    thus ?thesis by auto
  qed
  thus ?thesis
    using P2 by blast
qed

lemma l11_19:
  assumes "Per A B P1" and
    "Per A B P2" and
    "A B OS P1 P2"
  shows "B Out P1 P2"
proof cases
  assume "Col A B P1"
  thus ?thesis
    using assms(3) col123__nos by blast
next
  assume P1: "\<not> Col A B P1"
  have "B Out P1 P2"
  proof cases
    assume "Col A B P2"
    thus ?thesis
      using assms(3) one_side_not_col124 by blast
  next
    assume P2: "\<not> Col A B P2"
    obtain x where "A B P1 CongA A B x \<and> B A OS x P2 \<and>
          (\<forall> F1 F2. ((A B P1 CongA A B F1 \<and> B A OS F1 P2) \<and>
                          (A B P1 CongA A B F2 \<and> B A OS F2 P2))\<longrightarrow> B Out F1 F2)"
      using P1 P2 l11_15 by blast
    thus ?thesis
      by (metis P1 P2 assms(1) assms(2) assms(3) conga_os__out l11_16 not_col_distincts)
  qed
  thus ?thesis
    by simp
qed

lemma l11_22_bet:
  assumes "Bet A B C" and
    "P' B' TS A' C'" and
    "A B P CongA A' B' P'" and
    "P B C CongA P' B' C'"
  shows "Bet A' B' C'"
proof -
  obtain C'' where P1: "Bet A' B' C'' \<and> Cong B' C'' B C"
    using segment_construction by blast
  have P2: "C B P CongA C'' B' P'"
    by (metis P1 assms(1) assms(3) assms(4) cong_diff_3 conga_diff2 l11_13)
  have P3: "C'' B' P' CongA C' B' P'"
    by (meson P2 Tarski_neutral_dimensionless.conga_sym Tarski_neutral_dimensionless_axioms assms(4) conga_comm conga_trans)
  have P4: "B' Out C' C'' \<or> P' B' TS C' C''"
  proof -
    have P5: "Coplanar P' B' C' C''"
      by (meson P1 TS_def assms(2) bet__coplanar coplanar_trans_1 ncoplanar_perm_1 ncoplanar_perm_8 ts__coplanar)
    have "P' B' C' CongA P' B' C''"
      using P3 conga_comm conga_sym by blast
    thus ?thesis
      by (simp add: P5 conga_cop__or_out_ts)
  qed
  have P6: "B' Out C' C'' \<longrightarrow> Bet A' B' C'"
  proof -
    {
      assume "B' Out C' C''"
      then have "Bet A' B' C'"
        using P1 bet_out_out_bet between_exchange4 between_trivial2 col_trivial_3 l6_6 not_bet_out by blast
    }
    thus ?thesis by simp
  qed
  have "P' B' TS C' C'' \<longrightarrow> Bet A' B' C'"
  proof -
    {
      assume P7: "P' B' TS C' C''"
      then have "Bet A' B' C'"
      proof cases
        assume "Col C' B' P'"
        thus ?thesis
          using Col_perm TS_def assms(2) by blast
      next
        assume Q1: "\<not> Col C' B' P'"
        then have Q2: "B' \<noteq> P'"
          using not_col_distincts by blast
        have Q3: "B' P' TS A' C''"
          by (metis Col_perm P1 TS_def P7 assms(2) col_trivial_3)
        have Q4: "B' P' OS C' C''"
          using P7 Q3 assms(2) invert_two_sides l9_8_1 l9_9 by blast
        thus ?thesis
          using P7 invert_one_side l9_9 by blast
      qed
    }
    thus ?thesis by simp
  qed
  thus ?thesis using P6 P4 by blast
qed

lemma l11_22a:
  assumes "B P TS A C" and
    "B' P' TS A' C'" and
    "A B P CongA A' B' P'" and
    "P B C CongA P' B' C'"
  shows "A B C CongA A' B' C'"
proof -
  have P1: "A \<noteq> B \<and> A' \<noteq> B' \<and> P \<noteq> B \<and> P' \<noteq> B' \<and> C \<noteq> B \<and> C' \<noteq> B'"
    using assms(3) assms(4) conga_diff1 conga_diff2 conga_diff45 conga_diff56 by auto
  have P2: "A \<noteq> C \<and> A' \<noteq> C'"
    using assms(1) assms(2) not_two_sides_id by blast
  obtain A'' where P3: "B' Out A' A'' \<and> Cong B' A'' B A"
    using P1 segment_construction_3 by force
  have P4: "\<not> Col A B P"
    using TS_def assms(1) by blast
  obtain T where P5: "Col T B P \<and> Bet A T C"
    using TS_def assms(1) by blast
  have "A B C CongA A' B' C'"
  proof cases
    assume "B = T"
    thus ?thesis
      by (metis P1 P5 assms(2) assms(3) assms(4) conga_line invert_two_sides l11_22_bet)
  next
    assume P6: "B \<noteq> T"
    have "A B C CongA A' B' C'"
    proof cases
      assume P7A: "Bet P B T"
      obtain T'' where T1: "Bet P' B' T'' \<and> Cong B' T'' B T"
        using segment_construction by blast
      have "\<exists> T''.
  Col B' P' T'' \<and> (B' Out P' T'' \<longleftrightarrow> B Out P T) \<and> Cong B' T'' B T"
      proof -
        have T2: "Col B' P' T''" using T1
          by (simp add: bet_col col_permutation_4)
        have "(B' Out P' T'' \<longleftrightarrow> B Out P T) \<and> Cong B' T'' B T"
          using P7A T1 not_bet_and_out by blast
        thus ?thesis using T2 by blast
      qed
      then obtain T'' where T3:
        "Col B' P' T'' \<and> (B' Out P' T'' \<longleftrightarrow> B Out P T) \<and> Cong B' T'' B T" by blast
      then have T4: "B' \<noteq> T''"
        using P6 cong_diff_3 by blast
      obtain C'' where T5: "Bet A'' T'' C'' \<and> Cong T'' C'' T C"
        using segment_construction by blast
      have T6: "A B T CongA A' B' T''"
        by (smt Out_cases P5 P6 T3 T4 P7A assms(3) between_symmetry col_permutation_4 conga_comm l11_13 l6_4_1 or_bet_out)
      then have T7: "A B T CongA A'' B'  T''"
        by (smt P3 P4 P6 T3 Tarski_neutral_dimensionless.l11_10 Tarski_neutral_dimensionless_axioms bet_out col_trivial_3 cong_diff_3 l5_2 l6_6 not_col_permutation_1 or_bet_out)
      then have T8: "Cong A T A'' T''"
        using P3 T3 cong2_conga_cong cong_4321 not_cong_3412 by blast
      have T9: "Cong A C A'' C''"
        using P5 T5 T8 cong_symmetry l2_11_b by blast
      have T10: "Cong C B C'' B'"
        by (smt P3 P4 P5 T3 T5 T8 cong_commutativity cong_symmetry five_segment)
      have "A B C Cong3 A'' B' C''"
        using Cong3_def P3 T10 T9 not_cong_2143 not_cong_4321 by blast
      then have T11: "A B C CongA A'' B' C''"
        by (simp add: Tarski_neutral_dimensionless.cong3_conga Tarski_neutral_dimensionless_axioms P1)
      have "C B T Cong3 C'' B' T''"
        by (simp add: Cong3_def T10 T3 T5 cong_4321 cong_symmetry)
      then have T12: "C B T CongA C'' B' T''"
        using P1 P6 cong3_conga by auto
      have T13: "P B C CongA P' B' C''"
      proof -
        have K4: "Bet T B P"
          using Bet_perm P7A by blast
        have "Bet T'' B' P'"
          using Col_perm P7A T3 l6_6 not_bet_and_out or_bet_out by blast
        thus ?thesis
          using K4 P1 T12 conga_comm l11_13 by blast
      qed
      have T14: "P' B' C' CongA P' B' C''"
      proof -
        have "P' B' C' CongA P B C"
          by (simp add: assms(4) conga_sym)
        thus ?thesis
          using T13 conga_trans by blast
      qed
      have T15: "B' Out C' C'' \<or> P' B' TS C' C''"
      proof -
        have K7: "Coplanar P' B' C' C''"
        proof -
          have K8: "Coplanar A' P' B' C'"
            using assms(2) coplanar_perm_14 ts__coplanar by blast
          have K8A: "Coplanar P' C'' B' A''"
          proof -
            have "Col P' B' T'' \<and> Col C'' A'' T''"
              using Col_def Col_perm T3 T5 by blast
            then have "Col P' C'' T'' \<and> Col B' A'' T'' \<or>
Col P' B' T'' \<and> Col C'' A'' T'' \<or> Col P' A'' T'' \<and> Col C'' B' T''" by simp
            thus ?thesis
              using Coplanar_def by auto
          qed
          then have "Coplanar A' P' B' C''"
          proof -
            have K9: "B' \<noteq> A''"
              using P3 out_distinct by blast
            have "Col B' A'' A'"
              using Col_perm P3 out_col by blast
            thus ?thesis
              using K8A K9 col_cop__cop coplanar_perm_19 by blast
          qed
          thus ?thesis
            by (meson K8 TS_def assms(2) coplanar_perm_7 coplanar_trans_1 ncoplanar_perm_2)
        qed
        thus ?thesis
          by (simp add: T14 K7 conga_cop__or_out_ts)
      qed
      have "A B C CongA A' B' C'"
      proof cases
        assume "B' Out C' C''"
        thus ?thesis
          using P1 P3 T11 l11_10 out_trivial by blast
      next
        assume W1: "\<not> B' Out C' C''"
        then have W1A: " P' B' TS C' C''" using T15 by simp
        have W2: "B' P' TS A'' C'"
          using P3 assms(2) col_trivial_1 l9_5 by blast
        then have W3: "B' P' OS A'' C''"
          using T15 W1 invert_two_sides l9_2 l9_8_1 by blast
        have W4: "B' P' TS A''  C''"
        proof -
          have "\<not> Col A' B' P'"
            using TS_def assms(2) by auto
          thus ?thesis
            using Col_perm T3 T5 W3 one_side_chara by blast
        qed
        thus ?thesis
          using W1A W2 invert_two_sides l9_8_1 l9_9 by blast
      qed
      thus ?thesis by simp
    next
      assume R1: "\<not> Bet P B T"
      then have R2: "B Out P T"
        using Col_cases P5 l6_4_2 by blast
      have R2A: "\<exists> T''. Col B' P' T'' \<and> (B' Out P' T'' \<longleftrightarrow> B Out P T) \<and> Cong B' T'' B T"
      proof -
        obtain T'' where R3: "B' Out P' T'' \<and> Cong B' T'' B T"
          using P1 P6 segment_construction_3 by fastforce
        thus ?thesis
          using R2 out_col by blast
      qed
      then obtain T'' where R4: "Col B' P' T'' \<and> (B' Out P' T'' \<longleftrightarrow> B Out P T) \<and> Cong B' T'' B T" by auto
      have R5: "B' \<noteq> T''"
        using P6 R4 cong_diff_3 by blast
      obtain C'' where R6: "Bet A'' T'' C'' \<and> Cong T'' C'' T C"
        using segment_construction by blast
      have R7: "A B T CongA A' B' T''"
        using P1 R2 R4 assms(3) l11_10 l6_6 out_trivial by auto
      have R8: "A B T CongA A'' B'  T''"
        using P3 P4 R2 R4 assms(3) l11_10 l6_6 not_col_distincts out_trivial by blast
      have R9: "Cong A T A'' T''"
        using Cong_cases P3 R4 R8 cong2_conga_cong by blast
      have R10: "Cong A C A'' C''"
        using P5 R6 R9 l2_11_b not_cong_3412 by blast
      have R11: "Cong C B C'' B'"
        by (smt P3 P4 P5 R4 R6 R9 cong_commutativity cong_symmetry five_segment)
      have "A B C Cong3 A'' B' C''"
        by (simp add: Cong3_def P3 R10 R11 cong_4321 cong_commutativity)
      then have R12: "A B C CongA A'' B' C''"
        using P1 by (simp add: cong3_conga)
      have "C B T Cong3 C'' B' T''"
        using Cong3_def R11 R4 R6 not_cong_3412 not_cong_4321 by blast
      then have R13: "C B T CongA C'' B' T''"
        using P1 P6 Tarski_neutral_dimensionless.cong3_conga Tarski_neutral_dimensionless_axioms by fastforce
      have R13A: "\<not> Col A' B' P'"
        using TS_def assms(2) by blast
      have R14: "B' Out C' C'' \<or> P' B' TS C' C''"
      proof -
        have S1: "Coplanar P' B' C' C''"
        proof -
          have T1: "Coplanar A' P' B' C'"
            using assms(2) ncoplanar_perm_14 ts__coplanar by blast
          have "Coplanar A' P' B' C''"
          proof -
            have U6: "B' \<noteq> A''"
              using P3 out_diff2 by blast
            have "Coplanar P' C'' B' A''"
            proof -
              have "Col P' B' T'' \<and> Col C'' A'' T''"
                using Col_def Col_perm R4 R6 by blast
              thus ?thesis using Coplanar_def by auto
            qed
            thus ?thesis
              by (meson Col_cases P3 U6 col_cop__cop ncoplanar_perm_21 ncoplanar_perm_6 out_col)
          qed
          thus ?thesis
            using NCol_cases R13A T1 coplanar_trans_1 by blast
        qed
        have "P' B' C' CongA P' B' C''"
        proof -
          have "C B P CongA C'' B' P'"
            using P1 R12 R13 R2 R4 conga_diff56 l11_10 out_trivial by presburger
          then have "C' B' P' CongA C'' B' P'"
            by (meson Tarski_neutral_dimensionless.conga_trans Tarski_neutral_dimensionless_axioms assms(4) conga_comm conga_sym)
          thus ?thesis
            by (simp add: conga_comm)
        qed
        thus ?thesis
          by (simp add: S1 conga_cop__or_out_ts)
      qed
      have S1: "B Out A A"
        using P4 not_col_distincts out_trivial by blast
      have S2: "B Out C C"
        using TS_def assms(1) not_col_distincts out_trivial by auto
      have S3: "B' Out A' A''" using P3 by simp
      have "A B C CongA A' B' C'"
      proof cases
        assume "B' Out C' C''"
        thus ?thesis using S1 S2 S3
          using R12 l11_10 by blast
      next
        assume "\<not> B' Out C' C''"
        then have Z3: "P' B' TS C' C''" using R14 by simp
        have Q1: "B' P' TS A'' C'"
          using S3 assms(2) l9_5 not_col_distincts by blast
        have Q2: "B' P' OS A'' C''"
        proof -
          have "B' P' TS C'' C'"
          proof -
            have "B' P' TS C' C''" using Z3
              using invert_two_sides by blast
            thus ?thesis
              by (simp add: l9_2)
          qed
          thus ?thesis
            using Q1 l9_8_1 by blast
        qed
        have "B' P' TS A''  C''"
          using Col_perm Q2 R4 R6 one_side_chara by blast
        thus ?thesis
          using Q2 l9_9 by blast
      qed
      thus ?thesis using S1 S2 S3
        using R12 l11_10 by blast
    qed
    thus ?thesis by simp
  qed
  thus ?thesis by simp
qed

lemma l11_22b:
  assumes "B P OS A C" and
    "B' P' OS A' C'" and
    "A B P CongA A' B' P'" and
    "P B C CongA P' B' C'"
  shows "A B C CongA A' B' C'"
proof -
  obtain D where P1: "Bet A B D \<and> Cong B D A B"
    using segment_construction by blast
  obtain D' where P2: "Bet A' B' D' \<and> Cong B' D' A' B'"
    using segment_construction by blast
  have P3: "D B P CongA D' B' P'"
  proof -
    have Q3: "D \<noteq> B"
      by (metis P1 assms(1) col_trivial_3 cong_diff_3 one_side_not_col124 one_side_symmetry)
    have Q5: "D' \<noteq> B'"
      by (metis P2 assms(2) col_trivial_3 cong_diff_3 one_side_not_col124 one_side_symmetry)
    thus ?thesis
      using assms(3) P1 Q3 P2 l11_13 by blast
  qed
  have P5: "D B C CongA D' B' C'"
  proof -
    have Q1: "B P TS D C"
      by (metis P1 assms(1) bet__ts col_trivial_3 cong_diff_3 l9_2 l9_8_2 one_side_not_col124 one_side_symmetry)
    have "B' P' TS D' C'" by (metis Cong_perm P2 assms(2) bet__ts between_cong between_trivial2 l9_2 l9_8_2 one_side_not_col123 point_construction_different ts_distincts)
    thus ?thesis
      using assms(4) Q1 P3 l11_22a by blast
  qed
  have P6: "Bet D B A"
    using Bet_perm P1 by blast
  have P7: "A \<noteq> B"
    using assms(3) conga_diff1 by auto
  have P8: "Bet D' B' A'"
    using Bet_cases P2 by blast
  have "A' \<noteq> B'"
    using assms(3) conga_diff45 by blast
  thus ?thesis
    using P5 P6 P7 P8 l11_13 by blast
qed

lemma l11_22:
  assumes "((B P TS A C \<and> B' P' TS A' C')\<or>(B P OS A C \<and> B' P' OS A' C'))" and
    "A B P CongA A' B' P'" and
    "P B C CongA P' B' C'"
  shows "A B C CongA A' B' C'"
  by (meson assms(1) assms(2) assms(3) l11_22a l11_22b)

lemma l11_24:
  assumes "P InAngle A B C"
  shows "P InAngle C B A"
proof -
  obtain pp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p" where
    "\<forall>x0 x1 x2 x3. (\<exists>v4. Bet x2 v4 x0 \<and> (v4 = x1 \<or> x1 Out v4 x3)) = (Bet x2 (pp x0 x1 x2 x3) x0 \<and> ((pp x0 x1 x2 x3) = x1 \<or> x1 Out (pp x0 x1 x2 x3) x3))"
    by moura
  then have "A \<noteq> B \<and> C \<noteq> B \<and> P \<noteq> B \<and>Bet A (pp C B A P) C \<and> ((pp C B A P) = B \<or> B Out (pp C B A P) P)"
    using InAngle_def assms by presburger
  thus ?thesis
    by (metis (no_types) InAngle_def between_symmetry)
qed

lemma col_in_angle:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "P \<noteq> B" and
    "B Out A P \<or> B Out C P"
  shows "P InAngle A B C"
  by (meson InAngle_def assms(1) assms(2) assms(3) assms(4) between_trivial between_trivial2)

lemma out321__inangle:
  assumes "C \<noteq> B" and
    "B Out A P"
  shows "P InAngle A B C"
  using assms(1) assms(2) col_in_angle out_distinct by auto

lemma inangle1123:
  assumes "A \<noteq> B" and
    "C \<noteq> B"
  shows "A InAngle A B C"
  by (simp add: assms(1) assms(2) out321__inangle out_trivial)

lemma out341__inangle:
  assumes "A \<noteq> B" and
    "B Out C P"
  shows "P InAngle A B C"
  using assms(1) assms(2) col_in_angle out_distinct by auto

lemma inangle3123:
  assumes "A \<noteq> B" and
    "C \<noteq> B"
  shows "C InAngle A B C"
  by (simp add: assms(1) assms(2) inangle1123 l11_24)

lemma in_angle_two_sides:
  assumes "\<not> Col B A P" and
    "\<not> Col B C P" and
    "P InAngle A B C"
  shows "P B TS A C"
  by (metis InAngle_def TS_def assms(1) assms(2) assms(3) not_col_distincts not_col_permutation_1 out_col)

lemma in_angle_out:
  assumes "B Out A C" and
    "P InAngle A B C"
  shows "B Out A P"
  by (metis InAngle_def assms(1) assms(2) not_bet_and_out out2_bet_out)

lemma col_in_angle_out:
  assumes "Col B A P" and
    "\<not> Bet A B C" and
    "P InAngle A B C"
  shows "B Out A P"
proof -
  obtain X where P1: "Bet A X C \<and> (X = B \<or> B Out X P)"
    using InAngle_def assms(3) by auto
  have "B Out A P"
  proof cases
    assume "X = B"
    thus ?thesis
      using P1 assms(2) by blast
  next
    assume P2: "X \<noteq> B"
    thus ?thesis
    proof -
      have f1: "Bet B A P \<or> A Out B P"
        by (meson assms(1) l6_4_2)
      have f2: "B Out X P"
        using P1 P2 by blast
      have f3: "(Bet B P A \<or>Bet B A P) \<or>Bet P B A"
        using f1 by (meson Bet_perm Out_def)
      have f4: "Bet B P X \<or>Bet P X B"
        using f2 by (meson Bet_perm Out_def)
      then have f5: "((Bet B P X \<or>Bet X B A) \<or>Bet B P A) \<or>Bet B A P"
        using f3 by (meson between_exchange3)
      have "\<forall>p. Bet p X C \<or> \<not>Bet A p X"
        using P1 between_exchange3 by blast
      then have f6: "(P = B \<or>Bet B A P) \<or>Bet B P A"
        using f5 f3 by (meson Bet_perm P2 assms(2) outer_transitivity_between2)
      have f7: "Bet C X A"
        using Bet_perm P1 by blast
      have "P \<noteq> B"
        using f2 by (simp add: Out_def)
      moreover
      { assume "Bet B B C"
        then have "A \<noteq> B"
          using assms(2) by blast }
      ultimately have "A \<noteq> B"
        using f7 f4 f1 by (meson Bet_perm Out_def P2 between_exchange3 outer_transitivity_between2)
      thus ?thesis
        using f6 f2 by (simp add: Out_def)
    qed
  qed
  thus ?thesis by blast
qed

lemma l11_25_aux:
  assumes "P InAngle A B C" and
    "\<not> Bet A B C" and
    "B Out A' A"
  shows "P InAngle A' B C"
proof -
  have P1: "Bet B A' A \<or> Bet B A A'"
    using Out_def assms(3) by auto
  {
    assume P2: "Bet B A' A"
    obtain X where P3: "Bet A X C \<and> (X = B \<or> B Out X P)"
      using InAngle_def assms(1) by auto
    obtain T where P4: "Bet A' T C \<and> Bet X T B"
      using Bet_perm P2 P3 inner_pasch by blast
    {
      assume "X = B"
      then have "P InAngle A' B C"
        using P3 assms(2) by blast
    }
    {
      assume "B Out X P"
      then have "P InAngle A' B C"
        by (metis InAngle_def P4 assms(1) assms(3) bet_out_1 l6_7 out_diff1)
    }
    then have "P InAngle A' B C"
      using P3 \<open>X = B \<Longrightarrow> P InAngle A' B C\<close> by blast
  }
  {
    assume Q0: "Bet B A A'"
    obtain X where Q1: "Bet A X C \<and> (X = B \<or> B Out X P)"
      using InAngle_def assms(1) by auto
    {
      assume "X = B"
      then have "P InAngle A' B C"
        using Q1 assms(2) by blast
    }
    {
      assume Q2: "B Out X P"
      obtain T where Q3: "Bet A' T C \<and> Bet B X T"
        using Bet_perm Q1 Q0 outer_pasch by blast
      then have "P InAngle A' B C"
        by (metis InAngle_def Q0 Q2 assms(1) bet_out l6_6 l6_7 out_diff1)
    }
    then have "P InAngle A' B C"
      using \<open>X = B \<Longrightarrow> P InAngle A' B C\<close> Q1 by blast
  }
  thus ?thesis
    using P1 \<open>Bet B A' A \<Longrightarrow> P InAngle A' B C\<close> by blast
qed

lemma l11_25:
  assumes "P InAngle A B C" and
    "B Out A' A" and
    "B Out C' C" and
    "B Out P' P"
  shows "P' InAngle A' B C'"
proof cases
  assume "Bet A B C"
  thus ?thesis
    by (metis Bet_perm InAngle_def assms(2) assms(3) assms(4) bet_out__bet l6_6 out_distinct)
next
  assume P1: "\<not> Bet A B C"
  have P2: "P InAngle A' B C"
    using P1 assms(1) assms(2) l11_25_aux by blast
  have P3: "P InAngle A' B C'"
  proof -
    have "P InAngle C' B A'" using l11_25_aux
      using Bet_perm P1 P2 assms(2) assms(3) bet_out__bet l11_24 by blast
    thus ?thesis using l11_24 by blast
  qed
  obtain X where P4: "Bet A' X C' \<and> (X = B \<or> B Out X P)"
    using InAngle_def P3 by auto
  {
    assume "X = B"
    then have "P' InAngle A' B C'"
      using InAngle_def P3 P4 assms(4) out_diff1 by auto
  }
  {
    assume "B Out X P"
    then have "P' InAngle A' B C'"
    proof -
      have "\<forall>p. B Out p P' \<or> \<not> B Out p P"
        by (meson Out_cases assms(4) l6_7)
      thus ?thesis
        by (metis (no_types) InAngle_def P3 assms(4) out_diff1)
    qed
  }
  thus ?thesis
    using InAngle_def P4 assms(2) assms(3) assms(4) out_distinct by auto
qed

lemma inangle_distincts:
  assumes "P InAngle A B C"
  shows "A \<noteq> B \<and> C \<noteq> B \<and> P \<noteq> B"
  using InAngle_def assms by auto

lemma segment_construction_0:
  shows "\<exists> B'. Cong A' B' A B"
  using segment_construction by blast

lemma angle_construction_3:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "A' \<noteq> B'"
  shows "\<exists> C'. A B C CongA A' B' C'"
  by (metis angle_construction_2 assms(1) assms(2) assms(3) not_col_exists)

lemma l11_28:
  assumes "A B C Cong3 A' B' C'" and
    "Col A C D"
  shows "\<exists> D'. (Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D')"
proof cases
  assume P1: "A = C"
  have "\<exists> D'. (Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D')"
  proof cases
    assume "A = B"
    thus ?thesis
      by (metis P1 assms(1) cong3_diff cong3_symmetry cong_3_swap_2 not_cong_3421 segment_construction_0)
  next
    assume "A \<noteq> B"
    have "\<exists> D'. (Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D')"
    proof cases
      assume "A = D"
      thus ?thesis
        using Cong3_def P1 assms(1) cong_trivial_identity by blast
    next
      assume "A \<noteq> D"
      have "\<exists> D'. (Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D')"
      proof cases
        assume "B = D"
        thus ?thesis
          using Cong3_def assms(1) cong_3_swap_2 cong_trivial_identity by blast
      next
        assume Q1: "B \<noteq> D"
        obtain D'' where Q2: "B A D CongA B' A' D''"
          by (metis \<open>A \<noteq> B\<close> \<open>A \<noteq> D\<close> angle_construction_3 assms(1) cong3_diff)
        obtain D' where Q3: "A' Out D'' D' \<and> Cong A' D' A D"
          by (metis Q2 \<open>A \<noteq> D\<close> conga_diff56 segment_construction_3)
        have Q5: "Cong A D A' D'"
          using Q3 not_cong_3412 by blast
        have "B A D CongA B' A' D'"
          using Q2 Q3 \<open>A \<noteq> B\<close> \<open>A \<noteq> D\<close> conga_diff45 l11_10 l6_6 out_trivial by auto
        then have "Cong B D B' D'"
          using Cong3_def Cong_perm Q5 assms(1) cong2_conga_cong by blast
        thus ?thesis
          using Cong3_def P1 Q5 assms(1) cong_reverse_identity by blast
      qed
      thus ?thesis by simp
    qed
    thus ?thesis by simp
  qed
  thus ?thesis by simp
next
  assume Z1: "A \<noteq> C"
  have  "\<exists> D'. (Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D')"
  proof cases
    assume "A = D"
    thus ?thesis
      using Cong3_def Cong_perm assms(1) cong_trivial_identity by blast
  next
    assume "A \<noteq> D"
    {
      assume "Bet A C D"
      obtain D' where W1: "Bet A' C' D' \<and> Cong C' D' C D"
        using segment_construction by blast
      have W2: "Cong A D A' D'"
        by (meson Cong3_def W1 \<open>Bet A C D\<close> assms(1) cong_symmetry l2_11_b)
      have W3: "Cong B D B' D'"
      proof -
        have X1: "Cong C D C' D'"
          using W1 not_cong_3412 by blast
        have "Cong C B C' B'"
          using Cong3_def assms(1) cong_commutativity by presburger
        then have W4: "A C D B OFSC A' C' D' B'"
          using Cong3_def OFSC_def W1 X1 \<open>Bet A C D\<close> assms(1) by blast
        have "Cong D B D' B'"
          using W4 \<open>A \<noteq> C\<close> five_segment_with_def by blast
        thus ?thesis
          using Z1 not_cong_2143 by blast
      qed
      have "Cong C D C' D'"
        by (simp add: W1 cong_symmetry)
      then have "\<exists> D'. (Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D')"
        using W2 W3 by blast
    }
    {
      assume W3B: "Bet C D A"
      then obtain D' where W4A: "Bet A' D' C' \<and> A D C Cong3 A' D' C'"
        using Bet_perm Cong3_def assms(1) l4_5 by blast
      have W5: "Cong A D A' D'"
        using Cong3_def W4A by blast
      have "A D C B IFSC A' D' C' B'"
        by (meson Bet_perm Cong3_def Cong_perm IFSC_def W4A W3B assms(1))
      then have "Cong D B D' B'"
        using l4_2 by blast
      then have W6: "Cong B D B' D'"
        using Cong_perm by blast
      then have "Cong C D C' D'"
        using Cong3_def W4A not_cong_2143 by blast
      then have "\<exists> D'. (Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D')"
        using W5 W6 by blast
    }
    {
      assume W7: "Bet D A C"
      obtain D' where W7A: "Bet C' A' D' \<and> Cong A' D' A D"
        using segment_construction by blast
      then have W8: "Cong A D A' D'"
        using Cong_cases by blast
      have "C A D B OFSC C' A' D' B'"
        by (meson Bet_perm Cong3_def Cong_perm OFSC_def W7 W7A assms(1))
      then have "Cong D B D' B'"
        using Z1 five_segment_with_def by auto
      then have w9: "Cong B D B' D'"
        using Cong_perm by blast
      have "Cong C D C' D'"
      proof -
        have L1: "Bet C A D"
          using Bet_perm W7 by blast
        have L2: "Bet C' A' D'"
          using Bet_perm W7
          using W7A by blast
        have "Cong C A C' A'" using assms(1)
          using Cong3_def assms(1) not_cong_2143 by blast
        thus ?thesis using l2_11
          using L1 L2 W8 l2_11 by blast
      qed
      then have "\<exists> D'. (Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D')"
        using W8 w9 by blast
    }
    thus ?thesis
      using Bet_cases \<open>Bet A C D \<Longrightarrow> \<exists>D'. Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D'\<close> \<open>Bet C D A \<Longrightarrow> \<exists>D'. Cong A D A' D' \<and> Cong B D B' D' \<and> Cong C D C' D'\<close> assms(2) third_point by blast
  qed
  thus ?thesis
    by blast
qed

lemma bet_conga__bet:
  assumes "Bet A B C" and
    "A B C CongA A' B' C'"
  shows "Bet A' B' C'"
proof -
  obtain A0 C0 A1 C1 where P1:"
 Bet B A A0 \<and>Cong A A0 B' A' \<and>
 Bet B C C0 \<and>Cong C C0 B' C' \<and>
 Bet B' A' A1 \<and>Cong A' A1 B A \<and>
 Bet B' C' C1 \<and>Cong C' C1 B C \<and>
 Cong A0 C0 A1 C1" using CongA_def assms(2)
    by auto
  have "Bet C B A0" using P1 outer_transitivity_between
    by (metis assms(1) assms(2) between_symmetry conga_diff1)
  then have "Bet A0 B C"
    using Bet_cases by blast
  then have P2: "Bet A0 B C0"
    using P1 assms(2) conga_diff2 outer_transitivity_between by blast
  have P3: "A0 B C0 Cong3 A1 B' C1"
  proof -
    have Q1: "Cong A0 B A1 B'"
      by (meson Bet_cases P1 l2_11_b not_cong_1243 not_cong_4312)
    have Q3: "Cong B C0 B' C1"
      using P1 between_symmetry cong_3421 l2_11_b not_cong_1243 by blast
    thus ?thesis
      by (simp add: Cong3_def Q1 P1)
  qed
  then have P4: "Bet A1 B' C1" using P2 l4_6 by blast
  then have "Bet A' B' C1"
    using P1 Bet_cases between_exchange3 by blast
  thus ?thesis using between_inner_transitivity P1 by blast
qed

lemma in_angle_one_side:
  assumes "\<not> Col A B C" and
    "\<not> Col B A P" and
    "P InAngle A B C"
  shows "A B OS P C"
proof -
  obtain X where P1: "Bet A X C \<and> (X = B \<or> B Out X P)"
    using InAngle_def assms(3) by auto
  {
    assume "X = B"
    then have  "A B OS P C"
      using P1 assms(1) bet_col by blast
  }
  {
    assume P2: "B Out X P"
    obtain C' where P2A: "Bet C A C' \<and> Cong A C' C A"
      using segment_construction by blast
    have "A B TS X C'"
    proof -
      have Q1: "\<not> Col X A B"
        by (metis Col_def P1 assms(1) assms(2) col_transitivity_2 out_col)
      have Q2 :"\<not> Col C' A B"
        by (metis Col_def Cong_perm P2A assms(1) cong_diff l6_16_1)
      have "\<exists> T. Col T A B \<and> Bet X T C'"
        using Bet_cases P1 P2A between_exchange3 col_trivial_1 by blast
      thus ?thesis
        by (simp add: Q1 Q2 TS_def)
    qed
    then have P3: "A B TS P C'"
      using P2 col_trivial_3 l9_5 by blast
    then have "A B TS C C'"
      by (smt P1 P2 bet_out bet_ts__os between_trivial col123__nos col_trivial_3 invert_two_sides l6_6 l9_2 l9_5)
    then have "A B OS P C"
      using OS_def P3 by blast
  }
  thus ?thesis
    using P1 \<open>X = B \<Longrightarrow> A B OS P C\<close> by blast
qed

lemma inangle_one_side:
  assumes "\<not> Col A B C" and
    "\<not> Col A B P" and
    "\<not> Col A B Q" and
    "P InAngle A B C" and
    "Q InAngle A B C"
  shows "A B OS P Q"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) in_angle_one_side not_col_permutation_4 one_side_symmetry one_side_transitivity)

lemma inangle_one_side2:
  assumes "\<not> Col A B C" and
    "\<not> Col A B P" and
    "\<not> Col A B Q" and
    "\<not> Col C B P" and
    "\<not> Col C B Q" and
    "P InAngle A B C" and
    "Q InAngle A B C"
  shows "A B OS P Q \<and> C B OS P Q"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) inangle_one_side l11_24 not_col_permutation_3)

lemma col_conga_col:
  assumes "Col A B C" and
    "A B C CongA D E F"
  shows  "Col D E F"
proof -
  {
    assume "Bet A B C"
    then have "Col D E F"
      using Col_def assms(2) bet_conga__bet by blast
  }
  {
    assume "Bet B C A"
    then have "Col D E F"
      by (meson Col_perm Tarski_neutral_dimensionless.l11_21_a Tarski_neutral_dimensionless_axioms \<open>Bet A B C \<Longrightarrow> Col D E F\<close> assms(1) assms(2) or_bet_out out_col)
  }
  {
    assume "Bet C A B"
    then have "Col D E F"
      by (meson Col_perm Tarski_neutral_dimensionless.l11_21_a Tarski_neutral_dimensionless_axioms \<open>Bet A B C \<Longrightarrow> Col D E F\<close> assms(1) assms(2) or_bet_out out_col)
  }
  thus ?thesis
    using Col_def \<open>Bet A B C \<Longrightarrow> Col D E F\<close> \<open>Bet B C A \<Longrightarrow> Col D E F\<close> assms(1) by blast
qed

lemma ncol_conga_ncol:
  assumes "\<not> Col A B C" and
    "A B C CongA D E F"
  shows "\<not> Col D E F"
  using assms(1) assms(2) col_conga_col conga_sym by blast

lemma angle_construction_4:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "A' \<noteq> B'"
  shows "\<exists>C'. (A B C CongA A' B' C' \<and> Coplanar A' B' C' P)"
proof cases
  assume "Col A' B' P"
  thus ?thesis
    using angle_construction_3 assms(1) assms(2) assms(3) ncop__ncols by blast
next
  assume "\<not> Col A' B' P"
  {
    assume "Col A B C"
    then have "\<exists>C'. (A B C CongA A' B' C' \<and> Coplanar A' B' C' P)"
      by (meson angle_construction_3 assms(1) assms(2) assms(3) col__coplanar col_conga_col)
  }
  {
    assume "\<not> Col A B C"
    then obtain C' where "A B C CongA A' B' C' \<and> A' B' OS C' P"
      using \<open>\<not> Col A' B' P\<close> angle_construction_1 by blast
    then have  "\<exists>C'. (A B C CongA A' B' C' \<and> Coplanar A' B' C' P)"
      using os__coplanar by blast
  }
  thus ?thesis
    using \<open>Col A B C \<Longrightarrow> \<exists>C'. A B C CongA A' B' C' \<and> Coplanar A' B' C' P\<close> by blast
qed

lemma lea_distincts:
  assumes "A B C LeA D E F"
  shows "A\<noteq>B \<and> C\<noteq>B \<and> D\<noteq>E \<and> F\<noteq>E"
  by (metis (no_types) LeA_def Tarski_neutral_dimensionless.conga_diff1 Tarski_neutral_dimensionless.conga_diff2 Tarski_neutral_dimensionless_axioms assms inangle_distincts)

lemma l11_29_a:
  assumes "A B C LeA D E F"
  shows "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
proof -
  obtain P where P1: "P InAngle D E F \<and> A B C CongA D E P"
    using LeA_def assms by blast
  then have P2: "E \<noteq> D \<and> B \<noteq> A \<and> E \<noteq> F \<and> E \<noteq> P \<and> B \<noteq> C"
    using conga_diff1 conga_diff2 inangle_distincts by blast
  then have P3: "A \<noteq> B \<and> C \<noteq> B" by blast
  {
    assume Q1: "Bet A B C"
    then have Q2: "Bet D E P"
      by (meson P1 Tarski_neutral_dimensionless.bet_conga__bet Tarski_neutral_dimensionless_axioms)
    have Q3: "C InAngle A B C"
      by (simp add: P3 inangle3123)
    obtain X where Q4: "Bet D X F \<and> (X = E \<or> E Out X P)"
      using InAngle_def P1 by auto
    have "A B C CongA D E F"
    proof -
      {
        assume R1: "X = E"
        have R2: "Bet E F P \<or> Bet E P F"
        proof -
          have R3: "D \<noteq> E" using P2 by blast
          have "Bet D E F"
            using Col_def Col_perm P1 Q2 col_in_angle_out not_bet_and_out by blast
          have "Bet D E P" using Q2 by blast
          thus ?thesis using l5_2
            using R3 \<open>Bet D E F\<close> by blast
        qed
        then have "A B C CongA D E F"
          by (smt P1 P2 bet_out l11_10 l6_6 out_trivial)
      }
      {
        assume S1: "E Out X P"

        have S2: "E Out P F"
        proof -
          {
            assume "Bet E X P"
            then have "E Out P F"
            proof -
              have "Bet E X F"
                by (meson Bet_perm Q2 Q4 \<open>Bet E X P\<close> between_exchange3)
              thus ?thesis
                by (metis Bet_perm S1 bet2__out between_equality_2 between_trivial2 out2_bet_out out_diff1)
            qed
          }
          {
            assume "Bet E P X"
            then have "E Out P F"
              by (smt Bet_perm Q2 Q4 S1 bet_out_1 between_exchange3 not_bet_and_out outer_transitivity_between2)
          }
          thus ?thesis
            using Out_def S1 \<open>Bet E X P \<Longrightarrow> E Out P F\<close> by blast
        qed

        then have "A B C CongA D E F"
          by (metis Bet_perm P2 Q1 Q2 bet_out__bet conga_line)
      }
      thus ?thesis
        using Q4 \<open>X = E \<Longrightarrow> A B C CongA D E F\<close> by blast
    qed
    then have "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
      using conga_diff1 conga_diff2 inangle3123 by blast
  }
  {
    assume "B Out A C"
    obtain Q where "D E F CongA A B Q"
      by (metis P2 angle_construction_3)

    then have "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
      by (metis Tarski_neutral_dimensionless.conga_comm Tarski_neutral_dimensionless_axioms \<open>B Out A C\<close> conga_diff1 conga_sym out321__inangle)
  }
  {
    assume ZZ: "\<not> Col A B C"
    have Z1: "D \<noteq> E"
      using P2 by blast
    have Z2: "F \<noteq> E"
      using P2 by blast
    have Z3: "Bet D E F \<or> E Out D F \<or> \<not> Col D E F"
      using not_bet_out by blast
    {
      assume "Bet D E F"
      obtain Q where Z4: "Bet A B Q \<and> Cong B Q E F"
        using segment_construction by blast

      then have "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
        by (metis InAngle_def P3 Z1 Z2 \<open>Bet D E F\<close> conga_line point_construction_different)
    }
    {
      assume "E Out D F"
      then have Z5: "E Out D P"
        using P1 in_angle_out by blast
      have "D E P CongA A B C"
        by (simp add: P1 conga_sym)
      then have Z6: "B Out A C" using l11_21_a Z5
        by blast

      then have "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
        using \<open>B Out A C \<Longrightarrow> \<exists>Q. C InAngle A B Q \<and> A B Q CongA D E F\<close> by blast
    }
    {
      assume W1: "\<not> Col D E F"
      obtain Q where W2: "D E F CongA A B Q \<and> A B OS Q C"
        using W1 ZZ angle_construction_1 by moura
      obtain DD where W3: "E Out D DD \<and> Cong E DD B A"
        using P3 Z1 segment_construction_3 by force
      obtain FF where W4: "E Out F FF \<and> Cong E FF B Q"
        by (metis P2 W2 conga_diff56 segment_construction_3)
      then have W5: "P InAngle DD E FF"
        by (smt Out_cases P1 P2 W3 l11_25 out_trivial)
      obtain X where W6: "Bet DD X FF \<and> (X = E \<or> E Out X P)"
        using InAngle_def W5 by presburger
      {
        assume W7: "X = E"
        have W8: "Bet D E F"
        proof -
          have W10: "E Out DD D"
            by (simp add: W3 l6_6)
          have "E Out FF F"
            by (simp add: W4 l6_6)
          thus ?thesis using W6 W7 W10 bet_out_out_bet by blast
        qed
        then have "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
          using \<open>Bet D E F \<Longrightarrow> \<exists>Q. C InAngle A B Q \<and> A B Q CongA D E F\<close> by blast
      }
      {
        assume V1: "E Out X P"
        have "B \<noteq> C \<and> E \<noteq> X"
          using P3 V1 out_diff1 by blast
        then obtain CC where V2: "B Out C CC \<and> Cong B CC E X"
          using segment_construction_3 by blast
        then have V3: "A B CC CongA DD E X"
          by (smt P1 P2 V1 W3 l11_10 l6_6 out_trivial)
        have V4: "Cong A CC DD X"
        proof -
          have "Cong A B DD E"
            using W3 not_cong_4321 by blast
          thus ?thesis
            using V2 V3 cong2_conga_cong by blast
        qed

        have V5: "A B Q CongA DD E FF"
        proof -
          have U1: "D E F CongA A B Q"
            by (simp add: W2)
          then have U1A: "A B Q CongA D E F"
            by (simp add: conga_sym)
          have U2: "B Out A A"
            by (simp add: P3 out_trivial)
          have U3: "B Out Q Q"
            using W2 conga_diff56 out_trivial by blast
          have U4: "E Out DD D"
            using W3 l6_6 by blast
          have "E Out FF F"
            by (simp add: W4 l6_6)

          thus ?thesis using l11_10
            using U1A U2 U3 U4 by blast
        qed
        then have V6: "Cong A Q DD FF"
          using Cong_perm W3 W4 cong2_conga_cong by blast
        have "CC B Q CongA X E FF"
        proof -
          have U1: "B A OS CC Q"
            by (metis (no_types) V2 W2 col124__nos invert_one_side one_side_symmetry one_side_transitivity out_one_side)
          have U2: "E DD OS X FF"
          proof -
            have "\<not> Col DD E FF"
              by (metis Col_perm OS_def TS_def U1 V5 ncol_conga_ncol)
            then have "\<not> Col E DD X"
              by (metis Col_def V2 V4 W6 ZZ cong_identity l6_16_1 os_distincts out_one_side)
            then have "DD E OS X FF"
              by (metis Col_perm W6 bet_out not_col_distincts one_side_reflexivity out_out_one_side)
            thus ?thesis
              by (simp add: invert_one_side)
          qed
          have "CC B A CongA X E DD"
            by (simp add: V3 conga_comm)
          thus ?thesis
            using U1 U2 V5 l11_22b by blast
        qed
        then have V8: "Cong CC Q X FF"
          using V2 W4 cong2_conga_cong cong_commutativity not_cong_3412 by blast
        have V9: "CC InAngle A B Q"
        proof -
          have T2: "Q \<noteq> B"
            using W2 conga_diff56 by blast
          have T3: "CC \<noteq> B"
            using V2 out_distinct by blast
          have "Bet A CC Q"
          proof -
            have T4: "DD X FF Cong3 A CC Q"
              using Cong3_def V4 V6 V8 not_cong_3412 by blast
            thus ?thesis
              using W6 l4_6 by blast
          qed
          then have "\<exists> X0. Bet A X0 Q \<and> (X0 = B \<or> B Out X0 CC)"
            using out_trivial by blast
          thus ?thesis
            by (simp add: InAngle_def P3 T2 T3)
        qed
        then have "C InAngle A B Q"
          using V2 inangle_distincts l11_25 out_trivial by blast
        then have "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
          using W2 conga_sym by blast
      }
      then have "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
        using W6 \<open>X = E \<Longrightarrow> \<exists>Q. C InAngle A B Q \<and> A B Q CongA D E F\<close> by blast
    }
    then have "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
      using Z3 \<open>E Out D F \<Longrightarrow> \<exists>Q. C InAngle A B Q \<and> A B Q CongA D E F\<close> \<open>Bet D E F \<Longrightarrow> \<exists>Q. C InAngle A B Q \<and> A B Q CongA D E F\<close> by blast
  }
  thus ?thesis
    using \<open>B Out A C \<Longrightarrow> \<exists>Q. C InAngle A B Q \<and> A B Q CongA D E F\<close> \<open>Bet A B C \<Longrightarrow> \<exists>Q. C InAngle A B Q \<and> A B Q CongA D E F\<close> not_bet_out by blast
qed

lemma in_angle_line:
  assumes "P \<noteq> B" and
    "A \<noteq> B" and
    "C \<noteq> B" and
    "Bet A B C"
  shows "P InAngle A B C"
  using InAngle_def assms(1) assms(2) assms(3) assms(4) by auto

lemma l11_29_b:
  assumes "\<exists> Q. (C InAngle A B Q \<and> A B Q CongA D E F)"
  shows "A B C LeA D E F"
proof -
  obtain Q where P1: "C InAngle A B Q \<and> A B Q CongA D E F"
    using assms by blast
  obtain X where P2: "Bet A X Q \<and> (X = B \<or> B Out X C)"
    using InAngle_def P1 by auto
  {
    assume P2A: "X = B"
    obtain P where P3: "A B C CongA D E P"
      using angle_construction_3 assms conga_diff45 inangle_distincts by fastforce
    have "P InAngle D E F"
    proof -
      have O1: "Bet D E F"
        by (metis (no_types) P1 P2 Tarski_neutral_dimensionless.bet_conga__bet Tarski_neutral_dimensionless_axioms P2A)
      have O2: "P \<noteq> E"
        using P3 conga_diff56 by auto
      have O3: "D \<noteq> E"
        using P3 conga_diff45 by auto
      have "F \<noteq> E"
        using P1 conga_diff56 by blast
      thus ?thesis using in_angle_line
        by (simp add: O1 O2 O3)
    qed
    then have "A B C LeA D E F"
      using LeA_def P3 by blast
  }
  {
    assume G1: "B Out X C"
    obtain DD where G2: "E Out D DD \<and> Cong E DD B A"
      by (metis assms conga_diff1 conga_diff45 segment_construction_3)
    have G3: "D \<noteq> E \<and> DD \<noteq> E"
      using G2 out_diff1 out_diff2 by blast
    obtain FF where G3G: "E Out F FF \<and> Cong E FF B Q"
      by (metis P1 conga_diff56 inangle_distincts segment_construction_3)
    then have G3A: "F \<noteq> E"
      using out_diff1 by blast
    have G3B: "FF \<noteq> E"
      using G3G out_distinct by blast
    have G4: "Bet A B C \<or> B Out A C \<or> \<not> Col A B C"
      using not_bet_out by blast
    {
      assume G5: "Bet A B C"
      have G6: "F InAngle D E F"
        by (simp add: G3 G3A inangle3123)
      have "A B C CongA D E F"
        by (smt Bet_perm G3 G3A G5 Out_def P1 P2 bet_conga__bet between_exchange3 conga_line inangle_distincts outer_transitivity_between2)
      then have  "A B C LeA D E F"
        using G6 LeA_def by blast
    }
    {
      assume G8: "B Out A C"
      have G9: "D InAngle D E F"
        by (simp add: G3 G3A inangle1123)
      have "A B C CongA D E D"
        by (simp add: G3 G8 l11_21_b out_trivial)
      then have  "A B C LeA D E F" using G9 LeA_def by blast
    }
    {
      assume R1: "\<not> Col A B C"
      have R2: "Bet A B Q \<or> B Out A Q \<or> \<not> Col A B Q"
        using not_bet_out by blast
      {
        assume R3: "Bet A B Q"
        obtain P where R4: "A B C CongA D E P"
          by (metis G3 LeA_def \<open>Bet A B C \<Longrightarrow> A B C LeA D E F\<close> angle_construction_3 not_bet_distincts)
        have R5: "P InAngle D E F"
        proof -
          have R6: "P \<noteq> E"
            using R4 conga_diff56 by auto
          have "Bet D E F"
            by (metis (no_types) P1 R3 Tarski_neutral_dimensionless.bet_conga__bet Tarski_neutral_dimensionless_axioms)
          thus ?thesis
            by (simp add: R6 G3 G3A in_angle_line)
        qed
        then have  "A B C LeA D E F" using R4 R5 LeA_def by blast
      }
      {
        assume S1: "B Out A Q"
        have S2: "B Out A C"
          using G1 P2 S1 l6_7 out_bet_out_1 by blast
        have S3: "Col A B C"
          by (simp add: Col_perm S2 out_col)
        then have  "A B C LeA D E F"
          using R1 by blast
      }
      {
        assume S3B: "\<not> Col A B Q"
        obtain P where S4: "A B C CongA D E P \<and> D E OS P F"
          by (meson P1 R1 Tarski_neutral_dimensionless.ncol_conga_ncol Tarski_neutral_dimensionless_axioms S3B angle_construction_1)
        obtain PP where S4A: "E Out P PP \<and> Cong E PP B X"
          by (metis G1 S4 os_distincts out_diff1 segment_construction_3)
        have S5: "P InAngle D E F"
        proof -
          have "PP InAngle DD E FF"
          proof -
            have Z3: "PP \<noteq> E"
              using S4A l6_3_1 by blast
            have Z4: "Bet DD PP FF"
            proof -
              have L1: "C B Q CongA P E F"
              proof -
                have K1: "B A OS C Q"
                  using Col_perm P1 R1 S3B in_angle_one_side invert_one_side by blast
                have K2: "E D OS P F"
                  by (simp add: S4 invert_one_side)
                have "C B A CongA P E D"
                  by (simp add: S4 conga_comm)
                thus ?thesis
                  using K1 K2 P1 l11_22b by auto
              qed
              have L2: "Cong DD FF A Q"
              proof -
                have "DD E FF CongA A B Q"
                proof -
                  have L3: "A B Q CongA D E F"
                    by (simp add: P1)
                  then have L3A: "D E F CongA A B Q"
                    using conga_sym by blast
                  have L4: "E Out DD D"
                    using G2 Out_cases by auto
                  have L5: "E Out FF F"
                    using G3G Out_cases by blast
                  have L6: "B Out A A"
                    using S3B not_col_distincts out_trivial by auto
                  have "B Out Q Q"
                    by (metis S3B not_col_distincts out_trivial)
                  thus ?thesis using L3A L4 L5 L6 l11_10
                    by blast
                qed
                have L2B: "Cong DD E A B"
                  using Cong_perm G2 by blast
                have "Cong E FF B Q"
                  by (simp add: G3G)
                thus ?thesis
                  using L2B \<open>DD E FF CongA A B Q\<close> cong2_conga_cong by auto
              qed
              have L8: "Cong A X DD PP"
              proof -
                have L9: "A B X CongA DD E PP"
                proof -
                  have L9B: "B Out A A"
                    using S3B not_col_distincts out_trivial by blast
                  have L9D: "E Out D D "
                    using G3 out_trivial by auto
                  have "E Out PP P"
                    using Out_cases S4A by blast
                  thus ?thesis using l11_10 S4 L9B G1 L9D
                    using G2 Out_cases by blast
                qed
                have L10: "Cong A B DD E"
                  using G2 not_cong_4321 by blast
                have "Cong B X E PP"
                  using Cong_perm S4A by blast
                thus ?thesis
                  using L10 L9 cong2_conga_cong by blast
              qed
              have "A X Q Cong3 DD PP FF"
              proof -
                have L12B: "Cong A Q DD FF"
                  using L2 not_cong_3412 by blast
                have "Cong X Q PP FF"
                proof -
                  have L13A: "X B Q CongA PP E FF"
                  proof -
                    have L13AC: "B Out Q Q"
                      by (metis S3B col_trivial_2 out_trivial)
                    have L13AD: "E Out PP P"
                      by (simp add: S4A l6_6)
                    have "E Out FF F"
                      by (simp add: G3G l6_6)
                    thus ?thesis
                      using L1 G1 L13AC L13AD l11_10 by blast
                  qed
                  have L13B: "Cong X B PP E"
                    using S4A not_cong_4321 by blast
                  have "Cong B Q E FF"
                    using G3G not_cong_3412 by blast
                  thus ?thesis
                    using L13A L13B cong2_conga_cong by auto
                qed
                thus ?thesis
                  by (simp add: Cong3_def L12B L8)
              qed
              thus ?thesis using P2 l4_6 by blast
            qed
            have "PP = E \<or> E Out PP PP"
              using out_trivial by auto
            thus ?thesis
              using InAngle_def G3 G3B Z3 Z4 by auto
          qed
          thus ?thesis
            using G2 G3G S4A l11_25 by blast
        qed
        then have  "A B C LeA D E F"
          using S4 LeA_def by blast
      }
      then have  "A B C LeA D E F"
        using R2 \<open>B Out A Q \<Longrightarrow> A B C LeA D E F\<close> \<open>Bet A B Q \<Longrightarrow> A B C LeA D E F\<close> by blast
    }
    then have "A B C LeA D E F"
      using G4 \<open>B Out A C \<Longrightarrow> A B C LeA D E F\<close> \<open>Bet A B C \<Longrightarrow> A B C LeA D E F\<close> by blast
  }
  thus ?thesis
    using P2 \<open>X = B \<Longrightarrow> A B C LeA D E F\<close> by blast
qed

lemma bet_in_angle_bet:
  assumes "Bet A B P" and
    "P InAngle A B C"
  shows "Bet A B C"
  by (metis (no_types) Col_def Col_perm assms(1) assms(2) col_in_angle_out not_bet_and_out)

lemma lea_line:
  assumes "Bet A B P" and
    "A B P LeA A B C"
  shows "Bet A B C"
  by (metis Tarski_neutral_dimensionless.bet_conga__bet Tarski_neutral_dimensionless.l11_29_a Tarski_neutral_dimensionless_axioms assms(1) assms(2) bet_in_angle_bet)

lemma eq_conga_out:
  assumes "A B A CongA D E F"
  shows "E Out D F"
  by (metis CongA_def assms l11_21_a out_trivial)

lemma out_conga_out:
  assumes "B Out A C" and
    "A B C CongA D E F"
  shows "E Out D F"
  using assms(1) assms(2) l11_21_a by blast

lemma conga_ex_cong3:
  assumes "A B C CongA A' B' C'"
  shows "\<exists> AA CC. ((B Out A AA \<and> B Out C CC) \<longrightarrow> AA B CC Cong3 A' B' C')"
  using out_diff2 by blast

lemma conga_preserves_in_angle:
  assumes "A B C CongA A' B' C'" and
    "A B I CongA A' B' I'" and
    "I InAngle A B C" and "A' B' OS I' C'"
  shows "I' InAngle A' B' C'"
proof -
  have P1: "A \<noteq> B"
    using assms(1) conga_diff1 by auto
  have P2: "B \<noteq> C"
    using assms(1) conga_diff2 by blast
  have P3: "A' \<noteq> B'"
    using assms(1) conga_diff45 by auto
  have P4: "B' \<noteq> C'"
    using assms(1) conga_diff56 by blast
  have P5: "I \<noteq> B"
    using assms(2) conga_diff2 by auto
  have P6: "I' \<noteq> B'"
    using assms(2) conga_diff56 by blast
  have P7: "Bet A B C \<or> B Out A C \<or> \<not> Col A B C"
    using l6_4_2 by blast
  {
    assume "Bet A B C"
    have Q1: "Bet A' B' C'"
      using \<open>Bet A B C\<close> assms(1) assms(4) bet_col col124__nos col_conga_col by blast
    then have "I' InAngle A' B' C'"
      using assms(4) bet_col col124__nos by auto
  }
  {
    assume "B Out A C"
    then have "I' InAngle A' B' C'"
      by (metis P4 assms(2) assms(3) in_angle_out l11_21_a out321__inangle)
  }
  {
    assume Z1: "\<not> Col A B C"
    have Q2: "Bet A B I \<or> B Out A I \<or> \<not> Col A B I"
      by (simp add: or_bet_out)
    {
      assume "Bet A B I"
      then have "I' InAngle A' B' C'"
        using \<open>Bet A B C \<Longrightarrow> I' InAngle A' B' C'\<close> assms(3) bet_in_angle_bet by blast
    }
    {
      assume "B Out A I"
      then have "I' InAngle A' B' C'"
        using P4 assms(2) l11_21_a out321__inangle by auto
    }
    {
      assume "\<not> Col A B I"
      obtain AA' where Q3: "B' Out A' AA' \<and> Cong B' AA' B A"
        using P1 P3 segment_construction_3 by presburger
      obtain CC' where Q4: "B' Out C' CC' \<and> Cong B' CC' B C"
        using P2 P4 segment_construction_3 by presburger
      obtain J where Q5: "Bet A J C \<and> (J = B \<or> B Out J I)"
        using InAngle_def assms(3) by auto
      have Q6: "B \<noteq> J"
        using Q5 Z1 bet_col by auto
      have Q7: "\<not> Col A B J"
        using Q5 Q6 \<open>\<not> Col A B I\<close> col_permutation_2 col_transitivity_1 out_col by blast
      have "\<not> Col A' B' I'"
        by (metis assms(4) col123__nos)
      then have "\<exists> C'. (A B J CongA A' B' C' \<and> A' B' OS C' I')"
        using Q7 angle_construction_1 by blast
      then obtain J' where Q8: "A B J CongA A' B' J' \<and> A' B' OS J' I'" by blast
      have Q9: "B' \<noteq> J'"
        using Q8 conga_diff56 by blast
      obtain JJ' where Q10: "B' Out J' JJ' \<and> Cong B' JJ' B J"
        using segment_construction_3 Q6 Q9 by blast
      have Q11: "\<not> Col A' B' J'"
        using Q8 col123__nos by blast
      have Q12: "A' \<noteq> JJ'"
        by (metis Col_perm Q10 Q11 out_col)
      have Q13: "B' \<noteq> JJ'"
        using Q10 out_distinct by blast
      have Q14: "\<not> Col A' B' JJ'"
        using Col_perm Q10 Q11 Q13 l6_16_1 out_col by blast
      have Q15: "A B C CongA AA' B' CC'"
      proof -
        have T2: "C \<noteq> B" using P2 by auto
        have T3: "AA' \<noteq> B'"
          using Out_def Q3 by blast
        have T4: "CC' \<noteq> B'"
          using Q4 out_distinct by blast
        have T5: "\<forall> A' C' D' F'. (B Out A' A \<and> B Out C' C \<and> B' Out D' AA' \<and>
B' Out F' CC' \<and>Cong B A' B' D' \<and> Cong B C' B' F' \<longrightarrow> Cong A' C' D' F')"
          by (smt Q3 Q4 Tarski_neutral_dimensionless.l11_4_1 Tarski_neutral_dimensionless_axioms assms(1) l6_6 l6_7)
        thus ?thesis using P1 T2 T3 T4 l11_4_2 by blast
      qed
      have Q16: "A' B' J' CongA A' B' JJ'"
      proof -
        have P9: "B' Out A' A'"
          by (simp add: P3 out_trivial)
        have "B' Out JJ' J'"
          using Out_cases Q10 by auto
        thus ?thesis
          using l11_10
          by (simp add: P9 out2__conga)
      qed
      have Q17: "B' Out I' JJ' \<or> A' B' TS I' JJ'"
      proof -
        have "Coplanar A' I' B' J'"
          by (metis (full_types) Q8 ncoplanar_perm_3 os__coplanar)
        then have "Coplanar A' I' B' JJ'"
          using Q10 Q9 col_cop__cop out_col by blast
        then have R1: "Coplanar A' B' I' JJ'" using coplanar_perm_2
          by blast
        have "A' B' I' CongA A' B' JJ'"
        proof -
          have R2: "A' B' I' CongA A B I"
            by (simp add: assms(2) conga_sym)
          have "A B I CongA A' B' JJ'"
          proof -
            have f1: "\<forall>p pa pb. \<not> p Out pa pb \<and> \<not> p Out pb pa \<or> p Out pa pb"
              using Out_cases by blast
            then have f2: "B' Out JJ' J'"
              using Q10 by blast
            have "B Out J I"
              by (metis Q5 Q6)
            thus ?thesis
              using f2 f1 by (meson P3 Q8 Tarski_neutral_dimensionless.l11_10 Tarski_neutral_dimensionless_axioms \<open>\<not> Col A B I\<close> col_one_side_out col_trivial_2 one_side_reflexivity out_trivial)
          qed
          thus ?thesis
            using R2 conga_trans by blast
        qed
        thus ?thesis using R1 conga_cop__or_out_ts by blast
      qed
      {
        assume Z2: "B' Out I' JJ'"
        have Z3: "J B C CongA J' B' C'"
        proof -
          have R1: "B A OS J C"
            by (metis Q5 Q7 Z1 bet_out invert_one_side not_col_distincts out_one_side)
          have R2: "B' A' OS J' C'"
            by (meson Q10 Z2 assms(4) invert_one_side l6_6 one_side_symmetry out_out_one_side)
          have  "J B A CongA J' B' A'"
            using Q8 conga_comm by blast
          thus ?thesis using assms(1) R1 R2 l11_22b by blast
        qed
        then have "I' InAngle A' B' C'"
        proof -
          have "A J C Cong3 AA' JJ' CC'"
          proof -
            have R8: "Cong A J AA' JJ'"
            proof -
              have R8A: "A B J CongA AA' B' JJ'"
              proof -
                have R8AB: "B Out A A"
                  by (simp add: P1 out_trivial)
                have R8AC: "B Out J I"
                  using Q5 Q6 by auto
                have R8AD: "B' Out AA' A'"
                  using Out_cases Q3 by auto
                have "B' Out JJ' I'"
                  using Out_cases Z2 by blast
                thus ?thesis
                  using assms(2) R8AB R8AC R8AD l11_10 by blast
              qed
              have R8B: "Cong A B AA' B'"
                using Q3 not_cong_4321 by blast
              have R8C: "Cong B J B' JJ'"
                using Q10 not_cong_3412 by blast
              thus ?thesis
                using R8A R8B cong2_conga_cong by blast
            qed
            have LR8A: "Cong A C AA' CC'"
              using Q15 Q3 Q4 cong2_conga_cong cong_4321 cong_symmetry by blast
            have "Cong J C JJ' CC'"
            proof -
              have K1:"B' Out JJ' J'"
                using Out_cases Q10 by auto
              have "B' Out CC' C'"
                using Out_cases Q4 by auto
              then have "J' B' C' CongA JJ' B' CC'" using K1
                by (simp add: out2__conga)
              then have LR9A: "J B C CongA JJ' B' CC'"
                using Z3 conga_trans by blast                                     have LR9B: "Cong J B JJ' B'"
                using Q10 not_cong_4321 by blast
              have "Cong B C B' CC'"
                using Q4 not_cong_3412 by blast
              thus ?thesis
                using LR9A LR9B cong2_conga_cong by blast
            qed
            thus ?thesis using R8 LR8A
              by (simp add: Cong3_def)
          qed
          then have R10: "Bet AA' JJ' CC'" using Q5 l4_6 by blast
          have "JJ' InAngle AA' B' CC'"
          proof -
            have R11: "AA' \<noteq> B'"
              using Out_def Q3 by auto
            have R12: "CC' \<noteq> B'"
              using Out_def Q4 by blast
            have "Bet AA' JJ' CC' \<and> (JJ' = B' \<or> B' Out JJ' JJ')"
              using R10 out_trivial by auto
            thus ?thesis
              using InAngle_def Q13 R11 R12 by auto
          qed
          thus ?thesis
            using Z2 Q3 Q4 l11_25 by blast
        qed
      }
      {
        assume X1: "A' B' TS I' JJ'"
        have "A' B' OS I' J'"
          by (simp add: Q8 one_side_symmetry)
        then have X2: "B' A' OS I' JJ'"
          using Q10 invert_one_side out_out_one_side by blast
        then have "I' InAngle A' B' C'"
          using X1 invert_one_side l9_9 by blast
      }
      then have "I' InAngle A' B' C'"
        using Q17 \<open>B' Out I' JJ' \<Longrightarrow> I' InAngle A' B' C'\<close> by blast
    }
    then have "I' InAngle A' B' C'"
      using Q2 \<open>B Out A I \<Longrightarrow> I' InAngle A' B' C'\<close> \<open>Bet A B I \<Longrightarrow> I' InAngle A' B' C'\<close> by blast
  }
  thus ?thesis
    using P7 \<open>B Out A C \<Longrightarrow> I' InAngle A' B' C'\<close> \<open>Bet A B C \<Longrightarrow> I' InAngle A' B' C'\<close> by blast
qed

lemma l11_30:
  assumes "A B C LeA D E F" and
    "A B C CongA A' B' C'" and
    "D E F CongA D' E' F'"
  shows "A' B' C' LeA D' E' F'"
proof -
  obtain Q where P1: "C InAngle A B Q \<and> A B Q CongA D E F"
    using assms(1) l11_29_a by blast
  have P1A: "C InAngle A B Q" using P1 by simp
  have P1B: "A B Q CongA D E F" using P1 by simp
  have P2: "A \<noteq> B"
    using P1A inangle_distincts by auto
  have P3: "C \<noteq> B"
    using P1A inangle_distincts by blast
  have P4: "A' \<noteq> B'"
    using CongA_def assms(2) by blast
  have P5: "C' \<noteq> B'"
    using CongA_def assms(2) by auto
  have P6: "D \<noteq> E"
    using CongA_def P1B by blast
  have P7: "F \<noteq> E"
    using CongA_def P1B by blast
  have P8: "D' \<noteq> E'"
    using CongA_def assms(3) by blast
  have P9: "F' \<noteq> E'"
    using CongA_def assms(3) by blast
  have P10: "Bet A' B' C' \<or> B' Out A' C' \<or> \<not> Col A' B' C'"
    using or_bet_out by blast
  {
    assume "Bet A' B' C'"
    then have "\<exists> Q'. (C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F')"
      by (metis P1 P4 P5 P8 P9 assms(2) assms(3) bet_conga__bet bet_in_angle_bet conga_line conga_sym inangle3123)
  }
  {
    assume R1: "B' Out A' C'"
    obtain Q' where R2: "D' E' F' CongA A' B' Q'"
      using P4 P8 P9 angle_construction_3 by blast
    then have "C' InAngle A' B' Q'"
      using col_in_angle P1 R1 conga_diff56 out321__inangle by auto
    then have "\<exists> Q'. (C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F')"
      using R2 conga_sym by blast
  }
  {
    assume R3: "\<not> Col A' B' C'"
    have R3A: "Bet D' E' F' \<or> E' Out D' F' \<or> \<not> Col D' E' F'"
      using or_bet_out by blast
    {
      assume "Bet D' E' F'"
      have "\<exists> Q'. (C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F')"
        by (metis P4 P5 P8 P9 \<open>Bet D' E' F'\<close> conga_line in_angle_line point_construction_different)
    }
    {
      assume R4A: "E' Out D' F'"
      obtain Q' where R4: "D' E' F' CongA A' B' Q'"
        using P4 P8 P9 angle_construction_3 by blast
      then have R5: "B' Out A' Q'" using out_conga_out R4A by blast
      have R6: "A B Q CongA D' E' F'"
        using P1 assms(3) conga_trans by blast
      then have R7: "B Out A Q" using out_conga_out R4A R4
        using conga_sym by blast
      have R8: "B Out A C"
        using P1A R7 in_angle_out by blast
      then have R9: "B' Out A' C'" using out_conga_out assms(2)
        by blast
      have "\<exists> Q'. (C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F')"
        by (simp add: R9 \<open>B' Out A' C' \<Longrightarrow> \<exists>Q'. C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F'\<close>)
    }
    {
      assume "\<not> Col D' E' F'"
      obtain QQ where S1: "D' E' F' CongA A' B' QQ \<and> A' B' OS QQ C'"
        using R3 \<open>\<not> Col D' E' F'\<close> angle_construction_1 by blast
      have S1A: "A B Q CongA A' B' QQ" using S1
        using P1 assms(3) conga_trans by blast
      have "A' B' OS C' QQ" using S1
        by (simp add: S1 one_side_symmetry)
      then have S2: "C' InAngle A' B' QQ" using conga_preserves_in_angle S1A
        using P1A assms(2) by blast
      have S3: "A' B' QQ CongA D' E' F'"
        by (simp add: S1 conga_sym)
      then have "\<exists> Q'. (C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F')"
        using S2 by auto
    }
    then have "\<exists> Q'. (C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F')"
      using R3A \<open>E' Out D' F' \<Longrightarrow> \<exists>Q'. C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F'\<close> \<open>Bet D' E' F' \<Longrightarrow> \<exists>Q'. C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F'\<close> by blast
  }
  thus ?thesis using l11_29_b
    using P10 \<open>B' Out A' C' \<Longrightarrow> \<exists>Q'. C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F'\<close> \<open>Bet A' B' C' \<Longrightarrow> \<exists>Q'. C' InAngle A' B' Q' \<and> A' B' Q' CongA D' E' F'\<close> by blast
qed

lemma l11_31_1:
  assumes "B Out A C" and
    "D \<noteq> E" and
    "F \<noteq> E"
  shows "A B C LeA D E F"
  by (metis (full_types) LeA_def assms(1) assms(2) assms(3) l11_21_b out321__inangle segment_construction_3)

lemma l11_31_2:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "D \<noteq> E" and
    "F \<noteq> E" and
    "Bet D E F"
  shows "A B C LeA D E F"
  by (metis LeA_def angle_construction_3 assms(1) assms(2) assms(3) assms(4) assms(5) conga_diff56 in_angle_line)

lemma lea_refl:
  assumes "A \<noteq> B" and
    "C \<noteq> B"
  shows "A B C LeA A B C"
  by (meson assms(1) assms(2) conga_refl l11_29_b out341__inangle out_trivial)

lemma conga__lea:
  assumes "A B C CongA D E F"
  shows "A B C LeA D E F"
  by (metis Tarski_neutral_dimensionless.conga_diff1 Tarski_neutral_dimensionless.conga_diff2 Tarski_neutral_dimensionless.l11_30 Tarski_neutral_dimensionless_axioms assms conga_refl lea_refl)

lemma conga__lea456123:
  assumes "A B C CongA D E F"
  shows "D E F LeA A B C"
  by (simp add: Tarski_neutral_dimensionless.conga__lea Tarski_neutral_dimensionless_axioms assms conga_sym)

lemma lea_left_comm:
  assumes "A B C LeA D E F"
  shows "C B A LeA D E F"
  by (metis assms conga_pseudo_refl conga_refl l11_30 lea_distincts)

lemma lea_right_comm:
  assumes "A B C LeA D E F"
  shows "A B C LeA F E D"
  by (meson assms conga_right_comm l11_29_a l11_29_b)

lemma lea_comm:
  assumes"A B C LeA D E F"
  shows "C B A LeA F E D"
  using assms lea_left_comm lea_right_comm by blast

lemma lta_left_comm:
  assumes "A B C LtA D E F"
  shows "C B A LtA D E F"
  by (meson LtA_def Tarski_neutral_dimensionless.conga_left_comm Tarski_neutral_dimensionless.lea_left_comm Tarski_neutral_dimensionless_axioms assms)

lemma lta_right_comm:
  assumes "A B C LtA D E F"
  shows "A B C LtA F E D"
  by (meson Tarski_neutral_dimensionless.LtA_def Tarski_neutral_dimensionless.conga_comm Tarski_neutral_dimensionless.lea_comm Tarski_neutral_dimensionless.lta_left_comm Tarski_neutral_dimensionless_axioms assms)

lemma lta_comm:
  assumes "A B C LtA D E F"
  shows "C B A LtA F E D"
  using assms lta_left_comm lta_right_comm by blast

lemma lea_out4__lea:
  assumes "A B C LeA D E F" and
    "B Out A A'" and
    "B Out C C'" and
    "E Out D D'" and
    "E Out F F'"
  shows "A' B C' LeA D' E F'"
  using assms(1) assms(2) assms(3) assms(4) assms(5) l11_30 l6_6 out2__conga by auto


lemma lea121345:
  assumes "A \<noteq> B" and
    "C \<noteq> D" and
    "D \<noteq> E"
  shows "A B A LeA C D E"
  using assms(1) assms(2) assms(3) l11_31_1 out_trivial by auto

lemma inangle__lea:
  assumes "P InAngle A B C"
  shows "A B P LeA A B C"
  by (metis Tarski_neutral_dimensionless.l11_29_b Tarski_neutral_dimensionless_axioms assms conga_refl inangle_distincts)

lemma inangle__lea_1:
  assumes "P InAngle A B C"
  shows "P B C LeA A B C"
  by (simp add: Tarski_neutral_dimensionless.inangle__lea Tarski_neutral_dimensionless.lea_comm Tarski_neutral_dimensionless_axioms assms l11_24)

lemma inangle__lta:
  assumes "\<not> Col P B C" and
    "P InAngle A B C"
  shows "A B P LtA A B C"
  by (metis LtA_def TS_def Tarski_neutral_dimensionless.conga_cop__or_out_ts Tarski_neutral_dimensionless.conga_os__out Tarski_neutral_dimensionless.inangle__lea Tarski_neutral_dimensionless.ncol_conga_ncol Tarski_neutral_dimensionless_axioms assms(1) assms(2) col_one_side_out col_trivial_3 in_angle_one_side inangle__coplanar invert_two_sides l11_21_b ncoplanar_perm_12 not_col_permutation_3 one_side_reflexivity)

lemma in_angle_trans:
  assumes "C InAngle A B D" and
    "D InAngle A B E"
  shows "C InAngle A B E"
proof -
  obtain CC where P1: "Bet A CC D \<and> (CC = B \<or> B Out CC C)"
    using InAngle_def assms(1) by auto
  obtain DD where P2: "Bet A DD E \<and> (DD = B \<or> B Out DD D)"
    using InAngle_def assms(2) by auto
  then have P3: "Bet A DD E" by simp
  have P4: "DD = B \<or> B Out DD D" using P2 by simp
  {
    assume "CC = B \<and> DD = B"
    then have "C InAngle A B E"
      using InAngle_def P2 assms(1) assms(2) by auto
  }
  {
    assume "CC = B \<and> B Out DD D"
    then have "C InAngle A B E"
      by (metis InAngle_def P1 assms(1) assms(2) bet_in_angle_bet)
  }
  {
    assume "B Out CC C \<and> DD = B"
    then have "C InAngle A B E"
      by (metis Out_def P2 assms(2) in_angle_line inangle_distincts)
  }
  {
    assume P3: "B Out CC C \<and> B Out DD D"
    then have P3A: "B Out CC C" by simp
    have P3B: "B Out DD D" using P3 by simp
    have "C InAngle A B DD"
      using P3 assms(1) inangle_distincts l11_25 out_trivial by blast
    then obtain CC' where T1: "Bet A CC' DD \<and> (CC' = B \<or> B Out CC' C)"
      using InAngle_def by auto
    {
      assume "CC' = B"
      then have "C InAngle A B E"
        by (metis P2 P3 T1 assms(2) between_exchange4 in_angle_line inangle_distincts out_diff2)
    }
    {
      assume "B Out CC' C"
      then have "C InAngle A B E"
        by (metis InAngle_def P2 T1 assms(1) assms(2) between_exchange4)
    }

    then have "C InAngle A B E"
      using T1 \<open>CC' = B \<Longrightarrow> C InAngle A B E\<close> by blast
  }
  thus ?thesis
    using P1 P2 \<open>B Out CC C \<and> DD = B \<Longrightarrow> C InAngle A B E\<close> \<open>CC = B \<and> B Out DD D \<Longrightarrow> C InAngle A B E\<close> \<open>CC = B \<and> DD = B \<Longrightarrow> C InAngle A B E\<close> by blast
qed

lemma lea_trans:
  assumes "A B C LeA A1 B1 C1" and
    "A1 B1 C1 LeA A2 B2 C2"
  shows "A B C LeA A2 B2 C2"
proof -
  obtain P1 where T1: "P1 InAngle A1 B1 C1 \<and> A B C CongA A1 B1 P1"
    using LeA_def assms(1) by auto
  obtain P2 where T2: "P2 InAngle A2 B2 C2 \<and> A1 B1 C1 CongA A2 B2 P2"
    using LeA_def assms(2) by blast
  have T3: "A \<noteq> B"
    using CongA_def T1 by auto
  have T4: "C \<noteq> B"
    using CongA_def T1 by blast
  have T5: "A1 \<noteq> B1"
    using T1 inangle_distincts by blast
  have T6: "C1 \<noteq> B1"
    using T1 inangle_distincts by blast
  have T7: "A2 \<noteq> B2"
    using T2 inangle_distincts by blast
  have T8: "C2 \<noteq> B2"
    using T2 inangle_distincts by blast
  have T9: "Bet A B C  \<or> B Out A C \<or> \<not> Col A B C"
    using not_out_bet by auto
  {
    assume "Bet A B C"
    then have "A B C LeA A2 B2 C2"
      by (metis T1 T2 T3 T4 T7 T8 bet_conga__bet bet_in_angle_bet l11_31_2)
  }
  {
    assume "B Out A C"
    then have "A B C LeA A2 B2 C2"
      by (simp add: T7 T8 l11_31_1)
  }
  {
    assume H1: "\<not> Col A B C"
    have T10: "Bet A2 B2 C2 \<or> B2 Out A2 C2 \<or> \<not> Col A2 B2 C2"
      using not_out_bet by auto
    {
      assume "Bet A2 B2 C2"
      then have "A B C LeA A2 B2 C2"
        by (simp add: T3 T4 T7 T8 l11_31_2)
    }
    {
      assume T10A: "B2 Out A2 C2"
      have "B Out A C"
      proof -
        have "B1 Out A1 P1"
        proof -
          have "B1 Out A1 C1" using T2 conga_sym T2 T10A in_angle_out out_conga_out by blast
          thus ?thesis using T1 in_angle_out by blast
        qed
        thus ?thesis using T1 conga_sym l11_21_a by blast
      qed
      then have "A B C LeA A2 B2 C2"
        using \<open>B Out A C \<Longrightarrow> A B C LeA A2 B2 C2\<close> by blast
    }
    {
      assume T12: "\<not> Col A2 B2 C2"
      obtain P where T13: "A B C CongA A2 B2 P \<and> A2 B2 OS P C2"
        using T12 H1 angle_construction_1 by blast
      have T14: "A2 B2 OS P2 C2"
      proof -
        have "\<not> Col B2 A2 P2"
        proof -
          have "B2 \<noteq> A2"
            using T7 by auto
          {
            assume H2: "P2 = A2"
            have "A2 B2 A2 CongA A1 B1 C1"
              using T2 H2 conga_sym by blast
            then have "B1 Out A1 C1"
              using eq_conga_out by blast
            then have "B1 Out A1 P1"
              using T1 in_angle_out by blast
            then have "B Out A C"
              using T1 conga_sym out_conga_out by blast
            then have False
              using Col_cases H1 out_col by blast
          }
          then have "P2 \<noteq> A2" by blast
          have "Bet A2 B2 P2 \<or> B2 Out A2 P2 \<or> \<not> Col A2 B2 P2"
            using not_out_bet by auto
          {
            assume H4: "Bet A2 B2 P2"
            then have "Bet A2 B2 C2"
              using T2 bet_in_angle_bet by blast
            then have "Col B2 A2 P2 \<longrightarrow> False"
              using Col_def T12 by blast
            then have "\<not> Col B2 A2 P2"
              using H4 bet_col not_col_permutation_4 by blast
          }
          {
            assume H5: "B2 Out A2 P2"
            then have "B1 Out A1 C1"
              using T2 conga_sym out_conga_out by blast
            then have "B1 Out A1 P1"
              using T1 in_angle_out by blast
            then have "B Out A C"
              using H1 T1 ncol_conga_ncol not_col_permutation_4 out_col by blast
            then have "\<not> Col B2 A2 P2"
              using Col_perm H1 out_col by blast
          }
          {
            assume "\<not> Col A2 B2 P2"
            then have "\<not> Col B2 A2 P2"
              using Col_perm by blast
          }
          thus ?thesis
            using \<open>B2 Out A2 P2 \<Longrightarrow> \<not> Col B2 A2 P2\<close> \<open>Bet A2 B2 P2 \<Longrightarrow> \<not> Col B2 A2 P2\<close> \<open>Bet A2 B2 P2 \<or> B2 Out A2 P2 \<or> \<not> Col A2 B2 P2\<close> by blast
        qed
        thus ?thesis
          by (simp add: T2 T12 in_angle_one_side)
      qed
      have S1: "A2 B2 OS P P2"
        using T13 T14 one_side_symmetry one_side_transitivity by blast
      have "A1 B1 P1 CongA A2 B2 P"
        using conga_trans conga_sym T1 T13 by blast
      then have "P InAngle A2 B2 P2"
        using conga_preserves_in_angle T2 T1 S1 by blast
      then have "P InAngle A2 B2 C2"
        using T2 in_angle_trans by blast
      then have "A B C LeA A2 B2 C2"
        using T13 LeA_def by blast
    }
    then have "A B C LeA A2 B2 C2"
      using T10 \<open>B2 Out A2 C2 \<Longrightarrow> A B C LeA A2 B2 C2\<close> \<open>Bet A2 B2 C2 \<Longrightarrow> A B C LeA A2 B2 C2\<close> by blast
  }
  thus ?thesis
    using T9 \<open>B Out A C \<Longrightarrow> A B C LeA A2 B2 C2\<close> \<open>Bet A B C \<Longrightarrow> A B C LeA A2 B2 C2\<close> by blast
qed

lemma in_angle_asym:
  assumes "D InAngle A B C" and
    "C InAngle A B D"
  shows "A B C CongA A B D"
proof -
  obtain CC where P1: "Bet A CC D \<and> (CC = B \<or> B Out CC C)"
    using InAngle_def assms(2) by auto
  obtain DD where P2: "Bet A DD C \<and> (DD = B \<or> B Out DD D)"
    using InAngle_def assms(1) by auto
  {
    assume "(CC = B) \<and> (DD = B)"
    then have "A B C CongA A B D"
      by (metis P1 P2 assms(2) conga_line inangle_distincts)
  }
  {
    assume "(CC = B) \<and> (B Out DD D)"
    then have "A B C CongA A B D"
      by (metis P1 assms(1) bet_in_angle_bet conga_line inangle_distincts)
  }
  {
    assume "(B Out CC C) \<and> (DD = B)"
    then have "A B C CongA A B D"
      by (metis P2 assms(2) bet_in_angle_bet conga_line inangle_distincts)
  }
  {
    assume V1: "(B Out CC C) \<and> (B Out DD D)"
    obtain X where P3: "Bet CC X C \<and> Bet DD X D"
      using P1 P2 between_symmetry inner_pasch by blast
    then have "B Out X D"
      using V1 out_bet_out_2 by blast
    then have "B Out C D"
      using P3 V1 out2_bet_out by blast
    then have "A B C CongA A B D"
      using assms(2) inangle_distincts l6_6 out2__conga out_trivial by blast
  }
  thus ?thesis using P1 P2
    using \<open>B Out CC C \<and> DD = B \<Longrightarrow> A B C CongA A B D\<close> \<open>CC = B \<and> B Out DD D \<Longrightarrow> A B C CongA A B D\<close> \<open>CC = B \<and> DD = B \<Longrightarrow> A B C CongA A B D\<close> by blast
qed

lemma lea_asym:
  assumes "A B C LeA D E F" and
    "D E F LeA A B C"
  shows "A B C CongA D E F"
proof cases
  assume P1: "Col A B C"
  {
    assume P1A: "Bet A B C"
    have P2: "D \<noteq> E"
      using assms(1) lea_distincts by blast
    have P3: "F \<noteq> E"
      using assms(2) lea_distincts by auto
    have P4: "A \<noteq> B"
      using assms(1) lea_distincts by auto
    have P5: "C \<noteq> B"
      using assms(2) lea_distincts by blast
    obtain P where P6: "P InAngle D E F \<and> A B C CongA D E P"
      using LeA_def assms(1) by blast
    then have "A B C CongA D E P" by simp
    then have "Bet D E P" using P1 P1A bet_conga__bet
      by blast
    then have "Bet D E F"
      using P6 bet_in_angle_bet by blast
    then have "A B C CongA D E F"
      by (metis Tarski_neutral_dimensionless.bet_conga__bet Tarski_neutral_dimensionless.conga_line Tarski_neutral_dimensionless.l11_29_a Tarski_neutral_dimensionless_axioms P2 P3 P4 P5 assms(2) bet_in_angle_bet)
  }
  {
    assume T1: "\<not> Bet A B C"
    then have T2: "B Out A C"
      using P1 not_out_bet by auto
    obtain P where T3: "P InAngle A B C \<and> D E F CongA A B P"
      using LeA_def assms(2) by blast
    then have T3A: "P InAngle A B C" by simp
    have T3B: "D E F CongA A B P" using T3 by simp
    have T4: "E Out D F"
    proof -
      have T4A: "B Out A P"
        using T2 T3 in_angle_out by blast
      have "A B P CongA D E F"
        by (simp add: T3 conga_sym)
      thus ?thesis
        using T4A l11_21_a by blast
    qed
    then have "A B C CongA D E F"
      by (simp add: T2 l11_21_b)
  }
  thus ?thesis
    using \<open>Bet A B C \<Longrightarrow> A B C CongA D E F\<close> by blast
next
  assume T5: "\<not> Col A B C"
  obtain Q where T6: "C InAngle A B Q \<and> A B Q CongA D E F"
    using assms(1) l11_29_a by blast
  then have T6A: "C InAngle A B Q" by simp
  have T6B: "A B Q CongA D E F" by (simp add: T6)
  obtain P where T7: "P InAngle A B C \<and> D E F CongA A B P"
    using LeA_def assms(2) by blast
  then have T7A: "P InAngle A B C" by simp
  have T7B: "D E F CongA A B P" by (simp add: T7)
  have T13: "A B Q CongA  A B P"
    using T6 T7 conga_trans by blast
  have T14: "Bet A B Q \<or> B Out A Q \<or> \<not> Col A B Q"
    using not_out_bet by auto
  {
    assume R1: "Bet A B Q"
    then have "A B C CongA D E F"
      using T13 T5 T7 bet_col bet_conga__bet bet_in_angle_bet by blast
  }
  {
    assume R2: "B Out A Q"
    then have "A B C CongA D E F"
      using T6 in_angle_out l11_21_a l11_21_b by blast
  }
  {
    assume R3: "\<not> Col A B Q"
    have R3A: "Bet A B P \<or> B Out A P \<or> \<not> Col A B P"
      using not_out_bet by blast
    {
      assume R3AA: "Bet A B P"
      then have "A B C CongA D E F"
        using T5 T7 bet_col bet_in_angle_bet by blast
    }
    {
      assume R3AB: "B Out A P"
      then have "A B C CongA D E F"
        by (meson Col_cases R3 T13 ncol_conga_ncol out_col)
    }
    {
      assume R3AC: "\<not> Col A B P"
      have R3AD: "B Out P Q \<or> A B TS P Q"
      proof -
        have "Coplanar A B P Q"
          using T6A T7A coplanar_perm_8 in_angle_trans inangle__coplanar by blast
        thus ?thesis
          by (simp add: T13 conga_sym conga_cop__or_out_ts)
      qed
      {
        assume "B Out P Q"
        then have "C InAngle A B P"
          by (meson R3 T6A bet_col between_symmetry l11_24 l11_25_aux)
        then have "A B C CongA A B P"
          by (simp add: T7A in_angle_asym)
        then have "A B C CongA D E F"
          by (meson T7B Tarski_neutral_dimensionless.conga_sym Tarski_neutral_dimensionless.conga_trans Tarski_neutral_dimensionless_axioms)
      }
      {
        assume W1: "A B TS P Q"
        have "A B OS P Q"
          using Col_perm R3 R3AC T6A T7A in_angle_one_side in_angle_trans by blast
        then have "A B C CongA D E F"
          using W1 l9_9 by blast
      }
      then have "A B C CongA D E F"
        using R3AD \<open>B Out P Q \<Longrightarrow> A B C CongA D E F\<close> by blast
    }
    then have "A B C CongA D E F"
      using R3A \<open>B Out A P \<Longrightarrow> A B C CongA D E F\<close> \<open>Bet A B P \<Longrightarrow> A B C CongA D E F\<close> by blast
  }
  thus ?thesis
    using T14 \<open>B Out A Q \<Longrightarrow> A B C CongA D E F\<close> \<open>Bet A B Q \<Longrightarrow> A B C CongA D E F\<close> by blast
qed

lemma col_lta__bet:
  assumes "Col X Y Z" and
    "A B C LtA X Y Z"
  shows "Bet X Y Z"
proof -
  have "A B C LeA X Y Z \<and> \<not> A B C CongA X Y Z"
    using LtA_def assms(2) by auto
  then have "Y Out X Z \<longrightarrow> False"
    using Tarski_neutral_dimensionless.lea_asym Tarski_neutral_dimensionless.lea_distincts Tarski_neutral_dimensionless_axioms l11_31_1
    by fastforce
  thus ?thesis using not_out_bet assms(1)
    by blast
qed

lemma col_lta__out:
  assumes "Col A B C" and
    "A B C LtA X Y Z"
  shows "B Out A C"
proof -
  have "A B C LeA X Y Z \<and> \<not> A B C CongA X Y Z"
    using LtA_def assms(2) by auto
  thus ?thesis
    by (metis assms(1) l11_31_2 lea_asym lea_distincts or_bet_out)
qed

lemma lta_distincts:
  assumes "A B C LtA D E F"
  shows "A\<noteq>B \<and> C\<noteq>B \<and> D\<noteq>E \<and> F\<noteq>E \<and> D \<noteq> F"
  by (metis LtA_def assms bet_neq12__neq col_lta__bet lea_distincts not_col_distincts)

lemma gta_distincts:
  assumes "A B C GtA D E F"
  shows "A\<noteq>B \<and> C\<noteq>B \<and> D\<noteq>E \<and> F\<noteq>E \<and> A \<noteq> C"
  using GtA_def assms lta_distincts by presburger

lemma acute_distincts:
  assumes "Acute A B C"
  shows "A\<noteq>B \<and> C\<noteq>B"
  using Acute_def assms lta_distincts by blast

lemma obtuse_distincts:
  assumes "Obtuse A B C"
  shows "A\<noteq>B \<and> C\<noteq>B \<and> A \<noteq> C"
  using Obtuse_def assms lta_distincts by blast

lemma two_sides_in_angle:
  assumes "B \<noteq> P'" and
    "B P TS A C" and
    "Bet P B P'"
  shows "P InAngle A B C \<or> P' InAngle A B C"
proof -
  obtain T where P1: "Col T B P \<and> Bet A T C"
    using TS_def assms(2) by auto
  have P2: "A \<noteq> B"
    using assms(2) ts_distincts by blast
  have P3: "C \<noteq> B"
    using assms(2) ts_distincts by blast
  show ?thesis
  proof cases
    assume "B = T"
    thus ?thesis
      using P1 P2 P3 assms(1) in_angle_line by auto
  next
    assume "B \<noteq> T"
    thus ?thesis
      by (metis InAngle_def P1 assms(1) assms(2) assms(3) between_symmetry l6_3_2 or_bet_out ts_distincts)
  qed
qed

lemma in_angle_reverse:
  assumes "A' \<noteq> B" and
    "Bet A B A'" and
    "C InAngle A B D"
  shows  "D InAngle A' B C"
proof -
  have P1: "A \<noteq> B"
    using assms(3) inangle_distincts by auto
  have P2: "D \<noteq> B"
    using assms(3) inangle_distincts by blast
  have P3: "C \<noteq> B"
    using assms(3) inangle_distincts by auto
  show ?thesis
  proof cases
    assume "Col B A C"
    thus ?thesis
      by (smt P1 P2 P3 assms(1) assms(2) assms(3) bet_in_angle_bet between_inner_transitivity between_symmetry in_angle_line l6_3_2 out321__inangle outer_transitivity_between third_point)
  next
    assume P4: "\<not> Col B A C"
    thus ?thesis
    proof cases
      assume "Col B D C"
      thus ?thesis
        by (smt P2 P4 assms(1) assms(2) assms(3) bet_col1 col2__eq col_permutation_2 in_angle_one_side l9_19_R1 out341__inangle)
    next
      assume P5: "\<not> Col B D C"
      have P6: "C B TS A D"
        using P4 P5 assms(3) in_angle_two_sides by auto
      obtain X where P7: "Bet A X D \<and> (X = B \<or> B Out X C)"
        using InAngle_def assms(3) by auto
      have P8: "X = B \<Longrightarrow> D InAngle A' B C"
        using Out_def P1 P2 P3 P7 assms(1) assms(2) l5_2 out321__inangle by auto
      {
        assume P9: "B Out X C"
        have P10: "C \<noteq> B"
          by (simp add: P3)
        have P10A: "\<not> Col B A C"
          by (simp add: P4)
        have P10B: "\<not> Col B D C"
          by (simp add: P5)
        have P10C: "C InAngle D B A"
          by (simp add: assms(3) l11_24)
        {
          assume "Col D B A"
          have "Col B A C"
          proof -
            have "B \<noteq> X"
              using P9 out_distinct by blast
            have "Col B X A"
              by (meson Bet_perm P10C P5 P7 \<open>Col D B A\<close> bet_col1 col_permutation_3 in_angle_out or_bet_out out_col)
            have "Col B X C"
              by (simp add: P9 out_col)
            thus ?thesis
              using \<open>B \<noteq> X\<close> \<open>Col B X A\<close> col_transitivity_1 by blast
          qed
          then have False
            by (simp add: P4)
        }
        then have P10E: "\<not> Col D B A" by auto
        have P11: "D B OS C A"
          by (simp add: P10C P10E P5 in_angle_one_side)
        have P12: "\<not> Col A D B"
          using Col_cases P10E by auto
        have P13: "\<not> Col A' D B"
          by (metis Col_def \<open>Col D B A \<Longrightarrow> False\<close> assms(1) assms(2) col_transitivity_1)
        have P14: "D B TS A A'"
          using P12 P13 TS_def assms(2) col_trivial_3 by blast
        have P15: "D B TS C A'"
          using P11 P14 l9_8_2 one_side_symmetry by blast
        have P16: "\<not> Col C D B"
          by (simp add: P5 not_col_permutation_3)
        obtain Y where P17: "Col Y D B \<and> Bet C Y A'"
          using P15 TS_def by auto
        have P18: "Bet A' Y C"
          using Bet_perm P17 by blast
        {
          assume S1: "Y \<noteq> B"
          have S2: "Col D B Y"
            using P17 not_col_permutation_2 by blast
          then have S3: "Bet D B Y \<or> Bet B Y D \<or> Bet Y D B"
            using Col_def S2 by auto
          {
            assume S4: "Bet D B Y"
            have S5: "C B OS A' Y"
              by (metis P17 P18 P5 S1 bet_out_1 col_transitivity_2 l6_6 not_col_permutation_3 not_col_permutation_5 out_one_side)
            have S6: "C B TS Y D"
              by (metis Bet_perm P16 P17 S1 S4 bet__ts col3 col_trivial_3 invert_two_sides not_col_permutation_1)
            have "C B TS A A'"
              by (metis (full_types) P4 assms(1) assms(2) bet__ts invert_two_sides not_col_permutation_5)
            then have "C B TS Y A"
              using S5 l9_2 l9_8_2 by blast
            then have S9: "C B OS A D"
              using P6 S6 l9_8_1 l9_9 by blast
            then have "B Out Y D"
              using P6 S9 l9_9 by auto
          }
          {
            assume "Bet B Y D"
            then have "B Out Y D"
              by (simp add: S1 bet_out)
          }
          {
            assume "Bet Y D B"
            then have "B Out Y D"
              by (simp add: P2 bet_out_1 l6_6)
          }
          have "B Out Y D"
            using S3 \<open>Bet B Y D \<Longrightarrow> B Out Y D\<close> \<open>Bet D B Y \<Longrightarrow> B Out Y D\<close> \<open>Bet Y D B \<Longrightarrow> B Out Y D\<close> by blast
        }
        then have P19: "(Y = B \<or> B Out Y D)" by auto
        have "D InAngle A' B C"
          using InAngle_def P18 P19 P2 P3 assms(1) by auto
      }
      thus ?thesis using P7 P8 by blast
    qed
  qed
qed

lemma in_angle_trans2:
  assumes "C InAngle A B D" and
    "D InAngle A B E"
  shows "D InAngle C B E"
proof -
  obtain pp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
    f1: "\<forall>p pa. Bet p pa (pp p pa) \<and> pa \<noteq> (pp p pa)"
    using point_construction_different by moura
  then have f2: "\<forall>p. C InAngle D B (pp p B) \<or> \<not> D InAngle p B A"
    by (metis assms(1) in_angle_reverse in_angle_trans l11_24)
  have f3: "D InAngle E B A"
    using assms(2) l11_24 by blast
  then have "E \<noteq> B"
    by (simp add: inangle_distincts)
  thus ?thesis
    using f3 f2 f1 by (meson Bet_perm in_angle_reverse l11_24)
qed

lemma l11_36_aux1:
  assumes "A \<noteq> B" and
    "A' \<noteq> B" and
    "D \<noteq> E" and
    "D' \<noteq> E" and
    "Bet A B A'" and
    "Bet D E D'" and
    "A B C LeA D E F"
  shows "D' E F LeA A' B C"
proof -
  obtain P where P1: "C InAngle A B P \<and>
A B P CongA D E F"
    using assms(7) l11_29_a by blast
  thus ?thesis
    by (metis LeA_def Tarski_neutral_dimensionless.l11_13 Tarski_neutral_dimensionless_axioms assms(2) assms(4) assms(5) assms(6) conga_sym in_angle_reverse)
qed

lemma l11_36_aux2:
  assumes "A \<noteq> B" and
    "A' \<noteq> B" and
    "D \<noteq> E" and
    "D' \<noteq> E" and
    "Bet A B A'" and
    "Bet D E D'" and
    "D' E F LeA A' B C"
  shows "A B C LeA D E F"
  by (metis Bet_cases assms(1) assms(3) assms(5) assms(6) assms(7) l11_36_aux1 lea_distincts)

lemma l11_36:
  assumes "A \<noteq> B" and
    "A' \<noteq> B" and
    "D \<noteq> E" and
    "D' \<noteq> E" and
    "Bet A B A'" and
    "Bet D E D'"
  shows "A B C LeA D E F \<longleftrightarrow> D' E F LeA A' B C"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l11_36_aux1 l11_36_aux2 by auto

lemma l11_41_aux:
  assumes "\<not> Col A B C" and
    "Bet B A D" and
    "A \<noteq> D"
  shows "A C B LtA C A D"
proof -
  obtain M where P1: "M Midpoint A C"
    using midpoint_existence by auto
  obtain P where P2: "M Midpoint B P"
    using symmetric_point_construction by auto
  have P3: "A C B Cong3 C A P"
    by (smt Cong3_def P1 P2 assms(1) l7_13_R1 l7_2 midpoint_distinct_1 not_col_distincts)
  have P4: "A \<noteq> C"
    using assms(1) col_trivial_3 by blast
  have P5: "B \<noteq> C"
    using assms(1) col_trivial_2 by blast
  have P7: "A \<noteq> M"
    using P1 P4 is_midpoint_id by blast
  have P8: "A C B CongA C A P"
    by (simp add: P3 P4 P5 cong3_conga)
  have P8A: "Bet D A B"
    using Bet_perm assms(2) by blast
  have P8B: "Bet P M B"
    by (simp add: P2 between_symmetry midpoint_bet)
  then obtain X where P9: "Bet A X P \<and> Bet M X D" using P8A inner_pasch by blast
  have P9A: "Bet A X P" by (simp add: P9)
  have P9B: "Bet M X D" by (simp add: P9)
  have P10A: "P InAngle C A D"
  proof -
    have K1: "P InAngle M A D"
      by (metis InAngle_def P3 P5 P7 P9 assms(3) bet_out cong3_diff2)
    have K2: "A Out C M"
      using Out_def P1 P4 P7 midpoint_bet by auto
    have K3: "A Out D D"
      using assms(3) out_trivial by auto
    have "A Out P P"
      using K1 inangle_distincts out_trivial by auto
    thus ?thesis
      using K1 K2 K3 l11_25 by blast
  qed
  then have P10: "A C B LeA C A D"
    using LeA_def P8 by auto
  {
    assume K5: "A C B CongA C A D"
    then have K6: "C A D CongA C A P"
      using P8 conga_sym conga_trans by blast
    have K7: "Coplanar C A D P"
      using P10A inangle__coplanar ncoplanar_perm_18 by blast
    then have K8: "A Out D P \<or> C A TS D P"
      by (simp add: K6 conga_cop__or_out_ts)
    {
      assume "A Out D P"

      then have "Col M B A"
        by (meson P8A P8B bet_col1 bet_out__bet between_symmetry not_col_permutation_4)
      then have K8F: "Col A M B"
        using not_col_permutation_1 by blast
      have "Col A M C"
        by (simp add: P1 bet_col midpoint_bet)
      then have "False"
        using K8F P7 assms(1) col_transitivity_1 by blast
    }
    then have K9: "\<not> A Out D P" by auto
    {
      assume V1: "C A TS D P"
      then have V3: "A C TS B P"
        by (metis P10A P8A assms(1) col_trivial_1 col_trivial_2 in_angle_reverse in_angle_two_sides invert_two_sides l11_24 l9_18 not_col_permutation_5)
      have "A C TS B D"
        by (simp add: assms(1) assms(2) assms(3) bet__ts not_col_permutation_5)
      then have "A C OS D P"
        using V1 V3 invert_two_sides l9_8_1 l9_9 by blast
      then have "False"
        using V1 invert_one_side l9_9 by blast
    }
    then have "\<not> C A TS D P" by auto
    then have "False" using K8 K9 by auto
  }
  then have "\<not> A C B CongA C A D" by auto
  thus ?thesis
    by (simp add: LtA_def P10)
qed

lemma l11_41:
  assumes "\<not> Col A B C" and
    "Bet B A D" and
    "A \<noteq> D"
  shows "A C B LtA C A D \<and> A B C LtA C A D"
proof -
  have P1: "A C B LtA C A D"
    using assms(1) assms(2) assms(3) l11_41_aux by auto
  have "A B C LtA C A D"
  proof -
    obtain E where T1: "Bet C A E \<and> Cong A E C A"
      using segment_construction by blast
    have T1A: "Bet C A E" using T1 by simp
    have T1B: "Cong A E C A" using T1 by simp
    have T2: "A B C LtA B A E"
      using T1 assms(1) cong_reverse_identity l11_41_aux not_col_distincts not_col_permutation_5 by blast
    have T3: "B A C CongA C A B"
      by (metis assms(1) conga_pseudo_refl not_col_distincts)
    have T3A: "D A C CongA E A B"
      by (metis CongA_def T1 T3 assms(2) assms(3) cong_reverse_identity l11_13)
    then have T4: "B A E CongA C A D"
      using conga_comm conga_sym by blast
    have "A B C CongA A B C"
      using T2 Tarski_neutral_dimensionless.conga_refl Tarski_neutral_dimensionless.lta_distincts Tarski_neutral_dimensionless_axioms by fastforce
    then have T5: "A B C LeA C A D"
      by (meson T2 T4 Tarski_neutral_dimensionless.LtA_def Tarski_neutral_dimensionless.l11_30 Tarski_neutral_dimensionless_axioms)
    have "\<not> A B C CongA C A D"
      by (meson T2 Tarski_neutral_dimensionless.LtA_def Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless.conga_trans Tarski_neutral_dimensionless_axioms T3A)
    thus ?thesis
      by (simp add: LtA_def T5)
  qed
  thus ?thesis by (simp add: P1)
qed

lemma not_conga:
  assumes "A B C CongA A' B' C'" and
    "\<not> A B C CongA D E F"
  shows "\<not> A' B' C' CongA D E F"
  by (meson assms(1) assms(2) conga_trans)

lemma not_conga_sym:
  assumes "\<not> A B C CongA D E F"
  shows "\<not> D E F CongA A B C"
  using assms conga_sym by blast

lemma not_and_lta:
  shows "\<not> (A B C LtA D E F \<and> D E F LtA A B C)"
proof -
  {
    assume P1: "A B C LtA D E F \<and> D E F LtA A B C"
    then have "A B C CongA D E F"
      using LtA_def lea_asym by blast
    then have "False"
      using LtA_def P1 by blast
  }
  thus ?thesis by auto
qed

lemma conga_preserves_lta:
  assumes "A B C CongA A' B' C'" and
    "D E F CongA D' E' F'" and
    "A B C LtA D E F"
  shows "A' B' C' LtA D' E' F'"
  by (meson Tarski_neutral_dimensionless.LtA_def Tarski_neutral_dimensionless.conga_trans Tarski_neutral_dimensionless.l11_30 Tarski_neutral_dimensionless.not_conga_sym Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3))

lemma lta_trans:
  assumes "A B C LtA A1 B1 C1" and
    "A1 B1 C1 LtA A2 B2 C2"
  shows "A B C LtA A2 B2 C2"
proof -
  have P1: "A B C LeA A2 B2 C2"
    by (meson LtA_def assms(1) assms(2) lea_trans)
  {
    assume "A B C CongA A2 B2 C2"
    then have "False"
      by (meson Tarski_neutral_dimensionless.LtA_def Tarski_neutral_dimensionless.lea_asym Tarski_neutral_dimensionless.lea_trans Tarski_neutral_dimensionless_axioms assms(1) assms(2) conga__lea456123)
  }
  thus ?thesis
    using LtA_def P1 by blast
qed

lemma obtuse_sym:
  assumes "Obtuse A B C"
  shows "Obtuse C B A"
  by (meson Obtuse_def Tarski_neutral_dimensionless.lta_right_comm Tarski_neutral_dimensionless_axioms assms)

lemma acute_sym:
  assumes "Acute A B C"
  shows "Acute C B A"
  by (meson Acute_def Tarski_neutral_dimensionless.lta_left_comm Tarski_neutral_dimensionless_axioms assms)

lemma acute_col__out:
  assumes "Col A B C" and
    "Acute A B C"
  shows "B Out A C"
  by (meson Tarski_neutral_dimensionless.Acute_def Tarski_neutral_dimensionless_axioms assms(1) assms(2) col_lta__out)

lemma col_obtuse__bet:
  assumes "Col A B C" and
    "Obtuse A B C"
  shows "Bet A B C"
  using Obtuse_def assms(1) assms(2) col_lta__bet by blast

lemma out__acute:
  assumes "B Out A C"
  shows "Acute A B C"
proof -
  have P1: "A \<noteq> B"
    using assms out_diff1 by auto
  then obtain D where P3: "B D Perp A B"
    using perp_exists by blast
  then have P4: "B \<noteq> D"
    using perp_distinct by auto
  have P5: "Per A B D"
    by (simp add: P3 l8_2 perp_per_1)
  have P6: "A B C LeA A B D"
    using P1 P4 assms l11_31_1 by auto
  {
    assume "A B C CongA A B D"
    then have "False"
      by (metis Col_cases P1 P4 P5 assms col_conga_col l8_9 out_col)
  }
  then have "A B C LtA A B D"
    using LtA_def P6 by auto
  thus ?thesis
    using P5 Acute_def by auto
qed

lemma bet__obtuse:
  assumes "Bet A B C" and
    "A \<noteq> B" and "B \<noteq> C"
  shows "Obtuse A B C"
proof -
  obtain D where P1: "B D Perp A B"
    using assms(2) perp_exists by blast
  have P5: "B \<noteq> D"
    using P1 perp_not_eq_1 by auto
  have P6: "Per A B D"
    using P1 Perp_cases perp_per_1 by blast
  have P7: "A B D LeA A B C"
    using assms(2) assms(3) P5 assms(1) l11_31_2 by auto
  {
    assume "A B D CongA A B C"
    then have "False"
      using assms(2) P5 P6 assms(1) bet_col ncol_conga_ncol per_not_col by blast
  }
  then have "A B D LtA A B C"
    using LtA_def P7 by blast
  thus ?thesis
    using Obtuse_def P6 by blast
qed

lemma l11_43_aux:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "Per B A C \<or> Obtuse B A C"
  shows "Acute A B C"
proof cases
  assume P1: "Col A B C"
  {
    assume "Per B A C"
    then have "Acute A B C"
      using Col_cases P1 assms(1) assms(2) per_col_eq by blast
  }
  {
    assume "Obtuse B A C"
    then have "Bet B A C"
      using P1 col_obtuse__bet col_permutation_4 by blast
    then have "Acute A B C"
      by (simp add: assms(1) bet_out out__acute)
  }
  thus ?thesis
    using \<open>Per B A C \<Longrightarrow> Acute A B C\<close> assms(3) by blast
next
  assume P2: "\<not> Col A B C"
  then have P3: "B \<noteq> C"
    using col_trivial_2 by auto
  obtain B' where P4: "Bet B A B' \<and> Cong A B' B A"
    using segment_construction by blast
  have P5: "\<not> Col B' A C"
    by (metis Col_def P2 P4 col_transitivity_2 cong_reverse_identity)
  then have P6: "B' \<noteq> A \<and> B' \<noteq> C"
    using not_col_distincts by blast
  then have P7: "A C B LtA C A B' \<and> A B C LtA C A B'"
    using P2 P4 l11_41 by auto
  then have P7A: "A C B LtA C A B'" by simp
  have P7B: "A B C LtA C A B'" by (simp add: P7)
  {
    assume "Per B A C"
    have "Acute A B C"
      by (metis Acute_def P4 P7B \<open>Per B A C\<close> assms(1) bet_col col_per2__per col_trivial_3 l8_3 lta_right_comm)
  }
  {
    assume T1: "Obtuse B A C"
    then obtain a b c where T2: "Per a b c \<and> a b c LtA B A C"
      using Obtuse_def by blast
    then have T2A: "Per a b c" by simp
    have T2B: "a b c LtA B A C" by (simp add: T2)
    then have T3: "a b c LeA B A C \<and> \<not> a b c CongA B A C"
      by (simp add: LtA_def)
    then have T3A: "a b c LeA B A C" by simp
    have T3B: "\<not> a b c CongA B A C" by (simp add: T3)
    obtain P where T4: "P InAngle B A C \<and> a b c CongA B A P"
      using LeA_def T3 by blast
    then have T5: "Per B A P" using T4 T2 l11_17 by blast
    then have T6: "Per P A B"
      using l8_2 by blast
    have "Col A B B'"
      by (simp add: P4 bet_col col_permutation_4)
    then have "Per P A B'"
      using T6 assms(1) per_col by blast
    then have S3: "B A P CongA B' A P"
      using l8_2 P6 T5 T4 CongA_def assms(1) l11_16 by auto
    have "C A B' LtA P A B"
    proof -
      have S4: "B A P LeA B A C \<longleftrightarrow> B' A C LeA B' A P"
        using P4 P6 assms(1) l11_36 by auto
      have S5: "C A B' LeA P A B"
      proof -
        have S6: "B A P LeA B A C"
          using T4 inangle__lea by auto
        have "B' A P CongA P A B"
          using S3 conga_left_comm not_conga_sym by blast
        thus ?thesis
          using P6 S4 S6 assms(2) conga_pseudo_refl l11_30 by auto
      qed
      {
        assume T10: "C A B' CongA P A B"
        have "Per B' A C"
        proof -
          have "B A P CongA B' A C"
            using T10 conga_comm conga_sym by blast
          thus ?thesis
            using T5 l11_17 by blast
        qed
        then have "Per C A B"
          using Col_cases P6 \<open>Col A B B'\<close> l8_2 l8_3 by blast
        have "a b c CongA B A C"
        proof -
          have "a \<noteq> b"
            using T3A lea_distincts by auto
          have "c \<noteq> b"
            using T2B lta_distincts by blast
          have "Per B A C"
            using Per_cases \<open>Per C A B\<close> by blast
          thus ?thesis
            using T2 \<open>a \<noteq> b\<close> \<open>c \<noteq> b\<close> assms(1) assms(2) l11_16 by auto
        qed
        then have "False"
          using T3B by blast
      }
      then have "\<not> C A B' CongA P A B" by blast
      thus ?thesis
        by (simp add: LtA_def S5)
    qed
    then have "A B C LtA B A P"
      by (meson P7 lta_right_comm lta_trans)
    then have "Acute A B C"  using T5
      using Acute_def by blast
  }
  thus ?thesis
    using \<open>Per B A C \<Longrightarrow> Acute A B C\<close> assms(3) by blast
qed

lemma l11_43:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "Per B A C \<or> Obtuse B A C"
  shows "Acute A B C \<and> Acute A C B"
  using Per_perm assms(1) assms(2) assms(3) l11_43_aux obtuse_sym by blast

lemma acute_lea_acute:
  assumes "Acute D E F" and
    "A B C LeA D E F"
  shows "Acute A B C"
proof -
  obtain A' B' C' where P1: "Per A' B' C' \<and> D E F LtA A' B' C'"
    using Acute_def assms(1) by auto
  have P2: "A B C LeA A' B' C'"
    using LtA_def P1 assms(2) lea_trans by blast
  have "\<not> A B C CongA A' B' C'"
    by (meson LtA_def P1 assms(2) conga__lea456123 lea_asym lea_trans)
  then have "A B C LtA A' B' C'"
    by (simp add: LtA_def P2)
  thus ?thesis
    using Acute_def P1 by auto
qed

lemma lea_obtuse_obtuse:
  assumes "Obtuse D E F" and
    "D E F LeA A B C"
  shows "Obtuse A B C"
proof -
  obtain A' B' C' where P1: "Per A' B' C' \<and> A' B' C' LtA D E F"
    using Obtuse_def assms(1) by auto
  then have P2: "A' B' C' LeA A B C"
    using LtA_def assms(2) lea_trans by blast
  have "\<not> A' B' C' CongA A B C"
    by (meson LtA_def P1 assms(2) conga__lea456123 lea_asym lea_trans)
  then have "A' B' C' LtA A B C"
    by (simp add: LtA_def P2)
  thus ?thesis
    using Obtuse_def P1 by auto
qed

lemma l11_44_1_a:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "Cong B A B C"
  shows "B A C CongA B C A"
  by (metis (no_types, hide_lams) Cong3_def assms(1) assms(2) assms(3) cong3_conga cong_inner_transitivity cong_pseudo_reflexivity)

lemma l11_44_2_a:
  assumes "\<not> Col A B C" and
    "B A Lt B C"
  shows "B C A LtA B A C"
proof -
  have T1: "A \<noteq> B"
    using assms(1) col_trivial_1 by auto
  have T3: "A \<noteq> C"
    using assms(1) col_trivial_3 by auto
  have "B A Le B C"
    by (simp add: assms(2) lt__le)
  then obtain C' where P1: "Bet B C' C \<and> Cong B A B C'"
    using assms(2) Le_def by blast
  have T5: "C \<noteq> C'"
    using P1 assms(2) cong__nlt by blast
  have T5A: "C' \<noteq> A"
    using Col_def Col_perm P1 assms(1) by blast
  then have T6: "C' InAngle B A C"
    using InAngle_def P1 T1 T3 out_trivial by auto
  have T7: "C' A C LtA A C' B \<and> C' C A LtA A C' B"
  proof -
    have W1: "\<not> Col C' C A"
      by (metis Col_def P1 T5 assms(1) col_transitivity_2)
    have W2: "Bet C C' B"
      using Bet_perm P1 by blast
    have "C' \<noteq> B"
      using P1 T1 cong_identity by blast
    thus ?thesis
      using l11_41 W1 W2 by simp
  qed
  have T90: "B A C' LtA B A C"
  proof -
    have T90A: "B A C' LeA B A C"
      by (simp add: T6 inangle__lea)
    have "B A C' CongA B A C'"
      using T1 T5A conga_refl by auto
    {
      assume "B A C' CongA B A C"
      then have R1: "A Out C' C"
        by (metis P1 T7 assms(1) bet_out conga_os__out lta_distincts not_col_permutation_4 out_one_side)
      have "B A OS C' C"
        by (metis Col_perm P1 T1 assms(1) bet_out cong_diff_2 out_one_side)
      then have "False"
        using Col_perm P1 T5 R1 bet_col col2__eq one_side_not_col123 out_col by blast
    }
    then have "\<not> B A C' CongA B A C" by blast
    thus ?thesis
      by (simp add: LtA_def T90A)
  qed
  have "B A C' CongA B C' A"
    using P1 T1 T5A l11_44_1_a by auto
  then have K2: "A C' B CongA B A C'"
    using conga_left_comm not_conga_sym by blast
  have "B C A LtA B A C'"
  proof -
    have K1: "B C A CongA B C A"
      using assms(1) conga_refl not_col_distincts by blast
    have "B C A LtA A C' B"
    proof -
      have "C' C A CongA B C A"
      proof -
        have K2: "C Out B C'"
          using P1 T5 bet_out_1 l6_6 by auto
        have "C Out A A"
          by (simp add: T3 out_trivial)
        thus ?thesis
          by (simp add: K2 out2__conga)
      qed
      have "A C' B CongA A C' B"
        using CongA_def K2 conga_refl by auto
      thus ?thesis
        using T7 \<open>C' C A CongA B C A\<close> conga_preserves_lta by auto
    qed
    thus ?thesis
      using K1 K2 conga_preserves_lta by auto
  qed
  thus ?thesis
    using T90 lta_trans by blast
qed

lemma not_lta_and_conga:
  "\<not> ( A B C LtA D E F \<and> A B C CongA D E F)"
  by (simp add: LtA_def)

lemma conga_sym_equiv:
  "A B C CongA A' B' C' \<longleftrightarrow> A' B' C' CongA A B C"
  using not_conga_sym by blast

lemma conga_dec:
  "A B C CongA D E F \<or> \<not> A B C CongA D E F"
  by auto

lemma lta_not_conga:
  assumes "A B C LtA D E F"
  shows "\<not> A B C CongA D E F"
  using assms not_lta_and_conga by auto

lemma lta__lea:
  assumes "A B C LtA D E F"
  shows "A B C LeA D E F"
  using LtA_def assms by auto

lemma nlta:
  "\<not> A B C LtA A B C"
  using not_and_lta by blast

lemma lea__nlta:
  assumes "A B C LeA D E F"
  shows "\<not> D E F LtA A B C"
  by (meson Tarski_neutral_dimensionless.lea_asym Tarski_neutral_dimensionless.not_lta_and_conga Tarski_neutral_dimensionless_axioms assms lta__lea)

lemma lta__nlea:
  assumes "A B C LtA D E F"
  shows "\<not> D E F LeA A B C"
  using assms lea__nlta by blast

lemma l11_44_1_b:
  assumes "\<not> Col A B C" and
    "B A C CongA B C A"
  shows "Cong B A B C"
proof -
  have "B A Lt B C \<or> B A Gt B C \<or> Cong B A B C"
    by (simp add: or_lt_cong_gt)
  thus ?thesis
    by (meson Gt_def assms(1) assms(2) conga_sym l11_44_2_a not_col_permutation_3 not_lta_and_conga)
qed

lemma l11_44_2_b:
  assumes "B A C LtA B C A"
  shows "B C Lt B A"
proof cases
  assume "Col A B C"
  thus ?thesis
    using Col_perm assms bet__lt1213 col_lta__bet lta_distincts by blast
next
  assume P1: "\<not> Col A B C"
  then have P2: "A \<noteq> B"
    using col_trivial_1 by blast
  have P3: "A \<noteq> C"
    using P1 col_trivial_3 by auto
  have "B A Lt B C \<or> B A Gt B C \<or> Cong B A B C"
    by (simp add: or_lt_cong_gt)
  {
    assume "B A Lt B C"
    then have "B C Lt B A"
      using P1 assms l11_44_2_a not_and_lta by blast
  }
  {
    assume "B A Gt B C"
    then have "B C Lt B A"
      using Gt_def P1 assms l11_44_2_a not_and_lta by blast
  }
  {
    assume "Cong B A B C"
    then have "B A C CongA B C A"
      by (simp add: P2 P3 l11_44_1_a)
    then have "B C Lt B A"
      using assms not_lta_and_conga by blast
  }
  thus ?thesis
    by (meson P1 Tarski_neutral_dimensionless.not_and_lta Tarski_neutral_dimensionless_axioms \<open>B A Gt B C \<Longrightarrow> B C Lt B A\<close> \<open>B A Lt B C \<or> B A Gt B C \<or> Cong B A B C\<close> assms l11_44_2_a)
qed

lemma l11_44_1:
  assumes "\<not> Col A B C"
  shows "B A C CongA B C A \<longleftrightarrow> Cong B A B C"
  using assms l11_44_1_a l11_44_1_b not_col_distincts by blast

lemma l11_44_2:
  assumes "\<not> Col A B C"
  shows "B A C LtA B C A \<longleftrightarrow> B C Lt B A"
  using assms l11_44_2_a l11_44_2_b not_col_permutation_3 by blast

lemma l11_44_2bis:
  assumes "\<not> Col A B C"
  shows "B A C LeA B C A \<longleftrightarrow> B C Le B A"
proof -
  {
    assume P1: "B A C LeA B C A"
    {
      assume "B A Lt B C"
      then have "B C A LtA B A C"
        by (simp add: assms l11_44_2_a)
      then have "False"
        using P1 lta__nlea by auto
    }
    then have "\<not> B A Lt B C" by blast
    have "B C Le B A"
      using \<open>\<not> B A Lt B C\<close> nle__lt by blast
  }
  {
    assume P2: "B C Le B A"
    have "B A C LeA B C A"
    proof cases
      assume "Cong B C B A"
      then have "B A C CongA B C A"
        by (metis assms conga_sym l11_44_1_a not_col_distincts)
      thus ?thesis
        by (simp add: conga__lea)
    next
      assume "\<not> Cong B C B A"
      then have "B A C LtA B C A"
        by (simp add: l11_44_2 assms Lt_def P2)
      thus ?thesis
        by (simp add: lta__lea)
    qed
  }
  thus ?thesis
    using \<open>B A C LeA B C A \<Longrightarrow> B C Le B A\<close> by blast
qed

lemma l11_46:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per A B C \<or> Obtuse A B C"
  shows "B A Lt A C \<and> B C Lt A C"
proof cases
  assume "Col A B C"
  thus ?thesis
    by (meson assms(1) assms(2) assms(3) bet__lt1213 bet__lt2313 col_obtuse__bet lt_left_comm per_not_col)
next
  assume P1: "\<not> Col A B C"
  have P2: "A \<noteq> C"
    using P1 col_trivial_3 by auto
  have P3: "Acute B A C \<and> Acute B C A"
    using assms(1) assms(2) assms(3) l11_43 by auto
  then obtain A' B' C' where P4: "Per A' B' C' \<and> B C A LtA A' B' C'"
    using Acute_def P3 by auto
  {
    assume P5: "Per A B C"
    have P5A: "A C B CongA A C B"
      by (simp add: P2 assms(2) conga_refl)
    have S1: "A \<noteq> B"
      by (simp add: assms(1))
    have S2: "B \<noteq> C"
      by (simp add: assms(2))
    have S3: "A' \<noteq> B'"
      using P4 lta_distincts by blast
    have S4: "B' \<noteq> C'"
      using P4 lta_distincts by blast
    then have "A' B' C' CongA A B C" using l11_16
      using S1 S2 S3 S4 P4 P5 by blast
    then have "A C B LtA A B C"
      using P5A P4 conga_preserves_lta lta_left_comm by blast
  }
  {
    assume "Obtuse A B C"
    obtain A'' B'' C'' where P6: "Per A'' B'' C'' \<and> A'' B'' C'' LtA A B C"
      using Obtuse_def \<open>Obtuse A B C\<close> by auto
    have "B C A LtA A' B' C'"
      by (simp add: P4)
    then have P7: "A C B LtA A' B' C'"
      by (simp add: lta_left_comm)
    have "A' B' C' LtA A B C"
    proof -
      have U1: "A'' B'' C'' CongA A' B' C'"
      proof -
        have V2: "A'' \<noteq> B''"
          using P6 lta_distincts by blast
        have V3: "C'' \<noteq> B''"
          using P6 lta_distincts by blast
        have V5: "A' \<noteq> B'"
          using P7 lta_distincts by blast
        have "C' \<noteq> B'"
          using P4 lta_distincts by blast
        thus ?thesis using P6 V2 V3 P4 V5
          by (simp add: l11_16)
      qed
      have U2: "A B C CongA A B C"
        using assms(1) assms(2) conga_refl by auto
      have U3: "A'' B'' C'' LtA A B C"
        by (simp add: P6)
      thus ?thesis
        using U1 U2 conga_preserves_lta by auto
    qed
    then have "A C B LtA A B C"
      using P7 lta_trans by blast
  }
  then have "A C B LtA A B C"
    using \<open>Per A B C \<Longrightarrow> A C B LtA A B C\<close> assms(3) by blast
  then have "A B Lt A C"
    by (simp add: l11_44_2_b)
  then have "B A Lt A C"
    using Lt_cases by blast
  have "C A B LtA C B A"
  proof -
    obtain A' B' C' where U4: "Per A' B' C' \<and> B A C LtA A' B' C'"
      using Acute_def P3 by blast
    {
      assume "Per A B C"
      then have W3: "A' B' C' CongA C B A"
        using U4 assms(2) l11_16 l8_2 lta_distincts by blast
      have W2: "C A B CongA C A B"
        using P2 assms(1) conga_refl by auto
      have "C A B LtA A' B' C'"
        by (simp add: U4 lta_left_comm)
      then have "C A B LtA C B A"
        using W2 W3 conga_preserves_lta by blast
    }
    {
      assume "Obtuse A B C"
      then obtain A'' B'' C'' where W4: "Per A'' B'' C'' \<and> A'' B'' C'' LtA A B C"
        using Obtuse_def by auto
      have W5: "C A B LtA A' B' C'"
        by (simp add: U4 lta_left_comm)
      have "A' B' C' LtA C B A"
      proof -
        have W6: "A'' B'' C'' CongA A' B' C'" using l11_16 W4 U4
          using lta_distincts by blast
        have "C B A CongA C B A"
          using assms(1) assms(2) conga_refl by auto
        thus ?thesis
          using W4 W6 conga_left_comm conga_preserves_lta by blast
      qed
      then have "C A B LtA C B A"
        using W5 lta_trans by blast
    }
    thus ?thesis
      using \<open>Per A B C \<Longrightarrow> C A B LtA C B A\<close> assms(3) by blast
  qed
  then have "C B Lt C A"
    by (simp add: l11_44_2_b)
  then have "C B Lt A C"
    using Lt_cases by auto
  then have "B C Lt A C"
    using Lt_cases by blast
  thus ?thesis
    by (simp add: \<open>B A Lt A C\<close>)
qed

lemma l11_47:
  assumes "Per A C B" and
    "H PerpAt C H A B"
  shows "Bet A H B \<and> A \<noteq> H \<and> B \<noteq> H"
proof -
  have P1: "Per C H A"
    using assms(2) perp_in_per_1 by auto
  have P2: "C H Perp A B"
    using assms(2) perp_in_perp by auto
  thus ?thesis
  proof cases
    assume "Col A C B"
    thus ?thesis
      by (metis P1 assms(1) assms(2) per_distinct_1 per_not_col perp_in_distinct perp_in_id)
  next
    assume P3: "\<not> Col A C B"
    have P4: "A \<noteq> H"
      by (metis P2 Per_perm Tarski_neutral_dimensionless.l8_7 Tarski_neutral_dimensionless_axioms assms(1) assms(2) col_trivial_1 perp_in_per_2 perp_not_col2)
    have P5: "Per C H B"
      using assms(2) perp_in_per_2 by auto
    have P6: "B \<noteq> H"
      using P1 P2 assms(1) l8_2 l8_7 perp_not_eq_1 by blast
    have P7: "H A Lt A C \<and> H C Lt A C"
      by (metis P1 P2 P4 l11_46 l8_2 perp_distinct)
    have P8: "C A Lt A B \<and> C B Lt A B"
      using P3 assms(1) l11_46 not_col_distincts by blast
    have P9: "H B Lt B C \<and> H C Lt B C"
      by (metis P2 P5 P6 Per_cases l11_46 perp_not_eq_1)
    have P10: "Bet A H B"
    proof -
      have T1: "Col A H B"
        using assms(2) col_permutation_5 perp_in_col by blast
      have T2: "A H Le A B" using P7 P8
        by (meson lt_comm lt_transitivity nlt__le not_and_lt)
      have "H B Le A B"
        by (meson Lt_cases P8 P9 le_transitivity local.le_cases lt__nle)
      thus ?thesis
        using T1 T2 l5_12_b by blast
    qed
    thus ?thesis
      by (simp add: P4 P6)
  qed
qed

lemma l11_49:
  assumes "A B C CongA A' B' C'" and
    "Cong B A B' A'" and
    "Cong B C B' C'"
  shows "Cong A C A' C' \<and> (A \<noteq> C \<longrightarrow> (B A C CongA B' A' C' \<and> B C A CongA B' C' A'))"
proof -
  have T1:" Cong A C A' C'"
    using assms(1) assms(2) assms(3) cong2_conga_cong not_cong_2143 by blast
  {
    assume P1: "A \<noteq> C"
    have P2: "A \<noteq> B"
      using CongA_def assms(1) by blast
    have P3: "C \<noteq> B"
      using CongA_def assms(1) by blast
    have "B A C Cong3 B' A' C'"
      by (simp add: Cong3_def T1 assms(2) assms(3))
    then have T2: "B A C CongA B' A' C'"
      using P1 P2 cong3_conga by auto
    have "B C A Cong3 B' C' A'"
      using Cong3_def T1 assms(2) assms(3) cong_3_swap_2 by blast
    then have "B C A CongA B' C' A'"
      using P1 P3 cong3_conga by auto
    then have "B A C CongA B' A' C' \<and> B C A CongA B' C' A'" using T2 by blast
  }
  thus ?thesis
    by (simp add: T1)
qed

lemma l11_50_1:
  assumes "\<not> Col A B C" and
    "B A C CongA B' A' C'" and
    "A B C CongA A' B' C'" and
    "Cong A B A' B'"
  shows "Cong A C A' C' \<and> Cong B C B' C' \<and> A C B CongA A' C' B'"
proof -
  obtain C'' where P1: "B' Out C'' C' \<and> Cong B' C'' B C"
    by (metis Col_perm assms(1) assms(3) col_trivial_3 conga_diff56 l6_11_existence)
  have P2: "B' \<noteq> C''"
    using P1 out_diff1 by auto
  have P3: "\<not> Col A' B' C'"
    using assms(1) assms(3) ncol_conga_ncol by blast
  have P4: "\<not> Col A' B' C''"
    by (meson P1 P2 P3 col_transitivity_1 not_col_permutation_2 out_col)
  have P5: "Cong A C A' C''"
  proof -
    have Q1: "B Out A A"
      using assms(1) not_col_distincts out_trivial by auto
    have Q2: "B Out C C"
      using assms(1) col_trivial_2 out_trivial by force
    have Q3: "B' Out A' A'"
      using P3 not_col_distincts out_trivial by auto
    have Q5: "Cong B A B' A'"
      using assms(4) not_cong_2143 by blast
    have "Cong B C B' C''"
      using P1 not_cong_3412 by blast
    thus ?thesis
      using l11_4_1 P1 Q1 Q2 Q3 Q5 assms(3) by blast
  qed
  have P6: "B A C Cong3 B' A' C''"
    using Cong3_def Cong_perm P1 P5 assms(4) by blast
  have P7: "B A C CongA B' A' C''"
    by (metis P6 assms(1) cong3_conga not_col_distincts)
  have P8: "B' A' C' CongA B' A' C''"
    by (meson P7 assms(2) conga_sym conga_trans)
  have "B' A' OS C' C''"
    using Col_perm Out_cases P1 P3 out_one_side by blast
  then have "A' Out C' C''"
    using P8 conga_os__out by auto
  then have "Col A' C' C''"
    using out_col by auto
  then have P9: "C' = C''"
    using Col_perm P1 out_col P3 col_transitivity_1 by blast
  have T1: "Cong A C A' C'"
    by (simp add: P5 P9)
  have T2: "Cong B C B' C'"
    using Cong_perm P1 P9 by blast
  then have "A C B CongA A' C' B'"
    using T1 assms(1) assms(2) assms(4) col_trivial_2 l11_49 by blast
  thus ?thesis using T1 T2 by blast
qed

lemma l11_50_2:
  assumes "\<not> Col A B C" and
    "B C A CongA B' C' A'" and
    "A B C CongA A' B' C'" and
    "Cong A B A' B'"
  shows "Cong A C A' C' \<and> Cong B C B' C' \<and> C A B CongA C' A' B'"
proof -
  have P1: "A \<noteq> B"
    using assms(1) col_trivial_1 by auto
  have P2: "B \<noteq> C"
    using assms(1) col_trivial_2 by auto
  have P3: "A' \<noteq> B'"
    using P1 assms(4) cong_diff by blast
  have P4: "B' \<noteq> C'"
    using assms(2) conga_diff45 by auto
  then obtain C'' where P5: "B' Out C'' C' \<and> Cong B' C'' B C"
    using P2 l6_11_existence by presburger
  have P5BIS: "B' \<noteq> C''"
    using P5 out_diff1 by auto
  have P5A: "Col B' C'' C'"
    using P5 out_col by auto
  have P6: "\<not> Col A' B' C'"
    using assms(1) assms(3) ncol_conga_ncol by blast
  {
    assume "Col A' B' C''"
    then have "Col B' C'' A'"
      using not_col_permutation_2 by blast
    then have "Col B' C' A'" using col_transitivity_1 P5BIS P5A by blast
    then have "Col A' B' C'"
      using Col_perm by blast
    then have False
      using P6 by auto
  }
  then have P7: "\<not> Col A' B' C''" by blast
  have P8: "Cong A C A' C''"
  proof -
    have "B Out A A"
      by (simp add: P1 out_trivial)
    have K1: "B Out C C"
      using P2 out_trivial by auto
    have K2: "B' Out A' A'"
      using P3 out_trivial by auto
    have "Cong B A B' A'"
      by (simp add: Cong_perm assms(4))
    have "Cong B C B' C''"
      using Cong_perm P5 by blast
    thus ?thesis
      using P5 \<open>Cong B A B' A'\<close> P1 out_trivial K1 K2 assms(3) l11_4_1 by blast
  qed
  have P9: "B C A Cong3 B' C'' A'"
    using Cong3_def Cong_perm P5 P8 assms(4) by blast
  then have P10: "B C A CongA B' C'' A'"
    using assms(1) cong3_conga not_col_distincts by auto
  have P11: "B' C' A' CongA B' C'' A'"
    using P9 assms(2) cong3_conga2 conga_sym by blast
  show ?thesis
  proof cases
    assume L1: "C' = C''"
    then have L2: "Cong A C A' C'"
      by (simp add: P8)
    have L3: "Cong B C B' C'"
      using Cong_perm L1 P5 by blast
    have "C A B Cong3 C' A' B'"
      by (simp add: L1 P9 cong_3_swap cong_3_swap_2)
    then have "C A B CongA C' A' B'"
      by (metis CongA_def P1 assms(2) cong3_conga)
    thus ?thesis using L2 L3 by auto
  next
    assume R1: "C' \<noteq> C''"
    have R1A: "\<not> Col C'' C' A'"
      by (metis P5A P7 R1 col_permutation_2 col_trivial_2 colx)
    have R1B: "Bet B' C'' C' \<or> Bet B' C' C''"
      using Out_def P5 by auto
    {
      assume S1: "Bet B' C'' C'"
      then have S2: "C'' A' C' LtA A' C'' B' \<and> C'' C' A' LtA A' C'' B'"
        using P5BIS R1A between_symmetry l11_41 by blast
      have "B' C' A' CongA C'' C' A'"
        by (metis P11 R1 Tarski_neutral_dimensionless.conga_comm Tarski_neutral_dimensionless_axioms S1 bet_out_1 conga_diff45 not_conga_sym out2__conga out_trivial)
      then have "B' C' A' LtA A' C'' B'"
        by (meson P11 Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless.not_conga Tarski_neutral_dimensionless.not_conga_sym Tarski_neutral_dimensionless_axioms S2 not_lta_and_conga)
      then have "Cong A C A' C' \<and> Cong B C B' C'"
        by (meson P11 Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless_axioms not_lta_and_conga)
    }
    {
      assume Z1: "Bet B' C' C''"
      have Z2: "\<not> Col C' C'' A'"
        by (simp add: R1A not_col_permutation_4)
      have Z3: "C'' Out C' B'"
        by (simp add: R1 Z1 bet_out_1)
      have Z4: "C'' Out A' A'"
        using P7 not_col_distincts out_trivial by blast
      then have Z4A: "B' C'' A' CongA C' C'' A'"
        by (simp add: Z3 out2__conga)
      have Z4B: "B' C'' A' LtA A' C' B'"
      proof -
        have Z5: "C' C'' A' CongA B' C'' A'"
          using Z4A not_conga_sym by blast
        have Z6: "A' C' B' CongA A' C' B'"
          using P11 P4 conga_diff2 conga_refl by blast
        have "C' C'' A' LtA A' C' B'"
          using P4 Z1 Z2 between_symmetry l11_41 by blast
        thus ?thesis
          using Z5 Z6 conga_preserves_lta by auto
      qed
      have "B' C'' A' CongA B' C' A'"
        using P11 not_conga_sym by blast
      then have "Cong A C A' C' \<and> Cong B C B' C'"
        by (meson Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless_axioms Z4B not_lta_and_conga)
    }
    then have R2: "Cong A C A' C' \<and> Cong B C B' C'"
      using R1B \<open>Bet B' C'' C' \<Longrightarrow> Cong A C A' C' \<and> Cong B C B' C'\<close> by blast
    then have "C A B CongA C' A' B'"
      using P1 assms(2) l11_49 not_cong_2143 by blast
    thus ?thesis using R2 by auto
  qed
qed

lemma l11_51:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C" and
    "Cong A B A' B'" and
    "Cong A C A' C'" and
    "Cong B C B' C'"
  shows
    "B A C CongA B' A' C' \<and> A B C CongA A' B' C' \<and> B C A CongA B' C' A'"
proof -
  have "B A C Cong3 B' A' C' \<and> A B C Cong3 A' B' C' \<and> B C A Cong3 B' C' A'"
    using Cong3_def Cong_perm assms(4) assms(5) assms(6) by blast
  thus ?thesis
    using assms(1) assms(2) assms(3) cong3_conga by auto
qed

lemma conga_distinct:
  assumes "A B C CongA D E F"
  shows "A \<noteq> B \<and> C \<noteq> B \<and> D \<noteq> E \<and> F \<noteq> E"
  using CongA_def assms by auto

lemma l11_52:
  assumes "A B C CongA A' B' C'" and
    "Cong A C A' C'" and
    "Cong B C B' C'" and
    "B C Le A C"
  shows "Cong B A B' A' \<and> B A C CongA B' A' C' \<and> B C A CongA B' C' A'"
proof -
  have P1: "A \<noteq> B"
    using CongA_def assms(1) by blast
  have P2: "C \<noteq> B"
    using CongA_def assms(1) by blast
  have P3: "A' \<noteq> B'"
    using CongA_def assms(1) by blast
  have P4: "C' \<noteq> B'"
    using assms(1) conga_diff56 by auto
  have P5: "Cong B A B' A'"
  proof cases
    assume P6: "Col A B C"
    then have P7: "Bet A B C \<or> Bet B C A \<or> Bet C A B"
      using Col_def by blast
    {
      assume P8: "Bet A B C"
      then have "Bet A' B' C'"
        using assms(1) bet_conga__bet by blast
      then have "Cong B A B' A'"
        using P8 assms(2) assms(3) l4_3 not_cong_2143 by blast
    }
    {
      assume P9: "Bet B C A"
      then have P10: "B' Out A' C'"
        using Out_cases P2 assms(1) bet_out l11_21_a by blast
      then have P11: "Bet B' A' C' \<or> Bet B' C' A'"
        by (simp add: Out_def)
      {
        assume "Bet B' A' C'"
        then have "Cong B A B' A'"
          using P3 assms(2) assms(3) assms(4) bet_le_eq l5_6 by blast
      }
      {
        assume "Bet B' C' A'"
        then have "Cong B A B' A'"
          using Cong_perm P9 assms(2) assms(3) l2_11_b by blast
      }
      then have "Cong B A B' A'"
        using P11 \<open>Bet B' A' C' \<Longrightarrow> Cong B A B' A'\<close> by blast
    }
    {
      assume "Bet C A B"
      then have "Cong B A B' A'"
        using P1 assms(4) bet_le_eq between_symmetry by blast
    }
    thus ?thesis
      using P7 \<open>Bet A B C \<Longrightarrow> Cong B A B' A'\<close> \<open>Bet B C A \<Longrightarrow> Cong B A B' A'\<close> by blast
  next
    assume Z1: "\<not> Col A B C"
    obtain A'' where Z2: "B' Out A'' A' \<and> Cong B' A'' B A"
      using P1 P3 l6_11_existence by force
    then have Z3: "A' B' C' CongA A'' B' C'"
      by (simp add: P4 out2__conga out_trivial)
    have Z4: "A B C CongA A'' B' C'"
      using Z3 assms(1) not_conga by blast
    have Z5: "Cong A'' C' A C"
      using Z2 Z4 assms(3) cong2_conga_cong cong_4321 cong_symmetry by blast
    have Z6: "A'' B' C' Cong3 A B C"
      using Cong3_def Cong_perm Z2 Z5 assms(3) by blast
    have Z7: "Cong A'' C' A' C'"
      using Z5 assms(2) cong_transitivity by blast
    have Z8: "\<not> Col A' B' C'"
      by (metis Z1 assms(1) ncol_conga_ncol)
    then have Z9: "\<not> Col A'' B' C'"
      by (metis Z2 col_transitivity_1 not_col_permutation_4 out_col out_diff1)
    {
      assume Z9A: "A'' \<noteq> A'"
      have Z10: "Bet B' A'' A' \<or> Bet B' A' A''"
        using Out_def Z2 by auto
      {
        assume Z11: "Bet B' A'' A'"
        have Z12: "A'' C' B' LtA C' A'' A' \<and> A'' B' C' LtA C' A'' A'"
          by (simp add: Z11 Z9 Z9A l11_41)
        have Z13: "Cong A' C' A'' C'"
          using Cong_perm Z7 by blast
        have Z14: "\<not> Col A'' C' A'"
          by (metis Col_def Z11 Z9 Z9A col_transitivity_1)
        have Z15: "C' A'' A' CongA C' A' A'' \<longleftrightarrow> Cong C' A'' C' A'"
          by (simp add: Z14 l11_44_1)
        have Z16: "Cong C' A' C' A''"
          using Cong_perm Z7 by blast
        then have Z17: "Cong C' A'' C' A'"
          using Cong_perm by blast
        then have Z18: "C' A'' A' CongA C' A' A''"
          by (simp add: Z15)
        have Z19: "\<not> Col B' C' A''"
          using Col_perm Z9 by blast
        have Z20: "B' A' C' CongA A'' A' C'"
          by (metis Tarski_neutral_dimensionless.col_conga_col Tarski_neutral_dimensionless_axioms Z11 Z3 Z9 Z9A bet_out_1 col_trivial_3 out2__conga out_trivial)
        have Z21: "\<not> Col B' C' A'"
          using Col_perm Z8 by blast
        then have Z22: "C' B' A' LtA C' A' B' \<longleftrightarrow> C' A' Lt C' B'"
          by (simp add: l11_44_2)
        have "A'' B' C' CongA C' B' A'"
          using Z3 conga_right_comm not_conga_sym by blast
        then have U1: "C' B' A' LtA C' A' B'"
        proof -
          have f1: "\<forall>p pa pb pc pd pe pf pg ph pi pj pk pl pm. \<not> Tarski_neutral_dimensionless p pa \<or> \<not> Tarski_neutral_dimensionless.CongA p pa (pb::'p) pc pd pe pf pg \<or> \<not> Tarski_neutral_dimensionless.CongA p pa ph pi pj pk pl pm \<or> \<not> Tarski_neutral_dimensionless.LtA p pa pb pc pd ph pi pj \<or> Tarski_neutral_dimensionless.LtA p pa pe pf pg pk pl pm"
            by (simp add: Tarski_neutral_dimensionless.conga_preserves_lta)
          have f2: "C' A'' A' CongA C' A' A''"
            by (metis Z15 Z17)
          have f3: "\<forall>p pa pb pc pd pe pf pg. \<not> Tarski_neutral_dimensionless p pa \<or> \<not> Tarski_neutral_dimensionless.CongA p pa (pb::'p) pc pd pe pf pg \<or> Tarski_neutral_dimensionless.CongA p pa pe pf pg pb pc pd"
            by (metis (no_types) Tarski_neutral_dimensionless.conga_sym)
          then have "\<not> C' B' A' LtA C' A'' A' \<or> A'' B' C' LtA C' A' A''"
            using f2 f1 by (meson Tarski_neutral_dimensionless_axioms \<open>A'' B' C' CongA C' B' A'\<close>)
          then have "C' B' A' LtA C' A' B' \<or> A'' B' C' LtA A'' A' C' \<or> A'' = B'"
            using f2 f1 by (metis (no_types) Tarski_neutral_dimensionless.conga_refl Tarski_neutral_dimensionless_axioms Z12 \<open>A'' B' C' CongA C' B' A'\<close> lta_right_comm)
          thus ?thesis
            using f3 f2 f1 by (metis (no_types) Tarski_neutral_dimensionless_axioms Z12 Z20 \<open>A'' B' C' CongA C' B' A'\<close> lta_right_comm)
        qed
        then have Z23: "C' A' Lt C' B'"
          using Z22 by auto
        have Z24: "C' A'' Lt C' B'"
          using Z16 Z23 cong2_lt__lt cong_reflexivity by blast
        have Z25: "C A Le C B"
        proof -
          have Z26: "Cong C' A'' C A"
            using Z5 not_cong_2143 by blast
          have "Cong C' B' C B"
            using assms(3) not_cong_4321 by blast
          thus ?thesis
            using l5_6 Z24 Z26 lt__le by blast
        qed
        then have Z27: "Cong C A C B"
          by (simp add: assms(4) le_anti_symmetry le_comm)
        have "Cong C' A'' C' B'"
          by (metis Cong_perm Z13 Z27 assms(2) assms(3) cong_transitivity)
        then have "False"
          using Z24 cong__nlt by blast
        then have "Cong B A B' A'" by simp
      }
      {
        assume W1: "Bet B' A' A''"
        have W2: "A' \<noteq> A''"
          using Z9A by auto
        have W3: "A' C' B' LtA C' A' A'' \<and> A' B' C' LtA C' A' A''"
          using W1 Z8 Z9A l11_41 by blast
        have W4: "Cong A' C' A'' C'"
          using Z7 not_cong_3412 by blast
        have "\<not> Col A'' C' A'"
          by (metis Col_def W1 Z8 Z9A col_transitivity_1)
        then have W6: "C' A'' A' CongA C' A' A'' \<longleftrightarrow> Cong C' A'' C' A'"
          using l11_44_1 by auto
        have W7: "Cong C' A' C' A''"
          using Z7 not_cong_4321 by blast
        then have W8: "Cong C' A'' C' A'"
          using W4 not_cong_4321 by blast
        have W9: "\<not> Col B' C' A''"
          by (simp add: Z9 not_col_permutation_1)
        have W10: "B' A'' C' CongA A' A'' C'"
          by (metis Tarski_neutral_dimensionless.Out_def Tarski_neutral_dimensionless_axioms W1 Z9 Z9A bet_out_1 between_trivial not_col_distincts out2__conga)
        have W12: "C' B' A'' LtA C' A'' B' \<longleftrightarrow> C' A'' Lt C' B'"
          by (simp add: W9 l11_44_2)
        have W12A: "C' B' A'' LtA C' A'' B'"
        proof -
          have V1: "A' B' C' CongA C' B' A''"
            by (simp add: Z3 conga_right_comm)
          have "A' A'' C' CongA B' A'' C'"
            by (metis Tarski_neutral_dimensionless.Out_def Tarski_neutral_dimensionless_axioms W1 \<open>\<not> Col A'' C' A'\<close> between_equality_2 not_col_distincts or_bet_out out2__conga out_col)
          then have "C' A' A'' CongA C' A'' B'"
            by (meson W6 W8 conga_left_comm not_conga not_conga_sym)
          thus ?thesis
            using W3 V1 conga_preserves_lta by auto
        qed
        then have "C' A'' Lt C' B'" using W12 by auto
        then have W14: "C' A' Lt C' B'"
          using W8 cong2_lt__lt cong_reflexivity by blast
        have W15: "C A Le C B"
        proof -
          have Q1: "C' A'' Le C' B'"
            using W12 W12A lt__le by blast
          have Q2: "Cong C' A'' C A"
            using Z5 not_cong_2143 by blast
          have "Cong C' B' C B"
            using assms(3) not_cong_4321 by blast
          thus ?thesis using Q1 Q2 l5_6 by blast
        qed
        have "C B Le C A"
          by (simp add: assms(4) le_comm)
        then have "Cong C A C B"
          by (simp add: W15 le_anti_symmetry)
        then have "Cong C' A' C' B'"
          by (metis Cong_perm assms(2) assms(3) cong_inner_transitivity)
        then have "False"
          using W14 cong__nlt by blast
        then have "Cong B A B' A'" by simp
      }
      then  have "Cong B A B' A'"
        using Z10 \<open>Bet B' A'' A' \<Longrightarrow> Cong B A B' A'\<close> by blast
    }
    {
      assume "A'' = A'"
      then have "Cong B A B' A'"
        using Z2 not_cong_3412 by blast
    }
    thus ?thesis
      using \<open>A'' \<noteq> A' \<Longrightarrow> Cong B A B' A'\<close> by blast
  qed
  have P6: "A B C Cong3 A' B' C'"
    using Cong3_def Cong_perm P5 assms(2) assms(3) by blast
  thus ?thesis
    using P2 P5 assms(1) assms(3) assms(4) l11_49 le_zero by blast
qed

lemma l11_53:
  assumes "Per D C B" and
    "C \<noteq> D" and
    "A \<noteq> B" and
    "B \<noteq> C" and
    "Bet A B C"
  shows "C A D LtA C B D \<and> B D Lt A D"
proof -
  have P1: "C \<noteq> A"
    using assms(3) assms(5) between_identity by blast
  have P2: "\<not> Col B A D"
    by (smt assms(1) assms(2) assms(3) assms(4) assms(5) bet_col bet_col1 col3 col_permutation_4 l8_9)
  have P3: "A \<noteq> D"
    using P2 col_trivial_2 by blast
  have P4: "C A D LtA C B D"
  proof -
    have P4A: "B D A LtA D B C \<and> B A D LtA D B C"
      by (simp add: P2 assms(4) assms(5) l11_41)
    have P4AA:"A Out B C"
      using assms(3) assms(5) bet_out by auto
    have "A Out D D"
      using P3 out_trivial by auto
    then have P4B: "C A D CongA B A D" using P4AA
      by (simp add: out2__conga)
    then have P4C: "B A D CongA C A D"
      by (simp add: P4B conga_sym)
    have "D B C CongA C B D"
      using assms(1) assms(4) conga_pseudo_refl per_distinct_1 by auto
    thus ?thesis
      using P4A P4C conga_preserves_lta by blast
  qed
  obtain B' where P5: "C Midpoint B B' \<and> Cong D B D B'"
    using Per_def assms(1) by auto
  have K2: "A \<noteq> B'"
    using Bet_cases P5 assms(4) assms(5) between_equality_2 midpoint_bet by blast
  {
    assume "Col B D B'"
    then have "Col B A D"
      by (metis Col_cases P5 assms(1) assms(2) assms(4) col2__eq midpoint_col midpoint_distinct_2 per_not_col)
    then have "False"
      by (simp add: P2)
  }
  then have P6: "\<not> Col B D B'" by blast
  then have "D B B' CongA D B' B \<longleftrightarrow> Cong D B D B'"
    by (simp add: l11_44_1)
  then have "D B B' CongA D B' B" using P5 by simp
  {
    assume K1: "Col A D B'"
    have "Col B' A B"
      using Col_def P5 assms(4) assms(5) midpoint_bet outer_transitivity_between by blast
    then have "Col B' B D"
      using K1 K2 Col_perm col_transitivity_2 by blast
    then have "Col B D B'"
      using Col_perm by blast
    then have "False"
      by (simp add: P6)
  }
  then have K3B: "\<not> Col A D B'" by blast
  then have K4: "D A B' LtA D B' A \<longleftrightarrow> D B' Lt D A"
    by (simp add: l11_44_2)
  have K4A: "C A D LtA C B' D"
    by (metis Midpoint_def P1 P3 P4 P5 P5 P6 assms(2) assms(4) col_trivial_1 cong_reflexivity conga_preserves_lta conga_refl l11_51 not_cong_2134)
  have "D B' Lt D A"
  proof -
    have "D A B' LtA D B' A"
    proof -
      have K5A: "A Out D D"
        using P3 out_trivial by auto
      have K5AA: "A Out B' C"
        by (smt K2 Out_def P1 P5 assms(4) assms(5) midpoint_bet outer_transitivity_between2)
      then have K5: "D A C CongA D A B'"
        by (simp add: K5A out2__conga)
      have K6A: "B' Out D D"
        using K3B not_col_distincts out_trivial by blast
      have "B' Out A C"
        by (smt P5 K5AA assms(4) assms(5) between_equality_2 l6_4_2 midpoint_bet midpoint_distinct_2 out_col outer_transitivity_between2)
      then have K6: "D B' C CongA D B' A"
        by (simp add: K6A out2__conga)
      have "D A C LtA D B' C"
        by (simp add: K4A lta_comm)
      thus ?thesis
        using K5 K6 conga_preserves_lta by auto
    qed
    thus ?thesis
      by (simp add: K4)
  qed
  thus ?thesis
    using P4 P5 cong2_lt__lt cong_pseudo_reflexivity not_cong_4312 by blast
qed

lemma cong2_conga_obtuse__cong_conga2:
  assumes "Obtuse A B C" and
    "A B C CongA A' B' C'" and
    "Cong A C A' C'" and
    "Cong B C B' C'"
  shows "Cong B A B' A' \<and> B A C CongA B' A' C' \<and>
B C A CongA B' C' A'"
proof -
  have "B C Le A C"
  proof cases
    assume "Col A B C"
    thus ?thesis
      by (simp add: assms(1) col_obtuse__bet l5_12_a)
  next
    assume "\<not> Col A B C"
    thus ?thesis
      using l11_46 assms(1) lt__le not_col_distincts by auto
  qed
  thus ?thesis
    using l11_52 assms(2) assms(3) assms(4) by blast
qed

lemma cong2_per2__cong_conga2:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per A B C" and
    "Per A' B' C'" and
    "Cong A C A' C'" and
    "Cong B C B' C'"
  shows "Cong B A B' A' \<and> B A C CongA B' A' C' \<and>
B C A CongA B' C' A'"
proof -
  have P1: "B C Le A C \<and> \<not> Cong B C A C"
    using assms(1) assms(2) assms(3) cong__nlt l11_46 lt__le by blast
  then have "A B C CongA A' B' C'"
    using assms(2) assms(3) assms(4) assms(5) assms(6) cong_diff cong_inner_transitivity cong_symmetry l11_16 by blast
  thus ?thesis
    using P1 assms(5) assms(6) l11_52 by blast
qed

lemma cong2_per2__cong:
  assumes "Per A B C" and
    "Per A' B' C'" and
    "Cong A C A' C'" and
    "Cong B C B' C'"
  shows "Cong B A B' A'"
proof cases
  assume "B = C"
  thus ?thesis
    using assms(3) assms(4) cong_reverse_identity not_cong_2143 by blast
next
  assume "B \<noteq> C"
  show ?thesis
  proof cases
    assume "A = B"
    thus ?thesis
    proof -
      have "Cong A C B' C'"
        using \<open>A = B\<close> assms(4) by blast
      then have "B' = A'"
        by (meson Cong3_def Per_perm assms(2) assms(3) cong_inner_transitivity cong_pseudo_reflexivity l8_10 l8_7)
      thus ?thesis
        using \<open>A = B\<close> cong_trivial_identity by blast
    qed
  next
    assume "A \<noteq> B"
    show ?thesis
    proof cases
      assume "A' = B'"
      thus ?thesis
        by (metis Cong3_def Per_perm \<open>A \<noteq> B\<close> assms(1) assms(3) assms(4) cong_inner_transitivity cong_pseudo_reflexivity l8_10 l8_7)
    next
      assume "A' \<noteq> B'"
      thus ?thesis
        using cong2_per2__cong_conga2 \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> assms(1) assms(2) assms(3) assms(4) by blast
    qed
  qed
qed

lemma cong2_per2__cong_3:
  assumes "Per A B C"
    "Per A' B' C'" and
    "Cong A C A' C'" and
    "Cong B C B' C'"
  shows "A B C Cong3 A' B' C'"
  by (metis Tarski_neutral_dimensionless.Cong3_def Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) cong2_per2__cong cong_3_swap)

lemma cong_lt_per2__lt:
  assumes "Per A B C" and
    "Per A' B' C'" and
    "Cong A B A' B'" and
    "B C Lt B' C'"
  shows "A C Lt A' C'"
proof cases
  assume "A = B"
  thus ?thesis
    using assms(3) assms(4) cong_reverse_identity by blast
next
  assume "A \<noteq> B"
  show ?thesis
  proof cases
    assume "B = C"
    thus ?thesis
      by (smt assms(2) assms(3) assms(4) cong2_lt__lt cong_4312 cong_diff cong_reflexivity l11_46 lt_diff)
  next
    assume P0: "B \<noteq> C"
    have "B C Lt B' C'"
      by (simp add: assms(4))
    then have R1: "B C Le B' C' \<and> \<not> Cong B C B' C'"
      by (simp add: Lt_def)
    then obtain C0 where P1: "Bet B' C0 C' \<and> Cong B C B' C0"
      using Le_def by auto
    then have P2: "Per A' B' C0"
      by (metis Col_def Per_cases assms(2) bet_out_1 col_col_per_per col_trivial_1 l8_5 out_diff2)
    have "C0 A' Lt C' A'" using l11_53
      by (metis P1 P2 R1 P0 bet__lt2313 between_symmetry cong_diff)
    then have P3: "A' C0 Lt A' C'"
      using Lt_cases by blast
    have P4: "Cong A' C0 A C"
      using P1 P2 assms(1) assms(3) l10_12 not_cong_3412 by blast
    have "Cong A' C' A' C'"
      by (simp add: cong_reflexivity)
    thus ?thesis
      using cong2_lt__lt P3 P4 by blast
  qed
qed

lemma cong_le_per2__le:
  assumes "Per A B C" and
    "Per A' B' C'" and
    "Cong A B A' B'" and
    "B C Le B' C'"
  shows "A C Le A' C'"
proof cases
  assume "Cong B C B' C'"
  thus ?thesis
    using assms(1) assms(2) assms(3) cong__le l10_12 by blast
next
  assume "\<not> Cong B C B' C'"
  then have "B C Lt B' C'"
    using Lt_def assms(4) by blast
  thus ?thesis
    using assms(1) assms(2) assms(3) cong_lt_per2__lt lt__le by auto
qed

lemma lt2_per2__lt:
  assumes "Per A B C" and
    "Per A' B' C'" and
    "A B Lt A' B'" and
    "B C Lt B' C'"
  shows "A C Lt A' C'"
proof -
  have P2: "B A Lt B' A'"
    by (simp add: assms(3) lt_comm)
  have P3: "B C Le B' C' \<and> \<not> Cong B C B' C'"
    using assms(4) cong__nlt lt__le by auto
  then obtain C0 where P4: "Bet B' C0 C' \<and> Cong B C B' C0"
    using Le_def by auto
  have P4A: "B' \<noteq> C'"
    using assms(4) lt_diff by auto
  have "Col B' C' C0"
    using P4 bet_col not_col_permutation_5 by blast
  then have P5: "Per A' B' C0"
    using assms(2) P4A per_col by blast
  have P6: "A C Lt A' C0"
    by (meson P2 P4 P5 assms(1) cong_lt_per2__lt l8_2 lt_comm not_cong_2143)
  have "B' C0 Lt B' C'"
    by (metis P4 assms(4) bet__lt1213 cong__nlt)
  then have "A' C0 Lt A' C'"
    using P5 assms(2) cong_lt_per2__lt cong_reflexivity by blast
  thus ?thesis
    using P6 lt_transitivity by blast
qed

lemma le_lt_per2__lt:
  assumes "Per A B C" and
    "Per A' B' C'" and
    "A B Le A' B'" and
    "B C Lt B' C'"
  shows "A C Lt A' C'"
  using Lt_def assms(1) assms(2) assms(3) assms(4) cong_lt_per2__lt lt2_per2__lt by blast

lemma le2_per2__le:
  assumes "Per A B C" and
    "Per A' B' C'" and
    "A B Le A' B'" and
    "B C Le B' C'"
  shows "A C Le A' C'"
proof cases
  assume "Cong B C B' C'"
  thus ?thesis
    by (meson Per_cases Tarski_neutral_dimensionless.cong_le_per2__le Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) le_comm not_cong_2143)
next
  assume "\<not> Cong B C B' C'"
  then have "B C Lt B' C'"
    by (simp add: Lt_def assms(4))
  thus ?thesis
    using assms(1) assms(2) assms(3) le_lt_per2__lt lt__le by blast
qed

lemma cong_lt_per2__lt_1:
  assumes "Per A B C" and
    "Per A' B' C'" and
    "A B Lt A' B'" and
    "Cong A C A' C'"
  shows "B' C' Lt B C"
  by (meson Gt_def assms(1) assms(2) assms(3) assms(4) cong2_per2__cong cong_4321 cong__nlt cong_symmetry lt2_per2__lt or_lt_cong_gt)

lemma symmetry_preserves_conga:
  assumes "A \<noteq> B" and "C \<noteq> B" and
    "M Midpoint A A'" and
    "M Midpoint B B'" and
    "M Midpoint C C'"
  shows "A B C CongA A' B' C'"
  by (metis Mid_perm assms(1) assms(2) assms(3) assms(4) assms(5) conga_trivial_1 l11_51 l7_13 symmetric_point_uniqueness)

lemma l11_57:
  assumes "A A' OS B B'" and
    "Per B A A'" and
    "Per B' A' A" and
    "A A' OS C C'" and
    "Per C A A'" and
    "Per C' A' A"
  shows "B A C CongA B' A' C'"
proof -
  obtain M where P1: "M Midpoint A A'"
    using midpoint_existence by auto
  obtain B'' where P2: "M Midpoint B B''"
    using symmetric_point_construction by auto
  obtain C'' where P3: "M Midpoint C C''"
    using symmetric_point_construction by auto
  have P4: "\<not> Col A A' B"
    using assms(1) col123__nos by auto
  have P5: "\<not> Col A A' C"
    using assms(4) col123__nos by auto
  have P6: "B A C CongA B'' A' C''"
    by (metis P1 P2 P3 assms(1) assms(4) os_distincts symmetry_preserves_conga)
  have "B'' A' C'' CongA B' A' C'"
  proof -
    have "B \<noteq> M"
      using P1 P4 midpoint_col not_col_permutation_2 by blast
    then have P7: "\<not> Col B'' A A'"
      using Mid_cases P1 P2 P4 mid_preserves_col not_col_permutation_3 by blast
    have K3: "Bet B'' A' B'"
    proof -
      have "Per B'' A' A"
        using P1 P2 assms(2) per_mid_per by blast
      have "Col B B'' M \<and> Col A A' M"
        using P1 P2 midpoint_col not_col_permutation_2 by blast
      then have "Coplanar B A A' B''"
        using Coplanar_def by auto
      then have "Coplanar A B' B'' A'"
        by (meson assms(1) between_trivial2 coplanar_trans_1 ncoplanar_perm_4 ncoplanar_perm_8 one_side_chara os__coplanar)
      then have P8: "Col B' B'' A'"
        using cop_per2__col P1 P2 P7 assms(2) assms(3) not_col_distincts per_mid_per by blast
      have "A A' TS B B''"
        using P1 P2 P4 mid_two_sides by auto
      then have "A' A TS B'' B'"
        using assms(1) invert_two_sides l9_2 l9_8_2 by blast
      thus ?thesis
        using Col_cases P8 col_two_sides_bet by blast
    qed
    have "\<not> Col C'' A A'"
      by (smt Col_def P1 P3 P5 l7_15 l7_2 not_col_permutation_5)
    have "Bet C'' A' C'"
    proof -
      have Z2: "Col C' C'' A'"
      proof -
        have "Col C C'' M \<and> Col A A' M"
          using P1 P3 col_permutation_1 midpoint_col by blast
        then have "Coplanar C A A' C''"
          using Coplanar_def by blast
        then have Z1: "Coplanar A C' C'' A'"
          by (meson assms(4) between_trivial2 coplanar_trans_1 ncoplanar_perm_4 ncoplanar_perm_8 one_side_chara os__coplanar)
        have "Per C'' A' A"
          using P1 P3 assms(5) per_mid_per by blast
        thus ?thesis
          using Z1 P5 assms(6) col_trivial_1 cop_per2__col by blast
      qed
      have "A A' TS C C''"
        using P1 P3 P5 mid_two_sides by auto
      then have "A' A TS C'' C'"
        using assms(4) invert_two_sides l9_2 l9_8_2 by blast
      thus ?thesis
        using Col_cases Z2 col_two_sides_bet by blast
    qed
    thus ?thesis
      by (metis P6 K3 assms(1) assms(4) conga_diff45 conga_diff56 l11_14 os_distincts)
  qed
  thus ?thesis
    using P6 conga_trans by blast
qed

lemma cop3_orth_at__orth_at:
  assumes "\<not> Col D E F" and
    "Coplanar A B C D" and
    "Coplanar A B C E" and
    "Coplanar A B C F" and
    "X OrthAt A B C U V"
  shows "X OrthAt D E F U V"
proof -
  have P1: "\<not> Col A B C \<and> Coplanar A B C X"
    using OrthAt_def assms(5) by blast
  then have P2: "Coplanar D E F X"
    using assms(2) assms(3) assms(4) coplanar_pseudo_trans by blast
  {
    fix M
    assume "Coplanar A B C M"
    then have "Coplanar D E F M"
      using P1 assms(2) assms(3) assms(4) coplanar_pseudo_trans by blast
  }
  have T1: "U \<noteq> V"
    using OrthAt_def assms(5) by blast
  have T2: "Col U V X"
    using OrthAt_def assms(5) by auto
  {
    fix P Q
    assume P7: "Coplanar D E F P \<and> Col U V Q"
    then have "Coplanar A B C P"
      by (meson \<open>\<And>M. Coplanar A B C M \<Longrightarrow> Coplanar D E F M\<close> assms(1) assms(2) assms(3) assms(4) l9_30)
    then have "Per P X Q" using P7 OrthAt_def assms(5) by blast
  }
  thus ?thesis using assms(1)
    by (simp add: OrthAt_def P2 T1 T2)
qed

lemma col2_orth_at__orth_at:
  assumes "U \<noteq> V" and
    "Col P Q U" and
    "Col P Q V" and
    "X OrthAt A B C P Q"
  shows "X OrthAt A B C U V"
proof -
  have "Col P Q X"
    using OrthAt_def assms(4) by auto
  then have "Col U V X"
    by (metis OrthAt_def assms(2) assms(3) assms(4) col3)
  thus ?thesis
    using OrthAt_def assms(1) assms(2) assms(3) assms(4) colx by presburger
qed

lemma col_orth_at__orth_at:
  assumes "U \<noteq> W" and
    "Col U V W" and
    "X OrthAt A B C U V"
  shows "X OrthAt A B C U W"
  using assms(1) assms(2) assms(3) col2_orth_at__orth_at col_trivial_3 by blast

lemma orth_at_symmetry:
  assumes "X OrthAt A B C U V"
  shows "X OrthAt A B C V U"
  by (metis assms col2_orth_at__orth_at col_trivial_2 col_trivial_3)

lemma orth_at_distincts:
  assumes "X OrthAt A B C U V"
  shows "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> U \<noteq> V"
  using OrthAt_def assms not_col_distincts by fastforce

lemma orth_at_chara:
  "X OrthAt A B C X P \<longleftrightarrow>
  (\<not> Col A B C \<and> X \<noteq> P \<and> Coplanar A B C X \<and> (\<forall> D.(Coplanar A B C D \<longrightarrow> Per D X P)))"
proof -
  {
    assume "X OrthAt A B C X P"
    then have "\<not> Col A B C \<and> X \<noteq> P \<and> Coplanar A B C X \<and> (\<forall> D.(Coplanar A B C D \<longrightarrow> Per D X P))"
      using OrthAt_def col_trivial_2 by auto
  }
  {
    assume T1: "\<not> Col A B C \<and> X \<noteq> P \<and> Coplanar A B C X \<and> (\<forall> D.(Coplanar A B C D \<longrightarrow> Per D X P))"
    {
      fix P0 Q
      assume "Coplanar A B C P0 \<and> Col X P Q"
      then have "Per P0 X Q" using T1 OrthAt_def per_col by auto
    }
    then have "X OrthAt A B C X P"
      by (simp add: T1 \<open>\<And>Q P0. Coplanar A B C P0 \<and> Col X P Q \<Longrightarrow> Per P0 X Q\<close> Tarski_neutral_dimensionless.OrthAt_def Tarski_neutral_dimensionless_axioms col_trivial_3)
  }
  thus ?thesis
    using \<open>X OrthAt A B C X P \<Longrightarrow> \<not> Col A B C \<and> X \<noteq> P \<and> Coplanar A B C X \<and> (\<forall>D. Coplanar A B C D \<longrightarrow> Per D X P)\<close> by blast
qed

lemma cop3_orth__orth:
  assumes "\<not> Col D E F" and
    "Coplanar A B C D" and
    "Coplanar A B C E" and
    "Coplanar A B C F" and
    "A B C Orth U V"
  shows "D E F Orth U V"
  using Orth_def assms(1) assms(2) assms(3) assms(4) assms(5) cop3_orth_at__orth_at by blast

lemma col2_orth__orth:
  assumes "U \<noteq> V" and
    "Col P Q U" and
    "Col P Q V" and
    "A B C Orth P Q"
  shows "A B C Orth U V"
  by (meson Orth_def Tarski_neutral_dimensionless.col2_orth_at__orth_at Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4))

lemma col_orth__orth:
  assumes "U \<noteq> W" and
    "Col U V W" and
    "A B C Orth U V"
  shows "A B C Orth U W"
  by (meson assms(1) assms(2) assms(3) col2_orth__orth col_trivial_3)

lemma orth_symmetry:
  assumes "A B C Orth U V"
  shows "A B C Orth V U"
  by (meson Orth_def assms orth_at_symmetry)

lemma orth_distincts:
  assumes "A B C Orth U V"
  shows "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> U \<noteq> V"
  using Orth_def assms orth_at_distincts by blast

lemma col_cop_orth__orth_at:
  assumes "A B C Orth U V" and
    "Coplanar A B C X" and
    "Col U V X"
  shows "X OrthAt A B C U V"
proof -
  obtain Y where P1:
    "\<not> Col A B C \<and> U \<noteq> V \<and> Coplanar A B C Y \<and> Col U V Y \<and>
(\<forall> P Q. (Coplanar A B C P \<and> Col U V Q) \<longrightarrow> Per P Y Q)"
    by (metis OrthAt_def Tarski_neutral_dimensionless.Orth_def Tarski_neutral_dimensionless_axioms assms(1))
  then have P2: "X = Y"
    using assms(2) assms(3) per_distinct_1 by blast
  {
    fix P Q
    assume "Coplanar A B C P \<and> Col U V Q"
    then have "Per P X Q" using P1 P2 by auto
  }
  thus ?thesis
    using OrthAt_def Orth_def assms(1) assms(2) assms(3) by auto
qed

lemma l11_60_aux:
  assumes "\<not> Col A B C" and
    "Cong A P A Q" and
    "Cong B P B Q" and
    "Cong C P C Q" and
    "Coplanar A B C D"
  shows "Cong D P D Q"
proof -
  obtain M where P1: "Bet P M Q \<and> Cong P M M Q"
    by (meson Midpoint_def Tarski_neutral_dimensionless.midpoint_existence Tarski_neutral_dimensionless_axioms)
  obtain X where P2: " (Col A B X \<and> Col C D X) \<or>
            (Col A C X \<and> Col B D X) \<or>
            (Col A D X \<and> Col B C X)"
    using assms(5) Coplanar_def by auto
  {
    assume "Col A B X \<and> Col C D X"
    then have "Cong D P D Q"
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) l4_17 not_col_distincts not_col_permutation_5)
  }
  {
    assume "Col A C X \<and> Col B D X"
    then have "Cong D P D Q"
      by (metis (no_types, lifting) assms(1) assms(2) assms(3) assms(4) l4_17 not_col_distincts not_col_permutation_5)
  }
  {
    assume "Col A D X \<and> Col B C X"
    then have "Cong D P D Q"
      by (smt assms(1) assms(2) assms(3) assms(4) l4_17 not_col_distincts not_col_permutation_1)
  }
  thus ?thesis
    using P2 \<open>Col A B X \<and> Col C D X \<Longrightarrow> Cong D P D Q\<close> \<open>Col A C X \<and> Col B D X \<Longrightarrow> Cong D P D Q\<close> by blast
qed

lemma l11_60:
  assumes "\<not> Col A B C" and
    "Per A D P" and
    "Per B D P" and
    "Per C D P" and
    "Coplanar A B C E"
  shows "Per E D P"
  by (meson Per_def assms(1) assms(2) assms(3) assms(4) assms(5) l11_60_aux per_double_cong)

lemma l11_60_bis:
  assumes "\<not> Col A B C" and
    "D \<noteq> P" and
    "Coplanar A B C D" and
    "Per A D P" and
    "Per B D P" and
    "Per C D P"
  shows "D OrthAt A B C D P"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l11_60 orth_at_chara by auto

lemma l11_61:
  assumes "A \<noteq> A'" and
    "A \<noteq> B" and
    "A \<noteq> C" and
    "Coplanar A A' B B'" and
    "Per B A A'" and
    "Per B' A' A" and
    "Coplanar A A' C C'" and
    "Per C A A'" and
    "Per B A C"
  shows "Per B' A' C'"
proof -
  have P1: "\<not> Col C A A'"
    using assms(1) assms(3) assms(8) per_col_eq by blast
  obtain C'' where P2: "A A' Perp C'' A' \<and> A A' OS C C''" using l10_15
    using Col_perm P1 col_trivial_2 by blast
  have P6: "B' \<noteq> A"
    using assms(1) assms(6) per_distinct by blast
  have P8: "\<not> Col A' A C''"
    using P2 not_col_permutation_4 one_side_not_col124 by blast
  have P9: "Per A' A' B'"
    by (simp add: l8_2 l8_5)
  have P10: "Per A A' B'"
    by (simp add: assms(6) l8_2)
  {
    fix B'
    assume "A A' OS B B' \<and> Per B' A' A"
    then have "B A C CongA B' A' C''" using l11_17
      by (meson P2 Perp_cases Tarski_neutral_dimensionless.l11_57 Tarski_neutral_dimensionless_axioms assms(5) assms(8) perp_per_1)
    then have "Per B' A' C''"
      using assms(9) l11_17 by blast
  }
  then have Q1: "\<forall> B'. (A A' OS B B' \<and> Per B' A' A) \<longrightarrow> Per B' A' C''" by simp
  {
    fix B'
    assume P12: "Coplanar A A' B B' \<and> Per B' A' A \<and> B' \<noteq> A"
    have "Per B' A' C''"
    proof cases
      assume "B' = A'"
      thus ?thesis
        by (simp add: Per_perm l8_5)
    next
      assume P13: "B' \<noteq> A'"
      have P14: "\<not> Col B' A' A"
        using P12 P13 assms(1) l8_9 by auto
      have P15: "\<not> Col B A A'"
        using assms(1) assms(2) assms(5) per_not_col by auto
      then have Z1: "A A' TS B B' \<or> A A' OS B B'"
        using P12 P14 cop__one_or_two_sides not_col_permutation_5 by blast
      {
        assume "A A' OS B B'"
        then have "Per B' A' C''"
          by (simp add: P12 \<open>\<And>B'a. A A' OS B B'a \<and> Per B'a A' A \<Longrightarrow> Per B'a A' C''\<close>)
      }
      {
        assume Q2: "A A' TS B B'"
        obtain B'' where Z2: "Bet B' A' B'' \<and> Cong A' B'' A' B'"
          using segment_construction by blast
        have "B' \<noteq> B''"
          using P13 Z2 bet_neq12__neq by blast
        then have Z4: "A' \<noteq> B''"
          using Z2 cong_diff_4 by blast
        then have "A A' TS B'' B'"
          by (meson TS_def Z2 Q2 bet__ts invert_two_sides l9_2 not_col_permutation_1)
        then have Z5: "A A' OS B B''"
          using Q2 l9_8_1 by auto
        have "Per B'' A' A"
          using P12 P13 Z2 bet_col col_per2__per l8_2 l8_5 by blast
        then have "Per C'' A' B''"
          using l8_2 Q1 Z5 by blast
        then have "Per B' A' C''"
          by (metis Col_def Per_perm Tarski_neutral_dimensionless.l8_3 Tarski_neutral_dimensionless_axioms Z2 Z4)
      }
      thus ?thesis using Z1
        using \<open>A A' OS B B' \<Longrightarrow> Per B' A' C''\<close> by blast
    qed
  }
  then have "\<forall> B'. (Coplanar A A' B B' \<and> Per B' A' A \<and> B' \<noteq> A) \<longrightarrow> Per B' A' C''"
    by simp
  then have "Per B' A' C''"
    using P6 assms(4) assms(6) by blast
  then have P11: "Per C'' A' B'"
    using Per_cases by auto
  have "Coplanar A' A C'' C'"
    by (meson P1 P2 assms(7) coplanar_trans_1 ncoplanar_perm_6 ncoplanar_perm_8 os__coplanar)
  thus ?thesis
    using P8 P9 P10 P11 l8_2 l11_60 by blast
qed

lemma l11_61_bis:
  assumes "D OrthAt A B C D P" and
    "D E Perp E Q" and
    "Coplanar A B C E" and
    "Coplanar D E P Q"
  shows "E OrthAt A B C E Q"
proof -
  have P4: "D \<noteq> E"
    using assms(2) perp_not_eq_1 by auto
  have P5: "E \<noteq> Q"
    using assms(2) perp_not_eq_2 by auto
  have "\<exists> D'. (D E Perp D' D \<and> Coplanar A B C D')"
  proof -
    obtain F where T1: "Coplanar A B C F \<and> \<not> Col D E F"
      using P4 ex_ncol_cop by blast
    obtain D' where T2: "D E Perp D' D \<and> Coplanar D E F D'"
      using P4 ex_perp_cop by blast
    have "Coplanar A B C D'"
    proof -
      have T3A: "\<not> Col A B C"
        using OrthAt_def assms(1) by auto
      have T3B: "Coplanar A B C D"
        using OrthAt_def assms(1) by blast
      then have T4: "Coplanar D E F A"
        by (meson T1 T3A assms(3) coplanar_pseudo_trans ncop_distincts)
      have T5: "Coplanar D E F B"
        using T1 T3A T3B assms(3) coplanar_pseudo_trans ncop_distincts by blast
      have "Coplanar D E F C"
        using T1 T3A T3B assms(3) coplanar_pseudo_trans ncop_distincts by blast
      thus ?thesis
        using T1 T2 T4 T5 coplanar_pseudo_trans by blast
    qed
    thus ?thesis
      using T2 by auto
  qed
  then obtain D' where R1: "D E Perp D' D \<and> Coplanar A B C D'" by auto
  then have R2: "D \<noteq> D'"
    using perp_not_eq_2 by blast
  {
    fix M
    assume R3: "Coplanar A B C M"
    have "Col D P P"
      by (simp add: col_trivial_2)
    then have "Per E D P"
      using assms(1) assms(3) orth_at_chara by auto
    then have R4: "Per P D E" using l8_2 by auto
    have R5: "Per Q E D"
      using Perp_cases assms(2) perp_per_2 by blast
    have R6: "Coplanar D E D' M"
    proof -
      have S1: "\<not> Col A B C"
        using OrthAt_def assms(1) by auto
      have "Coplanar A B C D"
        using OrthAt_def assms(1) by auto
      thus ?thesis
        using S1 assms(3) R1 R3 coplanar_pseudo_trans by blast
    qed
    have R7: "Per D' D E"
      using Perp_cases R1 perp_per_1 by blast
    have "Per D' D P"
      using R1 assms(1) orth_at_chara by blast
    then have "Per P D D'"
      using Per_cases by blast
    then have "Per Q E M"
      using l11_61 R4 R5 R6 R7 OrthAt_def P4 R2 assms(1) assms(4) by blast
    then have "Per M E Q" using l8_2 by auto
  }
  {
    fix P0 Q0
    assume "Coplanar A B C P0 \<and> Col E Q Q0"
    then have "Per P0 E Q0"
      using P5 \<open>\<And>M. Coplanar A B C M \<Longrightarrow> Per M E Q\<close> per_col by blast
  }
  thus ?thesis
    using OrthAt_def P5 assms(1) assms(3) col_trivial_3 by auto
qed

lemma l11_62_unicity:
  assumes "Coplanar A B C D" and
    "Coplanar A B C D'" and
    "\<forall> E. Coplanar A B C E \<longrightarrow> Per E D P" and
    "\<forall> E. Coplanar A B C E \<longrightarrow> Per E D' P"
  shows "D = D'"
  by (metis assms(1) assms(2) assms(3) assms(4) l8_8 not_col_distincts per_not_colp)

lemma l11_62_unicity_bis:
  assumes "X OrthAt A B C X U" and
    "Y OrthAt A B C Y U"
  shows "X = Y"
proof -
  have P1: "Coplanar A B C X"
    using assms(1) orth_at_chara by blast
  have P2: "Coplanar A B C Y"
    using assms(2) orth_at_chara by blast
  {
    fix E
    assume "Coplanar A B C E"
    then have "Per E X U"
      using OrthAt_def assms(1) col_trivial_2 by auto
  }
  {
    fix E
    assume "Coplanar A B C E"
    then have "Per E Y U"
      using assms(2) orth_at_chara by auto
  }
  thus ?thesis
    by (meson P1 P2 \<open>\<And>E. Coplanar A B C E \<Longrightarrow> Per E X U\<close> l8_2 l8_7)
qed

lemma orth_at2__eq:
  assumes "X OrthAt A B C U V" and
    "Y OrthAt A B C U V"
  shows "X = Y"
proof -
  have P1: "Coplanar A B C X"
    using assms(1)
    by (simp add: OrthAt_def)
  have P2: "Coplanar A B C Y"
    using OrthAt_def assms(2) by auto
  {
    fix E
    assume "Coplanar A B C E"
    then have "Per E X U"
      using OrthAt_def assms(1) col_trivial_3 by auto
  }
  {
    fix E
    assume "Coplanar A B C E"
    then have "Per E Y U"
      using OrthAt_def assms(2) col_trivial_3 by auto
  }
  thus ?thesis
    by (meson P1 P2 Per_perm \<open>\<And>E. Coplanar A B C E \<Longrightarrow> Per E X U\<close> l8_7)
qed

lemma col_cop_orth_at__eq:
  assumes "X OrthAt A B C U V" and
    "Coplanar A B C Y" and
    "Col U V Y"
  shows "X = Y"
proof -
  have "Y OrthAt A B C U V"
    using Orth_def assms(1) assms(2) assms(3) col_cop_orth__orth_at by blast
  thus ?thesis
    using assms(1) orth_at2__eq by auto
qed

lemma orth_at__ncop1:
  assumes "U \<noteq> X" and
    "X OrthAt A B C U V"
  shows "\<not> Coplanar A B C U"
  using assms(1) assms(2) col_cop_orth_at__eq not_col_distincts by blast

lemma orth_at__ncop2:
  assumes "V \<noteq> X" and
    "X OrthAt A B C U V"
  shows "\<not> Coplanar A B C V"
  using assms(1) assms(2) col_cop_orth_at__eq not_col_distincts by blast

lemma orth_at__ncop:
  assumes "X OrthAt A B C X P"
  shows "\<not> Coplanar A B C P"
  by (metis assms orth_at__ncop2 orth_at_distincts)

lemma l11_62_existence:
  "\<exists> D. (Coplanar A B C D \<and> (\<forall> E. (Coplanar A B C E \<longrightarrow> Per E D P)))"
proof cases
  assume "Coplanar A B C P"
  thus ?thesis
    using l8_5 by auto
next
  assume P1: "\<not> Coplanar A B C P"
  then have P2: "\<not> Col A B C"
    using ncop__ncol by auto
  have "\<not> Col A B P"
    using P1 ncop__ncols by auto
  then obtain D0 where P4: "Col A B D0 \<and> A B Perp P D0" using l8_18_existence by blast
  have P5: "Coplanar A B C D0"
    using P4 ncop__ncols by auto
  have "A \<noteq> B"
    using P2 not_col_distincts by auto
  then obtain D1 where P10: "A B Perp D1 D0 \<and> Coplanar A B C D1"
    using ex_perp_cop by blast
  have P11: "\<not> Col A B D1"
    using P10 P4 perp_not_col2 by blast
  {
    fix D
    assume "Col D0 D1 D"
    then have "Coplanar A B C D"
      by (metis P10 P5 col_cop2__cop perp_not_eq_2)
  }
  obtain A0 where P11: "A \<noteq> A0 \<and> B \<noteq> A0 \<and> D0 \<noteq> A0 \<and> Col A B A0"
    using P4 diff_col_ex3 by blast
  have P12: "Coplanar A B C A0"
    using P11 ncop__ncols by blast
  have P13: "Per P D0 A0"
    using l8_16_1 P11 P4 by blast
  show ?thesis
  proof cases
    assume Z1: "Per P D0 D1"
    {
      fix E
      assume R1: "Coplanar A B C E"
      have R2: "\<not> Col A0 D1 D0"
        by (metis P10 P11 P4 col_permutation_5 colx perp_not_col2)
      have R3: "Per A0 D0 P"
        by (simp add: P13 l8_2)
      have R4: "Per D1 D0 P"
        by (simp add: Z1 l8_2)
      have R5: "Per D0 D0 P"
        by (simp add: l8_2 l8_5)
      have "Coplanar A0 D1 D0 E"
        using R1 P2 P12 P10 P5 coplanar_pseudo_trans by blast
      then have "Per E D0 P"
        using l11_60 R2 R3 R4 R5 by blast
    }
    thus ?thesis using P5 by auto
  next
    assume S1: "\<not> Per P D0 D1"
    {
      assume S2: "Col D0 D1 P"
      have "\<forall> D. Col D0 D1 D \<longrightarrow> Coplanar A B C D"
        by (simp add: \<open>\<And>Da. Col D0 D1 Da \<Longrightarrow> Coplanar A B C Da\<close>)
      then have "False"
        using P1 S2 by blast
    }
    then have S2A: "\<not> Col D0 D1 P" by blast
    then obtain D where S3: "Col D0 D1 D \<and> D0 D1 Perp P D"
      using l8_18_existence by blast
    have S4: "Coplanar A B C D"
      by (simp add: S3 \<open>\<And>Da. Col D0 D1 Da \<Longrightarrow> Coplanar A B C Da\<close>)
    {
      fix E
      assume S5: "Coplanar A B C E"
      have S6: "D \<noteq> D0"
        using S1 S3 l8_2 perp_per_1 by blast
      have S7: "Per D0 D P"
        by (metis Perp_cases S3 S6 perp_col perp_per_1)
      have S8: "Per D D0 A0"
      proof -
        have V4: "D0 \<noteq> D1"
          using P10 perp_not_eq_2 by blast
        have V6: "Per A0 D0 D1"
          using P10 P11 P4 l8_16_1 l8_2 by blast
        thus ?thesis
          using S3 V4 V6 l8_2 per_col by blast
      qed
      have S9: "Per A0 D P"
      proof -
        obtain A0' where W1: "D Midpoint A0 A0'"
          using symmetric_point_construction by auto
        obtain D0' where W2: "D Midpoint D0 D0'"
          using symmetric_point_construction by auto
        have "Cong P A0 P A0'"
        proof -
          have V3: "Cong P D0 P D0'"
            using S7 W2 l8_2 per_double_cong by blast
          have V4: "Cong D0 A0 D0' A0'"
            using W1 W2 cong_4321 l7_13 by blast
          have "Per P D0' A0'"
          proof -
            obtain P' where V5: "D Midpoint P P'"
              using symmetric_point_construction by blast
            have "Per P' D0 A0"
            proof -
              have "\<not> Col P D D0"
                by (metis S2A S3 S6 col2__eq col_permutation_1)
              thus ?thesis
                by (metis (full_types) P13 S3 S8 V5 S2A col_per2__per midpoint_col)
            qed
            thus ?thesis
              using midpoint_preserves_per V5 Mid_cases W1 W2 by blast
          qed
          thus ?thesis using l10_12 P13 V3 V4 by blast
        qed
        thus ?thesis
          using Per_def Per_perm W1 by blast
      qed
      have S13: "Per D D P"
        using Per_perm l8_5 by blast
      have S14: "\<not> Col D0 A0 D" using P11 S7 S9 per_not_col Col_perm S6 S8 by blast
      have "Coplanar A B C D" using S4 by auto
      then have "Coplanar D0 A0 D E"
        using P12 P2 P5 S5 coplanar_pseudo_trans by blast
      then have "Per E D P"
        using S13 S14 S7 S9 l11_60 by blast
    }
    thus ?thesis using S4 by blast
  qed
qed

lemma l11_62_existence_bis:
  assumes "\<not> Coplanar A B C P"
  shows "\<exists> X. X OrthAt A B C X P"
proof -
  obtain X where P1: "Coplanar A B C X \<and> (\<forall> E. Coplanar A B C E \<longrightarrow> Per E X P)"
    using l11_62_existence by blast
  then have P2: "X \<noteq> P"
    using assms by auto
  have P3: "\<not> Col A B C"
    using assms ncop__ncol by auto
  thus ?thesis
    using P1 P2 P3 orth_at_chara by auto
qed

lemma l11_63_aux:
  assumes "Coplanar A B C D" and
    "D \<noteq> E" and
    "E OrthAt A B C E P"
  shows "\<exists> Q. (D E OS P Q \<and> A B C Orth D Q)"
proof -
  have P1: "\<not> Col A B C"
    using OrthAt_def assms(3) by blast
  have P2: "E \<noteq> P"
    using OrthAt_def assms(3) by blast
  have P3: "Coplanar A B C E"
    using OrthAt_def assms(3) by blast
  have P4: "\<forall> P0 Q. (Coplanar A B C P0 \<and> Col E P Q) \<longrightarrow> Per P0 E Q"
    using OrthAt_def assms(3) by blast
  have P5: "\<not> Coplanar A B C P"
    using assms(3) orth_at__ncop by auto
  have P6: "Col D E D"
    by (simp add: col_trivial_3)
  have "\<not> Col D E P"
    using P3 P5 assms(1) assms(2) col_cop2__cop by blast
  then obtain Q where P6: "D E Perp Q D \<and> D E OS P Q"
    using P6 l10_15 by blast
  have "A B C Orth D Q"
  proof -
    obtain F where P7: "Coplanar A B C F \<and> \<not> Col D E F"
      using assms(2) ex_ncol_cop by blast
    obtain D' where P8: "D E Perp D' D \<and> Coplanar D E F D'"
      using assms(2) ex_perp_cop by presburger
    have P9: "\<not> Col D' D E"
      using P8 col_permutation_1 perp_not_col by blast
    have P10: "Coplanar D E F A"
      by (meson P1 P3 P7 assms(1) coplanar_pseudo_trans ncop_distincts)
    have P11: "Coplanar D E F B"
      by (meson P1 P3 P7 assms(1) coplanar_pseudo_trans ncop_distincts)
    have P12: "Coplanar D E F C"
      by (meson P1 P3 P7 assms(1) coplanar_pseudo_trans ncop_distincts)
    then have "D OrthAt A B C D Q"
    proof -
      have "Per D' D Q"
      proof -
        obtain E' where Y1: "D E Perp E' E \<and> Coplanar D E F E'"
          using assms(2) ex_perp_cop by blast
        have Y2: "E \<noteq> E'"
          using Y1 perp_distinct by auto
        have Y5: "Coplanar E D E' D'"
          by (meson P7 P8 Y1 coplanar_perm_12 coplanar_perm_7 coplanar_trans_1 not_col_permutation_2)
        have Y6: "Per E' E D"
          by (simp add: Perp_perm Tarski_neutral_dimensionless.perp_per_2 Tarski_neutral_dimensionless_axioms Y1)
        have Y7: "Per D' D E"
          using P8 col_trivial_2 col_trivial_3 l8_16_1 by blast
        have Y8: "Coplanar E D P Q"
          using P6 ncoplanar_perm_6 os__coplanar by blast
        have Y9: "Per P E D" using P4
          using assms(1) assms(3) l8_2 orth_at_chara by blast
        have Y10: "Coplanar A B C E'"
          using P10 P11 P12 P7 Y1 coplanar_pseudo_trans by blast
        then have Y11: "Per E' E P"
          using P4 Y10 col_trivial_2 by auto
        have "E \<noteq> D" using assms(2) by blast
        thus ?thesis
          using l11_61 Y2 assms(2) P2 Y5 Y6 Y7 Y8 Y9 Y10 Y11 by blast
      qed
      then have X1: "D OrthAt D' D E D Q" using l11_60_bis
        by (metis OS_def P6 P9 Per_perm TS_def Tarski_neutral_dimensionless.l8_5 Tarski_neutral_dimensionless_axioms col_trivial_3 invert_one_side ncop_distincts perp_per_1)
      have X3: "Coplanar D' D E A"
        using P10 P7 P8 coplanar_perm_14 coplanar_trans_1 not_col_permutation_3 by blast
      have X4: "Coplanar D' D E B"
        using P11 P7 P8 coplanar_perm_14 coplanar_trans_1 not_col_permutation_3 by blast
      have "Coplanar D' D E C"
        using P12 P7 P8 coplanar_perm_14 coplanar_trans_1 not_col_permutation_3 by blast
      thus ?thesis
        using X1 P1 X3 X4 cop3_orth_at__orth_at by blast
    qed
    thus ?thesis
      using Orth_def by blast
  qed
  thus ?thesis using P6 by blast
qed

lemma l11_63_existence:
  assumes "Coplanar A B C D" and
    "\<not> Coplanar A B C P"
  shows "\<exists> Q. A B C Orth D Q"
  using Orth_def assms(1) assms(2) l11_62_existence_bis l11_63_aux by fastforce

lemma l8_21_3:
  assumes "Coplanar A B C D" and
    "\<not> Coplanar A B C X"
  shows
    "\<exists> P T. (A B C Orth D P \<and> Coplanar A B C T \<and> Bet X T P)"
proof -
  obtain E where P1: "E OrthAt A B C E X"
    using assms(2) l11_62_existence_bis by blast
  thus ?thesis
  proof cases
    assume P2: "D = E"
    obtain Y where P3: "Bet X D Y \<and> Cong D Y D X"
      using segment_construction by blast
    have P4: "D \<noteq> X"
      using assms(1) assms(2) by auto
    have P5: "A B C Orth D X"
      using Orth_def P1 P2 by auto
    have P6: "D \<noteq> Y"
      using P3 P4 cong_reverse_identity by blast
    have "Col D X Y"
      using Col_def Col_perm P3 by blast
    then have "A B C Orth D Y"
      using P5 P6 col_orth__orth by auto
    thus ?thesis
      using P3 assms(1) by blast
  next
    assume K1: "D \<noteq> E"
    then obtain P' where P7: "D E OS X P' \<and> A B C Orth D P'"
      using P1 assms(1) l11_63_aux by blast
    have P8: "\<not> Col A B C"
      using assms(2) ncop__ncol by auto
    have P9: "E \<noteq> X"
      using P7 os_distincts by auto
    have P10: "\<forall> P Q. (Coplanar A B C P \<and> Col E X Q) \<longrightarrow> Per P E Q"
      using OrthAt_def P1 by auto
    have P11: "D OrthAt A B C D P'"
      by (simp add: P7 assms(1) col_cop_orth__orth_at col_trivial_3)
    have P12: "D \<noteq> P'"
      using P7 os_distincts by auto
    have P13: "\<not> Coplanar A B C P'"
      using P11 orth_at__ncop by auto
    have P14: "\<forall> P Q. (Coplanar A B C P \<and> Col D P' Q) \<longrightarrow> Per P D Q"
      using OrthAt_def P11 by auto
    obtain P where P15: "Bet P' D P \<and> Cong D P D P'"
      using segment_construction by blast
    have P16: "D E TS X P"
    proof -
      have P16A: "D E OS P' X" using P7 one_side_symmetry by blast
      then have "D E TS P' P"
        by (metis P12 P15 Tarski_neutral_dimensionless.bet__ts Tarski_neutral_dimensionless_axioms cong_diff_3 one_side_not_col123)
      thus ?thesis using l9_8_2 P16A by blast
    qed
    obtain T where P17: "Col T D E \<and> Bet X T P"
      using P16 TS_def by blast
    have P18: "D \<noteq> P"
      using P16 ts_distincts by blast
    have "Col D P' P"
      using Col_def Col_perm P15 by blast
    then have "A B C Orth D P"
      using P18 P7 col_orth__orth by blast
    thus ?thesis using col_cop2__cop
      by (meson P1 P17 Tarski_neutral_dimensionless.orth_at_chara Tarski_neutral_dimensionless_axioms K1 assms(1) col_permutation_1)
  qed
qed

lemma mid2_orth_at2__cong:
  assumes "X OrthAt A B C X P" and
    "Y OrthAt A B C Y Q" and
    "X Midpoint P P'" and
    "Y Midpoint Q Q'"
  shows "Cong P Q P' Q'"
proof -
  have Q1: "\<not> Col A B C"
    using assms(1) col__coplanar orth_at__ncop by blast
  have Q2: "X \<noteq> P"
    using assms(1) orth_at_distincts by auto
  have Q3: "Coplanar A B C X"
    using OrthAt_def assms(1) by auto
  have Q4: "\<forall> P0 Q. (Coplanar A B C P0 \<and> Col X P Q) \<longrightarrow> Per P0 X Q"
    using OrthAt_def assms(1) by blast
  have Q5: "Y \<noteq> P"
    by (metis assms(1) assms(2) orth_at__ncop2 orth_at_chara)
  have Q6: "Coplanar A B C Y"
    using OrthAt_def assms(2) by blast
  have Q7: "\<forall> P Q0. (Coplanar A B C P \<and> Col Y Q Q0) \<longrightarrow> Per P Y Q0"
    using OrthAt_def assms(2) by blast
  obtain Z where P1: "Z Midpoint X Y"
    using midpoint_existence by auto
  obtain R where P2: "Z Midpoint P R"
    using symmetric_point_construction by auto
  obtain R' where P3: "Z Midpoint P' R'"
    using symmetric_point_construction by auto
  have T1: "Coplanar A B C Z"
    using P1 Q3 Q6 bet_cop2__cop midpoint_bet by blast
  then have "Per Z X P"
    using Q4 assms(1) orth_at_chara by auto
  then have T2: "Cong Z P Z P'"
    using assms(3) per_double_cong by blast
  have T3: "Cong R Z R' Z"
    by (metis Cong_perm Midpoint_def P2 P3 T2 cong_transitivity)
  have T4: "Cong R Q R' Q'"
    by (meson P1 P2 P3 assms(3) assms(4) l7_13 not_cong_4321 symmetry_preserves_midpoint)
  have "Per Z Y Q"
    using Q7 T1 assms(2) orth_at_chara by auto
  then have T5: "Cong Z Q Z Q'"
    using assms(4) per_double_cong by auto
  have "R \<noteq> Z"
    by (metis P2 P3 Q2 T3 assms(3) cong_diff_3 l7_17_bis midpoint_not_midpoint)
  thus ?thesis
    using P2 P3 T2 T3 T4 T5 five_segment l7_2 midpoint_bet by blast
qed

lemma orth_at2_tsp__ts:
  assumes "P \<noteq> Q" and
    "P OrthAt A B C P X" and
    "Q OrthAt A B C Q Y" and
    "A B C TSP X Y"
  shows "P Q TS X Y"
proof -
  obtain T where P0: "Coplanar A B C T \<and> Bet X T Y"
    using TSP_def assms(4) by auto
  have P1: "\<not> Col A B C"
    using assms(4) ncop__ncol tsp__ncop1 by blast
  have P2: "P \<noteq> X "
    using assms(2) orth_at_distincts by auto
  have P3: "Coplanar A B C P"
    using OrthAt_def assms(2) by blast
  have P4: "\<forall> D. Coplanar A B C D \<longrightarrow> Per D P X"
    using assms(2) orth_at_chara by blast
  have P5: "Q \<noteq> Y"
    using assms(3) orth_at_distincts by auto
  have P6: "Coplanar A B C Q"
    using OrthAt_def assms(3) by blast
  have P7: "\<forall> D. Coplanar A B C D \<longrightarrow> Per D Q Y"
    using assms(3) orth_at_chara by blast
  have P8: "\<not> Col X P Q"
    using P3 P6 assms(1) assms(4) col_cop2__cop not_col_permutation_2 tsp__ncop1 by blast
  have P9: "\<not> Col Y P Q"
    using P3 P6 assms(1) assms(4) col_cop2__cop not_col_permutation_2 tsp__ncop2 by blast
  have "Col T P Q"
  proof -
    obtain X' where Q1: "P Midpoint X X'"
      using symmetric_point_construction by auto
    obtain Y' where Q2: "Q Midpoint Y Y'"
      using symmetric_point_construction by auto
    have "Per T P X"
      using P0 P4 by auto
    then have Q3: "Cong T X T X'"
      using Q1 per_double_cong by auto
    have "Per T Q Y"
      using P0 P7 by auto
    then have Q4: "Cong T Y T Y'" using Q2 per_double_cong by auto
    have "Cong X Y X' Y'"
      using P1 Q1 Q2 assms(2) assms(3) mid2_orth_at2__cong by blast
    then have "X T Y Cong3 X' T Y'"
      using Cong3_def Q3 Q4 not_cong_2143 by blast
    then have "Bet X' T Y'"
      using l4_6 P0 by blast
    thus ?thesis
      using Q1 Q2 Q3 Q4 Col_def P0 between_symmetry l7_22 by blast
  qed
  thus ?thesis
    using P0 P8 P9 TS_def by blast
qed

lemma orth_dec:
  shows "A B C Orth U V \<or> \<not> A B C Orth U V" by auto

lemma orth_at_dec:
  shows "X OrthAt A B C U V \<or> \<not> X OrthAt A B C U V" by auto

lemma tsp_dec:
  shows "A B C TSP X Y \<or> \<not> A B C TSP X Y" by auto

lemma osp_dec:
  shows "A B C OSP X Y \<or> \<not> A B C OSP X Y" by auto

lemma ts2__inangle:
  assumes "A C TS B P" and
    "B P TS A C"
  shows "P InAngle A B C"
  by (metis InAngle_def assms(1) assms(2) bet_out ts2__ex_bet2 ts_distincts)

lemma os_ts__inangle:
  assumes "B P TS A C" and
    "B A OS C P"
  shows "P InAngle A B C"
proof -
  have P1: "\<not> Col A B P"
    using TS_def assms(1) by auto
  have P2: "\<not> Col B A C"
    using assms(2) col123__nos by blast
  obtain P' where P3: "B Midpoint P P'"
    using symmetric_point_construction by blast
  then have P4: "\<not> Col B A P'"
    by (metis assms(2) col_one_side col_permutation_5 midpoint_col midpoint_distinct_2 one_side_not_col124)
  have P5: "(B \<noteq> P' \<and> B P TS A C \<and> Bet P B P') \<longrightarrow> (P InAngle A B C \<or> P' InAngle A B C)"
    using two_sides_in_angle by auto
  then have P6: "P InAngle A B C \<or> P' InAngle A B C"
    using P3 P4 assms(1) midpoint_bet not_col_distincts by blast
  {
    assume "P' InAngle A B C"
    then have P7: "A B OS P' C"
      using Col_cases P2 P4 in_angle_one_side by blast
    then have P8: "\<not> A B TS P' C"
      using l9_9 by auto
    have "B A TS P P'"
      using P1 P3 P4 bet__ts midpoint_bet not_col_distincts not_col_permutation_4 by auto
    then have "B A TS C P'"
      using P7 assms(2) invert_one_side l9_2 l9_8_2 l9_9 by blast
    then have "B A TS P' C"
      using l9_2 by blast
    then have "A B TS P' C"
      by (simp add: invert_two_sides)
    then have "P InAngle A B C"
      using P8 by auto
  }
  thus ?thesis
    using P6 by blast
qed

lemma os2__inangle:
  assumes "B A OS C P" and
    "B C OS A P"
  shows "P InAngle A B C"
  using assms(1) assms(2) col124__nos l9_9_bis os_ts__inangle two_sides_cases by blast

lemma acute_conga__acute:
  assumes "Acute A B C" and
    "A B C CongA D E F"
  shows "Acute D E F"
proof -
  have "D E F LeA A B C"
    by (simp add: assms(2) conga__lea456123)
  thus ?thesis
    using acute_lea_acute assms(1) by blast
qed

lemma acute_out2__acute:
  assumes "B Out A' A" and
    "B Out C' C" and
    "Acute A B C"
  shows "Acute A' B C'"
  by (meson Tarski_neutral_dimensionless.out2__conga Tarski_neutral_dimensionless_axioms acute_conga__acute assms(1) assms(2) assms(3))

lemma conga_obtuse__obtuse:
  assumes "Obtuse A B C" and
    "A B C CongA D E F"
  shows "Obtuse D E F"
  using assms(1) assms(2) conga__lea lea_obtuse_obtuse by blast

lemma obtuse_out2__obtuse:
  assumes "B Out A' A" and
    "B Out C' C" and
    "Obtuse A B C"
  shows "Obtuse A' B C'"
  by (meson Tarski_neutral_dimensionless.out2__conga Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) conga_obtuse__obtuse)

lemma bet_lea__bet:
  assumes "Bet A B C" and
    "A B C LeA D E F"
  shows "Bet D E F"
proof -
  have "A B C CongA D E F"
    by (metis assms(1) assms(2) l11_31_2 lea_asym lea_distincts)
  thus ?thesis
    using assms(1) bet_conga__bet by blast
qed

lemma out_lea__out:
  assumes "E Out D F" and
    "A B C LeA D E F"
  shows "B Out A C"
proof -
  have "D E F CongA A B C"
    using Tarski_neutral_dimensionless.l11_31_1 Tarski_neutral_dimensionless.lea_asym Tarski_neutral_dimensionless.lea_distincts Tarski_neutral_dimensionless_axioms assms(1) assms(2) by fastforce
  thus ?thesis
    using assms(1) out_conga_out by blast
qed

lemma bet2_lta__lta:
  assumes "A B C LtA D E F" and
    "Bet A B A'" and
    "A' \<noteq> B" and
    "Bet D E D'" and
    "D' \<noteq> E"
  shows "D' E F LtA A' B C"
proof -
  have P1: "D' E F LeA A' B C"
    by (metis Bet_cases assms(1) assms(2) assms(3) assms(4) assms(5) l11_36_aux2 lea_distincts lta__lea)
  have "\<not> D' E F CongA A' B C"
    by (metis assms(1) assms(2) assms(4) between_symmetry conga_sym l11_13 lta_distincts not_lta_and_conga)
  thus ?thesis
    by (simp add: LtA_def P1)
qed

lemma lea123456_lta__lta:
  assumes "A B C LeA D E F" and
    "D E F LtA G H I"
  shows "A B C LtA G H I"
proof -
  have "\<not> G H I LeA F E D"
    by (metis (no_types) Tarski_neutral_dimensionless.lea__nlta Tarski_neutral_dimensionless.lta_left_comm Tarski_neutral_dimensionless_axioms assms(2))
  then have "\<not> A B C CongA G H I"
    by (metis Tarski_neutral_dimensionless.lta_distincts Tarski_neutral_dimensionless_axioms assms(1) assms(2) conga_pseudo_refl l11_30)
  thus ?thesis
    by (meson LtA_def Tarski_neutral_dimensionless.lea_trans Tarski_neutral_dimensionless_axioms assms(1) assms(2))
qed

lemma lea456789_lta__lta:
  assumes "A B C LtA D E F" and
    "D E F LeA G H I"
  shows "A B C LtA G H I"
  by (meson LtA_def assms(1) assms(2) conga__lea456123 lea_trans lta__nlea)

lemma acute_per__lta:
  assumes "Acute A B C" and
    "D \<noteq> E" and
    "E \<noteq> F" and
    "Per D E F"
  shows "A B C LtA D E F"
proof -
  obtain G H I where P1: "Per G H I \<and> A B C LtA G H I"
    using Acute_def assms(1) by auto
  then have "G H I CongA D E F"
    using assms(2) assms(3) assms(4) l11_16 lta_distincts by blast
  thus ?thesis
    by (metis P1 conga_preserves_lta conga_refl lta_distincts)
qed

lemma obtuse_per__lta:
  assumes "Obtuse A B C" and
    "D \<noteq> E" and
    "E \<noteq> F" and
    "Per D E F"
  shows "D E F LtA A B C"
proof -
  obtain G H I where P1: "Per G H I \<and> G H I LtA A B C"
    using Obtuse_def assms(1) by auto
  then have "G H I CongA D E F"
    using assms(2) assms(3) assms(4) l11_16 lta_distincts by blast
  thus ?thesis
    by (metis P1 Tarski_neutral_dimensionless.l11_51 Tarski_neutral_dimensionless_axioms assms(1) cong_reflexivity conga_preserves_lta obtuse_distincts)
qed

lemma acute_obtuse__lta:
  assumes "Acute A B C" and
    "Obtuse D E F"
  shows "A B C LtA D E F"
  by (metis Acute_def assms(1) assms(2) lta_distincts lta_trans obtuse_per__lta)

lemma lea_in_angle:
  assumes "A B P LeA A B C" and
    "A B OS C P"
  shows "P InAngle A B C"
proof -
  obtain T where P3: "T InAngle A B C \<and> A B P CongA A B T"
    using LeA_def assms(1) by blast
  thus ?thesis
    by (metis assms(2) conga_preserves_in_angle conga_refl not_conga_sym one_side_symmetry os_distincts)
qed

lemma acute_bet__obtuse:
  assumes "Bet A B A'" and
    "A' \<noteq> B" and
    "Acute A B C"
  shows "Obtuse A' B C"
proof cases
  assume P1: "Col A B C"
  show ?thesis
  proof cases
    assume "Bet A B C"
    thus ?thesis
      using P1 acute_col__out assms(3) not_bet_and_out by blast
  next
    assume "\<not> Bet A B C"
    thus ?thesis
      by (smt P1 assms(1) assms(2) bet__obtuse between_inner_transitivity between_symmetry outer_transitivity_between third_point)
  qed
next
  assume P2: "\<not> Col A B C"
  then obtain D where P3: "A B Perp D B \<and> A B OS C D"
    using col_trivial_2 l10_15 by blast
  {
    assume P4: "Col C B D"
    then have "Per A B C"
    proof -
      have P5: "B \<noteq> D"
        using P3 perp_not_eq_2 by auto
      have "Per A B D"
        using P3 Perp_perm perp_per_2 by blast
      thus ?thesis
        using P4 P5 not_col_permutation_2 per_col by blast
    qed
    then have "A B C LtA A B C"
      by (metis Acute_def acute_per__lta assms(3) lta_distincts)
    then have "False"
      by (simp add: nlta)
  }
  then have P6: "\<not> Col C B D" by auto
  have P7: "B A' OS C D"
    by (metis P3 assms(1) assms(2) bet_col col2_os__os l5_3)
  have T1: "Per A B D"
    by (simp add: P3 perp_left_comm perp_per_1)
  have Q1: "B C TS A' A"
    using P2 assms(1) assms(2) bet__ts l9_2 not_col_permutation_1 by auto
  have "A B C LtA A B D"
    using P2 P6 T1 acute_per__lta assms(3) not_col_distincts by auto
  then have "A B C LeA A B D"
    by (simp add: lta__lea)
  then have "C InAngle A B D"
    by (simp add: P3 lea_in_angle one_side_symmetry)
  then have "C InAngle D B A"
    using l11_24 by blast
  then have "C B TS D A"
    by (simp add: P2 P6 in_angle_two_sides not_col_permutation_1 not_col_permutation_4)
  then have "B C TS D A"
    using invert_two_sides by blast
  then have "B C OS A' D"
    using Q1 l9_8_1 by auto
  then have T1A: "D InAngle A' B C"
    by (simp add: P7 os2__inangle)
  then have "A B D CongA A' B D"
    by (metis Per_cases T1 Tarski_neutral_dimensionless.conga_comm Tarski_neutral_dimensionless.l11_18_1 Tarski_neutral_dimensionless_axioms acute_distincts assms(1) assms(3) inangle_distincts)
  then have T2: "A B D LeA A' B C"
    using LeA_def T1A by auto
  {
    assume "A B D CongA A' B C"
    then have "False"
      by (metis OS_def P7 T1 TS_def Tarski_neutral_dimensionless.out2__conga Tarski_neutral_dimensionless_axioms \<open>A B C LtA A B D\<close> \<open>A B D CongA A' B D\<close> \<open>\<And>thesis. (\<And>D. A B Perp D B \<and> A B OS C D \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> col_trivial_2 invert_one_side l11_17 l11_19 not_lta_and_conga out_trivial)
  }
  then have "\<not> A B D CongA A' B C" by auto
  then have "A B D LtA A' B C"
    using T2 LtA_def by auto
  thus ?thesis
    using T1 Obtuse_def by blast
qed

lemma bet_obtuse__acute:
  assumes "Bet A B A'" and
    "A' \<noteq> B" and
    "Obtuse A B C"
  shows "Acute A' B C"
proof cases
  assume P1: "Col A B C"
  thus ?thesis
  proof cases
    assume "Bet A B C"
    then have "B Out A' C"
      by (smt Out_def assms(1) assms(2) assms(3) l5_2 obtuse_distincts)
    thus ?thesis
      by (simp add: out__acute)
  next
    assume "\<not> Bet A B C"
    thus ?thesis
      using P1 assms(3) col_obtuse__bet by blast
  qed
next
  assume P2: "\<not> Col A B C"
  then obtain D where P3: "A B Perp D B \<and> A B OS C D"
    using col_trivial_2 l10_15 by blast
  {
    assume P3A: "Col C B D"
    have P3B: "B \<noteq> D"
      using P3 perp_not_eq_2 by blast
    have P3C: "Per A B D"
      using P3 Perp_perm perp_per_2 by blast
    then have "Per A B C"
      using P3A P3B not_col_permutation_2 per_col by blast
    then have "A B C LtA A B C"
      using P2 assms(3) not_col_distincts obtuse_per__lta by auto
    then have "False"
      by (simp add: nlta)
  }
  then have P4: "\<not> Col C B D" by auto
  have "Col B A A'"
    using Col_def Col_perm assms(1) by blast
  then have P5: "B A' OS C D"
    using P3 assms(2) invert_one_side col2_os__os col_trivial_3 by blast
  have P7: "Per A' B D"
    by (meson Col_def P3 Tarski_neutral_dimensionless.Per_perm Tarski_neutral_dimensionless_axioms assms(1) col_trivial_2 l8_16_1)
  have "A' B C LtA A' B D"
  proof -
    have P8: "A' B C LeA A' B D"
    proof -
      have P9: "C InAngle A' B D"
      proof -
        have P10: "B A' OS D C"
          by (simp add: P5 one_side_symmetry)
        have "B D OS A' C"
        proof -
          have P6: "\<not> Col A B D"
            using P3 col124__nos by auto
          then have P11: "B D TS A' A"
            using Col_perm P5 assms(1) bet__ts l9_2 os_distincts by blast
          have "A B D LtA A B C"
          proof -
            have P11A: "A \<noteq> B"
              using P2 col_trivial_1 by auto
            have P11B: "B \<noteq> D"
              using P4 col_trivial_2 by blast
            have "Per A B D"
              using P3 Perp_cases perp_per_2 by blast
            thus ?thesis
              by (simp add: P11A P11B Tarski_neutral_dimensionless.obtuse_per__lta Tarski_neutral_dimensionless_axioms assms(3))
          qed
          then have "A B D LeA A B C"
            by (simp add: lta__lea)
          then have "D InAngle A B C"
            by (simp add: P3 lea_in_angle)
          then have "D InAngle C B A"
            using l11_24 by blast
          then have "D B TS C A"
            by (simp add: P4 P6 in_angle_two_sides not_col_permutation_4)
          then have "B D TS C A"
            by (simp add: invert_two_sides)
          thus ?thesis
            using OS_def P11 by blast
        qed
        thus ?thesis
          by (simp add: P10 os2__inangle)
      qed
      have "A' B C CongA A' B C"
        using assms(2) assms(3) conga_refl obtuse_distincts by blast
      thus ?thesis
        by (simp add: P9 inangle__lea)
    qed
    {
      assume "A' B C CongA A' B D"
      then have "B Out C D"
        using P5 conga_os__out invert_one_side by blast
      then have "False"
        using P4 not_col_permutation_4 out_col by blast
    }
    then have "\<not> A' B C CongA A' B D" by auto
    thus ?thesis
      by (simp add: LtA_def P8)
  qed
  thus ?thesis
    using Acute_def P7 by blast
qed

lemma inangle_dec:
  "P InAngle A B C \<or> \<not> P InAngle A B C" by blast

lemma lea_dec:
  "A B C LeA D E F \<or> \<not> A B C LeA D E F" by blast

lemma lta_dec:
  "A B C LtA D E F \<or> \<not> A B C LtA D E F" by blast

lemma lea_total:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "D \<noteq> E" and
    "E \<noteq> F"
  shows "A B C LeA D E F \<or> D E F LeA A B C"
proof cases
  assume P1: "Col A B C"
  show ?thesis
  proof cases
    assume "B Out A C"
    thus ?thesis
      using assms(3) assms(4) l11_31_1 by auto
  next
    assume "\<not> B Out A C"
    thus ?thesis
      by (metis P1 assms(1) assms(2) assms(3) assms(4) l11_31_2 or_bet_out)
  qed
next
  assume P2: "\<not> Col A B C"
  show ?thesis
  proof cases
    assume P3: "Col D E F"
    show ?thesis
    proof cases
      assume "E Out D F"
      thus ?thesis
        using assms(1) assms(2) l11_31_1 by auto
    next
      assume "\<not> E Out D F"
      thus ?thesis
        by (metis P3 assms(1) assms(2) assms(3) assms(4) l11_31_2 l6_4_2)
    qed
  next
    assume P4: "\<not> Col D E F"
    show ?thesis
    proof cases
      assume "A B C LeA D E F"
      thus ?thesis
        by simp
    next
      assume P5: "\<not> A B C LeA D E F"
      obtain P where P6: "D E F CongA A B P \<and> A B OS P C"
        using P2 P4 angle_construction_1 by blast
      then have P7: "B A OS C P"
        using invert_one_side one_side_symmetry by blast
      have "B C OS A P"
      proof -
        {
          assume "Col P B C"
          then have P7B: "B Out C P"
            using Col_cases P7 col_one_side_out by blast
          have "A B C CongA D E F"
          proof -
            have P7C: "A B P CongA D E F"
              by (simp add: P6 conga_sym)
            have P7D: "B Out A A"
              by (simp add: assms(1) out_trivial)
            have P7E: "E Out D D"
              by (simp add: assms(3) out_trivial)
            have "E Out F F"
              using assms(4) out_trivial by auto
            thus ?thesis
              using P7B P7C P7D P7E l11_10 by blast
          qed
          then have "A B C LeA D E F"
            by (simp add: conga__lea)
          then have "False"
            by (simp add: P5)
        }
        then have P8: "\<not> Col P B C" by auto
        {
          assume T0: "B C TS A P"
          have "A B C CongA D E F"
          proof -
            have T1: "A B C LeA A B P"
            proof -
              have T1A: "C InAngle A B P"
                by (simp add: P7 T0 one_side_symmetry os_ts__inangle)
              have "A B C CongA A B C"
                using assms(1) assms(2) conga_refl by auto
              thus ?thesis
                by (simp add: T1A inangle__lea)
            qed
            have T2: "A B C CongA A B C"
              using assms(1) assms(2) conga_refl by auto
            have "A B P CongA D E F"
              by (simp add: P6 conga_sym)
            thus ?thesis
              using P5 T1 T2 l11_30 by blast
          qed
          then have "A B C LeA D E F"
            by (simp add: conga__lea)
          then have "False"
            by (simp add: P5)
        }
        then have "\<not> B C TS A P" by auto
        thus ?thesis
          using Col_perm P7 P8 one_side_symmetry os_ts1324__os two_sides_cases by blast
      qed
      then have "P InAngle A B C"
        using P7 os2__inangle by blast
      then have "D E F LeA A B C"
        using P6 LeA_def by blast
      thus ?thesis
        by simp
    qed
  qed
qed

lemma or_lta2_conga:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "D \<noteq> E" and
    "F \<noteq> E"
  shows "A B C LtA D E F \<or> D E F LtA A B C \<or> A B C CongA D E F"
proof -
  have P1: "A B C LeA D E F \<or> D E F LeA A B C"
    using assms(1) assms(2) assms(3) assms(4) lea_total by auto
  {
    assume "A B C LeA D E F"
    then have "A B C LtA D E F \<or> D E F LtA A B C \<or> A B C CongA D E F"
      using LtA_def by blast
  }
  {
    assume "D E F LeA A B C"
    then have "A B C LtA D E F \<or> D E F LtA A B C \<or> A B C CongA D E F"
      using LtA_def conga_sym by blast
  }
  thus ?thesis
    using P1 \<open>A B C LeA D E F \<Longrightarrow> A B C LtA D E F \<or> D E F LtA A B C \<or> A B C CongA D E F\<close> by blast
qed

lemma angle_partition:
  assumes "A \<noteq> B" and
    "B \<noteq> C"
  shows "Acute A B C \<or> Per A B C \<or> Obtuse A B C"
proof -
  obtain A' B' D' where P1: "\<not> (Bet A' B' D' \<or> Bet B' D' A' \<or> Bet D' A' B')"
    using lower_dim by auto
  then have "\<not> Col A' B' D'"
    by (simp add: Col_def)
  obtain C' where P3: "A' B' Perp C' B'"
    by (metis P1 Perp_perm between_trivial2 perp_exists)
  then have P4: "A B C LtA A' B' C' \<or> A' B' C' LtA A B C \<or> A B C CongA A' B' C'"
    by (metis P1 assms(1) assms(2) between_trivial2 or_lta2_conga perp_not_eq_2)
  {
    assume "A B C LtA A' B' C'"
    then have "Acute A B C \<or> Per A B C \<or> Obtuse A B C"
      using Acute_def P3 Perp_cases perp_per_2 by blast
  }
  {
    assume "A' B' C' LtA A B C"
    then have "Acute A B C \<or> Per A B C \<or> Obtuse A B C"
      using Obtuse_def P3 Perp_cases perp_per_2 by blast
  }
  {
    assume "A B C CongA A' B' C'"
    then have "Acute A B C \<or> Per A B C \<or> Obtuse A B C"
      by (metis P3 Perp_cases Tarski_neutral_dimensionless.conga_sym Tarski_neutral_dimensionless.l11_17 Tarski_neutral_dimensionless_axioms perp_per_2)
  }
  thus ?thesis
    using P4 \<open>A B C LtA A' B' C' \<Longrightarrow> Acute A B C \<or> Per A B C \<or> Obtuse A B C\<close> \<open>A' B' C' LtA A B C \<Longrightarrow> Acute A B C \<or> Per A B C \<or> Obtuse A B C\<close> by auto
qed

lemma acute_chara_1:
  assumes "Bet A B A'" and
    "B \<noteq> A'" and
    "Acute A B C"
  shows "A B C LtA A' B C"
proof -
  have "Obtuse A' B C"
    using acute_bet__obtuse assms(1) assms(2) assms(3) by blast
  thus ?thesis
    by (simp add: acute_obtuse__lta assms(3))
qed

lemma acute_chara_2:
  assumes "Bet A B A'" and
    "A B C LtA A' B C"
  shows "Acute A B C"
  by (metis Tarski_neutral_dimensionless.Acute_def Tarski_neutral_dimensionless_axioms acute_chara_1 angle_partition assms(1) assms(2) bet_obtuse__acute between_symmetry lta_distincts not_and_lta)

lemma acute_chara:
  assumes "Bet A B A'" and
    "B \<noteq> A'"
  shows "Acute A B C \<longleftrightarrow> A B C LtA A' B C"
  using acute_chara_1 acute_chara_2 assms(1) assms(2) by blast

lemma obtuse_chara:
  assumes "Bet A B A'" and
    "B \<noteq> A'"
  shows "Obtuse A B C \<longleftrightarrow> A' B C LtA A B C"
  by (metis Tarski_neutral_dimensionless.Obtuse_def Tarski_neutral_dimensionless_axioms acute_bet__obtuse acute_chara assms(1) assms(2) bet_obtuse__acute between_symmetry lta_distincts)

lemma conga__acute:
  assumes "A B C CongA A C B"
  shows "Acute A B C"
  by (metis acute_sym angle_partition assms conga_distinct conga_obtuse__obtuse l11_17 l11_43)

lemma cong__acute:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Cong A B A C"
  shows "Acute A B C"
  using angle_partition assms(1) assms(2) assms(3) cong__nlt l11_46 lt_left_comm by blast

lemma nlta__lea:
  assumes "\<not> A B C LtA D E F" and
    "A \<noteq> B" and
    "B \<noteq> C" and
    "D \<noteq> E" and
    "E \<noteq> F"
  shows "D E F LeA A B C"
  by (metis LtA_def assms(1) assms(2) assms(3) assms(4) assms(5) conga__lea456123 or_lta2_conga)

lemma nlea__lta:
  assumes "\<not> A B C LeA D E F" and
    "A \<noteq> B" and
    "B \<noteq> C" and
    "D \<noteq> E" and
    "E \<noteq> F"
  shows "D E F LtA A B C"
  using assms(1) assms(2) assms(3) assms(4) assms(5) nlta__lea by blast

lemma triangle_strict_inequality:
  assumes "Bet A B D" and
    "Cong B C B D" and
    "\<not> Bet A B C"
  shows "A C Lt A D"
proof cases
  assume P1: "Col A B C"
  then have P2: "B Out A C"
    using assms(3) not_out_bet by auto
  {
    assume "Bet B A C"
    then have P3: "A C Le A D"
      by (meson assms(1) assms(2) cong__le l5_12_a le_transitivity)
    have "\<not> Cong A C A D"
      by (metis Out_def P1 P2 assms(1) assms(2) assms(3) l4_18)
    then have "A C Lt A D"
      by (simp add: Lt_def P3)
  }
  {
    assume "Bet A C B"
    then have P5: "Bet A C D"
      using assms(1) between_exchange4 by blast
    then have P6: "A C Le A D"
      by (simp add: bet__le1213)
    have "\<not> Cong A C A D"
      using P5 assms(1) assms(3) between_cong by blast
    then have "A C Lt A D"
      by (simp add: Lt_def P6)
  }
  thus ?thesis
    using P1 \<open>Bet B A C \<Longrightarrow> A C Lt A D\<close> assms(3) between_symmetry third_point by blast
next
  assume T1: "\<not> Col A B C"
  have T2: "A \<noteq> D"
    using T1 assms(1) between_identity col_trivial_1 by auto
  have T3: "\<not> Col A C D"
    by (metis Col_def T1 T2 assms(1) col_transitivity_2)
  have T4: "Bet D B A"
    using Bet_perm assms(1) by blast
  have T5: "C D A CongA D C B"
  proof -
    have T6: "C D B CongA D C B"
      by (metis assms(1) assms(2) assms(3) between_trivial conga_comm l11_44_1_a not_conga_sym)
    have T7: "D Out C C"
      using T3 not_col_distincts out_trivial by blast
    have T8: "D Out A B"
      by (metis assms(1) assms(2) assms(3) bet_out_1 cong_diff l6_6)
    have T9: "C Out D D"
      using T7 out_trivial by force
    have "C Out B B"
      using T1 not_col_distincts out_trivial by auto
    thus ?thesis
      using T6 T7 T8 T9 l11_10 by blast
  qed
  have "A D C LtA A C D"
  proof -
    have "B InAngle D C A"
      by (metis InAngle_def T1 T3 T4 not_col_distincts out_trivial)
    then have "C D A LeA D C A"
      using T5 LeA_def by auto
    then have T10: "A D C LeA A C D"
      by (simp add: lea_comm)
    have "\<not> A D C CongA A C D"
      by (metis Col_perm T3 assms(1) assms(2) assms(3) bet_col l11_44_1_b l4_18 not_bet_distincts not_cong_3412)
    thus ?thesis
      using LtA_def T10 by blast
  qed
  thus ?thesis
    by (simp add: l11_44_2_b)
qed

lemma triangle_inequality:
  assumes "Bet A B D" and
    "Cong B C B D"
  shows "A C Le A D"
proof cases
  assume "Bet A B C"
  thus ?thesis
    by (metis assms(1) assms(2) between_cong_3 cong__le le_reflexivity)
next
  assume "\<not> Bet A B C"
  then have "A C Lt A D"
    using assms(1) assms(2) triangle_strict_inequality by auto
  thus ?thesis
    by (simp add: Lt_def)
qed

lemma triangle_strict_inequality_2:
  assumes "Bet A' B' C'" and
    "Cong A B A' B'" and
    "Cong B C B' C'"  and
    "\<not> Bet A B C"
  shows "A C Lt A' C'"
proof -
  obtain D where P1: "Bet A B D \<and> Cong B D B C"
    using segment_construction by blast
  then have P2: "A C Lt A D"
    using P1 assms(4) cong_symmetry triangle_strict_inequality by blast
  have "Cong A D A' C'"
    using P1 assms(1) assms(2) assms(3) cong_transitivity l2_11_b by blast
  thus ?thesis
    using P2 cong2_lt__lt cong_reflexivity by blast
qed

lemma triangle_inequality_2:
  assumes "Bet A' B' C'" and
    "Cong A B A' B'" and
    "Cong B C B' C'"
  shows "A C Le A' C'"
proof -
  obtain D where P1: "Bet A B D \<and> Cong B D B C"
    using segment_construction by blast
  have P2: "A C Le A D"
    by (meson P1 Tarski_neutral_dimensionless.triangle_inequality Tarski_neutral_dimensionless_axioms not_cong_3412)
  have "Cong A D A' C'"
    using P1 assms(1) assms(2) assms(3) cong_transitivity l2_11_b by blast
  thus ?thesis
    using P2 cong__le le_transitivity by blast
qed

lemma triangle_strict_reverse_inequality:
  assumes "A Out B D" and
    "Cong A C A D" and
    "\<not> A Out B C"
  shows "B D Lt B C"
proof cases
  assume "Col A B C"
  thus ?thesis
    using assms(1) assms(2) assms(3) col_permutation_4 cong_symmetry not_bet_and_out or_bet_out triangle_strict_inequality by blast
next
  assume P1: "\<not> Col A B C"
  show ?thesis
  proof cases
    assume "B = D"
    thus ?thesis
      using P1 lt1123 not_col_distincts by auto
  next
    assume P2: "B \<noteq> D"
    then have P3: "\<not> Col B C D"
      using P1 assms(1) col_trivial_2 colx not_col_permutation_5 out_col by blast
    have P4: "\<not> Col A C D"
      using P1 assms(1) col2__eq col_permutation_4 out_col out_distinct by blast
    have P5: "C \<noteq> D"
      using assms(1) assms(3) by auto
    then have P6: "A C D CongA A D C"
      by (metis P1 assms(2) col_trivial_3 l11_44_1_a)
    {
      assume T1: "Bet A B D"
      then have T2: "Bet D B A"
        using Bet_perm by blast
      have "B C D LtA B D C"
      proof -
        have T3: "D C B CongA B C D"
          by (metis P3 conga_pseudo_refl not_col_distincts)
        have T3A: "D Out B A"
          by (simp add: P2 T1 bet_out_1)
        have T3B: "C Out D D"
          using P5 out_trivial by auto
        have T3C: "C Out A A"
          using P1 not_col_distincts out_trivial by blast
        have "D Out C C"
          by (simp add: P5 out_trivial)
        then have T4: "D C A CongA B D C" using T3A T3B T3C
          by (meson Tarski_neutral_dimensionless.conga_comm Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless.l11_10 Tarski_neutral_dimensionless_axioms P6)
        have "D C B LtA D C A"
        proof -
          have T4A: "D C B LeA D C A"
          proof -
            have T4AA: "B InAngle D C A"
              using InAngle_def P1 P5 T2 not_col_distincts out_trivial by auto
            have "D C B CongA D C B"
              using T3 conga_right_comm by blast
            thus ?thesis
              by (simp add: T4AA inangle__lea)
          qed
          {
            assume T5: "D C B CongA D C A"
            have "D C OS B A"
              using Col_perm P3 T3A out_one_side by blast
            then have "C Out B A"
              using T5 conga_os__out by blast
            then have "False"
              using Col_cases P1 out_col by blast
          }
          then have "\<not> D C B CongA D C A" by auto
          thus ?thesis
            using LtA_def T4A by blast
        qed
        thus ?thesis
          using T3 T4 conga_preserves_lta by auto
      qed
    }
    {
      assume Q1: "Bet B D A"
      obtain E where Q2: "Bet B C E \<and> Cong B C C E"
        using Cong_perm segment_construction by blast
      have "A D C LtA E C D"
      proof -
        have Q3: "D C OS A E"
        proof -
          have Q4: "D C TS A B"
            by (metis Col_perm P2 Q1 P4 bet__ts between_symmetry)
          then have "D C TS E B"
            by (metis Col_def Q1 Q2 TS_def bet__ts cong_identity invert_two_sides l9_2)
          thus ?thesis
            using OS_def Q4 by blast
        qed
        have Q5: "A C D LtA E C D"
        proof -
          have "D C A LeA D C E"
          proof -
            have "B Out D A"
              using P2 Q1 bet_out by auto
            then have "B C OS D A"
              by (simp add: P3 out_one_side)
            then have "C B OS D A"
              using invert_one_side by blast
            then have "C E OS D A"
              by (metis Col_def Q2 Q3 col124__nos col_one_side diff_col_ex not_col_permutation_5)
            then have Q5A: "A InAngle D C E"
              by (simp add: \<open>C E OS D A\<close> Q3 invert_one_side one_side_symmetry os2__inangle)
            have "D C A CongA D C A"
              using CongA_def P6 conga_refl by auto
            thus ?thesis
              by (simp add: Q5A inangle__lea)
          qed
          then have Q6: "A C D LeA E C D"
            using lea_comm by blast
          {
            assume "A C D CongA E C D"
            then have "D C A CongA D C E"
              by (simp add: conga_comm)
            then have "C Out A E"
              using Q3 conga_os__out by auto
            then have "False"
              by (meson Col_def Out_cases P1 Q2 not_col_permutation_3 one_side_not_col123 out_one_side)
          }
          then have "\<not> A C D CongA E C D" by auto
          thus ?thesis
            by (simp add: LtA_def Q6)
        qed
        have "E C D CongA E C D"
          by (metis P1 P5 Q2 cong_diff conga_refl not_col_distincts)
        thus ?thesis
          using Q5 P6 conga_preserves_lta by auto
      qed
      then have "B C D LtA B D C"
        using Bet_cases P1 P2 Q1 Q2 bet2_lta__lta not_col_distincts by blast
    }
    then have "B C D LtA B D C"
      by (meson Out_def \<open>Bet A B D \<Longrightarrow> B C D LtA B D C\<close> assms(1) between_symmetry)
    thus ?thesis
      by (simp add: l11_44_2_b)
  qed
qed

lemma triangle_reverse_inequality:
  assumes "A Out B D" and
    "Cong A C A D"
  shows "B D Le B C"
proof cases
  assume "A Out B C"
  thus ?thesis
    by (metis assms(1) assms(2) bet__le1213 cong_pseudo_reflexivity l6_11_uniqueness l6_6 not_bet_distincts not_cong_4312)
next
  assume "\<not> A Out B C"
  thus ?thesis
    using triangle_strict_reverse_inequality assms(1) assms(2) lt__le by auto
qed

lemma os3__lta:
  assumes "A B OS C D" and
    "B C OS A D" and
    "A C OS B D"
  shows "B A C LtA B D C"
proof -
  have P1: "D InAngle A B C"
    by (simp add: assms(1) assms(2) invert_one_side os2__inangle)
  then obtain E where P2: "Bet A E C \<and> (E = B \<or> B Out E D)"
    using InAngle_def by auto
  have P3: "\<not> Col A B C"
    using assms(1) one_side_not_col123 by auto
  have P4: "\<not> Col A C D"
    using assms(3) col124__nos by auto
  have P5: "\<not> Col B C D"
    using assms(2) one_side_not_col124 by auto
  have P6: "\<not> Col A B D"
    using assms(1) one_side_not_col124 by auto
  {
    assume "E = B"
    then have "B A C LtA B D C"
      using P2 P3 bet_col by blast
  }
  {
    assume P7: "B Out E D"
    have P8: "A \<noteq> E"
      using P6 P7 not_col_permutation_4 out_col by blast
    have P9: "C \<noteq> E"
      using P5 P7 out_col by blast
    have P10: "B A C LtA B E C"
    proof -
      have P10A: "\<not> Col E A B"
        by (metis Col_def P2 P3 P8 col_transitivity_1)
      then have P10B: "E B A LtA B E C"
        using P2 P9 Tarski_neutral_dimensionless.l11_41_aux Tarski_neutral_dimensionless_axioms by fastforce
      have P10C: "E A B LtA B E C"
        using P2 P9 P10A l11_41 by auto
      have P11: "E A B CongA B A C"
      proof -
        have P11A: "A Out B B"
          using assms(2) os_distincts out_trivial by auto
        have "A Out C E"
          using P2 P8 bet_out l6_6 by auto
        thus ?thesis
          using P11A conga_right_comm out2__conga by blast
      qed
      have P12: "B E C CongA B E C"
        by (metis Col_def P2 P3 P9 conga_refl)
      thus ?thesis
        using P11 P10C conga_preserves_lta by auto
    qed
    have "B E C LtA B D C"
    proof -
      have U1: "E Out D B"
      proof -
        obtain pp :: "'p \<Rightarrow> 'p \<Rightarrow> 'p" where
          f1: "\<forall>p pa. p \<noteq> (pp p pa) \<and> pa \<noteq> (pp p pa) \<and> Col p pa (pp p pa)"
          using diff_col_ex by moura
        then have "\<forall>p pa pb. Col pb pa p \<or> \<not> Col pb pa (pp p pa)"
          by (meson l6_16_1)
        then have f2: "\<forall>p pa. Col pa p pa"
          using f1 by metis
        have f3: "(E = B \<or> D = E) \<or> Col D E B"
          using f1 by (metis Col_def P2 col_out2_col l6_16_1 out_trivial)
        have "\<forall>p. (A = E \<or> Col p A C) \<or> \<not> Col p A E"
          using Col_def P2 l6_16_1 by blast
        thus ?thesis
          using f3 f2 by (metis (no_types) Col_def assms(3) not_out_bet one_side_chara one_side_symmetry)
      qed
      have U2: "D \<noteq> E"
        using P2 P4 bet_col not_col_permutation_5 by blast
      have U3: "\<not> Col D E C"
        by (metis Col_def P2 P4 P9 col_transitivity_1)
      have U4: "Bet E D B"
        by (simp add: P7 U1 out2__bet)
      have "D C E LtA C D B"
        using P5 U3 U4 l11_41_aux not_col_distincts by blast
      have U5: "D E C LtA C D B"
        using P7 U4 U3 l11_41 out_diff2 by auto
      have "D E C CongA B E C"
        by (simp add: P9 U1 l6_6 out2__conga out_trivial)
      thus ?thesis
        by (metis U5 conga_preserves_lta conga_pseudo_refl lta_distincts)
    qed
    then have "B A C LtA B D C"
      using P10 lta_trans by blast
  }
  thus ?thesis
    using P2 \<open>E = B \<Longrightarrow> B A C LtA B D C\<close> by blast
qed

lemma bet_le__lt:
  assumes "Bet A D B" and
    "A \<noteq> D" and
    "D \<noteq> B" and
    "A C Le B C"
  shows "D C Lt B C"
proof -
  have P1: "A \<noteq> B"
    using assms(1) assms(2) between_identity by blast
  have "C D Lt C B"
  proof cases
    assume P3: "Col A B C"
    thus ?thesis
    proof cases
      assume "Bet C D B"
      thus ?thesis
        by (simp add: assms(3) bet__lt1213)
    next
      assume "\<not> Bet C D B"
      then have "D Out C B"
        by (metis Out_def P1 P3 assms(1) col_transitivity_2 not_col_permutation_3 not_out_bet out_col)
      thus ?thesis
        by (smt Le_cases P3 assms(1) assms(2) assms(4) bet2_le2__le bet_le_eq bet_out_1 l6_6 l6_7 nle__lt or_bet_out out2__bet out_bet__out)
    qed
  next
    assume Q0A: "\<not> Col A B C"
    then have Q0B: "\<not> Col B C D"
      by (meson Col_def assms(1) assms(3) col_transitivity_2)
    have "C B D LtA C D B"
    proof -
      have Q1: "B Out C C"
        using Q0A not_col_distincts out_trivial by force
      have Q2: "B Out A D"
        using Out_cases assms(1) assms(3) bet_out_1 by blast
      have Q3: "A Out C C"
        by (metis Q0A col_trivial_3 out_trivial)
      have Q4: "A Out B B"
        using P1 out_trivial by auto
      have "C B A LeA C A B"
        using Col_perm Le_cases Q0A assms(4) l11_44_2bis by blast
      then have T9: "C B D LeA C A B"
        using Q1 Q2 Q3 Q4 lea_out4__lea by blast
      have "C A B LtA C D B"
      proof -
        have U2: "\<not> Col D A C"
          using Q0B assms(1) assms(2) bet_col col_transitivity_2 not_col_permutation_3 not_col_permutation_4 by blast
        have U3: "D \<noteq> C"
          using Q0B col_trivial_2 by blast
        have U4: "D C A LtA C D B"
          using U2 assms(1) assms(3) l11_41_aux by auto
        have U5: "D A C LtA C D B"
          by (simp add: U2 assms(1) assms(3) l11_41)
        have "A Out B D"
          using Out_def P1 assms(1) assms(2) by auto
        then have "D A C CongA C A B"
          using Q3 conga_right_comm out2__conga by blast
        thus ?thesis
          by (metis U5 U3 assms(3) conga_preserves_lta conga_refl)
      qed
      thus ?thesis
        using T9 lea123456_lta__lta by blast
    qed
    thus ?thesis
      by (simp add: l11_44_2_b)
  qed
  thus ?thesis
    using Lt_cases by auto
qed

lemma cong2__ncol:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "A \<noteq> C" and
    "Cong A P B P" and
    "Cong A P C P"
  shows "\<not> Col A B C"
proof -
  have "Cong B P C P"
    using assms(4) assms(5) cong_inner_transitivity by blast
  thus ?thesis using bet_le__lt
    by (metis assms(1) assms(2) assms(3) assms(4) assms(5) cong__le cong__nlt lt__nle not_col_permutation_5 third_point)
qed

lemma cong4_cop2__eq:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "A \<noteq> C" and
    "Cong A P B P" and
    "Cong A P C P" and
    "Coplanar A B C P" and
    "Cong A Q B Q" and
    "Cong A Q C Q" and
    "Coplanar A B C Q"
  shows "P = Q"
proof -
  have P1: "\<not> Col A B C"
    using assms(1) assms(2) assms(3) assms(4) assms(5) cong2__ncol by auto
  {
    assume P2: "P \<noteq> Q"
    have P3: "\<forall> R. Col P Q R \<longrightarrow> (Cong A R B R \<and> Cong A R C R)"
      using P2 assms(4) assms(5) assms(7) assms(8) l4_17 not_cong_4321 by blast
    obtain D where P4: "D Midpoint A B"
      using midpoint_existence by auto
    have P5: "Coplanar A B C D"
      using P4 coplanar_perm_9 midpoint__coplanar by blast
    have P6: "Col P Q D"
    proof -
      have P6A: "Coplanar P Q D A"
        using P1 P5 assms(6) assms(9) coplanar_pseudo_trans ncop_distincts by blast
      then have P6B: "Coplanar P Q D B"
        by (metis P4 col_cop__cop midpoint_col midpoint_distinct_1)
      have P6D: "Cong P A P B"
        using assms(4) not_cong_2143 by blast
      have P6E: "Cong Q A Q B"
        using assms(7) not_cong_2143 by blast
      have "Cong D A D B"
        using Midpoint_def P4 not_cong_2134 by blast
      thus ?thesis using cong3_cop2__col P6A P6B assms(1) P6D P6E by blast
    qed
    obtain R1 where P7: "P \<noteq> R1 \<and> Q \<noteq> R1 \<and> D \<noteq> R1 \<and> Col P Q R1"
      using P6 diff_col_ex3 by blast
    obtain R2 where P8: "Bet R1 D R2 \<and> Cong D R2 R1 D"
      using segment_construction by blast
    have P9: "Col P Q R2"
      by (metis P6 P7 P8 bet_col colx)
    have P9A: "Cong R1 A R1 B"
      using P3 P7 not_cong_2143 by blast
    then have "Per R1 D A"
      using P4 Per_def by auto
    then have "Per A D R1" using l8_2 by blast
    have P10: "Cong A R1 A R2"
    proof -
      have f1: "Bet R2 D R1 \<or>Bet R1 R2 D"
        by (metis (full_types) Col_def P7 P8 between_equality not_col_permutation_5)
      have f2: "Cong B R1 A R1"
        using Cong_perm \<open>Cong R1 A R1 B\<close> by blast
      have "Cong B R1 A R2 \<or> Bet R1 R2 D"
        using f1 Cong_perm Midpoint_def P4 P8 l7_13 by blast
      thus ?thesis
        using f2 P8 bet_cong_eq cong_inner_transitivity by blast
    qed
    have "Col A B C"
    proof -
      have P11: "Cong B R1 B R2"
        by (metis Cong_perm P10 P3 P9 P9A cong_inner_transitivity)
      have P12: "Cong C R1 C R2"
        using P10 P3 P7 P9 cong_inner_transitivity by blast
      have P12A: "Coplanar A B C R1"
        using P2 P7 assms(6) assms(9) col_cop2__cop by blast
      have P12B: "Coplanar A B C R2"
        using P2 P9 assms(6) assms(9) col_cop2__cop by blast
      have "R1 \<noteq> R2"
        using P7 P8 between_identity by blast
      thus ?thesis
        using P10 P11 P12A P12B P12 cong3_cop2__col by blast
    qed
    then have False
      by (simp add: P1)
  }
  thus ?thesis by auto
qed

lemma t18_18_aux:
  assumes "Cong A B D E" and
    "Cong A C D F" and
    "F D E LtA C A B" and
    "\<not> Col A B C" and
    "\<not> Col D E F" and
    "D F Le D E"
  shows "E F Lt B C"
proof -
  obtain G0 where P1: "C A B CongA F D G0 \<and> F D OS G0 E"
    using angle_construction_1 assms(4) assms(5) not_col_permutation_2 by blast
  then have P2: "\<not> Col F D G0"
    using col123__nos by auto
  then obtain G where P3: "D Out G0 G \<and> Cong D G A B"
    by (metis assms(4) bet_col between_trivial2 col_trivial_2 segment_construction_3)
  have P4: "C A B CongA F D G"
  proof -
    have P4B: "A Out C C"
      by (metis assms(4) col_trivial_3 out_trivial)
    have P4C: "A Out B B"
      by (metis assms(4) col_trivial_1 out_trivial)
    have P4D: "D Out F F"
      using P2 not_col_distincts out_trivial by blast
    have "D Out G G0"
      by (simp add: P3 l6_6)
    thus ?thesis using P1 P4B P4C P4D
      using l11_10 by blast
  qed
  have "D Out G G0"
    by (simp add: P3 l6_6)
  then have "D F OS G G0"
    using P2 not_col_permutation_4 out_one_side by blast
  then have "F D OS G G0"
    by (simp add: invert_one_side)
  then have P5: "F D OS G E"
    using P1 one_side_transitivity by blast
  have P6: "\<not> Col F D G"
    by (meson P5 one_side_not_col123)
  have P7: "Cong C B F G"
    using P3 P4 assms(2) cong2_conga_cong cong_commutativity cong_symmetry by blast
  have P8: "F E Lt F G"
  proof -
    have P9: "F D E LtA F D G"
      by (metis P4 assms(3) assms(5) col_trivial_1 col_trivial_3 conga_preserves_lta conga_refl)
    have P10: "Cong D G D E"
      using P3 assms(1) cong_transitivity by blast
    {
      assume P11: "Col E F G"
      have P12: "F D E LeA F D G"
        by (simp add: P9 lta__lea)
      have P13: "\<not> F D E CongA F D G"
        using P9 not_lta_and_conga by blast
      have "F D E CongA F D G"
      proof -
        have "F Out E G"
          using Col_cases P11 P5 col_one_side_out l6_6 by blast
        then have "E F D CongA G F D"
          by (metis assms(5) conga_os__out conga_refl l6_6 not_col_distincts one_side_reflexivity out2__conga)
        thus ?thesis
          by (meson P10 assms(2) assms(6) cong_4321 cong_inner_transitivity l11_52 le_comm)
      qed
      then have "False"
        using P13 by blast
    }
    then have P15: "\<not> Col E F G" by auto
    {
      assume P20: "Col D E G"
      have P21: "F D E LeA F D G"
        by (simp add: P9 lta__lea)
      have P22: "\<not> F D E CongA F D G"
        using P9 not_lta_and_conga by blast
      have "F D E CongA F D G"
      proof -
        have "D Out E G"
          by (meson Out_cases P5 P20 col_one_side_out invert_one_side not_col_permutation_5)
        thus ?thesis
          using P10 P15 \<open>D Out G G0\<close> cong_inner_transitivity l6_11_uniqueness l6_7 not_col_distincts by blast
      qed
      then have "False"
        by (simp add: P22)
    }
    then have P16: "\<not> Col D E G" by auto
    have P17: "E InAngle F D G"
      using lea_in_angle by (simp add: P5 P9 lta__lea)
    then obtain H where P18: "Bet F H G \<and> (H = D \<or> D Out H E)"
      using InAngle_def by auto
    {
      assume "H = D"
      then have "F G E LtA F E G"
        using P18 P6 bet_col by blast
    }
    {
      assume P19: "D Out H E"
      have P20: "H \<noteq> F"
        using Out_cases P19 assms(5) out_col by blast
      have P21: "H \<noteq> G"
        using P19 P16 l6_6 out_col by blast
      have "F D Le G D"
        using P10 assms(6) cong_pseudo_reflexivity l5_6 not_cong_4312 by blast
      then have "H D Lt G D"
        using P18 P20 P21 bet_le__lt by blast
      then have P22: "D H Lt D E"
        using Lt_cases P10 cong2_lt__lt cong_reflexivity by blast
      then have P23: "D H Le D E \<and> \<not> Cong D H D E"
        using Lt_def by blast
      have P24: "H \<noteq> E"
        using P23 cong_reflexivity by blast
      have P25: "Bet D H E"
        by (simp add: P19 P23 l6_13_1)
      have P26: "E G OS F D"
        by (metis InAngle_def P15 P16 P18 P25 bet_out_1 between_symmetry in_angle_one_side not_col_distincts not_col_permutation_1)
      have "F G E LtA F E G"
      proof -
        have P27: "F G E LtA D E G"
        proof -
          have P28: "D G E CongA D E G"
            by (metis P10 P16 l11_44_1_a not_col_distincts)
          have "F G E LtA D G E"
          proof -
            have P29: "F G E LeA D G E"
              by (metis OS_def P17 P26 P5 TS_def in_angle_one_side inangle__lea_1 invert_one_side l11_24 os2__inangle)
            {
              assume "F G E CongA D G E"
              then have "E G F CongA E G D"
                by (simp add: conga_comm)
              then have "G Out F D"
                using P26 conga_os__out by auto
              then have "False"
                using P6 not_col_permutation_2 out_col by blast
            }
            then have "\<not> F G E CongA D G E" by auto
            thus ?thesis
              by (simp add: LtA_def P29)
          qed
          thus ?thesis
            by (metis P28 P6 col_trivial_3 conga_preserves_lta conga_refl)
        qed
        have "G E D LtA G E F"
        proof -
          have P30: "G E D LeA G E F"
          proof -
            have P31: "D InAngle G E F"
              by (simp add: P16 P17 P26 assms(5) in_angle_two_sides l11_24 not_col_permutation_5 os_ts__inangle)
            have "G E D CongA G E D"
              by (metis P16 col_trivial_1 col_trivial_2 conga_refl)
            thus ?thesis
              using P31 inangle__lea by auto
          qed
          have "\<not> G E D CongA G E F"
            by (metis OS_def P26 P5 TS_def conga_os__out invert_one_side out_col)
          thus ?thesis
            by (simp add: LtA_def P30)
        qed
        then have "D E G LtA F E G"
          using lta_comm by blast
        thus ?thesis
          using P27 lta_trans by blast
      qed
    }
    then have "F G E LtA F E G"
      using P18 \<open>H = D \<Longrightarrow> F G E LtA F E G\<close> by blast
    thus ?thesis
      by (simp add: l11_44_2_b)
  qed
  then have "E F Lt F G"
    using lt_left_comm by blast
  thus ?thesis
    using P7 cong2_lt__lt cong_pseudo_reflexivity not_cong_4312 by blast
qed

lemma t18_18:
  assumes "Cong A B D E" and
    "Cong A C D F" and
    "F D E LtA C A B"
  shows "E F Lt B C"
proof -
  have P1: "F \<noteq> D"
    using assms(3) lta_distincts by blast
  have P2: "E \<noteq> D"
    using assms(3) lta_distincts by blast
  have P3: "C \<noteq> A"
    using assms(3) lta_distincts by auto
  have P4: "B \<noteq> A"
    using assms(3) lta_distincts by blast
  {
    assume P6: "Col A B C"
    {
      assume P7: "Bet B A C"
      obtain C' where P8:"Bet E D C' \<and> Cong D C' A C"
        using segment_construction by blast
      have P9: "Cong E F E F"
        by (simp add: cong_reflexivity)
      have P10: "Cong E C' B C"
        using P7 P8 assms(1) l2_11_b not_cong_4321 by blast
      have "E F Lt E C'"
      proof -
        have P11: "Cong D F D C'"
          using P8 assms(2) cong_transitivity not_cong_3412 by blast
        have "\<not> Bet E D F"
          using Bet_perm Col_def assms(3) col_lta__out not_bet_and_out by blast
        thus ?thesis
          using P11 P8 triangle_strict_inequality by blast
      qed
      then have "E F Lt B C"
        using P9 P10 cong2_lt__lt by blast
    }
    {
      assume "\<not> Bet B A C"
      then have "E F Lt B C"
        using P6 assms(3) between_symmetry col_lta__bet col_permutation_2 by blast
    }
    then have "E F Lt B C"
      using \<open>Bet B A C \<Longrightarrow> E F Lt B C\<close> by auto
  }
  {
    assume P12: "\<not> Col A B C"
    {
      assume P13: "Col D E F"
      {
        assume P14: "Bet F D E"
        then have "C A B LeA F D E"
          by (simp add: P1 P2 P3 P4 l11_31_2)
        then have "F D E LtA F D E"
          using assms(3) lea__nlta by auto
        then have "False"
          by (simp add: nlta)
        then have "E F Lt B C" by auto
      }
      {
        assume "\<not> Bet F D E"
        then have P16: "D Out F E"
          using P13 not_col_permutation_1 not_out_bet by blast
        obtain F' where P17: "A Out B F' \<and> Cong A F' A C"
          using P3 P4 segment_construction_3 by fastforce
        then have P18: "B F' Lt B C"
          by (meson P12 Tarski_neutral_dimensionless.triangle_strict_reverse_inequality Tarski_neutral_dimensionless_axioms not_cong_3412 out_col)
        have "Cong B F' E F"
          by (meson Out_cases P16 P17 assms(1) assms(2) cong_transitivity out_cong_cong)
        then have "E F Lt B C"
          using P18 cong2_lt__lt cong_reflexivity by blast
      }
      then have "E F Lt B C"
        using \<open>Bet F D E \<Longrightarrow> E F Lt B C\<close> by blast
    }
    {
      assume P20: "\<not> Col D E F"
      {
        assume "D F Le D E"
        then have "E F Lt B C"
          by (meson P12 Tarski_neutral_dimensionless.t18_18_aux Tarski_neutral_dimensionless_axioms P20 assms(1) assms(2) assms(3))
      }
      {
        assume "D E Le D F"
        then have "E F Lt B C"
          by (meson P12 P20 Tarski_neutral_dimensionless.lta_comm Tarski_neutral_dimensionless.t18_18_aux Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) lt_comm not_col_permutation_5)
      }
      then have "E F Lt B C"
        using \<open>D F Le D E \<Longrightarrow> E F Lt B C\<close> local.le_cases by blast
    }
    then have "E F Lt B C"
      using \<open>Col D E F \<Longrightarrow> E F Lt B C\<close> by blast
  }
  thus ?thesis
    using \<open>Col A B C \<Longrightarrow> E F Lt B C\<close> by auto
qed

lemma t18_19:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "Cong A B D E" and
    "Cong A C D F" and
    "E F Lt B C"
  shows "F D E LtA C A B"
proof -
  {
    assume P1: "C A B LeA F D E"
    {
      assume "C A B CongA F D E"
      then have "False"
        using Cong_perm assms(3) assms(4) assms(5) cong__nlt l11_49 by blast
    }
    {
      assume P2: "\<not> C A B CongA F D E"
      then have "C A B LtA F E D"
        by (metis P1 assms(3) assms(4) assms(5) cong_symmetry lea_distincts lta__nlea not_and_lt or_lta2_conga t18_18)
      then have "B C Lt E F"
        by (metis P1 P2 assms(3) assms(4) cong_symmetry lta__nlea lta_distincts or_lta2_conga t18_18)
      then have "False"
        using assms(5) not_and_lt by auto
    }
    then have "False"
      using \<open>C A B CongA F D E \<Longrightarrow> False\<close> by auto
  }
  then have "\<not> C A B LeA F D E" by auto
  thus ?thesis
    using assms(1) assms(2) assms(3) assms(4) cong_identity nlea__lta by blast
qed

lemma acute_trivial:
  assumes "A \<noteq> B"
  shows "Acute A B A"
  by (metis Tarski_neutral_dimensionless.acute_distincts Tarski_neutral_dimensionless_axioms angle_partition assms l11_43)

lemma acute_not_per:
  assumes "Acute A B C"
  shows "\<not> Per A B C"
proof -
  obtain A' B' C' where P1: "Per A' B' C' \<and> A B C LtA A' B' C'"
    using Acute_def assms by auto
  thus ?thesis
    using acute_distincts acute_per__lta assms nlta by fastforce
qed

lemma angle_bisector:
  assumes "A \<noteq> B" and
    "C \<noteq> B"
  shows "\<exists> P. (P InAngle A B C \<and> P B A CongA P B C)"
proof cases
  assume P1: "Col A B C"
  thus ?thesis
  proof cases
    assume P2: "Bet A B C"
    then obtain Q where P3: "\<not> Col A B Q"
      using assms(1) not_col_exists by auto
    then obtain P where P4: "A B Perp P B \<and> A B OS Q P"
      using P1 l10_15 os_distincts by blast
    then have P5: "P InAngle A B C"
      by (metis P2 assms(2) in_angle_line os_distincts)
    have "P B A CongA P B C"
    proof -
      have P9: "P \<noteq> B"
        using P4 os_distincts by blast
      have "Per P B A"
        by (simp add: P4 Perp_perm Tarski_neutral_dimensionless.perp_per_2 Tarski_neutral_dimensionless_axioms)
      thus ?thesis
        using P2 assms(1) assms(2) P9 l11_18_1 by auto
    qed
    thus ?thesis
      using P5 by auto
  next
    assume T1: "\<not> Bet A B C"
    then have T2: "B Out A C"
      by (simp add: P1 l6_4_2)
    have T3: "C InAngle A B C"
      by (simp add: assms(1) assms(2) inangle3123)
    have "C B A CongA C B C"
      using T2 between_trivial2 l6_6 out2__conga out2_bet_out by blast
    thus ?thesis
      using T3 by auto
  qed
next
  assume T4: "\<not> Col A B C"
  obtain C0 where T5: "B Out C0 C \<and> Cong B C0 B A"
    using assms(1) assms(2) l6_11_existence by fastforce
  obtain P where T6: "P Midpoint A C0"
    using midpoint_existence by auto
  have T6A: "\<not> Col A B C0"
    by (metis T4 T5 col3 l6_3_1 not_col_distincts out_col)
  have T6B: "P \<noteq> B"
    using Col_def Midpoint_def T6 T6A by auto
  have T6D: "P \<noteq> A"
    using T6 T6A is_midpoint_id not_col_distincts by blast
  have "P InAngle A B C0"
    using InAngle_def T5 T6 T6B assms(1) l6_3_1 midpoint_bet out_trivial by fastforce
  then have T7: "P InAngle A B C"
    using T5 T6B in_angle_trans2 l11_24 out341__inangle by blast
  have T8: "(P = B) \<or> B Out P P"
    using out_trivial by auto
  have T9: "B Out A A"
    by (simp add: assms(1) out_trivial)
  {
    assume T9A: "B Out P P"
    have "P B A CongA P B C0 \<and> B P A CongA B P C0 \<and> P A B CongA P C0 B"
    proof -
      have T9B: "Cong B P B P"
        by (simp add: cong_reflexivity)
      have T9C: "Cong B A B C0"
        using Cong_perm T5 by blast
      have "Cong P A P C0"
        using Midpoint_def T6 not_cong_2134 by blast
      thus ?thesis using l11_51 T6B assms(1) T9B T9C T6D by presburger
    qed
    then have "P B A CongA P B C0" by auto
    then have "P B A CongA P B C" using l11_10 T9A T9
      by (meson T5 l6_6)
    then have  "\<exists> P. (P InAngle A B C \<and> P B A CongA P B C)"
      using T7 by auto
  }
  thus ?thesis
    using T6B T8 by blast
qed

lemma reflectl__conga:
  assumes "A \<noteq> B" and
    "B \<noteq> P" and
    "P P' ReflectL A B"
  shows "A B P CongA A B P'"
proof -
  obtain A' where P1: "A' Midpoint P' P \<and> Col A B A' \<and> (A B Perp P' P \<or> P = P')"
    using ReflectL_def assms(3) by auto
  {
    assume P2: "A B Perp P' P"
    then have P3: "P \<noteq> P'"
      using perp_not_eq_2 by blast
    then have P4: "A' \<noteq> P'"
      using P1 is_midpoint_id by blast
    have P5: "A' \<noteq> P"
      using P1 P3 is_midpoint_id_2 by auto
    have  "A B P CongA A B P'"
    proof cases
      assume P6: "A' = B"
      then have P8: "B \<noteq> P'"
        using P4 by auto
      have P9: "Per A B P"
        by (smt P1 P3 P6 Perp_cases col_transitivity_2 midpoint_col midpoint_distinct_1 not_col_permutation_2 perp_col2_bis perp_per_2)
      have "Per A B P'"
        by (smt Mid_cases P1 P2 P6 P8 assms(1) col_trivial_3 midpoint_col not_col_permutation_3 perp_col4 perp_per_2)
      thus ?thesis
        using l11_16 P4 P5 P6 P9 assms(1) by auto
    next
      assume T1: "A' \<noteq> B"
      have T2: "B A' P CongA B A' P'"
      proof -
        have T2A: "Cong B P B P'"
          using assms(3) col_trivial_2 is_image_spec_col_cong l10_4_spec not_cong_4321 by blast
        then have T2B: "A' B P CongA A' B P'"
          by (metis Cong_perm Midpoint_def P1 P5 T1 Tarski_neutral_dimensionless.l11_51 Tarski_neutral_dimensionless_axioms assms(2) cong_reflexivity)
        have "A' P B CongA A' P' B"
          by (simp add: P5 T2A T2B cong_reflexivity conga_comm l11_49)
        thus ?thesis
          using P5 T2A T2B cong_reflexivity l11_49 by blast
      qed
      have T3: "Cong A' B A' B"
        by (simp add: cong_reflexivity)
      have "Cong A' P A' P'"
        using Midpoint_def P1 not_cong_4312 by blast
      then have T4: "A' B P CongA A' B P' \<and> A' P B CongA A' P' B" using l11_49
        using assms(2) T2 T3 by blast
      show ?thesis
      proof cases
        assume "Bet A' B A"
        thus ?thesis
          using T4 assms(1) l11_13 by blast
      next
        assume "\<not> Bet A' B A"
        then have T5: "B Out A' A"
          using P1 not_col_permutation_3 or_bet_out by blast
        have T6: "B \<noteq> P'"
          using T4 conga_distinct by blast
        have T8: "B Out A A'"
          by (simp add: T5 l6_6)
        have T9: "B Out P P"
          using assms(2) out_trivial by auto
        have "B Out P' P'"
          using T6 out_trivial by auto
        thus ?thesis
          using l11_10 T4 T8 T9 by blast
      qed
    qed
  }
  {
    assume "P = P'"
    then have "A B P CongA A B P'"
      using assms(1) assms(2) conga_refl by auto
  }
  thus ?thesis
    using P1 \<open>A B Perp P' P \<Longrightarrow> A B P CongA A B P'\<close> by blast
qed

lemma conga_cop_out_reflectl__out:
  assumes "\<not> B Out A C" and
    "Coplanar A B C P" and
    "P B A CongA P B C" and
    "B Out A T" and
    "T T' ReflectL B P"
  shows "B Out C T'"
proof -
  have P1: "P B T CongA P B T'"
    by (metis assms(3) assms(4) assms(5) conga_distinct is_image_spec_rev out_distinct reflectl__conga)
  have P2: "T T' Reflect B P"
    by (metis P1 assms(5) conga_distinct is_image_is_image_spec)
  have P3: "B \<noteq> T'"
    using CongA_def P1 by blast
  have P4: "P B C CongA P B T'"
  proof -
    have P5: "P B C CongA P B A"
      by (simp add: assms(3) conga_sym)
    have "P B A CongA P B T'"
    proof -
      have P7: "B Out P P"
        using assms(3) conga_diff45 out_trivial by blast
      have P8: "B Out A T"
        by (simp add: assms(4))
      have "B Out T' T'"
        using P3 out_trivial by auto
      thus ?thesis
        using P1 P7 P8 l11_10 by blast
    qed
    thus ?thesis
      using P5 not_conga by blast
  qed
  have "P B OS C T'"
  proof -
    have P9: "P B TS A C"
      using assms(1) assms(2) assms(3) conga_cop__or_out_ts coplanar_perm_20 by blast
    then have "T \<noteq> T'"
      by (metis Col_perm P2 P3 TS_def assms(4) col_transitivity_2 l10_8 out_col)
    then have "P B TS T T'"
      by (metis P2 P4 conga_diff45 invert_two_sides l10_14)
    then have "P B TS A T'"
      using assms(4) col_trivial_2 out_two_sides_two_sides by blast
    thus ?thesis
      using OS_def P9 l9_2 by blast
  qed
  thus ?thesis
    using P4 conga_os__out by auto
qed

lemma col_conga_cop_reflectl__col:
  assumes "\<not> B Out A C" and
    "Coplanar A B C P" and
    "P B A CongA P B C" and
    "Col B A T" and
    "T T' ReflectL B P"
  shows "Col B C T'"
proof cases
  assume "B = T"
  thus ?thesis
    using assms(5) col_image_spec__eq not_col_distincts by blast
next
  assume P1: "B \<noteq> T"
  thus ?thesis
  proof cases
    assume "B Out A T"
    thus ?thesis
      using out_col conga_cop_out_reflectl__out assms(1) assms(2) assms(3) assms(5) by blast
  next
    assume P2: "\<not> B Out A T"
    obtain A' where P3: "Bet A B A' \<and> Cong B A' A B"
      using segment_construction by blast
    obtain C' where P4: "Bet C B C' \<and> Cong B C' C B"
      using segment_construction by blast
    have P5: "B Out C' T'"
    proof -
      have P6: "\<not> B Out A' C'"
        by (metis P3 P4 assms(1) between_symmetry cong_diff_2 l6_2 out_diff1 out_diff2)
      have P7: "Coplanar A' B C' P"
      proof cases
        assume "Col A B C"
        thus ?thesis
          by (smt P3 P4 assms(1) assms(2) assms(3) bet_col bet_neq32__neq col2_cop__cop col_transitivity_1 colx conga_diff2 conga_diff56 l6_4_2 ncoplanar_perm_15 not_col_permutation_5)
      next
        assume P7B: "\<not> Col A B C"
        have P7C: "Coplanar A B C A'"
          using P3 bet_col ncop__ncols by blast
        have P7D: "Coplanar A B C B"
          using ncop_distincts by blast
        have "Coplanar A B C C'"
          using P4 bet__coplanar coplanar_perm_20 by blast
        thus ?thesis
          using P7B P7C P7D assms(2) coplanar_pseudo_trans by blast
      qed
      have P8: "P B A' CongA P B C'"
        by (metis CongA_def P3 P4 assms(3) cong_reverse_identity conga_left_comm l11_13 not_conga_sym)
      have P9: "B Out A' T"
        by (smt Out_def P1 P2 P3 P8 assms(3) assms(4) conga_distinct l5_2 l6_4_2 not_col_permutation_4)
      thus ?thesis
        using P6 P7 P8 P9 assms(5) conga_cop_out_reflectl__out by blast
    qed
    thus ?thesis
      by (metis Col_def P4 col_transitivity_1 out_col out_diff1)
  qed
qed

lemma conga2_cop2__col:
  assumes "\<not> B Out A C" and
    "P B A CongA P B C" and
    "P' B A CongA P' B C" and
    "Coplanar A B P P'" and
    "Coplanar B C P P'"
  shows "Col B P P'"
proof -
  obtain C' where P1: "B Out C' C \<and> Cong B C' B A"
    by (metis assms(2) conga_distinct l6_11_existence)
  have P1A: "Cong P A P C' \<and> (P \<noteq> A \<longrightarrow> (B P A CongA B P C' \<and> B A P CongA B C' P))"
  proof -
    have P2: "P B A CongA P B C'"
    proof -
      have P2A: "B Out P P"
        using assms(2) conga_diff45 out_trivial by auto
      have "B Out A A"
        using assms(2) conga_distinct out_trivial by auto
      thus ?thesis
        using P1 P2A assms(2) l11_10 by blast
    qed
    have P3: "Cong B P B P"
      by (simp add: cong_reflexivity)
    have "Cong B A B C'"
      using Cong_perm P1 by blast
    thus ?thesis using l11_49 P2 cong_reflexivity by blast
  qed
  have P4: "P' B A CongA P' B C'"
  proof -
    have P4A: "B Out P' P'"
      using assms(3) conga_diff1 out_trivial by auto
    have "B Out A A"
      using assms(2) conga_distinct out_trivial by auto
    thus ?thesis
      using P1 P4A assms(3) l11_10 by blast
  qed
  have P5: "Cong B P' B P'"
    by (simp add: cong_reflexivity)
  have P5A: "Cong B A B C'"
    using Cong_perm P1 by blast
  then have P6: "P' \<noteq> A \<longrightarrow> (B P' A CongA B P' C' \<and> B A P' CongA B C' P')"
    using P4 P5 l11_49 by blast
  have P7: "Coplanar B P P' A"
    using assms(4) ncoplanar_perm_18 by blast
  have P8: "Coplanar B P P' C'"
    by (smt Col_cases P1 assms(5) col_cop__cop ncoplanar_perm_16 ncoplanar_perm_8 out_col out_diff2)
  have "A \<noteq> C'"
    using P1 assms(1) by auto
  thus ?thesis
    using P4 P5 P7 P8 P5A P1A cong3_cop2__col l11_49 by blast
qed

lemma conga2_cop2__col_1:
  assumes "\<not> Col A B C" and
    "P B A CongA P B C" and
    "P' B A CongA P' B C" and
    "Coplanar A B C P" and
    "Coplanar A B C P'"
  shows "Col B P P'"
proof -
  have P1: "\<not> B Out A C"
    using Col_cases assms(1) out_col by blast
  have P2: "Coplanar A B P P'"
    by (meson assms(1) assms(4) assms(5) coplanar_perm_12 coplanar_trans_1 not_col_permutation_2)
  have "Coplanar B C P P'"
    using assms(1) assms(4) assms(5) coplanar_trans_1 by auto
  thus ?thesis using P1 P2 conga2_cop2__col assms(2) assms(3) conga2_cop2__col by auto
qed

lemma col_conga__conga:
  assumes "P B A CongA P B C" and
    "Col B P P'" and
    "B \<noteq> P'"
  shows "P' B A CongA P' B C"
proof cases
  assume "Bet P B P'"
  thus ?thesis
    using assms(1) assms(3) l11_13 by blast
next
  assume "\<not> Bet P B P'"
  then have P1: "B Out P P'"
    using Col_cases assms(2) or_bet_out by blast
  then have P2: "B Out P' P"
    by (simp add: l6_6)
  have P3: "B Out A A"
    using CongA_def assms(1) out_trivial by auto
  have "B Out C C"
    using assms(1) conga_diff56 out_trivial by blast
  thus ?thesis
    using P2 P3 assms(1) l11_10 by blast
qed

lemma cop_inangle__ex_col_inangle:
  assumes "\<not> B Out A C" and
    "P InAngle A B C" and
    "Coplanar A B C Q"
  shows "\<exists> R. (R InAngle A B C \<and> P \<noteq> R \<and> Col P Q R)"
proof -
  have P1: "A \<noteq> B"
    using assms(2) inangle_distincts by blast
  then have P4: "A \<noteq> C"
    using assms(1) out_trivial by blast
  have P2: "C \<noteq> B"
    using assms(2) inangle_distincts by auto
  have P3: "P \<noteq> B"
    using InAngle_def assms(2) by auto
  thus ?thesis
  proof cases
    assume "P = Q"
    thus ?thesis
      using P1 P2 P4 col_trivial_1 inangle1123 inangle3123 by blast
  next
    assume P5: "P \<noteq> Q"
    thus ?thesis
    proof cases
      assume P6: "Col B P Q"
      obtain R where P7: "Bet B P R \<and> Cong P R B P"
        using segment_construction by blast
      have P8: "R InAngle A B C"
        using Out_cases P1 P2 P3 P7 assms(2) bet_out l11_25 out_trivial by blast
      have "P \<noteq> R"
        using P3 P7 cong_reverse_identity by blast
      thus ?thesis
        by (metis P3 P6 P7 P8 bet_col col_transitivity_2)
    next
      assume T1: "\<not> Col B P Q"
      thus ?thesis
      proof cases
        assume T2: "Col A B C"
        have T3: "Q InAngle A B C"
          by (metis P1 P2 T1 T2 assms(1) in_angle_line l6_4_2 not_col_distincts)
        thus ?thesis
          using P5 col_trivial_2 by blast
      next
        assume Q1: "\<not> Col A B C"
        thus ?thesis
        proof cases
          assume Q2: "Col B C P"
          have Q3: "\<not> Col B A P"
            using Col_perm P3 Q1 Q2 col_transitivity_2 by blast
          have Q4: "Coplanar B P Q A"
            using P2 Q2 assms(3) col2_cop__cop col_trivial_3 ncoplanar_perm_22 ncoplanar_perm_3 by blast
          have Q5: "Q \<noteq> P"
            using P5 by auto
          have Q6: "Col B P P"
            using not_col_distincts by blast
          have Q7: "Col Q P P"
            using not_col_distincts by auto
          have "\<not> Col B P A"
            using Col_cases Q3 by auto
          then obtain Q0 where P10: "Col Q P Q0 \<and> B P OS A Q0"
            using cop_not_par_same_side Q4 Q5 Q6 Q7 T1 by blast
          have P13: "P \<noteq> Q0"
            using P10 os_distincts by auto
          {
            assume "B A OS P Q0"
            then have ?thesis
              using P10 P13 assms(2) in_angle_trans not_col_permutation_4 os2__inangle by blast
          }
          {
            assume V1: "\<not> B A OS P Q0"
            have "\<exists> R. Bet P R Q0 \<and> Col P Q R \<and> Col B A R"
            proof cases
              assume V3: "Col B A Q0"
              have "Col P Q Q0"
                using Col_cases P10 by auto
              thus ?thesis
                using V3 between_trivial by auto
            next
              assume V4: "\<not> Col B A Q0"
              then have V5: "\<not> Col Q0 B A"
                using Col_perm by blast
              have "\<not> Col P B A"
                using Col_cases Q3 by blast
              then obtain R where V8: "Col R B A \<and> Bet P R Q0"
                using cop_nos__ts V1 V5
                by (meson P10 TS_def ncoplanar_perm_2 os__coplanar)
              thus ?thesis
                by (metis Col_def P10 P13 col_transitivity_2)
            qed
            then obtain R where V9: "Bet P R Q0 \<and> Col P Q R \<and> Col B A R" by auto
            have V10: "P \<noteq> R"
              using Q3 V9 by blast
            have "R InAngle A B C"
            proof -
              have W1: "\<not> Col B P Q0"
                using P10 P13 T1 col2__eq by blast
              have "P Out Q0 R"
                using V10 V9 bet_out l6_6 by auto
              then have "B P OS Q0 R"
                using Q6 W1 out_one_side_1 by blast
              then have "B P OS A R"
                using P10 one_side_transitivity by blast
              then have "B Out A R"
                using V9 col_one_side_out by auto
              thus ?thesis
                by (simp add: P2 out321__inangle)
            qed
            then have ?thesis
              using V10 V9 by blast
          }
          thus ?thesis
            using \<open>B A OS P Q0 \<Longrightarrow> \<exists>R. R InAngle A B C \<and> P \<noteq> R \<and> Col P Q R\<close> by blast
        next
          assume Z1: "\<not> Col B C P"
          then have Z6: "\<not> Col B P C"
            by (simp add: not_col_permutation_5)
          have Z3: "Col B P P"
            by (simp add: col_trivial_2)
          have Z4: "Col Q P P"
            by (simp add: col_trivial_2)
          have "Coplanar A B C P"
            using Q1 assms(2) inangle__coplanar ncoplanar_perm_18 by blast
          then have "Coplanar B P Q C"
            using Q1 assms(3) coplanar_trans_1 ncoplanar_perm_5 by blast
          then obtain Q0 where Z5: "Col Q P Q0 \<and> B P OS C Q0"
            using cop_not_par_same_side by (metis Z3 Z4 T1 Z6)
          thus ?thesis
          proof cases
            assume "B C OS P Q0"
            thus ?thesis
            proof -
              have "\<forall>p. p InAngle C B A \<or> \<not> p InAngle C B P"
                using assms(2) in_angle_trans l11_24 by blast
              then show ?thesis
                by (metis Col_perm Z5 \<open>B C OS P Q0\<close> l11_24 os2__inangle os_distincts)
            qed
          next
            assume Z6: "\<not> B C OS P Q0"
            have Z7: "\<exists> R. Bet P R Q0 \<and> Col P Q R \<and> Col B C R"
            proof cases
              assume "Col B C Q0"
              thus ?thesis
                using Col_def Col_perm Z5 between_trivial by blast
            next
              assume Z8: "\<not> Col B C Q0"
              have "\<exists> R. Col R B C \<and> Bet P R Q0"
              proof -
                have Z10: "Coplanar B C P Q0"
                  using Z5 ncoplanar_perm_2 os__coplanar by blast
                have Z11: "\<not> Col P B C"
                  using Col_cases Z1 by blast
                have "\<not> Col Q0 B C"
                  using Col_perm Z8 by blast
                thus ?thesis
                  using cop_nos__ts Z6 Z10 Z11 by (simp add: TS_def)
              qed
              then obtain R where "Col R B C \<and> Bet P R Q0" by blast
              thus ?thesis
                by (smt Z5 bet_col col2__eq col_permutation_1 os_distincts)
            qed
            then obtain R where Z12: "Bet P R Q0 \<and> Col P Q R \<and> Col B C R" by blast
            have Z13: "P \<noteq> R"
              using Z1 Z12 by auto
            have Z14: "\<not> Col B P Q0"
              using Z5 one_side_not_col124 by blast
            have "P Out Q0 R"
              using Z12 Z13 bet_out l6_6 by auto
            then have "B P OS Q0 R"
              using Z14 Z3 out_one_side_1 by blast
            then have "B P OS C R"
              using Z5 one_side_transitivity by blast
            then have "B Out C R"
              using Z12 col_one_side_out by blast
            then have "R InAngle A B C"
              using P1 out341__inangle by auto
            thus ?thesis
              using Z12 Z13 by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma col_inangle2__out:
  assumes "\<not> Bet A B C" and
    "P InAngle A B C" and
    "Q InAngle A B C" and
    "Col B P Q"
  shows "B Out P Q"
proof cases
  assume "Col A B C"
  thus ?thesis
    by (meson assms(1) assms(2) assms(3) assms(4) bet_in_angle_bet bet_out__bet in_angle_out l6_6 not_col_permutation_4 or_bet_out)
next
  assume P1: "\<not> Col A B C"
  thus ?thesis
  proof cases
    assume "Col B A P"
    thus ?thesis
      by (meson assms(1) assms(2) assms(3) assms(4) bet_in_angle_bet bet_out__bet l6_6 not_col_permutation_4 or_bet_out)
  next
    assume P2: "\<not> Col B A P"
    have "\<not> Col B A Q"
      using P2 assms(3) assms(4) col2__eq col_permutation_4 inangle_distincts by blast
    then have "B A OS P Q"
      using P1 P2 assms(2) assms(3) inangle_one_side invert_one_side not_col_permutation_4 by auto
    thus ?thesis
      using assms(4) col_one_side_out by auto
  qed
qed

lemma inangle2__lea:
  assumes "P InAngle A B C" and
    "Q InAngle A B C"
  shows "P B Q LeA A B C"
proof -
  have P1: "P InAngle C B A"
    by (simp add: assms(1) l11_24)
  have P2: "Q InAngle C B A"
    by (simp add: assms(2) l11_24)
  have P3: "A \<noteq> B"
    using assms(1) inangle_distincts by auto
  have P4: "C \<noteq> B"
    using assms(1) inangle_distincts by blast
  have P5: "P \<noteq> B"
    using assms(1) inangle_distincts by auto
  have P6: "Q \<noteq> B"
    using assms(2) inangle_distincts by auto
  thus ?thesis
  proof cases
    assume P7: "Col A B C"
    thus ?thesis
    proof cases
      assume "Bet A B C"
      thus ?thesis
        by (simp add: P3 P4 P5 P6 l11_31_2)
    next
      assume "\<not> Bet A B C"
      then have "B Out A C"
        using P7 not_out_bet by blast
      then have "B Out P Q"
        using Out_cases assms(1) assms(2) in_angle_out l6_7 by blast
      thus ?thesis
        by (simp add: P3 P4 l11_31_1)
    qed
  next
    assume T1: "\<not> Col A B C"
    thus ?thesis
    proof cases
      assume T2: "Col B P Q"
      have "\<not> Bet A B C"
        using T1 bet_col by auto
      then have "B Out P Q"
        using T2 assms(1) assms(2) col_inangle2__out by auto
      thus ?thesis
        by (simp add: P3 P4 l11_31_1)
    next
      assume T3: "\<not> Col B P Q"
      thus ?thesis
      proof cases
        assume "Col B A P"
        then have "B Out A P"
          using Col_def T1 assms(1) col_in_angle_out by blast
        then have "P B Q CongA A B Q"
          using P6 out2__conga out_trivial by auto
        thus ?thesis
          using LeA_def assms(2) by blast
      next
        assume W0: "\<not> Col B A P"
        show ?thesis
        proof cases
          assume "Col B C P"
          then have "B Out C P"
            by (metis P1 P3 T1 bet_out_1 col_in_angle_out out_col)
          thus ?thesis
            by (smt P3 P4 P6 Tarski_neutral_dimensionless.lea_left_comm Tarski_neutral_dimensionless.lea_out4__lea Tarski_neutral_dimensionless_axioms assms(2) inangle__lea_1 out_trivial)
        next
          assume W0A: "\<not> Col B C P"
          show ?thesis
          proof cases
            assume "Col B A Q"
            then have "B Out A Q"
              using Col_def T1 assms(2) col_in_angle_out by blast
            thus ?thesis
              by (smt P3 P4 P5 Tarski_neutral_dimensionless.lea_left_comm Tarski_neutral_dimensionless.lea_out4__lea Tarski_neutral_dimensionless_axioms assms(1) inangle__lea out_trivial)
          next
            assume W0AA: "\<not> Col B A Q"
            thus ?thesis
            proof cases
              assume "Col B C Q"
              then have "B Out C Q"
                using Bet_cases P2 T1 bet_col col_in_angle_out by blast
              thus ?thesis
                by (smt P1 P3 P4 P5 Tarski_neutral_dimensionless.lea_comm Tarski_neutral_dimensionless.lea_out4__lea Tarski_neutral_dimensionless_axioms inangle__lea out_trivial)
            next
              assume W0B: "\<not> Col B C Q"
              have W1: "Coplanar B P A Q"
                by (metis Col_perm T1 assms(1) assms(2) col__coplanar inangle_one_side ncoplanar_perm_13 os__coplanar)
              have W2: "\<not> Col A B P"
                by (simp add: W0 not_col_permutation_4)
              have W3: "\<not> Col Q B P"
                using Col_perm T3 by blast
              then have W4: "B P TS A Q \<or> B P OS A Q"
                using cop__one_or_two_sides
                by (simp add: W1 W2)
              {
                assume W4A: "B P TS A Q"
                have "Q InAngle P B C"
                proof -
                  have W5: "P B OS C Q"
                    using OS_def P1 W0 W0A W4A in_angle_two_sides invert_two_sides l9_2 by blast
                  have "C B OS P Q"
                    by (meson P1 P2 T1 W0A W0B inangle_one_side not_col_permutation_3 not_col_permutation_4)
                  thus ?thesis
                    by (simp add: W5 invert_one_side os2__inangle)
                qed
                then have "P B Q LeA A B C"
                  by (meson assms(1) inangle__lea inangle__lea_1 lea_trans)
              }
              {
                assume W6: "B P OS A Q"
                have "B A OS P Q"
                  using Col_perm T1 W2 W0AA assms(1) assms(2) inangle_one_side invert_one_side by blast
                then have "Q InAngle P B A"
                  by (simp add: W6 os2__inangle)
                then have "P B Q LeA A B C"
                  by (meson P1 inangle__lea inangle__lea_1 lea_right_comm lea_trans)
              }
              thus ?thesis
                using W4 \<open>B P TS A Q \<Longrightarrow> P B Q LeA A B C\<close> by blast
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma conga_inangle_per__acute:
  assumes "Per A B C" and
    "P InAngle A B C" and
    "P B A CongA P B C"
  shows "Acute A B P"
proof -
  have P1: "\<not> Col A B C"
    using assms(1) assms(3) conga_diff2 conga_diff56 l8_9 by blast
  have P2: "A B P LeA A B C"
    by (simp add: assms(2) inangle__lea)
  {
    assume "A B P CongA A B C"
    then have P3: "Per A B P"
      by (meson Tarski_neutral_dimensionless.l11_17 Tarski_neutral_dimensionless.not_conga_sym Tarski_neutral_dimensionless_axioms assms(1))
    have P4: "Coplanar P C A B"
      using assms(2) inangle__coplanar ncoplanar_perm_3 by blast
    have P5: "P \<noteq> B"
      using assms(2) inangle_distincts by blast
    have "Per C B P"
      using P3 Per_cases assms(3) l11_17 by blast
    then have "False"
      using P1 P3 P4 P5 col_permutation_1 cop_per2__col by blast
  }
  then have "\<not> A B P CongA A B C" by auto
  then have "A B P LtA A B C"
    by (simp add: LtA_def P2)
  thus ?thesis
    using Acute_def assms(1) by blast
qed

lemma conga_inangle2_per__acute:
  assumes "Per A B C" and
    "P InAngle A B C" and
    "P B A CongA P B C" and
    "Q InAngle A B C"
  shows "Acute P B Q"
proof -
  have P1: "P InAngle C B A"
    using assms(2) l11_24 by auto
  have P2: "Q InAngle C B A"
    using assms(4) l11_24 by blast
  have P3: "A \<noteq> B"
    using assms(3) conga_diff2 by auto
  have P5: "P \<noteq> B"
    using assms(2) inangle_distincts by blast
  have P7: "\<not> Col A B C"
    using assms(1) assms(3) conga_distinct l8_9 by blast
  have P8: "Acute A B P"
    using assms(1) assms(2) assms(3) conga_inangle_per__acute by auto
  {
    assume "Col P B A"
    then have "Col P B C"
      using assms(3) col_conga_col by blast
    then have "False"
      using Col_perm P5 P7 \<open>Col P B A\<close> col_transitivity_2 by blast
  }
  then have P9: "\<not> Col P B A" by auto
  have P10: "\<not> Col P B C"
    using \<open>Col P B A \<Longrightarrow> False\<close> assms(3) ncol_conga_ncol by blast
  have P11: "\<not> Bet A B C"
    using P7 bet_col by blast
  show ?thesis
  proof cases
    assume "Col B A Q"
    then have "B Out A Q"
      using P11 assms(4) col_in_angle_out by auto
    thus ?thesis
      using Out_cases P5 P8 acute_out2__acute acute_sym out_trivial by blast
  next
    assume S0: "\<not> Col B A Q"
    show ?thesis
    proof cases
      assume S1: "Col B C Q"
      then have "B Out C Q"
        using P11 P2 between_symmetry col_in_angle_out by blast
      then have S2: "B Out Q C"
        using l6_6 by blast
      have S3: "B Out P P"
        by (simp add: P5 out_trivial)
      have "B Out A A"
        by (simp add: P3 out_trivial)
      then have "A B P CongA P B Q"
        using S2 conga_left_comm l11_10 S3 assms(3) by blast
      thus ?thesis
        using P8 acute_conga__acute by blast
    next
      assume S4: "\<not> Col B C Q"
      show ?thesis
      proof cases
        assume "Col B P Q"
        thus ?thesis
          using out__acute col_inangle2__out P11 assms(2) assms(4) by blast
      next
        assume S5: "\<not> Col B P Q"
        have S6: "Coplanar B P A Q"
          by (metis Col_perm P7 assms(2) assms(4) coplanar_trans_1 inangle__coplanar ncoplanar_perm_12 ncoplanar_perm_21)
        have S7: "\<not> Col A B P"
          using Col_cases P9 by auto
        have "\<not> Col Q B P"
          using Col_perm S5 by blast
        then have S8: "B P TS A Q \<or> B P OS A Q"
          using cop__one_or_two_sides S6 S7 by blast
        {
          assume S9: "B P TS A Q"
          have S10: "Acute P B C"
            using P8 acute_conga__acute acute_sym assms(3) by blast
          have "Q InAngle P B C"
          proof -
            have S11: "P B OS C Q"
              by (metis Col_perm OS_def P1 P10 P9 S9 in_angle_two_sides invert_two_sides l9_2)
            have "C B OS P Q"
              by (meson P1 P10 P2 P7 S4 inangle_one_side not_col_permutation_3 not_col_permutation_4)
            thus ?thesis
              by (simp add: S11 invert_one_side os2__inangle)
          qed
          then have "P B Q LeA P B C"
            by (simp add: inangle__lea)
          then have "Acute P B Q"
            using S10 acute_lea_acute by blast
        }
        {
          assume S12: "B P OS A Q"
          have "B A OS P Q"
            using Col_perm P7 S7 S0 assms(2) assms(4) inangle_one_side invert_one_side by blast
          then have "Q InAngle P B A"
            by (simp add: S12 os2__inangle)
          then have "Q B P LeA P B A"
            by (simp add: P3 P5 inangle1123 inangle2__lea)
          then have "P B Q LeA A B P"
            by (simp add: lea_comm)
          then have "Acute P B Q"
            using P8 acute_lea_acute by blast
        }
        thus ?thesis
          using \<open>B P TS A Q \<Longrightarrow> Acute P B Q\<close> S8 by blast
      qed
    qed
  qed
qed

lemma lta_os__ts:
  assumes (*"\<not> Col A O1 P" and*)
    "A O1 P LtA A O1 B" and
    "O1 A OS B P"
  shows "O1 P TS A B"
proof -
  have "A O1 P LeA A O1 B"
    by (simp add: assms(1) lta__lea)
  then have "\<exists> P0. P0 InAngle A O1 B \<and> A O1 P CongA A O1 P0"
    by (simp add: LeA_def)
  then obtain P' where P1: "P' InAngle A O1 B \<and> A O1 P CongA A O1 P'" by blast
  have P2: "\<not> Col A O1 B"
    using assms(2) col123__nos not_col_permutation_4 by blast
  obtain R where P3: "O1 A TS B R \<and> O1 A TS P R"
    using OS_def assms(2) by blast
  {
    assume "Col B O1 P"
    then have "Bet B O1 P"
      by (metis Tarski_neutral_dimensionless.out2__conga Tarski_neutral_dimensionless_axioms assms(1) assms(2) between_trivial col_trivial_2 lta_not_conga one_side_chara or_bet_out out_trivial)
    then have "O1 A TS B P"
      using assms(2) col_trivial_1 one_side_chara by blast
    then have P6: "\<not> O1 A OS B P"
      using l9_9_bis by auto
    then have "False"
      using P6 assms(2) by auto
  }
  then have P4: "\<not> Col B O1 P" by auto
  thus ?thesis
    by (meson P3 assms(1) inangle__lta l9_8_1 not_and_lta not_col_permutation_4 os_ts__inangle two_sides_cases)
qed

lemma bet__suppa:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "B \<noteq> A'" and
    "Bet A B A'"
  shows "A B C SuppA C B A'"
proof -
  have "C B A' CongA C B A'"
    using assms(2) assms(3) conga_refl by auto
  thus ?thesis using assms(4) assms(1) SuppA_def by auto
qed

lemma ex_suppa:
  assumes "A \<noteq> B" and
    "B \<noteq> C"
  shows "\<exists> D E F. A B C SuppA D E F"
proof -
  obtain A' where "Bet A B A' \<and> Cong B A' A B"
    using segment_construction by blast
  thus ?thesis
    by (meson assms(1) assms(2) bet__suppa point_construction_different)
qed

lemma suppa_distincts:
  assumes "A B C SuppA D E F"
  shows "A \<noteq> B \<and> B \<noteq> C \<and> D \<noteq> E \<and> E \<noteq> F"
  using CongA_def SuppA_def assms by auto

lemma suppa_right_comm:
  assumes "A B C SuppA D E F"
  shows "A B C SuppA F E D"
  using SuppA_def assms conga_left_comm by auto

lemma suppa_left_comm:
  assumes "A B C SuppA D E F"
  shows "C B A SuppA D E F"
proof -
  obtain A' where P1: "Bet A B A' \<and> D E F CongA C B A'"
    using SuppA_def assms by auto
  obtain C' where P2: "Bet C B C' \<and> Cong B C' C B"
    using segment_construction by blast
  then have "C B A' CongA A B C'"
    by (metis Bet_cases P1 SuppA_def assms cong_diff_3 conga_diff45 conga_diff56 conga_left_comm l11_14)
  then have "D E F CongA A B C'"
    using P1 conga_trans by blast
  thus ?thesis
    by (metis CongA_def P1 P2 SuppA_def)
qed

lemma suppa_comm:
  assumes "A B C SuppA D E F"
  shows "C B A SuppA F E D"
  using assms suppa_left_comm suppa_right_comm by blast

lemma suppa_sym:
  assumes "A B C SuppA D E F"
  shows "D E F SuppA A B C"
proof -
  obtain A' where P1: "Bet A B A' \<and> D E F CongA C B A'"
    using SuppA_def assms by auto
  obtain D' where P2: "Bet D E D' \<and> Cong E D' D E"
    using segment_construction by blast
  have "A' B C CongA D E F"
    using P1 conga_right_comm not_conga_sym by blast
  then have "A B C CongA F E D'"
    by (metis P1 P2 Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless.l11_13 Tarski_neutral_dimensionless.suppa_distincts Tarski_neutral_dimensionless_axioms assms between_symmetry cong_diff_3)
  thus ?thesis
    by (metis CongA_def P1 P2 SuppA_def)
qed

lemma conga2_suppa__suppa:
  assumes "A B C CongA A' B' C'" and
    "D E F CongA D' E' F'" and
    "A B C SuppA D E F"
  shows "A' B' C' SuppA D' E' F'"
proof -
  obtain A0 where P1: "Bet A B A0 \<and> D E F CongA C B A0"
    using SuppA_def assms(3) by auto
  then have "A B C SuppA D' E' F'"
    by (metis Tarski_neutral_dimensionless.SuppA_def Tarski_neutral_dimensionless_axioms assms(2) assms(3) conga_sym conga_trans)
  then have P2: "D' E' F' SuppA A B C"
    by (simp add: suppa_sym)
  then obtain D0 where P3: "Bet D' E' D0 \<and> A B C CongA F' E' D0"
    using P2 SuppA_def by auto
  have P5: "A' B' C' CongA F' E' D0"
    using P3 assms(1) not_conga not_conga_sym by blast
  then have "D' E' F' SuppA A' B' C'"
    using P2 P3 SuppA_def by auto
  thus ?thesis
    by (simp add: suppa_sym)
qed

lemma suppa2__conga456:
  assumes "A B C SuppA D E F" and
    "A B C SuppA D' E' F'"
  shows "D E F CongA D' E' F'"
proof -
  obtain A' where P1: "Bet A B A' \<and> D E F CongA C B A'"
    using SuppA_def assms(1) by auto
  obtain A'' where P2: "Bet A B A'' \<and> D' E' F' CongA C B A''"
    using SuppA_def assms(2) by auto
  have "C B A' CongA C B A''"
  proof -
    have P3: "B Out C C" using P1
      by (simp add: CongA_def out_trivial)
    have "B Out A'' A'" using P1 P2 l6_2
      by (metis assms(1) between_symmetry conga_distinct suppa_distincts)
    thus ?thesis
      by (simp add: P3 out2__conga)
  qed
  then have "C B A' CongA D' E' F'"
    using P2 not_conga not_conga_sym by blast
  thus ?thesis
    using P1 not_conga by blast
qed

lemma suppa2__conga123:
  assumes "A B C SuppA D E F" and
    "A' B' C' SuppA D E F"
  shows "A B C CongA A' B' C'"
  using assms(1) assms(2) suppa2__conga456 suppa_sym by blast

lemma bet_out__suppa:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Bet A B C" and
    "E Out D F"
  shows "A B C SuppA D E F"
proof -
  have "D E F CongA C B C"
    using assms(2) assms(4) l11_21_b out_trivial by auto
  thus ?thesis
    using SuppA_def assms(1) assms(3) by blast
qed

lemma bet_suppa__out:
  assumes "Bet A B C" and
    "A B C SuppA D E F"
  shows "E Out D F"
proof -
  have "A B C SuppA C B C"
    using assms(1) assms(2) bet__suppa suppa_distincts by auto
  then have "C B C CongA D E F"
    using assms(2) suppa2__conga456 by auto
  thus ?thesis
    using eq_conga_out by auto
qed

lemma out_suppa__bet:
  assumes "B Out A C" and
    "A B C SuppA D E F"
  shows "Bet D E F"
proof -
  obtain B' where P1: "Bet A B B' \<and> Cong B B' A B"
    using segment_construction by blast
  have "A B C SuppA A B B'"
    by (metis P1 assms(1) assms(2) bet__suppa bet_cong_eq bet_out__bet suppa_distincts suppa_left_comm)
  then have "A B B' CongA D E F"
    using assms(2) suppa2__conga456 by auto
  thus ?thesis
    using P1 bet_conga__bet by blast
qed

lemma per_suppa__per:
  assumes  "Per A B C" and
    "A B C SuppA D E F"
  shows "Per D E F"
proof -
  obtain A' where P1: "Bet A B A' \<and> D E F CongA C B A'"
    using SuppA_def assms(2) by auto
  have "Per C B A'"
  proof -
    have P2: "A \<noteq> B"
      using assms(2) suppa_distincts by auto
    have P3: "Per C B A"
      by (simp add: assms(1) l8_2)
    have "Col B A A'"
      using P1 Col_cases Col_def by blast
    thus ?thesis
      by (metis P2 P3 per_col)
  qed
  thus ?thesis
    using P1 l11_17 not_conga_sym by blast
qed

lemma per2__suppa:
  assumes  "A \<noteq> B" and
    "B \<noteq> C" and
    "D \<noteq> E" and
    "E \<noteq> F" and
    "Per A B C" and
    "Per D E F"
  shows "A B C SuppA D E F"
proof -
  obtain D' E' F' where P1: "A B C SuppA D' E' F'"
    using assms(1) assms(2) ex_suppa by blast
  have "D' E' F' CongA D E F"
    using P1 assms(3) assms(4) assms(5) assms(6) l11_16 per_suppa__per suppa_distincts by blast
  thus ?thesis
    by (meson P1 conga2_suppa__suppa suppa2__conga123)
qed

lemma suppa__per:
  assumes "A B C SuppA A B C"
  shows "Per A B C"
proof -
  obtain A' where P1: "Bet A B A' \<and> A B C CongA C B A'"
    using SuppA_def assms by auto
  then have "C B A CongA C B A'"
    by (simp add: conga_left_comm)
  thus ?thesis
    using P1 Per_perm l11_18_2 by blast
qed

lemma acute_suppa__obtuse:
  assumes "Acute A B C" and
    "A B C SuppA D E F"
  shows "Obtuse D E F"
proof -
  obtain A' where P1: "Bet A B A' \<and> D E F CongA C B A'"
    using SuppA_def assms(2) by auto
  then have "Obtuse C B A'"
    by (metis Tarski_neutral_dimensionless.obtuse_sym Tarski_neutral_dimensionless_axioms acute_bet__obtuse assms(1) conga_distinct)
  thus ?thesis
    by (meson P1 Tarski_neutral_dimensionless.conga_obtuse__obtuse Tarski_neutral_dimensionless.not_conga_sym Tarski_neutral_dimensionless_axioms)
qed

lemma obtuse_suppa__acute:
  assumes "Obtuse A B C" and
    "A B C SuppA D E F"
  shows "Acute D E F"
proof -
  obtain A' where P1: "Bet A B A' \<and> D E F CongA C B A'"
    using SuppA_def assms(2) by auto
  then have "Acute C B A'"
    using acute_sym assms(1) bet_obtuse__acute conga_distinct by blast
  thus ?thesis
    using P1 acute_conga__acute not_conga_sym by blast
qed

lemma lea_suppa2__lea:
  assumes "A B C SuppA A' B' C'" and
    "D E F SuppA D' E' F'"
    "A B C LeA D E F"
  shows "D' E' F' LeA A' B' C'"
proof -
  obtain A0 where P1: "Bet A B A0 \<and> A' B' C' CongA C B A0"
    using SuppA_def assms(1) by auto
  obtain D0 where P2: "Bet D E D0 \<and> D' E' F' CongA F E D0"
    using SuppA_def assms(2) by auto
  have "F E D0 LeA C B A0"
  proof -
    have P3: "D0 \<noteq> E"
      using CongA_def P2 by auto
    have P4: "A0 \<noteq> B"
      using CongA_def P1 by blast
    have P6: "Bet D0 E D"
      by (simp add: P2 between_symmetry)
    have "Bet A0 B A"
      by (simp add: P1 between_symmetry)
    thus ?thesis
      by (metis P3 P4 P6 assms(3) l11_36_aux2 lea_comm lea_distincts)
  qed
  thus ?thesis
    by (meson P1 P2 Tarski_neutral_dimensionless.l11_30 Tarski_neutral_dimensionless.not_conga_sym Tarski_neutral_dimensionless_axioms)
qed

lemma lta_suppa2__lta:
  assumes "A B C SuppA A' B' C'"
    and "D E F SuppA D' E' F'"
    and "A B C LtA D E F"
  shows "D' E' F' LtA A' B' C'"
proof -
  obtain A0 where P1: "Bet A B A0 \<and> A' B' C' CongA C B A0"
    using SuppA_def assms(1) by auto
  obtain D0 where P2: "Bet D E D0 \<and> D' E' F' CongA F E D0"
    using SuppA_def assms(2) by auto
  have "F E D0 LtA C B A0"
  proof -
    have P5: "A0 \<noteq> B"
      using CongA_def P1 by blast
    have "D0 \<noteq> E"
      using CongA_def P2 by auto
    thus ?thesis
      using assms(3) P1 P5 P2 bet2_lta__lta lta_comm by blast
  qed
  thus ?thesis
    using P1 P2 conga_preserves_lta not_conga_sym by blast
qed

lemma suppa_dec:
  "A B C SuppA D E F \<or> \<not> A B C SuppA D E F"
  by simp

lemma acute_one_side_aux:
  assumes "C A OS P B" and
    "Acute A C P" and
    "C A Perp B C"
  shows "C B OS A P"
proof -
  obtain R where T1: "C A TS P R \<and> C A TS B R"
    using OS_def assms(1) by blast
  obtain A' B' C' where P1: "Per A' B' C' \<and> A C P LtA A' B' C'"
    using Acute_def assms(2) by auto
  have P2: "Per A C B"
    by (simp add: assms(3) perp_per_1)
  then have P3: "A' B' C' CongA A C B"
    using P1 assms(1) l11_16 lta_distincts os_distincts by blast
  have P4: "A C P LtA A C B"
    by (metis P2 acute_per__lta assms(1) assms(2) os_distincts)
  {
    assume P4A: "Col P C B"
    have "Per A C P"
    proof -
      have P4B: "C \<noteq> B"
        using assms(1) os_distincts by blast
      have P4C: "Per A C B"
        by (simp add: P2)
      have "Col C B P"
        using P4A Col_cases by auto
      thus ?thesis using per_col P4B P4C by blast
    qed
    then have "False"
      using acute_not_per assms(2) by auto
  }
  then have P5: "\<not> Col P C B" by auto
  have P6: "\<not> Col A C P"
    using assms(1) col123__nos not_col_permutation_4 by blast
  have P7: "C B TS A P \<or> C B OS A P"
    using P5 assms(1) not_col_permutation_4 os_ts1324__os two_sides_cases by blast
  {
    assume P8: "C B TS A P"
    then obtain T where P9: "Col T C B \<and> Bet A T P"
      using TS_def by blast
    then have P10: "C \<noteq> T"
      using Col_def P6 P9 by auto
    have "T InAngle A C P"
      by (meson P4 P5 P8 Tarski_neutral_dimensionless.inangle__lta Tarski_neutral_dimensionless_axioms assms(1) not_and_lta not_col_permutation_3 os_ts__inangle)
    then have "C A OS T P"
      by (metis P10 P9 T1 TS_def col123__nos in_angle_one_side invert_one_side l6_16_1 one_side_reflexivity)
    then have P13: "C A OS T B"
      using assms(1) one_side_transitivity by blast
    have "C B OS A P"
      by (meson P4 Tarski_neutral_dimensionless.lta_os__ts Tarski_neutral_dimensionless_axioms assms(1) one_side_symmetry os_ts1324__os)
  }
  thus ?thesis
    using P7 by blast
qed

lemma acute_one_side_aux0:
  assumes "Col A C P" and
    "Acute A C P" and
    "C A Perp B C"
  shows "C B OS A P"
proof -
  have "Per A C B"
    by (simp add: assms(3) perp_per_1)
  then have P1: "A C P LtA A C B"
    using Tarski_neutral_dimensionless.acute_per__lta Tarski_neutral_dimensionless_axioms acute_distincts assms(2) assms(3) perp_not_eq_2 by fastforce
  have P2: "C Out A P"
    using acute_col__out assms(1) assms(2) by auto
  thus ?thesis
    using Perp_cases assms(3) out_one_side perp_not_col by blast
qed

lemma acute_cop_perp__one_side:
  assumes "Acute A C P" and
    "C A Perp B C" and
    "Coplanar A B C P"
  shows "C B OS A P"
proof cases
  assume "Col A C P"
  thus ?thesis
    by (simp add: acute_one_side_aux0 assms(1) assms(2))
next
  assume P1: "\<not> Col A C P"
  have P2: "C A TS P B \<or> C A OS P B"
    using Col_cases P1 assms(2) assms(3) cop_nos__ts coplanar_perm_13 perp_not_col by blast
  {
    assume P3: "C A TS P B"
    obtain Bs where P4: "C Midpoint B Bs"
      using symmetric_point_construction by auto
    have "C A TS Bs B"
      by (metis P3 P4 assms(2) bet__ts l9_2 midpoint_bet midpoint_distinct_2 perp_not_col ts_distincts)
    then have P6: "C A OS P Bs"
      using P3 l9_8_1 by auto
    have "C Bs Perp A C"
    proof -
      have P6A: "C \<noteq> Bs"
        using P6 os_distincts by blast
      have "Col C B Bs"
        using Bet_cases Col_def P4 midpoint_bet by blast
      thus ?thesis
        using Perp_cases P6A assms(2) perp_col by blast
    qed
    then have "Bs C Perp C A"
      using Perp_perm by blast
    then have "C A Perp Bs C"
      using Perp_perm by blast
    then have "C B OS A P" using acute_one_side_aux
      by (metis P4 P6 assms(1) assms(2) col_one_side midpoint_col not_col_permutation_5 perp_distinct)
  }
  {
    assume "C A OS P B"
    then have "C B OS A P" using acute_one_side_aux
      using assms(1) assms(2) by blast
  }
  thus ?thesis
    using P2 \<open>C A TS P B \<Longrightarrow> C B OS A P\<close> by auto
qed

lemma acute__not_obtuse:
  assumes "Acute A B C"
  shows "\<not> Obtuse A B C"
  using acute_obtuse__lta assms nlta by blast

subsubsection "Sum of angles"

lemma suma_distincts:
  assumes "A B C D E F SumA G H I"
  shows "A \<noteq> B \<and> B \<noteq>C \<and> D \<noteq> E \<and>  E \<noteq> F \<and> G \<noteq> H \<and> H \<noteq> I"
proof -
  obtain J where "C B J CongA D E F \<and> \<not> B C OS A J \<and> Coplanar A B C J \<and> A B J CongA G H I"
    using SumA_def assms by auto
  thus ?thesis
    using CongA_def by blast
qed

lemma trisuma_distincts:
  assumes "A B C TriSumA D E F"
  shows "A \<noteq> B \<and> B \<noteq> C \<and> A \<noteq> C \<and> D \<noteq> E \<and> E \<noteq> F"
proof -
  obtain G H I where "A B C B C A SumA G H I \<and> G H I C A B SumA D E F"
    using TriSumA_def assms by auto
  thus ?thesis
    using suma_distincts by blast
qed

lemma ex_suma:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "D \<noteq> E" and
    "E \<noteq> F"
  shows "\<exists> G H I. A B C D E F SumA G H I"
proof -
  have "\<exists> I. A B C D E F SumA A B I"
  proof cases
    assume P1: "Col A B C"
    obtain J where P2: "D E F CongA C B J \<and> Coplanar C B J A" using angle_construction_4
      using assms(2) assms(3) assms(4) by presburger
    have P3: "J \<noteq> B"
      using CongA_def P2 by blast
    have "\<not> B C OS A J"
      by (metis P1 between_trivial2 one_side_chara)
    then have "A B C D E F SumA A B J"
      by (meson P2 P3 SumA_def assms(1) conga_refl ncoplanar_perm_15 not_conga_sym)
    thus ?thesis by blast
  next
    assume T1: "\<not> Col A B C"
    show ?thesis
    proof cases
      assume T2: "Col D E F"
      show ?thesis
      proof cases
        assume T3: "Bet D E F"
        obtain J where T4: "B Midpoint C J"
          using symmetric_point_construction by blast
        have "A B C D E F SumA A B J"
        proof -
          have "C B J CongA D E F"
            by (metis T3 T4 assms(2) assms(3) assms(4) conga_line midpoint_bet midpoint_distinct_2)
          moreover have "\<not> B C OS A J"
            by (simp add: T4 col124__nos midpoint_col)
          moreover have "Coplanar A B C J"
            using T3 bet__coplanar bet_conga__bet calculation(1) conga_sym ncoplanar_perm_15 by blast
          moreover have "A B J CongA A B J"
            using CongA_def assms(1) calculation(1) conga_refl by auto
          ultimately show ?thesis
            using SumA_def by blast
        qed
        then show ?thesis
          by auto
      next
        assume T5: "\<not> Bet D E F"
        have "A B C D E F SumA A B C"
        proof -
          have "E Out D F"
            using T2 T5 l6_4_2 by auto
          then have "C B C CongA D E F"
            using assms(2) l11_21_b out_trivial by auto
          moreover have "\<not> B C OS A C"
            using os_distincts by blast
          moreover have "Coplanar A B C C"
            using ncop_distincts by auto
          moreover have "A B C CongA A B C"
            using assms(1) assms(2) conga_refl by auto
          ultimately show ?thesis
            using SumA_def by blast
        qed
        then show ?thesis
          by auto
      qed
    next
      assume T6: "\<not> Col D E F"
      then obtain J where T7: "D E F CongA C B J \<and> C B TS J A"
        using T1 ex_conga_ts not_col_permutation_4 not_col_permutation_5 by presburger
      then show ?thesis
      proof -
        have "C B J CongA D E F"
          using T7 not_conga_sym by blast
        moreover have "\<not> B C OS A J"
          by (simp add: T7 invert_two_sides l9_2 l9_9)
        moreover have "Coplanar A B C J"
          using T7 ncoplanar_perm_15 ts__coplanar by blast
        moreover have "A B J CongA A B J"
          using T7 assms(1) conga_diff56 conga_refl by blast
        ultimately show ?thesis
          using SumA_def by blast
      qed
    qed
  qed
  then show ?thesis
    by auto
qed

lemma suma2__conga:
  assumes "A B C D E F SumA G H I" and
    "A B C D E F SumA G' H' I'"
  shows "G H I CongA G' H' I'"
proof -
  obtain J where P1: "C B J CongA D E F \<and> \<not> B C OS A J \<and> Coplanar A B C J \<and> A B J CongA G H I"
    using SumA_def assms(1) by blast
  obtain J' where P2: "C B J' CongA D E F \<and> \<not> B C OS A J' \<and> Coplanar A B C J' \<and> A B J' CongA G' H' I'"
    using SumA_def assms(2) by blast
  have P3: "C B J CongA C B J'"
  proof -
    have "C B J CongA D E F"
      by (simp add: P1)
    moreover have "D E F CongA C B J'"
      by (simp add: P2 conga_sym)
    ultimately show ?thesis
      using not_conga by blast
  qed
  have P4: "A B J CongA A B J'"
  proof cases
    assume P5: "Col A B C"
    then show ?thesis
    proof cases
      assume P6: "Bet A B C"
      show ?thesis
      proof -
        have "C B J CongA C B J'"
          by (simp add: P3)
        moreover have "Bet C B A"
          by (simp add: P6 between_symmetry)
        moreover have "A \<noteq> B"
          using assms(1) suma_distincts by blast
        ultimately show ?thesis
          using l11_13 by blast
      qed
    next
      assume P7: "\<not> Bet A B C"
      moreover have "B Out A C"
        by (simp add: P5 calculation l6_4_2)
      moreover have "B \<noteq> J"
        using CongA_def P3 by blast
      then moreover have "B Out J J"
        using out_trivial by auto
      moreover have "B \<noteq> J'"
        using CongA_def P3 by blast
      then moreover have "B Out J' J'"
        using out_trivial by auto
      ultimately show ?thesis
        using P3 l11_10 by blast
    qed
  next
    assume P8: "\<not> Col A B C"
    show ?thesis
    proof cases
      assume P9: "Col D E F"
      have "B Out J' J"
      proof cases
        assume P10: "Bet D E F"
        show ?thesis
        proof -
          have "D E F CongA J' B C"
            using P2 conga_right_comm not_conga_sym by blast
          then have "Bet J' B C"
            using P10 bet_conga__bet by blast
          moreover have "D E F CongA J B C"
            by (simp add: P1 conga_right_comm conga_sym)
          then moreover have "Bet J B C"
            using P10 bet_conga__bet by blast
          ultimately show ?thesis
            by (metis CongA_def P3 l6_2)
        qed
      next
        assume P11: "\<not> Bet D E F"
        have P12: "E Out D F"
          by (simp add: P11 P9 l6_4_2)
        show ?thesis
        proof -
          have "B Out J' C"
          proof -
            have "D E F CongA J' B C"
              using P2 conga_right_comm conga_sym by blast
            then show ?thesis
              using l11_21_a P12 by blast
          qed
          moreover have "B Out C J"
            by (metis P3 P8 bet_conga__bet calculation col_conga_col col_out2_col l6_4_2 l6_6 not_col_distincts not_conga_sym out_bet_out_1 out_trivial)
          ultimately show ?thesis
            using l6_7 by blast
        qed
      qed
      then show ?thesis
        using P8 not_col_distincts out2__conga out_trivial by blast
    next
      assume P13: "\<not> Col D E F"
      show ?thesis
      proof -
        have "B C TS A J"
        proof -
          have "Coplanar B C A J"
            using P1 coplanar_perm_8 by blast
          moreover have "\<not> Col A B C"
            by (simp add: P8)
          moreover have "\<not> B C OS A J"
            using P1 by simp
          moreover have "\<not> Col J B C"
          proof -
            have "D E F CongA J B C"
              using P1 conga_right_comm not_conga_sym by blast
            then show ?thesis
              using P13 ncol_conga_ncol by blast
          qed
          ultimately show ?thesis
            using cop__one_or_two_sides by blast
        qed
        moreover have "B C TS A J'"
        proof -
          have "Coplanar B C A J'"
            using P2 coplanar_perm_8 by blast
          moreover have "\<not> Col A B C"
            by (simp add: P8)
          moreover have "\<not> B C OS A J'"
            using P2 by simp
          moreover have "\<not> Col J' B C"
          proof -
            have "D E F CongA J' B C"
              using P2 conga_right_comm not_conga_sym by blast
            then show ?thesis
              using P13 ncol_conga_ncol by blast
          qed
          ultimately show ?thesis
            using cop_nos__ts by blast
        qed
        moreover have "A B C CongA A B C"
          by (metis P8 conga_pseudo_refl conga_right_comm not_col_distincts)
        moreover have "C B J CongA C B J'"
          by (simp add: P3)
        ultimately show ?thesis
          using l11_22a by blast
      qed
    qed
  qed
  then show ?thesis
    by (meson P1 P2 not_conga not_conga_sym)
qed

lemma suma_sym:
  assumes "A B C D E F SumA G H I"
  shows "D E F A B C SumA G H I"
proof -
  obtain J where P1: "C B J CongA D E F \<and> \<not> B C OS A J \<and> Coplanar A B C J \<and> A B J CongA G H I"
    using SumA_def assms(1) by blast
  show ?thesis
  proof cases
    assume P2: "Col A B C"
    then show ?thesis
    proof cases
      assume P3: "Bet A B C"
      obtain K where P4: "Bet F E K \<and> Cong F E E K"
        using Cong_perm segment_construction by blast
      show ?thesis
      proof -
        have P5: "F E K CongA A B C"
          by (metis CongA_def P1 P3 P4 cong_diff conga_line)
        moreover have "\<not> E F OS D K"
          using P4 bet_col col124__nos invert_one_side by blast
        moreover have "Coplanar D E F K"
          using P4 bet__coplanar ncoplanar_perm_15 by blast
        moreover have "D E K CongA G H I"
        proof -
          have "D E K CongA A B J"
          proof -
            have "F E D CongA C B J"
              by (simp add: P1 conga_left_comm conga_sym)
            moreover have "Bet F E K"
              by (simp add: P4)
            moreover have "K \<noteq> E"
              using P4 calculation(1) cong_identity conga_diff1 by blast
            moreover have "Bet C B A"
              by (simp add: Bet_perm P3)
            moreover have "A \<noteq> B"
              using CongA_def P5 by blast
            ultimately show ?thesis
              using conga_right_comm l11_13 not_conga_sym by blast
          qed
          then show ?thesis
            using P1 not_conga by blast
        qed
        ultimately show ?thesis
          using SumA_def by blast
      qed
    next
      assume T1: "\<not> Bet A B C"
      then have T2: "B Out A C"
        by (simp add: P2 l6_4_2)
      show ?thesis
      proof -
        have "F E F CongA A B C"
          by (metis T2 assms l11_21_b out_trivial suma_distincts)
        moreover have "\<not> E F OS D F"
          using os_distincts by auto
        moreover have "Coplanar D E F F"
          using ncop_distincts by auto
        moreover have "D E F CongA G H I"
        proof -
          have "A B J CongA D E F"
          proof -
            have "C B J CongA D E F"
              by (simp add: P1)
            moreover have "B Out A C"
              by (simp add: T2)
            moreover have "J \<noteq> B"
              using calculation(1) conga_distinct by auto
            moreover have "D \<noteq> E"
              using calculation(1) conga_distinct by blast
            moreover have "F \<noteq> E"
              using calculation(1) conga_distinct by blast
            ultimately show ?thesis
              by (meson Out_cases not_conga out2__conga out_trivial)
          qed
          then have "D E F CongA A B J"
            using not_conga_sym by blast
          then show ?thesis
            using P1 not_conga by blast
        qed
        ultimately show ?thesis
          using SumA_def by blast
      qed
    qed
  next
    assume Q1: "\<not> Col A B C"
    show ?thesis
    proof cases
      assume Q2: "Col D E F"
      obtain K where Q3: "A B C CongA F E K"
        using P1 angle_construction_3 conga_diff1 conga_diff56 by fastforce
      show ?thesis
      proof -
        have "F E K CongA A B C"
          by (simp add: Q3 conga_sym)
        moreover have "\<not> E F OS D K"
          using Col_cases Q2 one_side_not_col123 by blast
        moreover have "Coplanar D E F K"
          by (simp add: Q2 col__coplanar)
        moreover have "D E K CongA G H I"
        proof -
          have "D E K CongA A B J"
          proof cases
            assume "Bet D E F"
            then have "J B A CongA D E K"
              by (metis P1 bet_conga__bet calculation(1) conga_diff45 conga_right_comm l11_13 not_conga_sym)
            then show ?thesis
              using conga_right_comm not_conga_sym by blast
          next
            assume "\<not> Bet D E F"
            then have W2: "E Out D F"
              using Q2 or_bet_out by blast
            have "A B J CongA D E K"
            proof -
              have "A B C CongA F E K"
                by (simp add: Q3)
              moreover have "A \<noteq> B"
                using Q1 col_trivial_1 by auto
              moreover have "E Out D F"
                by (simp add: W2)
              moreover have "B Out J C"
              proof -
                have "D E F CongA J B C"
                  by (simp add: P1 conga_left_comm conga_sym)
                then show ?thesis
                  using W2 out_conga_out by blast
              qed
              moreover have "K \<noteq> E"
                using CongA_def Q3 by blast
              ultimately show ?thesis
                using l11_10 out_trivial by blast
            qed
            then show ?thesis
              using not_conga_sym by blast
          qed
          then show ?thesis
            using P1 not_conga by blast
        qed
        ultimately show ?thesis
          using SumA_def by blast
      qed
    next
      assume W3: "\<not> Col D E F"
      then obtain K where W4: "A B C CongA F E K \<and> F E TS K D"
        using Q1 ex_conga_ts not_col_permutation_3 by blast
      show ?thesis
      proof -
        have "F E K CongA A B C"
          using W4 not_conga_sym by blast
        moreover have "\<not> E F OS D K"
        proof -
          have "E F TS D K"
            using W4 invert_two_sides l9_2 by blast
          then show ?thesis
            using l9_9 by auto
        qed
        moreover have "Coplanar D E F K"
        proof -
          have "E F TS D K"
            using W4 invert_two_sides l9_2 by blast
          then show ?thesis
            using ncoplanar_perm_8 ts__coplanar by blast
        qed
        moreover have "D E K CongA G H I"
        proof -
          have "A B J CongA K E D"
          proof -
            have "B C TS A J"
            proof -
              have "Coplanar B C A J"
                using P1 ncoplanar_perm_12 by blast
              moreover have "\<not> Col A B C"
                by (simp add: Q1)
              moreover have "\<not> B C OS A J"
                using P1 by simp
              moreover have "\<not> Col J B C"
              proof -
                {
                  assume "Col J B C"
                  have "Col D E F"
                  proof -
                    have "Col C B J"
                      using Col_perm \<open>Col J B C\<close> by blast
                    moreover have "C B J CongA D E F"
                      by (simp add: P1)
                    ultimately show ?thesis
                      using col_conga_col by blast
                  qed
                  then have "False"
                    by (simp add: W3)
                }
                then show ?thesis by blast
              qed
              ultimately show ?thesis
                using cop_nos__ts by blast
            qed
            moreover have "E F TS K D"
              using W4 invert_two_sides by blast
            moreover have "A B C CongA K E F"
              by (simp add: W4 conga_right_comm)
            moreover have "C B J CongA F E D"
              by (simp add: P1 conga_right_comm)
            ultimately show ?thesis
              using l11_22a by auto
          qed
          then have "D E K CongA A B J"
            using conga_left_comm not_conga_sym by blast
          then show ?thesis
            using P1 not_conga by blast
        qed
        ultimately show ?thesis
          using SumA_def by blast
      qed
    qed
  qed
qed

lemma conga3_suma__suma:
  assumes "A B C D E F SumA G H I" and
    "A B C CongA A' B' C'" and
    "D E F CongA D' E' F'" and
    "G H I CongA G' H' I'"
  shows "A' B' C' D' E' F' SumA G' H' I'"
proof -
  have "D' E' F' A B C SumA G' H' I'"
  proof -
    obtain J where P1: "C B J CongA D E F \<and> \<not> B C OS A J \<and> Coplanar A B C J \<and> A B J CongA G H I"
      using SumA_def assms(1) by blast
    have "A B C D' E' F' SumA G' H' I'"
    proof -
      have "C B J CongA D' E' F'"
        using P1 assms(3) not_conga by blast
      moreover have "\<not> B C OS A J"
        using P1 by simp
      moreover have "Coplanar A B C J"
        using P1 by simp
      moreover have "A B J CongA G' H' I'"
        using P1 assms(4) not_conga by blast
      ultimately show ?thesis
        using SumA_def by blast
    qed
    then show ?thesis
      by (simp add: suma_sym)
  qed
  then obtain J where P2: "F' E' J CongA A B C  \<and> \<not> E' F' OS D' J \<and> Coplanar D' E' F' J \<and> D' E' J CongA G' H' I'"
    using SumA_def by blast
  have "D' E' F' A' B' C' SumA G' H' I'"
  proof -
    have "F' E' J CongA A' B' C'"
    proof -
      have "F' E' J CongA A B C"
        by (simp add: P2)
      moreover have "A B C CongA A' B' C'"
        by (simp add: assms(2))
      ultimately show ?thesis
        using not_conga by blast
    qed
    moreover have "\<not> E' F' OS D' J"
      using P2 by simp
    moreover have "Coplanar D' E' F' J"
      using P2 by simp
    moreover have "D' E' J CongA G' H' I'"
      by (simp add: P2)
    ultimately show ?thesis
      using SumA_def by blast
  qed
  then show ?thesis
    by (simp add: suma_sym)
qed

lemma out6_suma__suma:
  assumes "A B C D E F SumA G H I" and
    "B Out A A'" and
    "B Out C C'" and
    "E Out D D'" and
    "E Out F F'" and
    "H Out G G'" and
    "H Out I I'"
  shows "A' B C' D' E F' SumA G' H I'"
proof -
  have "A B C CongA A' B C'"
    using Out_cases assms(2) assms(3) out2__conga by blast
  moreover have "D E F CongA D' E F'"
    using Out_cases assms(4) assms(5) out2__conga by blast
  moreover have "G H I CongA G' H I'"
    by (simp add: assms(6) assms(7) l6_6 out2__conga)
  ultimately show ?thesis
    using assms(1) conga3_suma__suma by blast
qed

lemma out546_suma__conga:
  assumes "A B C D E F SumA G H I" and
    "E Out D F"
  shows "A B C CongA G H I"
proof -
  have "A B C D E F SumA A B C"
  proof -
    have "C B C CongA D E F"
      by (metis assms(1) assms(2) l11_21_b out_trivial suma_distincts)
    moreover have "\<not> B C OS A C"
      using os_distincts by auto
    moreover have "Coplanar A B C C"
      using ncop_distincts by auto
    moreover have "A B C CongA A B C"
      by (metis Tarski_neutral_dimensionless.suma_distincts Tarski_neutral_dimensionless_axioms assms(1) conga_pseudo_refl conga_right_comm)
    ultimately show ?thesis
      using SumA_def by blast
  qed
  then show ?thesis using suma2__conga assms(1) by blast
qed

lemma out546__suma:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "E Out D F"
  shows "A B C D E F SumA A B C"
proof -
  have P1: "D \<noteq> E"
    using assms(3) out_diff1 by auto
  have P2: "F \<noteq> E"
    using Out_def assms(3) by auto
  then obtain G H I where P3: "A B C D E F SumA G H I"
    using P1 assms(1) assms(2) ex_suma by presburger
  then have "G H I CongA A B C"
    by (meson Tarski_neutral_dimensionless.conga_sym Tarski_neutral_dimensionless.out546_suma__conga Tarski_neutral_dimensionless_axioms assms(3))
  then show ?thesis
    using P1 P2 P3 assms(1) assms(2) assms(3) conga3_suma__suma conga_refl out_diff1 by auto
qed

lemma out213_suma__conga:
  assumes "A B C D E F SumA G H I" and
    "B Out A C"
  shows "D E F CongA G H I"
  using assms(1) assms(2) out546_suma__conga suma_sym by blast

lemma out213__suma:
  assumes "D \<noteq> E" and
    "E \<noteq> F" and
    "B Out A C"
  shows "A B C D E F SumA D E F"
  by (simp add: assms(1) assms(2) assms(3) out546__suma suma_sym)

lemma suma_left_comm:
  assumes "A B C D E F SumA G H I"
  shows "C B A D E F SumA G H I"
proof -
  have "A B C CongA C B A"
    using assms conga_pseudo_refl suma_distincts by fastforce
  moreover have "D E F CongA D E F"
    by (metis assms conga_refl suma_distincts)
  moreover have "G H I CongA G H I"
    by (metis assms conga_refl suma_distincts)
  ultimately show ?thesis
    using assms conga3_suma__suma by blast
qed

lemma suma_middle_comm:
  assumes "A B C D E F SumA G H I"
  shows "A B C F E D SumA G H I"
  using assms suma_left_comm suma_sym by blast

lemma suma_right_comm:
  assumes "A B C D E F SumA G H I"
  shows "A B C D E F SumA I H G"
proof -
  have "A B C CongA A B C"
    using assms conga_refl suma_distincts by fastforce
  moreover have "D E F CongA D E F"
    by (metis assms conga_refl suma_distincts)
  moreover have "G H I CongA I H G"
    by (meson Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless.suma2__conga Tarski_neutral_dimensionless_axioms assms)
  ultimately show ?thesis
    using assms conga3_suma__suma by blast
qed

lemma suma_comm:
  assumes "A B C D E F SumA G H I"
  shows "C B A F E D SumA I H G"
  by (simp add: assms suma_left_comm suma_middle_comm suma_right_comm)

lemma ts__suma:
  assumes "A B TS C D"
  shows "C B A A B D SumA C B D"
proof -
  have "A B D CongA A B D"
    by (metis Tarski_neutral_dimensionless.conga_right_comm Tarski_neutral_dimensionless_axioms assms conga_pseudo_refl ts_distincts)
  moreover have "\<not> B A OS C D"
    using assms invert_one_side l9_9 by blast
  moreover have "Coplanar C B A D"
    using assms ncoplanar_perm_14 ts__coplanar by blast
  moreover have "C B D CongA C B D"
    by (metis assms conga_refl ts_distincts)
  ultimately show ?thesis
    using SumA_def by blast
qed

lemma ts__suma_1:
  assumes "A B TS C D"
  shows "C A B B A D SumA C A D"
  by (simp add: assms invert_two_sides ts__suma)

lemma inangle__suma:
  assumes "P InAngle A B C"
  shows "A B P P B C SumA A B C"
proof -
  have "Coplanar A B P C"
    by (simp add: assms coplanar_perm_8 inangle__coplanar)
  moreover have "\<not> B P OS A C"
    by (meson assms col123__nos col124__nos in_angle_two_sides invert_two_sides l9_9_bis not_col_permutation_5)
  ultimately show ?thesis
    using SumA_def assms conga_refl inangle_distincts by blast
qed

lemma bet__suma:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "P \<noteq> B" and "Bet A B C"
  shows "A B P P B C SumA A B C"
proof -
  have "P InAngle A B C"
    using assms(1) assms(2) assms(3) assms(4) in_angle_line by auto
  then show ?thesis
    by (simp add: inangle__suma)
qed

lemma sams_chara:
  assumes "A \<noteq> B" and
    "A' \<noteq> B" and
    "Bet A B A'"
  shows "SAMS A B C D E F \<longleftrightarrow> D E F LeA C B A'"
proof -
  {
    assume T1: "SAMS A B C D E F"
    obtain J where T2: "C B J CongA D E F \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J"
      using SAMS_def T1 by auto
    have T3: "A \<noteq> A'"
      using assms(2) assms(3) between_identity by blast
    have T4: "C \<noteq> B"
      using T2 conga_distinct by blast
    have T5: "J \<noteq> B"
      using T2 conga_diff2 by blast
    have T6: "D \<noteq> E"
      using CongA_def T2 by auto
    have T7: "F \<noteq> E"
      using CongA_def T2 by blast
    {
      assume "E Out D F"
      then have "D E F LeA C B A'"
        by (simp add: T4 assms(2) l11_31_1)
    }
    {
      assume T8: "\<not> Bet A B C"
      have "D E F LeA C B A'"
      proof cases
        assume "Col A B C"
        then have "Bet C B A'"
          using T8 assms(1) assms(3) between_exchange3 outer_transitivity_between2 third_point by blast
        then show ?thesis
          by (simp add: T4 T6 T7 assms(2) l11_31_2)
      next
        assume T9: "\<not> Col A B C"
        show ?thesis
        proof cases
          assume T10: "Col D E F"
          show ?thesis
          proof cases
            assume T11: "Bet D E F"
            have "D E F CongA C B J"
              by (simp add: T2 conga_sym)
            then have T12: "Bet C B J"
              using T11 bet_conga__bet by blast
            have "A B TS C J"
            proof -
              have "\<not> Col J A B"
                using T5 T9 T12 bet_col col2__eq col_permutation_1 by blast
              moreover have "\<exists> T. Col T A B \<and> Bet C T J"
                using T12 col_trivial_3 by blast
              ultimately show ?thesis
                using T9 TS_def col_permutation_1 by blast
            qed
            then have "False"
              using T2 by simp
            then show ?thesis by simp
          next
            assume "\<not> Bet D E F"
            then show ?thesis
              using T10 \<open>E Out D F \<Longrightarrow> D E F LeA C B A'\<close> or_bet_out by auto
          qed
        next
          assume T13: "\<not> Col D E F"
          show ?thesis
          proof -
            have "C B J LeA C B A'"
            proof -
              have "J InAngle C B A'"
              proof -
                have "A' \<noteq> B"
                  by (simp add: assms(2))
                moreover have "Bet A B A'"
                  by (simp add: assms(3))
                moreover have "C InAngle A B J"
                proof -
                  have "\<not> Col J B C"
                  proof -
                    have "\<not> Col D E F"
                      by (simp add: T13)
                    moreover have "D E F CongA J B C"
                      using T2 conga_left_comm not_conga_sym by blast
                    ultimately show ?thesis
                      using ncol_conga_ncol by blast
                  qed
                  then have "B C TS A J"
                    by (simp add: T2 T9 cop_nos__ts coplanar_perm_8)
                  then obtain X where T14: "Col X B C \<and> Bet A X J"
                    using TS_def by blast
                  {
                    assume T15: "X \<noteq> B"
                    have "B Out X C"
                    proof -
                      have "Col B X C"
                        by (simp add: Col_perm T14)
                      moreover have "B A OS X C"
                      proof -
                        have "A B OS X C"
                        proof -
                          have "A B OS X J"
                            by (smt T14 T9 T15 bet_out calculation col_transitivity_2 col_trivial_2 l6_21 out_one_side)
                          moreover have "A B OS J C"
                            by (metis T14 T2 T9 calculation cop_nts__os l5_2 not_col_permutation_2 one_side_chara one_side_symmetry)
                          ultimately show ?thesis
                            using one_side_transitivity by blast
                        qed
                        then show ?thesis
                          by (simp add: invert_one_side)
                      qed
                      ultimately show ?thesis
                        using col_one_side_out by auto
                    qed
                  }
                  then have "Bet A X J \<and> (X = B \<or> B Out X C)"
                    using T14 by blast
                  then show ?thesis
                    using InAngle_def T4 T5 assms(1) by auto
                qed
                ultimately show ?thesis
                  using in_angle_reverse l11_24 by blast
              qed
              moreover have "C B J CongA C B J"
                by (simp add: T4 T5 conga_refl)
              ultimately show ?thesis
                by (simp add: inangle__lea)
            qed
            moreover have "D E F LeA C B J"
              by (simp add: T2 conga__lea456123)
            ultimately show ?thesis
              using lea_trans by blast
          qed
        qed
      qed
    }
    then have "D E F LeA C B A'"
      using SAMS_def T1 \<open>E Out D F \<Longrightarrow> D E F LeA C B A'\<close> by blast
  }
  {
    assume P1: "D E F LeA C B A'"
    have P2: "A \<noteq> A'"
      using assms(2) assms(3) between_identity by blast
    have P3: "C \<noteq> B"
      using P1 lea_distincts by auto
    have P4: "D \<noteq> E"
      using P1 lea_distincts by auto
    have P5: "F \<noteq> E"
      using P1 lea_distincts by auto
    have "SAMS A B C D E F"
    proof cases
      assume P6: "Col A B C"
      show ?thesis
      proof cases
        assume P7: "Bet A B C"
        have "E Out D F"
        proof -
          have "B Out C A'"
            by (meson Bet_perm P3 P7 assms(1) assms(2) assms(3) l6_2)
          moreover have "C B A' CongA D E F"
            using P1 calculation l11_21_b out_lea__out by blast
          ultimately show ?thesis
            using out_conga_out by blast
        qed
        moreover have "C B C CongA D E F"
          using P3 calculation l11_21_b out_trivial by auto
        moreover have "\<not> B C OS A C"
          using os_distincts by auto
        moreover have "\<not> A B TS C C"
          by (simp add: not_two_sides_id)
        moreover have "Coplanar A B C C"
          using ncop_distincts by auto
        ultimately show ?thesis
          using SAMS_def assms(1) by blast
      next
        assume P8: "\<not> Bet A B C"
        have P9: "B Out A C"
          by (simp add: P6 P8 l6_4_2)
        obtain J where P10: "D E F CongA C B J"
          using P3 P4 P5 angle_construction_3 by blast
        show ?thesis
        proof -
          have "C B J CongA D E F"
            using P10 not_conga_sym by blast
          moreover have "\<not> B C OS A J"
            using Col_cases P6 one_side_not_col123 by blast
          moreover have "\<not> A B TS C J"
            using Col_cases P6 TS_def by blast
          moreover have "Coplanar A B C J"
            using P6 col__coplanar by auto
          ultimately show ?thesis
            using P8 SAMS_def assms(1) by blast
        qed
      qed
    next
      assume P11: "\<not> Col A B C"
      have P12: "\<not> Col A' B C"
        using P11 assms(2) assms(3) bet_col bet_col1 colx by blast
      show ?thesis
      proof cases
        assume P13: "Col D E F"
        have P14: "E Out D F"
        proof -
          {
            assume P14: "Bet D E F"
            have "D E F LeA C B A'"
              by (simp add: P1)
            then have "Bet C B A'"
              using P14 bet_lea__bet by blast
            then have "Col A' B C"
              using Col_def Col_perm by blast
            then have "False"
              by (simp add: P12)
          }
          then have "\<not> Bet D E F" by auto
          then show ?thesis
            by (simp add: P13 l6_4_2)
        qed
        show ?thesis
        proof -
          have "C B C CongA D E F"
            by (simp add: P3 P14 l11_21_b out_trivial)
          moreover have "\<not> B C OS A C"
            using os_distincts by auto
          moreover have "\<not> A B TS C C"
            by (simp add: not_two_sides_id)
          moreover have "Coplanar A B C C"
            using ncop_distincts by auto
          ultimately show ?thesis
            using P14 SAMS_def assms(1) by blast
        qed
      next
        assume P15: "\<not> Col D E F"
        obtain J where P16: "D E F CongA C B J \<and> C B TS J A"
          using P11 P15 ex_conga_ts not_col_permutation_3 by presburger
        show ?thesis
        proof -
          have "C B J CongA D E F"
            by (simp add: P16 conga_sym)
          moreover have "\<not> B C OS A J"
          proof -
            have "C B TS A J"
              using P16 by (simp add: l9_2)
            then show ?thesis
              using invert_one_side l9_9 by blast
          qed
          moreover have "\<not> A B TS C J \<and> Coplanar A B C J"
          proof cases
            assume "Col A B J"
            then show ?thesis
              using TS_def ncop__ncols not_col_permutation_1 by blast
          next
            assume P17: "\<not> Col A B J"
            have "\<not> A B TS C J"
            proof -
              have "A' B OS J C"
              proof -
                have "\<not> Col A' B C"
                  by (simp add: P12)
                moreover have "\<not> Col B A' J"
                proof -
                  {
                    assume "Col B A' J"
                    then have "False"
                      by (metis P17 assms(2) assms(3) bet_col col_trivial_2 colx)
                  }
                  then show ?thesis by auto
                qed
                moreover have "J InAngle A' B C"
                proof -
                  obtain K where P20: "K InAngle C B A' \<and> D E F CongA C B K"
                    using LeA_def P1 by blast
                  have "J InAngle C B A'"
                  proof -
                    have "C B A' CongA C B A'"
                      by (simp add: P3 assms(2) conga_pseudo_refl conga_right_comm)
                    moreover have "C B K CongA C B J"
                    proof -
                      have "C B K CongA D E F"
                        using P20 not_conga_sym by blast
                      moreover have "D E F CongA C B J"
                        by (simp add: P16)
                      ultimately show ?thesis
                        using not_conga by blast
                    qed
                    moreover have "K InAngle C B A'"
                      using P20 by simp
                    moreover have "C B OS J A'"
                    proof -
                      have "C B TS J A" using P16
                        by simp
                      moreover have "C B TS A' A"
                        using Col_perm P12 assms(3) bet__ts between_symmetry calculation invert_two_sides ts_distincts by blast
                      ultimately show ?thesis
                        using OS_def by auto
                    qed
                    ultimately show ?thesis
                      using conga_preserves_in_angle by blast
                  qed
                  then show ?thesis
                    by (simp add: l11_24)
                qed
                ultimately show ?thesis
                  by (simp add: in_angle_one_side)
              qed
              then have "A' B OS C J"
                by (simp add: one_side_symmetry)
              then have "\<not> A' B TS C J"
                by (simp add: l9_9_bis)
              then show ?thesis
                using assms(2) assms(3) bet_col bet_col1 col_preserves_two_sides by blast
            qed
            moreover have "Coplanar A B C J"
            proof -
              have "C B TS J A"
                using P16 by simp
              then show ?thesis
                by (simp add: coplanar_perm_20 ts__coplanar)
            qed
            ultimately  show ?thesis by auto
          qed
          ultimately show ?thesis
            using P11 SAMS_def assms(1) bet_col by auto
        qed
      qed
    qed
  }
  then show ?thesis
    using \<open>SAMS A B C D E F \<Longrightarrow> D E F LeA C B A'\<close> by blast
qed

lemma sams_distincts:
  assumes "SAMS A B C D E F"
  shows "A \<noteq> B \<and> B \<noteq> C \<and> D \<noteq> E \<and> E \<noteq> F"
proof -
  obtain J where P1: "C B J CongA D E F \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J"
    using SAMS_def assms by auto
  then show ?thesis
    by (metis SAMS_def assms conga_distinct)
qed

lemma sams_sym:
  assumes "SAMS A B C D E F"
  shows "SAMS D E F A B C"
proof -
  have P1: "A \<noteq> B"
    using assms sams_distincts by blast
  have P3: "D \<noteq> E"
    using assms sams_distincts by blast
  obtain D' where P5: "E Midpoint D D'"
    using symmetric_point_construction by blast
  obtain A' where P6: "B Midpoint A A'"
    using symmetric_point_construction by blast
  have P8: "E \<noteq> D'"
    using P3 P5 is_midpoint_id_2 by blast
  have P9: "A \<noteq> A'"
    using P1 P6 l7_3 by auto
  then have P10: "B \<noteq> A'"
    using P6 P9 midpoint_not_midpoint by auto
  then have "D E F LeA C B A'"
    using P1 P6 assms midpoint_bet sams_chara by fastforce
  then have "D E F LeA A' B C"
    by (simp add: lea_right_comm)
  then have "A B C LeA D' E F"
    by (metis Mid_cases P1 P10 P3 P5 P6 P8 l11_36 midpoint_bet)
  then have "A B C LeA F E D'"
    by (simp add: lea_right_comm)
  moreover have "D \<noteq> E"
    by (simp add: P3)
  moreover have "D' \<noteq> E"
    using P8 by auto
  moreover have "Bet D E D'"
    by (simp add: P5 midpoint_bet)
  then show ?thesis
    using P3 P8 calculation(1) sams_chara by fastforce
qed

lemma sams_right_comm:
  assumes "SAMS A B C D E F"
  shows "SAMS A B C F E D"
proof -
  have P1: "E Out D F \<or> \<not> Bet A B C"
    using SAMS_def assms by blast
  obtain J where P2: "C B J CongA D E F \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J"
    using SAMS_def assms by auto
  {
    assume "E Out D F"
    then have "E Out F D \<or> \<not> Bet A B C"
      by (simp add: l6_6)
  }
  {
    assume "\<not> Bet A B C"
    then have "E Out F D \<or> \<not> Bet A B C" by auto
  }
  then have "E Out F D \<or> \<not> Bet A B C"
    using \<open>E Out D F \<Longrightarrow> E Out F D \<or> \<not> Bet A B C\<close> P1 by auto
  moreover have "C B J CongA F E D"
  proof -
    have "C B J CongA D E F"
      by (simp add: P2)
    then show ?thesis
      by (simp add: conga_right_comm)
  qed
  ultimately show ?thesis
    using P2 SAMS_def assms by auto
qed

lemma sams_left_comm:
  assumes "SAMS A B C D E F"
  shows "SAMS C B A D E F"
proof -
  have "SAMS D E F A B C"
    by (simp add: assms sams_sym)
  then have "SAMS D E F C B A"
    using sams_right_comm by blast
  then show ?thesis
    using sams_sym by blast
qed

lemma sams_comm:
  assumes "SAMS A B C D E F"
  shows "SAMS C B A F E D"
  using assms sams_left_comm sams_right_comm by blast

lemma conga2_sams__sams:
  assumes "A B C CongA A' B' C'" and
    "D E F CongA D' E' F'" and
    "SAMS A B C D E F"
  shows "SAMS A' B' C' D' E' F'"
proof -
  obtain A0 where "B Midpoint A A0"
    using symmetric_point_construction by auto
  obtain A'0 where "B' Midpoint A' A'0"
    using symmetric_point_construction by blast
  have "D' E' F' LeA C' B' A'0"
  proof -
    have "D E F LeA C B A0"
      by (metis \<open>B Midpoint A A0\<close> assms(1) assms(3) conga_distinct midpoint_bet midpoint_distinct_2 sams_chara)
    moreover have "D E F CongA D' E' F'"
      by (simp add: assms(2))
    moreover have "C B A0 CongA C' B' A'0"
    proof -
      have "A0 B C CongA A'0 B' C'"
        by (metis \<open>B Midpoint A A0\<close> \<open>B' Midpoint A' A'0\<close> assms(1) calculation(1) conga_diff45 l11_13 lea_distincts midpoint_bet midpoint_not_midpoint)
      then show ?thesis
        using conga_comm by blast
    qed
    ultimately show ?thesis
      using l11_30 by blast
  qed
  then show ?thesis
    by (metis \<open>B' Midpoint A' A'0\<close> assms(1) conga_distinct lea_distincts midpoint_bet sams_chara)
qed

lemma out546__sams:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "E Out D F"
  shows "SAMS A B C D E F"
proof -
  obtain A' where "Bet A B A' \<and> Cong B A' A B"
    using segment_construction by blast
  then have "D E F LeA C B A'"
    using assms(1) assms(2) assms(3) cong_diff_3 l11_31_1 by fastforce
  then show ?thesis
    using \<open>Bet A B A' \<and> Cong B A' A B\<close> assms(1) lea_distincts sams_chara by blast
qed

lemma out213__sams:
  assumes "D \<noteq> E" and
    "E \<noteq> F" and
    "B Out A C"
  shows "SAMS A B C D E F"
  by (simp add: Tarski_neutral_dimensionless.sams_sym Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) out546__sams)

lemma bet_suma__sams:
  assumes "A B C D E F SumA G H I" and
    "Bet G H I"
  shows "SAMS A B C D E F"
proof -
  obtain A' where P1: "C B A' CongA D E F \<and> \<not> B C OS A A' \<and> Coplanar A B C A' \<and> A B A' CongA G H I"
    using SumA_def assms(1) by auto
  then have "G H I CongA A B A'"
    using not_conga_sym by blast
  then have "Bet A B A'"
    using assms(2) bet_conga__bet by blast
  show ?thesis
  proof -
    have "E Out D F \<or> \<not> Bet A B C"
    proof -
      {
        assume "Bet A B C"
        then have "E Out D F"
        proof -
          have "B Out C A'"
          proof -
            have "C \<noteq> B"
              using assms(1) suma_distincts by blast
            moreover have "A' \<noteq> B"
              using CongA_def \<open>G H I CongA A B A'\<close> by blast
            moreover have "A \<noteq> B"
              using CongA_def \<open>G H I CongA A B A'\<close> by blast
            moreover have "Bet C B A"
              by (simp add: Bet_perm \<open>Bet A B C\<close>)
            ultimately show ?thesis
              using Out_def \<open>Bet A B A'\<close> \<open>Bet A B C\<close> l5_2 by auto
          qed
          moreover have "C B A' CongA D E F"
            using P1 by simp
          ultimately show ?thesis
            using l11_21_a by blast
        qed
      }
      then show ?thesis
        by blast
    qed
    moreover have "\<exists> J. (C B J CongA D E F \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J)"
    proof -
      have "C B A' CongA D E F"
        by (simp add: P1)
      moreover have "\<not> B C OS A A'"
        by (simp add: P1)
      moreover have "\<not> A B TS C A'"
        using Col_def TS_def \<open>Bet A B A'\<close> by blast
      moreover have "Coplanar A B C A'"
        by (simp add: P1)
      ultimately show ?thesis
        by blast
    qed
    ultimately show ?thesis
      using CongA_def SAMS_def \<open>C B A' CongA D E F \<and> \<not> B C OS A A' \<and> Coplanar A B C A' \<and> A B A' CongA G H I\<close> by auto
  qed
qed

lemma bet__sams:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "P \<noteq> B" and
    "Bet A B C"
  shows "SAMS A B P P B C"
  by (meson assms(1) assms(2) assms(3) assms(4) bet__suma bet_suma__sams)

lemma suppa__sams:
  assumes "A B C SuppA D E F"
  shows "SAMS A B C D E F"
proof -
  obtain A' where P1: "Bet A B A' \<and> D E F CongA C B A'"
    using SuppA_def assms by auto
  then have "SAMS A B C C B A'"
    by (metis assms bet__sams conga_diff45 conga_diff56 suppa2__conga123)
  thus ?thesis
    by (meson P1 assms conga2_sams__sams not_conga_sym suppa2__conga123)
qed

lemma os_ts__sams:
  assumes "B P TS A C" and
    "A B OS P C"
  shows "SAMS A B P P B C"
proof -
  have "B Out P C \<or> \<not> Bet A B P"
    using assms(2) bet_col col123__nos by blast
  moreover have "\<exists> J. (P B J CongA P B C \<and> \<not> B P OS A J \<and> \<not> A B TS P J \<and> Coplanar A B P J)"
    by (metis assms(1) assms(2) conga_refl l9_9 os__coplanar os_distincts)
  ultimately show ?thesis
    using SAMS_def assms(2) os_distincts by auto
qed

lemma os2__sams:
  assumes "A B OS P C" and
    "C B OS P A"
  shows "SAMS A B P P B C"
  by (simp add: Tarski_neutral_dimensionless.os_ts__sams Tarski_neutral_dimensionless_axioms assms(1) assms(2) invert_one_side l9_31)

lemma inangle__sams:
  assumes "P InAngle A B C"
  shows "SAMS A B P P B C"
proof -
  have "Bet A B C \<or> B Out A C \<or> \<not> Col A B C"
    using l6_4_2 by blast
  {
    assume "Bet A B C"
    then have "SAMS A B P P B C"
      using assms bet__sams inangle_distincts by fastforce
  }
  {
    assume "B Out A C"
    then have "SAMS A B P P B C"
      by (metis assms in_angle_out inangle_distincts out213__sams)
  }
  {
    assume "\<not> Col A B C"
    then have "\<not> Bet A B C"
      using Col_def by auto
    {
      assume "Col B A P"
      have "SAMS A B P P B C"
        by (metis \<open>Col B A P\<close> \<open>\<not> Bet A B C\<close> assms col_in_angle_out inangle_distincts out213__sams)
    }
    {
      assume "\<not> Col B A P"
      {
        assume "Col B C P"
        have "SAMS A B P P B C"
          by (metis Tarski_neutral_dimensionless.sams_comm Tarski_neutral_dimensionless_axioms \<open>Col B C P\<close> \<open>\<not> Bet A B C\<close> assms between_symmetry col_in_angle_out inangle_distincts l11_24 out546__sams)
      }
      {
        assume "\<not> Col B C P"
        have "SAMS A B P P B C"
        proof -
          have "B P TS A C"
            by (simp add: \<open>\<not> Col B A P\<close> \<open>\<not> Col B C P\<close> assms in_angle_two_sides invert_two_sides)
          moreover have "A B OS P C"
            by (simp add: \<open>\<not> Col A B C\<close> \<open>\<not> Col B A P\<close> assms in_angle_one_side)
          ultimately show ?thesis
            by (simp add: os_ts__sams)
        qed
      }
      then have "SAMS A B P P B C"
        using \<open>Col B C P \<Longrightarrow> SAMS A B P P B C\<close> by blast
    }
    then have "SAMS A B P P B C"
      using \<open>Col B A P \<Longrightarrow> SAMS A B P P B C\<close> by blast
  }
  thus ?thesis
    using \<open>B Out A C \<Longrightarrow> SAMS A B P P B C\<close> \<open>Bet A B C \<Longrightarrow> SAMS A B P P B C\<close> \<open>Bet A B C \<or> B Out A C \<or> \<not> Col A B C\<close> by blast
qed

lemma sams_suma__lea123789:
  assumes "A B C D E F SumA G H I" and
    "SAMS A B C D E F"
  shows "A B C LeA G H I"
proof cases
  assume "Col A B C"
  show ?thesis
  proof cases
    assume "Bet A B C"
    have P1: "(A \<noteq> B \<and> (E Out D F \<or> \<not> Bet A B C)) \<and> (\<exists> J. (C B J CongA D E F \<and> \<not> (B C OS A J) \<and> \<not> (A B TS C J) \<and> Coplanar A B C J))"
      using SAMS_def assms(2) by auto
    {
      assume "E Out D F"
      then have "A B C CongA G H I"
        using assms(1) out546_suma__conga by auto
      then have "A B C LeA G H I"
        by (simp add: conga__lea)
    }
    thus ?thesis
      using P1 \<open>Bet A B C\<close> by blast
  next
    assume "\<not> Bet A B C"
    then have "B Out A C"
      using \<open>Col A B C\<close> or_bet_out by auto
    thus ?thesis
      by (metis assms(1) l11_31_1 suma_distincts)
  qed
next
  assume "\<not> Col A B C"
  show ?thesis
  proof cases
    assume "Col D E F"
    show ?thesis
    proof cases
      assume "Bet D E F"
      have "SAMS D E F A B C"
        using assms(2) sams_sym by auto
      then have "B Out A C"
        using SAMS_def \<open>Bet D E F\<close> by blast
      thus ?thesis using l11_31_1
        by (metis assms(1) suma_distincts)
    next
      assume "\<not> Bet D E F"
      have "A B C CongA G H I"
      proof -
        have "A B C D E F SumA G H I"
          by (simp add: assms(1))
        moreover have "E Out D F"
          using \<open>Col D E F\<close> \<open>\<not> Bet D E F\<close> l6_4_2 by auto
        ultimately show ?thesis
          using out546_suma__conga by auto
      qed
      show ?thesis
        by (simp add: \<open>A B C CongA G H I\<close> conga__lea)
    qed
  next
    assume "\<not> Col D E F"
    show ?thesis
    proof cases
      assume "Col G H I"
      show ?thesis
      proof cases
        assume "Bet G H I"
        thus ?thesis
          by (metis assms(1) l11_31_2 suma_distincts)
      next
        assume "\<not> Bet G H I"
        then have "H Out G I"
          by (simp add: \<open>Col G H I\<close> l6_4_2)
        have "E Out D F \<or> \<not> Bet A B C"
          using \<open>\<not> Col A B C\<close> bet_col by auto
        {
          assume "\<not> Bet A B C"
          then obtain J where P2: "C B J CongA D E F \<and> \<not> B C OS A J \<and> Coplanar A B C J \<and> A B J CongA G H I"
            using SumA_def assms(1) by blast
          have "G H I CongA A B J"
            using P2 not_conga_sym by blast
          then have "B Out A J"
            using \<open>H Out G I\<close> out_conga_out by blast
          then have "B C OS A J"
            using Col_perm \<open>\<not> Col A B C\<close> out_one_side by blast
          then have "False"
            using \<open>C B J CongA D E F \<and> \<not> B C OS A J \<and> Coplanar A B C J \<and> A B J CongA G H I\<close> by linarith
        }
        then have "False"
          using Col_def \<open>\<not> Col A B C\<close> by blast
        thus ?thesis by blast
      qed
    next
      assume "\<not> Col G H I"
      obtain J where P4: "C B J CongA D E F \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J"
        using SAMS_def assms(2) by auto
      {
        assume "Col J B C"
        have "J B C CongA D E F"
          by (simp add: P4 conga_left_comm)
        then have "Col D E F"
          using col_conga_col \<open>Col J B C\<close> by blast
        then have "False"
          using \<open>\<not> Col D E F\<close> by blast
      }
      then have "\<not> Col J B C" by blast
      have "A B J CongA G H I"
      proof -
        have "A B C D E F SumA A B J"
        proof -
          have "C B J CongA D E F"
            using P4 by simp
          moreover have "\<not> B C OS A J"
            by (simp add: P4)
          moreover have "Coplanar A B C J"
            by (simp add: P4)
          moreover have "A B J CongA A B J"
            by (metis \<open>\<not> Col A B C\<close> \<open>\<not> Col J B C\<close> col_trivial_1 conga_refl)
          ultimately show ?thesis
            using SumA_def by blast
        qed
        then show ?thesis
          using assms(1) suma2__conga by auto
      qed
      have "\<not> Col J B A"
        using \<open>A B J CongA G H I\<close> \<open>\<not> Col G H I\<close> col_conga_col not_col_permutation_3 by blast
      have "A B C LeA A B J"
      proof -
        have "C InAngle A B J"
          by (metis Col_perm P4 \<open>\<not> Col A B C\<close> \<open>\<not> Col J B A\<close> \<open>\<not> Col J B C\<close> cop_nos__ts coplanar_perm_7 coplanar_perm_8 invert_two_sides l9_2 os_ts__inangle)
        moreover have "A B C CongA A B C"
          using calculation in_angle_asym inangle3123 inangle_distincts by auto
        ultimately show ?thesis
          using inangle__lea by blast
      qed
      thus ?thesis
        using \<open>A B J CongA G H I\<close> conga__lea lea_trans by blast
    qed
  qed
qed

lemma sams_suma__lea456789:
  assumes "A B C D E F SumA G H I" and
    "SAMS A B C D E F"
  shows "D E F LeA G H I"
proof -
  have "D E F A B C SumA G H I"
    by (simp add: assms(1) suma_sym)
  moreover have "SAMS D E F A B C"
    using assms(2) sams_sym by blast
  ultimately show ?thesis
    using sams_suma__lea123789 by auto
qed

lemma sams_lea2__sams:
  assumes "SAMS A' B' C' D' E' F'" and
    "A B C LeA A' B' C'" and
    "D E F LeA D' E' F'"
  shows "SAMS A B C D E F"
proof -
  obtain A0 where "B Midpoint A A0"
    using symmetric_point_construction by auto
  obtain A'0 where "B' Midpoint A' A'0"
    using symmetric_point_construction by auto
  have "D E F LeA C B A0"
  proof -
    have "D' E' F' LeA C B A0"
    proof -
      have "D' E' F' LeA C' B' A'0"
        by (metis \<open>B' Midpoint A' A'0\<close> assms(1) assms(2) lea_distincts midpoint_bet midpoint_distinct_2 sams_chara)
      moreover have "C' B' A'0 LeA C B A0"
        by (metis Mid_cases \<open>B Midpoint A A0\<close> \<open>B' Midpoint A' A'0\<close> assms(2) l11_36_aux2 l7_3_2 lea_comm lea_distincts midpoint_bet sym_preserve_diff)
      ultimately show ?thesis
        using lea_trans by blast
    qed
    moreover have "D E F LeA D' E' F'"
      using assms(3) by auto
    ultimately show ?thesis
      using \<open>D' E' F' LeA C B A0\<close> assms(3) lea_trans by blast
  qed
  then show ?thesis
    by (metis \<open>B Midpoint A A0\<close> assms(2) lea_distincts midpoint_bet sams_chara)
qed

lemma sams_lea456_suma2__lea:
  assumes "D E F LeA D' E' F'" and
    "SAMS A B C D' E' F'" and
    "A B C D E F SumA G H I" and
    "A B C D' E' F' SumA G' H' I'"
  shows "G H I LeA G' H' I'"
proof cases
  assume "E' Out D' F'"
  have "G H I CongA G' H' I'"
  proof -
    have "G H I CongA A B C"
    proof -
      have "A B C D E F SumA G H I"
        by (simp add: assms(3))
      moreover have "E Out D F"
        using \<open>E' Out D' F'\<close> assms(1) out_lea__out by blast
      ultimately show ?thesis
        using conga_sym out546_suma__conga by blast
    qed
    moreover have "A B C CongA G' H' I'"
      using \<open>E' Out D' F'\<close> assms(4) out546_suma__conga by blast
    ultimately show ?thesis
      using conga_trans by blast
  qed
  thus ?thesis
    by (simp add: conga__lea)
next
  assume T1: "\<not> E' Out D' F'"
  show ?thesis
  proof cases
    assume T2: "Col A B C"
    have "E' Out D' F' \<or> \<not> Bet A B C"
      using assms(2) SAMS_def by simp
    {
      assume "\<not> Bet A B C"
      then have "B Out A C"
        by (simp add: T2 l6_4_2)
      have "G H I LeA G' H' I'"
      proof -
        have "D E F LeA D' E' F'"
          by (simp add: assms(1))
        moreover have "D E F CongA G H I"
          using \<open>B Out A C\<close> assms(3) out213_suma__conga by auto
        moreover have "D' E' F' CongA G' H' I'"
          using \<open>B Out A C\<close> assms(4) out213_suma__conga by auto
        ultimately show ?thesis
          using l11_30 by blast
      qed
    }
    thus ?thesis
      using T1 \<open>E' Out D' F' \<or> \<not> Bet A B C\<close> by auto
  next
    assume "\<not> Col A B C"
    show ?thesis
    proof cases
      assume "Col D' E' F'"
      have "SAMS D' E' F' A B C"
        by (simp add: assms(2) sams_sym)
      {
        assume "\<not> Bet D' E' F'"
        then have "G H I LeA G' H' I'"
          using not_bet_out T1 \<open>Col D' E' F'\<close> by auto
      }
      thus ?thesis
        by (metis assms(2) assms(3) assms(4) bet_lea__bet l11_31_2 sams_suma__lea456789 suma_distincts)
    next
      assume "\<not> Col D' E' F'"
      show ?thesis
      proof cases
        assume "Col D E F"
        have "\<not> Bet D E F"
          using bet_lea__bet Col_def \<open>\<not> Col D' E' F'\<close> assms(1) by blast
        thus ?thesis
        proof -
          have "A B C LeA G' H' I'"
            using assms(2) assms(4) sams_suma__lea123789 by auto
          moreover have "A B C CongA G H I"
            by (meson \<open>Col D E F\<close> \<open>\<not> Bet D E F\<close> assms(3) or_bet_out out213_suma__conga suma_sym)
          moreover have "G' H' I' CongA G' H' I'"
          proof -
            have "G' \<noteq> H'"
              using calculation(1) lea_distincts by blast
            moreover have "H' \<noteq> I'"
              using \<open>A B C LeA G' H' I'\<close> lea_distincts by blast
            ultimately show ?thesis
              using conga_refl by auto
          qed
          ultimately show ?thesis
            using l11_30 by blast
        qed
      next
        assume "\<not> Col D E F"
        show ?thesis
        proof cases
          assume "Col G' H' I'"
          show ?thesis
          proof cases
            assume "Bet G' H' I'"
            show ?thesis
            proof -
              have "G \<noteq> H"
                using assms(3) suma_distincts by auto
              moreover have "I \<noteq> H"
                using assms(3) suma_distincts by blast
              moreover have "G' \<noteq> H'"
                using assms(4) suma_distincts by auto
              moreover have "I' \<noteq> H'"
                using assms(4) suma_distincts by blast
              ultimately show ?thesis
                by (simp add: \<open>Bet G' H' I'\<close> l11_31_2)
            qed
          next
            assume "\<not> Bet G' H' I'"
            have "B Out A C"
            proof -
              have "H' Out G' I'"
                using \<open>Col G' H' I'\<close> l6_4_2 by (simp add: \<open>\<not> Bet G' H' I'\<close>)
              moreover have "A B C LeA G' H' I'" using sams_suma__lea123789
                using assms(2) assms(4) by auto
              ultimately show ?thesis
                using out_lea__out by blast
            qed
            then have "Col A B C"
              using Col_perm out_col by blast
            then have "False"
              using \<open>\<not> Col A B C\<close> by auto
            thus ?thesis by blast
          qed
        next
          assume "\<not> Col G' H' I'"
          obtain F'1 where P5: "C B F'1 CongA D' E' F' \<and> \<not> B C OS A F'1 \<and> \<not> A B TS C F'1 \<and> Coplanar A B C F'1"
            using SAMS_def assms(2) by auto
          have P6: "D E F LeA C B F'1"
          proof -
            have "D E F CongA D E F"
              using \<open>\<not> Col D E F\<close> conga_refl not_col_distincts by fastforce
            moreover have "D' E' F' CongA C B F'1"
              by (simp add: P5 conga_sym)
            ultimately show ?thesis
              using assms(1) l11_30 by blast
          qed
          then obtain F1 where P6: "F1 InAngle C B F'1 \<and> D E F CongA C B F1"
            using LeA_def by auto
          have "A B F'1 CongA G' H' I'"
          proof -
            have "A B C D' E' F' SumA A B F'1"
            proof -
              have "C B F'1 CongA D' E' F'"
                using P5 by blast
              moreover have "\<not> B C OS A F'1"
                using P5 by auto
              moreover have "Coplanar A B C F'1"
                by (simp add: P5)
              moreover have "A B F'1 CongA A B F'1"
              proof -
                have "A \<noteq> B"
                  using \<open>\<not> Col A B C\<close> col_trivial_1 by blast
                moreover have "B \<noteq> F'1"
                  using P6 inangle_distincts by auto
                ultimately show ?thesis
                  using conga_refl by auto
              qed
              ultimately show ?thesis
                using SumA_def by blast
            qed
            moreover have "A B C D' E' F' SumA G' H' I'"
              by (simp add: assms(4))
            ultimately show ?thesis
              using suma2__conga by auto
          qed
          have "\<not> Col A B F'1"
            using \<open>A B F'1 CongA G' H' I'\<close> \<open>\<not> Col G' H' I'\<close> col_conga_col by blast
          have "\<not> Col C B F'1"
          proof -
            have "\<not> Col D' E' F'"
              by (simp add: \<open>\<not> Col D' E' F'\<close>)
            moreover have "D' E' F' CongA C B F'1"
              using P5 not_conga_sym by blast
            ultimately show ?thesis
              using ncol_conga_ncol by blast
          qed
          show ?thesis
          proof -
            have "A B F1 LeA A B F'1"
            proof -
              have "F1 InAngle A B F'1"
              proof -
                have "F1 InAngle F'1 B A"
                proof -
                  have "F1 InAngle F'1 B C"
                    by (simp add: P6 l11_24)
                  moreover have "C InAngle F'1 B A"
                  proof -
                    have "B C TS A F'1"
                      using Col_perm P5 \<open>\<not> Col A B C\<close> \<open>\<not> Col C B F'1\<close> cop_nos__ts ncoplanar_perm_12 by blast
                    obtain X where "Col X B C \<and> Bet A X F'1"
                      using TS_def \<open>B C TS A F'1\<close> by auto
                    have "Bet F'1 X A"
                      using Bet_perm \<open>Col X B C \<and> Bet A X F'1\<close> by blast
                    moreover have "(X = B) \<or> (B Out X C)"
                    proof -
                      have "B A OS X C"
                      proof -
                        have "A B OS X F'1"
                          by (metis \<open>Col X B C \<and> Bet A X F'1\<close> \<open>\<not> Col A B C\<close> \<open>\<not> Col A B F'1\<close> bet_out_1 calculation out_one_side)
                        moreover have "A B OS F'1 C"
                          using Col_perm P5 \<open>\<not> Col A B C\<close> \<open>\<not> Col A B F'1\<close> cop_nos__ts one_side_symmetry by blast
                        ultimately show ?thesis
                          using invert_one_side one_side_transitivity by blast
                      qed
                      thus ?thesis
                        using Col_cases \<open>Col X B C \<and> Bet A X F'1\<close> col_one_side_out by blast
                    qed
                    ultimately show ?thesis
                      by (metis InAngle_def \<open>\<not> Col A B C\<close> \<open>\<not> Col A B F'1\<close> not_col_distincts)
                  qed
                  ultimately show ?thesis
                    using in_angle_trans by blast
                qed
                then show ?thesis
                  using l11_24 by blast
              qed
              moreover have "A B F1 CongA A B F1"
              proof -
                have "A \<noteq> B"
                  using \<open>\<not> Col A B C\<close> col_trivial_1 by blast
                moreover have "B \<noteq> F1"
                  using P6 conga_diff56 by blast
                ultimately show ?thesis
                  using conga_refl by auto
              qed
              ultimately show ?thesis
                by (simp add: inangle__lea)
            qed
            moreover have "A B F1 CongA G H I"
            proof -
              have "A B C D E F SumA A B F1"
              proof -
                have "B C TS F1 A"
                proof -
                  have "B C TS F'1 A"
                  proof -
                    have "B C TS A F'1"
                      using Col_perm P5 \<open>\<not> Col A B C\<close> \<open>\<not> Col C B F'1\<close> cop_nos__ts ncoplanar_perm_12 by blast
                    thus ?thesis
                      using l9_2 by blast
                  qed
                  moreover have "B C OS F'1 F1"
                  proof -
                    have "\<not> Col C B F'1"
                      by (simp add: \<open>\<not> Col C B F'1\<close>)
                    moreover have "\<not> Col B C F1"
                    proof -
                      have "\<not> Col D E F"
                        using \<open>\<not> Col D E F\<close> by auto
                      moreover have "D E F CongA C B F1"
                        by (simp add: P6)
                      ultimately show ?thesis
                        using ncol_conga_ncol not_col_permutation_4 by blast
                    qed
                    moreover have "F1 InAngle C B F'1" using P6 by blast
                    ultimately show ?thesis
                      using in_angle_one_side invert_one_side one_side_symmetry by blast
                  qed
                  ultimately show ?thesis
                    using l9_8_2 by blast
                qed
                thus ?thesis
                proof -
                  have "C B F1 CongA D E F"
                    using P6 not_conga_sym by blast
                  moreover have "\<not> B C OS A F1"
                    using \<open>B C TS F1 A\<close> l9_9 one_side_symmetry by blast
                  moreover have "Coplanar A B C F1"
                    using \<open>B C TS F1 A\<close> ncoplanar_perm_9 ts__coplanar by blast
                  moreover have "A B F1 CongA A B F1"
                  proof -
                    have "A \<noteq> B"
                      using \<open>\<not> Col A B C\<close> col_trivial_1 by blast
                    moreover have "B \<noteq> F1"
                      using P6 conga_diff56 by blast
                    ultimately show ?thesis
                      using conga_refl by auto
                  qed
                  ultimately show ?thesis
                    using SumA_def by blast
                qed
              qed
              moreover have "A B C D E F SumA G H I"
                by (simp add: assms(3))
              ultimately show ?thesis
                using suma2__conga by auto
            qed
            ultimately show ?thesis
              using \<open>A B F'1 CongA G' H' I'\<close> l11_30 by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma sams_lea123_suma2__lea:
  assumes "A B C LeA A' B' C'" and
    "SAMS A' B' C' D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D E F SumA G' H' I'"
  shows "G H I LeA G' H' I'"
  by (meson assms(1) assms(2) assms(3) assms(4) sams_lea456_suma2__lea sams_sym suma_sym)

lemma sams_lea2_suma2__lea:
  assumes "A B C LeA A' B' C'" and
    "D E F LeA D' E' F'" and
    "SAMS A' B' C' D' E' F'" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "G H I LeA G' H' I'"
proof -
  obtain G'' H'' I'' where "A B C D' E' F' SumA G'' H'' I''"
    using assms(4) assms(5) ex_suma suma_distincts by presburger
  have "G H I LeA G'' H'' I''"
  proof -
    have "D E F LeA D' E' F'"
      by (simp add: assms(2))
    moreover have "SAMS A B C D' E' F'"
    proof -
      have "SAMS A' B' C' D' E' F'"
        by (simp add: assms(3))
      moreover have "A B C LeA A' B' C'"
        using assms(1) by auto
      moreover have "D' E' F' LeA D' E' F'"
        using assms(2) lea_distincts lea_refl by blast
      ultimately show ?thesis
        using sams_lea2__sams by blast
    qed
    moreover have "A B C D E F SumA G H I"
      by (simp add: assms(4))
    moreover have "A B C D' E' F' SumA G'' H'' I''"
      by (simp add: \<open>A B C D' E' F' SumA G'' H'' I''\<close>)
    ultimately show ?thesis
      using sams_lea456_suma2__lea by blast
  qed
  moreover have "G'' H'' I'' LeA G' H' I'"
    using sams_lea123_suma2__lea assms(3) assms(5) \<open>A B C D' E' F' SumA G'' H'' I''\<close> assms(1) by blast
  ultimately show ?thesis
    using lea_trans by blast
qed

lemma sams2_suma2__conga456:
  assumes "SAMS A B C D E F" and
    "SAMS A B C D' E' F'" and
    "A B C D E F SumA G H I" and
    "A B C D' E' F' SumA G H I"
  shows "D E F CongA D' E' F'"
proof cases
  assume "Col A B C"
  show ?thesis
  proof cases
    assume P2: "Bet A B C"
    then have "E Out D F"
      using assms(1) SAMS_def by blast
    moreover have "E' Out D' F'"
      using P2 assms(2) SAMS_def by blast
    ultimately show ?thesis
      by (simp add: l11_21_b)
  next
    assume "\<not> Bet A B C"
    then have "B Out A C"
      using \<open>Col A B C\<close> or_bet_out by blast
    show ?thesis
    proof -
      have "D E F CongA G H I"
      proof -
        have "A B C D E F SumA G H I"
          by (simp add: assms(3))
        thus ?thesis
          using \<open>B Out A C\<close> out213_suma__conga by auto
      qed
      moreover have "G H I CongA D' E' F'"
      proof -
        have "A B C D' E' F' SumA G H I"
          by (simp add: assms(4))
        then have "D' E' F' CongA G H I"
          using \<open>B Out A C\<close> out213_suma__conga by auto
        thus ?thesis
          using not_conga_sym by blast
      qed
      ultimately show ?thesis
        using not_conga by blast
    qed
  qed
next
  assume "\<not> Col A B C"
  obtain J where T1: "C B J CongA D E F \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J"
    using assms(1) SAMS_def by blast
  have T1A: "C B J CongA D E F"
    using T1 by simp
  have T1B: "\<not> B C OS A J"
    using T1 by simp
  have T1C: "\<not> A B TS C J"
    using T1 by simp
  have T1D: "Coplanar A B C J"
    using T1 by simp
  obtain J' where T2: "C B J' CongA D' E' F' \<and> \<not> B C OS A J' \<and> \<not> A B TS C J' \<and> Coplanar A B C J'"
    using assms(2) SAMS_def by blast
  have T2A: "C B J' CongA D' E' F'"
    using T2 by simp
  have T2B: "\<not> B C OS A J'"
    using T2 by simp
  have T2C: "\<not> A B TS C J'"
    using T2 by simp
  have T2D: "Coplanar A B C J'"
    using T2 by simp
  have T3: "C B J CongA C B J'"
  proof -
    have "A B J CongA A B J'"
    proof -
      have "A B J CongA G H I"
      proof -
        have "A B C D E F SumA A B J"
          using SumA_def T1A T1B T1D \<open>\<not> Col A B C\<close> conga_distinct conga_refl not_col_distincts by auto
        thus ?thesis
          using assms(3) suma2__conga by blast
      qed
      moreover have "G H I CongA A B J'"
      proof -
        have "A B C D' E' F' SumA G H I"
          by (simp add: assms(4))
        moreover have "A B C D' E' F' SumA A B J'"
          using SumA_def T2A T2B T2D \<open>\<not> Col A B C\<close> conga_distinct conga_refl not_col_distincts by auto
        ultimately show ?thesis
          using suma2__conga by auto
      qed
      ultimately show ?thesis
        using conga_trans by blast
    qed
    have "B Out J J' \<or> A B TS J J'"
    proof -
      have "Coplanar A B J J'"
        using T1D T2D \<open>\<not> Col A B C\<close> coplanar_trans_1 ncoplanar_perm_8 not_col_permutation_2 by blast
      moreover have "A B J CongA A B J'"
        by (simp add: \<open>A B J CongA A B J'\<close>)
      ultimately show ?thesis
        by (simp add: conga_cop__or_out_ts)
    qed
    {
      assume "B Out J J'"
      then have "C B J CongA C B J'"
        by (metis Out_cases \<open>\<not> Col A B C\<close> bet_out between_trivial not_col_distincts out2__conga)
    }
    {
      assume "A B TS J J'"
      then have "A B OS J C"
        by (meson T1C T1D TS_def \<open>\<not> Col A B C\<close> cop_nts__os not_col_permutation_2 one_side_symmetry)
      then have "A B TS C J'"
        using \<open>A B TS J J'\<close> l9_8_2 by blast
      then have "False"
        by (simp add: T2C)
      then have "C B J CongA C B J'"
        by blast
    }
    thus ?thesis
      using \<open>B Out J J' \<Longrightarrow> C B J CongA C B J'\<close> \<open>B Out J J' \<or> A B TS J J'\<close> by blast
  qed
  then have "C B J CongA D' E' F'"
    using T2A not_conga by blast
  thus ?thesis
    using T1A not_conga not_conga_sym by blast
qed

lemma sams2_suma2__conga123:
  assumes "SAMS A B C D E F" and
    "SAMS A' B' C' D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D E F SumA G H I"
  shows "A B C CongA A' B' C'"
proof -
  have "SAMS D E F A B C"
    by (simp add: assms(1) sams_sym)
  moreover have "SAMS D E F A' B' C'"
    by (simp add: assms(2) sams_sym)
  moreover have "D E F  A B C SumA G H I"
    by (simp add: assms(3) suma_sym)
  moreover have "D E F A' B' C' SumA G H I"
    using assms(4) suma_sym by blast
  ultimately show ?thesis
    using sams2_suma2__conga456 by auto
qed

lemma suma_assoc_1:
  assumes "SAMS A B C D E F" and
    "SAMS D E F G H I" and
    "A B C D E F SumA A' B' C'" and
    "D E F G H I SumA D' E' F'" and
    "A' B' C' G H I SumA K L M"
  shows "A B C D' E' F' SumA K L M"
proof -
  obtain A0 where P1: "Bet A B A0 \<and> Cong A B B A0"
    using Cong_perm segment_construction by blast
  obtain D0 where P2: "Bet D E D0 \<and> Cong D E E D0"
    using Cong_perm segment_construction by blast
  show ?thesis
  proof cases
    assume "Col A B C"
    show ?thesis
    proof cases
      assume "Bet A B C"
      then have "E Out D F"
        using SAMS_def assms(1) by simp
      show ?thesis
      proof -
        have "A' B' C' CongA A B C"
          using assms(3) \<open>E Out D F\<close> conga_sym out546_suma__conga by blast
        moreover have "G H I CongA D' E' F'"
          using assms(4) \<open>E Out D F\<close> out213_suma__conga by auto
        ultimately show ?thesis
          by (meson Tarski_neutral_dimensionless.conga3_suma__suma Tarski_neutral_dimensionless.suma2__conga Tarski_neutral_dimensionless_axioms assms(5))
      qed
    next
      assume "\<not> Bet A B C"
      then have "B Out A C"
        using \<open>Col A B C\<close> l6_4_2 by auto
      have "A \<noteq> B"
        using \<open>B Out A C\<close> out_distinct by auto
      have "B \<noteq> C"
        using \<open>\<not> Bet A B C\<close> between_trivial by auto
      have "D' \<noteq> E'"
        using assms(4) suma_distincts by blast
      have "E' \<noteq> F'"
        using assms(4) suma_distincts by auto
      show ?thesis
      proof -
        obtain K0 L0 M0 where P3:"A B C D' E' F' SumA K0 L0 M0"
          using ex_suma \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> \<open>D' \<noteq> E'\<close> \<open>E' \<noteq> F'\<close> by presburger
        moreover have "A B C CongA A B C"
          using \<open>A \<noteq> B\<close> \<open>B \<noteq> C\<close> conga_refl by auto
        moreover have "D' E' F' CongA D' E' F'"
          using \<open>D' \<noteq> E'\<close> \<open>E' \<noteq> F'\<close> conga_refl by auto
        moreover have "K0 L0 M0 CongA K L M"
        proof -
          have "K0 L0 M0 CongA D' E' F'"
            using P3 \<open>B Out A C\<close> conga_sym out213_suma__conga by blast
          moreover have "D' E' F' CongA K L M"
          proof -
            have "D E F G H I SumA D' E' F'"
              by (simp add: assms(4))
            moreover have "D E F G H I SumA K L M"
              by (meson Tarski_neutral_dimensionless.conga3_suma__suma Tarski_neutral_dimensionless.out213_suma__conga Tarski_neutral_dimensionless.sams2_suma2__conga456 Tarski_neutral_dimensionless.suma2__conga Tarski_neutral_dimensionless_axioms \<open>B Out A C\<close> assms(2) assms(3) assms(5) calculation not_conga_sym)
            ultimately show ?thesis
              using suma2__conga by auto
          qed
          ultimately show ?thesis
            using not_conga by blast
        qed
        ultimately show ?thesis
          using conga3_suma__suma by blast
      qed
    qed
  next
    assume T1: "\<not> Col A B C"
    have "\<not> Col C B A0"
      by (metis Col_def P1 \<open>\<not> Col A B C\<close> cong_diff l6_16_1)
    show ?thesis
    proof cases
      assume "Col D E F"
      show ?thesis
      proof cases
        assume "Bet D E F"
        have "H Out G I" using SAMS_def assms(2) \<open>Bet D E F\<close> by blast
        have "A B C D E F SumA A' B' C'"
          by (simp add: assms(3))
        moreover have "A B C CongA A B C"
          by (metis \<open>\<not> Col A B C\<close> conga_pseudo_refl conga_right_comm not_col_distincts)
        moreover have "D E F CongA D' E' F'"
          using \<open>H Out G I\<close> assms(4) out546_suma__conga by auto
        moreover have "A' B' C' CongA K L M"
          using \<open>H Out G I\<close> assms(5) out546_suma__conga by auto
        ultimately show ?thesis
          using conga3_suma__suma by blast
      next
        assume "\<not> Bet D E F"
        then have "E Out D F"
          using not_bet_out by (simp add: \<open>Col D E F\<close>)
        show ?thesis
        proof -
          have "A' B' C' CongA A B C"
            using assms(3) \<open>E Out D F\<close> conga_sym out546_suma__conga by blast
          moreover have "G H I CongA D' E' F'"
            using out546_suma__conga \<open>E Out D F\<close> assms(4) out213_suma__conga by auto
          moreover have "K L M CongA K L M"
          proof -
            have "K \<noteq> L \<and> L \<noteq> M"
              using assms(5) suma_distincts by blast
            thus ?thesis
              using conga_refl by auto
          qed
          ultimately show ?thesis
            using assms(5) conga3_suma__suma by blast
        qed
      qed
    next
      assume "\<not> Col D E F"
      then have "\<not> Col F E D0"
        by (metis Col_def P2 cong_diff l6_16_1 not_col_distincts)
      show ?thesis
      proof cases
        assume "Col G H I"
        show ?thesis
        proof cases
          assume "Bet G H I"
          have "SAMS G H I D E F"
            by (simp add: assms(2) sams_sym)
          then have "E Out D F"
            using SAMS_def \<open>Bet G H I\<close> by blast
          then have "Col D E F"
            using Col_perm out_col by blast
          then have "False"
            using \<open>\<not> Col D E F\<close> by auto
          thus ?thesis by simp
        next
          assume "\<not> Bet G H I"
          then have "H Out G I"
            using SAMS_def by (simp add: \<open>Col G H I\<close> l6_4_2)
          show ?thesis
          proof -
            have "A B C CongA A B C"
              by (metis \<open>\<not> Col A B C\<close> conga_refl not_col_distincts)
            moreover have "D E F CongA D' E' F'"
              using assms(4) out546_suma__conga \<open>H Out G I\<close> by auto
            moreover have "A' B' C' CongA K L M"
              using \<open>H Out G I\<close> assms(5) out546_suma__conga by auto
            ultimately show ?thesis
              using assms(3) conga3_suma__suma by blast
          qed
        qed
      next
        assume "\<not> Col G H I"
        have "\<not> B C OS A A0"
          using P1 col_trivial_1 one_side_chara by blast
        have "E F TS D D0"
          by (metis P2 \<open>\<not> Col D E F\<close> \<open>\<not> Col F E D0\<close> bet__ts bet_col between_trivial not_col_permutation_1)
        show ?thesis
        proof cases
          assume "Col A' B' C'"
          show ?thesis
          proof cases
            assume "Bet A' B' C'"
            show ?thesis
            proof cases
              assume "Col D' E' F'"
              show ?thesis
              proof cases
                assume "Bet D' E' F'"
                have "A B C CongA G H I"
                proof -
                  have "A B C CongA D0 E F"
                  proof -
                    have "SAMS A B C D E F"
                      by (simp add: assms(1))
                    moreover have "SAMS D0 E F D E F"
                      by (metis P2 \<open>\<not> Col D E F\<close> \<open>\<not> Col F E D0\<close> bet__sams between_symmetry not_col_distincts sams_right_comm)
                    moreover have "A B C D E F SumA A' B' C'"
                      by (simp add: assms(3))
                    moreover have "D0 E F D E F SumA A' B' C'"
                    proof -
                      have "D E F D0 E F SumA A' B' C'"
                      proof -
                        have "F E D0 CongA D0 E F"
                          by (metis \<open>\<not> Col F E D0\<close> col_trivial_1 col_trivial_2 conga_pseudo_refl)
                        moreover have "\<not> E F OS D D0"
                          using P2 col_trivial_1 one_side_chara by blast
                        moreover have "Coplanar D E F D0"
                          by (meson P2 bet__coplanar ncoplanar_perm_1)
                        moreover have "D E D0 CongA A' B' C'"
                          using assms(3) P2 \<open>Bet A' B' C'\<close> \<open>\<not> Col F E D0\<close> conga_line not_col_distincts suma_distincts by auto
                        ultimately show ?thesis
                          using SumA_def by blast
                      qed
                      thus ?thesis
                        by (simp add: \<open>D E F D0 E F SumA A' B' C'\<close> suma_sym)
                    qed
                    ultimately show ?thesis
                      using sams2_suma2__conga123 by blast
                  qed
                  moreover have "D0 E F CongA G H I"
                  proof -
                    have "SAMS D E F D0 E F"
                      using P2 \<open>\<not> Col D E F\<close> \<open>\<not> Col F E D0\<close> bet__sams not_col_distincts sams_right_comm by auto
                    moreover have "D E F D0 E F SumA D' E' F'"
                    proof -
                      have "F E D0 CongA D0 E F"
                        by (metis (no_types) \<open>\<not> Col F E D0\<close> col_trivial_1 col_trivial_2 conga_pseudo_refl)
                      moreover have "\<not> E F OS D D0"
                        using P2 col_trivial_1 one_side_chara by blast
                      moreover have "Coplanar D E F D0"
                        using P2 bet__coplanar ncoplanar_perm_1 by blast
                      moreover have "D E D0 CongA D' E' F'"
                        using assms(3) P2 \<open>Bet D' E' F'\<close> \<open>\<not> Col F E D0\<close> assms(4) conga_line not_col_distincts suma_distincts by auto
                      ultimately show ?thesis
                        using SumA_def by blast
                    qed
                    ultimately show ?thesis
                      using assms(2) assms(4) sams2_suma2__conga456 by auto
                  qed
                  ultimately show ?thesis
                    using conga_trans by blast
                qed
                then have "G H I CongA A B C"
                  using not_conga_sym by blast
                have "D' E' F' A B C SumA K L M"
                proof -
                  have "A' B' C' CongA D' E' F'"
                    by (metis Tarski_neutral_dimensionless.suma_distincts Tarski_neutral_dimensionless_axioms \<open>Bet A' B' C'\<close> \<open>Bet D' E' F'\<close> assms(4) assms(5) conga_line)
                  then show ?thesis
                    by (meson Tarski_neutral_dimensionless.conga3_suma__suma Tarski_neutral_dimensionless.suma2__conga Tarski_neutral_dimensionless_axioms \<open>G H I CongA A B C\<close> assms(5))
                qed
                thus ?thesis
                  by (simp add: suma_sym)
              next
                assume "\<not> Bet D' E' F'"
                then have "E' Out D' F'"
                  by (simp add: \<open>Col D' E' F'\<close> l6_4_2)
                have "D E F LeA D' E' F'"
                  using assms(2) assms(4) sams_suma__lea123789 by blast
                then have "E Out D F"
                  using \<open>E' Out D' F'\<close> out_lea__out by blast
                then have "Col D E F"
                  using Col_perm out_col by blast
                then have "False"
                  using \<open>\<not> Col D E F\<close> by auto
                thus ?thesis by simp
              qed
            next
              assume "\<not> Col D' E' F'"
              have "D E F CongA C B A0"
              proof -
                have "SAMS A B C D E F"
                  by (simp add: assms(1))
                moreover have "SAMS A B C C B A0"
                  using P1 \<open>\<not> Col A B C\<close> \<open>\<not> Col C B A0\<close> bet__sams not_col_distincts by auto
                moreover have "A B C D E F SumA A' B' C'"
                  by (simp add: assms(3))
                moreover have "A B C C B A0 SumA A' B' C'"
                proof -
                  have "A B C C B A0 SumA A B A0"
                    by (metis P1 \<open>\<not> Col A B C\<close> \<open>\<not> Col C B A0\<close> bet__suma col_trivial_1 col_trivial_2)
                  moreover have "A B C CongA A B C"
                    using \<open>SAMS A B C C B A0\<close> calculation sams2_suma2__conga123 by auto
                  moreover have "C B A0 CongA C B A0"
                    using \<open>SAMS A B C C B A0\<close> calculation(1) sams2_suma2__conga456 by auto
                  moreover have "A B A0 CongA A' B' C'"
                    using P1 \<open>Bet A' B' C'\<close> \<open>\<not> Col C B A0\<close> assms(3) conga_line not_col_distincts suma_distincts by auto
                  ultimately show ?thesis
                    using conga3_suma__suma by blast
                qed
                ultimately show ?thesis
                  using sams2_suma2__conga456 by blast
              qed
              have "SAMS C B A0 G H I"
              proof -
                have "D E F CongA C B A0"
                  by (simp add: \<open>D E F CongA C B A0\<close>)
                moreover have "G H I CongA G H I"
                  using \<open>\<not> Col G H I\<close> conga_refl not_col_distincts by fastforce
                moreover have "SAMS D E F G H I"
                  by (simp add: assms(2))
                ultimately show ?thesis
                  using conga2_sams__sams by blast
              qed
              then obtain J where P3: "A0 B J CongA G H I \<and> \<not> B A0 OS C J \<and> \<not> C B TS A0 J \<and> Coplanar C B A0 J"
                using SAMS_def by blast
              obtain F1 where P4: "F E F1 CongA G H I \<and> \<not> E F OS D F1 \<and> \<not> D E TS F F1 \<and> Coplanar D E F F1"
                using SAMS_def assms(2) by auto
              have "C B J CongA D' E' F'"
              proof -
                have "C B J CongA D E F1"
                proof -
                  have "(B A0 TS C J \<and> E F TS D F1) \<or> (B A0 OS C J \<and> E F OS D F1)"
                  proof -
                    have "B A0 TS C J"
                    proof -
                      have "Coplanar B A0 C J"
                        using P3 ncoplanar_perm_12 by blast
                      moreover have "\<not> Col C B A0"
                        by (simp add: \<open>\<not> Col C B A0\<close>)
                      moreover have "\<not> Col J B A0"
                        using P3 \<open>\<not> Col G H I\<close> col_conga_col not_col_permutation_3 by blast
                      moreover have "\<not> B A0 OS C J"
                        using P3 by simp
                      ultimately show ?thesis
                        by (simp add: cop_nos__ts)
                    qed
                    moreover have "E F TS D F1"
                    proof -
                      have "Coplanar E F D F1"
                        using P4 ncoplanar_perm_12 by blast
                      moreover have "\<not> Col D E F"
                        by (simp add: \<open>\<not> Col D E F\<close>)
                      moreover have "\<not> Col F1 E F"
                        using P4 \<open>\<not> Col G H I\<close> col_conga_col col_permutation_3 by blast
                      moreover have "\<not> E F OS D F1"
                        using P4 by auto
                      ultimately show ?thesis
                        by (simp add: cop_nos__ts)
                    qed
                    ultimately show ?thesis
                      by simp
                  qed
                  moreover have "C B A0 CongA D E F"
                    using \<open>D E F CongA C B A0\<close> not_conga_sym by blast
                  moreover have "A0 B J CongA F E F1"
                  proof -
                    have "A0 B J CongA G H I"
                      by (simp add: P3)
                    moreover have "G H I CongA F E F1"
                      using P4 not_conga_sym by blast
                    ultimately show ?thesis
                      using conga_trans by blast
                  qed
                  ultimately show ?thesis
                    using l11_22 by auto
                qed
                moreover have "D E F1 CongA D' E' F'"
                proof -
                  have "D E F G H I SumA D E F1"
                    using P4 SumA_def \<open>\<not> Col D E F\<close> conga_distinct conga_refl not_col_distincts by auto
                  moreover have "D E F G H I SumA D' E' F'"
                    by (simp add: assms(4))
                  ultimately show ?thesis
                    using suma2__conga by auto
                qed
                ultimately show ?thesis
                  using conga_trans by blast
              qed
              show ?thesis
              proof -
                have "A B C D' E' F' SumA A B J"
                proof -
                  have "C B TS J A"
                  proof -
                    have "C B TS A0 A"
                    proof -
                      have "B \<noteq> A0"
                        using \<open>\<not> Col C B A0\<close> not_col_distincts by blast
                      moreover have "\<not> Col B C A"
                        using Col_cases \<open>\<not> Col A B C\<close> by auto
                      moreover have "Bet A B A0"
                        by (simp add: P1)
                      ultimately show ?thesis
                        by (metis Bet_cases Col_cases \<open>\<not> Col C B A0\<close> bet__ts invert_two_sides not_col_distincts)
                    qed
                    moreover have "C B OS A0 J"
                    proof -
                      have "\<not> Col J C B"
                        using \<open>C B J CongA D' E' F'\<close> \<open>\<not> Col D' E' F'\<close> col_conga_col not_col_permutation_2 by blast
                      moreover have "\<not> Col A0 C B"
                        using Col_cases \<open>\<not> Col C B A0\<close> by blast
                      ultimately show ?thesis
                        using P3 cop_nos__ts by blast
                    qed
                    ultimately show ?thesis
                      using l9_8_2 by blast
                  qed
                  moreover have "C B J CongA D' E' F'"
                    by (simp add: \<open>C B J CongA D' E' F'\<close>)
                  moreover have "\<not> B C OS A J"
                    using calculation(1) invert_one_side l9_9_bis one_side_symmetry by blast
                  moreover have "Coplanar A B C J"
                    using calculation(1) ncoplanar_perm_15 ts__coplanar by blast
                  moreover have "A B J CongA A B J"
                  proof -
                    have "A \<noteq> B"
                      using \<open>\<not> Col A B C\<close> col_trivial_1 by auto
                    moreover have "B \<noteq> J"
                      using \<open>C B TS J A\<close> ts_distincts by blast
                    ultimately show ?thesis
                      using conga_refl by auto
                  qed
                  ultimately show ?thesis
                    using SumA_def by blast
                qed
                moreover have "A B J CongA K L M"
                proof -
                  have "A' B' C' G H I SumA A B J"
                  proof -
                    have "A B A0 CongA A' B' C'"
                      using P1 \<open>Bet A' B' C'\<close> \<open>\<not> Col A B C\<close> \<open>\<not> Col C B A0\<close> assms(5) conga_line not_col_distincts suma_distincts by auto
                    moreover have "A0 B J CongA G H I"
                      by (simp add: P3)
                    moreover have "A B A0 A0 B J SumA A B J"
                    proof -
                      have "A0 B J CongA A0 B J"
                      proof -
                        have "A0 \<noteq> B"
                          using \<open>\<not> Col C B A0\<close> col_trivial_2 by auto
                        moreover have "B \<noteq> J"
                          using CongA_def \<open>A0 B J CongA G H I\<close> by blast
                        ultimately show ?thesis
                          using conga_refl by auto
                      qed
                      moreover have "\<not> B A0 OS A J"
                        by (simp add: Col_def P1 col123__nos)
                      moreover have "Coplanar A B A0 J"
                        using P1 bet__coplanar by auto
                      moreover have "A B J CongA A B J"
                        using P1 \<open>\<not> Col A B C\<close> between_symmetry calculation(1) l11_13 not_col_distincts by blast
                      ultimately show ?thesis
                        using SumA_def by blast
                    qed
                    ultimately show ?thesis
                      by (meson conga3_suma__suma suma2__conga)
                  qed
                  moreover have "A' B' C' G H I SumA K L M"
                    by (simp add: assms(5))
                  ultimately show ?thesis
                    using suma2__conga by auto
                qed
                ultimately show ?thesis
                proof -
                  have "A B C CongA A B C \<and> D' E' F' CongA D' E' F'"
                    using CongA_def \<open>A B J CongA K L M\<close> \<open>C B J CongA D' E' F'\<close> conga_refl by presburger
                  then show ?thesis
                    using \<open>A B C D' E' F' SumA A B J\<close> \<open>A B J CongA K L M\<close> conga3_suma__suma by blast
                qed
              qed
            qed
          next
            assume "\<not> Bet A' B' C'"
            have "B Out A C"
            proof -
              have "A B C LeA A' B' C'" using assms(1) assms(3) sams_suma__lea123789 by auto
              moreover have "B' Out A' C'"
                using \<open>Col A' B' C'\<close> \<open>\<not> Bet A' B' C'\<close> or_bet_out by blast
              ultimately show ?thesis
                using out_lea__out by blast
            qed
            then have "Col A B C"
              using Col_perm out_col by blast
            then have "False"
              using \<open>\<not> Col A B C\<close> by auto
            thus ?thesis by simp
          qed
        next
          assume "\<not> Col A' B' C'"
          obtain C1 where P6: "C B C1 CongA D E F \<and> \<not> B C OS A C1 \<and> \<not> A B TS C C1 \<and> Coplanar A B C C1"
            using SAMS_def assms(1) by auto
          have P6A: "C B C1 CongA D E F"
            using P6 by simp
          have P6B: "\<not> B C OS A C1"
            using P6 by simp
          have P6C: "\<not> A B TS C C1"
            using P6 by simp
          have P6D: "Coplanar A B C C1"
            using P6 by simp
          have "A' B' C' CongA A B C1"
          proof -
            have "A B C D E F SumA A B C1"
              using P6A P6B P6D SumA_def \<open>\<not> Col A B C\<close> conga_distinct conga_refl not_col_distincts by auto
            moreover have "A B C D E F SumA A' B' C'"
              by (simp add: assms(3))
            ultimately show ?thesis
              using suma2__conga by auto
          qed
          have "B C1 OS C A"
          proof -
            have "B A OS C C1"
            proof -
              have "A B OS C C1"
              proof -
                have "\<not> Col C A B"
                  using Col_perm \<open>\<not> Col A B C\<close> by blast
                moreover have "\<not> Col C1 A B"
                  using \<open>\<not> Col A' B' C'\<close> \<open>A' B' C' CongA A B C1\<close> col_permutation_1 ncol_conga_ncol by blast
                ultimately show ?thesis
                  using P6C P6D cop_nos__ts by blast
              qed
              thus ?thesis
                by (simp add: invert_one_side)
            qed
            moreover have "B C TS A C1"
            proof -
              have "Coplanar B C A C1"
                using P6D ncoplanar_perm_12 by blast
              moreover have "\<not> Col C1 B C"
              proof -
                have "D E F CongA C1 B C"
                  using P6A conga_left_comm not_conga_sym by blast
                thus ?thesis
                  using  \<open>\<not> Col D E F\<close> ncol_conga_ncol by blast
              qed
              ultimately show ?thesis
                using T1 P6B cop_nos__ts by blast
            qed
            ultimately show ?thesis
              using os_ts1324__os one_side_symmetry by blast
          qed
          show ?thesis
          proof cases
            assume "Col D' E' F'"
            show ?thesis
            proof cases
              assume "Bet D' E' F'"
              obtain C0 where P7: "Bet C B C0 \<and> Cong C B B C0"
                using Cong_perm segment_construction by blast
              have "B C1 TS C C0"
                by (metis P7 \<open>B C1 OS C A\<close> bet__ts cong_diff_2 not_col_distincts one_side_not_col123)
              show ?thesis
              proof -
                have "A B C C B C0 SumA A B C0"
                proof -
                  have "C B C0 CongA C B C0"
                    by (metis P7 T1 cong_diff conga_line not_col_distincts)
                  moreover have "\<not> B C OS A C0"
                    using P7 bet_col col124__nos invert_one_side by blast
                  moreover have "Coplanar A B C C0"
                    using P7 bet__coplanar ncoplanar_perm_15 by blast
                  moreover have "A B C0 CongA A B C0"
                    by (metis P7 T1 cong_diff conga_refl not_col_distincts)
                  ultimately show ?thesis
                    using SumA_def by blast
                qed
                moreover have "A B C0 CongA K L M"
                proof -
                  have "A' B' C' G H I SumA A B C0"
                  proof -
                    have "A B C1 C1 B C0 SumA A B C0"
                      using \<open>B C1 TS C C0\<close> \<open>B C1 OS C A\<close> l9_8_2 ts__suma_1 by blast
                    moreover have "A B C1 CongA A' B' C'"
                      by (simp add: P6 \<open>A' B' C' CongA A B C1\<close> conga_sym)
                    moreover have "C1 B C0 CongA G H I"
                    proof -
                      have "SAMS C B C1 C1 B C0"
                        by (metis P7 \<open>B C1 TS C C0\<close> bet__sams ts_distincts)
                      moreover have "SAMS C B C1 G H I"
                      proof -
                        have "D E F CongA C B C1"
                          using P6A not_conga_sym by blast
                        moreover have "G H I CongA G H I"
                          using \<open>\<not> Col G H I\<close> conga_refl not_col_distincts by fastforce
                        moreover have "SAMS D E F G H I"
                          by (simp add: assms(2))
                        ultimately show ?thesis
                          using conga2_sams__sams by blast
                      qed
                      moreover have "C B C1 C1 B C0 SumA C B C0"
                        by (simp add: \<open>B C1 TS C C0\<close> ts__suma_1)
                      moreover have "C B C1 G H I SumA C B C0"
                      proof -
                        have "D E F G H I SumA D' E' F'"
                          by (simp add: assms(4))
                        moreover have "D E F CongA C B C1"
                          using P6A not_conga_sym by blast
                        moreover have "G H I CongA G H I"
                          using \<open>\<not> Col G H I\<close> conga_refl not_col_distincts by fastforce
                        moreover have "D' E' F' CongA C B C0" using P7 assms(4)
                          by (metis P6A Tarski_neutral_dimensionless.suma_distincts Tarski_neutral_dimensionless_axioms \<open>Bet D' E' F'\<close> cong_diff conga_diff1 conga_line)
                        ultimately show ?thesis
                          using conga3_suma__suma by blast
                      qed
                      ultimately show ?thesis
                        using sams2_suma2__conga456 by auto
                    qed
                    moreover have "A B C0 CongA A B C0"
                      by (metis P7 T1 cong_diff conga_refl not_col_distincts)
                    ultimately show ?thesis
                      using conga3_suma__suma by blast
                  qed
                  thus ?thesis
                    using assms(5) suma2__conga by auto
                qed
                moreover have "A B C CongA A B C"
                proof -
                  have "A \<noteq> B \<and> B \<noteq> C"
                    using T1 col_trivial_1 col_trivial_2 by auto
                  thus ?thesis
                    using conga_refl by auto
                qed
                moreover have "C B C0 CongA D' E' F'"
                proof -
                  have "C \<noteq> B"
                    using T1 col_trivial_2 by blast
                  moreover have "B \<noteq> C0"
                    using \<open>B C1 TS C C0\<close> ts_distincts by blast
                  moreover have "D' \<noteq> E'"
                    using assms(4) suma_distincts by blast
                  moreover have "E' \<noteq> F'"
                    using assms(4) suma_distincts by auto
                  ultimately show ?thesis
                    by (simp add: P7 \<open>Bet D' E' F'\<close> conga_line)
                qed
                ultimately show ?thesis
                  using conga3_suma__suma by blast
              qed
            next
              assume "\<not> Bet D' E' F'"
              then have "E' Out D' F'"
                by (simp add: \<open>Col D' E' F'\<close> l6_4_2)
              have "D E F LeA D' E' F'"
                using sams_suma__lea123789 assms(2) assms(4) by auto
              then have "E Out D F"
                using \<open>E' Out D' F'\<close> out_lea__out by blast
              then have "False"
                using Col_cases \<open>\<not> Col D E F\<close> out_col by blast
              thus ?thesis by simp
            qed
          next
            assume "\<not> Col D' E' F'"
            have "SAMS C B C1 G H I"
            proof -
              have "D E F CongA C B C1"
                using P6A not_conga_sym by blast
              moreover have "G H I CongA G H I"
                using \<open>\<not> Col G H I\<close> conga_refl not_col_distincts by fastforce
              ultimately show ?thesis
                using assms(2) conga2_sams__sams by blast
            qed
            then obtain J where P7: "C1 B J CongA G H I \<and> \<not> B C1 OS C J \<and> \<not> C B TS C1 J \<and> Coplanar C B C1 J"
              using SAMS_def by blast
            have P7A: "C1 B J CongA G H I"
              using P7 by simp
            have P7B: "\<not> B C1 OS C J"
              using P7 by simp
            have P7C: "\<not> C B TS C1 J"
              using P7 by simp
            have P7D: "Coplanar C B C1 J"
              using P7 by simp
            obtain F1 where P8: "F E F1 CongA G H I \<and> \<not> E F OS D F1 \<and> \<not> D E TS F F1 \<and> Coplanar D E F F1"
              using SAMS_def assms(2) by auto
            have P8A: "F E F1 CongA G H I"
              using P8 by simp
            have P8B: "\<not> E F OS D F1"
              using P8 by simp
            have P8C: "\<not> D E TS F F1"
              using P8 by simp
            have P8D: "Coplanar D E F F1"
              using P8 by simp
            have "C B J CongA D' E' F'"
            proof -
              have "C B J CongA D E F1"
              proof -
                have "B C1 TS C J"
                proof -
                  have "Coplanar B C1 C J"
                    using P7D ncoplanar_perm_12 by blast
                  moreover have "\<not> Col C B C1"
                    using \<open>B C1 OS C A\<close> not_col_permutation_2 one_side_not_col123 by blast
                  moreover have "\<not> Col J B C1"
                    using P7 \<open>\<not> Col G H I\<close> col_conga_col not_col_permutation_3 by blast
                  moreover have "\<not> B C1 OS C J"
                    by (simp add: P7B)
                  ultimately show ?thesis
                    by (simp add: cop_nos__ts)
                qed
                moreover have "E F TS D F1"
                proof -
                  have "Coplanar E F D F1"
                    using P8D ncoplanar_perm_12 by blast
                  moreover have "\<not> Col F1 E F"
                    using P8 \<open>\<not> Col G H I\<close> col_conga_col not_col_permutation_3 by blast
                  ultimately show ?thesis
                    using P8B \<open>\<not> Col D E F\<close> cop_nos__ts by blast
                qed
                moreover have "C B C1 CongA D E F"
                  using P6A by blast
                moreover have "C1 B J CongA F E F1"
                  using P8 by (meson P7A not_conga not_conga_sym)
                ultimately show ?thesis
                  using l11_22a by blast
              qed
              moreover have "D E F1 CongA D' E' F'"
              proof -
                have "D E F G H I SumA D E F1"
                  using P8A P8B P8D SumA_def \<open>\<not> Col D E F\<close> conga_distinct conga_refl not_col_distincts by auto
                moreover have "D E F G H I SumA D' E' F'"
                  by (simp add: assms(4))
                ultimately show ?thesis
                  using suma2__conga by auto
              qed
              ultimately show ?thesis
                using conga_trans by blast
            qed
            have "\<not> Col C B C1"
              using \<open>B C1 OS C A\<close> col123__nos col_permutation_1 by blast
            show ?thesis
            proof -
              have "A B C C B J SumA A B J"
              proof -
                have "B C TS J A"
                proof -
                  have "B C TS C1 A" using cop_nos__ts
                    using P6B P6D T1 \<open>\<not> Col C B C1\<close> l9_2 ncoplanar_perm_12 not_col_permutation_3 by blast
                  moreover have "B C OS C1 J"
                  proof -
                    have "\<not> Col C1 C B"
                      using Col_perm \<open>\<not> Col C B C1\<close> by blast
                    moreover have "\<not> Col J C B"
                      using \<open>C B J CongA D' E' F'\<close> \<open>\<not> Col D' E' F'\<close> col_conga_col col_permutation_1 by blast
                    ultimately show ?thesis
                      using P7C P7D cop_nos__ts invert_one_side by blast
                  qed
                  ultimately show ?thesis
                    using l9_8_2 by blast
                qed
                thus ?thesis
                  by (simp add: l9_2 ts__suma_1)
              qed
              moreover have "A B C CongA A B C"
                using T1 conga_refl not_col_distincts by fastforce
              moreover have "A B J CongA K L M"
              proof -
                have "A' B' C' G H I SumA A B J"
                proof -
                  have "A B C1 C1 B J SumA A B J"
                  proof -
                    have "B C1 TS A J"
                    proof -
                      have "B C1 TS C J"
                      proof -
                        have "Coplanar B C1 C J"
                          using P7D ncoplanar_perm_12 by blast
                        moreover have "\<not> Col J B C1"
                          using P7 \<open>\<not> Col G H I\<close> col_conga_col not_col_permutation_3 by blast
                        ultimately show ?thesis
                          by (simp add: \<open>\<not> Col C B C1\<close> P7B cop_nos__ts)
                      qed
                      moreover have "B C1 OS C A"
                        by (simp add: \<open>B C1 OS C A\<close>)
                      ultimately show ?thesis
                        using l9_8_2 by blast
                    qed
                    thus ?thesis
                      by (simp add: ts__suma_1)
                  qed
                  moreover have "A B C1 CongA A' B' C'"
                    using \<open>A' B' C' CongA A B C1\<close> not_conga_sym by blast
                  moreover have "C1 B J CongA G H I"
                    by (simp add: P7A)
                  moreover have "A B J CongA A B J"
                    using \<open>A B C C B J SumA A B J\<close> suma2__conga by auto
                  ultimately show ?thesis
                    using conga3_suma__suma by blast
                qed
                moreover have "A' B' C' G H I SumA K L M"
                  using assms(5) by simp
                ultimately show ?thesis
                  using suma2__conga by auto
              qed
              ultimately show ?thesis
                using  \<open>C B J CongA D' E' F'\<close> conga3_suma__suma by blast
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma suma_assoc_2:
  assumes "SAMS A B C D E F" and
    "SAMS D E F G H I" and
    "A B C D E F SumA A' B' C'" and
    "D E F G H I SumA D' E' F'" and
    "A B C D' E' F' SumA K L M"
  shows "A' B' C' G H I SumA K L M"
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) sams_sym suma_assoc_1 suma_sym)

lemma suma_assoc:
  assumes "SAMS A B C D E F" and
    "SAMS D E F G H I" and
    "A B C D E F SumA A' B' C'" and
    "D E F G H I SumA D' E' F'"
  shows
    "A' B' C' G H I SumA K L M \<longleftrightarrow> A B C D' E' F' SumA K L M"
  by (meson assms(1) assms(2) assms(3) assms(4) suma_assoc_1 suma_assoc_2)

lemma sams_assoc_1:
  assumes "SAMS A B C D E F" and
    "SAMS D E F G H I" and
    "A B C D E F SumA A' B' C'" and
    "D E F G H I SumA D' E' F'" and
    "SAMS A' B' C' G H I"
  shows "SAMS A B C D' E' F'"
proof cases
  assume "Col A B C"
  {
    assume "E Out D F"
    have "SAMS A B C D' E' F'"
    proof -
      have "A' B' C' CongA A B C"
        using assms(3) \<open>E Out D F\<close> conga_sym out546_suma__conga by blast
      moreover have "G H I CongA D' E' F'"
        using \<open>E Out D F\<close> assms(4) out213_suma__conga by blast
      ultimately show ?thesis
        using assms(5) conga2_sams__sams by blast
    qed
  }
  {
    assume "\<not> Bet A B C"
    then have P1: "B Out A C"
      using \<open>Col A B C\<close> or_bet_out by blast
    have "SAMS D' E' F' A B C"
    proof -
      have "D' \<noteq> E'"
        using assms(4) suma_distincts by auto
      moreover have "F' E' F' CongA A B C"
      proof -
        have "E' \<noteq> F'"
          using assms(4) suma_distincts by blast
        then have "E' Out F' F'"
          using out_trivial by auto
        thus ?thesis
          using P1 l11_21_b by blast
      qed
      moreover have "\<not> E' F' OS D' F'"
        using os_distincts by blast
      moreover have "\<not> D' E' TS F' F'"
        by (simp add: not_two_sides_id)
      moreover have "Coplanar D' E' F' F'"
        using ncop_distincts by blast
      ultimately show ?thesis using SAMS_def P1 by blast
    qed
    then have "SAMS A B C D' E' F'"
      using sams_sym by blast
  }
  thus ?thesis
    using SAMS_def assms(1) \<open>E Out D F \<Longrightarrow> SAMS A B C D' E' F'\<close> by blast
next
  assume "\<not> Col A B C"
  show ?thesis
  proof cases
    assume "Col D E F"
    have "H Out G I \<or> \<not> Bet D E F"
      using SAMS_def assms(2) by blast
    {
      assume "H Out G I"
      have "SAMS A B C D' E' F'"
      proof -
        have "A B C CongA A B C"
          using \<open>\<not> Col A B C\<close> conga_refl not_col_distincts by fastforce
        moreover have "D E F CongA D' E' F'"
          using \<open>H Out G I\<close> assms(4) out546_suma__conga by blast
        ultimately show ?thesis
          using assms(1) conga2_sams__sams by blast
      qed
    }
    {
      assume "\<not> Bet D E F"
      then have "E Out D F"
        using \<open>Col D E F\<close> l6_4_2 by blast
      have "SAMS A B C D' E' F'"
      proof -
        have "A' B' C' CongA A B C"
          using out546_suma__conga \<open>E Out D F\<close> assms(3) not_conga_sym by blast
        moreover have "G H I CongA D' E' F'"
          using out213_suma__conga \<open>E Out D F\<close> assms(4) by auto
        ultimately show ?thesis
          using assms(5) conga2_sams__sams by auto
      qed
    }
    thus ?thesis
      using \<open>H Out G I \<Longrightarrow> SAMS A B C D' E' F'\<close> \<open>H Out G I \<or> \<not> Bet D E F\<close> by blast
  next
    assume "\<not> Col D E F"
    show ?thesis
    proof cases
      assume "Col G H I"
      have "SAMS G H I D E F"
        by (simp add: assms(2) sams_sym)
      then have "E Out D F \<or> \<not> Bet G H I"
        using SAMS_def by blast
      {
        assume "E Out D F"
        then have "False"
          using Col_cases \<open>\<not> Col D E F\<close> out_col by blast
        then have "SAMS A B C D' E' F'"
          by simp
      }
      {
        assume "\<not> Bet G H I"
        then have "H Out G I"
          by (simp add: \<open>Col G H I\<close> l6_4_2)
        have "SAMS A B C D' E' F'"
        proof -
          have "A B C CongA A B C"
            by (metis \<open>\<not> Col A B C\<close> col_trivial_1 col_trivial_2 conga_refl)
          moreover have "D E F CongA D' E' F'"
            using out546_suma__conga \<open>H Out G I\<close> assms(4) by blast
          moreover have "SAMS A B C D E F"
            using assms(1) by auto
          ultimately show ?thesis
            using conga2_sams__sams by auto
        qed
      }
      thus ?thesis
        using \<open>E Out D F \<or> \<not> Bet G H I\<close> \<open>E Out D F \<Longrightarrow> SAMS A B C D' E' F'\<close> by blast
    next
      assume "\<not> Col G H I"
      show ?thesis
      proof -
        have "\<not> Bet A B C"
          using Col_def \<open>\<not> Col A B C\<close> by auto
        moreover have "\<exists> J. (C B J CongA D' E' F' \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J)"
        proof -
          have "\<not> Col A' B' C'"
          proof -
            {
              assume "Col A' B' C'"
              have "H Out G I \<or> \<not> Bet A' B' C'"
                using SAMS_def assms(5) by blast
              {
                assume "H Out G I"
                then have "False"
                  using Col_cases \<open>\<not> Col G H I\<close> out_col by blast
              }
              {
                assume "\<not> Bet A' B' C'"
                then have "B' Out A' C'"
                  using not_bet_out \<open>Col A' B' C'\<close> by blast
                have "A B C LeA A' B' C'"
                  using assms(1) assms(3) sams_suma__lea123789 by auto
                then have "B Out A C"
                  using \<open>B' Out A' C'\<close> out_lea__out by blast
                then have "Col A B C"
                  using Col_perm out_col by blast
                then have "False"
                  using \<open>\<not> Col A B C\<close> by auto
              }
              then have "False"
                using \<open>H Out G I \<Longrightarrow> False\<close> \<open>H Out G I \<or> \<not> Bet A' B' C'\<close> by blast
            }
            thus ?thesis by blast
          qed
          obtain C1 where P1: "C B C1 CongA D E F \<and> \<not> B C OS A C1 \<and> \<not> A B TS C C1 \<and> Coplanar A B C C1"
            using SAMS_def assms(1) by auto
          have P1A: "C B C1 CongA D E F"
            using P1 by simp
          have P1B: "\<not> B C OS A C1"
            using P1 by simp
          have P1C: "\<not> A B TS C C1"
            using P1 by simp
          have P1D: "Coplanar A B C C1"
            using P1 by simp
          have "A B C1 CongA A' B' C'"
          proof -
            have "A B C D E F SumA A B C1"
              using P1A P1B P1D SumA_def \<open>\<not> Col A B C\<close> conga_distinct conga_refl not_col_distincts by auto
            thus ?thesis
              using assms(3) suma2__conga by auto
          qed
          have "SAMS C B C1 G H I"
          proof -
            have "D E F CongA C B C1"
              using P1A not_conga_sym by blast
            moreover have "G H I CongA G H I"
              using \<open>\<not> Col G H I\<close> conga_refl not_col_distincts by fastforce
            ultimately show ?thesis using conga2_sams__sams
              using assms(2) by blast
          qed
          then obtain J where T1: "C1 B J CongA G H I \<and> \<not> B C1 OS C J \<and> \<not> C B TS C1 J \<and> Coplanar C B C1 J"
            using SAMS_def by auto
          have T1A: "C1 B J CongA G H I"
            using T1 by simp
          have T1B: "\<not> B C1 OS C J"
            using T1 by simp
          have T1C: "\<not> C B TS C1 J"
            using T1 by simp
          have T1D: "Coplanar C B C1 J"
            using T1 by simp
          have "SAMS A B C1 C1 B J"
          proof -
            have "A' B' C' CongA A B C1"
              using \<open>A B C1 CongA A' B' C'\<close> not_conga_sym by blast
            moreover have "G H I CongA C1 B J"
              using T1A not_conga_sym by blast
            ultimately show ?thesis
              using assms(5) conga2_sams__sams by auto
          qed
          then obtain J' where T2: "C1 B J' CongA C1 B J \<and> \<not> B C1 OS A J' \<and> \<not> A B TS C1 J' \<and> Coplanar A B C1 J'"
            using SAMS_def by auto
          have T2A: "C1 B J' CongA C1 B J"
            using T2 by simp
          have T2B: "\<not> B C1 OS A J'"
            using T2 by simp
          have T2C: "\<not> A B TS C1 J'"
            using T2 by simp
          have T2D: "Coplanar A B C1 J'"
            using T2 by simp
          have "A' B' C' CongA A B C1"
            using \<open>A B C1 CongA A' B' C'\<close> not_conga_sym by blast
          then have "\<not> Col A B C1"
            using ncol_conga_ncol \<open>\<not> Col A' B' C'\<close> by blast
          have "D E F CongA C B C1"
            using P1A not_conga_sym by blast
          then have "\<not> Col C B C1"
            using ncol_conga_ncol \<open>\<not> Col D E F\<close> by blast
          then have "Coplanar C1 B A J"
            using coplanar_trans_1 P1D T1D coplanar_perm_15 coplanar_perm_6 by blast
          have "Coplanar C1 B J' J"
            using T2D \<open>Coplanar C1 B A J\<close> \<open>\<not> Col A B C1\<close> coplanar_perm_14 coplanar_perm_6 coplanar_trans_1 by blast
          have "B Out J' J \<or> C1 B TS J' J"
            by (meson T2 \<open>Coplanar C1 B A J\<close> \<open>\<not> Col A B C1\<close> conga_cop__or_out_ts coplanar_trans_1 ncoplanar_perm_14 ncoplanar_perm_6)
          {
            assume "B Out J' J"
            have "\<exists> J. (C B J CongA D' E' F' \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J)"
            proof -
              have "C B C1 C1 B J SumA C B J"
              proof -
                have "C1 B J CongA C1 B J"
                  using CongA_def T2A conga_refl by auto
                moreover have "C B J CongA C B J"
                  using \<open>\<not> Col C B C1\<close> calculation conga_diff56 conga_pseudo_refl conga_right_comm not_col_distincts by blast
                ultimately show ?thesis
                  using T1D T1B SumA_def by blast
              qed
              then have "D E F G H I SumA C B J"
                using conga3_suma__suma by (meson P1A T1A suma2__conga)
              then have "C B J CongA D' E' F'"
                using assms(4) suma2__conga by auto
              moreover have "\<not> B C OS A J"
                by (metis (no_types, lifting) Col_perm P1B P1D T1C \<open>\<not> Col A B C\<close> \<open>\<not> Col C B C1\<close> cop_nos__ts coplanar_perm_8 invert_two_sides l9_2 l9_8_2)
              moreover have "\<not> A B TS C J"
              proof cases
                assume "Col A B J"
                thus ?thesis
                  using TS_def invert_two_sides not_col_permutation_3 by blast
              next
                assume "\<not> Col A B J"
                have "A B OS C J"
                proof -
                  have "A B OS C C1"
                    by (simp add: P1C P1D \<open>\<not> Col A B C1\<close> \<open>\<not> Col A B C\<close> cop_nts__os not_col_permutation_2)
                  moreover have "A B OS C1 J"
                  proof -
                    have "A B OS C1 J'"
                      by (metis T2C T2D \<open>B Out J' J\<close> \<open>\<not> Col A B C1\<close> \<open>\<not> Col A B J\<close> col_trivial_2 colx cop_nts__os not_col_permutation_2 out_col out_distinct)
                    thus ?thesis
                      using \<open>B Out J' J\<close> invert_one_side out_out_one_side by blast
                  qed
                  ultimately show ?thesis
                    using one_side_transitivity by blast
                qed
                thus ?thesis
                  using l9_9 by blast
              qed
              moreover have "Coplanar A B C J"
                by (meson P1D \<open>Coplanar C1 B A J\<close> \<open>\<not> Col A B C1\<close> coplanar_perm_18 coplanar_perm_2 coplanar_trans_1 not_col_permutation_2)
              ultimately show ?thesis
                by blast
            qed
          }
          {
            assume "C1 B TS J' J"
            have "B C1 OS C J"
            proof -
              have "B C1 TS C J'"
              proof -
                have "B C1 TS A J'"
                  by (meson T2B T2D TS_def \<open>C1 B TS J' J\<close> \<open>\<not> Col A B C1\<close> cop_nts__os invert_two_sides ncoplanar_perm_12)
                moreover have "B C1 OS A C"
                  by (meson P1B P1C P1D \<open>\<not> Col A B C1\<close> \<open>\<not> Col A B C\<close> \<open>\<not> Col C B C1\<close> cop_nts__os invert_one_side ncoplanar_perm_12 not_col_permutation_2 not_col_permutation_3 os_ts1324__os)
                ultimately show ?thesis
                  using l9_8_2 by blast
              qed
              moreover have "B C1 TS J J'"
                using \<open>C1 B TS J' J\<close> invert_two_sides l9_2 by blast
              ultimately show ?thesis
                using OS_def by blast
            qed
            then have "False"
              by (simp add: T1B)
            then have "\<exists> J. (C B J CongA D' E' F' \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J)"
              by auto
          }
          thus ?thesis
            using \<open>B Out J' J \<Longrightarrow> \<exists>J. C B J CongA D' E' F' \<and> \<not> B C OS A J \<and> \<not> A B TS C J \<and> Coplanar A B C J\<close> \<open>B Out J' J \<or> C1 B TS J' J\<close> by blast
        qed
        ultimately show ?thesis
          using SAMS_def not_bet_distincts by auto
      qed
    qed
  qed
qed

lemma sams_assoc_2:
  assumes "SAMS A B C D E F" and
    "SAMS D E F G H I" and
    "A B C D E F SumA A' B' C'" and
    "D E F G H I SumA D' E' F'" and
    "SAMS A B C D' E' F'"
  shows "SAMS A' B' C' G H I"
proof -
  have "SAMS G H I A' B' C'"
  proof -
    have "SAMS G H I D E F"
      by (simp add: assms(2) sams_sym)
    moreover have "SAMS D E F A B C"
      by (simp add: assms(1) sams_sym)
    moreover have "G H I D E F SumA D' E' F'"
      by (simp add: assms(4) suma_sym)
    moreover have "D E F A B C SumA A' B' C'"
      by (simp add: assms(3) suma_sym)
    moreover have "SAMS D' E' F' A B C"
      by (simp add: assms(5) sams_sym)
    ultimately show ?thesis
      using sams_assoc_1 by blast
  qed
  thus ?thesis
    using sams_sym by blast
qed

lemma sams_assoc:
  assumes "SAMS A B C D E F" and
    "SAMS D E F G H I" and
    "A B C D E F SumA A' B' C'" and
    "D E F G H I SumA D' E' F'"
  shows "(SAMS A' B' C' G H I) \<longleftrightarrow> (SAMS A B C D' E' F')"
  using sams_assoc_1 sams_assoc_2
  by (meson assms(1) assms(2) assms(3) assms(4))

lemma sams_nos__nts:
  assumes "SAMS A B C C B J" and
    "\<not> B C OS A J"
  shows "\<not>  A B TS C J"
proof -
  obtain J' where P1: "C B J' CongA C B J \<and> \<not> B C OS A J' \<and> \<not> A B TS C J' \<and> Coplanar A B C J'"
    using SAMS_def assms(1) by blast
  have P1A: "C B J' CongA C B J"
    using P1 by simp
  have P1B: "\<not> B C OS A J'"
    using P1 by simp
  have P1C: "\<not> A B TS C J'"
    using P1 by simp
  have P1D: "Coplanar A B C J'"
    using P1 by simp
  have P2: "B Out C J \<or> \<not> Bet A B C"
    using SAMS_def assms(1) by blast
  {
    assume "A B TS C J"
    have "Coplanar C B J J'"
    proof -
      have "\<not> Col A C B"
        using TS_def \<open>A B TS C J\<close> not_col_permutation_4 by blast
      moreover have "Coplanar A C B J"
        using \<open>A B TS C J\<close> ncoplanar_perm_2 ts__coplanar by blast
      moreover have "Coplanar A C B J'"
        using P1D ncoplanar_perm_2 by blast
      ultimately show ?thesis
        using coplanar_trans_1 by blast
    qed
    have "B Out J J' \<or> C B TS J J'"
      by (metis P1 \<open>A B TS C J\<close> \<open>Coplanar C B J J'\<close> bet_conga__bet bet_out col_conga_col col_two_sides_bet conga_distinct conga_os__out conga_sym cop_nts__os invert_two_sides l5_2 l6_6 not_col_permutation_3 not_col_permutation_4)
    {
      assume "B Out J J'"
      have "\<not> Col B A J \<or> \<not> Col B A J'"
        using TS_def \<open>A B TS C J\<close> not_col_permutation_3 by blast
      then have "A B OS C J'"
        by (metis (full_types) \<open>B Out J J'\<close> Col_cases P1C P1D TS_def \<open>A B TS C J\<close> col2__eq cop_nts__os l6_3_1 out_col)
      then have "A B TS C J'"
        by (meson \<open>A B TS C J\<close> \<open>B Out J J'\<close> l6_6 l9_2 not_col_distincts out_two_sides_two_sides)
      then have "False"
        by (simp add: P1C)
    }
    {
      assume "C B TS J J'"
      then have "\<not> Col C A B \<and> \<not> Col J A B"
        using TS_def \<open>A B TS C J\<close> by blast
      then have "False"
        by (metis P1B P1D TS_def \<open>C B TS J J'\<close> assms(2) cop_nts__os invert_two_sides l9_8_1 ncoplanar_perm_12 not_col_permutation_1)
    }
    then have "False"
      using \<open>B Out J J' \<Longrightarrow> False\<close> \<open>B Out J J' \<or> C B TS J J'\<close> by blast
  }
  thus ?thesis by auto
qed

lemma conga_sams_nos__nts:
  assumes "SAMS A B C D E F" and
    "C B J CongA D E F" and
    "\<not> B C OS A J"
  shows "\<not> A B TS C J"
proof -
  have "SAMS A B C C B J"
  proof -
    have "A B C CongA A B C"
      using assms(1) conga_refl sams_distincts by fastforce
    moreover have "D E F CongA C B J"
      using assms(2) not_conga_sym by blast
    ultimately show ?thesis
      using assms(1) conga2_sams__sams by auto
  qed
  thus ?thesis
    by (simp add: assms(3) sams_nos__nts)
qed

lemma sams_lea2_suma2__conga123:
  assumes "A B C LeA A' B' C'" and
    "D E F LeA D' E' F'" and
    "SAMS A' B' C' D' E' F'" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G H I"
  shows "A B C CongA A' B' C'"
proof -
  have "SAMS A B C D E F"
    using assms(1) assms(2) assms(3) sams_lea2__sams by blast
  moreover have "SAMS A' B' C' D E F"
    by (metis assms(2) assms(3) lea_refl sams_distincts sams_lea2__sams)
  moreover have "A' B' C' D E F SumA G H I"
  proof -
    obtain G' H' I' where P1: "A' B' C' D E F SumA G' H' I'"
      using calculation(2) ex_suma sams_distincts by blast
    show ?thesis
    proof -
      have "A' \<noteq> B' \<and> B' \<noteq> C'"
        using assms(1) lea_distincts by blast
      then have "A' B' C' CongA A' B' C'"
        using conga_refl by auto
      moreover
      have "D \<noteq> E \<and> E \<noteq> F"
        using \<open>SAMS A B C D E F\<close> sams_distincts by blast
      then have "D E F CongA D E F"
        using conga_refl by auto
      moreover have "G' H' I' CongA G H I"
      proof -
        have "G' H' I' LeA G H I"
          using P1 assms(2) assms(3) assms(5) sams_lea456_suma2__lea by blast
        moreover have "G H I LeA G' H' I'"
        proof -
          have "SAMS A' B' C' D E F"
            using \<open>SAMS A' B' C' D E F\<close> by auto
          thus ?thesis
            using P1 assms(1) assms(4) sams_lea123_suma2__lea by blast
        qed
        ultimately show ?thesis
          by (simp add: lea_asym)
      qed
      ultimately show ?thesis
        using P1 conga3_suma__suma by blast
    qed
  qed
  ultimately show ?thesis
    using assms(4) sams2_suma2__conga123 by blast
qed

lemma sams_lea2_suma2__conga456:
  assumes "A B C LeA A' B' C'" and
    "D E F LeA D' E' F'" and
    "SAMS A' B' C' D' E' F'" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G H I"
  shows "D E F CongA D' E' F'"
proof -
  have "SAMS D' E' F' A' B' C'"
    by (simp add: assms(3) sams_sym)
  moreover have "D E F A B C SumA G H I"
    by (simp add: assms(4) suma_sym)
  moreover have "D' E' F' A' B' C' SumA G H I"
    by (simp add: assms(5) suma_sym)
  ultimately show ?thesis
    using assms(1) assms(2) sams_lea2_suma2__conga123 by auto
qed

lemma sams_suma__out213:
  assumes "A B C D E F SumA D E F" and
    "SAMS A B C D E F"
  shows "B Out A C"
proof -
  have "E \<noteq> D"
    using assms(2) sams_distincts by blast
  then have "E Out D D"
    using out_trivial by auto
  moreover have "D E D CongA A B C"
  proof -
    have "D E D LeA A B C"
      using assms(1) lea121345 suma_distincts by auto
    moreover
    have "E \<noteq> D \<and> E \<noteq> F"
      using assms(2) sams_distincts by blast
    then have "D E F LeA D E F"
      using lea_refl by auto
    moreover have "D E D D E F SumA D E F"
    proof -
      have "\<not> E D OS D F"
        using os_distincts by auto
      moreover have "Coplanar D E D F"
        using ncop_distincts by auto
      ultimately show ?thesis
        using SumA_def \<open>D E F LeA D E F\<close> lea_asym by blast
    qed
    ultimately show ?thesis
      using assms(1) assms(2) sams_lea2_suma2__conga123 by auto
  qed
  ultimately show ?thesis
    using eq_conga_out by blast
qed

lemma sams_suma__out546:
  assumes "A B C D E F SumA A B C" and
    "SAMS A B C D E F"
  shows "E Out D F"
proof -
  have "D E F A B C SumA A B C"
    using assms(1) suma_sym by blast
  moreover have "SAMS D E F A B C"
    using assms(2) sams_sym by blast
  ultimately show ?thesis
    using sams_suma__out213 by blast
qed

lemma sams_lea_lta123_suma2__lta:
  assumes "A B C LtA A' B' C'" and
    "D E F LeA D' E' F'" and
    "SAMS A' B' C' D' E' F'" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "G H I LtA G' H' I'"
proof -
  have "G H I LeA G' H' I'"
  proof -
    have "A B C LeA A' B' C'"
      by (simp add: assms(1) lta__lea)
    thus ?thesis
      using assms(2) assms(3) assms(4) assms(5) sams_lea2_suma2__lea by blast
  qed
  moreover have "\<not> G H I CongA G' H' I'"
  proof -
    {
      assume "G H I CongA G' H' I'"
      have "A B C CongA A' B' C'"
      proof -
        have "A B C LeA A' B' C'"
          by (simp add: assms(1) lta__lea)
        moreover have "A' B' C' D' E' F' SumA G H I"
          by (meson \<open>G H I CongA G' H' I'\<close> assms(3) assms(5) conga3_suma__suma conga_sym sams2_suma2__conga123 sams2_suma2__conga456)
        ultimately show ?thesis
          using assms(2) assms(3) assms(4) sams_lea2_suma2__conga123 by blast
      qed
      then have "False"
        using assms(1) lta_not_conga by auto
    }
    thus ?thesis
      by auto
  qed
  ultimately show ?thesis
    using LtA_def by blast
qed

lemma sams_lea_lta456_suma2__lta:
  assumes "A B C LeA A' B' C'" and
    "D E F LtA D' E' F'" and
    "SAMS A' B' C' D' E' F'" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "G H I LtA G' H' I'"
  using sams_lea_lta123_suma2__lta
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) sams_sym suma_sym)

lemma sams_lta2_suma2__lta:
  assumes "A B C LtA A' B' C'" and
    "D E F LtA D' E' F'" and
    "SAMS A' B' C' D' E' F'" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "G H I LtA G' H' I'"
  using sams_lea_lta123_suma2__lta
  by (meson LtA_def assms(1) assms(2) assms(3) assms(4) assms(5))

lemma sams_lea2_suma2__lea123:
  assumes "D' E' F' LeA D E F" and
    "G H I LeA G' H' I'" and
    "SAMS A B C D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "A B C LeA A' B' C'"
proof cases
  assume "A' B' C' LtA A B C"
  then have "G' H' I' LtA G H I" using sams_lea_lta123_suma2__lta
    using assms(1) assms(3) assms(4) assms(5) by blast
  then have "\<not> G H I LeA G' H' I'"
    using lea__nlta by blast
  then have "False"
    using assms(2) by auto
  thus ?thesis by auto
next
  assume "\<not> A' B' C' LtA A B C"
  have "A' \<noteq> B' \<and> B' \<noteq> C' \<and> A \<noteq> B \<and> B \<noteq> C"
    using assms(4) assms(5) suma_distincts by auto
  thus ?thesis
    by (simp add: \<open>\<not> A' B' C' LtA A B C\<close> nlta__lea)
qed

lemma sams_lea2_suma2__lea456:
  assumes "A' B' C' LeA A B C" and
    "G H I LeA G' H' I'" and
    "SAMS A B C D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "D E F LeA D' E' F'"
proof -
  have "SAMS D E F A B C"
    by (simp add: assms(3) sams_sym)
  moreover have "D E F A B C SumA G H I"
    by (simp add: assms(4) suma_sym)
  moreover have "D' E' F' A' B' C' SumA G' H' I'"
    by (simp add: assms(5) suma_sym)
  ultimately show ?thesis
    using assms(1) assms(2) sams_lea2_suma2__lea123 by blast
qed

lemma sams_lea_lta456_suma2__lta123:
  assumes "D' E' F' LtA D E F" and
    "G H I LeA G' H' I'" and
    "SAMS A B C D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "A B C LtA A' B' C'"
proof cases
  assume "A' B' C' LeA A B C"
  then have "G' H' I' LtA G H I"
    using sams_lea_lta456_suma2__lta assms(1) assms(3) assms(4) assms(5) by blast
  then have "\<not> G H I LeA G' H' I'"
    using lea__nlta by blast
  then have "False"
    using assms(2) by blast
  thus ?thesis by blast
next
  assume "\<not> A' B' C' LeA A B C"
  have "A' \<noteq> B' \<and> B' \<noteq> C' \<and> A \<noteq> B \<and> B \<noteq> C"
    using assms(4) assms(5) suma_distincts by auto
  thus ?thesis using nlea__lta
    by (simp add: \<open>\<not> A' B' C' LeA A B C\<close>)
qed

lemma sams_lea_lta123_suma2__lta456:
  assumes "A' B' C' LtA A B C" and
    "G H I LeA G' H' I'" and
    "SAMS A B C D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "D E F LtA D' E' F'"
proof -
  have "SAMS D E F A B C"
    by (simp add: assms(3) sams_sym)
  moreover have "D E F A B C SumA G H I"
    by (simp add: assms(4) suma_sym)
  moreover have "D' E' F' A' B' C' SumA G' H' I'"
    by (simp add: assms(5) suma_sym)
  ultimately show ?thesis
    using assms(1) assms(2) sams_lea_lta456_suma2__lta123 by blast
qed

lemma sams_lea_lta789_suma2__lta123:
  assumes "D' E' F' LeA D E F" and
    "G H I LtA G' H' I'" and
    "SAMS A B C D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "A B C LtA A' B' C'"
proof cases
  assume "A' B' C' LeA A B C"
  then have "G' H' I' LeA G H I"
    using assms(1) assms(3) assms(4) assms(5) sams_lea2_suma2__lea by blast
  then have "\<not> G H I LtA G' H' I'"
    by (simp add: lea__nlta)
  then have "False"
    using assms(2) by blast
  thus ?thesis by auto
next
  assume "\<not> A' B' C' LeA A B C"
  have "A' \<noteq> B' \<and> B' \<noteq> C' \<and> A \<noteq> B \<and> B \<noteq> C"
    using assms(4) assms(5) suma_distincts by auto
  thus ?thesis
    using nlea__lta by (simp add: \<open>\<not> A' B' C' LeA A B C\<close>)
qed

lemma sams_lea_lta789_suma2__lta456:
  assumes "A' B' C' LeA A B C" and
    "G H I LtA G' H' I'" and
    "SAMS A B C D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "D E F LtA D' E' F'"
proof -
  have "SAMS D E F A B C"
    by (simp add: assms(3) sams_sym)
  moreover have "D E F A B C SumA G H I"
    by (simp add: assms(4) suma_sym)
  moreover have "D' E' F' A' B' C' SumA G' H' I'"
    using assms(5) suma_sym by blast
  ultimately show ?thesis
    using assms(1) assms(2) sams_lea_lta789_suma2__lta123 by blast
qed

lemma sams_lta2_suma2__lta123:
  assumes "D' E' F' LtA D E F" and
    "G H I LtA G' H' I'" and
    "SAMS A B C D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "A B C LtA A' B' C'"
proof -
  have "D' E' F' LeA D E F"
    by (simp add: assms(1) lta__lea)
  thus ?thesis
    using assms(2) assms(3) assms(4) assms(5) sams_lea_lta789_suma2__lta123 by blast
qed

lemma sams_lta2_suma2__lta456:
  assumes "A' B' C' LtA A B C" and
    "G H I LtA G' H' I'" and
    "SAMS A B C D E F" and
    "A B C D E F SumA G H I" and
    "A' B' C' D' E' F' SumA G' H' I'"
  shows "D E F LtA D' E' F'"
proof -
  have "A' B' C' LeA A B C"
    by (simp add: assms(1) lta__lea)
  thus ?thesis
    using assms(2) assms(3) assms(4) assms(5) sams_lea_lta789_suma2__lta456 by blast
qed

lemma sams123231:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "B \<noteq> C"
  shows "SAMS A B C B C A"
proof -
  obtain A' where "B Midpoint A A'"
    using symmetric_point_construction by auto
  then have "A' \<noteq> B"
    using assms(1) midpoint_not_midpoint by blast
  moreover have "Bet A B A'"
    by (simp add: \<open>B Midpoint A A'\<close> midpoint_bet)
  moreover have "B C A LeA C B A'"
  proof cases
    assume "Col A B C"
    show ?thesis
    proof cases
      assume "Bet A C B"
      thus ?thesis
        by (metis assms(2) assms(3) between_exchange3 calculation(1) calculation(2) l11_31_2)
    next
      assume "\<not> Bet A C B"
      then have "C Out B A"
        using Col_cases \<open>Col A B C\<close> l6_6 or_bet_out by blast
      thus ?thesis
        using assms(3) calculation(1) l11_31_1 by auto
    qed
  next
    assume "\<not> Col A B C"
    thus ?thesis
      using l11_41_aux \<open>B Midpoint A A'\<close> calculation(1) lta__lea midpoint_bet not_col_permutation_4 by blast
  qed
  ultimately show ?thesis
    using assms(1) sams_chara by blast
qed

lemma col_suma__col:
  assumes "Col D E F" and
    "A B C B C A SumA D E F"
  shows "Col A B C"
proof -
  {
    assume "\<not> Col A B C"
    have "False"
    proof cases
      assume "Bet D E F"
      obtain P where P1: "Bet A B P \<and> Cong A B B P"
        using Cong_perm segment_construction by blast
      have "D E F LtA A B P"
      proof -
        have "A B C LeA A B C"
          using \<open>\<not> Col A B C\<close> lea_total not_col_distincts by blast
        moreover
        have "B C TS A P"
          by (metis Cong_perm P1 \<open>\<not> Col A B C\<close> bet__ts bet_col between_trivial2 cong_reverse_identity not_col_permutation_1)
        then have "B C A LtA C B P"
          using Col_perm P1 \<open>\<not> Col A B C\<close> calculation l11_41_aux ts_distincts by blast
        moreover have "A B C C B P SumA A B P"
          by (simp add: \<open>B C TS A P\<close> ts__suma_1)
        ultimately show ?thesis
          by (meson P1 Tarski_neutral_dimensionless.sams_lea_lta456_suma2__lta Tarski_neutral_dimensionless_axioms assms(2) bet_suma__sams)
      qed
      thus ?thesis
        using P1 \<open>Bet D E F\<close> bet2_lta__lta lta_distincts by blast
    next
      assume "\<not> Bet D E F"
      have "C Out B A"
      proof -
        have "E Out D F"
          by (simp add: \<open>\<not> Bet D E F\<close> assms(1) l6_4_2)
        moreover have "B C A LeA D E F"
          using sams_suma__lea456789
          by (metis assms(2) sams123231 suma_distincts)
        ultimately show ?thesis
          using out_lea__out by blast
      qed
      thus ?thesis
        using Col_cases \<open>\<not> Col A B C\<close> out_col by blast
    qed
  }
  thus ?thesis by auto
qed

lemma ncol_suma__ncol:
  assumes "\<not> Col A B C" and
    "A B C B C A SumA D E F"
  shows "\<not> Col D E F"
  using col_suma__col assms(1) assms(2) by blast

lemma per2_suma__bet:
  assumes "Per A B C" and
    "Per D E F" and
    "A B C D E F SumA G H I"
  shows "Bet G H I"
proof -
  obtain A1 where P1: "C B A1 CongA D E F \<and> \<not> B C OS A A1 \<and> Coplanar A B C A1 \<and> A B A1 CongA G H I"
    using SumA_def assms(3) by blast
  then have "D E F CongA A1 B C"
    using conga_right_comm conga_sym by blast
  then have "Per A1 B C"
    using assms(2) l11_17 by blast
  have "Bet A B A1"
  proof -
    have "Col B A A1"
    proof -
      have "Coplanar C A A1 B"
        using P1 ncoplanar_perm_10 by blast
      moreover have "C \<noteq> B"
        using \<open>D E F CongA A1 B C\<close> conga_distinct by auto
      ultimately show ?thesis
        using assms(1) \<open>Per A1 B C\<close> col_permutation_2 cop_per2__col by blast
    qed
    moreover have "B C TS A A1"
    proof -
      have "Coplanar B C A A1"
        using calculation ncop__ncols by blast
      moreover
      have "A \<noteq> B \<and> B \<noteq> C"
        using CongA_def P1 by blast
      then have "\<not> Col A B C"
        by (simp add: assms(1) per_not_col)
      moreover
      have "A1 \<noteq> B \<and> B \<noteq> C"
        using \<open>D E F CongA A1 B C\<close> conga_distinct by blast
      then have "\<not> Col A1 B C"
        using  \<open>Per A1 B C\<close> by (simp add: per_not_col)
      ultimately show ?thesis
        by (simp add: P1 cop_nos__ts)
    qed
    ultimately show ?thesis
      using col_two_sides_bet by blast
  qed
  thus ?thesis
    using P1 bet_conga__bet by blast
qed

lemma bet_per2__suma:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "D \<noteq> E" and
    "E \<noteq> F" and
    "G \<noteq> H" and
    "H \<noteq> I" and
    "Per A B C" and
    "Per D E F" and
    "Bet G H I"
  shows "A B C D E F SumA G H I"
proof -
  obtain G' H' I' where "A B C D E F SumA G' H' I'"
    using assms(1) assms(2) assms(3) assms(4) ex_suma by blast
  moreover have "A B C CongA A B C"
    using assms(1) assms(2) conga_refl by auto
  moreover have "D E F CongA D E F"
    using assms(3) assms(4) conga_refl by auto
  moreover have "G' H' I' CongA G H I"
  proof -
    have "G' \<noteq> H'"
      using calculation(1) suma_distincts by auto
    moreover have "H' \<noteq> I'"
      using \<open>A B C D E F SumA G' H' I'\<close> suma_distincts by blast
    moreover have "Bet G' H' I'"
      using  \<open>A B C D E F SumA G' H' I'\<close> assms(7) assms(8) per2_suma__bet by auto
    ultimately show ?thesis
      using conga_line by (simp add: assms(5) assms(6) assms(9))
  qed
  ultimately show ?thesis
    using conga3_suma__suma by blast
qed

lemma per2__sams:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "D \<noteq> E" and
    "E \<noteq> F" and
    "Per A B C" and
    "Per D E F"
  shows "SAMS A B C D E F"
proof -
  obtain G H I where "A B C D E F SumA G H I"
    using assms(1) assms(2) assms(3) assms(4) ex_suma by blast
  moreover then have "Bet G H I"
    using assms(5) assms(6) per2_suma__bet by auto
  ultimately show ?thesis
    using bet_suma__sams by blast
qed

lemma bet_per_suma__per456:
  assumes "Per A B C" and
    "Bet G H I" and
    "A B C D E F SumA G H I"
  shows "Per D E F"
proof -
  obtain A1 where "B Midpoint A A1"
    using symmetric_point_construction by auto
  have "\<not> Col A B C"
    using assms(1) assms(3) per_col_eq suma_distincts by blast
  have "A B C CongA D E F"
  proof -
    have "SAMS A B C A B C"
      using \<open>\<not> Col A B C\<close> assms(1) not_col_distincts per2__sams by auto
    moreover have "SAMS A B C D E F"
      using assms(2) assms(3) bet_suma__sams by blast
    moreover have "A B C A B C SumA G H I"
      using assms(1) assms(2) assms(3) bet_per2__suma suma_distincts by blast
    ultimately show ?thesis
      using assms(3) sams2_suma2__conga456 by auto
  qed
  thus ?thesis
    using assms(1) l11_17 by blast
qed

lemma bet_per_suma__per123:
  assumes "Per D E F" and
    "Bet G H I" and
    "A B C D E F SumA G H I"
  shows "Per A B C"
  using bet_per_suma__per456
  by (meson assms(1) assms(2) assms(3) suma_sym)

lemma bet_suma__per:
  assumes "Bet D E F" and
    "A B C A B C SumA D E F"
  shows "Per A B C"
proof -
  obtain A' where "C B A' CongA A B C \<and> A B A' CongA D E F"
    using SumA_def assms(2) by blast
  have "Per C B A"
  proof -
    have "Bet A B A'"
    proof -
      have "D E F CongA A B A'"
        using \<open>C B A' CongA A B C \<and> A B A' CongA D E F\<close> not_conga_sym by blast
      thus ?thesis
        using assms(1) bet_conga__bet by blast
    qed
    moreover have "C B A CongA C B A'"
      using conga_left_comm not_conga_sym \<open>C B A' CongA A B C \<and> A B A' CongA D E F\<close> by blast
    ultimately show ?thesis
      using l11_18_2 by auto
  qed
  thus ?thesis
    using Per_cases by auto
qed

lemma acute__sams:
  assumes "Acute A B C"
  shows "SAMS A B C A B C"
proof -
  obtain A' where "B Midpoint A A'"
    using symmetric_point_construction by auto
  show ?thesis
  proof -
    have "A \<noteq> B \<and> A' \<noteq> B"
      using \<open>B Midpoint A A'\<close> acute_distincts assms is_midpoint_id_2 by blast
    moreover have "Bet A B A'"
      by (simp add: \<open>B Midpoint A A'\<close> midpoint_bet)
    moreover
    have "Obtuse C B A'"
      using acute_bet__obtuse assms calculation(1) calculation(2) obtuse_sym by blast
    then have "A B C LeA C B A'"
      by (metis acute__not_obtuse assms calculation(1) lea_obtuse_obtuse lea_total obtuse_distincts)
    ultimately show ?thesis
      using sams_chara by blast
  qed
qed

lemma acute_suma__nbet:
  assumes "Acute A B C" and
    "A B C A B C SumA D E F"
  shows  "\<not> Bet D E F"
proof -
  {
    assume "Bet D E F"
    then have "Per A B C"
      using assms(2) bet_suma__per by auto
    then have "A B C LtA A B C"
      using acute_not_per assms(1) by auto
    then have "False"
      by (simp add: nlta)
  }
  thus ?thesis by blast
qed

lemma acute2__sams:
  assumes "Acute A B C" and
    "Acute D E F"
  shows "SAMS A B C D E F"
  by (metis acute__sams acute_distincts assms(1) assms(2) lea_total sams_lea2__sams)

lemma acute2_suma__nbet_a:
  assumes "Acute A B C" and
    "D E F LeA A B C" and
    "A B C D E F SumA G H I"
  shows "\<not> Bet G H I"
proof -
  {
    assume "Bet G H I"
    obtain A' B' C' where "A B C A B C SumA A' B' C'"
      using acute_distincts assms(1) ex_suma by moura
    have "G H I LeA A' B' C'"
    proof -
      have "A B C LeA A B C"
        using acute_distincts assms(1) lea_refl by blast
      moreover have "SAMS A B C A B C"
        by (simp add: acute__sams assms(1))
      ultimately show ?thesis
        using \<open>A B C A B C SumA A' B' C'\<close> assms(1) assms(2) assms(3) sams_lea456_suma2__lea by blast
    qed
    then have "Bet A' B' C'"
      using \<open>Bet G H I\<close> bet_lea__bet by blast
    then have "False"
      using acute_suma__nbet assms(1) assms(3) \<open>A B C A B C SumA A' B' C'\<close> by blast
  }
  thus ?thesis by blast
qed

lemma acute2_suma__nbet:
  assumes "Acute A B C" and
    "Acute D E F" and
    "A B C D E F SumA G H I"
  shows "\<not> Bet G H I"
proof -
  have "A \<noteq> B \<and> B \<noteq> C \<and> D \<noteq> E \<and> E \<noteq> F"
    using assms(3) suma_distincts by auto
  then have "A B C LeA D E F \<or> D E F LeA A B C"
    by (simp add: lea_total)
  moreover
  {
    assume P3: "A B C LeA D E F"
    have "D E F A B C SumA G H I"
      by (simp add: assms(3) suma_sym)
    then have "\<not> Bet G H I"
      using P3 assms(2) acute2_suma__nbet_a by auto
  }
  {
    assume "D E F LeA A B C"
    then have  "\<not> Bet G H I"
      using acute2_suma__nbet_a assms(1) assms(3) by auto
  }
  thus ?thesis
    using \<open>A B C LeA D E F \<Longrightarrow> \<not> Bet G H I\<close> calculation by blast
qed

lemma acute_per__sams:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per A B C" and
    "Acute D E F"
  shows "SAMS A B C D E F"
proof -
  have "SAMS A B C A B C"
    by (simp add: assms(1) assms(2) assms(3) per2__sams)
  moreover have "A B C LeA A B C"
    using assms(1) assms(2) lea_refl by auto
  moreover have "D E F LeA A B C"
    by (metis acute_distincts acute_lea_acute acute_not_per assms(1) assms(2) assms(3) assms(4) lea_total)
  ultimately show ?thesis
    using sams_lea2__sams by blast
qed

lemma acute_per_suma__nbet:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Per A B C" and
    "Acute D E F" and
    "A B C D E F SumA G H I"
  shows "\<not> Bet G H I"
proof -
  {
    assume "Bet G H I"
    have "G H I LtA G H I"
    proof -
      have "A B C LeA A B C"
        using assms(1) assms(2) lea_refl by auto
      moreover have "D E F LtA A B C"
        by (simp add: acute_per__lta assms(1) assms(2) assms(3) assms(4))
      moreover have "SAMS A B C A B C"
        by (simp add: assms(1) assms(2) assms(3) per2__sams)
      moreover have "A B C D E F SumA G H I"
        by (simp add: assms(5))
      moreover have "A B C A B C SumA G H I"
        by (meson Tarski_neutral_dimensionless.bet_per_suma__per456 Tarski_neutral_dimensionless_axioms \<open>Bet G H I\<close> acute_not_per assms(3) assms(4) calculation(4))
      ultimately show ?thesis
        using sams_lea_lta456_suma2__lta by blast
    qed
    then have "False"
      by (simp add: nlta)
  }
  thus ?thesis by blast
qed

lemma obtuse__nsams:
  assumes "Obtuse A B C"
  shows "\<not> SAMS A B C A B C"
proof -
  {
    assume "SAMS A B C A B C"
    obtain A' where "B Midpoint A A'"
      using symmetric_point_construction by auto
    have "A B C LtA A B C"
    proof -
      have "A B C LeA A' B C"
        by (metis \<open>B Midpoint A A'\<close> \<open>SAMS A B C A B C\<close> lea_right_comm midpoint_bet midpoint_distinct_2 sams_chara sams_distincts)
      moreover have "A' B C LtA A B C"
        using \<open>B Midpoint A A'\<close> assms calculation lea_distincts midpoint_bet obtuse_chara by blast
      ultimately show ?thesis
        using lea__nlta by blast
    qed
    then have "False"
      by (simp add: nlta)
  }
  thus ?thesis by blast
qed

lemma nbet_sams_suma__acute:
  assumes "\<not> Bet D E F" and
    "SAMS A B C A B C" and
    "A B C A B C SumA D E F"
  shows "Acute A B C"
proof -
  have "Acute A B C \<or> Per A B C \<or> Obtuse A B C"
    by (metis angle_partition l8_20_1_R1 l8_5)
  {
    assume "Per A B C"
    then have "Bet D E F"
      using assms(3) per2_suma__bet by auto
    then have "False"
      using assms(1) by auto
  }
  {
    assume "Obtuse A B C"
    then have "\<not> SAMS A B C A B C"
      by (simp add: obtuse__nsams)
    then have "False"
      using assms(2) by auto
  }
  thus ?thesis
    using \<open>Acute A B C \<or> Per A B C \<or> Obtuse A B C\<close> \<open>Per A B C \<Longrightarrow> False\<close> by auto
qed

lemma nsams__obtuse:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "\<not> SAMS A B C A B C"
  shows "Obtuse A B C"
proof -
  {
    assume "Per A B C"
    obtain A' where "B Midpoint A A'"
      using symmetric_point_construction by blast
    have "\<not> Col A B C"
      using \<open>Per A B C\<close> assms(1) assms(2) per_col_eq by blast
    have "SAMS A B C A B C"
    proof -
      have "C B A' CongA A B C"
        using \<open>Per A B C\<close> assms(1) assms(2) assms(3) per2__sams by blast
      moreover have "\<not> B C OS A A'"
        by (meson Col_cases \<open>B Midpoint A A'\<close> col_one_side_out l6_4_1 midpoint_bet midpoint_col)
      moreover have "\<not> A B TS C A'"
        using Col_def Midpoint_def TS_def \<open>B Midpoint A A'\<close> by blast
      moreover have "Coplanar A B C A'"
        using \<open>Per A B C\<close> assms(1) assms(2) assms(3) per2__sams by blast
      ultimately show ?thesis
        using SAMS_def \<open>\<not> Col A B C\<close> assms(1) bet_col by auto
    qed
    then have "False"
      using assms(3) by auto
  }
  {
    assume "Acute A B C"
    then have "SAMS A B C A B C"
      by (simp add: acute__sams)
    then have "False"
      using assms(3) by auto
  }
  thus ?thesis
    using \<open>Per A B C \<Longrightarrow> False\<close> angle_partition assms(1) assms(2) by auto
qed

lemma sams2_suma2__conga:
  assumes "SAMS A B C A B C" and
    "A B C A B C SumA D E F" and
    "SAMS A' B' C' A' B' C'" and
    "A' B' C' A' B' C' SumA D E F"
  shows "A B C CongA A' B' C'"
proof -
  have "A B C LeA A' B' C' \<or> A' B' C' LeA A B C"
    using assms(1) assms(3) lea_total sams_distincts by auto
  moreover
  have "A B C LeA A' B' C' \<longrightarrow> A B C CongA A' B' C'"
    using assms(2) assms(3) assms(4) sams_lea2_suma2__conga123 by auto
  ultimately show ?thesis
    by (meson Tarski_neutral_dimensionless.conga_sym Tarski_neutral_dimensionless.sams_lea2_suma2__conga123 Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(4))
qed

lemma acute2_suma2__conga:
  assumes "Acute A B C" and
    "A B C A B C SumA D E F" and
    "Acute A' B' C'" and
    "A' B' C' A' B' C' SumA D E F"
  shows "A B C CongA A' B' C'"
proof -
  have "SAMS A B C A B C"
    by (simp add: acute__sams assms(1))
  moreover have "SAMS A' B' C' A' B' C'"
    by (simp add: acute__sams assms(3))
  ultimately show ?thesis
    using assms(2) assms(4) sams2_suma2__conga by auto
qed

lemma bet2_suma__out:
  assumes "Bet A B C" and
    "Bet D E F" and
    "A B C D E F SumA G H I"
  shows "H Out G I"
proof -
  have "A B C D E F SumA A B A"
  proof -
    have "C B A CongA D E F"
      by (metis Bet_cases assms(1) assms(2) assms(3) conga_line suma_distincts)
    moreover have "\<not> B C OS A A"
      by (simp add: Col_def assms(1) col124__nos)
    moreover have "Coplanar A B C A"
      using ncop_distincts by blast
    moreover have "A B A CongA A B A"
      using calculation(1) conga_diff2 conga_trivial_1 by auto
    ultimately show ?thesis
      using SumA_def by blast
  qed
  then have "A B A CongA G H I"
    using assms(3) suma2__conga by auto
  thus ?thesis
    using eq_conga_out by auto
qed

lemma col2_suma__col:
  assumes "Col A B C" and
    "Col D E F" and
    "A B C D E F SumA G H I"
  shows "Col G H I"
proof cases
  assume "Bet A B C"
  show ?thesis
  proof cases
    assume "Bet D E F"
    thus ?thesis using bet2_suma__out
      by (meson \<open>Bet A B C\<close> assms(3) not_col_permutation_4 out_col)
  next
    assume "\<not> Bet D E F"
    show ?thesis
    proof -
      have "E Out D F"
        using \<open>\<not> Bet D E F\<close> assms(2) or_bet_out by auto
      then have "A B C CongA G H I"
        using assms(3) out546_suma__conga by auto
      thus ?thesis
        using assms(1) col_conga_col by blast
    qed
  qed
next
  assume "\<not> Bet A B C"
  have "D E F CongA G H I"
  proof -
    have "B Out A C"
      by (simp add: \<open>\<not> Bet A B C\<close> assms(1) l6_4_2)
    thus ?thesis
      using assms(3) out213_suma__conga by auto
  qed
  thus ?thesis
    using assms(2) col_conga_col by blast
qed

lemma suma_suppa__bet:
  assumes "A B C SuppA D E F" and
    "A B C D E F SumA G H I"
  shows "Bet G H I"
proof -
  obtain A' where P1: "Bet A B A' \<and> D E F CongA C B A'"
    using SuppA_def assms(1) by auto
  obtain A'' where P2: "C B A'' CongA D E F \<and> \<not> B C OS A A'' \<and> Coplanar A B C A'' \<and> A B A'' CongA G H I"
    using SumA_def assms(2) by auto
  have "B Out A' A'' \<or> C B TS A' A''"
  proof -
    have "Coplanar C B A' A''"
    proof -
      have "Coplanar C A'' B A"
        using P2 coplanar_perm_17 by blast
      moreover have "B \<noteq> A"
        using SuppA_def assms(1) by auto
      moreover have "Col B A A'" using P1
        by (simp add: bet_col col_permutation_4)
      ultimately show ?thesis
        using col_cop__cop coplanar_perm_3 by blast
    qed
    moreover have "C B A' CongA C B A''"
    proof -
      have "C B A' CongA D E F"
        using P1 not_conga_sym by blast
      moreover have "D E F CongA C B A''"
        using P2 not_conga_sym by blast
      ultimately show ?thesis
        using not_conga by blast
    qed
    ultimately show ?thesis
      using conga_cop__or_out_ts by simp
  qed
  have "Bet A B A''"
  proof -
    have "\<not> C B TS A' A''"
    proof -
      {
        assume "C B TS A' A''"
        have "B C TS A A'"
        proof -
          {
            assume "Col A B C"
            then have "Col A' C B"
              using P1 assms(1) bet_col bet_col1 col3 suppa_distincts by blast
            then have "False"
              using TS_def \<open>C B TS A' A''\<close> by auto
          }
          then have "\<not> Col A B C" by auto
          moreover have "\<not> Col A' B C"
            using TS_def \<open>C B TS A' A''\<close> not_col_permutation_5 by blast
          moreover
          have "\<exists> T. (Col T B C \<and> Bet A T A')"
            using P1 not_col_distincts by blast
          ultimately show ?thesis
            by (simp add: TS_def)
        qed
        then have "B C OS A A''"
          using OS_def \<open>C B TS A' A''\<close> invert_two_sides l9_2 by blast
        then have "False"
          using P2 by simp
      }
      thus ?thesis by blast
    qed
    then have "B Out A' A''"
      using \<open>B Out A' A'' \<or> C B TS A' A''\<close> by auto
    moreover have "A' \<noteq> B \<and> A'' \<noteq> B \<and> A \<noteq> B"
      using P2 calculation conga_diff1 out_diff1 out_diff2 by blast
    moreover have "Bet A' B A"
      using P1 Bet_perm by blast
    ultimately show ?thesis
      using bet_out__bet between_symmetry by blast
  qed
  moreover have "A B A'' CongA G H I"
    using P2 by blast
  ultimately show ?thesis
    using bet_conga__bet by blast
qed

lemma bet_suppa__suma:
  assumes "G \<noteq> H" and
    "H \<noteq> I" and
    "A B C SuppA D E F" and
    "Bet G H I"
  shows "A B C D E F SumA G H I"
proof -
  obtain G' H' I' where "A B C D E F SumA G' H' I'"
    using assms(3) ex_suma suppa_distincts by blast
  moreover have "A B C CongA A B C"
    using calculation conga_refl suma_distincts by fastforce
  moreover
  have "D \<noteq> E \<and> E \<noteq> F"
    using assms(3) suppa_distincts by auto
  then have "D E F CongA D E F"
    using conga_refl by auto
  moreover
  have "G' H' I' CongA G H I"
  proof -
    have "G' \<noteq> H' \<and> H' \<noteq> I'"
      using calculation(1) suma_distincts by auto
    moreover have "Bet G' H' I'"
      using  \<open>A B C D E F SumA G' H' I'\<close> assms(3) suma_suppa__bet by blast
    ultimately show ?thesis
      using assms(1) assms(2) assms(4) conga_line by auto
  qed
  ultimately show ?thesis
    using conga3_suma__suma by blast
qed

lemma bet_suma__suppa:
  assumes "A B C D E F SumA G H I" and
    "Bet G H I"
  shows "A B C SuppA D E F"
proof -
  obtain A' where "C B A' CongA D E F \<and> A B A' CongA G H I"
    using SumA_def assms(1) by blast
  moreover
  have "G H I CongA A B A'"
    using calculation not_conga_sym by blast
  then have "Bet A B A'"
    using assms(2) bet_conga__bet by blast
  moreover have "D E F CongA C B A'"
    using calculation(1) not_conga_sym by blast
  ultimately show ?thesis
    by (metis SuppA_def conga_diff1)
qed

lemma bet2_suma__suma:
  assumes "A' \<noteq> B" and
    "D' \<noteq>  E" and
    "Bet A B A'" and
    "Bet D E D'" and
    "A B C D E F SumA G H I"
  shows "A' B C D' E F SumA G H I"
proof -
  obtain J where P1: "C B J CongA D E F \<and> \<not> B C OS A J \<and> Coplanar A B C J \<and> A B J CongA G H I"
    using SumA_def assms(5) by auto
  moreover
  obtain C' where P2: "Bet C B C' \<and> Cong B C' B C"
    using segment_construction by blast
  moreover
  have "A B C' D' E F SumA G H I"
  proof -
    have "C' B J CongA D' E F"
      by (metis assms(2) assms(4) calculation(1) calculation(2) cong_diff_3 conga_diff1 l11_13)
    moreover have "\<not> B C' OS A J"
      by (metis Col_cases P1 P2 bet_col col_one_side cong_diff)
    moreover have "Coplanar A B C' J"
      by (smt P1 P2 bet_col bet_col1 col2_cop__cop cong_diff ncoplanar_perm_5)
    ultimately show ?thesis
      using P1 SumA_def by blast
  qed
  moreover have "A B C' CongA A' B C"
    using assms(1) assms(3) assms(5) between_symmetry calculation(2) calculation(3) l11_14 suma_distincts by auto
  moreover
  have "D' \<noteq> E \<and> E \<noteq> F"
    using assms(2) calculation(1) conga_distinct by blast
  then have "D' E F CongA D' E F"
    using conga_refl by auto
  moreover
  have "G \<noteq> H \<and> H \<noteq> I"
    using assms(5) suma_distincts by blast
  then have "G H I CongA G H I"
    using conga_refl by auto
  ultimately show ?thesis
    using conga3_suma__suma by blast
qed

lemma suma_suppa2__suma:
  assumes "A B C SuppA A' B' C'" and
    "D E F SuppA D' E' F'" and
    "A B C D E F SumA G H I"
  shows "A' B' C' D' E' F' SumA G H I"
proof -
  obtain A0 where P1: "Bet A B A0 \<and> A' B' C' CongA C B A0"
    using SuppA_def assms(1) by auto
  obtain D0 where P2: "Bet D E D0 \<and> D' E' F' CongA F E D0"
    using SuppA_def assms(2) by auto
  show ?thesis
  proof -
    have "A0 B C D0 E F SumA G H I"
    proof -
      have "A0 \<noteq> B"
        using CongA_def P1 by auto
      moreover have "D0 \<noteq> E"
        using CongA_def P2 by blast
      ultimately show ?thesis
        using P1 P2 assms(3) bet2_suma__suma by auto
    qed
    moreover have "A0 B C CongA A' B' C'"
      using P1 conga_left_comm not_conga_sym by blast
    moreover have "D0 E F CongA D' E' F'"
      using P2 conga_left_comm not_conga_sym by blast
    moreover
    have "G \<noteq> H \<and> H \<noteq> I"
      using assms(3) suma_distincts by blast
    then have "G H I CongA G H I"
      using conga_refl by auto
    ultimately show ?thesis
      using conga3_suma__suma by blast
  qed
qed

lemma suma2_obtuse2__conga:
  assumes "Obtuse A B C" and
    "A B C A B C SumA D E F" and
    "Obtuse A' B' C'" and
    "A' B' C' A' B' C' SumA D E F"
  shows "A B C CongA A' B' C'"
proof -
  obtain A0 where P1: "Bet A B A0 \<and> Cong B A0 A B"
    using segment_construction by blast
  moreover
  obtain A0' where P2: "Bet A' B' A0' \<and> Cong B' A0' A' B'"
    using segment_construction by blast
  moreover
  have "A0 B C CongA A0' B' C'"
  proof -
    have "Acute A0 B C"
      using assms(1) bet_obtuse__acute P1 cong_diff_3 obtuse_distincts by blast
    moreover have "A0 B C A0 B C SumA D E F"
      using P1 acute_distincts assms(2) bet2_suma__suma calculation by blast
    moreover have "Acute A0' B' C'"
      using P2 assms(3) bet_obtuse__acute cong_diff_3 obtuse_distincts by blast
    moreover have "A0' B' C' A0' B' C' SumA D E F"
      by (metis P2 assms(4) bet2_suma__suma cong_diff_3)
    ultimately show ?thesis
      using acute2_suma2__conga by blast
  qed
  moreover have "Bet A0 B A"
    using Bet_perm calculation(1) by blast
  moreover have "Bet A0' B' A'"
    using Bet_perm calculation(2) by blast
  moreover have "A \<noteq> B"
    using assms(1) obtuse_distincts by blast
  moreover have "A' \<noteq> B'"
    using assms(3) obtuse_distincts by blast
  ultimately show ?thesis
    using l11_13 by blast
qed

lemma bet_suma2__or_conga:
  assumes "A0 \<noteq> B" and
    "Bet A B A0" and
    "A B C A B C SumA D E F" and
    "A' B' C' A' B' C' SumA D E F"
  shows "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'"
proof -
  {
    fix A' B' C'
    assume"Acute A' B' C' \<and> A' B' C' A' B' C' SumA D E F"
    have "Per A B C \<or> Acute A B C \<or> Obtuse A B C"
      by (metis angle_partition l8_20_1_R1 l8_5)
    {
      assume "Per A B C"
      then have "Bet D E F"
        using per2_suma__bet assms(3) by auto
      then have "False"
        using  \<open>Acute A' B' C' \<and> A' B' C' A' B' C' SumA D E F\<close> acute_suma__nbet by blast
      then have "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'" by blast
    }
    {
      assume "Acute A B C"
      have "Acute A' B' C'"
        by (simp add: \<open>Acute A' B' C' \<and> A' B' C' A' B' C' SumA D E F\<close>)
      moreover have "A' B' C' A' B' C' SumA D E F"
        by (simp add: \<open>Acute A' B' C' \<and> A' B' C' A' B' C' SumA D E F\<close>)
      ultimately
      have "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'"
        using assms(3) \<open>Acute A B C\<close> acute2_suma2__conga by auto
    }
    {
      assume "Obtuse A B C"
      have "Acute A0 B C"
        using \<open>Obtuse A B C\<close> assms(1) assms(2) bet_obtuse__acute by auto
      moreover have "A0 B C A0 B C SumA D E F"
        using assms(1) assms(2) assms(3) bet2_suma__suma by auto
      ultimately have "A0 B C CongA A' B' C'"
        using \<open>Acute A' B' C' \<and> A' B' C' A' B' C' SumA D E F\<close> acute2_suma2__conga by auto
      then have "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'" by blast
    }
    then have "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'"
      using \<open>Acute A B C \<Longrightarrow> A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'\<close> \<open>Per A B C \<Longrightarrow> A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'\<close> \<open>Per A B C \<or> Acute A B C \<or> Obtuse A B C\<close> by blast
  }
  then have P1: "\<forall> A' B' C'. (Acute A' B' C' \<and> A' B' C' A' B' C' SumA D E F) \<longrightarrow> (A B C CongA A' B' C' \<or> A0 B C CongA A' B' C')" by blast
  have "Per A' B' C' \<or> Acute A' B' C' \<or> Obtuse A' B' C'"
    by (metis angle_partition l8_20_1_R1 l8_5)
  {
    assume P2: "Per A' B' C'"
    have "A B C CongA A' B' C'"
    proof -
      have "A \<noteq> B \<and> B \<noteq> C"
        using assms(3) suma_distincts by blast
      moreover have "A' \<noteq> B' \<and> B' \<noteq> C'"
        using assms(4) suma_distincts by auto
      moreover have "Per A B C"
      proof -
        have "Bet D E F"
          using P2 assms(4) per2_suma__bet by blast
        moreover have "A B C A B C SumA D E F"
          by (simp add: assms(3))
        ultimately show ?thesis
          using assms(3) bet_suma__per by blast
      qed
      ultimately show ?thesis
        using P2 l11_16 by blast
    qed
    then have "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'" by blast
  }
  {
    assume "Acute A' B' C'"
    then have "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'"
      using P1 assms(4) by blast
  }
  {
    assume "Obtuse A' B' C'"
    obtain A0' where "Bet A' B' A0' \<and> Cong B' A0' A' B'"
      using segment_construction by blast
    moreover
    have "Acute A0' B' C'"
      using \<open>Obtuse A' B' C'\<close> bet_obtuse__acute calculation cong_diff_3 obtuse_distincts by blast
    moreover have "A0' B' C' A0' B' C' SumA D E F"
      using acute_distincts assms(4) bet2_suma__suma calculation(1) calculation(2) by blast
    ultimately
    have "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'"
      using P1 by (metis assms(1) assms(2) assms(3) assms(4) between_symmetry l11_13 suma_distincts)
  }
  thus ?thesis
    using \<open>Acute A' B' C' \<Longrightarrow> A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'\<close> \<open>Per A' B' C' \<Longrightarrow> A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'\<close> \<open>Per A' B' C' \<or> Acute A' B' C' \<or> Obtuse A' B' C'\<close> by blast
qed

lemma suma2__or_conga_suppa:
  assumes "A B C A B C SumA D E F" and
    "A' B' C' A' B' C' SumA D E F"
  shows "A B C CongA A' B' C' \<or> A B C SuppA A' B' C'"
proof -
  obtain A0 where P1: "Bet A B A0 \<and> Cong B A0 A B"
    using segment_construction by blast
  then have "A0 \<noteq> B"
    using  assms(1) bet_cong_eq suma_distincts by blast
  then have "A B C CongA A' B' C' \<or> A0 B C CongA A' B' C'"
    using assms(1) assms(2) P1 bet_suma2__or_conga by blast
  thus ?thesis
    by (metis P1 SuppA_def cong_diff conga_right_comm conga_sym)
qed

lemma ex_trisuma:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "A \<noteq> C"
  shows "\<exists> D E F. A B C TriSumA D E F"
proof -
  obtain G H I where "A B C B C A SumA G H I"
    using assms(1) assms(2) assms(3) ex_suma by presburger
  moreover
  then obtain D E F where "G H I C A B SumA D E F"
    using ex_suma suma_distincts by presburger
  ultimately show ?thesis
    using TriSumA_def by blast
qed

lemma trisuma_perm_231:
  assumes "A B C TriSumA D E F"
  shows "B C A TriSumA D E F"
proof -
  obtain A1 B1 C1 where P1: "A B C B C A SumA A1 B1 C1 \<and> A1 B1 C1 C A B SumA D E F"
    using TriSumA_def assms(1) by auto
  obtain A2 B2 C2 where P2: "B C A C A B SumA B2 C2 A2"
    using P1 ex_suma suma_distincts by fastforce
  have "A B C B2 C2 A2 SumA D E F"
  proof -
    have "SAMS A B C B C A"
      using assms sams123231 trisuma_distincts by auto
    moreover have "SAMS B C A C A B"
      using P2 sams123231 suma_distincts by fastforce
    ultimately show ?thesis
      using P1 P2 suma_assoc by blast
  qed
  thus ?thesis
    using P2 TriSumA_def suma_sym by blast
qed

lemma trisuma_perm_312:
  assumes "A B C TriSumA D E F"
  shows "C A B TriSumA D E F"
  by (simp add: assms trisuma_perm_231)

lemma trisuma_perm_321:
  assumes "A B C TriSumA D E F"
  shows "C B A TriSumA D E F"
proof -
  obtain G H I where "A B C B C A SumA G H I \<and> G H I C A B SumA D E F"
    using TriSumA_def assms(1) by auto
  thus ?thesis
    by (meson TriSumA_def suma_comm suma_right_comm suma_sym trisuma_perm_231)
qed

lemma trisuma_perm_213:
  assumes "A B C TriSumA D E F"
  shows "B A C TriSumA D E F"
  using assms trisuma_perm_231 trisuma_perm_321 by blast

lemma trisuma_perm_132:
  assumes "A B C TriSumA D E F"
  shows "A C B TriSumA D E F"
  using assms trisuma_perm_312 trisuma_perm_321 by blast

lemma conga_trisuma__trisuma:
  assumes "A B C TriSumA D E F" and
    "D E F CongA D' E' F'"
  shows "A B C TriSumA D' E' F'"
proof -
  obtain G H I where P1: "A B C B C A SumA G H I \<and> G H I C A B SumA D E F"
    using TriSumA_def assms(1) by auto
  have "G H I C A B SumA D' E' F'"
  proof -
    have f1: "B \<noteq> A"
      by (metis P1 suma_distincts)
    have f2: "C \<noteq> A"
      using P1 suma_distincts by blast
    have "G H I CongA G H I"
      by (metis (full_types) P1 conga_refl suma_distincts)
    then show ?thesis
      using f2 f1 by (meson P1 assms(2) conga3_suma__suma conga_refl)
  qed
  thus ?thesis using P1 TriSumA_def by blast
qed

lemma trisuma2__conga:
  assumes "A B C TriSumA D E F" and
    "A B C TriSumA D' E' F'"
  shows "D E F CongA D' E' F'"
proof -
  obtain G H I where P1: "A B C B C A SumA G H I \<and> G H I C A B SumA D E F"
    using TriSumA_def assms(1) by auto
  then have P1A: "G H I C A B SumA D E F" by simp
  obtain G' H' I' where P2: "A B C B C A SumA G' H' I' \<and> G' H' I' C A B SumA D' E' F'"
    using TriSumA_def assms(2) by auto
  have "G' H' I' C A B SumA D E F"
  proof -
    have "G H I CongA G' H' I'" using P1 P2 suma2__conga by blast
    moreover have "D E F CongA D E F \<and> C A B CongA C A B"
      by (metis assms(1) conga_refl trisuma_distincts)
    ultimately show ?thesis
      by (meson P1 conga3_suma__suma)
  qed
  thus ?thesis
    using P2 suma2__conga by auto
qed

lemma conga3_trisuma__trisuma:
  assumes "A B C TriSumA D E F" and
    "A B C CongA A' B' C'" and
    "B C A CongA B' C' A'" and
    "C A B CongA C' A' B'"
  shows "A' B' C' TriSumA D E F"
proof -
  obtain G H I where P1: "A B C B C A SumA G H I \<and> G H I C A B SumA D E F"
    using TriSumA_def assms(1) by auto
  thus ?thesis
  proof -
    have "A' B' C' B' C' A' SumA G H I"
      using conga3_suma__suma P1 by (meson assms(2) assms(3) suma2__conga)
    moreover have "G H I C' A' B' SumA D E F"
      using conga3_suma__suma P1 by (meson P1 assms(4) suma2__conga)
    ultimately show ?thesis
      using TriSumA_def by blast
  qed
qed

lemma col_trisuma__bet:
  assumes "Col A B C" and
    "A B C TriSumA P Q R"
  shows "Bet P Q R"
proof -
  obtain D E F where P1: "A B C B C A SumA D E F \<and> D E F C A B SumA P Q R"
    using TriSumA_def assms(2) by auto
  {
    assume "Bet A B C"
    have "A B C CongA P Q R"
    proof -
      have "A B C CongA D E F"
      proof -
        have "C \<noteq> A \<and> C \<noteq> B"
          using assms(2) trisuma_distincts by blast
        then have "C Out B A"
          using \<open> Bet A B C\<close> bet_out_1 by fastforce
        thus ?thesis
          using P1 out546_suma__conga by auto
      qed
      moreover have "D E F CongA P Q R"
      proof -
        have "A \<noteq> C \<and> A \<noteq> B"
          using assms(2) trisuma_distincts by blast
        then have "A Out C B"
          using Out_def \<open>Bet A B C\<close> by auto
        thus ?thesis
          using P1 out546_suma__conga by auto
      qed
      ultimately show ?thesis
        using conga_trans by blast
    qed
    then have "Bet P Q R"
      using \<open>Bet A B C\<close> bet_conga__bet by blast
  }
  {
    assume "Bet B C A"
    have "B C A CongA P Q R"
    proof -
      have "B C A CongA D E F"
      proof -
        have "B \<noteq> A \<and> B \<noteq> C"
          using assms(2) trisuma_distincts by blast
        then have "B Out A C"
          using Out_def \<open>Bet B C A\<close> by auto
        thus ?thesis
          using P1 out213_suma__conga by blast
      qed
      moreover have "D E F CongA P Q R"
      proof -
        have "A \<noteq> C \<and> A \<noteq> B"
          using assms(2) trisuma_distincts by auto
        then have "A Out C B"
          using \<open>Bet B C A\<close> bet_out_1 by auto
        thus ?thesis
          using P1 out546_suma__conga by blast
      qed
      ultimately show ?thesis
        using not_conga by blast
    qed
    then have "Bet P Q R"
      using \<open>Bet B C A\<close> bet_conga__bet by blast
  }
  {
    assume "Bet C A B"
    have "E Out D F"
    proof -
      have "C Out B A"
        using \<open>Bet C A B\<close> assms(2) bet_out l6_6 trisuma_distincts by blast
      moreover have "B C A CongA D E F"
      proof -
        have "B \<noteq> A \<and> B \<noteq> C"
          using P1 suma_distincts by blast
        then have "B Out A C"
          using \<open>Bet C A B\<close> bet_out_1 by auto
        thus ?thesis using out213_suma__conga P1 by blast
      qed
      ultimately show ?thesis
        using l11_21_a by blast
    qed

    then have "C A B CongA P Q R"
      using P1 out213_suma__conga by blast
    then have "Bet P Q R"
      using \<open>Bet C A B\<close> bet_conga__bet by blast
  }
  thus ?thesis
    using Col_def \<open>Bet A B C \<Longrightarrow> Bet P Q R\<close> \<open>Bet B C A \<Longrightarrow> Bet P Q R\<close> assms(1) by blast
qed

lemma suma_dec:
  "A B C D E F SumA G H I \<or> \<not> A B C D E F SumA G H I" by simp

lemma sams_dec:
  "SAMS A B C D E F \<or> \<not> SAMS A B C D E F" by simp

lemma trisuma_dec:
  "A B C TriSumA P Q R \<or> \<not> A B C TriSumA P Q R"
  by simp

subsection "Parallelism"

lemma par_reflexivity:
  assumes "A \<noteq> B"
  shows "A B Par A B"
  using Par_def assms not_col_distincts by blast

lemma par_strict_irreflexivity:
  "\<not> A B ParStrict A B"
  using ParStrict_def col_trivial_3 by blast

lemma not_par_strict_id:
  "\<not> A B ParStrict A C"
  using ParStrict_def col_trivial_1 by blast

lemma par_id:
  assumes "A B Par A C"
  shows "Col A B C"
  using Col_cases Par_def assms not_par_strict_id by auto

lemma par_strict_not_col_1:
  assumes "A B ParStrict C D"
  shows "\<not> Col A B C"
  using Col_perm ParStrict_def assms col_trivial_1 by blast

lemma par_strict_not_col_2:
  assumes "A B ParStrict C D"
  shows "\<not> Col B C D"
  using ParStrict_def assms col_trivial_3 by auto

lemma par_strict_not_col_3:
  assumes "A B ParStrict C D"
  shows "\<not> Col C D A"
  using Col_perm ParStrict_def assms col_trivial_1 by blast

lemma par_strict_not_col_4:
  assumes "A B ParStrict C D"
  shows "\<not> Col A B D"
  using Col_perm ParStrict_def assms col_trivial_3 by blast

lemma par_id_1:
  assumes "A B Par A C"
  shows "Col B A C"
  using Par_def assms not_par_strict_id by auto

lemma par_id_2:
  assumes "A B Par A C"
  shows "Col B C A"
  using Col_perm assms par_id_1 by blast

lemma par_id_3:
  assumes "A B Par A C"
  shows "Col A C B"
  using Col_perm assms par_id_2 by blast

lemma par_id_4:
  assumes "A B Par A C"
  shows "Col C B A"
  using Col_perm assms par_id_2 by blast

lemma par_id_5:
  assumes "A B Par A C"
  shows "Col C A B"
  using assms col_permutation_2 par_id by blast

lemma par_strict_symmetry:
  assumes "A B ParStrict C D"
  shows "C D ParStrict A B"
  using ParStrict_def assms coplanar_perm_16 by blast

lemma par_symmetry:
  assumes "A B Par C D"
  shows "C D Par A B"
  by (smt NCol_perm Par_def assms l6_16_1 par_strict_symmetry)

lemma par_left_comm:
  assumes "A B Par C D"
  shows "B A Par C D"
  by (metis (mono_tags, lifting) ParStrict_def Par_def assms ncoplanar_perm_6 not_col_permutation_5)

lemma par_right_comm:
  assumes "A B Par C D"
  shows "A B Par D C"
  using assms par_left_comm par_symmetry by blast

lemma par_comm:
  assumes "A B Par C D"
  shows "B A Par D C"
  using assms par_left_comm par_right_comm by blast

lemma par_strict_left_comm:
  assumes "A B ParStrict C D"
  shows "B A ParStrict C D"
  using ParStrict_def assms ncoplanar_perm_6 not_col_permutation_5 by blast

lemma par_strict_right_comm:
  assumes "A B ParStrict C D"
  shows "A B ParStrict D C"
  using assms par_strict_left_comm par_strict_symmetry by blast

lemma par_strict_comm:
  assumes "A B ParStrict C D"
  shows "B A ParStrict D C"
  by (simp add: assms par_strict_left_comm par_strict_right_comm)

lemma par_strict_neq1:
  assumes "A B ParStrict C D"
  shows "A \<noteq> B"
  using assms col_trivial_1 par_strict_not_col_4 by blast

lemma par_strict_neq2:
  assumes "A B ParStrict C D"
  shows "C \<noteq> D"
  using assms col_trivial_2 par_strict_not_col_2 by blast

lemma par_neq1:
  assumes "A B Par C D"
  shows "A \<noteq> B"
  using Par_def assms par_strict_neq1 by blast

lemma par_neq2:
  assumes "A B Par C D"
  shows "C \<noteq> D"
  using assms par_neq1 par_symmetry by blast

lemma Par_cases:
  assumes "A B Par C D \<or> B A Par C D \<or> A B Par D C \<or> B A Par D C \<or> C D Par A B \<or> C D Par B A \<or> D C Par A B \<or> D C Par B A"
  shows "A B Par C D"
  using assms par_right_comm par_symmetry by blast

lemma Par_perm:
  assumes "A B Par C D"
  shows "A B Par C D \<and> B A Par C D \<and> A B Par D C \<and> B A Par D C \<and> C D Par A B \<and> C D Par B A \<and> D C Par A B \<and> D C Par B A"
  using Par_cases assms by blast

lemma Par_strict_cases:
  assumes "A B ParStrict C D \<or> B A ParStrict C D \<or> A B ParStrict D C \<or> B A ParStrict D C \<or> C D ParStrict A B \<or> C D ParStrict B A \<or> D C ParStrict A B \<or> D C ParStrict B A"
  shows "A B ParStrict C D"
  using assms par_strict_right_comm par_strict_symmetry by blast

lemma Par_strict_perm:
  assumes "A B ParStrict C D"
  shows "A B ParStrict C D \<and> B A ParStrict C D \<and> A B ParStrict D C \<and> B A ParStrict D C \<and> C D ParStrict A B \<and> C D ParStrict B A \<and> D C ParStrict A B \<and> D C ParStrict B A"
  using Par_strict_cases assms by blast

lemma l12_6:
  assumes "A B ParStrict C D"
  shows "A B OS C D"
  by (metis Col_def ParStrict_def Par_strict_perm TS_def assms cop_nts__os par_strict_not_col_2)

lemma pars__os3412:
  assumes "A B ParStrict C D"
  shows "C D OS A B"
  by (simp add: assms l12_6 par_strict_symmetry)

lemma perp_dec:
  "A B Perp C D \<or> \<not> A B Perp C D"
  by simp

lemma col_cop2_perp2__col:
  assumes "X1 X2 Perp A B" and
    "Y1 Y2 Perp A B" and
    "Col X1 Y1 Y2" and
    "Coplanar A B X2 Y1" and
    "Coplanar A B X2 Y2"
  shows "Col X2 Y1 Y2"
proof cases
  assume "X1 = Y2"
  thus ?thesis
    using assms(1) assms(2) assms(4) cop_perp2__col not_col_permutation_2 perp_left_comm by blast
next
  assume "X1 \<noteq> Y2"
  then have "Y2 X1 Perp A B"
    by (metis Col_cases assms(2) assms(3) perp_col perp_comm perp_right_comm)
  then have P1: "X1 Y2 Perp A B"
    using Perp_perm by blast
  thus ?thesis
  proof cases
    assume "X1 = Y1"
    thus ?thesis
      using assms(1) assms(2) assms(5) cop_perp2__col not_col_permutation_4 by blast
  next
    assume "X1 \<noteq> Y1"
    then have "X1 Y1 Perp A B"
      using Col_cases P1 assms(3) perp_col by blast
    thus ?thesis
      using P1 assms(1) assms(4) assms(5) col_transitivity_2 cop_perp2__col perp_not_eq_1 by blast
  qed
qed

lemma col_perp2_ncol_col:
  assumes "X1 X2 Perp A B" and
    "Y1 Y2 Perp A B" and
    "Col X1 Y1 Y2" and
    "\<not> Col X1 A B"
  shows "Col X2 Y1 Y2"
proof -
  have "Coplanar A B X2 Y1"
  proof cases
    assume "X1 = Y1"
    thus ?thesis
      using assms(1) ncoplanar_perm_22 perp__coplanar by blast
  next
    assume "X1 \<noteq> Y1"
    then have "Y1 X1 Perp A B"
      by (metis Col_cases assms(2) assms(3) perp_col)
    thus ?thesis
      by (meson assms(1) assms(4) coplanar_trans_1 ncoplanar_perm_18 ncoplanar_perm_4 perp__coplanar)
  qed
  then moreover have "Coplanar A B X2 Y2"
    by (smt assms(1) assms(2) assms(3) assms(4) col_cop2__cop coplanar_perm_17 coplanar_perm_18 coplanar_trans_1 perp__coplanar)
  ultimately show ?thesis
    using assms(1) assms(2) assms(3) col_cop2_perp2__col by blast
qed

lemma l12_9:
  assumes
    "Coplanar C1 C2 A1 B1" and
    "Coplanar C1 C2 A1 B2" and
    "Coplanar C1 C2 A2 B1" and
    "Coplanar C1 C2 A2 B2" and
    "A1 A2 Perp C1 C2" and
    "B1 B2 Perp C1 C2"
  shows "A1 A2 Par B1 B2"
proof -
  have P1: "A1 \<noteq> A2 \<and> C1 \<noteq> C2"
    using assms(5) perp_distinct by auto
  have P2: "B1 \<noteq> B2"
    using assms(6) perp_distinct by auto
  show ?thesis
  proof cases
    assume "Col A1 B1 B2"
    then show ?thesis
      using P1 P2 Par_def assms(3) assms(4) assms(5) assms(6) col_cop2_perp2__col by blast
  next
    assume P3: "\<not> Col A1 B1 B2"
    {
      assume "\<not> Col C1 C2 A1"
      then have "Coplanar A1 A2 B1 B2"
        by (smt assms(1) assms(2) assms(5) coplanar_perm_22 coplanar_perm_8 coplanar_pseudo_trans ncop_distincts perp__coplanar)
    }
    have "C1 C2 Perp A1 A2"
      using Perp_cases assms(5) by blast
    then have "Coplanar A1 A2 B1 B2"
      by (smt \<open>\<not> Col C1 C2 A1 \<Longrightarrow> Coplanar A1 A2 B1 B2\<close> assms(3) assms(4) coplanar_perm_1 coplanar_pseudo_trans ncop_distincts perp__coplanar perp_not_col2)
    {
      assume "\<exists> X. Col X A1 A2 \<and> Col X B1 B2"
      then obtain AB where P4: "Col AB A1 A2 \<and> Col AB B1 B2" by auto
      then have "False"
      proof cases
        assume "AB = A1"
        thus ?thesis
          using P3 P4 by blast
      next
        assume "AB \<noteq> A1"
        then have "A1 AB Perp C1 C2"
          by (metis P4 assms(5) not_col_permutation_2 perp_col)
        then have "AB A1 Perp C1 C2"
          by (simp add: perp_left_comm)
        thus ?thesis
          using P3 P4 assms(1) assms(2) assms(6) col_cop2_perp2__col by blast
      qed
    }
    then show ?thesis
      using ParStrict_def Par_def \<open>Coplanar A1 A2 B1 B2\<close> by blast
  qed
qed

lemma parallel_existence:
  assumes "A \<noteq> B"
  shows "\<exists> C D. C \<noteq> D \<and> A B Par C D \<and> Col P C D"
proof cases
  assume "Col A B P"
  then show ?thesis
    using Col_perm assms par_reflexivity by blast
next
  assume P1: "\<not> Col A B P"
  then obtain P' where P2: "Col A B P' \<and> A B Perp P P'"
    using l8_18_existence by blast
  then have P3: "P \<noteq> P'"
    using P1 by blast
  show ?thesis
  proof cases
    assume P4: "P' = A"
    have "\<exists> Q. Per Q P A \<and> Cong Q P A B \<and> A P OS Q B"
    proof -
      have "Col A P P"
        using not_col_distincts by auto
      moreover have "\<not> Col A P B"
        by (simp add: P1 not_col_permutation_5)
      ultimately show ?thesis
        using P3 P4 assms ex_per_cong by simp
    qed
    then obtain Q where T1: "Per Q P A \<and> Cong Q P A B \<and> A P OS Q B" by auto
    then have T2: "P \<noteq> Q"
      using os_distincts by auto
    have T3: "A B Par P Q"
    proof -
      have "P Q Perp P A"
      proof -
        have "P \<noteq> A"
          using P3 P4 by auto
        moreover have "Col P P Q"
          by (simp add: col_trivial_1)
        ultimately show ?thesis
          by (metis T1 T2 Tarski_neutral_dimensionless.Perp_perm Tarski_neutral_dimensionless_axioms per_perp)
      qed
      moreover have "Coplanar P A A P"
        using ncop_distincts by auto
      moreover have "Coplanar P A B P"
        using ncop_distincts by auto
      moreover have "Coplanar P A B Q"
        by (metis (no_types) T1 ncoplanar_perm_7 os__coplanar)
      moreover have "A B Perp P A"
        using P2 P4 by auto
      ultimately show ?thesis using l12_9 ncop_distincts by blast
    qed
    thus ?thesis
      using T2 col_trivial_1 by auto
  next
    assume T4: "P' \<noteq> A"
    have "\<exists> Q. Per Q P P' \<and> Cong Q P A B \<and> P' P OS Q A"
    proof -
      have "P' \<noteq> P"
        using P3 by auto
      moreover have "A \<noteq> B"
        by (simp add: assms)
      moreover have "Col P' P P"
        using not_col_distincts by blast
      moreover have "\<not> Col P' P A"
        by (metis P1 P2 T4 col2__eq col_permutation_1)
      ultimately show ?thesis
        using ex_per_cong by blast
    qed
    then obtain Q where T5: "Per Q P P' \<and> Cong Q P A B \<and> P' P OS Q A" by blast
    then have T6: "P \<noteq> Q"
      using os_distincts by blast
    moreover have "A B Par P Q"
    proof -
      have "Coplanar P P' A P"
        using ncop_distincts by auto
      moreover have "Coplanar P P' A Q"
        by (meson T5 ncoplanar_perm_7 os__coplanar)
      then moreover have "Coplanar P P' B Q"
        by (smt P2 T4 col2_cop__cop col_permutation_5 col_transitivity_1 coplanar_perm_5)
      moreover have "Coplanar P P' B P"
        using ncop_distincts by auto
      moreover have "A B Perp P P'"
        by (simp add: P2)
      moreover have "P Q Perp P P'"
        by (metis P3 T5 T6 Tarski_neutral_dimensionless.Perp_perm Tarski_neutral_dimensionless_axioms per_perp)
      ultimately show ?thesis
        using l12_9 by blast
    qed
    moreover have "Col P P Q"
      by (simp add: col_trivial_1)
    ultimately show ?thesis
      by blast
  qed
qed

lemma par_col_par:
  assumes "C \<noteq> D'" and
    "A B Par C D" and
    "Col C D D'"
  shows "A B Par C D'"
proof -
  {
    assume P1: "A B ParStrict C D"
    have "Coplanar A B C D'"
      using assms(2) assms(3) col2__eq col2_cop__cop par__coplanar par_neq2 by blast
    then have "A B Par C D'"
      by (smt ParStrict_def Par_def P1 assms(1) assms(3) colx not_col_distincts not_col_permutation_5)
  }
  {
    assume "A \<noteq> B \<and> C \<noteq> D \<and> Col A C D \<and> Col B C D"
    then have "A B Par C D'"
      using Par_def assms(1) assms(3) col2__eq col_permutation_2 by blast
  }
  thus ?thesis
    using Par_def \<open>A B ParStrict C D \<Longrightarrow> A B Par C D'\<close> assms(2) by auto
qed

lemma parallel_existence1:
  assumes "A \<noteq> B"
  shows "\<exists> Q. A B Par P Q"
proof -
  obtain C D where "C \<noteq> D \<and> A B Par C D \<and> Col P C D"
    using assms parallel_existence by blast
  then show ?thesis
    by (metis Col_cases Par_cases par_col_par)
qed

lemma par_not_col:
  assumes "A B ParStrict C D" and
    "Col X A B"
  shows "\<not> Col X C D"
  using ParStrict_def assms(1) assms(2) by blast

lemma not_strict_par1:
  assumes "A B Par C D" and
    "Col A B X" and
    "Col C D X"
  shows "Col A B C"
  by (smt Par_def assms(1) assms(2) assms(3) col2__eq col_permutation_2 par_not_col)

lemma not_strict_par2:
  assumes "A B Par C D" and
    "Col A B X" and
    "Col C D X"
  shows "Col A B D"
  using Par_cases assms(1) assms(2) assms(3) not_col_permutation_4 not_strict_par1 by blast

lemma not_strict_par:
  assumes "A B Par C D" and
    "Col A B X" and
    "Col C D X"
  shows "Col A B C \<and> Col A B D"
  using assms(1) assms(2) assms(3) not_strict_par1 not_strict_par2 by blast

lemma not_par_not_col:
  assumes "A \<noteq> B" and
    "A \<noteq> C" and
    "\<not> A B Par A C"
  shows "\<not> Col A B C"
  using Par_def assms(1) assms(2) assms(3) not_col_distincts not_col_permutation_4 by blast

lemma not_par_inter_uniqueness:
  assumes "A \<noteq> B" and
    "C \<noteq> D" and
    "\<not> A B Par C D" and
    "Col A B X" and
    "Col C D X" and
    "Col A B Y" and
    "Col C D Y"
  shows "X = Y"
proof cases
  assume P1: "C = Y"
  thus ?thesis
  proof cases
    assume P2: "C = X"
    thus ?thesis
      using P1 by auto
  next
    assume "C \<noteq> X"
    thus ?thesis
      by (smt Par_def assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) col3 col_permutation_5 l6_21)
  qed
next
  assume "C \<noteq> Y"
  thus ?thesis
    by (smt Par_def assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) col_permutation_2 col_permutation_4 l6_21)
qed

lemma inter_uniqueness_not_par:
  assumes  "\<not> Col A B C" and
    "Col A B P" and
    "Col C D P"
  shows "\<not> A B Par C D"
  using assms(1) assms(2) assms(3) not_strict_par1 by blast

lemma col_not_col_not_par:
  assumes "\<exists> P. Col A B P \<and> Col C D P" and
    "\<exists> Q. Col C D Q \<and> \<not>Col A B Q"
  shows "\<not> A B Par C D"
  using assms(1) assms(2) colx not_strict_par par_neq2 by blast

lemma par_distincts:
  assumes "A B Par C D"
  shows "A B Par C D \<and> A \<noteq> B \<and> C \<noteq> D"
  using assms par_neq1 par_neq2 by blast

lemma par_not_col_strict:
  assumes "A B Par C D" and
    "Col C D P" and
    "\<not> Col A B P"
  shows "A B ParStrict C D"
  using Col_cases Par_def assms(1) assms(2) assms(3) col3 by blast

lemma col_cop_perp2_pars:
  assumes "\<not> Col A B P" and
    "Col C D P" and
    "Coplanar A B C D" and
    "A B Perp P Q" and
    "C D Perp P Q"
  shows  "A B ParStrict C D"
proof -
  have P1: "C \<noteq> D"
    using assms(5) perp_not_eq_1 by auto
  then have P2: "Coplanar A B C P"
    using col_cop__cop assms(2) assms(3) by blast
  moreover have P3: "Coplanar A B D P" using col_cop__cop
    using P1 assms(2) assms(3) col2_cop__cop col_trivial_2 by blast
  have "A B Par C D"
  proof -
    have "Coplanar P A Q C"
    proof -
      have "\<not> Col B P A"
        by (simp add: assms(1) not_col_permutation_1)
      moreover have "Coplanar B P A Q"
        by (meson assms(4) ncoplanar_perm_12 perp__coplanar)
      moreover have "Coplanar B P A C"
        using P2 ncoplanar_perm_13 by blast
      ultimately show ?thesis
        using coplanar_trans_1 by auto
    qed
    then have P4: "Coplanar P Q A C"
      using ncoplanar_perm_2 by blast
    have "Coplanar P A Q D"
    proof -
      have "\<not> Col B P A"
        by (simp add: assms(1) not_col_permutation_1)
      moreover have "Coplanar B P A Q"
        by (meson assms(4) ncoplanar_perm_12 perp__coplanar)
      moreover have "Coplanar B P A D"
        using P3 ncoplanar_perm_13 by blast
      ultimately show ?thesis
        using coplanar_trans_1 by blast
    qed
    then moreover have "Coplanar P Q A D"
      using ncoplanar_perm_2 by blast
    moreover have "Coplanar P Q B C"
      using P2 assms(1) assms(4) coplanar_perm_1 coplanar_perm_10 coplanar_trans_1 perp__coplanar by blast
    moreover have "Coplanar P Q B D"
      by (meson P3 assms(1) assms(4) coplanar_trans_1 ncoplanar_perm_1 ncoplanar_perm_13 perp__coplanar)
    ultimately show ?thesis
      using assms(4) assms(5) l12_9 P4 by auto
  qed
  thus ?thesis
    using assms(1) assms(2) par_not_col_strict by auto
qed

lemma all_one_side_par_strict:
  assumes "C \<noteq> D" and
    "\<forall> P. Col C D P \<longrightarrow> A B OS C P"
  shows "A B ParStrict C D"
proof -
  have P1: "Coplanar A B C D"
    by (simp add: assms(2) col_trivial_2 os__coplanar)
  {
    assume "\<exists> X. Col X A B \<and> Col X C D"
    then obtain X where P2: "Col X A B \<and> Col X C D" by blast
    have "A B OS C X"
      by (simp add: P2 Col_perm assms(2))
    then obtain M where "A B TS C M \<and> A B TS X M"
      by (meson Col_cases P2 col124__nos)
    then have "False"
      using P2 TS_def by blast
  }
  thus ?thesis
    using P1 ParStrict_def by auto
qed

lemma par_col_par_2:
  assumes "A \<noteq> P" and
    "Col A B P" and
    "A B Par C D"
  shows "A P Par C D"
  using assms(1) assms(2) assms(3) par_col_par par_symmetry by blast

lemma par_col2_par:
  assumes "E \<noteq> F" and
    "A B Par C D" and
    "Col C D E" and
    "Col C D F"
  shows "A B Par E F"
  by (metis assms(1) assms(2) assms(3) assms(4) col_transitivity_2 not_col_permutation_4 par_col_par par_distincts par_right_comm)

lemma par_col2_par_bis:
  assumes "E \<noteq> F" and
    "A B Par C D" and
    "Col E F C" and
    "Col E F D"
  shows "A B Par E F"
  by (metis assms(1) assms(2) assms(3) assms(4) col_transitivity_1 not_col_permutation_2 par_col2_par)

lemma par_strict_col_par_strict:
  assumes "C \<noteq> E" and
    "A B ParStrict C D" and
    "Col C D E"
  shows "A B ParStrict C E"
proof -
  have P1: "C E Par A B"
    using Par_def Par_perm assms(1) assms(2) assms(3) par_col_par_2 by blast
  {
    assume "C E ParStrict A B"
    then have "A B ParStrict C E"
      by (metis par_strict_symmetry)
  }
  thus ?thesis
    using Col_cases Par_def P1 assms(2) par_strict_not_col_1 by blast
qed

lemma par_strict_col2_par_strict:
  assumes "E \<noteq> F" and
    "A B ParStrict C D" and
    "Col C D E" and
    "Col C D F"
  shows "A B ParStrict E F"
  by (smt ParStrict_def assms(1) assms(2) assms(3) assms(4) col2_cop__cop colx not_col_permutation_1 par_strict_neq1 par_strict_symmetry)

lemma line_dec:
  "(Col C1 B1 B2 \<and> Col C2 B1 B2) \<or> \<not> (Col C1 B1 B2 \<and> Col C2 B1 B2)"
  by simp

lemma par_distinct:
  assumes "A B Par C D"
  shows "A \<noteq> B \<and> C \<noteq> D"
  using assms par_neq1 par_neq2 by auto

lemma par_col4__par:
  assumes "E \<noteq> F" and
    "G \<noteq> H" and
    "A B Par C D" and
    "Col A B E" and
    "Col A B F" and
    "Col C D G" and
    "Col C D H"
  shows "E F Par G H"
proof -
  have "C D Par E F"
    using Par_cases assms(1) assms(3) assms(4) assms(5) par_col2_par by blast
  then have "E F Par C D"
    by (simp add: \<open>C D Par E F\<close> par_symmetry)
  thus ?thesis
    using assms(2) assms(6) assms(7) par_col2_par by blast
qed

lemma par_strict_col4__par_strict:
  assumes "E \<noteq> F" and
    "G \<noteq> H" and
    "A B ParStrict C D" and
    "Col A B E" and
    "Col A B F" and
    "Col C D G" and
    "Col C D H"
  shows "E F ParStrict G H"
proof -
  have "C D ParStrict E F"
    using Par_strict_cases assms(1) assms(3) assms(4) assms(5) par_strict_col2_par_strict by blast
  then have "E F ParStrict C D"
    by (simp add: \<open>C D ParStrict E F\<close> par_strict_symmetry)
  thus ?thesis
    using assms(2) assms(6) assms(7) par_strict_col2_par_strict by blast
qed

lemma par_strict_one_side:
  assumes "A B ParStrict C D" and
    "Col C D P"
  shows "A B OS C P"
proof cases
  assume "C = P"
  thus ?thesis
    using assms(1) assms(2) not_col_permutation_5 one_side_reflexivity par_not_col by blast
next
  assume "C \<noteq> P"
  thus ?thesis
    using assms(1) assms(2) l12_6 par_strict_col_par_strict by blast
qed

lemma par_strict_all_one_side:
  assumes "A B ParStrict C D"
  shows "\<forall> P. Col C D P \<longrightarrow> A B OS C P"
  using assms par_strict_one_side by blast

lemma inter_trivial:
  assumes "\<not> Col A B X"
  shows "X Inter A X B X"
  by (metis Col_perm Inter_def assms col_trivial_1)

lemma inter_sym:
  assumes "X Inter A B C D"
  shows "X Inter C D A B"
proof -
  obtain P where P1: "Col P C D \<and> \<not> Col P A B"
    using Inter_def assms by auto
  have P2: "A \<noteq> B"
    using P1 col_trivial_2 by blast
  then show ?thesis
  proof cases
    assume "A = X"
    have "Col B A B"
      by (simp add: col_trivial_3)
    {
      assume P3: "Col B C D"
      have "Col P A B"
      proof -
        have "C \<noteq> D"
          using Inter_def assms by blast
        moreover have "Col C D P"
          using P1 not_col_permutation_2 by blast
        moreover have "Col C D A"
          using Inter_def \<open>A = X\<close> assms by auto
        moreover have "Col C D B"
          using P3 not_col_permutation_2 by blast
        ultimately show ?thesis
          using col3 by blast
      qed
      then have "False"
        by (simp add: P1)
    }
    then have "\<not> Col B C D" by auto
    then show ?thesis
      using Inter_def P2 assms by (meson col_trivial_3)
  next
    assume P5: "A \<noteq> X"
    have P6: "Col A A B"
      using not_col_distincts by blast
    {
      assume P7: "Col A C D"
      have "Col A P X"
      proof -
        have "C \<noteq> D"
          using Inter_def assms by auto
        moreover have "Col C D A"
          using Col_cases P7 by blast
        moreover have "Col C D P"
          using Col_cases P1 by auto
        moreover have "Col C D X"
          using Inter_def assms by auto
        ultimately show ?thesis
          using col3 by blast
      qed
      then have "Col P A B"
        by (metis (full_types) Col_perm Inter_def P5 assms col_transitivity_2)
      then have "False"
        by (simp add: P1)
    }
    then have "\<not> Col A C D" by auto
    then show ?thesis
      by (meson Inter_def P2 assms col_trivial_1)
  qed
qed

lemma inter_left_comm:
  assumes "X Inter A B C D"
  shows "X Inter B A C D"
  using Col_cases Inter_def assms by auto

lemma inter_right_comm:
  assumes "X Inter A B C D"
  shows "X Inter A B D C"
  by (metis assms inter_left_comm inter_sym)

lemma inter_comm:
  assumes "X Inter A B C D"
  shows "X Inter B A D C"
  using assms inter_left_comm inter_right_comm by blast

lemma l12_17:
  assumes "A \<noteq> B" and
    "P Midpoint A C" and
    "P Midpoint B D"
  shows "A B Par C D"
proof cases
  assume P1: "Col A B P"
  thus ?thesis
  proof cases
    assume "A = P"
    thus ?thesis
      using assms(1) assms(2) assms(3) cong_diff_2 is_midpoint_id midpoint_col midpoint_cong not_par_not_col by blast
  next
    assume P2: "A \<noteq> P"
    thus ?thesis
    proof cases
      assume "B = P"
      thus ?thesis
        by (metis assms(1) assms(2) assms(3) midpoint_col midpoint_distinct_2 midpoint_distinct_3 not_par_not_col par_comm)
    next
      assume P3: "B \<noteq> P"
      have P4: "Col B P D"
        using assms(3) midpoint_col not_col_permutation_4 by blast
      have P5: "Col A P C"
        using assms(2) midpoint_col not_col_permutation_4 by blast
      then have P6: "Col B C P"
        using P1 P2 col_transitivity_2 not_col_permutation_3 not_col_permutation_5 by blast
      have "C \<noteq> D"
        using assms(1) assms(2) assms(3) l7_9 by blast
      moreover have "Col A C D"
        using P1 P3 P4 P6 col3 not_col_permutation_3 not_col_permutation_5 by blast
      moreover have "Col B C D"
        using P3 P4 P6 col_trivial_3 colx by blast
      ultimately show ?thesis
        by (simp add: Par_def assms(1))
    qed
  qed
next
  assume T1: "\<not> Col A B P"
  then obtain E where T2: "Col A B E \<and> A B Perp P E"
    using l8_18_existence by blast
  have T3: "A \<noteq> P"
    using T1 col_trivial_3 by blast
  then show ?thesis
  proof cases
    assume T4: "A = E"
    then have T5: "Per P A B"
      using T2 l8_2 perp_per_1 by blast
    obtain B' where T6: "Bet B A B' \<and> Cong A B' B A"
      using segment_construction by blast
    obtain D' where T7: "Bet B' P D' \<and> Cong P D' B' P"
      using segment_construction by blast
    have T8: "C Midpoint D D'"
      using T6 T7 assms(2) assms(3) midpoint_def not_cong_3412 symmetry_preserves_midpoint by blast
    have "Col A B B'"
      using Col_cases Col_def T6 by blast
    then have T9: "Per P A B'"
      using per_col T5 assms(1) by blast
    obtain B'' where T10: "A Midpoint B B'' \<and> Cong P B P B''"
      using Per_def T5 by auto
    then have "B' = B''"
      using T6 cong_symmetry midpoint_def symmetric_point_uniqueness by blast
    then have "Cong P D P D'"
      by (metis Cong_perm Midpoint_def T10 T7 assms(3) cong_inner_transitivity)
    then have T12: "Per P C D"
      using Per_def T8 by auto
    then have T13: "C PerpAt P C C D"
      by (metis T3 assms(1) assms(2) assms(3) l7_3_2 per_perp_in sym_preserve_diff)
    have T14: "P \<noteq> C"
      using T3 assms(2) is_midpoint_id_2 by auto
    have T15: "C \<noteq> D"
      using assms(1) assms(2) assms(3) l7_9 by auto
    have T15A: "C C Perp C D \<or> P C Perp C D"
      using T12 T14 T15 per_perp by auto
    {
      assume "C C Perp C D"
      then have "A B Par C D"
        using perp_distinct by auto
    }
    {
      assume "P C Perp C D"
      have "A B Par C D"
      proof -
        have "Coplanar P A A C"
          using ncop_distincts by blast
        moreover have "Coplanar P A A D"
          using ncop_distincts by blast
        moreover have "Coplanar P A B C"
          by (simp add: assms(2) coplanar_perm_1 midpoint__coplanar)
        moreover have "Coplanar P A B D"
          using assms(3) midpoint_col ncop__ncols by blast
        moreover have "A B Perp P A"
          using T2 T4 by auto
        moreover have "C D Perp P A"
        proof -
          have "P A Perp C D"
          proof -
            have "P \<noteq> A"
              using T3 by auto
            moreover have "P C Perp C D"
              using T14 T15 T12 per_perp by blast
            moreover have "Col P C A"
              by (simp add: assms(2) l7_2 midpoint_col)
            ultimately show ?thesis
              using perp_col by blast
          qed
          then show ?thesis
            using Perp_perm by blast
        qed
        ultimately show ?thesis using l12_9 by blast
      qed
    }
    then show ?thesis using T15A
      using \<open>C C Perp C D \<Longrightarrow> A B Par C D\<close> by blast
  next
    assume S1B: "A \<noteq> E"
    obtain F where S2: "Bet E P F \<and> Cong P F E P"
      using segment_construction by blast
    then have S2A: "P Midpoint E F"
      using midpoint_def not_cong_3412 by blast
    then have S3: "Col C D F"
      using T2 assms(2) assms(3) mid_preserves_col by blast
    obtain A' where S4: "Bet A E A' \<and> Cong E A' A E"
      using segment_construction by blast
    obtain C' where S5: "Bet A' P C' \<and> Cong P C' A' P"
      using segment_construction by blast
    have S6: "F Midpoint C C'"
      using S4 S5 S2A assms(2) midpoint_def not_cong_3412 symmetry_preserves_midpoint by blast
    have S7: "Per P E A"
      using T2 col_trivial_3 l8_16_1 by blast
    have S8: "Cong P C P C'"
    proof -
      have "Cong P C P A"
        using Cong_perm Midpoint_def assms(2) by blast
      moreover have "Cong P A P C'"
      proof -
        obtain A'' where S9: "E Midpoint A A'' \<and> Cong P A P A''"
          using Per_def S7 by blast
        have S10: "A' = A''"
          using Cong_perm Midpoint_def S4 S9 symmetric_point_uniqueness by blast
        then have "Cong P A P A'" using S9 by auto
        moreover have "Cong P A' P C'"
          using Cong_perm S5 by blast
        ultimately show ?thesis
          using cong_transitivity by blast
      qed
      ultimately show ?thesis
        using cong_transitivity by blast
    qed
    then have S9: "Per P F C"
      using S6 Per_def by blast
    then have "F PerpAt P F F C"
      by (metis S2 S2A T1 T2 S1B assms(2) cong_diff_3 l7_9 per_perp_in)
    then have "F PerpAt F P C F"
      using Perp_in_perm by blast
    then have S10: "F P Perp C F \<or> F F Perp C F"
      using l8_15_2 perp_in_col by blast
    {
      assume S11: "F P Perp C F"
      have "Coplanar P E A C"
      proof -
        have "Col P E P \<and> Col A C P"
          using assms(2) col_trivial_3 midpoint_col not_col_permutation_2 by blast
        then show ?thesis
          using Coplanar_def by blast
      qed
      moreover have "Coplanar P E A D"
      proof -
        have "Col P D B \<and> Col E A B"
          using Mid_cases T2 assms(3) midpoint_col not_col_permutation_1 by blast
        then show ?thesis
          using Coplanar_def by blast
      qed
      moreover have "Coplanar P E B C"
        by (metis S1B T2 calculation(1) col2_cop__cop col_transitivity_1 ncoplanar_perm_5 not_col_permutation_5)
      moreover have "Coplanar P E B D"
        by (metis S1B T2 calculation(2) col2_cop__cop col_transitivity_1 ncoplanar_perm_5 not_col_permutation_5)
      moreover have "C D Perp P E"
      proof -
        have "C \<noteq> D"
          using assms(1) assms(2) assms(3) sym_preserve_diff by blast
        moreover have "P F Perp C F"
          using Perp_perm S11 by blast
        moreover have "Col P F E"
          by (simp add: Col_def S2)
        moreover have "Col C F D"
          using Col_perm S3 by blast
        ultimately show ?thesis using per_col
          by (smt Perp_cases S2 col_trivial_3 cong_diff perp_col4 perp_not_eq_1)
      qed
      ultimately have "A B Par C D"
        using T2 l12_9 by blast
    }
    {
      assume "F F Perp C F"
      then have "A B Par C D"
        using perp_distinct by blast
    }
    thus ?thesis
      using S10 \<open>F P Perp C F \<Longrightarrow> A B Par C D\<close> by blast
  qed
qed

lemma l12_18_a:
  assumes "Cong A B C D" and
    "Cong B C D A" and
    "\<not> Col A B C" and
    "B \<noteq> D" and
    "Col A P C" and
    "Col B P D"
  shows "A B Par C D"
proof -
  have "P Midpoint A C \<and> P Midpoint B D"
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l7_21 by blast
  then show ?thesis
    using assms(3) l12_17 not_col_distincts by blast
qed

lemma l12_18_b:
  assumes "Cong A B C D" and
    "Cong B C D A" and
    "\<not> Col A B C" and
    "B \<noteq> D" and
    "Col A P C" and
    "Col B P D"
  shows "B C Par D A"
  by (smt assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) cong_symmetry inter_uniqueness_not_par l12_18_a l6_21 not_col_distincts)

lemma l12_18_c:
  assumes "Cong A B C D" and
    "Cong B C D A" and
    "\<not> Col A B C" and
    "B \<noteq> D" and
    "Col A P C" and
    "Col B P D"
  shows "B D TS A C"
proof -
  have "P Midpoint A C \<and> P Midpoint B D"
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l7_21 by blast
  then show ?thesis
  proof -
    have "A C TS B D"
      by (metis Col_cases Tarski_neutral_dimensionless.mid_two_sides Tarski_neutral_dimensionless_axioms \<open>P Midpoint A C \<and> P Midpoint B D\<close> assms(3))
    then have "\<not> Col B D A"
      by (meson Col_cases Tarski_neutral_dimensionless.mid_preserves_col Tarski_neutral_dimensionless.ts__ncol Tarski_neutral_dimensionless_axioms \<open>P Midpoint A C \<and> P Midpoint B D\<close> l7_2)
    then show ?thesis
      by (meson Tarski_neutral_dimensionless.mid_two_sides Tarski_neutral_dimensionless_axioms \<open>P Midpoint A C \<and> P Midpoint B D\<close>)
  qed
qed

lemma l12_18_d:
  assumes "Cong A B C D" and
    "Cong B C D A" and
    "\<not> Col A B C" and
    "B \<noteq> D" and
    "Col A P C" and
    "Col B P D"
  shows "A C TS B D"
  by (metis (no_types, lifting) Col_cases TS_def assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l12_18_c not_col_distincts not_cong_2143 not_cong_4321)

lemma l12_18:
  assumes "Cong A B C D" and
    "Cong B C D A" and
    "\<not> Col A B C" and
    "B \<noteq> D" and
    "Col A P C" and
    "Col B P D"
  shows "A B Par C D \<and> B C Par D A \<and> B D TS A C \<and> A C TS B D"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l12_18_a l12_18_b l12_18_c l12_18_d by auto

lemma par_two_sides_two_sides:
  assumes "A B Par C D" and
    "B D TS A C"
  shows "A C TS B D"
  by (metis Par_def TS_def assms(1) assms(2) invert_one_side invert_two_sides l12_6 l9_31 not_col_permutation_4 one_side_symmetry os_ts1324__os pars__os3412)

lemma par_one_or_two_sides:
  assumes "A B ParStrict C D"
  shows "(A C TS B D \<and> B D TS A C) \<or> (A C OS B D \<and> B D OS A C)"
  by (smt Par_def assms invert_one_side l12_6 l9_31 not_col_permutation_3 os_ts1324__os par_strict_not_col_1 par_strict_not_col_2 par_two_sides_two_sides pars__os3412 two_sides_cases)

lemma l12_21_b:
  assumes "A C TS B D" and
    "B A C CongA D C A"
  shows "A B Par C D"
proof -
  have P1: "\<not> Col A B C"
    using TS_def assms(1) not_col_permutation_4 by blast
  then have P2: "A \<noteq> B"
    using col_trivial_1 by auto
  have P3: "C \<noteq> D"
    using assms(1) ts_distincts by blast
  then obtain D' where P4: "C Out D D' \<and> Cong C D' A B"
    using P2 segment_construction_3 by blast
  have P5: "B A C CongA D' C A"
  proof -
    have "A Out B B"
      using P2 out_trivial by auto
    moreover have "A Out C C"
      using P1 col_trivial_3 out_trivial by force
    moreover have "C Out D' D"
      by (simp add: P4 l6_6)
    moreover have "C Out A A"
      using P1 not_col_distincts out_trivial by auto
    ultimately show ?thesis
      using assms(2) l11_10 by blast
  qed
  then have P6: "Cong D' A B C"
    using Cong_perm P4 cong_pseudo_reflexivity l11_49 by blast
  have P7: "A C TS D' B"
  proof -
    have "A C TS D B"
      by (simp add: assms(1) l9_2)
    moreover have "Col C A C"
      using col_trivial_3 by auto
    ultimately show ?thesis
      using P4 l9_5 by blast
  qed
  then obtain M where P8: "Col M A C \<and> Bet D' M B"
    using TS_def by blast
  have "B \<noteq> D'"
    using P7 not_two_sides_id by blast
  then have "M Midpoint A C \<and> M Midpoint B D'"
    by (metis Col_cases P1 P4 P6 P8 bet_col l7_21 not_cong_3412)
  then have "A B Par C D'"
    using P2 l12_17 by blast
  thus ?thesis
    by (meson P3 P4 Tarski_neutral_dimensionless.par_col_par Tarski_neutral_dimensionless_axioms l6_6 out_col)
qed

lemma l12_22_aux:
  assumes "P \<noteq> A" and
    "A \<noteq> C" and
    "Bet P A C" and
    "P A OS B D" and
    "B A P CongA D C P"
  shows "A B Par C D"
proof -
  have P1: "P \<noteq> C"
    using CongA_def assms(5) by blast
  obtain B' where P2: "Bet B A B' \<and> Cong A B' B A"
    using segment_construction by blast
  have P3: "P A B CongA C A B'"
    by (metis CongA_def P2 assms(2) assms(3) assms(5) cong_reverse_identity l11_14)
  have P4: "D C A CongA D C P"
    by (metis Col_def assms(2) assms(3) assms(4) bet_out_1 col124__nos l6_6 out2__conga out_trivial)
  have P5: "A B' Par C D"
  proof -
    have "\<not> Col B P A"
      using assms(4) col123__nos not_col_permutation_2 by blast
    then have "P A TS B B'"
      by (metis P2 assms(4) bet__ts cong_reverse_identity invert_two_sides not_col_permutation_3 os_distincts)
    then have "A C TS B' D"
      by (meson assms(2) assms(3) assms(4) bet_col bet_col1 col_preserves_two_sides l9_2 l9_8_2)
    moreover have "B' A C CongA D C A"
    proof -
      have "B' A C CongA B A P"
        by (simp add: P3 conga_comm conga_sym)
      moreover have "B A P CongA D C A"
        using P4 assms(5) not_conga not_conga_sym by blast
      ultimately show ?thesis
        using not_conga by blast
    qed
    ultimately show ?thesis
      using l12_21_b by blast
  qed
  have "C D Par A B"
  proof -
    have "A \<noteq> B"
      using assms(4) os_distincts by blast
    moreover have "C D Par A B'"
      using P5 par_symmetry by blast
    moreover have "Col A B' B"
      by (simp add: Col_def P2)
    ultimately show ?thesis
      using par_col_par by blast
  qed
  thus ?thesis
    using Par_cases by blast
qed

lemma l12_22_b:
  assumes "P Out A C" and
    "P A OS B D" and
    "B A P CongA D C P"
  shows "A B Par C D"
proof cases
  assume "A = C"
  then show ?thesis
    using assms(2) assms(3) conga_comm conga_os__out not_par_not_col os_distincts out_col by blast
next
  assume P1: "A \<noteq> C"
  {
    assume "Bet P A C"
    then have "A B Par C D"
      using P1 assms(2) assms(3) conga_diff2 l12_22_aux by blast
  }
  {
    assume P2: "Bet P C A"
    have "C D Par A B"
    proof -
      have "P C OS D B"
        using assms(1) assms(2) col_one_side one_side_symmetry out_col out_diff2 by blast
      moreover have "D C P CongA B A P"
        using assms(3) not_conga_sym by blast
      then show ?thesis
        by (metis P1 P2 assms(1) calculation l12_22_aux out_distinct)
    qed
    then have "A B Par C D"
      using Par_cases by auto
  }
  then show ?thesis
    using Out_def \<open>Bet P A C \<Longrightarrow> A B Par C D\<close> assms(1) by blast
qed

lemma par_strict_par:
  assumes "A B ParStrict C D"
  shows "A B Par C D"
  using Par_def assms by auto

lemma par_strict_distinct:
  assumes "A B ParStrict C D"
  shows " A \<noteq> B \<and> C \<noteq> D"
  using assms par_strict_neq1 par_strict_neq2 by auto

lemma col_par:
  assumes "A \<noteq> B" and
    "B \<noteq> C" and
    "Col A B C"
  shows "A B Par B C"
  by (simp add: Par_def assms(1) assms(2) assms(3) col_trivial_1)

lemma acute_col_perp__out:
  assumes "Acute A B C" and
    "Col B C A'" and
    "B C Perp A A'"
  shows "B Out A' C"
proof -
  {
    assume P1: "\<not> Col B C A"
    then obtain B' where P2: "B C Perp B' B \<and> B C OS A B'"
      using assms(2) l10_15 os_distincts by blast
    have P3: "\<not> Col B' B C"
      using P2 col124__nos col_permutation_1 by blast
    {
      assume "Col B B' A"
      then have "A B C LtA A B C"
        using P2 acute_one_side_aux acute_sym assms(1) one_side_not_col124 by blast
      then have "False"
        by (simp add: nlta)
    }
    then have P4: "\<not> Col B B' A" by auto
    have P5: "B B' ParStrict A A'"
    proof -
      have "B B' Par A A'"
      proof -
        have "Coplanar B C B A"
          using ncop_distincts by blast
        moreover have "Coplanar B C B A'"
          using ncop_distincts by blast
        moreover have "Coplanar B C B' A"
          using P2 coplanar_perm_1 os__coplanar by blast
        moreover have "Coplanar B C B' A'"
          using assms(2) ncop__ncols by auto
        moreover have "B B' Perp B C"
          using P2 Perp_perm by blast
        moreover have "A A' Perp B C"
          using Perp_perm assms(3) by blast
        ultimately show ?thesis
          using l12_9 by auto
      qed
      moreover have "Col A A' A"
        by (simp add: col_trivial_3)
      moreover have "\<not> Col B B' A"
        by (simp add: P4)
      ultimately show ?thesis
        using par_not_col_strict by auto
    qed
    then have P6: "\<not> Col B B' A'"
      using P5 par_strict_not_col_4 by auto
    then have "B B' OS A' C"
    proof -
      have "B B' OS A' A"
        using P5 l12_6 one_side_symmetry by blast
      moreover have "B B' OS A C"
        using P2 acute_one_side_aux acute_sym assms(1) one_side_symmetry by blast
      ultimately show ?thesis
        using one_side_transitivity by blast
    qed
    then have "B Out A' C"
      using Col_cases assms(2) col_one_side_out by blast
  }
  then show ?thesis
    using assms(2) assms(3) perp_not_col2 by blast
qed

lemma acute_col_perp__out_1:
  assumes "Acute A B C" and
    "Col B C A'" and
    "B A Perp A A'"
  shows "B Out A' C"
proof -
  obtain A0 where P1: "Bet A B A0 \<and> Cong B A0 A B"
    using segment_construction by blast
  obtain C0 where P2: "Bet C B C0 \<and> Cong B C0 C B"
    using segment_construction by blast
  have P3: "\<not> Col B A A'"
    using assms(3) col_trivial_2 perp_not_col2 by blast
  have "Bet A' B C0"
  proof -
    have P4: "Col A' B C0"
      using P2 acute_distincts assms(1) assms(2) bet_col col_transitivity_2 not_col_permutation_4 by blast
    {
      assume P5: "B Out A' C0"
      have "B Out A A0"
      proof -
        have "Bet C B A'"
          by (smt Bet_perm Col_def P2 P5 assms(2) between_exchange3 not_bet_and_out outer_transitivity_between2)
        then have "A B C CongA A0 B A'"
          using P1 P3 acute_distincts assms(1) cong_diff_4 l11_14 not_col_distincts by blast
        then have "Acute A' B A0"
          using acute_conga__acute acute_sym assms(1) by blast
        moreover have "B A0 Perp A' A"
        proof -
          have "B \<noteq> A0"
            using P1 P3 col_trivial_1 cong_reverse_identity by blast
          moreover have "B A Perp A' A"
            using Perp_perm assms(3) by blast
          moreover have "Col B A A0"
            using P1 bet_col not_col_permutation_4 by blast
          ultimately show ?thesis
            using perp_col by blast
        qed
        ultimately show ?thesis
          using Col_cases P1 acute_col_perp__out bet_col by blast
      qed
      then have "False"
        using P1 not_bet_and_out by blast
    }
    moreover then have "\<not> B Out A' C0" by auto
    ultimately show ?thesis
      using l6_4_2 P4 by blast
  qed
  then show ?thesis
    by (metis P2 P3 acute_distincts assms(1) cong_diff_3 l6_2 not_col_distincts)
qed

lemma conga_inangle_per2__inangle:
  assumes "Per A B C" and
    "T InAngle A B C" and
    "P B A CongA P B C" and
    "Per B P T" and
    "Coplanar A B C P"
  shows "P InAngle A B C"
proof cases
  assume "P = T"
  then show ?thesis
    by (simp add: assms(2))
next
  assume P1: "P \<noteq> T"
  obtain P' where P2: "P' InAngle A B C \<and> P' B A CongA P' B C"
    using CongA_def angle_bisector assms(3) by presburger
  have P3: "Acute P' B A"
    using P2 acute_sym assms(1) conga_inangle_per__acute by blast
  have P4: "\<not> Col A B C"
    using assms(1) assms(3) conga_diff2 conga_diff56 l8_9 by blast
  have P5: "Col B P P'"
  proof -
    have "\<not> B Out A C"
      using Col_cases P4 out_col by blast
    moreover have "Coplanar A B P P'"
    proof -
      have T1: "\<not> Col C A B"
        using Col_perm P4 by blast
      moreover have "Coplanar C A B P"
        using assms(5) ncoplanar_perm_8 by blast
      moreover have "Coplanar C A B P'"
        using P2 inangle__coplanar ncoplanar_perm_21 by blast
      ultimately show ?thesis
        using coplanar_trans_1 by blast
    qed
    moreover have "Coplanar B C P P'"
    proof -
      have "Coplanar A B C P"
        by (meson P2 bet__coplanar calculation(1) calculation(2) col_in_angle_out coplanar_perm_18 coplanar_trans_1 inangle__coplanar l11_21_a l6_6 l6_7 not_col_permutation_4 not_col_permutation_5)
      have "Coplanar A B C P'"
        using P2 inangle__coplanar ncoplanar_perm_18 by blast
      then show ?thesis
        using P4 \<open>Coplanar A B C P\<close> coplanar_trans_1 by blast
    qed
    ultimately show ?thesis using conga2_cop2__col P2 assms(3) by blast
  qed
  have "B Out P P'"
  proof -
    have "Acute T B P'"
      using P2 acute_sym assms(1) assms(2) conga_inangle2_per__acute by blast
    moreover have "B P' Perp T P"
      by (metis P1 P5 acute_distincts assms(3) assms(4) calculation col_per_perp conga_distinct l8_2 not_col_permutation_4)
    ultimately show ?thesis
      using Col_cases P5 acute_col_perp__out by blast
  qed
  then show ?thesis
    using Out_cases P2 in_angle_trans inangle_distincts out341__inangle by blast
qed

lemma perp_not_par:
  assumes "A B Perp X Y"
  shows "\<not> A B Par X Y"
proof -
  obtain P where P1: "P PerpAt A B X Y"
    using Perp_def assms by blast
  {
    assume P2: "A B Par X Y"
    {
      assume P3: "A B ParStrict X Y"
      then have "False"
      proof -
        have "Col P A B"
          using Col_perm P1 perp_in_col by blast
        moreover have "Col P X Y"
          using P1 col_permutation_2 perp_in_col by blast
        ultimately show ?thesis
          using P3 par_not_col by blast
      qed
    }
    {
      assume P4: "A \<noteq> B \<and> X \<noteq> Y \<and> Col A X Y \<and> Col B X Y"
      then have "False"
      proof cases
        assume "A = Y"
        thus ?thesis
          using P4 assms not_col_permutation_1 perp_not_col by blast
      next
        assume "A \<noteq> Y"
        thus ?thesis
          using Col_perm P4 Perp_perm assms perp_not_col2 by blast
      qed
    }
    then have "False"
      using Par_def P2 \<open>A B ParStrict X Y \<Longrightarrow> False\<close> by auto
  }
  thus ?thesis by auto
qed

lemma cong_conga_perp:
  assumes "B P TS A C" and
    "Cong A B C B" and
    "A B P CongA C B P"
  shows "A C Perp B P"
proof -
  have P1: " \<not> Col A B P"
    using TS_def assms(1) by blast
  then have P2: "B \<noteq> P"
    using col_trivial_2 by blast
  have P3: "A \<noteq> B"
    using assms(1) ts_distincts by blast
  have P4: "C \<noteq> B"
    using assms(1) ts_distincts by auto
  have P5: "A \<noteq> C"
    using assms(1) not_two_sides_id by auto
  show ?thesis
  proof cases
    assume P6: "Bet A B C"
    then have "Per P B A"
      by (meson Tarski_neutral_dimensionless.conga_comm Tarski_neutral_dimensionless_axioms assms(3) l11_18_2)
    then show ?thesis
      using P2 P3 P5 Per_perm P6 bet_col per_perp perp_col by blast
  next
    assume P7: "\<not> Bet A B C"
    obtain T where P7A: "Col T B P \<and> Bet A T C"
      using TS_def assms(1) by auto
    then have P8: "B \<noteq> T"
      using P7 by blast
    then have P9: "T B A CongA T B C"
      by (meson Col_cases P7A Tarski_neutral_dimensionless.col_conga__conga Tarski_neutral_dimensionless.conga_comm Tarski_neutral_dimensionless_axioms assms(3))
    then have P10: "Cong T A T C"
      using assms(2) cong2_conga_cong cong_reflexivity not_cong_2143 by blast
    then have P11: "T Midpoint A C"
      using P7A midpoint_def not_cong_2134 by blast
    have P12: "Per B T A"
      using P11 Per_def assms(2) not_cong_2143 by blast
    then show ?thesis
    proof -
      have "A C Perp B T"
        by (metis P11 P12 P5 P8 col_per_perp midpoint_col midpoint_distinct_1)
      moreover have "B \<noteq> T"
        by (simp add: P8)
      moreover have "T \<noteq> A"
        using P1 P7A by blast
      moreover have "C \<noteq> T"
        using P10 P5 cong_identity by blast
      moreover have "C \<noteq> A"
        using P5 by auto
      moreover have "Col T A C"
        by (meson P7A bet_col not_col_permutation_4)
      ultimately show ?thesis
        using P2 P7A not_col_permutation_4 perp_col1 by blast
    qed
  qed
qed

lemma perp_inter_exists:
  assumes "A B Perp C D"
  shows "\<exists> P. Col A B P \<and> Col C D P"
proof -
  obtain P where "P PerpAt A B C D"
    using Perp_def assms by auto
  then show ?thesis
    using perp_in_col by blast
qed

lemma perp_inter_perp_in:
  assumes "A B Perp C D"
  shows "\<exists> P. Col A B P \<and> Col C D P \<and> P PerpAt A B C D"
  by (meson Perp_def Tarski_neutral_dimensionless.perp_in_col Tarski_neutral_dimensionless_axioms assms)

end

context Tarski_2D

begin

lemma l12_9_2D:
  assumes "A1 A2 Perp C1 C2" and
    "B1 B2 Perp C1 C2"
  shows "A1 A2 Par B1 B2"
  using l12_9 all_coplanar assms(1) assms(2) by auto

end

context Tarski_neutral_dimensionless

begin

subsection "Tarski: Chapter 13"

subsubsection "Introduction"

lemma per2_col_eq:
  assumes "A \<noteq> P" and
    "A \<noteq> P'" and
    "Per A P B" and
    "Per A P' B" and
    "Col P A P'"
  shows "P = P'"
  by (metis assms(1) assms(2) assms(3) assms(4) assms(5) col_per2_cases l6_16_1 l8_2 not_col_permutation_3)

lemma per2_preserves_diff:
  assumes "PO \<noteq> A'" and
    "PO \<noteq> B'" and
    "Col PO A' B'" and
    "Per PO A' A" and
    "Per PO B' B" and
    "A' \<noteq> B'"
  shows "A \<noteq> B"
  using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) not_col_permutation_4 per2_col_eq by blast

lemma per23_preserves_bet:
  assumes "Bet A B C" and
    "A \<noteq> B'" and "A \<noteq> C'" and
    "Col A B' C'" and
    "Per A B' B" and
    "Per A C' C"
  shows "Bet A B' C'"
proof -
  have P1: "Col A B C"
    by (simp add: assms(1) bet_col)
  show ?thesis
  proof cases
    assume P2: "B = B'"
    then have "Col A C' C"
      using P1 assms(2) assms(4) col_transitivity_1 by blast
    then have P4: "A = C' \<or> C = C'"
      by (simp add: assms(6) l8_9)
    {
      assume "A = C'"
      then have "Bet A B' C'"
        using assms(3) by auto
    }
    {
      assume "C = C'"
      then have "Bet A B' C'"
        using P2 assms(1) by auto
    }
    then show ?thesis
      using P4 assms(3) by auto
  next
    assume T1: "B \<noteq> B'"
    have T2: "A \<noteq> C"
      using assms(3) assms(6) l8_8 by auto
    have T3: "C \<noteq> C'"
      using P1 T1 assms(2) assms(3) assms(4) assms(5) col_trivial_3 colx l8_9 not_col_permutation_5 by blast
    have T3A: "A B' Perp B' B"
      using T1 assms(2) assms(5) per_perp by auto
    have T3B: "A C' Perp C' C"
      using T3 assms(3) assms(6) per_perp by auto
    have T4: "B B' Par C C'"
    proof -
      have "Coplanar A B' B C"
        using P1 ncop__ncols by blast
      moreover have "Coplanar A B' B C'"
        using assms(4) ncop__ncols by blast
      moreover have "Coplanar A B' B' C"
        using ncop_distincts by blast
      moreover have "B B' Perp A B'"
        using Perp_perm \<open>A B' Perp B' B\<close> by blast
      moreover have "C C' Perp A B'"
        using Col_cases Perp_cases T3B assms(2) assms(4) perp_col1 by blast
      ultimately show ?thesis
        using l12_9 bet__coplanar between_trivial by auto
    qed
    moreover have "Bet A B' C'"
    proof cases
      assume "B = C"
      then show ?thesis
        by (metis T1 Tarski_neutral_dimensionless.per_col_eq Tarski_neutral_dimensionless_axioms assms(4) assms(5) calculation l6_16_1 l6_6 or_bet_out out_diff1 par_id)
    next
      assume T6: "B \<noteq> C"
      have T7: "\<not> Col A B' B"
        using T1 assms(2) assms(5) l8_9 by blast
      have T8: "\<not> Col A C' C"
        using T3 assms(3) assms(6) l8_9 by blast
      have T9: "B' \<noteq> C'"
        using P1 T6 assms(2) assms(5) assms(6) col_per2__per col_permutation_1 l8_2 l8_8 by blast
      have T10: "B B' ParStrict C C' \<or> (B \<noteq> B' \<and> C \<noteq> C' \<and> Col B C C' \<and> Col B' C C')"
        using Par_def calculation by blast
      {
        assume T11: "B B' ParStrict C C'"
        then have T12: "B B' OS C' C"
          using l12_6 one_side_symmetry by blast
        have "B B' TS A C"
          using Col_cases T6 T7 assms(1) bet__ts by blast
        then have "Bet A B' C'"
          using T12 assms(4) l9_5 l9_9 not_col_distincts or_bet_out by blast
      }
      {
        assume "B \<noteq> B' \<and> C \<noteq> C' \<and> Col B C C' \<and> Col B' C C'"
        then have "Bet A B' C'"
          using Col_def T6 T8 assms(1) col_transitivity_2 by blast
      }
      then show ?thesis
        using T10 \<open>B B' ParStrict C C' \<Longrightarrow> Bet A B' C'\<close> by blast
    qed
    ultimately show ?thesis
      by (smt P1 Par_def T1 T2 assms(4) col_transitivity_2 not_col_permutation_1 par_strict_not_col_2)
  qed
qed

lemma per23_preserves_bet_inv:
  assumes "Bet A B' C'" and
    "A \<noteq> B'" and
    "Col A B C" and
    "Per A B' B" and
    "Per A C' C"
  shows "Bet A B C"
proof cases
  assume T1: "B = B'"
  then have "Col A C' C"
    using Col_def assms(1) assms(2) assms(3) col_transitivity_1 by blast
  then have T2: "A = C' \<or> C = C'"
    by (simp add: assms(5) l8_9)
  {
    assume "A = C'"
    then have "Bet A B C"
      using assms(1) assms(2) between_identity by blast
  }
  {
    assume "C = C'"
    then have "Bet A B C"
      by (simp add: T1 assms(1))
  }
  then show ?thesis
    using T2 \<open>A = C' \<Longrightarrow> Bet A B C\<close> by auto
next
  assume P1: "B \<noteq> B'"
  then have P2: "A B' Perp B' B"
    using assms(2) assms(4) per_perp by auto
  have "Per A C' C"
    by (simp add: assms(5))
  then have P2: "C' PerpAt A C' C' C"
    by (metis (mono_tags, lifting) Col_cases P1 assms(1) assms(2) assms(3) assms(4) bet_col bet_neq12__neq col_transitivity_1 l8_9 per_perp_in)
  then have P3: "A C' Perp C' C"
    using perp_in_perp by auto
  then have "C' \<noteq> C"
    using \<open>A C' Perp C' C\<close> perp_not_eq_2 by auto
  have "C' PerpAt C' A C C'"
    by (simp add: Perp_in_perm P2)
  then have "(C' A Perp C C') \<or> (C' C' Perp C C')"
    using Perp_def by blast
  have "A \<noteq> C'"
    using assms(1) assms(2) between_identity by blast
  {
    assume "C' A Perp C C'"
    have "Col A B' C'" using assms(1)
      by (simp add: Col_def)
    have "A B' Perp C' C"
      using Col_cases \<open>A C' Perp C' C\<close> \<open>Col A B' C'\<close> assms(2) perp_col by blast
    have P7: "B' B Par C' C"
    proof -
      have "Coplanar A B' B' C'"
        using ncop_distincts by blast
      moreover have "Coplanar A B' B' C"
        using ncop_distincts by auto
      moreover have "Coplanar A B' B C'"
        using Bet_perm assms(1) bet__coplanar ncoplanar_perm_20 by blast
      moreover have "Coplanar A B' B C"
        using assms(3) ncop__ncols by auto
      moreover have "B' B Perp A B'"
        by (metis P1 Perp_perm assms(2) assms(4) per_perp)
      moreover have "C' C Perp A B'"
        using Perp_cases \<open>A B' Perp C' C\<close> by auto
      ultimately show ?thesis using l12_9 by blast
    qed
    have "Bet A B C"
    proof cases
      assume "B = C"
      then show ?thesis
        by (simp add: between_trivial)
    next
      assume T1: "B \<noteq> C"
      have T2: "B' B ParStrict C' C \<or> (B' \<noteq> B \<and> C' \<noteq> C \<and> Col B' C' C \<and> Col B C' C)"
        using P7 Par_def by auto
      {
        assume T3: "B' B ParStrict C' C"
        then have "B' \<noteq> C'"
          using not_par_strict_id by auto
        have "\<exists> X. Col X B' B \<and> Col X B' C"
          using col_trivial_1 by blast
        have "B' B OS C' C"
          by (simp add: T3 l12_6)
        have "B' B TS A C'"
          by (metis Bet_cases T3 assms(1) assms(2) bet__ts l9_2 par_strict_not_col_1)
        then have T8: "B' B TS C A"
          using \<open>B' B OS C' C\<close> l9_2 l9_8_2 by blast
        then obtain T where T9: "Col T B' B \<and> Bet C T A"
          using TS_def by auto
        have "\<not> Col A C B'"
          using T8 assms(3) not_col_permutation_2 not_col_permutation_3 ts__ncol by blast
        then have "T = B"
          by (metis Col_def Col_perm T9 assms(3) colx)
        then have "Bet A B C"
          using Bet_cases T9 by auto
      }
      {
        assume "B' \<noteq> B \<and> C' \<noteq> C \<and> Col B' C' C \<and> Col B C' C"
        then have "Col A B' B"
          by (metis Col_perm T1 assms(3) l6_16_1)
        then have "A = B' \<or> B = B'"
          using assms(4) l8_9 by auto
        then have "Bet A B C"
          by (simp add: P1 assms(2))
      }
      then show ?thesis
        using T2 \<open>B' B ParStrict C' C \<Longrightarrow> Bet A B C\<close> by auto
    qed
  }
  then show ?thesis
    by (simp add: P3 perp_comm)
qed

lemma per13_preserves_bet:
  assumes "Bet A B C" and
    "B \<noteq> A'" and
    "B \<noteq> C'" and
    "Col A' B C'" and
    "Per B A' A" and
    "Per B C' C"
  shows "Bet A' B C'"
  by (smt Col_cases Tarski_neutral_dimensionless.per23_preserves_bet_inv Tarski_neutral_dimensionless_axioms assms(1) assms(4) assms(5) assms(6) bet_col between_equality between_symmetry per_distinct third_point)

lemma per13_preserves_bet_inv:
  assumes "Bet A' B C'" and
    "B \<noteq> A'" and
    "B \<noteq> C'" and
    "Col A B C" and
    "Per B A' A" and
    "Per B C' C"
  shows "Bet A B C"
proof -
  have P1: "Col A' B C'"
    by (simp add: Col_def assms(1))
  show ?thesis
  proof cases
    assume "A = A'"
    then show ?thesis
      using P1 assms(1) assms(3) assms(4) assms(6) col_transitivity_2 l8_9 not_bet_distincts by blast
  next
    assume "A \<noteq> A'"
    show ?thesis
      by (metis Col_cases P1 Tarski_neutral_dimensionless.per23_preserves_bet Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) between_equality between_symmetry third_point)
  qed
qed

lemma per3_preserves_bet1:
  assumes "Col PO A B" and
    "Bet A B C" and
    "PO \<noteq> A'" and
    "PO \<noteq> B'" and
    "PO \<noteq> C'" and
    "Per PO A' A" and
    "Per PO B' B" and
    "Per PO C' C" and
    "Col A' B' C'" and
    "Col PO A' B'"
  shows "Bet A' B' C'"
proof cases
  assume "A = B"
  then show ?thesis
    using assms(10) assms(3) assms(4) assms(6) assms(7) between_trivial2 per2_preserves_diff by blast
next
  assume P1: "A \<noteq> B"
  show ?thesis
  proof cases
    assume P2: "A = A'"
    show ?thesis
    proof cases
      assume P3: "B = B'"
      then have "Col PO C C'"
        by (metis (no_types, hide_lams) Col_def P1 P2 assms(1) assms(2) assms(9) col_transitivity_1)
      then have "C = C'"
        using assms(5) assms(8) l8_9 not_col_permutation_5 by blast
      then show ?thesis
        using P2 P3 assms(2) by blast
    next
      assume P4: "B \<noteq> B'"
      show ?thesis
      proof cases
        assume "A = B'"
        then show ?thesis
          using P2 between_trivial2 by auto
      next
        assume "A \<noteq> B'"
        have "A \<noteq> C"
          using P1 assms(2) between_identity by blast
        have P7: "\<not> Col PO B' B"
          using P4 assms(4) assms(7) l8_9 by blast
        show ?thesis
          using P2 P7 assms(1) assms(10) assms(3) col_transitivity_1 by blast
      qed
    qed
  next
    assume R1: "A \<noteq> A'"
    show ?thesis
    proof cases
      assume R2: "A' = B'"
      then show ?thesis
        by (simp add: between_trivial2)
    next
      assume R3: "A' \<noteq> B'"
      show ?thesis
      proof cases
        assume "B = C"
        have "B' = C'"
          by (metis Tarski_neutral_dimensionless.per2_col_eq Tarski_neutral_dimensionless_axioms \<open>A' \<noteq> B'\<close> \<open>B = C\<close> assms(10) assms(4) assms(5) assms(7) assms(8) assms(9) col_transitivity_2 not_col_permutation_2)
        then show ?thesis
          by (simp add: between_trivial)
      next
        assume R4: "B \<noteq> C"
        show ?thesis
        proof cases
          assume "B = B'"
          then show ?thesis
            by (metis R1 assms(1) assms(10) assms(3) assms(4) assms(6) l6_16_1 l8_9 not_col_permutation_2)
        next
          assume R5: "B \<noteq> B'"
          show ?thesis
          proof cases
            assume "A' = B"
            then show ?thesis
              using R5 assms(10) assms(4) assms(7) col_permutation_5 l8_9 by blast
          next
            assume R5A: "A' \<noteq> B"
            have R6: "C \<noteq> C'"
              by (metis P1 R1 R3 assms(1) assms(10) assms(2) assms(3) assms(5) assms(6) assms(9) bet_col col_permutation_1 col_trivial_2 l6_21 l8_9)
            have R7: "A A' Perp PO A'"
              by (metis Perp_cases R1 assms(3) assms(6) per_perp)
            have R8: "C C' Perp PO A'"
              by (smt Perp_cases R3 R6 assms(10) assms(3) assms(5) assms(8) assms(9) col2__eq col3 col_per_perp col_trivial_2 l8_2 per_perp)
            have "A A' Par C C'"
            proof -
              have "Coplanar PO A' A C"
                using P1 assms(1) assms(2) bet_col col_trivial_2 colx ncop__ncols by blast
              moreover have "Coplanar PO A' A C'"
                using R3 assms(10) assms(9) col_trivial_2 colx ncop__ncols by blast
              moreover have "Coplanar PO A' A' C"
                using ncop_distincts by blast
              moreover have "Coplanar PO A' A' C'"
                using ncop_distincts by blast
              ultimately show ?thesis using l12_9 R7 R8 by blast
            qed
            have S1: "B B' Perp PO A'"
              by (metis Col_cases Per_cases Perp_perm R5 assms(10) assms(3) assms(4) assms(7) col_per_perp)
            have "A A' Par B B'"
            proof -
              have "Coplanar PO A' A B"
                using assms(1) ncop__ncols by auto
              moreover have "Coplanar PO A' A B'"
                using assms(10) ncop__ncols by auto
              moreover have "Coplanar PO A' A' B"
                using ncop_distincts by auto
              moreover have "Coplanar PO A' A' B'"
                using ncop_distincts by auto
              moreover have "A A' Perp PO A'"
                by (simp add: R7)
              moreover have "B B' Perp PO A'"
                by (simp add: S1)
              ultimately show ?thesis
                using l12_9 by blast
            qed
            {
              assume "A A' ParStrict B B'"
              then have "A A' OS B B'"
                by (simp add: l12_6)
              have "B B' TS A C"
                using R4 \<open>A A' ParStrict B B'\<close> assms(2) bet__ts par_strict_not_col_3 by auto
              have "B B' OS A A'"
                using \<open>A A' ParStrict B B'\<close> pars__os3412 by auto
              have "B B' TS A' C"
                using \<open>B B' OS A A'\<close> \<open>B B' TS A C\<close> l9_8_2 by blast
              have "Bet A' B' C'"
              proof cases
                assume "C = C'"
                then show ?thesis
                  using R6 by auto
              next
                assume "C \<noteq> C'"
                have "C C' Perp PO A'"
                  by (simp add: R8)
                have Q2: "B B' Par C C'"
                proof -
                  have "Coplanar PO A' B C"
                    by (metis P1 assms(1) assms(2) bet_col col_transitivity_1 colx ncop__ncols not_col_permutation_5)
                  moreover have "Coplanar PO A' B C'"
                    using R3 assms(10) assms(9) col_trivial_2 colx ncop__ncols by blast
                  moreover have "Coplanar PO A' B' C"
                    by (simp add: assms(10) col__coplanar)
                  moreover have "Coplanar PO A' B' C'"
                    using assms(10) col__coplanar by auto
                  moreover have "B B' Perp PO A'"
                    by (simp add: S1)
                  moreover have "C C' Perp PO A'"
                    by (simp add: R8)
                  ultimately show ?thesis
                    using l12_9 by auto
                qed
                then have Q3: "(B B' ParStrict C C') \<or> (B \<noteq> B' \<and> C \<noteq> C' \<and> Col B C C' \<and> Col B' C C')"
                  by (simp add: Par_def)
                {
                  assume "B B' ParStrict C C'"
                  then have "B B' OS C C'"
                    using l12_6 by auto
                  then have "B B' TS C' A'"
                    using \<open>B B' TS A' C\<close> l9_2 l9_8_2 by blast
                  then obtain T where Q4: "Col T B B' \<and> Bet C' T A'"
                    using TS_def by blast
                  have "T = B'"
                  proof -
                    have "\<not> Col B B' A'"
                      using \<open>B B' OS A A'\<close> col124__nos by auto
                    moreover have "A' \<noteq> C'"
                      using \<open>B B' TS C' A'\<close> not_two_sides_id by auto
                    moreover have "Col B B' T"
                      using Col_cases Q4 by auto
                    moreover have "Col B B' B'"
                      using not_col_distincts by blast
                    moreover have "Col A' C' T"
                      by (simp add: Col_def Q4)
                    ultimately show ?thesis
                      by (meson assms(9) col_permutation_5 l6_21)
                  qed
                  then have "Bet A' B' C'"
                    using Q4 between_symmetry by blast
                }
                {
                  assume "B \<noteq> B' \<and> C \<noteq> C' \<and> Col B C C' \<and> Col B' C C'"
                  then have "Bet A' B' C'"
                    using TS_def \<open>B B' TS A C\<close> l6_16_1 not_col_permutation_2 by blast
                }
                then show ?thesis
                  using Q3 \<open>B B' ParStrict C C' \<Longrightarrow> Bet A' B' C'\<close> by blast
              qed
            }
            {
              assume R8: "A \<noteq> A' \<and> B \<noteq> B' \<and> Col A B B' \<and> Col A' B B'"
              have "A' A Perp PO A'"
                by (simp add: R7 perp_left_comm)
              have "\<not> Col A' A PO"
                using Col_cases R8 assms(3) assms(6) l8_9 by blast
              then have "Bet A' B' C'"
                using Col_perm P1 R8 assms(1) l6_16_1 by blast
            }
            then show ?thesis
              using Par_def \<open>A A' Par B B'\<close> \<open>A A' ParStrict B B' \<Longrightarrow> Bet A' B' C'\<close> by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma per3_preserves_bet2_aux:
  assumes "Col PO A C" and
    "A \<noteq> C'" and
    "Bet A B' C'" and
    "PO \<noteq> A" and
    "PO \<noteq> B'" and
    "PO \<noteq> C'" and
    "Per PO B' B" and
    "Per PO C' C" and
    "Col A B C" and
    "Col PO A C'"
  shows "Bet A B C"
proof cases
  assume "A = B"
  then show ?thesis
    by (simp add: between_trivial2)
next
  assume P1: "A \<noteq> B"
  show ?thesis
  proof cases
    assume "B = C"
    then show ?thesis
      by (simp add: between_trivial)
  next
    assume P2: "B \<noteq> C"
    have P3: "Col PO A B'"
      by (metis Col_def assms(10) assms(2) assms(3) l6_16_1)
    then have P4: "Col PO B' C'"
      using assms(10) assms(4) col_transitivity_1 by blast
    show ?thesis
    proof cases
      assume "B = B'"
      thus ?thesis
        by (metis Tarski_neutral_dimensionless.per_col_eq Tarski_neutral_dimensionless_axioms assms(1) assms(10) assms(3) assms(4) assms(6) assms(8) col_transitivity_1)
    next
      assume P5: "B \<noteq> B'"
      have P6: "C = C'"
        using assms(1) assms(10) assms(4) assms(6) assms(8) col_transitivity_1 l8_9 by blast
      then have "False"
        by (metis P3 P5 P6 Tarski_neutral_dimensionless.per_col_eq Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(4) assms(5) assms(7) assms(9) col_transitivity_1 l6_16_1 not_col_permutation_4)
      then show ?thesis by blast
    qed
  qed
qed

lemma per3_preserves_bet2:
  assumes "Col PO A C" and
    "A' \<noteq> C'" and
    "Bet A' B' C'" and
    "PO \<noteq> A'" and
    "PO \<noteq> B'" and
    "PO \<noteq> C'" and
    "Per PO A' A" and
    "Per PO B' B" and
    "Per PO C' C" and
    "Col A B C" and
    "Col PO A' C'"
  shows "Bet A B C"
proof cases
  assume "A = A'"
  then show ?thesis
    using assms(1) assms(10) assms(11) assms(2) assms(3) assms(4) assms(5) assms(6) assms(8) assms(9) per3_preserves_bet2_aux by blast
next
  assume P1: "A \<noteq> A'"
  show ?thesis
  proof cases
    assume "C = C'"
    thus ?thesis
      by (metis P1 assms(1) assms(11) assms(4) assms(6) assms(7) col_trivial_3 l6_21 l8_9 not_col_permutation_2)
  next
    assume P2: "C \<noteq> C'"
    then have P3: "PO A' Perp C C'"
      by (metis assms(11) assms(4) assms(6) assms(9) col_per_perp l8_2 not_col_permutation_1)
    have P4: "PO A' Perp A A'"
      using P1 assms(4) assms(7) per_perp perp_right_comm by auto
    have "A A' Par C C'"
    proof -
      have "Coplanar PO A' A C"
        using assms(1) ncop__ncols by blast
      moreover have "Coplanar PO A' A C'"
        by (meson assms(11) ncop__ncols)
      moreover have "Coplanar PO A' A' C"
        using ncop_distincts by blast
      moreover have "Coplanar PO A' A' C'"
        using ncop_distincts by blast
      moreover have "A A' Perp PO A'"
        using P4 Perp_cases by blast
      moreover have "C C' Perp PO A'"
        using P3 Perp_cases by auto
      ultimately show ?thesis
        using l12_9 by blast
    qed
    {
      assume P5: "A A' ParStrict C C'"
      then have P6: "A A' OS C C'"
        by (simp add: l12_6)
      have P7: "C C' OS A A'"
        by (simp add: P5 pars__os3412)

      have "Bet A B C"
      proof cases
        assume P8: "B = B'"
        then have "A' A OS B C'"
          by (metis P6 assms(10) assms(3) bet_out col123__nos col124__nos invert_one_side out_one_side)
        then have "A A' OS B C'"
          by (simp add: invert_one_side)
        then have "A A' OS B C"
          using P6 one_side_symmetry one_side_transitivity by blast
        then have P12: "A Out B C"
          using assms(10) col_one_side_out by blast
        have "C' C OS B A'"
          by (metis Col_perm P5 P7 P8 assms(10) assms(3) bet_out_1 col123__nos out_one_side par_strict_not_col_2)
        then have "C C' OS B A"
          by (meson P7 invert_one_side one_side_symmetry one_side_transitivity)
        then have "C C' OS A B"
          using one_side_symmetry by blast
        then have "C Out A B"
          using assms(10) col_one_side_out col_permutation_2 by blast
        then show ?thesis
          by (simp add: P12 out2__bet)
      next
        assume T1: "B \<noteq> B'"
        have T2: "PO A' Perp B B'"
        proof -
          have "Per PO B' B"
            by (simp add: assms(8))
          then have "B' PerpAt PO B' B' B"
            using T1 assms(5) per_perp_in by auto
          then have "B' PerpAt B' PO B B'"
            by (simp add: perp_in_comm)
          then have T4: "B' PO Perp B B' \<or> B' B' Perp B B'"
            using Perp_def by auto
          {
            assume T5: "B' PO Perp B B'"
            have "Col A' B' C'"
              by (simp add: assms(3) bet_col)
            then have "Col PO B' A'"
              using assms(11) assms(2) col2__eq col_permutation_4 col_permutation_5 by blast
            then have "PO A' Perp B B'"
              by (metis T5 assms(4) col_trivial_3 perp_col2 perp_comm)
          }
          {
            assume "B' B' Perp B B'"
            then have "PO A' Perp B B'"
              using perp_distinct by auto
          }
          then show ?thesis
            using T4 \<open>B' PO Perp B B' \<Longrightarrow> PO A' Perp B B'\<close> by linarith
        qed
        have T6: "B B' Par A A'"
        proof -
          have "Coplanar PO A' B A"
            by (metis Col_cases P7 assms(1) assms(10) col_transitivity_2 ncop__ncols os_distincts)
          moreover have "Coplanar PO A' B A'"
            using ncop_distincts by blast
          moreover have "Coplanar PO A' B' A"
          proof -
            have "(Bet PO A' C' \<or> Bet PO C' A') \<or> Bet C' PO A'"
              by (meson assms(11) third_point)
            then show ?thesis
              by (meson Bet_perm assms(3) bet__coplanar between_exchange2 l5_3 ncoplanar_perm_8)
          qed
          moreover have "Coplanar PO A' B' A'"
            using ncop_distincts by auto
          moreover have "B B' Perp PO A'"
            using Perp_cases T2 by blast
          moreover have "A A' Perp PO A'"
            using P4 Perp_cases by blast
          ultimately show ?thesis
            using l12_9 by blast
        qed
        {
          assume "B B' ParStrict A A'"
          then have "B B' OS A A'"
            by (simp add: l12_6)
          have "B B' Par C C'"
          proof -
            have "Coplanar PO A' B C"
              by (metis Col_cases P7 assms(1) assms(10) col2__eq ncop__ncols os_distincts)
            moreover have "Coplanar PO A' B C'"
              using assms(11) ncop__ncols by auto
            moreover have "Coplanar PO A' B' C"
              by (metis Out_def assms(11) assms(2) assms(3) col_trivial_2 l6_16_1 ncop__ncols not_col_permutation_1 out_col)
            moreover have "Coplanar PO A' B' C'"
              using assms(11) ncop__ncols by blast
            moreover have "B B' Perp PO A'"
              using Perp_cases T2 by blast
            moreover have "C C' Perp PO A'"
              using P3 Perp_cases by auto
            ultimately show ?thesis
              using l12_9 by blast
          qed
          {
            assume T9: "B B' ParStrict C C'"
            then have T10: "B B' OS C C'"
              by (simp add: l12_6)
            have T11: "B B' TS A' C'"
              by (metis Col_cases T10 \<open>B B' ParStrict A A'\<close> assms(3) bet__ts invert_two_sides os_distincts par_strict_not_col_4)
            have T12: "B B' TS A C'"
              using \<open>B B' OS A A'\<close> \<open>B B' TS A' C'\<close> l9_8_2 one_side_symmetry by blast
            then have T12A: "B B' TS C A"
              using T10 l9_2 l9_8_2 one_side_symmetry by blast
            then obtain T where T13: "Col T B B' \<and> Bet C T A"
              using TS_def by auto
            then have "B = T"
              by (metis Col_perm TS_def T12A assms(10) bet_col1 col_transitivity_2 col_two_sides_bet)
            then have "Bet A B C"
              using Bet_perm T13 by blast
          }
          {
            assume "B \<noteq> B' \<and> C \<noteq> C' \<and> Col B C C' \<and> Col B' C C'"
            then have "Bet A B C"
              by (metis Col_cases P5 assms(10) col3 col_trivial_2 not_bet_distincts par_strict_not_col_3)
          }
          then have "Bet A B C"
            using Par_def \<open>B B' Par C C'\<close> \<open>B B' ParStrict C C' \<Longrightarrow> Bet A B C\<close> by auto
        }
        {
          assume "B \<noteq> B' \<and> A \<noteq> A' \<and> Col B A A' \<and> Col B' A A'"
          then have "Bet A B C"
            by (smt P6 assms(10) col123__nos l6_16_1 not_bet_distincts not_col_permutation_1)
        }
        then show ?thesis
          using Par_def T6 \<open>B B' ParStrict A A' \<Longrightarrow> Bet A B C\<close> by auto
      qed
    }
    {
      assume "A \<noteq> A' \<and> C \<noteq> C' \<and> Col A C C' \<and> Col A' C C'"
      then have "Bet A B C"
        by (metis Col_perm P3 Par_def assms(11) assms(2) assms(4) col_transitivity_1 perp_not_par)
    }
    thus ?thesis
      using Par_def \<open>A A' Par C C'\<close> \<open>A A' ParStrict C C' \<Longrightarrow> Bet A B C\<close> by auto
  qed
qed

lemma symmetry_preserves_per:
  assumes "Per B P A" and
    "B Midpoint A A'" and
    "B Midpoint P P'"
  shows "Per B P' A'"
proof -
  obtain C where P1: "P Midpoint A C"
    using symmetric_point_construction by blast
  obtain C' where P2: "B Midpoint C C'"
    using symmetric_point_construction by blast
  have P3: "P' Midpoint A' C'"
    using P1 P2 assms(2) assms(3) symmetry_preserves_midpoint by blast
  have "Cong B A' B C'"
    by (meson P1 P2 assms(1) assms(2) l7_16 l7_3_2 per_double_cong)
  then show ?thesis
    using P3 Per_def by blast
qed

lemma l13_1_aux:
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows
    "\<exists> X Y. (R PerpAt X Y A B \<and> X Y Perp P Q \<and> Coplanar A B C X \<and> Coplanar A B C Y)"
proof -
  have P1: "Q \<noteq> C"
    using assms(1) assms(3) midpoint_not_midpoint not_col_distincts by blast
  have P2: "P \<noteq> C"
    using assms(1) assms(2) is_midpoint_id_2 not_col_distincts by blast
  then have "Q \<noteq> R"
    using assms(2) assms(3) assms(4) l7_3 symmetric_point_uniqueness by blast
  have "R \<noteq> B"
    using assms(1) assms(4) midpoint_not_midpoint not_col_distincts by blast
  {
    assume V1: "Col P Q C"
    have V2: "Col B P C"
      by (simp add: assms(2) bet_col midpoint_bet)
    have V3: "Col A Q C"
      by (simp add: assms(3) bet_col midpoint_bet)
    have "Col A R B"
      using assms(4) midpoint_col not_col_permutation_4 by blast
    then have "Col A B C" using V1 V2 V3
      by (metis P1 P2 col2__eq col_permutation_5)
    then have "False"
      using assms(1) by auto
  }
  then have P2A: "\<not> Col P Q C" by auto
  then obtain C' where P3: "Col P Q C' \<and> P Q Perp C C'"
    using l8_18_existence by blast
  obtain A' where P4: "Q Midpoint C' A'"
    using symmetric_point_construction by auto
  obtain B' where P5: "P Midpoint C' B'"
    using symmetric_point_construction by auto
  have P6: "Cong C C' B B'"
    using Mid_cases P5 assms(2) l7_13 by blast
  have P7: "Cong C C' A A'"
    using P4 assms(3) l7_13 l7_2 by blast
  have P8: "Per P B' B"
  proof cases
    assume "P = C'"
    then show ?thesis
      using P5 Per_cases is_midpoint_id l8_5 by blast
  next
    assume "P \<noteq> C'"
    then have "P C' Perp C C'"
      using P3 perp_col by blast
    then have "Per P C' C"
      using Perp_perm perp_per_2 by blast
    then show ?thesis
      using symmetry_preserves_per Mid_perm P5 assms(2) by blast
  qed
  have P8A: "Per Q A' A"
  proof cases
    assume "Q = C'"
    then show ?thesis
      using P4 Per_cases is_midpoint_id l8_5 by blast
  next
    assume "Q \<noteq> C'"
    then have "C' Q Perp C C'"
      using P3 col_trivial_2 perp_col2 by auto
    then have "Per Q C' C"
      by (simp add: perp_per_1)
    then show ?thesis
      by (meson Mid_cases P4 assms(3) l7_3_2 midpoint_preserves_per)
  qed
  have P9: "Col A' C' Q"
    using P4 midpoint_col not_col_permutation_3 by blast
  have P10: "Col B' C' P"
    using P5 midpoint_col not_col_permutation_3 by blast
  have P11: "P \<noteq> Q"
    using P2A col_trivial_1 by auto
  then have P12: "A' \<noteq> B'"
    using P4 P5 l7_17 by blast
  have P13: "Col A' B' P"
    by (metis P10 P3 P4 P5 P9 col2__eq col_permutation_5 midpoint_distinct_1 not_col_distincts)
  have P14: "Col A' B' Q"
    by (smt P10 P3 P4 P5 P9 col3 col_permutation_1 midpoint_distinct_1 not_col_distincts)
  have P15: "Col A' B' C'"
    using P11 P13 P14 P3 colx by blast
  have P16: "C \<noteq> C'"
    using P2A P3 by blast
  then have P17: "A \<noteq> A'"
    using P7 cong_diff by blast
  have P18: "B \<noteq> B'"
    using P16 P6 cong_diff by blast
  have P19: "Per P A' A"
  proof cases
    assume P20: "A' = Q"
    then have "A' P Perp C A'"
      by (metis P3 P4 Perp_cases midpoint_not_midpoint)
    then have "Per P A' C"
      by (simp add: perp_per_1)
    then show ?thesis
      using P20 assms(3) l7_2 l8_4 by blast
  next
    assume "A' \<noteq> Q"
    then show ?thesis
      by (meson P12 P13 P14 P8A col_transitivity_1 l8_2 per_col)
  qed
  have "Per Q B' B"
  proof cases
    assume P21: "P = B'"
    then have P22: "C' = B'"
      using P5 is_midpoint_id_2 by auto
    then have "Per Q B' C"
      using P3 P21 perp_per_1 by auto
    thus ?thesis
      by (metis Col_perm P16 P21 P22 assms(2) midpoint_col per_col)
  next
    assume P23: "P \<noteq> B'"
    have "Col B' P Q"
      using P12 P13 P14 col_transitivity_2 by blast
    then have "Per B B' Q"
      using P8 P23 l8_2 l8_3 by blast
    thus ?thesis
      using Per_perm by blast
  qed
  then have P24: "Per A' B' B"
    using P11 P13 P14 P8 l8_3 not_col_permutation_2 by blast
  have P25: "Per A A' B'"
    using P11 P13 P14 P19 P8A l8_2 l8_3 not_col_permutation_5 by blast
  then have "Per B' A' A"
    using Per_perm by blast
  then have "\<not> Col B' A' A"
    using P12 P17 P25 per_not_col by auto
  then have P26: "\<not> Col A' B' A"
    using Col_cases by auto
  have "\<not> Col A' B' B"
    using P12 P18 P24 l8_9 by auto
  obtain X where P28: "X Midpoint A' B'"
    using midpoint_existence by blast
  then have P28A: "Col A' B' X"
    using midpoint_col not_col_permutation_2 by blast
  then have "\<exists> Q. A' B' Perp Q X \<and> A' B' OS A Q"
    by (simp add: P26 l10_15)
  then obtain y where P29: "A' B' Perp y X \<and> A' B' OS A y" by blast
  then obtain B'' where P30: "(X y Perp A B'' \<or> A = B'') \<and> (\<exists> M. (Col X y M \<and> M Midpoint A B''))"
    using ex_sym by blast
  then have P31: "B'' A ReflectL X y"
    using P30 ReflectL_def by blast
  have P32: "X \<noteq> y"
    using P29 P28A col124__nos by blast
  then have "X \<noteq> y \<and> B'' A ReflectL X y \<or> X = y \<and> X Midpoint A B''"
    using P31 by auto
  then have P33: "B'' A Reflect X y"
    by (simp add: Reflect_def)
  have P33A: "X \<noteq> y \<and> A' B' ReflectL X y"
    using P28 P29 Perp_cases ReflectL_def P32 col_trivial_3 l10_4_spec by blast
  then have P34: "A' B' Reflect X y"
    using Reflect_def by blast
  have P34A: "A B'' Reflect X y"
    using P33 l10_4 by blast
  then have P35: "Cong B'' B' A A'"
    using P34 l10_10 by auto
  have "Per A' B' B''"
  proof -
    have R1: "X \<noteq> y \<and> A B'' ReflectL X y \<or> X = y \<and> X Midpoint B'' A"
      by (simp add: P31 P32 l10_4_spec)
    have R2: "X \<noteq> y \<and> A' B' ReflectL X y \<or> X = y \<and> X Midpoint B' A'"
      using P33A by linarith
    {
      assume "X \<noteq> y \<and> A B'' ReflectL X y \<and> X \<noteq> y \<and> A' B' ReflectL X y"
      then have "Per A' B' B''"
        using \<open>Per B' A' A\<close> image_spec_preserves_per l10_4_spec by blast
    }
    {
      assume "X \<noteq> y \<and> A B'' ReflectL X y \<and> X = y \<and> X Midpoint B' A'"
      then have "Per A' B' B''" by blast
    }
    {
      assume "X = y \<and> X Midpoint B'' A \<and> X \<noteq> y \<and> A' B' ReflectL X y"
      then have "Per A' B' B''" by blast
    }
    {
      assume "X = y \<and> X Midpoint B'' A \<and> X = y \<and> X Midpoint B' A'"
      then have "Per A' B' B''"
        using P32 by blast
    }
    then show ?thesis using R1 R2
      using \<open>X \<noteq> y \<and> A B'' ReflectL X y \<and> X \<noteq> y \<and> A' B' ReflectL X y \<Longrightarrow> Per A' B' B''\<close> by auto
  qed
  have "A' B' OS A B''"
  proof -
    {
      assume S1: "X y Perp A B''"
      have "Coplanar A y A' X"
        by (metis P28A P29 col_one_side coplanar_perm_16 ncop_distincts os__coplanar)
      have "Coplanar A y B' X"
        by (smt P12 P28A P29 col2_cop__cop col_transitivity_1 ncoplanar_perm_22 not_col_permutation_5 os__coplanar)
      have S2: "\<not> Col A X y"
        using Col_perm P34A S1 local.image_id perp_distinct by blast

      have "A' B' Par A B''"
      proof -
        have "Coplanar X y A' A"
          using \<open>Coplanar A y A' X\<close> ncoplanar_perm_21 by blast
        moreover have "Coplanar X y A' B''"
        proof -
          have "Coplanar A X y A'"
            using \<open>Coplanar X y A' A\<close> ncoplanar_perm_9 by blast
          moreover  have "Coplanar A X y B''"
            using Coplanar_def S1 perp_inter_exists by blast
          ultimately show ?thesis
            using S2 coplanar_trans_1 by auto
        qed
        moreover have "Coplanar X y B' A"
        proof -
          have "\<not> Col A X y"
            by (simp add: S2)
          moreover have "Coplanar A X y B'"
            using \<open>Coplanar A y B' X\<close> ncoplanar_perm_3 by blast
          moreover have "Coplanar A X y B''"
            using Coplanar_def S1 perp_inter_exists by blast
          ultimately show ?thesis
            using ncoplanar_perm_18 by blast
        qed
        moreover have "Coplanar X y B' B''"
        proof -
          have "\<not> Col A X y"
            by (simp add: S2)
          moreover have "Coplanar A X y B'"
            using \<open>Coplanar X y B' A\<close> ncoplanar_perm_9 by blast
          moreover have "Coplanar A X y B''"
            using Coplanar_def S1 perp_inter_exists by blast
          ultimately show ?thesis
            using coplanar_trans_1 by blast
        qed
        ultimately show ?thesis using l12_9
          using P29 Perp_cases S1 by blast
      qed
      have "A' B' OS A B''"
      proof -
        {
          assume "A' B' ParStrict A B''"
          have "A' B' OS A B''" using l12_6
            using \<open>A' B' ParStrict A B''\<close> by blast
        }
        {
          assume "A' \<noteq> B' \<and> A \<noteq> B'' \<and> Col A' A B'' \<and> Col B' A B''"
          have "A' B' OS A B''"
            using P26 \<open>A' B' Par A B''\<close> \<open>A' B' ParStrict A B'' \<Longrightarrow> A' B' OS A B''\<close> col_trivial_3 par_not_col_strict by blast
        }
        then show ?thesis
          using Par_def \<open>A' B' Par A B''\<close> \<open>A' B' ParStrict A B'' \<Longrightarrow> A' B' OS A B''\<close> by auto
      qed
    }
    {
      assume "A = B''"
      then have "A' B' OS A B''"
        using P12 P25 \<open>Per A' B' B''\<close> l8_2 l8_7 by blast
    }
    then show ?thesis
      using P30 \<open>X y Perp A B'' \<Longrightarrow> A' B' OS A B''\<close> by blast
  qed
  have "A' B' OS A B"
  proof -
    have "A' B' TS A C"
    proof -
      have "\<not> Col A A' B'"
        using Col_perm \<open>\<not> Col B' A' A\<close> by blast
      moreover have "\<not> Col C A' B'"
        by (metis P13 P14 P2A \<open>\<not> Col B' A' A\<close> col3 not_col_distincts not_col_permutation_3 not_col_permutation_4)
      moreover have "\<exists> T. Col T A' B' \<and> Bet A T C"
        using P14 assms(3) midpoint_bet not_col_permutation_1 by blast
      ultimately show ?thesis
        by (simp add: TS_def)
    qed
    moreover have "A' B' TS B C"
      by (metis Col_cases P13 TS_def \<open>\<not> Col A' B' B\<close> assms(2) calculation midpoint_bet)
    ultimately show ?thesis
      using OS_def by blast
  qed
  have "Col B B'' B'"
  proof -
    have "Coplanar A' B B'' B'"
    proof -
      have "Coplanar A' B' B B''"
      proof -
        have "\<not> Col A A' B'"
          using Col_perm \<open>\<not> Col B' A' A\<close> by blast
        moreover have "Coplanar A A' B' B"
          using \<open>A' B' OS A B\<close> ncoplanar_perm_8 os__coplanar by blast
        moreover have "Coplanar A A' B' B''"
          using \<open>A' B' OS A B''\<close> ncoplanar_perm_8 os__coplanar by blast
        ultimately show ?thesis
          using coplanar_trans_1 by blast
      qed
      then show ?thesis
        using ncoplanar_perm_4 by blast
    qed
    moreover have "A' \<noteq> B'"
      by (simp add: P12)
    moreover have "Per B B' A'"
      by (simp add: P24 l8_2)
    moreover have "Per B'' B' A'"
      using Per_cases \<open>Per A' B' B''\<close> by auto
    ultimately show ?thesis
      using cop_per2__col by blast
  qed
  have "Cong B B' A A'"
    using P6 P7 cong_inner_transitivity by blast
  have "B = B'' \<or> B' Midpoint B B''"
  proof -
    have "Col B B' B''"
      using \<open>Col B B'' B'\<close> not_col_permutation_5 by blast
    moreover have "Cong B' B B' B''"
      by (metis Cong_perm P35 P6 P7 cong_inner_transitivity)
    ultimately show ?thesis
      using l7_20 by simp
  qed
  {
    assume "B = B''"
    then obtain M where S1: "Col X y M \<and> M Midpoint A B"
      using P30 by blast
    then have "R = M"
      using assms(4) l7_17 by auto
    have "A \<noteq> B"
      using assms(1) col_trivial_1 by auto
    have "Col R A B"
      by (simp add: assms(4) midpoint_col)
    have "X \<noteq> R"
      using Midpoint_def P28 \<open>A' B' OS A B''\<close> \<open>B = B''\<close> assms(4) midpoint_col one_side_chara by auto
    then have "\<exists> X Y. (R PerpAt X Y A B \<and> X Y Perp P Q \<and> Coplanar A B C X \<and> Coplanar A B C Y)"
    proof -
      have "R PerpAt R X A B"
      proof -
        have "R X Perp A B"
          using P30 S1 \<open>A \<noteq> B\<close> \<open>B = B''\<close> \<open>R = M\<close> \<open>X \<noteq> R\<close> perp_col perp_left_comm by blast
        then show ?thesis
          using \<open>Col R A B\<close> l8_14_2_1b_bis not_col_distincts by blast
      qed
      moreover have "R X Perp P Q"
      proof -
        have "X R Perp P Q"
        proof -
          have "X y Perp P Q"
          proof -
            have "P Q Perp X y"
              using P11 P13 P14 P29 P33A col_trivial_2 col_trivial_3 perp_col4 by blast
            then show ?thesis
              using Perp_perm by blast
          qed
          moreover have "Col X y R"
            by (simp add: S1 \<open>R = M\<close>)
          ultimately show ?thesis
            using \<open>X \<noteq> R\<close> perp_col by blast
        qed
        then show ?thesis
          using Perp_perm by blast
      qed
      moreover have "Coplanar A B C R"
        using \<open>Col R A B\<close> ncop__ncols not_col_permutation_2 by blast
      moreover have "Coplanar A B C X"
      proof -
        have "Col P Q X"
          using P12 P13 P14 P28A col3 by blast
        moreover  have "\<not> Col P Q C"
          by (simp add: P2A)
        moreover have "Coplanar P Q C A"
          using assms(3) coplanar_perm_19 midpoint__coplanar by blast
        moreover have "Coplanar P Q C B"
          using assms(2) midpoint_col ncop__ncols not_col_permutation_5 by blast
        moreover have "Coplanar P Q C C"
          using ncop_distincts by auto
        moreover have "Coplanar P Q C X"
          using calculation(1) ncop__ncols by blast
        ultimately show ?thesis
          using coplanar_pseudo_trans by blast
      qed
      ultimately show ?thesis by blast
    qed
  }
  {
    assume "B' Midpoint B B''"
    have "A' B' TS B B''"
    proof -
      have "\<not> Col B A' B'"
        using Col_perm \<open>\<not> Col A' B' B\<close> by blast
      moreover have "\<not> Col B'' A' B'"
        using \<open>A' B' OS A B''\<close> col124__nos not_col_permutation_2 by blast
      moreover have "\<exists> T. Col T A' B' \<and> Bet B T B''"
        using \<open>B' Midpoint B B''\<close> col_trivial_3 midpoint_bet by blast
      ultimately show ?thesis
        by (simp add: TS_def)
    qed
    have "A' B' OS B B''"
      using \<open>A' B' OS A B''\<close> \<open>A' B' OS A B\<close> one_side_symmetry one_side_transitivity by blast
    have "\<not> A' B' OS B B''"
      using \<open>A' B' TS B B''\<close> l9_9_bis by blast
    then have "False"
      by (simp add: \<open>A' B' OS B B''\<close>)
    then have "\<exists> X Y. (R PerpAt X Y A B \<and> X Y Perp P Q \<and> Coplanar A B C X \<and> Coplanar A B C Y)"
      by auto
  }
  then show ?thesis
    using \<open>B = B'' \<Longrightarrow> \<exists>X Y. R PerpAt X Y A B \<and> X Y Perp P Q \<and> Coplanar A B C X \<and> Coplanar A B C Y\<close> \<open>B = B'' \<or> B' Midpoint B B''\<close> by blast
qed

lemma l13_1:
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C" and
    "R Midpoint A B"
  shows
    "\<exists> X Y.(R PerpAt X Y A B \<and> X Y Perp P Q)"
proof -
  obtain X Y where "R PerpAt X Y A B \<and> X Y Perp P Q \<and> Coplanar A B C X \<and> Coplanar A B C Y"
    using l13_1_aux assms(1) assms(2) assms(3) assms(4) by blast
  then show ?thesis by blast
qed

lemma per_lt:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "Per A B C"
  shows "A B Lt A C \<and> C B Lt A C"
proof -
  have "B A Lt A C \<and> B C Lt A C"
    using assms(1) assms(2) assms(3) l11_46 by auto
  then show ?thesis
    using lt_left_comm by blast
qed

lemma cong_perp_conga:
  assumes "Cong A B C B" and
    "A C Perp B P"
  shows "A B P CongA C B P \<and> B P TS A C"
proof -
  have P1: "A \<noteq> C"
    using assms(2) perp_distinct by auto
  have P2: "B \<noteq> P"
    using assms(2) perp_distinct by auto
  have P3: "A \<noteq> B"
    by (metis P1 assms(1) cong_diff_3)
  have P4: "C \<noteq> B"
    using P3 assms(1) cong_diff by blast
  show ?thesis
  proof cases
    assume P5: "Col A B C"
    have P6: "\<not> Col B A P"
      using P3 P5 assms(2) col_transitivity_1 not_col_permutation_4 not_col_permutation_5 perp_not_col2 by blast
    have "Per P B A"
      using P3 P5 Perp_perm assms(2) not_col_permutation_5 perp_col1 perp_per_1 by blast
    then have P8: "Per A B P"
      using Per_cases by blast
    have "Per P B C"
      using P3 P5 P8 col_per2__per l8_2 l8_5 by blast
    then have P10: "Per C B P"
      using Per_perm by blast
    show ?thesis
    proof -
      have "A B P CongA C B P"
        using P2 P3 P4 P8 P10 l11_16 by auto
      moreover have "B P TS A C"
        by (metis Col_cases P1 P5 P6 assms(1) bet__ts between_cong not_cong_2143 not_cong_4321 third_point)
      ultimately show ?thesis
        by simp
    qed
  next
    assume T1: "\<not> Col A B C"
    obtain T where T2: "T PerpAt A C B P"
      using assms(2) perp_inter_perp_in by blast
    then have T3: "Col A C T \<and> Col B P T"
      using perp_in_col by auto
    have T4: "B \<noteq> T"
      using Col_perm T1 T3 by blast
    have T5: "B T Perp A C"
      using Perp_cases T3 T4 assms(2) perp_col1 by blast
    {
      assume T5_1: "A = T"
      have "B A Lt B C \<and> C A Lt B C"
      proof -
        have "B \<noteq> A"
          using P3 by auto
        moreover have "C \<noteq> A"
          using P1 by auto
        moreover have "Per B A C"
          using T5 T5_1 perp_comm perp_per_1 by blast
        ultimately show ?thesis
          by (simp add: per_lt)
      qed
      then have "False"
        using Cong_perm assms(1) cong__nlt by blast
    }
    then have T6: "A \<noteq> T" by auto
    {
      assume T6_1: "C = T"
      have "B C Lt B A \<and> A C Lt B A"
      proof -
        have "B \<noteq> C"
          using P4 by auto
        moreover have "A \<noteq> C"
          by (simp add: P1)
        moreover have "Per B C A"
          using T5 T6_1 perp_left_comm perp_per_1 by blast
        ultimately show ?thesis
          by (simp add: per_lt)
      qed
      then have "False"
        using Cong_perm assms(1) cong__nlt by blast
    }
    then have T7: "C \<noteq> T" by auto
    have T8: "T PerpAt B T T A"
      by (metis Perp_in_cases T2 T3 T4 T6 perp_in_col_perp_in)
    have T9: "T PerpAt B T T C"
      by (metis Col_cases T3 T7 T8 perp_in_col_perp_in)
    have T10: "Cong T A T C \<and> T A B CongA T C B \<and> T B A CongA T B C"
    proof -
      have "A T B CongA C T B"
      proof -
        have "Per A T B"
          using T2 perp_in_per_1 by auto
        moreover have "Per C T B"
          using T2 perp_in_per_3 by auto
        ultimately show ?thesis
          by (simp add: T4 T6 T7 l11_16)
      qed
      moreover have "Cong A B C B"
        by (simp add: assms(1))
      moreover have "Cong T B T B"
        by (simp add: cong_reflexivity)
      moreover have "T B Le A B"
      proof -
        have "Per B T A"
          using T8 perp_in_per by auto
        then have "B T Lt B A \<and> A T Lt B A"
          using T4 T6 per_lt by blast
        then show ?thesis
          using Le_cases Lt_def by blast
      qed
      ultimately show ?thesis
        using l11_52 by blast
    qed
    show ?thesis
    proof -
      have T11: "A B P CongA C B P"
      proof -
        have "P B A CongA P B C"
          using Col_cases P2 T10 T3 col_conga__conga by blast
        thus ?thesis
          using conga_comm by blast
      qed
      moreover have "B P TS A C"
      proof -
        have T12: "A = C \<or> T Midpoint A C"
          using T10 T3 l7_20_bis not_col_permutation_5 by blast
        {
          assume "T Midpoint A C"
          then have "B P TS A C"
            by (smt Col_perm P2 T1 T3 \<open>A = T \<Longrightarrow> False\<close> \<open>C = T \<Longrightarrow> False\<close> col2__eq l9_18 midpoint_bet)
        }
        then show ?thesis
          using P1 T12 by auto
      qed
      ultimately show ?thesis
        by simp
    qed
  qed
qed

lemma perp_per_bet:
  assumes "\<not> Col A B C" and
    (*  "Col A P C" and *)
    "Per A B C" and
    "P PerpAt P B A C"
  shows "Bet A P C"
proof -
  have "A \<noteq> C"
    using assms(1) col_trivial_3 by auto
  then show ?thesis
    using assms(2) assms(3) l11_47 perp_in_left_comm by blast
qed

lemma ts_per_per_ts:
  assumes "A B TS C D" and
    "Per B C A" and
    "Per B D A"
  shows "C D TS A B"
proof -
  have P1: "\<not> Col C A B"
    using TS_def assms(1) by blast
  have P2: "A \<noteq> B"
    using P1 col_trivial_2 by auto
  obtain P where P3: "Col P A B \<and> Bet C P D"
    using TS_def assms(1) by blast
  have P4: "C \<noteq> D"
    using assms(1) not_two_sides_id by auto
  show ?thesis
  proof -
    {
      assume "Col A C D"
      then have "C = D"
        by (metis assms(1) assms(2) assms(3) col_per2_cases col_permutation_2 not_col_distincts ts_distincts)
      then have "False"
        using P4 by auto
    }
    then have "\<not> Col A C D" by auto
    moreover have "\<not> Col B C D"
      using assms(1) assms(2) assms(3) per2_preserves_diff ts_distincts by blast
    moreover have "\<exists> T. Col T C D \<and> Bet A T B"
    proof -
      have "Col P C D"
        using Col_def Col_perm P3 by blast
      moreover have "Bet A P B"
      proof -
        have "\<exists> X. Col A B X \<and> A B Perp C X"
          using Col_perm P1 l8_18_existence by blast
        then obtain C' where P5: "Col A B C' \<and> A B Perp C C'" by blast
        have "\<exists> X. Col A B X \<and> A B Perp D X"
          by (metis (no_types) Col_perm TS_def assms(1) l8_18_existence)
        then obtain D' where P6: "Col A B D' \<and> A B Perp D D'" by blast
        have P7: "A \<noteq> C'"
          using P5 assms(2) l8_7 perp_not_eq_2 perp_per_1 by blast
        have P8: "A \<noteq> D'"
          using P6 assms(3) l8_7 perp_not_eq_2 perp_per_1 by blast
        have P9: "Bet A C' B"
        proof -
          have "\<not> Col A C B"
            using Col_cases P1 by blast
          moreover have "Per A C B"
            by (simp add: assms(2) l8_2)
          moreover have "C' PerpAt C' C A B"
            using P5 Perp_in_perm l8_15_1 by blast
          ultimately show ?thesis
            using perp_per_bet by blast
        qed
        have P10: "Bet A D' B"
        proof -
          have "\<not> Col A D B"
            using P6 col_permutation_5 perp_not_col2 by blast
          moreover have "Per A D B"
            by (simp add: assms(3) l8_2)
          moreover have "D' PerpAt D' D A B"
            using P6 Perp_in_perm l8_15_1 by blast
          ultimately show ?thesis
            using perp_per_bet by blast
        qed
        show ?thesis
        proof cases
          assume "P = C'"
          then show ?thesis
            by (simp add: P9)
        next
          assume "P \<noteq> C'"
          show ?thesis
          proof cases
            assume "P = D'"
            then show ?thesis
              by (simp add: P10)
          next
            assume "P \<noteq> D'"
            show ?thesis
            proof cases
              assume "A = P"
              then show ?thesis
                by (simp add: between_trivial2)
            next
              assume "A \<noteq> P"
              show ?thesis
              proof cases
                assume "B = P"
                then show ?thesis
                  using between_trivial by auto
              next
                assume "B \<noteq> P"
                have "Bet C' P D'"
                proof -
                  have "Bet C P D"
                    by (simp add: P3)
                  moreover have "P \<noteq> C'"
                    by (simp add: \<open>P \<noteq> C'\<close>)
                  moreover have "P \<noteq> D'"
                    by (simp add: \<open>P \<noteq> D'\<close>)
                  moreover have "Col C' P D'"
                    by (meson P2 P3 P5 P6 col3 col_permutation_2)
                  moreover have "Per P C' C"
                    using P3 P5 l8_16_1 l8_2 not_col_permutation_3 not_col_permutation_4 by blast
                  moreover have "Per P D' D"
                    by (metis P3 P6 calculation(3) not_col_permutation_2 perp_col2 perp_per_1)
                  ultimately show ?thesis
                    using per13_preserves_bet by blast
                qed
                then show ?thesis
                  using P10 P9 bet3__bet by blast
              qed
            qed
          qed
        qed
      qed
      ultimately show ?thesis
        by auto
    qed
    ultimately show ?thesis
      by (simp add: TS_def)
  qed
qed

lemma l13_2_1:
  assumes "A B TS C D" and
    "Per B C A" and
    "Per B D A" and
    "Col C D E" and
    "A E Perp C D" and
    "C A B CongA D A B"
  shows "B A C CongA D A E \<and> B A D CongA C A E \<and> Bet C E D"
proof -
  have P1: "\<not> Col C A B"
    using TS_def assms(1) by auto
  have P2: "A \<noteq> C"
    using P1 col_trivial_1 by blast
  have P3: "A \<noteq> B"
    using P1 col_trivial_2 by auto
  have P4: "A \<noteq> D"
    using assms(1) ts_distincts by auto
  have P5: "Cong B C B D \<and> Cong A C A D \<and> C B A CongA D B A"
  proof -
    have "\<not> Col B A C"
      by (simp add: P1 not_col_permutation_3)
    moreover have "A C B CongA A D B"
      using assms(1) assms(2) assms(3) l11_16 l8_2 ts_distincts by blast
    moreover have "B A C CongA B A D"
      by (simp add: assms(6) conga_comm)
    moreover have "Cong B A B A"
      by (simp add: cong_reflexivity)
    ultimately show ?thesis
      using l11_50_2 by blast
  qed
  then have P6: "C D Perp A B"
    using assms(1) assms(6) cong_conga_perp not_cong_2143 by blast
  then have P7: "C D TS A B"
    by (simp add: assms(1) assms(2) assms(3) ts_per_per_ts)
  obtain T1 where P8: "Col T1 C D \<and> Bet A T1 B"
    using P7 TS_def by auto
  obtain T where P9: "Col T A B \<and> Bet C T D"
    using TS_def assms(1) by blast
  have P10: "T1 = T"
    by (metis (no_types) Col_def P1 P3 P8 P9 between_equality_2 between_trivial2 l6_16_1)
  have P11: "T = E"
  proof -
    have "\<not> Col A B C"
      using Col_perm P1 by blast
    moreover have "C \<noteq> D"
      using assms(1) ts_distincts by blast
    moreover have "Col A B T"
      using Col_cases P9 by auto
    moreover have "Col A B E"
      by (metis P7 Perp_cases P6 assms(1) assms(5) col_perp2_ncol_col col_trivial_3 not_col_permutation_3 one_side_not_col123 os_ts1324__os ts_ts_os)
    moreover have "Col C D T"
      using NCol_cases P9 bet_col by blast
    moreover have "Col C D E"
      by (simp add: assms(4))
    ultimately show ?thesis
      using l6_21 by blast
  qed
  show ?thesis
  proof -
    have "B A C CongA D A E"
    proof -
      have "A Out C C"
        using P2 out_trivial by auto
      moreover have "A Out B B"
        using P3 out_trivial by auto
      moreover have "A Out D D"
        using P4 out_trivial by auto
      moreover have "A Out E B"
        by (metis P10 P11 P7 P8 TS_def bet_out)
      ultimately show ?thesis
        by (meson assms(6) conga_comm conga_right_comm l11_10)
    qed
    moreover have "B A D CongA C A E"
    proof -
      have "C A E CongA D A B"
        by (meson Perp_cases P5 assms(5) assms(6) calculation cong_perp_conga conga_right_comm conga_trans not_cong_2143 not_conga_sym)
      then have "C A E CongA B A D"
        by (simp add: conga_right_comm)
      then show ?thesis
        by (simp add: conga_sym)
    qed
    moreover have "Bet C E D"
      using P11 P9 by auto
    ultimately show ?thesis by simp
  qed
qed

lemma triangle_mid_par:
  assumes "\<not> Col A B C" and
    "P Midpoint B C" and
    "Q Midpoint A C"
  shows "A B ParStrict Q P"
proof -
  obtain R where P1: "R Midpoint A B"
    using midpoint_existence by auto
  then obtain X Y where P2: "R PerpAt X Y A B \<and> X Y Perp P Q \<and> Coplanar A B C X \<and> Coplanar A B C Y"
    using l13_1_aux assms(1) assms(2) assms(3) by blast
  have P3: "Coplanar X Y A P \<and> Coplanar X Y A Q \<and> Coplanar X Y B P \<and> Coplanar X Y B Q"
  proof -
    have "Coplanar A B C A"
      using ncop_distincts by auto
    moreover have "Coplanar A B C B"
      using ncop_distincts by auto
    moreover have "Coplanar A B C P"
      using assms(2) coplanar_perm_21 midpoint__coplanar by blast
    moreover have "Coplanar A B C Q"
      using assms(3) coplanar_perm_11 midpoint__coplanar by blast
    ultimately show ?thesis
      using P2 assms(1) coplanar_pseudo_trans by blast
  qed
  have P4: "Col X Y R \<and> Col A B R"
    using P2 perp_in_col by blast
  have P5: "R Y Perp A B \<or> X R Perp A B"
    using P2 perp_in_perp_bis by auto
  have P6: "Col A R B"
    using Col_perm P4 by blast
  have P7: "X \<noteq> Y"
    using P2 perp_not_eq_1 by auto
  {
    assume P8: "R Y Perp A B"
    have "Col Y R X"
      using P4 not_col_permutation_2 by blast
    then have "Y X Perp A B"
      using P2 Perp_cases perp_in_perp by blast
    then have P10: "X Y Perp A B"
      using Perp_cases by blast
    have "A B Par P Q"
    proof -
      have "Coplanar X Y A P"
        by (simp add: P3)
      moreover have "Coplanar X Y A Q"
        by (simp add: P3)
      moreover have "Coplanar X Y B P"
        by (simp add: P3)
      moreover have "Coplanar X Y B Q"
        by (simp add: P3)
      moreover have "A B Perp X Y"
        using P10 Perp_cases by auto
      moreover have "P Q Perp X Y"
        using P2 Perp_cases by auto
      ultimately show ?thesis
        using l12_9 by blast
    qed
    {
      assume "A B ParStrict P Q"
      then have "A B ParStrict Q P"
        using Par_strict_perm by blast
    }
    {
      assume "A \<noteq> B \<and> P \<noteq> Q \<and> Col A P Q \<and> Col B P Q"
      then have "Col A B P"
        using l6_16_1 not_col_permutation_1 by blast
      then have "P = B"
        by (metis Col_perm assms(1) assms(2) l6_16_1 midpoint_col)
      then have "A B ParStrict Q P"
        using assms(1) assms(2) col_trivial_2 is_midpoint_id by blast
    }
    then have "A B ParStrict Q P"
      using Par_def \<open>A B Par P Q\<close> \<open>A B ParStrict P Q \<Longrightarrow> A B ParStrict Q P\<close> by auto
  }
  {
    assume P10: "X R Perp A B"
    have "Col X R Y"
      by (simp add: Col_perm P4)
    then have P11: "X Y Perp A B"
      using P7 P10 perp_col by blast
    have "A B Par P Q"
    proof -
      have "A B Perp X Y"
        using P11 Perp_perm by blast
      moreover have "P Q Perp X Y"
        using P2 Perp_perm by blast
      ultimately show ?thesis
        using P3 l12_9 by blast
    qed
    {
      assume "A B ParStrict P Q"
      then have "A B ParStrict Q P"
        by (simp add: par_strict_right_comm)
    }
    {
      assume "A \<noteq> B \<and> P \<noteq> Q \<and> Col A P Q \<and> Col B P Q"
      then have "Col A B P"
        using Col_perm l6_16_1 by blast
      then have "P = B"
        by (metis Col_perm assms(1) assms(2) l6_16_1 midpoint_col)
      then have "A B ParStrict Q P"
        using assms(1) assms(2) col_trivial_2 is_midpoint_id by blast
    }
    then have "A B ParStrict Q P"
      using Par_def \<open>A B Par P Q\<close> \<open>A B ParStrict P Q \<Longrightarrow> A B ParStrict Q P\<close> by auto
  }
  then show ?thesis
    using P5 \<open>R Y Perp A B \<Longrightarrow> A B ParStrict Q P\<close> by blast
qed

lemma cop4_perp_in2__col:
  assumes "Coplanar X Y A A'" and
    "Coplanar X Y A B'" and
    "Coplanar X Y B A'" and
    "Coplanar X Y B B'" and
    "P PerpAt A B X Y" and
    "P PerpAt A' B' X Y"
  shows "Col A B A'"
proof -
  have P1: "Col A B P \<and> Col X Y P"
    using assms(5) perp_in_col by auto
  show ?thesis
  proof cases
    assume P2: "A = P"
    show ?thesis
    proof cases
      assume P3: "P = X"
      have "Col B A' P"
      proof -
        have "Coplanar Y B A' P"
          using P3 assms(3) ncoplanar_perm_18 by blast
        moreover have "Y \<noteq> P"
          using P3 assms(6) perp_in_distinct by blast
        moreover have "Per B P Y"
          using assms(5) perp_in_per_4 by auto
        moreover have "Per A' P Y"
          using assms(6) perp_in_per_2 by auto
        ultimately show ?thesis
          using cop_per2__col by auto
      qed
      then show ?thesis
        using Col_perm P2 by blast
    next
      assume P4: "P \<noteq> X"
      have "Col B A' P"
      proof -
        have "Coplanar X B A' P"
          by (metis P1 assms(3) assms(6) col2_cop__cop col_trivial_3 ncoplanar_perm_9 perp_in_distinct)
        moreover have "Per B P X"
          using assms(5) perp_in_per_3 by auto
        moreover have "Per A' P X"
          using assms(6) perp_in_per_1 by auto
        ultimately show ?thesis
          using cop_per2__col P4 by auto
      qed
      then show ?thesis
        using Col_perm P2 by blast
    qed
  next
    assume P5: "A \<noteq> P"
    have P6: "Per A P Y"
      using assms(5) perp_in_per_2 by auto
    show ?thesis
    proof cases
      assume P7: "P = A'"
      have P8: "Per B' P Y"
        using assms(6) perp_in_per_4 by auto
      have "Col A B' P"
      proof -
        have "Coplanar Y A B' P"
          using assms(2) by (metis P1 assms(6) col_transitivity_2 coplanar_trans_1 ncop__ncols perp_in_distinct)
        then show ?thesis using P6 P8 cop_per2__col
          by (metis assms(2) assms(5) assms(6) col_permutation_4 coplanar_perm_5 perp_in_distinct perp_in_per_1 perp_in_per_3)
      qed
      then show ?thesis
        using P1 P7 by auto
    next
      assume T1: "P \<noteq> A'"
      show ?thesis
      proof cases
        assume T2: "Y = P"
        {
          assume R1: "Coplanar X P A A' \<and> P PerpAt A B X P \<and> P PerpAt A' B' X P \<and> A \<noteq> P"
          then have R2: "Per A P X"
            using perp_in_per_1 by auto
          have "Per A' P X"
            using R1 perp_in_per_1 by auto
          then have "Col A B A'"
            by (metis R1 R2 PerpAt_def col_permutation_3 col_transitivity_2 cop_per2__col ncoplanar_perm_5)
        }
        then show ?thesis
          using P5 T1 T2 assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by blast
      next
        assume P10: "Y \<noteq> P"
        have "Col A A' P"
        proof -
          have "Coplanar Y A A' P"
            by (metis P1 assms(1) assms(6) col2_cop__cop col_trivial_2 ncoplanar_perm_9 perp_in_distinct)
          moreover have "Per A P Y"
            by (simp add: P6)
          moreover  have "Per A' P Y"
            using assms(6) perp_in_per_2 by auto
          ultimately show ?thesis
            using cop_per2__col P10 by auto
        qed
        then show ?thesis
          using P1 P5 col2__eq col_permutation_4 by blast
      qed
    qed
  qed
qed

lemma l13_2:
  assumes "A B TS C D" and
    "Per B C A" and
    "Per B D A" and
    "Col C D E" and
    "A E Perp C D"
  shows "B A C CongA D A E \<and> B A D CongA C A E \<and> Bet C E D"
proof -
  have P2: "\<not> Col C A B"
    using TS_def assms(1) by auto
  have P3: "C \<noteq> D"
    using assms(1) not_two_sides_id by blast
  have P4: "\<exists> C'. B A C CongA D A C' \<and> D A OS C' B"
  proof -
    have "\<not> Col B A C"
      using Col_cases P2 by auto
    moreover have "\<not> Col D A B"
      using TS_def assms(1) by blast
    ultimately show ?thesis
      by (simp add: angle_construction_1)
  qed
  then obtain E' where P5: "B A C CongA D A E' \<and> D A OS E' B" by blast
  have P6: "A \<noteq> B"
    using P2 not_col_distincts by blast
  have P7: "A \<noteq> C"
    using P2 not_col_distincts by blast
  have P8: "A \<noteq> D"
    using P5 os_distincts by blast
  have P9: "((A B TS C E' \<and> A E' TS D B) \<or> (A B OS C E' \<and> A E' OS D B \<and> C A B CongA D A E' \<and> B A E' CongA E' A B)) \<longrightarrow> C A E' CongA D A B"
    by (metis P5 P6 conga_diff56 conga_left_comm conga_pseudo_refl l11_22)
  have P10: "C D TS A B"
    by (simp add: assms(1) assms(2) assms(3) ts_per_per_ts)
  have P11: "\<not> Col A C D"
    using P10 TS_def by auto
  obtain T where P12: "Col T A B \<and> Bet C T D"
    using TS_def assms(1) by blast
  obtain T2 where P13: "Col T2 C D \<and> Bet A T2 B"
    using P10 TS_def by auto
  then have P14: "T = T2"
    by (metis Col_def Col_perm P12 P2 P3 P6 l6_16_1)
  have P15: "B InAngle D A C"
    using P10 assms(1) l11_24 ts2__inangle by blast
  have P16: "C A B LeA C A D"
    by (simp add: P10 assms(1) inangle__lea ts2__inangle)
  have P17: "E' InAngle D A C"
  proof -
    have "D A E' LeA D A C"
      using P16 P5 P7 P8 conga_left_comm conga_pseudo_refl l11_30 by presburger
    moreover have "D A OS C E'"
      by (meson P11 P15 P5 col124__nos in_angle_one_side invert_one_side not_col_permutation_2 one_side_symmetry one_side_transitivity)
    ultimately show ?thesis
      by (simp add: lea_in_angle)
  qed
  obtain E'' where P18: "Bet D E'' C \<and> (E'' = A \<or> A Out E'' E')"
    using InAngle_def P17 by auto
  {
    assume "E'' = A"
    then have "B A C CongA D A E \<and> B A D CongA C A E \<and> Bet C E D"
      using Col_def P11 P18 by auto
  }
  {
    assume P19: "A Out E'' E'"
    then have P20: "B A C CongA D A E''"
      by (meson OS_def P5 Tarski_neutral_dimensionless.out2__conga Tarski_neutral_dimensionless_axioms col_one_side_out col_trivial_2 l9_18_R1 not_conga one_side_reflexivity)
    have P21: "A \<noteq> T"
      using P11 P13 P14 by auto
    have "B A C CongA D A E \<and> B A D CongA C A E \<and> Bet C E D"
    proof cases
      assume P22: "E'' = T"
      have P23: "C A B CongA D A B"
      proof -
        have "C A B CongA D A T"
          using P22 P20 conga_left_comm by blast
        moreover have "A Out C C"
          using P7 out_trivial by presburger
        moreover have "A Out B B"
          using P6 out_trivial by auto
        moreover have "A Out D D"
          using P8 out_trivial by auto
        moreover have "A Out B T"
          using Out_def P13 P14 P6 P21 by blast
        ultimately show ?thesis
          using l11_10 by blast
      qed
      then show ?thesis
        using assms(1) assms(2) assms(3) assms(4) assms(5) l13_2_1 by blast
    next
      assume P23A: "E'' \<noteq> T"
      have P24: "D \<noteq> E''"
        using P2 P20 col_trivial_3 ncol_conga_ncol not_col_permutation_3 by blast
      {
        assume P24A: "C = E''"
        have P24B: "C A OS B D"
          by (meson P10 assms(1) invert_one_side ts_ts_os)
        have P24C: "A Out B D"
        proof -
          have "C A B CongA C A D"
            using P20 P24A conga_comm by blast
          moreover have "C A OS B D"
            by (simp add: P24B)
          ultimately show ?thesis
            using conga_os__out by blast
        qed
        then have "False"
          using Col_def P5 one_side_not_col124 out_col by blast
      }
      then have P25: "C \<noteq> E''" by auto
      have P26: "A \<noteq> E''"
        using P19 out_diff1 by auto
      {
        assume "Col E'' A B"
        then have "E'' = T"
          by (smt P13 P14 P18 P2 P3 bet_col l6_21 not_col_permutation_2 not_col_permutation_3)
        then have "False"
          using P23A by auto
      }
      then have P27: "\<not> Col E'' A B" by auto
      have "(A B TS C E'' \<and> A E'' TS D B) \<or> (A B OS C E'' \<and> A E'' OS D B \<and> C A B CongA D A E'' \<and> B A E'' CongA E'' A B)"
      proof cases
        assume P27_0: "A B OS C E''"
        have "A E'' OS D B"
        proof -
          have P27_1: "A E'' TS D C"
            by (metis Col_def P10 P18 P24 TS_def P25 bet__ts invert_two_sides l6_16_1)
          moreover have "A E'' TS B C"
          proof -
            have "A E'' TS T C"
            proof -
              have "\<not> Col T A E''"
                by (metis NCol_cases P13 P14 P21 P27 bet_col col3 col_trivial_2)
              moreover have "\<not> Col C A E''"
                using P27_1 TS_def by auto
              moreover have "\<exists> T0. (Col T0 A E'' \<and> Bet T T0 C)"
                by (meson P12 P18 P27_0 between_symmetry col_trivial_3 l5_3 one_side_chara)
              ultimately show ?thesis
                by (simp add: TS_def)
            qed
            moreover have "A Out T B"
              using Out_def P13 P14 P21 P6 by auto
            ultimately show ?thesis
              using col_trivial_1 l9_5 by blast
          qed
          ultimately show ?thesis
            using OS_def by auto
        qed
        thus ?thesis
          using P20 P27_0 conga_distinct conga_left_comm conga_pseudo_refl by blast
      next
        assume P27_2: "\<not> A B OS C E''"
        show ?thesis
        proof -
          have P27_3: "A B TS C E''"
            using P18 P2 P27_2 P27 assms(1) bet_cop__cop between_symmetry cop_nos__ts ts__coplanar by blast
          moreover have "A E'' TS D B"
          proof -
            have P27_3: "A B OS D E''"
              using P18 bet_ts__os between_symmetry calculation one_side_symmetry by blast
            have P27_4: "A E'' TS T D"
            proof -
              have "\<not> Col T A E''"
                by (metis NCol_cases P13 P14 P21 P27 bet_col col3 col_trivial_2)
              moreover have "\<not> Col D A E''"
                by (smt Col_def P11 P18 P24 P27_3 bet3__bet bet_col1 col3 col_permutation_5 col_two_sides_bet l5_1)
              moreover have "\<exists> T0. (Col T0 A E'' \<and> Bet T T0 D)"
                by (meson Bet_perm P12 P18 P27_3 bet_col1 bet_out__bet between_exchange3 col_trivial_3 not_bet_out one_side_chara)
              ultimately show ?thesis
                by (simp add: TS_def)
            qed
            have "A E'' TS B D"
            proof -
              have "A E'' TS T D"
                using P27_4 by simp
              moreover have "Col A A E''"
                using col_trivial_1 by auto
              moreover have "A Out T B"
                using P13 P14 P21 bet_out by auto
              ultimately show ?thesis
                using l9_5 by blast
            qed
            thus ?thesis
              by (simp add: l9_2)
          qed
          ultimately show ?thesis
            by simp
        qed
      qed
      then have P28: "C A E'' CongA D A B" using l11_22
        by (metis P20 P26 P6 conga_left_comm conga_pseudo_refl)
      obtain C' where P29: "Bet B C C' \<and> Cong C C' B C"
        using segment_construction by blast
      obtain D' where P30: "Bet B D D' \<and> Cong D D' B D"
        using segment_construction by blast
      have P31: "B A D Cong3 D' A D"
      proof -
        have "Per A D B"
          by (simp add: assms(3) l8_2)
        then obtain D'' where P31_2: "D Midpoint B D'' \<and> Cong A B A D''"
          using Per_def by auto
        have "D Midpoint B D'"
          using Cong_perm Midpoint_def P30 by blast
        then have "D' = D''"
          using P31_2 symmetric_point_uniqueness by auto
        thus ?thesis
          using Cong3_def Cong_perm P30 P31_2 cong_reflexivity by blast
      qed
      then have P32: "B A D CongA D' A D"
        using P6 P8 cong3_conga by auto
      have "B A C Cong3 C' A C"
      proof -
        obtain C'' where P33_1: "C Midpoint B C'' \<and> Cong A B A C''"
          using Per_def assms(2) l8_2 by blast
        have "C Midpoint B C'"
          using Cong_perm Midpoint_def P29 by blast
        then have "C' = C''"
          using P33_1 symmetric_point_uniqueness by auto
        thus ?thesis
          using Cong3_def Cong_perm P29 P33_1 cong_reflexivity by blast
      qed
      then have P34: "B A C CongA C' A C"
        using P6 P7 cong3_conga by auto
      have P35: "E'' A C' CongA D' A E''"
      proof -
        have "(A C TS E'' C' \<and> A D TS D' E'') \<or> (A C OS E'' C' \<and> A D OS D' E'')"
        proof -
          have P35_1: "C A OS D E''"
            by (metis Col_perm P11 P18 P25 bet_out between_symmetry one_side_symmetry out_one_side)
          have P35_2: "C A OS B D"
            using P10 assms(1) one_side_symmetry ts_ts_os by blast
          have P35_3: "C A TS B C'"
            by (metis P2 P29 bet__ts cong_diff_4 not_col_distincts)
          have P35_4: "C A OS B E''"
            using P35_1 P35_2 one_side_transitivity by blast
          have P35_5: "D A OS C E''"
            by (metis Col_perm P18 P24 P35_1 bet2__out l5_1 one_side_not_col123 out_one_side)
          have P35_6: "D A OS B C"
            by (simp add: P10 assms(1) invert_two_sides l9_2 one_side_symmetry ts_ts_os)
          have P35_7: "D A TS B D'"
            by (metis P30 TS_def assms(1) bet__ts cong_diff_3 ts_distincts)
          have P35_8: "D A OS B E''"
            using P35_5 P35_6 one_side_transitivity by blast
          have P35_9: "A C TS E'' C'"
            using P35_3 P35_4 invert_two_sides l9_8_2 by blast
          have "A D TS D' E''"
            using P35_7 P35_8 invert_two_sides l9_2 l9_8_2 by blast
          thus ?thesis
            using P35_9 by simp
        qed
        moreover have "E'' A C CongA D' A D"
        proof -
          have "E'' A C CongA B A D"
            by (simp add: P28 conga_comm)
          moreover have "B A D CongA D' A D"
            by (simp add: P32)
          ultimately show ?thesis
            using conga_trans by blast
        qed
        moreover have "C A C' CongA D A E''"
        proof -
          have "D A E'' CongA C A C'"
          proof -
            have "D A E'' CongA B A C"
              by (simp add: P20 conga_sym)
            moreover have "B A C CongA C A C'"
              by (simp add: P34 conga_right_comm)
            ultimately show ?thesis
              using conga_trans by blast
          qed
          thus ?thesis
            using not_conga_sym by blast
        qed
        ultimately show ?thesis
          using l11_22 by auto
      qed
      have P36: "D' \<noteq> B"
        using P30 assms(1) bet_neq32__neq ts_distincts by blast
      have P37: "C' \<noteq> B"
        using P29 assms(1) bet_neq32__neq ts_distincts by blast
      then have P38: "\<not> Col C' D' B"
        by (metis Col_def P10 P29 P30 P36 TS_def col_transitivity_2)
      have P39: "C' D' ParStrict C D"
      proof -
        have "\<not> Col C' D' B"
          by (simp add: P38)
        moreover have "D Midpoint D' B"
          using P30 l7_2 midpoint_def not_cong_3412 by blast
        moreover have "C Midpoint C' B"
          using P29 l7_2 midpoint_def not_cong_3412 by blast
        ultimately show ?thesis
          using triangle_mid_par by auto
      qed
      have P40: "A E'' TS C D"
        by (metis Bet_perm Col_def P10 P18 P24 TS_def \<open>C = E'' \<Longrightarrow> False\<close> bet__ts col_transitivity_2 invert_two_sides)
      have P41: "B A TS C D"
        by (simp add: assms(1) invert_two_sides)
      have P42: "A B OS C C'"
      proof -
        have "\<not> Col A B C"
          by (simp add: P2 not_col_permutation_1)
        moreover have "Col A B B"
          by (simp add: col_trivial_2)
        moreover have "B Out C C'"
          by (metis P29 P37 bet_out cong_identity)
        ultimately show ?thesis
          using out_one_side_1 by blast
      qed
      have P43: "A B OS D D'" using out_one_side_1
        by (metis Col_perm P30 TS_def assms(1) bet_out col_trivial_1)
      then have P44: "A B OS D D'" using invert_two_sides by blast
      have P45: "A B TS C' D"
        using P42 assms(1) l9_8_2 by blast
      then have P46: "A B TS C' D'"
        using P44 l9_2 l9_8_2 by blast
      have P47: "C' D' Perp A E''"
      proof -
        have "A E'' TS C' D'"
        proof -
          have "A Out C' D' \<or> E'' A TS C' D'"
          proof -
            have "E'' A C' CongA E'' A D'"
              by (simp add: P35 conga_right_comm)
            moreover have "Coplanar E'' A C' D'"
            proof -
              have f1: "B A OS C C'"
                by (metis P42 invert_one_side)
              have f2: "Coplanar B A C' C"
                by (meson P42 ncoplanar_perm_7 os__coplanar)
              have f3: "Coplanar D' A C' D"
                by (meson P44 P46 col124__nos coplanar_trans_1 invert_one_side ncoplanar_perm_7 os__coplanar ts__coplanar)
              have "Coplanar D' A C' C"
                using f2 f1 by (meson P46 col124__nos coplanar_trans_1 ncoplanar_perm_6 ncoplanar_perm_8 ts__coplanar)
              then show ?thesis
                using f3 by (meson P18 bet_cop2__cop ncoplanar_perm_6 ncoplanar_perm_7 ncoplanar_perm_8)
            qed
            ultimately show ?thesis using conga_cop__or_out_ts
              by simp
          qed
          then show ?thesis
            using P46 col_two_sides_bet invert_two_sides not_bet_and_out out_col by blast
        qed
        moreover have "Cong C' A D' A"
          using Cong3_def P31 \<open>B A C Cong3 C' A C\<close> cong_inner_transitivity by blast
        moreover have "C' A E'' CongA D' A E''"
          by (simp add: P35 conga_left_comm)
        ultimately show ?thesis
          by (simp add: cong_conga_perp)
      qed
      have T1: "Cong A C' A D'"
      proof -
        have "Cong A C' A B"
          using Cong3_def Cong_perm \<open>B A C Cong3 C' A C\<close> by blast
        moreover have "Cong A D' A B"
          using Cong3_def P31 not_cong_4321 by blast
        ultimately show ?thesis
          using Cong_perm \<open>Cong A C' A B\<close> \<open>Cong A D' A B\<close> cong_inner_transitivity by blast
      qed
      obtain R where T2: "R Midpoint C' D'"
        using midpoint_existence by auto
      have "\<exists> X Y. (R PerpAt X Y C' D' \<and> X Y Perp D C \<and> Coplanar C' D' B X \<and> Coplanar C' D' B Y)"
      proof -
        have "\<not> Col C' D' B"
          by (simp add: P38)
        moreover have "D Midpoint D' B"
          using P30 l7_2 midpoint_def not_cong_3412 by blast
        moreover have "C Midpoint C' B"
          using Cong_perm Mid_perm Midpoint_def P29 by blast
        moreover have "R Midpoint C' D'"
          by (simp add: T2)
        ultimately show ?thesis using l13_1_aux by blast
      qed
      then obtain X Y where T3: "R PerpAt X Y C' D' \<and> X Y Perp D C \<and> Coplanar C' D' B X \<and> Coplanar C' D' B Y"
        by blast
      then have "X \<noteq> Y"
        using perp_not_eq_1 by blast
      have "C D Perp A E''"
      proof cases
        assume "A = R"
        then have W1: "A PerpAt C' D' A E''"
          using Col_def P47 T2 between_trivial2 l8_14_2_1b_bis midpoint_col by blast
        have "Coplanar B C' D' E''"
        proof -
          have "\<not> Col B C D"
            using P10 TS_def by auto
          moreover have "Coplanar B C D B"
            using ncop_distincts by auto
          moreover have "Coplanar B C D C'"
            using P29 bet_col ncop__ncols by blast
          moreover have "Coplanar B C D D'"
            using P30 bet_col ncop__ncols by blast
          moreover have "Coplanar B C D E''"
            by (simp add: P18 bet__coplanar coplanar_perm_22)
          ultimately show ?thesis
            using coplanar_pseudo_trans by blast
        qed
        have "Coplanar C' D' X E''"
        proof -
          have "\<not> Col B C' D'"
            by (simp add: P38 not_col_permutation_2)
          moreover have "Coplanar B C' D' X"
            using T3 ncoplanar_perm_8 by blast
          moreover have "Coplanar B C' D' E''"
            by (simp add: \<open>Coplanar B C' D' E''\<close>)
          ultimately show ?thesis
            using coplanar_trans_1 by blast
        qed
        have "Coplanar C' D' Y E''"
        proof -
          have "\<not> Col B C' D'"
            by (simp add: P38 not_col_permutation_2)
          moreover have "Coplanar B C' D' Y"
            by (simp add: T3 coplanar_perm_12)
          moreover have "Coplanar B C' D' E''"
            by (simp add: \<open>Coplanar B C' D' E''\<close>)
          ultimately show ?thesis
            using coplanar_trans_1 by blast
        qed
        have "Coplanar C' D' X A"
        proof -
          have "Col C' D' A"
            using T2 \<open>A = R\<close> midpoint_col not_col_permutation_2 by blast
          moreover have "Col X A A"
            by (simp add: col_trivial_2)
          ultimately show ?thesis
            using ncop__ncols by blast
        qed
        have "Coplanar C' D' Y A"
        proof -
          have "Col C' D' A"
            using T2 \<open>A = R\<close> midpoint_col not_col_permutation_2 by blast
          moreover have "Col Y A A"
            by (simp add: col_trivial_2)
          ultimately show ?thesis
            using ncop__ncols by blast
        qed
        have "Col X Y A"
        proof -
          have "Coplanar C' D' X A"
            by (simp add: \<open>Coplanar C' D' X A\<close>)
          moreover have "Coplanar C' D' X E''"
            by (simp add: \<open>Coplanar C' D' X E''\<close>)
          moreover have "Coplanar C' D' Y A"
            by (simp add: \<open>Coplanar C' D' Y A\<close>)
          moreover have "Coplanar C' D' Y E''"
            by (simp add: \<open>Coplanar C' D' Y E''\<close>)
          moreover have "A PerpAt X Y C' D'"
            using T3 \<open>A = R\<close> Perp_in_cases by auto
          moreover have "A PerpAt A E'' C' D'"
            using Perp_in_cases \<open>A PerpAt C' D' A E''\<close> by blast
          ultimately show ?thesis
            using cop4_perp_in2__col by blast
        qed
        have "Col X Y E''"
        proof -
          have "Coplanar C' D' X E''"
            using \<open>Coplanar C' D' X E''\<close> by auto
          moreover have "Coplanar C' D' X A"
            by (simp add: \<open>Coplanar C' D' X A\<close>)
          moreover have "Coplanar C' D' Y E''"
            by (simp add: \<open>Coplanar C' D' Y E''\<close>)
          moreover have "Coplanar C' D' Y A"
            using \<open>Coplanar C' D' Y A\<close> by auto
          moreover have "A PerpAt X Y C' D'"
            using T3 \<open>A = R\<close> Perp_in_cases by auto
          moreover have "A PerpAt E'' A C' D'"
            using Perp_in_perm W1 by blast
          ultimately show ?thesis
            using cop4_perp_in2__col by blast
        qed
        have "A E'' Perp C D"
        proof cases
          assume "Y = A"
          show ?thesis
          proof -
            have "A \<noteq> E''"
              by (simp add: P26)
            moreover have "A X Perp C D"
              using T3 Perp_cases \<open>Y = A\<close> by blast
            moreover have "Col A X E''"
              using Col_perm \<open>Col X Y E''\<close> \<open>Y = A\<close> by blast
            ultimately show ?thesis
              using perp_col by blast
          qed
        next
          assume "Y \<noteq> A"
          show ?thesis
          proof -
            have "A \<noteq> E''"
              by (simp add: P26)
            moreover have "A Y Perp C D"
            proof -
              have "Y X Perp C D"
                using T3 by (simp add: perp_comm)
              then have "Y A Perp C D"
                using \<open>Col X Y A\<close> \<open>Y \<noteq> A\<close> col_trivial_2 perp_col2 perp_left_comm by blast
              then show ?thesis
                using Perp_cases by blast
            qed
            moreover have "Col A Y E''"
              using Col_perm \<open>Col X Y A\<close> \<open>Col X Y E''\<close> \<open>X \<noteq> Y\<close> col_transitivity_2 by blast
            ultimately show ?thesis
              using perp_col by blast
          qed
        qed
        thus ?thesis
          using Perp_perm by blast
      next
        assume "A \<noteq> R"
        have "R \<noteq> C'"
          using P46 T2 is_midpoint_id ts_distincts by blast
        have "Per A R C'" using T1 T2 Per_def by blast
        then have "R PerpAt A R R C'"
          by (simp add: \<open>A \<noteq> R\<close> \<open>R \<noteq> C'\<close> per_perp_in)
        then have "R PerpAt R C' A R"
          using Perp_in_perm by blast
        then have "R C' Perp A R \<or> R R Perp A R"
          using perp_in_perp by auto
        {
          assume "R C' Perp A R"
          then have "C' R Perp A R"
            by (simp add: \<open>R C' Perp A R\<close> Perp_perm)
          have "C' D' Perp R A"
            by (metis P47 T2 \<open>A \<noteq> R\<close> \<open>Per A R C'\<close> \<open>R \<noteq> C'\<close> col_per_perp midpoint_col perp_distinct perp_right_comm)
          then have "R PerpAt C' D' R A"
            using T2 l8_14_2_1b_bis midpoint_col not_col_distincts by blast
          have "Col B D D'"
            by (simp add: Col_def P30)
          have "Col B C C'"
            using Col_def P29 by auto
          have "Col D E'' C"
            using P18 bet_col by auto
          have "Col R C' D'"
            using \<open>R PerpAt C' D' R A\<close> by (simp add: T2 midpoint_col)
          have "Col A E'' E'"
            by (simp add: P19 out_col)
          have "Coplanar C' D' X A"
          proof -
            have "\<not> Col B C' D'"
              using Col_perm P38 by blast
            moreover have "Coplanar B C' D' X"
              using T3 ncoplanar_perm_8 by blast
            moreover have "Coplanar B C' D' A"
              using P46 ncoplanar_perm_18 ts__coplanar by blast
            ultimately show ?thesis
              using coplanar_trans_1 by auto
          qed
          have "Coplanar C' D' Y A"
          proof -
            have "\<not> Col B C' D'"
              using Col_perm P38 by blast
            moreover have "Coplanar B C' D' Y"
              using T3 ncoplanar_perm_8 by blast
            moreover have "Coplanar B C' D' A"
              using P46 ncoplanar_perm_18 ts__coplanar by blast
            ultimately show ?thesis
              using coplanar_trans_1 by auto
          qed
          have "Coplanar C' D' X R"
          proof -
            have "Col C' D' R"
              using Col_perm \<open>Col R C' D'\<close> by blast
            moreover have "Col X R R"
              by (simp add: col_trivial_2)
            ultimately show ?thesis
              using ncop__ncols by blast
          qed
          have "Coplanar C' D' Y R"
            using Col_perm T2 midpoint_col ncop__ncols by blast
          have "Col X Y A"
          proof -
            have "R PerpAt X Y C' D'"
              using T3 by simp
            moreover have "R PerpAt A R C' D'"
              using Perp_in_perm \<open>R PerpAt C' D' R A\<close> by blast
            ultimately show ?thesis
              using \<open>Coplanar C' D' Y R\<close>  \<open>Coplanar C' D' X R\<close> cop4_perp_in2__col \<open>Coplanar C' D' X A\<close> \<open>Coplanar C' D' Y A\<close> by blast
          qed
          have Z1: "Col X Y R"
            using T3 perp_in_col by blast
          have "Col A E'' R"
          proof -
            have "Coplanar C' D' E'' R"
              using Col_cases \<open>Col R C' D'\<close> ncop__ncols by blast
            moreover have "A E'' Perp C' D'"
              using P47 Perp_perm by blast
            moreover have "A R Perp C' D'"
              using Perp_perm \<open>C' D' Perp R A\<close> by blast
            ultimately show ?thesis
              using cop_perp2__col by blast
          qed
          then have "Col X Y E''" using Z1
            by (metis (full_types) \<open>A \<noteq> R\<close> \<open>Col X Y A\<close> col_permutation_4 col_trivial_2 l6_21)
          have "Col A E'' R"
          proof -
            have "Coplanar C' D' E'' R"
              using Col_cases \<open>Col R C' D'\<close> ncop__ncols by blast
            moreover have "A E'' Perp C' D'"
              using P47 Perp_perm by blast
            moreover have "A R Perp C' D'"
              using Perp_perm \<open>C' D' Perp R A\<close> by blast
            ultimately show ?thesis
              using cop_perp2__col by blast
          qed
          have "Col A R X"
            using \<open>Col X Y A\<close> \<open>Col X Y R\<close> \<open>X \<noteq> Y\<close> col_transitivity_1 not_col_permutation_3 by blast
          have "Col A R Y"
            using \<open>Col X Y A\<close> \<open>Col X Y R\<close> \<open>X \<noteq> Y\<close> col_transitivity_2 not_col_permutation_3 by blast
          have "A E'' Perp C D"
          proof cases
            assume "X = A"
            show ?thesis
            proof -
              have "A \<noteq> E''"
                by (simp add: P26)
              moreover have "A Y Perp C D"
                using T3 \<open>X = A\<close> perp_right_comm by blast
              moreover have "Col A Y E''"
                using Col_perm \<open>A \<noteq> R\<close> \<open>Col A E'' R\<close> \<open>Col A R Y\<close> col_transitivity_1 by blast
              ultimately show ?thesis
                using perp_col by auto
            qed
          next
            assume "X \<noteq> A"
            show ?thesis
            proof -
              have "A X Perp C D"
                by (smt P3 T3 \<open>Col X Y A\<close> \<open>X \<noteq> A\<close> col_trivial_2 col_trivial_3 perp_col4)
              moreover have "Col A X E''"
                using Col_perm \<open>A \<noteq> R\<close> \<open>Col A E'' R\<close> \<open>Col A R X\<close> col_transitivity_1 by blast
              ultimately show ?thesis
                using P26 perp_col by blast
            qed
          qed
        }
        {
          assume "R R Perp A R"
          then have "A E'' Perp C D"
            using perp_distinct by blast
        }
        then have "A E'' Perp C D"
          using Perp_cases \<open>R C' Perp A R \<Longrightarrow> A E'' Perp C D\<close> \<open>R C' Perp A R \<or> R R Perp A R\<close> by auto
        then show ?thesis
          using Perp_perm by blast
      qed
      show ?thesis
      proof -
        have "Col A E E''"
        proof -
          have "Coplanar C D E E'"
            using assms(4) col__coplanar by auto
          moreover have "A E Perp C D"
            using assms(5) by auto
          moreover have "A E'' Perp C D"
            using Perp_perm \<open>C D Perp A E''\<close> by blast
          ultimately show ?thesis
            by (meson P11 col_perp2_ncol_col col_trivial_3 not_col_permutation_2)
        qed
        moreover have "E'' = E"
        proof -
          have f1: "C = E'' \<or> Col C E'' D"
            by (metis P18 bet_out_1 out_col)
          then have f2: "C = E'' \<or> Col C E'' E"
            using Col_perm P3 assms(4) col_transitivity_1 by blast
          have "\<forall>p. (C = E'' \<or> Col C p D) \<or> \<not> Col C E'' p"
            using f1 by (meson col_transitivity_1)
          then have "\<exists>p. \<not> Col E'' p A \<and> Col E'' E p"
            using f2 by (metis (no_types) Col_perm P11 assms(4))
          then show ?thesis
            using Col_perm calculation col_transitivity_1 by blast
        qed
        ultimately show ?thesis
          by (metis Bet_perm P18 P20 P28 Tarski_neutral_dimensionless.conga_left_comm Tarski_neutral_dimensionless_axioms not_conga_sym)
      qed
    qed
    then have "B A C CongA D A E \<and> B A D CongA C A E \<and> Bet C E D"
      by blast
  }
  thus ?thesis
    using P18 \<open>E'' = A \<Longrightarrow> B A C CongA D A E \<and> B A D CongA C A E \<and> Bet C E D\<close> by blast
qed

lemma perp2_refl:
  assumes "A \<noteq> B"
  shows "P Perp2 A B A B"
proof cases
  assume "Col A B P"
  obtain X where "\<not> Col A B X"
    using assms not_col_exists by blast
  then obtain Q where "A B Perp Q P \<and> A B OS X Q"
    using \<open>Col A B P\<close> l10_15 by blast
  thus ?thesis
    using Perp2_def Perp_cases col_trivial_3 by blast
next
  assume "\<not> Col A B P"
  then obtain Q where "Col A B Q \<and> A B Perp P Q"
    using l8_18_existence by blast
  thus ?thesis
    using Perp2_def Perp_cases col_trivial_3 by blast
qed

lemma perp2_sym:
  assumes "P Perp2 A B C D"
  shows "P Perp2 C D A B"
proof -
  obtain X Y where "Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms by auto
  thus ?thesis
    using Perp2_def by blast
qed

lemma perp2_left_comm:
  assumes "P Perp2 A B C D"
  shows "P Perp2 B A C D"
proof -
  obtain X Y where "Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms by auto
  thus ?thesis
    using Perp2_def perp_right_comm by blast
qed

lemma perp2_right_comm:
  assumes "P Perp2 A B C D"
  shows "P Perp2 A B D C"
proof -
  obtain X Y where "Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms by auto
  thus ?thesis
    using Perp2_def perp_right_comm by blast
qed

lemma perp2_comm:
  assumes "P Perp2 A B C D"
  shows "P Perp2 B A D C"
proof -
  obtain X Y where "Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms by auto
  thus ?thesis
    using assms perp2_left_comm perp2_right_comm by blast
qed

lemma perp2_pseudo_trans:
  assumes "P Perp2 A B C D" and
    "P Perp2 C D E F" and
    "\<not> Col C D P"
  shows "P Perp2 A B E F"
proof -
  obtain X Y where P1: "Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms(1) by auto
  obtain X' Y' where P2: "Col P X' Y' \<and> X' Y' Perp C D \<and> X' Y' Perp E F"
    using Perp2_def assms(2) by auto
  have "X Y Par X' Y'"
  proof -
    have "Coplanar P C D X"
    proof cases
      assume "X = P"
      thus ?thesis
        using ncop_distincts by blast
    next
      assume "X \<noteq> P"
      then have "X P Perp C D"
        using Col_cases P1 perp_col by blast
      then have "Coplanar X P C D"
        by (simp add: perp__coplanar)
      thus ?thesis
        using ncoplanar_perm_18 by blast
    qed
    have "Coplanar P C D Y"
    proof cases
      assume "Y = P"
      thus ?thesis
        using ncop_distincts by blast
    next
      assume "Y \<noteq> P"
      then have "Y P Perp C D"
        by (metis (full_types) Col_cases P1 Perp_cases col_transitivity_2 perp_col2)
      then have "Coplanar Y P C D"
        by (simp add: perp__coplanar)
      thus ?thesis
        using ncoplanar_perm_18 by blast
    qed
    have "Coplanar P C D X'"
    proof cases
      assume "X' = P"
      thus ?thesis
        using ncop_distincts by blast
    next
      assume "X' \<noteq> P"
      then have "X' P Perp C D"
        using Col_cases P2 perp_col by blast
      then have "Coplanar X' P C D"
        by (simp add: perp__coplanar)
      thus ?thesis
        using ncoplanar_perm_18 by blast
    qed
    have "Coplanar P C D Y'"
    proof cases
      assume "Y' = P"
      thus ?thesis
        using ncop_distincts by blast
    next
      assume "Y' \<noteq> P"
      then have "Y' P Perp C D"
        by (metis (full_types) Col_cases P2 Perp_cases col_transitivity_2 perp_col2)
      then have "Coplanar Y' P C D"
        by (simp add: perp__coplanar)
      thus ?thesis
        using ncoplanar_perm_18 by blast
    qed
    show ?thesis
    proof -
      have "Coplanar C D X X'"
        using Col_cases \<open>Coplanar P C D X'\<close> \<open>Coplanar P C D X\<close> assms(3) coplanar_trans_1 by blast
      moreover have "Coplanar C D X Y'"
        using Col_cases \<open>Coplanar P C D X\<close> \<open>Coplanar P C D Y'\<close> assms(3) coplanar_trans_1 by blast
      moreover have "Coplanar C D Y X'"
        using Col_cases \<open>Coplanar P C D X'\<close> \<open>Coplanar P C D Y\<close> assms(3) coplanar_trans_1 by blast
      moreover have "Coplanar C D Y Y'"
        using Col_cases \<open>Coplanar P C D Y'\<close> \<open>Coplanar P C D Y\<close> assms(3) coplanar_trans_1 by blast
      ultimately show ?thesis
        using l12_9 P1 P2 by blast
    qed
  qed
  thus ?thesis
  proof -
    {
      assume "X Y ParStrict X' Y'"
      then have "Col X X' Y'"
        using P1 P2 \<open>X Y ParStrict X' Y'\<close> par_not_col by blast
    }
    then have "Col X X' Y'"
      using Par_def \<open>X Y Par X' Y'\<close> by blast
    moreover have "Col Y X' Y'"
    proof -
      {
        assume "X Y ParStrict X' Y'"
        then have "Col Y X' Y'"
          using P1 P2 \<open>X Y ParStrict X' Y'\<close> par_not_col by blast
      }
      thus ?thesis
        using Par_def \<open>X Y Par X' Y'\<close> by blast
    qed
    moreover have "X \<noteq> Y"
      using P1 perp_not_eq_1 by auto
    ultimately show ?thesis
      by (meson Perp2_def P1 P2 col_permutation_1 perp_col2)
  qed
qed

lemma col_cop_perp2__pars_bis:
  assumes "\<not> Col A B P" and
    "Col C D P" and
    "Coplanar A B C D" and
    "P Perp2 A B C D"
  shows "A B ParStrict C D"
proof -
  obtain X Y where P1: "Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms(4) by auto
  then have "Col X Y P"
    using Col_perm by blast
  obtain Q where "X \<noteq> Q \<and> Y \<noteq> Q \<and> P \<noteq> Q \<and> Col X Y Q"
    using \<open>Col X Y P\<close> diff_col_ex3 by blast
  thus ?thesis
    by (smt P1 Perp_perm assms(1) assms(2) assms(3) col_cop_perp2_pars col_permutation_1 col_transitivity_2 not_col_distincts perp_col4 perp_distinct)
qed

lemma perp2_preserves_bet23:
  assumes "Bet PO A B" and
    "Col PO A' B'" and
    "\<not> Col PO A A'" and
    "PO Perp2 A A' B B'"
  shows "Bet PO A' B'"
proof -
  have "A \<noteq> A'"
    using assms(3) not_col_distincts by auto
  show ?thesis
  proof cases
    assume "A' = B'"
    thus ?thesis
      using between_trivial by auto
  next
    assume "A' \<noteq> B'"
    {
      assume "A = B"
      then obtain X Y where P1: "Col PO X Y \<and> X Y Perp A A' \<and> X Y Perp A B'"
        using Perp2_def assms(4) by blast
      have "Col A A' B'"
      proof -
        have "Coplanar X Y A' B'"
          using Col_cases Coplanar_def P1 assms(2) by auto
        moreover have "A A' Perp X Y"
          using P1 Perp_perm by blast
        moreover have "A B' Perp X Y"
          using P1 Perp_perm by blast
        ultimately show ?thesis
          using cop_perp2__col by blast
      qed
      then have "False"
        using Col_perm \<open>A' \<noteq> B'\<close> assms(2) assms(3) l6_16_1 by blast
    }
    then have "A \<noteq> B" by auto
    have "A A' Par B B'"
    proof -
      obtain X Y where P2: "Col PO X Y \<and> X Y Perp A A' \<and> X Y Perp B B'"
        using Perp2_def assms(4) by auto
      then have "Coplanar X Y A B"
        using Coplanar_def assms(1) bet_col not_col_permutation_2 by blast
      show ?thesis
      proof -
        have "Coplanar X Y A B'"
          by (metis (full_types) Col_cases P2 assms(2) assms(3) col_cop2__cop col_trivial_3 ncop__ncols perp__coplanar)
        moreover have "Coplanar X Y A' B"
        proof cases
          assume "Col A X Y"
          then have "Col Y X A"
            by (metis (no_types) Col_cases)
          then show ?thesis
            by (metis Col_cases P2 assms(1) assms(3) bet_col colx ncop__ncols not_col_distincts)
        next
          assume "\<not> Col A X Y"
          moreover have "Coplanar A X Y A'"
            using Coplanar_def P2 perp_inter_exists by blast
          moreover have "Coplanar A X Y B"
            using \<open>Coplanar X Y A B\<close> ncoplanar_perm_8 by blast
          ultimately show ?thesis
            using coplanar_trans_1 by auto
        qed
        moreover have "Coplanar X Y A' B'"
          using Col_cases Coplanar_def P2 assms(2) by auto
        moreover have "A A' Perp X Y"
          using P2 Perp_perm by blast
        moreover have "B B' Perp X Y"
          using P2 Perp_perm by blast
        ultimately show ?thesis
          using \<open>Coplanar X Y A B\<close> l12_9 by auto
      qed
    qed
    {
      assume "A A' ParStrict B B'"
      then have "A A' OS B B'"
        by (simp add: l12_6)
      have "A A' TS PO B"
        using Col_cases \<open>A \<noteq> B\<close> assms(1) assms(3) bet__ts by blast
      then have "A A' TS B' PO"
        using \<open>A A' OS B B'\<close> l9_2 l9_8_2 by blast
      then have "Bet PO A' B'"
        using Col_cases assms(2) between_symmetry col_two_sides_bet invert_two_sides by blast
    }
    thus ?thesis
      by (metis Col_cases Par_def \<open>A A' Par B B'\<close> \<open>A \<noteq> B\<close> assms(1) assms(3) bet_col col_trivial_3 l6_21)
  qed
qed

lemma perp2_preserves_bet13:
  assumes "Bet B PO C" and
    "Col PO B' C'" and
    "\<not> Col PO B B'" and
    "PO Perp2 B C' C B'"
  shows "Bet B' PO C'"
proof cases
  assume "C' = PO"
  thus ?thesis
    using not_bet_distincts by blast
next
  assume "C' \<noteq> PO"
  show ?thesis
  proof cases
    assume "B' = PO"
    thus ?thesis
      using between_trivial2 by auto
  next
    assume "B' \<noteq> PO"
    have "B \<noteq> PO"
      using assms(3) col_trivial_1 by auto
    have "Col B PO C"
      by (simp add: Col_def assms(1))
    show ?thesis
    proof cases
      assume "B = C"
      thus ?thesis
        using \<open>B = C\<close> \<open>B \<noteq> PO\<close> assms(1) between_identity by blast
    next
      assume "B \<noteq> C"
      have "B C' Par C B'"
      proof -
        obtain X Y where P1: "Col PO X Y \<and> X Y Perp B C' \<and> X Y Perp C B'"
          using Perp2_def assms(4) by auto
        have "Coplanar X Y B C"
          by (meson P1 \<open>Col B PO C\<close> assms(1) l9_18_R2 ncop__ncols not_col_permutation_2 not_col_permutation_5 ts__coplanar)
        have "Coplanar X Y C' B'"
          using Col_cases Coplanar_def P1 assms(2) by auto
        show ?thesis
        proof -
          have "Coplanar X Y B C"
            by (simp add: \<open>Coplanar X Y B C\<close>)
          moreover have "Coplanar X Y B B'"
            by (metis P1 \<open>C' \<noteq> PO\<close> assms(1) assms(2) bet_cop__cop calculation col_cop2__cop not_col_permutation_5 perp__coplanar)
          moreover have "Coplanar X Y C' C"
            by (smt P1 \<open>B \<noteq> PO\<close> \<open>Col B PO C\<close> \<open>Coplanar X Y C' B'\<close> assms(2) col2_cop__cop col_cop2__cop col_permutation_1 col_transitivity_2 coplanar_perm_1 perp__coplanar)
          moreover have "Coplanar X Y C' B'"
            by (simp add: \<open>Coplanar X Y C' B'\<close>)
          moreover have "B C' Perp X Y"
            using P1 Perp_perm by blast
          moreover have "C B' Perp X Y"
            by (simp add: P1 Perp_perm)
          ultimately show ?thesis
            using l12_9 by blast
        qed
      qed
      have "B C' ParStrict C B'"
        by (metis Out_def Par_def \<open>B C' Par C B'\<close> \<open>B \<noteq> C\<close> \<open>B \<noteq> PO\<close> assms(1) assms(3) col_transitivity_1 not_col_permutation_4 out_col)
      have "B' \<noteq> PO"
        by (simp add: \<open>B' \<noteq> PO\<close>)
      obtain X Y where P5: "Col PO X Y \<and> X Y Perp B C' \<and> X Y Perp C B'"
        using Perp2_def assms(4) by auto
      have "X \<noteq> Y"
        using P5 perp_not_eq_1 by auto
      show ?thesis
      proof cases
        assume "Col X Y B"
        have "Col X Y C"
          using P5 \<open>B \<noteq> PO\<close> \<open>Col B PO C\<close> \<open>Col X Y B\<close> col_permutation_1 colx by blast
        show ?thesis
        proof -
          have "Col B' PO C'"
            using Col_cases assms(2) by auto
          moreover have "Per PO C B'"
            by (metis P5 \<open>B C' ParStrict C B'\<close> \<open>Col X Y C\<close> assms(2) col_permutation_2 par_strict_not_col_2 perp_col2 perp_per_2)
          moreover have "Per PO B C'"
            using P5 \<open>B \<noteq> PO\<close> \<open>Col X Y B\<close> col_permutation_1 perp_col2 perp_per_2 by blast
          ultimately show ?thesis
            by (metis Tarski_neutral_dimensionless.per13_preserves_bet_inv Tarski_neutral_dimensionless_axioms \<open>B C' ParStrict C B'\<close> assms(1) assms(3) between_symmetry not_col_distincts not_col_permutation_3 par_strict_not_col_2)
        qed
      next
        assume "\<not> Col X Y B"
        then obtain B0 where U1: "Col X Y B0 \<and> X Y Perp B B0"
          using l8_18_existence by blast
        have "\<not> Col X Y C"
          by (smt P5 \<open>B C' ParStrict C B'\<close> \<open>Col B PO C\<close> \<open>\<not> Col X Y B\<close> assms(2) col_permutation_2 colx par_strict_not_col_2)
        then obtain C0 where U2: "Col X Y C0 \<and> X Y Perp C C0"
          using l8_18_existence by blast
        have "B0 \<noteq> PO"
          by (metis P5 Perp_perm \<open>Col B PO C\<close> \<open>Col X Y B0 \<and> X Y Perp B B0\<close> \<open>\<not> Col X Y C\<close> assms(3) col_permutation_2 col_permutation_3 col_perp2_ncol_col)
        {
          assume "C0 = PO"
          then have "C PO Par C B'"
            by (metis P5 Par_def Perp_cases \<open>Col X Y C0 \<and> X Y Perp C C0\<close> \<open>\<not> Col X Y C\<close> col_perp2_ncol_col not_col_distincts not_col_permutation_3 perp_distinct)
          then have "False"
            by (metis \<open>B C' ParStrict C B'\<close> assms(2) assms(3) col3 not_col_distincts par_id_2 par_strict_not_col_2)
        }
        then have "C0 \<noteq> PO" by auto
        have "Bet B0 PO C0"
        proof -
          have "Bet B PO C"
            by (simp add: assms(1))
          moreover have "PO \<noteq> B0"
            using \<open>B0 \<noteq> PO\<close> by auto
          moreover have "PO \<noteq> C0"
            using \<open>C0 \<noteq> PO\<close> by auto
          moreover have "Col B0 PO C0"
            using U1 U2 P5 \<open>X \<noteq> Y\<close> col3 not_col_permutation_2 by blast
          moreover have "Per PO B0 B"
          proof -
            have "B0 PerpAt PO B0 B0 B"
            proof cases
              assume "X = B0"
              have "B0 PO Perp B B0"
                by (metis P5 U1 calculation(2) col3 col_trivial_2 col_trivial_3 perp_col2)
              show ?thesis
              proof -
                have "B0 \<noteq> PO"
                  using calculation(2) by auto
                moreover have "B0 Y Perp B B0"
                  using U1 \<open>X = B0\<close> by auto
                moreover have "Col B0 Y PO"
                  using Col_perm P5 \<open>X = B0\<close> by blast
                ultimately show ?thesis
                  using \<open>B0 PO Perp B B0\<close> perp_in_comm perp_perp_in by blast
              qed
            next
              assume "X \<noteq> B0"
              have "X B0 Perp B B0"
                using U1 \<open>X \<noteq> B0\<close> perp_col by blast
              have "B0 PO Perp B B0"
                by (metis P5 U1 calculation(2) not_col_permutation_2 perp_col2)
              then have "B0 PerpAt B0 PO B B0"
                by (simp add: perp_perp_in)
              thus ?thesis
                using Perp_in_perm by blast
            qed
            then show ?thesis
              by (simp add: perp_in_per)
          qed
          moreover have "Per PO C0 C"
          proof -
            have "C0 PO Perp C C0"
              by (metis P5 U2 calculation(3) col3 col_trivial_2 col_trivial_3 perp_col2)
            then have "C0 PerpAt PO C0 C0 C"
              by (simp add: perp_in_comm perp_perp_in)
            thus ?thesis
              using perp_in_per_2 by auto
          qed
          ultimately show ?thesis
            using per13_preserves_bet by blast
        qed
        show ?thesis
        proof cases
          assume "C' = B0"
          have "B' = C0"
          proof -
            have "\<not> Col C' PO C"
              using P5 U1 \<open>B0 \<noteq> PO\<close> \<open>C' = B0\<close> \<open>\<not> Col X Y C\<close> colx not_col_permutation_3 not_col_permutation_4 by blast
            moreover have "C \<noteq> C0"
              using U2 \<open>\<not> Col X Y C\<close> by auto
            moreover have "Col C C0 B'"
            proof -
              have "Coplanar X Y C0 B'"
              proof -
                have "Col X Y C0"
                  by (simp add: U2)
                moreover have "Col C0 B' C0"
                  by (simp add: col_trivial_3)
                ultimately show ?thesis
                  using ncop__ncols by blast
              qed
              moreover have "C C0 Perp X Y"
                using Perp_perm U2 by blast
              moreover have "C B' Perp X Y"
                using P5 Perp_perm by blast
              ultimately show ?thesis
                using cop_perp2__col by auto
            qed
            ultimately show ?thesis
              by (metis Col_def \<open>C' = B0\<close> \<open>Bet B0 PO C0\<close> assms(2) colx)
          qed
          show ?thesis
            using Bet_cases \<open>B' = C0\<close> \<open>C' = B0\<close> \<open>Bet B0 PO C0\<close> by blast
        next
          assume "C' \<noteq> B0"
          then have "B' \<noteq> C0"
            by (metis P5 U1 U2 \<open>C0 \<noteq> PO\<close> assms(2) col_permutation_1 colx l8_18_uniqueness)
          have "B C' Par B B0"
          proof -
            have "Coplanar X Y B B"
              using ncop_distincts by auto
            moreover have "Coplanar X Y B B0"
              using U1 ncop__ncols by blast
            moreover have "Coplanar X Y C' B"
              using P5 ncoplanar_perm_1 perp__coplanar by blast
            moreover have "Coplanar X Y C' B0"
              using \<open>\<not> Col X Y B\<close> calculation(2) calculation(3) col_permutation_1 coplanar_perm_12 coplanar_perm_18 coplanar_trans_1 by blast
            moreover have "B C' Perp X Y"
              using P5 Perp_perm by blast
            moreover have "B B0 Perp X Y"
              using Perp_perm U1 by blast
            ultimately show ?thesis
              using l12_9 by blast
          qed
          {
            assume "B C' ParStrict B B0"
            have "Col B B0 C'"
              by (simp add: \<open>B C' Par B B0\<close> par_id_3)
          }
          then have "Col B B0 C'"
            using \<open>B C' Par B B0\<close> par_id_3 by blast
          have "Col C C0 B'"
          proof -
            have "Coplanar X Y C0 B'"
              by (simp add: U2 col__coplanar)
            moreover have "C C0 Perp X Y"
              by (simp add: Perp_perm U2)
            moreover have "C B' Perp X Y"
              using P5 Perp_perm by blast
            ultimately show ?thesis
              using cop_perp2__col by auto
          qed
          show ?thesis
          proof -
            have "Col B' PO C'"
              using assms(2) not_col_permutation_4 by blast
            moreover have "Per PO C0 B'"
            proof -
              have "C0 PerpAt PO C0 C0 B'"
              proof cases
                assume "X = C0"
                have "C0 PO Perp C B'"
                proof -
                  have "C0 \<noteq> PO"
                    by (simp add: \<open>C0 \<noteq> PO\<close>)
                  moreover have "C0 Y Perp C B'"
                    using P5 \<open>X = C0\<close> by auto
                  moreover have "Col C0 Y PO"
                    using Col_perm P5 \<open>X = C0\<close> by blast
                  ultimately show ?thesis
                    using perp_col by blast
                qed
                then have "B' C0 Perp C0 PO"
                  using Perp_perm \<open>B' \<noteq> C0\<close> \<open>Col C C0 B'\<close> not_col_permutation_1 perp_col1 by blast
                then have "C0 PerpAt C0 B' PO C0"
                  using Perp_perm perp_perp_in by blast
                thus ?thesis
                  using Perp_in_perm by blast
              next
                assume "X \<noteq> C0"
                then have "X C0 Perp C B'"
                  using P5 U2 perp_col by blast
                have "C0 PO Perp C B'"
                  using Col_cases P5 U2 \<open>C0 \<noteq> PO\<close> perp_col2 by blast
                then have "B' C0 Perp C0 PO"
                  using Perp_cases \<open>B' \<noteq> C0\<close> \<open>Col C C0 B'\<close> col_permutation_2 perp_col by blast
                thus ?thesis
                  using Perp_in_perm Perp_perm perp_perp_in by blast
              qed
              then show ?thesis
                using perp_in_per_2 by auto
            qed
            moreover have "Per PO B0 C'"
            proof -
              have "B0 PerpAt PO B0 B0 C'"
              proof -
                have "Col C' B B0"
                  using Col_cases \<open>Col B B0 C'\<close> by blast
                then have "C' B0 Perp X Y" using perp_col P5 Perp_cases \<open>C' \<noteq> B0\<close> by blast
                show ?thesis
                proof -
                  have "PO B0 Perp B0 C'"
                    by (smt P5 U1 \<open>B0 \<noteq> PO\<close> \<open>C' \<noteq> B0\<close> \<open>Col B B0 C'\<close> col_trivial_2 not_col_permutation_2 perp_col4)
                  then show ?thesis
                    using Perp_in_cases Perp_perm perp_perp_in by blast
                qed
              qed
              thus ?thesis
                by (simp add: perp_in_per)
            qed
            ultimately show ?thesis
              using \<open>B0 \<noteq> PO\<close> \<open>C0 \<noteq> PO\<close> \<open>Bet B0 PO C0\<close> between_symmetry per13_preserves_bet_inv by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma is_image_perp_in:
  assumes "A \<noteq> A'" and
    "X \<noteq> Y" and
    "A A' Reflect X Y"
  shows "\<exists> P. P PerpAt A A' X Y"
  by (metis Perp_def Tarski_neutral_dimensionless.Perp_perm Tarski_neutral_dimensionless_axioms assms(1) assms(2) assms(3) ex_sym1 l10_6_uniqueness)

lemma perp_inter_perp_in_n:
  assumes "A B Perp C D"
  shows "\<exists> P. Col A B P \<and> Col C D P \<and> P PerpAt A B C D"
  by (simp add: assms perp_inter_perp_in)

lemma perp2_perp_in:
  assumes "PO Perp2 A B C D" and
    "\<not> Col PO A B" and
    "\<not> Col PO C D"
  shows "\<exists> P Q. Col A B P \<and> Col C D Q \<and> Col PO P Q \<and> P PerpAt PO P A B \<and> Q PerpAt PO Q C D"
proof -
  obtain X Y where P1: "Col PO X Y  \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms(1) by blast
  have "X \<noteq> Y"
    using P1 perp_not_eq_1 by auto
  obtain P where P2: "Col X Y P \<and> Col A B P \<and> P PerpAt X Y A B"
    using P1 perp_inter_perp_in_n by blast
  obtain Q where P3: "Col X Y Q \<and> Col C D Q \<and> Q PerpAt X Y C D"
    using P1 perp_inter_perp_in_n by blast
  have "Col A B P"
    using P2 by simp
  moreover have "Col C D Q"
    using P3 by simp
  moreover have "Col PO P Q"
    using P2 P3 P1 \<open>X \<noteq> Y\<close> col3 not_col_permutation_2 by blast
  moreover have "P PerpAt PO P A B"
  proof cases
    assume "X = PO"
    thus ?thesis
      by (metis P2 assms(2) not_col_permutation_3 not_col_permutation_4 perp_in_col_perp_in perp_in_sym)
  next
    assume "X \<noteq> PO"
    then have "P PerpAt A B X PO"
      by (meson Col_cases P1 P2 perp_in_col_perp_in perp_in_sym)
    then have "P PerpAt A B PO X"
      using Perp_in_perm by blast
    then have "P PerpAt A B PO P"
      by (metis Col_cases assms(2) perp_in_col perp_in_col_perp_in)
    thus ?thesis
      by (simp add: perp_in_sym)
  qed
  moreover have "Q PerpAt PO Q C D"
    by (metis P1 P3 \<open>X \<noteq> Y\<close> assms(3) col_trivial_2 colx not_col_permutation_3 not_col_permutation_4 perp_in_col_perp_in perp_in_right_comm perp_in_sym)
  ultimately show ?thesis
    by blast
qed

lemma l13_8:
  assumes "U \<noteq> PO" and
    "V \<noteq> PO" and
    "Col PO P Q" and
    "Col PO U V" and
    "Per P U PO" and
    "Per Q V PO"
  shows "PO Out P Q \<longleftrightarrow> PO Out U V"
  by (smt Out_def assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) l8_2 not_col_permutation_5 per23_preserves_bet per23_preserves_bet_inv per_distinct_1)

lemma perp_in_rewrite:
  assumes "P PerpAt A B C D"
  shows "P PerpAt A P P C \<or> P PerpAt A P P D \<or> P PerpAt B P P C \<or> P PerpAt B P P D"
  by (metis assms per_perp_in perp_in_distinct perp_in_per_1 perp_in_per_3 perp_in_per_4)

lemma perp_out_acute:
  assumes "B Out A C'" and
    "A B Perp C C'"
  shows "Acute A B C"
proof -
  have "A \<noteq> B"
    using assms(1) out_diff1 by auto
  have "C' \<noteq> B"
    using Out_def assms(1) by auto
  then have "B C' Perp C C'"
    by (metis assms(1) assms(2) out_col perp_col perp_comm perp_right_comm)
  then have "Per C C' B"
    using Perp_cases perp_per_2 by blast
  then have "Acute C' C B \<and> Acute C' B C"
    by (metis \<open>C' \<noteq> B\<close> assms(2) l11_43 perp_not_eq_2)
  have "C \<noteq> B"
    using \<open>B C' Perp C C'\<close> l8_14_1 by auto
  show ?thesis
  proof -
    have "B Out A C'"
      by (simp add: assms(1))
    moreover have "B Out C C"
      by (simp add: \<open>C \<noteq> B\<close> out_trivial)
    moreover have "Acute C' B C"
      by (simp add: \<open>Acute C' C B \<and> Acute C' B C\<close>)
    ultimately show ?thesis
      using acute_out2__acute by auto
  qed
qed

lemma perp_bet_obtuse:
  assumes "B \<noteq> C'" and
    "A B Perp C C'" and
    "Bet A B C'"
  shows "Obtuse A B C"
proof -
  have "Acute C' B C"
  proof -
    have "B Out C' C'"
      using assms(1) out_trivial by auto
    moreover have "Col A B C'"
      by (simp add: Col_def assms(3))
    then have "C' B Perp C C'"
      using Out_def assms(2) assms(3) bet_col1 calculation perp_col2 by auto
    ultimately show ?thesis
      using perp_out_acute by blast
  qed
  thus ?thesis
    using acute_bet__obtuse assms(2) assms(3) between_symmetry perp_not_eq_1 by blast
qed

end

subsubsection "Part 1: 2D"

context Tarski_2D
begin

lemma perp_in2__col:
  assumes "P PerpAt A B X Y" and
    "P PerpAt A' B' X Y"
  shows "Col A B A'"
  using cop4_perp_in2__col all_coplanar assms by blast

lemma perp2_trans:
  assumes "P Perp2 A B C D" and
    "P Perp2 C D E F"
  shows "P Perp2 A B E F"
proof -
  obtain X Y where P1: "Col P X Y \<and> X Y Perp A B \<and> X Y Perp C D"
    using Perp2_def assms(1) by blast
  obtain X' Y' where P2: "Col P X' Y' \<and> X' Y' Perp C D \<and> X' Y' Perp E F"
    using Perp2_def assms(2) by blast
  {
    assume "X Y Par X' Y'"
    then have P3: "X Y ParStrict X' Y' \<or> (X \<noteq> Y \<and> X' \<noteq> Y' \<and> Col X X' Y' \<and> Col Y X' Y')"
      using Par_def by blast
    {
      assume "X Y ParStrict X' Y'"
      then have "P Perp2 A B E F"
        using P1 P2 par_not_col by auto
    }
    {
      assume "X \<noteq> Y \<and> X' \<noteq> Y' \<and> Col X X' Y' \<and> Col Y X' Y'"
      then have "P Perp2 A B E F"
        by (meson P1 P2 Perp2_def col_permutation_1 perp_col2)
    }
    then have "P Perp2 A B E F"
      using P3 \<open>X Y ParStrict X' Y' \<Longrightarrow> P Perp2 A B E F\<close> by blast
  }
  {
    assume "\<not> X Y Par X' Y'"
    then have "P Perp2 A B E F"
      using P1 P2 l12_9_2D by blast
  }
  thus ?thesis
    using \<open>X Y Par X' Y' \<Longrightarrow> P Perp2 A B E F\<close> by blast
qed

lemma perp2_par:
  assumes "PO Perp2 A B C D"
  shows "A B Par C D"
  using Perp2_def l12_9_2D Perp_perm assms by blast

end

subsubsection "Part 2: length"

context Tarski_neutral_dimensionless

begin

lemma lg_exists:
  "\<exists> l. (QCong l \<and> l A B)"
  using QCong_def cong_pseudo_reflexivity by blast

lemma lg_cong:
  assumes "QCong l" and
    "l A B" and
    "l C D"
  shows "Cong A B C D"
  by (metis QCong_def assms(1) assms(2) assms(3) cong_inner_transitivity)

lemma lg_cong_lg:
  assumes "QCong l" and
    "l A B" and
    "Cong A B C D"
  shows "l C D"
  by (metis QCong_def assms(1) assms(2) assms(3) cong_transitivity)

lemma lg_sym:
  assumes "QCong l"
    and "l A B"
  shows "l B A"
  using assms(1) assms(2) cong_pseudo_reflexivity lg_cong_lg by blast

lemma ex_points_lg:
  assumes "QCong l"
  shows "\<exists> A B. l A B"
  using QCong_def assms cong_pseudo_reflexivity by fastforce

lemma is_len_cong:
  assumes "TarskiLen A B l" and
    "TarskiLen C D l"
  shows "Cong A B C D"
  using TarskiLen_def assms(1) assms(2) lg_cong by auto

lemma is_len_cong_is_len:
  assumes "TarskiLen A B l" and
    "Cong A B C D"
  shows "TarskiLen C D l"
  using TarskiLen_def assms(1) assms(2) lg_cong_lg by fastforce

lemma not_cong_is_len:
  assumes "\<not> Cong A B C D" and
    "TarskiLen A B l"
  shows "\<not> l C D"
  using TarskiLen_def assms(1) assms(2) lg_cong by auto

lemma not_cong_is_len1:
  assumes "\<not> Cong A B C D"
    and "TarskiLen A B l"
  shows "\<not> TarskiLen C D l"
  using assms(1) assms(2) is_len_cong by blast

lemma lg_null_instance:
  assumes "QCongNull l"
  shows "l A A"
  by (metis QCongNull_def QCong_def assms cong_diff cong_trivial_identity)

lemma lg_null_trivial:
  assumes "QCong l"
    and "l A A"
  shows "QCongNull l"
  using QCongNull_def assms(1) assms(2) by auto

lemma lg_null_dec:
  (*assumes "QCong l" *)
  shows "QCongNull l \<or> \<not> QCongNull l"
  by simp

lemma ex_point_lg:
  assumes "QCong l"
  shows "\<exists> B. l A B"
  by (metis QCong_def assms not_cong_3412 segment_construction)

lemma ex_point_lg_out:
  assumes "A \<noteq> P" and
    "QCong l" and
    "\<not> QCongNull l"
  shows "\<exists> B. (l A B \<and> A Out B P)"
proof -
  obtain X Y where P1: "\<forall> X0 Y0. (Cong X Y X0 Y0 \<longleftrightarrow> l X0 Y0)"
    using QCong_def assms(2) by auto
  then have "l X Y"
    using cong_reflexivity by auto
  then have "X \<noteq> Y"
    using assms(2) assms(3) lg_null_trivial by auto
  then obtain B where "A Out P B \<and> Cong A B X Y"
    using assms(1) segment_construction_3 by blast
  thus ?thesis
    using Cong_perm Out_cases P1 by blast
qed

lemma ex_point_lg_bet:
  assumes "QCong l"
  shows "\<exists> B. (l M B \<and> Bet A M B)"
proof -
  obtain X Y where P1: "\<forall> X0 Y0. (Cong X Y X0 Y0 \<longleftrightarrow> l X0 Y0)"
    using QCong_def assms by auto
  then have "l X Y"
    using cong_reflexivity by blast
  obtain B where "Bet A M B \<and> Cong M B X Y"
    using segment_construction by blast
  thus ?thesis
    using Cong_perm P1 by blast
qed

lemma ex_points_lg_not_col:
  assumes "QCong l"
    and "\<not> QCongNull l"
  shows "\<exists> A B. (l A B \<and> \<not> Col A B P)"
proof -
  have  "\<exists> B::'p. A \<noteq> B"
    using another_point by blast
  then obtain A::'p where "P \<noteq> A"
    by metis
  then obtain Q where "\<not> Col P A Q"
    using not_col_exists by auto
  then have "A \<noteq> Q"
    using col_trivial_2 by auto
  then obtain B where "l A B \<and> A Out B Q"
    using assms(1) assms(2) ex_point_lg_out by blast
  thus ?thesis
    by (metis \<open>\<not> Col P A Q\<close> col_transitivity_1 not_col_permutation_1 out_col out_diff1)
qed

lemma ex_eql:
  assumes  "\<exists> A B. (TarskiLen A B l1 \<and> TarskiLen A B l2)"
  shows "l1 = l2"
proof -
  obtain A B where P1: "TarskiLen A B l1 \<and> TarskiLen A B l2"
    using assms by auto
  have "\<forall> A0 B0. (l1 A0 B0 \<longrightarrow> l2 A0 B0)"
    by (metis TarskiLen_def \<open>TarskiLen A B l1 \<and> TarskiLen A B l2\<close> lg_cong lg_cong_lg)
  have "\<forall> A0 B0. (l1 A0 B0 \<longleftrightarrow> l2 A0 B0)"
  proof -
    have "\<forall> A0 B0. (l1 A0 B0 \<longrightarrow> l2 A0 B0)"
      by (metis TarskiLen_def \<open>TarskiLen A B l1 \<and> TarskiLen A B l2\<close> lg_cong lg_cong_lg)
    moreover have "\<forall> A0 B0. (l2 A0 B0 \<longrightarrow> l1 A0 B0)"
      by (metis TarskiLen_def \<open>TarskiLen A B l1 \<and> TarskiLen A B l2\<close> lg_cong lg_cong_lg)
    ultimately show ?thesis by blast
  qed
  thus ?thesis by blast
qed

lemma all_eql:
  assumes "TarskiLen A B l1" and
    "TarskiLen A B l2"
  shows "l1 = l2"
  using assms(1) assms(2) ex_eql by auto

lemma null_len:
  assumes "TarskiLen A A la" and
    "TarskiLen B B lb"
  shows "la = lb"
  by (metis TarskiLen_def all_eql assms(1) assms(2) lg_null_instance lg_null_trivial)

lemma eqL_equivalence:
  assumes "QCong la" and
    "QCong lb" and
    "QCong lc"
  shows "la = la \<and> (la = lb \<longrightarrow> lb = la) \<and> (la = lb \<and> lb = lc \<longrightarrow> la = lc)"
  by simp

lemma ex_lg:
  "\<exists> l. (QCong l \<and> l A B)"
  by (simp add: lg_exists)

lemma lg_eql_lg:
  assumes "QCong l1" and
    "l1 = l2"
  shows "QCong l2"
  using assms(1) assms(2) by auto

lemma ex_eqL:
  assumes "QCong l1" and
    "QCong l2" and
    "\<exists> A B. (l1 A B \<and> l2 A B)"
  shows "l1 = l2"
  using TarskiLen_def all_eql assms(1) assms(2) assms(3) by auto

subsubsection "Part 3 : angles"

lemma ang_exists:
  assumes "A \<noteq> B" and
    "C \<noteq> B"
  shows "\<exists> a. (QCongA a \<and> a A B C)"
proof -
  have "A B C CongA A B C"
    by (simp add: assms(1) assms(2) conga_refl)
  thus ?thesis
    using QCongA_def assms(1) assms(2) by auto
qed

lemma ex_points_eng:
  assumes "QCongA a"
  shows "\<exists> A B C. (a A B C)"
proof -
  obtain A B C where "A \<noteq> B \<and> C \<noteq> B \<and> (\<forall> X Y Z. (A B C CongA X Y Z \<longleftrightarrow> a X Y Z))"
    using QCongA_def assms by auto
  thus ?thesis
    using conga_pseudo_refl by blast
qed

lemma ang_conga:
  assumes "QCongA a" and
    "a A B C" and
    "a A' B' C'"
  shows "A B C CongA A' B' C'"
proof -
  obtain A0 B0 C0 where "A0 \<noteq> B0 \<and> C0 \<noteq> B0 \<and> (\<forall> X Y Z. (A0 B0 C0 CongA X Y Z \<longleftrightarrow> a X Y Z))"
    using QCongA_def assms(1) by auto
  thus ?thesis
    by (meson assms(2) assms(3) not_conga not_conga_sym)
qed

lemma is_ang_conga:
  assumes "A B C Ang a" and
    "A' B' C' Ang a"
  shows "A B C CongA A' B' C'"
  using Ang_def ang_conga assms(1) assms(2) by auto

lemma is_ang_conga_is_ang:
  assumes "A B C Ang a" and
    "A B C CongA A' B' C'"
  shows "A' B' C' Ang a"
proof -
  have "QCongA a"
    using Ang_def assms(1) by auto
  then obtain A0 B0 C0 where "A0 \<noteq> B0 \<and> C0 \<noteq> B0 \<and> (\<forall> X Y Z. (A0 B0 C0 CongA X Y Z \<longleftrightarrow> a X Y Z))"
    using QCongA_def by auto
  thus ?thesis
    by (metis Ang_def assms(1) assms(2) not_conga)
qed

lemma not_conga_not_ang:
  assumes "QCongA a" and
    "\<not> A B C CongA A' B' C'" and
    "a A B C"
  shows "\<not> a A' B' C'"
  using ang_conga assms(1) assms(2) assms(3) by auto

lemma not_conga_is_ang:
  assumes "\<not> A B C CongA A' B' C'" and
    "A B C Ang a"
  shows "\<not> a A' B' C'"
  using Ang_def ang_conga assms(1) assms(2) by auto

lemma not_cong_is_ang1:
  assumes "\<not> A B C CongA A' B' C'" and
    "A B C Ang a"
  shows "\<not> A' B' C' Ang a"
  using assms(1) assms(2) is_ang_conga by blast

lemma ex_eqa:
  assumes "\<exists> A B C.(A B C Ang a1 \<and> A B C Ang a2)"
  shows "a1 = a2"
proof -
  obtain A B C where P1: "A B C Ang a1 \<and> A B C Ang a2"
    using assms by auto
  {
    fix x y z
    assume "a1 x y z"
    then have "x y z Ang a1"
      using Ang_def assms by auto
    then have "x y z CongA A B C"
      using P1 not_cong_is_ang1 by blast
    then have "x y z Ang a2"
      using P1 is_ang_conga_is_ang not_conga_sym by blast
    then have "a2 x y z"
      using Ang_def assms by auto
  }
  {
    fix x y z
    assume "a2 x y z"
    then have "x y z Ang a2"
      using Ang_def assms by auto
    then have "x y z CongA A B C"
      using P1 not_cong_is_ang1 by blast
    then have "x y z Ang a1"
      using P1 is_ang_conga_is_ang not_conga_sym by blast
    then have "a1 x y z"
      using Ang_def assms by auto
  }
  then have "\<forall> x y z. (a1 x y z) \<longleftrightarrow> (a2 x y z)"
    using \<open>\<And>z y x. a1 x y z \<Longrightarrow> a2 x y z\<close> by blast
  then have "\<And>x y. (\<forall> z. (a1 x y) z = (a2 x y) z)"
    by simp
  then have "\<And> x y. (a1 x y) = (a2 x y)" using fun_eq_iff by auto
  thus ?thesis using fun_eq_iff by auto
qed

lemma all_eqa:
  assumes "A B C Ang a1" and
    "A B C Ang a2"
  shows "a1 = a2"
  using assms(1) assms(2) ex_eqa by blast

lemma is_ang_distinct:
  assumes "A B C Ang a"
  shows "A \<noteq> B \<and> C \<noteq> B"
  using assms conga_diff1 conga_diff2 is_ang_conga by blast

lemma null_ang:
  assumes "A B A Ang a1" and
    "C D C Ang a2"
  shows "a1 = a2"
  using all_eqa assms(1) assms(2) conga_trivial_1 is_ang_conga_is_ang is_ang_distinct by auto

lemma flat_ang:
  assumes "Bet A B C" and
    "Bet A' B' C'" and
    "A B C Ang a1" and
    "A' B' C' Ang a2"
  shows "a1  = a2"
proof -
  have "A B C Ang a2"
  proof -
    have "A' B' C' Ang a2"
      by (simp add: assms(4))
    moreover have "A' B' C' CongA A B C"
      by (metis assms(1) assms(2) assms(3) calculation conga_line is_ang_distinct)
    ultimately show ?thesis
      using is_ang_conga_is_ang by blast
  qed
  then show ?thesis
    using assms(3) all_eqa by auto
qed

lemma ang_distinct:
  assumes "QCongA a" and
    "a A B C"
  shows "A \<noteq> B \<and> C \<noteq> B"
proof -
  have "A B C Ang a"
    by (simp add: Ang_def assms(1) assms(2))
  thus ?thesis
    using is_ang_distinct by auto
qed

lemma ex_ang:
  assumes "B \<noteq> A" and
    "B \<noteq> C"
  shows "\<exists> a. (QCongA a \<and> a A B C)"
  using ang_exists assms(1) assms(2) by auto

lemma anga_exists:
  assumes "A \<noteq> B" and
    "C \<noteq> B" and
    "Acute A B C"
  shows "\<exists> a. (QCongAAcute a \<and> a A B C)"
proof -
  have "A B C CongA A B C"
    by (simp add: assms(1) assms(2) conga_refl)
  thus ?thesis
    using assms(1) QCongAAcute_def assms(3) by blast
qed

lemma anga_is_ang:
  assumes "QCongAAcute a"
  shows "QCongA a"
proof -
  obtain A0 B0 C0 where P1: "Acute A0 B0 C0 \<and> (\<forall> X Y Z.(A0 B0 C0 CongA X Y Z \<longleftrightarrow> a X Y Z))"
    using QCongAAcute_def assms by auto
  thus ?thesis
    using QCongA_def by (metis acute_distincts)
qed

lemma ex_points_anga:
  assumes "QCongAAcute a"
  shows "\<exists> A B C. a A B C"
  by (simp add: anga_is_ang assms ex_points_eng)

lemma anga_conga:
  assumes "QCongAAcute a" and
    "a A B C" and
    "a A' B' C'"
  shows "A B C CongA A' B' C'"
  by (meson Tarski_neutral_dimensionless.ang_conga Tarski_neutral_dimensionless_axioms anga_is_ang assms(1) assms(2) assms(3))

lemma is_anga_to_is_ang:
  assumes "A B C AngAcute a"
  shows "A B C Ang a"
  using AngAcute_def Ang_def anga_is_ang assms by auto

lemma is_anga_conga:
  assumes "A B C AngAcute a" and
    "A' B' C' AngAcute a"
  shows "A B C CongA A' B' C'"
  using AngAcute_def anga_conga assms(1) assms(2) by auto

lemma is_anga_conga_is_anga:
  assumes "A B C AngAcute a" and
    "A B C CongA A' B' C'"
  shows "A' B' C' AngAcute a"
  using Tarski_neutral_dimensionless.AngAcute_def Tarski_neutral_dimensionless.Ang_def Tarski_neutral_dimensionless.is_ang_conga_is_ang Tarski_neutral_dimensionless_axioms assms(1) assms(2) is_anga_to_is_ang by fastforce

lemma not_conga_is_anga:
  assumes "\<not> A B C CongA A' B' C'" and
    "A B C AngAcute a"
  shows "\<not> a A' B' C'"
  using AngAcute_def anga_conga assms(1) assms(2) by auto

lemma not_cong_is_anga1:
  assumes "\<not> A B C CongA A' B' C'" and
    "A B C AngAcute a"
  shows "\<not> A' B' C' AngAcute a"
  using assms(1) assms(2) is_anga_conga by auto

lemma ex_eqaa:
  assumes "\<exists> A B C. (A B C AngAcute a1 \<and> A B C AngAcute a2)"
  shows "a1 = a2"
  using all_eqa assms is_anga_to_is_ang by blast

lemma all_eqaa:
  assumes "A B C AngAcute a1" and
    "A B C AngAcute a2"
  shows "a1 = a2"
  using assms(1) assms(2) ex_eqaa by blast

lemma is_anga_distinct:
  assumes "A B C AngAcute a"
  shows "A \<noteq> B \<and> C \<noteq> B"
  using assms is_ang_distinct is_anga_to_is_ang by blast

lemma null_anga:
  assumes "A B A AngAcute a1" and
    "C D C AngAcute a2"
  shows "a1 = a2"
  using assms(1) assms(2) is_anga_to_is_ang null_ang by blast

lemma anga_distinct:
  assumes "QCongAAcute a" and
    "a A B C"
  shows "A \<noteq> B \<and> C \<noteq> B"
  using ang_distinct anga_is_ang assms(1) assms(2) by blast

lemma out_is_len_eq:
  assumes "A Out B C" and
    "TarskiLen A B l" and
    "TarskiLen A C l"
  shows "B = C"
  using Out_def assms(1) assms(2) assms(3) between_cong not_cong_is_len1 by fastforce

lemma out_len_eq:
  assumes "QCong l" and
    "A Out B C" and
    "l A B" and
    "l A C"
  shows "B = C" using out_is_len_eq
  using TarskiLen_def assms(1) assms(2) assms(3) assms(4) by auto

lemma ex_anga:
  assumes "Acute A B C"
  shows "\<exists> a. (QCongAAcute a \<and> a A B C)"
  using acute_distincts anga_exists assms by blast

lemma not_null_ang_ang:
  assumes "QCongAnNull a"
  shows "QCongA a"
  using QCongAnNull_def assms by blast

lemma not_null_ang_def_equiv:
  "QCongAnNull a \<longleftrightarrow> (QCongA a \<and> (\<exists> A B C. (a A B C \<and>  \<not> B Out A C)))"
proof -
  {
    assume "QCongAnNull a"
    have "QCongA a \<and> (\<exists> A B C. (a A B C \<and>  \<not> B Out A C))"
      using QCongAnNull_def \<open>QCongAnNull a\<close> ex_points_eng by fastforce
  }
  {
    assume "QCongA a \<and> (\<exists> A B C. (a A B C \<and>  \<not> B Out A C))"
    have "QCongAnNull a"
      by (metis Ang_def QCongAnNull_def Tarski_neutral_dimensionless.l11_21_a Tarski_neutral_dimensionless_axioms \<open>QCongA a \<and> (\<exists>A B C. a A B C \<and> \<not> B Out A C)\<close> not_conga_is_ang)
  }
  thus ?thesis
    using \<open>QCongAnNull a \<Longrightarrow> QCongA a \<and> (\<exists>A B C. a A B C \<and> \<not> B Out A C)\<close> by blast
qed

lemma not_flat_ang_def_equiv:
  "QCongAnFlat a \<longleftrightarrow> (QCongA a \<and> (\<exists> A B C. (a A B C \<and> \<not> Bet A B C)))"
proof -
  {
    assume "QCongAnFlat a"
    then have "QCongA a \<and> (\<exists> A B C. (a A B C \<and> \<not> Bet A B C))"
      using QCongAnFlat_def ex_points_eng by fastforce
  }
  {
    assume "QCongA a \<and> (\<exists> A B C. (a A B C \<and> \<not> Bet A B C))"
    have "QCongAnFlat a"
    proof -
      obtain pp :: 'p and ppa :: 'p and ppb :: 'p where
        f1: "QCongA a \<and> a pp ppa ppb \<and> \<not> Bet pp ppa ppb"
        using \<open>QCongA a \<and> (\<exists>A B C. a A B C \<and> \<not> Bet A B C)\<close> by moura
      then have f2: "\<forall>p pa pb. pp ppa ppb CongA pb pa p \<or> \<not> a pb pa p"
        by (metis (no_types) Ang_def Tarski_neutral_dimensionless.not_cong_is_ang1 Tarski_neutral_dimensionless_axioms)
      then have f3: "\<forall>p pa pb. (Col pp ppa ppb \<or> \<not> a pb pa p) \<or> \<not> Bet pb pa p"
        by (metis (no_types) Col_def Tarski_neutral_dimensionless.ncol_conga_ncol Tarski_neutral_dimensionless_axioms)
      have f4: "\<forall>p pa pb. (\<not> Bet ppa ppb pp \<or> \<not> Bet pb pa p) \<or> \<not> a pb pa p"
        using f2 f1 by (metis Col_def Tarski_neutral_dimensionless.l11_21_a Tarski_neutral_dimensionless_axioms not_bet_and_out not_out_bet)
      have f5: "\<forall>p pa pb. (\<not> Bet ppb pp ppa \<or> \<not> Bet pb pa p) \<or> \<not> a pb pa p"
        using f2 f1 by (metis Col_def Tarski_neutral_dimensionless.l11_21_a Tarski_neutral_dimensionless_axioms not_bet_and_out not_out_bet)
      { assume "Bet ppa ppb pp"
        then have ?thesis
          using f4 f1 QCongAnFlat_def by blast }
      moreover
      { assume "Bet ppb pp ppa"
        then have ?thesis
          using f5 f1 QCongAnFlat_def by blast }
      ultimately show ?thesis
        using f3 f1 Col_def QCongAnFlat_def by blast
    qed
  }
  thus ?thesis
    using \<open>QCongAnFlat a \<Longrightarrow> QCongA a \<and> (\<exists>A B C. a A B C \<and> \<not> Bet A B C)\<close> by blast
qed

lemma ang_const:
  assumes "QCongA a" and
    "A \<noteq> B"
  shows "\<exists> C. a A B C"
proof -
  obtain A0 B0 C0 where "A0 \<noteq> B0 \<and> C0 \<noteq> B0 \<and> (\<forall> X Y Z. (A0 B0 C0 CongA X Y Z \<longrightarrow> a X Y Z))"
    by (metis QCongA_def assms(1))
  then have "(A0 B0 C0 CongA A0 B0 C0) \<longleftrightarrow> a A0 B0 C0"
    by (simp add: conga_refl)
  then have "a A0 B0 C0"
    using \<open>A0 \<noteq> B0 \<and> C0 \<noteq> B0 \<and> (\<forall>X Y Z. A0 B0 C0 CongA X Y Z \<longrightarrow> a X Y Z)\<close> conga_refl by blast
  then show ?thesis
    using \<open>A0 \<noteq> B0 \<and> C0 \<noteq> B0 \<and> (\<forall>X Y Z. A0 B0 C0 CongA X Y Z \<longrightarrow> a X Y Z)\<close> angle_construction_3 assms(2) by blast
qed

lemma ang_sym:
  assumes "QCongA a" and
    "a A B C"
  shows "a C B A"
proof -
  obtain A0 B0 C0 where "A0 \<noteq> B0 \<and> C0 \<noteq> B0 \<and> (\<forall> X Y Z. (A0 B0 C0 CongA X Y Z \<longrightarrow> a X Y Z))"
    by (metis QCongA_def assms(1))
  then show ?thesis
    by (metis Tarski_neutral_dimensionless.ang_conga Tarski_neutral_dimensionless_axioms assms(1) assms(2) conga_left_comm conga_refl not_conga_sym)
qed

lemma ang_not_null_lg:
  assumes "QCongA a" and
    "QCong l" and
    "a A B C" and
    "l A B"
  shows "\<not> QCongNull l"
  by (metis QCongNull_def TarskiLen_def ang_distinct assms(1) assms(3) assms(4) cong_reverse_identity not_cong_is_len)

lemma ang_distincts:
  assumes "QCongA a" and
    "a A B C"
  shows "A \<noteq> B \<and> C \<noteq> B"
  using ang_distinct assms(1) assms(2) by auto

lemma anga_sym:
  assumes "QCongAAcute a" and
    "a A B C"
  shows "a C B A"
  by (simp add: ang_sym anga_is_ang assms(1) assms(2))

lemma anga_not_null_lg:
  assumes "QCongAAcute a" and
    "QCong l" and
    "a A B C" and
    "l A B"
  shows "\<not> QCongNull l"
  using ang_not_null_lg anga_is_ang assms(1) assms(2) assms(3) assms(4) by blast

lemma anga_distincts:
  assumes "QCongAAcute a" and
    "a A B C"
  shows "A \<noteq> B \<and> C \<noteq> B"
  using anga_distinct assms(1) assms(2) by blast

lemma ang_const_o:
  assumes "\<not> Col A B P" and
    "QCongA a" and
    "QCongAnNull a" and
    "QCongAnFlat a"
  shows "\<exists> C. a A B C \<and> A B OS C P"
proof -
  obtain A0 B0 C0 where P1: "A0 \<noteq> B0 \<and> C0 \<noteq> B0 \<and> (\<forall> X Y Z. (A0 B0 C0 CongA X Y Z \<longrightarrow> a X Y Z))"
    by (metis QCongA_def assms(2))
  then have "a A0 B0 C0"
    by (simp add: conga_refl)
  then have T1: "A0 \<noteq> C0"
    using P1 Tarski_neutral_dimensionless.QCongAnNull_def Tarski_neutral_dimensionless_axioms assms(3) out_trivial by fastforce
  have "A \<noteq> B"
    using assms(1) col_trivial_1 by blast
  have "A0 \<noteq> B0 \<and> B0 \<noteq> C0"
    using P1 by auto
  then obtain C where P2: "A0 B0 C0 CongA A B C \<and> (A B OS C P \<or> Col A B C)"
    using angle_construction_2 assms(1) by blast
  then have "a A B C"
    by (simp add: P1)
  have P3: "A B OS C P \<or> Col A B C"
    using P2 by simp
  have P4: "\<forall> A B C. (a A B C \<longrightarrow> \<not> B Out A C)"
    using assms(3) by (simp add: QCongAnNull_def)
  have P5: "\<forall> A B C. (a A B C \<longrightarrow> \<not> Bet A B C)"
    using assms(4) QCongAnFlat_def by auto
  {
    assume "Col A B C"
    have "\<not> B Out A C"
      using P4 by (simp add: \<open>a A B C\<close>)
    have "\<not> Bet A B C"
      using P5 by (simp add: \<open>a A B C\<close>)
    then have "A B OS C P"
      using \<open>Col A B C\<close> \<open>\<not> B Out A C\<close> l6_4_2 by blast
    then have "\<exists> C1. (a A B C1 \<and> A B OS C1 P)"
      using \<open>a A B C\<close> by blast
  }
  then have "\<exists> C1. (a A B C1 \<and> A B OS C1 P)"
    using P3 \<open>a A B C\<close> by blast
  then show ?thesis
    by simp
qed

lemma anga_const:
  assumes "QCongAAcute a" and
    "A \<noteq> B"
  shows "\<exists> C. a A B C"
  using Tarski_neutral_dimensionless.ang_const Tarski_neutral_dimensionless_axioms anga_is_ang assms(1) assms(2) by fastforce

lemma null_anga_null_angaP:
  "QCongANullAcute a \<longleftrightarrow> IsNullAngaP a"
proof -
  have "QCongANullAcute a \<longrightarrow> IsNullAngaP a"
    using IsNullAngaP_def QCongANullAcute_def ex_points_anga by fastforce
  moreover have "IsNullAngaP a \<longrightarrow> QCongANullAcute a"
    by (metis IsNullAngaP_def QCongAnNull_def Tarski_neutral_dimensionless.QCongANullAcute_def Tarski_neutral_dimensionless_axioms anga_is_ang not_null_ang_def_equiv)
  ultimately show ?thesis
    by blast
qed

lemma is_null_anga_out:
  assumes (*"QCongAAcute a" and *)
    "a A B C" and
    "QCongANullAcute a"
  shows "B Out A C"
  using QCongANullAcute_def assms(1) assms(2) by auto

lemma acute_not_bet:
  assumes "Acute A B C"
  shows "\<not> Bet A B C"
  using acute_col__out assms bet_col not_bet_and_out by blast

lemma anga_acute:
  assumes "QCongAAcute a" and
    "a A B C"
  shows "Acute A B C"
  by (smt Tarski_neutral_dimensionless.QCongAAcute_def Tarski_neutral_dimensionless_axioms acute_conga__acute assms(1) assms(2))

lemma not_null_not_col:
  assumes "QCongAAcute a" and
    "\<not> QCongANullAcute a" and
    "a A B C"
  shows "\<not> Col A B C"
proof -
  have "Acute A B C"
    using anga_acute assms(1) assms(3) by blast
  then show ?thesis
    using Tarski_neutral_dimensionless.IsNullAngaP_def Tarski_neutral_dimensionless_axioms acute_col__out assms(1) assms(2) assms(3) null_anga_null_angaP by blast
qed

lemma ang_cong_ang:
  assumes "QCongA a" and
    "a A B C" and
    "A B C CongA A' B' C'"
  shows "a A' B' C'"
  by (metis QCongA_def assms(1) assms(2) assms(3) not_conga)

lemma is_null_ang_out:
  assumes (*"QCongA a" and *)
    "a A B C" and
    "QCongANull a"
  shows "B Out A C"
proof -
  have "a A B C \<longrightarrow> B Out A C"
    using QCongANull_def assms(2) by auto
  then show ?thesis
    by (simp add: assms(1))
qed

lemma out_null_ang:
  assumes "QCongA a" and
    "a A B C" and
    "B Out A C"
  shows "QCongANull a"
  by (metis QCongANull_def QCongAnNull_def assms(1) assms(2) assms(3) not_null_ang_def_equiv)

lemma bet_flat_ang:
  assumes "QCongA a" and
    "a A B C" and
    "Bet A B C"
  shows "AngFlat a"
  by (metis AngFlat_def QCongAnFlat_def assms(1) assms(2) assms(3) not_flat_ang_def_equiv)

lemma out_null_anga:
  assumes "QCongAAcute a" and
    "a A B C" and
    "B Out A C"
  shows "QCongANullAcute a"
  using IsNullAngaP_def assms(1) assms(2) assms(3) null_anga_null_angaP by auto

lemma anga_not_flat:
  assumes "QCongAAcute a"
  shows "QCongAnFlat a"
  by (metis (no_types, lifting) Tarski_neutral_dimensionless.QCongAnFlat_def Tarski_neutral_dimensionless.anga_is_ang Tarski_neutral_dimensionless_axioms assms bet_col is_null_anga_out not_bet_and_out not_null_not_col)

lemma anga_const_o:
  assumes "\<not> Col A B P" and
    "\<not> QCongANullAcute a" and
    "QCongAAcute a"
  shows "\<exists> C. (a A B C \<and> A B OS C P)"
proof -
  have "QCongA a"
    by (simp add: anga_is_ang assms(3))
  moreover  have "QCongAnNull a"
    using QCongANullAcute_def assms(2) assms(3) calculation not_null_ang_def_equiv by auto
  moreover have "QCongAnFlat a"
    by (simp add: anga_not_flat assms(3))
  ultimately show ?thesis
    by (simp add: ang_const_o assms(1))
qed

lemma anga_conga_anga:
  assumes "QCongAAcute a" and
    "a A B C" and
    "A B C CongA A' B' C'"
  shows "a A' B' C'"
  using ang_cong_ang anga_is_ang assms(1) assms(2) assms(3) by blast

lemma anga_out_anga:
  assumes "QCongAAcute a" and
    "a A B C" and
    "B Out A A'" and
    "B Out C C'"
  shows "a A' B C'"
proof -
  have "A B C CongA A' B C'"
    by (simp add: assms(3) assms(4) l6_6 out2__conga)
  thus ?thesis
    using anga_conga_anga assms(1) assms(2) by blast
qed

lemma out_out_anga:
  assumes "QCongAAcute a" and
    "B Out A C" and
    "B' Out A' C'" and
    "a A B C"
  shows "a A' B' C'"
proof -
  have "A B C CongA A' B' C'"
    by (simp add: assms(2) assms(3) l11_21_b)
  thus ?thesis
    using anga_conga_anga assms(1) assms(4) by blast
qed

lemma is_null_all:
  assumes "A \<noteq> B" and
    "QCongANullAcute a"
  shows "a A B A"
proof -
  obtain A0 B0 C0 where "Acute A0 B0 C0 \<and> (\<forall> X Y Z. (A0 B0 C0 CongA X Y Z \<longleftrightarrow> a X Y Z))"
    using QCongAAcute_def QCongANullAcute_def assms(2) by auto
  then have "a A0 B0 C0"
    using acute_distincts conga_refl by blast
  thus ?thesis
    by (smt QCongANullAcute_def assms(1) assms(2) out_out_anga out_trivial)
qed

lemma anga_col_out:
  assumes "QCongAAcute a" and
    "a A B C" and
    "Col A B C"
  shows "B Out A C"
proof -
  have "Acute A B C"
    using anga_acute assms(1) assms(2) by auto
  then have P1: "Bet A B C \<longrightarrow> B Out A C"
    using acute_not_bet by auto
  then have "Bet C A B \<longrightarrow> B Out A C"
    using assms(3) l6_4_2 by auto
  thus ?thesis
    using P1 assms(3) l6_4_2 by blast
qed

lemma ang_not_lg_null:
  assumes "QCong la" and
    "QCong lc" and
    "QCongA a" and
    "la A B" and
    "lc C B" and
    "a A B C"
  shows "\<not> QCongNull la \<and> \<not> QCongNull lc"
  by (metis ang_not_null_lg ang_sym assms(1) assms(2) assms(3) assms(4) assms(5) assms(6))

lemma anga_not_lg_null:
  assumes (*"QCong la" and
  "QCong lc" and*)
    "QCongAAcute a" and
    "la A B" and
    "lc C B" and
    "a A B C"
  shows  "\<not> QCongNull la \<and> \<not> QCongNull lc"
  by (metis QCongNull_def anga_not_null_lg anga_sym assms(1) assms(2) assms(3) assms(4))

lemma anga_col_null:
  assumes "QCongAAcute a" and
    "a A B C" and
    "Col A B C"
  shows "B Out A C \<and> QCongANullAcute a"
  using anga_col_out assms(1) assms(2) assms(3) out_null_anga by blast

lemma eqA_preserves_ang:
  assumes "QCongA a" and
    "a = b"
  shows "QCongA b"
  using assms(1) assms(2) by auto

lemma eqA_preserves_anga:
  assumes "QCongAAcute a" and
    (* "QCongA b" and*)
    "a = b"
  shows "QCongAAcute b"
  using assms(1) assms(2) by auto

section "Some postulates of the parallels"

lemma euclid_5__original_euclid:
  assumes "Euclid5"
  shows "EuclidSParallelPostulate"
proof -
  {
    fix A B C D P Q R
    assume P1: "B C OS A D \<and> SAMS A B C B C D \<and> A B C B C D SumA P Q R \<and> \<not> Bet P Q R"
    obtain M where P2: "M Midpoint B C"
      using midpoint_existence by auto
    obtain D' where P3: "C Midpoint D D'"
      using symmetric_point_construction by auto
    obtain E where P4: "M Midpoint D' E"
      using symmetric_point_construction by auto
    have P5: "A \<noteq> B"
      using P1 os_distincts by blast
    have P6: "B \<noteq> C"
      using P1 os_distincts by blast
    have P7: "C \<noteq> D"
      using P1 os_distincts by blast
    have P10: "M \<noteq> B"
      using P2 P6 is_midpoint_id by auto
    have P11: "M \<noteq> C"
      using P2 P6 is_midpoint_id_2 by auto
    have P13: "C \<noteq> D'"
      using P3 P7 is_midpoint_id_2 by blast
    have P16: "\<not> Col B C A"
      using one_side_not_col123 P1 by blast
    have "B C OS D A"
      using P1 one_side_symmetry by blast
    then have P17: "\<not> Col B C D"
      using one_side_not_col123 P1 by blast
    then have P18: "\<not> Col M C D"
      using P2 Col_perm P11 col_transitivity_2 midpoint_col by blast
    then have P19: "\<not> Col M C D'"
      by (metis P13  P3 Col_perm col_transitivity_2 midpoint_col)
    then have P20: "\<not> Col D' C B"
      by (metis Col_perm P13 P17 P3 col_transitivity_2 midpoint_col)
    then have P21: "\<not> Col M C E"
      by (metis P19 P4 bet_col col2__eq col_permutation_4 midpoint_bet midpoint_distinct_2)
    have P22: "M C D' CongA M B E \<and> M D' C CongA M E B" using P13 l11_49
      by (metis Cong_cases P19 P2 P4 l11_51 l7_13_R1 l7_2 midpoint_cong not_col_distincts)
    have P23: "Cong C D' B E"
      using P11 P2 P4 l7_13_R1 l7_2 by blast
    have P27: "C B TS D D'"
      by (simp add: P13 P17 P3 bet__ts midpoint_bet not_col_permutation_4)
    have P28: "A InAngle C B E"
    proof -
      have "C B A LeA C B E"
      proof -
        have "A B C LeA B C D'"
        proof -
          have "Bet D C D'"
            by (simp add: P3 midpoint_bet)
          then show ?thesis using P1 P7 P13 sams_chara
            by (metis sams_left_comm sams_sym)
        qed
        moreover have "A B C CongA C B A"
          using P5 P6 conga_pseudo_refl by auto
        moreover have "B C D' CongA C B E"
          by (metis CongA_def Mid_cases P2 P22 P4 P6 symmetry_preserves_conga)
        ultimately show ?thesis
          using l11_30 by blast
      qed
      moreover have "C B OS E A"
      proof -
        have "C B TS E D'"
          using P2 P20 P4 l7_2 l9_2 mid_two_sides not_col_permutation_1 by blast
        moreover have "C B TS A D'"
          using P27 \<open>B C OS D A\<close> invert_two_sides l9_8_2 by blast
        ultimately show ?thesis
          using OS_def by blast
      qed
      ultimately show ?thesis
        using lea_in_angle by simp
    qed
    obtain A' where P30: "Bet C A' E \<and> (A' = B \<or> B Out A' A)" using P28 InAngle_def by auto
    {
      assume "A' = B"
      then have "Col D' C B"
        by (metis Col_def P2 P21 P30 P6 col_transitivity_1 midpoint_col)
      then have "False"
        by (simp add: P20)
      then have "\<exists> Y. B Out A Y \<and> C Out D Y" by auto
    }
    {
      assume P31: "B Out A' A"
      have "\<exists> I. BetS D' C I \<and> BetS B A' I"
      proof -
        have P32: "BetS B M C"
          using BetS_def Midpoint_def P10 P11 P2 by auto
        moreover have "BetS E M D'"
          using BetS_def Bet_cases P19 P21 P4 midpoint_bet not_col_distincts by fastforce
        moreover have "BetS C A' E"
        proof -
          have P32A: "C \<noteq> A'"
            using P16 P31 out_col by auto
          {
            assume "A' = E"
            then have P33: "B Out A E"
              using P31 l6_6 by blast
            then have "A B C B C D SumA D' C D"
            proof -
              have "D' C B CongA A B C"
              proof -
                have "D' C M CongA E B M"
                  by (simp add: P22 conga_comm)
                moreover have "C Out D' D'"
                  using P13 out_trivial by auto
                moreover have "C Out B M"
                  using BetSEq Out_cases P32 bet_out_1 by blast
                moreover have "B Out A E"
                  using P33 by auto
                moreover have "B Out C M"
                  using BetSEq Out_def P32 by blast
                ultimately show ?thesis
                  using l11_10 by blast
              qed
              moreover have "D' C B B C D SumA D' C D"
                by (simp add: P27 l9_2 ts__suma_1)
              moreover have "B C D CongA B C D"
                using P6 P7 conga_refl by auto
              moreover have "D' C D CongA D' C D"
                using P13 P7 conga_refl by presburger
              ultimately show ?thesis
                using conga3_suma__suma by blast
            qed
            then have "D' C D CongA P Q R"
              using P1 suma2__conga by auto
            then have "Bet P Q R"
              using Bet_cases P3 bet_conga__bet midpoint_bet by blast
            then have "False" using P1 by simp
          }
          then have "A' \<noteq> E" by auto
          then show ?thesis
            by (simp add: BetS_def P30 P32A)
        qed
        moreover have "\<not> Col B C D'"
          by (simp add: P20 not_col_permutation_3)
        moreover have "Cong B M C M"
          using Midpoint_def P2 not_cong_1243 by blast
        moreover have "Cong E M D' M"
          using Cong_perm Midpoint_def P4 by blast
        ultimately show ?thesis
          using euclid_5_def assms by blast
      qed
      then obtain Y where P34: "Bet D' C Y \<and> BetS B A' Y" using BetSEq by blast
      then have "\<exists> Y. B Out A Y \<and> C Out D Y"
      proof -
        have P35: "B Out A Y"
          by (metis BetSEq Out_def P31 P34 l6_7)
        moreover have "C Out D Y"
        proof -
          have "D \<noteq> C"
            using P7 by auto
          moreover have "Y \<noteq> C"
            using P16 P35 l6_6 out_col by blast
          moreover have "D' \<noteq> C"
            using P13 by auto
          moreover have "Bet D C D'"
            by (simp add: P3 midpoint_bet)
          moreover have "Bet Y C D'"
            by (simp add: Bet_perm P34)
          ultimately show ?thesis
            using l6_2 by blast
        qed
        ultimately show ?thesis by auto
      qed
    }
    then have "\<exists> Y. B Out A Y \<and> C Out D Y"
      using P30 \<open>A' = B \<Longrightarrow> \<exists>Y. B Out A Y \<and> C Out D Y\<close> by blast
  }
  then show ?thesis using euclid_s_parallel_postulate_def  by blast
qed

lemma tarski_s_euclid_implies_euclid_5:
  assumes "TarskiSParallelPostulate"
  shows "Euclid5"
proof -
  {
    fix P Q R S T U
    assume
      P1: "BetS P T Q \<and> BetS R T S \<and> BetS Q U R \<and> \<not> Col P Q S \<and> Cong P T Q T \<and> Cong R T S T"
    have P1A: "BetS P T Q" using P1 by simp
    have P1B: "BetS R T S" using P1 by simp
    have P1C: "BetS Q U R" using P1 by simp
    have P1D: "\<not> Col P Q S" using P1 by simp
    have P1E: "Cong P T Q T" using P1 by simp
    have P1F: "Cong R T S T" using P1 by simp
    obtain V where P2: "P Midpoint R V"
      using symmetric_point_construction by auto
    have P3: "Bet V P R"
      using Mid_cases P2 midpoint_bet by blast
    then obtain W where P4: "Bet P W Q \<and> Bet U W V" using inner_pasch
      using BetSEq P1C by blast
    {
      assume "P = W"
      have "P \<noteq> V"
        by (metis BetSEq Bet_perm Col_def Cong_perm Midpoint_def P1A P1B P1D P1E P1F P2 between_trivial is_midpoint_id_2 l7_9)
      have "Col P Q S"
      proof -
        have f1: "Col V P R"
          by (meson Col_def P3)
        have f2: "Col U R Q"
          by (simp add: BetSEq Col_def P1)
        have f3: "Bet P T Q"
          using BetSEq P1 by fastforce
        have f4: "R = P \<or> Col V P U"
          by (metis (no_types) Col_def P4 \<open>P = W\<close> \<open>P \<noteq> V\<close> l6_16_1)
        have f5: "Col Q P T"
          using f3 by (meson Col_def)
        have f6: "Col T Q P"
          using f3 by (meson Col_def)
        have f7: "Col P T Q"
          using f3 by (meson Col_def)
        have f8: "Col P Q P"
          using Col_def P4 \<open>P = W\<close> by blast
        have "Col R T S"
          by (meson BetSEq Col_def P1)
        then have "T = P \<or> Q = P"
          using f8 f7 f6 f5 f4 f2 f1 by (metis (no_types) BetSEq P1 \<open>P \<noteq> V\<close> colx l6_16_1)
        then show ?thesis
          by (metis BetSEq P1)
      qed
      then have "False"
        by (simp add: P1D)
    }
    then have P5: "P \<noteq> W" by auto
    have "Bet V W U"
      using Bet_cases P4 by auto
    then obtain X Y where P7: "Bet P V X \<and> Bet P U Y \<and> Bet X Q Y"
      using assms(1) P1 P4 P5 tarski_s_parallel_postulate_def by blast
    have "Q S Par P R"
    proof -
      have "Q \<noteq> S"
        using P1D col_trivial_2 by auto
      moreover have "T Midpoint Q P"
        using BetSEq P1A P1E l7_2 midpoint_def not_cong_1243 by blast
      moreover have "T Midpoint S R"
        using BetSEq P1B P1F l7_2 midpoint_def not_cong_1243 by blast
      ultimately show ?thesis
        using l12_17 by auto
    qed
    then have P9: "Q S ParStrict P R"
      using P1D Par_def par_strict_symmetry par_symmetry by blast
    have P10: "Q S TS P Y"
    proof -
      have P10A: "P \<noteq> R"
        using P9 par_strict_distinct by auto
      then have P11: "P \<noteq> X"
        by (metis P2 P7 bet_neq12__neq midpoint_not_midpoint)
      have P12: "\<not> Col X Q S"
      proof -
        have "Q S ParStrict P R"
          by (simp add: P9)
        then have "Col P R X"
          by (metis P2 P3 P7 bet_col between_symmetry midpoint_not_midpoint not_col_permutation_4 outer_transitivity_between)
        then have "P X ParStrict Q S"
          using P9 Par_strict_perm P11 par_strict_col_par_strict by blast
        then show ?thesis
          using par_strict_not_col_2 by auto
      qed
      {
        assume W1: "Col Y Q S"
        have W2: "Q = Y"
          by (metis P12 P7 W1 bet_col bet_col1 colx)
        then have "\<not> Col Q P R"
          using P9 W1 par_not_col by auto
        then have W3: "Q = U"
          by (smt BetS_def Col_def P1C P7 W2 col_transitivity_2)
        then have "False"
          using BetS_def P1C by auto
      }
      then have "\<not> Col Y Q S" by auto
      then have "Q S TS X Y"
        by (metis P7 P12 bet__ts not_col_distincts not_col_permutation_1)
      moreover have "Q S OS X P"
      proof -
        have "P \<noteq> V"
          using P10A P2 is_midpoint_id_2 by blast
        then have "Q S ParStrict P X"
          by (meson Bet_perm P3 P7 P9 P11 bet_col not_col_permutation_4 par_strict_col_par_strict)
        then have "Q S ParStrict X P"
          by (simp add: par_strict_right_comm)
        then show ?thesis
          by (simp add: l12_6)
      qed
      ultimately show ?thesis
        using l9_8_2 by auto
    qed
    then obtain I where W4: "Col I Q S \<and> Bet P I Y"
      using TS_def by blast
    have "\<exists> I. (BetS S Q I \<and> BetS P U I)"
    proof -
      have "BetS P U I"
      proof -
        have "P \<noteq> Y"
          using P10 not_two_sides_id by auto
        have W4A: "Bet P U I"
        proof -
          have W5: "Col P U I"
            using P7 W4 bet_col1 by auto
          {
            assume W6: "Bet U I P"
            have W7: "Q S OS P U"
            proof -
              have "Q S OS R U"
              proof -
                have "\<not> Col Q S R"
                  using P9 par_strict_not_col_4 by auto
                moreover have "Q Out R U"
                  using BetSEq Out_def P1C by blast
                ultimately show ?thesis
                  by (simp add: out_one_side)
              qed
              moreover have "Q S OS P R"
                by (simp add: P9 l12_6)
              ultimately show ?thesis
                using one_side_transitivity by blast
            qed
            have W8: "I Out P U \<or> \<not> Col Q S P"
              by (simp add: P1D not_col_permutation_1)
            have "False"
            proof -
              have "I Out U P"
                using W4 W6 W7 between_symmetry one_side_chara by blast
              then show ?thesis
                using W6 not_bet_and_out by blast
            qed
          }
          {
            assume V1: "Bet I P U"
            have "P R OS I U"
            proof -
              have "P R OS I Q"
              proof -
                {
                  assume "Q = I"
                  then have "Col P Q S"
                    by (metis BetSEq Col_def P1C P7 P9 V1 W4 between_equality outer_transitivity_between par_not_col)
                  then have "False"
                    using P1D by blast
                }
                then have "Q \<noteq> I" by blast
                moreover have "P R ParStrict Q S"
                  using P9 par_strict_symmetry by blast
                moreover have "Col Q S I"
                  using Col_cases W4 by blast
                ultimately show ?thesis
                  using one_side_symmetry par_strict_all_one_side by blast
              qed
              moreover have "P R OS Q U"
              proof -
                have "Q S ParStrict P R"
                  using P9 by blast
                have "R Out Q U \<and> \<not> Col P R Q"
                  by (metis BetSEq Bet_cases Out_def P1C calculation col124__nos)
                then show ?thesis
                  by (metis P7 V1 W4 \<open>Bet U I P \<Longrightarrow> False\<close> between_equality col_permutation_2 not_bet_distincts out_col outer_transitivity_between)
              qed
              ultimately show ?thesis
                using one_side_transitivity by blast
            qed
            then have V2: "P Out I U"
              using P7 W4 bet2__out os_distincts by blast
            then have "Col P I U"
              using V1 not_bet_and_out by blast
            then have "False"
              using V1 V2 not_bet_and_out by blast
          }
          then moreover have "\<not> (Bet U I P \<or> Bet I P U)"
            using \<open>Bet U I P \<Longrightarrow> False\<close> by auto
          ultimately show ?thesis
            using Col_def W5 by blast
        qed
        {
          assume "P = U"
          then have "Col P R Q"
            using BetSEq Col_def P1C by blast
          then have "False"
            using P9 par_strict_not_col_3 by blast
        }
        then have V6: "P \<noteq> U" by auto
        {
          assume "U = I"
          have "Q = U"
          proof -
            have f1: "BetS Q I R"
              using P1C \<open>U = I\<close> by blast
            then have f2: "Col Q I R"
              using BetSEq Col_def by blast
            have f3: "Col I R Q"
              using f1 by (simp add: BetSEq Col_def)
            { assume "R \<noteq> Q"
              moreover
              { assume "(R \<noteq> Q \<and> R \<noteq> I) \<and> \<not> Col I Q R"
                moreover
                { assume "\<exists>p. (R \<noteq> Q \<and> \<not> Col I p I) \<and> Col Q I p"
                  then have "I = Q"
                    using f1 by (metis (no_types) BetSEq Col_def col_transitivity_2) }
                ultimately have "(\<exists>p pa. ((pa \<noteq> I \<and> \<not> Col pa p R) \<and> Col Q I pa) \<and> Col I pa p) \<or> I = Q"
                  using f3 f2 by (metis (no_types) col_transitivity_2) }
              ultimately have "(\<exists>p pa. ((pa \<noteq> I \<and> \<not> Col pa p R) \<and> Col Q I pa) \<and> Col I pa p) \<or> I = Q"
                using f1 by (metis (no_types) BetSEq P9 W4 col_transitivity_2 par_strict_not_col_4) }
            then show ?thesis
              using f2 by (metis P9 W4 \<open>U = I\<close> col_transitivity_2 par_strict_not_col_4)
          qed
          then have "False"
            using BetSEq P1C by blast
        }
        then have "U \<noteq> I" by auto
        then show ?thesis
          by (simp add: W4A V6 BetS_def)
      qed
      moreover have "BetS S Q I"
      proof -
        have "Q R TS S I"
        proof -
          have "Q R TS P I"
          proof -
            have "\<not> Col P Q R"
              using P9 col_permutation_5 par_strict_not_col_3 by blast
            moreover have "\<not> Col I Q R"
            proof -
              {
                assume "Col I Q R"
                then have "Col Q S R"
                proof -
                  have f1: "\<forall>p pa pb. Col p pa pb \<or> \<not> BetS pb p pa"
                    by (meson BetSEq Col_def)
                  then have f2: "Col U I P"
                    using \<open>BetS P U I\<close> by blast
                  have f3: "Col I P U"
                    by (simp add: BetSEq Col_def \<open>BetS P U I\<close>)
                  have f4: "\<forall>p. (U = Q \<or> Col Q p R) \<or> \<not> Col Q U p"
                    by (metis BetSEq Col_def P1C col_transitivity_1)
                  { assume "P \<noteq> Q"
                    moreover
                    { assume "(P \<noteq> Q \<and> U \<noteq> Q) \<and> Col Q P Q"
                      then have "(P \<noteq> Q \<and> U \<noteq> Q) \<and> \<not> Col Q P R"
                        using Col_cases \<open>\<not> Col P Q R\<close> by blast
                      moreover
                      { assume "\<exists>p. ((U \<noteq> Q \<and> P \<noteq> Q) \<and> \<not> Col Q p P) \<and> Col Q P p"
                        then have "U \<noteq> Q \<and> \<not> Col Q P P"
                          by (metis col_transitivity_1)
                        then have "\<not> Col U Q P"
                          using col_transitivity_2 by blast }
                      ultimately have "\<not> Col U Q P \<or> I \<noteq> Q"
                        using f4 f3 by blast }
                    ultimately have "I \<noteq> Q"
                      using f2 f1 by (metis BetSEq P1C col_transitivity_1 col_transitivity_2) }
                  then have "I \<noteq> Q"
                    using BetSEq \<open>BetS P U I\<close> by blast
                  then show ?thesis
                    by (simp add: W4 \<open>Col I Q R\<close> col_transitivity_2)
                qed
                then have "False"
                  using P9 par_strict_not_col_4 by blast
              }
              then show ?thesis by blast
            qed
            moreover have "Col U Q R"
              using BetSEq Bet_cases Col_def P1C by blast
            moreover have "Bet P U I"
              by (simp add: BetSEq \<open>BetS P U I\<close>)
            ultimately show ?thesis
              using TS_def by blast
          qed
          moreover have "Q R OS P S"
          proof -
            have "Q R Par P S"
            proof -
              have "Q \<noteq> R"
                using BetSEq P1 by blast
              moreover have "T Midpoint Q P"
                using BetSEq Bet_cases P1A P1E cong_3421 midpoint_def by blast
              moreover have "T Midpoint R S"
                using BetSEq P1B P1F midpoint_def not_cong_1243 by blast
              ultimately show ?thesis
                using l12_17 by blast
            qed
            then have "Q R ParStrict P S"
              by (simp add: P1D Par_def not_col_permutation_4)
            then show ?thesis
              using l12_6 by blast
          qed
          ultimately show ?thesis
            using l9_8_2 by blast
        qed
        then show ?thesis
          by (metis BetS_def W4 col_two_sides_bet not_col_permutation_2 ts_distincts)
      qed
      ultimately show ?thesis
        by auto
    qed
  }
  then show ?thesis using euclid_5_def by blast
qed

lemma tarski_s_implies_euclid_s_parallel_postulate:
  assumes "TarskiSParallelPostulate"
  shows "EuclidSParallelPostulate"
  by (simp add: assms euclid_5__original_euclid tarski_s_euclid_implies_euclid_5)

theorem tarski_s_euclid_implies_playfair_s_postulate:
  assumes "TarskiSParallelPostulate"
  shows "PlayfairSPostulate"
proof -
  {
    fix A1 A2 B1 B2 P C1 C2
    assume P1: "\<not> Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2"
    have P1A: "\<not> Col P A1 A2"
      by (simp add: P1)
    have P2: "A1 A2 Par B1 B2"
      by (simp add: P1)
    have P3: "Col P B1 B2"
      by (simp add: P1)
    have P4: "A1 A2 Par C1 C2"
      by (simp add: P1)
    have P5: "Col P C1 C2"
      by (simp add: P1)
    have P6: "A1 A2 ParStrict B1 B2"
    proof -
      have "A1 A2 Par B1 B2"
        by (simp add: P1)
      moreover have "Col B1 B2 P"
        using P3 not_col_permutation_2 by blast
      moreover have "\<not> Col A1 A2 P"
        by (simp add: P1A not_col_permutation_1)
      ultimately show ?thesis
        using par_not_col_strict by auto
    qed
    have P7: "A1 A2 ParStrict C1 C2"
    proof -
      have "A1 A2 Par C1 C2"
        by (simp add: P1)
      moreover have "Col C1 C2 P"
        using Col_cases P1 by blast
      moreover have "\<not> Col A1 A2 P"
        by (simp add: P1A not_col_permutation_1)
      ultimately show ?thesis
        using par_not_col_strict by auto
    qed
    {
      assume "\<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2"
      have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'"
      proof -
        have T2: "Coplanar A1 A2 P A1"
          using ncop_distincts by auto
        have T3: "Coplanar A1 A2 B1 B2"
          by (simp add: P1 par__coplanar)
        have T4: "Coplanar A1 A2 C1 C2"
          by (simp add: P7 pars__coplanar)
        have T5: "Coplanar A1 A2 P B1"
          using P1 col_trivial_2 ncop_distincts par__coplanar par_col2_par_bis by blast
        then have T6: "Coplanar A1 A2 P B2"
          using P3 T3 col_cop__cop by blast
        have T7: "Coplanar A1 A2 P C1"
          using P1 T4 col_cop__cop coplanar_perm_1 not_col_permutation_2 par_distincts by blast
        then have T8: "Coplanar A1 A2 P C2"
          using P5 T4 col_cop__cop by blast
        {
          assume "\<not> Col C1 B1 B2"
          moreover have "C1 \<noteq> C2"
            using P1 par_neq2 by auto
          moreover have "Col B1 B2 P"
            using P1 not_col_permutation_2 by blast
          moreover have "Col C1 C2 P"
            using Col_cases P5 by auto
          moreover have "\<not> Col B1 B2 C1"
            using Col_cases calculation(1) by auto
          moreover have "\<not> Col B1 B2 A1"
            using P6 par_strict_not_col_3 by auto
          moreover have "Coplanar B1 B2 C1 A1"
            using Col_cases P1A T5 T2 T6 T7 coplanar_pseudo_trans by blast
          ultimately have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'"
            using cop_not_par_other_side by blast
        }
        {
          assume "\<not> Col C2 B1 B2"
          moreover have "C2 \<noteq> C1"
            using P1 par_neq2 by blast
          moreover have "Col B1 B2 P"
            using Col_cases P3 by auto
          moreover have "Col C2 C1 P"
            using Col_cases P5 by auto
          moreover have "\<not> Col B1 B2 C2"
            by (simp add: calculation(1) not_col_permutation_1)
          moreover have "\<not> Col B1 B2 A1"
            using P6 par_strict_not_col_3 by auto
          moreover have "Coplanar B1 B2 C2 A1"
            using Col_cases P1A T2 T5 T6 T8 coplanar_pseudo_trans by blast
          ultimately have "\<exists> C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'" using cop_not_par_other_side
            by (meson not_col_permutation_4)
        }
        then show ?thesis
          using \<open>\<not> Col C1 B1 B2 \<Longrightarrow> \<exists>C'. Col C1 C2 C' \<and> B1 B2 TS A1 C'\<close> \<open>\<not> Col C1 B1 B2 \<or> \<not> Col C2 B1 B2\<close> by blast
      qed
      then obtain C' where W1: "Col C1 C2 C' \<and> B1 B2 TS A1 C'" by auto
      then have W2: "\<not> Col A1 B1 B2"
        using TS_def by blast
      obtain B where W3: "Col B B1 B2 \<and> Bet A1 B C'"
        using TS_def W1 by blast
      obtain C where W4: "P Midpoint C' C"
        using symmetric_point_construction by blast
      then have W4A: "Bet A1 B C' \<and> Bet C P C'"
        using Mid_cases W3 midpoint_bet by blast
      then obtain D where W5: "Bet B D C \<and> Bet P D A1" using inner_pasch by blast
      have W6: "C' \<noteq> P"
        using P3 TS_def W1 by blast
      then have "A1 A2 Par C' P"
        by (meson P1 W1 not_col_permutation_2 par_col2_par)
      have W9: "A1 A2 ParStrict C' P"
        using Col_cases P5 P7 W1 W6 par_strict_col2_par_strict by blast
      then have W10: "B \<noteq> P"
        by (metis W6 W4A bet_out_1 out_col par_strict_not_col_3)
      have W11: "P \<noteq> C"
        using W6 W4 is_midpoint_id_2 by blast
      {
        assume "P = D"
        then have "False"
          by (metis Col_def P3 W1 W3 W4A W5 W10 W11 col_trivial_2 colx l9_18_R1)
      }
      then have "P \<noteq> D" by auto
      then obtain X Y where W12: "Bet P B X \<and> Bet P C Y \<and> Bet X A1 Y"
        using W5 assms tarski_s_parallel_postulate_def by blast
      then have "P \<noteq> X"
        using W10 bet_neq12__neq by auto
      then have "A1 A2 ParStrict P X"
        by (metis Col_cases P3 P6 W10 W12 W3 bet_col colx par_strict_col2_par_strict)
      then have W15: "A1 A2 OS P X"
        by (simp add: l12_6)
      have "P \<noteq> Y"
        using W11 W12 between_identity by blast
      then have "A1 A2 ParStrict P Y"
        by (metis Col_def W11 W12 W4A W9 col_trivial_2 par_strict_col2_par_strict)
      then have W16: "A1 A2 OS P Y"
        using l12_6 by auto
      have "Col A1 X Y"
        by (simp add: W12 bet_col col_permutation_4)
      then have "A1 Out X Y" using col_one_side_out W15 W16
        using one_side_symmetry one_side_transitivity by blast
      then have "False"
        using W12 not_bet_and_out by blast
    }
    then have "Col C1 B1 B2 \<and> Col C2 B1 B2"
      by auto
  }
  {
    fix A1 A2 B1 B2 P C1 C2
    assume P1: "Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2"
    have "Col C1 B1 B2"
      by (smt P1 l9_10 not_col_permutation_3 not_strict_par2 par_col2_par par_comm par_id_5 par_symmetry ts_distincts)
    moreover have "Col C2 B1 B2"
      by (smt P1 l9_10 not_col_permutation_3 not_strict_par2 par_col2_par par_id_5 par_left_comm par_symmetry ts_distincts)
    ultimately have "Col C1 B1 B2 \<and> Col C2 B1 B2" by auto
  }
  then show ?thesis
    using playfair_s_postulate_def
    by (metis \<open>\<And>P C2 C1 B2 B1 A2 A1. \<not> Col P A1 A2 \<and> A1 A2 Par B1 B2 \<and> Col P B1 B2 \<and> A1 A2 Par C1 C2 \<and> Col P C1 C2 \<Longrightarrow> Col C1 B1 B2 \<and> Col C2 B1 B2\<close>)
qed

end
end
