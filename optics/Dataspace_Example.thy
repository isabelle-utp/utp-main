theory Dataspace_Example
  imports Dataspace
begin

dataspace C1 = 
  constants c1 :: string c2 :: nat
  assumes a1: "c2 > 2" and a2: "c2 < 5"
  variables x :: string y :: int 
  channels ch1 :: "int \<times> string" ch2 :: int

dataspace C2 =
  constants c3 :: nat
  variables z :: int
  channels ch4 :: int

dataspace C3 = C1 + C2 +
  variables k :: int

end