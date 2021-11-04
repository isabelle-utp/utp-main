theory Lens_Statespace_Example
  imports Lenses
begin

statespace myss =
  x :: int
  y :: int

statespace myss' =
  a :: string

statespace myss2 = myss + myss' +
  z :: string

context myss2
begin

lemma "x \<bowtie> y"
  by (simp)

end

statespace myss3 = myss2 +
  v :: string

text \<open> We can instantiate one of the statespaces with a concrete alphabet type as shown below. \<close>

alphabet myss_c =
  x :: int
  y :: int
  a :: string
  z :: string
  v :: string

lemma "myss3 x y a z v"
  by (simp add: myss'_def myss2_axioms_def myss2_def myss3.intro myss3_axioms.intro myss_def)

end