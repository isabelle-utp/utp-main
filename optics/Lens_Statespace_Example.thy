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

thm indeps

end