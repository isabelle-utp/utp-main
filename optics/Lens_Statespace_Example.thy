theory Lens_Statespace_Example
  imports Lenses
begin

statespace myss =
  x :: int
  y :: int

statespace myss2 = myss +
  z :: string

end