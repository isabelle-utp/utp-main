theory Channel_Type_Example
  imports Channel_Type
begin

chantype ch_buffer =
  inp :: nat
  outp :: nat
  mod :: bool

thm ch_buffer.codeps

end