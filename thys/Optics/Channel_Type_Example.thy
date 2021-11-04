theory Channel_Type_Example
  imports Channel_Type
begin

chantype ch_buffer =
  inp :: unit
  outp :: nat
  mod :: bool

thm ch_buffer.inp_wb_prism

thm ch_buffer.codeps

locale C1
begin

chantype ch_buffer2 =
  inp2 :: unit
  outp2 :: nat
  mod2 :: bool

end

end