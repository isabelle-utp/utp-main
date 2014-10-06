(*  Title:      Uint8_Test.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

theory Uint8_Test imports
  Uint8
  Code_Target_Bits_Int
begin

text {*
  Test that @{typ uint8} is emulated for OCaml via @{typ "8 word"} 
  if @{theory Code_Target_Bits_Int} is imported.
*}

definition test_uint8_emulation :: bool where
  "test_uint8_emulation \<longleftrightarrow> (0xFFF - 0x10 = (0xEF :: uint8))"

export_code test_uint8_emulation checking OCaml?
  -- {* test the other target languages as well *} SML Haskell? Scala

hide_const test_uint8_emulation
hide_fact test_uint8_emulation_def

end
