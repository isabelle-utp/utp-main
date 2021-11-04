(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>IHOL_IDE\<close>\<close>
theory IHOL_IDE
  imports "IDE_Tools/IDE_Tools"
  keywords "mk_ide" :: thy_defn
    and "rf"
    and "|intro" "|dest" "|elim" 
begin



subsection\<open>Miscellaneous results\<close>
           
lemma PQ_P_Q: "P \<equiv> Q \<Longrightarrow> P \<Longrightarrow> Q" by auto
    


subsection\<open>Import\<close>

ML_file\<open>IDE.ML\<close>

end