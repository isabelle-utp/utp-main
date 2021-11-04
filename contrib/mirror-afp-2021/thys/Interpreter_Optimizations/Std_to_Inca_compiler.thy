theory Std_to_Inca_compiler
  imports Std_to_Inca_simulation
    "VeriComp.Compiler"
begin

fun compile_instr where
  "compile_instr (Std.IPush d) = Inca.IPush d" |
  "compile_instr Std.IPop = Inca.IPop" |
  "compile_instr (Std.ILoad x) = Inca.ILoad x" |
  "compile_instr (Std.IStore x) = Inca.IStore x" |
  "compile_instr (Std.IOp op) = Inca.IOp op" |
  "compile_instr (Std.ICJump n) = Inca.ICJump n" |
  "compile_instr (Std.ICall f) = Inca.ICall f"

fun compile_fundef where
  "compile_fundef (Fundef xs ar) = Fundef (map compile_instr xs) ar"

context std_inca_simulation begin

lemma norm_compile_instr:
  "norm_instr (compile_instr instr) = instr"
by (cases instr) auto

lemma rel_compile_fundef: "rel_fundef norm_eq fd (compile_fundef fd)"
proof (cases fd)
  case (Fundef xs ar)
  then show ?thesis
    by (simp add: list.rel_map list.rel_eq norm_compile_instr)
qed

definition compile_env where
  "compile_env e = Sinca.Fenv.from_list (map (map_prod id compile_fundef) (Fstd_to_list e))"

lemma Finca_get_compile: "Finca_get (compile_env e) x = map_option compile_fundef (Fstd_get e x)"
  using Sinca.Fenv.from_list_correct[symmetric] Sstd.Fenv.to_list_correct
  by (simp add: compile_env_def map_prod_def map_of_map)

lemma rel_fundefs_compile_env: "rel_fundefs (Fstd_get e) (Finca_get (compile_env e))"
  unfolding rel_fundefs_def
  unfolding Finca_get_compile
  unfolding option.rel_map
  by (auto intro: option.rel_refl rel_compile_fundef)

fun compile where
  "compile (Prog F H main) = Some (Prog (compile_env F) H main)"

theorem compile_load:
  assumes "compile p1 = Some p2" and "Sinca.load p2 s2"
  shows "\<exists>s1. Sstd.load p1 s1 \<and> match s1 s2"
proof (cases p1)
  case (Prog F H main)
  then have p2_def: "p2 = Prog (compile_env F) H main"
    using assms(1) by simp

  show ?thesis
    using assms(2) unfolding p2_def
  proof (cases _ s2 rule: Sinca.load.cases)
    case (1 fd')
    let ?s1 = "State F H [Frame main 0 []]"

    from 1 obtain fd where
      Fstd_main: "Fstd_get F main = Some fd" and "fd' = compile_fundef fd"
      using Finca_get_compile by auto
    with 1 have "arity fd = 0"
      by (metis fundef.rel_sel rel_compile_fundef)
    hence "Sstd.load p1 ?s1"
      unfolding Prog
      by (auto intro: Sstd.load.intros[OF Fstd_main])
    moreover have "?s1 \<sim> s2"
      unfolding 1
      using rel_fundefs_compile_env
      by (auto intro!: match.intros)
    ultimately show ?thesis by auto
  qed
qed

sublocale std_to_inca_compiler:
  compiler Sstd.step Sinca.step Sstd.final Sinca.final Sstd.load Sinca.load
    "\<lambda>_ _. False" "\<lambda>_. match" compile
using compile_load
  by unfold_locales auto

theorem compile_complete:
  assumes "Sstd.load p\<^sub>1 s\<^sub>1"
  shows "\<exists>p\<^sub>2 s\<^sub>2. compile p\<^sub>1 = Some p\<^sub>2 \<and> Sinca.load p\<^sub>2 s\<^sub>2 \<and> match s\<^sub>1 s\<^sub>2"
  using assms
  by (auto elim!: Sstd.load.cases
      intro!: match.intros rel_fundefs_compile_env
      simp add: Sinca.load.simps Finca_get_compile rel_fundef_arities[OF rel_compile_fundef])

end

end