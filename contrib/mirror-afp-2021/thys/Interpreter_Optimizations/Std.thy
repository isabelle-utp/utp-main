theory Std
  imports List_util Global Op Env Env_list Dynamic
    "VeriComp.Language"
begin

datatype ('dyn, 'var, 'fun, 'op) instr =
  IPush 'dyn |
  IPop |
  ILoad 'var |
  IStore 'var |
  IOp 'op |
  ICJump nat |
  ICall 'fun

locale std =
  Fenv: env F_empty F_get F_add F_to_list +
  Henv: env heap_empty heap_get heap_add heap_to_list +
  dynval is_true is_false +
  nary_operations \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy>
  for
    F_empty and
    F_get :: "'fenv \<Rightarrow> 'fun \<Rightarrow> ('dyn, 'var, 'fun, 'op) instr fundef option" and
    F_add and F_to_list and
    heap_empty and
    heap_get :: "'henv \<Rightarrow> 'var \<times> 'dyn \<Rightarrow> 'dyn option" and
    heap_add and heap_to_list and
    is_true :: "'dyn \<Rightarrow> bool" and is_false and
    \<OO>\<pp> :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn" and \<AA>\<rr>\<ii>\<tt>\<yy>
begin

inductive final :: "('fenv, 'henv, ('fun, 'dyn) frame) state \<Rightarrow> bool" where
  "F_get F f = Some fd \<Longrightarrow> pc = length (body fd) \<Longrightarrow> final (State F H [Frame f pc \<Sigma>])"

inductive step (infix "\<rightarrow>" 55) where
  step_push:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IPush d \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F H (Frame f (Suc pc) (d # \<Sigma>) # st)" |

  step_pop:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IPop \<Longrightarrow>
    State F H (Frame f pc (d # \<Sigma>) # st) \<rightarrow> State F H (Frame f (Suc pc) \<Sigma> # st)" |

  step_load:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ILoad x \<Longrightarrow>
    heap_get H (x, y) = Some d \<Longrightarrow>
    State F H (Frame f pc (y # \<Sigma>) # st) \<rightarrow> State F H (Frame f (Suc pc) (d # \<Sigma>) # st)" |

  step_store:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IStore x \<Longrightarrow>
    heap_add H (x, y) d = H' \<Longrightarrow>
    State F H (Frame f pc (y # d # \<Sigma>) # st) \<rightarrow> State F H' (Frame f (Suc pc) \<Sigma> # st)" |

  step_op:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IOp op \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow> \<OO>\<pp> op (take ar \<Sigma>) = x \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st)" |

  step_cjump_true:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ICJump n \<Longrightarrow>
    is_true d \<Longrightarrow>
    State F H (Frame f pc (d # \<Sigma>) # st) \<rightarrow> State F H (Frame f n \<Sigma> # st)" |

  step_cjump_false:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ICJump n \<Longrightarrow>
    is_false d \<Longrightarrow>
    State F H (Frame f pc (d # \<Sigma>) # st) \<rightarrow> State F H (Frame f (Suc pc) \<Sigma> # st)" |

  step_fun_call:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ICall g \<Longrightarrow>
    F_get F g = Some gd \<Longrightarrow> arity gd \<le> length \<Sigma> \<Longrightarrow>
    frame\<^sub>f = Frame f pc \<Sigma> \<Longrightarrow> frame\<^sub>g = Frame g 0 (take (arity gd) \<Sigma>) \<Longrightarrow>
    State F H (frame\<^sub>f # st) \<rightarrow> State F H (frame\<^sub>g # frame\<^sub>f # st)" |

  step_fun_end:
    "F_get F g = Some gd \<Longrightarrow> arity gd \<le> length \<Sigma>\<^sub>f \<Longrightarrow> pc\<^sub>g = length (body gd) \<Longrightarrow>
    frame\<^sub>g = Frame g pc\<^sub>g \<Sigma>\<^sub>g \<Longrightarrow> frame\<^sub>f = Frame f pc\<^sub>f \<Sigma>\<^sub>f \<Longrightarrow>
    frame\<^sub>f' = Frame f (Suc pc\<^sub>f) (\<Sigma>\<^sub>g @ drop (arity gd) \<Sigma>\<^sub>f) \<Longrightarrow>
    State F H (frame\<^sub>g # frame\<^sub>f # st) \<rightarrow> State F H (frame\<^sub>f' # st)"

lemma step_deterministic: "s1 \<rightarrow> s2 \<Longrightarrow> s1 \<rightarrow> s3 \<Longrightarrow> s2 = s3"
  by (induction rule: step.cases;
      auto elim!: step.cases dest: is_true_and_is_false_implies_False)

lemma final_finished: "final s \<Longrightarrow> finished step s"
  unfolding finished_def
proof
  assume "final s" and "\<exists>x. step s x"
  then obtain s' where "step s s'"
    by auto
  thus False
    using \<open>final s\<close>
    by (auto elim!: step.cases final.cases)
qed

sublocale semantics step final
  using final_finished step_deterministic
  by unfold_locales

inductive load :: "('fenv, 'a, 'fun) prog \<Rightarrow> ('fenv, 'a, ('fun, 'b) frame) state \<Rightarrow> bool" where
  "F_get F main = Some fd \<Longrightarrow> arity fd = 0 \<Longrightarrow>
  load (Prog F H main) (State F H [Frame main 0 []])"

sublocale language step final load
  by unfold_locales

end

end