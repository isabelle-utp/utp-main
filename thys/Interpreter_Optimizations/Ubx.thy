theory Ubx
  imports Global OpUbx Env
    "VeriComp.Language"
begin


section \<open>Unboxed caching\<close>

datatype ('dyn, 'var, 'fun, 'op, 'opinl, 'opubx, 'num, 'bool) instr =
  IPush 'dyn | IPushUbx1 'num | IPushUbx2 'bool |
  IPop |
  ILoad 'var | ILoadUbx type 'var |
  IStore 'var | IStoreUbx type 'var |
  IOp 'op |
  IOpInl 'opinl |
  IOpUbx 'opubx |
  is_jump: ICJump nat |
  is_fun_call: ICall 'fun

locale ubx =
  Fenv: env F_empty F_get F_add F_to_list +
  Henv: env heap_empty heap_get heap_add heap_to_list +
  nary_operations_ubx
    \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy>
    \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll>
    is_true is_false box_ubx1 unbox_ubx1 box_ubx2 unbox_ubx2
    \<UU>\<bb>\<xx>\<OO>\<pp> \<UU>\<bb>\<xx> \<BB>\<oo>\<xx> \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
  for
    \<comment> \<open>Functions environment\<close>
    F_empty and
    F_get :: "'fenv \<Rightarrow> 'fun \<Rightarrow> ('dyn, 'var, 'fun, 'op, 'opinl, 'opubx, 'num, 'bool) instr fundef option" and
    F_add and F_to_list and

    \<comment> \<open>Memory heap\<close>
    heap_empty and
    heap_get :: "'henv \<Rightarrow> 'var \<times> 'dyn \<Rightarrow> 'dyn option" and
    heap_add and heap_to_list and

    \<comment> \<open>Unboxed values\<close>
    is_true :: "'dyn \<Rightarrow> bool" and is_false and
    box_ubx1 and unbox_ubx1 and
    box_ubx2 and unbox_ubx2 and

    \<comment> \<open>n-ary operations\<close>
    \<OO>\<pp> :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn" and \<AA>\<rr>\<ii>\<tt>\<yy> and
    \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> :: "'opinl \<Rightarrow> 'op" and
    \<UU>\<bb>\<xx>\<OO>\<pp> :: "'opubx \<Rightarrow> ('dyn, 'num, 'bool) unboxed list \<Rightarrow> ('dyn, 'num, 'bool) unboxed option" and
    \<UU>\<bb>\<xx> :: "'opinl \<Rightarrow> type option list \<Rightarrow> 'opubx option" and
    \<BB>\<oo>\<xx> :: "'opubx \<Rightarrow> 'opinl" and
    \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>
begin

fun generalize_instr where
  "generalize_instr (IPushUbx1 n) = IPush (box_ubx1 n)" |
  "generalize_instr (IPushUbx2 b) = IPush (box_ubx2 b)" |
  "generalize_instr (ILoadUbx _ x) = ILoad x" |
  "generalize_instr (IStoreUbx _ x) = IStore x" |
  "generalize_instr (IOpUbx opubx) = IOpInl (\<BB>\<oo>\<xx> opubx)" |
  "generalize_instr instr = instr"

fun generalize_fundef where
  "generalize_fundef (Fundef xs ar) = Fundef (map generalize_instr xs) ar"

lemma generalize_instr_idempotent[simp]:
  "generalize_instr (generalize_instr x) = generalize_instr x"
  by (cases x) simp_all

lemma generalize_instr_idempotent_comp[simp]:
  "generalize_instr \<circ> generalize_instr = generalize_instr"
  by fastforce

lemma generalize_fundef_length[simp]: "length (body (generalize_fundef fd)) = length (body fd)"
  by (cases fd) simp

lemma body_generalize_fundef[simp]: "body (generalize_fundef fd) = map generalize_instr (body fd)"
  by (cases fd) simp

lemma arity_generalize_fundef[simp]: "arity (generalize_fundef fd2) = arity fd2"
  by (cases fd2) simp

inductive final where
  "F_get F f = Some fd \<Longrightarrow> pc = length (body fd) \<Longrightarrow> final (State F H [Frame f pc \<Sigma>])"


subsection \<open>Semantics\<close>

inductive step (infix "\<rightarrow>" 55) where
  step_push:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IPush d \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F H (Frame f (Suc pc) (OpDyn d # \<Sigma>) # st)" |

  step_push_ubx1:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IPushUbx1 n \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F H (Frame f (Suc pc) (OpUbx1 n # \<Sigma>) # st)" |

  step_push_ubx2:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IPushUbx2 b \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F H (Frame f (Suc pc) (OpUbx2 b # \<Sigma>) # st)" |

  step_pop:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IPop \<Longrightarrow>
    State F H (Frame f pc (x # \<Sigma>) # st) \<rightarrow> State F H (Frame f (Suc pc) \<Sigma> # st)" |

  step_load:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ILoad x \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> heap_get H (x, i') = Some d \<Longrightarrow>
    State F H (Frame f pc (i # \<Sigma>) # st) \<rightarrow> State F H (Frame f (Suc pc) (OpDyn d # \<Sigma>) # st)" |

  step_load_ubx_hit:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ILoadUbx \<tau> x \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> heap_get H (x, i') = Some d \<Longrightarrow> unbox \<tau> d = Some blob \<Longrightarrow>
    State F H (Frame f pc (i # \<Sigma>) # st) \<rightarrow> State F H (Frame f (Suc pc) (blob # \<Sigma>) # st)" |

  step_load_ubx_miss:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ILoadUbx \<tau> x \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> heap_get H (x, i') = Some d \<Longrightarrow> unbox \<tau> d = None \<Longrightarrow>
    F_add F f (generalize_fundef fd) = F' \<Longrightarrow>
    State F H (Frame f pc (i # \<Sigma>) # st) \<rightarrow> State F' H (box_stack f (Frame f (Suc pc) (OpDyn d # \<Sigma>) # st))" |

  step_store:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IStore x \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> cast_Dyn y = Some d \<Longrightarrow> heap_add H (x, i') d = H' \<Longrightarrow>
    State F H (Frame f pc (i # y # \<Sigma>) # st) \<rightarrow> State F H' (Frame f (Suc pc) \<Sigma> # st)" |

  step_store_ubx:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IStoreUbx \<tau> x \<Longrightarrow>
    cast_Dyn i = Some i' \<Longrightarrow> cast_and_box \<tau> blob = Some d \<Longrightarrow> heap_add H (x, i') d = H' \<Longrightarrow>
    State F H (Frame f pc (i # blob # \<Sigma>) # st) \<rightarrow> State F H' (Frame f (Suc pc) \<Sigma> # st)" |

  step_op:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IOp op \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    traverse cast_Dyn (take ar \<Sigma>) = Some \<Sigma>' \<Longrightarrow>
    \<II>\<nn>\<ll> op \<Sigma>' = None \<Longrightarrow> \<OO>\<pp> op \<Sigma>' = x \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F H (Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>) # st)" |

  step_op_inl:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IOp op \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    traverse cast_Dyn (take ar \<Sigma>) = Some \<Sigma>' \<Longrightarrow>
    \<II>\<nn>\<ll> op \<Sigma>' = Some opinl \<Longrightarrow> \<II>\<nn>\<ll>\<OO>\<pp> opinl \<Sigma>' = x \<Longrightarrow>
    F_add F f (rewrite_fundef_body fd pc (IOpInl opinl)) = F' \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F' H (Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>) # st)" |

  step_op_inl_hit:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IOpInl opinl \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    traverse cast_Dyn (take ar \<Sigma>) = Some \<Sigma>' \<Longrightarrow>
    \<II>\<ss>\<II>\<nn>\<ll> opinl \<Sigma>' \<Longrightarrow> \<II>\<nn>\<ll>\<OO>\<pp> opinl \<Sigma>' = x \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F H (Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>) # st)" |

  step_op_inl_miss:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IOpInl opinl \<Longrightarrow>
    \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    traverse cast_Dyn (take ar \<Sigma>) = Some \<Sigma>' \<Longrightarrow>
    \<not> \<II>\<ss>\<II>\<nn>\<ll> opinl \<Sigma>' \<Longrightarrow> \<II>\<nn>\<ll>\<OO>\<pp> opinl \<Sigma>' = x \<Longrightarrow>
    F_add F f (rewrite_fundef_body fd pc (IOp (\<DD>\<ee>\<II>\<nn>\<ll> opinl))) = F' \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F' H (Frame f (Suc pc) (OpDyn x # drop ar \<Sigma>) # st)" |

  step_op_ubx:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = IOpUbx opubx \<Longrightarrow>
    \<DD>\<ee>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx) = op \<Longrightarrow> \<AA>\<rr>\<ii>\<tt>\<yy> op = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    \<UU>\<bb>\<xx>\<OO>\<pp> opubx (take ar \<Sigma>) = Some x \<Longrightarrow>
    State F H (Frame f pc \<Sigma> # st) \<rightarrow> State F H (Frame f (Suc pc) (x # drop ar \<Sigma>) # st)" |

  step_cjump_true:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ICJump n \<Longrightarrow>
    cast_Dyn y = Some d \<Longrightarrow> is_true d \<Longrightarrow>
    State F H (Frame f pc (y # \<Sigma>) # st) \<rightarrow> State F H (Frame f n \<Sigma> # st)" |

  step_cjump_false:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ICJump n \<Longrightarrow>
    cast_Dyn y = Some d \<Longrightarrow> is_false d \<Longrightarrow>
    State F H (Frame f pc (y # \<Sigma>) # st) \<rightarrow> State F H (Frame f (Suc pc) \<Sigma> # st)" |

  step_fun_call:
    "F_get F f = Some fd \<Longrightarrow> pc < length (body fd) \<Longrightarrow> body fd ! pc = ICall g \<Longrightarrow>
    F_get F g = Some gd \<Longrightarrow> arity gd = ar \<Longrightarrow> ar \<le> length \<Sigma> \<Longrightarrow>
    frame\<^sub>f = Frame f pc \<Sigma> \<Longrightarrow> list_all is_dyn_operand (take ar \<Sigma>) \<Longrightarrow>
    frame\<^sub>g = Frame g 0 (take ar \<Sigma>) \<Longrightarrow>
    State F H (frame\<^sub>f # st) \<rightarrow> State F H (frame\<^sub>g # frame\<^sub>f # st)" |

  step_fun_end:
    "F_get F g = Some gd \<Longrightarrow> arity gd \<le> length \<Sigma>\<^sub>f \<Longrightarrow> pc\<^sub>g = length (body gd) \<Longrightarrow>
    frame\<^sub>g = Frame g pc\<^sub>g \<Sigma>\<^sub>g \<Longrightarrow> frame\<^sub>f = Frame f pc\<^sub>f \<Sigma>\<^sub>f \<Longrightarrow>
    frame\<^sub>f' = Frame f (Suc pc\<^sub>f) (\<Sigma>\<^sub>g @ drop (arity gd) \<Sigma>\<^sub>f) \<Longrightarrow>
    State F H (frame\<^sub>g # frame\<^sub>f # st) \<rightarrow> State F H (frame\<^sub>f' # st)"

theorem step_deterministic: "s1 \<rightarrow> s2 \<Longrightarrow> s1 \<rightarrow> s3 \<Longrightarrow> s2 = s3"
  by (induction rule: step.induct;
      erule step.cases; safe;
      auto dest: is_true_and_is_false_implies_False)

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

sublocale ubx_sem: semantics step final
  using final_finished step_deterministic
  by unfold_locales

inductive load :: "('fenv, 'a, 'fun) prog \<Rightarrow> ('fenv, 'a, ('fun, 'b) frame) state \<Rightarrow> bool" where
  "F_get F main = Some fd \<Longrightarrow> arity fd = 0 \<Longrightarrow>
  load (Prog F H main) (State F H [Frame main 0 []])"

sublocale inca_lang: language step final load
  by unfold_locales

end

end