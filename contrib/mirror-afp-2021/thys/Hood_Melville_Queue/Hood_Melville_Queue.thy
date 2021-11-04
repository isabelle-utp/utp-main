theory Hood_Melville_Queue
imports
  "HOL-Data_Structures.Queue_Spec"
begin

(* All the possible states a queue can be in *)
datatype 'a status =
  (* front \<ge> rear the queue operates like a normal split queue *)
  Idle
  (* The queue is performing the first step to create the new front *)
  | Rev nat "'a list" "'a list" "'a list" "'a list"
  (* Finishing creating the new front  *)
  | App nat "'a list" "'a list"
  (* The new front is ready *)
  | Done "'a list"

(* A queue with constant time dequeue and enqueue *)
record 'a queue = lenf   :: nat            (* length of the front *)
                  front  :: "'a list"      (* front of the queue *)
                  status :: "'a status"    (* status representing intermediate operations *)
                  rear   :: "'a list"      (* rear of the queue *)
                  lenr   :: nat            (* length of the rear *)

(* exec performs a single step towards creating the new front
   by reversing the rear and appending the front
*)
fun exec :: "'a status \<Rightarrow> 'a status" where
  "exec (Rev ok (x#f) f' (y#r) r') = Rev (ok+1) f  (x#f') r (y#r')"
| "exec (Rev ok []    f' [y]   r') = App ok f' (y#r')"
| "exec (App 0  f'     r')         = Done r' "
| "exec (App ok (x#f') r')         = App (ok-1) f' (x#r')"
| "exec s                          = s"

(* When a deq is performed decreases the number keeping track of
   how many element of the original queue should be used
*)
fun invalidate where
  "invalidate (Rev ok f f' r r') = Rev (ok-1) f f' r r'"
| "invalidate (App 0 f' (x#r'))  = Done r'"
| "invalidate (App ok f' r')     = App (ok-1) f' r'"
| "invalidate s = s"

(* Performs 2 steps and deals with the result *)
fun exec2 :: "'a queue \<Rightarrow> 'a queue" where
"exec2 q =
   (case exec (exec (status q)) of
     Done newf \<Rightarrow> q\<lparr>status := Idle,front := newf\<rparr> |
     newstate  \<Rightarrow> q\<lparr>status := newstate\<rparr>)"

(* Checks if the rear has became greater than the front,
   in which case the rear is cleared and a process to generate
   a new front is started, otherwise the queue functions normally
*)
definition check :: "'a queue \<Rightarrow> 'a queue" where
"check q = (if lenr q \<le> lenf q
            then exec2 q
            else let newstate = Rev 0 (front q) [] (rear q) []
                 in  exec2 (q\<lparr>lenf := lenf q + lenr q, status := newstate, rear := [], lenr := 0\<rparr>))"

(* empty queue *)
definition empty :: "'a queue" where
  "empty = queue.make 0 [] Idle [] 0"

(* Enqueue operation *)
fun enq where
  "enq x q = check (q\<lparr>rear := x#(rear q), lenr := lenr q + 1\<rparr>)"

(* Dequeue opertion *)
fun deq where
  "deq q = check (q\<lparr> lenf  := lenf q - 1
                  , front  := tl (front q)
                  , status := invalidate (status q)\<rparr>)"

(* Computes the "true" front of a queue *)
fun front_list :: "'a queue \<Rightarrow> 'a list" where
  "front_list q = (case status q of
                     Idle   \<Rightarrow> front q
                   | Done f \<Rightarrow> f
                   | Rev ok f f' r r' \<Rightarrow> rev (take ok f') @ f @ rev r @ r'
                   | App ok f' r'     \<Rightarrow> rev (take ok f') @ r')"

(* Rear of the queue in the proper order (oldest element in head) *)
definition rear_list :: "'a queue \<Rightarrow> 'a list" where
  "rear_list = rev o rear"

(* Queue to list projection *)
fun list :: "'a queue \<Rightarrow> 'a list" where
  "list q = front_list q @ rear_list q"

(* Query operation (irrelevant) *)
fun first where
 "first q = hd (front q)"

(* How many applications of exec are needed to reach Idle or Done status *)
fun rem_steps :: "'a status \<Rightarrow> nat" where
  "rem_steps (Rev ok f f' r r') = 2*length f + ok + 2"
| "rem_steps (App ok   f'   r') = ok + 1"
| "rem_steps _ = 0"

(* Status invariants *)
fun st_inv :: "'a status \<Rightarrow> bool" where
  "st_inv (Rev ok f f' r r') = (length f + 1 = length r \<and>
                                      length f' = length r'   \<and>
                                      ok \<le> length f')"
| "st_inv (App ok f' r') = (ok \<le> length f' \<and> length f' < length r')"
| "st_inv _ = True"

fun steps :: "nat \<Rightarrow> 'a status \<Rightarrow> 'a status" where
  "steps n st = (exec ^^ n) st"

lemma rev_steps_app:
  assumes inv: "st_inv (Rev ok f f' r r')"
  shows "steps (length f + 1) (Rev ok f f' r r') = App (length f + ok) (rev f @ f') (rev r @ r')"
proof -
  show ?thesis using inv
  proof (induction f arbitrary: ok f' r r')
    case Nil
    then obtain x where "r = [x]"
      by (metis One_nat_def Suc_length_conv add.right_neutral add_Suc_right length_0_conv st_inv.simps(1))
    then show ?case using Nil by simp
  next
    case (Cons a f)
    then obtain x and xs where "r = x # xs"
      by (metis One_nat_def Suc_length_conv add_Suc_right st_inv.simps(1))
    hence r_x: "r = x # xs" by simp
    then show ?case using Cons Nat.funpow_add by (simp add: Nat.funpow_swap1)
  qed
qed

lemma st_inv_steps:
  assumes inv      : "st_inv s"
  assumes not_idle : "s \<noteq> Idle"
  shows              "\<exists>x. steps (rem_steps s) s = Done x" (is "?reach_done s")
proof -
  let ?steps = "\<lambda>x. steps (rem_steps x)"
  have app_inv: "st_inv (App ok f r) \<Longrightarrow> ?reach_done (App ok f r)"
    for ok f r
  proof (induct f arbitrary: ok r)
    case (Cons a f') then show ?case
      by (induct ok; simp add: Nat.funpow_swap1)
  qed simp
  show ?thesis
  proof (cases s)
    case (App ok f' r')
    then show ?thesis using inv app_inv unfolding App by simp
  next
    case (Rev ok f f' r r')
    have rep_split: "rem_steps (Rev ok f f' r r') = (length f + ok + 1) + (length f + 1)" by simp
    then have split: "\<And>stp. ?steps (Rev ok f f' r r') stp = (steps (length f + ok + 1)) ((steps (length f + 1)) stp) "
      unfolding rep_split Nat.funpow_add steps.simps by simp
    also have f: "st_inv (App (length f + ok) (rev f @ f') (rev r @ r'))"
      using Rev inv by simp
    thus ?thesis using inv f[THEN app_inv]
      unfolding Rev split inv[simplified Rev,THEN rev_steps_app] by simp
  qed (auto simp add: not_idle)
qed

(* Preservation of the status invariants by exec2 *)
lemma st_inv_exec:
  assumes st_inv: "st_inv s"
  shows "st_inv (exec s)"
proof (cases s)
next
  case (Rev ok f f' r r')
  show ?thesis
  proof (cases f)
    case Nil
    then show ?thesis using st_inv unfolding Rev
      by (simp; cases r;cases ok; cases f'; simp)
  next
    case C_a: (Cons a as)
    then obtain x xs where "r = x # xs" using st_inv unfolding Rev Cons
      by (metis One_nat_def length_Suc_conv list.size(4) st_inv.simps(1))
    hence r_x: "r = x # xs" by simp
    then show ?thesis
    proof (cases as)
      case Nil then show ?thesis using st_inv unfolding Rev C_a Nil r_x by (simp; cases xs; simp)
    next
      case (Cons b bs)
      then show ?thesis using st_inv unfolding Rev C_a r_x by (simp; cases xs; simp)
    qed
  qed
next
  case (App ok f r)
  then show ?thesis
  proof (cases ok)
    case (Suc ok')
    then obtain x xs where "f = x # xs" using st_inv unfolding App Suc
      by (metis Suc_le_D Zero_not_Suc list.exhaust list.size(3) st_inv.simps(2))
    then show ?thesis using st_inv unfolding App Suc
      by (cases ok'; cases xs; simp)
  qed simp
qed simp+

(* Preservation of the status invariants by exec2 *)
lemma st_inv_exec2:
  assumes st_inv: "st_inv s"
  shows "st_inv (exec (exec s))"
proof -
  show ?thesis using st_inv st_inv_exec
  by auto
qed

lemma st_inv_invalidate:
  assumes st_inv: "st_inv s"
  shows "st_inv (invalidate s)"
proof (cases s)
next
  case (Rev ok f f' r r')
  show ?thesis using st_inv unfolding Rev by auto
next
  case (App ok f r)
  then show ?thesis 
    using st_inv unfolding App
    by (cases ok; cases r; simp)
qed simp+

(* Queue invariants *)
definition invar where
  "invar q = (lenf q = length (front_list q) \<and>
              lenr q = length (rear_list q)  \<and>
              lenr q \<le> lenf q \<and>
              (case status q of
                 Rev ok f f' r r' \<Rightarrow> 2*lenr q  \<le> length f' \<and> ok \<noteq> 0 
               | App ok f r       \<Rightarrow> 2*lenr q  \<le> length r
               | _ \<Rightarrow> True) \<and>
              rem_steps (status q) \<le> 2*length (front q) \<and>
              (\<exists>rest. front_list q = front q @ rest) \<and>
              (\<forall>x. status q \<noteq> Done x) \<and>
              st_inv (status q))"

(* The empty list satisfies the invariant *)
lemma invar_empty: "invar empty"
  by(simp add: invar_def empty_def make_def rear_list_def)

(* List lemmas *)

lemma tl_rev_take: "\<lbrakk>0 < ok; ok \<le> length f\<rbrakk> \<Longrightarrow> rev (take ok (x # f)) = tl (rev (take ok f)) @ [x]"
by(simp add: rev_take Suc_diff_le drop_Suc tl_drop)

lemma tl_rev_take_Suc:
  "n + 1 \<le> length l \<Longrightarrow> rev (take n l) = tl (rev (take (Suc n) l))"
by(simp add: rev_take tl_drop Suc_diff_Suc flip: drop_Suc)

(* Dequeue operations preserve the invariants *)
lemma invar_deq:
  assumes inv: "invar q"
  shows "invar (deq q)"
proof (cases q)
  case (fields lenf front status rear lenr)
  have pre_inv: "\<exists>rest. front @ rest = front_list q" using inv unfolding fields
    by(simp add: invar_def check_def; cases status; auto simp add: invar_def Let_def rear_list_def)
  have tl_app: "status \<noteq> Idle \<Longrightarrow> \<forall>l. tl front @ l = tl (front @ l)" using inv unfolding fields
    by (simp add: invar_def check_def; cases status; cases front;auto simp add: invar_def Let_def rear_list_def)
  then show ?thesis
  proof (cases status rule: exec.cases)
    case st: (1 ok x f f' y r r')
    then show ?thesis
    proof (cases f)
      case Nil
      have pre: "\<exists>rest. front_list (deq q) = tl front @ rest" using inv pre_inv unfolding fields st Nil
        apply (simp add: invar_def check_def; cases r; simp add: invar_def Let_def rear_list_def)
        apply (erule exE)
        apply (rule_tac x=rest in exI)
        apply (simp add: tl_app st tl_rev_take)
        apply (cases f'; auto)
        done
     then show ?thesis using inv unfolding fields st Nil
       by (simp add: invar_def check_def rear_list_def; cases r; auto simp add: min_absorb2 invar_def rear_list_def Let_def)
    next
      case (Cons a list)
      then show ?thesis using pre_inv inv
        unfolding fields st Nil 
        apply (simp add: invar_def check_def inv ; cases r; simp add: invar_def inv min_absorb2 rear_list_def)
        apply (erule exE)
        apply (rule conjI, force)
        apply (rule_tac x=rest in exI)
        apply (simp add: tl_app st tl_rev_take)
        apply (cases f'; auto)
        done
    qed
  next
    case st: (2 ok f y r)
    then show ?thesis
    proof(cases ok)
      case ok: 0
      then show ?thesis using inv unfolding fields st
        by (simp add: invar_def check_def rear_list_def)
    next
      case (Suc ok')
      obtain fx fs where "f = fx # fs"
        using inv lessI less_le_trans not_less_zero
        unfolding fields st Suc invar_def
        by (metis list.exhaust list.size(3) select_convs(3) st_inv.simps(1))
      hence f_x: "f = fx # fs" by simp
      obtain rx rs where "r = rx # rs"
        using inv lessI less_le_trans not_less_zero
        unfolding fields st Suc invar_def
        by (metis list.exhaust list.size(3) select_convs(3) st_inv.simps(1))
      hence r_x: "r = rx # rs" by simp
      then show ?thesis using pre_inv inv unfolding fields st Suc invar_def rear_list_def r_x f_x
        apply (simp add: check_def; cases ok'; simp add: check_def min_absorb2)       
        apply (erule exE)
        apply (rule conjI, arith)
        apply (rule_tac x=rest in exI)
        apply (simp add: tl_app st tl_rev_take_Suc)
        by (metis Suc_le_length_iff length_take list.sel(3) min_absorb2 n_not_Suc_n rev_is_Nil_conv take_tl tl_Nil tl_append2)        
    qed
  next
    case st: (3 f r)
    show ?thesis using inv unfolding fields st
      by(cases r; simp add: invar_def check_def rear_list_def)
  next
    case st: (4 ok x f r)
    then show ?thesis
    proof(cases ok)
      case 0
      then show ?thesis using inv unfolding fields st invar_def rear_list_def
        by (simp add: check_def)
    next
      case (Suc ok')
      then show ?thesis using pre_inv inv unfolding fields st invar_def rear_list_def Suc
        apply (cases f; cases ok'; simp add: invar_def rear_list_def check_def min_absorb2)
        apply (erule exE)
        apply (rule conjI, arith)
        apply (rule_tac x=rest in exI)
        apply (simp add: tl_app st tl_rev_take_Suc)
        by (metis length_take list.size(3) min.absorb2 nat.distinct(1) rev.simps(1) rev_rev_ident tl_append2)                
    qed
  next
    case st: "5_1"
    then show ?thesis
    proof (cases "lenr \<le> lenf - 1")
      case True
      then show ?thesis using inv unfolding st fields
        by (simp add: check_def rear_list_def invar_def)
    next
      case overflows: False
      then have f_eq_r: "length front = length rear" using inv unfolding st fields
        by (simp add: le_antisym rear_list_def invar_def)
      then show ?thesis
      proof (cases front)
        case Nil
        show ?thesis using inv overflows unfolding st fields Nil
          by (cases rear; auto simp add: rear_list_def check_def Let_def invar_def)
      next
        case C_a : (Cons a as)
        then obtain x xs where "rear = x # xs"
          using inv overflows unfolding st fields Cons invar_def
          by (metis f_eq_r length_Suc_conv C_a)
        hence rear_x: "rear = x # xs" by simp
        then show ?thesis
        proof (cases as)
          case Nil
          then show ?thesis using inv overflows unfolding st fields Nil rear_x C_a
            by (cases xs; simp add: invar_def check_def Let_def rear_list_def)
        next
          case (Cons b bs)
          then show ?thesis using inv overflows unfolding st fields Cons rear_x C_a invar_def
            by (cases xs; cases bs; simp add: check_def Let_def rear_list_def)
        qed
      qed
    qed
  next
    case st: "5_2" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def inv fields st)
  next
    case st: "5_3" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  next
    case st: "5_4" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  next
    case st: "5_5" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  next
    case st: ("5_6" v) then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  qed
qed

(* Enqueue operation preserv the invariants *)
lemma invar_enq:
  assumes inv: "invar q"
  shows "invar (enq x q)"
proof (cases q)
  case (fields lenf front status rear lenr)
  then show ?thesis
  proof(cases status rule: exec.cases)
    case st: (1 ok x f f' y r r')
    then show ?thesis
    proof (cases f)
      case Nil
      then show ?thesis using inv unfolding fields st Nil
        by (simp add: invar_def check_def rear_list_def; cases r; auto simp add: min_absorb2 invar_def rear_list_def Let_def)
    next
      case (Cons a list)
      then show ?thesis using inv check_def rear_list_def
        unfolding fields st Nil invar_def check_def rear_list_def
        by (simp; cases r; auto simp add: min_absorb2 check_def)
    qed
  next
    case st: (2 ok f y r)
    then show ?thesis
    proof(cases ok)
      case ok: 0
      then show ?thesis using inv unfolding fields st
        by (simp add: invar_def check_def rear_list_def)
    next
      case (Suc ok')
      obtain fx fs where "f = fx # fs"
        using inv lessI less_le_trans not_less_zero
        unfolding fields st Suc invar_def
        by (metis list.exhaust list.size(3) select_convs(3) st_inv.simps(1))
      hence f_x: "f = fx # fs" by simp
      obtain rx rs where "r = rx # rs"
        using inv lessI less_le_trans not_less_zero
        unfolding fields st Suc invar_def
        by (metis list.exhaust list.size(3) select_convs(3) st_inv.simps(1))
      hence r_x: "r = rx # rs" by simp
      then show ?thesis using inv unfolding fields st Suc invar_def rear_list_def r_x f_x
        by (simp add: check_def; cases ok'; simp add: check_def min_absorb2)
    qed
  next
    case st: (3 f r)
    then show ?thesis
    proof(cases r)
      case Nil
      then show ?thesis using inv unfolding fields st
        by(simp add:  check_def rear_list_def Let_def invar_def)
    next
      case (Cons a list)
      then show ?thesis using inv unfolding fields st
        by (simp add:  check_def rear_list_def Let_def invar_def)
    qed
  next
    case st: (4 ok x f r)
    then show ?thesis
    proof(cases ok)
      case 0
      then show ?thesis using inv unfolding fields st invar_def rear_list_def
        by (simp add: check_def)
    next
      case (Suc ok')
      then show ?thesis using inv unfolding fields st invar_def rear_list_def Suc
        by (cases f; cases ok'; auto simp add: invar_def rear_list_def check_def min_absorb2)
    qed
  next
    case st: "5_1"
    then show ?thesis
    proof (cases "lenr + 1 \<le> lenf")
      case True
      then show ?thesis using inv unfolding st fields
        by (simp add: check_def rear_list_def invar_def)
    next
      case overflows: False
      then have f_eq_r: "length front = length rear" using inv unfolding st fields
        by (simp add: le_antisym rear_list_def invar_def)
      then show ?thesis
      proof (cases front)
        case Nil
        show ?thesis using inv overflows unfolding st fields Nil
          by (cases rear; auto simp add: rear_list_def check_def Let_def invar_def)
      next
        case C_a : (Cons a as)
        then obtain x xs where "rear = x # xs"
          using inv overflows unfolding st fields Cons invar_def
          by (metis f_eq_r length_Suc_conv C_a)
        hence rear_x: "rear = x # xs" by simp
        then show ?thesis
        proof (cases as)
          case Nil
          then show ?thesis using inv overflows unfolding st fields Nil rear_x C_a
            by (cases xs; simp add: invar_def check_def Let_def rear_list_def)
        next
          case (Cons b bs)
          then show ?thesis using inv overflows unfolding st fields Cons rear_x C_a invar_def
            by (cases xs; cases bs; simp add: check_def Let_def rear_list_def)
        qed
      qed
    qed
  next
    case st: "5_2" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  next
    case st: "5_3" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  next
    case st: "5_4" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  next
    case st: "5_5" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  next
    case st: "5_6" then show ?thesis using inv unfolding fields st
      by (simp add: invar_def)
  qed
qed

(* Correctness proof of the dequeue operation *)
lemma queue_correct_deq :
  assumes inv: "invar q"
  shows "list (deq q) = tl (list q)"
proof (cases q)
  case (fields lenf front status rear lenr)
  have inv_deq: "invar (deq q)" using inv invar_deq by simp
  then show ?thesis
  proof (cases status rule: exec.cases)
    case st: (1 ok x f f' y r r')
    then show ?thesis using inv inv_deq unfolding st fields
      apply (cases f; cases r; simp add: invar_def check_def rear_list_def min_absorb2 tl_rev_take)
      by (metis le_zero_eq length_take list.size(3) min.absorb2 not_le rev_is_Nil_conv tl_append2)+
  next
    case st: (2 ok f y r)
    then show ?thesis
      proof(cases ok)
      case ok: 0
      then show ?thesis using inv unfolding fields st
        by (simp add: invar_def check_def rear_list_def)
    next
      case (Suc ok')
      then show ?thesis using inv inv_deq unfolding fields st Suc invar_def
        apply (cases f; cases r; cases ok'; simp add: check_def min_absorb2 rear_list_def tl_rev_take_Suc)
        by (metis (no_types) length_greater_0_conv less_le_trans old.nat.distinct(2) rev_is_Nil_conv take_eq_Nil tl_append2 zero_less_Suc)
    qed
  next
    case st: (3 f r)
    then show ?thesis using inv inv_deq unfolding st fields
      by (cases f; cases r; simp add: invar_def check_def rear_list_def)
  next
    case st: (4 ok x f r)
    then show ?thesis
    proof(cases ok)
      case 0
      then show ?thesis using inv inv_deq unfolding fields st invar_def rear_list_def
        by (simp add: check_def rear_list_def)
    next
      case (Suc ok')
      then show ?thesis using inv inv_deq unfolding fields st invar_def rear_list_def Suc
        apply (cases f; cases ok'; auto simp add: rear_list_def check_def min_absorb2 tl_rev_take_Suc)
        by (metis Nitpick.size_list_simp(2) length_rev length_take min.absorb2 nat.simps(3) tl_append2)
    qed
  next
    case st: "5_1"
    then show ?thesis
    proof (cases "lenr \<le> lenf - 1")
      case True
      then show ?thesis
        using inv inv_deq Nil_is_rev_conv append_Nil diff_is_0_eq diff_zero length_0_conv
        unfolding st fields
        by (simp add: check_def rear_list_def invar_def; metis  list.sel(2) tl_append2)
    next
      case overflows: False
      then have f_eq_r: "length front = length rear" using inv unfolding st fields
        by (simp add: le_antisym rear_list_def invar_def)
      then show ?thesis
      proof (cases front)
        case Nil
        show ?thesis using inv overflows inv_deq unfolding st fields Nil
          by (cases rear; auto simp add: rear_list_def check_def Let_def invar_def)
      next
        case C_a : (Cons a as)
        then obtain x xs where "rear = x # xs"
          using inv overflows unfolding st fields Cons invar_def
          by (metis f_eq_r length_Suc_conv C_a)
        hence rear_x: "rear = x # xs" by simp
        then show ?thesis
        proof (cases as)
          case Nil
          then show ?thesis using inv overflows unfolding st fields Nil rear_x C_a
            by (cases xs; simp add: invar_def check_def Let_def rear_list_def)
        next
          case (Cons b bs)
          then show ?thesis using inv overflows unfolding st fields Cons rear_x C_a invar_def
            by (cases xs; cases bs; simp add: check_def Let_def rear_list_def)
        qed
      qed
    qed
  next
    case st: "5_2" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  next
    case st: "5_3" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  next
    case st: "5_4" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  next
    case st: "5_5" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  next
    case st: "5_6" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  qed
qed

(* Correctness proof of the enqueue operation *)
lemma queue_correct_enq :
  assumes inv: "invar q"
  shows "list (enq x q) = (list q) @ [x]"
proof (cases q)
  case (fields lenf front status rear lenr)
  have inv_deq: "invar (enq x q)" using inv invar_enq by simp
  then show ?thesis
  proof (cases status rule: exec.cases)
    case st: (1 ok x f f' y r r')
    then show ?thesis using inv inv_deq unfolding st fields
      by (cases f; cases r; simp add: invar_def check_def rear_list_def min_absorb2 tl_rev_take)
  next
    case st: (2 ok f y r)
    then show ?thesis
      proof(cases ok)
      case ok: 0
      then show ?thesis using inv unfolding fields st
        by (simp add: invar_def check_def rear_list_def)
    next
      case (Suc ok')
      then show ?thesis using inv inv_deq unfolding fields st Suc invar_def
        by (cases f; cases r; cases ok'; simp add: check_def min_absorb2 rear_list_def tl_rev_take_Suc)
    qed
  next
    case st: (3 f r)
    then show ?thesis using inv inv_deq unfolding st fields
      by (cases f; cases r; simp add: invar_def check_def rear_list_def)
  next
    case st: (4 ok x f r)
    then show ?thesis
    proof(cases ok)
      case 0
      then show ?thesis using inv inv_deq unfolding fields st invar_def rear_list_def
        by (simp add: check_def rear_list_def)
    next
      case (Suc ok')
      then show ?thesis using inv inv_deq unfolding fields st invar_def rear_list_def Suc
        by (cases f; cases ok'; auto simp add: rear_list_def check_def min_absorb2 tl_rev_take_Suc)
    qed
  next
    case st: "5_1"
    then show ?thesis
    proof (cases "lenr + 1 \<le> lenf")
      case True
      then show ?thesis
        using inv inv_deq Nil_is_rev_conv append_Nil diff_is_0_eq diff_zero length_0_conv
        unfolding st fields
        by (simp add: check_def rear_list_def invar_def; metis  list.sel(2) tl_append2)
    next
      case overflows: False
      then have f_eq_r: "length front = length rear" using inv unfolding st fields
        by (simp add: le_antisym rear_list_def invar_def)
      then show ?thesis
      proof (cases front)
        case Nil
        show ?thesis using inv overflows inv_deq unfolding st fields Nil
          by (cases rear; auto simp add: rear_list_def check_def Let_def invar_def)
      next
        case C_a : (Cons a as)
        then obtain x xs where "rear = x # xs"
          using inv overflows unfolding st fields Cons invar_def
          by (metis f_eq_r length_Suc_conv C_a)
        hence rear_x: "rear = x # xs" by simp
        then show ?thesis
        proof (cases as)
          case Nil
          then show ?thesis using inv overflows unfolding st fields Nil rear_x C_a
            by (cases xs; simp add: invar_def check_def Let_def rear_list_def)
        next
          case (Cons b bs)
          then show ?thesis using inv overflows unfolding st fields Cons rear_x C_a invar_def
            by (cases xs; cases bs; simp add: check_def Let_def rear_list_def)
        qed
      qed
    qed
  next
    case st: "5_2" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  next
    case st: "5_3" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  next
    case st: "5_4" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  next
    case st: "5_5" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  next
    case st: "5_6" then show ?thesis using inv inv_deq unfolding st fields
      by (simp add: invar_def check_def rear_list_def)
  qed
qed

(* Constructive approach *)
datatype 'a action = Deq | Enq 'a

type_synonym 'a actions = "'a action list"

(* Perform a given action on the queue *)
fun do_act :: "'a action \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "do_act Deq q     = deq q"
| "do_act (Enq x) q = enq x q"

(* Create a queue from a list of actions *)
definition qfa :: "'a actions \<Rightarrow> 'a queue" where
  "qfa = (\<lambda>acts. foldr do_act acts empty)"

(* Any queue created from list of actions satisfies the invariants *)
lemma invar_qfa : "invar (qfa l)"
proof(induction l)
  case Nil
  then show ?case by (simp add: qfa_def invar_empty)
next
  case (Cons x xs)
  have qfa_cons: "qfa (x#xs) = do_act x (qfa xs)" by (simp add: qfa_def)
  then show ?case
  proof(cases x)
    case Deq
    then show ?thesis using invar_deq[of "qfa xs"] unfolding qfa_cons
      by (simp add: Cons)
  next
    case (Enq a)
    then show ?thesis using invar_enq[of "qfa xs"] unfolding qfa_cons
      by (simp add: Cons)
  qed
qed

(* Correctness proof *)
lemma qfa_deq_correct: "list (deq (qfa l)) = tl (list (qfa l))"
  using invar_qfa queue_correct_deq by blast

lemma qfa_enq_correct: "list (enq x (qfa l)) = (list (qfa l)) @ [x]"
  by (meson invar_qfa queue_correct_enq)

fun rev_steps :: "('a list \<times> 'a list) \<Rightarrow> ('a list \<times> 'a list)" where
  "rev_steps ((x#xs),ys) = (xs,x#ys)"
| "rev_steps l = l"

lemma first_correct :
  assumes inv:      "invar q"
  assumes not_nil : "list q \<noteq> []"
  shows             "first q = hd (list q)"
proof (cases "front q")
  obtain rest where front_l: "front_list q = front q @ rest"
    using inv
    by (auto simp add: invar_def simp del: front_list.simps)
  case front_nil: Nil
  have rear_nil: "rear_list q = []" using inv unfolding invar_def rear_list_def front_nil
    by (simp; cases "status q"; simp add: front_nil)
  have front_nil: "front_list q = []" using inv unfolding invar_def rear_list_def front_nil
    by (simp; cases "status q"; simp add: front_nil)
  show ?thesis using not_nil unfolding  list.simps rear_nil front_nil
    by simp
next
  case front_cons: (Cons x xs)
  show ?thesis using inv unfolding list.simps first.simps front_cons front_list.simps    
    apply (simp add: invar_def rear_list_def)
    by (metis append_Cons front_cons list.sel(1))
qed

fun is_empty :: "'a queue \<Rightarrow> bool" where
  "is_empty q = (list q = [])"

interpretation HMQ: Queue where
  empty    = empty    and
  enq      = enq      and
  first    = first    and
  deq      = deq      and
  is_empty = is_empty and
  list     = list  and
  invar    = invar
proof (standard, goal_cases)
  case 1 thus ?case
    by (simp add: empty_def make_def rear_list_def)
next
  case 2 thus ?case using queue_correct_enq by simp
next
  case 3 thus ?case using queue_correct_deq by simp
next
  case 4 thus ?case using first_correct by simp
next
  case 5 thus ?case by simp
next
  case 6 thus ?case
    by (simp add: empty_def invar_def make_def rear_list_def)
next
  case 7 thus ?case using invar_enq by simp
next
  case 8 thus ?case using invar_deq by simp
qed

end