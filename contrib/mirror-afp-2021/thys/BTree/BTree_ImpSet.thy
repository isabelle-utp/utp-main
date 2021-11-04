theory BTree_ImpSet
  imports
    BTree_Imp
    BTree_Set
begin

section "Imperative Set operations"

subsection "Auxiliary operations"

definition "split_relation xs \<equiv>
   \<lambda>(as,bs) i. i \<le> length xs \<and> as = take i xs \<and> bs = drop i xs"

lemma split_relation_alt: 
  "split_relation as (ls,rs) i = (as = ls@rs \<and> i = length ls)"
  by (auto simp add: split_relation_def)


lemma split_relation_length: "split_relation xs (ls,rs) (length xs) = (ls = xs \<and> rs = [])"
  by (simp add: split_relation_def)

(* auxiliary lemmas on assns *)
(* simp? not sure if it always makes things more easy *)
lemma list_assn_prod_map: "list_assn (A \<times>\<^sub>a B) xs ys = list_assn B (map snd xs) (map snd ys) * list_assn A (map fst xs) (map fst ys)"
  apply(induct "(A \<times>\<^sub>a B)" xs ys rule: list_assn.induct)
     apply(auto simp add: ab_semigroup_mult_class.mult.left_commute ent_star_mono star_aci(2) star_assoc)
  done

(* concrete *)
lemma id_assn_list: "h \<Turnstile> list_assn id_assn (xs::'a list) ys \<Longrightarrow> xs = ys"
  apply(induction "id_assn::('a \<Rightarrow> 'a \<Rightarrow> assn)" xs ys rule: list_assn.induct)
     apply(auto simp add: less_Suc_eq_0_disj pure_def)
  done


lemma snd_map_help:
  "x \<le> length tsi \<Longrightarrow>
       (\<forall>j<x. snd (tsi ! j) = ((map snd tsi)!j))"
  "x < length tsi \<Longrightarrow> snd (tsi!x) = ((map snd tsi)!x)"
  by auto


lemma split_ismeq: "((a::nat) \<le> b \<and> X) = ((a < b \<and> X) \<or> (a = b \<and> X))"
  by auto

lemma split_relation_map: "split_relation as (ls,rs) i \<Longrightarrow> split_relation (map f as) (map f ls, map f rs) i"
  apply(induction as arbitrary: ls rs i)
   apply(auto simp add: split_relation_def take_map drop_Cons')
  apply(metis list.simps(9) take_map)
  done

lemma split_relation_access: "\<lbrakk>split_relation as (ls,rs) i; rs = r#rrs\<rbrakk> \<Longrightarrow> as!i = r"
  by (simp add: split_relation_alt)



lemma index_to_elem_all: "(\<forall>j<length xs. P (xs!j)) = (\<forall>x \<in> set xs. P x)"
  by (simp add: all_set_conv_nth)

lemma index_to_elem: "n < length xs \<Longrightarrow> (\<forall>j<n. P (xs!j)) = (\<forall>x \<in> set (take n xs). P x)"
  by (simp add: all_set_conv_nth)
    (* ----------------- *)

definition split_half :: "('a::heap \<times> 'b::{heap}) pfarray \<Rightarrow> nat Heap"
  where
    "split_half a \<equiv> do {
  l \<leftarrow> pfa_length a;
  return (l div 2)
}"

lemma split_half_rule[sep_heap_rules]: "<
    is_pfa c tsi a
  * list_assn R ts tsi> 
    split_half a
  <\<lambda>i. 
      is_pfa c tsi a
    * list_assn R ts tsi
    * \<up>(i = length ts div 2 \<and>  split_relation ts (BTree_Set.split_half ts) i)>"
  unfolding split_half_def split_relation_def
  apply(rule hoare_triple_preI)
  apply(sep_auto dest!: list_assn_len mod_starD)
  done

subsection "The imperative split locale"

text "This locale extends the abstract split locale,
assuming that we are provided with an imperative program
that refines the abstract split function."


locale imp_split = abs_split: BTree_Set.split split
  for split::
    "('a btree \<times> 'a::{heap,default,linorder}) list \<Rightarrow> 'a
       \<Rightarrow> ('a btree \<times> 'a) list \<times> ('a btree \<times> 'a) list" +
  fixes imp_split:: "('a btnode ref option \<times> 'a::{heap,default,linorder}) pfarray \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes imp_split_rule [sep_heap_rules]:"sorted_less (separators ts) \<Longrightarrow>
   <is_pfa c tsi (a,n)
  * blist_assn k ts tsi> 
    imp_split (a,n) p 
  <\<lambda>i. 
    is_pfa c tsi (a,n)
    * blist_assn k ts tsi
    * \<up>(split_relation ts (split ts p) i)>\<^sub>t"
begin

subsection "Membership"

partial_function (heap) isin :: "'a btnode ref option \<Rightarrow> 'a \<Rightarrow>  bool Heap"
  where
    "isin p x = 
  (case p of
     None \<Rightarrow> return False |
     (Some a) \<Rightarrow> do {
       node \<leftarrow> !a;
       i \<leftarrow> imp_split (kvs node) x;
       tsl \<leftarrow> pfa_length (kvs node);
       if i < tsl then do {
         s \<leftarrow> pfa_get (kvs node) i;
         let (sub,sep) = s in
         if x = sep then
           return True
         else
           isin sub x
       } else
           isin (last node) x
    }
)"

subsection "Insertion"


datatype 'b btupi = 
  T\<^sub>i "'b btnode ref option" |
  Up\<^sub>i "'b btnode ref option" "'b" "'b btnode ref option"

fun btupi_assn where
  "btupi_assn k (abs_split.T\<^sub>i l) (T\<^sub>i li) =
   btree_assn k l li" |
  "btupi_assn k (abs_split.Up\<^sub>i l a r) (Up\<^sub>i li ai ri) =
   btree_assn k l li * id_assn a ai * btree_assn k r ri" |
  "btupi_assn _ _ _ = false"



definition node\<^sub>i :: "nat \<Rightarrow> ('a btnode ref option \<times> 'a) pfarray \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btupi Heap" where
  "node\<^sub>i k a ti \<equiv> do {
    n \<leftarrow> pfa_length a;
    if n \<le> 2*k then do {
      a' \<leftarrow> pfa_shrink_cap (2*k) a;
      l \<leftarrow> ref (Btnode a' ti);
      return (T\<^sub>i (Some l))
    }
    else do {
      b \<leftarrow> (pfa_empty (2*k) :: ('a btnode ref option \<times> 'a) pfarray Heap);
      i \<leftarrow> split_half a;
      m \<leftarrow> pfa_get a i;
      b' \<leftarrow> pfa_drop a (i+1) b;
      a' \<leftarrow> pfa_shrink i a;
      a'' \<leftarrow> pfa_shrink_cap (2*k) a';
      let (sub,sep) = m in do {
        l \<leftarrow> ref (Btnode a'' sub);
        r \<leftarrow> ref (Btnode b' ti);
        return (Up\<^sub>i (Some l) sep (Some r))
      }
    }
}"


partial_function (heap) ins :: "nat \<Rightarrow> 'a \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btupi Heap"
  where
    "ins k x apo = (case apo of
  None \<Rightarrow> 
    return (Up\<^sub>i None x None) |
  (Some ap) \<Rightarrow> do {
    a \<leftarrow> !ap;
    i \<leftarrow> imp_split (kvs a) x;
    tsl \<leftarrow> pfa_length (kvs a);
    if i < tsl then do {
      s \<leftarrow> pfa_get (kvs a) i;
      let (sub,sep) = s in
      if sep = x then
        return (T\<^sub>i apo)
      else do {
        r \<leftarrow> ins k x sub;
        case r of 
          (T\<^sub>i lp) \<Rightarrow> do {
            pfa_set (kvs a) i (lp,sep);
            return (T\<^sub>i apo)
          } |
          (Up\<^sub>i lp x' rp) \<Rightarrow> do {
            pfa_set (kvs a) i (rp,sep);
            if tsl < 2*k then do {
                kvs' \<leftarrow> pfa_insert (kvs a) i (lp,x');
                ap := (Btnode kvs' (last a));
                return (T\<^sub>i apo)
            } else do {
              kvs' \<leftarrow> pfa_insert_grow (kvs a) i (lp,x');
              node\<^sub>i k kvs' (last a)
            }
          }
        }
      }
    else do {
      r \<leftarrow> ins k x (last a);
      case r of 
        (T\<^sub>i lp) \<Rightarrow> do {
          ap := (Btnode (kvs a) lp);
          return (T\<^sub>i apo)
        } |
        (Up\<^sub>i lp x' rp) \<Rightarrow> 
          if tsl < 2*k then do {
            kvs' \<leftarrow> pfa_append (kvs a) (lp,x');
            ap := (Btnode kvs' rp);
            return (T\<^sub>i apo)
          } else do {
            kvs' \<leftarrow> pfa_append_grow' (kvs a) (lp,x');
            node\<^sub>i k kvs' rp
        }
    }
  }
)"


(*fun tree\<^sub>i::"'a up\<^sub>i \<Rightarrow> 'a btree" where
  "tree\<^sub>i (T\<^sub>i sub) = sub" |
  "tree\<^sub>i (Up\<^sub>i l a r) = (Node [(l,a)] r)" 

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a btree \<Rightarrow> 'a btree" where
  "insert k x t = tree\<^sub>i (ins k x t)"
*)

definition insert :: "nat \<Rightarrow> ('a::{heap,default,linorder}) \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option Heap" where
  "insert \<equiv> \<lambda>k x ti. do {
  ti' \<leftarrow> ins k x ti;
  case ti' of
     T\<^sub>i sub \<Rightarrow> return sub |
     Up\<^sub>i l a r \<Rightarrow> do {
        kvs \<leftarrow> pfa_init (2*k) (l,a) 1;
        t' \<leftarrow> ref (Btnode kvs r);
        return (Some t')
      }
}"

subsection "Deletion"

text "Note that the below operations have not been verified to
refine the abstract set operations."


(* rebalance middle tree gets a list of trees, an index pointing to
the position of sub/sep and a last tree *)
definition rebalance_middle_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder}) btnode ref option \<times> 'a) pfarray \<Rightarrow> nat \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode Heap"
  where
    "rebalance_middle_tree \<equiv> \<lambda> k tsi i r_ti. (
  case r_ti of
  None \<Rightarrow> do {
    return (Btnode tsi r_ti)
  } |
  Some p_t \<Rightarrow> do {
      ti \<leftarrow> !p_t;
      (r_sub,sep) \<leftarrow> pfa_get tsi i;
      case r_sub of (Some p_sub) \<Rightarrow>  do {
      sub \<leftarrow> !p_sub;
      l_sub \<leftarrow> pfa_length (kvs sub);
      l_tts \<leftarrow> pfa_length (kvs ti);
      if l_sub \<ge> k \<and> l_tts \<ge> k then do {
        return (Btnode tsi r_ti)
      } else do {
        l_tsi \<leftarrow> pfa_length tsi;
        if l_tsi = i then do {
          mts' \<leftarrow> pfa_append_extend_grow (kvs sub) (last sub,sep) (kvs ti);
          res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (last ti);
          case res_node\<^sub>i of
            T\<^sub>i u \<Rightarrow> return (Btnode tsi u) |
            Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_append tsi (l,a);
              return (Btnode tsi' r)
            }
        } else do {
          (r_rsub,rsep) \<leftarrow> pfa_get tsi (i+1);
          case r_rsub of Some p_rsub \<Rightarrow> do {
            rsub \<leftarrow> !p_rsub;
            mts' \<leftarrow> pfa_append_extend_grow (kvs sub) (last sub,sep) (kvs rsub);
            res_node\<^sub>i \<leftarrow> node\<^sub>i k mts' (last rsub);
            case res_node\<^sub>i of
             T\<^sub>i u \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi (i+1) (u,rsep);              
              tsi'' \<leftarrow> pfa_delete tsi' i;
              return (Btnode tsi'' r_ti)
            } |
             Up\<^sub>i l a r \<Rightarrow> do {
              tsi' \<leftarrow> pfa_set tsi i (l,a);
              tsi'' \<leftarrow> pfa_set tsi' (i+1) (r,rsep);
              return (Btnode tsi'' r_ti)
            }
          }
        }
      }
  }
})
"


definition rebalance_last_tree:: "nat \<Rightarrow> (('a::{default,heap,linorder}) btnode ref option \<times> 'a) pfarray \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode Heap"
  where
    "rebalance_last_tree \<equiv> \<lambda>k tsi ti. do {
   l_tsi \<leftarrow> pfa_length tsi;
   rebalance_middle_tree k tsi (l_tsi-1) ti
}"

partial_function (heap) split_max ::"nat \<Rightarrow> ('a::{default,heap,linorder}) btnode ref option \<Rightarrow> ('a btnode ref option \<times> 'a) Heap"
  where
    "split_max k r_t = (case r_t of Some p_t \<Rightarrow> do {
   t \<leftarrow> !p_t;
   (case t of Btnode tsi r_ti \<Rightarrow>
     case r_ti of None \<Rightarrow> do {
      (sub,sep) \<leftarrow> pfa_last tsi;
      tsi' \<leftarrow> pfa_butlast tsi;
      p_t := Btnode tsi' sub;
      return (Some p_t, sep)
  } |
    _ \<Rightarrow> do {
      (sub,sep) \<leftarrow> split_max k r_ti;
      p_t' \<leftarrow> rebalance_last_tree k tsi sub;
      p_t := p_t';
      return (Some p_t, sep)
  })
})
"

partial_function (heap) del ::"nat \<Rightarrow> 'a \<Rightarrow> ('a::{default,heap,linorder}) btnode ref option \<Rightarrow> 'a btnode ref option Heap"
  where
    "del k x ti = (case ti of None \<Rightarrow> return None |
   Some p \<Rightarrow> do {
   node \<leftarrow> !p;
   i \<leftarrow> imp_split (kvs node) x;
   tsl \<leftarrow> pfa_length (kvs node);
   if i < tsl then do {
     s \<leftarrow> pfa_get (kvs node) i;
     let (sub,sep) = s in
     if x \<noteq> sep then do {
       sub' \<leftarrow> del k x sub;
       kvs' \<leftarrow> pfa_set (kvs node) i (sub',sep);
       node' \<leftarrow> rebalance_middle_tree k kvs' i (last node);
       ti' \<leftarrow> ref node';
       return (Some ti')
      }
     else if sub = None then do{
       pfa_delete (kvs node) i;
       return ti
     }
     else do {
        sm \<leftarrow> split_max k sub;
        kvs' \<leftarrow> pfa_set (kvs node) i sm;
        node' \<leftarrow> rebalance_middle_tree k kvs' i (last node);
        ti' \<leftarrow> ref node';
        return (Some ti')
     }
   } else do {
       t' \<leftarrow> del k x (last node);
       node' \<leftarrow> rebalance_last_tree k (kvs node) t';
       ti' \<leftarrow> ref node';
       return (Some ti')
    }
})
"

partial_function (heap) reduce_root ::"('a::{default,heap,linorder}) btnode ref option \<Rightarrow> 'a btnode ref option Heap"
  where
    "reduce_root ti = (case ti of
  None \<Rightarrow> return None |
  Some p_t \<Rightarrow> do {
    node \<leftarrow> !p_t;
    tsl \<leftarrow> pfa_length (kvs node);
    case tsl of 0 \<Rightarrow> return (last node) |
    _ \<Rightarrow> return ti
})"

partial_function (heap) delete ::"nat \<Rightarrow> 'a \<Rightarrow> ('a::{default,heap,linorder}) btnode ref option \<Rightarrow> 'a btnode ref option Heap"
  where
    "delete k x ti = do {
  ti' \<leftarrow> del k x ti;
  reduce_root ti'
}"

subsection "Refinement of the abstract B-tree operations"

definition empty ::"('a::{default,heap,linorder}) btnode ref option Heap"
  where "empty = return None"


lemma P_imp_Q_implies_P: "P \<Longrightarrow> (Q \<longrightarrow> P)"
  by simp


lemma  "sorted_less (inorder t) \<Longrightarrow>
   <btree_assn k t ti>
     isin ti x
   <\<lambda>r. btree_assn k t ti * \<up>(abs_split.isin t x = r)>\<^sub>t"
proof(induction t x arbitrary: ti rule: abs_split.isin.induct)
  case (1 x)
  then show ?case
    apply(subst isin.simps)
    apply (cases ti)
     apply (auto simp add: return_cons_rule)
    done
next
  case (2 ts t x)
  then obtain ls rs where list_split[simp]: "split ts x = (ls,rs)"
    by (cases "split ts x")
  then show ?case
  proof (cases rs)
    (* NOTE: induction condition trivial here *)
    case [simp]: Nil
    show ?thesis
      apply(subst isin.simps)
      apply(sep_auto)
      using "2.prems" sorted_inorder_separators apply blast
      apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
      apply(rule hoare_triple_preI)
      apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
      using 2(3) apply(sep_auto heap: "2.IH"(1)[of ls "[]"] simp add: sorted_wrt_append)
      done
  next
    case [simp]: (Cons h rrs)
    obtain sub sep where h_split[simp]: "h = (sub,sep)"
      by (cases h)
    show ?thesis
    proof (cases "sep = x")
      (* NOTE: no induction required here, only vacuous counter cases generated *)
      case [simp]: True
      then show ?thesis
        apply(simp split: list.splits prod.splits)
        apply(subst isin.simps)
        using "2.prems" sorted_inorder_separators apply(sep_auto)
         apply(rule hoare_triple_preI)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest!: sym[of "[]"] mod_starD list_assn_len)[]
        done
    next
      case [simp]: False
      show ?thesis
        apply(simp split: list.splits prod.splits)
        apply safe
        using False apply simp
        apply(subst isin.simps)
        using "2.prems" sorted_inorder_separators 
        apply(sep_auto)
          (*eliminate vacuous case*)
          apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!:  mod_starD list_assn_len)[]
          (* simplify towards induction step *)
         apply(auto simp add: split_relation_alt list_assn_append_Cons_left dest!: mod_starD list_assn_len)[]

(* NOTE show that z = (suba, sepa) *)
         apply(rule norm_pre_ex_rule)+
         apply(rule hoare_triple_preI)
        subgoal for p tsi n ti xsi suba sepa zs1 z zs2 _
          apply(subgoal_tac "z = (suba, sepa)", simp)
          using 2(3) apply(sep_auto
              heap:"2.IH"(2)[of ls rs h rrs sub sep]
              simp add: sorted_wrt_append)
          using list_split Cons h_split apply simp_all
            (* proof that previous assumptions hold later *)
           apply(rule P_imp_Q_implies_P)
           apply(rule ent_ex_postI[where x="(tsi,n)"])
           apply(rule ent_ex_postI[where x="ti"])
           apply(rule ent_ex_postI[where x="(zs1 @ (suba, sepa) # zs2)"])
           apply(rule ent_ex_postI[where x="zs1"])
           apply(rule ent_ex_postI[where x="z"])
           apply(rule ent_ex_postI[where x="zs2"])
           apply sep_auto
            (* prove subgoal_tac assumption *)
          apply (metis (no_types, lifting) list_assn_aux_ineq_len list_assn_len nth_append_length star_false_left star_false_right)
          done
            (* eliminate last vacuous case *)
        apply(rule hoare_triple_preI)
        apply(auto simp add: split_relation_def dest!: mod_starD list_assn_len)[]
        done
    qed
  qed
qed



declare abs_split.node\<^sub>i.simps [simp add]
lemma node\<^sub>i_rule: assumes c_cap: "2*k \<le> c" "c \<le> 4*k+1"
  shows "<is_pfa c tsi (a,n) * list_assn ((btree_assn k) \<times>\<^sub>a id_assn) ts tsi * btree_assn k t ti>
  node\<^sub>i k (a,n) ti
  <\<lambda>r. btupi_assn k (abs_split.node\<^sub>i k ts t) r >\<^sub>t"
proof (cases "length ts \<le> 2*k")
  case [simp]: True
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto dest!: mod_starD list_assn_len)
       apply(sep_auto simp add: is_pfa_def)[]
    using c_cap apply(sep_auto simp add: is_pfa_def)[]
     apply(sep_auto  dest!: mod_starD list_assn_len)[]
    using True apply(sep_auto dest!: mod_starD list_assn_len)
    done
next
  case [simp]: False
  then obtain ls sub sep rs where
    split_half_eq: "BTree_Set.split_half ts = (ls,(sub,sep)#rs)"
    using abs_split.node\<^sub>i_cases by blast
  then show ?thesis
    apply(subst node\<^sub>i_def)
    apply(rule hoare_triple_preI)
    apply(sep_auto dest!: mod_starD list_assn_len)
       apply(sep_auto simp add:  split_relation_alt split_relation_length is_pfa_def dest!: mod_starD list_assn_len)

    using False apply(sep_auto simp add: split_relation_alt )
    using False  apply(sep_auto simp add: is_pfa_def)[]
    apply(sep_auto)[]
      apply(sep_auto simp add: is_pfa_def split_relation_alt)[]
    using c_cap apply(sep_auto simp add: is_pfa_def)[]
    apply(sep_auto)[]
    using c_cap apply(sep_auto simp add: is_pfa_def)[]
    using c_cap apply(simp)
    apply(vcg)
    apply(simp)
    apply(rule impI)
    subgoal for  _ _ _ _ rsa subi ba rn lsi al ar _
      thm ent_ex_postI
      thm ent_ex_postI[where x="take (length tsi div 2) tsi"]
        (* instantiate right hand side *)
      apply(rule ent_ex_postI[where x="(rsa,rn)"])
      apply(rule ent_ex_postI[where x="ti"])
      apply(rule ent_ex_postI[where x="(drop (Suc (length tsi div 2)) tsi)"])
      apply(rule ent_ex_postI[where x="lsi"])
      apply(rule ent_ex_postI[where x="subi"])
      apply(rule ent_ex_postI[where x="take (length tsi div 2) tsi"])
        (* introduce equality between equality of split tsi/ts and original lists *)
      apply(simp add: split_relation_alt)
      apply(subgoal_tac "tsi =
            take (length tsi div 2) tsi @ (subi, ba) # drop (Suc (length tsi div 2)) tsi")
       apply(rule back_subst[where a="blist_assn k ts (take (length tsi div 2) tsi @ (subi, ba) # (drop (Suc (length tsi div 2)) tsi))" and b="blist_assn k ts tsi"])
        apply(rule back_subst[where a="blist_assn k (take (length tsi div 2) ts @ (sub, sep) # rs)" and b="blist_assn k ts"])
         apply(subst list_assn_aux_append_Cons)
          apply sep_auto
         apply sep_auto
        apply simp
       apply simp
      apply(rule back_subst[where a="tsi ! (length tsi div 2)" and b="(subi, ba)"])
       apply(rule id_take_nth_drop)
       apply simp
      apply simp
      done
    done
qed
declare abs_split.node\<^sub>i.simps [simp del]


lemma node\<^sub>i_no_split: "length ts \<le> 2*k \<Longrightarrow> abs_split.node\<^sub>i k ts t = abs_split.T\<^sub>i (Node ts t)"
  by (simp add: abs_split.node\<^sub>i.simps)


lemma node\<^sub>i_rule_app: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1\<rbrakk> \<Longrightarrow>
<is_pfa c (tsi' @ [(li, ai)]) (aa, al) *
   blist_assn k ls tsi' *
   btree_assn k l li *
   id_assn a ai *
   btree_assn k r ri> node\<^sub>i k (aa, al) ri
 <btupi_assn k (abs_split.node\<^sub>i k (ls @ [(l, a)]) r)>\<^sub>t"
proof -
  note node\<^sub>i_rule[of k c "(tsi' @ [(li, ai)])" aa al "(ls @ [(l, a)])" r ri]
  moreover assume "2*k \<le> c" "c \<le> 4*k+1"
  ultimately show ?thesis
    by (simp add: mult.left_assoc)
qed

lemma node\<^sub>i_rule_ins2: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1; length ls = length lsi\<rbrakk> \<Longrightarrow>
 <is_pfa c (lsi @ (li, ai) # (ri,a'i) # rsi) (aa, al) *
   blist_assn k ls lsi *
   btree_assn k l li *
   id_assn a ai *
   btree_assn k r ri *
   id_assn a' a'i *
   blist_assn k rs rsi *
   btree_assn k t ti> node\<^sub>i k (aa, al)
          ti <btupi_assn k (abs_split.node\<^sub>i k (ls @ (l, a) # (r,a') # rs) t)>\<^sub>t"
proof -
  assume [simp]: "2*k \<le> c" "c \<le> 4*k+1" "length ls = length lsi"
  moreover note node\<^sub>i_rule[of k c "(lsi @ (li, ai) # (ri,a'i) # rsi)" aa al "(ls @ (l, a) # (r,a') # rs)" t ti]
  ultimately show ?thesis
    by (simp add: mult.left_assoc list_assn_aux_append_Cons)
qed

lemma ins_rule:
  "sorted_less (inorder t) \<Longrightarrow> <btree_assn k t ti>
  ins k x ti
  <\<lambda>r. btupi_assn k (abs_split.ins k x t) r>\<^sub>t"
proof (induction k x t arbitrary: ti rule: abs_split.ins.induct)
  case (1 k x)
  then show ?case
    apply(subst ins.simps)
    apply (sep_auto simp add: pure_app_eq)
    done
next
  case (2 k x ts t)
  obtain ls rrs where list_split: "split ts x = (ls,rrs)"
    by (cases "split ts x")
  have [simp]: "sorted_less (separators ts)"
    using "2.prems" sorted_inorder_separators by simp
  have [simp]: "sorted_less (inorder t)"
    using "2.prems" sorted_inorder_induct_last by simp
  show ?case
  proof (cases rrs)
    case Nil
    then show ?thesis
    proof (cases "abs_split.ins k x t")
      case (T\<^sub>i a)
      then show ?thesis
        apply(subst ins.simps)
        apply(sep_auto)
        subgoal for p tsil tsin tti
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' i tsin' _ sub sep
          apply(rule hoare_triple_preI)
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi'
          thm "2.IH"(1)[of ls rrs tti]
          using Nil list_split T\<^sub>i apply(sep_auto split!: list.splits simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
             apply sep_auto
            apply sep_auto
            done
          done
        done
    next
      case (Up\<^sub>i l a r)
      then show ?thesis
        apply(subst ins.simps)
        apply(sep_auto)
        subgoal for p tsil tsin tti
          using Nil list_split
          by (simp add: list_assn_aux_ineq_len split_relation_alt)                 
        subgoal for p tsil tsin tti tsi' i tsin' _ sub sep
          using Nil list_split 
          by (simp add: list_assn_aux_ineq_len split_relation_alt)
        subgoal for p tsil tsin tti tsi' i tsin'
          thm "2.IH"(1)[of ls rrs tti]
          using Nil list_split Up\<^sub>i apply(sep_auto split!: list.splits 
              simp add: split_relation_alt
              heap add: "2.IH"(1)[of ls rrs tti])
          subgoal for ai
            apply(cases ai)
             apply sep_auto
            apply(rule hoare_triple_preI)
            apply(sep_auto)
              apply(auto dest!: mod_starD simp add: is_pfa_def)[]
             apply (sep_auto)
            subgoal for li ai ri (* no split case *)
              apply(subgoal_tac "length (ls @ [(l,a)]) \<le> 2*k")
               apply(simp add: node\<^sub>i_no_split)
               apply(rule ent_ex_postI[where x="(tsil,Suc tsin)"])
               apply(rule ent_ex_postI[where x="ri"])
               apply(rule ent_ex_postI[where x="tsi' @ [(li, ai)]"])
               apply(sep_auto)
              apply (sep_auto dest!: mod_starD list_assn_len simp add: is_pfa_def)
              done
                (* split case*)
            apply(sep_auto heap add: node\<^sub>i_rule_app)
            done
          done
        done
    qed
  next
    case (Cons a rs)
    obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then have [simp]: "sorted_less (inorder sub)"
      using "2.prems" abs_split.split_axioms list_split Cons sorted_inorder_induct_subtree split_def
      by fastforce
    then show ?thesis
    proof(cases "x = sep")
      case True
      show ?thesis
        apply(subst ins.simps)
        apply(sep_auto)
        subgoal for p tsil tsin tti tsi j subi
          using Cons list_split a_split True
          by sep_auto
        subgoal for p tsil tsin tti tsi j _ _ subi sepi
          apply(rule hoare_triple_preI)
          using Cons list_split a_split True
          apply(subgoal_tac "sepi = sep")
           apply (sep_auto simp add: split_relation_alt)
          apply(sep_auto simp add: list_assn_prod_map dest!: mod_starD id_assn_list)
          by (metis length_map snd_conv snd_map_help(2) split_relation_access)
        subgoal for p tsil tsin tti tsi j
          apply(rule hoare_triple_preI)
          using Cons list_split
          by (sep_auto simp add: split_relation_alt dest!: mod_starD list_assn_len)
        done
    next
      case False
      then show ?thesis
      proof (cases "abs_split.ins k x sub")
        case (T\<^sub>i a')
        then show ?thesis
          apply(auto simp add: Cons list_split a_split False)
          using False apply simp
          apply(subst ins.simps)
          apply vcg
           apply auto
          apply(rule norm_pre_ex_rule)+
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
           apply sep_auto
          using list_split Cons
          apply(simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply sep_auto
            (* discard wrong branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(subgoal_tac "sepi  = x")
            using list_split Cons a_split
             apply(auto  dest!:  mod_starD )[]
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
              (* actual induction branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ n z suba sepa
            apply (cases a, simp)
            apply(subgoal_tac "subi = suba", simp)
            using list_split a_split T\<^sub>i False
             apply (vcg heap: 2)
               apply(auto split!: btupi.splits)
              (* careful progression for manual value insertion *)
             apply vcg
              apply simp
             apply vcg
             apply simp
            subgoal for a'i q r
              apply(rule impI)
              apply(simp add: list_assn_append_Cons_left)
              apply(rule ent_ex_postI[where x="(tsil,tsin)"])
              apply(rule ent_ex_postI[where x="ti"])
              apply(rule ent_ex_postI[where x="(zs1 @ (a'i, sepi) # zs2)"])
              apply(rule ent_ex_postI[where x="zs1"])
              apply(rule ent_ex_postI[where x="(a'i,sep)"])
              apply(rule ent_ex_postI[where x="zs2"])
              apply sep_auto
               apply (simp add: pure_app_eq)
              apply(sep_auto dest!:  mod_starD list_assn_len)[]
              done
            apply (metis list_assn_aux_ineq_len Pair_inject list_assn_len nth_append_length star_false_left star_false_right)
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          done
      next
        case (Up\<^sub>i l w r)
        then show ?thesis
          apply(auto simp add: Cons list_split a_split False)
          using False apply simp
          apply(subst ins.simps)
          apply vcg
           apply auto
          apply(rule norm_pre_ex_rule)+
            (* at this point, we want to introduce the split, and after that tease the
  hoare triple assumptions out of the bracket, s.t. we don't split twice *)
          apply vcg
           apply sep_auto
          using list_split Cons
          apply(simp add: split_relation_alt list_assn_append_Cons_left)
          apply (rule impI)
          apply(rule norm_pre_ex_rule)+
          apply(rule hoare_triple_preI)
          apply sep_auto
            (* discard wrong branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(subgoal_tac "sepi  = x")
            using list_split Cons a_split
             apply(auto  dest!:  mod_starD )[]
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
              (* actual induction branch *)
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ n z suba sepa
            apply(subgoal_tac "subi = suba", simp)
            thm 2(2)[of ls rrs a rs sub sep]
            using list_split a_split Cons Up\<^sub>i False
             apply (sep_auto heap: 2(2))
             apply(auto split!: btupi.splits)
              (* careful progression for manual value insertion *)
              apply vcg
               apply simp
            subgoal for li wi ri u (* no split case *)
              apply (cases u,simp)
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
                apply (simp add: is_pfa_def)[]
                apply (metis le_less_linear length_append length_take less_not_refl min.absorb2 trans_less_add1)
               apply(simp add: is_pfa_def)
               apply (metis add_Suc_right length_Cons length_append length_take min.absorb2)
              apply(sep_auto split: prod.splits  dest!: mod_starD list_assn_len)[]
                (* no split case *)
              apply(subgoal_tac "length (ls @ [(l,w)]) \<le> 2*k")
               apply(simp add: node\<^sub>i_no_split)
               apply(rule ent_ex_postI[where x="(tsil,Suc tsin)"])
               apply(rule ent_ex_postI[where x="ti"])
               apply(rule ent_ex_postI[where x="(zs1 @ (li, wi) # (ri, sep) # zs2)"])
               apply(sep_auto dest!: mod_starD list_assn_len)
              apply (sep_auto dest!: mod_starD list_assn_len simp add: is_pfa_def)
              done
             apply vcg
              apply simp
            subgoal for x21 x22 x23 u (* split case *)
              apply (cases u,simp)
              thm pfa_insert_grow_rule[where ?l="((zs1 @ (suba, sepi) # zs2)[length ls := (x23, sepa)])"]
              apply (sep_auto dest!: mod_starD list_assn_len heap: pfa_insert_grow_rule)
               apply (simp add: is_pfa_def)[]
               apply (metis le_less_linear length_append length_take less_not_refl min.absorb2 trans_less_add1)
              apply(auto split: prod.splits  dest!: mod_starD list_assn_len)[]

              apply (vcg heap: node\<^sub>i_rule_ins2)
                 apply simp
                apply simp
               apply simp
              apply sep_auto
              done
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          subgoal for p tsil tsin ti zs1 subi sepi zs2 _ _ suba
            apply(auto dest!:  mod_starD list_assn_len)[]
            done
          done
      qed
    qed
  qed
qed

text "The imperative insert refines the abstract insert."

lemma insert_rule:
  assumes "k > 0" "sorted_less (inorder t)"
  shows "<btree_assn k t ti>
  insert k x ti
  <\<lambda>r. btree_assn k (abs_split.insert k x t) r>\<^sub>t"
  unfolding insert_def
  apply(cases "abs_split.ins k x t")
   apply(sep_auto split!: btupi.splits heap: ins_rule[OF assms(2)])
  using assms
  apply(vcg heap: ins_rule[OF assms(2)])
  apply(simp split!: btupi.splits)
  apply(vcg)
   apply auto[]
  apply vcg
  apply auto[]
  subgoal for l a r li ai ri tsa tsn ti
    apply(rule ent_ex_postI[where x="(tsa,tsn)"])
    apply(rule ent_ex_postI[where x="ri"])
    apply(rule ent_ex_postI[where x="[(li, ai)]"])
    apply sep_auto
    done
  done

text "The \"pure\" resulting rule follows automatically."
lemma insert_rule':
  shows "<btree_assn (Suc k) t ti * \<up>(abs_split.invar_inorder (Suc k) t \<and> sorted_less (inorder t))>
  insert (Suc k) x ti
  <\<lambda>ri.\<exists>\<^sub>Ar. btree_assn (Suc k) r ri * \<up>(abs_split.invar_inorder (Suc k) r \<and> sorted_less (inorder r) \<and> inorder r = (ins_list x (inorder t)))>\<^sub>t"
  using abs_split.insert_bal abs_split.insert_order abs_split.insert_inorder 
  by (sep_auto heap: insert_rule simp add: sorted_ins_list)


lemma node\<^sub>i_rule_ins: "\<lbrakk>2*k \<le> c; c \<le> 4*k+1; length ls = length lsi\<rbrakk> \<Longrightarrow>
 <is_pfa c (lsi @ (li, ai) # rsi) (aa, al) *
   blist_assn k ls lsi *
   btree_assn k l li *
   id_assn a ai *
   blist_assn k rs rsi *
   btree_assn k t ti> node\<^sub>i k (aa, al)
          ti <btupi_assn k (abs_split.node\<^sub>i k (ls @ (l, a) # rs) t)>\<^sub>t"
proof -
  assume [simp]: "2*k \<le> c" "c \<le> 4*k+1" "length ls = length lsi"
  moreover note node\<^sub>i_rule[of k c "(lsi @ (li, ai) # rsi)" aa al "(ls @ (l, a) # rs)" t ti]
  ultimately show ?thesis
    by (simp add: mult.left_assoc list_assn_aux_append_Cons)
qed


lemma empty_rule:
  shows "<emp>
  empty
  <\<lambda>r. btree_assn k (abs_split.empty_btree) r>"
  apply(subst empty_def)
  apply(sep_auto simp add: abs_split.empty_btree_def)
  done

end

end

