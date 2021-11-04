theory OpUbx
  imports OpInl Unboxed
begin


section \<open>n-ary operations\<close>

locale nary_operations_ubx =
  nary_operations_inl \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy> \<II>\<nn>\<ll>\<OO>\<pp> \<II>\<nn>\<ll> \<II>\<ss>\<II>\<nn>\<ll> \<DD>\<ee>\<II>\<nn>\<ll> +
  unboxedval is_true is_false box_ubx1 unbox_ubx1 box_ubx2 unbox_ubx2
  for
    \<OO>\<pp> :: "'op \<Rightarrow> 'dyn list \<Rightarrow> 'dyn" and \<AA>\<rr>\<ii>\<tt>\<yy> and
    \<II>\<nn>\<ll>\<OO>\<pp> and \<II>\<nn>\<ll> and \<II>\<ss>\<II>\<nn>\<ll> and \<DD>\<ee>\<II>\<nn>\<ll> :: "'opinl \<Rightarrow> 'op" and
    is_true :: "'dyn \<Rightarrow> bool" and is_false and
    box_ubx1 :: "'ubx1 \<Rightarrow> 'dyn" and unbox_ubx1 and
    box_ubx2 :: "'ubx2 \<Rightarrow> 'dyn" and unbox_ubx2 +
  fixes
    \<UU>\<bb>\<xx>\<OO>\<pp> :: "'opubx \<Rightarrow> ('dyn, 'ubx1, 'ubx2) unboxed list \<Rightarrow> ('dyn, 'ubx1, 'ubx2) unboxed option" and
    \<UU>\<bb>\<xx> :: "'opinl \<Rightarrow> type option list \<Rightarrow> 'opubx option" and
    \<BB>\<oo>\<xx> :: "'opubx \<Rightarrow> 'opinl" and
    \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> :: "'opubx \<Rightarrow> type option list \<times> type option"
  assumes
    \<UU>\<bb>\<xx>_invertible:
      "\<UU>\<bb>\<xx> opinl ts = Some opubx \<Longrightarrow> \<BB>\<oo>\<xx> opubx = opinl" and
    \<UU>\<bb>\<xx>\<OO>\<pp>_correct:
      "\<UU>\<bb>\<xx>\<OO>\<pp> opubx \<Sigma> = Some z \<Longrightarrow> \<II>\<nn>\<ll>\<OO>\<pp> (\<BB>\<oo>\<xx> opubx) (map norm_unboxed \<Sigma>) = norm_unboxed z" and
    \<UU>\<bb>\<xx>\<OO>\<pp>_to_\<II>\<nn>\<ll>:
      "\<UU>\<bb>\<xx>\<OO>\<pp> opubx \<Sigma> = Some z \<Longrightarrow> \<II>\<nn>\<ll> (\<DD>\<ee>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx)) (map norm_unboxed \<Sigma>) = Some (\<BB>\<oo>\<xx> opubx)" and
    
    \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_\<AA>\<rr>\<ii>\<tt>\<yy>:
      "\<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> (\<BB>\<oo>\<xx> opubx)) = length (fst (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx))" and
    \<UU>\<bb>\<xx>_opubx_type:
      "\<UU>\<bb>\<xx> opinl ts = Some opubx \<Longrightarrow> fst (\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx) = ts" and

    \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_correct:
      "\<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx = (map typeof xs, \<tau>) \<Longrightarrow>
        \<exists>y. \<UU>\<bb>\<xx>\<OO>\<pp> opubx xs = Some y \<and> typeof y = \<tau>" and
    \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp>_complete:
      "\<UU>\<bb>\<xx>\<OO>\<pp> opubx xs = Some y \<Longrightarrow> \<TT>\<yy>\<pp>\<ee>\<OO>\<ff>\<OO>\<pp> opubx = (map typeof xs, typeof y)"

begin

end

end