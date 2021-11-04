theory OpInl
  imports Op
begin

section \<open>n-ary operations\<close>

locale nary_operations_inl =
  nary_operations \<OO>\<pp> \<AA>\<rr>\<ii>\<tt>\<yy>
  for
    \<OO>\<pp> :: "'op \<Rightarrow> 'a list \<Rightarrow> 'a" and \<AA>\<rr>\<ii>\<tt>\<yy> +
  fixes
    \<II>\<nn>\<ll>\<OO>\<pp> :: "'opinl \<Rightarrow> 'a list \<Rightarrow> 'a" and
    \<II>\<nn>\<ll> :: "'op \<Rightarrow> 'a list \<Rightarrow> 'opinl option" and
    \<II>\<ss>\<II>\<nn>\<ll> :: "'opinl \<Rightarrow> 'a list \<Rightarrow> bool" and
    \<DD>\<ee>\<II>\<nn>\<ll> :: "'opinl \<Rightarrow> 'op"
  assumes
    \<II>\<nn>\<ll>_invertible: "\<II>\<nn>\<ll> op xs = Some opinl \<Longrightarrow> \<DD>\<ee>\<II>\<nn>\<ll> opinl = op" and
    \<II>\<nn>\<ll>\<OO>\<pp>_correct: "length xs = \<AA>\<rr>\<ii>\<tt>\<yy> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) \<Longrightarrow> \<II>\<nn>\<ll>\<OO>\<pp> opinl xs = \<OO>\<pp> (\<DD>\<ee>\<II>\<nn>\<ll> opinl) xs" and
    \<II>\<nn>\<ll>_\<II>\<ss>\<II>\<nn>\<ll>: "\<II>\<nn>\<ll> op xs = Some opinl \<Longrightarrow> \<II>\<ss>\<II>\<nn>\<ll> opinl xs"

begin

lemma \<II>\<nn>\<ll>_inj_on: "inj_on \<II>\<nn>\<ll> { op | op args. \<II>\<nn>\<ll> op args \<noteq> None }"
  apply (simp add: inj_on_def)
proof (intro allI impI, elim exE)
  fix op\<^sub>1 op\<^sub>2 args\<^sub>1 args\<^sub>2 opinl\<^sub>1 opinl\<^sub>2
  assume assms: "\<II>\<nn>\<ll> op\<^sub>1 = \<II>\<nn>\<ll> op\<^sub>2" "\<II>\<nn>\<ll> op\<^sub>1 args\<^sub>1 = Some opinl\<^sub>1" "\<II>\<nn>\<ll> op\<^sub>2 args\<^sub>2 = Some opinl\<^sub>2"
  hence "\<DD>\<ee>\<II>\<nn>\<ll> opinl\<^sub>1 = op\<^sub>1" "\<DD>\<ee>\<II>\<nn>\<ll> opinl\<^sub>1 = op\<^sub>2"
    by (auto intro: \<II>\<nn>\<ll>_invertible)
  thus "op\<^sub>1 = op\<^sub>2"
    by simp
qed

abbreviation \<II>\<nn>\<ll>_dom where
  "\<II>\<nn>\<ll>_dom \<equiv> {op | op args. \<II>\<nn>\<ll> op args \<noteq> None }"

lemma "bij_betw \<II>\<nn>\<ll> \<II>\<nn>\<ll>_dom { \<II>\<nn>\<ll> op | op. op \<in> \<II>\<nn>\<ll>_dom}"
  using bij_betw_def
  unfolding image_def
  using \<II>\<nn>\<ll>_inj_on
  by (auto simp add: bij_betw_def)

end

end