(*  Title:      CoW_Graph_Lemma.Graph_Lemma
    Author:     Štěpán Holub, Charles University
    Author:     Štěpán Starosta, CTU in Prague
*)

theory Graph_Lemma
  imports Combinatorics_Words.Submonoids

begin

chapter \<open>Graph Lemma\<close>

text\<open>The Graph Lemma is an important tool for gaining information about systems of word equations. 
It yields an upper bound on the rank of the solution, that is, on the number of factors into all images of unknowns can be factorized.
The most straightforward application is showing that a system of equations admits periodic solutions only, which
in particular holds for any nontrivial equation over two words.

The name refers to a graph whose vertices are the unknowns of the system, and edges connect front letters of the left- and right-
hand sides of equations. The bound mentioned above is then the number of connected components of the graph.

We formalize the algebraic proof from @{cite Berstel1979} \<close>

text\<open>Let @{term C} be a set of generators, and $b$ its distinguished element. We define the set of all 
 products that do not start with $b$.\<close>

inductive_set no_head :: "'a list set \<Rightarrow> 'a list \<Rightarrow> 'a list set"
  for C b where
  emp_in_no_head[simp]:  "\<epsilon> \<in> no_head C b"
  | "u \<in> C \<Longrightarrow> u \<noteq> b \<Longrightarrow> u \<in> no_head C b" 
  | "u \<noteq> \<epsilon> \<Longrightarrow> u \<in> no_head C b \<Longrightarrow> v \<in> \<langle>C\<rangle> \<Longrightarrow>  u \<cdot> v \<in> no_head C b"

text\<open>The set is a submonoid of @{term "\<langle>C\<rangle>"}\<close>

lemma no_head_sub: "no_head C b \<subseteq> \<langle>C\<rangle>"
proof
  fix u assume "u \<in> no_head C b"
  show "u \<in> \<langle>C\<rangle>"
  proof (induction rule: no_head.induct[OF \<open>u \<in> no_head C b\<close>], auto)
    case (3 u v)
    then show "u \<cdot> v \<in> \<langle>C\<rangle>"
      using hull_closed by blast 
  qed
qed



lemma no_head_closed:  "\<langle>no_head C b\<rangle> = no_head C b"
proof(intro equalityI) 
  show "no_head C b \<subseteq> \<langle>no_head C b\<rangle>" by (simp add: genset_sub) 
next
  show "\<langle>no_head C b\<rangle> \<subseteq> no_head C b"
  proof
    fix x assume "x \<in> \<langle>no_head C b\<rangle>"
    thus "x \<in> no_head C b" 
    proof (induction rule: hull.induct, simp)
      case (prod_cl w1 w2)
      then show "w1 \<cdot> w2 \<in> no_head C b"
        using no_head.intros(3)[OF _ \<open>w1 \<in> no_head C b\<close>]
          in_mono[OF no_head_sub, of w2] by fastforce
    qed
  qed
qed

text\<open>We are interested mainly in the situation when @{term C} is a code.\<close>

context code
begin

text\<open>We characterize the set @{term no_head} in terms of the decomposition of its (nonempty) elements: the first factor is not b\<close>

lemma no_head_hd: assumes "u \<in> no_head \<C> b" and "u \<noteq> \<epsilon>" shows "hd (Dec \<C> u) \<noteq> b"
  using \<open>u \<noteq> \<epsilon>\<close> 
proof(induct rule: no_head.induct[OF \<open>u \<in> no_head \<C> b\<close>], simp)
  case (2 u)
  then show ?case
    using code_el_dec by auto
next
  case (3 u v)
  have "Dec \<C> u \<noteq> \<epsilon>" and "u \<in> \<langle>\<C>\<rangle>" and "v \<in> \<langle>\<C>\<rangle>" 
    using dec_nemp no_head_sub "3.hyps" by blast+
  show "hd (Dec \<C> u \<cdot> v) \<noteq> b" 
    using "3.hyps"(3)[OF \<open>u \<noteq> \<epsilon>\<close>] hd_append2[OF \<open>Dec \<C> u \<noteq> \<epsilon>\<close>, of "Dec \<C> v"] 
    unfolding code_dec_morph[OF \<open> u \<in> \<langle>\<C>\<rangle>\<close> \<open>v \<in> \<langle>\<C>\<rangle>\<close>] by simp
qed 

lemma b_not_in_no_head: assumes "b \<in> \<C>" shows "b \<notin> no_head \<C> b"
  using \<open>b \<in> \<C>\<close> code_el_dec emp_not_in_code no_head_hd by fastforce

lemma hd_no_head: assumes "u \<in> \<langle>\<C>\<rangle>" and "hd (Dec \<C> u) \<noteq> b" shows "u \<in> no_head \<C> b"
proof(cases "u \<noteq> \<epsilon>")
  assume "u \<noteq> \<epsilon>"
  have "Dec \<C> u \<noteq> \<epsilon>"
    using dec_nemp'[OF \<open>u \<noteq> \<epsilon>\<close> \<open>u \<in> \<langle>\<C>\<rangle>\<close>].  
  have "u = hd (Dec \<C> u) \<cdot> concat (tl (Dec \<C> u))"
    using concat.simps(2)[of "hd (Dec \<C> u)" "tl(Dec \<C> u)"] 
    unfolding hd_Cons_tl[OF \<open>Dec \<C> u \<noteq> \<epsilon>\<close>] decI[OF \<open>u \<in> \<langle>\<C>\<rangle>\<close>].
  have "hd (Dec \<C> u) # tl (Dec \<C> u) \<in> lists \<C>" and "hd (Dec \<C> u) \<in> \<C>"
    using \<open>Dec \<C> u \<noteq> \<epsilon>\<close> \<open>u \<in> \<langle>\<C>\<rangle>\<close> dec_dom' lists_hd by auto blast
  have "concat (tl (decompose \<C> u)) \<in> \<langle>\<C>\<rangle>"
    using concat_tl[of "hd (Dec \<C> u)" "tl(Dec \<C> u)" \<C>, OF \<open>hd (Dec \<C> u) # tl (Dec \<C> u) \<in> lists \<C>\<close>].
  have "hd (Dec \<C> u) \<noteq> \<epsilon>" and "hd (Dec \<C> u) \<in> no_head \<C> b"
    using no_head.intros(2)[OF \<open>hd (Dec \<C> u) \<in> \<C>\<close> \<open>hd (Dec \<C> u) \<noteq> b\<close>] \<open>hd (Dec \<C> u) \<in> \<C>\<close> emp_not_in_code by auto
  from no_head.intros(3)[OF this \<open>concat (tl (decompose \<C> u)) \<in> \<langle>\<C>\<rangle>\<close> ] 
  show "u \<in> no_head \<C> b"
    unfolding sym[OF \<open>u = hd (Dec \<C> u) \<cdot> concat (tl (Dec \<C> u))\<close>].
qed simp

corollary "no_head \<C> b = {u \<in> \<langle>\<C>\<rangle>. u = \<epsilon> \<or> hd (Dec \<C> u) \<noteq> b}"
proof(intro equalityI subsetI, standard)
  fix x assume  "x \<in> no_head \<C> b"
  thus "x \<in> \<langle>\<C>\<rangle> \<and> (x = \<epsilon> \<or> hd (Dec \<C> x) \<noteq> b)"
    using no_head_hd no_head_sub by blast
next
  fix x assume "x \<in> {u \<in> \<langle>\<C>\<rangle>. u = \<epsilon> \<or> hd (Dec \<C> u) \<noteq> b}"
  thus "x \<in> no_head \<C> b"
    using hd_no_head no_head.simps by blast 
qed

end

text\<open>The set @{term no_head} is generated by the following set.\<close>

inductive_set no_head_gen :: "'a list set \<Rightarrow> 'a list \<Rightarrow> 'a list set"
  for C b where
    "u \<in> C \<Longrightarrow> u \<noteq> b \<Longrightarrow> u \<in> no_head_gen C b" 
  | "u \<in> no_head_gen C b \<Longrightarrow>  u \<cdot> b \<in> no_head_gen C b"

lemma no_head_gen_set: "no_head_gen C b = {z \<cdot> b\<^sup>@k |z k. z \<in> C \<and> z \<noteq> b}"
proof(intro equalityI subsetI)
  fix x assume "x \<in> no_head_gen C b"
  hence "\<exists> z k. z \<in> C \<and> z \<noteq> b \<and> x = z \<cdot> b\<^sup>@k" 
  proof (rule no_head_gen.induct)
    fix u assume "u \<in> C" and "u \<noteq> b"
    show "\<exists>z k. z \<in> C \<and> z \<noteq> b \<and> u = z \<cdot> b\<^sup>@k"
      using \<open>u \<in> C\<close> \<open>u \<noteq> b\<close> pow_zero by blast
  next
    fix u assume "u \<in> no_head_gen C b" and "\<exists>z k. z \<in> C \<and> z \<noteq> b \<and> u = z \<cdot> b\<^sup>@k"
    thus "\<exists>z k. z \<in> C \<and> z \<noteq> b \<and> u \<cdot> b = z \<cdot> b\<^sup>@k"
      using pow_Suc2_list append.assoc by metis         
  qed
  thus "x \<in> {z \<cdot> b\<^sup>@k |z k. z \<in> C \<and> z \<noteq> b}"
    by auto
next
  fix x assume "x \<in> {z \<cdot> b \<^sup>@ k |z k. z \<in> C \<and> z \<noteq> b}"
  then obtain z k where "z \<in> C" and "z \<noteq> b" and "x = z\<cdot>b\<^sup>@k" by blast   
  then show "x \<in> no_head_gen C b"
  proof(induct k arbitrary: x)
    case 0
    then show ?case
      by (simp add: \<open>z \<in> C\<close> \<open>z \<noteq> b\<close> no_head_gen.intros(1)) 
  next
    case (Suc k)
    from this(1)[OF this(2) this(3), of "z \<cdot> b \<^sup>@ k", 
        THEN no_head_gen.intros(2), unfolded rassoc, 
        folded pow_Suc2_list[of b k] \<open>x = z\<cdot>b\<^sup>@Suc k\<close>]
    show ?case
      by blast      
  qed
qed

lemma no_head_genE: assumes "u \<in> no_head_gen C b"
  obtains z k where "z \<in> C" and  "z \<noteq> b" and "u = z \<cdot> b\<^sup>@k"
proof(induct rule: no_head_gen.induct[OF assms])
  case (1 u)
  show ?case
    using "1.prems"[OF "1.hyps", of 0] by simp  
next
  case (2 u)
  have "(z \<cdot> b\<^sup>@k) \<cdot> b = z \<cdot> b\<^sup>@(Suc k)" for z k
    by (simp add: power_commutes)  
  then show ?case   
    using "2.prems" "2.hyps"(2) by blast
qed

context code
begin

text\<open>We show that this indeed is a set of generators\<close>

lemma emp_not_in_Cb: "\<epsilon> \<notin> no_head_gen \<C> b"
  by (simp add: emp_not_in_code no_head_gen_set)

lemma no_head_sub': "b \<in> \<C> \<Longrightarrow> no_head_gen \<C> b \<subseteq> no_head \<C> b"
proof
  fix u assume "b \<in> \<C>" "u \<in> no_head_gen \<C> b"
  show "u \<in> no_head \<C> b"
  proof (induction rule: no_head_gen.induct[OF \<open>u \<in> no_head_gen \<C> b\<close>], simp add: no_head.intros(2))
    case (2 u)
    show "u \<cdot> b \<in> no_head \<C> b"
      using no_head.intros(3)[OF _ \<open>u \<in> no_head \<C> b\<close> gen_in[OF \<open>b \<in> \<C>\<close>]]
       "2.hyps" emp_not_in_Cb by blast 
  qed
qed

lemma no_head_generates0: assumes "v \<in> \<langle>\<C>\<rangle>" shows 
  "u \<noteq> \<epsilon> \<longrightarrow> u \<in> \<langle>no_head_gen \<C> b\<rangle> \<longrightarrow> u \<cdot> v \<in>  \<langle>no_head_gen \<C> b\<rangle>"
proof (induct arbitrary: u rule: hull.induct[OF \<open>v \<in> \<langle>\<C>\<rangle>\<close>], simp)
  case (2 w1 w2)
  then show ?case
  proof(cases "w1 = b")
    assume "w1 \<noteq> b" 
    show ?thesis
      using "2.hyps"(1) emp_not_in_code  no_head_gen.intros(1)[OF \<open>w1 \<in> \<C>\<close> \<open>w1 \<noteq> b\<close>,THEN gen_in]
            "2.hyps"(3)[of w1] hull_closed[of u "no_head_gen \<C> b" "w1\<cdot> w2"] by blast
  next 
    assume "w1 = b"
    show ?thesis
    proof (standard, standard)
      assume "u \<noteq> \<epsilon>" and "u \<in> \<langle>no_head_gen \<C> b\<rangle>"
      hence dec_nemp: "Dec (no_head_gen \<C> b) u \<noteq> \<epsilon>"
        using dec_nemp' by blast
      from concat_butlast_last[OF this]
      have u_w1: "u \<cdot> w1 = concat (butlast (Dec (no_head_gen \<C> b) u)) \<cdot> (last (Dec (no_head_gen \<C> b) u) \<cdot> w1)"
        unfolding decI[OF \<open>u \<in> \<langle>no_head_gen \<C> b\<rangle>\<close>] by simp
      from dec_dom'[OF \<open>u \<in> \<langle>no_head_gen \<C> b\<rangle>\<close>] append_butlast_last_id[OF dec_nemp]
      have con_but: "concat (butlast (Dec (no_head_gen \<C> b) u)) \<in> \<langle>no_head_gen \<C> b\<rangle>" and last_in: "last (Dec (no_head_gen \<C> b) u) \<in> no_head_gen \<C> b"
        using append_in_lists_conv[of "butlast (Dec (no_head_gen \<C> b) u)" "[last (Dec (no_head_gen \<C> b) u)]" "no_head_gen \<C> b"] 
          concat_in_hull'[of "butlast (Dec (no_head_gen \<C> b) u)" "no_head_gen \<C> b"] by auto 
      hence "last (Dec (no_head_gen \<C> b) u) \<cdot> w1 \<in> no_head_gen \<C> b"
        unfolding \<open>w1 = b\<close> using  no_head_gen.intros(2)[of "last (Dec (no_head_gen \<C> b) u)" \<C> b] by blast
      from this[THEN  gen_in,THEN[2] hull_closed, OF con_but]
      have "u \<cdot> w1 \<in> \<langle>no_head_gen \<C> b\<rangle>"
        unfolding u_w1.
      from "2.hyps"(3)[rule_format, OF _ this, unfolded rassoc]
      show "u \<cdot> w1 \<cdot> w2 \<in> \<langle>no_head_gen \<C> b\<rangle>"
        using  pref_nemp[OF \<open>u\<noteq>\<epsilon>\<close>] by blast
    qed
  qed
qed


theorem no_head_generates: assumes "b \<in> \<C>" shows "\<langle>no_head_gen \<C> b\<rangle> =  no_head \<C> b"
proof (intro equalityI)  
  show "\<langle>no_head_gen \<C> b\<rangle> \<subseteq> no_head \<C> b"
    using hull_mon[OF no_head_sub'[OF \<open>b \<in> \<C>\<close>]] unfolding no_head_closed.  
  show "no_head \<C> b \<subseteq> \<langle>no_head_gen \<C> b\<rangle>"
  proof (intro subsetI)
    fix x assume "x \<in> no_head \<C> b" 
    show "x \<in> \<langle>no_head_gen \<C> b\<rangle>"
      by (induct rule: no_head.induct[OF \<open>x \<in> no_head \<C> b\<close>],auto, simp add: gen_in no_head_gen.intros(1),simp add: no_head_generates0)
  qed
qed

text\<open>Moreover, the generating set @{term no_head_gen} is a code\<close>

lemma lists_no_head_sub: "b \<in> \<C> \<Longrightarrow> us \<in> lists (no_head_gen \<C> b) \<Longrightarrow> us \<in> lists \<langle>\<C>\<rangle>"
  using no_head_sub' no_head_sub by blast   

lemma ref_hd: assumes "z \<in> \<C>" and  "b \<in> \<C>" and "z \<noteq> b" and "vs \<in> lists (no_head_gen \<C> b)" 
  shows "refine \<C> ((z\<cdot>b\<^sup>@k) # vs) = [z]\<cdot>[b]\<^sup>@k \<cdot> refine \<C> vs" 
proof-
  have "refine \<C> ((z\<cdot>b\<^sup>@k) # vs) = (Dec \<C> (z\<cdot>b\<^sup>@k)) \<cdot> refine \<C> vs" 
    using ref_pop_hd lists_no_head_sub[OF \<open>b \<in> \<C>\<close>]  by simp 
  have "[z]\<cdot>[b]\<^sup>@k \<in> lists \<C>"
    by (induct k, simp add: \<open>z \<in> \<C>\<close>, simp add: \<open>b \<in> \<C>\<close>)
  have "concat ([z]\<cdot>[b]\<^sup>@k) = z \<cdot> b\<^sup>@k"
    using concat_sing_pow by auto
  hence "Dec \<C> (z\<cdot>b\<^sup>@k) = [z]\<cdot>[b]\<^sup>@k"
    using  code.code_unique_dec[OF code_axioms \<open>[z]\<cdot>[b]\<^sup>@k \<in> lists \<C>\<close>] by auto
  thus ?thesis
    by simp
qed


lemma no_head_gen_code_ind_step:
  assumes "vs \<in> lists (no_head_gen \<C> b)" "us \<in> lists (no_head_gen \<C> b)" "b \<in> \<C>"
    and eq: "[b]\<^sup>@ku \<cdot> (refine \<C> us) = [b]\<^sup>@kv \<cdot> (refine \<C> vs)"
  shows  "ku = kv"
proof-
  {fix ku :: nat and kv and us and vs and b 
    assume "kv \<le> ku" "[b]\<^sup>@ku \<cdot> (refine \<C> us) = [b]\<^sup>@kv \<cdot> (refine \<C> vs)"
      "vs \<in> lists (no_head_gen \<C> b)" "us \<in> lists (no_head_gen \<C> b)" "b \<in> \<C>"
    have  "concat vs \<in> no_head \<C> b"
      using  \<open>vs \<in> lists (no_head_gen \<C> b)\<close> no_head_generates[OF \<open>b \<in> \<C>\<close>] by fastforce
    have  "Ref \<C> vs = Dec \<C> (concat vs)"
      using \<open>vs \<in> lists (no_head_gen \<C> b)\<close> \<open>b \<in> \<C>\<close> code_unique_ref lists_no_head_sub by auto
    have "vs \<noteq> \<epsilon> \<Longrightarrow> concat vs \<noteq> \<epsilon>"
      using  emp_not_in_Cb[of b] concat.simps(2) \<open>vs \<in> lists (no_head_gen \<C> b)\<close>[unfolded lists.simps[of vs]]
        pref_nemp by auto 
    have "[b]\<^sup>@(ku - kv) \<cdot> (refine \<C> us) = refine \<C> vs"
      using \<open>kv \<le> ku\<close> eq pop_pow_cancel \<open>[b]\<^sup>@ku \<cdot> (refine \<C> us) = [b]\<^sup>@kv \<cdot> (refine \<C> vs) \<close>by blast
    hence "ku - kv \<noteq> 0 \<Longrightarrow> hd (refine \<C> vs) = b \<and> vs \<noteq> \<epsilon>"
      using hd_append2[of "[b]\<^sup>@(ku - kv)" "refine \<C> us"]  \<open>[b]\<^sup>@(ku - kv) \<cdot> (refine \<C> us) = refine \<C> vs\<close>
        hd_sing_power[of "ku - kv" b] 
        append_is_Nil_conv[of "[b]\<^sup>@(ku - kv)" "refine \<C> us"]  sing_pow_empty[of b "ku - kv"]
        dec_emp[of \<C>] by auto 
    hence "ku = kv"
      using \<open>kv \<le> ku\<close> no_head_hd[OF \<open>concat vs \<in> no_head \<C> b\<close>] \<open>vs \<noteq> \<epsilon> \<Longrightarrow> concat vs \<noteq> \<epsilon>\<close> 
      unfolding \<open>Ref \<C> vs = Dec \<C> (concat vs)\<close> by auto} 
  thus ?thesis  using assms nat_le_linear[of ku kv] by metis
qed 

lemma no_head_gen_code':
  "b \<in> \<C> \<Longrightarrow> xs \<in> lists (no_head_gen \<C> b) 
   \<Longrightarrow> ys \<in>  lists (no_head_gen \<C> b) \<Longrightarrow> concat xs = concat ys \<Longrightarrow> xs = ys"
proof (induct xs ys rule: list_induct2', simp, simp add: emp_not_in_Cb, simp add: emp_not_in_Cb)
  case (4 hx xs hy ys)
  then show ?case 
  proof-
    have "hx # xs \<in> lists \<langle>\<C>\<rangle>" and "hy # ys \<in> lists \<langle>\<C>\<rangle>"
      using \<open>b \<in> \<C>\<close>  \<open>hx # xs \<in> lists (no_head_gen \<C> b)\<close> \<open>hy # ys \<in> lists (no_head_gen \<C> b)\<close> lists_no_head_sub by blast+
    have eq: "refine \<C> (hx#xs) = refine \<C>  (hy#ys)"
      using \<open>concat (hx # xs) = concat (hy # ys)\<close> \<open>hx # xs \<in> lists \<langle>\<C>\<rangle>\<close> \<open>hy # ys \<in> lists \<langle>\<C>\<rangle>\<close>
      using code_unique_ref by presburger 
    have "hx \<in> (no_head_gen \<C> b)" and "hy \<in> (no_head_gen \<C> b)"
      using \<open>hx # xs \<in> lists (no_head_gen \<C> b)\<close> \<open>hy # ys \<in> lists (no_head_gen \<C> b)\<close> by auto+
    then obtain zx zy kx ky where "hx = zx \<cdot> b\<^sup>@kx" and "hy = zy \<cdot> b\<^sup>@ky" "zx \<noteq> b" "zy \<noteq> b" "zx \<in> \<C>" "zy \<in> \<C>"
      using no_head_genE by metis
    have r1: "refine \<C> (hx#xs) = [zx] \<cdot> [b]\<^sup>@kx \<cdot> refine \<C> xs"
      using \<open>hx = zx \<cdot> b\<^sup>@kx\<close> \<open>zx \<in> \<C>\<close> \<open>zx \<noteq> b\<close> ref_hd \<open>b \<in> \<C>\<close> by auto
    have r2: "refine \<C> (hy#ys) = [zy] \<cdot> [b]\<^sup>@ky \<cdot> refine \<C> ys"
      using \<open>hy = zy \<cdot> b\<^sup>@ky\<close> \<open>zy \<in> \<C>\<close> \<open>zy \<noteq> b\<close> ref_hd \<open>b \<in> \<C>\<close> by auto
    hence "zx = zy"
      using r1 r2 eq by auto
    hence "[b]\<^sup>@kx \<cdot> refine \<C> xs = [b]\<^sup>@ky \<cdot> refine \<C> ys"
      using eq r1 r2 by auto 
    hence "kx = ky" 
      using no_head_gen_code_ind_step \<open>b \<in> \<C>\<close> \<open>hx # xs \<in> lists (no_head_gen \<C> b)\<close> \<open>hy # ys \<in> lists (no_head_gen \<C> b)\<close> 
        listsE  by metis 
    hence "hx = hy"
      by (simp add: \<open>hx = zx \<cdot> b\<^sup>@kx\<close> \<open>hy = zy \<cdot> b\<^sup>@ky\<close> \<open>zx = zy\<close>)
    hence "xs = ys" using "4.hyps" 
      using \<open>hx # xs \<in> lists (no_head_gen \<C> b)\<close> \<open>hy # ys \<in> lists (no_head_gen \<C> b)\<close> 
        \<open>concat (hx # xs) = concat (hy # ys)\<close> \<open>b \<in> \<C>\<close> by auto
    thus ?thesis
      by (simp add: \<open>hx = hy\<close>) 
  qed
qed  

end

theorem no_head_gen_code:
  assumes "code C" and "b \<in> C"
  shows "code {z \<cdot> b\<^sup>@k | z k. z \<in> C \<and> z \<noteq> b}"
  using code.no_head_gen_code'[OF \<open>code C\<close> \<open>b \<in> C\<close>] code.intro
  unfolding no_head_gen_set  by blast

text\<open>We are now ready to prove the Graph Lemma \<close>

theorem graph_lemma: "\<BB>\<^sub>F X = {hd (Dec (\<BB>\<^sub>F X) x) | x. x \<in> X \<and> x \<noteq> \<epsilon>}"
proof 
  \<comment> \<open>the core is to show that each element of the free basis must be a head\<close>
  show "\<BB>\<^sub>F X \<subseteq> {hd (Dec (\<BB>\<^sub>F X) x) | x. x \<in> X \<and> x \<noteq> \<epsilon>}"
  proof (rule ccontr)
    \<comment> \<open>Assume the contrary.\<close>
     assume "\<not> \<BB>\<^sub>F X \<subseteq> {hd (Dec \<BB>\<^sub>F X x) |x. x \<in> X \<and> x \<noteq> \<epsilon>}"  
    \<comment> \<open>And let b be the not-head\<close>
    then obtain b where "b \<in> \<BB>\<^sub>F X" and nohd: "\<And> x.   x \<in> X \<and> x \<noteq> \<epsilon> \<Longrightarrow> hd (Dec (\<BB>\<^sub>F X) x) \<noteq> b"
      by blast
    interpret code "\<BB>\<^sub>F X"
        using free_basis_code by auto
          \<comment> \<open>For contradiction: We have a free hull which does not contain b but contains X.\<close>
      let ?Cb = "no_head_gen (\<BB>\<^sub>F X) b"
      have "code ?Cb"
        using \<open>b \<in> \<BB>\<^sub>F X\<close> code_def no_head_gen_code' by blast 
      have "b \<notin> \<langle>?Cb\<rangle>"
        using \<open>b \<in> \<BB>\<^sub>F X\<close> b_not_in_no_head no_head_generates by blast
      have "X \<subseteq> \<langle>?Cb\<rangle>"
      proof
        fix x assume "x \<in> X" 
        hence "x \<in> \<langle>\<BB>\<^sub>F X\<rangle>"
          using basis_gen_hull free_hull.free_gen_in 
          unfolding free_basis_def by blast
        have " x \<in> X \<and> x \<noteq> \<epsilon> \<Longrightarrow> x \<in> \<langle>?Cb\<rangle>"
          using hd_no_head[OF \<open>x \<in> \<langle>\<BB>\<^sub>F X\<rangle>\<close> nohd]
            \<open>b \<in> \<BB>\<^sub>F X\<close> no_head_generates by blast
        thus "x \<in> \<langle>?Cb\<rangle>"
          using \<open>x \<in> X\<close> by blast 
      qed
      have "\<langle>X\<rangle>\<^sub>F \<subseteq> \<langle>?Cb\<rangle>" 
        using free_hull_min[OF \<open>code ?Cb\<close> \<open>X \<subseteq> \<langle>?Cb\<rangle>\<close>].
      from this[unfolded subset_eq, rule_format, of b]
      show False
        using \<open>b \<in> \<BB>\<^sub>F X\<close> \<open>b \<notin> \<langle>?Cb\<rangle>\<close> basisD simp_el_el unfolding free_basis_def by blast
  qed
next
  \<comment> \<open>The opposite inclusion is easy\<close>
  show "{hd (Dec (\<BB>\<^sub>F X) x) | x.  x \<in> X \<and> x \<noteq> \<epsilon>} \<subseteq> \<BB>\<^sub>F X"
    using basis_gen_hull_free dec_hd genset_sub_free by blast
qed

section \<open>Binary code\<close>

text\<open>We illustrate the use of the Graph Lemma in an alternative proof of the fact that two non-commuting words form a code.
See also @{thm no_comm_bin_code [no_vars]} in @{theory Combinatorics_Words.CoWBasic}.

First, we prove a lemma which is the core of the alternative proof.
\<close>

lemma non_comm_hds_neq: assumes "u \<cdot> v \<noteq> v \<cdot> u" shows "hd (Dec \<BB>\<^sub>F {u,v} u) \<noteq> hd (Dec \<BB>\<^sub>F {u,v} v)"
proof
  have "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" using assms by auto
  hence basis: "\<BB>\<^sub>F {u,v} = {hd (Dec \<BB>\<^sub>F {u,v} u),hd (Dec \<BB>\<^sub>F {u,v} v)}"
    using graph_lemma[of "{u,v}"] by blast
  assume eq: "hd (Dec \<BB>\<^sub>F {u,v} u) = hd (Dec \<BB>\<^sub>F {u,v} v)"
  hence "u \<in> (hd (Dec \<BB>\<^sub>F {u,v} u))*" 
    using basis unfolding free_basis_def
    by (metis basis_gen_hull free_hull.simps free_hull_hull insertI1 insert_absorb2 sing_gen)
  moreover have  "v \<in> (hd (Dec \<BB>\<^sub>F {u,v} u))*"
    using basis eq unfolding free_basis_def
    by (metis basis_gen_hull free_hull_hull genset_sub_free insert_absorb2 insert_subset sing_gen) 
  ultimately show False
    using comm_root assms by blast
qed

theorem assumes "u \<cdot> v \<noteq> v \<cdot> u" 
  shows "xs \<in> lists {u, v} \<Longrightarrow> ys \<in> lists {u, v} \<Longrightarrow> concat xs = concat ys \<Longrightarrow> xs = ys"
proof (induct xs ys rule: list_induct2', simp)
  case (2 x xs)
  then show ?case
    using Nil_is_append_conv append_Nil assms by auto 
next
  case (3 y ys)
  then show ?case
    using Nil_is_append_conv append_Nil assms by auto 
next
  case (4 x xs y ys)
  then show ?case
  proof-
    have "u \<noteq> \<epsilon>" and "v \<noteq> \<epsilon>" using assms by force+
    hence "x \<noteq> \<epsilon>" and "y \<noteq> \<epsilon>" using \<open>x # xs \<in> lists {u, v}\<close> \<open>y # ys \<in> lists {u, v}\<close> by auto
    have or_x: "x = u \<or> x = v" and or_y: "y = u \<or> y = v" using \<open>x # xs \<in> lists {u, v}\<close> \<open>y # ys \<in> lists {u, v}\<close> by auto

    have hd_z: "z \<noteq> \<epsilon> \<Longrightarrow> z # zs \<in> lists {u, v} \<Longrightarrow> hd (Dec \<BB>\<^sub>F {u,v} (concat (z#zs))) = hd (Dec \<BB>\<^sub>F {u,v} z)" for z zs
    proof-
      assume "z \<noteq> \<epsilon>" "z # zs \<in> lists {u, v}"
      have "z \<in> \<langle>{u,v}\<rangle>\<^sub>F"
        using \<open>z # zs \<in> lists {u, v}\<close> by auto
      moreover have "concat zs \<in> \<langle>{u,v}\<rangle>\<^sub>F"
        using concat_tl[OF \<open>z # zs \<in> lists {u, v}\<close>] hull_in_free_hull[of "{u,v}"] by blast 
      ultimately have "Dec \<BB>\<^sub>F {u,v} (concat (z#zs)) = (Dec \<BB>\<^sub>F {u,v} z) \<cdot> (Dec \<BB>\<^sub>F {u,v} (concat zs))"
        using free_basis_dec_morph[of z "{u,v}" "concat zs"] by fastforce
      moreover have "Dec \<BB>\<^sub>F {u,v} z \<noteq> \<epsilon>"
        using \<open>z \<in> \<langle>{u, v}\<rangle>\<^sub>F\<close> basis_gen_hull_free dec_nemp'[OF  \<open>z \<noteq> \<epsilon>\<close>] by blast
      ultimately show "hd (Dec \<BB>\<^sub>F {u,v} (concat (z#zs))) = hd (Dec \<BB>\<^sub>F {u,v} z)"
        using hd_append  by simp
    qed
    
    have "hd (Dec \<BB>\<^sub>F {u,v} u) \<noteq> hd (Dec \<BB>\<^sub>F {u,v} v)" 
      using non_comm_hds_neq[OF assms].
    hence "x  = y"
      using hd_z[OF \<open>x \<noteq> \<epsilon>\<close> \<open>x # xs \<in> lists {u, v}\<close> , unfolded \<open>concat (x # xs) = concat (y # ys)\<close> hd_z[OF \<open>y \<noteq> \<epsilon>\<close> \<open>y # ys \<in> lists {u, v}\<close>]] or_x or_y 
      by fastforce
    thus ?thesis
      using "4.hyps" "4.prems" by auto 
  qed
qed

end