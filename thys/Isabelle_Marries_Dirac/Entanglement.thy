(* 
Authors: 

  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk;
  Yijun He, University of Cambridge, yh403@cam.ac.uk
*)

section \<open>Quantum Entanglement\<close>

theory Entanglement
imports
  Quantum
  More_Tensor
begin


subsection \<open>The Product States and Entangled States of a 2-qubits System\<close>

text \<open>Below we add the condition that @{term v} and @{term w} are two-dimensional states, otherwise 
@{term u} can always be represented by the tensor product of the 1-dimensional vector @{term 1} and 
@{term u} itself.\<close>

definition prod_state2:: "complex Matrix.mat \<Rightarrow> bool" where
"prod_state2 u \<equiv> if state 2 u then \<exists>v w. state 1 v \<and> state 1 w \<and> u = v \<Otimes> w else undefined"

definition entangled2:: "complex Matrix.mat \<Rightarrow> bool" where
"entangled2 u \<equiv> \<not> prod_state2 u"

text \<open>The Bell states are entangled states.\<close>

lemma bell00_is_entangled2 [simp]:
  "entangled2 |\<beta>\<^sub>0\<^sub>0\<rangle>" 
proof -
  have "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>0\<^sub>0\<rangle> \<noteq> v \<Otimes> w"
  proof((rule allI)+,(rule impI)+, rule notI)
    fix v w
    assume a0:"state 1 v" and a1:"state 1 w" and a2:"|\<beta>\<^sub>0\<^sub>0\<rangle> = v \<Otimes> w"
    have "(v $$ (0,0) * w $$ (0,0)) * (v $$ (1,0) * w $$ (1,0)) = 
          (v $$ (0,0) * w $$ (1,0)) * (v $$ (1,0) * w $$ (0,0))" by simp
    then have "(v \<Otimes> w) $$ (0,0) * (v \<Otimes> w) $$ (3,0) = (v \<Otimes> w) $$ (1,0) * (v \<Otimes> w) $$ (2,0)"
      using a0 a1 by simp
    then have "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (0,0) * |\<beta>\<^sub>0\<^sub>0\<rangle> $$ (3,0) = |\<beta>\<^sub>0\<^sub>0\<rangle> $$ (1,0) * |\<beta>\<^sub>0\<^sub>0\<rangle> $$ (2,0)"
      using a2 by simp
    then have "1/ sqrt 2 * 1/sqrt 2 = 0" by simp
    thus False by simp
  qed
  thus ?thesis by(simp add: entangled2_def prod_state2_def)
qed

lemma bell01_is_entangled2 [simp]:
  "entangled2 |\<beta>\<^sub>0\<^sub>1\<rangle>"
proof -
  have "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>0\<^sub>1\<rangle> \<noteq> v \<Otimes> w"
  proof((rule allI)+,(rule impI)+, rule notI)
    fix v w
    assume a0:"state 1 v" and a1:"state 1 w" and a2:"|\<beta>\<^sub>0\<^sub>1\<rangle> = v \<Otimes> w"
    have "(v $$ (0,0) * w $$ (1,0)) * (v $$ (1,0) * w $$ (0,0)) = 
          (v $$ (0,0) * w $$ (0,0)) * (v $$ (1,0) * w $$ (1,0))" by simp
    then have "(v \<Otimes> w) $$ (1,0) * (v \<Otimes> w) $$ (2,0) = (v \<Otimes> w) $$ (0,0) * (v \<Otimes> w) $$ (3,0)"
      using a0 a1 by simp
    then have "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (1,0) * |\<beta>\<^sub>0\<^sub>1\<rangle> $$ (2,0) = |\<beta>\<^sub>0\<^sub>1\<rangle> $$ (0,0) * |\<beta>\<^sub>0\<^sub>1\<rangle> $$ (3,0)"
      using a2 by simp
    then have "1/sqrt 2 * 1/sqrt 2 = 0" 
      using bell01_index by simp
    thus False by simp
  qed
  thus ?thesis by(simp add: entangled2_def prod_state2_def)
qed

lemma bell10_is_entangled2 [simp]:
  "entangled2 |\<beta>\<^sub>1\<^sub>0\<rangle>"
proof -
  have "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>1\<^sub>0\<rangle> \<noteq> v \<Otimes> w"
  proof((rule allI)+,(rule impI)+, rule notI)
    fix v w
    assume a0:"state 1 v" and a1:"state 1 w" and a2:"|\<beta>\<^sub>1\<^sub>0\<rangle> = v \<Otimes> w"
    have "(v $$ (0,0) * w $$ (0,0)) * (v $$ (1,0) * w $$ (1,0)) = 
          (v $$ (0,0) * w $$ (1,0)) * (v $$ (1,0) * w $$ (0,0))" by simp
    then have "(v \<Otimes> w) $$ (0,0) * (v \<Otimes> w) $$ (3,0) = (v \<Otimes> w) $$ (1,0) * (v \<Otimes> w) $$ (2,0)"
      using a0 a1 by simp
    then have "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (1,0) * |\<beta>\<^sub>1\<^sub>0\<rangle> $$ (2,0) = |\<beta>\<^sub>1\<^sub>0\<rangle> $$ (0,0) * |\<beta>\<^sub>1\<^sub>0\<rangle> $$ (3,0)"
      using a2 by simp
    then have "1/sqrt 2 * 1/sqrt 2 = 0" by simp
    thus False by simp
  qed
  thus ?thesis by(simp add: entangled2_def prod_state2_def)
qed

lemma bell11_is_entangled2 [simp]:
  "entangled2 |\<beta>\<^sub>1\<^sub>1\<rangle>"
proof -
  have "\<forall>v w. state 1 v \<longrightarrow> state 1 w \<longrightarrow> |\<beta>\<^sub>1\<^sub>1\<rangle> \<noteq> v \<Otimes> w"
  proof((rule allI)+,(rule impI)+, rule notI)
    fix v w
    assume a0:"state 1 v" and a1:"state 1 w" and a2:"|\<beta>\<^sub>1\<^sub>1\<rangle> = v \<Otimes> w"
    have "(v $$ (0,0) * w $$ (1,0)) * (v $$ (1,0) * w $$ (0,0)) = 
          (v $$ (0,0) * w $$ (0,0)) * (v $$ (1,0) * w $$ (1,0))" by simp
    then have "(v \<Otimes> w) $$ (1,0) * (v \<Otimes> w) $$ (2,0) = (v \<Otimes> w) $$ (0,0) * (v \<Otimes> w) $$ (3,0)"
      using a0 a1 by simp
    then have "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (1,0) * |\<beta>\<^sub>1\<^sub>1\<rangle> $$ (2,0) = |\<beta>\<^sub>1\<^sub>1\<rangle> $$ (0,0) * |\<beta>\<^sub>1\<^sub>1\<rangle> $$ (3,0)"
      using a2 by simp
    then have "1/sqrt 2 * 1/sqrt 2 = 0"
      using bell_11_index by simp
    thus False by simp
  qed
  thus ?thesis by(simp add: entangled2_def prod_state2_def)
qed

text \<open>
An entangled state is a state that cannot be broken down as the tensor product of smaller states.
\<close>

definition prod_state:: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
"prod_state m u \<equiv> if state m u then \<exists>n p::nat.\<exists>v w. state n v \<and> state p w \<and> 
  n < m \<and> p < m \<and>  u = v \<Otimes> w else undefined"

definition entangled:: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
"entangled n v \<equiv> \<not> (prod_state n v)"

(* To do: as an exercise prove the equivalence between entangled2 and (entangled 2). *)

lemma sanity_check: 
  "\<not>(entangled 2 (mat_of_cols_list 2 [[1/sqrt(2), 1/sqrt(2)]] \<Otimes> mat_of_cols_list 2 [[1/sqrt(2), 1/sqrt(2)]]))"
proof -
  define u where "u = mat_of_cols_list 2 [[1/sqrt(2), 1/sqrt(2)]]"
  then have "state 1 u"
  proof -
    have "dim_col u = 1"
      using u_def mat_of_cols_list_def by simp
    moreover have f:"dim_row u = 2"
      using u_def mat_of_cols_list_def by simp
    moreover have "\<parallel>Matrix.col u 0\<parallel> = 1"
    proof -
      have "(\<Sum>i<2. (cmod (u $$ (i, 0)))\<^sup>2) = (1/sqrt 2)\<^sup>2 + (1/sqrt 2)\<^sup>2"
        by(simp add: u_def cmod_def numeral_2_eq_2)
      then have "\<parallel>Matrix.col u 0\<parallel> = sqrt ((1/sqrt 2)\<^sup>2 + (1/sqrt 2)\<^sup>2)"
        using f by(auto simp: Matrix.col_def u_def cpx_vec_length_def)
      thus ?thesis by(simp add: power_divide)
    qed
    ultimately show ?thesis by(simp add: state_def)
  qed
  then have "state 2 (u \<Otimes> u)"
    using tensor_state by(metis one_add_one)
  thus ?thesis
    using entangled_def prod_state_def by(metis \<open>state 1 u\<close> one_less_numeral_iff semiring_norm(76) u_def)
qed

end