(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>n\<close>-ary operation\<close>
theory CZH_Sets_NOP
  imports CZH_Sets_FBRelations
begin



subsection\<open>Partial \<open>n\<close>-ary operation\<close>

locale pnop = vsv f for A n f :: V +
  assumes pnop_n: "n \<in>\<^sub>\<circ> \<omega>" 
    and pnop_vdomain: "\<D>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A ^\<^sub>\<times> n"
    and pnop_vrange: "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"


text\<open>Rules.\<close>

lemma pnopI[intro]:
  assumes "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  shows "pnop A n f"
  using assms unfolding pnop_def pnop_axioms_def by blast

lemma pnopD[dest]:
  assumes "pnop A n f"
  shows "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  using assms unfolding pnop_def pnop_axioms_def by blast+

lemma pnopE[elim]:
  assumes "pnop A n f"
  obtains "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  using assms by force



subsection\<open>Total \<open>n\<close>-ary operation\<close>

locale nop = vsv f for A n f :: V +
  assumes nop_n: "n \<in>\<^sub>\<circ> \<omega>" 
    and nop_vdomain: "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and nop_vrange: "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"

sublocale nop \<subseteq> pnop A n f
proof(intro pnopI)
  show "vsv f" by (rule vsv_axioms)
  show "n \<in>\<^sub>\<circ> \<omega>" by (rule nop_n)
  from nop_vdomain show "\<D>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A ^\<^sub>\<times> n" by simp
  show "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A" by (rule nop_vrange)
qed


text\<open>Rules.\<close>

lemma nopI[intro]:
  assumes "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  shows "nop A n f"
  using assms unfolding nop_def nop_axioms_def by blast

lemma nopD[dest]:
  assumes "nop A n f"
  shows "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  using assms unfolding nop_def nop_axioms_def by blast+

lemma nopE[elim]:
  assumes "nop A n f"
  obtains "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  using assms by force



subsection\<open>Injective \<open>n\<close>-ary operation\<close>

locale nop_v11 = v11 f for A n f :: V +
  assumes nop_v11_n: "n \<in>\<^sub>\<circ> \<omega>" 
    and nop_v11_vdomain: "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and nop_v11_vrange: "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"

sublocale nop_v11 \<subseteq> nop 
proof
  show "vsv f" by (rule vsv_axioms)
  show "n \<in>\<^sub>\<circ> \<omega>" by (rule nop_v11_n)
  show "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n" by (rule nop_v11_vdomain)
  show "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A" by (rule nop_v11_vrange)
qed


text\<open>Rules.\<close>

lemma nop_v11I[intro]:
  assumes "v11 f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  shows "nop_v11 A n f"
  using assms unfolding nop_v11_def nop_v11_axioms_def by blast

lemma nop_v11D[dest]:
  assumes "nop_v11 A n f"
  shows "v11 f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  using assms unfolding nop_v11_def nop_v11_axioms_def by blast+

lemma nop_v11E[elim]:
  assumes "nop_v11 A n f"
  obtains "v11 f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A"
  using assms by force



subsection\<open>Surjective \<open>n\<close>-ary operation\<close>

locale nop_onto = vsv f for A n f :: V +
  assumes nop_onto_n: "n \<in>\<^sub>\<circ> \<omega>" 
    and nop_onto_vdomain: "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and nop_onto_vrange: "\<R>\<^sub>\<circ> f = A"

sublocale nop_onto \<subseteq> nop 
proof
  show "vsv f" by (rule vsv_axioms)
  show "n \<in>\<^sub>\<circ> \<omega>" by (rule nop_onto_n)
  show "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n" by (rule nop_onto_vdomain)
  show "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A" by (simp add: nop_onto_vrange)
qed


text\<open>Rules.\<close>

lemma nop_ontoI[intro]:
  assumes "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f = A"
  shows "nop_onto A n f"
  using assms unfolding nop_onto_def nop_onto_axioms_def by blast

lemma nop_ontoD[dest]:
  assumes "nop_onto A n f"
  shows "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f = A"
  using assms unfolding nop_onto_def nop_onto_axioms_def by auto

lemma nop_ontoE[elim]:
  assumes "nop_onto A n f"
  obtains "vsv f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f = A"
  using assms by force



subsection\<open>Bijective \<open>n\<close>-ary operation\<close>

locale nop_bij = v11 f for A n f :: V +
  assumes nop_bij_n: "n \<in>\<^sub>\<circ> \<omega>" 
    and nop_bij_vdomain: "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and nop_bij_vrange: "\<R>\<^sub>\<circ> f = A"

sublocale nop_bij \<subseteq> nop_v11 
proof
  show "v11 f" by (rule v11_axioms)
  show "n \<in>\<^sub>\<circ> \<omega>" by (rule nop_bij_n)
  show "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n" by (rule nop_bij_vdomain)
  show "\<R>\<^sub>\<circ> f \<subseteq>\<^sub>\<circ> A" by (simp add: nop_bij_vrange)
qed

sublocale nop_bij \<subseteq> nop_onto 
proof
  show "vsv f" by (rule vsv_axioms)
  show "n \<in>\<^sub>\<circ> \<omega>" by (rule nop_bij_n)
  show "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n" by (rule nop_bij_vdomain)
  show "\<R>\<^sub>\<circ> f = A" by (rule nop_bij_vrange)
qed


text\<open>Rules.\<close>

lemma nop_bijI[intro]:
  assumes "v11 f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f = A"
  shows "nop_bij A n f"
  using assms unfolding nop_bij_def nop_bij_axioms_def by blast

lemma nop_bijD[dest]:
  assumes "nop_bij A n f"
  shows "v11 f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f = A"
  using assms unfolding nop_bij_def nop_bij_axioms_def by auto

lemma nop_bijE[elim]:
  assumes "nop_bij A n f"
  obtains "v11 f"
    and "n \<in>\<^sub>\<circ> \<omega>"
    and "\<D>\<^sub>\<circ> f = A ^\<^sub>\<times> n"
    and "\<R>\<^sub>\<circ> f = A"
  using assms by force



subsection\<open>Scalar\<close>

locale scalar = 
  fixes A f
  assumes scalar_nop: "nop A 0 f"

sublocale scalar \<subseteq> nop A 0 f
  rewrites scalar_vdomain[simp]: "A ^\<^sub>\<times> 0 = set {0}"
  by (auto simp: scalar_nop)


text\<open>Rules.\<close>

lemmas scalarI[intro] = scalar.intro

lemma scalarD[dest]:
  assumes "scalar A f"
  shows "nop A 0 f" 
  using assms unfolding scalar_def by auto

lemma scalarE[elim]:
  assumes "scalar A f"
  obtains "nop A 0 f"
  using assms by auto



subsection\<open>Unary operation\<close>

locale unop = nop A \<open>1\<^sub>\<nat>\<close> f for A f


text\<open>Rules.\<close>

lemmas unopI[intro] = unop.intro

lemma unopD[dest]:
  assumes "unop A f"
  shows "nop A (1\<^sub>\<nat>) f" 
  using assms unfolding unop_def by auto

lemma unopE[elim]:
  assumes "unop A f"
  obtains "nop A (1\<^sub>\<nat>) f"
  using assms by blast



subsection\<open>Injective unary operation\<close>

locale unop_v11 = nop_v11 A \<open>1\<^sub>\<nat>\<close> f for A f

sublocale unop_v11 \<subseteq> unop A f by (intro unopI) (simp add: nop_axioms)


text\<open>Rules.\<close>

lemma unop_v11I[intro]:
  assumes "nop_v11 A (1\<^sub>\<nat>) f"
  shows "unop_v11 A f"
  using assms by (rule unop_v11.intro)

lemma unop_v11D[dest]:
  assumes "unop_v11 A f"
  shows "nop_v11 A (1\<^sub>\<nat>) f"
  using assms by (rule unop_v11.axioms)

lemma unop_v11E[elim]:
  assumes "unop_v11 A f"
  obtains "nop_v11 A (1\<^sub>\<nat>) f"
  using assms by blast



subsection\<open>Surjective unary operation\<close>

locale unop_onto = nop_onto A \<open>1\<^sub>\<nat>\<close> f for A f

sublocale unop_onto \<subseteq> unop A f by (intro unopI) (simp add: nop_axioms)


text\<open>Rules.\<close>

lemma unop_ontoI[intro]:
  assumes "nop_onto A (1\<^sub>\<nat>) f"
  shows "unop_onto A f"
  using assms by (rule unop_onto.intro)

lemma unop_ontoD[dest]:
  assumes "unop_onto A f"
  shows "nop_onto A (1\<^sub>\<nat>) f"
  using assms by (rule unop_onto.axioms)

lemma unop_ontoE[elim]:
  assumes "unop_onto A f"
  obtains "nop_onto A (1\<^sub>\<nat>) f"
  using assms by blast

lemma unop_ontoI'[intro]:
  assumes "unop A f" and "A \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
  shows "unop_onto A f"
proof-
  interpret unop A f by (rule assms(1))
  from assms(2) nop_vrange have "A = \<R>\<^sub>\<circ> f" by simp
  with assms(1) show "unop_onto A f" by auto
qed



subsection\<open>Bijective unary operation\<close>

locale unop_bij = nop_bij A \<open>1\<^sub>\<nat>\<close> f for A f

sublocale unop_bij \<subseteq> unop_v11 A f  
  by (intro unop_v11I) (simp add: nop_v11_axioms)

sublocale unop_bij \<subseteq> unop_onto A f  
  by (intro unop_ontoI) (simp add: nop_onto_axioms)


text\<open>Rules.\<close>

lemma unop_bijI[intro]:
  assumes "nop_bij A (1\<^sub>\<nat>) f"
  shows "unop_bij A f"
  using assms by (rule unop_bij.intro)

lemma unop_bijD[dest]:
  assumes "unop_bij A f"
  shows "nop_bij A (1\<^sub>\<nat>) f"
  using assms by (rule unop_bij.axioms)

lemma unop_bijE[elim]:
  assumes "unop_bij A f"
  obtains "nop_bij A (1\<^sub>\<nat>) f"
  using assms by blast

lemma unop_bijI'[intro]:
  assumes "unop_v11 A f" and "A \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
  shows "unop_bij A f"
proof-
  interpret unop_v11 A f by (rule assms(1))
  from assms(2) nop_vrange have "A = \<R>\<^sub>\<circ> f" by simp
  with assms(1) show "unop_bij A f" by auto
qed



subsection\<open>Partial binary operation\<close>

locale pbinop = pnop A \<open>2\<^sub>\<nat>\<close> f for A f

sublocale pbinop \<subseteq> dom: fbrelation \<open>\<D>\<^sub>\<circ> f\<close> 
proof
  from pnop_vdomain show "fpairs (\<D>\<^sub>\<circ> f) = \<D>\<^sub>\<circ> f"
    by (intro vsubset_antisym vsubsetI) auto
qed


text\<open>Rules.\<close>

lemmas pbinopI[intro] = pbinop.intro

lemma pbinopD[dest]:
  assumes "pbinop A f"
  shows "pnop A (2\<^sub>\<nat>) f"
  using assms unfolding pbinop_def by auto

lemma pbinopE[elim]:
  assumes "pbinop A f"
  obtains "pnop A (2\<^sub>\<nat>) f"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in pbinop) fbinop_vcard: 
  assumes "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f" 
  shows "vcard x = 2\<^sub>\<nat>"
proof-
  from assms dom.fbrelation_axioms obtain a b where x_def: "x = [a, b]\<^sub>\<circ>" by blast
  show ?thesis by (auto simp: x_def nat_omega_simps)
qed




subsection\<open>Total binary operation\<close>

locale binop = nop A \<open>2\<^sub>\<nat>\<close> f for A f

sublocale binop \<subseteq> pbinop by unfold_locales


text\<open>Rules.\<close>

lemmas binopI[intro] = binop.intro

lemma binopD[dest]:
  assumes "binop A f"
  shows "nop A (2\<^sub>\<nat>) f"
  using assms unfolding binop_def by auto

lemma binopE[elim]:
  assumes "binop A f"
  obtains "nop A (2\<^sub>\<nat>) f"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in binop) binop_app_in_vrange[intro]:
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A"
  shows "f\<lparr>a, b\<rparr>\<^sub>\<bullet> \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
proof-
  from assms have "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> A ^\<^sub>\<times> 2\<^sub>\<nat>" by (auto simp: nat_omega_simps)
  then show ?thesis by (simp add: nop_vdomain vsv_vimageI2)
qed



subsection\<open>Injective binary operation\<close>

locale binop_v11 = nop_v11 A \<open>2\<^sub>\<nat>\<close> f for A f

sublocale binop_v11 \<subseteq> binop A f by (intro binopI) (simp add: nop_axioms)


text\<open>Rules.\<close>

lemma binop_v11I[intro]:
  assumes "nop_v11 A (2\<^sub>\<nat>) f"
  shows "binop_v11 A f"
  using assms by (rule binop_v11.intro)

lemma binop_v11D[dest]:
  assumes "binop_v11 A f"
  shows "nop_v11 A (2\<^sub>\<nat>) f"
  using assms by (rule binop_v11.axioms)

lemma binop_v11E[elim]:
  assumes "binop_v11 A f"
  obtains "nop_v11 A (2\<^sub>\<nat>) f"
  using assms by blast



subsection\<open>Surjective binary operation\<close>

locale binop_onto = nop_onto A \<open>2\<^sub>\<nat>\<close> f for A f

sublocale binop_onto \<subseteq> binop A f by (intro binopI) (simp add: nop_axioms)


text\<open>Rules.\<close>

lemma binop_ontoI[intro]:
  assumes "nop_onto A (2\<^sub>\<nat>) f"
  shows "binop_onto A f"
  using assms by (rule binop_onto.intro)

lemma binop_ontoD[dest]:
  assumes "binop_onto A f"
  shows "nop_onto A (2\<^sub>\<nat>) f"
  using assms by (rule binop_onto.axioms)

lemma binop_ontoE[elim]:
  assumes "binop_onto A f"
  obtains "nop_onto A (2\<^sub>\<nat>) f"
  using assms by blast

lemma binop_ontoI'[intro]:
  assumes "binop A f" and "A \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
  shows "binop_onto A f"
proof-
  interpret binop A f by (rule assms(1))
  from assms(2) nop_vrange have "A = \<R>\<^sub>\<circ> f" by simp
  with assms(1) show "binop_onto A f" by auto
qed



subsection\<open>Bijective binary operation\<close>

locale binop_bij = nop_bij A \<open>2\<^sub>\<nat>\<close> f for A f

sublocale binop_bij \<subseteq> binop_v11 A f 
  by (intro binop_v11I) (simp add: nop_v11_axioms)

sublocale binop_bij \<subseteq> binop_onto A f 
  by (intro binop_ontoI) (simp add: nop_onto_axioms)


text\<open>Rules.\<close>

lemma binop_bijI[intro]:
  assumes "nop_bij A (2\<^sub>\<nat>) f"
  shows "binop_bij A f"
  using assms by (rule binop_bij.intro)

lemma binop_bijD[dest]:
  assumes "binop_bij A f"
  shows "nop_bij A (2\<^sub>\<nat>) f"
  using assms by (rule binop_bij.axioms)

lemma binop_bijE[elim]:
  assumes "binop_bij A f"
  obtains "nop_bij A (2\<^sub>\<nat>) f"
  using assms by blast

lemma binop_bijI'[intro]:
  assumes "binop_v11 A f" and "A \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
  shows "binop_bij A f"
proof-
  interpret binop_v11 A f by (rule assms(1))
  from assms(2) nop_vrange have "A = \<R>\<^sub>\<circ> f" by simp
  with assms(1) show "binop_bij A f" by auto
qed



subsection\<open>Flip\<close>

definition fflip :: "V \<Rightarrow> V"
  where "fflip f = (\<lambda>ab\<in>\<^sub>\<circ>(\<D>\<^sub>\<circ> f)\<inverse>\<^sub>\<bullet>. f\<lparr>ab\<lparr>1\<^sub>\<nat>\<rparr>, ab\<lparr>0\<rparr>\<rparr>\<^sub>\<bullet>)"


text\<open>Elementary properties.\<close>

lemma fflip_vsv: "vsv (fflip f)"
  by (intro vsvI) (auto simp: fflip_def)

lemma vdomain_fflip[simp]: "\<D>\<^sub>\<circ> (fflip f) = (\<D>\<^sub>\<circ> f)\<inverse>\<^sub>\<bullet>" 
  unfolding fflip_def by simp

lemma (in pbinop) vrange_fflip: "\<R>\<^sub>\<circ> (fflip f) = \<R>\<^sub>\<circ> f"
  unfolding fflip_def
proof(intro vsubset_antisym vsubsetI)
  fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> ((\<lambda>x\<in>\<^sub>\<circ>(\<D>\<^sub>\<circ> f)\<inverse>\<^sub>\<bullet>. f\<lparr>x\<lparr>1\<^sub>\<nat>\<rparr>, x\<lparr>0\<rparr>\<rparr>\<^sub>\<bullet>))" 
  then obtain x where "x \<in>\<^sub>\<circ> (\<D>\<^sub>\<circ> f)\<inverse>\<^sub>\<bullet>" and y_def: "y = f\<lparr>x\<lparr>1\<^sub>\<nat>\<rparr>, x\<lparr>0\<rparr>\<rparr>\<^sub>\<bullet>" by fast
  then obtain a b where x_def: "x = [b, a]\<^sub>\<circ>" by clarsimp
  have y_def': "y = f\<lparr>a, b\<rparr>\<^sub>\<bullet>" 
    unfolding y_def x_def by (simp add: nat_omega_simps)
  from x_def \<open>x \<in>\<^sub>\<circ> (\<D>\<^sub>\<circ> f)\<inverse>\<^sub>\<bullet>\<close> have "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f" by clarsimp
  then show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f" unfolding y_def' by (simp add: vsv_vimageI2)
next
  fix y assume "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> f"
  with vrange_atD obtain x where x: "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f" and y_def: "y = f\<lparr>x\<rparr>" by blast
  with dom.fbrelation obtain a b where x_def: "x = [a, b]\<^sub>\<circ>" by blast
  from x have ba: "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> (\<D>\<^sub>\<circ> f)\<inverse>\<^sub>\<bullet>" unfolding x_def by clarsimp
  then have y_def': "y = f\<lparr>[b, a]\<^sub>\<circ>\<lparr>1\<^sub>\<nat>\<rparr>, [b, a]\<^sub>\<circ>\<lparr>0\<rparr>\<rparr>\<^sub>\<bullet>"
    unfolding y_def x_def by (auto simp: nat_omega_simps)
  then show "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> ((\<lambda>ab\<in>\<^sub>\<circ>(\<D>\<^sub>\<circ> f)\<inverse>\<^sub>\<bullet>. f\<lparr>ab\<lparr>1\<^sub>\<nat>\<rparr>, ab\<lparr>0\<rparr>\<rparr>\<^sub>\<bullet>))"
    unfolding y_def'
    by (metis (lifting) ba beta rel_VLambda.vsv_vimageI2 vdomain_VLambda)
qed

lemma fflip_app[simp]: 
  assumes "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f"
  shows "fflip f\<lparr>b, a\<rparr>\<^sub>\<bullet> = f\<lparr>a, b\<rparr>\<^sub>\<bullet>"
proof-
  from assms have "[b, a]\<^sub>\<circ> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (fflip f)" by clarsimp
  then show "fflip f\<lparr>b, a\<rparr>\<^sub>\<bullet> = f\<lparr>a, b\<rparr>\<^sub>\<bullet>" 
    by (simp add: fflip_def ord_of_nat_succ_vempty)
qed

lemma (in pbinop) pbinop_fflip_fflip: "fflip (fflip f) = f"
proof(rule vsv_eqI)
  show "vsv (fflip (fflip f))" by (simp add: fflip_vsv)
  show "vsv f" by (rule vsv_axioms)
  show dom: "\<D>\<^sub>\<circ> (fflip (fflip f)) = \<D>\<^sub>\<circ> f" by simp
  fix x assume prems: "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (fflip (fflip f))"
  with dom dom.fbrelation_axioms obtain a b where x_def: "x = [a, b]\<^sub>\<circ>" by auto
  from prems show "fflip (fflip f)\<lparr>x\<rparr> = f\<lparr>x\<rparr>" 
    unfolding x_def by (auto simp: fconverseI)
qed

lemma (in binop) pbinop_fflip_app[simp]: 
  assumes "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> A"
  shows "fflip f\<lparr>b, a\<rparr>\<^sub>\<bullet> = f\<lparr>a, b\<rparr>\<^sub>\<bullet>"
proof-
  from assms have "[a, b]\<^sub>\<circ> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f" 
    unfolding nop_vdomain by (auto simp: nat_omega_simps)
  then show ?thesis by auto
qed

lemma fflip_vsingleton: "fflip (set {\<langle>[a, b]\<^sub>\<circ>, c\<rangle>}) = set {\<langle>[b, a]\<^sub>\<circ>, c\<rangle>}"
proof-
  have dom_lhs: "\<D>\<^sub>\<circ> (fflip (set {\<langle>[a, b]\<^sub>\<circ>, c\<rangle>})) = set {[b, a]\<^sub>\<circ>}"
    unfolding fflip_def by auto
  have dom_rhs: "\<D>\<^sub>\<circ> (set {\<langle>[b, a]\<^sub>\<circ>, c\<rangle>}) = set {[b, a]\<^sub>\<circ>}" by simp
  show ?thesis
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix q assume "q \<in>\<^sub>\<circ> set {[b, a]\<^sub>\<circ>}"
    then have q_def: "q = [b, a]\<^sub>\<circ>" by simp
    show "fflip (set {\<langle>[a, b]\<^sub>\<circ>, c\<rangle>})\<lparr>q\<rparr> = set {\<langle>[b, a]\<^sub>\<circ>, c\<rangle>}\<lparr>q\<rparr>"
      unfolding q_def by auto
  qed (auto simp: fflip_def)
qed

text\<open>\newpage\<close>

end