(*  Title:      JinjaDCI/J/DefAss.thy
    Author:     Tobias Nipkow, Susannah Mansky
    Copyright   2003 Technische Universitaet Muenchen, 2019-20 UIUC

    Based on the Jinja theory J/DefAss.thy by Tobias Nipkow
*)

section \<open> Definite assignment \<close>

theory DefAss imports BigStep begin

subsection "Hypersets"

type_synonym 'a hyperset = "'a set option"

definition hyperUn :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> 'a hyperset"   (infixl "\<squnion>" 65)
where
  "A \<squnion> B  \<equiv>  case A of None \<Rightarrow> None
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> None | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>A \<union> B\<rfloor>)"

definition hyperInt :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> 'a hyperset"   (infixl "\<sqinter>" 70)
where
  "A \<sqinter> B  \<equiv>  case A of None \<Rightarrow> B
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> \<lfloor>A\<rfloor> | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>A \<inter> B\<rfloor>)"

definition hyperDiff1 :: "'a hyperset \<Rightarrow> 'a \<Rightarrow> 'a hyperset"   (infixl "\<ominus>" 65)
where
  "A \<ominus> a  \<equiv>  case A of None \<Rightarrow> None | \<lfloor>A\<rfloor> \<Rightarrow> \<lfloor>A - {a}\<rfloor>"

definition hyper_isin :: "'a \<Rightarrow> 'a hyperset \<Rightarrow> bool"   (infix "\<in>\<in>" 50)
where
  "a \<in>\<in> A  \<equiv>  case A of None \<Rightarrow> True | \<lfloor>A\<rfloor> \<Rightarrow> a \<in> A"

definition hyper_subset :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> bool"   (infix "\<sqsubseteq>" 50)
where
  "A \<sqsubseteq> B  \<equiv>  case B of None \<Rightarrow> True
                 | \<lfloor>B\<rfloor> \<Rightarrow> (case A of None \<Rightarrow> False | \<lfloor>A\<rfloor> \<Rightarrow> A \<subseteq> B)"

lemmas hyperset_defs =
 hyperUn_def hyperInt_def hyperDiff1_def hyper_isin_def hyper_subset_def

lemma [simp]: "\<lfloor>{}\<rfloor> \<squnion> A = A  \<and>  A \<squnion> \<lfloor>{}\<rfloor> = A"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "\<lfloor>A\<rfloor> \<squnion> \<lfloor>B\<rfloor> = \<lfloor>A \<union> B\<rfloor> \<and> \<lfloor>A\<rfloor> \<ominus> a = \<lfloor>A - {a}\<rfloor>"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "None \<squnion> A = None \<and> A \<squnion> None = None"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "a \<in>\<in> None \<and> None \<ominus> a = None"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma hyper_isin_union: "x \<in>\<in> \<lfloor>A\<rfloor> \<Longrightarrow> x \<in>\<in> \<lfloor>A\<rfloor> \<squnion> B"
 by(case_tac B, auto simp: hyper_isin_def)

lemma hyperUn_assoc: "(A \<squnion> B) \<squnion> C = A \<squnion> (B \<squnion> C)"
(*<*)by(simp add:hyperset_defs Un_assoc)(*>*)

lemma hyper_insert_comm: "A \<squnion> \<lfloor>{a}\<rfloor> = \<lfloor>{a}\<rfloor> \<squnion> A \<and> A \<squnion> (\<lfloor>{a}\<rfloor> \<squnion> B) = \<lfloor>{a}\<rfloor> \<squnion> (A \<squnion> B)"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma hyper_comm: "A \<squnion> B = B \<squnion> A \<and> A \<squnion> B \<squnion> C = B \<squnion> A \<squnion> C"
apply(case_tac A, simp, case_tac B, simp)
apply(case_tac C, simp add: Un_commute)
apply(simp add: Un_left_commute Un_commute)
done

subsection "Definite assignment"

primrec
  \<A>  :: "'a exp \<Rightarrow> 'a hyperset"
  and \<A>s :: "'a exp list \<Rightarrow> 'a hyperset"
where
  "\<A> (new C) = \<lfloor>{}\<rfloor>"
| "\<A> (Cast C e) = \<A> e"
| "\<A> (Val v) = \<lfloor>{}\<rfloor>"
| "\<A> (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = \<A> e\<^sub>1 \<squnion> \<A> e\<^sub>2"
| "\<A> (Var V) = \<lfloor>{}\<rfloor>"
| "\<A> (LAss V e) = \<lfloor>{V}\<rfloor> \<squnion> \<A> e"
| "\<A> (e\<bullet>F{D}) = \<A> e"
| "\<A> (C\<bullet>\<^sub>sF{D}) = \<lfloor>{}\<rfloor>"
| "\<A> (e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = \<A> e\<^sub>1 \<squnion> \<A> e\<^sub>2"
| "\<A> (C\<bullet>\<^sub>sF{D}:=e\<^sub>2) = \<A> e\<^sub>2"
| "\<A> (e\<bullet>M(es)) = \<A> e \<squnion> \<A>s es"
| "\<A> (C\<bullet>\<^sub>sM(es)) = \<A>s es"
| "\<A> ({V:T; e}) = \<A> e \<ominus> V"
| "\<A> (e\<^sub>1;;e\<^sub>2) = \<A> e\<^sub>1 \<squnion> \<A> e\<^sub>2"
| "\<A> (if (e) e\<^sub>1 else e\<^sub>2) =  \<A> e \<squnion> (\<A> e\<^sub>1 \<sqinter> \<A> e\<^sub>2)"
| "\<A> (while (b) e) = \<A> b"
| "\<A> (throw e) = None"
| "\<A> (try e\<^sub>1 catch(C V) e\<^sub>2) = \<A> e\<^sub>1 \<sqinter> (\<A> e\<^sub>2 \<ominus> V)"
| "\<A> (INIT C (Cs,b) \<leftarrow> e) = \<lfloor>{}\<rfloor>"
| "\<A> (RI (C,e);Cs \<leftarrow> e') = \<A> e"

| "\<A>s ([]) = \<lfloor>{}\<rfloor>"
| "\<A>s (e#es) = \<A> e \<squnion> \<A>s es"

primrec
  \<D>  :: "'a exp \<Rightarrow> 'a hyperset \<Rightarrow> bool"
  and \<D>s :: "'a exp list \<Rightarrow> 'a hyperset \<Rightarrow> bool"
where
  "\<D> (new C) A = True"
| "\<D> (Cast C e) A = \<D> e A"
| "\<D> (Val v) A = True"
| "\<D> (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) A = (\<D> e\<^sub>1 A \<and> \<D> e\<^sub>2 (A \<squnion> \<A> e\<^sub>1))"
| "\<D> (Var V) A = (V \<in>\<in> A)"
| "\<D> (LAss V e) A = \<D> e A"
| "\<D> (e\<bullet>F{D}) A = \<D> e A"
| "\<D> (C\<bullet>\<^sub>sF{D}) A = True"
| "\<D> (e\<^sub>1\<bullet>F{D}:=e\<^sub>2) A = (\<D> e\<^sub>1 A \<and> \<D> e\<^sub>2 (A \<squnion> \<A> e\<^sub>1))"
| "\<D> (C\<bullet>\<^sub>sF{D}:=e\<^sub>2) A = \<D> e\<^sub>2 A"
| "\<D> (e\<bullet>M(es)) A = (\<D> e A \<and> \<D>s es (A \<squnion> \<A> e))"
| "\<D> (C\<bullet>\<^sub>sM(es)) A = \<D>s es A"
| "\<D> ({V:T; e}) A = \<D> e (A \<ominus> V)"
| "\<D> (e\<^sub>1;;e\<^sub>2) A = (\<D> e\<^sub>1 A \<and> \<D> e\<^sub>2 (A \<squnion> \<A> e\<^sub>1))"
| "\<D> (if (e) e\<^sub>1 else e\<^sub>2) A =
  (\<D> e A \<and> \<D> e\<^sub>1 (A \<squnion> \<A> e) \<and> \<D> e\<^sub>2 (A \<squnion> \<A> e))"
| "\<D> (while (e) c) A = (\<D> e A \<and> \<D> c (A \<squnion> \<A> e))"
| "\<D> (throw e) A = \<D> e A"
| "\<D> (try e\<^sub>1 catch(C V) e\<^sub>2) A = (\<D> e\<^sub>1 A \<and> \<D> e\<^sub>2 (A \<squnion> \<lfloor>{V}\<rfloor>))"
| "\<D> (INIT C (Cs,b) \<leftarrow> e) A = \<D> e A"
| "\<D> (RI (C,e);Cs \<leftarrow> e') A = (\<D> e A \<and> \<D> e' A)"

| "\<D>s ([]) A = True"
| "\<D>s (e#es) A = (\<D> e A \<and> \<D>s es (A \<squnion> \<A> e))"

lemma As_map_Val[simp]: "\<A>s (map Val vs) = \<lfloor>{}\<rfloor>"
(*<*)by (induct vs) simp_all(*>*)

lemma D_append[iff]: "\<And>A. \<D>s (es @ es') A = (\<D>s es A \<and> \<D>s es' (A \<squnion> \<A>s es))"
(*<*)by (induct es type:list) (auto simp:hyperUn_assoc)(*>*)


lemma A_fv: "\<And>A. \<A> e = \<lfloor>A\<rfloor> \<Longrightarrow> A \<subseteq> fv e"
and  "\<And>A. \<A>s es = \<lfloor>A\<rfloor> \<Longrightarrow> A \<subseteq> fvs es"
(*<*)
apply(induct e and es rule: \<A>.induct \<A>s.induct)
apply (simp_all add:hyperset_defs)
apply blast+
done
(*>*)


lemma sqUn_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<squnion> B \<sqsubseteq> A' \<squnion> B"
(*<*)by(simp add:hyperset_defs) blast(*>*)

lemma diff_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<ominus> b \<sqsubseteq> A' \<ominus> b"
(*<*)by(simp add:hyperset_defs) blast(*>*)

(* This order of the premises avoids looping of the simplifier *)
lemma D_mono: "\<And>A A'. A \<sqsubseteq> A' \<Longrightarrow> \<D> e A \<Longrightarrow> \<D> (e::'a exp) A'"
and Ds_mono: "\<And>A A'. A \<sqsubseteq> A' \<Longrightarrow> \<D>s es A \<Longrightarrow> \<D>s (es::'a exp list) A'"
(*<*)
apply(induct e and es rule: \<D>.induct \<D>s.induct)
apply simp
apply simp
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply (fastforce simp add:hyperset_defs)
apply simp
apply simp
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply simp
apply simp apply (iprover dest:diff_lem)
apply simp apply (iprover dest:sqUn_lem)
apply simp apply (iprover dest:sqUn_lem)
apply simp apply (iprover dest:sqUn_lem)
apply simp
apply simp apply (iprover dest:sqUn_lem)
apply simp
apply simp
apply simp
apply simp apply (iprover dest:sqUn_lem)
done
(*>*)

(* And this is the order of premises preferred during application: *)
lemma D_mono': "\<D> e A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> \<D> e A'"
and Ds_mono': "\<D>s es A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> \<D>s es A'"
(*<*)by(blast intro:D_mono, blast intro:Ds_mono)(*>*)


lemma Ds_Vals: "\<D>s (map Val vs) A" by(induct vs, auto)

end
