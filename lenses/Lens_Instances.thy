section {* Lens instances *}

theory Lens_Instances
  imports Lens_Order
  keywords "alphabet" :: "thy_decl_block"
begin

text {* Product functor lens *}

definition prod_lens :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'd) \<Rightarrow> ('a \<times> 'b \<Longrightarrow> 'c \<times> 'd)" (infixr "\<times>\<^sub>L" 85) where
[lens_defs]: "prod_lens X Y = \<lparr> lens_get = map_prod get\<^bsub>X\<^esub> get\<^bsub>Y\<^esub>
                              , lens_put = \<lambda> (u, v) (x, y). (put\<^bsub>X\<^esub> u x, put\<^bsub>Y\<^esub> v y) \<rparr>"

lemma prod_mwb_lens:
  "\<lbrakk> mwb_lens X; mwb_lens Y \<rbrakk> \<Longrightarrow> mwb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_wb_lens:
  "\<lbrakk> wb_lens X; wb_lens Y \<rbrakk> \<Longrightarrow> wb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_vwb_lens:
  "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> vwb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_bij_lens:
  "\<lbrakk> bij_lens X; bij_lens Y \<rbrakk> \<Longrightarrow> bij_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: prod_lens_def prod.case_eq_if)

lemma prod_as_plus: "X \<times>\<^sub>L Y = X ;\<^sub>L fst\<^sub>L +\<^sub>L Y ;\<^sub>L snd\<^sub>L"
  by (auto simp add: prod_lens_def fst_lens_def snd_lens_def lens_comp_def lens_plus_def)

lemma prod_lens_sublens_cong:
  "\<lbrakk> X\<^sub>1 \<subseteq>\<^sub>L X\<^sub>2; Y\<^sub>1 \<subseteq>\<^sub>L Y\<^sub>2 \<rbrakk> \<Longrightarrow> (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) \<subseteq>\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
  apply (auto simp add: sublens_def)
  apply (rename_tac Z\<^sub>1 Z\<^sub>2)
  apply (rule_tac x="Z\<^sub>1 \<times>\<^sub>L Z\<^sub>2" in exI)
  apply (auto)
  using prod_vwb_lens apply blast
  apply (auto simp add: prod_lens_def lens_comp_def prod.case_eq_if)
  apply (rule ext, rule ext)
  apply (auto simp add: prod_lens_def lens_comp_def prod.case_eq_if)
done

lemma prod_lens_equiv_cong:
  "\<lbrakk> X\<^sub>1 \<approx>\<^sub>L X\<^sub>2; Y\<^sub>1 \<approx>\<^sub>L Y\<^sub>2 \<rbrakk> \<Longrightarrow> (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) \<approx>\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
  by (simp add: lens_equiv_def prod_lens_sublens_cong)

lemma prod_lens_id_equiv:
  "1\<^sub>L \<times>\<^sub>L 1\<^sub>L = 1\<^sub>L"
  by (auto simp add: prod_lens_def id_lens_def)

lemma lens_indep_prod:
  "\<lbrakk> X\<^sub>1 \<bowtie> X\<^sub>2; Y\<^sub>1 \<bowtie> Y\<^sub>2 \<rbrakk> \<Longrightarrow> X\<^sub>1 \<times>\<^sub>L Y\<^sub>1 \<bowtie> X\<^sub>2 \<times>\<^sub>L Y\<^sub>2"
  apply (rule lens_indepI)
  apply (auto simp add: prod_lens_def prod.case_eq_if lens_indep_comm map_prod_def)
  apply (simp_all add: lens_indep_sym)
done

lemma lens_plus_prod_exchange:
  "(X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2) \<approx>\<^sub>L (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
proof (rule lens_equivI)
  show "(X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2) \<subseteq>\<^sub>L (X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2)"
    apply (simp add: sublens_def)
    apply (rule_tac x="((fst\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (fst\<^sub>L ;\<^sub>L snd\<^sub>L)) +\<^sub>L ((snd\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (snd\<^sub>L ;\<^sub>L snd\<^sub>L))" in exI)
    apply (auto)
    apply (auto intro!: plus_vwb_lens comp_vwb_lens fst_vwb_lens snd_vwb_lens lens_indep_right_comp)
    apply (auto intro!: lens_indepI simp add: lens_comp_def lens_plus_def fst_lens_def snd_lens_def)
    apply (auto simp add: prod_lens_def lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if comp_def)[1]
    apply (rule ext, rule ext, auto simp add: prod.case_eq_if)
  done
  show "(X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) +\<^sub>L (X\<^sub>2 \<times>\<^sub>L Y\<^sub>2) \<subseteq>\<^sub>L (X\<^sub>1 +\<^sub>L X\<^sub>2) \<times>\<^sub>L (Y\<^sub>1 +\<^sub>L Y\<^sub>2)"
    apply (simp add: sublens_def)
    apply (rule_tac x="((fst\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (fst\<^sub>L ;\<^sub>L snd\<^sub>L)) +\<^sub>L ((snd\<^sub>L ;\<^sub>L fst\<^sub>L) +\<^sub>L (snd\<^sub>L ;\<^sub>L snd\<^sub>L))" in exI)
    apply (auto)
    apply (auto intro!: plus_vwb_lens comp_vwb_lens fst_vwb_lens snd_vwb_lens lens_indep_right_comp)
    apply (auto intro!: lens_indepI simp add: lens_comp_def lens_plus_def fst_lens_def snd_lens_def)
    apply (auto simp add: prod_lens_def lens_plus_def lens_comp_def fst_lens_def snd_lens_def prod.case_eq_if comp_def)[1]
    apply (rule ext, rule ext, auto simp add: prod_lens_def prod.case_eq_if)
  done
qed

text {* We require that range type of a lens function has cardinality of at least 2; this ensures
        that properties of independence are provable. *}

definition fun_lens :: "'a \<Rightarrow> ('b::two \<Longrightarrow> ('a \<Rightarrow> 'b))" where
[lens_defs]: "fun_lens x = \<lparr> lens_get = (\<lambda> f. f x), lens_put = (\<lambda> f u. f(x := u)) \<rparr>"

lemma fun_wb_lens: "wb_lens (fun_lens x)"
  by (unfold_locales, simp_all add: fun_lens_def)

lemma fun_lens_indep:
  "fun_lens x \<bowtie> fun_lens y \<longleftrightarrow> x \<noteq> y"
proof -
  obtain u v :: "'a::two" where "u \<noteq> v"
    using two_diff by auto
  thus ?thesis
    by (auto simp add: fun_lens_def lens_indep_def)
qed

text {* The function range lens allows us to focus on a particular region on a functions range *}

definition fun_ran_lens :: "('c \<Longrightarrow> 'b) \<Rightarrow> (('a \<Rightarrow> 'b) \<Longrightarrow> '\<alpha>) \<Rightarrow> (('a \<Rightarrow> 'c) \<Longrightarrow> '\<alpha>)" where
[lens_defs]: "fun_ran_lens X Y = \<lparr> lens_get = \<lambda> s. get\<^bsub>X\<^esub> \<circ> get\<^bsub>Y\<^esub> s
                                 , lens_put = \<lambda> s v. put\<^bsub>Y\<^esub> s (\<lambda> x::'a. put\<^bsub>X\<^esub> (get\<^bsub>Y\<^esub> s x) (v x)) \<rparr>"

lemma fun_ran_mwb_lens: "\<lbrakk> mwb_lens X; mwb_lens Y \<rbrakk> \<Longrightarrow> mwb_lens (fun_ran_lens X Y)"
  by (unfold_locales, auto simp add: fun_ran_lens_def)

lemma fun_ran_wb_lens: "\<lbrakk> wb_lens X; wb_lens Y \<rbrakk> \<Longrightarrow> wb_lens (fun_ran_lens X Y)"
  by (unfold_locales, auto simp add: fun_ran_lens_def)

lemma fun_ran_vwb_lens: "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> vwb_lens (fun_ran_lens X Y)"
  by (unfold_locales, auto simp add: fun_ran_lens_def)

definition map_lens :: "'a \<Rightarrow> ('b \<Longrightarrow> ('a \<rightharpoonup> 'b))" where
[lens_defs]: "map_lens x = \<lparr> lens_get = (\<lambda> f. the (f x)), lens_put = (\<lambda> f u. f(x \<mapsto> u)) \<rparr>"

lemma map_mwb_lens: "mwb_lens (map_lens x)"
  by (unfold_locales, simp_all add: map_lens_def)

definition list_pad_out :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
"list_pad_out xs k = xs @ replicate (k + 1 - length xs) undefined"

definition list_augment :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
"list_augment xs k v = (list_pad_out xs k)[k := v]"

definition nth' :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" where
"nth' xs i = (if (length xs > i) then xs ! i else undefined)"

lemma list_update_append_lemma1: "i < length xs \<Longrightarrow> xs[i := v] @ ys = (xs @ ys)[i := v]"
  by (simp add: list_update_append)

lemma list_update_append_lemma2: "i < length ys \<Longrightarrow> xs @ ys[i := v] = (xs @ ys)[i + length xs := v]"
  by (simp add: list_update_append)

lemma nth'_0 [simp]: "nth' (x # xs) 0 = x"
  by (simp add: nth'_def)

lemma nth'_Suc [simp]: "nth' (x # xs) (Suc n) = nth' xs n"
  by (simp add: nth'_def)

lemma list_augment_0 [simp]:
  "list_augment (x # xs) 0 y = y # xs"
  by (simp add: list_augment_def list_pad_out_def)

lemma list_augment_Suc [simp]:
  "list_augment (x # xs) (Suc n) y = x # list_augment xs n y"
  by (simp add: list_augment_def list_pad_out_def)

lemma list_augment_twice:
  "list_augment (list_augment xs i u) j v = list_pad_out xs (max i j)[i := u, j := v]"
  apply (auto simp add: list_augment_def list_pad_out_def list_update_append_lemma1 replicate_add[THEN sym] max_def)
  apply (metis Suc_le_mono add.commute diff_diff_add diff_le_mono le_add_diff_inverse2)
done

lemma list_augment_commute:
  "i \<noteq> j \<Longrightarrow> list_augment (list_augment \<sigma> j v) i u = list_augment (list_augment \<sigma> i u) j v"
  by (simp add: list_augment_twice list_update_swap max.commute)

lemma nth_list_augment: "list_augment xs k v ! k = v"
  by (simp add: list_augment_def list_pad_out_def)

lemma nth'_list_augment: "nth' (list_augment xs k v) k = v"
  by (auto simp add: nth'_def nth_list_augment list_augment_def list_pad_out_def)

lemma list_augment_same_twice: "list_augment (list_augment xs k u) k v = list_augment xs k v"
  by (simp add: list_augment_def list_pad_out_def)

lemma nth'_list_augment_diff: "i \<noteq> j \<Longrightarrow> nth' (list_augment \<sigma> i v) j = nth' \<sigma> j"
  by (auto simp add: list_augment_def list_pad_out_def nth_append nth'_def)

definition list_lens :: "nat \<Rightarrow> ('a::two \<Longrightarrow> 'a list)" where
[lens_defs]: "list_lens i = \<lparr> lens_get = (\<lambda> xs. nth' xs i)
                            , lens_put = (\<lambda> xs x. list_augment xs i x) \<rparr>"

abbreviation "hd_lens \<equiv> list_lens 0"

definition tl_lens :: "'a list \<Longrightarrow> 'a list" where
[lens_defs]: "tl_lens = \<lparr> lens_get = (\<lambda> xs. tl xs)
                        , lens_put = (\<lambda> xs xs'. hd xs # xs') \<rparr>"

lemma list_mwb_lens: "mwb_lens (list_lens x)"
  by (unfold_locales, simp_all add: list_lens_def nth'_list_augment list_augment_same_twice)

lemma tail_lens_mwb:
  "mwb_lens tl_lens"
  by (unfold_locales, simp_all add: tl_lens_def)

lemma list_lens_indep:
  "i \<noteq> j \<Longrightarrow> list_lens i \<bowtie> list_lens j"
  by (simp add: list_lens_def lens_indep_def list_augment_commute nth'_list_augment_diff)

lemma hd_tl_lens_indep [simp]:
  "hd_lens \<bowtie> tl_lens"
  apply (rule lens_indepI)
  apply (simp_all add: list_lens_def tl_lens_def)
  apply (metis hd_conv_nth hd_def length_greater_0_conv list.case(1) nth'_def nth'_list_augment)
  apply (metis (full_types) hd_conv_nth hd_def length_greater_0_conv list.case(1) nth'_def)
  apply (metis Nitpick.size_list_simp(2) One_nat_def add_Suc_right append.simps(1) append_Nil2 diff_Suc_Suc diff_zero hd_Cons_tl list.inject list.size(4) list_augment_0 list_augment_def list_augment_same_twice list_pad_out_def nth_list_augment replicate.simps(1) replicate.simps(2) tl_Nil)
done

subsection {* Record field lenses *}

abbreviation (input) "fld_put f \<equiv> (\<lambda> \<sigma> u. f (\<lambda>_. u) \<sigma>)"

syntax "_FLDLENS" :: "id \<Rightarrow> ('a \<Longrightarrow> 'r)"  ("FLDLENS _")
translations "FLDLENS x" => "\<lparr> lens_get = x, lens_put = CONST fld_put (_update_name x) \<rparr>"

text {* Introduce the alphabet command that creates a record with lenses for each field *}


ML_file "Lens_Record.ML"

text {* The following theorem attribute stores splitting theorems for alphabet types *}

named_theorems alpha_splits

(*  
alphabet mylens =
  x :: nat
  y :: string
  
alphabet mylens_2 = mylens +
  z :: int
  k :: "string list"
*)

subsection {* Lens Interpretation *}

named_theorems lens_interp_laws

locale lens_interp = interp
begin
declare meta_interp_law [lens_interp_laws]
declare all_interp_law [lens_interp_laws]
declare exists_interp_law [lens_interp_laws]
end

end
