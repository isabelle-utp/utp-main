section {* Reactive processes *}

theory utp_reactive
imports 
  utp_concurrency 
  utp_event
begin

text {* Following the way of UTP to describe reactive processes, more observational
variables are needed to record the interaction with the environment. Three observational 
variables are defined for this subset of relations: $wait$, $tr$ and $ref$.
The boolean variable $wait$ records if the process is waiting for an interaction
or has terminated. $tr$ records the list (trace) of interactions the process has
performed so far. The variable $ref$ contains the set of interactions (events) the
process may refuse to perform. *}

text {* In this section, we introduce first some preliminary notions, useful for 
 trace manipulations. The definitions of reactive process alphabets and healthiness 
conditions are also given. Finally, proved lemmas and theorems are listed.*}

subsection {* Preliminaries *}

type_synonym '\<alpha> trace = "'\<alpha> list"

fun list_diff::"'\<alpha> list \<Rightarrow> '\<alpha> list \<Rightarrow> '\<alpha> list option" where
   "list_diff l [] = Some l"
  | "list_diff [] l = None"
  | "list_diff (x#xs) (y#ys) = (if (x = y) then (list_diff xs ys) else None)"

lemma list_diff_empty [simp]: "the (list_diff l []) = l"
by (cases l) auto

lemma prefix_subst [simp]: "l @ t = m \<Longrightarrow> m - l = t"
by (auto)

lemma prefix_subst1 [simp]: "m = l @ t \<Longrightarrow> m - l = t"
by (auto)


text {* The definitions of reactive process alphabets and healthiness conditions are given
in the following. The healthiness conditions of reactive processes are defined by 
$R1$, $R2$, $R3$ and their composition $R$.*}

type_synonym '\<theta> refusal = "'\<theta> set"
  
record '\<theta> alpha_rp  = alpha_d + 
                         rp_wait :: bool
                         rp_tr   :: "'\<theta> trace"
                         rp_ref  :: "'\<theta> refusal"

definition "wait = VAR rp_wait"
definition "tr   = VAR rp_tr"
definition "ref  = VAR rp_ref"

declare wait_def [upred_defs]
declare tr_def [upred_defs]
declare ref_def [upred_defs]

instantiation alpha_rp_ext :: (type, vst) vst
begin
  definition get_vstore_alpha_rp_ext :: "('a, 'b) alpha_rp_ext \<Rightarrow> vstore"
  where [simp]: "get_vstore_alpha_rp_ext x = get_vstore (alpha_rp.more (alpha_d.extend undefined x))"
  definition upd_vstore_alpha_rp_ext :: "(vstore \<Rightarrow> vstore) \<Rightarrow> ('a, 'b) alpha_rp_ext \<Rightarrow> ('a, 'b) alpha_rp_ext"
  where [simp]: "upd_vstore_alpha_rp_ext f x = alpha_d.more (alpha_rp.more_update (upd_vstore f) (alpha_d.extend undefined x))"
instance
  apply (intro_classes, auto simp add: upd_store_parm[THEN sym] alpha_rp.defs alpha_d.defs)
  apply (metis (no_types, lifting) alpha_d.ext_inject alpha_d.surjective alpha_rp.select_convs(4) alpha_rp.surjective alpha_rp.update_convs(4) get_upd_vstore)
  apply (smt alpha_d.select_convs(2) alpha_rp.surjective alpha_rp.update_convs(4) upd_vstore_comp)
  apply (metis alpha_d.select_convs(2) alpha_rp.surjective alpha_rp.update_convs(4) upd_vstore_eta)
  apply (metis alpha_rp.unfold_congs(5) upd_store_parm)
done
end

lemma uvar_wait [simp]: "uvar wait"
  by (unfold_locales, simp_all add: wait_def)

lemma uvar_tr [simp]: "uvar tr"
  by (unfold_locales, simp_all add: tr_def)

lemma uvar_ref [simp]: "uvar ref"
  by (unfold_locales, simp_all add: ref_def)

text{* Note that we define here the class of UTP alphabets that contain
$wait$, $tr$ and $ref$, or, in other words, we define here the class of reactive process
alphabets. *}

type_synonym ('\<theta>,'\<alpha>) alphabet_rp  = "('\<theta>,'\<alpha>) alpha_rp_scheme alphabet"
type_synonym ('\<theta>,'\<alpha>,'\<beta>) relation_rp  = "(('\<theta>,'\<alpha>) alphabet_rp, ('\<theta>,'\<beta>) alphabet_rp) relation"
type_synonym ('\<theta>,'\<alpha>) hrelation_rp  = "(('\<theta>,'\<alpha>) alphabet_rp, ('\<theta>,'\<alpha>) alphabet_rp) relation"
type_synonym ('\<theta>,'\<sigma>) predicate_rp  = "('\<theta>,'\<sigma>) alphabet_rp upred"

lift_definition lift_rea :: "('\<alpha>, '\<beta>) relation \<Rightarrow> ('\<theta>, '\<alpha>, '\<beta>) relation_rp" ("\<lceil>_\<rceil>\<^sub>R") is
"\<lambda> P (A, A'). P (more A, more A')" .

lift_definition drop_rea :: "('\<theta>, '\<alpha>, '\<beta>) relation_rp \<Rightarrow> ('\<alpha>, '\<beta>) relation" ("\<lfloor>_\<rfloor>\<^sub>R") is
"\<lambda> P (A, A'). P (\<lparr> des_ok = True, rp_wait = True, rp_tr = [], rp_ref = {}, \<dots> = A \<rparr>, 
                 \<lparr> des_ok = True, rp_wait = True, rp_tr = [], rp_ref = {}, \<dots> = A' \<rparr>)" .

definition R1_def [upred_defs]: "R1 (P) =  (P \<and> ($tr \<le>\<^sub>u $tr\<acute>))"

definition R2_def [upred_defs]: "R2 (P) = (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>($tr\<acute> - $tr)/ $tr\<acute>\<rbrakk> \<and> ($tr \<le>\<^sub>u $tr\<acute>))"

definition skip_rea_def [urel_defs]: "II\<^sub>r = (II \<or> (\<not> $ok \<and> $tr \<le>\<^sub>u $tr\<acute>))"

text {* There are two versions of R3 in the UTP book. Here we opt for the version that works for CSP *}

definition R3_def [urel_defs]: "R3c (P) = (II\<^sub>r \<triangleleft> $wait \<triangleright> P)"

definition "RH(P) = R1(R2(R3c(P)))"

lemma R1_idem: "R1(R1(P)) = R1(P)"
  by pred_tac

lemma R2_idem: "R2(R2(P)) = R2(P)"
  by (pred_tac)

lemma tr_prefix_as_concat: "(xs \<le>\<^sub>u ys) = (\<^bold>\<exists> zs \<bullet> ys =\<^sub>u xs ^\<^sub>u \<guillemotleft>zs\<guillemotright>)"
  by (rel_tac, simp add: less_eq_list_def prefixeq_def)

lemma R2_form:
  "R2(P) = (\<^bold>\<exists> tt \<bullet> P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<guillemotright>)"
  by (rel_tac, metis prefix_subst strict_prefixE)

lemma uconc_left_unit [simp]: "\<langle>\<rangle> ^\<^sub>u e = e"
  by pred_tac

lemma uconc_right_unit [simp]: "e ^\<^sub>u \<langle>\<rangle> = e"
  by pred_tac

text {* This laws is proven only for homogeneous relations, can it be generalised? *}

lemma R2_seqr_form: 
  fixes P Q :: "('\<theta>,'\<alpha>,'\<alpha>) relation_rp"
  shows "(R2(P) ;; R2(Q)) = 
         (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                        \<and> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
proof -
  have "(R2(P) ;; R2(Q)) = (\<^bold>\<exists> tr\<^sub>0 \<bullet> (R2(P))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<acute>\<rbrakk> ;; (R2(Q))\<lbrakk>\<guillemotleft>tr\<^sub>0\<guillemotright>/$tr\<rbrakk>)"
    by (subst seqr_middle[of tr], simp_all)
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) ;; 
                                (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by (simp add: R2_form usubst unrest uquant_lift var_in_var var_out_var, rel_tac)
  also have "... =
       (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((\<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; 
                                (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)))"
    by (simp add: conj_comm)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> \<^bold>\<exists> tr\<^sub>0 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                                \<and> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
    by (simp add: seqr_pre_out seqr_post_out unrest, rel_tac)
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                        \<and> (\<^bold>\<exists> tr\<^sub>0 \<bullet> \<guillemotleft>tr\<^sub>0\<guillemotright> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> $tr\<acute> =\<^sub>u \<guillemotleft>tr\<^sub>0\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by rel_tac
  also have "... =
       (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> ((P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk>) ;; (Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)) 
                        \<and> ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
    by rel_tac
  finally show ?thesis .
qed

lemma R2_seqr_distribute: 
  fixes P Q :: "('\<theta>,'\<alpha>,'\<alpha>) relation_rp"
  shows "R2(R2(P) ;; R2(Q)) = (R2(P) ;; R2(Q))"
proof -
  have "R2(R2(P) ;; R2(Q)) = 
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>($tr\<acute> - $tr)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
    by (simp add: R2_seqr_form, simp add: R2_def usubst unrest, rel_tac)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)\<lbrakk>(\<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)/$tr\<acute>\<rbrakk>
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (subst subst_eq_replace, simp)
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr)"
      by (simp add: usubst unrest)
  also have "... =
    (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> ($tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright> \<and> $tr\<acute> \<ge>\<^sub>u $tr))"
    by pred_tac
  also have "... =
    ((\<^bold>\<exists> tt\<^sub>1 \<bullet> \<^bold>\<exists> tt\<^sub>2 \<bullet> (P\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>1\<guillemotright>/$tr\<acute>\<rbrakk> ;; Q\<lbrakk>\<langle>\<rangle>/$tr\<rbrakk>\<lbrakk>\<guillemotleft>tt\<^sub>2\<guillemotright>/$tr\<acute>\<rbrakk>)
      \<and> $tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>))"
  proof -
    have "\<And> tt\<^sub>1 tt\<^sub>2. ((($tr\<acute> - $tr =\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>) \<and> $tr\<acute> \<ge>\<^sub>u $tr) :: ('\<theta>,'\<alpha>,'\<alpha>) relation_rp)
           = ($tr\<acute> =\<^sub>u $tr ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> ^\<^sub>u \<guillemotleft>tt\<^sub>2\<guillemotright>)"
      by (rel_tac, metis prefix_subst strict_prefixE)
    thus ?thesis by simp
  qed
  also have "... = (R2(P) ;; R2(Q))"
    by (simp add: R2_seqr_form)
  finally show ?thesis .
qed


lemma R3c_idem: "R3c(R3c(P)) = R3c(P)"
  by rel_tac

end