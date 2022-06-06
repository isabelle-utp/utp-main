theory utp_hyprog_ex
  imports utp_hyprog
begin

type_synonym gravs = "(real^3, unit) hybs_scheme"

abbreviation h :: "real \<Longrightarrow> real^3" where "h \<equiv> \<Pi>[0]"
abbreviation v :: "real \<Longrightarrow> real^3" where "v \<equiv> \<Pi>[Suc 0]"
abbreviation t :: "real \<Longrightarrow> real^3" where "t \<equiv> \<Pi>[Suc (Suc 0)]"

lemma dInv_grav_ex:
  "\<lbrace>[&\<^bold>c:v <\<^sub>P 0 \<and>\<^sub>P &\<^bold>c:h \<le>\<^sub>P 2]\<^sub>P\<rbrace>ode [h \<mapsto>\<^sub>s &v, v \<mapsto>\<^sub>s -9.81, t \<mapsto>\<^sub>s \<guillemotleft>1\<guillemotright>] true\<lbrace>[&\<^bold>c:v <\<^sub>P 0 \<and>\<^sub>P &\<^bold>c:h \<le>\<^sub>P 2]\<^sub>P\<rbrace>\<^sub>u"
  apply (rule dCut_split)
   apply (rule dInv)
    apply (simp add: closure)
   apply (simp add: closure uderiv usubst fode_def mkuexpr alpha)
   apply (rel_auto)
  apply (simp)
  apply (rule dInv)
   apply (simp add: closure)
  apply (simp add: closure uderiv usubst fode_def mkuexpr alpha hyprop_pred_def)
  apply (rel_simp')
  done   

abbreviation "g \<equiv> (981 / 10\<^sup>2)"

abbreviation 
  "BBall \<equiv> (\<langle>der(h) = v, der(v) = -g, der(t) = 1 | (&h \<ge>\<^sub>u 0)\<rangle> ;;
            (if (&h =\<^sub>u 0 \<and> &t >\<^sub>u 0)
              then v := (-0.8 * &v) ;; t := 0 
              else II fi))\<^sup>\<star>"

lemma "\<lbrace>[&v\<^sup>2 \<le>\<^sub>P 2*\<guillemotleft>g\<guillemotright>*(\<guillemotleft>H\<guillemotright>-&h) \<and>\<^sub>P 0 \<le>\<^sub>P \<guillemotleft>H\<guillemotright>]\<^sub>P\<rbrace> BBall \<lbrace>[&v\<^sup>2 \<le>\<^sub>P 2*\<guillemotleft>g\<guillemotright>*(\<guillemotleft>H\<guillemotright>-&h) \<and>\<^sub>P 0 \<le>\<^sub>P \<guillemotleft>H\<guillemotright>]\<^sub>P\<rbrace>\<^sub>u"
  apply (rule iter_hoare_r)
  apply (rule seq_hoare_invariant)
    apply (simp add: hyprop_pred_def usubst unrest)
   apply (rel_simp)
  oops

end