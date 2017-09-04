theory Prisms
  imports Congruence
begin
  
record ('v, 's) lens =
  lens_get :: "'s \<Rightarrow> 'v" ("get\<index>")
  lens_put :: "'s \<Rightarrow> 'v \<Rightarrow> 's" ("put\<index>")
  lens_source :: "'s set" ("\<S>\<index>")
  lens_view :: "'v set" ("\<V>\<index>")

type_notation
  lens (infixr "\<Longrightarrow>" 0)

named_theorems lens_defs
  
definition lens_create :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("create\<index>") where
[lens_defs]: "lens_create X v = lens_put X (SOME s. s \<in> lens_source X) v"
  
subsection {* Weak lenses *}

locale pweak_lens =
  fixes x :: "'a \<Longrightarrow> 'b" (structure)
  assumes source_nonempty: "\<S> \<noteq> {}"
  and get_type: "get \<in> \<S> \<rightarrow> \<V>"
  and put_type: "put \<in> \<S> \<rightarrow> \<V> \<rightarrow> \<S>"
  and put_get: "\<lbrakk> s \<in> \<S>; v \<in> \<V> \<rbrakk> \<Longrightarrow> get (put s v) = v"
begin

  abbreviation some_source :: "'b" ("\<^bold>s") where
  "some_source \<equiv> (SOME s. s \<in> \<S>)"
  
  lemma some_source: "\<^bold>s \<in> \<S>"
    by (simp add: some_in_eq source_nonempty)
  
  lemma view_nonempty: "\<V> \<noteq> {}"
    using get_type source_nonempty by force

  lemma create_get: "v \<in> \<V> \<Longrightarrow> get (create v) = v"
    by (simp add: lens_create_def put_get some_source)

  lemma create_inj: "inj_on create \<V>"
    by (metis create_get inj_onI)

  definition update :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b)" where
  [lens_defs]: "update f s = put s (f (get s))"

  lemma get_update: "\<lbrakk> s \<in> \<S>; f \<in> \<V> \<rightarrow> \<V> \<rbrakk> \<Longrightarrow> get (update f s) = f (get s)"
    using get_type put_get update_def by fastforce

  lemma view_determination: "\<lbrakk> s \<in> \<S>; u \<in> \<V>; v \<in> \<V> \<rbrakk> \<Longrightarrow> put s u = put s v \<Longrightarrow> u = v"
    by (metis put_get)

  lemma put_inj: "s \<in> \<S> \<Longrightarrow> inj_on (put s) \<V>"
    by (simp add: inj_onI view_determination)

end
  
declare pweak_lens.put_get [simp]
declare pweak_lens.create_get [simp]

locale weak_lens = pweak_lens +
  assumes source_UNIV [simp]: "\<S> = UNIV"
  and view_UNIV [simp]: "\<V> = UNIV"
begin
  
  lemma put_get: "get (put s v) = v"
    by (simp add: put_get)

  lemma create_get: "get (create v) = v"
    by (simp add: create_get)

end
  
subsection {* Well-behaved lenses *}

locale pwb_lens = pweak_lens +
  assumes get_put: "s \<in> \<S> \<Longrightarrow> put s (get s) = s"
begin

  lemma put_twice: "\<lbrakk> s \<in> \<S>; v \<in> \<V> \<rbrakk> \<Longrightarrow> put (put s v) v = put s v"
    using funcset_mem get_put put_get put_type by force

  lemma put_surjectivity: "s \<in> \<S> \<Longrightarrow> \<exists> s'\<in>\<S>. \<exists> v\<in>\<V>. put s' v = s"
    by (meson funcset_mem get_type get_put)

  lemma source_stability: "s \<in> \<S> \<Longrightarrow> \<exists> v\<in>\<V>. put s v = s"
    using get_type get_put by force

end

declare pwb_lens.get_put [simp]

lemma pwb_lens_pweak [simp]: "pwb_lens x \<Longrightarrow> pweak_lens x"
  by (simp_all add: pwb_lens_def)

locale wb_lens = weak_lens + pwb_lens
begin
  
  lemma get_put: "put s (get s) = s"
    by (simp add: get_put)
      
  lemma put_twice: "put (put s v) v = put s v"
    by (simp add: put_twice)

end
    

subsection {* Mainly well-behaved lenses *}

locale pmwb_lens = pweak_lens +
  assumes put_put: "\<lbrakk> s \<in> \<S>; u \<in> \<V>; v \<in> \<V> \<rbrakk> \<Longrightarrow> put (put s v) u = put s u"
begin

  lemma update_comp: "\<lbrakk> f \<in> \<V> \<rightarrow> \<V>; g \<in> \<V> \<rightarrow> \<V>; s \<in> \<S> \<rbrakk> \<Longrightarrow> update f (update g s) = update (f \<circ> g) s"
    using get_type get_update put_put update_def by fastforce

end

declare pmwb_lens.put_put [simp]

lemma pmwb_lens_weak [simp]:
  "pmwb_lens x \<Longrightarrow> pweak_lens x"
  by (simp add: pmwb_lens_def)

locale mwb_lens = pmwb_lens + weak_lens
begin
  lemma put_put: "put (put s v) u = put s u"
    by (simp add: put_put)
end
    
subsection {* Very well-behaved lenses *}

locale pvwb_lens = pwb_lens + pmwb_lens
begin

  lemma source_determination: "\<lbrakk> s \<in> \<S>; s' \<in> \<S>; v \<in> \<V> \<rbrakk> \<Longrightarrow> get s = get s' \<Longrightarrow> put s v = put s' v \<Longrightarrow> s = s'"
    by (metis PiE get_put get_type put_put)

 lemma put_eq:
   "\<lbrakk> s \<in> \<S>; s' \<in> \<S>; u \<in> \<V>; v \<in> \<V>; get s = k; put s u = put s' v \<rbrakk> \<Longrightarrow> put s' k = s"
   by (metis put_get put_put put_surjectivity)
   

end

lemma pvwb_lens_wb [simp]: "pvwb_lens x \<Longrightarrow> pwb_lens x"
  by (simp_all add: pvwb_lens_def)

lemma pvwb_lens_mwb [simp]: "pvwb_lens x \<Longrightarrow> pmwb_lens x"
  by (simp_all add: pvwb_lens_def)

locale vwb_lens = pvwb_lens + weak_lens
  
subsection {* Lens independence *}

locale lens_indep =
  fixes X :: "'a \<Longrightarrow> 'c" and Y :: "'b \<Longrightarrow> 'c"
  assumes lens_put_comm: "put\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> s v) u = put\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> s u) v"
  and lens_put_irr1: "get\<^bsub>X\<^esub> (put\<^bsub>Y\<^esub> s v) = get\<^bsub>X\<^esub> s"
  and lens_put_irr2: "get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> s u) = get\<^bsub>Y\<^esub> s"
begin
  
thm lens_put_irr2
  
notation lens_indep (infix "\<bowtie>" 50)

lemma lens_indepI:
  "\<lbrakk> \<And> u v \<sigma>. lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v;
     \<And> v \<sigma>. lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>;
     \<And> u \<sigma>. lens_get y (lens_put x \<sigma> u) = lens_get y \<sigma> \<rbrakk> \<Longrightarrow> x \<bowtie> y"
  by (simp add: lens_indep_def)

text {* Independence is irreflexive for effectual lenses *}

lemma lens_indep_sym:  "x \<bowtie> y \<Longrightarrow> y \<bowtie> x"
  by (simp add: lens_indep_def)

lemma lens_indep_comm:
  "x \<bowtie> y \<Longrightarrow> lens_put x (lens_put y \<sigma> v) u = lens_put y (lens_put x \<sigma> u) v"
  by (simp add: lens_indep_def)

lemma lens_indep_get [simp]:
  assumes "x \<bowtie> y"
  shows "lens_get x (lens_put y \<sigma> v) = lens_get x \<sigma>"
  using assms lens_indep_def by fastforce

  
end