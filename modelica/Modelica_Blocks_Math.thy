section \<open> Modelica.Blocks.Math \<close>

theory Modelica_Blocks_Math
  imports Modelica_Core Modelica_Math
begin
    
definition Gain :: 
  "'a \<Rightarrow> ('a::real_algebra \<Longrightarrow> 'c) \<Rightarrow> 
  ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Gain k u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>k\<guillemotright> * $u\<acute>\<rceil>\<^sub>h ]\<^sub>M"
 
text \<open> The Sum block sums up a vector of inputs. We use the Analysis 
  package's finite Cartesian product type to encode vectors, with a type 
  acting as the length in the first parameter. \<close>

definition Sum :: 
  "'i itself \<Rightarrow> real ^ 'i::finite \<Rightarrow> 
   (real^'i \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> 
   ('d,'c::t2_space) hyrel" where 
[urel_defs]: "Sum nin k u y = [ true | \<lceil>$y\<acute> =\<^sub>u sum\<^sub>u(\<guillemotleft>k\<guillemotright> * $u\<acute>)\<rceil>\<^sub>h ]\<^sub>M"
  
definition Feedback :: 
  "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> 
   (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Feedback u1 u2 y = [ true | \<lceil>$y\<acute> =\<^sub>u $u1\<acute> - $u2\<acute>\<rceil>\<^sub>h ]\<^sub>M"

definition Add :: 
  "real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> 
  (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where 
[urel_defs]: "Add k1 k2 u1 u2 y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>k1\<guillemotright> * $u1\<acute> + \<guillemotleft>k2\<guillemotright> * $u2\<acute>\<rceil>\<^sub>h ]\<^sub>M"
  
definition Add3 :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Add3 k1 k2 k3 u1 u2 u3 y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>k1\<guillemotright> * $u1\<acute> + \<guillemotleft>k2\<guillemotright> * $u2\<acute> + \<guillemotleft>k3\<guillemotright> * $u3\<acute>\<rceil>\<^sub>h ]\<^sub>M"

definition Product :: "('a::real_algebra \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Product u1 u2 y = [ true | \<lceil>$y\<acute> =\<^sub>u $u1\<acute> * $u2\<acute>\<rceil>\<^sub>h ]\<^sub>M"

definition Division :: "('a::real_field \<Longrightarrow> 'c::t2_space) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c) \<Rightarrow> ('d,'c) hyrel" where
[urel_defs]: "Division u1 u2 y = [ $u2\<acute> \<noteq>\<^sub>u 0 | \<lceil>$y\<acute> =\<^sub>u $u1\<acute> / $u2\<acute>\<rceil>\<^sub>h ]\<^sub>M"

definition Abs :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Abs u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>abs\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"
  
definition Sign :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Sign u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>sign\<^sub>m\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

definition Sqrt :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Sqrt u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>sqrt\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

definition Sin :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Sin u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>sin\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

definition Cos :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Cos u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>cos\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

definition Tan :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Tan u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>tan\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

definition Asin :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Asin u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>arcsin\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

definition Acos :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Acos u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>arccos\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

definition Atan :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Atan u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>arctan\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

text \<open> From the Modelica Manual: "u1 and u2 shall not be zero at the same time instant" -- hence
  we encode this as an assumption in the following block. \<close>

definition Atan2 :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
[urel_defs]: "Atan2 u1 u2 y = [ \<not> ($u1\<acute> =\<^sub>u 0 \<and> $u2\<acute> =\<^sub>u 0) | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>atan2\<^sub>m\<guillemotright>($u1\<acute>)\<^sub>a($u2\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

definition Exp :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
"Exp u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>exp\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M" 
  
definition Log :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
"Log u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>ln\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M" 

definition Log10 :: "(real \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
"Log10 u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>log 10\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M" 

definition RealToInteger :: "(real \<Longrightarrow> 'c) \<Rightarrow> (int \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
"RealToInteger u y = [ true | \<lceil>$y\<acute> =\<^sub>u (\<guillemotleft>floor\<guillemotright>($u\<acute> + 0.5)\<^sub>a \<triangleleft> $u\<acute> >\<^sub>u 0 \<triangleright> \<guillemotleft>ceiling\<guillemotright>($u\<acute> - 0.5)\<^sub>a)\<rceil>\<^sub>h]\<^sub>M"

definition IntegerToReal :: "(int \<Longrightarrow> 'c) \<Rightarrow> (real \<Longrightarrow> 'c) \<Rightarrow> ('d,'c::t2_space) hyrel" where
"IntegerToReal u y = [ true | \<lceil>$y\<acute> =\<^sub>u \<guillemotleft>of_int\<guillemotright>($u\<acute>)\<^sub>a\<rceil>\<^sub>h ]\<^sub>M"

end