section \<open>Fresh identifier generation for strings\<close>

theory Fresh_String
  imports Fresh
begin

subsection \<open>A partial order on strings\<close>

text
\<open>The first criterion is the length, and the second the encoding of last character. \<close>

definition ordst :: "string \<Rightarrow> string \<Rightarrow> bool" where
"ordst X Y \<equiv>
 (length X \<le> length Y \<and> X \<noteq> [] \<and> Y \<noteq> [] \<and> of_char (last X) < (of_char(last Y) :: nat))
 \<or> (length X < length Y)"

definition ordstNS :: "string \<Rightarrow> string \<Rightarrow> bool" where
"ordstNS X Y \<equiv> X = Y \<or> ordst X Y"

lemma ordst_antirefl: "\<not> ordst X X"
by(auto simp add: ordst_def)

lemma ordst_trans:
assumes As1: "ordst X Y" and As2: "ordst Y Z"
shows "ordst X Z"
proof(cases "(length X < length Y) \<or> (length Y < length Z)")
  assume "(length X < length Y) \<or> (length Y < length Z)"
  moreover
  {assume "length X < length Y"
   moreover have "length Y \<le> length Z"
   using As2 ordst_def by force
   ultimately have "length X < length Z" by force
   hence ?thesis using ordst_def by force}
  moreover
  {assume "length Y < length Z"
   moreover have "length X \<le> length Y"
   using As1 ordst_def by force
   ultimately have "length X < length Z" by force
   hence ?thesis using ordst_def by force}
  ultimately show ?thesis by force
next
  assume "\<not> (length X < length Y \<or> length Y < length Z)"
  hence Ft: "\<not> length X < length Y  \<and> \<not> length Y < length Z" by force
  hence "(of_char(last X) :: nat) < of_char(last Y) \<and>
         (of_char(last Y) :: nat) < of_char(last Z) \<and>
         length X \<le> length Y \<and> length Y \<le> length Z"
  using As1 As2 ordst_def by force
  hence "(of_char(last X) :: nat) < of_char(last Z) \<and>
         length X \<le> length Z" by force
  moreover have "X \<noteq> [] \<and> Z \<noteq> []"
  using As1 As2 Ft ordst_def by force
  ultimately show ?thesis using ordst_def[of X Z] by force
qed

lemma ordstNS_refl: "ordstNS X X"
by(simp add: ordstNS_def)

lemma ordstNS_trans:
"ordstNS X Y \<Longrightarrow> ordstNS Y Z \<Longrightarrow> ordstNS X Z"
by (metis ordstNS_def ordst_trans)

lemma ordst_ordstNS_trans:
"ordst X Y \<Longrightarrow> ordstNS Y Z \<Longrightarrow> ordst X Z"
by (metis ordstNS_def ordst_trans)

lemma ordstNS_ordst_trans:
"ordstNS X Y \<Longrightarrow> ordst Y Z \<Longrightarrow> ordst X Z"
by (metis ordstNS_def ordst_trans)


subsection \<open>Incrementing a string \<close>

text \<open>If the last character is $\geq$ 'a' and $<$ 'z',
   then \<open>upChar\<close> increments this last character;
   otherwise \<open>upChar\<close> appends an 'a'.  \<close>

fun upChar :: "string \<Rightarrow> string" where
"upChar Y =
 (if (Y \<noteq> [] \<and> of_char(last Y) \<ge> (97 :: nat) \<and>
               of_char(last Y) < (122 :: nat))
    then (butlast Y) @
         [char_of(of_char(last Y) + (1 :: nat))]
    else Y @ ''a''
 )"

lemma upChar_ordst: "ordst Y (upChar Y)"
proof-
  {assume "\<not>(Y \<noteq> [] \<and> of_char(last Y) \<ge> (97 :: nat)
                       \<and> of_char(last Y) < (122 :: nat))"
   hence "upChar Y = Y @ ''a''" by force
   hence ?thesis using ordst_def by force
  }
  moreover
  {assume As: "Y \<noteq> [] \<and> of_char(last Y) \<ge> (97 :: nat)
                       \<and> of_char(last Y) < (122 :: nat)"
   hence Ft: "upChar Y = (butlast Y) @
                     [char_of(of_char(last Y) + (1 :: nat))]"
   by force
   hence Ft': "last (upChar Y) = char_of(of_char(last Y) + (1 :: nat))"
   by force
   hence "of_char(last (upChar Y)) mod (256 :: nat)  =
          (of_char(last Y) + 1) mod 256"
   by force
   moreover
   have "of_char(last(upChar Y))  < (256 :: nat) \<and>
         of_char(last Y) + 1 < (256 :: nat)"
   using As Ft' by force
   ultimately
   have "of_char (last Y) < (of_char (last(upChar Y)) :: nat)" by force
   moreover
   from Ft have "length Y \<le> length (upChar Y)" by force
   ultimately have ?thesis using ordst_def by force}
  ultimately show ?thesis by force
qed


subsection \<open>The fresh-identifier operator\<close>

text \<open>\<open>fresh Xs Y\<close> changes \<open>Y\<close> as little as possible so that
   it becomes disjoint from all strings in \<open>Xs\<close>. \<close>

function fresh_string :: "string set \<Rightarrow> string \<Rightarrow> string"
where
Up: "Y \<in> Xs \<Longrightarrow> finite Xs \<Longrightarrow> fresh_string Xs Y = fresh_string (Xs - {Y}) (upChar Y)"
|
Fresh: "Y \<notin> Xs \<or> infinite Xs \<Longrightarrow> fresh_string Xs Y = Y"
by auto
termination
  apply(relation "measure (\<lambda>(Xs,Y). card Xs)", simp_all)
  by (metis card_gt_0_iff diff_Suc_less empty_iff)

lemma fresh_string_ordstNS: "ordstNS Y (fresh_string Xs Y)"
proof (induction Xs Y rule: fresh_string.induct[case_names Up Fresh])
  case (Up Y Xs)
  hence "ordst Y (fresh_string (Xs - {Y}) (upChar Y))"
    using upChar_ordst[of Y] ordst_ordstNS_trans by force
  hence "ordstNS Y (fresh_string (Xs - {Y}) (upChar Y))"
    using ordstNS_def by auto
  thus ?case
    using Up.hyps by auto
next
  case (Fresh Y Xs)
  then show ?case
    by (auto intro: ordstNS_refl)
qed

lemma fresh_string_set: "finite Xs \<Longrightarrow> fresh_string Xs Y \<notin> Xs"
proof (induction Xs Y rule: fresh_string.induct[case_names Up Fresh])
  case (Up Y Xs)
  show ?case
  proof
    assume "fresh_string Xs Y \<in> Xs"
    then have "fresh_string (Xs - {Y}) (upChar Y) \<in> Xs"
      using Up.hyps by force
    then have "fresh_string (Xs - {Y}) (upChar Y) = Y"
      using Up.IH \<open>finite Xs\<close> by blast
    moreover have "ordst Y (fresh_string (Xs - {Y}) (upChar Y))"
      using upChar_ordst[of Y] fresh_string_ordstNS ordst_ordstNS_trans by auto
    ultimately show False
      using ordst_antirefl by auto
  qed
qed auto

text \<open>Code generation:\<close>

lemma fresh_string_if:
  "fresh_string Xs Y = (
     if Y \<in> Xs \<and> finite Xs then fresh_string (Xs - {Y}) (upChar Y)
     else Y)"
  by simp

lemmas fresh_string_list[code] = fresh_string_if[where Xs = "set Xs" for Xs, simplified]

text \<open>Some tests: \<close>

value "[fresh_string {} ''Abc'',
        fresh_string {''X'', ''Abc''} ''Abd'',
        fresh_string {''X'', ''Y''} ''Y'',
        fresh_string {''X'', ''Yaa'', ''Ya'', ''Yaa''} ''Ya'',
        fresh_string {''X'', ''Yaa'', ''Yz'', ''Yza''} ''Yz'',
        fresh_string {''X'', ''Y'', ''Yab'', ''Y''} ''Y'']"

text \<open>Here we do locale interpretation rather than class instantiation,
since \<^typ>\<open>string\<close> is a type synonym for \<^typ>\<open>char list\<close>.\<close>

interpretation fresh_string: fresh where fresh = fresh_string
  by standard (use fresh_string_set in auto)

subsection \<open>Lifting to string literals\<close>

abbreviation "is_ascii str \<equiv> (\<forall>c \<in> set str. \<not>digit7 c)"

lemma map_ascii_of_idem:
  "is_ascii str \<Longrightarrow> map String.ascii_of str = str"
  by (induction str) (auto simp: String.ascii_of_idem)

lemma is_ascii_butlast:
  "is_ascii str \<Longrightarrow> is_ascii (butlast str)"
  by (auto dest: in_set_butlastD)

lemma ascii_char_of:
  fixes c :: nat
  assumes "c < 128"
  shows "\<not>digit7 (char_of c)"
  using assms
  by (auto simp: char_of_def bit_iff_odd)

lemmas ascii_of_char_of_idem = ascii_char_of[THEN String.ascii_of_idem]

lemma is_ascii_upChar:
  "is_ascii str \<Longrightarrow> is_ascii (upChar str)"
  by (auto simp: ascii_char_of is_ascii_butlast)

lemma is_ascii_fresh_string:
  "is_ascii Y \<Longrightarrow> is_ascii (fresh_string Xs Y)"
proof (induction Xs Y rule: fresh_string.induct[case_names Up Fresh])
  case (Up Y Xs)
  show ?case
    using Up.IH[OF is_ascii_upChar[OF \<open>is_ascii Y\<close>]] Up.hyps
    by auto
qed auto

text \<open>For string literals we can properly instantiate the class.\<close>

instantiation String.literal :: fresh
begin

context
  includes literal.lifting
begin

lift_definition fresh_literal :: "String.literal set \<Rightarrow> String.literal \<Rightarrow> String.literal"
  is fresh_string
  using is_ascii_fresh_string
  by blast

instance by (standard; transfer) (use fresh_string_set in auto)

end

end

text \<open>Code generation:\<close>

context
  includes literal.lifting
begin

lift_definition upChar_literal :: "String.literal \<Rightarrow> String.literal" is upChar
  using is_ascii_upChar
  by blast

lemma upChar_literal_upChar[code]:
  "upChar_literal s = String.implode (upChar (String.explode s))"
  by transfer (auto simp: map_ascii_of_idem is_ascii_butlast ascii_of_char_of_idem)

lemma fresh_literal_if:
  "fresh xs y = (if y \<in> xs \<and> finite xs then fresh (xs - {y}) (upChar_literal y) else y)"
  by transfer (intro fresh_string_if)

lemmas fresh_literal_list[code] = fresh_literal_if[where xs = "set xs" for xs, simplified]

end

text \<open>Some tests: \<close>

value "[fresh {} (STR ''Abc''),
        fresh {STR ''X'', STR ''Abc''} (STR ''Abd''),
        fresh {STR ''X'', STR ''Y''} (STR  ''Y''),
        fresh {STR ''X'', STR ''Yaa'', STR ''Ya'', STR ''Yaa''} (STR ''Ya''),
        fresh {STR ''X'', STR ''Yaa'', STR ''Yz'', STR ''Yza''} (STR ''Yz''),
        fresh {STR ''X'', STR ''Y'', STR ''Yab'', STR ''Y''} (STR ''Y'')]"

end
