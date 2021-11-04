(*<*)
theory Blue_Eyes
  imports Main
begin
(*>*)

section \<open>Introduction\<close>

text \<open>The original problem statement @{cite xkcd} explains the puzzle well:

\begin{quotation}
A group of people with assorted eye colors live on an island.
They are all perfect logicians -- if a conclusion can be logically deduced,
they will do it instantly.
No one knows the color of their eyes.
Every night at midnight, a ferry stops at the island.
Any islanders who have figured out the color of their own eyes then leave the island, and the rest stay.
Everyone can see everyone else at all times
and keeps a count of the number of people they see with each eye color (excluding themselves),
but they cannot otherwise communicate.
Everyone on the island knows all the rules in this paragraph.

On this island there are 100 blue-eyed people,
100 brown-eyed people,
and the Guru (she happens to have green eyes).
So any given blue-eyed person can see 100 people with brown eyes and 99 people with blue eyes (and one with green),
but that does not tell him his own eye color;
as far as he knows the totals could be 101 brown and 99 blue.
Or 100 brown, 99 blue, and he could have red eyes.

The Guru is allowed to speak once (let's say at noon),
on one day in all their endless years on the island.
Standing before the islanders, she says the following:

``I can see someone who has blue eyes.''

Who leaves the island, and on what night?
\end{quotation}

It might seem weird that the Guru's declaration gives anyone any new information.
For an informal discussion, see \cite[Section~1.1]{fagin1995}.\<close>

section \<open>Modeling the world \label{sec:world}\<close>

text \<open>We begin by fixing two type variables: @{typ "'color"} and @{typ "'person"}.
The puzzle doesn't specify how many eye colors are possible, but four are mentioned.
Crucially, we must assume they are distinct. We specify the existence of colors other
than blue and brown, even though we don't mention them later, because when blue and brown
are the only possible colors, the puzzle has a different solution — the brown-eyed logicians
may leave one day after the blue-eyed ones.

We refrain from specifying the exact population of the island, choosing to only assume
it is finite and denote a specific person as the Guru.

We could also model the Guru as an outside entity instead of a participant. This doesn't change
the answer and results in a slightly simpler proof, but is less faithful to the problem statement.\<close>

context
  fixes blue brown green red :: 'color
  assumes colors_distinct: "distinct [blue, brown, green, red]"

  fixes guru :: 'person
  assumes "finite (UNIV :: 'person set)"
begin

text \<open>It's slightly tricky to formalize the behavior of perfect logicians.
The representation we use is centered around the type of a @{emph \<open>world\<close>},
which describes the entire state of the environment. In our case, it's a function
@{typ "'person => 'color"} that assigns an eye color to everyone.@{footnote \<open>We would introduce
a type synonym, but at the time of writing Isabelle doesn't support including type variables fixed
by a locale in a type synonym.\<close>}

The only condition known to everyone and not dependent on the observer is Guru's declaration:\<close>

definition valid :: "('person \<Rightarrow> 'color) \<Rightarrow> bool" where
  "valid w \<longleftrightarrow> (\<exists>p. p \<noteq> guru \<and> w p = blue)"

text \<open>We then define the function @{term "possible n p w w'"}, which returns @{term True}
if on day \<open>n\<close> the potential world \<open>w'\<close> is plausible from the perspective of person \<open>p\<close>,
based on the observations they made in the actual world \<open>w\<close>.

Then, @{term "leaves n p w"} is @{term True} if \<open>p\<close> is able to unambiguously deduce
the color of their own eyes, i.e. if it is the same in all possible worlds. Note that if \<open>p\<close> actually
left many moons ago, this function still returns @{term True}.\<close>

fun leaves :: "nat \<Rightarrow> 'person \<Rightarrow> ('person \<Rightarrow> 'color) \<Rightarrow> bool"
  and possible :: "nat \<Rightarrow> 'person \<Rightarrow> ('person \<Rightarrow> 'color) \<Rightarrow> ('person \<Rightarrow> 'color) \<Rightarrow> bool"
  where
    "leaves n p w = (\<forall>w'. possible n p w w' \<longrightarrow> w' p = w p)" |
    "possible n p w w' \<longleftrightarrow> valid w \<and> valid w'
    \<and> (\<forall>p' \<noteq> p. w p' = w' p')
    \<and> (\<forall>n' < n. \<forall>p'. leaves n' p' w = leaves n' p' w')"

text \<open>Naturally, the act of someone leaving can be observed by others, thus the two definitions
are mutually recursive. As such, we need to instruct the simplifier to not unfold these definitions endlessly.\<close>
declare possible.simps[simp del] leaves.simps[simp del]

text \<open>A world is possible if
  \<^enum> The Guru's declaration holds.
  \<^enum> The eye color of everyone but the observer matches.
  \<^enum> The same people left on each of the previous days.

Moreover, we require that the actual world \<open>w\<close> is \<open>valid\<close>, so that the relation is symmetric:\<close>

lemma possible_sym: "possible n p w w' = possible n p w' w"
  by (auto simp: possible.simps)

text \<open>In fact, \<open>possible n p\<close> is an equivalence relation:\<close>

lemma possible_refl: "valid w \<Longrightarrow> possible n p w w"
  by (auto simp: possible.simps)

lemma possible_trans: "possible n p w1 w2 \<Longrightarrow> possible n p w2 w3 \<Longrightarrow> possible n p w1 w3"
  by (auto simp: possible.simps)

section \<open>Eye colors other than blue\<close>

text \<open>Since there is no way to distinguish between the colors other than blue,
only the blue-eyed people will ever leave. To formalize this notion, we define
a function that takes a world and replaces the eye color of a specified person.
The original color is specified too, so that the transformation composes nicely
with the recursive hypothetical worlds of @{const possible}.\<close>

definition try_swap :: "'person \<Rightarrow> 'color \<Rightarrow> 'color \<Rightarrow> ('person \<Rightarrow> 'color) \<Rightarrow> ('person \<Rightarrow> 'color)" where
  "try_swap p c\<^sub>1 c\<^sub>2 w x = (if c\<^sub>1 = blue \<or> c\<^sub>2 = blue \<or> x \<noteq> p then w x else Fun.swap c\<^sub>1 c\<^sub>2 id (w x))"

lemma try_swap_valid[simp]: "valid (try_swap p c\<^sub>1 c\<^sub>2 w) = valid w"
  by (auto simp add: try_swap_def valid_def swap_def)

lemma try_swap_eq[simp]: "try_swap p c\<^sub>1 c\<^sub>2 w x = try_swap p c\<^sub>1 c\<^sub>2 w' x \<longleftrightarrow> w x = w' x"
  by (auto simp add: try_swap_def swap_def)

lemma try_swap_inv[simp]: "try_swap p c\<^sub>1 c\<^sub>2 (try_swap p c\<^sub>1 c\<^sub>2 w) = w"
  by (rule ext) (auto simp add: try_swap_def swap_def)

lemma leaves_try_swap[simp]:
  assumes "valid w"
  shows "leaves n p (try_swap p' c\<^sub>1 c\<^sub>2 w) = leaves n p w"
  using assms
proof (induction n arbitrary: p w rule: less_induct)
  case (less n)
  have "leaves n p w" if "leaves n p (try_swap p' c\<^sub>1 c\<^sub>2 w)" for w
  proof (unfold leaves.simps; rule+)
    fix w'
    assume "possible n p w w'"
    then have "possible n p (try_swap p' c\<^sub>1 c\<^sub>2 w) (try_swap p' c\<^sub>1 c\<^sub>2 w')"
      by (fastforce simp: possible.simps less.IH)
    with `leaves n p (try_swap p' c\<^sub>1 c\<^sub>2 w)` have "try_swap p' c\<^sub>1 c\<^sub>2 w' p = try_swap p' c\<^sub>1 c\<^sub>2 w p"
      unfolding leaves.simps
      by simp
    thus "w' p = w p" by simp
  qed

  with try_swap_inv show ?case by auto
qed

text \<open>This lets us prove that only blue-eyed people will ever leave the island.\<close>

proposition only_blue_eyes_leave:
  assumes "leaves n p w" and "valid w"
  shows "w p = blue"
proof (rule ccontr)
  assume "w p \<noteq> blue"
  then obtain c where c: "w p \<noteq> c"  "c \<noteq> blue"
    using colors_distinct
    by (metis distinct_length_2_or_more) 

  let ?w' = "try_swap p (w p) c w"
  have "possible n p w ?w'"
    using `valid w` apply (simp add: possible.simps)
    by (auto simp: try_swap_def)
  moreover have "?w' p \<noteq> w p"
    using c `w p \<noteq> blue` by (auto simp: try_swap_def)
  ultimately have "\<not> leaves n p w"
    by (auto simp: leaves.simps)
  with assms show False by simp
qed

section "The blue-eyed logicians"

text \<open>We will now consider the behavior of the logicians with blue eyes. First,
some simple lemmas. Reasoning about set cardinalities often requires considering infinite
sets separately. Usefully, all sets of people are finite by assumption.\<close>

lemma people_finite[simp]: "finite (S::'person set)"
proof (rule finite_subset)
  show "S \<subseteq> UNIV" by auto
  show "finite (UNIV::'person set)" by fact
qed

text \<open>Secondly, we prove a destruction rule for @{const possible}. It is strictly weaker than
the definition, but thanks to the simpler form, it's easier to guide the automation with it.\<close>
lemma possibleD_colors:
  assumes "possible n p w w'" and "p' \<noteq> p"
  shows "w' p' = w p'"
  using assms unfolding possible.simps by simp

text \<open>A central concept in the reasoning is the set of blue-eyed people someone can see.\<close>
definition blues_seen :: "('person \<Rightarrow> 'color) \<Rightarrow> 'person \<Rightarrow> 'person set" where
  "blues_seen w p = {p'. w p' = blue} - {p}"

lemma blues_seen_others:
  assumes "w p' = blue" and "p \<noteq> p'"
  shows "w p = blue \<Longrightarrow> card (blues_seen w p) = card (blues_seen w p')"
    and "w p \<noteq> blue \<Longrightarrow> card (blues_seen w p) = Suc (card (blues_seen w p'))"
proof -
  assume "w p = blue"
  then have "blues_seen w p' = blues_seen w p \<union> {p} - {p'}"
    by (auto simp add: blues_seen_def)
  moreover have "p \<notin> blues_seen w p"
    unfolding blues_seen_def by auto
  moreover have "p' \<in> blues_seen w p \<union> {p}"
    unfolding blues_seen_def using `p \<noteq> p'` `w p' = blue` by auto
  ultimately show "card (blues_seen w p) = card (blues_seen w p')"
    by simp
next
  assume "w p \<noteq> blue"
  then have "blues_seen w p' = blues_seen w p - {p'}"
    by (auto simp add: blues_seen_def)
  moreover have "p' \<in> blues_seen w p"
    unfolding blues_seen_def using `p \<noteq> p'` `w p' = blue` by auto
  ultimately show "card (blues_seen w p) = Suc (card (blues_seen w p'))"
    by (simp only: card_Suc_Diff1 people_finite)
qed

lemma blues_seen_same[simp]:
  assumes "possible n p w w'"
  shows "blues_seen w' p = blues_seen w p"
  using assms
  by (auto simp: blues_seen_def possible.simps)

lemma possible_blues_seen:
  assumes "possible n p w w'"
  assumes "w p' = blue" and "p \<noteq> p'"
  shows "w' p = blue \<Longrightarrow> card (blues_seen w p) = card (blues_seen w' p')"
    and "w' p \<noteq> blue \<Longrightarrow> card (blues_seen w p) = Suc (card (blues_seen w' p'))"
  using possibleD_colors[OF `possible n p w w'`] and blues_seen_others assms
  by (auto simp flip: blues_seen_same)

text \<open>Finally, the crux of the solution. We proceed by strong induction.\<close>

lemma blue_leaves:
  assumes "w p = blue" and "valid w"
    and guru: "w guru \<noteq> blue"
  shows "leaves n p w \<longleftrightarrow> n \<ge> card (blues_seen w p)"
  using assms
proof (induction n arbitrary: p w rule: less_induct)
  case (less n)
  show ?case
  proof
    \<comment> \<open>First, we show that day \<open>n\<close> is sufficient to deduce that the eyes are blue.\<close>
    assume "n \<ge> card (blues_seen w p)"
    have "w' p = blue" if "possible n p w w'" for w'
    proof (cases "card (blues_seen w' p)")
      case 0
      moreover from `possible n p w w'` have "valid w'"
        by (simp add: possible.simps)
      ultimately show "w' p = blue"
        unfolding valid_def blues_seen_def by auto
    next
      case (Suc k)
      \<comment> \<open>We consider the behavior of somebody else, who also has blue eyes.\<close>
      then have "blues_seen w' p \<noteq> {}"
        by auto
      then obtain p' where "w' p' = blue" and "p \<noteq> p'"
        unfolding blues_seen_def by auto
      then have "w p' = blue"
        using possibleD_colors[OF `possible n p w w'`] by simp

      have "p \<noteq> guru"
        using `w p = blue` and `w guru \<noteq> blue` by auto
      hence "w' guru \<noteq> blue"
        using `w guru \<noteq> blue` and possibleD_colors[OF `possible n p w w'`] by simp

      have "valid w'"
        using `possible n p w w'` unfolding possible.simps by simp

      show "w' p = blue"
      proof (rule ccontr)
        assume "w' p \<noteq> blue"
        \<comment> \<open>If our eyes weren't blue, then \<open>p'\<close> would see one blue-eyed person less than us.\<close>
        with possible_blues_seen[OF `possible n p w w'` `w p' = blue` `p \<noteq> p'`]
        have *: "card (blues_seen w p) = Suc (card (blues_seen w' p'))"
          by simp
        \<comment> \<open>By induction, they would've left on day \<open>k = blues_seen w' p'\<close>.\<close>
        let ?k = "card (blues_seen w' p')"
        have "?k < n"
          using `n \<ge> card (blues_seen w p)` and * by simp
        hence "leaves ?k p' w'"
          using `valid w'` `w' p' = blue` `w' guru \<noteq> blue`
          by (intro less.IH[THEN iffD2]; auto)
        \<comment> \<open>However, we know that actually, \<open>p'\<close> didn't leave that day yet.\<close>
        moreover have "\<not> leaves ?k p' w"
        proof
          assume "leaves ?k p' w"
          then have "?k \<ge> card (blues_seen w p')"
            using `?k < n` `w p' = blue` `valid w` `w guru \<noteq> blue`
            by (intro less.IH[THEN iffD1]; auto)

          have "card (blues_seen w p) = card (blues_seen w p')"
            by (intro blues_seen_others; fact)
          with * have "?k < card (blues_seen w p')"
            by simp
          with `?k \<ge> card (blues_seen w p')` show False by simp
        qed
        moreover have "leaves ?k p' w' = leaves ?k p' w"
          using `possible n p w w'` `?k < n`
          unfolding possible.simps by simp
        ultimately show False by simp
      qed
    qed
    thus "leaves n p w"
      unfolding leaves.simps using `w p = blue` by simp
  next
    \<comment> \<open>Then, we show that it's not possible to deduce the eye color any earlier.\<close>
    {
      assume "n < card (blues_seen w p)"
      \<comment> \<open>Consider a hypothetical world where \<open>p\<close> has brown eyes instead. We will prove that this
        world is \<open>possible\<close>.\<close>
      let ?w' = "w(p := brown)"
      have "?w' guru \<noteq> blue"
        using `w guru \<noteq> blue` `w p = blue`
        by auto
      have "valid ?w'"
      proof -
        from `n < card (blues_seen w p)` have "card (blues_seen w p) \<noteq> 0" by auto
        hence "blues_seen w p \<noteq> {}"
          by auto
        then obtain p' where "p' \<in> blues_seen w p"
          by auto
        hence "p \<noteq> p'" and "w p' = blue"
          by (auto simp: blues_seen_def)
        hence "?w' p' = blue" by auto
        with `?w' guru \<noteq> blue` show "valid ?w'"
          unfolding valid_def by auto
      qed
      moreover have "leaves n' p' w = leaves n' p' ?w'" if "n' < n" for n' p'
      proof -
        have not_leavesI: "\<not>leaves n' p' w'"
          if "valid w'"  "w' guru \<noteq> blue" and P: "w' p' = blue \<Longrightarrow> n' < card (blues_seen w' p')" for w'
        proof (cases "w' p' = blue")
          case True
          then have "leaves n' p' w' \<longleftrightarrow> n' \<ge> card (blues_seen w' p')"
            using less.IH `n' < n` `valid w'` `w' guru \<noteq> blue`
            by simp
          with P[OF `w' p' = blue`] show "\<not>leaves n' p' w'" by simp
        next
          case False
          then show "\<not> leaves n' p' w'"
            using only_blue_eyes_leave `valid w'` by auto
        qed

        have "\<not>leaves n' p' w"
        proof (intro not_leavesI)
          assume "w p' = blue"
          with `w p = blue` have "card (blues_seen w p) = card (blues_seen w p')"
            apply (cases "p = p'", simp)
            by (intro blues_seen_others; auto)
          with `n' < n` and `n < card (blues_seen w p)` show "n' < card (blues_seen w p')"
            by simp
        qed fact+

        moreover have "\<not> leaves n' p' ?w'"
        proof (intro not_leavesI)
          assume "?w' p' = blue"
          with colors_distinct have "p \<noteq> p'" and "?w' p \<noteq> blue" by auto
          hence "card (blues_seen ?w' p) = Suc (card (blues_seen ?w' p'))"
            using `?w' p' = blue` 
            by (intro blues_seen_others; auto)
          moreover have "blues_seen w p = blues_seen ?w' p"
            unfolding blues_seen_def by auto
          ultimately show "n' < card (blues_seen ?w' p')"
            using `n' < n` and `n < card (blues_seen w p)`
            by auto
        qed fact+

        ultimately show "leaves n' p' w = leaves n' p' ?w'" by simp
      qed
      ultimately have "possible n p w ?w'"
        using `valid w`
        by (auto simp: possible.simps)
      moreover have "?w' p \<noteq> blue"
        using colors_distinct by auto
      ultimately have "\<not> leaves n p w"
        unfolding leaves.simps
        using `w p = blue` by blast
    }
    then show "leaves n p w \<Longrightarrow> n \<ge> card (blues_seen w p)"
      by fastforce
  qed
qed

text \<open>This can be combined into a theorem that describes the behavior of the logicians based
on the objective count of blue-eyed people, and not the count by a specific person. The xkcd
puzzle is the instance where \<open>n = 99\<close>.\<close>

theorem blue_eyes:
  assumes "card {p. w p = blue} = Suc n" and "valid w" and "w guru \<noteq> blue"
  shows "leaves k p w \<longleftrightarrow> w p = blue \<and> k \<ge> n"
proof (cases "w p = blue")
  case True
  with assms have "card (blues_seen w p) = n"
    unfolding blues_seen_def by simp
  then show ?thesis
    using `w p = blue` `valid w` `w guru \<noteq> blue` blue_leaves
    by simp
next
  case False
  then show ?thesis
    using only_blue_eyes_leave `valid w` by auto
qed

end

(*<*)
end
(*>*)

section \<open>Future work\<close>

text \<open>After completing this formalization, I have been made aware of epistemic logic.
The @{emph \<open>possible worlds\<close>} model in \cref{sec:world} turns out to be quite similar
to the usual semantics of this logic. It might be interesting to solve this puzzle within
the axiom system of epistemic logic, without explicit reasoning about possible worlds.\<close>