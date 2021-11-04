\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Examples\<close>
theory SpecCheck_Examples
imports SpecCheck_Dynamic
begin

subsection \<open>List examples\<close>

ML \<open>
open SpecCheck
open SpecCheck_Dynamic
structure Gen = SpecCheck_Generator
structure Prop = SpecCheck_Property
structure Show = SpecCheck_Show
structure Shrink = SpecCheck_Shrink
structure Random = SpecCheck_Random
\<close>

ML_command \<open>
let
  val int_gen = Gen.range_int (~10000000, 10000000)
  val size_gen = Gen.nonneg 10
  val check_list = check_shrink (Show.list Show.int) (Shrink.list Shrink.int)
    (Gen.list size_gen int_gen)
  fun list_test (k, f, xs) =
    AList.lookup (op=) (AList.map_entry (op=) k f xs) k = Option.map f (AList.lookup (op=) xs k)

  val list_test_show = Show.zip3 Show.int Show.none (Show.list (Show.zip Show.int Show.int))
  val list_test_gen = Gen.zip3 int_gen (Gen.function' int_gen)
    (Gen.list size_gen (Gen.zip int_gen int_gen))
in
  Lecker.test_group @{context} (Random.new ()) [
    Prop.prop (fn xs => rev xs = xs) |> check_list "rev = I",
    Prop.prop (fn xs => rev (rev xs) = xs) |> check_list "rev o rev = I",
    Prop.prop list_test |> check list_test_show list_test_gen "lookup map equiv map lookup"
  ]
end
\<close>

text \<open>The next three examples roughly correspond to the above test group (except that there's no
shrinking). Compared to the string-based method, the method above is more flexible - you can change
your generators, shrinking methods, and show instances - and robust - you are not reflecting strings
(which might contain typos) but entering type-checked code. In exchange, it is a bit more work to
set up the generators. However, in practice, one shouldn't rely on default generators in most cases
anyway.\<close>

ML_command \<open>
check_dynamic @{context} "ALL xs. rev xs = xs";
\<close>

ML_command \<open>
check_dynamic @{context} "ALL xs. rev (rev xs) = xs";
\<close>

subsection \<open>AList Specification\<close>

ML_command \<open>
(*map_entry applies the function to the element*)
check_dynamic @{context} (implode
  ["ALL k f xs. AList.lookup (op =) (AList.map_entry (op =) k f xs) k = ",
   "Option.map f (AList.lookup (op =) xs k)"])
\<close>

ML_command \<open>
(*update always results in an entry*)
check_dynamic @{context} "ALL k v xs. AList.defined (op =) (AList.update (op =) (k, v) xs) k";
\<close>

ML_command \<open>
(*update always writes the value*)
check_dynamic @{context}
  "ALL k v xs. AList.lookup (op =) (AList.update (op =) (k, v) xs) k = SOME v";
\<close>

ML_command \<open>
(*default always results in an entry*)
check_dynamic @{context} "ALL k v xs. AList.defined (op =) (AList.default (op =) (k, v) xs) k";
\<close>

ML_command \<open>
(*delete always removes the entry*)
check_dynamic @{context} "ALL k xs. not (AList.defined (op =) (AList.delete (op =) k xs) k)";
\<close>

ML_command \<open>
(*default writes the entry iff it didn't exist*)
check_dynamic @{context} (implode
  ["ALL k v xs. (AList.lookup (op =) (AList.default (op =) (k, v) xs) k = ",
   "(if AList.defined (op =) xs k then AList.lookup (op =) xs k else SOME v))"])
\<close>

subsection \<open>Examples on Types and Terms\<close>

ML_command \<open>
check_dynamic @{context} "ALL f g t. map_types (g o f) t = (map_types f o map_types g) t";
\<close>

ML_command \<open>
check_dynamic @{context} "ALL f g t. map_types (f o g) t = (map_types f o map_types g) t";
\<close>


text \<open>One would think this holds:\<close>

ML_command \<open>
check_dynamic @{context} "ALL t ts. strip_comb (list_comb (t, ts)) = (t, ts)"
\<close>

text \<open>But it only holds with this precondition:\<close>

ML_command \<open>
check_dynamic @{context}
  "ALL t ts. case t of _ $ _ => true | _ => strip_comb (list_comb (t, ts)) = (t, ts)"
\<close>

subsection \<open>Some surprises\<close>

ML_command \<open>
check_dynamic @{context} "ALL Ts t. type_of1 (Ts, t) = fastype_of1 (Ts, t)"
\<close>


ML_command \<open>
val thy = \<^theory>;
check_dynamic (Context.the_local_context ())
  "ALL t u. if Pattern.matches thy (t, u) then Term.could_unify (t, u) else true"
\<close>

end
