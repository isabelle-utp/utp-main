theory insertion_sort
  imports "UTP.utp_easy_parser"
begin

alphabet st_insertion_sort =
  arr :: "int list"
  i   :: nat
  key :: int
  j   :: nat
  n   :: nat

abbreviation insertion_sort :: "st_insertion_sort hrel" where
  "insertion_sort \<equiv>
  i := 1 ;;
  n := #arr ;;
  while (i < n)
  do 
    key := arr[i] ;;
    j := i ;;
    while (j > 0 \<and> arr[j-1] > key)
    do
      arr[j] := arr[j-1] ;;
      j := (j - 1)
    od ;;
    arr[j] := key ;;
    i := (i + 1)
  od"

lemma "TRY([&arr \<mapsto>\<^sub>s \<guillemotleft>[4,3,7,1,12,8]\<guillemotright>] \<Turnstile> insertion_sort)"
  apply (sym_eval)
  oops


end