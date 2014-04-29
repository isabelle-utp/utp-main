(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header "Standard Set Implementations"
theory SetStdImpl
imports 
  ListSetImpl 
  ListSetImpl_Invar 
  ListSetImpl_NotDist
  ListSetImpl_Sorted
  RBTSetImpl HashSet 
  TrieSetImpl 
  ArrayHashSet
  ArraySetImpl
begin
text_raw {*\label{thy:SetStdImpl}*}
text {*
  This theory summarizes standard set implementations, namely list-sets RB-tree-sets, trie-sets and hashsets.
*}

end
