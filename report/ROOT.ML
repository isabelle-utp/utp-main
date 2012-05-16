
(* Temporary hack, remove when all sorrys have been proved. *)

quick_and_dirty := true;

no_document use_thys [
  "~~/src/HOL/Library/Countable",
  "~~/src/HOL/Library/Nat_Bijection"
];

use_thys [ "../theories/utp" ];
