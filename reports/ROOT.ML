Thy_Load.legacy_add_path "../theories";
Thy_Load.legacy_add_path "../theories/utils";
Thy_Load.legacy_add_path "../theories/generic";
Thy_Load.legacy_add_path "../theories/models";
Thy_Load.legacy_add_path "../theories/theories";

no_document use_thys [
  "Nat_Bijection",
  "Countable"
];

use_thys [
  "GLOBAL",
  "utp_base",
  "utp_config",
  "utp_name",
  "utp_sorts",
  "utp_theory",
  "utp_sets",
  "utp_generic",
  "utp_typed_pred",
  "utp_theories",
  "utp_default_values",
  "utp_default_pred"
];
