theory Lattice_extra
imports "~~/src/HOL/Algebra/Lattice"
begin

sublocale weak_bounded_lattice \<subseteq> weak_partial_order ..

sublocale bounded_lattice \<subseteq> partial_order ..

sublocale bounded_lattice \<subseteq> weak_bounded_lattice ..

end