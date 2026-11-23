import EqualOpportunity

/-! Prints the axioms each paper theorem depends on.

Run:  lake env lean scripts/axioms.lean

A fully checked theorem lists exactly `propext`, `Classical.choice`, `Quot.sound`.
`sorryAx` in the list means some proof it depends on is still `sorry`. -/

open EqualOpportunity.Paper

#print axioms thm_3_1
#print axioms thm_3_2
#print axioms cor_eps2
#print axioms thm_3_3
#print axioms thm_3_4
#print axioms thm_3_4_upper
#print axioms thm_3_4_lower
#print axioms thm_3_4_degenerate
#print axioms app_thm_3_3
#print axioms app_thm_3_4_lower
#print axioms app_thm_3_4_lower_tight
#print axioms app_thm_3_4_upper
#print axioms app_thm_3_4
