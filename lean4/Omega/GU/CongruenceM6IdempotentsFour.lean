import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic

namespace Omega.GU.CongruenceM6IdempotentsFour

/-- The idempotents in `ZMod 21`. -/
def idem21 : Finset (ZMod 21) := Finset.univ.filter (fun x => x * x = x)

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: `ZMod 21` has exactly four idempotents.
    prop:bdry-tower-zeck-gut-part2 -/
theorem paper_congruence_m6_idempotents_four_seeds : idem21.card = 4 := by
  decide

/-- Wrapper theorem matching the paper-facing package name. -/
theorem paper_congruence_m6_idempotents_four_package : idem21.card = 4 :=
  paper_congruence_m6_idempotents_four_seeds

/-- Paper-facing theorem matching the statement label used in the manuscript.
    prop:congruence-m6-idempotents-four -/
theorem paper_congruence_m6_idempotents_four : idem21.card = 4 :=
  paper_congruence_m6_idempotents_four_package

end Omega.GU.CongruenceM6IdempotentsFour
