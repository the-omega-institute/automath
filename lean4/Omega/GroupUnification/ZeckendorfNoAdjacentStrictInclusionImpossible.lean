import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Omega.Folding.ZeckendorfSignature

namespace Omega.GroupUnification

/-- Paper label: `cor:zeckendorf-no-adjacent-strict-inclusion-impossible`.
The paper-facing name is a thin wrapper around the existing strict-inclusion exclusion lemma for
gap-`≥ 2` Zeckendorf index sets. -/
theorem paper_zeckendorf_no_adjacent_strict_inclusion_impossible
    (S : Finset Nat)
    (h_gap : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a : Int) - b ≠ 1 ∧ (a : Int) - b ≠ -1)
    (h4 : 4 ∈ S) (h6 : 6 ∈ S) (h8 : 8 ∈ S) :
    5 ∉ S ∧ 7 ∉ S := by
  exact Omega.ZeckSig.zeckendorf_no_adjacent_strict_inclusion S h_gap h4 h6 h8

end Omega.GroupUnification
