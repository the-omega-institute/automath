import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-tqft-noncontractible-genus-equals-odd-spectrum`. -/
theorem paper_conclusion_tqft_noncontractible_genus_equals_odd_spectrum
    {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ)
    (noncontractible : X → Prop) [DecidablePred noncontractible]
    [DecidablePred (fun x => Odd (d x))]
    (hodd : ∀ x, noncontractible x ↔ Odd (d x)) (g : ℕ) :
    (∑ x ∈ Finset.univ.filter noncontractible, (d x : ℤ) ^ g) =
      ∑ x ∈ Finset.univ.filter (fun x => Odd (d x)), (d x : ℤ) ^ g := by
  classical
  have hfilter :
      Finset.univ.filter noncontractible = Finset.univ.filter (fun x => Odd (d x)) := by
    ext x
    simp [hodd x]
  rw [hfilter]

end Omega.Conclusion
