import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-principal-shadow-inverse-limit-pointed-rigidity`.
Finite agreement on every principal-shadow prefix gives equality of all moments by applying the
`n = k + 1` layer to the `k`th moment; moment determinacy then gives pointed-unitary rigidity. -/
theorem paper_conclusion_principal_shadow_inverse_limit_pointed_rigidity
    (moment target : Nat → ℝ) (pointedUnitaryEquivalent : Prop)
    (hMomentDeterminate : (∀ k : Nat, moment k = target k) → pointedUnitaryEquivalent)
    (hTower :
      ∀ n : Nat, 1 ≤ n → ∀ k : Nat, k ≤ 2 * n - 1 → moment k = target k) :
    pointedUnitaryEquivalent := by
  apply hMomentDeterminate
  intro k
  exact hTower (k + 1) (by omega) k (by omega)

end Omega.Conclusion
