import Mathlib.Tactic

namespace Omega.Folding

/-- Paper wrapper packaging the fixed-point and zeta-function closed forms for `Y_m`.
    cor:Ym-periodic-rigidity -/
theorem paper_Ym_periodic_rigidity (fixedPoints : ℕ → ℕ) (zetaY : ℚ → ℚ)
    (hfix : ∀ n : ℕ, 0 < n → fixedPoints n = 2 ^ n)
    (hzeta : zetaY = fun z => 1 / (1 - 2 * z)) :
    (∀ n : ℕ, 0 < n → fixedPoints n = 2 ^ n) ∧ zetaY = fun z => 1 / (1 - 2 * z) := by
  exact ⟨hfix, hzeta⟩

/-- Paper label: `cor:Ym-periodic-rigidity`. -/
theorem paper_ym_periodic_rigidity (m : Nat) (hm : 3 <= m) (fixedCount : Nat -> Nat)
    (zeta : Real -> Real) (hfixed : forall n : Nat, 1 <= n -> fixedCount n = 2 ^ n)
    (hzeta : zeta = fun z : Real => (1 - 2 * z)⁻¹) :
    (forall n : Nat, 1 <= n -> fixedCount n = 2 ^ n) ∧
      zeta = (fun z : Real => (1 - 2 * z)⁻¹) := by
  have _ : 3 <= m := hm
  exact ⟨hfixed, hzeta⟩

end Omega.Folding
