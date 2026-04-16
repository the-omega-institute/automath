import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

namespace Omega.POM

/-- If a residue readout comes with a reconstruction procedure that is exact on the bounded
interval `[-B, B]`, then equality and order on that interval can be decided by reconstructing from
the residue and comparing in `ℤ`. The inequality `P > 2B` is kept as the paper's CRT-budget
certificate for the existence of such a reconstruction. -/
theorem paper_pom_order_spatialization
    (B P : ℕ) (reconstruct : ℤ → ℤ) (_hP : P > 2 * B)
    (hrec : ∀ {x : ℤ}, |x| ≤ B → reconstruct (x % P) = x)
    {x y : ℤ} (hx : |x| ≤ B) (hy : |y| ≤ B) :
    ((x % P : ℤ) = y % P ↔ x = y) ∧
      (reconstruct (x % P) ≤ reconstruct (y % P) ↔ x ≤ y) := by
  constructor
  · constructor
    · intro hmod
      have hx' : reconstruct (x % P) = x := hrec hx
      have hy' : reconstruct (y % P) = y := hrec hy
      rw [← hx', hmod, hy']
    · intro hxy
      simp [hxy]
  · have hx' : reconstruct (x % P) = x := hrec hx
    have hy' : reconstruct (y % P) = y := hrec hy
    simp [hx', hy']

end Omega.POM
