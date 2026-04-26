import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `cor:pom-diagonal-rate-binary-linear-mixture`. -/
theorem paper_pom_diagonal_rate_binary_linear_mixture (p δ δ0 ε : ℝ)
    (hδ0 : δ0 = 2 * p * (1 - p)) (hδ0_ne : δ0 ≠ 0) (hε : ε = 1 - δ / δ0) :
    (fun x y : Bool =>
        if x = y then (if x then p - δ / 2 else 1 - p - δ / 2) else δ / 2) =
      (fun x y : Bool =>
        (1 - ε) * (if x then p else 1 - p) * (if y then p else 1 - p) +
          ε * (if x = y then (if x then p else 1 - p) else 0)) := by
  subst ε
  have hδ0_half : δ0 / 2 = p * (1 - p) := by
    rw [hδ0]
    ring
  have hmix : δ / δ0 * (p * (1 - p)) = δ / 2 := by
    rw [← hδ0_half]
    field_simp [hδ0_ne]
  funext x y
  cases x <;> cases y <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  · rw [← hmix]
    ring
  · rw [← hmix]
    ring
  · rw [← hmix]
    ring
  · rw [← hmix]
    ring

end Omega.POM
