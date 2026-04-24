import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-entropy-loss-feasibility-cone`. -/
theorem paper_pom_entropy_loss_feasibility_cone (P : Nat -> Real) (alphaStar logPhi : Real)
    (hsubadd : ∀ a b : Nat, 2 ≤ b -> P (a * b) ≤ (b : Real) * P a)
    (hupper : ∀ a b : Nat, 2 ≤ b -> (b : Real) * P a - P (a * b) ≤ (b - 1 : Real) * logPhi)
    (hquot : ∀ a : Nat, ∀ eps > 0, ∃ B : Nat, ∀ b : Nat, B ≤ b ->
      abs (P (a * b) / b - (a : Real) * alphaStar) < eps) :
    (∀ a b : Nat, 2 ≤ b -> 0 ≤ (b : Real) * P a - P (a * b) ∧
      (b : Real) * P a - P (a * b) ≤ (b - 1 : Real) * logPhi) ∧
    (∀ a b c : Nat, 2 ≤ b -> 2 ≤ c ->
      ((b * c : Nat) : Real) * P a - P (a * (b * c)) =
        (c : Real) * ((b : Real) * P a - P (a * b)) +
          ((c : Real) * P (a * b) - P (a * b * c))) ∧
    (∀ a : Nat, ∀ eps > 0, ∃ B : Nat, ∀ b : Nat, B ≤ b ->
      abs ((((b : Real) * P a - P (a * b)) / b) - (P a - (a : Real) * alphaStar)) < eps) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hb
    refine ⟨?_, hupper a b hb⟩
    linarith [hsubadd a b hb]
  · intro a b c _hb _hc
    rw [Nat.mul_assoc, Nat.cast_mul]
    ring
  · intro a eps heps
    rcases hquot a eps heps with ⟨B, hB⟩
    refine ⟨max B 1, ?_⟩
    intro b hb
    have hBb : B ≤ b := le_trans (Nat.le_max_left _ _) hb
    have h1b : 1 ≤ b := le_trans (Nat.le_max_right _ _) hb
    have hbpos : 0 < b := Nat.succ_le_iff.mp h1b
    have hb0 : (b : Real) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hbpos
    have hquot' := hB b hBb
    have hrewrite :
        ((((b : Real) * P a - P (a * b)) / b) - (P a - (a : Real) * alphaStar)) =
          - (P (a * b) / b - (a : Real) * alphaStar) := by
      calc
        ((((b : Real) * P a - P (a * b)) / b) - (P a - (a : Real) * alphaStar))
            = ((((b : Real) * P a) / b - P (a * b) / b) -
                (P a - (a : Real) * alphaStar)) := by
                rw [sub_div]
        _ = ((P a - P (a * b) / b) - (P a - (a : Real) * alphaStar)) := by
              rw [mul_div_cancel_left₀ (P a) hb0]
        _ = - (P (a * b) / b - (a : Real) * alphaStar) := by ring
    rw [hrewrite, abs_neg]
    exact hquot'

end Omega.POM
