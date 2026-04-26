import Omega.POM.OrderSpatialization

namespace Omega.POM

/-- Paper label: `prop:pom-order-elimination-correct`.
This is the paper-facing restatement of the hard-threshold RCRT correctness claim, obtained
directly from the stronger spatialization theorem. -/
theorem paper_pom_order_elimination_correct (B P : ℕ) (reconstruct : ℤ → ℤ) (hP : P > 2 * B)
    (hrec : ∀ {x : ℤ}, |x| ≤ B → reconstruct (x % P) = x) {x y : ℤ} (hx : |x| ≤ B)
    (hy : |y| ≤ B) :
    ((x % P : ℤ) = y % P ↔ x = y) ∧
      (reconstruct (x % P) ≤ reconstruct (y % P) ↔ x ≤ y) := by
  simpa using paper_pom_order_spatialization B P reconstruct hP hrec hx hy

end Omega.POM
