import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

/-- `cor:conclusion-finite-periodic-peripheral-phase-fourier-tomography` -/
theorem paper_conclusion_finite_periodic_peripheral_phase_fourier_tomography {L : ℕ}
    [NeZero L] (m : Fin L → ℂ) (χ : Fin L → Fin L → ℂ)
    (hortho : ∀ r a : Fin L,
      (1 / (L : ℂ)) * ∑ q : Fin L, χ a q * (χ r q)⁻¹ = if a = r then 1 else 0) :
    ∀ r : Fin L,
      (1 / (L : ℂ)) * ∑ q : Fin L, (∑ a : Fin L, m a * χ a q) * (χ r q)⁻¹ =
        m r := by
  classical
  intro r
  calc
    (1 / (L : ℂ)) * ∑ q : Fin L, (∑ a : Fin L, m a * χ a q) * (χ r q)⁻¹ =
        ∑ q : Fin L, ∑ a : Fin L, (1 / (L : ℂ)) * (m a * χ a q * (χ r q)⁻¹) := by
          rw [mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_mul, mul_sum]
    _ =
        ∑ a : Fin L, ∑ q : Fin L, (1 / (L : ℂ)) * (m a * χ a q * (χ r q)⁻¹) := by
          rw [Finset.sum_comm]
    _ =
        ∑ a : Fin L, m a * ((1 / (L : ℂ)) * ∑ q : Fin L, χ a q * (χ r q)⁻¹) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
    _ = ∑ a : Fin L, m a * (if a = r then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hortho r a]
    _ = m r := by
          rw [Finset.sum_eq_single r]
          · simp
          · intro a ha har
            simp [har]
          · intro hr
            exact False.elim (hr (Finset.mem_univ r))

end Omega.Conclusion
