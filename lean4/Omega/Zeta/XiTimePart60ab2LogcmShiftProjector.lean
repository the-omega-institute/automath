import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.GU.LogCmStableInverseExponentialSeparation

namespace Omega.Zeta

open scoped BigOperators

/-- The finite product of spectral gaps appearing in the shift-projector denominator. -/
noncomputable def xi_time_part60ab2_logcm_shift_projector_denominator
    (q : ℕ → ℝ) (r : ℕ) : ℝ :=
  Finset.prod (Finset.Icc 1 (r - 1)) (fun j => q r - q j)

/-- Concrete package for the shift-projector identity: if the derived shift-annihilator limit
already identifies `f r` with `a r` times the finite product over the earlier spectral gaps, then
strict separation of the `q_j` makes the denominator nonzero and division recovers `a r`. -/
def xi_time_part60ab2_logcm_shift_projector_package (f q a : ℕ → ℝ) : Prop :=
  ∀ r : ℕ,
    1 ≤ r →
    (∀ j : ℕ, 1 ≤ j → j < r → q r ≠ q j) →
    f r = a r * xi_time_part60ab2_logcm_shift_projector_denominator q r →
    xi_time_part60ab2_logcm_shift_projector_denominator q r ≠ 0 ∧
      f r / xi_time_part60ab2_logcm_shift_projector_denominator q r = a r

/-- Paper label: `thm:xi-time-part60ab2-logcm-shift-projector`. The strict separation of the
spectral parameters implies each factor `q_r - q_j` is nonzero, hence the finite denominator
product is nonzero, and the existing product identity can be divided through to isolate `a_r`. -/
theorem paper_xi_time_part60ab2_logcm_shift_projector
    (f q a : ℕ → ℝ) : xi_time_part60ab2_logcm_shift_projector_package f q a := by
  intro r hr hsep hf
  have hden_ne : xi_time_part60ab2_logcm_shift_projector_denominator q r ≠ 0 := by
    unfold xi_time_part60ab2_logcm_shift_projector_denominator
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hjr⟩
    exact sub_ne_zero.mpr (hsep j hj1 (by omega))
  refine ⟨hden_ne, ?_⟩
  calc
    f r / xi_time_part60ab2_logcm_shift_projector_denominator q r =
        (a r * xi_time_part60ab2_logcm_shift_projector_denominator q r) /
          xi_time_part60ab2_logcm_shift_projector_denominator q r := by
          rw [hf]
    _ = a r := by
      field_simp [hden_ne]

end Omega.Zeta
