import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9v-resonance-zero-count-renormalization`. -/
theorem paper_xi_time_part9v_resonance_zero_count_renormalization
    (Nphi : Real -> Nat)
    (hrec : forall R, 0 <= R ->
      Nphi R =
        Nphi (R / Real.goldenRatio) +
          2 * Nat.floor (R / Real.goldenRatio ^ 2 + 1 / 2)) :
    (forall R, 0 <= R ->
      Nphi R =
        Nphi (R / Real.goldenRatio) +
          2 * Nat.floor (R / Real.goldenRatio ^ 2 + 1 / 2)) ∧
      (forall R, 0 <= R ->
        Nphi (Real.goldenRatio * R) =
          Nphi R + 2 * Nat.floor (R / Real.goldenRatio + 1 / 2)) := by
  refine ⟨hrec, ?_⟩
  intro R hR
  have hscaled_nonneg : 0 <= Real.goldenRatio * R :=
    mul_nonneg Real.goldenRatio_pos.le hR
  have h := hrec (Real.goldenRatio * R) hscaled_nonneg
  have harg1 : Real.goldenRatio * R / Real.goldenRatio = R := by
    field_simp [Real.goldenRatio_ne_zero]
  have harg2 : Real.goldenRatio * R / Real.goldenRatio ^ 2 = R / Real.goldenRatio := by
    field_simp [Real.goldenRatio_ne_zero]
  have harg2' : Real.goldenRatio * R / (Real.goldenRatio + 1) = R / Real.goldenRatio := by
    simpa [Real.goldenRatio_sq] using harg2
  simpa [harg1, harg2, harg2'] using h

end Omega.Zeta
