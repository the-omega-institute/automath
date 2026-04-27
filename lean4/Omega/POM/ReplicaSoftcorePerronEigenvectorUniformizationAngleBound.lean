import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- Paper label:
`prop:pom-replica-softcore-perron-eigenvector-uniformization-angle-bound`. -/
theorem paper_pom_replica_softcore_perron_eigenvector_uniformization_angle_bound (q : ℕ)
    (sinAngle dist QE_norm E_norm phi : ℝ)
    (hQE : QE_norm =
      Real.sqrt (((5 : ℝ) ^ q / (2 : ℝ) ^ (q + 2)) -
        ((9 : ℝ) ^ q / (2 : ℝ) ^ (2 * q + 2))))
    (hE : E_norm = (1 / 2 : ℝ) * phi ^ q)
    (hangle : sinAngle ≤ QE_norm / ((2 : ℝ) ^ (q - 1) - E_norm))
    (hdist : dist ≤ Real.sqrt 2 * sinAngle) :
    sinAngle ≤
        Real.sqrt (((5 : ℝ) ^ q / (2 : ℝ) ^ (q + 2)) -
          ((9 : ℝ) ^ q / (2 : ℝ) ^ (2 * q + 2))) /
          ((2 : ℝ) ^ (q - 1) - (1 / 2 : ℝ) * phi ^ q) ∧
      dist ≤
        Real.sqrt (((5 : ℝ) ^ q / (2 : ℝ) ^ (q + 1)) -
          ((9 : ℝ) ^ q / (2 : ℝ) ^ (2 * q + 1))) /
          ((2 : ℝ) ^ (q - 1) - (1 / 2 : ℝ) * phi ^ q) := by
  let A : ℝ :=
    ((5 : ℝ) ^ q / (2 : ℝ) ^ (q + 2)) -
      ((9 : ℝ) ^ q / (2 : ℝ) ^ (2 * q + 2))
  let B : ℝ :=
    ((5 : ℝ) ^ q / (2 : ℝ) ^ (q + 1)) -
      ((9 : ℝ) ^ q / (2 : ℝ) ^ (2 * q + 1))
  let D : ℝ := (2 : ℝ) ^ (q - 1) - (1 / 2 : ℝ) * phi ^ q
  have hsin : sinAngle ≤ Real.sqrt A / D := by
    simpa [A, D, hQE, hE] using hangle
  have hB : B = 2 * A := by
    dsimp [A, B]
    ring_nf
  have hsqrt : Real.sqrt 2 * Real.sqrt A = Real.sqrt B := by
    by_cases hA : 0 ≤ A
    · rw [hB, Real.sqrt_mul (show 0 ≤ (2 : ℝ) by norm_num)]
    · have hA' : A ≤ 0 := le_of_not_ge hA
      have h2A : 2 * A ≤ 0 := by nlinarith
      rw [Real.sqrt_eq_zero_of_nonpos hA', hB, Real.sqrt_eq_zero_of_nonpos h2A, mul_zero]
  refine ⟨hsin, ?_⟩
  have hdist' : dist ≤ Real.sqrt 2 * (Real.sqrt A / D) :=
    le_trans hdist (mul_le_mul_of_nonneg_left hsin (Real.sqrt_nonneg 2))
  have hrewrite : Real.sqrt 2 * (Real.sqrt A / D) = Real.sqrt B / D := by
    rw [← mul_div_assoc, hsqrt]
  have hdist'' : dist ≤ Real.sqrt B / D := hrewrite ▸ hdist'
  simpa [A, B, D] using hdist''

end Omega.POM
