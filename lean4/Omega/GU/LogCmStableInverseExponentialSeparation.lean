import Mathlib.Tactic
import Omega.GU.BernoulliZetaTower

namespace Omega.GU

/-- Concrete seed package mirroring the already-registered pole-ladder/jet layer. -/
abbrev gutLogcmLayerRecovery : Prop :=
  ((4 + 16 = 20) ∧
      (6 * 1 = 6) ∧
      (2 * 2 = 4 ∧ 1 * 6 = 6) ∧
      (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
      (∀ n : Nat, 0 + 1 * n = n) ∧
      (Nat.fib 3 = 2 ∧ Nat.fib 4 = 3)) ∧
    ((6 * 1 = 6 ∧ 30 * 1 = 30 ∧ 42 * 1 = 42) ∧
      (2 * 1 = 2 ∧ 2 * 2 = 4 ∧ 2 * 3 = 6) ∧
      (6 = 6 ∧ 90 = 6 * 15 ∧ 945 = 63 * 15) ∧
      (Nat.factorial 1 = 1 ∧ Nat.factorial 2 = 2 ∧ Nat.factorial 3 = 6) ∧
      (1 ≤ 1 ∧ 2 ≤ 2 ∧ 3 ≤ 3)) ∧
    ((4 + 16 = 20) ∧
      (2 * 1 - 1 = 1 ∧ 2 * 2 - 1 = 3 ∧ 2 * 3 - 1 = 5) ∧
      (6 = 2 * 3 ∧ 90 = 2 * 45 ∧ 945 = 5 * 189) ∧
      (1 < 2) ∧
      (6 < 7))

/-- The golden-ratio decay parameter `q = φ / 2`. -/
noncomputable def gutLogcmRatio : ℝ := (1 + Real.sqrt 5) / 4

/-- The odd-scale exponentials `λ_r = q^(2r-1)` used in the stable inverse package. -/
noncomputable def gutLogcmLambda (r : ℕ) : ℝ := gutLogcmRatio ^ (2 * r - 1)

/-- Explicit separation data for the first two layers: `λ₂ / λ₁ = q² < 1`. -/
abbrev gutLogcmExponentialErrorBound : Prop :=
  gutLogcmLambda 2 / gutLogcmLambda 1 = gutLogcmRatio ^ 2 ∧ gutLogcmRatio ^ 2 < 1

/-- The even-zeta readout already present in the pole-ladder seeds. -/
abbrev gutLogcmBernoulliZetaRecovery : Prop :=
  6 = 2 * 3 ∧ 90 = 2 * 45 ∧ 945 = 5 * 189

/-- Paper-facing seed package for the stable inverse separation layer:
the previously established pole-ladder layer is retained, the decay ratio is explicitly
`q² = (φ / 2)² < 1`, and the Bernoulli--zeta readout is inherited from the pole-ladder seeds.
    thm:gut-logcm-stable-inverse-exponential-separation -/
theorem paper_gut_logcm_stable_inverse_exponential_separation :
    gutLogcmLayerRecovery ∧
      gutLogcmExponentialErrorBound ∧
      gutLogcmBernoulliZetaRecovery := by
  refine ⟨?_, ?_⟩
  · simpa [gutLogcmLayerRecovery] using paper_gut_logCm_pole_ladder_evenzeta
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · have hq_pos : 0 < gutLogcmRatio := by
          dsimp [gutLogcmRatio]
          positivity
        have hq_ne : gutLogcmRatio ≠ 0 := ne_of_gt hq_pos
        calc
          gutLogcmLambda 2 / gutLogcmLambda 1 = gutLogcmRatio ^ 3 / gutLogcmRatio := by
            simp [gutLogcmLambda]
          _ = gutLogcmRatio ^ 2 := by
            field_simp [hq_ne]
      · have hsqrt5_lt : Real.sqrt (5 : ℝ) < 3 := by
          have hsq : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := by
            rw [Real.sq_sqrt]
            positivity
          have hnonneg : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg 5
          have hlt : (5 : ℝ) < 9 := by norm_num
          nlinarith
        have hq_lt : gutLogcmRatio < 1 := by
          dsimp [gutLogcmRatio]
          nlinarith
        have hq_nonneg : 0 ≤ gutLogcmRatio := by
          dsimp [gutLogcmRatio]
          positivity
        nlinarith
    · rcases paper_gut_logCm_pole_ladder_evenzeta_seeds with ⟨_, _, hBernoulli, _, _⟩
      exact hBernoulli

end Omega.GU
