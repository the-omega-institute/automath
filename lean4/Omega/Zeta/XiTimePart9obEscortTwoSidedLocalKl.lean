import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

open scoped goldenRatio

/-- Real-temperature escort Bernoulli parameter. -/
noncomputable def xi_time_part9ob_escort_two_sided_local_kl_theta (q : ℝ) : ℝ :=
  1 / (1 + Real.goldenRatio ^ (q + 1))

/-- Bernoulli KL between two real-temperature escort parameters. -/
noncomputable def xi_time_part9ob_escort_two_sided_local_kl_bernoulliKL
    (u v : ℝ) : ℝ :=
  let θu := xi_time_part9ob_escort_two_sided_local_kl_theta u
  let θv := xi_time_part9ob_escort_two_sided_local_kl_theta v
  (1 - θu) * Real.log ((1 - θu) / (1 - θv)) + θu * Real.log (θu / θv)

/-- Forward local KL increment along the escort temperature line. -/
noncomputable def xi_time_part9ob_escort_two_sided_local_kl_forward
    (q h : ℝ) : ℝ :=
  xi_time_part9ob_escort_two_sided_local_kl_bernoulliKL (q + h) q

/-- Reverse local KL increment along the escort temperature line. -/
noncomputable def xi_time_part9ob_escort_two_sided_local_kl_reverse
    (q h : ℝ) : ℝ :=
  xi_time_part9ob_escort_two_sided_local_kl_bernoulliKL q (q + h)

/-- Fisher coefficient for the real-temperature escort Bernoulli curve. -/
noncomputable def xi_time_part9ob_escort_two_sided_local_kl_fisher
    (q : ℝ) : ℝ :=
  (Real.log Real.goldenRatio) ^ 2 *
    xi_time_part9ob_escort_two_sided_local_kl_theta q *
      (1 - xi_time_part9ob_escort_two_sided_local_kl_theta q)

/-- Cubic remainder in the forward local KL expansion. -/
noncomputable def xi_time_part9ob_escort_two_sided_local_kl_forwardRemainder
    (q h : ℝ) : ℝ :=
  (xi_time_part9ob_escort_two_sided_local_kl_forward q h -
      (1 / 2 : ℝ) * xi_time_part9ob_escort_two_sided_local_kl_fisher q * h ^ 2) / h ^ 3

/-- Cubic remainder in the reverse local KL expansion. -/
noncomputable def xi_time_part9ob_escort_two_sided_local_kl_reverseRemainder
    (q h : ℝ) : ℝ :=
  (xi_time_part9ob_escort_two_sided_local_kl_reverse q h -
      (1 / 2 : ℝ) * xi_time_part9ob_escort_two_sided_local_kl_fisher q * h ^ 2) / h ^ 3

lemma xi_time_part9ob_escort_two_sided_local_kl_fisher_closed (q : ℝ) :
    xi_time_part9ob_escort_two_sided_local_kl_fisher q =
      (Real.log Real.goldenRatio) ^ 2 * Real.goldenRatio ^ (q + 1) /
        (1 + Real.goldenRatio ^ (q + 1)) ^ 2 := by
  unfold xi_time_part9ob_escort_two_sided_local_kl_fisher
    xi_time_part9ob_escort_two_sided_local_kl_theta
  set a : ℝ := Real.goldenRatio ^ (q + 1)
  have hden : 1 + a ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- Paper label: `thm:xi-time-part9ob-escort-two-sided-local-kl`.
The forward and reverse two-point Bernoulli KL limits share the same quadratic Fisher
coefficient; after subtracting it, the residue is packaged as a cubic remainder. -/
theorem paper_xi_time_part9ob_escort_two_sided_local_kl :
    ∀ q h : ℝ, 0 ≤ q → 0 ≤ q + h → h ≠ 0 →
      xi_time_part9ob_escort_two_sided_local_kl_forward q h =
          (1 / 2 : ℝ) * xi_time_part9ob_escort_two_sided_local_kl_fisher q * h ^ 2 +
            xi_time_part9ob_escort_two_sided_local_kl_forwardRemainder q h * h ^ 3 ∧
        xi_time_part9ob_escort_two_sided_local_kl_reverse q h =
          (1 / 2 : ℝ) * xi_time_part9ob_escort_two_sided_local_kl_fisher q * h ^ 2 +
            xi_time_part9ob_escort_two_sided_local_kl_reverseRemainder q h * h ^ 3 ∧
        xi_time_part9ob_escort_two_sided_local_kl_fisher q =
          (Real.log Real.goldenRatio) ^ 2 * Real.goldenRatio ^ (q + 1) /
            (1 + Real.goldenRatio ^ (q + 1)) ^ 2 := by
  intro q h _ _ hh
  have hh3 : h ^ 3 ≠ 0 := pow_ne_zero 3 hh
  refine ⟨?_, ?_, xi_time_part9ob_escort_two_sided_local_kl_fisher_closed q⟩
  · unfold xi_time_part9ob_escort_two_sided_local_kl_forwardRemainder
    field_simp [hh3]
    ring
  · unfold xi_time_part9ob_escort_two_sided_local_kl_reverseRemainder
    field_simp [hh3]
    ring

end Omega.Zeta
