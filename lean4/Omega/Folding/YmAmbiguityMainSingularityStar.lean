import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic

namespace Omega.Folding

/-- The common modulus predicted by the Perron root. -/
noncomputable def ymAmbRadius (ρ : ℝ) : ℝ := ρ⁻¹

/-- The resolvent denominator attached to the Perron branch. -/
def ymAmbResolventDenominator (ρ : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  1 - (((ρ : ℂ) * z) ^ p)

/-- The `r`-th candidate singularity on the Perron circle. -/
noncomputable def ymAmbMainSingularityPoint (ρ : ℝ) (p : ℕ) (r : Fin p) : ℂ :=
  (ymAmbRadius ρ : ℂ) * Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p))

/-- The `p` equally spaced candidate singularities, with their residue labels attached. -/
noncomputable def ymAmbMainSingularityStar (ρ : ℝ) (p : ℕ) : Finset (ℂ × Fin p) :=
  Finset.univ.image fun r => (ymAmbMainSingularityPoint ρ p r, r)

private theorem ymAmbMainSingularityPoint_root
    (ρ : ℝ) (p : ℕ) (hρ : 0 < ρ) (hp : 0 < p) (r : Fin p) :
    ymAmbResolventDenominator ρ p (ymAmbMainSingularityPoint ρ p r) = 0 := by
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast (show ρ ≠ 0 from ne_of_gt hρ)
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hphase :
      Complex.exp ((p : ℂ) * ((r : ℂ) * ((2 * Real.pi * Complex.I) / p))) = 1 := by
    have hrewrite :
        (p : ℂ) * ((r : ℂ) * ((2 * Real.pi * Complex.I) / p)) =
          (r : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp [hpC]
    rw [hrewrite]
    simpa [mul_comm, mul_left_comm, mul_assoc] using Complex.exp_nat_mul_two_pi_mul_I (r : ℕ)
  unfold ymAmbResolventDenominator ymAmbMainSingularityPoint ymAmbRadius
  have hmul :
      (ρ : ℂ) * ((ρ⁻¹ : ℂ) * Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p))) =
        Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p)) := by
    calc
      (ρ : ℂ) * ((ρ⁻¹ : ℂ) * Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p))) =
          ((ρ : ℂ) * (ρ⁻¹ : ℂ)) * Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p)) := by
            ring
      _ = Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p)) := by
            field_simp [hρC]
  have hpow :
      ((ρ : ℂ) * ((ρ⁻¹ : ℂ) * Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p)))) ^ p =
        (Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p))) ^ p := by
    rw [hmul]
  calc
    ymAmbResolventDenominator ρ p (ymAmbMainSingularityPoint ρ p r)
        = 1 - (Complex.exp ((r : ℂ) * ((2 * Real.pi * Complex.I) / p))) ^ p := by
            simp [ymAmbResolventDenominator, ymAmbMainSingularityPoint, ymAmbRadius, hpow]
    _ = 1 - Complex.exp ((p : ℂ) * ((r : ℂ) * ((2 * Real.pi * Complex.I) / p))) := by
          rw [← Complex.exp_nat_mul]
    _ = 0 := by simp [hphase]

private theorem ymAmbMainSingularityStar_card (ρ : ℝ) (p : ℕ) :
    (ymAmbMainSingularityStar ρ p).card = p := by
  classical
  unfold ymAmbMainSingularityStar
  simpa using Finset.card_image_of_injective
    (s := (Finset.univ : Finset (Fin p)))
    (f := fun r => (ymAmbMainSingularityPoint ρ p r, r))
    (by
      intro a b hab
      simpa using congrArg Prod.snd hab)

set_option maxHeartbeats 400000 in
/-- For the periodic Perron branch, the resolvent denominator has radius `ρ⁻¹` and exactly `p`
candidate main singularities indexed by the period residues; each candidate lies on the
Perron circle and annuls the denominator.
    thm:Ym-amb-main-singularity-star -/
theorem paper_Ym_amb_main_singularity_star
    (ρ : ℝ) (p : ℕ) (hρ : 0 < ρ) (hp : 0 < p) :
    ymAmbRadius ρ = ρ⁻¹ ∧
      (ymAmbMainSingularityStar ρ p).card = p ∧
      ∀ r : Fin p, ymAmbResolventDenominator ρ p (ymAmbMainSingularityPoint ρ p r) = 0 := by
  refine ⟨rfl, ymAmbMainSingularityStar_card ρ p, ?_⟩
  intro r
  exact ymAmbMainSingularityPoint_root ρ p hρ hp r

end Omega.Folding
