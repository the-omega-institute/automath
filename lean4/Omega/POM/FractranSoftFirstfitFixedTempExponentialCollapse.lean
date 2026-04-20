import Mathlib

namespace Omega.POM

open scoped BigOperators

/-- Weight of the hard first-fit copy after duplicating each instruction in the paired FRACTRAN
program. -/
def pairedFirstFitWeight (u : ℚ) (i : ℕ) : ℚ :=
  u ^ (2 * i + 1)

/-- Weight of the duplicated backup copy of the same hard rule. -/
def pairedBackupWeight (u : ℚ) (i : ℕ) : ℚ :=
  u ^ (2 * i + 2)

/-- Conditional probability that soft first-fit still selects the earlier copy of the duplicated
hard rule. -/
def pairedFirstFitMatchProb (u : ℚ) (i : ℕ) : ℚ :=
  pairedFirstFitWeight u i /
    (pairedFirstFitWeight u i + pairedBackupWeight u i)

/-- Product of the conditional match probabilities over the first `T` steps. -/
def pairedFirstFitTrajectoryProb (u : ℚ) (T : ℕ) : ℚ :=
  (Finset.range T).prod fun t => pairedFirstFitMatchProb u t

lemma pairedFirstFitMatchProb_eq (hu : 0 < u) (i : ℕ) :
    pairedFirstFitMatchProb u i = 1 / (1 + u) := by
  unfold pairedFirstFitMatchProb pairedFirstFitWeight pairedBackupWeight
  have hu0 : u ≠ 0 := ne_of_gt hu
  have h1u : 1 + u ≠ 0 := by linarith
  have hpow : u ^ (2 * i + 1) ≠ 0 := pow_ne_zero _ hu0
  have hsplit : u ^ (2 * i + 2) = u ^ (2 * i + 1) * u := by
    rw [show 2 * i + 2 = (2 * i + 1) + 1 by omega, pow_succ]
  rw [hsplit]
  calc
    u ^ (2 * i + 1) / (u ^ (2 * i + 1) + u ^ (2 * i + 1) * u)
        = u ^ (2 * i + 1) / (u ^ (2 * i + 1) * (1 + u)) := by ring
    _ = 1 / (1 + u) := by
        field_simp [hpow, h1u]

lemma pairedFirstFitTrajectoryProb_eq (hu : 0 < u) (T : ℕ) :
    pairedFirstFitTrajectoryProb u T = (1 / (1 + u)) ^ T := by
  induction T with
  | zero =>
      simp [pairedFirstFitTrajectoryProb]
  | succ T ih =>
      have ih' : (Finset.range T).prod (fun t => pairedFirstFitMatchProb u t) = (1 / (1 + u)) ^ T := by
        simpa [pairedFirstFitTrajectoryProb] using ih
      simp [pairedFirstFitTrajectoryProb, Finset.prod_range_succ, pow_succ]
      rw [ih', pairedFirstFitMatchProb_eq hu T]
      simp [div_eq_mul_inv]

/-- In the paired FRACTRAN program obtained by duplicating each hard rule, the conditional
probability of matching the hard first-fit branch is exactly `1 / (1 + u)` at every feasible
step. Consequently the probability of matching the hard trajectory for `T` consecutive steps
collapses to the exponential bound `(1 / (1 + u))^T`.
    thm:pom-fractran-soft-firstfit-fixed-temp-exponential-collapse -/
theorem paper_pom_fractran_soft_firstfit_fixed_temp_exponential_collapse :
    ∀ ⦃u : ℚ⦄, 0 < u →
      (∀ i : ℕ, pairedFirstFitMatchProb u i = 1 / (1 + u)) ∧
        ∀ T : ℕ,
          pairedFirstFitTrajectoryProb u T = (1 / (1 + u)) ^ T ∧
            pairedFirstFitTrajectoryProb u T ≤ (1 / (1 + u)) ^ T := by
  intro u hu
  refine ⟨pairedFirstFitMatchProb_eq hu, ?_⟩
  intro T
  constructor
  · exact pairedFirstFitTrajectoryProb_eq hu T
  · rw [pairedFirstFitTrajectoryProb_eq hu T]

end Omega.POM
