import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

/-- Concrete finite-shell model for the logscale pseudomartingale recursion. The fields record the
shell energies, the layer energies, the near-orthogonal error term at each step, and a global
budget controlling the geometric sum of the shellwise errors. -/
structure RSLogscaleOrthogonalRecursionData where
  L : ℕ
  shellEnergy : ℕ → ℝ
  layerEnergy : ℕ → ℝ
  crossError : ℕ → ℝ
  shellBound : ℕ → ℝ
  totalShellBound : ℝ
  nearOrthogonalBound : ∀ ⦃ℓ : ℕ⦄, ℓ < L → |crossError ℓ| ≤ shellBound ℓ
  energyStep :
    ∀ ⦃ℓ : ℕ⦄, ℓ < L →
      shellEnergy ℓ = shellEnergy (ℓ + 1) + layerEnergy ℓ + crossError ℓ
  geometricErrorSum : Finset.sum (Finset.range L) shellBound ≤ totalShellBound

namespace RSLogscaleOrthogonalRecursionData

/-- The off-diagonal shell interaction is controlled by the declared shellwise budget. -/
def nearOrthogonalDifference (D : RSLogscaleOrthogonalRecursionData) : Prop :=
  ∀ ⦃ℓ : ℕ⦄, ℓ < D.L → |D.crossError ℓ| ≤ D.shellBound ℓ

/-- The energy recursion holds up to the shellwise near-orthogonal error. -/
def energyRecurrence (D : RSLogscaleOrthogonalRecursionData) : Prop :=
  ∀ ⦃ℓ : ℕ⦄, ℓ < D.L →
    |D.shellEnergy ℓ - (D.shellEnergy (ℓ + 1) + D.layerEnergy ℓ)| ≤ D.shellBound ℓ

/-- Telescoping the shell recursion bounds the total discrepancy by the geometric error budget. -/
def chainTelescoping (D : RSLogscaleOrthogonalRecursionData) : Prop :=
  |D.shellEnergy 0 - (Finset.sum (Finset.range D.L) D.layerEnergy + D.shellEnergy D.L)| ≤
    D.totalShellBound

lemma nearOrthogonalDifference_holds (D : RSLogscaleOrthogonalRecursionData) :
    nearOrthogonalDifference D := by
  intro ℓ hℓ
  exact D.nearOrthogonalBound hℓ

lemma energyRecurrence_holds (D : RSLogscaleOrthogonalRecursionData) :
    energyRecurrence D := by
  intro ℓ hℓ
  have hstep := D.energyStep hℓ
  have hrewrite :
      D.shellEnergy ℓ - (D.shellEnergy (ℓ + 1) + D.layerEnergy ℓ) = D.crossError ℓ := by
    rw [hstep]
    ring
  rw [hrewrite]
  exact D.nearOrthogonalBound hℓ

lemma telescoping_to_range (D : RSLogscaleOrthogonalRecursionData) :
    ∀ n : ℕ,
      n ≤ D.L →
        |D.shellEnergy 0 - (Finset.sum (Finset.range n) D.layerEnergy + D.shellEnergy n)| ≤
          Finset.sum (Finset.range n) D.shellBound := by
  intro n hn
  induction' n with n ih
  · simp
  · have hnL : n < D.L := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have ih' := ih (Nat.le_of_succ_le hn)
    have hstep := D.energyStep hnL
    have hrewrite :
        D.shellEnergy 0 -
            (Finset.sum (Finset.range (n + 1)) D.layerEnergy + D.shellEnergy (n + 1)) =
          (D.shellEnergy 0 - (Finset.sum (Finset.range n) D.layerEnergy + D.shellEnergy n)) +
            D.crossError n := by
      rw [Finset.sum_range_succ, hstep]
      ring
    rw [hrewrite, Finset.sum_range_succ]
    exact le_trans (abs_add_le _ _) (add_le_add ih' (D.nearOrthogonalBound hnL))

lemma chainTelescoping_holds (D : RSLogscaleOrthogonalRecursionData) :
    chainTelescoping D := by
  refine le_trans (D.telescoping_to_range D.L le_rfl) D.geometricErrorSum

end RSLogscaleOrthogonalRecursionData

open RSLogscaleOrthogonalRecursionData

/-- Paper-facing finite-shell recursion package for the logscale decomposition. The near-orthogonal
difference is declared shellwise, the energy recurrence follows from the exact shell decomposition,
and the full chain telescopes with the geometric error budget.
    thm:cdim-rs-logscale-pseudomartingale-orthogonal-recursion -/
theorem paper_cdim_rs_logscale_pseudomartingale_orthogonal_recursion
    (D : RSLogscaleOrthogonalRecursionData) :
    D.nearOrthogonalDifference ∧ D.energyRecurrence ∧ D.chainTelescoping := by
  exact ⟨D.nearOrthogonalDifference_holds, D.energyRecurrence_holds, D.chainTelescoping_holds⟩

end Omega.CircleDimension
