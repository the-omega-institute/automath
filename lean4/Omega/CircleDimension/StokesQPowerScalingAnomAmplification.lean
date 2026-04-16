import Mathlib.Tactic
import Omega.CircleDimension.StokesExactSequenceDictionary
import Omega.Core.AnomGapAmplification

namespace Omega.CircleDimension

open Omega.CircleDimension.StokesHomologyExactSplitting
open Omega.POM
open scoped BigOperators

/-- Coordinate `q`-power pullback on the split Stokes model: the bulk factor is unchanged and the
boundary factor is multiplied by the degree `q`. -/
def stokesQPowerPullback (u v q : ℕ) :
    ((Fin u → ℤ) × (Fin v → ℤ)) → ((Fin u → ℤ) × (Fin v → ℤ)) :=
  fun p => (p.1, q • p.2)

/-- On the explicit relative-basis model, a degree-`|I|` basis class scales by `q^|I|`. -/
def stokesRelativeBasisWeight {v : ℕ} (q : ℕ) (I : Finset (Fin v)) : ℕ :=
  q ^ I.card

/-- Character-pair anomaly readout on the boundary `H¹` factor. -/
def stokesBoundaryAnomaly {v : ℕ} (y : Fin v → ℤ) : ℝ :=
  ∑ i, (y i : ℝ)

lemma stokesBoundaryAnomaly_nsmul {v q : ℕ} (y : Fin v → ℤ) :
    stokesBoundaryAnomaly (q • y) = anomAmp (stokesBoundaryAnomaly y) q := by
  unfold stokesBoundaryAnomaly anomAmp
  simp [Finset.mul_sum, mul_comm]

/-- Paper-facing wrapper for the split Stokes exact-sequence model under the coordinatewise
`q`-power pullback: the boundary factor acquires degree `q`, the corresponding relative-basis
weight is `q^|I|`, and the boundary anomaly readout matches the standard anomaly-amplification
law on the character-pair model.
    prop:cdim-stokes-qpower-scaling-anom-amplification -/
theorem paper_cdim_stokes_qpower_scaling_anom_amplification (u v q : ℕ) :
    Function.Injective (stokesBoundaryInclusion u v) ∧
      Function.Surjective (stokesProjection u v) ∧
      Set.range (stokesBoundaryInclusion u v) = {p | stokesProjection u v p = 0} ∧
      (∀ p,
        stokesQPowerPullback u v q p =
          stokesSection u v (stokesProjection u v p) +
            stokesBoundaryInclusion u v (q • p.2)) ∧
      (∀ I : Finset (Fin v), stokesRelativeBasisWeight q I = q ^ I.card) ∧
      (∀ y : Fin v → ℤ,
        stokesBoundaryAnomaly ((stokesQPowerPullback u v q (stokesBoundaryInclusion u v y)).2) =
          anomAmp (stokesBoundaryAnomaly y) q) := by
  rcases paper_cdim_stokes_exact_sequence_dictionary u v with ⟨hInj, hSurj, hRange, _⟩
  refine ⟨hInj, hSurj, hRange, ?_, ?_, ?_⟩
  · intro p
    rcases p with ⟨x, y⟩
    ext i <;> simp [stokesQPowerPullback, stokesProjection, stokesSection, stokesBoundaryInclusion]
  · intro I
    rfl
  · intro y
    simpa [stokesQPowerPullback, stokesBoundaryInclusion, nsmul_eq_mul] using
      stokesBoundaryAnomaly_nsmul (q := q) y

end Omega.CircleDimension
