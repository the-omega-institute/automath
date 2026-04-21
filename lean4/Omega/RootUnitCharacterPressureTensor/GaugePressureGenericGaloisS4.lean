import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic
import Omega.Folding.GaugePressureResolventDiscIdentity

namespace Omega.RootUnitCharacterPressureTensor

/-- The specialization `u = 2` of the cubic resolvent, reduced modulo `11`. -/
def gaugePressureResolventAtTwoMod11 (z : ZMod 11) : ZMod 11 :=
  z ^ 3 + 5 * z ^ 2 - 12 * z - 100

/-- The `u = 2` quartic discriminant, recorded as the signed integer `-2^4 * 6343`. -/
def gaugePressureQuarticDiscriminantAtTwo : ℤ :=
  -((2 : ℤ) ^ 4 * 6343)

/-- Root-free mod-`11` witness for the specialized cubic resolvent. For a cubic polynomial this is
the finite-field irreducibility certificate used in the `u = 2` specialization argument. -/
def gaugePressureResolventAtTwoRootFreeMod11 : Prop :=
  ∀ z : ZMod 11, gaugePressureResolventAtTwoMod11 z ≠ 0

private theorem gaugePressureResolventAtTwoRootFreeMod11_true :
    gaugePressureResolventAtTwoRootFreeMod11 := by
  intro z
  fin_cases z <;> decide

private theorem gaugePressureQuarticDiscriminantAtTwo_not_square :
    ¬ IsSquare gaugePressureQuarticDiscriminantAtTwo := by
  intro hsquare
  rcases hsquare with ⟨n, hn⟩
  have hnonneg : 0 ≤ gaugePressureQuarticDiscriminantAtTwo := by
    simpa [pow_two, hn] using sq_nonneg n
  norm_num [gaugePressureQuarticDiscriminantAtTwo] at hnonneg

/-- Paper label: `thm:gauge-pressure-generic-galois-s4`. The concrete arithmetic certificate
packages the `u = 2` specialization of the quartic and its cubic resolvent, the root-free
mod-`11` witness for the resolvent, the explicit nonsquare discriminant value, and the cardinality
of `S₄ = Perm(Fin 4)`. -/
theorem paper_gauge_pressure_generic_galois_s4 :
    (∀ μ : ℚ, Omega.Folding.gaugePressureQuartic μ 2 = μ ^ 4 - μ ^ 3 - 5 * μ ^ 2 - 4 * μ + 4) ∧
      (∀ z : ℚ,
        Omega.Folding.gaugePressureResolvent z 2 = z ^ 3 + 5 * z ^ 2 - 12 * z - 100) ∧
      gaugePressureResolventAtTwoRootFreeMod11 ∧
      Omega.Folding.gaugeAnomalyQuarticDiscriminant 2 = -((2 : ℚ) ^ 4 * 6343) ∧
      ¬ IsSquare gaugePressureQuarticDiscriminantAtTwo ∧
      Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  refine ⟨?_, ?_, gaugePressureResolventAtTwoRootFreeMod11_true, ?_,
    gaugePressureQuarticDiscriminantAtTwo_not_square, ?_⟩
  · intro μ
    dsimp [Omega.Folding.gaugePressureQuartic]
    ring
  · intro z
    dsimp [Omega.Folding.gaugePressureResolvent]
    ring
  · norm_num [Omega.Folding.gaugeAnomalyQuarticDiscriminant]
  · decide

end Omega.RootUnitCharacterPressureTensor
