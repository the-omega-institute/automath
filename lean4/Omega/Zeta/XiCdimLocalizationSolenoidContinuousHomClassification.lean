import Mathlib.Tactic
import Omega.Zeta.LocalizedHomAutCompleteClassification

namespace Omega.Zeta

/-- The concrete compact-side model is the discrete localized cross-hom on the Pontryagin-dual
side with source and target reversed. -/
abbrev XiLocalizedSolenoidContinuousHomModel (S T : Finset ℕ) :=
  LocalizedCrossHom T S

/-- A nonzero discrete scalar gives an injective map, which is the algebraic input for the
surjectivity of the dual compact map. -/
def xiLocalizedDiscreteMapInjective {S T : Finset ℕ}
    (φ : XiLocalizedSolenoidContinuousHomModel S T) : Prop :=
  Function.Injective φ.1

/-- Paper-facing surrogate for the continuous-hom classification between localized solenoids:
the compact-side Hom set is modeled by the opposite-direction discrete Hom set, which is
classified by the image of `1`, and every nonzero scalar map on the discrete side is injective. -/
def XiCdimLocalizationSolenoidContinuousHomClassification (S T : Finset ℕ) : Prop :=
  (T ⊆ S →
      ∀ φ : XiLocalizedSolenoidContinuousHomModel S T, ∀ z : LocalizedIntegerGroup T,
        φ.1 z = z * localizedCrossHomScalar φ) ∧
    (¬ T ⊆ S →
      ∀ φ : XiLocalizedSolenoidContinuousHomModel S T, ∀ z : LocalizedIntegerGroup T, φ.1 z = 0) ∧
    (T ⊆ S →
      ∀ φ : XiLocalizedSolenoidContinuousHomModel S T,
        localizedCrossHomScalar φ ≠ 0 → xiLocalizedDiscreteMapInjective φ)

/-- Paper label: `thm:xi-cdim-localization-solenoid-continuous-hom-classification`. -/
theorem paper_xi_cdim_localization_solenoid_continuous_hom_classification
    (S T : Finset ℕ) : XiCdimLocalizationSolenoidContinuousHomClassification S T := by
  rcases paper_xi_time_part69d_localized_hom_aut_complete_classification T S with
    ⟨hClass, _, hScalar, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hTS φ z
    exact hClass.1 hTS φ z
  · intro hTS φ z
    exact hClass.2 hTS φ z
  · intro _hTS φ hφ x y hxy
    have hx : φ.1 x = x * localizedCrossHomScalar φ := hScalar φ x
    have hy : φ.1 y = y * localizedCrossHomScalar φ := hScalar φ y
    rw [hx, hy] at hxy
    have hmul : (x - y) * localizedCrossHomScalar φ = 0 := by
      rw [sub_mul, hxy, sub_self]
    rcases Int.mul_eq_zero.mp hmul with hzero | hq
    · exact sub_eq_zero.mp hzero
    · exact False.elim (hφ hq)

end Omega.Zeta
