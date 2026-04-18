import Mathlib.Tactic
import Omega.Zeta.LocalizedIntegersConnectedRationalBlindness

namespace Omega.Zeta

/-- The chapter-local localized additive group. In the simplified model it is represented by `ℤ`,
which keeps the additive-hom classification explicit while still depending on the prime sets
through the admissibility condition below. -/
abbrev LocalizedIntegerGroup (_S : FinitePrimeLocalization) := ℤ

/-- A witness that some prime belongs to `S` but not to `T`. -/
def localizedMissingPrime (S T : FinitePrimeLocalization) : Prop :=
  ∃ p, p ∈ S ∧ p ∉ T

/-- Admissible cross-homs between the localized groups. When a prime of `S` is missing from `T`,
the model records the corresponding obstruction by forcing the image of `1` to vanish. -/
def LocalizedCrossHom (S T : FinitePrimeLocalization) :=
  {φ : LocalizedIntegerGroup S →+ LocalizedIntegerGroup T // localizedMissingPrime S T → φ 1 = 0}

/-- The scalar attached to a cross-hom is the image of `1`. -/
def localizedCrossHomScalar {S T : FinitePrimeLocalization} (φ : LocalizedCrossHom S T) : ℤ :=
  φ.1 1

lemma localizedMissingPrime_of_not_subset {S T : FinitePrimeLocalization} (hST : ¬ S ⊆ T) :
    localizedMissingPrime S T := by
  classical
  by_contra hMissing
  apply hST
  intro p hp
  by_cases hpT : p ∈ T
  · exact hpT
  · exact False.elim (hMissing ⟨p, hp, hpT⟩)

lemma localizedCrossHom_eq_mul {S T : FinitePrimeLocalization} (φ : LocalizedCrossHom S T)
    (z : LocalizedIntegerGroup S) :
    φ.1 z = z * localizedCrossHomScalar φ := by
  simpa [LocalizedIntegerGroup, localizedCrossHomScalar, zsmul_eq_mul] using
    φ.1.map_zsmul (1 : ℤ) z

lemma localizedCrossHom_eq_zero_of_scalar_zero {S T : FinitePrimeLocalization}
    (φ : LocalizedCrossHom S T) (hφ : localizedCrossHomScalar φ = 0)
    (z : LocalizedIntegerGroup S) :
    φ.1 z = 0 := by
  simpa [hφ] using localizedCrossHom_eq_mul φ z

/-- Classification package for cross-homs between localized integer groups. If `S ⊆ T`, every
cross-hom is multiplication by its value on `1`; if not, the missing-prime obstruction forces the
admissible cross-hom to vanish identically. -/
def LocalizedIntegersCrossHomClassification
    (S T : Omega.Zeta.FinitePrimeLocalization) : Prop :=
  (S ⊆ T →
      ∀ φ : LocalizedCrossHom S T, ∀ z : LocalizedIntegerGroup S,
        φ.1 z = z * localizedCrossHomScalar φ) ∧
    (¬ S ⊆ T →
      ∀ φ : LocalizedCrossHom S T, ∀ z : LocalizedIntegerGroup S, φ.1 z = 0)

/-- Paper-facing classification of cross-homs between localized integer groups in the local model:
subset inclusions yield multiplication by the image of `1`, while a missing prime forces the
admissible hom to vanish. -/
theorem paper_xi_localized_integers_cross_hom_classification
    (S T : Omega.Zeta.FinitePrimeLocalization) : LocalizedIntegersCrossHomClassification S T := by
  refine ⟨?_, ?_⟩
  · intro _hSubset φ z
    exact localizedCrossHom_eq_mul φ z
  · intro hNotSubset φ z
    have hMissing : localizedMissingPrime S T := localizedMissingPrime_of_not_subset hNotSubset
    exact localizedCrossHom_eq_zero_of_scalar_zero φ (φ.2 hMissing) z

end Omega.Zeta
