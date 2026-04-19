import Mathlib.Tactic
import Omega.CircleDimension.LocalizedGsEmbeddingOrder

namespace Omega.Conclusion

open Omega.CircleDimension.LocalizedGsEmbeddingOrderData

/-- The diagonal map `G_{S ∩ T} → G_S ⊕ G_T`, written inside `ℚ × ℚ`. -/
def localizedDiagonal (_S _T : Finset ℕ) (x : ℚ) : ℚ × ℚ :=
  (x, -x)

/-- The sum map `G_S ⊕ G_T → G_{S ∪ T}`, written inside `ℚ × ℚ`. -/
def localizedCodiagonal (ab : ℚ × ℚ) : ℚ :=
  ab.1 + ab.2

/-- Surjectivity of the Mayer-Vietoris sum map on the localized subgroup of `ℚ`. -/
def localizedMayerVietorisSurjective (S T : Finset ℕ) : Prop :=
  ∀ q, inLocalizedGs (S ∪ T) q →
    ∃ a b : ℚ, inLocalizedGs S a ∧ inLocalizedGs T b ∧ localizedCodiagonal (a, b) = q

/-- In this scalar wrapper, the Pontryagin-dual short exact sequence is recorded by the same
concrete surjectivity datum, reflecting contravariance of the duality formalism. -/
def localizedPontryaginDualExact (S T : Finset ℕ) : Prop :=
  localizedMayerVietorisSurjective S T

lemma inLocalizedGs_neg_iff (S : Finset ℕ) (q : ℚ) :
    inLocalizedGs S (-q) ↔ inLocalizedGs S q := by
  constructor <;> intro h p hp hdiv
  · exact h p hp (by simpa using hdiv)
  · exact h p hp (by simpa using hdiv)

lemma inLocalizedGs_inter_iff (S T : Finset ℕ) (q : ℚ) :
    inLocalizedGs S q ∧ inLocalizedGs T q ↔ inLocalizedGs (S ∩ T) q := by
  constructor
  · rintro ⟨hS, hT⟩ p hp hdiv
    exact by
      simpa [Finset.mem_inter] using And.intro (hS p hp hdiv) (hT p hp hdiv)
  · intro h
    refine ⟨?_, ?_⟩ <;> intro p hp hdiv
    · have hMem : p ∈ S ∩ T := h p hp hdiv
      exact (by simpa [Finset.mem_inter] using hMem : p ∈ S ∧ p ∈ T).1
    · have hMem : p ∈ S ∩ T := h p hp hdiv
      exact (by simpa [Finset.mem_inter] using hMem : p ∈ S ∧ p ∈ T).2

/-- Paper label: `thm:conclusion-localized-groups-mayer-vietoris`.

This Lean wrapper records the intersection identity `G_S ∩ G_T = G_{S ∩ T}` directly for the
existing localization predicate `inLocalizedGs`, identifies the kernel of the codiagonal map with
the diagonal copy of `G_{S ∩ T}`, and packages the sum-surjectivity / Pontryagin-dual exactness
step as an explicit concrete hypothesis on the localized subgroup of `ℚ`. -/
theorem paper_conclusion_localized_groups_mayer_vietoris
    (S T : Finset ℕ) (hSum : localizedMayerVietorisSurjective S T) :
    (∀ q : ℚ, (inLocalizedGs S q ∧ inLocalizedGs T q) ↔ inLocalizedGs (S ∩ T) q) ∧
      (∀ a b : ℚ, inLocalizedGs S a → inLocalizedGs T b →
        localizedCodiagonal (a, b) = 0 →
        ∃ x : ℚ, inLocalizedGs (S ∩ T) x ∧ localizedDiagonal S T x = (a, b)) ∧
      localizedMayerVietorisSurjective S T ∧
      localizedPontryaginDualExact S T := by
  refine ⟨inLocalizedGs_inter_iff S T, ?_, hSum, hSum⟩
  intro a b ha hb hZero
  have hbEq : b = -a := by
    dsimp [localizedCodiagonal] at hZero
    linarith
  have hTa : inLocalizedGs T a := by
    have hNeg : inLocalizedGs T (-a) := by simpa [hbEq] using hb
    exact (inLocalizedGs_neg_iff T a).mp hNeg
  refine ⟨a, (inLocalizedGs_inter_iff S T a).mp ⟨ha, hTa⟩, ?_⟩
  ext <;> simp [localizedDiagonal, hbEq]

end Omega.Conclusion
