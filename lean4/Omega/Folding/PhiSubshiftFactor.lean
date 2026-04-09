import Omega.Folding.PhiSlidingBlockCode
import Mathlib.Data.Set.Image

namespace Omega.Folding

variable {A B : Type*}

/-- Shift-invariant subset of bi-infinite sequences.
    prop:Phi_m-factor-on-subshift -/
def ShiftInvariant (S : Set (ℤ → A)) : Prop :=
  ∀ s ∈ S, shiftSeq s ∈ S

/-- The universal set is shift-invariant.
    prop:Phi_m-factor-on-subshift -/
theorem shiftInvariant_univ : ShiftInvariant (Set.univ : Set (ℤ → A)) :=
  fun _ _ => Set.mem_univ _

/-- The empty set is shift-invariant.
    prop:Phi_m-factor-on-subshift -/
theorem shiftInvariant_empty : ShiftInvariant (∅ : Set (ℤ → A)) :=
  fun _ h => absurd h (Set.notMem_empty _)

/-- Restriction of `slideBlockCode` to a shift-invariant subset preserves
    shift equivariance.
    prop:Phi_m-factor-on-subshift -/
theorem slideBlockCode_restriction_equivariant
    (m : ℕ) (f : (Fin m → A) → B) (S : Set (ℤ → A))
    (_hS : ShiftInvariant S) (s : ℤ → A) (_hs : s ∈ S) :
    slideBlockCode m f (shiftSeq s) = shiftSeq (slideBlockCode m f s) :=
  slideBlockCode_shift_equivariant m f s

/-- The image of a shift-invariant set under `slideBlockCode` is shift-invariant.
    prop:Phi_m-factor-on-subshift -/
theorem slideBlockCode_image_shiftInvariant
    (m : ℕ) (f : (Fin m → A) → B) (S : Set (ℤ → A))
    (hS : ShiftInvariant S) :
    ShiftInvariant (slideBlockCode m f '' S) := by
  intro t ht
  obtain ⟨s, hs, hst⟩ := ht
  refine ⟨shiftSeq s, hS s hs, ?_⟩
  rw [slideBlockCode_shift_equivariant, hst]

/-- Trivial surjectivity onto the image.
    prop:Phi_m-factor-on-subshift -/
theorem slideBlockCode_restrict_surjective
    (m : ℕ) (f : (Fin m → A) → B) (S : Set (ℤ → A)) :
    ∀ t ∈ slideBlockCode m f '' S, ∃ s ∈ S, slideBlockCode m f s = t := by
  intro _ ht
  exact ht

/-- Paper package: Φ_m as a subshift factor map.
    prop:Phi_m-factor-on-subshift -/
theorem paper_Phi_m_factor_on_subshift :
    ShiftInvariant (Set.univ : Set (ℤ → A)) ∧
    ShiftInvariant (∅ : Set (ℤ → A)) ∧
    (∀ (m : ℕ) (f : (Fin m → A) → B) (S : Set (ℤ → A)),
      ShiftInvariant S → ShiftInvariant (slideBlockCode m f '' S)) ∧
    (∀ (m : ℕ) (f : (Fin m → A) → B) (S : Set (ℤ → A)),
      ∀ t ∈ slideBlockCode m f '' S, ∃ s ∈ S, slideBlockCode m f s = t) :=
  ⟨shiftInvariant_univ,
   shiftInvariant_empty,
   slideBlockCode_image_shiftInvariant,
   slideBlockCode_restrict_surjective⟩

end Omega.Folding
