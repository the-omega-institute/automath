import Mathlib.Tactic

namespace Omega.Folding

variable {A B : Type*}

/-- Shift operator on bi-infinite sequences.
    prop:Phi_m-equivariant -/
def shiftSeq (s : ℤ → A) : ℤ → A := fun t => s (t + 1)

/-- Sliding block code of window width `m` from a local rule `f`.
    prop:Phi_m-equivariant -/
def slideBlockCode (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A) : ℤ → B :=
  fun t => f (fun i => s (t + i.val))

/-- Pointwise formula for the sliding block code.
    prop:Phi_m-equivariant -/
theorem slideBlockCode_apply (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A) (t : ℤ) :
    slideBlockCode m f s t = f (fun i => s (t + i.val)) := rfl

/-- Shift equivariance: sliding block codes commute with the shift operator.
    prop:Phi_m-equivariant -/
theorem slideBlockCode_shift_equivariant
    (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A) :
    slideBlockCode m f (shiftSeq s) = shiftSeq (slideBlockCode m f s) := by
  funext t
  unfold slideBlockCode shiftSeq
  congr 1
  funext i
  congr 1
  omega

/-- Pointwise shift application.
    prop:Phi_m-equivariant -/
theorem slideBlockCode_shift_apply
    (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A) (t : ℤ) :
    slideBlockCode m f (shiftSeq s) t = slideBlockCode m f s (t + 1) := by
  unfold slideBlockCode shiftSeq
  congr 1
  funext i
  congr 1
  omega

/-- Paper package: Φ_m sliding block code shift equivariance.
    prop:Phi_m-equivariant / prop:Phi_m-radius -/
theorem paper_phi_m_sliding_block_code :
    (∀ (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A) (t : ℤ),
      slideBlockCode m f s t = f (fun i => s (t + i.val))) ∧
    (∀ (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A),
      slideBlockCode m f (shiftSeq s) = shiftSeq (slideBlockCode m f s)) ∧
    (∀ (m : ℕ) (f : (Fin m → A) → B) (s : ℤ → A) (t : ℤ),
      slideBlockCode m f (shiftSeq s) t = slideBlockCode m f s (t + 1)) :=
  ⟨slideBlockCode_apply,
   slideBlockCode_shift_equivariant,
   slideBlockCode_shift_apply⟩

end Omega.Folding
