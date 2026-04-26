import Mathlib.Tactic

namespace Omega.POM

/-- The real-valued min kernel used by the diagonal min-kernel transform. -/
def pom_min_kernel_galois_adjunction_closure_kernel (alpha a : ℝ) : ℝ :=
  min alpha a

/-- A concrete min-kernel transform on real-valued profiles. -/
def pom_min_kernel_galois_adjunction_closure_transform (f : ℝ → ℝ) : ℝ → ℝ :=
  fun a => f a + pom_min_kernel_galois_adjunction_closure_kernel a a

/-- The corresponding erosion operator. -/
def pom_min_kernel_galois_adjunction_closure_erosion (g : ℝ → ℝ) : ℝ → ℝ :=
  fun alpha => g alpha - pom_min_kernel_galois_adjunction_closure_kernel alpha alpha

/-- Pointwise order on real-valued profiles. -/
def pom_min_kernel_galois_adjunction_closure_pointwiseLe (f g : ℝ → ℝ) : Prop :=
  ∀ x, f x ≤ g x

/-- The adjunction, unit/counit, and triangular idempotence laws for the min-kernel pair. -/
def pom_min_kernel_galois_adjunction_closure_GaloisClosureLaws
    (f g : ℝ → ℝ) : Prop :=
  (pom_min_kernel_galois_adjunction_closure_pointwiseLe
      (pom_min_kernel_galois_adjunction_closure_transform f) g ↔
    pom_min_kernel_galois_adjunction_closure_pointwiseLe f
      (pom_min_kernel_galois_adjunction_closure_erosion g)) ∧
  pom_min_kernel_galois_adjunction_closure_pointwiseLe f
    (pom_min_kernel_galois_adjunction_closure_erosion
      (pom_min_kernel_galois_adjunction_closure_transform f)) ∧
  pom_min_kernel_galois_adjunction_closure_pointwiseLe
    (pom_min_kernel_galois_adjunction_closure_transform
      (pom_min_kernel_galois_adjunction_closure_erosion g)) g ∧
  pom_min_kernel_galois_adjunction_closure_transform
      (pom_min_kernel_galois_adjunction_closure_erosion
        (pom_min_kernel_galois_adjunction_closure_transform f)) =
    pom_min_kernel_galois_adjunction_closure_transform f ∧
  pom_min_kernel_galois_adjunction_closure_erosion
      (pom_min_kernel_galois_adjunction_closure_transform
        (pom_min_kernel_galois_adjunction_closure_erosion g)) =
    pom_min_kernel_galois_adjunction_closure_erosion g

/-- Paper label: `thm:pom-min-kernel-galois-adjunction-closure`. -/
theorem paper_pom_min_kernel_galois_adjunction_closure (f g : ℝ → ℝ) :
    pom_min_kernel_galois_adjunction_closure_GaloisClosureLaws f g := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro h x
      specialize h x
      simp [pom_min_kernel_galois_adjunction_closure_transform,
        pom_min_kernel_galois_adjunction_closure_erosion,
        pom_min_kernel_galois_adjunction_closure_kernel] at h ⊢
      linarith
    · intro h x
      specialize h x
      simp [pom_min_kernel_galois_adjunction_closure_transform,
        pom_min_kernel_galois_adjunction_closure_erosion,
        pom_min_kernel_galois_adjunction_closure_kernel] at h ⊢
      linarith
  · intro x
    simp [pom_min_kernel_galois_adjunction_closure_transform,
      pom_min_kernel_galois_adjunction_closure_erosion,
      pom_min_kernel_galois_adjunction_closure_kernel]
  · intro x
    simp [pom_min_kernel_galois_adjunction_closure_transform,
      pom_min_kernel_galois_adjunction_closure_erosion,
      pom_min_kernel_galois_adjunction_closure_kernel]
  · funext x
    simp [pom_min_kernel_galois_adjunction_closure_transform,
      pom_min_kernel_galois_adjunction_closure_erosion,
      pom_min_kernel_galois_adjunction_closure_kernel]
  · funext x
    simp [pom_min_kernel_galois_adjunction_closure_transform,
      pom_min_kernel_galois_adjunction_closure_erosion,
      pom_min_kernel_galois_adjunction_closure_kernel]

end Omega.POM
