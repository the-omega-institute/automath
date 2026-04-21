import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Omega.POM.VisibleWalshCommutatorDefect

namespace Omega.POM

open scoped BigOperators

/-- The visible Walsh family is exactly the image of the ambient Walsh family under `U⋆`. -/
def pom_visible_walsh_parseval_frame_visible_image
    {m : ℕ} {V W : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (Ustar : V →ₗ[ℤ] W) (χ : Finset (Fin m) → V) : Prop :=
  ∀ I, visibleWalshMode Ustar (χ I) = Ustar (χ I)

/-- Parseval identity for the visible Walsh family at a fixed test vector `f`. -/
def pom_visible_walsh_parseval_frame_parseval
    {m : ℕ} {W : Type*} [AddCommGroup W] [Module ℤ W]
    (energyW : W → ℤ) (coeff : W → Finset (Fin m) → ℤ) (f : W) : Prop :=
  energyW f = ∑ I : Finset (Fin m), (coeff f I) ^ 2

/-- Reconstruction of a fixed vector `f` from its visible Walsh coefficients. -/
def pom_visible_walsh_parseval_frame_reconstruction
    {m : ℕ} {V W : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (Ustar : V →ₗ[ℤ] W) (χ : Finset (Fin m) → V)
    (coeff : W → Finset (Fin m) → ℤ) (f : W) : Prop :=
  f = ∑ I : Finset (Fin m), coeff f I • visibleWalshMode Ustar (χ I)

/-- Paper label: `thm:pom-visible-walsh-parseval-frame`. If `U` embeds the visible space into the
ambient cube, `U⋆` is its left inverse, and the ambient Walsh basis satisfies Parseval and
reconstruction after pulling back the coefficients of `f`, then the visible Walsh images inherit the
same Parseval and reconstruction formulas. -/
theorem paper_pom_visible_walsh_parseval_frame
    {m : ℕ} {V W : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (U : W →ₗ[ℤ] V) (Ustar : V →ₗ[ℤ] W) (χ : Finset (Fin m) → V)
    (energyV : V → ℤ) (energyW : W → ℤ)
    (coeff : W → Finset (Fin m) → ℤ) (f : W)
    (hLeftInverse : Function.LeftInverse Ustar U)
    (hIsometry : energyW f = energyV (U f))
    (hAmbientParseval : energyV (U f) = ∑ I : Finset (Fin m), (coeff f I) ^ 2)
    (hAmbientReconstruction : U f = ∑ I : Finset (Fin m), coeff f I • χ I) :
    pom_visible_walsh_parseval_frame_visible_image Ustar χ ∧
      pom_visible_walsh_parseval_frame_parseval energyW coeff f ∧
      pom_visible_walsh_parseval_frame_reconstruction Ustar χ coeff f := by
  refine ⟨?_, ?_, ?_⟩
  · intro I
    rfl
  · exact hIsometry.trans hAmbientParseval
  · calc
      f = Ustar (U f) := by
            symm
            exact hLeftInverse f
      _ = Ustar (∑ I : Finset (Fin m), coeff f I • χ I) := by
            rw [hAmbientReconstruction]
      _ = ∑ I : Finset (Fin m), coeff f I • visibleWalshMode Ustar (χ I) := by
            simp [visibleWalshMode]

end Omega.POM
