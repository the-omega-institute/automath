import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.POM

/-- The visible Walsh eigenvalue attached to a finite coordinate set on an `m`-cube. -/
def visibleWalshEigenvalue (m : ℕ) (I : Finset (Fin m)) : ℤ :=
  m - 2 * I.card

/-- The visible Walsh mode is the observed image of the ambient Walsh vector. -/
def visibleWalshMode {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (Ustar : V →ₗ[ℤ] W) (χ : V) : W :=
  Ustar χ

/-- The compressed visible action of `P` along the observable `E`. -/
def visibleWalshCompression {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (P E : Module.End ℤ V) (Ustar : V →ₗ[ℤ] W) (χ : V) : W :=
  Ustar (P (E χ))

/-- The commutator defect transported to the visible layer. -/
def visibleWalshCommutatorDefect {V W : Type*} [AddCommGroup V] [Module ℤ V]
    [AddCommGroup W] [Module ℤ W] (P E : Module.End ℤ V) (Ustar : V →ₗ[ℤ] W) (χ : V) : W :=
  Ustar (P (E χ) - E (P χ))

/-- Paper label: `thm:pom-visible-walsh-commutator-defect`. Rewriting the compressed observable as
`U⋆ P E`, inserting the commutator decomposition, and using the Walsh eigenrelation isolates the
visible defect term and yields the eigenfunction criterion. -/
theorem paper_pom_visible_walsh_commutator_defect
    {m : ℕ} (I : Finset (Fin m))
    {V W : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (P E : Module.End ℤ V) (Ustar : V →ₗ[ℤ] W) (χ : V)
    (hvisible : Ustar (E (P χ)) = Ustar (P χ))
    (hWalsh : P χ = visibleWalshEigenvalue m I • χ) :
    let g := visibleWalshMode Ustar χ
    let defect := visibleWalshCommutatorDefect P E Ustar χ
    (visibleWalshCompression P E Ustar χ - visibleWalshEigenvalue m I • g = defect) ∧
      ((visibleWalshCompression P E Ustar χ = visibleWalshEigenvalue m I • g) ↔ defect = 0) := by
  dsimp [visibleWalshMode, visibleWalshCompression, visibleWalshCommutatorDefect]
  set lam : ℤ := visibleWalshEigenvalue m I
  have hsplit : P (E χ) = E (P χ) + (P (E χ) - E (P χ)) := by
    abel
  have hPE :
      Ustar (P (E χ)) = Ustar (E (P χ)) + Ustar (P (E χ) - E (P χ)) := by
    rw [hsplit]
    simpa using Ustar.map_add (E (P χ)) (P (E χ) - E (P χ))
  have hformula :
      Ustar (P (E χ)) - lam • Ustar χ = Ustar (P (E χ) - E (P χ)) := by
    calc
      Ustar (P (E χ)) - lam • Ustar χ
          = (Ustar (E (P χ)) + Ustar (P (E χ) - E (P χ))) - lam • Ustar χ := by
              rw [hPE]
      _ = (Ustar (P χ) + Ustar (P (E χ) - E (P χ))) - lam • Ustar χ := by
            rw [hvisible]
      _ = (lam • Ustar χ + Ustar (P (E χ) - E (P χ))) - lam • Ustar χ := by
            rw [hWalsh, map_zsmul]
      _ = Ustar (P (E χ) - E (P χ)) := by
            abel
  refine ⟨hformula, ?_⟩
  constructor
  · intro hEig
    have hzero : Ustar (P (E χ)) - lam • Ustar χ = 0 := sub_eq_zero.mpr hEig
    simpa [hformula] using hzero
  · intro hDefect
    have hzero : Ustar (P (E χ)) - lam • Ustar χ = 0 := by
      simpa [hformula] using hDefect
    exact sub_eq_zero.mp hzero

end Omega.POM
