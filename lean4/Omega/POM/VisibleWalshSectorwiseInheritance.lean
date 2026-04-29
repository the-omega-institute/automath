import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.POM.FoldFactorChainDerivedInvariants
import Omega.POM.VisibleWalshCommutatorDefect

namespace Omega.POM

open scoped BigOperators

/-- The ambient Walsh layer vector obtained by summing the `k`-th layer with the given integer
coefficients. -/
def pom_visible_walsh_sectorwise_inheritance_layer_vector {m k : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℤ V] (χ : Finset (Fin m) → V)
    (coeff : Finset (Fin m) → ℤ) : V :=
  Finset.sum (Finset.powersetCard k (Finset.univ : Finset (Fin m))) fun I => coeff I • χ I

/-- The corresponding visible image of the `k`-th Walsh layer vector. -/
def pom_visible_walsh_sectorwise_inheritance_visible_layer_vector {m k : ℕ} {V W : Type*}
    [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W] (Ustar : V →ₗ[ℤ] W)
    (χ : Finset (Fin m) → V) (coeff : Finset (Fin m) → ℤ) : W :=
  Finset.sum (Finset.powersetCard k (Finset.univ : Finset (Fin m))) fun I =>
    coeff I • visibleWalshMode Ustar (χ I)

/-- Paper label: `cor:pom-visible-walsh-sectorwise-inheritance`. If the visible commutator defect
vanishes on the entire `k`-th Walsh layer, then every visible Walsh basis vector in that layer
inherits the expected eigenvalue. For a nonzero first-layer visible
mode, any compatible spectral-gap upper bound therefore collapses to the lower bound `2 / m`. -/
theorem paper_pom_visible_walsh_sectorwise_inheritance
    {m k : ℕ} {V W : Type*} [AddCommGroup V] [Module ℤ V] [AddCommGroup W] [Module ℤ W]
    (P E : Module.End ℤ V) (Ustar : V →ₗ[ℤ] W) (χ : Finset (Fin m) → V)
    (hvisible : ∀ I, I.card = k → Ustar (E (P (χ I))) = Ustar (P (χ I)))
    (hWalsh : ∀ I, I.card = k → P (χ I) = visibleWalshEigenvalue m I • χ I)
    (hdefect : ∀ I, I.card = k → visibleWalshCommutatorDefect P E Ustar (χ I) = 0)
    (i0 : Fin m)
    (hvisible1 : Ustar (E (P (χ ({i0} : Finset (Fin m))))) = Ustar (P (χ ({i0} : Finset (Fin m)))))
    (hWalsh1 :
      P (χ ({i0} : Finset (Fin m))) =
        visibleWalshEigenvalue m ({i0} : Finset (Fin m)) • χ ({i0} : Finset (Fin m)))
    (hdefect1 :
      visibleWalshCommutatorDefect P E Ustar (χ ({i0} : Finset (Fin m))) = 0)
    (gap : ℝ) (hgap_lower : foldFactorChainGapLower m ≤ gap)
    (hgap_upper :
      visibleWalshCompression P E Ustar (χ ({i0} : Finset (Fin m))) =
          visibleWalshEigenvalue m ({i0} : Finset (Fin m)) •
            visibleWalshMode Ustar (χ ({i0} : Finset (Fin m))) →
        visibleWalshMode Ustar (χ ({i0} : Finset (Fin m))) ≠ 0 →
          gap ≤ 1 - ((visibleWalshEigenvalue m ({i0} : Finset (Fin m)) : ℝ) / m))
    (hnonzero : visibleWalshMode Ustar (χ ({i0} : Finset (Fin m))) ≠ 0) :
    (∀ I, I.card = k →
      visibleWalshCompression P E Ustar (χ I) =
        visibleWalshEigenvalue m I • visibleWalshMode Ustar (χ I)) ∧
      gap = 2 / (m : ℝ) := by
  have hsector :
      ∀ I, I.card = k →
        visibleWalshCompression P E Ustar (χ I) =
          visibleWalshEigenvalue m I • visibleWalshMode Ustar (χ I) := by
    intro I hI
    exact ((paper_pom_visible_walsh_commutator_defect (m := m) I P E Ustar (χ I)
      (hvisible I hI) (hWalsh I hI)).2).mpr (hdefect I hI)
  have hfirst :
      visibleWalshCompression P E Ustar (χ ({i0} : Finset (Fin m))) =
        visibleWalshEigenvalue m ({i0} : Finset (Fin m)) •
          visibleWalshMode Ustar (χ ({i0} : Finset (Fin m))) := by
    exact ((paper_pom_visible_walsh_commutator_defect (m := m) ({i0} : Finset (Fin m)) P E Ustar
      (χ ({i0} : Finset (Fin m))) hvisible1 hWalsh1).2).mpr hdefect1
  have hm_pos_nat : 0 < m := lt_of_le_of_lt (Nat.zero_le i0.1) i0.2
  have hm : 1 ≤ m := Nat.succ_le_of_lt hm_pos_nat
  have hm_real : (0 : ℝ) < m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hupper : gap ≤ 2 / (m : ℝ) := by
    have hraw := hgap_upper hfirst hnonzero
    have hformula :
        1 - ((visibleWalshEigenvalue m ({i0} : Finset (Fin m)) : ℝ) / m) = 2 / (m : ℝ) := by
      simp [visibleWalshEigenvalue]
      field_simp [hm_real.ne']
      ring
    simpa [hformula] using hraw
  have hlower : 2 / (m : ℝ) ≤ gap := by
    simpa [foldFactorChainGapLower] using hgap_lower
  exact ⟨hsector, le_antisymm hupper hlower⟩

end Omega.POM
