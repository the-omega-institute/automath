import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

open scoped BigOperators ComplexConjugate

noncomputable section

/-- Finite partial-fraction model of the appendix horizon Weyl function. -/
def app_horizon_weyl_herglotz_weyl (roots : Finset ℂ) (z : ℂ) : ℂ :=
  Finset.sum roots fun ρ => (ρ - z)⁻¹

/-- Pole-freeness of the logarithmic derivative on the upper half-plane means exactly that the
audited zero multiset has no root with positive imaginary part. -/
def app_horizon_weyl_herglotz_pole_free (roots : Finset ℂ) : Prop :=
  ∀ z ∈ roots, z.im ≤ 0

/-- Herglotz positivity for the finite partial-fraction model. -/
def app_horizon_weyl_herglotz_herglotz (roots : Finset ℂ) : Prop :=
  ∀ z, 0 < z.im → 0 ≤ (app_horizon_weyl_herglotz_weyl roots z).im

/-- Paper label: `thm:app-horizon-weyl-herglotz`.
For a finite real-entire model whose non-real zeros occur in conjugate pairs, the horizon Weyl
function `Σ (ρ - z)⁻¹` is Herglotz on the upper half-plane exactly when every zero is real. The
forward direction is the real-zero partial-fraction expansion, and the converse reduces pole
freeness to the conjugate-symmetry obstruction. -/
theorem paper_app_horizon_weyl_herglotz
    (roots : Finset ℂ)
    (hconj : ∀ z ∈ roots, conj z ∈ roots) :
    (∀ z ∈ roots, z.im = 0) ↔
      app_horizon_weyl_herglotz_pole_free roots ∧
        app_horizon_weyl_herglotz_herglotz roots := by
  constructor
  · intro hreal
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [hreal z hz]
    · intro z hzIm
      have hsum_nonneg :
          0 ≤ Finset.sum roots (fun ρ => ((ρ - z)⁻¹).im) := by
        refine Finset.sum_nonneg ?_
        intro ρ hρ
        have hρreal : ρ.im = 0 := hreal ρ hρ
        have him :
            ((ρ - z)⁻¹).im = z.im / Complex.normSq (ρ - z) := by
          rw [Complex.inv_im]
          simp [hρreal]
        rw [him]
        exact div_nonneg (le_of_lt hzIm) (Complex.normSq_nonneg _)
      simpa [app_horizon_weyl_herglotz_weyl] using hsum_nonneg
  · rintro ⟨hpole, _⟩ z hz
    by_contra hnotreal
    rcases lt_or_gt_of_ne hnotreal with himneg | himpos
    · have hconj_mem : conj z ∈ roots := hconj z hz
      have hconj_pos : 0 < (conj z).im := by
        simpa using neg_pos.mpr himneg
      have hconj_le : (conj z).im ≤ 0 := hpole (conj z) hconj_mem
      linarith
    · have hzle : z.im ≤ 0 := hpole z hz
      linarith

end

end Omega.UnitCirclePhaseArithmetic
