import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- Paper label: `prop:pom-max-fiber-hidden-bit-minentropy-spectrum`. -/
theorem paper_pom_max_fiber_hidden_bit_minentropy_spectrum (phi p : ℝ) (hphi_pos : 0 < phi)
    (hhalf_le_inv : 1 / 2 ≤ phi⁻¹) (hinv_le_one : phi⁻¹ ≤ 1)
    (hcomp : phi ^ (-2 : ℤ) = 1 - phi⁻¹)
    (hlog_half : -Real.log (1 / 2) / Real.log 2 = 1)
    (hlog_phi : -Real.log phi⁻¹ / Real.log 2 = Real.log phi / Real.log 2)
    (hp : p = 1 / 2 ∨ p = phi⁻¹ ∨ p = phi ^ (-2 : ℤ)) :
    let Hmin : ℝ → ℝ := fun q => -Real.log (max q (1 - q)) / Real.log 2;
    (max p (1 - p) = 1 / 2 ∨ max p (1 - p) = phi⁻¹) ∧
      (Hmin p = 1 ∨ Hmin p = Real.log phi / Real.log 2) := by
  have _hphi_ne : phi ≠ 0 := ne_of_gt hphi_pos
  have _hinv_upper : phi⁻¹ ≤ 1 := hinv_le_one
  rcases hp with hp | hp | hp
  · subst p
    have hmax : max (1 / 2 : ℝ) (1 - 1 / 2) = 1 / 2 := by norm_num
    constructor
    · exact Or.inl hmax
    · exact Or.inl (by
        dsimp
        rw [hmax]
        exact hlog_half)
  · subst p
    have hle : 1 - phi⁻¹ ≤ phi⁻¹ := by linarith
    have hmax : max phi⁻¹ (1 - phi⁻¹) = phi⁻¹ := max_eq_left hle
    constructor
    · exact Or.inr hmax
    · exact Or.inr (by
        dsimp
        rw [hmax]
        exact hlog_phi)
  · subst p
    have hle : 1 - phi⁻¹ ≤ phi⁻¹ := by linarith
    have hone_sub : 1 - (1 - phi⁻¹) = phi⁻¹ := by ring
    have hmax : max (phi ^ (-2 : ℤ)) (1 - phi ^ (-2 : ℤ)) = phi⁻¹ := by
      rw [hcomp, hone_sub]
      exact max_eq_right hle
    constructor
    · exact Or.inr hmax
    · exact Or.inr (by
        dsimp
        rw [hmax]
        exact hlog_phi)

end

end Omega.POM
