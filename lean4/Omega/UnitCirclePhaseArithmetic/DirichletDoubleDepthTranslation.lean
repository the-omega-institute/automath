import Mathlib.Data.PNat.Notation
import Mathlib.Tactic

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The logarithmic depth attached to the Dirichlet radial coordinate `σ log λ`. -/
def dirichletSigmaDepth (lam σ : ℝ) : ℝ :=
  Real.log (σ * Real.log lam)

/-- The logarithmic depth attached to the translated Cayley height `|t|`. -/
def dirichletTimeDepth (t : ℝ) : ℝ :=
  Real.log |t|

/-- The difference of the two depth coordinates, constant along dilation rays. -/
def dirichletRayInvariant (lam σ t : ℝ) : ℝ :=
  dirichletSigmaDepth lam σ - dirichletTimeDepth t

/-- Paper label: `thm:dirichlet-double-depth-translation`. Dilation by an integer factor translates
both logarithmic depth coordinates by `log m`, so their difference is invariant. -/
theorem paper_dirichlet_double_depth_translation (m : ℕ+) {lam σ t : ℝ}
    (hlam : 1 < lam) (hσ : 0 < σ) (ht : t ≠ 0) :
    dirichletSigmaDepth lam ((m : ℝ) * σ) = dirichletSigmaDepth lam σ + Real.log m ∧
      dirichletTimeDepth ((m : ℝ) * t) = dirichletTimeDepth t + Real.log m ∧
      dirichletRayInvariant lam ((m : ℝ) * σ) ((m : ℝ) * t) = dirichletRayInvariant lam σ t := by
  have hm : 0 < (m : ℝ) := by
    exact_mod_cast m.pos
  have hloglam : 0 < Real.log lam := Real.log_pos hlam
  have hσlog_ne : σ * Real.log lam ≠ 0 := (mul_pos hσ hloglam).ne'
  have htabs_ne : |t| ≠ 0 := abs_ne_zero.mpr ht
  have hσ_translate :
      dirichletSigmaDepth lam ((m : ℝ) * σ) = dirichletSigmaDepth lam σ + Real.log m := by
    calc
      dirichletSigmaDepth lam ((m : ℝ) * σ)
          = Real.log ((m : ℝ) * (σ * Real.log lam)) := by
              simp [dirichletSigmaDepth, mul_assoc]
      _ = Real.log (m : ℝ) + Real.log (σ * Real.log lam) := by
            rw [Real.log_mul hm.ne' hσlog_ne]
      _ = dirichletSigmaDepth lam σ + Real.log m := by
            simp [dirichletSigmaDepth, add_comm]
  have ht_translate :
      dirichletTimeDepth ((m : ℝ) * t) = dirichletTimeDepth t + Real.log m := by
    calc
      dirichletTimeDepth ((m : ℝ) * t)
          = Real.log ((m : ℝ) * |t|) := by
              rw [dirichletTimeDepth, abs_mul, abs_of_pos hm]
      _ = Real.log (m : ℝ) + Real.log |t| := by
            rw [Real.log_mul hm.ne' htabs_ne]
      _ = dirichletTimeDepth t + Real.log m := by
            simp [dirichletTimeDepth, add_comm]
  refine ⟨hσ_translate, ht_translate, ?_⟩
  unfold dirichletRayInvariant
  rw [hσ_translate, ht_translate]
  ring

end

end Omega.UnitCirclePhaseArithmetic
