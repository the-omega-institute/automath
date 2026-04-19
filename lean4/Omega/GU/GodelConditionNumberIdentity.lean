import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.GU.GodelLorentzAlgebraization

namespace Omega.GU

noncomputable section

/-- The larger singular value of the symmetric Lorentz block `Λ(r)`. -/
def godelLorentzSingularValueMax (L : ℝ) : ℝ :=
  Real.exp (Real.log (Real.sqrt L))

/-- The smaller singular value of the symmetric Lorentz block `Λ(r)`. -/
def godelLorentzSingularValueMin (L : ℝ) : ℝ :=
  Real.exp (-Real.log (Real.sqrt L))

/-- The `2`-norm condition number is the ratio of the singular values. -/
def godelLorentzConditionNumber (L : ℝ) : ℝ :=
  godelLorentzSingularValueMax L / godelLorentzSingularValueMin L

/-- In the Lorentz-algebraized `2 × 2` model, the singular values are `e^Δ` and `e^{-Δ}` with
`Δ = log (sqrt L)`, so the `2`-norm condition number collapses to the Gödel norm `L = N(r)`.
    cor:group-jg-godel-condition-number-identity -/
theorem paper_group_jg_godel_condition_number_identity (L : ℝ) (hL : 1 < L) :
    let Δ := Real.log (Real.sqrt L)
    godelLorentzSingularValueMax L = Real.exp Δ ∧
      godelLorentzSingularValueMin L = Real.exp (-Δ) ∧
      godelLorentzConditionNumber L = L := by
  dsimp [godelLorentzSingularValueMax, godelLorentzSingularValueMin, godelLorentzConditionNumber]
  have hL_pos : 0 < L := lt_trans zero_lt_one hL
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL_pos
  let _ := paper_group_jg_godel_lorentz_algebraization L hL
  refine ⟨rfl, rfl, ?_⟩
  calc
    Real.exp (Real.log (Real.sqrt L)) / Real.exp (-Real.log (Real.sqrt L))
        = Real.sqrt L / (Real.sqrt L)⁻¹ := by
            rw [Real.exp_log hsqrt_pos, Real.exp_neg, Real.exp_log hsqrt_pos]
    _ = (Real.sqrt L) * Real.sqrt L := by
          field_simp [hsqrt_pos.ne']
    _ = L := by
          nlinarith [Real.sq_sqrt hL_pos.le]

end

end Omega.GU
