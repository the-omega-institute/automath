import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace Omega.POM

open Matrix

theorem paper_pom_golden_grammar_fixed_point_rho_aq {n : Type} [Fintype n] [DecidableEq n]
    (T0q T1q : Matrix n n ℝ) («λq» : ℝ) (u0 : n → ℝ) (hLambdaq : 0 < «λq»)
    (hfixed :
      u0 = «λq»⁻¹ • T0q.mulVec u0 + («λq» ^ (2 : ℕ))⁻¹ • T1q.mulVec (T0q.mulVec u0)) :
    ∃ u1 : n → ℝ,
      «λq» • u0 = T0q.mulVec u0 + T1q.mulVec u1 ∧ «λq» • u1 = T0q.mulVec u0 := by
  let u1 : n → ℝ := «λq»⁻¹ • T0q.mulVec u0
  refine ⟨u1, ?_, ?_⟩
  · dsimp [u1]
    rw [Matrix.mulVec_smul]
    ext i
    change «λq» * u0 i = (T0q.mulVec u0 + «λq»⁻¹ • T1q.mulVec (T0q.mulVec u0)) i
    simp only [Pi.add_apply, Pi.smul_apply]
    set a : ℝ := (T0q.mulVec u0) i
    set b : ℝ := (T1q.mulVec (T0q.mulVec u0)) i
    have hfixedi : u0 i = «λq»⁻¹ * a + («λq» ^ (2 : ℕ))⁻¹ * b := by
      simpa [a, b, Matrix.mulVec_mulVec] using congrFun hfixed i
    have hpow : «λq» * («λq» ^ (2 : ℕ))⁻¹ = «λq»⁻¹ := by
      field_simp [hLambdaq.ne']
    calc
      «λq» * u0 i = «λq» * («λq»⁻¹ * a + («λq» ^ (2 : ℕ))⁻¹ * b) := by rw [hfixedi]
      _ = «λq» * («λq»⁻¹ * a) + «λq» * ((«λq» ^ (2 : ℕ))⁻¹ * b) := by ring
      _ = a + («λq» * («λq» ^ (2 : ℕ))⁻¹) * b := by
            simp [hLambdaq.ne', mul_assoc]
      _ = a + «λq»⁻¹ * b := by rw [hpow]
      _ = (T0q.mulVec u0) i + «λq»⁻¹ * (T1q.mulVec (T0q.mulVec u0)) i := by
            simp [a, b]
  · ext i
    dsimp [u1]
    change «λq» * («λq»⁻¹ * (T0q.mulVec u0) i) = (T0q.mulVec u0) i
    field_simp [hLambdaq.ne']

end Omega.POM
