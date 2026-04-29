import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace Omega.RootUnitCharacterPressureTensor

theorem paper_gauge_pressure_quartic (θ : ℝ) :
    ∃ y : ℝ,
      IsGreatest
        {y : ℝ |
          0 < y ∧
            8 * y ^ 4 - 4 * y ^ 3 - (4 * Real.exp θ + 2) * y ^ 2 +
                (2 * Real.exp θ - (Real.exp θ) ^ 3) * y + Real.exp θ = 0}
        y := by
  let x : ℝ := Real.exp θ
  let p : ℝ → ℝ := fun y =>
    8 * y ^ 4 - 4 * y ^ 3 - (4 * x + 2) * y ^ 2 + (2 * x - x ^ 3) * y + x
  let q : Polynomial ℝ :=
    8 * Polynomial.X ^ 4 - 4 * Polynomial.X ^ 3 - Polynomial.C (4 * x + 2) * Polynomial.X ^ 2 +
      Polynomial.C (2 * x - x ^ 3) * Polynomial.X + Polynomial.C x
  have hx : 0 < x := by
    dsimp [x]
    exact Real.exp_pos θ
  have hp0 : p 0 = x := by
    simp [p]
  have hp34' : p (3 / 4 : ℝ) = -(24 * x ^ 3 - 8 * x + 9) / 32 := by
    dsimp [p]
    ring_nf
  have hp34 : p (3 / 4 : ℝ) < 0 := by
    have hnum : 0 < 24 * x ^ 3 - 8 * x + 9 := by
      have : 0 < 24 * (x - 1 / 3) ^ 2 * (x + 2 / 3) + 65 / 9 := by
        positivity
      nlinarith
    rw [hp34']
    nlinarith
  have hcont : Continuous p := by
    dsimp [p]
    continuity
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (p (3 / 4 : ℝ)) (p 0) := by
    rw [hp0]
    exact ⟨le_of_lt hp34, hx.le⟩
  have hyImage : (0 : ℝ) ∈ p '' Set.Icc (0 : ℝ) (3 / 4 : ℝ) :=
    intermediate_value_Icc' (show (0 : ℝ) ≤ 3 / 4 by norm_num) hcont.continuousOn hzero_mem
  rcases hyImage with ⟨y, hyIcc, hyroot⟩
  have hyne : y ≠ 0 := by
    intro hy0
    subst hy0
    rw [hp0] at hyroot
    linarith
  have hypos : 0 < y := lt_of_le_of_ne hyIcc.1 hyne.symm
  have hq_eval : ∀ z : ℝ, q.eval z = p z := by
    intro z
    simp [q, p]
  have hq_ne_zero : q ≠ 0 := by
    intro hq0
    have : q.eval 0 = 0 := by
      simp [hq0]
    rw [hq_eval, hp0] at this
    linarith
  have hsfinite : ({z : ℝ | 0 < z ∧ p z = 0} : Set ℝ).Finite := by
    refine (Polynomial.finite_setOf_isRoot hq_ne_zero).subset ?_
    intro z hz
    simpa [Polynomial.IsRoot, hq_eval z] using hz.2
  have hsnonempty : ({z : ℝ | 0 < z ∧ p z = 0} : Set ℝ).Nonempty := ⟨y, hypos, hyroot⟩
  rcases Set.exists_max_image {z : ℝ | 0 < z ∧ p z = 0} id hsfinite hsnonempty with
    ⟨zmax, hzmax, hzmax_bound⟩
  refine ⟨zmax, ?_⟩
  have hgreat : IsGreatest {z : ℝ | 0 < z ∧ p z = 0} zmax := by
    refine ⟨hzmax, ?_⟩
    intro z hz
    simpa using hzmax_bound z hz
  simpa [x, p] using hgreat

end Omega.RootUnitCharacterPressureTensor
