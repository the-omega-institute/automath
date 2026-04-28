import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-blaschke-radial-action-geometric-mean-barrier`. -/
theorem paper_conclusion_blaschke_radial_action_geometric_mean_barrier {κ : ℕ}
    (a : Fin κ → ℝ) (rmax A δ logL : ℝ) (hκ : 0 < κ) (hpos : ∀ j, 0 < a j)
    (hle : ∀ j, a j ≤ rmax) (hrmax_pos : 0 < rmax)
    (hA : A = ∑ j, Real.log (1 / a j))
    (hdelta : δ * logL = Real.log (1 / rmax)) (hlogL : 0 < logL) :
    (κ : ℝ) * δ * logL ≤ A ∧ δ ≤ A / ((κ : ℝ) * logL) := by
  have hlog_le : ∀ j : Fin κ, Real.log (1 / rmax) ≤ Real.log (1 / a j) := by
    intro j
    exact Real.log_le_log (by positivity) (one_div_le_one_div_of_le (hpos j) (hle j))
  have hsum :
      (∑ _j : Fin κ, Real.log (1 / rmax)) ≤ ∑ j : Fin κ, Real.log (1 / a j) :=
    Finset.sum_le_sum fun j _ => hlog_le j
  have hmain : (κ : ℝ) * δ * logL ≤ A := by
    rw [hA]
    convert hsum using 1
    simp [hdelta, mul_assoc]
  refine ⟨hmain, ?_⟩
  have hκ_real : 0 < (κ : ℝ) := by exact_mod_cast hκ
  have hden : 0 < (κ : ℝ) * logL := mul_pos hκ_real hlogL
  rw [le_div_iff₀ hden]
  nlinarith

end Omega.Conclusion
