import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete padding model for the degeneration of the positive average density: a single positive
energy loop is diluted by arbitrarily long zero-energy padding blocks. The loop parameter is the
padding length, so the spliced loop with padding `n` has average density `energy / (n + padOffset)`.
-/
structure IharaGapDegeneracyData where
  energy : ℝ
  padOffset : ℕ
  deltaK : ℝ
  energy_pos : 0 < energy
  padOffset_pos : 0 < padOffset
  deltaK_nonneg : 0 ≤ deltaK
  deltaK_le_avg : ∀ n : ℕ, deltaK ≤ energy / ((n + padOffset : ℕ) : ℝ)

namespace IharaGapDegeneracyData

/-- The spliced loops are indexed by the zero-energy padding length. -/
abbrev loops (_D : IharaGapDegeneracyData) : Type := ℕ

/-- Average density of the spliced loop with padding length `p`. -/
def avgDensity (D : IharaGapDegeneracyData) (p : D.loops) : ℝ :=
  D.energy / (((p : ℕ) + D.padOffset : ℕ) : ℝ)

/-- The loop corresponding to padding length `n`. -/
abbrev splicedLoop (D : IharaGapDegeneracyData) (n : ℕ) : D.loops := n

lemma avgDensity_pos (D : IharaGapDegeneracyData) (p : D.loops) : 0 < D.avgDensity p := by
  unfold avgDensity
  have hnat : 0 < (p : ℕ) + D.padOffset := Nat.add_pos_right _ D.padOffset_pos
  have hden : 0 < ((((p : ℕ) + D.padOffset : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  exact div_pos D.energy_pos hden

lemma deltaK_le_avgDensity (D : IharaGapDegeneracyData) (p : D.loops) :
    D.deltaK ≤ D.avgDensity p := by
  simpa [avgDensity] using D.deltaK_le_avg (p : ℕ)

end IharaGapDegeneracyData

open IharaGapDegeneracyData

/-- Paper label: `prop:ihara-gap-degeneracy`.
Arbitrarily long zero-energy padding drives the positive average density to `0`. Consequently the
minimum positive density collapses to `0`, so any candidate gap `Δ_K` is forced to vanish. -/
theorem paper_ihara_gap_degeneracy (D : IharaGapDegeneracyData) :
    (∀ ε > 0, ∃ p : D.loops, 0 < D.avgDensity p ∧ D.avgDensity p < ε) ∧
      (D.deltaK = 0 ∨ ¬ ∃ p : D.loops, 0 < D.avgDensity p ∧ D.avgDensity p = D.deltaK) := by
  have hsmall : ∀ ε > 0, ∃ p : D.loops, 0 < D.avgDensity p ∧ D.avgDensity p < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, D.energy / ε < N := exists_nat_gt (D.energy / ε)
    refine ⟨D.splicedLoop N, D.avgDensity_pos N, ?_⟩
    unfold IharaGapDegeneracyData.avgDensity IharaGapDegeneracyData.splicedLoop
    have hden : 0 < ((N + D.padOffset : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_pos_right N D.padOffset_pos
    apply (div_lt_iff₀ hden).2
    have hlt' : D.energy < ε * (N : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hN
    have hpad : (N : ℝ) < ((N + D.padOffset : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_add_of_pos_right D.padOffset_pos
    have hmul : ε * (N : ℝ) < ε * (((N + D.padOffset : ℕ) : ℝ)) := by
      exact mul_lt_mul_of_pos_left hpad hε
    nlinarith
  have hdelta_zero : D.deltaK = 0 := by
    have hnotpos : ¬ 0 < D.deltaK := by
      intro hδ
      rcases hsmall D.deltaK hδ with ⟨p, hpPos, hpLt⟩
      exact not_lt_of_ge (D.deltaK_le_avgDensity p) hpLt
    linarith [D.deltaK_nonneg]
  refine ⟨hsmall, ?_⟩
  exact Or.inl hdelta_zero

end
end Omega.SyncKernelWeighted
