import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Omega.Folding.FoldResonanceLadderFibonacciDirectionalLimit

open Filter
open scoped Topology goldenRatio

namespace Omega.Folding

noncomputable section

/-- Paper label: `cor:fold-resonance-ladder-fib-luc-limits`.
Specializing the Fibonacci directional-limit package at the Fibonacci seeds `(0, 1)` and the
Lucas seeds `(2, 1)` gives the explicit Binet coefficients and the corresponding directional
limits. The paired cosine factors collapse to the displayed squares by evenness of cosine. -/
theorem paper_fold_resonance_ladder_fib_luc_limits :
    fold_resonance_ladder_fibonacci_directional_limit_alpha 0 1 = 1 / Real.sqrt 5 ∧
      fold_resonance_ladder_fibonacci_directional_limit_beta 0 1 = -(1 / Real.sqrt 5) ∧
      fold_resonance_ladder_fibonacci_directional_limit_alpha 2 1 = 1 ∧
      fold_resonance_ladder_fibonacci_directional_limit_beta 2 1 = 1 ∧
      (∀ k : ℕ,
        Tendsto
          (fun n : ℕ =>
            fold_resonance_ladder_fibonacci_directional_limit_seq 0 1 n /
              Real.goldenRatio ^ (n + k))
          atTop
          (𝓝 ((1 / Real.sqrt 5) / Real.goldenRatio ^ k))) ∧
      (∀ k : ℕ,
        Tendsto
          (fun n : ℕ =>
            fold_resonance_ladder_fibonacci_directional_limit_seq 0 1 (n + k) /
              Real.goldenRatio ^ n)
          atTop
          (𝓝 ((1 / Real.sqrt 5) * Real.goldenRatio ^ k))) ∧
      (∀ k : ℕ,
        Tendsto
          (fun n : ℕ =>
            fold_resonance_ladder_fibonacci_directional_limit_seq 2 1 n /
              Real.goldenRatio ^ (n + k))
          atTop
          (𝓝 (1 / Real.goldenRatio ^ k))) ∧
      (∀ k : ℕ,
        Tendsto
          (fun n : ℕ =>
            fold_resonance_ladder_fibonacci_directional_limit_seq 2 1 (n + k) /
              Real.goldenRatio ^ n)
          atTop
          (𝓝 (Real.goldenRatio ^ k))) ∧
      (∀ k : ℕ,
        |Real.cos (Real.pi * (fold_resonance_ladder_fibonacci_directional_limit_alpha 0 1) /
            Real.goldenRatio ^ k)| *
            |Real.cos (Real.pi * (fold_resonance_ladder_fibonacci_directional_limit_beta 0 1) /
              Real.goldenRatio ^ k)| =
          |Real.cos (Real.pi * (1 / Real.sqrt 5) / Real.goldenRatio ^ k)| ^ 2) ∧
      (∀ k : ℕ,
        |Real.cos (Real.pi * (fold_resonance_ladder_fibonacci_directional_limit_alpha 2 1) /
            Real.goldenRatio ^ k)| *
            |Real.cos (Real.pi * (fold_resonance_ladder_fibonacci_directional_limit_beta 2 1) /
              Real.goldenRatio ^ k)| =
          |Real.cos (Real.pi / Real.goldenRatio ^ k)| ^ 2) := by
  rcases paper_fold_resonance_ladder_fibonacci_directional_limit 0 1 with
    ⟨_, _, _, hFibTail, hFibHead⟩
  rcases paper_fold_resonance_ladder_fibonacci_directional_limit 2 1 with
    ⟨_, _, _, hLucTail, hLucHead⟩
  have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  have hαFib : fold_resonance_ladder_fibonacci_directional_limit_alpha 0 1 = 1 / Real.sqrt 5 := by
    simp [fold_resonance_ladder_fibonacci_directional_limit_alpha]
  have hβFib :
      fold_resonance_ladder_fibonacci_directional_limit_beta 0 1 = -(1 / Real.sqrt 5) := by
    unfold fold_resonance_ladder_fibonacci_directional_limit_beta
    field_simp [hsqrt5_ne]
    ring_nf
  have hαLuc : fold_resonance_ladder_fibonacci_directional_limit_alpha 2 1 = 1 := by
    have hnum : (1 : ℝ) - (2 : ℝ) * Real.goldenConj = Real.sqrt 5 := by
      nlinarith [Real.goldenRatio_add_goldenConj, Real.goldenRatio_sub_goldenConj]
    unfold fold_resonance_ladder_fibonacci_directional_limit_alpha
    simpa [hsqrt5_ne] using congrArg (fun x : ℝ => x / Real.sqrt 5) hnum
  have hβLuc : fold_resonance_ladder_fibonacci_directional_limit_beta 2 1 = 1 := by
    have hnum : (2 : ℝ) * Real.goldenRatio - (1 : ℝ) = Real.sqrt 5 := by
      nlinarith [Real.goldenRatio_add_goldenConj, Real.goldenRatio_sub_goldenConj]
    unfold fold_resonance_ladder_fibonacci_directional_limit_beta
    simpa [hsqrt5_ne] using congrArg (fun x : ℝ => x / Real.sqrt 5) hnum
  refine ⟨hαFib, hβFib, hαLuc, hβLuc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    simpa [hαFib] using hFibTail k
  · intro k
    simpa [hαFib] using hFibHead k
  · intro k
    simpa [hαLuc] using hLucTail k
  · intro k
    simpa [hαLuc] using hLucHead k
  · intro k
    rw [hαFib, hβFib]
    have hneg :
        |Real.cos (Real.pi * (-(1 / Real.sqrt 5)) / Real.goldenRatio ^ k)| =
          |Real.cos (Real.pi * (1 / Real.sqrt 5) / Real.goldenRatio ^ k)| := by
      rw [show Real.pi * (-(1 / Real.sqrt 5)) / Real.goldenRatio ^ k =
          -(Real.pi * (1 / Real.sqrt 5) / Real.goldenRatio ^ k) by ring, Real.cos_neg]
    rw [hneg]
    ring
  · intro k
    rw [hαLuc, hβLuc]
    ring

end

end Omega.Folding
