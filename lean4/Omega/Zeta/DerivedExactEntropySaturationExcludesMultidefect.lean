import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import Omega.Zeta.XiEntropyGapExponentialSuppressionNonzeroFingerprint

namespace Omega.Zeta

/-- The Hankel matrix built from the comoving Fourier modes. -/
noncomputable def derived_exact_entropy_saturation_excludes_multidefect_hankel (κ : Nat)
    (mass δ phase : Fin κ → ℝ) : Matrix (Fin κ) (Fin κ) ℝ :=
  fun i j => xiComovingFourier mass δ phase (i.1 + j.1)

/-- Paper label: `cor:derived-exact-entropy-saturation-excludes-multidefect`. Exact entropy-gap
saturation forces every nonzero Fourier mode to vanish, so the associated Hankel matrix has only
its `(0,0)` entry possibly nonzero and therefore rank at most one. -/
theorem paper_derived_exact_entropy_saturation_excludes_multidefect {κ : Nat}
    (mass δ phase : Fin κ → ℝ) (hm : ∀ j, 0 ≤ mass j) (hδ : ∀ j, 0 < δ j)
    (hphase : ∀ j, |phase j| ≤ 1) (hgap : xiEntropyGap mass δ = 0) :
    (∀ n : Nat, 1 ≤ n → xiComovingFourier mass δ phase n = 0) ∧
      Matrix.rank (derived_exact_entropy_saturation_excludes_multidefect_hankel κ mass δ phase) ≤
        1 := by
  have hvanish : ∀ n : Nat, 1 ≤ n → xiComovingFourier mass δ phase n = 0 := by
    intro n hn
    have hbound :=
      (paper_xi_entropy_gap_exponential_suppression_nonzero_fingerprint
        mass δ phase hm hδ hphase (n := n) hn).1
    have habs : |xiComovingFourier mass δ phase n| = 0 := by
      exact le_antisymm (by simpa [hgap] using hbound) (abs_nonneg _)
    exact abs_eq_zero.mp habs
  let a : Fin κ → ℝ := fun i => if i.1 = 0 then xiComovingFourier mass δ phase 0 else 0
  let b : Fin κ → ℝ := fun j => if j.1 = 0 then 1 else 0
  have hhankel :
      derived_exact_entropy_saturation_excludes_multidefect_hankel κ mass δ phase =
        Matrix.vecMulVec a b := by
    ext i j
    by_cases hi : i.1 = 0
    · by_cases hj : j.1 = 0
      · have hij : i.1 + j.1 = 0 := by omega
        simp [derived_exact_entropy_saturation_excludes_multidefect_hankel, a, b,
          Matrix.vecMulVec_apply, hi, hj]
      · have hsum : 1 ≤ i.1 + j.1 := by
          have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj
          omega
        have hjone : 1 ≤ j.1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj)
        simp [derived_exact_entropy_saturation_excludes_multidefect_hankel, a, b, hi, hj,
          Matrix.vecMulVec_apply, hvanish j.1 hjone]
    · have hsum : 1 ≤ i.1 + j.1 := by
        have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi
        omega
      exact by
        by_cases hj : j.1 = 0
        · have hione : 1 ≤ i.1 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi)
          simp [derived_exact_entropy_saturation_excludes_multidefect_hankel, a, b, hi, hj,
            Matrix.vecMulVec_apply, hvanish i.1 hione]
        · simp [derived_exact_entropy_saturation_excludes_multidefect_hankel, a, b, hi, hj,
            Matrix.vecMulVec_apply, hvanish (i.1 + j.1) hsum]
  refine ⟨hvanish, ?_⟩
  rw [hhankel]
  exact Matrix.rank_vecMulVec_le a b

end Omega.Zeta
