import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

namespace Omega.CircleDimension

private lemma normSq_sub_one (z : ℂ) :
    Complex.normSq (z - 1) = Complex.normSq z + 1 - 2 * Complex.re z := by
  simp [Complex.normSq_apply, sub_eq_add_neg]
  ring

private lemma normSq_add_one (z : ℂ) :
    Complex.normSq (z + 1) = Complex.normSq z + 1 + 2 * Complex.re z := by
  simp [Complex.normSq_apply]
  ring

/-- Interior singularities for the Cayley transform are excluded by nonnegative real part, so any
admissible singular behavior is forced to the boundary. -/
def xiHorizonBoundaryOnlySingularity (C : ℂ → ℂ) : Prop :=
  ∀ w, 0 ≤ Complex.re (C w) → C w + 1 ≠ 0

private lemma carath_schur_pointwise (z : ℂ) :
    0 ≤ Complex.re z ↔ z + 1 ≠ 0 ∧ ‖(z - 1) / (z + 1)‖ ≤ 1 := by
  constructor
  · intro hRe
    have hz_ne : z + 1 ≠ 0 := by
      intro hz
      have hz_re : Complex.re z + 1 = 0 := by
        simpa using congrArg Complex.re hz
      linarith
    have hnum_le :
        Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) := by
      nlinarith [normSq_sub_one z, normSq_add_one z, hRe]
    have hnorm_sq : ‖z - 1‖ ^ 2 ≤ ‖z + 1‖ ^ 2 := by
      simpa [Complex.normSq_eq_norm_sq] using hnum_le
    have hnorm_le : ‖z - 1‖ ≤ ‖z + 1‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hnorm_sq
    have hden_pos : 0 < ‖z + 1‖ := norm_pos_iff.mpr hz_ne
    have habs : ‖(z - 1) / (z + 1)‖ ≤ 1 := by
      have hdiv : ‖z - 1‖ / ‖z + 1‖ ≤ 1 := by
        exact (div_le_iff₀ hden_pos).2 (by simpa using hnorm_le)
      simpa [norm_div] using hdiv
    exact ⟨hz_ne, habs⟩
  · rintro ⟨hz_ne, hNorm⟩
    have hden_pos : 0 < ‖z + 1‖ := norm_pos_iff.mpr hz_ne
    have hdiv : ‖z - 1‖ / ‖z + 1‖ ≤ 1 := by
      simpa [norm_div] using hNorm
    have hnorm_le : ‖z - 1‖ ≤ ‖z + 1‖ := by
      have htmp : ‖z - 1‖ ≤ 1 * ‖z + 1‖ := by
        exact (div_le_iff₀ hden_pos).1 (by simpa using hdiv)
      simpa using htmp
    have hnorm_sq : ‖z - 1‖ ^ 2 ≤ ‖z + 1‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm_le
    have hnum_le : Complex.normSq (z - 1) ≤ Complex.normSq (z + 1) := by
      simpa [Complex.normSq_eq_norm_sq] using hnorm_sq
    nlinarith [normSq_sub_one z, normSq_add_one z, hnum_le]

/-- Paper-facing Cayley equivalence: nonnegative real part of the horizon Carathéodory field is
equivalent to the Schur bound for its Cayley transform, and the same hypothesis rules out any
interior pole of the denominator `C + 1`.
    thm:xi-horizon-carath-schur-equivalence -/
theorem paper_xi_horizon_carath_schur_equivalence (C S : ℂ → ℂ)
    (hS : ∀ w, S w = (C w - 1) / (C w + 1)) :
    (∀ w, 0 ≤ Complex.re (C w) ↔ C w + 1 ≠ 0 ∧ ‖S w‖ ≤ 1) ∧
      xiHorizonBoundaryOnlySingularity C := by
  constructor
  · intro w
    simpa [hS w] using carath_schur_pointwise (C w)
  · intro w hRe
    exact (carath_schur_pointwise (C w)).1 hRe |>.1

end Omega.CircleDimension
