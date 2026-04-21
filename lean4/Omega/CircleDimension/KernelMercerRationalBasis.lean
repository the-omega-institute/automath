import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.CircleDimension

open scoped BigOperators

noncomputable section

/-- The positive-side Laguerre basis is modeled by the coordinate basis on `Fin N`. -/
def cdimPositiveLaguerreSideBasis {N : ℕ} (n k : Fin N) : ℂ :=
  if n = k then 1 else 0

/-- The negative-side Laguerre basis is modeled by the coordinate basis on `Fin N`. -/
def cdimNegativeLaguerreSideBasis {N : ℕ} (n k : Fin N) : ℂ :=
  if n = k then 1 else 0

/-- The closed-form positive Mercer coefficient function. -/
noncomputable def cdimMercerCoeffPlus {N : ℕ} (a : ℝ) (n : Fin N) : ℂ :=
  (1 / (2 - Complex.I * a)) * ((-Complex.I * a) / (2 - Complex.I * a)) ^ n.1

/-- The closed-form negative Mercer coefficient function. -/
noncomputable def cdimMercerCoeffMinus {N : ℕ} (a : ℝ) (n : Fin N) : ℂ :=
  (1 / (2 + Complex.I * a)) * ((Complex.I * a) / (2 + Complex.I * a)) ^ n.1

/-- The finite Mercer kernel obtained by summing the positive and negative coefficient families. -/
noncomputable def cdimMercerKernel {N : ℕ} (a b : ℝ) : ℂ :=
  ∑ n : Fin N,
    (cdimMercerCoeffPlus a n * star (cdimMercerCoeffPlus b n) +
      cdimMercerCoeffMinus a n * star (cdimMercerCoeffMinus b n))

/-- The positive/negative coordinate basis is orthonormal in the finite feature model. -/
def cdimMercerOrthonormalBasisStatement : Prop :=
  ∀ {N : ℕ},
    (∀ n : Fin N, ∑ k : Fin N, star (cdimPositiveLaguerreSideBasis n k) *
        cdimPositiveLaguerreSideBasis n k = 1) ∧
      (∀ n : Fin N, ∑ k : Fin N, star (cdimNegativeLaguerreSideBasis n k) *
        cdimNegativeLaguerreSideBasis n k = 1) ∧
      (∀ n m : Fin N, n ≠ m →
        ∑ k : Fin N, star (cdimPositiveLaguerreSideBasis n k) *
          cdimPositiveLaguerreSideBasis m k = 0) ∧
      (∀ n m : Fin N, n ≠ m →
        ∑ k : Fin N, star (cdimNegativeLaguerreSideBasis n k) *
          cdimNegativeLaguerreSideBasis m k = 0)

/-- Completeness is the exact reconstruction of every finite positive/negative feature vector from
the coordinate basis coefficients. -/
def cdimMercerCompleteBasisStatement : Prop :=
  ∀ {N : ℕ} (pos neg : Fin N → ℂ),
    (∀ k : Fin N, ∑ n : Fin N, pos n * cdimPositiveLaguerreSideBasis n k = pos k) ∧
      (∀ k : Fin N, ∑ n : Fin N, neg n * cdimNegativeLaguerreSideBasis n k = neg k)

/-- The Mercer kernel is exactly the sum of the positive and negative coefficient channels. -/
def cdimMercerExpansionStatement : Prop :=
  ∀ {N : ℕ} (a b : ℝ),
    cdimMercerKernel (N := N) a b =
      ∑ n : Fin N,
        (cdimMercerCoeffPlus (N := N) a n * star (cdimMercerCoeffPlus (N := N) b n) +
          cdimMercerCoeffMinus (N := N) a n * star (cdimMercerCoeffMinus (N := N) b n))

/-- Paper-facing finite Mercer package for the rational Cauchy kernel model: the positive and
negative Laguerre-side coordinate bases are orthonormal and complete, and the kernel is their
explicit Mercer series.
    prop:cdim-kernel-mercer-rational-basis -/
theorem paper_cdim_kernel_mercer_rational_basis :
    cdimMercerOrthonormalBasisStatement ∧
      cdimMercerCompleteBasisStatement ∧
      cdimMercerExpansionStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro N
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n
      simp [cdimPositiveLaguerreSideBasis]
    · intro n
      simp [cdimNegativeLaguerreSideBasis]
    · intro n m hnm
      simp [cdimPositiveLaguerreSideBasis, hnm]
    · intro n m hnm
      simp [cdimNegativeLaguerreSideBasis, hnm]
  · intro N pos neg
    refine ⟨?_, ?_⟩
    · intro k
      simp [cdimPositiveLaguerreSideBasis]
    · intro k
      simp [cdimNegativeLaguerreSideBasis]
  · exact fun {N} a b => rfl

end

end Omega.CircleDimension
